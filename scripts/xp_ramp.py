#!/usr/bin/env python3
"""Ramp metering for the sources (simulation; nothing here is proved).

Traffic engineering keeps a highway at its critical density with a feedback controller on the
on-ramps (ALINEA: r(t+1) = r(t) + K (o_target - o_measured)), because throughput collapses past
the critical density (the fundamental diagram).  Our proved schemes throttle the sources with a
fixed rule: a packet leaves its injection channel only towards a router with at least g = 4 of
its 8 outgoing channels free.  This script replaces that rule by controllers and compares.

It does not re-implement the simulators: it takes the source of `routing_sim.simulate` (8 x 8
mesh, `duatoMesh` with the `tiered` selection, XY escape) and of `torus_experiments.sim` (8 x 8
torus, `min` and `bandit2m7f5k`) and replaces, at run time, the throttle line by a call to a
controller (`gate`) and adds a per-cycle call (`tick`).  With the controller `fix4` the result is
bit-for-bit the original simulator's (`python3 scripts/xp_ramp.py check`).  The controllers use
their own random generator, so the simulators' streams are unchanged.

Controllers (spec strings):
  fix<g>                fixed threshold g (fix4 = the proved scheme), g = 0 .. 8
  gcap<o>_<g>           time-free, global: a source may inject only while the global network
                        occupancy is below o/100 (and the next router has >= g of 8 free)
  lcap<o>_<r>_<g>       time-free, local: same with the occupancy of the routers within distance
                        r of the source (r = 0: the source's own router)
  lg<lo>_<hi>_<o>_<r>   time-free, local: threshold lo while the local occupancy (radius r) is
                        below o/100, hi above it
  alr<K>_<o>_<r>_<g>    ALINEA on an injection probability: every cycle
                        p_s += K/1000 (o/100 - occupancy_s), clipped to [0.02, 1]; the source may
                        inject in a cycle with probability p_s (and >= g of 8 free next);
                        r = -1: global occupancy (reference)
  alg<K>_<o>_<r>        ALINEA on the threshold: G_s += K/1000 (occupancy_s - o/100), clipped to
                        [0, 8]; threshold round(G_s)
  le.., age.., are..    as lg, alg, alr, measuring the occupancy of the escape channels
                        (virtual channel 0) only
  lr<lo>_<hi>_<f>_<r>   time-free: threshold hi while at least f % of the occupied channels within
                        distance r (r = -1: the whole network) are escape channels, lo otherwise
  lx<lo>_<hi>_<f>_<r>   as lr, and in the high mode also the rule of nesc
  nesc<g>               fixed threshold g; and a source injects into the escape channel only
                        while its own router's outgoing channels are all free

Usage: python3 scripts/xp_ramp.py check
       python3 scripts/xp_ramp.py run mesh|torus|torusB SPECS PATTERNS RATES SEEDS [CYCLES]
           (torus: scheme `min`; torusB: scheme `bandit2m7f5k`)
       python3 scripts/xp_ramp.py table FILES...                    peak over loads, mean ± se
       python3 scripts/xp_ramp.py paired fix4 FILES...              paired differences to fix4
Results of `run` are appended as JSON lines to $XP_OUT (default ./xp_ramp.jsonl).
The fundamental diagram is `run` with the controllers gcap<o>_0 at offered load 1.0: the
occupancy cap sets the network occupancy, and the accepted throughput is read against it.
"""
import inspect, json, os, random, sys, time
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import routing_sim as R
import torus_experiments as T

K = 8
N = K * K


# ---------------------------------------------------------------- controllers

class Ctrl:
    """Source controller.  `tick` runs at the start of every cycle and sets, per source, whether
    it may inject this cycle (`allow`) and its threshold (`g`, out of 8 outgoing channels)."""

    def __init__(self, spec, out_counts, nbrs, seed):
        self.spec = spec
        self.rnd = random.Random(1000 + seed)
        self.nout = out_counts          # existing outgoing network channels per router
        self.nch = sum(out_counts)
        self.allow = [True] * N
        self.g = [4] * N
        self.kind, self.par = self.parse(spec)
        r = self.par.get('r', None)
        self.ball = None
        if r is not None and r >= 0:
            # routers within distance r (BFS on the router graph)
            self.ball = []
            for s in range(N):
                seen = {s}; fr = [s]
                for _ in range(r):
                    fr = [v for u in fr for v in nbrs[u] if v not in seen and not seen.add(v)]
                b = sorted(seen)
                self.ball.append((b, sum(out_counts[v] for v in b)))
        self.p = [1.0] * N
        self.G = [float(self.par.get('g0', 4))] * N
        # statistics
        self.t = 0; self.occ_sum = 0.0; self.nsamp = 0; self.occ0_sum = 0.0
        self.series = []                # (cycle, global occupancy) samples
        self.ctl_sum = 0.0

    @staticmethod
    def parse(spec):
        def nums(s):
            return [int(x) for x in s.split('_')]
        if spec.startswith('fix'):
            return 'fix', {'g': int(spec[3:])}
        if spec.startswith('gcap'):
            o, g = nums(spec[4:]); return 'cap', {'o': o / 100, 'r': -1, 'g': g}
        if spec.startswith('lcap'):
            o, r, g = nums(spec[4:]); return 'cap', {'o': o / 100, 'r': r, 'g': g}
        if spec.startswith('lg'):
            lo, hi, o, r = nums(spec[2:]); return 'lg', {'lo': lo, 'hi': hi, 'o': o / 100, 'r': r}
        if spec.startswith('alr'):
            k, o, r, g = (int(x) for x in spec[3:].split('_'))
            return 'alr', {'K': k / 1000, 'o': o / 100, 'r': r, 'g': g}
        if spec.startswith('lr'):
            lo, hi, o, r = nums(spec[2:])
            return 'lg', {'lo': lo, 'hi': hi, 'o': o / 100, 'r': r, 'sig': 'frac'}
        if spec.startswith('lx'):
            lo, hi, o, r = nums(spec[2:])
            return 'lg', {'lo': lo, 'hi': hi, 'o': o / 100, 'r': r, 'sig': 'frac', 'nesc': True}
        if spec.startswith('nesc'):
            return 'fix', {'g': int(spec[4:]), 'nesc': True}
        if spec.startswith('le'):
            lo, hi, o, r = nums(spec[2:])
            return 'lg', {'lo': lo, 'hi': hi, 'o': o / 100, 'r': r, 'sig': 'esc'}
        if spec.startswith('age'):
            k, o, r = (int(x) for x in spec[3:].split('_'))
            return 'alg', {'K': k / 1000, 'o': o / 100, 'r': r, 'g0': 4, 'sig': 'esc'}
        if spec.startswith('are'):
            k, o, r, g = (int(x) for x in spec[3:].split('_'))
            return 'alr', {'K': k / 1000, 'o': o / 100, 'r': r, 'g': g, 'sig': 'esc'}
        if spec.startswith('alg'):
            k, o, r = (int(x) for x in spec[3:].split('_'))
            return 'alg', {'K': k / 1000, 'o': o / 100, 'r': r, 'g0': 4}
        raise ValueError(spec)

    def tick(self, t, occ):
        cnt = [0] * N
        cnt0 = [0] * N                  # escape (virtual channel 0) channels only
        tot = tot0 = 0
        for c in occ:
            if (c >> 1) % 5 != 4:
                cnt[c // 10] += 1; tot += 1
                if c % 2 == 0:
                    cnt0[c // 10] += 1; tot0 += 1
        glob = tot / self.nch
        glob0 = 2 * tot0 / self.nch
        self.t = t
        if t >= self.warmup:
            self.occ_sum += glob; self.nsamp += 1; self.occ0_sum += glob0
        k, P = self.kind, self.par
        if P.get('nesc'):
            self.own_busy = [cnt[s] > 0 for s in range(N)]
            if not hasattr(self, 'hmode'):
                self.hmode = [True] * N
        if k == 'fix':
            return
        r = P['r']
        if P.get('sig') == 'esc':
            cnt, glob, half = cnt0, glob0, 2
        else:
            half = 1
        if P.get('sig') == 'frac':      # share of the occupied channels that are escape channels
            if r >= 0:
                loc = [sum(cnt0[v] for v in b) / max(1, sum(cnt[v] for v in b)) for b, m in self.ball]
            else:
                loc = [tot0 / max(1, tot)] * N
        elif r >= 0:
            loc = [half * sum(cnt[v] for v in b) / m for b, m in self.ball]
        else:
            loc = [glob] * N
        if k == 'cap':
            for s in range(N):
                self.allow[s] = loc[s] < P['o']; self.g[s] = P['g']
        elif k == 'lg':
            for s in range(N):
                self.g[s] = P['lo'] if loc[s] < P['o'] else P['hi']
            if P.get('nesc'):
                self.hmode = [loc[s] >= P['o'] for s in range(N)]
        elif k == 'alr':
            Kp, o = P['K'], P['o']
            rr = self.rnd.random
            for s in range(N):
                p = self.p[s] + Kp * (o - loc[s])
                p = 1.0 if p > 1 else 0.02 if p < 0.02 else p
                self.p[s] = p
                self.allow[s] = p >= 1.0 or rr() < p
                self.g[s] = P['g']
            if t >= self.warmup:
                self.ctl_sum += sum(self.p) / N
        elif k == 'alg':
            Kp, o = P['K'], P['o']
            for s in range(N):
                G = self.G[s] + Kp * (loc[s] - o)
                G = 8.0 if G > 8 else 0.0 if G < 0 else G
                self.G[s] = G
                self.g[s] = int(G + 0.5)
            if t >= self.warmup:
                self.ctl_sum += sum(self.G) / N

    def gate(self, s, free, nfree):
        """`free`: the free hops of the packet in the injection channel of `s`; `nfree(x)`: free
        outgoing channels (out of 8) of the router `x` leads to."""
        if not self.allow[s]:
            return []
        if self.par.get('nesc') and self.own_busy[s] and self.hmode[s]:
            free = [x for x in free if x % 2 == 1]   # no direct injection into the escape
        g = self.g[s] if self.kind != 'fix' else self.par['g']
        if g <= 0:
            return free
        return [x for x in free if nfree(x) >= g]


# ---------------------------------------------------------------- hooked simulators

def _patch(fn, repl, extra):
    src = inspect.getsource(fn)
    for a, b in repl:
        assert src.count(a) == 1, (fn.__name__, a)
        src = src.replace(a, b)
    ns = dict(fn.__globals__)
    ns.update(extra)
    exec(compile(src, f'<xp_ramp {fn.__name__}>', 'exec'), ns)
    return ns[fn.__name__]


_CUR = {}

MESH_SIM = _patch(R.simulate, [
    ("""            if throttle is not None and c // 2 % 5 == 4:
                free = [c2 for c2 in free if free_after(c2) >= throttle]""",
     """            if c // 2 % 5 == 4:
                free = _CUR['ctrl'].gate(c // 10, free, free_after)"""),
    ("""    for t in range(cycles):
        for c in [c for c, (d, _) in occ.items() if head(c) == d]:""",
     """    for t in range(cycles):
        _CUR['ctrl'].tick(t, occ)
        for c in [c for c, (d, _) in occ.items() if head(c) == d]:"""),
], {'_CUR': _CUR})

TORUS_SIM = _patch(T.sim, [
    ("""                if g and src: free = [x for x in free if sum(1 for o in out[head[x]] if o not in occ) >= thr[head[x]]]""",
     """                if src: free = _CUR['ctrl'].gate(u, free, lambda x: sum(1 for o in out[head[x]] if o not in occ) * 8 / (2 * net.deg[head[x]]))"""),
    ("""    for t in range(cycles):
        if scheme.startswith('ring')""",
     """    for t in range(cycles):
        _CUR['ctrl'].tick(t, occ)
        if scheme.startswith('ring')"""),
], {'_CUR': _CUR})


def mesh_info():
    nb = [[v for v in (u + 1 if u % K < K - 1 else -1, u - 1 if u % K else -1,
                       u + K if u // K < K - 1 else -1, u - K if u >= K else -1) if v >= 0]
          for u in range(N)]
    return [2 * len(a) for a in nb], nb


def torus_info():
    net = T.NET
    nb = [[v for v in net.adj[u] if v >= 0] for u in range(N)]
    return [2 * len(a) for a in nb], nb


import functools
MESH_ROUTE = functools.lru_cache(maxsize=None)(R.mesh(K)[2]['duatoMesh'])   # same lists, memoised


def run_one(topo, spec, pattern, rate, seed, cycles=3000, warmup=1000):
    oc, nb = mesh_info() if topo == 'mesh' else torus_info()
    ctrl = Ctrl(spec, oc, nb, seed)
    ctrl.warmup = warmup
    _CUR['ctrl'] = ctrl
    if topo == 'mesh':
        thr, lat = MESH_SIM(K, MESH_ROUTE, rate, pattern, 'tiered', cycles=cycles,
                            warmup=warmup, seed=seed)
    else:
        scheme = 'min' if topo == 'torus' else 'bandit2m7f5k'
        thr, lat = TORUS_SIM(scheme, rate, pattern, seed=seed, cycles=cycles, warmup=warmup)
    return {'topo': topo, 'spec': spec, 'pattern': pattern, 'rate': rate, 'seed': seed,
            'cycles': cycles, 'thr': thr, 'lat': lat,
            'occ': ctrl.occ_sum / max(1, ctrl.nsamp), 'occ0': ctrl.occ0_sum / max(1, ctrl.nsamp),
            'ctl': ctrl.ctl_sum / max(1, ctrl.nsamp)}


def check():
    a = R.simulate(K, MESH_ROUTE, 0.6, 'uniform', 'T4:tiered', cycles=1500, warmup=500, seed=3)
    b = run_one('mesh', 'fix4', 'uniform', 0.6, 3, cycles=1500, warmup=500)
    print('mesh  original', a, 'hooked', (b['thr'], b['lat']))
    assert a == (b['thr'], b['lat'])
    a = T.sim('min', 0.8, 'transpose', seed=3, cycles=1500, warmup=500)
    b = run_one('torus', 'fix4', 'transpose', 0.8, 3, cycles=1500, warmup=500)
    print('torus original', a, 'hooked', (b['thr'], b['lat']))
    assert a == (b['thr'], b['lat'])
    a = T.sim('bandit2m7f5k', 0.8, 'tornado', seed=3, cycles=1500, warmup=500)
    b = run_one('torusB', 'fix4', 'tornado', 0.8, 3, cycles=1500, warmup=500)
    print('torusB original', a, 'hooked', (b['thr'], b['lat']))
    assert a == (b['thr'], b['lat'])
    print('ok: fix4 reproduces the original simulators exactly')


def main():
    cmd = sys.argv[1]
    if cmd == 'check':
        check(); return
    if cmd == 'run':
        topo, specs, pats, rates, seeds = sys.argv[2:7]
        cycles = int(sys.argv[7]) if len(sys.argv) > 7 else 3000
        out = os.environ.get('XP_OUT', 'xp_ramp.jsonl')
        for spec in specs.split(','):
            for pat in pats.split(','):
                for rate in (float(x) for x in rates.split(',')):
                    for seed in (int(x) for x in seeds.split(',')):
                        t0 = time.time()
                        res = run_one(topo, spec, pat, rate, seed, cycles=cycles,
                                      warmup=cycles // 3)
                        res['sec'] = round(time.time() - t0, 2)
                        with open(out, 'a') as f:
                            f.write(json.dumps(res) + '\n')
                        print(json.dumps(res), flush=True)
        return
    if cmd == 'table':
        table(sys.argv[2:]); return
    if cmd == 'paired':
        paired(sys.argv[2], sys.argv[3:]); return
    raise SystemExit(__doc__)


def table(files):
    """Peak over offered loads of the seed mean (as `torus_significance.py`), with its standard
    error, per topology, controller and pattern; and the value at the highest offered load."""
    rows = [json.loads(l) for f in files for l in open(f)]
    from collections import defaultdict
    by = defaultdict(list)
    for r in rows:
        by[(r['topo'], r['spec'], r['pattern'], r['rate'])].append(r)
    keys = sorted({(t, s) for t, s, _, _ in by}, key=lambda x: (x[0], x[1]))
    for topo in sorted({t for t, _ in keys}):
        pats = [p for p in ['uniform', 'transpose', 'shuffle', 'bitrev', 'bitcomp', 'hotspot',
                            'tornado', 'neighbor', 'randperm']
                if any(k[0] == topo and k[2] == p for k in by)]
        print(f'== {topo}: peak over offered loads, mean ± se (1e-4) [seeds]; last: at the highest load')
        print(f'{"spec":<18}' + ''.join(f'{p[:9]:>20}' for p in pats))
        for t, spec in keys:
            if t != topo: continue
            cells = []
            for p in pats:
                rs = sorted(r for (tt, ss, pp, r) in by if tt == t and ss == spec and pp == p)
                if not rs: cells.append(''); continue
                def stat(r):
                    v = [x['thr'] for x in by[(t, spec, p, r)]]
                    m = sum(v) / len(v)
                    se = (sum((a - m) ** 2 for a in v) / (len(v) - 1)) ** .5 / len(v) ** .5 if len(v) > 1 else 0
                    return m, se, len(v)
                best = max(rs, key=lambda r: stat(r)[0])
                m, se, n = stat(best)
                cells.append(f'{m:.4f}±{se*1e4:.0f}[{n}]@{best:g}')
            print(f'{spec:<18}' + ''.join(f'{c:>20}' for c in cells))



def paired(base, files):
    """Each controller against `base` (e.g. fix4) on the same seeds: per seed, the peak over the
    offered loads both were run at; mean difference and its standard error (paired)."""
    rows = [json.loads(l) for f in files for l in open(f)]
    from collections import defaultdict
    v = defaultdict(dict)
    for r in rows:
        v[(r['topo'], r['spec'], r['pattern'], r['seed'])][r['rate']] = r['thr']
    for topo in sorted({k[0] for k in v}):
        specs = sorted({k[1] for k in v if k[0] == topo and k[1] != base})
        pats = [p for p in ['uniform', 'transpose', 'shuffle', 'bitrev', 'bitcomp', 'hotspot',
                            'tornado', 'neighbor', 'randperm'] if any(k[0] == topo and k[2] == p for k in v)]
        print(f'== {topo}: peak minus {base}, paired by seed, mean ± se (1e-4) [seeds]')
        print(f'{"spec":<16}' + ''.join(f'{p[:9]:>16}' for p in pats))
        for spec in specs:
            cells = []
            for p in pats:
                d = []
                for (t, s2, pp, sd), a in v.items():
                    if t == topo and s2 == spec and pp == p and (t, base, p, sd) in v:
                        b = v[(t, base, p, sd)]
                        common = [r for r in a if r in b]
                        if common:
                            d.append(max(a[r] for r in common) - max(b[r] for r in common))
                if not d: cells.append(''); continue
                m = sum(d) / len(d)
                se = (sum((x - m) ** 2 for x in d) / (len(d) - 1)) ** .5 / len(d) ** .5 if len(d) > 1 else 0
                cells.append(f'{m*1e4:+.0f}±{se*1e4:.0f}[{len(d)}]')
            print(f'{spec:<16}' + ''.join(f'{c:>16}' for c in cells))


if __name__ == '__main__':
    main()
