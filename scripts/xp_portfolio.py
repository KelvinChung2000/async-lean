#!/usr/bin/env python3
"""A portfolio (mode-selection) learner on top of the mesh and torus schemes of `xp_combo2.py`
(simulation only).

A network-wide controller runs one of K modes at a time.  Time is cut into epochs of E cycles;
the controller measures the packets delivered per cycle in each epoch (after a settling time of
S cycles when the epoch started with a switch), keeps the mean of the last W samples of every
mode, and
  1. explores: R0 rounds over all modes, each round in a random order;
  2. exploits the mode with the best estimate (the incumbent);
  3. probes every other mode again after I_m epochs: I_m starts at I0, doubles (up to Imax) each
     time a probe finds the mode more than `far` below the incumbent (straight to Imax when more
     than `elim` below, if elim > 0), and resets to I0 when the probe finds it close; a probed
     mode becomes the incumbent only when its estimate beats the incumbent's by more than the
     hysteresis h.
The controller reads only delivery counts (ejections) and the occupancy of the injection
channels (configurations), i.e. history, and decides which selection is in force.

Every mode is a selection of ONE proved network:
  mesh   the west-first mesh (`route=wf`: XY escape on VC0, the west-first VC0 hops, any
         productive VC1 hop); every mode's tier list contains the throttled escape tier
         `esc` with a fixed g <= 8, so each mode alone is `westFirstTiers_correct`.  The
         switching is a history-dependent strategy whose selections satisfy SourceSel; the
         strategy theorem is instantiated for `duatoMesh` (`duatoMesh_strategy_safe`), not yet
         for `westFirstMesh` (the same `Strategy.safe` with `wf_closed`, `wf_pairs_finite`,
         `xyEscape`, `wf_esc_conn`, `wf_wf`, `Mesh.esc_not_source`, `Mesh.turnDuato_not_source`,
         `wfDist` / `wf_dist`).
  torus  the combined scheme `xp_combo.csim` (price hops, toll detours); modes differ in the
         escape-share throttle thresholds (`thr`, `thr2`, `thr3`/`dth`), all <= 8 with the lx
         blocking rule: `torus_throttle_safe` / `torus_combo_safe` cover any history-dependent
         choice among them.

Specs (colon-separated; first token names the portfolio, then learner overrides key=value):
  PM:<set>[:E=..:S=..:R0=..:I0=..:Imax=..:h=..:far=..:W=..:elim=..:th=..:d=..]
                                                            mesh portfolio, modes MSETS[set]
      th >= 0: congestion-gated learning: run the default mode d until an epoch in which at
      least a share th of the sources had their injection channel occupied >= 97 % of the
      epoch; from then on learn as above, but do not probe while the incumbent's last epoch
      was below th (th < 0: learn from the start).
  PT:<set>[:...]                                            torus portfolio, modes TSETS[set]
  anything else: xp_combo2.run_one (M:, A:, T:, TC:)
Result of a portfolio run: [throughput, latency/hops, -, -, switches after warmup,
 fraction of the measured cycles in each mode...].

Usage:
  python3 scripts/xp_portfolio.py check
  python3 scripts/xp_portfolio.py run SPECS PATTERNS RATES SEEDS CHAINS CYCLES
  python3 scripts/xp_portfolio.py jobs FILE          (one 'spec|pats|rates|seeds|chains|cycles' per line)
  python3 scripts/xp_portfolio.py report MAIN OTHERS RATES SEEDS CHAINS CYCLES [PATS]
          [REFCACHE REFCYC [REFSEEDS [REFRATES]]]
Cache: XP_PF_CACHE (default xp_portfolio.json in the system temporary directory);
XP_PF_PROCS processes (default 3).
"""
import inspect
import json
import os
import random
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import xp_combo2 as X2
import xp_backpressure as XP
import xp_arbiter as XA
import xp_ramp as XR

# ------------------------------------------------------------------ mode sets
MESH_B = 'route=wf:tiers=str+esc+vc1:sel=P:gdev=2:devset=all'      # best mesh config (g4)
MSETS = {
    # best config / west-first adaptive, weak throttle / XY on both VCs / price tiers
    'm4': [MESH_B, 'route=wf:tiers=all+esc:thr=g2', 'route=wf:tiers=xy+esc:thr=g0',
           'route=wf:tiers=pref+esc+vc1:sel=price'],
    'm3': [MESH_B, 'route=wf:tiers=all+esc:thr=g2', 'route=wf:tiers=xy+esc:thr=g0'],
    'm1': [MESH_B],
}
_TB = 'hop=price:src=toll:pm=0.2'
TSETS = {
    # three-way threshold (xp_combo2) / published combined / single threshold 33
    't3': [(_TB, 'lx2_4_34_2', 'lx2_4_36_2', 'lx2_4_32_2', 0.01),
           (_TB, 'lx2_4_32_2', 'lx2_4_35_2', '-', -1.0),
           (_TB, 'lx2_4_33_2', 'lx2_4_33_2', '-', -1.0)],
    't1': [(_TB, 'lx2_4_34_2', 'lx2_4_36_2', 'lx2_4_32_2', 0.01)],
}
LDEF = dict(E=250, S=50, R0=2, I0=8, Imax=64, h=0.005, far=0.03, W=4, th=-1.0, d=0, elim=0.0)


# ------------------------------------------------------------------ the learner
class Learner:
    def __init__(self, K, seed, warmup, E=250, S=50, R0=2, I0=8, Imax=64, h=0.005, far=0.03,
                 W=4, th=-1.0, d=0, elim=0.0, nsrc=64):
        self.K, self.E, self.S, self.I0, self.Imax = K, int(E), int(S), int(I0), int(Imax)
        self.th, self.nsrc, self.elim = th, nsrc, elim
        self.inj = [0] * nsrc            # per source: cycles with its injection channel occupied
        self.congested = th < 0          # th < 0: always explore
        self.occ_log = []
        self.h, self.far, self.W = h, far, int(W)
        self.warmup = warmup
        self.rnd = random.Random(7919 + seed)
        self.n = 0                       # deliveries so far (incremented by the simulator)
        self.samples = [[] for _ in range(K)]
        self.queue = []
        for _ in range(int(R0)):
            r = list(range(K))
            self.rnd.shuffle(r)
            self.queue += r
        self.cur = self.queue.pop(0) if K > 1 and th < 0 else int(d)
        self.inc = None
        self.I = [self.I0] * K
        self.due = [0] * K
        self.epoch = 0
        self.ms = self.S                 # start of the measurement in this epoch
        self.n0 = 0
        self.time = [0] * K
        self.switches = 0

    def est(self, m):
        s = self.samples[m]
        return sum(s) / len(s) if s else -1.0

    def step(self, t, inj=()):
        """Called at the start of every cycle with the sources whose injection channel is occupied;
        returns the mode to use from now on, or None."""
        if t >= self.warmup:
            self.time[self.cur] += 1
        if t == self.ms:
            self.n0 = self.n
        if inj:
            acc = self.inj
            for s in inj:
                acc[s] += 1
        if t == 0 or t % self.E:
            return None
        # the share of sources whose injection channel was occupied >= 97 % of the epoch
        occ = sum(1 for x in self.inj if x >= 0.97 * self.E) / self.nsrc
        self.inj = [0] * self.nsrc
        self.occ_log.append(round(occ, 3))
        busy = self.th < 0 or occ >= self.th
        if self.K == 1:
            return None
        if not self.congested:           # the default mode keeps up: nothing to learn
            if not busy:
                return None
            self.congested = True
        # end of an epoch: record the sample
        span = t - self.ms
        if span > 0:
            s = self.samples[self.cur]
            s.append((self.n - self.n0) / span)
            if len(s) > self.W:
                s.pop(0)
        self.epoch += 1
        old = self.cur
        if self.queue:
            nxt = self.queue.pop(0)
        else:
            if self.inc is None:         # end of the exploration
                self.inc = max(range(self.K), key=self.est)
                for m in range(self.K):
                    if m != self.inc:
                        self._resched(m)
            elif old != self.inc:        # end of a probe
                if self.est(old) > self.est(self.inc) * (1 + self.h):
                    prev, self.inc = self.inc, old
                    self._resched(prev)
                else:
                    self._resched(old)
            due = [m for m in range(self.K) if m != self.inc and self.due[m] <= self.epoch]
            if not busy and old == self.inc:
                due = []                 # the incumbent keeps up: no probe
            nxt = min(due, key=lambda m: self.due[m]) if due else self.inc
        self.cur = nxt
        sw = nxt != old
        if sw and t >= self.warmup:
            self.switches += 1
        self.ms = t + (self.S if sw else 0)
        if self.ms == t:
            self.n0 = self.n
        return nxt if sw else None

    def _resched(self, m):
        if self.elim > 0 and self.est(m) < self.est(self.inc) * (1 - self.elim):
            self.I[m] = self.Imax        # eliminated: probed again only after Imax epochs
        elif self.est(m) < self.est(self.inc) * (1 - self.far):
            self.I[m] = min(2 * self.I[m], self.Imax)
        else:
            self.I[m] = self.I0
        self.due[m] = self.epoch + self.I[m]


def lparse(toks):
    o = dict(LDEF)
    for tok in toks:
        if tok:
            k, v = tok.split('=')
            o[k] = float(v)
    return o


# ------------------------------------------------------------------ patched simulators
_HOOK_OLD = "    for t in range(cycles):\n        if ctrl is not None:\n            ctrl.tick(t, occ)\n"


def _exec(src, ns, name):
    exec(compile(src, f'<xp_portfolio {name}>', 'exec'), ns)
    return ns[name]


_PMSIM = None


def pmsim_fn():
    """xp_combo2.msim with the learner switching tiers / stiers / sx / sel / dev / gdev / devset
    / fixed g at the start of a cycle."""
    global _PMSIM
    if _PMSIM is not None:
        return _PMSIM
    src = inspect.getsource(X2.msim)
    patches = [
        ("def msim(spec, rate, pattern, seed=1, chain='seq', cycles=2000, warmup=None, k=8):",
         "def pmsim(spec, rate, pattern, seed=1, chain='seq', cycles=2000, warmup=None, k=8):"),
        ("    useprice = sel == 'price'\n", "    useprice = _PF['useprice']\n"),
        (_HOOK_OLD,
         "    for t in range(cycles):\n"
         "        _m = _PF['L'].step(t, [_s for _s in range(n) if ch(_s, 4, 0) in occ])\n"
         "        if _m is not None:\n"
         "            tiers_n, stiers_n, sx, sel, delta, gdev, devset, gfix = _PF['modes'][_m]\n"
         "        if ctrl is not None:\n            ctrl.tick(t, occ)\n"),
        ("            _, born = take(c)\n",
         "            _, born = take(c)\n            _PF['L'].n += 1\n"),
    ]
    for old, new in patches:
        assert src.count(old) == 1, old
        src = src.replace(old, new)
    ns = dict(vars(X2))
    ns['_PF'] = {}
    _PMSIM = (_exec(src, ns, 'pmsim'), ns)
    return _PMSIM


def mesh_mode(spec):
    o = X2.mparse(spec)
    assert o['route'] == 'wf' and o['thr'].startswith('g') and 'esc' in o['tiers'].split('+'), spec
    tiers_n = o['tiers'].split('+')
    stiers_n = o['stiers'].split('+') if o['stiers'] else tiers_n
    sx = set(o['sx'].split('+')) if o['sx'] else set()
    return (tiers_n, stiers_n, sx, o['sel'], o['dev'], o['gdev'], o['devset'], int(o['thr'][1:]))


def pm_run(spec, rate, pattern, seed, chain, cycles):
    toks = spec.split(':')
    modes = MSETS[toks[0]]
    lo = lparse(toks[1:])
    fn, ns = pmsim_fn()
    warmup = cycles // 3
    L = Learner(len(modes), seed, warmup, **lo)
    ns['_PF'].update(L=L, modes=[mesh_mode(m) for m in modes],
                     useprice=any(X2.mparse(m)['sel'] == 'price' for m in modes))
    r = fn(modes[L.cur], rate, pattern, seed=seed, chain=chain, cycles=cycles, warmup=warmup)
    tot = max(1, sum(L.time))
    return [r[0], r[1], 0.0, 0.0, L.switches] + [x / tot for x in L.time]


_PTSIM = None


def ptsim_fn():
    """xp_combo2's patched csim with the learner switching the throttle controllers (thr, thr2,
    thr3 and dth).  The recent-destination signal is always tracked."""
    global _PTSIM
    if _PTSIM is not None:
        return _PTSIM
    X2.tcsim()                          # registers thr3 / dth / dsa in xp_combo's defaults
    import xp_combo as XC
    src = inspect.getsource(XC.csim)
    patches = [   # xp_combo2.tcsim's patches, as there
        ("    ctrl = ctrl2 = None\n", "    ctrl = ctrl2 = ctrl3 = None\n"),
        ("            ctrl2.warmup = warmup\n",
         "            ctrl2.warmup = warmup\n"
         "        if o['thr3'] != '-':\n"
         "            ctrl3 = XR.Ctrl(o['thr3'], oc, nb, seed)\n"
         "            ctrl3.warmup = warmup\n"),
        ("        if ctrl2 is not None:\n            ctrl2.tick(t, occ)\n",
         "        if ctrl2 is not None:\n            ctrl2.tick(t, occ)\n"
         "        if ctrl3 is not None:\n            ctrl3.tick(t, occ)\n"),
        ("free = (ctrl2 if spread[u] else ctrl).gate(",
         "free = (ctrl3 if ctrl3 is not None and (dsh[u] >= o['dth'] if o['dth'] >= 0 else cur[u] != 0) else ctrl2 if spread[u] and ctrl2 is not None else ctrl).gate("),
        ("    cur = [0] * N\n", "    cur = [0] * N\n    dsh = [0.0] * N\n"),
        ("                if t >= warmup:\n                    nopt[opt] += 1\n",
         "                dsh[s] += o['dsa'] * ((opt != 0) - dsh[s])\n"
         "                if t >= warmup:\n                    nopt[opt] += 1\n"),
        # the portfolio
        ("def csim(spec,", "def ptsim(spec,"),
        (_HOOK_OLD,
         "    for t in range(cycles):\n"
         "        _m = _PF['L'].step(t, [_s for _s in range(N) if _s * 10 + 8 in occ])\n"
         "        if _m is not None:\n"
         "            ctrl, ctrl2, ctrl3, o['dth'] = _PF['ctrls'][_m]\n"
         "        if ctrl is not None:\n            ctrl.tick(t, occ)\n"),
        ("            pk = occ.pop(c)\n            if t >= warmup:\n                lat.append",
         "            pk = occ.pop(c)\n            _PF['L'].n += 1\n            if t >= warmup:\n"
         "                lat.append"),
    ]
    for old, new in patches:
        assert src.count(old) == 1, old
        src = src.replace(old, new)
    ns = dict(vars(XC))
    ns['_PF'] = {}
    _PTSIM = (_exec(src, ns, 'ptsim'), ns)
    return _PTSIM


def pt_spec(mode):
    base, thr, thr2, thr3, dth = mode
    return f'{base}:thr={thr}:thr2={thr2}:thr3={thr3}:dth={dth}'


def pt_run(spec, rate, pattern, seed, chain, cycles):
    toks = spec.split(':')
    modes = TSETS[toks[0]]
    lo = lparse(toks[1:])
    fn, ns = ptsim_fn()
    warmup = cycles // 4
    L = Learner(len(modes), seed, warmup, **lo)
    oc, nb = XR.torus_info()
    ctrls = []
    for _, thr, thr2, thr3, dth in modes:
        cs = []
        for sp in (thr, thr2, thr3):
            if sp == '-':
                cs.append(None)
            else:
                c = XR.Ctrl(sp, oc, nb, seed)
                c.warmup = warmup
                cs.append(c)
        ctrls.append((cs[0], cs[1], cs[2], dth))
    ns['_PF'].update(L=L, ctrls=ctrls)
    r = fn(pt_spec(modes[L.cur]), rate, pattern, seed=seed, chain=chain, cycles=cycles,
           warmup=warmup)
    tot = max(1, sum(L.time))
    return [r[0], r[1], r[2], r[3], L.switches] + [x / tot for x in L.time]


def run_one(spec, rate, pattern, seed, chain='seq', cycles=2000):
    kind, _, sp = spec.partition(':')
    if kind == 'PM':
        return pm_run(sp, rate, pattern, seed, chain, cycles)
    if kind == 'PT':
        return pt_run(sp, rate, pattern, seed, chain, cycles)
    return list(X2.run_one(spec, rate, pattern, seed, chain, cycles))


def check():
    """A one-mode portfolio is the scheme itself; the learner's bookkeeping on a short run."""
    for ch in ('seq', 'none'):
        a = X2.msim(MESH_B, 0.6, 'transpose', seed=3, chain=ch, cycles=900)
        b = pm_run('m1', 0.6, 'transpose', 3, ch, 900)
        print('mesh m1', ch, a[:2], b[:2], tuple(a[:2]) == tuple(b[:2]))
        a = X2.run_one('A:R:dualXY:random/random', 0.3, 'bitcomp', 3, ch, 900)
        b = X2.msim('route=wf:tiers=xy+esc:thr=g0', 0.3, 'bitcomp', seed=3, chain=ch, cycles=900)
        print('dualXY = wf xy+esc g0', ch, a[:2], b[:2], tuple(a[:2]) == tuple(b[:2]))
        a = X2.run_one('A:R:westFirstMesh:random/random', 0.5, 'transpose', 3, ch, 900)
        b = X2.msim('route=wf:tiers=all+esc:thr=g0', 0.5, 'transpose', seed=3, chain=ch,
                    cycles=900)
        print('westFirst random = wf all+esc g0', ch, a[:2], b[:2], tuple(a[:2]) == tuple(b[:2]))
        a = X2.msim('sel=price', 0.5, 'hotspot', seed=3, chain=ch, cycles=900)
        b = X2.msim('route=wf:tiers=pref+esc+vc1:sel=price', 0.5, 'hotspot', seed=3, chain=ch,
                    cycles=900)
        print('duato ptier = wf ptier', ch, a[:2], b[:2], tuple(a[:2]) == tuple(b[:2]))
        sp = pt_spec(TSETS['t1'][0])
        a = X2.tcsim()(sp, 0.8, 'hotspot', seed=5, chain=ch, cycles=800)
        b = pt_run('t1', 0.8, 'hotspot', 5, ch, 800)
        print('torus t1', ch, a[:2], b[:2], tuple(a[:2]) == tuple(b[:2]))
    print('PM:m4', pm_run('m4', 0.6, 'transpose', 3, 'seq', 3000))
    print('PT:t3', pt_run('t3', 0.8, 'hotspot', 3, 'seq', 2400))


# ------------------------------------------------------------------ driver
CACHE = os.environ.get('XP_PF_CACHE', os.path.join(tempfile.gettempdir(), 'xp_portfolio.json'))


def _job(a):
    return a, run_one(*a)


def load(path=None):
    try:
        with open(path or CACHE) as f:
            return {tuple(json.loads(kk)): v for kk, v in json.load(f).items()}
    except (OSError, ValueError):
        return {}


def save(new):
    res = load()
    res.update(new)
    tmp = CACHE + f'.tmp{os.getpid()}'
    with open(tmp, 'w') as f:
        json.dump({json.dumps(list(kk)): v for kk, v in res.items()}, f)
    os.replace(tmp, CACHE)


def cost(j):
    sp = j[0]
    return (sp.startswith('PT') or sp.startswith('T') or 'price' in sp or sp.startswith('PM'),
            j[5])


def compute(jobs):
    from multiprocessing import Pool
    res = load()
    todo = [j for j in dict.fromkeys(jobs) if j not in res]
    if todo:
        todo.sort(key=cost, reverse=True)       # longest first
        with Pool(int(os.environ.get('XP_PF_PROCS', 3))) as pool:
            new = {}
            for i, (a, r) in enumerate(pool.imap_unordered(_job, todo, chunksize=1)):
                new[a] = list(r)
                if i % 10 == 9:
                    save(new)
                    new = {}
                    print(f'{i + 1}/{len(todo)}', file=sys.stderr, flush=True)
        save(new)
    return load()


def jobs_of(spec, pats, rates, seeds, chains, cycles):
    return [(sp, float(r), p, sd, ch, int(cycles)) for ch in chains.split(',')
            for sp in spec.split(',') for p in X2.pats_of(pats) for r in rates.split(',')
            for sd in X2.seedlist(seeds)]


def report(argv):
    """report MAIN OTHERS RATES SEEDS CHAINS CYCLES [PATS] [REFCACHE REFCYC [REFSEEDS [REFRATES]]]:
    MAIN (a portfolio)
    against each of OTHERS, from this cache; '@' before a spec in OTHERS takes it from REFCACHE
    at REFCYC cycles (the published 2000 / 1600-cycle tables), '~' marks a reference not in the
    best.  Per pattern the rates used are those every spec was run at (peak over them)."""
    main, others, rates, seeds, chains, cycles = argv[:6]
    cycles = int(cycles)
    pats = X2.pats_of(argv[6]) if len(argv) > 6 else X2.MPATS
    ref = load(argv[7]) if len(argv) > 7 else {}
    refcyc = int(argv[8]) if len(argv) > 8 else cycles
    rates = [float(x) for x in rates.split(',')]
    seeds = X2.seedlist(seeds)
    refseeds = X2.seedlist(argv[9]) if len(argv) > 9 else seeds
    refrates = [float(x) for x in argv[10].split(',')] if len(argv) > 10 else rates
    res = load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-9, (a[1] ** 2 + b[1] ** 2) ** .5)

    def cellx(sp, p, ch):
        isr = sp.startswith('@')
        src, cyc = (ref, refcyc) if isr else (res, cycles)
        s = sp.lstrip('@')
        best = None
        for r in (refrates if isr else rates):
            v = [src.get((s, r, p, sd, ch, cyc)) for sd in (refseeds if isr else seeds)]
            v = [x for x in v if x is not None]
            if len(v) < 2:
                continue
            m, se = XP.stats([x[0] for x in v])
            if best is None or m > best[0]:
                best = (m, se, r, len(v), v)
        return best

    out = []
    for ch in chains.split(','):
        names = [main] + [o.lstrip('~') for o in others.split(',')]
        isref = {o.lstrip('~'): o.startswith('~') for o in others.split(',')}
        tab = {sp: [cellx(sp, p, ch) for p in pats] for sp in names}
        print(f'\n== chain={ch}, {cycles} cycles (@: {refcyc}), peak over offered {rates}: '
              'mean ± se (x1e-4) @rate [seeds]')
        print(f'{"":<44}' + ''.join(f'{p[:9]:>22}' for p in pats))
        for sp in names:
            print(f'{sp[:44]:<44}' + ''.join(
                f'{c[0]:>9.4f}±{c[1] * 1e4:<3.0f}@{c[2]:<4g}[{c[3]}]' if c else f'{"-":>22}'
                for c in tab[sp]))
        m = tab[main]
        if main.startswith('P'):
            print(f'{"MAIN mode share at peak (switches)":<44}' + ''.join(
                f'{"/".join(f"{100 * sum(x[5 + i] for x in c[4]) / len(c[4]):.0f}" for i in range(len(c[4][0]) - 5)) + " (" + str(round(sum(x[4] for x in c[4]) / len(c[4]))) + ")":>22}'
                if c else f'{"-":>22}' for c in m))
        oth = [s for s in names[1:] if not isref[s]]
        bestrow = []
        for i in range(len(pats)):
            cand = [s for s in oth if tab[s][i]]
            bestrow.append(max(cand, key=lambda s: tab[s][i][0]) if cand else None)
        print(f'{"best of the others":<44}' + ''.join(
            f'{tab[b][i][0]:>22.4f}' if b else f'{"-":>22}' for i, b in enumerate(bestrow)))
        print(f'{"  by":<44}' + ''.join(f'{(b or "-")[-21:]:>22}' for b in bestrow))
        print(f'{"MAIN vs best: %, z":<44}' + ''.join(
            f'{100 * (m[i][0] / tab[b][i][0] - 1):>+14.2f}%{z(m[i], tab[b][i]):>+6.1f}z'
            if b and m[i] else f'{"-":>22}' for i, b in enumerate(bestrow)))
        for r in names[1:]:
            print(f'{"vs " + r[:41]:<44}' + ''.join(
                f'{100 * (m[i][0] / tab[r][i][0] - 1):>+14.2f}%{z(m[i], tab[r][i]):>+6.1f}z'
                if m[i] and tab[r][i] else f'{"-":>22}' for i in range(len(pats))))
        out.append(tab)
    return out


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check()
    elif sys.argv[1] == 'run':
        compute(jobs_of(*sys.argv[2:8]))
    elif sys.argv[1] == 'jobs':
        jobs = []
        with open(sys.argv[2]) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    jobs += jobs_of(*line.split('|'))
        print(len(jobs), 'jobs', file=sys.stderr)
        compute(jobs)
    elif sys.argv[1] == 'report':
        report(sys.argv[2:])
