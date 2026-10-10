#!/usr/bin/env python3
"""One mesh scheme against every mesh scheme, in both move models of `xp_arbiter.py`, and a
configuration-driven throttle for the torus combined scheme of `xp_combo.py` (simulation only;
nothing here is proved).

MESH (8 x 8, 2 one-packet VC lanes per link, random arbitration).  `msim` is
`xp_backpressure.mesh_sim` (= `routing_sim.simulate(duatoMesh, 'T4:tiered')`) generalised; spec
`M:<key=value:...>`:
  route=duato|wf            permitted hops: Duato's mesh (XY escape on VC0, any productive hop
                            on VC1) or the west-first mesh (also the west-first VC0 hops)
  tiers=pref+esc+vc1        the tier list (the free hops of the first tier that has one):
                              pref  the tieredMesh preferred hop (XY on VC0 / YX on VC1; from a
                                    source either)
                              esc   the XY hop on VC0 (the escape hop)
                              xy    the XY hop on either VC        xy1  the XY hop on VC1
                              yx1   the YX hop on VC1             vc1  any productive VC1 hop
                              wf0   the extra west-first VC0 hops  all  every permitted hop
                              str   straight on (same direction as the current channel, either
                                    VC; from a source every hop)
  stiers=<list>             the tier list for packets in an injection channel (default: tiers)
  sel=rand|P|D|price        choice within the tier: random; the hop into the router with the most
                            free hops this packet may take next (P); the most free outgoing
                            channels (D); the cheapest link price + propagated minimal-route
                            cost (xp_prices `ptier`; eps, a)
  dev=<delta>               in the first tier: leave it for a free hop of `devset` (default vc1)
                            whose P-score is at least delta higher (xp_backpressure `X<delta>`)
  gdev=<delta>              before the tiers: a free hop of devset (not in the first tier) whose
                            P-score is at least delta above the best P-score of the first tier's
                            permitted hops, free or not (a configuration-dependent first tier)
  thr=g<n>|<xp_ramp spec>   source throttle: n of the next router's 8 outgoing channels free, or
                            an xp_ramp controller (fix<g>, lx.., alg.., ...)
  sx=<tiers>                tiers whose source hops are exempt from the throttle (e.g. sx=xy; lists are '+'-separated)
Every such selection reads only the configuration (except sel=price, which reads smoothed
flows, i.e. history), and contains the throttled escape tier when `esc` is in the list with a
fixed g; `duatoTiers_correct` / `westFirstTiers_correct` then cover it.  A configuration-only
xp_ramp controller is a configuration-dependent threshold in front of the escape tier (an
earlier tier admitting a source hop only under the controller's condition, then `escTier k 8`).

Baselines (published): `A:R:dualXY:random`, `A:R:westFirstMesh:random`, `A:R:duatoMesh:o1turn`,
`A:R:duatoMesh:random`, `A:R:duatoMesh:T4_random` (xp_arbiter.run_one, chain-patched).  Our own:
tieredMesh `M:` (default spec), ptier `M:sel=price`, X2 `M:sel=P:dev=2:thr=g3`, throttles
`M:thr=<ctrl>`.  Patterns: the six of routing_sim plus tornado (x -> x + k/2 - 1 mod k) and the
random permutation of routing_graph_sim.

TORUS: `T:<xp_combo spec>` runs xp_combo.csim patched with `thr3=<xp_ramp spec>`: the throttle
of a source whose current (toll-chosen) option is a detour; with `dth=<x>` instead: of a source
whose smoothed share of detoured packets (EMA factor dsa=0.02) is at least x.

Usage:
  python3 scripts/xp_combo2.py check
  python3 scripts/xp_combo2.py run SPECS PATTERNS RATES SEEDS CHAINS [CYCLES]
  python3 scripts/xp_combo2.py report MAIN OTHERS RATES SEEDS CHAINS [CYCLES]
Cache: XP_COMBO2_CACHE (default xp_combo2_cache.json in the system temporary directory);
XP_COMBO2_PROCS processes (default 3).
"""
import inspect
import json
import os
import random
import sys
import tempfile
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np

import routing_sim as R
import routing_graph_sim as G
import xp_backpressure as XP
import xp_arbiter as XA
import xp_ramp as XR

GHOST = XA.GHOST
MPATS = ['uniform', 'transpose', 'shuffle', 'bitrev', 'hotspot', 'bitcomp', 'tornado',
         'randperm']


def mdest(pattern, s, k, rnd):
    if pattern == 'tornado':
        return (s % k + k // 2 - 1) % k + s // k * k
    if pattern == 'randperm':
        return G.RANDPERM[s]
    return R.destination(pattern, s, k, rnd)


# every mesh simulator used here draws destinations through mdest
XP.destination = mdest
XA.mesh_sim.__globals__['destination'] = mdest
XA.simulate.__globals__['destination'] = mdest
XR.MESH_SIM.__globals__['destination'] = mdest

# ------------------------------------------------------------------ mesh tables
_T = {}


def tables(k, route):
    key = (k, route)
    if key in _T:
        return _T[key]
    ch, head, routes = R.mesh(k)
    n = k * k
    hd = [head(c) for c in range(n * 10)]
    xy = lambda u, d: 0 if u % k < d % k else 1 if d % k < u % k else 2 if u // k < d // k else 3
    yx = lambda u, d: 2 if u // k < d // k else 3 if d // k < u // k else xy(u, d)
    rt = routes['duatoMesh' if route == 'duato' else 'westFirstMesh']
    RT = [[rt(ch(u, 4, 0), d) if u != d else [] for d in range(n)] for u in range(n)]
    XY0 = [[ch(u, xy(u, d), 0) if u != d else -1 for d in range(n)] for u in range(n)]
    XY1 = [[ch(u, xy(u, d), 1) if u != d else -1 for d in range(n)] for u in range(n)]
    YX1 = [[ch(u, yx(u, d), 1) if u != d else -1 for d in range(n)] for u in range(n)]
    _T[key] = (ch, hd, RT, XY0, XY1, YX1)
    return _T[key]


MDEF = dict(route='duato', tiers='pref+esc+vc1', stiers='', sel='rand', dev=-1.0, gdev=-1.0, devset='vc1',
            thr='g4', sx='', eps=4.0, a=0.02)
MSTR = ('route', 'tiers', 'stiers', 'sel', 'devset', 'thr', 'sx')


def mparse(spec):
    o = dict(MDEF)
    for tok in spec.split(':'):
        if tok:
            kk, v = tok.split('=')
            o[kk] = v if kk in MSTR else float(v)
    return o


def msim(spec, rate, pattern, seed=1, chain='seq', cycles=2000, warmup=None, k=8):
    o = mparse(spec)
    warmup = cycles // 3 if warmup is None else warmup
    ch, hd, RT, XY0, XY1, YX1 = tables(k, o['route'])
    rnd = random.Random(seed)
    n = k * k
    occ = {}
    queues = [deque() for _ in range(n)]
    latencies = []
    nfree = [8] * n
    tiers_n = o['tiers'].split('+')
    stiers_n = o['stiers'].split('+') if o['stiers'] else tiers_n
    sx = set(o['sx'].split('+')) if o['sx'] else set()
    sel = o['sel']
    delta = o['dev']
    gdev = o['gdev']
    devset = o['devset']
    none = chain == 'none'
    thr = o['thr']
    ctrl = None
    gfix = None
    if thr.startswith('g'):
        gfix = int(thr[1:])
    else:
        oc, nb = XR.mesh_info()
        ctrl = XR.Ctrl(thr, oc, nb, seed)
        ctrl.warmup = warmup
    useprice = sel == 'price'
    if useprice:
        eps, a = o['eps'], o['a']
        adjm = [[u + 1 if u % k < k - 1 else -1, u - 1 if u % k > 0 else -1,
                 u + k if u // k < k - 1 else -1, u - k if u // k > 0 else -1] for u in range(n)]
        A = np.array(adjm)
        nbr = np.where(A >= 0, A, 0)
        dm = np.array([[abs(u % k - v % k) + abs(u // k - v // k) for v in range(n)]
                       for u in range(n)])
        prodinf = np.full((n, 4, n), np.inf)
        for u in range(n):
            for p in range(4):
                if adjm[u][p] >= 0:
                    prodinf[u, p][dm[adjm[u][p]] == dm[u] - 1] = 0.0
        eye = np.eye(n, dtype=bool)
        flow = np.zeros((n, 4))
        mvs = np.zeros((n, 4))
        C = dm.astype(float)
        Cl = C.tolist()
        Pl = np.ones((n, 4)).tolist()
    moves = chained = 0

    def useful(q, d):
        v = hd[q]
        if v == d:
            return 99
        return sum(1 for x in RT[v][d] if x not in occ)

    def put(c, pk):
        occ[c] = pk
        if c // 2 % 5 != 4:
            nfree[c // 10] -= 1

    def take(c):
        if c // 2 % 5 != 4:
            nfree[c // 10] += 1
        return occ.pop(c)

    def tier_fn(name, u, d, c, src):
        esc = XY0[u][d]
        if name == 'pref':
            pref = esc if c % 2 == 0 and not src else YX1[u][d]
            return lambda q: q == pref or (src and q == esc)
        if name == 'esc':
            return lambda q: q == esc
        if name == 'vc1':
            return lambda q: q % 2 == 1
        if name == 'xy':
            x1 = XY1[u][d]
            return lambda q: q == esc or q == x1
        if name == 'xy1':
            x1 = XY1[u][d]
            return lambda q: q == x1
        if name == 'yx1':
            y1 = YX1[u][d]
            return lambda q: q == y1
        if name == 'wf0':
            return lambda q: q % 2 == 0 and q != esc
        if name == 'all':
            return lambda q: True
        if name == 'str':
            # straight on: a hop in the direction of the current channel (either VC); from a
            # source, any hop (the first hop chooses the dimension order)
            if src:
                return lambda q: True
            dr = c // 2 % 5
            return lambda q: q // 2 % 5 == dr
        raise ValueError(name)

    nfree_of = lambda x: nfree[hd[x]]
    for t in range(cycles):
        if ctrl is not None:
            ctrl.tick(t, occ)
        if useprice:
            price = np.exp(eps * flow)
            C = np.min(prodinf + price[:, :, None] + C[nbr], axis=1)
            C[eye] = 0.0
            Cl = C.tolist()
            Pl = price.tolist()
        for c in [c for c, v in occ.items() if v is not GHOST and hd[c] == v[0]]:
            _, born = take(c)
            if t >= warmup:
                latencies.append(t - born)
        moved = set()
        vacated = set()
        packets = list(occ)
        rnd.shuffle(packets)
        for c in packets:
            if c in moved or c not in occ:
                continue
            pk = occ[c]
            if pk is GHOST:
                continue
            d = pk[0]
            u = hd[c]
            if u == d:
                continue
            hops = RT[u][d]
            free = [c2 for c2 in hops if c2 not in occ]
            src = c // 2 % 5 == 4
            names = stiers_n if src else tiers_n
            if src:
                if sx:
                    exempt = [q for q in free if any(tier_fn(nm, u, d, c, src)(q) for nm in sx)]
                else:
                    exempt = []
                if gfix is not None:
                    free = [c2 for c2 in free if nfree[hd[c2]] >= gfix]
                else:
                    free = ctrl.gate(u, free, nfree_of)
                if exempt:
                    free = free + [q for q in exempt if q not in free]
            pick = []
            if gdev >= 0:
                # leave the first tier, whether or not it has a free hop, for a free hop of
                # devset whose P-score beats the best of the first tier's permitted hops
                t0 = tier_fn(names[0], u, d, c, src)
                sc0 = [useful(q, d) for q in hops if t0(q)]
                if sc0:
                    dv = tier_fn(devset, u, d, c, src)
                    b0 = max(sc0) + gdev
                    pick = [q for q in free if dv(q) and not t0(q) and useful(q, d) >= b0]
            for ti, nm in enumerate(names if not pick else ()):
                tier = tier_fn(nm, u, d, c, src)
                if any(tier(q) for q in free):
                    if delta >= 0 and ti == 0:
                        best = max(useful(q, d) for q in free if tier(q))
                        dv = tier_fn(devset, u, d, c, src)
                        alt = [q for q in free if dv(q) and useful(q, d) >= best + delta]
                        if alt:
                            pick = alt
                            break
                    pick = [q for q in free if tier(q)]
                    break
            if len(pick) > 1 and sel != 'rand':
                if sel == 'price':
                    sc = [Pl[u][q // 2 % 5] + Cl[hd[q]][d] for q in pick]
                    mn = min(sc)
                    pick = [q for q, y in zip(pick, sc) if y <= mn * 1.0000001]
                else:
                    score = (lambda q: nfree[hd[q]]) if sel == 'D' else (lambda q: useful(q, d))
                    top = max(score(q) for q in pick)
                    pick = [q for q in pick if score(q) == top]
            if pick:
                c2 = rnd.choice(pick)
                put(c2, take(c))
                if none:
                    put(c, GHOST)
                moved.add(c2)
                if t >= warmup:
                    moves += 1
                    chained += c2 in vacated
                vacated.add(c)
                if useprice:
                    pp = c2 // 2 % 5
                    if pp < 4:
                        mvs[c2 // 10, pp] += 1
        if none:
            for c in vacated:
                if occ.get(c) is GHOST:
                    take(c)
        if useprice:
            flow += a * (mvs - flow)
            mvs[:] = 0
        for s in range(n):
            if rnd.random() < rate:
                d = mdest(pattern, s, k, rnd)
                if d != s:
                    queues[s].append((d, t))
            if queues[s] and ch(s, 4, 0) not in occ:
                put(ch(s, 4, 0), queues[s].popleft())
    throughput = len(latencies) / ((cycles - warmup) * n)
    latency = sum(latencies) / len(latencies) if latencies else float('nan')
    return throughput, latency, moves / (cycles - warmup), chained / max(1, moves)


# ------------------------------------------------------------------ torus: xp_combo patched
_tcsim = None


def tcsim():
    """xp_combo.csim with `thr3` (throttle of a source whose current option is a detour) and
    `tsel` (how a source picks among thr / thr2 / thr3)."""
    global _tcsim
    if _tcsim is not None:
        return _tcsim
    import xp_combo as XC
    XC.DEF.setdefault('thr3', '-')
    XC.DEF.setdefault('tsel', 'k')
    XC.DEF.setdefault('dth', -1.0)
    XC.DEF.setdefault('dsa', 0.02)
    XC.STR = XC.STR + ('thr3', 'tsel')
    src = inspect.getsource(XC.csim)
    patches = [
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
    ]
    for old, new in patches:
        assert src.count(old) == 1, old
        src = src.replace(old, new)
    ns = dict(vars(XC))
    exec(compile(src, '<xp_combo2 csim>', 'exec'), ns)
    _tcsim = ns['csim']
    return _tcsim


# ------------------------------------------------------------------ driver
def run_one(spec, rate, pattern, seed, chain='seq', cycles=2000):
    kind, _, sp = spec.partition(':')
    if kind == 'M':
        return list(msim(sp, rate, pattern, seed=seed, chain=chain, cycles=cycles))
    if kind == 'A':
        r = XA.run_one('mesh', sp, rate, pattern, seed, chain, cycles)
        return list(r)
    if kind == 'T':
        r = tcsim()(sp, rate, pattern, seed=seed, chain=chain, cycles=cycles)
        return list(r)
    if kind == 'TC':                      # an unpatched xp_combo spec (C:, A:, R:, PR:, TL:)
        import xp_combo as XC
        return list(XC.run_one(sp, rate, pattern, seed, chain, cycles))
    raise ValueError(spec)


def check():
    import xp_prices as XPR
    a = XP.mesh_sim(8, 0.45, 'transpose', cycles=900, warmup=300, seed=3)
    b = msim('', 0.45, 'transpose', seed=3, cycles=900, warmup=300)
    print('tiered seq', a[:2], b[:2], a[:2] == b[:2])
    a = XP.mesh_sim(8, 0.45, 'uniform', 'X2', 'random', 'g3', cycles=900, warmup=300, seed=3)
    b = msim('sel=P:dev=2:thr=g3', 0.45, 'uniform', seed=3, cycles=900, warmup=300)
    print('X2 seq', a[:2], b[:2], a[:2] == b[:2])
    a = XA.mesh_sim(8, 0.6, 'bitcomp', 'tiered', 'random', 'g4', seed=4, chain='none',
                    cycles=900, warmup=300)
    b = msim('', 0.6, 'bitcomp', seed=4, chain='none', cycles=900, warmup=300)
    print('tiered none', a[:2], b[:2], a[:2] == b[:2])
    a = XPR.sim_mesh('mode=ptier', 0.5, 'shuffle', cycles=900, warmup=300, seed=2)
    b = msim('sel=price', 0.5, 'shuffle', seed=2, cycles=900, warmup=300)
    print('ptier seq', a[:2], b[:2], a[:2] == b[:2])
    a = XR.run_one('mesh', 'alg50_50_1', 'uniform', 0.6, 3, cycles=900, warmup=300)
    b = msim('thr=alg50_50_1', 0.6, 'uniform', seed=3, cycles=900, warmup=300)
    print('alg seq', (a['thr'], a['lat']), b[:2], (a['thr'], a['lat']) == b[:2])
    a = XA.run_one('mesh', 'R:dualXY:random', 0.3, 'tornado', 3, 'seq', 900)
    print('dualXY tornado', a)
    import xp_combo as XC
    a = XC.csim('hop=price:src=toll:pm=0.2:thr=lx2_4_32_2:thr2=lx2_4_35_2', 0.8, 'tornado',
                seed=5, cycles=600)
    b = tcsim()('hop=price:src=toll:pm=0.2:thr=lx2_4_32_2:thr2=lx2_4_35_2', 0.8, 'tornado',
                seed=5, cycles=600)
    print('torus combo', a, b, a == b)


CACHE = os.environ.get('XP_COMBO2_CACHE',
                       os.path.join(tempfile.gettempdir(), 'xp_combo2_cache.json'))


def _job(a):
    return a, run_one(*a)


def load():
    try:
        with open(CACHE) as f:
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


def compute(jobs):
    from multiprocessing import Pool
    res = load()
    todo = [j for j in jobs if j not in res]
    if todo:
        todo.sort(key=lambda j: (not j[0].startswith('T'), 'price' not in j[0], j[0]))
        with Pool(int(os.environ.get('XP_COMBO2_PROCS', 3))) as pool:
            new = {}
            for i, (a, r) in enumerate(pool.imap_unordered(_job, todo, chunksize=1)):
                new[a] = list(r)
                if i % 20 == 19:
                    save(new)
                    new = {}
        save(new)
    return load()


def cell(res, spec, pattern, rates, seeds, chain, cycles, minseeds=2):
    best = None
    for r in rates:
        v = [res.get((spec, r, pattern, s, chain, cycles)) for s in seeds]
        v = [x for x in v if x is not None]
        if len(v) < minseeds:
            continue
        m, se = XP.stats([x[0] for x in v])
        if best is None or m > best[0]:
            best = (m, se, r, len(v))
    return best


def seedlist(s):
    if '-' in s:
        a, b = s.split('-')
        return list(range(int(a), int(b) + 1))
    return [int(x) for x in s.split(',')]


def pats_of(p):
    if p == 'all':
        return MPATS
    if p == 'tall':
        return XA.TPATS
    return p.split(',')


def run_cmd(argv):
    specs, pats, rates, seeds, chains = argv[:5]
    cycles = int(argv[5]) if len(argv) > 5 else 2000
    specs, chains, pats = specs.split(','), chains.split(','), pats_of(pats)
    rates = [float(x) for x in rates.split(',')]
    seeds = seedlist(seeds)
    jobs = [(sp, r, p, sd, ch, cycles) for ch in chains for sp in specs for p in pats
            for r in rates for sd in seeds]
    res = compute(jobs)
    print(f'seeds {seeds}, rates {rates}, cycles {cycles}: peak mean ± se (x1e-4) @rate')
    for ch in chains:
        print(f'{ch:<5}{"":<44}' + ''.join(f'{p[:9]:>16}' for p in pats))
        for sp in specs:
            cells = []
            for p in pats:
                m, se, r, _ = cell(res, sp, p, rates, seeds, ch, cycles, min(2, len(seeds)))
                cells.append(f'{m:.4f}±{se * 1e4:<3.0f}@{r:g}')
            print(f'{ch:<5}{sp[:44]:<44}' + ''.join(f'{x:>16}' for x in cells), flush=True)


def report(argv):
    """report MAIN OTHERS RATES SEEDS CHAINS [CYCLES] [PATS]: MAIN against each of OTHERS ('~'
    prefix: reference, compared but not in the best)."""
    main, others, rates, seeds, chains = argv[:5]
    cycles = int(argv[5]) if len(argv) > 5 else 2000
    pats = pats_of(argv[6]) if len(argv) > 6 else MPATS
    others = others.split(',')
    refs = [x[1:] for x in others if x.startswith('~')]
    others = [x for x in others if not x.startswith('~')]
    rates = [float(x) for x in rates.split(',')]
    seeds = seedlist(seeds)
    res = load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-9, (a[1] ** 2 + b[1] ** 2) ** .5)
    for ch in chains.split(','):
        tab = {}
        for sp in [main] + others + refs:
            row = [cell(res, sp, p, rates, seeds, ch, cycles) for p in pats]
            if all(x is not None for x in row):
                tab[sp] = row
        print(f'\n== chain={ch}, {cycles} cycles, peak over offered {rates}: mean ± se (x1e-4) '
              '[seeds]')
        print(f'{"":<40}' + ''.join(f'{p[:9]:>16}' for p in pats))
        for sp, row in tab.items():
            name = ('~' if sp in refs else '') + sp
            print(f'{name[:40]:<40}' + ''.join(f'{c[0]:>9.4f}±{c[1] * 1e4:<3.0f}[{c[3]}]'
                                                for c in row))
        if main not in tab:
            continue
        oth = [s for s in others if s in tab]
        if oth:
            best = [max(oth, key=lambda s: tab[s][i][0]) for i in range(len(pats))]
            print(f'{"best of the others":<40}' + ''.join(f'{tab[b][i][0]:>16.4f}'
                                                         for i, b in enumerate(best)))
            print(f'{"  by":<40}' + ''.join(f'{b[-15:]:>16}' for b in best))
            print(f'{"MAIN vs best: %, z":<40}' + ''.join(
                f'{100 * (tab[main][i][0] / tab[b][i][0] - 1):>+9.2f}%{z(tab[main][i], tab[b][i]):>+5.1f}z'
                for i, b in enumerate(best)))
        for r in oth + refs:
            print(f'{"vs " + r[:37]:<40}' + ''.join(
                f'{100 * (tab[main][i][0] / tab[r][i][0] - 1):>+9.2f}%{z(tab[main][i], tab[r][i]):>+5.1f}z'
                for i in range(len(pats))))


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check()
    elif sys.argv[1] == 'run':
        run_cmd(sys.argv[2:])
    elif sys.argv[1] == 'report':
        report(sys.argv[2:])
