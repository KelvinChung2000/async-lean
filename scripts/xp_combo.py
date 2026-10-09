#!/usr/bin/env python3
"""One torus scheme combining price-chosen adaptive hops, restricted toll-chosen source
detours and (optionally) the escape-share throttle, compared with every other scheme in both
move models of `xp_arbiter.py` (simulation only; nothing here is proved).

Components of a combination (`C:<spec>`, colon-separated key=value tokens):
  hop=rand|price|P|priceP   choice among the free minimal VC1 hops: random (`min`); cheapest
                            link price + propagated cheapest-minimal-route cost (`H` of
                            xp_prices: price = exp(eps * smoothed flow), one Bellman-Ford step
                            per cycle); the most free usable hops at the next router (`P` of
                            xp_backpressure); price, ties broken by P
  eps=4 a=0.02              price exponent and flow smoothing
  src=none|toll|price       source detours: none; toll = the bandit options (minimal, long way
                            in x / y, random intermediate) ranked by the M/M/1 marginal cost
                            L^2 / h^(r/10) of their learned latency (xp_tolls); price = the
                            cheapest of the same options under the price table (xp_prices)
  e=2 f=5 r=10 k=1          toll: exploration %, long-way flow gate f/10 (long-direction flow
                            out of the source at most f/10 of the minimal direction's), toll
                            exponent, random intermediate only for concentrated sources
  sx=10 sl=0.5              toll: estimated-dual filter (xp_tolls `slex`): a link costs 1 while
                            it carries >= sx/10 packets/cycle; a detour is offered only when its
                            smoothed path sum is <= the minimal option's + sl.  sx=0: no filter
  pm=-1                     price filter: a detour is offered only when its price-table cost is
                            below (1 - pm) x the minimal route's (pm < 0: no filter); pl / pv
                            override it for the long way / the random intermediate
  vg=-1                     random intermediate only when its first hops carry <= vg/10 of the
                            minimal first hops' flow (vg < 0: no gate)
  nv=1                      the random intermediate: the cheapest (price table) of nv samples
  va=0                      1: the random intermediate only when a long-way option passed its gate
  xe=0                      1: explore only among options that passed every filter (always so)
  m=0.4 ch=softm beta=10    src=price: margin, choice (min | softm) as xp_prices
  thr=g4|<xp_ramp spec>     source throttle: g = 4, or an xp_ramp controller (e.g. lx2_4_36_2)
  thr2=-|<xp_ramp spec>     a second controller for sources whose last 8 destinations include
                            more than 2 nodes (spread-out traffic; the `k` signal)
The safety of every configuration choice is `Routing/GraphDetour.lean` (any intermediate at the
source, any choice among the free minimal hops, tree escape, bounded returns); prices, learned
latencies and estimated duals are history, outside the configuration-only selection theorems.

Baselines (same move models, random arbitration):
  A:<xp_arbiter torus spec>   dor, val/base, ugal/base, min/base, minC/base, min/P, bandit2m7f5k/base
  TL:<xp_tolls scheme>        xp_tolls.sim (m7, slex10m10, dlexm10, ...), patched for chain=none
  PR:<xp_prices spec>         xp_prices.sim_price (H, P), patched for chain=none
  R:<xp_ramp spec>            xp_ramp's hooked torus `min` with the controller, chain=none patched

Usage:
  python3 scripts/xp_combo.py check
  python3 scripts/xp_combo.py run SPECS PATTERNS RATES SEEDS CHAINS [CYCLES]
  python3 scripts/xp_combo.py report SPEC SPECS... (full tables vs the others, from the cache)
Cache: XP_COMBO_CACHE (default xp_combo_cache.json in the system temporary directory);
XP_COMBO_PROCS processes (default 3).
"""
import inspect
import json
import math
import os
import random
import sys
import tempfile
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np

import xp_arbiter as XA
import xp_backpressure as XP
import xp_prices as XPR
import xp_tolls as XT
import xp_ramp as XR
import torus_experiments as T

GHOST = XA.GHOST
K, N = T.K, T.N
NET = T.NET
NBR, PRODINF, EYE, DIST = XPR.NBR, XPR.PRODINF, XPR.EYE, XPR._dist


# ------------------------------------------------------------------ the combined simulator
DEF = dict(hop='price', eps=4.0, a=0.02, src='toll', e=2.0, f=5.0, r=10.0, k=1.0, sx=10.0,
           sl=0.5, pm=-1.0, pl=-9.0, pv=-9.0, vg=-1.0, va=0.0, nv=1.0, xe=0.0, m=0.4, ch='softm', beta=10.0, thr='g4',
           tol=0.0, thr2='-')
STR = ('hop', 'src', 'ch', 'thr', 'thr2')


def parse(spec):
    o = dict(DEF)
    for tok in spec.split(':'):
        if tok:
            k, v = tok.split('=')
            o[k] = v if k in STR else float(v)
    return o


def longway(s, d, dim):
    return XT.longway(s, d, dim)


def csim(spec, rate, pattern, seed=1, chain='seq', cycles=1600, warmup=None, g=4, budget=2):
    o = parse(spec)
    warmup = cycles // 4 if warmup is None else warmup
    net = NET
    head, esc, vc1, out, dist, adj = net.head, net.esc, net.vc1, net.out, net.dist, net.adj
    rnd = random.Random(seed)
    occ = {}
    queues = [deque() for _ in range(N)]
    lat = []
    hopsum = 0
    thr = [g * 2 * net.deg[v] / 8 for v in range(N)]
    hopm, srcm = o['hop'], o['src']
    eps, a = o['eps'], o['a']
    pl = o['pm'] if o['pl'] < -1 else o['pl']
    pv = o['pm'] if o['pv'] < -1 else o['pv']
    usepr = hopm in ('price', 'priceP') or srcm == 'price' or pl >= 0 or pv >= 0 or o['nv'] > 1
    flow = np.zeros((N, 4))
    moves = np.zeros((N, 4))
    C = DIST.astype(float)
    Cl = C.tolist()
    Pl = np.ones((N, 4)).tolist()
    Fl = flow.tolist()
    ctrl = ctrl2 = None
    if o['thr'] != 'g4':
        oc, nb = XR.torus_info()
        ctrl = XR.Ctrl(o['thr'], oc, nb, seed)
        ctrl.warmup = warmup
        if o['thr2'] != '-':           # the throttle of sources with spread-out destinations
            ctrl2 = XR.Ctrl(o['thr2'], oc, nb, seed)
            ctrl2.warmup = warmup
    spread = [False] * N
    # toll sources
    explore = o['e'] / 100
    fgate = o['f'] / 10
    mexp = o['r'] / 10
    sx = o['sx'] / 10
    slack = o['sl']
    est = [[0.0] * 4 for _ in range(N)]
    est2 = [[0.0] * 4 for _ in range(N)]
    toll = [0.0] * (N * 5)
    recent = [deque(maxlen=8) for _ in range(N)]
    cur = [0] * N
    nopt = [0] * 4
    none = chain == 'none'
    tol = 1.0 + 1e-7 + o['tol']

    def useful(x, d, tgt):
        v = head[x]
        if v == tgt:
            return 99
        return sum(1 for q in vc1[v][tgt] if q not in occ) + (esc[x][d] not in occ)

    for t in range(cycles):
        if ctrl is not None:
            ctrl.tick(t, occ)
        if ctrl2 is not None:
            ctrl2.tick(t, occ)
        if usepr:
            price = np.exp(eps * flow)
            C = np.min(PRODINF + price[:, :, None] + C[NBR], axis=1)
            C[EYE] = 0.0
            Cl = C.tolist()
            Pl = price.tolist()
        for c in [c for c, p in occ.items() if head[c] == p[0]]:
            pk = occ.pop(c)
            if t >= warmup:
                lat.append(t - pk[1])
                hopsum += pk[2]
            if srcm == 'toll':
                e0 = est[pk[9]][pk[7]]
                est[pk[9]][pk[7]] = 0.9 * e0 + 0.1 * (t - pk[8]) if e0 else float(t - pk[8])
                e1 = est2[pk[9]][pk[7]]
                est2[pk[9]][pk[7]] = 0.9 * e1 + 0.1 * pk[10] if e0 else float(pk[10])
        moved = set()
        pks = list(occ)
        rnd.shuffle(pks)
        for c in pks:
            if c in moved:
                continue
            pk = occ[c]
            d = pk[0]
            u = head[c]
            if u == d:
                continue
            src = c // 2 % 5 == 4
            if pk[6] >= 0 and u == pk[6]:
                pk[6] = -1
            tgt = pk[6] if pk[6] >= 0 else d
            e = esc[c][d]
            onesc = c % 2 == 0 and not src
            canret = not (onesc and pk[4] >= budget)
            tiers = [vc1[u][tgt], [e]] if canret else [[e]]
            q = None
            for tier in tiers:
                free = [x for x in tier if x not in occ]
                if src:
                    if ctrl is not None:
                        free = (ctrl2 if spread[u] else ctrl).gate(u, free, lambda x: sum(1 for oo in out[head[x]] if oo not in occ))
                    elif g:
                        free = [x for x in free if sum(1 for oo in out[head[x]] if oo not in occ) >= thr[head[x]]]
                if free:
                    if len(free) > 1:
                        if hopm in ('price', 'priceP') and free[0] % 2 == 1:
                            Pu = Pl[u]
                            sc = [Pu[(x >> 1) % 5] + Cl[head[x]][tgt] for x in free]
                            mn = min(sc)
                            free = [x for x, y in zip(free, sc) if y <= mn * tol]
                        if len(free) > 1 and hopm in ('P', 'priceP'):
                            sc = [useful(x, d, tgt) for x in free]
                            mx = max(sc)
                            free = [x for x, y in zip(free, sc) if y == mx]
                    q = rnd.choice(free)
                    break
            if q is None:
                continue
            if q % 2 == 0 and not (c % 2 == 0):
                pk[6] = -1
            pk[2] += 1
            if onesc and q % 2 == 1:
                pk[4] += 1
            pk[10] += toll[q // 2]
            occ[q] = occ.pop(c)
            moved.add(q)
            if none:
                occ[c] = GHOST
            pp = (q >> 1) % 5
            if pp < 4:
                moves[q // 10, pp] += 1
        if none:
            for x in [x for x, v in occ.items() if v is GHOST]:
                del occ[x]
        flow += a * (moves - flow)
        moves[:] = 0
        if srcm == 'toll':
            Fl = flow.tolist()
            if sx > 0:
                for uu in range(N):
                    fu = Fl[uu]
                    for p in range(4):
                        toll[uu * 5 + p] = 1.0 if fu[p] >= sx else 0.0
        for s in range(N):
            if rnd.random() < rate:
                dd = T.tdest(pattern, s, rnd)
                if dd != s:
                    queues[s].append((dd, t))
            c = s * 10 + 8
            if queues[s] and c not in occ:
                d, born = queues[s].popleft()
                inter = -1
                opt = 0
                if ctrl2 is not None:          # the last 8 destinations, as for `k`
                    if not (srcm == 'toll' and dist[s][d] > 1):
                        recent[s].append(d)
                    spread[s] = len(set(recent[s]) | {d}) > 2
                if srcm == 'toll' and dist[s][d] > 1:
                    Fs = Fl[s]
                    fmin = min(Fs[(c2 // 2) % 5] for c2 in vc1[s][d])
                    base = Cl[s][d]
                    opts = [(0, -1, dist[s][d])]
                    for dim in (0, 1):
                        lw = longway(s, d, dim)
                        if lw and Fs[lw[1]] <= fgate * fmin:
                            if pl < 0 or Cl[s][lw[0]] + Cl[lw[0]][d] < (1 - pl) * base:
                                opts.append((1 + dim, lw[0], lw[2]))
                    recent[s].append(d)
                    w = rnd.randrange(N)
                    for _ in range(int(o['nv']) - 1):      # the cheapest of nv samples
                        w2 = rnd.randrange(N)
                        if w2 not in (s, d) and (w in (s, d) or
                                                 Cl[s][w2] + Cl[w2][d] < Cl[s][w] + Cl[w][d]):
                            w = w2
                    if o['k'] and len(set(recent[s])) > 2:
                        w = s
                    if o['va'] and len(opts) == 1:
                        w = s
                    if w not in (s, d) and o['vg'] >= 0 and \
                            min(Fs[(c2 // 2) % 5] for c2 in vc1[s][w]) > o['vg'] / 10 * fmin:
                        w = s
                    if w not in (s, d) and pv >= 0 and \
                            not Cl[s][w] + Cl[w][d] < (1 - pv) * base:
                        w = s
                    if w not in (s, d):
                        opts.append((3, w, dist[s][w] + dist[w][d]))
                    if sx > 0:
                        b0 = est2[s][0]
                        opts = [x for x in opts if x[0] == 0 or est2[s][x[0]] <= b0 + slack]
                    price_o = lambda x: est[s][x[0]] ** 2 / x[2] ** mexp
                    if rnd.random() < explore:
                        opt, inter, _ = rnd.choice(opts)
                    else:
                        bo = min(opts, key=price_o)
                        co = [x for x in opts if x[0] == cur[s]]
                        if co and price_o(bo) >= price_o(co[0]):
                            bo = co[0]
                        cur[s] = bo[0]
                        opt, inter, _ = bo
                elif srcm == 'price' and dist[s][d] > 1:
                    base = Cl[s][d]
                    cand = [(1, longway(s, d, 0)), (2, longway(s, d, 1)), (3, None)]
                    opts = [(0, -1, base)]
                    for oi, lw in cand:
                        w = lw[0] if lw else (rnd.randrange(N) if oi == 3 else None)
                        if w is not None and w not in (s, d):
                            opts.append((oi, w, Cl[s][w] + Cl[w][d]))
                    ok = [x for x in opts[1:] if x[2] < (1 - o['m']) * base]
                    if ok:
                        if o['ch'] == 'softm':
                            w8 = [math.exp(-o['beta'] * (x[2] / base - 1.0)) for x in ok]
                            opt, inter, _ = rnd.choices(ok, weights=w8)[0]
                        else:
                            opt, inter, _ = min(ok, key=lambda x: x[2])
                if inter in (s, d):
                    inter = -1
                    opt = 0
                if t >= warmup:
                    nopt[opt] += 1
                occ[c] = [d, born, 0, dist[s][d], 0, 0, inter, opt, t, s, 0.0]
    tot = max(1, sum(nopt))
    return (len(lat) / ((cycles - warmup) * N), hopsum / max(1, len(lat)),
            (nopt[1] + nopt[2]) / tot, nopt[3] / tot)


# ------------------------------------------------------------------ baselines, chain-patched
def _patched(fn, patches, base_globals):
    src = inspect.getsource(fn)
    for old, new in patches:
        n = src.count(old)
        assert n == 1, (fn.__name__, old, n)
        src = src.replace(old, new)
    ns = dict(base_globals)
    ns.update(GHOST=GHOST)
    exec(compile(src, f'<xp_combo {fn.__name__}>', 'exec'), ns)
    return ns[fn.__name__]


_CLEAN = ('{i}if chain == "none":\n'
          '{i}    for _x in [_x for _x, _v in occ.items() if _v is GHOST]: del occ[_x]\n')

tolls_sim = _patched(XT.sim, [
    ('fgate=0.5, mexp=0.7):', 'fgate=0.5, mexp=0.7, chain="seq"):'),
    ('            occ[q] = occ.pop(c); moved.add(q)\n',
     '            occ[q] = occ.pop(c); moved.add(q)\n'
     '            if chain == "none": occ[c] = GHOST\n'),
    ('        for u in range(N):\n            for p in range(4):\n                flow[u][p] = 0.98',
     _CLEAN.format(i='        ') +
     '        for u in range(N):\n            for p in range(4):\n                flow[u][p] = 0.98'),
], vars(XT))

prices_sim = _patched(XPR.sim_price, [
    ('cycles=4000, warmup=1000, seed=1):', 'cycles=4000, warmup=1000, seed=1, chain="seq"):'),
    ('            occ[q] = occ.pop(c)\n            moved.add(q)\n',
     '            occ[q] = occ.pop(c)\n            moved.add(q)\n'
     '            if chain == "none": occ[c] = GHOST\n'),
    ('        flow += a * (moves - flow)\n',
     _CLEAN.format(i='        ') + '        flow += a * (moves - flow)\n'),
], vars(XPR))

ramp_sim = _patched(T.sim, [
    ('cycles=4000, warmup=1000, seed=1):', 'cycles=4000, warmup=1000, seed=1, chain="seq"):'),
    ("""                if g and src: free = [x for x in free if sum(1 for o in out[head[x]] if o not in occ) >= thr[head[x]]]""",
     """                if src: free = _CUR['ctrl'].gate(u, free, lambda x: sum(1 for o in out[head[x]] if o not in occ) * 8 / (2 * net.deg[head[x]]))"""),
    ("""    for t in range(cycles):
        if scheme.startswith('ring')""",
     """    for t in range(cycles):
        _CUR['ctrl'].tick(t, occ)
        if scheme.startswith('ring')"""),
    ('            occ[q] = occ.pop(c); moved.add(q)\n',
     '            occ[q] = occ.pop(c); moved.add(q)\n'
     '            if chain == "none": occ[c] = GHOST\n'),
    ('        for s in range(N):\n            if rnd.random() < rate:',
     _CLEAN.format(i='        ') + '        for s in range(N):\n            if rnd.random() < rate:'),
], dict(vars(T), _CUR=XR._CUR))


PRICE_SPECS = {'H': 'src=none:hop=price', 'P': 'src=all:hop=price:choice=softm:m=0.4'}


def run_one(spec, rate, pattern, seed, chain='seq', cycles=1600):
    """-> (throughput, hops or latency, long-way share, random-intermediate share)."""
    kind, _, sp = spec.partition(':')
    w = cycles // 4
    if kind == 'A':
        r = XA.run_one('torus', sp, rate, pattern, seed, chain, cycles)
        return [r[0], r[1], 0.0, 0.0]
    if kind == 'TL':
        r = tolls_sim(sp, rate, pattern, seed=seed, chain=chain, cycles=cycles, warmup=w)
        return [r[0], 0.0, r[1], r[2]]
    if kind == 'PR':
        r = prices_sim(PRICE_SPECS.get(sp, sp), rate, pattern, seed=seed, chain=chain,
                       cycles=cycles, warmup=w)
        return [r[0], r[1], r[2], 0.0]
    if kind == 'R':
        oc, nb = XR.torus_info()
        ctrl = XR.Ctrl(sp, oc, nb, seed)
        ctrl.warmup = w
        XR._CUR['ctrl'] = ctrl
        r = ramp_sim('min', rate, pattern, seed=seed, chain=chain, cycles=cycles, warmup=w)
        return [r[0], r[1], 0.0, 0.0]
    if kind == 'C':
        return list(csim(sp, rate, pattern, seed=seed, chain=chain, cycles=cycles))
    raise ValueError(spec)


def check():
    for ch in ('seq', 'none'):
        a = XA.run_one('torus', 'min/base', 0.7, 'tornado', 5, ch, 600)
        b = csim('hop=rand:src=none', 0.7, 'tornado', seed=5, chain=ch, cycles=600)
        print('min', ch, a[:2], b[:2], a[:2] == b[:2])
        a = XA.run_one('torus', 'min/P', 0.7, 'transpose', 5, ch, 600)
        b = csim('hop=P:src=none', 0.7, 'transpose', seed=5, chain=ch, cycles=600)
        print('min/P', ch, a[:2], b[:2], a[:2] == b[:2])
    a = XPR.sim_price('src=none:hop=price', 0.7, 'transpose', seed=5, cycles=600, warmup=150)
    b = csim('hop=price:src=none', 0.7, 'transpose', seed=5, cycles=600)
    c = prices_sim('src=none:hop=price', 0.7, 'transpose', seed=5, cycles=600, warmup=150)
    print('H seq', a[:2], b[:2], c[:2], a[:2] == b[:2] == c[:2])
    a = XT.sim('slex10m10', 0.7, 'tornado', seed=5, cycles=600, warmup=150)
    c = tolls_sim('slex10m10', 0.7, 'tornado', seed=5, cycles=600, warmup=150)
    print('slex seq', a, c, a == c)
    a = XR.run_one('torus', 'lx2_4_36_2', 'uniform', 0.7, 5, cycles=600, warmup=150)
    c = run_one('R:lx2_4_36_2', 0.7, 'uniform', 5, 'seq', 600)
    print('lx seq', a['thr'], c[0], a['thr'] == c[0])
    b = csim('hop=rand:src=none:thr=lx2_4_36_2', 0.7, 'uniform', seed=5, cycles=600)
    print('lx csim', b[0], a['thr'] == b[0])
    for sp in ('PR:H', 'TL:slex10m10', 'R:lx2_4_36_2', 'C:hop=price:src=toll'):
        print(sp, 'none', run_one(sp, 0.7, 'tornado', 5, 'none', 600))


# ------------------------------------------------------------------ driver
CACHE = os.environ.get('XP_COMBO_CACHE',
                       os.path.join(tempfile.gettempdir(), 'xp_combo_cache.json'))


def _job(a):
    return a, run_one(*a)


def load():
    try:
        with open(CACHE) as f:
            return {tuple(json.loads(k)): v for k, v in json.load(f).items()}
    except (OSError, ValueError):
        return {}


def save(new):
    """Merges new results into the cache on disk (several drivers may run at once)."""
    res = load()
    res.update(new)
    tmp = CACHE + f'.tmp{os.getpid()}'
    with open(tmp, 'w') as f:
        json.dump({json.dumps(list(k)): v for k, v in res.items()}, f)
    os.replace(tmp, CACHE)


def compute(jobs):
    from multiprocessing import Pool
    res = load()
    todo = [j for j in jobs if j not in res]
    if todo:
        # longest first: the combined and price schemes
        todo.sort(key=lambda j: (j[0][:2] not in ('C:', 'PR'), j[0]))
        with Pool(int(os.environ.get('XP_COMBO_PROCS', 3))) as pool:
            new = {}
            for i, (a, r) in enumerate(pool.imap_unordered(_job, todo, chunksize=1)):
                new[a] = list(r)
                if i % 10 == 9:
                    save(new)
        save(new)
    return load()


def cell(res, spec, pattern, rates, seeds, chain, cycles):
    """Peak over the rates of the mean over the seeds that were run (at least 4 of `seeds`)."""
    best = None
    for r in rates:
        v = [res.get((spec, r, pattern, s, chain, cycles)) for s in seeds]
        v = [x for x in v if x is not None]
        if len(v) < 4:
            continue
        m, se = XP.stats([x[0] for x in v])
        if best is None or m > best[0]:
            best = (m, se, r, sum(x[2] for x in v) / len(v), sum(x[3] for x in v) / len(v),
                    len(v))
    return best


PATS = XA.TPATS
SEEDS = [11, 12, 13, 14]


def run_cmd(argv):
    specs, pats, rates, seeds, chains = argv[:5]
    cycles = int(argv[5]) if len(argv) > 5 else 1600
    specs, chains = specs.split(','), chains.split(',')
    pats = PATS if pats == 'all' else pats.split(',')
    rates = [float(x) for x in rates.split(',')]
    seeds = [int(x) for x in seeds.split(',')] if '-' not in seeds else \
        list(range(int(seeds.split('-')[0]), int(seeds.split('-')[1]) + 1))
    jobs = [(sp, r, p, sd, ch, cycles) for ch in chains for sp in specs for p in pats
            for r in rates for sd in seeds]
    res = compute(jobs)
    print(f'seeds {seeds}, rates {rates}, cycles {cycles}: peak mean ± se (x1e-4) '
          '[long-way %/random-intermediate %]')
    for ch in chains:
        print(f'{ch:<5}{"":<44}' + ''.join(f'{p[:9]:>20}' for p in pats))
        for sp in specs:
            cells = []
            for p in pats:
                m, se, r, lw, va, _ = cell(res, sp, p, rates, seeds, ch, cycles)
                cells.append(f'{m:.4f}±{se * 1e4:<3.0f}[{100*lw:.0f}/{100*va:.0f}]')
            print(f'{ch:<5}{sp[:44]:<44}' + ''.join(f'{x:>20}' for x in cells), flush=True)


def report(argv):
    """report MAIN OTHERS RATES SEEDS CHAINS [CYCLES]: MAIN against every other scheme, per model
    and pattern (peak mean ± se over the seeds run, n seeds); the best of OTHERS and MAIN's
    difference to it in % and in combined standard errors (z).  Specs in OTHERS prefixed with
    '~' are references: shown, and compared separately, but not part of the best."""
    main, others, rates, seeds, chains = argv[:5]
    cycles = int(argv[5]) if len(argv) > 5 else 1600
    others = others.split(',')
    refs = [x[1:] for x in others if x.startswith('~')]
    others = [x for x in others if not x.startswith('~')]
    rates = [float(x) for x in rates.split(',')]
    seeds = list(range(int(seeds.split('-')[0]), int(seeds.split('-')[1]) + 1)) \
        if '-' in seeds else [int(x) for x in seeds.split(',')]
    res = load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-9, (a[1] ** 2 + b[1] ** 2) ** .5)
    for ch in chains.split(','):
        tab = {}
        for sp in [main] + others + refs:
            row = [cell(res, sp, p, XA.DOR_RATES if sp == 'A:dor' else rates, seeds, ch, cycles)
                   for p in PATS]
            if all(x is not None for x in row):
                tab[sp] = row
        print(f'\n== chain={ch}, {cycles} cycles, peak over offered {rates}: mean ± se (x1e-4) '
              '[seeds]')
        print(f'{"":<34}' + ''.join(f'{p[:9]:>16}' for p in PATS))
        for sp, row in tab.items():
            name = ('~' if sp in refs else '') + sp
            print(f'{name[:34]:<34}' + ''.join(f'{c[0]:>9.4f}±{c[1] * 1e4:<3.0f}[{c[5]}]'
                                                for c in row))
        if main not in tab:
            continue
        oth = [s for s in others if s in tab]
        best = [max(oth, key=lambda s: tab[s][i][0]) for i in range(len(PATS))]
        print(f'{"best of the others":<34}' + ''.join(f'{tab[b][i][0]:>16.4f}'
                                                     for i, b in enumerate(best)))
        print(f'{"  by":<34}' + ''.join(f'{b[-15:]:>16}' for b in best))
        print(f'{"MAIN vs best: %, z":<34}' + ''.join(
            f'{100 * (tab[main][i][0] / tab[b][i][0] - 1):>+9.2f}%{z(tab[main][i], tab[b][i]):>+5.1f}z'
            for i, b in enumerate(best)))
        print(f'{"MAIN vs each: min z":<34}' + ''.join(
            f'{min(z(tab[main][i], tab[s][i]) if tab[main][i][0] != tab[s][i][0] else 0.0 for s in oth):>15.1f}z'
            for i in range(len(PATS))))
        for r in refs:
            if r in tab:
                print(f'{"MAIN vs ~" + r[:25]:<34}' + ''.join(
                    f'{100 * (tab[main][i][0] / tab[r][i][0] - 1):>+9.2f}%{z(tab[main][i], tab[r][i]):>+5.1f}z'
                    for i in range(len(PATS))))


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check()
    elif sys.argv[1] == 'run':
        run_cmd(sys.argv[2:])
    elif sys.argv[1] == 'report':
        report(sys.argv[2:])
