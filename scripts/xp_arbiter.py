#!/usr/bin/env python3
"""Arbitration orders without the chaining artefact, and for every scheme alike (simulation only;
nothing here is proved).

`xp_backpressure.py` found that moving in-network packets before the injection lane, oldest
first, at each router (`l:io`) raises peak throughput.  Two confounds are checked here.

1. Chaining.  The simulators move packets one after another within a cycle, so a packet can
   enter a channel vacated earlier in the same cycle; a move order can gain by chaining more.
   Three move models (`chain`):
     seq   the original: sequential, a channel vacated earlier in the cycle is free (chaining
           depends on the order);
     none  no chaining: a move may only enter a channel that was free at the start of the
           move phase (after ejection); conflicts for such a channel are resolved by the
           arbitration order.  Implemented by leaving a ghost in each vacated channel until the
           end of the move phase, so every occupancy read (free hops, throttles, scores) sees
           the start-of-cycle configuration plus this cycle's claims.  This is what credit-based
           flow control with a credit delay of at least one cycle gives;
     full  maximal chaining: after the ordered pass, packets that did not move try again, in
           the same order, until a pass moves nobody -- every packet whose hop is vacated at any
           point of the cycle may take it (a combinational-backpressure pipeline; whole cycles
           of full buffers rotating at once are not modelled).
   Ejection at the start of a cycle and the source queue refilling the injection lane at its
   end are the same in every model and order.
2. Fairness.  The published baselines (torus: `dor`, `val`, `ugal`; mesh: Duato with a random
   selection, XY on both VCs, the west-first mesh, O1TURN) get the same orders and models.

The simulators are those of `xp_backpressure` (mesh `duatoMesh`/`tieredMesh` and the torus
schemes), `torus_experiments.sim_dor` and `routing_sim.simulate`, patched textually at load time
(each patch must apply exactly once); with `chain=seq, order=random` all reproduce the originals
bit for bit (`--check`).

Specs (`/`-separated):
  torus  dor/<order>                 dimension order with dateline VCs
         <scheme>/<sel>/<order>      xp_backpressure.sim (min, val, ugal, bandit2m7f5k, ...)
  mesh   R:<route>:<policy>/<order>  routing_sim.simulate (e.g. R:dualXY:random,
                                     R:westFirstMesh:random, R:duatoMesh:o1turn)
         <sel>/<order>/<thr>         xp_backpressure.mesh_sim (tiered/random/g4, X2/l:io/g3)
  orders: random, l:io, l:old, l:inj, g:io, g:old (see xp_backpressure)

Usage:
  python3 scripts/xp_arbiter.py --check
  python3 scripts/xp_arbiter.py run torus 'min/P/random,min/P/l:io' uniform 0.6,0.7 1,2,3,4 seq,none [cycles]
Prints, per spec, model and pattern, the peak over the rates of the mean accepted throughput
± its standard error over the seeds (x1e-4), the peak rate, and the fraction of chained moves.
  python3 scripts/xp_arbiter.py suite [seq,none|full]   (the experiment of the report below)
  python3 scripts/xp_arbiter.py report                  (its tables, from the cache)
  python3 scripts/xp_arbiter.py fair                    (per-source injection under l:io)
Results are cached in a JSON file (XP_ARB_CACHE, default xp_arbiter_cache.json in the system
temporary directory); XP_ARB_PROCS processes (default 2).
"""
import inspect
import json
import os
import sys
import tempfile

import xp_backpressure as XP
import torus_experiments as T
import routing_sim as R


class _Ghost(tuple):
    """Marks a channel vacated in the current move phase (no-chaining model)."""


GHOST = _Ghost((-1, -1, -1))


def passes(pks, occ, moved, chain):
    """The move loop's iteration: one ordered pass, repeated over the packets that did not move
    while a pass moves somebody when chain == 'full'."""
    yield from pks
    if chain != 'full':
        return
    while True:
        rest = [c for c in pks if c in occ and c not in moved and occ[c] is not GHOST]
        n0 = len(moved)
        yield from rest
        if len(moved) == n0:
            return
        pks = rest


def local(pks, router, kf):
    """xp_backpressure.local with a router function."""
    groups = {}
    for i, c in enumerate(pks):
        groups.setdefault(router(c), []).append(i)
    out = pks[:]
    for idx in groups.values():
        if len(idx) > 1:
            for i, c in zip(idx, sorted((pks[i] for i in idx), key=kf)):
                out[i] = c
    return out


def arrange(pks, occ, rnd, order, router, isinj):
    rnd.shuffle(pks)
    if order == 'random':
        return pks
    scope, key = order.split(':')
    kf = {'io': lambda c: (isinj(c), occ[c][1]), 'old': lambda c: occ[c][1],
          'inj': lambda c: isinj(c)}[key]
    if scope == 'g':
        pks.sort(key=kf)
        return pks
    return local(pks, router, kf)


def patched(fn, patches, base_globals):
    src = inspect.getsource(fn)
    for old, new in patches:
        n = src.count(old)
        assert n == 1, (fn.__name__, old, n)
        src = src.replace(old, new)
    ns = dict(base_globals)
    ns.update(passes=passes, GHOST=GHOST, arrange=arrange)
    exec(compile(src, f'<patched {fn.__name__}>', 'exec'), ns)
    return ns[fn.__name__]


CLEAN = ('if chain == "none":\n{i}    for _c in vacated:\n'
         '{i}        if occ.get(_c) is GHOST: {take}\n')

mesh_sim = patched(XP.mesh_sim, [
    ('warmup=2000, seed=1):', 'warmup=2000, seed=1, chain="seq"):'),
    ('        for c in packets:\n', '        for c in passes(packets, occ, moved, chain):\n'),
    ('                put(c2, take(c))\n',
     '                put(c2, take(c))\n                if chain == "none": put(c, GHOST)\n'),
    ("        if order == 'rr':\n",
     '        ' + CLEAN.format(i='        ', take='take(_c)') + "        if order == 'rr':\n"),
], vars(XP))

torus_sim = patched(XP.sim, [
    ("sel='base', order='random'):", "sel='base', order='random', chain='seq'):"),
    ('        for c in pks:\n', '        for c in passes(pks, occ, moved, chain):\n'),
    ('            occ[q] = occ.pop(c); moved.add(q)\n',
     '            occ[q] = occ.pop(c); moved.add(q)\n'
     '            if chain == "none": occ[c] = GHOST\n'),
    ("        if order == 'rr':",
     '        ' + CLEAN.format(i='        ', take='del occ[_c]') + "        if order == 'rr':"),
], vars(XP))

sim_dor = patched(T.sim_dor, [
    ('seed=1):\n', 'seed=1, order="random", chain="seq"):\n    _st = [0, 0]\n'),
    ('moved = set(); pks = list(occ); rnd.shuffle(pks)\n        for c in pks:\n',
     'moved = set(); vacated = set()\n'
     '        pks = arrange(list(occ), occ, rnd, order, lambda c: c[3], lambda c: c[1] == 4)\n'
     '        for c in passes(pks, occ, moved, chain):\n'),
    ('            occ[q] = occ.pop(c); moved.add(q)\n',
     '            occ[q] = occ.pop(c); moved.add(q)\n'
     '            if t >= warmup: _st[0] += 1; _st[1] += q in vacated\n'
     '            vacated.add(c)\n'
     '            if chain == "none": occ[c] = GHOST\n'),
    ('        for s in range(N):\n',
     '        ' + CLEAN.format(i='        ', take='del occ[_c]') + '        for s in range(N):\n'),
    ('    return len(lat)/((cycles-warmup)*N), 0',
     '    return len(lat)/((cycles-warmup)*N), 0, _st[0]/(cycles-warmup), _st[1]/max(1, _st[0])'),
], vars(T))

simulate = patched(R.simulate, [
    ('warmup=2000, seed=1):\n', 'warmup=2000, seed=1, order="random", chain="seq"):\n'
                                '    _st = [0, 0]\n'),
    ('        moved = set()\n        packets = list(occ)\n        rnd.shuffle(packets)\n'
     '        for c in packets:\n',
     '        moved = set(); vacated = set()\n'
     '        packets = arrange(list(occ), occ, rnd, order, head, lambda c: c // 2 % 5 == 4)\n'
     '        for c in passes(packets, occ, moved, chain):\n'),
    ('                occ[c2] = occ.pop(c)\n                moved.add(c2)\n',
     '                occ[c2] = occ.pop(c)\n                moved.add(c2)\n'
     '                if t >= warmup: _st[0] += 1; _st[1] += c2 in vacated\n'
     '                vacated.add(c)\n'
     '                if chain == "none": occ[c] = GHOST\n'),
    ('        for s in range(n):\n            if rnd.random() < rate:\n',
     '        ' + CLEAN.format(i='        ', take='del occ[_c]') +
     '        for s in range(n):\n            if rnd.random() < rate:\n'),
    ('    return throughput, latency\n',
     '    return throughput, latency, _st[0] / (cycles - warmup), _st[1] / max(1, _st[0])\n'),
], vars(R))

_ROUTES = R.mesh(8)[2]

# Injection fairness: the same simulators, also counting the packets each source moves from its
# queue into its injection lane after warmup and the longest wait of a packet in an injection
# lane; they return (..., min / mean of the per-source counts, longest injection-lane wait).
_FAIR_RET = ('_inj = [x for x in _inj]; _m = sum(_inj) / len(_inj)\n'
             '    return {ret}, min(_inj) / max(1e-9, _m), _w[0]\n')
_mesh_fair = patched(XP.mesh_sim, [
    ('warmup=2000, seed=1):', 'warmup=2000, seed=1, chain="seq"):\n'
                              '    _inj = [0] * (k * k); _w = [0]'),
    ('        for c in packets:\n', '        for c in passes(packets, occ, moved, chain):\n'),
    ('                put(c2, take(c))\n',
     '                if src and t >= warmup: _w[0] = max(_w[0], t - since.get(c, t))\n'
     '                put(c2, take(c))\n                if chain == "none": put(c, GHOST)\n'),
    ("        if order == 'rr':\n",
     '        ' + CLEAN.format(i='        ', take='take(_c)') + "        if order == 'rr':\n"),
    ('                put(ch(s, 4, 0), queues[s].popleft())\n',
     '                put(ch(s, 4, 0), queues[s].popleft())\n'
     '                if t >= warmup: _inj[s] += 1\n'),
    ('    return throughput, latency, moves / (cycles - warmup), chained / max(1, moves)\n',
     '    ' + _FAIR_RET.format(
         ret='throughput, latency, moves / (cycles - warmup), chained / max(1, moves)')),
], vars(XP))

_torus_fair = patched(XP.sim, [
    ("sel='base', order='random'):", "sel='base', order='random', chain='seq'):\n"
                                     "    _inj = [0] * N; _w = [0]"),
    ('        for c in pks:\n', '        for c in passes(pks, occ, moved, chain):\n'),
    ('            occ[q] = occ.pop(c); moved.add(q)\n',
     '            if src and t >= warmup: _w[0] = max(_w[0], t - since.get(c, t))\n'
     '            occ[q] = occ.pop(c); moved.add(q)\n'
     '            if chain == "none": occ[c] = GHOST\n'),
    ("        if order == 'rr':",
     '        ' + CLEAN.format(i='        ', take='del occ[_c]') + "        if order == 'rr':"),
    ('                occ[c] = [d, born, 0, dist[s][d]',
     '                if t >= warmup: _inj[s] += 1\n'
     '                occ[c] = [d, born, 0, dist[s][d]'),
    ('    return len(lat)/((cycles-warmup)*N), hopsum/max(1,len(lat)), nmv/(cycles-warmup), '
     'nchain/max(1, nmv)\n',
     '    ' + _FAIR_RET.format(
         ret='len(lat)/((cycles-warmup)*N), hopsum/max(1,len(lat)), nmv/(cycles-warmup), '
             'nchain/max(1, nmv)')),
], vars(XP))


def fair_one(topo, spec, rate, pattern, seed, chain, cycles):
    p = spec.split('/')
    if topo == 'mesh':
        return _mesh_fair(8, rate, pattern, p[0], p[1], p[2], seed=seed, chain=chain,
                          cycles=cycles, warmup=cycles // 3)
    return _torus_fair(p[0], rate, pattern, sel=p[1], order=p[2], seed=seed, chain=chain,
                       cycles=cycles, warmup=cycles // 4)


def fair():
    """Injection fairness at and past saturation: per-source injected packets (min / mean) and
    the longest wait in an injection lane, random against l:io."""
    from multiprocessing import Pool
    jobs = [(topo, f'{s}/{o}{g}', r, p, sd, ch, cyc)
            for topo, s, g, pats, rs, cyc in (
                ('torus', 'min/P', '', ('uniform', 'tornado', 'hotspot'), (0.7, 1.0), TCYC),
                ('mesh', 'X2', '/g3', ('uniform', 'transpose', 'hotspot'), (0.55, 0.75), MCYC))
            for o in ORDERS for p in pats for r in rs for ch in ('seq', 'none') for sd in (11, 12)]
    with Pool(int(os.environ.get('XP_ARB_PROCS', 2))) as pool:
        out = pool.starmap(fair_one, jobs)
    agg = {}
    for j, o in zip(jobs, out):
        agg.setdefault(j[:4] + j[5:6], []).append(o)
    print('spec, rate, pattern, chain: throughput, min/mean per-source injections, '
          'longest injection-lane wait (cycles), mean of 2 seeds')
    for k, v in agg.items():
        print(f'{k[0]:<6}{k[1]:<16}{k[2]:<5}{k[3]:<10}{k[4]:<5} thr {sum(x[0] for x in v) / 2:.4f}'
              f'  min/mean {sum(x[-2] for x in v) / 2:.3f}  maxwait {max(x[-1] for x in v)}')


def run_one(topo, spec, rate, pattern, seed, chain='seq', cycles=None):
    """-> (throughput, latency or hops, moves per cycle, fraction of chained moves)."""
    parts = spec.split('/')
    if topo == 'mesh':
        kw = {} if cycles is None else {'cycles': cycles, 'warmup': cycles // 3}
        if parts[0].startswith('R:'):
            _, route, policy = parts[0].split(':', 2)
            policy = policy.replace('_', ':')      # T4_random -> T4:random
            order = parts[1] if len(parts) > 1 else 'random'
            return simulate(8, _ROUTES[route], rate, pattern, policy, seed=seed, order=order,
                            chain=chain, **kw)
        sel = parts[0]; order = parts[1] if len(parts) > 1 else 'random'
        thr = parts[2] if len(parts) > 2 else 'g4'
        return mesh_sim(8, rate, pattern, sel, order, thr, seed=seed, chain=chain, **kw)
    kw = {} if cycles is None else {'cycles': cycles, 'warmup': cycles // 4}
    if parts[0] == 'dor':
        order = parts[1] if len(parts) > 1 else 'random'
        return sim_dor(rate, pattern, seed=seed, order=order, chain=chain, **kw)
    scheme = parts[0]; sel = parts[1] if len(parts) > 1 else 'base'
    order = parts[2] if len(parts) > 2 else 'random'
    return torus_sim(scheme, rate, pattern, sel=sel, order=order, seed=seed, chain=chain, **kw)


def check():
    a = R.simulate(8, _ROUTES['westFirstMesh'], 0.45, 'transpose', 'random', cycles=900,
                   warmup=300, seed=3)
    b = run_one('mesh', 'R:westFirstMesh:random/random', 0.45, 'transpose', 3, cycles=900)
    print('mesh R  ', a, b[:2], a == b[:2])
    a = R.simulate(8, _ROUTES['duatoMesh'], 0.45, 'bitcomp', 'o1turn', cycles=900, warmup=300,
                   seed=4)
    b = run_one('mesh', 'R:duatoMesh:o1turn/random', 0.45, 'bitcomp', 4, cycles=900)
    print('mesh o1 ', a, b[:2], a == b[:2])
    a = XP.mesh_sim(8, 0.45, 'transpose', 'X2', 'l:io', 'g3', cycles=900, warmup=300, seed=3)
    b = run_one('mesh', 'X2/l:io/g3', 0.45, 'transpose', 3, cycles=900)
    print('mesh xp ', a, b, a == b)
    a = T.sim_dor(0.3, 'tornado', cycles=800, warmup=200, seed=5)
    b = run_one('torus', 'dor/random', 0.3, 'tornado', 5, cycles=800)
    print('dor     ', a, b[:2], a == b[:2])
    for sch in ('min/P/l:io', 'ugal/base/random', 'bandit2m7f5k/base/random'):
        p = sch.split('/')
        a = XP.sim(p[0], 0.7, 'tornado', sel=p[1], order=p[2], cycles=800, warmup=200, seed=5)
        b = run_one('torus', sch, 0.7, 'tornado', 5, cycles=800)
        print('torus   ', sch, a, b, a == b)
    for topo, spec, r in (('torus', 'min/P/l:io', 0.5), ('torus', 'dor/l:io', 0.3),
                          ('mesh', 'X2/l:io/g3', 0.4), ('mesh', 'R:dualXY:random/l:io', 0.3)):
        for ch in ('seq', 'none', 'full'):
            print(f'{topo} {spec} {ch}:', run_one(topo, spec, r, 'uniform', 1, ch, 800))


# ------------------------------------------------------------------ driver
CACHE = os.environ.get('XP_ARB_CACHE', os.path.join(tempfile.gettempdir(), 'xp_arbiter_cache.json'))


def _job(a):
    return a, run_one(*a)


def load():
    try:
        with open(CACHE) as f:
            return {tuple(json.loads(k)): v for k, v in json.load(f).items()}
    except (OSError, ValueError):
        return {}


def save(res):
    tmp = CACHE + '.tmp'
    with open(tmp, 'w') as f:
        json.dump({json.dumps(list(k)): v for k, v in res.items()}, f)
    os.replace(tmp, CACHE)


def compute(jobs, procs=None):
    from multiprocessing import Pool
    res = load()
    todo = [j for j in jobs if j not in res]
    if todo:
        with Pool(procs or int(os.environ.get('XP_ARB_PROCS', 2))) as pool:
            for i, (a, r) in enumerate(pool.imap_unordered(_job, todo, chunksize=1)):
                res[a] = list(r)
                if i % 20 == 19:
                    save(res)
        save(res)
    return res


def cell(res, topo, spec, pattern, rates, seeds, chain, cycles):
    """Peak over rates of the mean throughput: (mean, se, rate, chained fraction)."""
    best = None
    for r in rates:
        v = [res.get((topo, spec, r, pattern, s, chain, cycles)) for s in seeds]
        if any(x is None for x in v):
            continue
        m, se = XP.stats([x[0] for x in v])
        if best is None or m > best[0]:
            best = (m, se, r, sum(x[3] for x in v) / len(v))
    return best


# ------------------------------------------------------------------ the experiment
TPATS = ['uniform', 'transpose', 'shuffle', 'bitrev', 'bitcomp', 'hotspot', 'tornado',
         'neighbor', 'randperm']
MPATS = ['uniform', 'transpose', 'shuffle', 'bitrev', 'hotspot', 'bitcomp']
ORDERS = ['random', 'l:io']
T_OURS = ['min/base', 'min/P', 'bandit2m7f5k/base']
T_PUB = ['dor', 'val/base', 'ugal/base']
M_OURS = [('tiered', 'g4'), ('X2', 'g3')]
M_PUB = ['R:duatoMesh:random', 'R:duatoMesh:T4_random', 'R:dualXY:random',
         'R:westFirstMesh:random', 'R:duatoMesh:o1turn']
SEEDS = [11, 12, 13, 14]
TCYC, MCYC, PCYC = 1600, 2000, 1000
T_RATES = [0.7, 1.0]                  # torus schemes are throttled: flat past saturation
DOR_RATES = [0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 1.0]
M_RATES = [0.55, 0.75]               # throttled mesh schemes (flat past saturation)
PILOT = [0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.55]


def mspec(base, order, thr=None):
    return f'{base}/{order}' if thr is None else f'{base}/{order}/{thr}'


def specs(topo, which):
    if topo == 'torus':
        names = T_OURS if which == 'ours' else T_PUB
        return [mspec(b, o) for b in names for o in ORDERS]
    if which == 'ours':
        return [mspec(s, o, g) for s, g in M_OURS for o in ORDERS]
    return [mspec(b, o) for b in M_PUB for o in ORDERS]


def rates_for(res, topo, spec, pattern, chain):
    if topo == 'torus':
        return DOR_RATES if spec.startswith('dor') else T_RATES
    if not spec.startswith('R:') or 'T4' in spec:
        return M_RATES
    # unthrottled mesh baselines collapse past saturation: the 3 best rates of a 1-seed pilot
    pc = 'seq' if chain == 'full' else chain
    v = {r: res[('mesh', spec, r, pattern, 1, pc, PCYC)][0] for r in PILOT}
    top = sorted(v, key=v.get)[-3:]
    if max(v, key=v.get) == PILOT[-1]:
        top += [0.6, 0.65]
    return sorted(top)


def suite(chains):
    res = load()
    for chain in [c for c in chains if c != 'full']:     # pilot of the unthrottled mesh baselines
        res = compute([('mesh', sp, r, p, 1, chain, PCYC) for sp in specs('mesh', 'pub')
                       if 'T4' not in sp for p in MPATS for r in PILOT])
    if 'full' in chains:
        res = compute([('mesh', sp, r, p, 1, 'seq', PCYC) for sp in specs('mesh', 'pub')
                       if 'T4' not in sp for p in MPATS for r in PILOT])
    for topo, pats, cyc in (('torus', TPATS, TCYC), ('mesh', MPATS, MCYC)):
        jobs = [(topo, sp, r, p, sd, ch, cyc) for ch in chains
                for sp in specs(topo, 'ours') + specs(topo, 'pub') for p in pats
                for r in rates_for(res, topo, sp, p, ch) for sd in SEEDS]
        print(topo, len(jobs), 'jobs', flush=True)
        res = compute(jobs)


def report():
    res = load()
    for topo, pats, cyc in (('torus', TPATS, TCYC), ('mesh', MPATS, MCYC)):
        for chain in ('seq', 'none', 'full'):
            table = {}
            for sp in specs(topo, 'ours') + specs(topo, 'pub'):
                try:
                    cells = [cell(res, topo, sp, p, rates_for(res, topo, sp, p, chain), SEEDS,
                                  chain, cyc) for p in pats]
                except KeyError:
                    continue
                if all(c is not None for c in cells):
                    table[sp] = cells
            if not table:
                continue
            print(f'\n== {topo}, chain={chain}: peak mean ± se (x1e-4) over seeds {SEEDS}, '
                  f'{cyc} cycles; (chained fraction)')
            print(f'{"":<28}' + ''.join(f'{p[:9]:>18}' for p in pats))
            for sp, cells in table.items():
                print(f'{sp:<28}' + ''.join(f'{m:>8.4f}±{se * 1e4:<3.0f}({ch:.2f})'
                                            for m, se, r, ch in cells))
            for o in ORDERS:
                pub = [sp for sp in table if sp.endswith('/' + o) and
                       any(sp.startswith(b) for b in (T_PUB if topo == 'torus' else M_PUB))]
                if not pub:
                    continue
                best = [max(pub, key=lambda sp: table[sp][i][0]) for i in range(len(pats))]
                print(f'{"best published, " + o:<28}' +
                      ''.join(f'{table[b][i][0]:>8.4f} {b.split("/")[0][-9:]:>9}'
                              for i, b in enumerate(best)))
                for sp in table:
                    if sp in pub:
                        continue
                    print(f'{"  " + sp + " vs":<28}' + ''.join(
                        f'{100 * (table[sp][i][0] / table[b][i][0] - 1):>+7.1f}% '
                        f'{(table[sp][i][0] - table[b][i][0]) / max(1e-9, (table[sp][i][1] ** 2 + table[b][i][1] ** 2) ** .5):>+6.1f}se  '
                        for i, b in enumerate(best)))


def main():
    if sys.argv[1] == '--check':
        check()
        return
    if sys.argv[1] == 'suite':
        suite(sys.argv[2].split(',') if len(sys.argv) > 2 else ['seq', 'none'])
        return
    if sys.argv[1] == 'report':
        report()
        return
    if sys.argv[1] == 'fair':
        fair()
        return
    _, topo, specs, pats, rates, seeds, chains = sys.argv[1:8]
    specs, pats, chains = specs.split(','), pats.split(','), chains.split(',')
    rates = [float(x) for x in rates.split(',')]
    seeds = [int(x) for x in seeds.split(',')]
    cycles = int(sys.argv[8]) if len(sys.argv) > 8 else None
    jobs = [(topo, sp, r, p, sd, ch, cycles) for ch in chains for sp in specs for p in pats
            for r in rates for sd in seeds]
    res = compute(jobs)
    print(f'{topo}, seeds {seeds}, rates {rates}, cycles {cycles}: peak mean ± se (x1e-4) '
          '[rate, chained]')
    for ch in chains:
        for sp in specs:
            cells = []
            for p in pats:
                m, se, r, chn = cell(res, topo, sp, p, rates, seeds, ch, cycles)
                cells.append(f'{p[:8]} {m:.4f}±{se * 1e4:.0f} [{r},{chn:.2f}]')
            print(f'{ch:<5}{sp:<26}' + ' | '.join(cells), flush=True)


if __name__ == '__main__':
    main()
