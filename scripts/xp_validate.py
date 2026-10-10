#!/usr/bin/env python3
"""Validation of the mesh learner and the torus combined scheme: 16 x 16, longer runs, fairness
(simulation only; nothing here is proved).

Runs the existing simulators unchanged (imported, and patched textually where noted; every patch
must apply exactly once):
  mesh   `xp_transpose.xsim` (msim with the extra tiers / selections and the per-source injection
         counters of `xp_transpose`) for the published schemes as bit-identical tier lists
         (XY on both VCs, west-first random, Duato random, Duato throttled g4), the learner of
         `xp_transpose.pxsim` (`PX:t5b:th=0.7:d=2:elim=0.1`), and O1TURN through
         `xp_arbiter.simulate` (routing_sim's `o1turn` policy on `duatoMesh`);
  torus  `xp_combo.csim` (the combined scheme `C:hop=price:src=toll:pm=0.2:thr=lx2_4_32_2:
         thr2=lx2_4_35_2`) and the published `dor` / `val` / `ugal` of `xp_arbiter`
         (`torus_experiments.sim_dor`, `xp_backpressure.sim`), each with the move models of
         `xp_arbiter` and, here, per-source injection counters (`check`: bit-identical results).

Grid size.  The scripts fix K = 8 at module level.  With XPV_K=16 in the environment this module
re-executes the modules that hard-code the size from their own source with the size lines
replaced (same line count, so `inspect.getsource` -- which the patch machinery uses -- still
returns the unchanged function texts), before anything else imports them:
  routing_graph_sim  RANDPERM = a random permutation of the k^2 nodes (Random(0).shuffle, as for 64)
  torus_experiments, xp_backpressure, xp_ramp, xp_bitcomp, xp_transpose   K = k
  torus_experiments, xp_backpressure  spanning-tree root 27 = (3, 3) -> (k/2 - 1)(k + 1)
  xp_arbiter         _ROUTES = R.mesh(k)
Patterns at k = 16: uniform, transpose, shuffle and bit reversal (k a power of 2), bit
complement, hotspot (a fifth of the packets to node (k/2, k/2)), tornado x -> x + k/2 - 1,
neighbour, random permutation of the 256 nodes.  The mesh `msim` takes k as an argument; the
learner gets `nsrc = k^2` (its congestion gate counts sources).  Tuned constants are used as
they are (X' fd = 5 / fs = 3, the learner's th = 0.7, epochs of 250 cycles, the lx thresholds
32 / 35 % with radius 2, the toll / price constants): the honest generalisation test.

Specs (key = (k, spec, rate, pattern, seed, chain, cycles)):
  MX:<msim spec>       mesh tier list (xsim), + [min/mean, Jain] of per-source injections
  MPX:<set>[:opts]     mesh learner (sets: xp_transpose.MSETS / FSETS here), + fairness
  MFX:<set>[:opts]     the fairness-gated learner (FairLearner below), + fairness
  MO1                  O1TURN (xp_arbiter.simulate, duatoMesh / o1turn)
  TC:<xp_combo spec>   torus combined scheme (csim), + fairness
  TA:dor | TA:val | TA:ugal   torus published schemes (random arbitration), + fairness
Results: [throughput, latency/hops, ., ., (learner: switches, mode shares...), min/mean, Jain].

Usage:
  python3 scripts/xp_validate.py check
  python3 scripts/xp_validate.py jobs FILE    lines 'specs|pats|rates|seeds|chains|cycles' (k from XPV_K)
  python3 scripts/xp_validate.py table K PLANFILE
Cache XPV_CACHE (default xp_validate.json in the system temporary directory), XPV_PROCS
processes (default 3).
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
_DIR = os.path.dirname(os.path.abspath(__file__))
KV = int(os.environ.get('XPV_K', '8'))


# ------------------------------------------------------------------ grid size
def _resize(k):
    """re-execute the size-dependent modules with K = k (see the module docstring)"""
    import types
    root = (k // 2 - 1) * (k + 1)
    plan = [
        ('routing_graph_sim', [('RANDPERM = list(range(64))\n', f'RANDPERM = list(range({k * k}))\n')]),
        ('torus_experiments', [('K = 8; N = K*K\n', f'K = {k}; N = K*K\n'),
                               ("escape='updown', root=27)", f"escape='updown', root={root})")]),
        ('xp_backpressure', [('K = 8; N = K*K\n', f'K = {k}; N = K*K\n'),
                             ("escape='updown', root=27)\n\n# a copy",
                              f"escape='updown', root={root})\n\n# a copy")]),
        ('xp_ramp', [('K = 8\nN = K * K\n', f'K = {k}\nN = K * K\n')]),
        ('xp_arbiter', [('_ROUTES = R.mesh(8)[2]\n', f'_ROUTES = R.mesh({k})[2]\n')]),
        ('xp_bitcomp', [('K = 8\nN = K * K\n', f'K = {k}\nN = K * K\n')]),
        ('xp_transpose', [('K = 8\nN = K * K\n', f'K = {k}\nN = K * K\n')]),
    ]
    import routing_sim  # noqa: F401  (size-free; imported first so the others bind to it)
    for name, reps in plan:
        assert name not in sys.modules, name
        path = os.path.join(_DIR, name + '.py')
        with open(path) as f:
            src = f.read()
        for old, new in reps:
            assert src.count(old) == 1, (name, old)
            assert old.count('\n') == new.count('\n')
            src = src.replace(old, new)
        mod = types.ModuleType(name)
        mod.__file__ = path
        sys.modules[name] = mod
        # the dependency order of `plan` is the import order: each module's imports of earlier
        # names find the resized ones in sys.modules; later names are imported on demand
        exec(compile(src, path, 'exec'), mod.__dict__)


if KV != 8:
    _resize(KV)

import inspect                      # noqa: E402
import json                         # noqa: E402
import random                       # noqa: E402
import tempfile                     # noqa: E402

import routing_sim as R             # noqa: E402
import torus_experiments as T       # noqa: E402
import xp_backpressure as XP        # noqa: E402
import xp_arbiter as XA             # noqa: E402
import xp_combo as XC               # noqa: E402
import xp_combo2 as X2              # noqa: E402
import xp_portfolio as PF           # noqa: E402
import xp_portfolio2 as P2          # noqa: E402
import xp_transpose as XT           # noqa: E402

assert T.K == XP.K == XT.K == KV and len(sys.modules['routing_graph_sim'].RANDPERM) == KV * KV
NN = KV * KV


def fairness(inj, gen):
    """(min / mean, Jain's index) of the per-source injections after warmup, over the sources
    that generated traffic (as xp_transpose.fairness)"""
    v = [i for i, g in zip(inj, gen) if g > 0]
    if not v:
        return 1.0, 1.0
    m = sum(v) / len(v)
    return min(v) / max(1e-9, m), sum(v) ** 2 / max(1e-9, len(v) * sum(x * x for x in v))


# ------------------------------------------------------------------ mesh
FSETS = {}          # extra mode sets (fairness variants), filled below


def _modes(name):
    return FSETS.get(name) or XT.MSETS.get(name) or PF.MSETS[name]


def mesh_x(sp, rate, pattern, seed, chain, cycles):
    fn, ns = XT.xsim_fn()
    ns['_INJ'] = [0] * NN
    ns['_GEN'] = [0] * NN
    r = fn(sp, rate, pattern, seed=seed, chain=chain, cycles=cycles, k=KV)
    return list(r) + list(fairness(ns['_INJ'], ns['_GEN']))


class FairLearner(PF.Learner):
    """xp_portfolio.Learner whose estimate of a mode is its delivery rate if the mean Jain index
    of the per-source injections in its last W measured epochs is at least `jmin`, else that rate
    times (1 - pen): an unfair mode is used only when nothing fair comes close.  gm >= 0: only
    mode gm is gated (the throttle mode that trades fairness for throughput).  Reads only
    history (injection counts), like the learner itself."""

    def __init__(self, K, seed, warmup, jmin=0.95, pen=0.5, gm=-1, nsrc=64, **kw):
        super().__init__(K, seed, warmup, nsrc=nsrc, **kw)
        self.jmin, self.pen, self.gm = jmin, pen, int(gm)
        self.ninj = [0] * nsrc
        self.inj0 = [0] * nsrc
        self.jays = [[] for _ in range(K)]

    def est(self, m):
        s = self.samples[m]
        if not s:
            return -1.0
        v = sum(s) / len(s)
        j = self.jays[m]
        if (self.gm < 0 or m == self.gm) and j and sum(j) / len(j) < self.jmin:
            v *= 1 - self.pen
        return v

    def step(self, t, inj=()):
        if t == self.ms:
            self.inj0 = list(self.ninj)
        rec = (t > 0 and t % self.E == 0 and self.K > 1 and t - self.ms > 0)
        if rec:
            cur = self.cur
            d = [a - b for a, b in zip(self.ninj, self.inj0)]
            tot = sum(d)
            jay = tot * tot / max(1e-9, len(d) * sum(x * x for x in d)) if tot else 1.0
            snap = [list(x) for x in self.samples]
        r = super().step(t, inj)
        if rec and [list(x) for x in self.samples] != snap:
            js = self.jays[cur]                # the base recorded a sample for `cur`
            js.append(jay)
            if len(js) > self.W:
                js.pop(0)
        if self.ms == t:
            self.inj0 = list(self.ninj)
        return r


_PXF = None


def pxsim_fair_fn():
    """xp_transpose.pxsim_fn with the injections also counted for the learner (L.ninj)"""
    global _PXF
    if _PXF is None:
        extra = [
            ("def msim(spec, rate, pattern, seed=1, chain='seq', cycles=2000, warmup=None, k=8):",
             "def pmsim(spec, rate, pattern, seed=1, chain='seq', cycles=2000, warmup=None, k=8):"),
            ("    useprice = sel == 'price'\n", "    useprice = _PF['useprice']\n"),
            (PF._HOOK_OLD,
             "    for t in range(cycles):\n"
             "        _m = _PF['L'].step(t, [_s for _s in range(n) if ch(_s, 4, 0) in occ])\n"
             "        if _m is not None:\n"
             "            tiers_n, stiers_n, sx, sel, delta, gdev, devset, gfix = _PF['modes'][_m]\n"
             "        if ctrl is not None:\n            ctrl.tick(t, occ)\n"),
            ("            if _DG and t >= warmup:\n                _DG['ej'][_dd] += 1\n",
             "            if _DG and t >= warmup:\n                _DG['ej'][_dd] += 1\n"
             "            _PF['L'].n += 1\n"),
            ("                    _INJ[s] += 1\n",
             "                    _INJ[s] += 1\n"
             "                _PF['L'].ninj[s] += 1\n"),
        ]
        _PXF = XT._build(extra, 'pmsim')
        _PXF[1].update(_XT=XT._XT, _XS=XT._XS, _DG=None)
    return _PXF


def mesh_px(spec, rate, pattern, seed, chain, cycles, fair=False):
    """xp_transpose.pm_run with nsrc = k^2 and k passed on; fair: the FairLearner (jmin, pen)"""
    toks = spec.split(':')
    modes = _modes(toks[0])
    lo = PF.lparse([t for t in toks[1:] if t.split('=')[0] not in ('jmin', 'pen', 'gm')])
    fo = {t.split('=')[0]: float(t.split('=')[1]) for t in toks[1:]
          if t.split('=')[0] in ('jmin', 'pen', 'gm')}
    fn, ns = pxsim_fair_fn() if fair else XT.pxsim_fn()
    ns['_INJ'] = [0] * NN
    ns['_GEN'] = [0] * NN
    warmup = cycles // 3
    L = (FairLearner(len(modes), seed, warmup, nsrc=NN, **fo, **lo) if fair
         else PF.Learner(len(modes), seed, warmup, nsrc=NN, **lo))
    ns['_PF'].update(L=L, modes=[PF.mesh_mode(m) for m in modes],
                     useprice=any(X2.mparse(m)['sel'] == 'price' for m in modes))
    r = fn(modes[L.cur], rate, pattern, seed=seed, chain=chain, cycles=cycles, warmup=warmup,
           k=KV)
    tot = max(1, sum(L.time))
    return ([r[0], r[1], 0.0, 0.0, L.switches] + [x / tot for x in L.time] +
            list(fairness(ns['_INJ'], ns['_GEN'])))


_RT = {}


def mesh_o1(rate, pattern, seed, chain, cycles):
    if 'r' not in _RT:
        _RT['r'] = R.mesh(KV)[2]['duatoMesh']
    return list(XA.simulate(KV, _RT['r'], rate, pattern, 'o1turn', cycles=cycles,
                            warmup=cycles // 3, seed=seed, order='random', chain=chain))


# ------------------------------------------------------------------ torus, with fairness
_FT = {}


def _torus_fns():
    if _FT:
        return _FT
    CLEAN = XA.CLEAN
    inj = ('                d, born = queues[s].popleft()\n',
           '                d, born = queues[s].popleft()\n'
           '                if t >= warmup: _INJ[s] += 1\n')
    # xp_arbiter.torus_sim's patches + counters
    _FT['sim'] = XA.patched(XP.sim, [
        ("sel='base', order='random'):", "sel='base', order='random', chain='seq'):"),
        ('        for c in pks:\n', '        for c in passes(pks, occ, moved, chain):\n'),
        ('            occ[q] = occ.pop(c); moved.add(q)\n',
         '            occ[q] = occ.pop(c); moved.add(q)\n'
         '            if chain == "none": occ[c] = GHOST\n'),
        ("        if order == 'rr':",
         '        ' + CLEAN.format(i='        ', take='del occ[_c]') + "        if order == 'rr':"),
        ('                if d != s: queues[s].append((d, t))\n',
         '                if d != s: queues[s].append((d, t)); _GEN[s] += 1\n'),
        inj,
    ], vars(XP))
    # xp_arbiter.sim_dor's patches + counters
    _FT['dor'] = XA.patched(T.sim_dor, [
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
        ('                if d != s: queues[s].append((d, t))\n',
         '                if d != s: queues[s].append((d, t)); _GEN[s] += 1\n'),
        ('                d, born = queues[s].popleft(); occ[c] = [d, born, 0]\n',
         '                d, born = queues[s].popleft(); occ[c] = [d, born, 0]\n'
         '                if t >= warmup: _INJ[s] += 1\n'),
    ], vars(T))
    # xp_combo.csim + counters
    src = inspect.getsource(XC.csim)
    for old, new in [('                    queues[s].append((dd, t))\n',
                      '                    queues[s].append((dd, t))\n'
                      '                    _GEN[s] += 1\n'), inj]:
        assert src.count(old) == 1, old
        src = src.replace(old, new)
    ns = dict(vars(XC))
    exec(compile(src, '<xp_validate csim>', 'exec'), ns)
    _FT['csim'] = ns['csim']
    return _FT


def _run_counted(fn, *a, **kw):
    g = fn.__globals__
    g['_INJ'] = [0] * NN
    g['_GEN'] = [0] * NN
    r = fn(*a, **kw)
    return list(r) + list(fairness(g['_INJ'], g['_GEN']))


def torus_c(sp, rate, pattern, seed, chain, cycles):
    return _run_counted(_torus_fns()['csim'], sp, rate, pattern, seed=seed, chain=chain,
                        cycles=cycles)


def torus_a(sp, rate, pattern, seed, chain, cycles):
    f = _torus_fns()
    w = cycles // 4
    if sp == 'dor':
        return _run_counted(f['dor'], rate, pattern, seed=seed, order='random', chain=chain,
                            cycles=cycles, warmup=w)
    return _run_counted(f['sim'], sp, rate, pattern, sel='base', order='random', seed=seed,
                        chain=chain, cycles=cycles, warmup=w)


# ------------------------------------------------------------------ fairness variants (mesh)
# t5a: t5b with the g = 6 mode replaced by g = 5; t5c: both tornado modes
FSETS['t5a'] = XT.MSETS['t5a']
FSETS['t5c'] = XT.MSETS['t5b'] + ['route=wf:tiers=all+esc:thr=g5']


# ------------------------------------------------------------------ driver
CACHE = os.environ.get('XPV_CACHE', os.path.join(tempfile.gettempdir(), 'xp_validate.json'))


def run_one(spec, rate, pattern, seed, chain, cycles):
    kind, _, sp = spec.partition(':')
    if kind == 'MX':
        return mesh_x(sp, rate, pattern, seed, chain, cycles)
    if kind == 'MPX':
        return mesh_px(sp, rate, pattern, seed, chain, cycles)
    if kind == 'MFX':
        return mesh_px(sp, rate, pattern, seed, chain, cycles, fair=True)
    if kind == 'MO1':
        return mesh_o1(rate, pattern, seed, chain, cycles)
    if kind == 'TC':
        return torus_c(sp, rate, pattern, seed, chain, cycles)
    if kind == 'TA':
        return torus_a(sp, rate, pattern, seed, chain, cycles)
    raise ValueError(spec)


def _job(a):
    import time
    t0 = time.time()
    r = run_one(*a[1:])
    return a, r, time.time() - t0


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


def cost(j):
    k, sp, r, p, sd, ch, cyc = j
    w = 2.2 if sp.startswith(('MPX', 'MFX', 'TC')) else 1.6 if sp.startswith('MO1') else 1.0
    return cyc * w * min(1.0, r * 2 + 0.2)


def compute(jobs):
    from multiprocessing import Pool
    res = load()
    todo = [j for j in dict.fromkeys(jobs) if j not in res]
    print(len(todo), 'to run', file=sys.stderr, flush=True)
    if todo:
        todo.sort(key=cost, reverse=True)
        with Pool(int(os.environ.get('XPV_PROCS', 3))) as pool:
            new = {}
            for i, (a, r, dt) in enumerate(pool.imap_unordered(_job, todo, chunksize=1)):
                new[a] = list(r) + [round(dt, 1)]
                if i % 6 == 5 or i == len(todo) - 1:
                    save(new)
                    new = {}
                    print(f'{i + 1}/{len(todo)} last {a} {dt:.0f}s', file=sys.stderr, flush=True)
        save(new)
    return load()


def jobs_of(specs, pats, rates, seeds, chains, cycles):
    return [(KV, sp, float(r), p, sd, ch, int(cycles)) for ch in chains.split(',')
            for sp in specs.split(',') for p in pats.split(',') for r in rates.split(',')
            for sd in X2.seedlist(seeds)]


# ------------------------------------------------------------------ check
def check():
    ok = True
    for chn in ('seq', 'none'):
        a = XT.run_fair('X:route=wf:tiers=xy+esc:thr=g0', 0.4, 'tornado', 3, chn, 900)
        b = mesh_x('route=wf:tiers=xy+esc:thr=g0', 0.4, 'tornado', 3, chn, 900)
        ok &= a == b
        print('xp_transpose F:X / mesh_x', chn, a[:2], a[-2:], b[-2:], a == b)
        a = XT.run_fair('PX:t5b:th=0.7:d=2:elim=0.1', 1.0, 'tornado', 3, chn, 1500)
        b = mesh_px('t5b:th=0.7:d=2:elim=0.1', 1.0, 'tornado', 3, chn, 1500)
        ok &= a == b
        print('xp_transpose F:PX / mesh_px', chn, a[:2], a[-2:], b[-2:], a == b)
        a = XA.run_one('mesh', 'R:duatoMesh:o1turn/random', 0.4, 'bitcomp', 3, chn, 900)
        b = mesh_o1(0.4, 'bitcomp', 3, chn, 900)
        ok &= list(a) == b
        print('o1turn', chn, a[:2], b[:2], list(a) == b)
        for sp in ('dor', 'val', 'ugal'):
            a = XC.run_one('A:' + (sp if sp == 'dor' else sp + '/base'), 0.7, 'tornado', 5, chn, 800)
            b = torus_a(sp, 0.7, 'tornado', 5, chn, 800)
            e = a[:2] == b[:2]
            ok &= e
            print('torus', sp, chn, a[:2], b[:2], b[-2:], e)
        sp = 'hop=price:src=toll:pm=0.2:thr=lx2_4_32_2:thr2=lx2_4_35_2'
        a = XC.run_one('C:' + sp, 0.8, 'hotspot', 5, chn, 800)
        b = torus_c(sp, 0.8, 'hotspot', 5, chn, 800)
        ok &= a == b[:4]
        print('torus combined', chn, a[:2], b[:2], b[-2:], a == b[:4])
        # the fair learner with jmin = 0 is the learner
        a = mesh_px('t5b:th=0.7:d=2:elim=0.1', 1.0, 'tornado', 4, chn, 1500)
        b = mesh_px('t5b:th=0.7:d=2:elim=0.1:jmin=0', 1.0, 'tornado', 4, chn, 1500, fair=True)
        ok &= a == b
        print('FairLearner jmin=0 / learner', chn, a[:2], b[:2], a == b)
    print('ALL OK' if ok else 'MISMATCH')


# ------------------------------------------------------------------ report
NAMES = {'MX:route=wf:tiers=xy+esc:thr=g0': 'XY both VCs', 'MX:route=wf:tiers=all+esc:thr=g0':
         'west-first rand', 'MX:route=duato:tiers=all+esc:thr=g0': 'Duato rand',
         'MX:route=duato:tiers=all+esc:thr=g4': 'Duato T4', 'MO1': 'O1TURN', 'TA:dor': 'dor',
         'TA:val': 'val', 'TA:ugal': 'ugal'}


def cell(res, k, sp, p, ch, cyc, seeds, rates=None):
    """peak over the offered loads (all cached ones with every seed, or `rates`) of the mean over
    the seeds: (mean, se, rate, rows)"""
    have = {}
    for kk, v in res.items():
        if kk[0] == k and kk[1] == sp and kk[3] == p and kk[5] == ch and kk[6] == cyc \
                and kk[4] in seeds and (rates is None or kk[2] in rates):
            have.setdefault(kk[2], {})[kk[4]] = v
    best = None
    for r, d in have.items():
        if len(d) < len(seeds):
            continue
        rows = [d[s] for s in seeds]
        m, se = XP.stats([x[0] for x in rows])
        if best is None or m > best[0]:
            best = (m, se, r, rows)
    return best


def table(k, main, mcyc, pubs, pcyc, pats, chains, seeds, pseeds=None):
    """main vs every published scheme (peak over the cached loads); pubs with their own cycles"""
    res = load()
    pseeds = pseeds or seeds
    z = lambda a, b: (a[0] - b[0]) / max(1e-12, (a[1] ** 2 + b[1] ** 2) ** .5)
    for ch in chains:
        print(f'\n== k={k} {ch}: {main} ({mcyc} cycles, seeds {seeds[0]}..{seeds[-1]}) vs '
              f'published ({pcyc} cycles, seeds {pseeds[0]}..{pseeds[-1]}); '
              'peak mean ± se (1e-4) @offered; fairness min/mean, Jain at the peak')
        for p in pats:
            m = cell(res, k, main, p, ch, mcyc, seeds)
            line = f'{p:<10}'
            if m is None:
                print(line + ' main incomplete')
                continue
            fm = (sum(x[-3] for x in m[3]) / len(m[3]), sum(x[-2] for x in m[3]) / len(m[3])) \
                if len(m[3][0]) >= 7 else None
            sh = ''
            if main.split(':')[0] in ('MPX', 'MFX'):
                nmo = len(m[3][0]) - 8
                sh = ' modes ' + '/'.join(f'{100 * sum(x[5 + i] for x in m[3]) / len(m[3]):.0f}'
                                          for i in range(nmo))
            print(f'{line} MAIN {m[0]:.4f}±{m[1] * 1e4:<4.0f}@{m[2]:<5g}' +
                  (f' fair {fm[0]:.2f}/{fm[1]:.3f}' if fm else '') + sh)
            best = None
            for sp in pubs:
                c = cell(res, k, sp, p, ch, pcyc, pseeds)
                if c is None:
                    print(f'{"":<12}{NAMES.get(sp, sp):<16} incomplete')
                    continue
                fr = (sum(x[-3] for x in c[3]) / len(c[3]), sum(x[-2] for x in c[3]) / len(c[3])) \
                    if len(c[3][0]) >= 7 and sp != 'MO1' else None
                print(f'{"":<12}{NAMES.get(sp, sp):<16} {c[0]:.4f}±{c[1] * 1e4:<4.0f}@{c[2]:<5g}' +
                      (f' fair {fr[0]:.2f}/{fr[1]:.3f}' if fr else '              ') +
                      f'   MAIN {100 * (m[0] / c[0] - 1):+6.2f}% {z(m, c):+7.1f}z')
                if best is None or c[0] > best[1][0]:
                    best = (sp, c)
            if best:
                print(f'{"":<12}{"=> vs best":<16} {NAMES.get(best[0], best[0])}: '
                      f'{100 * (m[0] / best[1][0] - 1):+6.2f}% {z(m, best[1]):+7.1f}z')


def pilot(k, specs, pats, chains, cyc, seeds):
    """per spec / pattern / chain: throughput at every cached load (mean over seeds)"""
    res = load()
    for ch in chains:
        for p in pats:
            print(f'-- k={k} {ch} {p}')
            for sp in specs:
                rs = sorted({kk[2] for kk in res if kk[0] == k and kk[1] == sp and kk[3] == p
                             and kk[5] == ch and kk[6] == cyc})
                cells = []
                for r in rs:
                    v = [res[(k, sp, r, p, sd, ch, cyc)] for sd in seeds
                         if (k, sp, r, p, sd, ch, cyc) in res]
                    if len(v) == len(seeds):
                        cells.append(f'{r:g}:{sum(x[0] for x in v) / len(v):.4f}')
                print(f'   {NAMES.get(sp, sp)[:40]:<40} ' + ' '.join(cells))


def fairpeak(k, ref, rcyc, specs, cyc, p, ch, seeds):
    """every spec at every cached load against `ref` at its own peak: throughput, min/mean, Jain;
    the fair peak = the best load whose mean min/mean and Jain are both at least ref's at its peak"""
    res = load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-12, (a[1] ** 2 + b[1] ** 2) ** .5)
    rc = cell(res, k, ref, p, ch, rcyc, seeds)
    rf = (sum(x[-3] for x in rc[3]) / len(rc[3]), sum(x[-2] for x in rc[3]) / len(rc[3]))
    print(f'== k={k} {p} {ch}, seeds {seeds[0]}..{seeds[-1]}: reference {NAMES.get(ref, ref)} peak '
          f'{rc[0]:.4f}±{rc[1] * 1e4:.0f}@{rc[2]:g} fair {rf[0]:.2f}/{rf[1]:.3f}')
    for sp in specs:
        rs = sorted({kk[2] for kk in res if kk[0] == k and kk[1] == sp and kk[3] == p
                     and kk[5] == ch and kk[6] == cyc})
        cells, fbest, pbest = [], None, None
        for r in rs:
            c = cell(res, k, sp, p, ch, cyc, seeds, rates=[r])
            if c is None:
                continue
            fm = sum(x[-3] for x in c[3]) / len(c[3])
            fj = sum(x[-2] for x in c[3]) / len(c[3])
            cells.append(f'{r:g}:{c[0]:.4f}({fm:.2f}/{fj:.3f})')
            if pbest is None or c[0] > pbest[0][0]:
                pbest = (c, fm, fj)
            if fm >= rf[0] and fj >= rf[1] and (fbest is None or c[0] > fbest[0][0]):
                fbest = (c, fm, fj)
        print(f'  {NAMES.get(sp, sp)[:44]:<44} ' + ' '.join(cells))
        for nm, b in (('peak', pbest), ('fair peak', fbest)):
            if b:
                c = b[0]
                print(f'  {"":<44} {nm:<9} {c[0]:.4f}±{c[1] * 1e4:.0f}@{c[2]:g} fair '
                      f'{b[1]:.2f}/{b[2]:.3f}: {100 * (c[0] / rc[0] - 1):+.2f}% {z(c, rc):+.1f}z vs ref')
            else:
                print(f'  {"":<44} {nm:<9} none')


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'check':
        check()
    elif cmd == 'jobs':
        jobs = []
        with open(sys.argv[2]) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    jobs += jobs_of(*line.split('|'))
        compute(jobs)
    elif cmd == 'table':      # table K MAIN MCYC PUBS PCYC PATS CHAINS SEEDS [PSEEDS]
        a = sys.argv[2:]
        table(int(a[0]), a[1], int(a[2]), a[3].split(','), int(a[4]), a[5].split(','),
              a[6].split(','), X2.seedlist(a[7]), X2.seedlist(a[8]) if len(a) > 8 else None)
    elif cmd == 'pilot':      # pilot K SPECS PATS CHAINS CYCLES SEEDS
        a = sys.argv[2:]
        pilot(int(a[0]), a[1].split(','), a[2].split(','), a[3].split(','), int(a[4]),
              X2.seedlist(a[5]))
    elif cmd == 'fairpeak':   # fairpeak K REF RCYC SPECS CYC PAT CHAIN SEEDS
        a = sys.argv[2:]
        fairpeak(int(a[0]), a[1], int(a[2]), a[3].split(','), int(a[4]), a[5], a[6],
                 X2.seedlist(a[7]))
    elif cmd == 'one':
        import time
        t0 = time.time()
        print(run_one(sys.argv[2], float(sys.argv[3]), sys.argv[4], int(sys.argv[5]),
                      sys.argv[6], int(sys.argv[7])), f'{time.time() - t0:.1f}s')
