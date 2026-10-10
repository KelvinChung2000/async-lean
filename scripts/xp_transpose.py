#!/usr/bin/env python3
"""Transpose and tornado on the 8 x 8 mesh (simulation only; nothing here is proved).

GOAL 1: a mode of the west-first mesh (a tier list containing the throttled escape tier
`escTier k g`, g <= 8; tiers and preferences read only the configuration, the packet's channel
and its destination, so `westFirstTiers_correct` / `westFirstMesh_modes_safe` cover it) that is
strictly better than the published west-first random (`A:R:westFirstMesh:random/random` =
`M:route=wf:tiers=all+esc:thr=g0`) on transpose, and the mesh learner with it added.
GOAL 2: tornado (x -> x + 3 mod 8, same row) with non-minimal schemes.

`xsim` is `xp_combo2.msim` with the `xyc` tier of `xp_portfolio2` and, here, a registry of extra
tiers (`_XT`) and selections (`_XS`), patched textually (each patch must apply exactly once);
with the existing tier names it reproduces msim bit for bit (`check`).  `pxsim` is the same with
the portfolio learner of `xp_portfolio` (mode switching at the start of a cycle).

Specs: `X:<msim spec>` (xsim; extra selections `sel=`: P/Pd/Pv/Pa score maxima, `_bal`/`_unb`/
`_str` tie-breaks, `L0`/`L1` lane rules, `s` suffix = sources uniform, `c-<step>-<step>...`
compositions, `spr<m>`/`cen<m>`), `PX:<set>[:learner opts]` (the learner on pxsim, sets MSETS here
or xp_portfolio's), `G:<scheme>[/g<g>]` / `GX:...` (graph detour network on the mesh, GOAL 2),
anything else `xp_portfolio2.run_one` (`A:`, `M:`, `B:`, `PM:`, `MX:`).

Usage:
  python3 scripts/xp_transpose.py check
  python3 scripts/xp_transpose.py diag SPEC PATTERN RATE SEED CHAIN [CYCLES] [occ/W,mv/N,blk/E,...]
  python3 scripts/xp_transpose.py run SPECS PATTERNS RATES SEEDS CHAINS [CYCLES] [REF]
  python3 scripts/xp_transpose.py jobs FILE          (lines 'specs|pats|rates|seeds|chains|cycles')
  python3 scripts/xp_transpose.py learnrep LEARNER [CYCLES]
Cache XP_TR_CACHE (default xp_transpose.json in the system temporary directory), XP_TR_PROCS
processes (default 3).

FINDINGS (8 x 8, offered-load sweeps, peak of the mean over seeds; seq / none move models)
Diagnosis.  Under transpose the two halves use disjoint links: sources with x > y go west+north
(WN), x < y east+south (ES).  Every packet enters a diagonal node exactly once.  On the west-first
mesh an ES packet may use both lanes of every E/S link, but a WN packet may take N on VC0 only
in its destination column, and that column lies past the diagonal: the N links into the diagonal
have one usable lane (VC1) for WN, the W links two.  So 21 entry lanes serve WN and 28 serve ES;
without chaining a lane passes <= 1/2 packet per cycle, so no west-first scheme exceeds
(10.5 + 14) / 64 = 0.383 (west-first random 0.364 = 95 %; its entry lanes run at 0.94 - 0.99 of
capacity, the corner nodes' lanes the least used).  With chaining the entry lanes pass ~0.7 per
lane per cycle.  WN delivers 0.49 per source, ES 0.61 (seq).  Near-diagonal sources starve
(0.16 - 0.3 / cycle) while far sources get ~1.
What does not work: pushing packets toward the diagonal's corners by s = x + y (`spr`, -5 to
-9 %), towards its centre (`cen`, +-0), straight-on preference, throttles g >= 2, the hop into
the router with the most free channels (`Pa`, D: -0.5 %).
What works: a preference within west-first random's tier [all, esc] (g = 0):
  MODE_T = route=wf:tiers=all+esc:thr=g0:sel=Pd_balL0
  Pd   the hops into the router with the most free productive directions for this packet,
  bal  then the dimension with the larger remaining offset (route near the straight line),
  L0   then VC0 when both lanes of the chosen direction are free (leaves VC1, the only N lane of
       WN traffic before its last column, to others).
  It fills the under-used corner entry lanes (e.g. WN into (0,0): 0.92 -> 1.18 / 0.90 -> 0.98).
  12 fresh seeds (1001-1012), offered 0.6-1.0: transpose 0.4973 / 0.3701 against west-first random
  0.4817 / 0.3645: +3.2 % (z = 93) / +1.5 % (z = 49).  `N_balL0` (no score): +2.5 % / +1.7 %.
  Proof: tiers [T1, all, esc] with T1 the filtered free hops (configuration + own channel +
  destination), escTier k 0: `westFirstTiers_correct`; as a learner mode `westFirstMesh_modes_safe`.
Learner `PX:t4:th=0.7:d=2:elim=0.1` = x4 with W -> MODE_T, 12000 cycles, fresh seeds 1101-1108
(bit complement 1101-1112): strictly ahead of every published scheme on 7 of 8 patterns in both
models (transpose +3.2 % / +1.4 %, uniform +5.9 / +4.4, shuffle +14 / +21, bit reversal +23 / +21,
hotspot +4.5 / +4.5, bit complement +0.8 / +1.7, random permutation +2.9 / +8.5); tornado
-0.03 % / -0.4 % as before.  At 6000 cycles transpose +2.4 % / +0.9 %.
GOAL 2, tornado (seeds 1201-1208 / 1301-1308): on the tree-escape detour network (GraphDetour,
throttle g = 4 scaled by degree): minimal 0.4290 / 0.3192, Valiant 0.3467 / 0.2485, UGAL 0.4114 /
0.2950, row spreading rowv25/50/100 0.4176 / 0.3031 ... 0.3262 / 0.2424, banditx 0.4272 / 0.3156,
against 0.4268 / 0.3182 published: no detour gains.  But on the mesh tornado only E/W lanes are
used, so an escape threshold g <= 4 never binds (the next router's 4 N/S lanes are free); g = 5
gives 0.4359 / 0.3226 (+2.1 % / +1.4 %), g = 6 0.4317 / 0.3345 (+1.1 % / +5.1 %): a throttle that
favours some sources over others (with unequal rates a row can carry 3 instead of 8/3 packets per
cycle without chaining).  Learner t5b (t4 plus the g = 6 mode): tornado +0.6 % / +4.2 %.
Learner t5b on all 8 patterns (`fairrep`; seeds 1401-1408, 1401-1412 for transpose / tornado /
bit complement; published schemes as bit-identical msim specs `F:X:...` with fairness): strictly
ahead of every published scheme on every pattern in both models (smallest: bit complement +0.73 %
z = 7.8 seq, tornado +0.62 % z = 16 seq, transpose +1.38 % z = 37 none).  Fairness (min/mean
per-source injections, Jain) at the peaks is comparable to the best published scheme's except
tornado without chaining (Jain 0.92 against 0.98 for dualXY at its sub-saturation peak 0.34; at
offered 1.0 dualXY is 0.43 / 0.88, the g = 6 mode 0.67 / 0.92) and bit reversal (0.26-0.35 min/mean
against 0.35-0.47 for west-first at its lower peak load).
"""
import inspect
import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import xp_combo2 as X2
import xp_backpressure as XP
import xp_portfolio as PF
import xp_portfolio2 as P2
import xp_bitcomp as BC

K = 8
N = K * K
GHOST = X2.GHOST


def dist(u, d, k=K):
    return abs(u % k - d % k) + abs(u // k - d // k)


# ------------------------------------------------------------------ extra tiers / selections
# A tier factory: f(ctx, c, u, d, src, esc) -> predicate on hops q (free permitted hops of the
# west-first mesh).  A selection: f(ctx, pick, c, u, d, src) -> non-empty sub-list of pick.
# Both may read only ctx['occ'] / ctx['nfree'] (the configuration) and c, u, d.
_XT = {}
_XS = {}


def tier(name):
    def reg(f):
        _XT[name] = f
        return f
    return reg


def selection(name):
    def reg(f):
        _XS[name] = f
        return f
    return reg


def _hop_dir(q):
    return q // 2 % 5


# s = x + y, the anti-diagonal coordinate: E / N raise it, W / S lower it
_DS = (1, -1, 1, -1)


def _spread(m, toward=False):
    """prefer the hops that move s = x + y away from the centre anti-diagonal s = k - 1 (toward
    the corners of the diagonal) when |s - (k - 1)| >= m; `toward`: the opposite (control)"""
    def f(ctx, pick, c, u, d, src):
        k = ctx['k']
        off = u % k + u // k - (k - 1)
        if abs(off) < m or off == 0:
            return pick
        want = (1 if off > 0 else -1) * (-1 if toward else 1)
        p2 = [q for q in pick if _DS[_hop_dir(q)] == want]
        return p2 or pick
    return f


for _m in range(1, 8):
    _XS[f'spr{_m}'] = _spread(_m)
    _XS[f'cen{_m}'] = _spread(_m, True)


def _useful(ctx, q, d):
    """xp_combo2.msim's P-score: free permitted hops of the packet at the next router"""
    v = ctx['hd'][q]
    if v == d:
        return 99
    occ = ctx['occ']
    return sum(1 for x in ctx['RT'][v][d] if x not in occ)


def _pmax(ctx, pick, d):
    sc = [_useful(ctx, q, d) for q in pick]
    top = max(sc)
    return [q for q, y in zip(pick, sc) if y == top]


def _lane0(pick):
    """the same direction weights as a uniform choice among pick, but the VC0 lane whenever both
    lanes of the chosen direction are free (VC1 left to packets that cannot use VC0)"""
    ps = set(pick)
    return [q - 1 if q % 2 == 1 and q - 1 in ps else q for q in pick]


def _lane1(pick):
    ps = set(pick)
    return [q + 1 if q % 2 == 0 and q + 1 in ps else q for q in pick]


_XS['L0'] = lambda ctx, pick, c, u, d, src: _lane0(pick)
_XS['L1'] = lambda ctx, pick, c, u, d, src: _lane1(pick)
_XS['PL0'] = lambda ctx, pick, c, u, d, src: _lane0(_pmax(ctx, pick, d))
_XS['PL1'] = lambda ctx, pick, c, u, d, src: _lane1(_pmax(ctx, pick, d))


def _pscore(ctx, q, d, mode):
    v = ctx['hd'][q]
    if v == d:
        return 99
    occ = ctx['occ']
    hops = ctx['RT'][v][d]
    if mode == 'dir':           # free productive directions at the next router
        return len({x // 2 % 5 for x in hops if x not in occ})
    if mode == 'v1':            # free VC1 hops at the next router
        return sum(1 for x in hops if x % 2 == 1 and x not in occ)
    if mode == 'all':           # free outgoing channels at the next router (any direction)
        return ctx['nfree'][v]
    return sum(1 for x in hops if x not in occ)


def _pmaxm(ctx, pick, d, mode):
    sc = [_pscore(ctx, q, d, mode) for q in pick]
    top = max(sc)
    return [q for q, y in zip(pick, sc) if y == top]


def _offsets(k, v, d):
    return abs(v % k - d % k), abs(v // k - d // k)


def _tiebreak(ctx, pick, c, u, d, how):
    if len(pick) < 2:
        return pick
    k = ctx['k']
    if how == 'str':            # straight on
        p2 = [q for q in pick if _hop_dir(q) == c // 2 % 5]
    elif how in ('bal', 'unb'):  # the dimension with the larger (bal) / smaller (unb) offset
        ax, ay = _offsets(k, u, d)
        if ax == ay:
            return pick
        big = 0 if ax > ay else 1
        want = big if how == 'bal' else 1 - big
        p2 = [q for q in pick if (_hop_dir(q) >= 2) == bool(want)]
    else:
        raise ValueError(how)
    return p2 or pick


def _mksel(mode='free', lane='0', tb='', srcrand=False):
    def f(ctx, pick, c, u, d, src):
        if srcrand and src:
            return pick
        p = _pmaxm(ctx, pick, d, mode) if mode != 'none' else pick
        if tb:
            p = _tiebreak(ctx, p, c, u, d, tb)
        if lane == '0':
            p = _lane0(p)
        elif lane == '1':
            p = _lane1(p)
        return p
    return f


for _mode, _mn in (('free', 'P'), ('dir', 'Pd'), ('v1', 'Pv'), ('all', 'Pa'), ('none', 'N')):
    for _tb in ('', 'str', 'bal', 'unb'):
        for _ln in ('', '0', '1'):
            for _sr in (False, True):
                _nm = _mn + (_tb and '_' + _tb) + ('L' + _ln if _ln else '') + ('s' if _sr else '')
                if _nm != 'P':                 # msim's own sel=P
                    _XS.setdefault(_nm, _mksel(_mode, _ln, _tb, _sr))


def _bal(ctx, pick, c, u, d, m):
    """prefer the dimension with the larger remaining offset when the offsets differ by >= m"""
    k = ctx['k']
    ax, ay = _offsets(k, u, d)
    if abs(ax - ay) < m:
        return pick
    want = ay > ax
    p2 = [q for q in pick if (_hop_dir(q) >= 2) == want]
    return p2 or pick


def _compose(steps):
    """sel=c-<step>-<step>...: filters applied in order (each keeps a non-empty sub-list):
    bal / bal<m> (larger remaining offset, when the offsets differ by >= m), unb, str,
    P / Pd / Pv / Pa (P-score maxima), L0 / L1 (lane), s (sources: stop here, uniform)"""
    def f(ctx, pick, c, u, d, src):
        p = pick
        for st in steps:
            if len(p) < 2:
                break
            if st == 's':
                if src:
                    break
            elif st.startswith('bal'):
                p = _bal(ctx, p, c, u, d, int(st[3:] or 1))
            elif st in ('unb', 'str'):
                p = _tiebreak(ctx, p, c, u, d, st)
            elif st in ('P', 'Pd', 'Pv', 'Pa'):
                p = _pmaxm(ctx, p, d, {'P': 'free', 'Pd': 'dir', 'Pv': 'v1', 'Pa': 'all'}[st])
            elif st == 'L0':
                p = _lane0(p)
            elif st == 'L1':
                p = _lane1(p)
            else:
                raise ValueError(st)
        return p
    return f


class _SelReg(dict):
    def __missing__(self, key):
        raise KeyError(key)

    def __contains__(self, key):
        return dict.__contains__(self, key) or key.startswith('c-')

    def __getitem__(self, key):
        if not dict.__contains__(self, key) and key.startswith('c-'):
            self[key] = _compose(key.split('-')[1:])
        return dict.__getitem__(self, key)


_XS = _SelReg(_XS)


# ------------------------------------------------------------------ patched simulators
_SETUP_OLD = "    def useful(q, d):\n"
_SETUP_NEW = ("    _ctx = dict(occ=occ, nfree=nfree, hd=hd, RT=RT, XY0=XY0, XY1=XY1, YX1=YX1, k=k, "
              "n=n, ch=ch, o=o)\n"
              "    def useful(q, d):\n")
_TIER_OLD = "        raise ValueError(name)\n"
_TIER_NEW = ("        if name in _XT:\n"
             "            return _XT[name](_ctx, c, u, d, src, esc)\n"
             "        raise ValueError(name)\n")
_SEL_OLD = "            if len(pick) > 1 and sel != 'rand':\n"
_SEL_NEW = ("            if len(pick) > 1 and sel in _XS:\n"
            "                pick = _XS[sel](_ctx, pick, c, u, d, src)\n"
            "            elif len(pick) > 1 and sel != 'rand':\n")
# diagnosis counters (module-level _DG dict, single process)
_DIAG = [
    ("            _, born = take(c)\n",
     "            _dd, born = take(c)\n"
     "            if _DG and t >= warmup:\n"
     "                _DG['ej'][_dd] += 1\n"),
    ("        moved = set()\n        vacated = set()\n",
     "        moved = set()\n        vacated = set()\n"
     "        if _DG and t >= warmup:\n"
     "            _DG['T'] += 1\n"
     "            for _c, _v in occ.items():\n"
     "                if _v is not GHOST:\n"
     "                    _DG['occ'][_c] += 1\n"),
    ("                moved.add(c2)\n                if t >= warmup:\n",
     "                moved.add(c2)\n"
     "                if _DG and t >= warmup:\n"
     "                    _DG['mv'][c2] += 1\n"
     "                if t >= warmup:\n"),
]


def _src():
    src = inspect.getsource(X2.msim)
    # blocked packets: insert an else branch to `if pick:` (at its indentation)
    old = ("                if useprice:\n                    pp = c2 // 2 % 5\n"
           "                    if pp < 4:\n                        mvs[c2 // 10, pp] += 1\n")
    new = old + ("            elif _DG and t >= warmup:\n"
                 "                _DG['blk'][c] += 1\n"
                 "                if src:\n"
                 "                    _DG['sblk'][u] += 1\n")
    assert src.count(old) == 1
    return src.replace(old, new)


# per-source injection counts (after warmup) and generated packets (any time), for fairness
_FAIR = [
    ("                    queues[s].append((d, t))\n",
     "                    queues[s].append((d, t))\n"
     "                    _GEN[s] += 1\n"),
    ("                put(ch(s, 4, 0), queues[s].popleft())\n",
     "                put(ch(s, 4, 0), queues[s].popleft())\n"
     "                if t >= warmup:\n"
     "                    _INJ[s] += 1\n"),
]


def _build(extra, name):
    fn, ns = P2._patched(_src(), [(_SETUP_OLD, _SETUP_NEW), (_TIER_OLD, _TIER_NEW),
                                  (_SEL_OLD, _SEL_NEW)] + _DIAG + _FAIR + extra, name)
    ns.update(_INJ=[0] * N, _GEN=[0] * N)
    return fn, ns


def fairness(ns):
    """(min / mean, Jain's index) of the per-source injections after warmup, over the sources
    that generated traffic"""
    v = [i for i, g in zip(ns['_INJ'], ns['_GEN']) if g > 0]
    m = sum(v) / len(v)
    return min(v) / max(1e-9, m), sum(v) ** 2 / max(1e-9, len(v) * sum(x * x for x in v))


def run_fair(spec, rate, pattern, seed, chain, cycles):
    """F:X:<msim spec> or F:PX:<learner>: the result plus [min/mean, Jain]"""
    kind, _, sp = spec.partition(':')
    ns = (pxsim_fn() if kind == 'PX' else xsim_fn())[1]
    ns['_INJ'][:] = [0] * N
    ns['_GEN'][:] = [0] * N
    r = list(run_one(spec, rate, pattern, seed, chain, cycles))
    return r + list(fairness(ns))


_X = None


def xsim_fn():
    global _X
    if _X is None:
        _X = _build([], 'msim')
        _X[1].update(_XT=_XT, _XS=_XS, _DG=None)
    return _X


_PX = None


def pxsim_fn():
    """the learner version (xp_portfolio2.pmsim2_fn's patches)"""
    global _PX
    if _PX is None:
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
        ]
        _PX = _build(extra, 'pmsim')
        _PX[1].update(_XT=_XT, _XS=_XS, _DG=None)
    return _PX


def xsim(spec, rate, pattern, seed=1, chain='seq', cycles=2000, warmup=None):
    fn, ns = xsim_fn()
    return fn(spec, rate, pattern, seed=seed, chain=chain, cycles=cycles, warmup=warmup)


# the new transpose mode: west-first random's tier list [all, esc], g = 0, with a preference
# within the tier (configuration, own channel and destination only):
#   Pd   the hops into the router with the most free productive directions for this packet,
#   bal  then the dimension with the larger remaining offset,
#   L0   then the VC0 lane when both lanes of the chosen direction are free.
MODE_T = 'route=wf:tiers=all+esc:thr=g0:sel=Pd_balL0'
MODE_T2 = 'route=wf:tiers=all+esc:thr=g0:sel=N_balL0'
MSETS = {
    't4': [PF.MESH_B, MODE_T, P2.XPRIME, P2.MODE_P],                 # x4 with W -> MODE_T
    't5': [PF.MESH_B, P2.MODE_W, MODE_T, P2.XPRIME, P2.MODE_P],      # x4 plus MODE_T (d=3: X')
    't4n': [PF.MESH_B, MODE_T2, P2.XPRIME, P2.MODE_P],
    # plus a tornado mode: west-first random with escape threshold g = 5 / 6 (on tornado only
    # E/W lanes are used, so g <= 4 never binds: the 4 N/S lanes of the next router are free)
    't5a': [PF.MESH_B, MODE_T, P2.XPRIME, P2.MODE_P, 'route=wf:tiers=all+esc:thr=g5'],
    't5b': [PF.MESH_B, MODE_T, P2.XPRIME, P2.MODE_P, 'route=wf:tiers=all+esc:thr=g6'],
}


def pm_run(spec, rate, pattern, seed, chain, cycles):
    """xp_portfolio.pm_run on pxsim (modes from MSETS here or xp_portfolio.MSETS)"""
    toks = spec.split(':')
    modes = MSETS.get(toks[0]) or PF.MSETS[toks[0]]
    lo = PF.lparse(toks[1:])
    fn, ns = pxsim_fn()
    warmup = cycles // 3
    L = PF.Learner(len(modes), seed, warmup, **lo)
    ns['_PF'].update(L=L, modes=[PF.mesh_mode(m) for m in modes],
                     useprice=any(X2.mparse(m)['sel'] == 'price' for m in modes))
    r = fn(modes[L.cur], rate, pattern, seed=seed, chain=chain, cycles=cycles, warmup=warmup)
    tot = max(1, sum(L.time))
    return [r[0], r[1], 0.0, 0.0, L.switches] + [x / tot for x in L.time]


# ------------------------------------------------------------------ diagnosis
DIRN = ['E', 'W', 'N', 'S']


def diagnose(spec, pattern, rate, seed, chain, cycles=6000):
    fn, ns = xsim_fn()
    dg = dict(ej=[0] * N, occ=[0] * (N * 10), mv=[0] * (N * 10), blk=[0] * (N * 10),
              sblk=[0] * N, T=0)
    ns['_DG'] = dg
    try:
        r = fn(spec, rate, pattern, seed=seed, chain=chain, cycles=cycles)
    finally:
        ns['_DG'] = None
    T = dg['T']
    print(f'{spec} {pattern} @{rate} {chain}: throughput {r[0]:.4f} latency {r[1]:.0f} '
          f'chained {r[3]:.2f}')
    if pattern == 'transpose':
        wn = sum(dg['ej'][d] for d in range(N) if d % K < d // K)
        es = sum(dg['ej'][d] for d in range(N) if d % K > d // K)
        print(f'  delivered per active source per cycle: WN half (x>y: west+north) '
              f'{wn / T / 28:.4f}, ES half (x<y: east+south) {es / T / 28:.4f}')
        # per-source rate map
        print('  per-source delivered rate (row y = 7 at top; source (x, y))')
        for y in range(K - 1, -1, -1):
            row = []
            for x in range(K):
                s = y * K + x
                dd = x * K + y
                row.append(f'{dg["ej"][dd] / T:6.3f}' if dd != s else '   -  ')
            print('   ' + ' '.join(row))
    if pattern == 'transpose':
        # moves per cycle on the links entering each diagonal node (both lanes)
        hd = X2.tables(K, 'wf')[1]
        mvl = lambda u, dr: sum(dg['mv'][(u * 5 + dr) * 2 + vc] for vc in (0, 1)) / T
        wn = [(mvl(z * K + z + 1, 1) if z < K - 1 else 0, mvl((z - 1) * K + z, 2) if z else 0)
              for z in range(K)]
        es = [(mvl(z * K + z - 1, 0) if z else 0, mvl((z + 1) * K + z, 3) if z < K - 1 else 0)
              for z in range(K)]
        print('  entering diagonal node z: WN (W-in + N-in), ES (E-in + S-in), moves/cycle')
        print('   z   ' + ''.join(f'{z:>12}' for z in range(K)))
        print('   WN  ' + ''.join(f'{a:>6.2f}{b:>6.2f}' for a, b in wn) +
              f'   total {sum(a + b for a, b in wn):.2f}')
        print('   ES  ' + ''.join(f'{a:>6.2f}{b:>6.2f}' for a, b in es) +
              f'   total {sum(a + b for a, b in es):.2f}')
    # per (dir, vc): mean occupancy, moves per cycle per lane, P(blocked | occupied)
    print(f'  {"dir vc":<8}{"occ":>7}{"moves":>8}{"blk|occ":>9}')
    for dr in range(5):
        for vc in (0, 1) if dr < 4 else (0,):
            cs = [(u * 5 + dr) * 2 + vc for u in range(N)
                  if dr == 4 or 0 <= X2.tables(K, 'wf')[1][(u * 5 + dr) * 2 + vc] < N and
                  (dr > 1 or X2.tables(K, 'wf')[1][(u * 5 + dr) * 2 + vc] // K == u // K)]
            oc = sum(dg['occ'][c] for c in cs)
            mv = sum(dg['mv'][c] for c in cs)
            bl = sum(dg['blk'][c] for c in cs)
            name = (DIRN[dr] if dr < 4 else 'inj') + str(vc)
            print(f'  {name:<8}{oc / T / len(cs):>7.3f}{mv / T / len(cs):>8.3f}'
                  f'{bl / max(1, oc):>9.3f}')
    return dg


def linkmap(dg, dr, what='occ'):
    """grid of a per-link quantity (both lanes summed) for direction dr"""
    T = dg['T']
    print(f'  {what} {DIRN[dr]} (both lanes), row y = 7 at top')
    for y in range(K - 1, -1, -1):
        row = []
        for x in range(K):
            u = y * K + x
            v = sum(dg[what][(u * 5 + dr) * 2 + vc] for vc in (0, 1))
            row.append(f'{v / T:5.2f}')
        print('   ' + ' '.join(row))


# ------------------------------------------------------------------ GOAL 2: graph detour on the mesh
# xp_backpressure.sim (= torus_experiments.sim: VC1 minimal adaptive towards the target, VC0
# up*/down* spanning-tree escape towards the final destination, return budget B = 2, source
# throttle g, intermediates chosen at the source) on the 8 x 8 mesh (TOPO=mesh), with the
# no-chaining move model of xp_arbiter (the same patches as xp_arbiter.torus_sim).
# Spec `G:<scheme>[/g<g>][/<sel>]` (scheme: min, val, ugal, banditx..., cmb...; the long way round
# does not exist on the mesh).  `GX:...` the same with the XY escape (Net(escape='xy')): Duato's
# mesh plus intermediates (not a GraphData tree escape; for comparison only).
_GSIM = {}


def gsim_fn(escape='updown', topo='mesh'):
    """escape: updown (spanning tree, root 27) or xy; topo: mesh or torus (torus + updown is
    xp_arbiter.torus_sim, for the check).  Extra scheme `rowv<p>`: with probability p % the
    source picks an intermediate in its own column and a uniformly random other row (Valiant
    spreading of the x travel over the rows between)."""
    if (escape, topo) in _GSIM:
        return _GSIM[(escape, topo)]
    import routing_graph_sim as G
    import xp_arbiter as XA
    adj = G.mesh_adj(K) if topo == 'mesh' else G.torus_adj(K)
    net = (G.Net(adj, escape='updown', root=27) if escape == 'updown'
           else G.Net(adj, escape='xy', k=K))
    base = dict(vars(XP))
    base.update(TOPO=topo, NET=net)
    fn = XA.patched(XP.sim, [
        ("                if scheme == 'val':\n                    inter = rnd.randrange(N)\n",
         "                if scheme == 'val':\n                    inter = rnd.randrange(N)\n"
         "                elif scheme.startswith('rowv'):\n"
         "                    if rnd.random() < int(scheme[4:]) / 100:\n"
         "                        inter = s % K + (s // K + 1 + rnd.randrange(K - 1)) % K * K\n"),
        ("sel='base', order='random'):", "sel='base', order='random', chain='seq'):"),
        ('        for c in pks:\n', '        for c in passes(pks, occ, moved, chain):\n'),
        ('            occ[q] = occ.pop(c); moved.add(q)\n',
         '            occ[q] = occ.pop(c); moved.add(q)\n'
         '            if chain == "none": occ[c] = GHOST\n'),
        ("        if order == 'rr':",
         '        ' + XA.CLEAN.format(i='        ', take='del occ[_c]') + "        if order == 'rr':"),
    ], base)
    _GSIM[(escape, topo)] = fn
    return fn


def grun(spec, rate, pattern, seed, chain, cycles):
    kind, _, sp = spec.partition(':')
    parts = sp.split('/')
    scheme, g, sel = parts[0], 4, 'base'
    for p in parts[1:]:
        if p.startswith('g') and p[1:].isdigit():
            g = int(p[1:])
        else:
            sel = p
    fn = gsim_fn('xy' if kind == 'GX' else 'updown')
    return list(fn(scheme, rate, pattern, g=g, sel=sel, seed=seed, chain=chain, cycles=cycles,
                   warmup=cycles // 3))


# ------------------------------------------------------------------ driver
CACHE = os.environ.get('XP_TR_CACHE', os.path.join(tempfile.gettempdir(), 'xp_transpose.json'))


def run_one(spec, rate, pattern, seed, chain='seq', cycles=2000):
    kind, _, sp = spec.partition(':')
    if kind == 'X':
        return list(xsim(sp, rate, pattern, seed=seed, chain=chain, cycles=cycles))
    if kind == 'PX':
        return pm_run(sp, rate, pattern, seed, chain, cycles)
    if kind == 'F':
        return run_fair(sp, rate, pattern, seed, chain, cycles)
    if kind in ('G', 'GX'):
        return grun(spec, rate, pattern, seed, chain, cycles)
    return P2.run_one(spec, rate, pattern, seed, chain, cycles)


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
    todo = [j for j in dict.fromkeys(jobs) if j not in res]
    print(len(todo), 'to run', file=sys.stderr, flush=True)
    if todo:
        todo.sort(key=lambda j: (j[5], j[0].startswith('P')), reverse=True)
        with Pool(int(os.environ.get('XP_TR_PROCS', 3))) as pool:
            new = {}
            for i, (a, r) in enumerate(pool.imap_unordered(_job, todo, chunksize=1)):
                new[a] = list(r)
                if i % 12 == 11:
                    save(new)
                    new = {}
                    print(f'{i + 1}/{len(todo)}', file=sys.stderr, flush=True)
        save(new)
    return load()


def cell(res, spec, pattern, rates, seeds, chain, cycles):
    best = None
    for r in rates:
        v = [res.get((spec, r, pattern, s, chain, cycles)) for s in seeds]
        v = [x for x in v if x is not None]
        if len(v) < len(seeds):
            continue
        m, se = XP.stats([x[0] for x in v])
        if best is None or m > best[0]:
            best = (m, se, r, len(v))
    return best


def run_cmd(argv):
    """run SPECS PATTERNS RATES SEEDS CHAINS [CYCLES] [REF]: peak over RATES; vs REF"""
    specs, pats, rates, seeds, chains = argv[:5]
    cycles = int(argv[5]) if len(argv) > 5 else 6000
    ref = argv[6] if len(argv) > 6 else None
    specs, chains, pats = specs.split(','), chains.split(','), X2.pats_of(pats)
    if ref and ref not in specs:
        specs = [ref] + specs
    rates = [float(x) for x in rates.split(',')]
    seeds = X2.seedlist(seeds)
    res = compute([(sp, r, p, sd, ch, cycles) for ch in chains for sp in specs for p in pats
                   for r in rates for sd in seeds])
    z = lambda a, b: (a[0] - b[0]) / max(1e-12, (a[1] ** 2 + b[1] ** 2) ** .5)
    print(f'seeds {seeds[0]}..{seeds[-1]} ({len(seeds)}), rates {rates}, cycles {cycles}: '
          'peak mean ± se (x1e-4) @rate' + (f'  [% and z vs {ref}]' if ref else ''))
    for ch in chains:
        print(f'{ch:<5}{"":<52}' + ''.join(f'{p[:9]:>28}' for p in pats))
        for sp in specs:
            cells = []
            for p in pats:
                c = cell(res, sp, p, rates, seeds, ch, cycles)
                s = f'{c[0]:.4f}±{c[1] * 1e4:<3.0f}@{c[2]:g}'
                if ref and sp != ref:
                    rc = cell(res, ref, p, rates, seeds, ch, cycles)
                    s += f' {100 * (c[0] / rc[0] - 1):+5.2f}% {z(c, rc):+5.1f}z'
                cells.append(s)
            print(f'{ch:<5}{sp[-52:]:<52}' + ''.join(f'{x:>28}' for x in cells), flush=True)


def check():
    ok = True
    for chn in ('seq', 'none'):
        for sp, p, r in (('route=wf:tiers=all+esc:thr=g0', 'transpose', 0.8),
                         ('route=wf:tiers=str+esc+vc1:sel=P:gdev=2:devset=all', 'uniform', 0.6),
                         (P2.XPRIME, 'bitcomp', 0.3), (P2.MODE_P, 'shuffle', 0.6)):
            a = (P2.xmsim_fn()(sp, r, p, seed=3, chain=chn, cycles=900) if 'xyc' in sp
                 else X2.msim(sp, r, p, seed=3, chain=chn, cycles=900))
            b = xsim(sp, r, p, seed=3, chain=chn, cycles=900)
            ok &= tuple(a) == tuple(b)
            print('msim / xsim', chn, sp, p, a[:2], b[:2], tuple(a) == tuple(b))
        a = X2.run_one('A:R:westFirstMesh:random/random', 0.8, 'transpose', 4, chn, 900)
        b = xsim('route=wf:tiers=all+esc:thr=g0', 0.8, 'transpose', seed=4, chain=chn, cycles=900)
        ok &= tuple(a[:2]) == tuple(b[:2])
        print('published WF / xsim', chn, a[:2], b[:2])
        a = P2.run_one('PM:x4:th=0.7:d=2', 1.0, 'transpose', 3, chn, 1500)
        b = run_one('PX:x4:th=0.7:d=2', 1.0, 'transpose', 3, chn, 1500)
        ok &= list(a) == list(b)
        print('PM:x4 / PX:x4', chn, a[:2], b[:2], list(a) == list(b))
    import xp_arbiter as XA
    for chn in ('seq', 'none'):
        a = XA.torus_sim('ugal', 0.6, 'tornado', sel='base', order='random', seed=5, chain=chn,
                         cycles=800, warmup=200)
        b = gsim_fn('updown', 'torus')('ugal', 0.6, 'tornado', seed=5, chain=chn, cycles=800,
                                       warmup=200)
        ok &= tuple(a) == tuple(b)
        print('torus ugal: xp_arbiter / gsim', chn, a[:2], b[:2], tuple(a) == tuple(b))
    print('ALL OK' if ok else 'MISMATCH')


# the fresh-seed evaluation of the learner (`jobs` file in the report; seeds 1101-1108,
# bit complement 1101-1112): pattern -> chain -> (learner rates, [(published spec, rates)])
_DX, _WF, _DR = 'A:R:dualXY:random/random', 'A:R:westFirstMesh:random/random', \
    'A:R:duatoMesh:random/random'
LPLAN = {
    'uniform': {'seq': ([1.0], [(_DX, [1.0], 6000)]), 'none': ([0.75, 1.0], [(_DX, [1.0], 6000)])},
    'transpose': {c: ([0.75, 1.0], [(_WF, [0.75, 1.0], 12000)]) for c in ('seq', 'none')},
    'shuffle': {c: ([1.0], [(_WF, [1.0], 6000)]) for c in ('seq', 'none')},
    'bitrev': {'seq': ([0.75], [(_WF, [0.4, 0.42, 0.45], 6000)]),
               'none': ([0.4, 0.45], [(_WF, [0.28, 0.3, 0.32], 6000)])},
    'hotspot': {'seq': ([0.6, 1.0], [(_DR, [0.44, 0.46], 6000)]),
                'none': ([0.45, 1.0], [(_DR, [0.32, 0.34], 6000)])},
    'bitcomp': {'seq': ([0.31, 0.32], [(_DX, [0.31, 0.32], 6000)]),
                'none': ([0.24, 0.25], [(_DX, [0.24, 0.25], 6000)])},
    'tornado': {'seq': ([0.7], [(_DX, [0.7], 12000)]), 'none': ([0.33, 0.34], [(_DX, [0.33, 0.34], 12000)])},
    'randperm': {c: ([1.0], [(_DX, [1.0], 6000)]) for c in ('seq', 'none')},
}


def learn_report(main, cycles=12000):
    res = load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-12, (a[1] ** 2 + b[1] ** 2) ** .5)
    for ch in ('seq', 'none'):
        print(f'\n== {ch}: {main} ({cycles} cycles) against the best published scheme, peak over '
              'the offered loads, fresh seeds')
        for p, d in LPLAN.items():
            lr, pubs = d[ch]
            seeds = list(range(1101, 1113 if p == 'bitcomp' else 1109))
            m = cell(res, main, p, lr, seeds, ch, cycles)
            for sp, rs, cyc in pubs:
                b = cell(res, sp, p, rs, seeds, ch, cyc)
                if m and b:
                    sh = ''
                    v = [res[(main, m[2], p, sd, ch, cycles)] for sd in seeds]
                    if len(v[0]) > 5:
                        sh = ' modes ' + '/'.join(f'{100 * sum(x[5 + i] for x in v) / len(v):.0f}'
                                                  for i in range(len(v[0]) - 5))
                    print(f'{p:<10} learner {m[0]:.4f}±{m[1] * 1e4:<3.0f}@{m[2]:<5g} '
                          f'{sp.split(":")[2]:<14} {b[0]:.4f}±{b[1] * 1e4:<3.0f}@{b[2]:<5g} '
                          f'{100 * (m[0] / b[0] - 1):+6.2f}% {z(m, b):+6.1f}z{sh}')


# the t5b evaluation (seeds 1401-1408; 1401-1412 for transpose, tornado, bit complement):
# pattern -> chain -> [(spec, rates, cycles)], the learner first
_FL = 'F:PX:t5b:th=0.7:d=2:elim=0.1'
_FDX, _FWF = 'F:X:route=wf:tiers=xy+esc:thr=g0', 'F:X:route=wf:tiers=all+esc:thr=g0'
_FDR, _FT4 = 'F:X:route=duato:tiers=all+esc:thr=g0', 'F:X:route=duato:tiers=all+esc:thr=g4'
PUBNAME = {_FDX: 'dualXY', _FWF: 'westFirstMesh', _FDR: 'duatoMesh rand', _FT4: 'duatoMesh T4'}
FPLAN = {
    'uniform': {'seq': [(_FL, [1.0], 12000), (_FDX, [0.75, 1.0], 6000), (_FDR, [0.46, 0.48, 0.5], 6000),
                        (_FT4, [0.75, 1.0], 6000)],
                'none': [(_FL, [0.75, 1.0], 12000), (_FDX, [0.75, 1.0], 6000),
                         (_FDR, [0.33, 0.35, 0.37], 6000), (_FT4, [0.75, 1.0], 6000)]},
    'transpose': {c: [(_FL, [0.75, 1.0], 12000), (_FWF, [0.75, 1.0], 12000)] for c in ('seq', 'none')},
    'shuffle': {c: [(_FL, [1.0], 12000), (_FWF, [0.75, 1.0], 6000)] for c in ('seq', 'none')},
    'bitrev': {'seq': [(_FL, [0.75], 12000), (_FWF, [0.4, 0.42, 0.44, 0.46], 6000),
                       (_FDR, [0.38, 0.4], 6000), (_FT4, [0.75, 1.0], 6000)],
               'none': [(_FL, [0.4, 0.45], 12000), (_FWF, [0.28, 0.3, 0.32, 0.34, 0.36], 6000),
                        (_FDR, [0.28, 0.3], 6000), (_FT4, [0.75, 1.0], 6000)]},
    'hotspot': {'seq': [(_FL, [0.6, 1.0], 12000), (_FDR, [0.44, 0.46, 0.48, 0.5], 6000),
                        (_FT4, [0.6, 1.0], 6000)],
                'none': [(_FL, [0.45, 1.0], 12000), (_FDR, [0.32, 0.34, 0.36, 0.38], 6000),
                         (_FT4, [0.6, 1.0], 6000)]},
    'bitcomp': {'seq': [(_FL, [0.31, 0.32], 12000), (_FDX, [0.31, 0.32, 0.33], 6000)],
                'none': [(_FL, [0.24, 0.25], 12000), (_FDX, [0.23, 0.24, 0.25], 6000)]},
    'tornado': {'seq': [(_FL, [0.7, 1.0], 12000), (_FDX, [0.43, 0.7], 12000)],
                'none': [(_FL, [0.33, 0.34, 1.0], 12000), (_FDX, [0.33, 0.34, 0.35], 12000)]},
    'randperm': {c: [(_FL, [1.0], 12000), (_FDX, [0.75, 1.0], 6000)] for c in ('seq', 'none')},
}


def fair_report():
    res = load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-12, (a[1] ** 2 + b[1] ** 2) ** .5)
    for ch in ('seq', 'none'):
        print(f'\n== {ch}: learner t5b (12000 cycles) vs every published scheme at its peak; '
              'fairness = min/mean per-source injections, Jain (mean over seeds, at the peak)')
        for p, d in FPLAN.items():
            seeds = list(range(1401, 1413 if p in ('transpose', 'tornado', 'bitcomp') else 1409))
            rows = []
            for sp, rs, cyc in d[ch]:
                c = cell(res, sp, p, rs, seeds, ch, cyc)
                if c is None:
                    rows.append(None)
                    continue
                v = [res[(sp, c[2], p, sd, ch, cyc)] for sd in seeds]
                fm = sum(x[-2] for x in v) / len(v)
                fj = sum(x[-1] for x in v) / len(v)
                sh = ''
                if sp.startswith('F:PX'):
                    nm = len(v[0]) - 7
                    sh = ' modes ' + '/'.join(f'{100 * sum(x[5 + i] for x in v) / len(v):.0f}'
                                              for i in range(nm))
                rows.append((c, fm, fj, sh))
            L = rows[0]
            if L is None:
                print(f'{p:<10} (incomplete)')
                continue
            print(f'{p:<10} t5b {L[0][0]:.4f}±{L[0][1] * 1e4:<3.0f}@{L[0][2]:<5g} '
                  f'fair {L[1]:.2f}/{L[2]:.3f}{L[3]}')
            for (sp, rs, cyc), r in zip(d[ch][1:], rows[1:]):
                if r is None:
                    print(f'{"":<10}   {PUBNAME[sp]:<15} (incomplete)')
                    continue
                print(f'{"":<10}   {PUBNAME[sp]:<15} {r[0][0]:.4f}±{r[0][1] * 1e4:<3.0f}@{r[0][2]:<5g}'
                      f' fair {r[1]:.2f}/{r[2]:.3f}   t5b {100 * (L[0][0] / r[0][0] - 1):+6.2f}% '
                      f'{z(L[0], r[0]):+6.1f}z')


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'check':
        check()
    elif cmd == 'diag':
        a = sys.argv[2:]
        dg = diagnose(a[0], a[1], float(a[2]), int(a[3]), a[4], int(a[5]) if len(a) > 5 else 6000)
        for w in a[6].split(',') if len(a) > 6 else ():
            what, dr = w.split('/')
            linkmap(dg, DIRN.index(dr), what)
    elif cmd == 'run':
        run_cmd(sys.argv[2:])
    elif cmd == 'fairrep':
        fair_report()
    elif cmd == 'learnrep':
        learn_report(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 12000)
    elif cmd == 'jobs':          # jobs FILE: lines 'specs|pats|rates|seeds|chains|cycles'
        jobs = []
        with open(sys.argv[2]) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    jobs += P2.jobs_of(*line.split('|'))
        compute(jobs)
