#!/usr/bin/env python3
"""The torus combined scheme scaled to 16 x 16 (simulation only; the routing it simulates is
covered by the torus theorems listed under Safety).

At 16 x 16 the combined scheme of `xp_combo.py` (`C:hop=price:src=toll:pm=0.2:thr=lx2_4_32_2:
thr2=lx2_4_35_2`, tuned at 8 x 8) collapses past its knee (uniform 0.30 at offered 0.3, 0.17 at
1.0; random permutation 0.29 -> 0.10 at 0.4), and so do the published schemes (Valiant past
~0.15, UGAL past ~0.2 to 0.3; dimension order is flat but low).  The collapse is the escape tree
saturating: the `lx` throttle's high threshold 4 (of 8 free outputs at the next router) does
not hold the sources back enough on the larger network.

The scaled scheme (k = grid size; at k = 8 every parameter is the published one):
  hop=price:src=toll:pm=0.2                      unchanged (prices, tolls, long-way and random
                                                 intermediates scale by themselves)
  thr  = lx2_<hi1>_32_<r>   concentrated sources (<= 2 recent destinations)
  thr2 = lx2_<hi2>_35_<r>   spread-out sources
  r = k / 4 (ball radius), hi1 = min(8, 2 + k / 4), hi2 = min(8, k / 2)
  lm = lx2_<hi1>_32_<r>+lx2_<hi1>_<o2>_<r>:lE=250:lS=50:lR=1, o2 = 28 + k / 2
      a network-wide mode-switching learner (xp_portfolio.Learner: congestion gate 0.7,
      epochs of 250 cycles, 50 settling cycles, one exploration round, default mode 0) choosing
      the concentrated sources' share threshold, 32 % or o2, by delivered packets per epoch.
  At k = 16: TD:hop=price:src=toll:pm=0.2:thr=lx2_6_32_4:thr2=lx2_8_35_4:
             lm=lx2_6_32_4+lx2_6_36_4:lE=250:lS=50:lR=1
  At k = 8 both modes are lx2_4_32_2, the learner is inert (`check`: bit for bit the scheme
  without it), so the scheme is exactly the published combined scheme (TC:...).
Why each part (16 x 16, seed-1 pilots, 3000 cycles): hi1 = hi2 = 6, r = 4 removes the collapse
(uniform 0.30 at 1.0, random permutation 0.31, bit complement 0.17 against 0.09 to 0.13); hi2 = 8
adds +3 to +9 % under hotspot; no single share threshold for concentrated sources serves both
transpose (wants 36 to 40 %: 0.25 / 0.18 against 0.22 / 0.17 at 32 %) and random permutation
(collapses at 36 to 40 %: 0.23 / 0.10), hence the learner.  hi1 = 5 or 8, o = 25, 34, radius 2
or 3 and a learner over 32 / 40 % were worse somewhere.

Simulator: `csim16` = xp_combo.csim patched textually (every patch applies exactly once) with
  xp_validate's per-source injection counters (fairness), diagnostics (escape share of the
  occupied link channels, link occupancy, share of source-cycles in the throttle's high mode)
  and the learner `lm` (the concentrated controller is swapped; deliveries and injection-channel
  occupancy feed xp_portfolio.Learner; only the controller in force ticks).
Specs (key = (k, spec, rate, pattern, seed, chain, cycles), cache XPV_CACHE):
  TD:<xp_combo spec>[:lm=A+B..:lE:lS:lR:lth:ld]  -> [thr, hops, long-way share, random-
      intermediate share, escape share, occupancy, high-mode share, (switches, time shares),
      min/mean, Jain]
  TC: / TA:dor|val|ugal   as xp_validate (TA: random arbitration, g = 4 as published)
Published schemes are swept per pattern and move model on a fine grid with one pilot seed
(dor 0.04 to 1.0, val 0.05 to 0.3, ugal 0.1 to 1.0, steps of 0.025 near the knees), then re-run on
fresh seeds at their best pilot loads plus the midpoints next to the best (`topjobs ... knee|up`);
each is reported at the peak over those loads of its mean over the fresh seeds.

Usage:  python3 scripts/xp_torus16.py K CMD ...      (K = grid size; resizing as xp_validate)
  K check              k = 8 bit-identity of TD with xp_validate's TC
  K jobs FILE          lines 'specs|pats|rates|seeds|chains|cycles' (as xp_validate)
  K topjobs SPECS PATS CHAINS PCYC PSEED N SEEDS CYC [EXTRA [knee|up]]
  K pilot SPECS PATS CHAINS CYCLES SEEDS
  K report MAIN MCYC PCYC CHAINS SEEDS PSEEDS
  K one SPEC RATE PAT SEED CHAIN CYCLES
Cache XPV_CACHE (as xp_validate), XPV_PROCS processes.

Safety (Lean, AsyncLean/Examples/Strategy.lean, every k): the price-chosen minimal hops and the
toll-chosen intermediates (long way, random) are any history-dependent choice on the detour
network (`torus_choice_safe`, `torus_price_safe`); the two `lx` controllers with any
neighbourhood (radius r), any share threshold and lo, hi <= 8, read from the start-of-cycle
snapshot, with the per-source spread flag, are `torus_combo_safe`; the learner chooses, from
history (deliveries, injection-channel occupancy), which of two such thresholds is in force, a
history-dependent threshold <= 8 with lxBlock-style escape blocking, i.e. `torus_throttle_safe`
(thr h f s <= 8, any block).  Not covered, as for every torus result here: the simulator's escape
is up*/down* routing over BFS levels from the root (k/2 - 1)(k + 1), while `torus k` in Lean has
the comb tree rooted at (0, 0) (tree-edge routing only); the no-chaining model is a different
scheduling of the same moves.

FINDINGS (simulation; scheme fixed on pilot seed 1, evaluated on fresh seeds 11-14, 3000 cycles
with 750 warmup for every scheme, random arbitration; MAIN at its peak over offered 0.3, 0.4, 1.0;
published at the peak over their fine-swept loads, see above)
16 x 16, sequential moves: MAIN vs the best published at its own peak (mean ± se, z):
  uniform    0.3079±22 vs UGAL 0.2495±1 @0.25    +23.4 %  z 27
  transpose  0.2470±6  vs UGAL 0.2275±11 @0.275  +8.6 %   z 16
  shuffle    0.2942±16 vs UGAL 0.1883±11 @0.2    +56 %    z 53
  bit rev.   0.2812±16 vs UGAL 0.2227±1 @0.2375  +26 %    z 37
  bit comp.  0.1712±4  vs UGAL 0.1375±2 @0.1375  +24 %    z 70
  hotspot    0.1361±6  vs UGAL 0.1303±5 @0.15    +4.5 %   z 7.0
  tornado    0.1786±5  vs Valiant 0.1501±2 @0.15 +19 %    z 52
  random p.  0.3122±14 vs UGAL 0.2461±2 @0.25    +27 %    z 48
  neighbour  1.0 = dimension order 1.0 (injection limit); UGAL 0.9938, Valiant 0.64
16 x 16, no chaining:
  uniform    0.2402±8  vs UGAL 0.1878±2 @0.1875  +28 %    z 64
  transpose  0.1844±7  vs UGAL 0.1735±5 @0.2     +6.2 %   z 13
  shuffle    0.2159±9  vs UGAL 0.1457±17 @0.15   +48 %    z 37
  bit rev.   0.2092±6  vs UGAL 0.1639±3 @0.175   +28 %    z 68
  bit comp.  0.1328±3  vs UGAL 0.1002±1 @0.1     +33 %    z 110
  hotspot    0.1140±2  vs UGAL 0.1073±6 @0.15    +6.2 %   z 9.9
  tornado    0.1364±3  vs UGAL 0.1227±6 @0.125   +11 %    z 22
  random p.  0.2410±7  vs UGAL 0.1842±0 @0.1875  +31 %    z 77
  neighbour  1.0 = dimension order 1.0; UGAL 0.9880, Valiant 0.52
Fairness at the peaks (min/mean, Jain): MAIN's peak is past saturation (offered 0.4 or 1.0), the
published schemes' at their knees, so MAIN is less even on most patterns, e.g. bit complement
0.15 / 0.75 against UGAL 0.86 / 0.997, shuffle 0.19 / 0.75 against 0.44 / 0.98; under hotspot it
is comparable (0.05 / 0.75 against 0.10 / 0.92 seq; 0.12 / 0.80 against 0.03 / 0.81 none).
At a load where MAIN is at least as even as UGAL at its peak (both min/mean and Jain; loads 0.3,
0.4, 1.0 tried) MAIN leads only under random permutation, seq (0.2951 at 0.3, +20 %); elsewhere
no tried load is that even (xp_validate.fairpeak): the throughput lead is bought partly with
less even injection, as for the published schemes past their knees.
Mode usage at the peak: the throttle's high mode in 27 to 100 % of source-cycles (bit
complement 99 to 100 %, transpose 27 to 37 %); the learner settles on 36 % under transpose (92 to
100 % of the measured time) and on 32 % under random permutation, bit reversal, bit complement,
shuffle and tornado (97 to 100 %), 0.2 to 2 switches per run; random intermediates 25 to 29 %
under tornado, long-way detours below 1.5 % everywhere (the long-way option is almost never
offered at 16 x 16; not investigated).
8 x 8 (the scaled scheme is the published combined scheme there; fresh seeds 31-34, 1600 cycles,
peak over offered 0.8 / 1.0; published at their peaks over dor 0.1 to 0.3 and 1.0, Valiant and
UGAL 0.6 to 1.0): ahead on all eight patterns in both move models, tied with dimension order on
neighbour at 1.0.  Smallest leads: hotspot +4.3 % (z 9.8, seq), transpose +3.0 % (z 18, none),
tornado +5.6 % (z 13, none, vs Valiant); the others +6 to +13 %.  (With the learner active at
k = 8, modes 32 / 36 %, also ahead everywhere: transpose +8.3 / +4.0 %, random permutation
+12 / +13.5 %, but 0.2 to 1.1 % below the static scheme on shuffle, bit complement and tornado,
hence the rule o2 = 28 + k / 2 that leaves k = 8 unchanged.)
VERDICT: at 16 x 16 the scaled scheme is strictly ahead of dimension order, Valiant and UGAL,
each at its own peak, on all eight non-trivial patterns in both move models (+4.5 % to +56 %,
z >= 7.0), and at the injection limit with dimension order on neighbour (UGAL 0.99, Valiant
0.52 to 0.64 there); at 8 x 8 it is unchanged and still ahead everywhere.  Caveats: the
parameters were chosen on pilot seed 1 at the evaluated loads; runs are 3000 cycles (the
learner explores during the 750-cycle warmup; longer runs not tested); its peak is past
saturation, where it is less fair than the published schemes at their knees (above); the
published schemes collapse past knees whose position varies by seed, so their peaks are taken
over a fine grid around the pilot knee, and a slightly higher knee between grid points
cannot be excluded where UGAL / Valiant deliver their offered load at the best grid point
(not the close cells: under hotspot and transpose UGAL is flat past its knee).
"""
import os
import sys

if __name__ == '__main__':
    os.environ['XPV_K'] = sys.argv[1]
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import xp_validate as XV            # noqa: E402  (resizes first)
import xp_combo2 as X2              # noqa: E402

KV = XV.KV
NN = KV * KV


import inspect                      # noqa: E402
import xp_combo as XC               # noqa: E402
import xp_portfolio as PF           # noqa: E402

_XV_RUN = XV.run_one
_CS = {}


def csim16():
    """xp_combo.csim with xp_validate's injection counters and diagnostics (see the docstring)"""
    if 'f' in _CS:
        return _CS['f']
    XC.DEF.update(lm='-', lE=1000.0, lS=200.0, lR=1.0, lth=0.7, ld=0.0)
    XC.STR = XC.STR + ('lm',)
    src = inspect.getsource(XC.csim)
    patches = [
        # xp_validate's counters (identical text)
        ('                    queues[s].append((dd, t))\n',
         '                    queues[s].append((dd, t))\n'
         '                    _GEN[s] += 1\n'),
        ('                d, born = queues[s].popleft()\n',
         '                d, born = queues[s].popleft()\n'
         '                if t >= warmup: _INJ[s] += 1\n'),
        # diagnostics: escape share of the occupied link channels, link occupancy, share of
        # source-cycles in the high (throttling) mode of the controller in force
        ('    for t in range(cycles):\n',
         '    _dg = [0.0, 0.0, 0.0, 0]\n'
         '    for t in range(cycles):\n'),
        ('        if ctrl2 is not None:\n            ctrl2.tick(t, occ)\n',
         '        if ctrl2 is not None:\n            ctrl2.tick(t, occ)\n'
         '        if t >= warmup:\n'
         '            _l = [c for c in occ if (c >> 1) % 5 != 4]\n'
         '            _e = sum(1 for c in _l if c % 2 == 0)\n'
         '            _dg[0] += _e / max(1, len(_l)); _dg[1] += len(_l) / (8 * N); _dg[3] += 1\n'
         '            if ctrl is not None and hasattr(ctrl, "hmode"):\n'
         '                _dg[2] += sum(1 for _s in range(N) if (ctrl2 if spread[_s] and ctrl2 is not None else ctrl).g[_s] == (ctrl2 if spread[_s] and ctrl2 is not None else ctrl).par["hi"]) / N\n'),
        ('            (nopt[1] + nopt[2]) / tot, nopt[3] / tot)\n',
         '            (nopt[1] + nopt[2]) / tot, nopt[3] / tot,\n'
         '            _dg[0] / max(1, _dg[3]), _dg[1] / max(1, _dg[3]), _dg[2] / max(1, _dg[3]))'
         ' + ((_L.switches,) + tuple(x / max(1, sum(_L.time)) for x in _L.time) if _L else ())\n'),
        # the mode-switching learner over the throttle of concentrated sources (lm=A+B+...)
        ('    ctrl = ctrl2 = None\n', '    ctrl = ctrl2 = None\n    _L = None\n'),
        ('            ctrl2.warmup = warmup\n',
         '            ctrl2.warmup = warmup\n'
         "        if o['lm'] != '-':\n"
         "            _lms = [XR.Ctrl(x, oc, nb, seed) for x in o['lm'].split('+')]\n"
         '            for _c in _lms:\n'
         '                _c.warmup = warmup\n'
         "            _L = PF.Learner(len(_lms), seed, warmup, E=o['lE'], S=o['lS'], R0=o['lR'],\n"
         "                            th=o['lth'], d=o['ld'], nsrc=N)\n"
         '            ctrl = _lms[_L.cur]\n'),
        ('    for t in range(cycles):\n        if ctrl is not None:\n',
         '    for t in range(cycles):\n'
         '        if _L is not None:\n'
         '            _m = _L.step(t, [_s for _s in range(N) if _s * 10 + 8 in occ])\n'
         '            if _m is not None:\n'
         '                ctrl = _lms[_m]\n'
         '        if ctrl is not None:\n'),
        ('            pk = occ.pop(c)\n            if t >= warmup:\n                lat.append(t - pk[1])\n',
         '            pk = occ.pop(c)\n'
         '            if _L is not None:\n'
         '                _L.n += 1\n'
         '            if t >= warmup:\n                lat.append(t - pk[1])\n'),
    ]
    for old, new in patches:
        assert src.count(old) == 1, old
        src = src.replace(old, new)
    ns = dict(vars(XC))
    ns['PF'] = PF
    exec(compile(src, '<xp_torus16 csim>', 'exec'), ns)
    _CS['f'] = ns['csim']
    return _CS['f']


def check():
    """k = 8: TD without a learner is xp_validate's counted csim (TC) bit for bit, and so is the
    scaled scheme at k = 8 (learner over two identical modes)"""
    ok = True
    sp = 'hop=price:src=toll:pm=0.2:thr=lx2_4_32_2:thr2=lx2_4_35_2'
    for ch in ('seq', 'none'):
        a = XV.torus_c(sp, 0.8, 'hotspot', 5, ch, 800)
        b = run_one('TD:' + sp, 0.8, 'hotspot', 5, ch, 800)
        c = run_one('TD:' + sp + ':lm=lx2_4_32_2+lx2_4_32_2:lE=250:lS=50:lR=1', 0.8, 'hotspot', 5,
                    ch, 800)
        e = a[:4] == b[:4] == c[:4] and a[-2:] == b[-2:] == c[-2:]
        ok &= e
        print(ch, a[:2], b[:2], c[:2], e)
    print('ALL OK' if ok else 'MISMATCH')


def run_one(spec, rate, pattern, seed, chain, cycles):
    kind, _, sp = spec.partition(':')
    if kind == 'TD':                  # the combined scheme with diagnostics
        return XV._run_counted(csim16(), sp, rate, pattern, seed=seed, chain=chain,
                               cycles=cycles)
    return _XV_RUN(spec, rate, pattern, seed, chain, cycles)


def top_rates(res, spec, pat, chain, cyc, seed, n):
    """the n offered loads with the highest pilot throughput (one seed)"""
    have = [(v[0], kk[2]) for kk, v in res.items() if kk[0] == KV and kk[1] == spec and
            kk[3] == pat and kk[5] == chain and kk[6] == cyc and kk[4] == seed]
    return [r for _, r in sorted(have, reverse=True)[:n]]


def knee_rates(res, spec, pat, chain, cyc, seed, up_only=False):
    """the midpoints between the best pilot load and its neighbours on the pilot grid (the
    published schemes collapse past a sharp knee at 16 x 16)"""
    grid = sorted({kk[2] for kk in res if kk[0] == KV and kk[1] == spec and kk[3] == pat and
                   kk[5] == chain and kk[6] == cyc and kk[4] == seed})
    best = top_rates(res, spec, pat, chain, cyc, seed, 1)[0]
    i = grid.index(best)
    out = []
    if i + 1 < len(grid):
        out.append(round((best + grid[i + 1]) / 2, 4))
    if i > 0 and not up_only:
        out.append(round((best + grid[i - 1]) / 2, 4))
    return out


def topjobs(specs, pats, chains, pcyc, pseed, n, seeds, cyc, extra=(), knee=False):
    """jobs on fresh seeds at the n best pilot loads of each spec / pattern / chain (knee: and
    the midpoints next to the best)"""
    res = XV.load()
    jobs = []
    for sp in specs:
        for p in pats:
            for ch in chains:
                rs = top_rates(res, sp, p, ch, pcyc, pseed, n)
                assert rs, (sp, p, ch)
                if knee:
                    rs += knee_rates(res, sp, p, ch, pcyc, pseed, up_only=knee == 'up')
                for r in sorted(set(rs) | set(extra)):
                    jobs += [(KV, sp, r, p, sd, ch, cyc) for sd in seeds]
    return jobs


PUBS = ('TA:dor', 'TA:val', 'TA:ugal')
TPATS = ['uniform', 'transpose', 'shuffle', 'bitrev', 'bitcomp', 'hotspot', 'tornado', 'neighbor',
         'randperm']


def report(main, mcyc, pcyc, chains, seeds, pseeds, pats=TPATS):
    """MAIN at its peak (over its cached loads, mean over the seeds) against each published
    scheme at its own peak: mean ± se, %, z, fairness (min/mean, Jain) of both at their peaks,
    and MAIN's mode usage at its peak (learner switches and time shares, share of source-cycles
    in the throttling mode, long-way and random-intermediate shares)"""
    res = XV.load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-12, (a[1] ** 2 + b[1] ** 2) ** .5)
    fr = lambda rows: (sum(x[-3] for x in rows) / len(rows), sum(x[-2] for x in rows) / len(rows))
    avg = lambda rows, i: sum(x[i] for x in rows) / len(rows)
    print(f'k={KV}: {main} ({mcyc} cycles, seeds {seeds}) vs published at their own peaks '
          f'({pcyc} cycles, seeds {pseeds})')
    for ch in chains:
        print(f'\n== {ch}')
        print(f'{"pattern":<10} {"MAIN peak@load":<20} {"fair m/m,J":<11} {"best published":<26}'
              f' {"lead %":>7} {"z":>6}  {"best fair":<11} modes')
        for p in pats:
            m = XV.cell(res, KV, main, p, ch, mcyc, seeds)
            if m is None:
                print(f'{p:<10} main incomplete')
                continue
            fm = fr(m[3])
            mode = ''
            if main.startswith('TD:'):
                n = len(m[3][0])
                mode = (f'hi {avg(m[3], 6):.2f} lw {avg(m[3], 2):.3f} va {avg(m[3], 3):.3f}')
                if n >= 13:
                    k = n - 10
                    mode += (f' sw {avg(m[3], 7):.1f} t ' +
                             '/'.join(f'{avg(m[3], 8 + i):.2f}' for i in range(k - 1)))
            best = None
            others = []
            for sp in PUBS:
                c = XV.cell(res, KV, sp, p, ch, pcyc, pseeds)
                if c is None:
                    others.append(f'{sp[3:]}:n/a')
                    continue
                others.append(f'{sp[3:]} {c[0]:.4f}±{c[1] * 1e4:.0f}@{c[2]:g} '
                              f'({100 * (m[0] / c[0] - 1):+.1f}%, z {z(m, c):+.1f})')
                if best is None or c[0] > best[1][0]:
                    best = (sp, c)
            if best is None:
                print(f'{p:<10} no published')
                continue
            sp, c = best
            fb = fr(c[3])
            print(f'{p:<10} {m[0]:.4f}±{m[1] * 1e4:<3.0f}@{m[2]:<6g} {fm[0]:.2f},{fm[1]:.3f} '
                  f'{sp[3:]:<5}{c[0]:.4f}±{c[1] * 1e4:<3.0f}@{c[2]:<6g} '
                  f'{100 * (m[0] / c[0] - 1):>+7.2f} {z(m, c):>+6.1f}  {fb[0]:.2f},{fb[1]:.3f}  {mode}')
            print(f'{"":<10}   all: ' + '; '.join(others))


if __name__ == '__main__':
    cmd = sys.argv[2]
    a = sys.argv[3:]
    XV.run_one = run_one
    if cmd == 'check':
        check()
    elif cmd == 'jobs':
        jobs = []
        with open(a[0]) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    jobs += XV.jobs_of(*line.split('|'))
        XV.compute(jobs)
    elif cmd == 'topjobs':    # SPECS PATS CHAINS PCYC PSEED N SEEDS CYC [EXTRA_RATES [knee|up]]
        XV.compute(topjobs(a[0].split(','), a[1].split(','), a[2].split(','), int(a[3]),
                           int(a[4]), int(a[5]), X2.seedlist(a[6]), int(a[7]),
                           [float(x) for x in a[8].split(',')] if len(a) > 8 and a[8] else (),
                           knee=a[9] if len(a) > 9 else False))
    elif cmd == 'pilot':
        XV.pilot(KV, a[0].split(','), a[1].split(','), a[2].split(','), int(a[3]),
                 X2.seedlist(a[4]))
    elif cmd == 'table':
        XV.table(KV, a[0], int(a[1]), a[2].split(','), int(a[3]), a[4].split(','),
                 a[5].split(','), X2.seedlist(a[6]), X2.seedlist(a[7]) if len(a) > 7 else None)
    elif cmd == 'report':     # MAIN MCYC PCYC CHAINS SEEDS PSEEDS
        report(a[0], int(a[1]), int(a[2]), a[3].split(','), X2.seedlist(a[4]),
               X2.seedlist(a[5]))
    elif cmd == 'one':
        import time
        t0 = time.time()
        print(run_one(a[0], float(a[1]), a[2], int(a[3]), a[4], int(a[5])),
              f'{time.time() - t0:.1f}s')
