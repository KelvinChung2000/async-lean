#!/usr/bin/env python3
"""The mesh learner scaled with the network size (simulation only; nothing here is proved).

Usage:  python3 scripts/xp_scale.py K CMD ...    (K = grid size; sets XPV_K before importing
`xp_validate`, which resizes the size-dependent modules)
  K check                      the Duato-random tier list reproduces `route=duato` bit for bit
  K jobs FILE                  lines 'specs|pats|rates|seeds|chains|cycles'
  K pilot SPECS PATS CHAINS CYCLES SEEDS
  K table MAIN MCYC PUBS PCYC PATS CHAINS SEEDS [PSEEDS]   (xp_validate.table)
  K one SPEC RATE PATTERN SEED CHAIN CYCLES
Cache XPS_CACHE (default xps_k<K>.json in the system temporary directory), XPV_PROCS processes.

Specs: everything of `xp_validate` (MX:, MPX:, MO1, TC:, TA:), plus
  SPX:<set>[:opts]   the learner of `xp_validate.mesh_px` (xp_portfolio.Learner) with the
                     k-scaling rule applied first (r = k/8), then explicit opts:
                       E = 250 r^2, S = 50 r^3   (epoch and settling time, cycles: the time a
                                                  saturated network needs to drain grows faster
                                                  than its latency),
                       R0 = max(1, round(2/r))   (exploration rounds),
                       th = 0.7 / sqrt(r)        (congestion gate: the share of sources whose
                                                  injection channel is busy >= 97 % of an epoch;
                                                  fewer sources are blocked in a larger network
                                                  at the same relative load),
                       fd = 5 r, fs = 3 r        (X' distance thresholds of the xyc tier)
                     (all equal the 8 x 8 values of t5b at k = 8: E 250, S 50, R0 2, th 0.7,
                     fd 5, fs 3); other learner opts as xp_portfolio (I0, Imax, h, far, W, d,
                     elim); re-probe intervals I0 / Imax are in epochs, so they scale with E.
                     `nosc=1` skips the rule.  Fitted at k = 16 on pilot seeds (1651).
New tier (registered in xp_transpose._XT, read by every mesh simulator here):
  dua   a free productive VC1 hop or the XY escape hop on VC0.  `route=wf:tiers=dua+esc:thr=g0`
        is Duato's mesh with random selection (`route=duato:tiers=all+esc:thr=g0`, bit for bit:
        `check`) written as a tier list of the west-first mesh: [dua, esc] with escTier k 0.
Mode sets (xp_validate.FSETS):
  s6   t5b + Duato random (D = route=wf:tiers=dua+esc:thr=g0)
  s6v  t5b + Duato VC1-first (route=wf:tiers=vc1+esc:thr=g0)
  s7   t5b + D + Duato throttled (route=wf:tiers=dua+esc:thr=g4)
  s6g  t5b + Duato throttled (D4 = route=wf:tiers=dua+esc:thr=g4)
Every mode of every set is a west-first tier list containing escTier k g with g <= 8:
  B  = str+esc+vc1, g4 (sel P / gdev: selection within tiers)      escTier k 4
  T  = all+esc, g0, sel Pd_balL0                                    escTier k 0
  X' = xyc+esc, g0 (fd, fs: configuration + own channel/destination) escTier k 0
  P  = pref+esc+vc1, g4, sel price                                   escTier k 4
  W6 = all+esc, g6                                                   escTier k 6
  D  = dua+esc, g0 / g4;  V = vc1+esc, g0                            escTier k 0 / 4
so `westFirstMesh_modes_safe` covers any history-dependent switching among them.

FINDINGS (fresh seeds; published schemes 6000 cycles, peak over fine knee sweeps)
8 x 8 (rule = t5b's settings; learner SPX:s6:d=2:elim=0.1, 12000 cycles, seeds 2101-2108):
  strictly ahead of every published scheme on all 8 patterns in both move models; smallest
  leads tornado +0.45 % (z 7.0, seq), bit complement +0.83 % (z 11, seq), transpose +1.4 % (none).
16 x 16 (learner 18000 cycles, seeds 2001-2005 on hotspot / uniform-none, 2001-2002 elsewhere;
  published seeds 2001-2005, far schemes 1601-1603):
  ahead on transpose (+2.3 / +0.9 %), shuffle (+21 / +24), bit reversal (+8 / +18), bit
  complement (+0.8 / +1.5 %, z 3.7 / 15; = X' with fd 10, fs 6, the learner never leaves it),
  tornado (+5.5 / +5.1), random permutation (+9.2 / +9.6);  behind on hotspot (-2.4 % z -2.1 at
  offered 0.16 / -4.3 %) and uniform (-2.3 % / -4.2 %).  The price mode alone beats Duato on
  hotspot at 16 x 16 (pilot seed 1651: 0.121 vs 0.115 seq), but the learner's samples are taken
  in a jammed network (switching leaves tree saturation that persists for thousands of cycles),
  so it sometimes picks a poor mode and its probes cost more than at 8 x 8.  The gate th = 0.49
  makes it learn at sub-saturation uniform loads, where X' alone ties XY (th = 0.7 kept X').
"""
import os
import sys
import tempfile

if __name__ == '__main__':
    os.environ['XPV_K'] = sys.argv[1]
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import xp_validate as XV            # noqa: E402  (resizes first)
import xp_transpose as XT           # noqa: E402
import xp_combo2 as X2              # noqa: E402

KV = XV.KV
XV.CACHE = os.environ.get('XPS_CACHE', os.path.join(tempfile.gettempdir(), f'xps_k{KV}.json'))


# ------------------------------------------------------------------ the Duato tier
@XT.tier('dua')
def _dua(ctx, c, u, d, src, esc):
    return lambda q: q % 2 == 1 or q == esc


MODE_D = 'route=wf:tiers=dua+esc:thr=g0'
MODE_D4 = 'route=wf:tiers=dua+esc:thr=g4'
MODE_V = 'route=wf:tiers=vc1+esc:thr=g0'
T5B = XT.MSETS['t5b']
XV.FSETS['s6'] = T5B + [MODE_D]
XV.FSETS['s6v'] = T5B + [MODE_V]
XV.FSETS['s7'] = T5B + [MODE_D, MODE_D4]
XV.FSETS['s6g'] = T5B + [MODE_D4]


def scaled_opts(k, toks):
    """the k-scaling rule, then explicit overrides"""
    r = k / 8
    o = {} if 'nosc=1' in toks else dict(E=250 * r ** 2, S=50 * r ** 3, R0=max(1, round(2 / r)),
                                         th=round(0.7 / r ** 0.5, 2), fd=5 * r, fs=3 * r)
    for t in toks:
        if t and t != 'nosc=1':
            a, b = t.split('=')
            o[a] = float(b)
    return o


def mesh_spx(sp, rate, pattern, seed, chain, cycles):
    toks = sp.split(':')
    o = scaled_opts(KV, toks[1:])
    fd, fs = o.pop('fd', None), o.pop('fs', None)
    old = dict(X2.MDEF)
    try:
        if fd is not None:
            X2.MDEF['fd'] = float(round(fd))
        if fs is not None:
            X2.MDEF['fs'] = float(round(fs))
        spec = ':'.join([toks[0]] + [f'{a}={round(b)}' if a in ('E', 'S', 'R0') else f'{a}={b:g}'
                                     for a, b in o.items()])
        return XV.mesh_px(spec, rate, pattern, seed, chain, cycles)
    finally:
        X2.MDEF.clear()
        X2.MDEF.update(old)


_run_one_v = XV.run_one


def run_one(spec, rate, pattern, seed, chain, cycles):
    kind, _, sp = spec.partition(':')
    if kind == 'SPX':
        return mesh_spx(sp, rate, pattern, seed, chain, cycles)
    return _run_one_v(spec, rate, pattern, seed, chain, cycles)


XV.run_one = run_one                # xp_validate's pool workers call run_one through its globals
XV.NAMES.update({'MX:' + MODE_D: 'Duato rand (wf)', 'MX:' + MODE_V: 'Duato VC1-first'})
_cost_v = XV.cost


def cost(j):
    return _cost_v(j) * (2.2 if j[1].startswith('SPX') else 1.0)


XV.cost = cost


def check():
    ok = True
    for chn in ('seq', 'none'):
        for p, r, sd in (('hotspot', 0.5, 3), ('uniform', 0.6, 4), ('transpose', 0.4, 5)):
            a = XV.mesh_x('route=duato:tiers=all+esc:thr=g0', r, p, sd, chn, 600)
            b = XV.mesh_x(MODE_D, r, p, sd, chn, 600)
            a4 = XV.mesh_x('route=duato:tiers=all+esc:thr=g4', r, p, sd, chn, 600)
            b4 = XV.mesh_x(MODE_D4, r, p, sd, chn, 600)
            e = a == b and a4 == b4
            ok &= e
            print('duato / wf dua+esc', chn, p, a[:2], b[:2], a4[:2], b4[:2], e)
    # at k = 8 the scaled learner with t5b is the published t5b learner
    if KV == 8:
        a = XV.mesh_px('t5b:th=0.7:d=2:elim=0.1', 1.0, 'bitcomp', 3, 'seq', 1500)
        b = mesh_spx('t5b:th=0.7:d=2:elim=0.1', 1.0, 'bitcomp', 3, 'seq', 1500)
        ok &= a == b
        print('t5b / scaled t5b at k=8', a[:2], b[:2], a == b)
    print('ALL OK' if ok else 'MISMATCH')


# ------------------------------------------------------------------ evaluation plans
def read_plan(path):
    """lines 'role|pats|chains|spec|rates|seeds|cycles', role main (the learner) or pub (a
    published scheme: peak over its rates); returns [(role, pat, chain, spec, rates, seeds, cyc)]"""
    out = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            role, pats, chains, spec, rates, seeds, cyc = line.split('|')
            for p in pats.split(','):
                for ch in chains.split(','):
                    out.append((role, p, ch, spec, [float(r) for r in rates.split(',')],
                                X2.seedlist(seeds), int(cyc)))
    return out


def plan_jobs(plan):
    return [(KV, sp, r, p, sd, ch, cyc) for _, p, ch, sp, rs, seeds, cyc in plan
            for r in rs for sd in seeds]


def plan_report(plan):
    res = XV.load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-12, (a[1] ** 2 + b[1] ** 2) ** .5)
    fair = lambda c: (sum(x[-3] for x in c[3]) / len(c[3]), sum(x[-2] for x in c[3]) / len(c[3]))
    cells = {}
    for role, p, ch, sp, rs, seeds, cyc in plan:
        d = cells.setdefault((ch, p), {})
        key = (role, sp, cyc, tuple(seeds))
        d.setdefault(key, set()).update(rs)
    summary = []
    for ch in ('seq', 'none'):
        print(f'\n== k={KV} {ch}: peak of the mean over seeds (± se, 1e-4) @offered; fairness '
              'min/mean, Jain at that peak (mean over seeds)')
        for p in X2.MPATS:
            if (ch, p) not in cells:
                continue
            d = cells[(ch, p)]
            got = {}
            for (role, sp, cyc, seeds), rs in d.items():
                got[(role, sp, cyc, seeds)] = XV.cell(res, KV, sp, p, ch, cyc, list(seeds),
                                                      sorted(rs))
            mains = [(k, c) for k, c in got.items() if k[0] == 'main']
            pubs = [(k, c) for k, c in got.items() if k[0] == 'pub']
            for (role, sp, cyc, seeds), m in mains:
                if m is None:
                    print(f'{p:<10} MAIN {sp} incomplete')
                    continue
                nmo = len(m[3][0]) - 8
                sh = '/'.join(f'{100 * sum(x[5 + i] for x in m[3]) / len(m[3]):.0f}'
                              for i in range(nmo))
                fm = fair(m)
                print(f'{p:<10} {sp[:34]:<34} {m[0]:.4f}±{m[1] * 1e4:<4.0f}@{m[2]:<6g}'
                      f'fair {fm[0]:.2f}/{fm[1]:.3f} modes {sh} [{len(seeds)} seeds, {cyc}]')
                best = None
                for (r2, sp2, cyc2, seeds2), c in sorted(pubs, key=lambda x: x[0][1]):
                    nm = XV.NAMES.get(sp2, sp2)[:34]
                    if c is None:
                        print(f'{"":<10} {nm:<34} incomplete')
                        continue
                    fr = fair(c) if sp2 != 'MO1' else None
                    print(f'{"":<10} {nm:<34} {c[0]:.4f}±{c[1] * 1e4:<4.0f}@{c[2]:<6g}' +
                          (f'fair {fr[0]:.2f}/{fr[1]:.3f}' if fr else f'{"":<15}') +
                          f' MAIN {100 * (m[0] / c[0] - 1):+6.2f}% {z(m, c):+7.1f}z'
                          f' [{len(seeds2)} seeds, {cyc2}]')
                    if best is None or c[0] > best[1][0]:
                        best = (nm, c)
                if best:
                    print(f'{"":<10} {"=> vs best: " + best[0]:<34} '
                          f'{100 * (m[0] / best[1][0] - 1):+6.2f}% {z(m, best[1]):+7.1f}z')
                    summary.append((ch, p, sp, m, best))
    return summary


if __name__ == '__main__':
    cmd = sys.argv[2]
    a = sys.argv[3:]
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
    elif cmd == 'planrun':
        XV.compute(plan_jobs(read_plan(a[0])))
    elif cmd == 'planrep':
        plan_report(read_plan(a[0]))
    elif cmd == 'pilot':
        XV.pilot(KV, a[0].split(','), a[1].split(','), a[2].split(','), int(a[3]),
                 X2.seedlist(a[4]))
    elif cmd == 'table':
        XV.table(KV, a[0], int(a[1]), a[2].split(','), int(a[3]), a[4].split(','),
                 a[5].split(','), X2.seedlist(a[6]), X2.seedlist(a[7]) if len(a) > 7 else None)
    elif cmd == 'one':
        import time
        t0 = time.time()
        print(run_one(a[0], float(a[1]), a[2], int(a[3]), a[4], int(a[5])),
              f'{time.time() - t0:.1f}s')
