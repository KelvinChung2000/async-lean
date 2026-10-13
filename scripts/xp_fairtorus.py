#!/usr/bin/env python3
"""A fair torus scheme: the scaled combined scheme of `xp_torus16.py` with per-source fair-share
admission and starvation relaxation, compared with dimension order, Valiant and UGAL under the
`fairpeak` criterion (simulation only; the rules' proof coverage is listed under Safety).

PROBLEM.  The torus scheme's lead is measured at its peak past saturation, where per-source
injection is much less even than the published schemes' at their knees (16 x 16 bit complement
Jain 0.75 against UGAL's 0.997).  Criterion (`xp_validate.fairpeak`): the reference of a cell
(k, pattern, move model) is the best published scheme at its own peak, with its fairness there
(min / mean and Jain of the per-source injection counts after warmup); every scheme's throughput
counts only at offered loads where both its mean min / mean and its mean Jain over the seeds are
at least the reference's ("fair peak").  The published schemes' fair peaks are at most their
peaks, so a scheme is ahead in a cell iff its fair peak beats the reference's peak.

RULES (spec `TF:<xp_torus16 TD spec>:<rules>`; all off by default = TD bit for bit, `check`):
  fs=1 fw=W fd=D fa=A fr=R   fair-share admission: the head of source s's queue enters the
      injection lane only while s's recent injection count (exponentially decayed, time
      constant W cycles; W = 0: since cycle 0) is at most (1 + D) x the mean count of the
      sources that have generated traffic (within distance R of s; R < 0: the whole network)
      plus A packets; fs=2: at most (1 + D) x the smallest count (of the sources that have
      generated traffic, network-wide) plus A packets.  History only (injection counts); the environment's packets are delayed
      in the source queue, never dropped.
  fl=L flo=G                 deficit relaxation: a source whose recent count is below (1 - L) x
      that mean takes its lane packet's first hop with threshold G (free outputs of 8 at the
      next router) and no escape blocking, instead of the lx controller's threshold / blocking.
  sw=T slo=G                 wait relaxation: the same once the lane packet has waited >= T
      cycles in the injection lane.
  (age priority among injection lanes is not used: the order in which ready packets move is
  the environment's schedule, not a selection.)

Safety (Lean; every k, the simulator's up*/down* escape):
  fs     an injection rule of the strategy: `Strategy.admit` (any predicate of the history and
         the injected packet) is unconstrained in `simUD_combo_safe` / `udComboStrategy` and in
         every `StrategySafe` theorem; the scheme with fs alone is `simUD_combo_safe` with that
         `admit` (history = decayed injection counts).
  fl, sw the first hop of a source's lane packet through the source gate with a threshold
         chosen from history (the lx threshold <= 8, or G <= 8) and escape blocking chosen from
         history (lxBlock or none): `simUD_throttle_safe` / `torus_ud_throttle_safe`
         (thr h f s <= 8, any block h f s), with the price / toll choices `ChoiceOK` as in
         `simUD_combo_safe`.  Not the udComboStrategy form (its threshold is the lx one per spread
         flag); the general throttle theorem covers it.
  The learner (`lm`) and the price / toll choices are covered as in xp_torus16.  As there: the
  no-chaining model is a different scheduling of the same moves; throughput and fairness are not
  proved.

Usage:  python3 scripts/xp_fairtorus.py K CMD ...     (K = grid size)
  K check                               TF with no rule = TD (xp_torus16) bit for bit
  K jobs FILE                           lines 'specs|pats|rates|seeds|chains|cycles'
  K pilot SPECS PATS CHAINS CYCLES SEEDS
  K fair SPECS MCYC PCYC CHAINS SEEDS PSEEDS [PATS]   the fairpeak table (see `fairtab`)
  K pf SPECS PATS CHAINS CYCLES SEEDS    throughput (min/mean / Jain) at every cached load
  K one SPEC RATE PAT SEED CHAIN CYCLES
Cache XPV_CACHE (default xpf<K>.json in this script's scratch directory given by XPF_DIR, else
the system temporary directory), XPV_PROCS processes.

FINDINGS (simulation; rules chosen on seed 1, evaluated on seeds 11-14 at 16 x 16 (3000 cycles)
and 31-38 at 8 x 8 (1600 cycles); published schemes on the same seeds at their fine-grid loads
(16 x 16: xp_torus16's knee grid; 8 x 8: ugal / val at 0.5 .. 1.0, dor 0.1 .. 0.3 and 1.0); every
scheme 1/4 warmup, random arbitration; fair peak as above; ± = se over the seeds, z vs the ref).
16 x 16, FT16 = TF:<xp_torus16 scheme>:fs=1:fw=0:fa=2:fl=0.05:flo=0 at offered 1.0 (fair-share
cap: cumulative count <= network mean + 2; a source 5 % below the mean takes its first hop with
threshold 0 and no escape blocking):
                 seq: FT16 (mm/Jain)     ref (mm/Jain)              lead     | none: FT16       ref               lead
  uniform    0.2945±12 (.95/.9999) ugal 0.2495 (.90/.9987) +18.0 % z 39  | 0.2232±3 (.95)  ugal 0.1878 (.88)  +18.8 % z 88
  transpose  0.2287±3  (.94/.9998) ugal 0.2275 (.48/.967)  +0.6 % z 1.1  | 0.1723±1 (.94)  ugal 0.1735 (.50)  -0.7 % z -2.6
  shuffle    0.2027±4  (.95/.9998) ugal 0.1883 (.44/.983)  +7.7 % z 12  | 0.1534±6 (.94)  ugal 0.1457 (.66)  +5.3 % z 4.4
  bit rev.   0.2640±53 (.94/.9998) ugal 0.2227 (.90/.9986) +18.5 % z 7.8 | 0.2012±9 (.93)  ugal 0.1639 (.88)  +22.8 % z 38
  bit comp.  0.1568±9  (.94/.9997) ugal 0.1375 (.86/.9973) +14.0 % z 21 | 0.1168±7 (.94)  ugal 0.1002 (.83)  +16.6 % z 22
  hotspot    0.1343±5  (.49/.9978) ugal 0.1303 (.10/.920)  +3.1 % z 5.2  | 0.1146±5 (.58)  ugal 0.1073 (.03)  +6.8 % z 9.1
  tornado    0.1765±9  (.91/.9997) val  0.1501 (.87/.9975) +17.6 % z 28 | 0.1379±10 (.79) ugal 0.1227 (.56)  +12.4 % z 14
  random p.  0.3058±5  (.95/.9999) ugal 0.2461 (.90/.9987) +24.3 % z 103 | 0.2322±2 (.95)  ugal 0.1842 (.87)  +26.1 % z 255
  neighbour  1.0 = dor 1.0 (both models)
  Its fairness at its own peak is at least the reference's in every cell (min/mean 0.49 to 0.95
  against 0.03 to 0.90, Jain >= 0.9978 against <= 0.9987), so its fair peak is its peak.  The
  unmodified scheme (TD) has a fair load only under random permutation, seq (README).  Cost of
  fairness vs TD's unfair peak: +1.1 to -31 % (shuffle -31 / -29 %, transpose -7 %, bit complement
  -8 / -12 %, uniform -4 / -7 %).  Transpose is a tie: the max-min fair share of transpose
  traffic is about UGAL's (unfair) knee; looser caps (fa = 3, 4, 6; fd = 0.05, 0.1), stronger
  relaxation (fl = 0.02) and the learner over 32 / 40 % moved it by < 1 % on seed 1, while
  fd >= 0.05 or fa >= 4 lost the min/mean margin under bit complement / shuffle.
8 x 8, FT8 = TF:hop=price:src=toll:pm=0.2:thr=lx2_4_32_2:thr2=lx2_4_35_2:fs=1:fw=0:fd=0.1:fa=2:
fl=0.2:flo=0 (cap 1.1 x mean + 2, relaxation 20 % below the mean), peak over offered 0.8 / 1.0:
  seq:  uniform +7.9 % (z 64), transpose +5.5 % (52), shuffle -3.4 % (-27), bit reversal +5.4 %
        (58), bit complement +2.8 % (8.0), hotspot +4.4 % (9.1), tornado +8.7 % (62, vs val),
        random permutation +10.2 % (151)
  none: uniform +10.3 % (60), transpose +0.9 % (8.5), shuffle -6.9 % (-44), bit reversal +5.7 %
        (36), bit complement +3.1 % (5.8), hotspot +10.0 % (25), tornado +5.3 % (23), random
        permutation +12.9 % (81); neighbour 1.0 = dor in both.
  The published 8 x 8 references peak past their knees (min/mean 0.39 to 0.77, Jain 0.89 to
  0.99), so FT8 uses a looser cap than FT16.  FT16's tight rule at 8 x 8 is fair-ahead on only
  8 of 16 cells (shuffle -16 %, transpose -3 / -8 %), the ungated published combined scheme on 8
  of 16 (it is less even than UGAL under bit complement, hotspot seq, shuffle none, ...).
VERDICT: the goal is met at 16 x 16 on 14 of the 16 non-trivial cells by a wide margin
(+3.1 to +26 %, z >= 4.4) and missed on transpose (a statistical tie: +0.6 % z 1.1 seq,
-0.7 % z -2.6 none); at 8 x 8 on 14 of 16 cells, missed on shuffle (-3.4 % / -6.9 %).  So no
single scheme is strictly ahead on every pattern in both models at both sizes under the
fairpeak criterion.  Caveats: the rule parameters differ by size (tight cap at 16 x 16, 1.1 x
mean at 8 x 8; chosen on seed 1 against the published references on the evaluation seeds); the
fair-share cap reads every source's injection count (global history; a neighbourhood version,
fr = R, was not evaluated); below saturation such a cap also smooths the Bernoulli noise of the
generator, but the evaluated points are all saturated (offered 0.8 / 1.0); the 16 x 16 runs are
3000 cycles; the published 8 x 8 grid has 0.05 steps (a knee between grid points is possible).
Proof coverage: fs = Strategy.admit (unconstrained in simUD_combo_safe); fl / sw =
simUD_throttle_safe (thresholds 0 <= 8 from history, blocking from history); the rest as
xp_torus16.
"""
import os
import sys

if __name__ == '__main__':
    os.environ['XPV_K'] = sys.argv[1]
    os.environ.setdefault('XPV_CACHE', os.path.join(
        os.environ.get('XPF_DIR', __import__('tempfile').gettempdir()), f'xpf{sys.argv[1]}.json'))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import builtins                     # noqa: E402
import xp_torus16 as X16            # noqa: E402  (imports xp_validate, which resizes)
import xp_validate as XV            # noqa: E402
import xp_combo as XC               # noqa: E402
import xp_combo2 as X2              # noqa: E402
import xp_backpressure as XP        # noqa: E402
import torus_experiments as T       # noqa: E402

KV = XV.KV
NN = KV * KV


# ------------------------------------------------------------------ the rules
class FairGate:
    """per-source fair-share admission and deficit / wait relaxation (see the docstring); reads
    only history: the decayed injection counts and the injection lane's waiting time"""

    def __init__(self, o, n):
        self.n = n
        self.W = o['fw']
        self.dec = 1.0 - 1.0 / self.W if self.W > 0 else 1.0
        self.fs = o['fs'] > 0
        self.fmin = o['fs'] >= 2
        self.mn = 0.0
        self.fd, self.fa = o['fd'], o['fa']
        self.fl, self.flo = o['fl'], int(o['flo'])
        self.sw, self.slo = o['sw'], int(o['slo'])
        self.rc = [0.0] * n
        self.act = [0] * n
        self.actl = []
        self.mean = 0.0
        self.ball = None
        R = int(o['fr'])
        if R >= 0:
            dist = T.NET.dist
            self.ball = [[v for v in range(n) if dist[s][v] <= R] for s in range(n)]
        self.relaxed = 0
        self.blocked = 0

    def activate(self, s):
        if not self.act[s]:
            self.act[s] = 1
            self.actl.append(s)

    def tick(self, t):
        if self.dec < 1.0:
            d = self.dec
            self.rc = [x * d for x in self.rc]
        if self.actl and self.ball is None:
            rc = self.rc
            self.mean = sum(rc[i] for i in self.actl) / len(self.actl)
            if self.fmin:
                self.mn = min(rc[i] for i in self.actl)

    def ref(self, s):
        if self.ball is None:
            return self.mean
        rc, act = self.rc, self.act
        v = [rc[i] for i in self.ball[s] if act[i]]
        return sum(v) / len(v) if v else 0.0

    def admit(self, s):
        if not self.fs:
            return True
        base = self.mn if self.fmin else self.ref(s)
        ok = self.rc[s] <= (1 + self.fd) * base + self.fa
        if not ok:
            self.blocked += 1
        return ok

    def note(self, s):
        self.rc[s] += 1.0

    def relax(self, s, t, pk):
        """the lane packet of s takes its first hop with a low threshold and no blocking"""
        if self.sw > 0 and t - pk[8] >= self.sw:
            return self.slo
        if self.fl > 0 and self.rc[s] < (1 - self.fl) * self.ref(s):
            return self.flo
        return -1


RULES = dict(fs=0.0, fw=0.0, fd=0.0, fa=2.0, fr=-1.0, fl=0.0, flo=2.0, sw=0.0, slo=2.0)

PATCHES = [
    ('    _L = None\n',
     '    _L = None\n'
     "    _FS = _FG(o, N) if (o['fs'] or o['fl'] or o['sw']) else None\n"),
    ('        if _L is not None:\n            _m = _L.step',
     '        if _FS is not None:\n            _FS.tick(t)\n'
     '        if _L is not None:\n            _m = _L.step'),
    ('                    _GEN[s] += 1\n',
     '                    _GEN[s] += 1\n'
     '                    if _FS is not None:\n                        _FS.activate(s)\n'),
    ('            if queues[s] and c not in occ:\n',
     '            if queues[s] and c not in occ and (_FS is None or _FS.admit(s)):\n'),
    ('                if t >= warmup: _INJ[s] += 1\n',
     '                if t >= warmup: _INJ[s] += 1\n'
     '                if _FS is not None:\n                    _FS.note(s)\n'),
    ('                    if ctrl is not None:\n'
     '                        free = (ctrl2 if spread[u] else ctrl).gate(',
     '                    _rl = _FS.relax(u, t, pk) if (_FS is not None and ctrl is not None) else -1\n'
     '                    if _rl >= 0:\n'
     '                        free = [x for x in free if sum(1 for oo in out[head[x]] if oo not in occ) >= _rl]\n'
     '                        if t >= warmup:\n                            _FS.relaxed += 1\n'
     '                    elif ctrl is not None:\n'
     '                        free = (ctrl2 if spread[u] else ctrl).gate('),
]

_CF = {}


def csimF():
    """xp_torus16.csim16 with the patches above applied to its text (each exactly once)"""
    if 'f' in _CF:
        return _CF['f']
    X16.csim16()                       # the unpatched TD simulator first (keeps its cache)
    saved = X16._CS.pop('f')
    XC.DEF.update(RULES)

    def comp(src, name, mode):
        for old, new in PATCHES:
            assert src.count(old) == 1, old
            src = src.replace(old, new)
        return builtins.compile(src, '<xp_fairtorus csim>', mode)

    X16.compile = comp
    try:
        f = X16.csim16()
    finally:
        del X16.compile
        X16._CS['f'] = saved
    f.__globals__['_FG'] = FairGate
    _CF['f'] = f
    return f


def run_one(spec, rate, pattern, seed, chain, cycles):
    kind, _, sp = spec.partition(':')
    if kind == 'TF':
        return XV._run_counted(csimF(), sp, rate, pattern, seed=seed, chain=chain, cycles=cycles)
    return X16.run_one(spec, rate, pattern, seed, chain, cycles)


def check():
    ok = True
    td = 'hop=price:src=toll:pm=0.2:thr=lx2_6_32_4:thr2=lx2_8_35_4:lm=lx2_6_32_4+lx2_6_36_4:lE=250:lS=50:lR=1'
    if KV == 8:
        td = 'hop=price:src=toll:pm=0.2:thr=lx2_4_32_2:thr2=lx2_4_35_2'
    cyc = 600 if KV == 16 else 800
    for ch in ('seq', 'none'):
        for p in ('hotspot', 'bitcomp'):
            a = X16.run_one('TD:' + td, 0.8, p, 5, ch, cyc)
            b = run_one('TF:' + td, 0.8, p, 5, ch, cyc)
            e = a == b
            ok &= e
            print(ch, p, a[:2], a[-2:], b[:2], b[-2:], e)
        # a rule that never binds (huge slack) is also identical
        b = run_one('TF:' + td + ':fs=1:fa=1e9', 0.8, 'hotspot', 5, ch, cyc)
        e = b == X16.run_one('TD:' + td, 0.8, 'hotspot', 5, ch, cyc)
        ok &= e
        print(ch, 'fs never binding', b[:2], b[-2:], e)
    print('ALL OK' if ok else 'MISMATCH')


# ------------------------------------------------------------------ the fairpeak table
PUBS = ('TA:dor', 'TA:val', 'TA:ugal')
PATS8 = ['uniform', 'transpose', 'shuffle', 'bitrev', 'bitcomp', 'hotspot', 'tornado', 'randperm']


def _fr(rows):
    return (sum(x[-3] for x in rows) / len(rows), sum(x[-2] for x in rows) / len(rows))


def fair_cells(res, sp, p, ch, cyc, seeds, ref):
    """(peak, fair peak) of sp: each (mean, se, rate, rows, min/mean, Jain) or None"""
    rs = sorted({kk[2] for kk in res if kk[0] == KV and kk[1] == sp and kk[3] == p
                 and kk[5] == ch and kk[6] == cyc})
    pk = fb = None
    for r in rs:
        c = XV.cell(res, KV, sp, p, ch, cyc, seeds, rates=[r])
        if c is None:
            continue
        fm, fj = _fr(c[3])
        x = c + (fm, fj)
        if pk is None or c[0] > pk[0]:
            pk = x
        if ref is not None and fm >= ref[0] and fj >= ref[1] and (fb is None or c[0] > fb[0]):
            fb = x
    return pk, fb


def fairtab(mains, mcyc, pcyc, chains, seeds, pseeds, pats=PATS8):
    res = XV.load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-12, (a[1] ** 2 + b[1] ** 2) ** .5)
    print(f'k={KV}: schemes ({mcyc} cycles, seeds {seeds}) vs published ({pcyc} cycles, seeds '
          f'{pseeds}); reference = best published at its peak; fair peak = best load with '
          'mean min/mean and Jain >= the reference\'s')
    summ = {m: [] for m in mains}
    for ch in chains:
        print(f'\n== {ch}')
        for p in pats:
            best = None
            pubs = []
            for sp in PUBS:
                pk, _ = fair_cells(res, sp, p, ch, pcyc, pseeds, None)
                if pk is None:
                    continue
                pubs.append((sp, pk))
                if best is None or pk[0] > best[1][0]:
                    best = (sp, pk)
            if best is None:
                print(f'{p:<10} no published')
                continue
            rsp, rc = best
            ref = (rc[4], rc[5])
            print(f'{p:<10} ref {rsp[3:]:<4} {rc[0]:.4f}±{rc[1] * 1e4:<3.0f}@{rc[2]:<6g} '
                  f'fair {ref[0]:.2f}/{ref[1]:.4f}   ' +
                  '  '.join(f'{sp[3:]} {c[0]:.4f}@{c[2]:g} ({c[4]:.2f}/{c[5]:.3f})'
                            for sp, c in pubs if sp != rsp))
            for m in mains:
                pk, fb = fair_cells(res, m, p, ch, mcyc, seeds, ref)
                nm = m if len(m) < 60 else '...' + m[-57:]
                if pk is None:
                    print(f'{"":<10} {nm}: incomplete')
                    summ[m].append(None)
                    continue
                s = (f'{"":<10}   peak {pk[0]:.4f}±{pk[1] * 1e4:<3.0f}@{pk[2]:<5g} '
                     f'({pk[4]:.2f}/{pk[5]:.4f}) {100 * (pk[0] / rc[0] - 1):+6.1f}%  ')
                if fb is None:
                    s += 'fair peak: none'
                    summ[m].append(-99.0)
                else:
                    lead = 100 * (fb[0] / rc[0] - 1)
                    summ[m].append(lead)
                    s += (f'fair {fb[0]:.4f}±{fb[1] * 1e4:<3.0f}@{fb[2]:<5g} '
                          f'({fb[4]:.2f}/{fb[5]:.4f}) {lead:+6.2f}% z {z(fb, rc):+5.1f}')
                print(s + f'  [{nm[-38:]}]')
    print('\nfair-peak leads per scheme (all cells, -99 = no fair load):')
    for m, v in summ.items():
        vv = [x for x in v if x is not None]
        print(f'  {m[-70:]:<70} n={len(vv)} min {min(vv) if vv else float("nan"):+.2f} '
              f'ahead {sum(1 for x in vv if x > 0)}/{len(v)}')


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
    elif cmd == 'pilot':
        XV.pilot(KV, a[0].split(','), a[1].split(','), a[2].split(','), int(a[3]),
                 X2.seedlist(a[4]))
    elif cmd == 'pf':         # pf SPECS PATS CHAINS CYCLES SEEDS: throughput (min/mean, Jain)
        res = XV.load()
        sds = X2.seedlist(a[4])
        for ch in a[2].split(','):
            for p in a[1].split(','):
                print(f'-- {ch} {p}')
                for sp in a[0].split(','):
                    rs = sorted({kk[2] for kk in res if kk[0] == KV and kk[1] == sp and
                                 kk[3] == p and kk[5] == ch and kk[6] == int(a[3])})
                    cells = []
                    for r in rs:
                        c = XV.cell(res, KV, sp, p, ch, int(a[3]), sds, rates=[r])
                        if c:
                            fm, fj = _fr(c[3])
                            cells.append(f'{r:g}:{c[0]:.4f}({fm:.2f}/{fj:.3f})')
                    print(f'   {sp[-46:]:<46} ' + ' '.join(cells))
    elif cmd == 'fair':
        fairtab(a[0].split(','), int(a[1]), int(a[2]), a[3].split(','), X2.seedlist(a[4]),
                X2.seedlist(a[5]), a[6].split(',') if len(a) > 6 else PATS8)
    elif cmd == 'one':
        import time
        t0 = time.time()
        print(run_one(a[0], float(a[1]), a[2], int(a[3]), a[4], int(a[5])),
              f'{time.time() - t0:.1f}s')
