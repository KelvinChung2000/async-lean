#!/usr/bin/env python3
"""The scaled mesh learner of `xp_scale.py` with a traffic-signature rule (simulation only;
nothing here is proved).

Usage:  python3 scripts/xp_scale2.py K CMD ...    (K = grid size, as xp_scale.py)
  K check                      bit-identity checks (see `check`)
  K planrun PLAN | K planrep PLAN | K jobs FILE | K pilot ... | K one ...   as xp_scale.py
Cache XPS_CACHE, XPV_PROCS processes (as xp_scale.py).

Spec  SQX:<set>[:opts]   (mode sets of xp_validate / xp_scale: s6 = t5b + Duato random)
  the learner of `xp_scale` (SPX: xp_portfolio.Learner with the k-scaling rule for E, S, R0,
  fd, fs) with four changes:
  1. the congestion gate keeps its 8 x 8 value th = 0.7 at every k (xp_scale scaled it to
     0.7 / sqrt(k / 8), which made the learner explore below saturation under uniform traffic);
  2. destination concentration (cth > 0, default 0.1): the controller counts the
     destinations of the packets that entered the network (the packet in a source's injection
     channel, i.e. the configuration); every 100 cycles, once at least cmin (1000) packets
     were counted, if one destination received a share >= cth of them, it switches to mode
     hm (default 3 = P, price-chosen hops) and keeps it for the rest of the run (no
     exploration, no probes).  Under uniform traffic every destination's share is about
     1 / k^2; under a permutation it is one source's share of the injections, at most
     1 / (k^2 x mean injection rate) (< 0.07 at every benchmark load here); under hotspot
     traffic the centre's is ~ 20 %.
     The learner's tree-saturated samples misjudged P under hotspot at 16 x 16 (every switch
     leaves congestion that persists for thousands of cycles); the rule avoids learning there.
  3. random destinations (db >= 0, default 0 = B): at the first 100-cycle check at which half
     the sources have injected two packets (and >= cmin packets were counted), if at least a
     share sth (0.5) of those sources used more than one destination, and the learner is still
     in its default mode d (the congestion gate has not fired), it switches to mode db and
     continues as the learner (db is its new default; the gate and the learning are as before).
     Under every permutation pattern each source has one destination (rule 3 never fires; X'
     stays the default, which bit complement needs); under uniform traffic B is the best mode
     below saturation (16 x 16 pilot, seed 1651: B 0.2413 seq / 0.1835 none at its knee, X'
     0.2256 / 0.1803, XY on both VCs 0.2280 / 0.1785 on seeds 2001-2005).
  4. exploration (xs=1): the epoch in which the congestion gate fires is the current mode's
     sample of the first exploration round (that mode is not explored again in the round).
     At 16 x 16 (E = 1000, R0 = 1) the exploration then ends at cycle 6000 instead of 7000,
     i.e. at the end of the warmup of an 18000-cycle run instead of inside the measurement
     (with xs=0 the last explored mode -- often not the one chosen -- took 1000 of the 12000
     measured cycles: -1 to -4.5 % on transpose for 3 of 5 seeds).
  The evaluated learner is SQX:s6:d=2:elim=0.1:xs=1 (defaults cth=0.1, hm=3, cmin=1000,
  db=0, sth=0.5, th=0.7).
  cth=0, db=-1, xs=0 and th=<0.7/sqrt(r)> give back xp_scale's SPX bit for bit (`check`).
Safety: the controller reads only history (deliveries, injection-channel occupancy and the
destinations of packets in injection channels) and chooses among the modes of s6, each a
west-first tier list containing escTier k g with g <= 8 (B, P: g = 4; T, X', D: g = 0; W6:
g = 6), so `westFirstMesh_modes_safe` covers it, as for SPX.

FINDINGS (SQX:s6:d=2:elim=0.1:xs=1; published schemes 6000 cycles at their own peaks, the
previous agent's knee sweeps; the learner on the same seeds)
16 x 16 (18000 cycles; seeds 2001-2005, 2001-2004 on shuffle / bit rev. / tornado / random
  perm.; bit complement seq 2001-2008 with XY re-run on 2006-2008): strictly ahead on all 8
  patterns in both move models.  seq / none: uniform +5.1 % (z 21, vs Duato T4) / +2.3 %
  (z 28, vs XY); transpose +2.3 / +0.9 % (z 64 / 29); shuffle +26 / +30 %; bit reversal
  +13 / +21 %; hotspot +5.1 / +5.0 % (z 19 / 19, vs Duato random); bit complement +1.1 %
  (z 10, 8 seeds) / +1.6 % (z 15); tornado +6.5 / +5.9 %; random permutation +18 / +19 %.
8 x 8 (12000 cycles, seeds 2101-2108): strictly ahead on all 16 cells; smallest leads
  tornado +0.42 % (z 7.1, seq), bit complement +0.83 % (z 11, seq), transpose +1.37 % (none);
  hotspot +4.2 / +4.5 % (SPX: +3.6 / +3.5 %).
"""
import os
import sys

if __name__ == '__main__':
    os.environ['XPV_K'] = sys.argv[1]
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import xp_scale as XS               # noqa: E402  (resizes first, via xp_validate)
import xp_validate as XV            # noqa: E402
import xp_transpose as XT           # noqa: E402
import xp_portfolio as PF           # noqa: E402
import xp_combo2 as X2              # noqa: E402

KV = XV.KV
NN = KV * KV


class SLearner(PF.Learner):
    """xp_portfolio.Learner plus the traffic-signature rules (see the docstring)."""

    def __init__(self, K, seed, warmup, cth=0.1, hm=3, cmin=1000, db=0, sth=0.5, xs=0, nsrc=64,
                 **kw):
        super().__init__(K, seed, warmup, nsrc=nsrc, **kw)
        self.cth, self.hm, self.cmin, self.db, self.sth = cth, int(hm), cmin, int(db), sth
        self.d0 = int(kw.get('d', 0))
        self.xs = int(xs)
        self.dst = [0] * nsrc            # injected packets per destination
        self.first = [-1] * nsrc         # per source: its first destination
        self.cnt = [0] * nsrc            # per source: injected packets
        self.var = [False] * nsrc        # per source: a destination other than its first
        self.locked = None               # the cycle of the concentration lock
        self.spread = None               # the cycle of the spread decision

    def saw(self, s, d):
        """a packet of source s with destination d entered the injection channel"""
        self.dst[d] += 1
        c = self.cnt[s]
        if c == 0:
            self.first[s] = d
        elif d != self.first[s]:
            self.var[s] = True
        self.cnt[s] = c + 1

    def step(self, t, inj=()):
        if self.locked is not None:
            if t >= self.warmup:
                self.time[self.cur] += 1
            return None
        chk = t > 0 and t % 100 == 0 and sum(self.dst) >= self.cmin
        if chk and self.cth > 0 and max(self.dst) >= self.cth * sum(self.dst):
            self.locked = t
            old, self.cur = self.cur, self.hm
            if t >= self.warmup:
                self.time[self.cur] += 1
                self.switches += old != self.hm
            return self.hm if old != self.hm else None
        before, m0 = self.congested, self.cur
        r = super().step(t, inj)
        if self.xs and not before and self.congested and self.K > 1:
            # the epoch in which the gate fired is m0's sample of the first exploration round
            if r is None and self.cur == m0:     # the base popped m0 itself: take the next
                if self.queue:
                    nxt = self.queue.pop(0)
                    if nxt != m0:
                        self.cur = nxt
                        if t >= self.warmup:
                            self.switches += 1
                        self.ms = t + self.S
                        return nxt
            else:                                # drop m0 from the rest of the first round
                rest = self.queue[:self.K - 1]
                if m0 in rest:
                    del self.queue[rest.index(m0)]
            return r
        if chk and r is None and self.db >= 0 and self.spread is None:
            n2 = sum(1 for c in self.cnt if c >= 2)
            if 2 * n2 >= self.nsrc:      # half the sources injected twice: decide once
                self.spread = t
                nv = sum(self.var)
                if nv >= self.sth * n2 and not self.congested and self.cur == self.d0 \
                        and self.db != self.d0:
                    self.cur = self.db   # random-destination traffic: default mode db
                    if t >= self.warmup:
                        self.switches += 1
                    self.ms = t + self.S
                    return self.db
        return r


_PXD = None


def pxsim_dst_fn():
    """xp_transpose.pxsim_fn plus the destination count of every injected packet (L.dst)"""
    global _PXD
    if _PXD is None:
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
             "                _PF['L'].saw(s, occ[ch(s, 4, 0)][0])\n"),
        ]
        _PXD = XT._build(extra, 'pmsim')
        _PXD[1].update(_XT=XT._XT, _XS=XT._XS, _DG=None)
    return _PXD


LKEYS = ('cth', 'hm', 'cmin', 'db', 'sth', 'xs')


def sqx_opts(toks):
    """xp_scale's k-scaling rule with th = 0.7 kept, then explicit overrides"""
    o = XS.scaled_opts(KV, [t for t in toks if t.split('=')[0] not in LKEYS])
    if not any(t.startswith('th=') for t in toks):
        o['th'] = 0.7
    lo = {t.split('=')[0]: float(t.split('=')[1]) for t in toks if t.split('=')[0] in LKEYS}
    return o, lo


def mesh_sqx(sp, rate, pattern, seed, chain, cycles):
    toks = sp.split(':')
    o, lk = sqx_opts(toks[1:])
    fd, fs = o.pop('fd', None), o.pop('fs', None)
    old = dict(X2.MDEF)
    try:
        if fd is not None:
            X2.MDEF['fd'] = float(round(fd))
        if fs is not None:
            X2.MDEF['fs'] = float(round(fs))
        lo = PF.lparse([f'{a}={round(b)}' if a in ('E', 'S', 'R0') else f'{a}={b:g}'
                        for a, b in o.items()])
        modes = XV._modes(toks[0])
        fn, ns = pxsim_dst_fn()
        ns['_INJ'] = [0] * NN
        ns['_GEN'] = [0] * NN
        warmup = cycles // 3
        L = SLearner(len(modes), seed, warmup, nsrc=NN, **lk, **lo)
        ns['_PF'].update(L=L, modes=[PF.mesh_mode(m) for m in modes],
                         useprice=any(X2.mparse(m)['sel'] == 'price' for m in modes))
        r = fn(modes[L.cur], rate, pattern, seed=seed, chain=chain, cycles=cycles,
               warmup=warmup, k=KV)
        tot = max(1, sum(L.time))
        return ([r[0], r[1], 0.0, 0.0, L.switches] + [x / tot for x in L.time] +
                list(XV.fairness(ns['_INJ'], ns['_GEN'])))
    finally:
        X2.MDEF.clear()
        X2.MDEF.update(old)


_run_one_s = XV.run_one             # xp_scale's (SPX, then xp_validate's kinds)


def run_one(spec, rate, pattern, seed, chain, cycles):
    kind, _, sp = spec.partition(':')
    if kind == 'SQX':
        return mesh_sqx(sp, rate, pattern, seed, chain, cycles)
    return _run_one_s(spec, rate, pattern, seed, chain, cycles)


XV.run_one = run_one
_cost_s = XV.cost
XV.cost = lambda j: _cost_s(j) * (2.2 if j[1].startswith('SQX') else 1.0)


def check():
    ok = True
    th = round(0.7 / (KV / 8) ** 0.5, 2)
    for p, r, chn in (('uniform', 1.0, 'seq'), ('hotspot', 0.5, 'none'), ('tornado', 1.0, 'none')):
        a = XS.mesh_spx('s6:d=2:elim=0.1', r, p, 3, chn, 2400)
        b = mesh_sqx(f's6:d=2:elim=0.1:cth=0:db=-1:th={th}', r, p, 3, chn, 2400)
        e = a == b
        ok &= e
        print('SPX / SQX cth=0 th=scaled', p, chn, a[:2], b[:2], e)
    # with the lock: under hotspot the run is mode P from the lock on; nothing locks otherwise
    for p in ('hotspot', 'uniform', 'transpose', 'randperm', 'tornado', 'bitcomp'):
        b = mesh_sqx('s6:d=2:elim=0.1', 1.0, p, 3, 'seq', 1500)
        print('SQX rules', p, [round(x, 4) for x in b[:2]], 'modes',
              [round(x, 2) for x in b[5:-2]])
    print('ALL OK' if ok else 'MISMATCH')


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
        XV.compute(XS.plan_jobs(XS.read_plan(a[0])))
    elif cmd == 'planrep':
        XS.plan_report(XS.read_plan(a[0]))
    elif cmd == 'pilot':
        XV.pilot(KV, a[0].split(','), a[1].split(','), a[2].split(','), int(a[3]),
                 X2.seedlist(a[4]))
    elif cmd == 'one':
        import time
        t0 = time.time()
        print(run_one(a[0], float(a[1]), a[2], int(a[3]), a[4], int(a[5])),
              f'{time.time() - t0:.1f}s')
