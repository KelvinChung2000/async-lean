#!/usr/bin/env python3
"""Can anything beat "XY on both virtual channels" on bit complement and random permutation on the
8 x 8 mesh?  (simulation only; nothing here is proved)

The model is the one of `routing_sim.py` / `xp_combo2.msim` (2 one-packet VC lanes per link,
random arbitration, unbounded source queues) in both move models of `xp_arbiter.py` (`seq`,
`none`).  `bsim` is `xp_combo2.msim` restricted to the west-first mesh's permitted hops and
specialised to XY-based selections; with the default spec it reproduces
`xp_combo2.msim('route=wf:tiers=xy+esc:thr=g0')` = `A:R:dualXY:random` bit for bit (`check`).

Spec `B:<key=value:...>` (every option keeps the throttled escape tier `escTier k g` -- the XY
hop on VC0 -- in the tier list, unless marked UNCOVERED):
  c0=<classes>     packets of these classes take only the XY hop on VC0 (tier list [esc]); every
                   other packet the XY hop on either VC ([xy, esc]).  Classes ('+'-separated):
                     turn  the hop enters a router where the packet turns (X -> Y)
                     src   the packet is in its injection channel
                     str   the hop enters a router where the packet goes straight on
                     ej    the hop enters the destination router
                     far   the packet is more than `fd` hops from its destination
                     farX, farY   far, and the hop is in X (resp. Y)
                     srcfar  src and far
                     fary  far while a nearer packet (at most fd hops to go) in a link into the
                           router or in its injection channel waits for the same output
                     farz  fary, counting only packets in links (not sources)
                     srcwf srcw for a source more than `fs` hops from its destination; with
                           fs >= 0, fary counts a waiting source as nearer when it is at most fs
                           hops from its destination (instead of fd)
                     srcw  src while a packet in a link into the router waits for the same
                           output direction (sources yield the VC1 lane to transit traffic)
  lane=<rule>      a lane preference among the two free XY lanes, with fallback to the other:
                   vc1, keep (the current VC), switch, par (destination parity), dirn (VC by
                   travel direction).  For XY routing the lane label never matters: both lanes
                   of a link lead to the same next hops, so the process of per-link counts (and
                   of ghosts, without chaining) is the same under every such rule
  yld=turn|all     a packet going straight on in Y takes only the VC0 lane while a turner (all:
                   also a packet going straight in X, while a turner or a source) waits at its
                   router for the same output direction: the VC1 lane is left to the waiting
                   packet (a configuration-dependent first tier; covered)
  c1=<classes>     UNCOVERED (diagnostic): these classes take only the XY hop on VC1
  pat=<k>          patience: a packet that has not moved for k cycles may also take the free
                   hops of `dset` (vc1: productive hops on VC1 -- Duato; all: every permitted
                   west-first hop) after its XY tier; ps=P picks the deviation into the router
                   with the most free usable hops (history: the waiting time)
  sg=<g>           escape threshold of sources (g of the next router's 8 outgoing channels free)
  sc=<cond>        sources take an XY hop (either VC) only when cond holds, else the throttled
                   escape (with sg, normally 8): up (no packet in the inbound lane(s) going
                   straight through this router in the same direction), own<m> (at most m of the
                   source router's 8 outgoing channels occupied), lane (both XY lanes out free),
                   gap<G> (history: at least G cycles since this source last injected),
                   ld<m> (at most m packets in the links of the source's XY row ahead)
  dor=yx|bis       UNCOVERED by the tier theorems unless with VC1 only: YX on VC1 (O1TURN-like)
                   per packet: yx = every packet YX on VC1 (escape XY VC0), bis = chosen by side
Findings (fresh seeds 101-112, 2000 cycles, peak over offered 0.29-0.34 / 0.22-0.27 for bit
complement, 0.9 / 1.0 for random permutation):
  B:c0=fary+srcwf:fd=5:fs=3 (far packets leave the VC1 lane to nearer waiting packets, far
  sources leave it to waiting transit)   bitcomp 0.3018 / 0.2293, randperm 0.4799 / 0.3911
  B: (= dualXY)                           bitcomp 0.3006 / 0.2256, randperm 0.4652 / 0.3608
  (seq / none).  Lane preferences with fallback (lane=...) reproduce dualXY bit for bit.

Baselines through `xp_combo2.run_one` (`A:...`, `M:...`) and `xp_portfolio.run_one` (`PM:...`).

Usage:
  python3 scripts/xp_bitcomp.py check
  python3 scripts/xp_bitcomp.py diag SPEC PATTERN RATE SEED CHAIN [CYCLES]
  python3 scripts/xp_bitcomp.py run SPECS PATTERNS RATES SEEDS CHAINS [CYCLES]
  python3 scripts/xp_bitcomp.py report MAIN OTHERS PATTERNS RATES SEEDS CHAINS [CYCLES]
Cache: XP_BC_CACHE (default xp_bitcomp.json in the system temporary directory); XP_BC_PROCS
processes (default 3).
"""
import json
import os
import random
import sys
import tempfile
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import routing_sim as R
import xp_backpressure as XP
import xp_combo2 as X2

K = 8
N = K * K

BDEF = dict(c0='', c1='', pat=-1, dset='vc1', ps='rand', sg=0, sc='', fd=4, dor='xy', lane='', yld='', fs=-1)
BSTR = ('c0', 'c1', 'dset', 'ps', 'sc', 'dor', 'lane', 'yld')


def bparse(spec):
    o = dict(BDEF)
    for tok in spec.split(':'):
        if tok:
            kk, v = tok.split('=')
            o[kk] = v if kk in BSTR else int(v)
    return o


_TB = None


def tabs():
    global _TB
    if _TB is None:
        ch, hd, RT, XY0, XY1, YX1 = X2.tables(K, 'wf')
        xyd = [[0 if u % K < d % K else 1 if d % K < u % K else 2 if u // K < d // K else 3
                if d // K < u // K else -1 for d in range(N)] for u in range(N)]
        _TB = (ch, hd, RT, XY0, XY1, YX1, xyd)
    return _TB


def bsim(spec, rate, pattern, seed=1, chain='seq', cycles=2000, warmup=None, diag=None):
    o = bparse(spec)
    warmup = cycles // 3 if warmup is None else warmup
    ch, hd, RT, XY0, XY1, YX1, xyd = tabs()
    k, n = K, N
    rnd = random.Random(seed)
    occ = {}
    queues = [deque() for _ in range(n)]
    latencies = []
    nfree = [8] * n
    none = chain == 'none'
    c0 = set(o['c0'].split('+')) if o['c0'] else set()
    c1 = set(o['c1'].split('+')) if o['c1'] else set()
    pat, dset, ps, sg, fd = o['pat'], o['dset'], o['ps'], o['sg'], o['fd']
    fs = o['fs']
    sc = o['sc']
    lane = o['lane']
    yld = o['yld']
    dor = o['dor']
    last_inj = [-10 ** 9] * n
    gapG = int(sc[3:]) if sc.startswith('gap') else 0
    ownm = int(sc[3:]) if sc.startswith('own') else 0
    ldm = int(sc[2:]) if sc.startswith('ld') else 0
    moves = chained = 0
    dist = lambda u, d: abs(u % k - d % k) + abs(u // k - d // k)

    def put(c, pk):
        occ[c] = pk
        if c // 2 % 5 != 4:
            nfree[c // 10] -= 1

    def take(c):
        if c // 2 % 5 != 4:
            nfree[c // 10] += 1
        return occ.pop(c)

    def klass(c, u, d, q, src):
        """the classes of a packet in channel c at router u (destination d) taking hop q"""
        cl = set()
        if src:
            cl.add('src')
            if dist(u, d) > fd:
                cl.add('srcfar')
            if 'srcw' in c0 or ('srcwf' in c0 and dist(u, d) > fs):
                # a packet in a link into u waits for the same output direction
                dr = q // 2 % 5
                for vv, dd in ((u - 1, 0), (u + 1, 1), (u - k, 2), (u + k, 3)):
                    if 0 <= vv < n and (dd > 1 or vv // k == u // k):
                        for vc in (0, 1):
                            pq = occ.get(ch(vv, dd, vc))
                            if pq is not None and pq is not GHOST and pq[0] != u and \
                                    xyd[u][pq[0]] == dr:
                                cl.add('srcw')
                                cl.add('srcwf')
        v = hd[q]
        if v == d:
            cl.add('ej')
        elif xyd[v][d] != q // 2 % 5:
            cl.add('turn')
        else:
            cl.add('str')
        if dist(u, d) > fd:
            cl.add('far')
            cl.add('farX' if q // 2 % 5 < 2 else 'farY')
            if 'fary' in c0 or 'farz' in c0:
                # a nearer packet (at most fd hops from its destination) in a link into u or in
                # u's injection channel waits for the same output direction
                dr = q // 2 % 5
                for vv, dd in ((u - 1, 0), (u + 1, 1), (u - k, 2), (u + k, 3), (u, 4)):
                    if dd == 4 and 'fary' not in c0:
                        continue
                    if 0 <= vv < n and (dd > 1 or vv // k == u // k):
                        for vc in ((0, 1) if dd < 4 else (0,)):
                            q2 = ch(vv, dd, vc)
                            if q2 == c:
                                continue
                            pq = occ.get(q2)
                            if pq is not None and pq is not GHOST and pq[0] != u and \
                                    xyd[u][pq[0]] == dr and \
                                    dist(u, pq[0]) <= (fs if dd == 4 and fs >= 0 else fd):
                                cl.add('fary')
                                cl.add('farz')
        return cl

    def useful(q, d):
        v = hd[q]
        if v == d:
            return 99
        return sum(1 for x in RT[v][d] if x not in occ)

    def src_ok(s, u, d):
        if sc == 'up':
            dr = xyd[u][d]
            # the inbound lanes that continue straight through u in direction dr
            back = [u - 1, u + 1, u - k, u + k][dr]
            if 0 <= back < n and (dr > 1 or back // k == u // k):
                for vc in (0, 1):
                    c = ch(back, dr, vc)
                    pk = occ.get(c)
                    if pk is not None and pk is not GHOST and xyd[u][pk[0]] == dr:
                        return False
            return True
        if sc.startswith('own'):
            return 8 - nfree[u] <= ownm
        if sc == 'lane':
            return XY0[u][d] not in occ and XY1[u][d] not in occ
        if sc.startswith('gap'):
            return t - last_inj[s] >= gapG
        if sc.startswith('ld'):
            dr = xyd[u][d]
            cnt = 0
            v = u
            for _ in range(4):
                c = ch(v, dr, 0)
                if hd[c] < 0 or hd[c] >= n or (dr < 2 and hd[c] // k != v // k):
                    break
                cnt += (c in occ) + (c + 1 in occ)
                v = hd[c]
            return cnt <= ldm
        return True

    if diag is not None:
        diag.update(lc=[[0, 0, 0] for _ in range(n * 4)], mv=[0] * (n * 10), blk=[0] * (n * 10),
                    occn=[0] * (n * 10), srcblk=0, srcocc=0, devs=0, ejd=[0] * n, blkt=[0] * (n * 10))
    for t in range(cycles):
        for c in [c for c, v in occ.items() if v is not GHOST and hd[c] == v[0]]:
            _d, born = take(c)[:2]
            if t >= warmup:
                latencies.append(t - born)
                if diag is not None:
                    diag['ejd'][_d] += 1
        if diag is not None and t >= warmup:
            for u in range(n):
                for dr in range(4):
                    diag['lc'][u * 4 + dr][(ch(u, dr, 0) in occ) + (ch(u, dr, 1) in occ)] += 1
            for c in occ:
                diag['occn'][c] += 1
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
            src = c // 2 % 5 == 4
            e0, e1 = XY0[u][d], XY1[u][d]
            pick = []
            if dor != 'xy' and (src and (dor == 'yx' or (dor == 'bis' and pk[3])) or
                                (not src and c % 2 == 1 and pk[3])):
                # a YX packet: YX on VC1, then the escape (XY on VC0, after which it is XY)
                y1 = YX1[u][d]
                if src:
                    pk[3] = 1
                if y1 not in occ and (not src or nfree[hd[y1]] >= sg):
                    pick = [y1]
                elif e0 not in occ and (not src or nfree[hd[e0]] >= sg):
                    pick = [e0]
                    pk[3] = 0
            else:
                cand = []
                if src and sc:
                    if src_ok(c // 10, u, d):
                        cand = [e0, e1]
                else:
                    cand = [e0, e1]
                if yld and not src and xyd[u][d] == c // 2 % 5 and (
                        yld == 'turn' and c // 2 % 5 >= 2 or yld == 'all'):
                    # a packet going straight leaves the VC1 lane to a turner (or, with
                    # 'all', also to a source) waiting at this router for the same direction
                    dr = xyd[u][d]
                    wait = False
                    for q in ((ch(u - 1, 0, 0), ch(u - 1, 0, 1)) if u % k > 0 else ()) + \
                            ((ch(u + 1, 1, 0), ch(u + 1, 1, 1)) if u % k < k - 1 else ()) + \
                            ((ch(u, 4, 0),) if yld == 'all' else ()):
                        pq = occ.get(q)
                        if pq is not None and pq is not GHOST and pq[0] != u and \
                                xyd[u][pq[0]] == dr:
                            wait = True
                            break
                    if wait:
                        cand = [e0]
                if c0 or c1:
                    cl = klass(c, u, d, e0, src)
                    if cl & c0:
                        cand = [e0] if e0 in cand else []
                    elif cl & c1:
                        cand = [e1] if e1 in cand else []
                pick = [q for q in cand if q not in occ and (not src or sc or nfree[hd[q]] >= sg)]
                if lane and len(pick) == 2:
                    # a lane preference with fallback (the other lane when the preferred is taken)
                    if lane == 'vc1':
                        want = 1
                    elif lane == 'keep':
                        want = c % 2 if not src else 0
                    elif lane == 'switch':
                        want = 1 - c % 2 if not src else 1
                    elif lane == 'par':
                        want = (d % k + d // k) % 2
                    else:                    # 'dirn': VC by travel direction
                        want = e0 // 2 % 5 % 2
                    pick = [e1 if want else e0]
                if not pick and not (c1 and klass(c, u, d, e0, src) & c1):
                    if e0 not in occ and (not src or nfree[hd[e0]] >= sg):
                        pick = [e0]
                if not pick and pat >= 0 and not src and pk[2] >= pat:
                    hops = RT[u][d]
                    if dset == 'vc1':
                        dev = [q for q in hops if q % 2 == 1 and q != e1 and q not in occ]
                    else:
                        dev = [q for q in hops if q != e0 and q != e1 and q not in occ]
                    if dev and ps == 'P':
                        top = max(useful(q, d) for q in dev)
                        dev = [q for q in dev if useful(q, d) == top]
                    pick = dev
                    if dev and diag is not None and t >= warmup:
                        diag['devs'] += 1
            if pick:
                c2 = rnd.choice(pick)
                pk = take(c)
                if len(pk) > 2:
                    pk[2] = 0
                put(c2, pk)
                if none:
                    put(c, GHOST)
                moved.add(c2)
                if src:
                    last_inj[c // 10] = t
                if t >= warmup:
                    moves += 1
                    chained += c2 in vacated
                    if diag is not None:
                        diag['mv'][c2] += 1
                vacated.add(c)
            else:
                if len(pk) > 2:
                    pk[2] += 1
                if diag is not None and t >= warmup:
                    if src:
                        diag['srcblk'] += 1
                    else:
                        diag['blk'][c] += 1
                        if xyd[u][d] != c // 2 % 5:
                            diag['blkt'][c] += 1
        if none:
            for c in vacated:
                if occ.get(c) is GHOST:
                    take(c)
        for s in range(n):
            if rnd.random() < rate:
                d = X2.mdest(pattern, s, k, rnd)
                if d != s:
                    queues[s].append((d, t))
            if queues[s] and ch(s, 4, 0) not in occ:
                d, born = queues[s].popleft()
                if pat >= 0 or dor != 'xy':
                    yxbit = 0
                    if dor == 'bis':
                        # YX for packets whose source row is in the lower half and column in the
                        # left half or the reverse: balances the two orders on every bisection
                        yxbit = int((s % k < k // 2) == (s // k < k // 2))
                    put(ch(s, 4, 0), [d, born, 0, yxbit])
                else:
                    put(ch(s, 4, 0), (d, born))
        if diag is not None and t >= warmup:
            diag['srcocc'] += sum(1 for s in range(n) if ch(s, 4, 0) in occ)
    throughput = len(latencies) / ((cycles - warmup) * n)
    latency = sum(latencies) / len(latencies) if latencies else float('nan')
    if diag is not None:
        diag['T'] = cycles - warmup
    return throughput, latency, moves / (cycles - warmup), chained / max(1, moves)


GHOST = X2.GHOST


# ------------------------------------------------------------------ diagnosis
def diagnose(spec, pattern, rate, seed, chain, cycles=2000):
    dg = {}
    thr, lat, mv, chn = bsim(spec, rate, pattern, seed, chain, cycles, diag=dg)
    ch, hd = tabs()[0], tabs()[1]
    T = dg['T']
    k = K
    print(f'{spec or "dualXY"} {pattern} offered {rate} {chain}: throughput {thr:.4f} latency '
          f'{lat:.1f}, moves/cycle {mv:.1f}, chained {chn:.2f}, mean source-lane occupancy '
          f'{dg["srcocc"] / T / N:.3f}, deviations/cycle {dg["devs"] / T:.2f}')
    # bisection links: east/west across x = 3|4, north/south across y = 3|4
    rows = []
    for name, links in (
            ('X-bisection E', [(y * k + 3, 0) for y in range(k)]),
            ('X-bisection W', [(y * k + 4, 1) for y in range(k)]),
            ('Y-bisection N', [(3 * k + x, 2) for x in range(k)]),
            ('Y-bisection S', [(4 * k + x, 3) for x in range(k)]),
            ('X links 2->3 E', [(y * k + 2, 0) for y in range(k)]),
            ('X links 4->5 E', [(y * k + 4, 0) for y in range(k)]),
            ('Y links 2->3 N', [(2 * k + x, 2) for x in range(k)]),
            ('Y links 4->5 N', [(4 * k + x, 2) for x in range(k)])):
        lc = [0, 0, 0]
        m = b = oc = bt = 0
        for u, dr in links:
            for i in range(3):
                lc[i] += dg['lc'][u * 4 + dr][i]
            for vc in (0, 1):
                c = ch(u, dr, vc)
                m += dg['mv'][c]
                b += dg['blk'][c]
                bt += dg['blkt'][c]
                oc += dg['occn'][c]
        L = len(links)
        rows.append((name, [x / (T * L) for x in lc], m / (T * L * 2), oc / (T * L * 2),
                     b / max(1, oc), bt / max(1, b)))
    print(f'{"links":<16}{"P(0/1/2 full)":>22}{"moves/lane":>12}{"occupancy":>11}'
          f'{"P(blocked|occ)":>16}{"turners/blocked":>17}')
    for name, lc, m, oc, b, bt in rows:
        print(f'{name:<16}{lc[0]:>8.3f}{lc[1]:>7.3f}{lc[2]:>7.3f}{m:>12.3f}{oc:>11.3f}{b:>16.3f}'
              f'{bt:>17.3f}')
    print(f'source blocked per cycle per node {dg["srcblk"] / T / N:.3f}')
    return dg


# ------------------------------------------------------------------ driver
def run_one(spec, rate, pattern, seed, chain='seq', cycles=2000):
    kind, _, sp = spec.partition(':')
    if kind == 'B':
        return list(bsim(sp, rate, pattern, seed=seed, chain=chain, cycles=cycles))
    if kind == 'PM':
        import xp_portfolio as PF
        return PF.run_one(spec, rate, pattern, seed, chain, cycles)
    return list(X2.run_one(spec, rate, pattern, seed, chain, cycles))


def check():
    for ch in ('seq', 'none'):
        for p, r in (('bitcomp', 0.3), ('randperm', 0.6), ('uniform', 0.45)):
            a = X2.msim('route=wf:tiers=xy+esc:thr=g0', r, p, seed=3, chain=ch, cycles=900)
            b = bsim('', r, p, seed=3, chain=ch, cycles=900)
            c = X2.run_one('A:R:dualXY:random/random', r, p, 3, ch, 900)
            print('dualXY', ch, p, a[:2], b[:2], c[:2], tuple(a[:2]) == tuple(b[:2]) == tuple(c[:2]))
        a = X2.msim('route=wf:tiers=xy+esc:thr=g4', 0.4, 'bitcomp', seed=5, chain=ch, cycles=900)
        b = bsim('sg=4', 0.4, 'bitcomp', seed=5, chain=ch, cycles=900)
        print('xy g4', ch, a[:2], b[:2], tuple(a[:2]) == tuple(b[:2]))


CACHE = os.environ.get('XP_BC_CACHE', os.path.join(tempfile.gettempdir(), 'xp_bitcomp.json'))


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
    if todo:
        todo.sort(key=lambda j: (j[0].startswith('PM'), j[5]), reverse=True)
        with Pool(int(os.environ.get('XP_BC_PROCS', 3))) as pool:
            new = {}
            for i, (a, r) in enumerate(pool.imap_unordered(_job, todo, chunksize=2)):
                new[a] = list(r)
                if i % 40 == 39:
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
        if len(v) < min(2, len(seeds)):
            continue
        m, se = XP.stats([x[0] for x in v])
        if best is None or m > best[0]:
            best = (m, se, r, len(v))
    return best


def run_cmd(argv):
    specs, pats, rates, seeds, chains = argv[:5]
    cycles = int(argv[5]) if len(argv) > 5 else 2000
    specs, chains, pats = specs.split(','), chains.split(','), X2.pats_of(pats)
    rates = [float(x) for x in rates.split(',')]
    seeds = X2.seedlist(seeds)
    jobs = [(sp, r, p, sd, ch, cycles) for ch in chains for sp in specs for p in pats
            for r in rates for sd in seeds]
    res = compute(jobs)
    print(f'seeds {seeds}, rates {rates}, cycles {cycles}: peak mean ± se (x1e-4) @rate')
    for ch in chains:
        print(f'{ch:<5}{"":<44}' + ''.join(f'{p[:9]:>17}' for p in pats))
        for sp in specs:
            cells = []
            for p in pats:
                m, se, r, _ = cell(res, sp, p, rates, seeds, ch, cycles)
                cells.append(f'{m:.4f}±{se * 1e4:<3.0f}@{r:g}')
            print(f'{ch:<5}{sp[-44:]:<44}' + ''.join(f'{x:>17}' for x in cells), flush=True)


def curve_cmd(argv):
    """curve SPECS PATTERN RATES SEEDS CHAIN [CYCLES]: mean throughput at every rate"""
    specs, pat, rates, seeds, ch = argv[:5]
    cycles = int(argv[5]) if len(argv) > 5 else 2000
    rates = [float(x) for x in rates.split(',')]
    seeds = X2.seedlist(seeds)
    res = compute([(sp, r, pat, sd, ch, cycles) for sp in specs.split(',') for r in rates
                   for sd in seeds])
    print(f'{pat} {ch}: mean throughput at offered ' + ' '.join(f'{r:g}' for r in rates))
    for sp in specs.split(','):
        print(f'{sp[-40:]:<40}' + ''.join(
            f'{XP.stats([res[(sp, r, pat, sd, ch, cycles)][0] for sd in seeds])[0]:>8.4f}'
            for r in rates))


def report(argv):
    """report MAIN OTHERS PATTERNS RATES SEEDS CHAINS [CYCLES]: MAIN against each of OTHERS
    (peak over RATES; per pattern, 'pat=r1/r2/...' in RATES overrides)."""
    main, others, pats, rates, seeds, chains = argv[:6]
    cycles = int(argv[6]) if len(argv) > 6 else 2000
    pats = X2.pats_of(pats)
    others = others.split(',')
    prates = {}
    dflt = []
    for tok in rates.split(','):
        if '=' in tok:
            p, rs = tok.split('=')
            prates[p] = [float(x) for x in rs.split('/')]
        else:
            dflt.append(float(tok))
    seeds = X2.seedlist(seeds)
    res = load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-9, (a[1] ** 2 + b[1] ** 2) ** .5)
    for ch in chains.split(','):
        tab = {sp: [cell(res, sp, p, prates.get(p, dflt), seeds, ch, cycles) for p in pats]
               for sp in [main] + others}
        print(f'\n== chain={ch}, {cycles} cycles, seeds {seeds[0]}..{seeds[-1]} ({len(seeds)}): '
              'peak mean ± se (x1e-4) @rate')
        print(f'{"":<44}' + ''.join(f'{p[:9]:>20}' for p in pats))
        for sp in [main] + others:
            print(f'{sp[-44:]:<44}' + ''.join(
                f'{c[0]:>9.4f}±{c[1] * 1e4:<3.0f}@{c[2]:<5g}' if c else f'{"-":>20}'
                for c in tab[sp]))
        m = tab[main]
        for r in others:
            print(f'{"vs " + r[-41:]:<44}' + ''.join(
                f'{100 * (m[i][0] / tab[r][i][0] - 1):>+12.2f}%{z(m[i], tab[r][i]):>+6.1f}z'
                if m[i] and tab[r][i] else f'{"-":>20}' for i in range(len(pats))))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'check':
        check()
    elif cmd == 'diag':
        a = sys.argv[2:]
        diagnose('' if a[0] == '-' else a[0], a[1], float(a[2]), int(a[3]), a[4],
                 int(a[5]) if len(a) > 5 else 2000)
    elif cmd == 'run':
        run_cmd(sys.argv[2:])
    elif cmd == 'curve':
        curve_cmd(sys.argv[2:])
    elif cmd == 'report':
        report(sys.argv[2:])
