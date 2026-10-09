#!/usr/bin/env python3
"""Backpressure-style selections and arbitration orders on the 8 x 8 mesh and torus
(simulation only; nothing here is proved).

Ideas from queueing theory (max-weight / backpressure, age-based arbitration), adapted to
one-packet lanes.  The mechanics are those of `routing_sim.simulate` (mesh, `duatoMesh` with
`T4:tiered`) and `torus_experiments.sim` (torus, copied below with hooks), kept identical:
with `sel=tiered|base`, `order=random`, `thr=g4` both reproduce the originals bit for bit
(`--check`).

Selections (applied among the free hops of the tier that `tieredMesh` / the torus scheme
picks; they read only the current configuration):
  tiered / base   the original (uniformly random among the tier's free hops)
  D               the hop into the router with the most free outgoing channels (= flag C of
                  torus_experiments; the occupancy differential to the current router, whose
                  count is the same for every candidate)
  P               the hop into the router with the most free channels *this packet may use
                  next* (its permitted hops there; destination reached = best)
  X<delta>        mesh: as P, and leave the preferred tier for a free VC1 hop whose P-score is
                  at least delta higher (a configuration-dependent tier list)
Arbitration orders (who moves first in a cycle; in hardware the arbiter):
  random          uniformly random order (the original)
  g:<key>         one global order by <key> (changes which channel frees first, i.e. how many
                  moves chain within a cycle, not only arbitration)
  l:<key>         the random global interleaving is kept; only the packets competing at the
                  same router (the only ones that can want the same output) are re-ordered by
                  <key> -- arbitration only
  rr              l: with per-router round-robin over the 10 input lanes (pointer moves past
                  the first winner)
  keys: old (oldest packet first), young, wait (longest in its current lane first), esc
  (escape VC0, then VC1, then injection), inj (injection lane last)
Source throttles (mesh): g<n> = at least n (g4: 4 of the next router's 8 outputs free (original);
  tA = g4 or the next router at least as free as the source router; tB = g4 and the next
  router at most 2 less free than the source router.

Usage:
  python3 scripts/xp_backpressure.py --check
  python3 scripts/xp_backpressure.py mesh 'tiered/random/g4,D/l:old/g4' uniform,transpose 0.4,0.5 1,2,3,4
  python3 scripts/xp_backpressure.py torus 'min/base/random,min/D/l:old' uniform 0.7,0.8 11,12
Prints, per variant and pattern, the peak (over the rates) of the mean accepted throughput,
its standard error over the seeds, moves per cycle and the fraction of chained moves (into a
channel vacated earlier in the same cycle).
"""
import random
import sys
from collections import deque

from routing_sim import mesh, destination
import routing_graph_sim as G


# ------------------------------------------------------------------ arbitration orders
def make_order(order, hd, keyfns, rnd):
    """Returns f(pks) -> ordered list (pks = list(occ), already in dict order)."""
    if order == 'random':
        def f(pks, t):
            rnd.shuffle(pks)
            return pks
        return f
    if order == 'rr':
        def f(pks, t):
            rnd.shuffle(pks)
            return local(pks, hd, keyfns['rr'])
        return f
    scope, key = order.split(':')
    kf = keyfns[key]
    if scope == 'g':
        def f(pks, t):
            rnd.shuffle(pks)
            pks.sort(key=kf)
            return pks
        return f

    def f(pks, t):
        rnd.shuffle(pks)
        return local(pks, hd, kf)
    return f


def local(pks, hd, kf):
    groups = {}
    for i, c in enumerate(pks):
        groups.setdefault(hd[c], []).append(i)
    out = pks[:]
    for idx in groups.values():
        if len(idx) > 1:
            for i, c in zip(idx, sorted((pks[i] for i in idx), key=kf)):
                out[i] = c
    return out


def stats(res):
    m = sum(res) / len(res)
    se = (sum((a - m) ** 2 for a in res) / (len(res) - 1)) ** .5 / len(res) ** .5 if len(res) > 1 else 0.0
    return m, se


# ------------------------------------------------------------------ mesh
_MESH = {}


def mesh_tables(k):
    if k in _MESH:
        return _MESH[k]
    ch, head, routes = mesh(k)
    n = k * k
    hd = [head(c) for c in range(n * 10)]
    xy = lambda u, d: 0 if u % k < d % k else 1 if d % k < u % k else 2 if u // k < d // k else 3
    yx = lambda u, d: 2 if u // k < d // k else 3 if d // k < u // k else xy(u, d)
    route = routes['duatoMesh']
    R = [[route(ch(u, 4, 0), d) if u != d else [] for d in range(n)] for u in range(n)]
    XY = [[ch(u, xy(u, d), 0) if u != d else -1 for d in range(n)] for u in range(n)]
    YX = [[ch(u, yx(u, d), 1) if u != d else -1 for d in range(n)] for u in range(n)]
    _MESH[k] = (ch, hd, R, XY, YX)
    return _MESH[k]


def mesh_sim(k, rate, pattern, sel='tiered', order='random', thr='g4', cycles=6000,
             warmup=2000, seed=1):
    """`routing_sim.simulate(k, duatoMesh, rate, pattern, 'T4:tiered')` with hooks."""
    ch, hd, R, XY, YX = mesh_tables(k)
    rnd = random.Random(seed)
    n = k * k
    occ = {}
    queues = [deque() for _ in range(n)]
    latencies = []
    nfree = [8] * n                   # free outgoing channels (of 8, missing ones count free)
    since = {}                        # channel -> cycle its packet entered it
    ptr = [0] * n
    g = 4
    delta = int(sel[1:]) if sel.startswith('X') else None

    def useful(q, d):                 # free channels the packet may take at the next router
        v = hd[q]
        if v == d:
            return 99
        return sum(1 for x in R[v][d] if x not in occ)

    keyfns = {'old': lambda c: occ[c][1], 'young': lambda c: -occ[c][1],
              'wait': lambda c: since[c],
              'esc': lambda c: 2 if c // 2 % 5 == 4 else c % 2,
              'inj': lambda c: c // 2 % 5 == 4,
              'eo': lambda c: (2 if c // 2 % 5 == 4 else c % 2, occ[c][1]),
              'io': lambda c: (c // 2 % 5 == 4, occ[c][1]),
              'if': lambda c: c // 2 % 5 != 4,
              'rr': lambda c: (c % 10 - ptr[hd[c]]) % 10}
    arrange = make_order(order, hd, keyfns, rnd)
    moves = chained = 0

    def put(c, pk):
        occ[c] = pk
        if c // 2 % 5 != 4:
            nfree[c // 10] -= 1

    def take(c):
        if c // 2 % 5 != 4:
            nfree[c // 10] += 1
        return occ.pop(c)

    for t in range(cycles):
        for c in [c for c, (d, _) in occ.items() if hd[c] == d]:
            _, born = take(c)
            if t >= warmup:
                latencies.append(t - born)
        moved = set()
        vacated = set()
        won = {}
        packets = arrange(list(occ), t)
        for c in packets:
            if c in moved or c not in occ:
                continue
            d, _ = occ[c]
            u = hd[c]
            if u == d:
                continue
            hops = R[u][d]
            free = [c2 for c2 in hops if c2 not in occ]
            src = c // 2 % 5 == 4
            if src:
                if thr[0] == 'g':
                    free = [c2 for c2 in free if nfree[hd[c2]] >= int(thr[1:])]
                elif thr == 'tA':
                    free = [c2 for c2 in free if nfree[hd[c2]] >= g or nfree[hd[c2]] >= nfree[u]]
                elif thr == 'tB':
                    free = [c2 for c2 in free if nfree[hd[c2]] >= g and nfree[hd[c2]] >= nfree[u] - 2]
            esc = XY[u][d]
            pref = esc if c % 2 == 0 and not src else YX[u][d]
            tiers = (lambda q: q == pref or (src and q == esc), lambda q: q == esc,
                     lambda q: q % 2 == 1)
            for ti, tier in enumerate(tiers):
                if any(tier(q) for q in free):
                    if delta is not None and ti == 0:
                        best = max(useful(q, d) for q in free if tier(q))
                        alt = [q for q in free if q % 2 == 1 and useful(q, d) >= best + delta]
                        if alt:
                            free = alt
                            break
                    free = [q for q in free if tier(q)]
                    break
            else:
                free = []
            if len(free) > 1 and sel != 'tiered':
                score = (lambda q: nfree[hd[q]]) if sel == 'D' else (lambda q: useful(q, d))
                top = max(score(q) for q in free)
                free = [q for q in free if score(q) == top]
            if free:
                c2 = rnd.choice(free)
                put(c2, take(c))
                moved.add(c2)
                vacated.add(c)
                if t >= warmup:
                    moves += 1
                    chained += c2 in vacated
                since[c2] = t
                if u not in won:
                    won[u] = c % 10
        if order == 'rr':
            for u, lane in won.items():
                ptr[u] = (lane + 1) % 10
        for s in range(n):
            if rnd.random() < rate:
                d = destination(pattern, s, k, rnd)
                if d != s:
                    queues[s].append((d, t))
            if queues[s] and ch(s, 4, 0) not in occ:
                put(ch(s, 4, 0), queues[s].popleft())
                since[ch(s, 4, 0)] = t
    throughput = len(latencies) / ((cycles - warmup) * n)
    latency = sum(latencies) / len(latencies) if latencies else float('nan')
    return throughput, latency, moves / (cycles - warmup), chained / max(1, moves)


# ------------------------------------------------------------------ torus
K = 8; N = K*K
def tdest(pattern, s, rnd):
    x, y = s % K, s // K
    if pattern == 'tornado': return (x + K//2 - 1) % K + y*K
    if pattern == 'neighbor': return (x + 1) % K + y*K
    if pattern == 'randperm': return G.RANDPERM[s]
    return destination(pattern, s, K, rnd)

TOPO = 'torus'
NET = G.Net(G.torus_adj(K), escape='updown', root=27)

# a copy of torus_experiments.sim; changes marked `# xp`
def sim(scheme, rate, pattern, g=4, budget=2, mis=2, cycles=4000, warmup=1000, seed=1,
        sel='base', order='random'):   # xp: sel, order
    flagC, flagY, flagA = 'C' in scheme, 'Y' in scheme, 'A' in scheme
    scheme = scheme.replace('C', '').replace('Y', '').replace('A', '')
    net = NET; head, esc, vc1, out, dist, adj = net.head, net.esc, net.vc1, net.out, net.dist, net.adj
    rnd = random.Random(seed); occ = {}; queues = [deque() for _ in range(N)]; lat = []
    thr = [g * 2 * net.deg[v] / 8 for v in range(N)]
    allvc1 = [[(u*5+p)*2+1 for p in range(4) if adj[u][p] >= 0] for u in range(N)]
    hopsum = 0
    ema = [[0.0]*4 for _ in range(N)]
    if scheme.startswith('fg'):
        pL, pV, fL, fV = (float(x) / 100 for x in scheme[2:].split('_'))
    if scheme.startswith('bandit'):
        bspec = scheme.lstrip('banditx').split('f')[0].split('m')[0].split('q')[0].split('g')[0].split('h')
        eps = float(bspec[0]) / 100 if bspec[0] else 0.05
        hyst = float(bspec[1]) / 100 if len(bspec) > 1 and bspec[1] else 0.0
        qpen = float(scheme.split('q')[1].split('g')[0]) / 10 if 'q' in scheme else 0.0
        bgate = float(scheme.split('g')[1]) / 10 if 'g' in scheme else None
        marg = 'm' in scheme[6:].split('f')[0]
        mtail = scheme.split('f')[0].split('m')[-1]
        mexp = float(mtail) / 10 if marg and mtail else 1.0
    cur = [0] * N                            # bandit: the option each source currently uses
    est = [[0.0] * 4 for _ in range(N)]     # bandit: smoothed network latency per source and option
    flow = [[0.0] * 4 for _ in range(N)]    # smoothed packets per cycle through each output port
    fgate = float(scheme.split('kr')[0].rstrip('nk').split('e')[0].split('f')[1].split('v')[0].rstrip('u')) / 10 if scheme.startswith('bandit') and 'f' in scheme else None
    if scheme.startswith('fg'): fgate = 0.0
    vgate = 'v' in scheme[6:]
    vnodisc = scheme.endswith('u')
    perhop = scheme.startswith('bandit') and scheme.endswith('n')
    focus = scheme.startswith('bandit') and ('kr' in scheme or scheme.endswith('k'))
    rmarg = float(scheme.split('kr')[-1].split('w')[0]) / 100 if scheme.startswith('bandit') and 'kr' in scheme else 0.0
    vmarg = float(scheme.split('w')[-1]) / 100 if scheme.startswith('bandit') and 'kr' in scheme and 'w' in scheme.split('kr')[-1] else rmarg
    recent = [deque(maxlen=8) for _ in range(N)]   # the last destinations of each source
    vextra = int(scheme.split('kr')[0].rstrip('nk').split('e')[-1]) if scheme.startswith('bandit') and 'e' in scheme[6:] else None
    vtail = scheme.split('kr')[0].rstrip('nk').split('e')[0].split('v')[-1] if vgate else ''
    vthr = (float(vtail) / 10 if vtail else (fgate or 0)) if vgate else 0
    moves = [[0] * 4 for _ in range(N)]
    if scheme.startswith('cmb'):
        aL, aV, gt, md = scheme[3:].split('_')
        aL, aV, gt, md = float(aL), float(aV), float(gt) / 10, int(md)
    spec = scheme.lstrip('ringvxd').split('m') if scheme.startswith('ring') else ['3']
    alpha = float(spec[0]) if spec[0] else 3.0
    margin = float(spec[1]) / 10 if len(spec) > 1 else 0.0
    useema = scheme.startswith('ring')
    since = {}; ptr = [0] * N; nmv = nchain = 0          # xp
    keyfns = {'old': lambda c: occ[c][1], 'young': lambda c: -occ[c][1],
              'wait': lambda c: since.get(c, 0),
              'esc': lambda c: 2 if c // 2 % 5 == 4 else c % 2,
              'inj': lambda c: c // 2 % 5 == 4,
              'eo': lambda c: (2 if c // 2 % 5 == 4 else c % 2, occ[c][1]),
              'io': lambda c: (c // 2 % 5 == 4, occ[c][1]),
              'if': lambda c: c // 2 % 5 != 4,
              'rr': lambda c: (c % 10 - ptr[head[c]]) % 10}
    arrange = make_order(order, head, keyfns, rnd)
    if flagC: sel = 'D'
    def useful(x, d, tgt):                               # xp: free hops usable at the next router
        v = head[x]
        if v == tgt: return 99
        return sum(1 for o in vc1[v][tgt] if o not in occ) + (esc[x][d] not in occ)
    def longway(s, d, dim):
        if TOPO == 'mesh': return None            # no wrap-around: no long way round
        x, dx = (s % K, d % K) if dim == 0 else (s // K, d // K)
        r = (dx - x) % K
        if r == 0 or 2*r == K: return None
        short = 1 if r < K - r else -1
        delta = min(r, K - r); m = K//2 - delta + 1
        nx = (x - short*m) % K
        w = nx + (s // K)*K if dim == 0 else (s % K) + nx*K
        port = (1 if short == 1 else 0) if dim == 0 else (3 if short == 1 else 2)
        return w, port, K - delta + (dist[s][d] - delta)
    for t in range(cycles):
        if scheme.startswith('ring') or scheme.startswith('cmb') or 'g' in scheme[6:]:
            for u in range(N):
                for p in range(4):
                    if adj[u][p] >= 0:
                        b = 1.0 if (u*5+p)*2+1 in occ else 0.0
                        ema[u][p] = 0.9*ema[u][p] + 0.1*b
        for c in [c for c, p in occ.items() if head[c] == p[0]]:
            pk = occ.pop(c)
            if t >= warmup: lat.append(t-pk[1]); hopsum += pk[2]
            if len(pk) > 9:
                e0 = est[pk[9]][pk[7]]
                x = (t - pk[8]) / max(1, pk[2]) if perhop else t - pk[8]
                est[pk[9]][pk[7]] = 0.9 * e0 + 0.1 * x if e0 else float(x)
        moved = set(); vacated = set(); won = {}; pks = arrange(list(occ), t)   # xp
        for c in pks:
            if c in moved: continue
            pk = occ[c]; d = pk[0]; u = head[c]
            if u == d: continue
            src = c // 2 % 5 == 4
            if pk[6] >= 0 and u == pk[6]: pk[6] = -1          # reached the intermediate
            tgt = pk[6] if pk[6] >= 0 else d
            e = esc[c][d]
            onesc = c % 2 == 0 and not src
            canret = not (onesc and pk[4] >= budget)
            tiers = []
            if canret:
                tiers.append(vc1[u][tgt])
                if scheme.startswith('mis') and pk[5] > 0:
                    tiers.append([q for q in allvc1[u] if q not in vc1[u][tgt]])
            tiers.append([e])
            q = None
            for ti, tier in enumerate(tiers):
                free = [x for x in tier if x not in occ]
                if g and src: free = [x for x in free if sum(1 for o in out[head[x]] if o not in occ) >= thr[head[x]]]
                if free:
                    if sel != 'base' and len(free) > 1:     # xp
                        score = (lambda x: sum(1 for o in out[head[x]] if o not in occ)) if sel == 'D' \
                            else (lambda x: useful(x, d, tgt))
                        top = max(score(x) for x in free)
                        free = [x for x in free if score(x) == top]
                    q = rnd.choice(free)
                    if scheme.startswith('mis') and canret and ti == 1 and pk[5] > 0 and q % 2 == 1 and q not in vc1[u][tgt]:
                        pk[5] -= 1
                    break
            if q is None: continue
            if q % 2 == 0 and not (c % 2 == 0): pk[6] = -1      # escape drops the intermediate
            pk[2] += 1
            if onesc and q % 2 == 1: pk[4] += 1
            occ[q] = occ.pop(c); moved.add(q)
            vacated.add(c); since[q] = t                      # xp
            if t >= warmup: nmv += 1; nchain += q in vacated
            if u not in won: won[u] = c % 10
            if fgate is not None and (q // 2) % 5 < 4: moves[q // 10][(q // 2) % 5] += 1
        if order == 'rr':                                    # xp
            for u, lane in won.items(): ptr[u] = (lane + 1) % 10
        if fgate is not None:
            for u in range(N):
                for p in range(4):
                    flow[u][p] = 0.98 * flow[u][p] + 0.02 * moves[u][p]; moves[u][p] = 0
        for s in range(N):
            if rnd.random() < rate:
                d = tdest(pattern, s, rnd)
                if d != s: queues[s].append((d, t))
            c = s*10 + 8
            if queues[s] and c not in occ:
                d, born = queues[s].popleft()
                inter = -1
                if scheme == 'val':
                    inter = rnd.randrange(N)
                elif scheme.startswith('ugal'):
                    w = rnd.randrange(N)
                    busy = lambda tg: sum(1 for x in vc1[s][tg] if x in occ) / max(1, len(vc1[s][tg]))
                    hm, hv = dist[s][d], dist[s][w] + dist[w][d]
                    if (busy(w) + 0.1) * hv < (busy(d) + 0.1) * hm: inter = w
                elif scheme.startswith('ring'):
                    mp = [(c2 // 2) % 5 for c2 in vc1[s][d]]
                    best = dist[s][d] * (1 + alpha*min(ema[s][p] for p in mp)) / (1 + margin)
                    for dim in ((0, 1) if not scheme.startswith('ringvx') else ()):
                        lw = longway(s, d, dim)
                        if lw and not (scheme.startswith('ringvd') and ema[s][lw[1]] + 0.3 > min(ema[s][p] for p in mp)):
                            cost = lw[2] * (1 + alpha*ema[s][lw[1]])
                            if cost < best: best, inter = cost, lw[0]
                elif scheme == 'goal':
                    for dim in (0, 1):
                        lw = longway(s, d, dim)
                        if lw:
                            x, dx = (s % K, d % K) if dim == 0 else (s // K, d // K)
                            delta = min((dx-x) % K, (x-dx) % K)
                            if rnd.random() < delta / K: inter = lw[0]; break
                if scheme.startswith('ringv'):
                    w = rnd.randrange(N)
                    if w not in (s, d):
                        mpw = [(c2 // 2) % 5 for c2 in vc1[s][w]]
                        cost = (dist[s][w] + dist[w][d]) * (1 + alpha*min(ema[s][p] for p in mpw))
                        if cost < best: best, inter = cost, w
                elif scheme.startswith('cmb') and dist[s][d] > md:
                    mp = [(c2 // 2) % 5 for c2 in vc1[s][d]]
                    em = min(ema[s][p] for p in mp)
                    best = dist[s][d] * (1 + aV*em); bestL = dist[s][d] * (1 + aL*em)
                    w = rnd.randrange(N)
                    if w not in (s, d):
                        mpw = [(c2 // 2) % 5 for c2 in vc1[s][w]]
                        cost = (dist[s][w] + dist[w][d]) * (1 + aV*min(ema[s][p] for p in mpw))
                        if cost < best: inter = w
                    if inter < 0:
                        for dim in (0, 1):
                            lw = longway(s, d, dim)
                            if lw and ema[s][lw[1]] + gt <= em:
                                cost = lw[2] * (1 + aL*ema[s][lw[1]])
                                if cost < bestL: bestL, inter = cost, lw[0]
                opt = 0
                if scheme.startswith('fg') and dist[s][d] > 1:
                    recent[s].append(d)
                    mports = [(c2 // 2) % 5 for c2 in vc1[s][d]]
                    fmin = min(flow[s][p] for p in mports)
                    done = False
                    for dim in (0, 1):
                        lw = longway(s, d, dim)
                        if lw and flow[s][lw[1]] <= fL * fmin and rnd.random() < pL:
                            inter, opt, done = lw[0], 1 + dim, True
                            break
                    if not done and len(set(recent[s])) <= 2:
                        others = [p for p in range(4) if adj[s][p] >= 0 and p not in mports]
                        if others and min(flow[s][p] for p in others) <= fV * fmin and rnd.random() < pV:
                            w = rnd.randrange(N)
                            if w not in (s, d): inter, opt = w, 3
                if scheme.startswith('bandit') and dist[s][d] > 1:
                    opts = [(0, -1, dist[s][d])]
                    for dim in ((0, 1) if not scheme.startswith('banditx') else ()):
                        lw = longway(s, d, dim)
                        if lw and (bgate is None or ema[s][lw[1]] + bgate <=
                                   min(ema[s][(c2 // 2) % 5] for c2 in vc1[s][d])) and \
                                (fgate is None or flow[s][lw[1]] <= fgate *
                                 min(flow[s][(c2 // 2) % 5] for c2 in vc1[s][d])):
                            opts.append((1 + dim, lw[0], lw[2]))
                    recent[s].append(d)
                    w = rnd.randrange(N)
                    if focus and len(set(recent[s])) > 2:
                        w = s
                    if vextra is not None:
                        for _ in range(30):
                            if dist[s][w] + dist[w][d] <= dist[s][d] + vextra: break
                            w = rnd.randrange(N)
                        else:
                            w = s
                    if flagY or (flagA and len(opts) == 1): w = s
                    if w not in (s, d) and not (vgate and fgate is not None and
                            min(flow[s][(c2 // 2) % 5] for c2 in vc1[s][w]) > vthr *
                            min(flow[s][(c2 // 2) % 5] for c2 in vc1[s][d])):
                        opts.append((3, w, dist[s][w] + dist[w][d]))
                    if perhop:
                        price = lambda o: (est[s][o[0]] * o[2]) ** 2 / o[2] ** mexp
                    elif marg:
                        price = lambda o: est[s][o[0]] ** 2 / (dist[s][d] if vnodisc and o[0] == 3 else o[2]) ** mexp
                    else:
                        price = lambda o: est[s][o[0]] * (o[2] / dist[s][d]) ** qpen
                    if rnd.random() < eps: opt, inter, _ = rnd.choice(opts)
                    else:
                        bo = min(opts, key=price)
                        if bo[0] != 0 and price(bo) > (1 - (vmarg if bo[0] == 3 else rmarg)) * price(opts[0]):
                            bo = opts[0]
                        co = [o for o in opts if o[0] == cur[s]]
                        if co and price(bo) >= price(co[0]) * (1 - hyst): bo = co[0]
                        cur[s] = bo[0]; opt, inter, _ = bo
                if inter in (s, d): inter = -1
                occ[c] = [d, born, 0, dist[s][d], 0, mis if scheme.startswith('mis') else 0, inter,
                          opt, t, s]
                since[c] = t                                     # xp
    return len(lat)/((cycles-warmup)*N), hopsum/max(1,len(lat)), nmv/(cycles-warmup), nchain/max(1, nmv)


# ------------------------------------------------------------------ driver
def run_one(topo, spec, rate, pattern, seed, cycles=None):
    parts = spec.split('/')
    if topo == 'mesh':
        sel = parts[0]; order = parts[1] if len(parts) > 1 else 'random'
        thr = parts[2] if len(parts) > 2 else 'g4'
        kw = {} if cycles is None else {'cycles': cycles, 'warmup': cycles // 3}
        return mesh_sim(8, rate, pattern, sel, order, thr, seed=seed, **kw)
    scheme = parts[0]; sel = parts[1] if len(parts) > 1 else 'base'
    order = parts[2] if len(parts) > 2 else 'random'
    kw = {} if cycles is None else {'cycles': cycles, 'warmup': cycles // 4}
    return sim(scheme, rate, pattern, sel=sel, order=order, seed=seed, **kw)


def check():
    import routing_sim as R
    import torus_experiments as T
    a = R.simulate(8, R.mesh(8)[2]['duatoMesh'], 0.45, 'transpose', 'T4:tiered', cycles=1500,
                   warmup=500, seed=3)
    b = mesh_sim(8, 0.45, 'transpose', cycles=1500, warmup=500, seed=3)
    print('mesh ', a, b[:2], a == b[:2])
    for sch in ('min', 'minC', 'bandit2m7f5k'):
        a = T.sim(sch, 0.7, 'tornado', cycles=1200, warmup=300, seed=5)
        b = sim(sch, 0.7, 'tornado', cycles=1200, warmup=300, seed=5)
        print('torus', sch, a, b[:2], a == b[:2])


def main():
    if sys.argv[1] == '--check':
        check()
        return
    import time
    topo, specs, pats = sys.argv[1], sys.argv[2].split(','), sys.argv[3].split(',')
    rates = [float(x) for x in sys.argv[4].split(',')]
    seeds = [int(x) for x in sys.argv[5].split(',')]
    cycles = int(sys.argv[6]) if len(sys.argv) > 6 else None
    print(f'{topo}, seeds {seeds}, rates {rates}, cycles {cycles or "default"}: '
          'peak mean ± se (x1e-4) [rate, moves/cycle, chained]', flush=True)
    for spec in specs:
        t0 = time.time()
        cells = []
        for p in pats:
            res = {r: [run_one(topo, spec, r, p, sd, cycles) for sd in seeds] for r in rates}
            r = max(rates, key=lambda r: sum(x[0] for x in res[r]))
            m, se = stats([x[0] for x in res[r]])
            mv = sum(x[2] for x in res[r]) / len(seeds); chn = sum(x[3] for x in res[r]) / len(seeds)
            cells.append(f'{p[:8]} {m:.4f}±{se * 1e4:.0f} [{r},{mv:.0f},{chn:.2f}]')
            print('  ', spec, cells[-1], flush=True)
        print(f'{spec:<22}' + ' | '.join(cells) + f'  ({time.time() - t0:.0f}s)', flush=True)


if __name__ == '__main__':
    main()
