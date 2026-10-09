#!/usr/bin/env python3
"""Routing on the 8 x 8 torus with 2 virtual channels of one-packet buffers (simulation; the
safety of the tree-escape schemes is proved in `Routing/Graph.lean`, `GraphBudget.lean`).

Same mechanics as `routing_graph_sim.py` (random move order, unbounded source queues, source
throttle g = 4, return budget B = 2). Schemes:

* `dor` : dimension order with two dateline virtual channels per ring (Dally & Seitz);
* `min` : `GraphData.net`: VC1 minimal adaptive, VC0 up*/down* spanning-tree escape;
* `val` : Valiant: VC1 minimal adaptive to a random intermediate node, then to the destination;
* `ugal`: UGAL: the source picks minimal or Valiant by hops x occupancy of the first hops;
* `mis2`: minimal adaptive plus up to 2 non-minimal VC1 hops in flight;
* `goal`: GOAL-style: the long way round a ring with probability (distance / k);
* `ringv<a>`, `ringvx<a>`, `ringvd<a>`: the source picks the minimal route, the long way round
  a ring (not in `ringvx`; in `ringvd` only when the long direction is clearly less busy), or a
  random intermediate, by hops x (1 + a * smoothed occupancy of the first hop).
* `cmb<aL>_<aV>_<g>_<m>`: no detour for routes of at most m hops; otherwise a random
  intermediate weighted by aV, else the long way round a ring weighted by aL, only when the
  long direction is less busy by at least g/10.
* `bandit<e>[h<h>]`: each source keeps the smoothed in-network latency of its packets per option
  (minimal, long way in x or y, random intermediate) and picks the fastest, exploring e %; with
  `h`, it switches away from its current option only when another is h % faster; `banditx`
  without the long-way options; `q<q>`: each option's latency is
  multiplied by (its hops / the minimal hops)^(q/10), a price for the extra links it uses; `g<g>`: the long way
  only when its first hop is less busy than the minimal ones by g/10 (smoothed occupancy);
  `m[r]` prices each option by its marginal cost latency^2 / hops^(r/10), r = 10 by default (for a queue with
  latency L and free-flow latency L0 the marginal cost is about L^2 / L0): system-optimal
  instead of selfish choices; `f<f>`: the long way only when the packets leaving the source
  in the long direction are at most f/10 of those leaving in the minimal direction (smoothed
  flow counts, which unlike occupancy still differ at saturation); a trailing `v` gates the
  random intermediate the same way (its first hop against the minimal first hops); a trailing
  `u` instead prices the random intermediate with the minimal hop count (no discount for its
  extra hops).
The escape always heads to the final destination and drops the intermediate.

Usage: python3 scripts/torus_experiments.py dor,min,val,ugal,ringvd30
"""
import random, sys
from collections import deque
from routing_sim import destination
import routing_graph_sim as G

K = 8; N = K*K
def tdest(pattern, s, rnd):
    x, y = s % K, s // K
    if pattern == 'tornado': return (x + K//2 - 1) % K + y*K
    if pattern == 'neighbor': return (x + 1) % K + y*K
    if pattern == 'randperm': return G.RANDPERM[s]
    return destination(pattern, s, K, rnd)

NET = G.Net(G.torus_adj(K), escape='updown', root=27)

def sim(scheme, rate, pattern, g=4, budget=2, mis=2, cycles=4000, warmup=1000, seed=1):
    net = NET; head, esc, vc1, out, dist, adj = net.head, net.esc, net.vc1, net.out, net.dist, net.adj
    rnd = random.Random(seed); occ = {}; queues = [deque() for _ in range(N)]; lat = []
    thr = [g * 2 * net.deg[v] / 8 for v in range(N)]
    allvc1 = [[(u*5+p)*2+1 for p in range(4) if adj[u][p] >= 0] for u in range(N)]
    hopsum = 0
    ema = [[0.0]*4 for _ in range(N)]
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
    fgate = float(scheme.split('f')[1].rstrip('vu')) / 10 if scheme.startswith('bandit') and 'f' in scheme else None
    vgate = scheme.endswith('v')
    vnodisc = scheme.endswith('u')
    moves = [[0] * 4 for _ in range(N)]
    if scheme.startswith('cmb'):
        aL, aV, gt, md = scheme[3:].split('_')
        aL, aV, gt, md = float(aL), float(aV), float(gt) / 10, int(md)
    spec = scheme.lstrip('ringvxd').split('m') if scheme.startswith('ring') else ['3']
    alpha = float(spec[0]) if spec[0] else 3.0
    margin = float(spec[1]) / 10 if len(spec) > 1 else 0.0
    useema = scheme.startswith('ring')
    def longway(s, d, dim):
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
                est[pk[9]][pk[7]] = 0.9 * e0 + 0.1 * (t - pk[8]) if e0 else float(t - pk[8])
        moved = set(); pks = list(occ); rnd.shuffle(pks)
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
                    q = rnd.choice(free)
                    if scheme.startswith('mis') and canret and ti == 1 and pk[5] > 0 and q % 2 == 1 and q not in vc1[u][tgt]:
                        pk[5] -= 1
                    break
            if q is None: continue
            if q % 2 == 0 and not (c % 2 == 0): pk[6] = -1      # escape drops the intermediate
            pk[2] += 1
            if onesc and q % 2 == 1: pk[4] += 1
            occ[q] = occ.pop(c); moved.add(q)
            if fgate is not None and (q // 2) % 5 < 4: moves[q // 10][(q // 2) % 5] += 1
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
                if scheme.startswith('bandit') and dist[s][d] > 1:
                    opts = [(0, -1, dist[s][d])]
                    for dim in ((0, 1) if not scheme.startswith('banditx') else ()):
                        lw = longway(s, d, dim)
                        if lw and (bgate is None or ema[s][lw[1]] + bgate <=
                                   min(ema[s][(c2 // 2) % 5] for c2 in vc1[s][d])) and \
                                (fgate is None or flow[s][lw[1]] <= fgate *
                                 min(flow[s][(c2 // 2) % 5] for c2 in vc1[s][d])):
                            opts.append((1 + dim, lw[0], lw[2]))
                    w = rnd.randrange(N)
                    if w not in (s, d) and not (vgate and fgate is not None and
                            min(flow[s][(c2 // 2) % 5] for c2 in vc1[s][w]) > fgate *
                            min(flow[s][(c2 // 2) % 5] for c2 in vc1[s][d])):
                        opts.append((3, w, dist[s][w] + dist[w][d]))
                    if marg:
                        price = lambda o: est[s][o[0]] ** 2 / (dist[s][d] if vnodisc and o[0] == 3 else o[2]) ** mexp
                    else:
                        price = lambda o: est[s][o[0]] * (o[2] / dist[s][d]) ** qpen
                    if rnd.random() < eps: opt, inter, _ = rnd.choice(opts)
                    else:
                        bo = min(opts, key=price)
                        co = [o for o in opts if o[0] == cur[s]]
                        if co and price(bo) >= price(co[0]) * (1 - hyst): bo = co[0]
                        cur[s] = bo[0]; opt, inter, _ = bo
                if inter in (s, d): inter = -1
                occ[c] = [d, born, 0, dist[s][d], 0, mis if scheme.startswith('mis') else 0, inter,
                          opt, t, s]
    return len(lat)/((cycles-warmup)*N), hopsum/max(1,len(lat))

def sim_dor(rate, pattern, cycles=4000, warmup=1000, seed=1):
    """Dimension-order routing on the torus with two dateline VCs per link (Dally & Seitz):
    in each ring a packet uses VC0 until it crosses the wrap-around link, VC1 after.  Ties at
    distance k/2 go in the positive direction."""
    rnd = random.Random(seed); occ = {}; queues = [deque() for _ in range(N)]; lat = []
    def step(u, d):           # (port, next, wraps)
        x, y, dx, dy = u % K, u // K, d % K, d // K
        if x != dx:
            r = (dx - x) % K
            if r <= K//2: return 0, (x+1) % K + y*K, x == K-1
            return 1, (x-1) % K + y*K, x == 0
        r = (dy - y) % K
        if r <= K//2: return 2, x + ((y+1) % K)*K, y == K-1
        return 3, x + ((y-1) % K)*K, y == 0
    # channel key: (u, port, vc) with head stored
    for t in range(cycles):
        for c in [c for c, p in occ.items() if c[3] == p[0]]:
            pk = occ.pop(c)
            if t >= warmup: lat.append(t - pk[1])
        moved = set(); pks = list(occ); rnd.shuffle(pks)
        for c in pks:
            if c in moved: continue
            pk = occ[c]; u = c[3]; d = pk[0]
            if u == d: continue
            port, v, wrap = step(u, d)
            dimchange = c[1] == 4 or (c[1] < 2) != (port < 2)
            crossed = (0 if dimchange else pk[2]) or wrap
            q = (u, port, 1 if crossed else 0, v)
            if q in occ: continue
            pk[2] = 1 if crossed else 0
            occ[q] = occ.pop(c); moved.add(q)
            if fgate is not None and (q // 2) % 5 < 4: moves[q // 10][(q // 2) % 5] += 1
        if fgate is not None:
            for u in range(N):
                for p in range(4):
                    flow[u][p] = 0.98 * flow[u][p] + 0.02 * moves[u][p]; moves[u][p] = 0
        for s in range(N):
            if rnd.random() < rate:
                d = tdest(pattern, s, rnd)
                if d != s: queues[s].append((d, t))
            c = (s, 4, 0, s)
            if queues[s] and c not in occ:
                d, born = queues[s].popleft(); occ[c] = [d, born, 0]
    return len(lat)/((cycles-warmup)*N), 0

PATS = ['uniform', 'transpose', 'shuffle', 'bitrev', 'bitcomp', 'hotspot', 'tornado', 'neighbor', 'randperm']
def job(a):
    scheme, rate, p, seed = a
    if scheme == 'dor': return sim_dor(rate, p, seed=seed)[0]
    if scheme == 'min0': return sim('min', rate, p, g=0, seed=seed)[0]
    return sim(scheme, rate, p, seed=seed)[0]

if __name__ == '__main__':
    from multiprocessing import Pool
    schemes = sys.argv[1].split(',')
    rates = [0.4, 0.6, 0.8, 1.0]
    jobs = [(s, r, p, sd) for s in schemes for r in rates for p in PATS for sd in (1, 2)]
    with Pool() as pool: res = dict(zip(jobs, pool.map(job, jobs)))
    print(f'{"scheme":<10}' + ''.join(f'{p[:9]:>10}' for p in PATS))
    for s in schemes:
        print(f'{s:<10}' + ''.join(f'{max((res[(s,r,p,1)]+res[(s,r,p,2)])/2 for r in rates):>10.3f}' for p in PATS), flush=True)
