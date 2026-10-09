#!/usr/bin/env python3
"""Experiment (simulation only, nothing here is proved): routing by LINK PRICES that grow
exponentially with the load (Garg-Koenemann / Fleischer multiplicative weights).

1. `fluid`: multiplicative weights on the fluid model of `graph_certificates.py` (8 x 8 torus,
   capacity 2 per directed link).  Every phase routes every commodity on its cheapest path
   under the lengths len_e = exp(eps * load_e / cap_e) (load_e = flow so far / phases); the
   average flow scaled to capacity is a feasible theta (primal), and any lengths give the
   upper bound sum cap*len / sum dem*dist_len (`Fluid.potential_bound`, weak LP duality).
   Both are compared with the exact LP optimum (HiGHS, `graph_certificates.lp_dual`).

2. `sim_price`: packets, with the mechanics of `torus_experiments.sim` (same network NET,
   2 VCs of one-packet buffers, VC1 minimal adaptive towards the target, VC0 up*/down*
   spanning-tree escape towards the destination, return budget B = 2, throttle g = 4, random
   move order).  Each directed link keeps a smoothed load (flow of packets per cycle, EMA
   with factor a, plus optionally its occupancy), its price is exp(eps * load); a distance
   vector table C[u][t] = cheapest MINIMAL route u -> t under the prices is relaxed one
   Bellman-Ford step every cycle (a hop of propagation per cycle).  Options:
     * source: intermediate w minimising C[s][w] + C[w][d] (+ bias per extra hop), among
       `all` nodes, the two long-way-round nodes (`ring`), or `none`; a detour is taken only
       when cheaper than the minimal route by the margin m;
     * adaptive hops: among the free VC1 minimal hops, the cheapest price[u][p] + C[v][tgt]
       (`hop=price`) or a random one (`hop=rand`, as `min`).
   Both choices stay inside `detourNet` (`Routing/GraphDetour.lean`): an intermediate picked
   at the source, minimal adaptive hops, the unchanged tree escape and budget.

Usage: python3 scripts/xp_prices.py fluid
       python3 scripts/xp_prices.py sim <spec> <patterns> <rates> <seeds>
"""
import heapq
import math
import os
import random
import sys
from collections import deque

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


# ------------------------------------------------------------------ 1. fluid check
def fluid(eps=0.5, phases=400, pats=None):
    import graph_certificates as GC
    g = GC.TORUS
    L = len(g.links)
    out = {u: [] for u in range(GC.N)}
    for li, (u, _, v) in enumerate(g.links):
        out[u].append((li, v))
    dems = GC.demands()
    pats = pats or ['tornado', 'transpose', 'shuffle', 'neighbor', 'bitrev', 'bitcomp',
                    'uniform', 'hotspot']
    print(f'{"pattern":<10}{"LP opt":>9}{"MW primal":>11}{"MW dual":>10}{"primal/opt":>11}'
          f'{"dual/opt":>10}  (eps {eps}, {phases} phases)')
    for p in pats:
        dem = dems[p]
        com = [(s, [(d, float(dem[s][d])) for d in range(GC.N) if dem[s][d]])
               for s in range(GC.N)]
        com = [(s, ds) for s, ds in com if ds]
        flow = np.zeros(L)
        best_dual = math.inf
        best_primal = 0.0
        for ph in range(1, phases + 1):
            for s, ds in com:
                # prices from the average load so far (flow / completed phases)
                ln = np.exp(eps * flow / max(ph - 1, 1) / GC.CAP)
                dist = [math.inf] * GC.N
                pred = [-1] * GC.N
                dist[s] = 0.0
                h = [(0.0, s)]
                while h:
                    du, u = heapq.heappop(h)
                    if du > dist[u]:
                        continue
                    for li, v in out[u]:
                        nd = du + ln[li]
                        if nd < dist[v] - 1e-15:
                            dist[v], pred[v] = nd, li
                            heapq.heappush(h, (nd, v))
                for d, a in ds:
                    v = d
                    while v != s:
                        li = pred[v]
                        flow[li] += a
                        v = g.links[li][0]
            # primal: the average flow routes theta = 1 per phase, scaled to capacity
            best_primal = max(best_primal, ph / (flow.max() / GC.CAP))
            # dual: the current lengths (potential bound)
            ln = np.exp(eps * flow / ph / GC.CAP)
            den = 0.0
            for s, ds in com:
                dist = [math.inf] * GC.N
                dist[s] = 0.0
                h = [(0.0, s)]
                while h:
                    du, u = heapq.heappop(h)
                    if du > dist[u]:
                        continue
                    for li, v in out[u]:
                        if du + ln[li] < dist[v]:
                            dist[v] = du + ln[li]
                            heapq.heappush(h, (dist[v], v))
                den += sum(a * dist[d] for d, a in ds)
            best_dual = min(best_dual, GC.CAP * ln.sum() / den)
        opt, _ = GC.lp_dual(g, dem, False)
        print(f'{p:<10}{opt:>9.4f}{best_primal:>11.4f}{best_dual:>10.4f}'
              f'{best_primal / opt:>11.4f}{best_dual / opt:>10.4f}', flush=True)


if __name__ == '__main__' and sys.argv[1:2] == ['fluid']:
    e = float(sys.argv[2]) if len(sys.argv) > 2 else 0.5
    ph = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    fluid(e, ph, sys.argv[4].split(',') if len(sys.argv) > 4 else None)
    sys.exit()


# ------------------------------------------------------------------ 2. packets
import torus_experiments as T    # NET honours TOPO=mesh

K, N = T.K, T.N
NET = T.NET
_adj = np.array(NET.adj)
NBR = np.where(_adj >= 0, _adj, 0)
_dist = np.array(NET.dist)
# PROD[u, p, t]: port p of u is a minimal hop towards t
PROD = np.zeros((N, 4, N), bool)
for u in range(N):
    for p in range(4):
        v = NET.adj[u][p]
        if v >= 0:
            PROD[u, p] = _dist[v] == _dist[u] - 1
PRODINF = np.where(PROD, 0.0, np.inf)
EYE = np.eye(N, dtype=bool)


def longway(s, d, dim):
    """The torus_experiments long-way intermediate (None on the mesh)."""
    if T.TOPO == 'mesh':
        return None
    x, dx = (s % K, d % K) if dim == 0 else (s // K, d // K)
    r = (dx - x) % K
    if r == 0 or 2 * r == K:
        return None
    short = 1 if r < K - r else -1
    delta = min(r, K - r)
    m = K // 2 - delta + 1
    nx = (x - short * m) % K
    return nx + (s // K) * K if dim == 0 else (s % K) + nx * K


def parse(spec):
    o = dict(eps=4.0, wf=1.0, a=0.02, occ=0.0, src='all', hop='price', m=0.0, bias=0.0,
             choice='min', beta=10.0, eta=0.05, prop=1, minw=0)
    for tok in spec.split(':'):
        if tok:
            k, v = tok.split('=')
            o[k] = v if k in ('src', 'hop', 'choice') else float(v)
    return o


def sim_price(spec, rate, pattern, g=4, budget=2, cycles=4000, warmup=1000, seed=1):
    o = parse(spec)
    eps, a, wocc, srcm, hopm = o['eps'], o['a'], o['occ'], o['src'], o['hop']
    margin, bias, choice, beta, eta = o['m'], o['bias'], o['choice'], o['beta'], o['eta']
    prop = int(o['prop'])
    net = NET
    head, esc, vc1, out, dist, adj = net.head, net.esc, net.vc1, net.out, net.dist, net.adj
    rnd = random.Random(seed)
    occ = {}
    queues = [deque() for _ in range(N)]
    lat = []
    hopsum = 0
    ndet = 0
    ninj = 0
    thr = [g * 2 * net.deg[v] / 8 for v in range(N)]
    flow = np.zeros((N, 4))          # smoothed packets per cycle through each link
    oema = np.zeros((N, 4))          # smoothed occupied VCs per link
    moves = np.zeros((N, 4))
    price = np.ones((N, 4))
    C = _dist.astype(float)          # cheapest minimal route under the prices (DV table)
    Cl = C.tolist()
    Pl = price.tolist()
    split = {}                       # choice=fp: smoothed option frequencies per (s, d)
    for t in range(cycles):
        # ---- prices and one distance-vector relaxation per cycle
        if t % prop == 0:
            if wocc:
                ob = np.zeros((N, 4))
                for c in occ:
                    pp = (c >> 1) % 5
                    if pp < 4:
                        ob[c // 10, pp] += 1
                oema += a * (ob - oema)
            price = np.exp(eps * (o['wf'] * flow + wocc * oema))
            C = np.min(PRODINF + price[:, :, None] + C[NBR], axis=1)
            C[EYE] = 0.0
            Cl = C.tolist()
            Pl = price.tolist()
        for c in [c for c, p in occ.items() if head[c] == p[0]]:
            pk = occ.pop(c)
            if t >= warmup:
                lat.append(t - pk[1])
                hopsum += pk[2]
        moved = set()
        pks = list(occ)
        rnd.shuffle(pks)
        for c in pks:
            if c in moved:
                continue
            pk = occ[c]
            d = pk[0]
            u = head[c]
            if u == d:
                continue
            src = c // 2 % 5 == 4
            if pk[6] >= 0 and u == pk[6]:
                pk[6] = -1
            tgt = pk[6] if pk[6] >= 0 else d
            e = esc[c][d]
            onesc = c % 2 == 0 and not src
            canret = not (onesc and pk[4] >= budget)
            tiers = [vc1[u][tgt], [e]] if canret else [[e]]
            q = None
            for tier in tiers:
                free = [x for x in tier if x not in occ]
                if g and src:
                    free = [x for x in free if sum(1 for o2 in out[head[x]] if o2 not in occ) >= thr[head[x]]]
                if free:
                    if len(free) > 1 and hopm == 'price' and free[0] % 2 == 1:
                        Pu = Pl[u]
                        sc = [Pu[(x >> 1) % 5] + Cl[head[x]][tgt] for x in free]
                        mn = min(sc)
                        free = [x for x, y in zip(free, sc) if y <= mn * 1.0000001]
                    q = rnd.choice(free)
                    break
            if q is None:
                continue
            if q % 2 == 0 and not (c % 2 == 0):
                pk[6] = -1
            pk[2] += 1
            if onesc and q % 2 == 1:
                pk[4] += 1
            occ[q] = occ.pop(c)
            moved.add(q)
            pp = (q >> 1) % 5
            if pp < 4:
                moves[q // 10, pp] += 1
        flow += a * (moves - flow)
        moves[:] = 0
        for s in range(N):
            if rnd.random() < rate:
                d = T.tdest(pattern, s, rnd)
                if d != s:
                    queues[s].append((d, t))
            c = s * 10 + 8
            if queues[s] and c not in occ:
                d, born = queues[s].popleft()
                inter = -1
                if srcm != 'none' and dist[s][d] > 1:
                    base = Cl[s][d]
                    if srcm == 'all':
                        cost = C[s] + C[:, d]
                        if bias:
                            cost = cost + bias * (_dist[s] + _dist[:, d] - dist[s][d])
                        if not o['minw']:
                            cost = np.where(_dist[s] + _dist[:, d] > dist[s][d], cost, np.inf)
                        cost[s] = cost[d] = np.inf
                        if choice == 'softm':
                            ok = np.flatnonzero(cost < (1 - margin) * base)
                            if len(ok):
                                w8 = np.exp(-beta * (cost[ok] / base - 1.0))
                                inter = int(rnd.choices(ok.tolist(), weights=w8.tolist())[0])
                        elif choice == 'soft':
                            z = np.concatenate(([base], cost))
                            w8 = np.exp(-beta * (z / base - 1.0))
                            i = rnd.choices(range(N + 1), weights=w8.tolist())[0]
                            inter = i - 1
                        else:
                            w = int(np.argmin(cost))
                            if cost[w] < (1 - margin) * base:
                                inter = w
                    else:
                        cand = [longway(s, d, 0), longway(s, d, 1)]
                        if srcm == 'ringv':
                            cand.append(rnd.randrange(N))
                        opts = [(-1, base)]
                        for w in cand:
                            if w is not None and w not in (s, d):
                                cw = Cl[s][w] + Cl[w][d] + bias * (dist[s][w] + dist[w][d] - dist[s][d])
                                opts.append((w, cw))
                        if choice == 'fp':
                            key = (s, d)
                            fr = split.setdefault(key, {})
                            bw = min(opts, key=lambda x: x[1] if x[0] < 0 else x[1] / (1 - margin))[0]
                            ks = [x[0] for x in opts if x[0] >= 0 and x[0] != cand[-1]] if srcm == 'ringv' else [x[0] for x in opts]
                            for kk in list(fr):
                                fr[kk] *= (1 - eta)
                            fr[bw] = fr.get(bw, 0.0) + eta
                            tot = sum(fr.values())
                            r = rnd.random() * tot
                            for kk, vv in fr.items():
                                r -= vv
                                if r <= 0:
                                    inter = kk
                                    break
                        elif choice == 'soft':
                            ws = [math.exp(-beta * (x[1] / base - 1.0)) for x in opts]
                            inter = rnd.choices([x[0] for x in opts], weights=ws)[0]
                        else:
                            bo = min(opts[1:], key=lambda x: x[1], default=None)
                            if bo and bo[1] < (1 - margin) * base:
                                inter = bo[0]
                if inter in (s, d):
                    inter = -1
                if t >= warmup:
                    ninj += 1
                    ndet += inter >= 0
                occ[c] = [d, born, 0, dist[s][d], 0, 0, inter]
    return len(lat) / ((cycles - warmup) * N), hopsum / max(1, len(lat)), ndet / max(1, ninj)



# ------------------------------------------------------------------ 3. mesh (routing_sim mechanics)
def sim_mesh(spec, rate, pattern, k=8, cycles=6000, warmup=2000, seed=1, g=4):
    """`routing_sim.simulate(duatoMesh, 'T4:tiered')` with price-based choices.  spec:
    mode=tiered (exactly tieredMesh), mode=ptier (tieredMesh; where a tier offers two free
    hops, the cheapest price + C), mode=pdev (the preferred hop only when its cost is within
    (1 + tol) of the cheapest free VC1 minimal hop, otherwise that cheapest hop; then the
    escape; then any VC1 hop, cheapest)."""
    import routing_sim as R
    o = dict(eps=4.0, a=0.02, occ=0.0, mode='ptier', tol=0.1)
    for tok in spec.split(':'):
        if tok:
            kk, v = tok.split('=')
            o[kk] = v if kk == 'mode' else float(v)
    eps, a, wocc, mode, tol = o['eps'], o['a'], o['occ'], o['mode'], o['tol']
    ch, head, routes = R.mesh(k)
    route = routes['duatoMesh']
    n = k * k
    adjm = [[u + 1 if u % k < k - 1 else -1, u - 1 if u % k > 0 else -1,
             u + k if u // k < k - 1 else -1, u - k if u // k > 0 else -1] for u in range(n)]
    A = np.array(adjm)
    nbr = np.where(A >= 0, A, 0)
    dm = np.array([[abs(u % k - v % k) + abs(u // k - v // k) for v in range(n)] for u in range(n)])
    prodinf = np.full((n, 4, n), np.inf)
    for u in range(n):
        for p in range(4):
            if adjm[u][p] >= 0:
                prodinf[u, p][dm[adjm[u][p]] == dm[u] - 1] = 0.0
    eye = np.eye(n, dtype=bool)
    rnd = random.Random(seed)
    occ = {}
    queues = [deque() for _ in range(n)]
    lat = []
    flow = np.zeros((n, 4)); oema = np.zeros((n, 4)); moves = np.zeros((n, 4))
    C = dm.astype(float); Cl = C.tolist(); Pl = np.ones((n, 4)).tolist()

    def free_after(c2):
        v = head(c2)
        return sum(1 for dr in range(4) for vc in (0, 1) if ch(v, dr, vc) not in occ)

    def xy(u, d):
        return 0 if u % k < d % k else 1 if d % k < u % k else 2 if u // k < d // k else 3

    def yx(u, d):
        return 2 if u // k < d // k else 3 if d // k < u // k else xy(u, d)

    def cost(u, q, d):
        return Pl[u][q // 2 % 5] + Cl[head(q)][d]

    def cheapest(u, qs, d):
        sc = [cost(u, q, d) for q in qs]
        mn = min(sc)
        return [q for q, y in zip(qs, sc) if y <= mn * 1.0000001]

    for t in range(cycles):
        if mode != 'tiered':
            if wocc:
                ob = np.zeros((n, 4))
                for c in occ:
                    pp = c // 2 % 5
                    if pp < 4:
                        ob[c // 10, pp] += 1
                oema += a * (ob - oema)
            price = np.exp(eps * (flow + wocc * oema))
            C = np.min(prodinf + price[:, :, None] + C[nbr], axis=1)
            C[eye] = 0.0
            Cl = C.tolist(); Pl = price.tolist()
        for c in [c for c, (d, _) in occ.items() if head(c) == d]:
            _, born = occ.pop(c)
            if t >= warmup:
                lat.append(t - born)
        moved = set()
        packets = list(occ)
        rnd.shuffle(packets)
        for c in packets:
            if c in moved or c not in occ:
                continue
            d, _ = occ[c]
            u = head(c)
            if u == d:
                continue
            hops = route(c, d)
            free = [c2 for c2 in hops if c2 not in occ]
            src = c // 2 % 5 == 4
            if src:
                free = [c2 for c2 in free if free_after(c2) >= g]
            esc = ch(u, xy(u, d), 0)
            pref = esc if c % 2 == 0 and not src else ch(u, yx(u, d), 1)
            pick = []
            if mode in ('tiered', 'ptier'):
                for tier in (lambda q: q == pref or (src and q == esc), lambda q: q == esc,
                             lambda q: q % 2 == 1):
                    if any(tier(q) for q in free):
                        pick = [q for q in free if tier(q)]
                        break
                if mode == 'ptier' and len(pick) > 1:
                    pick = cheapest(u, pick, d)
            else:   # pdev
                v1 = [q for q in free if q % 2 == 1 or (src and q == esc)]
                if pref in free or (src and esc in free):
                    cands = [q for q in (pref, esc if src else -1) if q in free]
                    best = cheapest(u, v1, d) if v1 else []
                    pc = min(cost(u, q, d) for q in cands)
                    if pc <= (1 + tol) * cost(u, best[0], d):
                        pick = cheapest(u, cands, d)
                    else:
                        pick = best
                elif v1 and min(cost(u, q, d) for q in v1) < (cost(u, esc, d) if esc in free else 1e18) / (1 + tol):
                    pick = cheapest(u, v1, d)
                elif esc in free:
                    pick = [esc]
                elif v1:
                    pick = cheapest(u, v1, d)
            if pick:
                c2 = rnd.choice(pick)
                occ[c2] = occ.pop(c)
                moved.add(c2)
                pp = c2 // 2 % 5
                if pp < 4:
                    moves[c2 // 10, pp] += 1
        flow += a * (moves - flow)
        moves[:] = 0
        for s in range(n):
            if rnd.random() < rate:
                d = R.destination(pattern, s, k, rnd)
                if d != s:
                    queues[s].append((d, t))
            if queues[s] and ch(s, 4, 0) not in occ:
                occ[ch(s, 4, 0)] = queues[s].popleft()
    return len(lat) / ((cycles - warmup) * n), sum(lat) / max(1, len(lat)), 0.0


def main_sim(argv):
    import time
    specs = argv[0].split(',')
    pats = argv[1].split(',')
    rates = [float(x) for x in argv[2].split(',')]
    seeds = [int(x) for x in argv[3].split(',')]
    for spec in specs:
        for p in pats:
            t0 = time.time()
            f = sim_mesh if spec.startswith('mesh') else sim_price
            sp = spec[4:] if spec.startswith('mesh') else spec
            res = {r: [f(sp, r, p, seed=sd) for sd in seeds] for r in rates}
            means = {r: sum(x[0] for x in v) / len(v) for r, v in res.items()}
            rb = max(rates, key=means.get)
            v = [x[0] for x in res[rb]]
            m = means[rb]
            se = (sum((x - m) ** 2 for x in v) / (len(v) - 1)) ** .5 / len(v) ** .5 if len(v) > 1 else 0
            det = sum(x[2] for x in res[rb]) / len(v)
            hops = sum(x[1] for x in res[rb]) / len(v)
            curve = ' '.join(f'{r}:{means[r]:.4f}' for r in rates)
            print(f'{spec:<40} {p:<10} {m:.4f} ±{se:.4f} @{rb} det {det:.3f} hops {hops:.2f} '
                  f'[{curve}] {time.time() - t0:.0f}s', flush=True)


if __name__ == '__main__' and sys.argv[1:2] == ['sim']:
    main_sim(sys.argv[2:])
