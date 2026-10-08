#!/usr/bin/env python3
"""Cycle-level simulator for arbitrary undirected graphs (nothing here is proved; the networks
are those of `AsyncLean/Routing/Graph.lean` and `GraphBudget.lean`, whose safety is) (radix <= 4 + local port), with the
mechanics of scripts/routing_sim.py kept identical:

  * channel ch(u, port, vc) = (u * 5 + port) * 2 + vc; port 4 = injection channel (vc 0 only);
    every directed link has 2 VCs, each a one-packet buffer; adj[u][port] = neighbour or -1;
  * every cycle: packets whose channel head is their destination are ejected; every other
    packet tries one hop in random order (at most one move per packet per cycle, into a
    currently free channel); then each node generates a packet with probability `rate` into an
    unbounded source queue and moves the queue head into its injection channel if free.

Routing (2 VCs):
  VC1  minimal adaptive: any neighbour on a shortest path to the destination;
  VC0  escape: 'xy' (mesh only, dimension order) or 'updown' (up*/down* over a BFS spanning
       tree from `root`; link u->v is "up" if (level[v], v) < (level[u], u)).  The phase is
       encoded in the channel: a VC0 channel entered by a down hop allows only down hops; a VC0
       channel entered by an up hop, a VC1 channel or an injection channel starts a fresh
       up*/down* path.  The escape hop is the first hop of a SHORTEST legal path (lowest port
       on ties).
  absorbing=True: a packet on VC0 may only take escape hops (stays on VC0).
  absorbing=False: Duato-style, VC0 -> VC1 allowed.
  budget=B: a packet may return from VC0 to VC1 at most B times (`GraphData.budgetNet B`);
  budget=None: unbounded (not livelock free in general).

Deadlock freedom (one-packet buffers = virtual cut-through): in a deadlock every non-ejected
packet has an escape option; it is occupied by a packet on VC0, whose escape option is a legal
up*/down* continuation of ITS channel; the up*/down* channel order (up channels ascending, up ->
down, down channels descending) is acyclic, so the chain cannot close.

Selection policies: 'random' (random among free permitted hops), 'tiered' (free VC1 minimal
hops first, random among them; otherwise the escape hop).  Source throttling g: a packet leaves
its injection channel only towards a router v with at least g * 2deg(v) / 8 of its 2deg(v)
outgoing channels free ('scaled'); 'phantom' mode reproduces routing_sim exactly (counts the 8
channels of a mesh router, the missing boundary ones as free).
"""
import random
from collections import deque

import sys
from routing_sim import destination, PATTERNS  # reused as-is


# ---------------------------------------------------------------- topologies
def mesh_adj(k):
    adj = []
    for u in range(k * k):
        x, y = u % k, u // k
        adj.append([u + 1 if x < k - 1 else -1, u - 1 if x > 0 else -1,
                    u + k if y < k - 1 else -1, u - k if y > 0 else -1])
    return adj


def torus_adj(k):
    adj = []
    for u in range(k * k):
        x, y = u % k, u // k
        adj.append([y * k + (x + 1) % k, y * k + (x - 1) % k,
                    ((y + 1) % k) * k + x, ((y - 1) % k) * k + x])
    return adj


def circulant_adj(n, s):
    return [[(u + 1) % n, (u - 1) % n, (u + s) % n, (u - s) % n] for u in range(n)]


def random_regular_adj(n, d, seed):
    rnd = random.Random(seed)
    while True:
        stubs = [u for u in range(n) for _ in range(d)]
        rnd.shuffle(stubs)
        edges = set()
        ok = True
        for i in range(0, len(stubs), 2):
            a, b = stubs[i], stubs[i + 1]
            e = (min(a, b), max(a, b))
            if a == b or e in edges:
                ok = False
                break
            edges.add(e)
        if not ok:
            continue
        nb = [[] for _ in range(n)]
        for a, b in sorted(edges):
            nb[a].append(b)
            nb[b].append(a)
        adj = [l + [-1] * (4 - len(l)) for l in nb]
        if all(x < 1e9 for x in bfs(adj, 0)):
            return adj


def bfs(adj, src):
    n = len(adj)
    dist = [float('inf')] * n
    dist[src] = 0
    q = deque([src])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v >= 0 and dist[v] == float('inf'):
                dist[v] = dist[u] + 1
                q.append(v)
    return dist


def avg_dist(adj):
    n = len(adj)
    return sum(sum(bfs(adj, s)) for s in range(n)) / (n * (n - 1))


def best_circulant(n):
    best = min(range(2, n // 2), key=lambda s: (avg_dist(circulant_adj(n, s)), s))
    return best, circulant_adj(n, best)


# ---------------------------------------------------------------- routing tables
INF = 10 ** 9


class Net:
    def __init__(self, adj, escape='updown', root=0, k=None):
        self.adj = adj
        n = self.n = len(adj)
        ch = lambda u, p, vc: (u * 5 + p) * 2 + vc
        nch = n * 10
        self.head = head = [-1] * nch
        self.tail = [-1] * nch
        for u in range(n):
            for p in range(4):
                v = adj[u][p]
                if v >= 0:
                    for vc in (0, 1):
                        head[ch(u, p, vc)] = v
                        self.tail[ch(u, p, vc)] = u
            head[ch(u, 4, 0)] = u
        self.deg = [sum(1 for v in a if v >= 0) for a in adj]
        self.out = [[ch(u, p, vc) for p in range(4) if adj[u][p] >= 0 for vc in (0, 1)]
                    for u in range(n)]
        self.dist = dist = [bfs(adj, s) for s in range(n)]
        # VC1 minimal hops from node u towards d (port order)
        self.vc1 = [[[ch(u, p, 1) for p in range(4) if adj[u][p] >= 0
                      and dist[adj[u][p]][d] == dist[u][d] - 1] for d in range(n)]
                    for u in range(n)]
        # escape channel per (channel, destination)
        self.esc = [None] * nch
        if escape == 'xy':
            def xyp(u, d):
                return 0 if u % k < d % k else 1 if d % k < u % k else 2 if u // k < d // k else 3
            tab = [[ch(u, xyp(u, d), 0) if u != d else -1 for d in range(n)] for u in range(n)]
            for c in range(nch):
                if head[c] >= 0:
                    self.esc[c] = tab[head[c]]
            self.isdown = [False] * nch
        else:
            lev = bfs(adj, root)
            self.level = lev
            key = lambda u: (lev[u], u)
            up = lambda u, v: key(v) < key(u)
            # D[ph][v][d]: shortest legal up*/down* distance from state (v, ph); ph=1: down only
            D = [[[INF] * n for _ in range(n)] for _ in range(2)]
            for d in range(n):
                # reverse BFS on states (v, ph)
                D[0][d][d] = D[1][d][d] = 0
                q = deque([(d, 0), (d, 1)])
                while q:
                    w, ph2 = q.popleft()
                    dd = D[ph2][w][d]
                    for u in adj[w]:
                        if u < 0:
                            continue
                        # hop u -> w producing phase ph2 at w
                        if up(u, w):
                            if ph2 == 0 and D[0][u][d] == INF:   # up hop: only from phase 0
                                D[0][u][d] = dd + 1
                                q.append((u, 0))
                        else:
                            if ph2 == 1:                          # down hop: from either phase
                                for ph in (0, 1):
                                    if D[ph][u][d] == INF:
                                        D[ph][u][d] = dd + 1
                                        q.append((u, ph))
            self.D = D

            def esc_hop(u, ph, d):
                best, bc = INF, -1
                for p in range(4):
                    w = adj[u][p]
                    if w < 0:
                        continue
                    if up(u, w):
                        if ph == 1:
                            continue
                        val = D[0][w][d]
                    else:
                        val = D[1][w][d]
                    if val + 1 < best:
                        best, bc = val + 1, ch(u, p, 0)
                assert best == D[ph][u][d], (u, ph, d, best)
                return bc
            tabs = [[[esc_hop(u, ph, d) if u != d else -1 for d in range(n)] for u in range(n)]
                    for ph in (0, 1)]
            self.isdown = [False] * nch
            for c in range(nch):
                if head[c] < 0:
                    continue
                ph = 0
                if c % 2 == 0 and c // 2 % 5 != 4 and not up(self.tail[c], head[c]):
                    ph = 1
                    self.isdown[c] = True
                self.esc[c] = tabs[ph][head[c]]
            self.esc_stretch = sum(D[0][s][d] for s in range(n) for d in range(n)) / \
                sum(dist[s][d] for s in range(n) for d in range(n))


# ---------------------------------------------------------------- simulation
def simulate(net, rate, pattern, policy='tiered', g=0, absorbing=False, throttle_mode='scaled',
             cycles=6000, warmup=2000, seed=1, k=8, budget=None):
    # budget: a packet may return from VC0 to VC1 at most `budget` times (None: unbounded;
    # absorbing=True is budget 0)
    if absorbing: budget = 0
    head, esc, vc1, out = net.head, net.esc, net.vc1, net.out
    n = net.n
    rnd = random.Random(seed)
    occ = {}                      # channel -> [destination, generation time, hops]
    queues = [deque() for _ in range(n)]
    latencies = []
    hopsum = distsum = maxhops = 0
    dist = net.dist
    if throttle_mode == 'phantom':
        thr = [g + 2 * net.deg[v] - 8 for v in range(n)]   # free_real >= g - phantom
    else:
        thr = [g * 2 * net.deg[v] / 8 for v in range(n)]
    tiered = policy == 'tiered'
    for t in range(cycles):
        for c in [c for c, p in occ.items() if head[c] == p[0]]:
            pk = occ.pop(c)
            if t >= warmup:
                latencies.append(t - pk[1])
                hopsum += pk[2]
                distsum += pk[3]
                if pk[2] > maxhops:
                    maxhops = pk[2]
        moved = set()
        packets = list(occ)
        rnd.shuffle(packets)
        for c in packets:
            if c in moved:
                continue
            pk = occ[c]
            d = pk[0]
            u = head[c]
            if u == d:
                continue
            e = esc[c][d]
            src = c // 2 % 5 == 4
            if budget is not None and c % 2 == 0 and not src and pk[4] >= budget:
                hops = [e]
            else:
                hops = [e] + vc1[u][d]
            free = [q for q in hops if q not in occ]
            if g and src and free:
                free = [q for q in free
                        if sum(1 for o in out[head[q]] if o not in occ) >= thr[head[q]]]
            if tiered and free:
                f1 = [q for q in free if q % 2 == 1]
                free = f1 if f1 else free
            if free:
                q = rnd.choice(free)
                pk[2] += 1
                if c % 2 == 0 and not src and q % 2 == 1:
                    pk[4] += 1
                occ[q] = occ.pop(c)
                moved.add(q)
        for s in range(n):
            if rnd.random() < rate:
                d = RANDPERM[s] if pattern == 'randperm' else destination(pattern, s, k, rnd)
                if d != s:
                    queues[s].append((d, t))
            c = s * 10 + 8
            if queues[s] and c not in occ:
                d, born = queues[s].popleft()
                occ[c] = [d, born, 0, dist[s][d], 0]
    m = len(latencies)
    return dict(thr=m / ((cycles - warmup) * n),
                lat=sum(latencies) / m if m else float('nan'),
                stretch=hopsum / distsum if distsum else float('nan'),
                maxhops=maxhops)


RANDPERM = list(range(64))
random.Random(0).shuffle(RANDPERM)
ALL_PATTERNS = PATTERNS + ['randperm']


# ---------------------------------------------------------------- wire-budget designs (8 x 8)
# Rows and columns built from 1-D link patterns on positions 0..7 (node (x, y) = y * 8 + x).
_P = [(i, i + 1) for i in range(7)]                                    # path, wire 7
_C = [(0, 1), (1, 2), (2, 3), (2, 4), (3, 5), (4, 5), (5, 6), (6, 7)]   # braided middle, wire 10
_D = _P + [(2, 4), (3, 5)]                                             # path + 2 express links
_F = [(0, 1), (0, 2), (2, 4), (4, 6), (6, 7), (1, 3), (3, 5), (5, 7)]  # folded ring
_TL = [(i, i + 1) for i in range(1, 7)]                                # path without its left end
_TR = [(i, i + 1) for i in range(0, 6)]                                # path without its right end
DESIGNS = {
    # same radix and total wire (112) as the mesh, wire moved from the outer to the middle cuts
    'CA_112': [_C, _TL, _TR, _TL, _TR, _TL, _TR, _C],
    # the mesh plus 8 length-2 express links on the boundary rows and columns (wire 128)
    'D_128': [_D, _P, _P, _P, _P, _P, _P, _D],
    # D_128 with rows and columns 1 and 6 folded rings (wire 156)
    'DF_156': [_D, _F, _P, _P, _P, _P, _F, _D],
}


def design_adj(name, k=8):
    """Adjacency (4 ports, -1 = none) of a design: the same pattern list for rows and columns."""
    pats = DESIGNS[name]
    edges = set()
    for r, pat in enumerate(pats):
        for a, b in pat:
            edges.add((r * k + a, r * k + b))
            edges.add((a * k + r, b * k + r))
    adj = [[] for _ in range(k * k)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    assert max(len(a) for a in adj) <= 4
    return [a + [-1] * (4 - len(a)) for a in adj]


def main():
    import argparse
    ap = argparse.ArgumentParser(description='peak throughput of topologies, tiered selection, g = 4')
    ap.add_argument('--topologies', default='mesh_xy,mesh,D_128,CA_112,DF_156')
    ap.add_argument('--budget', default='2', help="returns from VC0 to VC1: a number, 'none' or 'absorb'")
    ap.add_argument('--rates', default='0.2,0.3,0.4,0.5,0.6,0.8')
    ap.add_argument('--seeds', type=int, default=2)
    args = ap.parse_args()
    budget = None if args.budget == 'none' else 0 if args.budget == 'absorb' else int(args.budget)
    rates = [float(r) for r in args.rates.split(',')]
    print(f'{"topology":<10}' + ''.join(f'{p:>10}' for p in ALL_PATTERNS))
    for t in args.topologies.split(','):
        net = (Net(mesh_adj(8), escape='xy', k=8) if t == 'mesh_xy' else
               Net(mesh_adj(8), root=27) if t == 'mesh' else Net(design_adj(t), root=27))
        cells = []
        for p in ALL_PATTERNS:
            cells.append(max(sum(simulate(net, r, p, 'tiered', g=4, budget=budget, seed=s)['thr']
                                 for s in range(args.seeds)) / args.seeds for r in rates))
        print(f'{t:<10}' + ''.join(f'{c:>10.3f}' for c in cells), flush=True)


if __name__ == '__main__':
    main()
