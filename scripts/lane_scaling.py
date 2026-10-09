#!/usr/bin/env python3
"""Throughput against the number of connections per link (nothing here is proved; the three
networks are `Network.lanes` (AsyncLean/Routing/Lanes.lean), `GraphData.sharedNet`
(SharedLanes.lean) and `Network.widen` with `GraphData.sharedSlots` (Widen.lean), whose safety
is).

Every directed link has m connections, each with 2 one-packet virtual channels, and every node
has m injection channels; the offered load is m * rate packets per node per cycle (m sources of
rate `rate`).  The mechanics are those of scripts/routing_graph_sim.py (routing tables `Net`,
ejection, one hop per packet per cycle in random order, tiered selection, bounded returns,
throttled injection), with three ways to use the m connections:

  lanes   `Network.lanes`: lane L is a full copy of the network on virtual channels 2L (escape,
          spanning tree or XY) and 2L + 1 (minimal adaptive); a packet picks a lane at its
          source (the first free injection channel, lanes in random order) and stays on it.
          With --trees, lane L uses a spanning tree rooted at a different node.
  shared  the widening, one wide network: virtual channel 0 is the escape, virtual channels
          1 .. 2m - 1 are all minimal adaptive; a packet may take any of them.
  hybrid  shared lanes: the escapes of the lanes (virtual channel 2L for a packet of lane L, its
          own spanning tree with --trees), the adaptive channels of every lane for every packet.

The script prints the peak accepted throughput per node and per connection
(packets / cycle / node / m): linear scaling keeps it constant as m grows.
"""
import argparse
import random
from collections import deque

from routing_graph_sim import Net, mesh_adj, torus_adj, ALL_PATTERNS, RANDPERM
from routing_sim import destination


def simulate(nets, m, mode, rate, pattern, g=4, budget=2, cycles=6000, warmup=2000, seed=1, k=8):
    base = nets[0]
    n, adj = base.n, base.adj
    V = 2 * m                                        # virtual channels per directed link
    ch = lambda u, p, vc: (u * 5 + p) * V + vc
    head = lambda c: adj[c // V // 5][c // V % 5] if c // V % 5 < 4 else c // V // 5
    rnd = random.Random(seed)
    occ = {}            # channel -> [dest, born, hops, dist, returns, lane]
    queues = [deque() for _ in range(n)]
    out = [[ch(u, p, vc) for p in range(4) if adj[u][p] >= 0 for vc in range(V)] for u in range(n)]
    thr_free = [g * len(out[v]) / 8 for v in range(n)]
    dist = base.dist
    delivered = 0

    def esc_of(c, d, lane):
        """The escape hop of a packet in channel c for d, on the escape VC of its lane."""
        u, p = c // V // 5, c // V % 5
        net = nets[lane % len(nets)] if mode != 'shared' else base
        # a packet on an adaptive VC (or injected) starts a fresh up*/down* path: phase 0,
        # the base table's VC1 entry; on an escape VC the phase is that of the link
        eb = net.esc[(u * 5 + p) * 2 + (0 if p == 4 or is_esc(c) else 1)][d] // 2
        return ch(eb // 5, eb % 5, 2 * lane if mode != 'shared' else 0)

    def is_esc(c):
        vc = c % V
        return (vc % 2 == 0) if mode != 'shared' else vc == 0

    for t in range(cycles):
        for c in [c for c, pk in occ.items() if head(c) == pk[0]]:
            occ.pop(c)
            if t >= warmup:
                delivered += 1
        moved = set()
        packets = list(occ)
        rnd.shuffle(packets)
        for c in packets:
            if c in moved:
                continue
            pk = occ[c]
            d, lane = pk[0], pk[5]
            u = head(c)
            src = c // V % 5 == 4
            e = esc_of(c, d, lane)
            if is_esc(c) and not src and pk[4] >= budget:
                hops = [e]
            else:
                ports = [q // 2 % 5 for q in base.vc1[u][d]]
                if mode == 'lanes':
                    ad = [ch(u, p, 2 * lane + 1) for p in ports]
                elif mode == 'hybrid':
                    ad = [ch(u, p, vc) for p in ports for vc in range(1, V, 2)]
                else:
                    ad = [ch(u, p, vc) for p in ports for vc in range(1, V)]
                hops = [e] + ad
            free = [q for q in hops if q not in occ]
            if g and src and free:
                free = [q for q in free
                        if sum(1 for o in out[head(q)] if o not in occ) >= thr_free[head(q)]]
            if free:
                f1 = [q for q in free if not is_esc(q)]
                q = rnd.choice(f1 if f1 else free)
                pk[2] += 1
                if is_esc(c) and not src and not is_esc(q):
                    pk[4] += 1
                occ[q] = occ.pop(c)
                moved.add(q)
        for s in range(n):
            for _ in range(m):
                if rnd.random() < rate:
                    d = RANDPERM[s] if pattern == 'randperm' else destination(pattern, s, k, rnd)
                    if d != s:
                        queues[s].append((d, t))
            for lane in rnd.sample(range(m), m):
                c = ch(s, 4, lane)
                if queues[s] and c not in occ:
                    d, born = queues[s].popleft()
                    occ[c] = [d, born, 0, dist[s][d], 0, lane if mode != 'shared' else 0]
    return delivered / ((cycles - warmup) * n)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--topology', default='torus', choices=['torus', 'mesh', 'mesh_xy'])
    ap.add_argument('--ms', default='1,2,4')
    ap.add_argument('--modes', default='lanes,hybrid,shared')
    ap.add_argument('--patterns', default=','.join(ALL_PATTERNS))
    ap.add_argument('--rates', default='0.3,0.4,0.5,0.6,0.7,0.8,1.0')
    ap.add_argument('--seeds', type=int, default=2)
    ap.add_argument('--trees', action='store_true', help='a different spanning-tree root per lane')
    ap.add_argument('--cycles', type=int, default=6000)
    args = ap.parse_args()
    k = 8
    if args.topology == 'mesh_xy':
        mk = lambda root: Net(mesh_adj(k), escape='xy', k=k)
    else:
        adj = torus_adj(k) if args.topology == 'torus' else mesh_adj(k)
        mk = lambda root: Net(adj, root=root)
    roots = [27, 36, 0, 63, 7, 56, 18, 45]
    rates = [float(r) for r in args.rates.split(',')]
    pats = args.patterns.split(',')
    print(f'{args.topology}, peak accepted throughput per node / m (mean of {args.seeds} seeds)')
    print(f'{"mode":<8}{"m":>3}' + ''.join(f'{p:>10}' for p in pats))
    for mode in args.modes.split(','):
        for m in [int(x) for x in args.ms.split(',')]:
            nets = [mk(roots[i]) for i in range(m)] if (args.trees and mode != 'shared') \
                else [mk(roots[0])]
            cells = []
            for p in pats:
                best = max(sum(simulate(nets, m, mode, r, p, seed=s, cycles=args.cycles,
                                        warmup=args.cycles // 3, k=k)
                               for s in range(args.seeds)) / args.seeds for r in rates)
                cells.append(best / m)
            print(f'{mode:<8}{m:>3}' + ''.join(f'{c:>10.3f}' for c in cells), flush=True)


if __name__ == '__main__':
    main()
