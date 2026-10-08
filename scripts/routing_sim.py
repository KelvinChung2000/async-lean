#!/usr/bin/env python3
"""Cycle-level simulation of the mesh routing functions of `Examples/Routing.lean` and
`Examples/OptimalRouting.lean` (not part of the Lean development; nothing here is proved).

The model is the one of `AsyncLean.Routing.Basic`: one-packet channel buffers, channel
`ch(u, dir, vc) = (u * 5 + dir) * 2 + vc`, an injection channel per node (dir 4), and a
selection function that moves each packet to one of its free permitted channels.  Every cycle:
arrived packets are ejected, every other packet tries one hop (in random order), and each node
generates a packet with probability `rate` into an unbounded source queue that feeds its
injection channel.

Usage: python3 scripts/routing_sim.py [--k 8]
           [--policy random|vc1first|vc1xy|congestion|gated<g>]
           [--schemes xyMesh,westFirst1,northLast1,duatoMesh,westFirstMesh,northLastMesh]
           [--patterns uniform,transpose,bitcomp] [--rates 0.1,0.2,0.3,0.4,0.5]

Each cell is "accepted throughput (packets / node / cycle) / average latency (cycles)".
"""
import argparse
import random
from collections import deque


def mesh(k):
    def ch(u, dr, vc):
        return (u * 5 + dr) * 2 + vc

    def head(c):
        u, dr = c // 10, c // 2 % 5
        return [u + 1, u - 1, u + k, u - k, u][dr]

    def productive(u, d):
        r = []
        if u % k < d % k: r.append(0)
        if d % k < u % k: r.append(1)
        if u // k < d // k: r.append(2)
        if d // k < u // k: r.append(3)
        return r

    def xy(u, d):
        return productive(u, d)[0]

    def west_first(u, d):
        p = productive(u, d)
        return [1] if 1 in p else p

    def north_last(u, d):
        p = productive(u, d)
        q = [x for x in p if x != 2]
        return q if q else p

    def duato(c, d):
        u = head(c)
        return [ch(u, xy(u, d), 0)] + [ch(u, x, 1) for x in productive(u, d)]

    def turn_duato(turn):
        def route(c, d):
            u = head(c)
            vc0 = [ch(u, xy(u, d), 0)] + [ch(u, x, 0) for x in turn(u, d) if x != xy(u, d)]
            return vc0 + [ch(u, x, 1) for x in productive(u, d)]
        return route

    def one_vc(turn):
        def route(c, d):
            u = head(c)
            return [ch(u, x, 0) for x in turn(u, d)]
        return route

    routes = {
        'xyMesh': one_vc(lambda u, d: [xy(u, d)]),
        'westFirst1': one_vc(west_first),
        'northLast1': one_vc(north_last),
        'duatoMesh': duato,
        'westFirstMesh': turn_duato(west_first),
        'northLastMesh': turn_duato(north_last),
    }
    return ch, head, routes


def simulate(k, route, rate, pattern, policy, cycles=6000, warmup=2000, seed=1):
    ch, head, _ = mesh(k)
    rnd = random.Random(seed)
    n = k * k
    occ = {}                      # channel -> (destination, generation time)
    queues = [deque() for _ in range(n)]
    latencies = []

    def destination(s):
        x, y = s % k, s // k
        if pattern == 'uniform':
            d = rnd.randrange(n - 1)
            return d if d < s else d + 1
        if pattern == 'transpose':
            return x * k + y
        if pattern == 'bitcomp':
            return (k - 1 - x) + (k - 1 - y) * k
        raise ValueError(pattern)

    def free_after(c2):
        v = head(c2)
        return sum(1 for dr in range(4) for vc in (0, 1) if ch(v, dr, vc) not in occ)

    for t in range(cycles):
        for c in [c for c, (d, _) in occ.items() if head(c) == d]:
            _, born = occ.pop(c)
            if t >= warmup:
                latencies.append(t - born)
        moved = set()
        packets = list(occ)
        rnd.shuffle(packets)
        for c in packets:
            if c in moved or c not in occ:
                continue
            d, _ = occ[c]
            if head(c) == d:
                continue
            hops = route(c, d)
            free = [c2 for c2 in hops if c2 not in occ]
            if policy in ('vc1first', 'vc1xy'):
                vc1 = [c2 for c2 in free if c2 % 2 == 1]
                if vc1:
                    free = vc1
                elif policy == 'vc1xy' and hops[0] in free:
                    free = [hops[0]]
            elif policy.startswith('gated'):
                # Duato's preference (virtual channel 1, then the escape hop); the extra
                # virtual-channel-0 hops only towards a router with at least `g` of its 8
                # outgoing channels free
                g = int(policy[5:] or 6)
                vc1 = [c2 for c2 in free if c2 % 2 == 1]
                if vc1:
                    free = vc1
                elif hops[0] in free:
                    free = [hops[0]]
                else:
                    free = [c2 for c2 in free if free_after(c2) >= g]
            elif policy == 'congestion' and free:
                best = max(free_after(c2) for c2 in free)
                free = [c2 for c2 in free if free_after(c2) == best]
            if free:
                c2 = rnd.choice(free)
                occ[c2] = occ.pop(c)
                moved.add(c2)
        for s in range(n):
            if rnd.random() < rate:
                d = destination(s)
                if d != s:
                    queues[s].append((d, t))
            if queues[s] and ch(s, 4, 0) not in occ:
                occ[ch(s, 4, 0)] = queues[s].popleft()
    throughput = len(latencies) / ((cycles - warmup) * n)
    latency = sum(latencies) / len(latencies) if latencies else float('nan')
    return throughput, latency


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--k', type=int, default=8)
    ap.add_argument('--policy', default='random')
    ap.add_argument('--patterns', default='uniform,transpose,bitcomp')
    ap.add_argument('--rates', default='0.1,0.2,0.3,0.4,0.5')
    ap.add_argument('--schemes', default='duatoMesh,westFirstMesh,northLastMesh')
    args = ap.parse_args()
    rates = [float(r) for r in args.rates.split(',')]
    _, _, routes = mesh(args.k)
    for pattern in args.patterns.split(','):
        print(f'== {pattern}, {args.k} x {args.k} mesh, selection: {args.policy}')
        print(f'{"routing":<16}' + ''.join(f'{"rate " + str(r):>15}' for r in rates))
        for name in args.schemes.split(','):
            route = routes[name]
            cells = []
            for r in rates:
                thr, lat = simulate(args.k, route, r, pattern, args.policy)
                cells.append(f'{thr:.3f}/{lat:.1f}')
            print(f'{name:<16}' + ''.join(f'{c:>15}' for c in cells))


if __name__ == '__main__':
    main()
