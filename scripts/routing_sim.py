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
           [--policy random|vc1first|vc1xy|congestion|gated<g>|tiered|o1turn|T<g>:<policy>]
           [--schemes xyMesh,westFirst1,northLast1,duatoMesh,dualXY,westFirstMesh,northLastMesh]
           [--patterns uniform,transpose,bitcomp,shuffle,bitrev,hotspot] [--rates 0.1,...,0.5]
       python3 scripts/routing_sim.py --bench [--k 8] [--rates 0.7] [--seeds 3]

Each cell is "accepted throughput (packets / node / cycle) / average latency (cycles)".

`T<g>:<policy>` throttles the sources: a packet leaves its injection channel only towards a
router with at least `g` of its 8 outgoing channels free.  `tiered` is the selection
`tieredMesh` of `AsyncLean.Examples.MeshTiered` (with `T4:tiered`, the proved scheme with
threshold 4).  `--bench` compares it with the existing schemes, averaged over seeds.
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
        'dualXY': lambda c, d: [ch(head(c), xy(head(c), d), vc) for vc in (0, 1)],
        'westFirstMesh': turn_duato(west_first),
        'northLastMesh': turn_duato(north_last),
    }
    return ch, head, routes


PATTERNS = ['uniform', 'transpose', 'shuffle', 'bitrev', 'hotspot', 'bitcomp']


def destination(pattern, s, k, rnd):
    n, x, y = k * k, s % k, s // k
    if pattern == 'uniform':
        d = rnd.randrange(n - 1)
        return d if d < s else d + 1
    if pattern == 'transpose':
        return x * k + y
    if pattern == 'bitcomp':
        return (k - 1 - x) + (k - 1 - y) * k
    b = (n - 1).bit_length()          # shuffle and bit reversal: k a power of 2
    if pattern == 'bitrev':
        return int(format(s, f'0{b}b')[::-1], 2)
    if pattern == 'shuffle':
        return ((s << 1) | (s >> (b - 1))) & (n - 1)
    if pattern == 'hotspot':          # a fifth of the packets go to the centre
        h = (k // 2) * k + k // 2
        return h if s != h and rnd.random() < 0.2 else destination('uniform', s, k, rnd)
    raise ValueError(pattern)


def simulate(k, route, rate, pattern, policy, cycles=6000, warmup=2000, seed=1):
    ch, head, _ = mesh(k)
    rnd = random.Random(seed)
    n = k * k
    occ = {}                      # channel -> (destination, generation time)
    queues = [deque() for _ in range(n)]
    latencies = []
    throttle = None
    if policy.startswith('T'):
        g, policy = policy[1:].split(':')
        throttle = int(g)

    def free_after(c2):
        v = head(c2)
        return sum(1 for dr in range(4) for vc in (0, 1) if ch(v, dr, vc) not in occ)

    def xy(u, d):
        return 0 if u % k < d % k else 1 if d % k < u % k else 2 if u // k < d // k else 3

    def yx(u, d):
        return 2 if u // k < d // k else 3 if d // k < u // k else xy(u, d)

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
            if throttle is not None and c // 2 % 5 == 4:
                free = [c2 for c2 in free if free_after(c2) >= throttle]
            if policy == 'tiered':
                # `tieredMesh`: the free hops of the first tier that has one -- the preferred
                # hop (XY on virtual channel 0, YX on virtual channel 1, either from a source),
                # the escape hop, then any hop on virtual channel 1
                u = head(c)
                esc = ch(u, xy(u, d), 0)
                src = c // 2 % 5 == 4
                pref = esc if c % 2 == 0 and not src else ch(u, yx(u, d), 1)
                for tier in (lambda q: q == pref or (src and q == esc), lambda q: q == esc,
                             lambda q: q % 2 == 1):
                    if any(tier(q) for q in free):
                        free = [q for q in free if tier(q)]
                        break
                else:
                    free = []
            elif policy == 'o1turn':
                # one dimension order per packet: XY on virtual channel 0 or YX on virtual
                # channel 1, drawn at the source
                u = head(c)
                if c // 2 % 5 == 4:
                    want = rnd.choice([ch(u, xy(u, d), 0), ch(u, yx(u, d), 1)])
                else:
                    want = ch(u, xy(u, d), 0) if c % 2 == 0 else ch(u, yx(u, d), 1)
                free = [want] if want in free else []
            elif policy in ('vc1first', 'vc1xy'):
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
                d = destination(pattern, s, k, rnd)
                if d != s:
                    queues[s].append((d, t))
            if queues[s] and ch(s, 4, 0) not in occ:
                occ[ch(s, 4, 0)] = queues[s].popleft()
    throughput = len(latencies) / ((cycles - warmup) * n)
    latency = sum(latencies) / len(latencies) if latencies else float('nan')
    return throughput, latency


BENCH = [('duatoMesh', 'random'), ('duatoMesh', 'T4:random'), ('dualXY', 'random'),
         ('duatoMesh', 'o1turn'), ('westFirstMesh', 'random'), ('duatoMesh', 'T4:tiered')]


def _run(job):
    k, name, policy, rate, pattern, seed = job
    return simulate(k, mesh(k)[2][name], rate, pattern, policy, seed=seed)


def bench(k, rates, seeds):
    from multiprocessing import Pool
    jobs = [(k, name, pol, r, pat, sd) for name, pol in BENCH for r in rates
            for pat in PATTERNS for sd in range(seeds)]
    with Pool() as pool:
        res = dict(zip(jobs, pool.map(_run, jobs)))
    for r in rates:
        print(f'== {k} x {k} mesh, offered {r}, mean of {seeds} seeds: '
              'accepted throughput / latency')
        print(f'{"scheme":<26}' + ''.join(f'{p:>15}' for p in PATTERNS))
        for name, pol in BENCH:
            cells = []
            for pat in PATTERNS:
                v = [res[(k, name, pol, r, pat, sd)] for sd in range(seeds)]
                cells.append(f'{sum(x[0] for x in v) / seeds:.3f}/{sum(x[1] for x in v) / seeds:.0f}')
            print(f'{name + " " + pol:<26}' + ''.join(f'{c:>15}' for c in cells))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--k', type=int, default=8)
    ap.add_argument('--policy', default='random')
    ap.add_argument('--patterns', default='uniform,transpose,bitcomp')
    ap.add_argument('--rates', default='0.1,0.2,0.3,0.4,0.5')
    ap.add_argument('--schemes', default='duatoMesh,westFirstMesh,northLastMesh')
    ap.add_argument('--bench', action='store_true')
    ap.add_argument('--seeds', type=int, default=3)
    args = ap.parse_args()
    rates = [float(r) for r in args.rates.split(',')]
    if args.bench:
        bench(args.k, rates, args.seeds)
        return
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
