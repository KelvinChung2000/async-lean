#!/usr/bin/env python3
"""Experiments with selections on the mesh, beyond `tieredMesh` (nothing here is proved).

Same mechanics as `routing_sim.py` (one-packet channels, random move order, one injection
channel per node).  A packet carries a mode, chosen at its source; a scheme is a mode or a rule
choosing modes.  `name@g` throttles the sources at `g` free channels (default 4, 0 = off),
`name:w` sets the patience `w`.

Modes (all take hops of Duato's mesh, those ending in `_wf` and `wf` of the west-first mesh):
  tiered      the tiers of `tieredMesh`
  tiered_wf   the same, then the extra west-first hops
  xy2         XY on either virtual channel (with `@0`: `dualXY` of routing_sim.py)
  xyfirst(_wf) XY on either virtual channel, then any hop on virtual channel 1 (then the rest)
  patient(_wf) XY on either virtual channel until blocked `w` cycles, then the tiered order
  yx          YX on virtual channel 1, then the escape hop
  romm        two-phase XY through a random intermediate node of the minimal quadrant
  oracle      the free hop whose remaining dimension-order path is least occupied, looking at
              the whole network
  rand, wf    random among the free hops of Duato's / the west-first mesh
Rules choosing modes:
  learn       every source learns, per destination quadrant, the mode with the least latency
              (epsilon-greedy over tiered, xy2, yx, rand, wf)
  portfolio   a controller switches the mode of new packets between tiered@4, tiered_wf@4 and
              xy2@0, keeping the one with the most deliveries per epoch
  dist<D>     xy2@0 for packets travelling at least D hops, tiered_wf@4 for the others

Usage: python3 scripts/routing_experiments.py K SCHEMES RATES SEEDS
  e.g. python3 scripts/routing_experiments.py 8 tiered,oracle,learn 0.15,0.2,0.3,0.4,0.6 2
prints the peak accepted throughput (packets / node / cycle) over RATES for every pattern.
"""
import sys, random
from routing_sim import mesh, destination, PATTERNS
from collections import deque

ARMS = ['tiered', 'xy2', 'yx', 'rand', 'wf']

def sim(k, scheme, rate, pattern, cycles=6000, warmup=2000, seed=1, eps=0.1, alpha=0.1):
    g, w = 4, 0
    if ':' in scheme:
        scheme, w = scheme.split(':'); w = int(w)
    if '@' in scheme:
        scheme, g = scheme.split('@'); g = int(g)
    ch, head, routes = mesh(k)
    duato, wfm = routes['duatoMesh'], routes['westFirstMesh']
    rnd = random.Random(seed)
    n = k * k
    occ = {}                       # channel -> [dest, born, mode, (injected, source), mid, waited, g]
    queues = [deque() for _ in range(n)]
    lat = []
    est = {}                       # (s, key, arm) -> ewma network latency
    def X(u): return u % k
    def Y(u): return u // k
    def xy(u, d): return 0 if X(u) < X(d) else 1 if X(d) < X(u) else 2 if Y(u) < Y(d) else 3
    def yx(u, d): return 2 if Y(u) < Y(d) else 3 if Y(d) < Y(u) else xy(u, d)
    def nfree(v): return sum(1 for dr in range(4) for vc in (0, 1) if ch(v, dr, vc) not in occ)
    nb = lambda u, r: [u + 1, u - 1, u + k, u - k][r]
    def pathcost(u, d, first):
        # occupied channels (both VCs) along "go `first`, finish that dimension, then the other"
        cost, v, r = 0, u, first
        steps = 0
        while v != d and steps < 4 * k:
            cost += (ch(v, r, 0) in occ) + (ch(v, r, 1) in occ)
            v = nb(v, r); steps += 1
            if v == d: break
            hor = r in (0, 1)
            if hor and X(v) == X(d): r = yx(v, d)
            elif not hor and Y(v) == Y(d): r = xy(v, d)
        return cost
    def key(s, d):
        return ((X(d) > X(s)) - (X(d) < X(s)), (Y(d) > Y(s)) - (Y(d) < Y(s)))

    PORT = [('tiered', 4), ('tiered_wf', 4), ('xy2', 0)]
    E, R = 400, 10
    cur, dl, score = [PORT[0]], [0], {}
    for t in range(cycles):
        for c in [c for c, p in occ.items() if head(c) == p[0]]:
            d, born, mode, inj = occ.pop(c)[:4]
            if t >= warmup: lat.append(t - born)
            if scheme == 'portfolio' and t % E >= E // 2: dl[0] += 1
            if scheme == 'learn':
                s = inj[1]; kk = (s, key(s, d), mode)
                est[kk] = (1 - alpha) * est.get(kk, t - inj[0]) + alpha * (t - inj[0])
        moved = set()
        packets = list(occ); rnd.shuffle(packets)
        for c in packets:
            if c in moved or c not in occ: continue
            pk = occ[c]; d, _, mode, _, mid = pk[:5]
            u = head(c)
            if u == d: continue
            src = c // 2 % 5 == 4
            base = wfm if mode in ('wf', 'xyfirst_wf', 'tiered_wf', 'patient_wf') else duato
            hops = base(c, d)
            free = [q for q in hops if q not in occ]
            gg = pk[6] if len(pk) > 6 else g
            if src and gg: free = [q for q in free if nfree(head(q)) >= gg]     # throttle
            esc = ch(u, xy(u, d), 0)
            if mode == 'tiered':
                pref = esc if c % 2 == 0 and not src else ch(u, yx(u, d), 1)
                tiers = [lambda q: q == pref or (src and q == esc), lambda q: q == esc, lambda q: q % 2 == 1]
            elif mode == 'xyfirst':
                tiers = [lambda q: q // 2 == esc // 2, lambda q: q % 2 == 1]
            elif mode == 'xyfirst_wf':
                tiers = [lambda q: q // 2 == esc // 2, lambda q: q % 2 == 1, lambda q: True]
            elif mode == 'tiered_wf':
                pref = esc if c % 2 == 0 and not src else ch(u, yx(u, d), 1)
                tiers = [lambda q: q == pref or (src and q == esc), lambda q: q == esc, lambda q: q % 2 == 1, lambda q: True]
            elif mode in ('patient', 'patient_wf'):
                # XY on either virtual channel; after waiting w cycles, the tiered order (plus the
                # extra hops of the west-first mesh for patient_wf)
                if pk[5] < w:
                    tiers = [lambda q: q // 2 == esc // 2]
                else:
                    pref = esc if c % 2 == 0 and not src else ch(u, yx(u, d), 1)
                    tiers = [lambda q: q // 2 == esc // 2, lambda q: q == pref, lambda q: q % 2 == 1, lambda q: True]
            elif mode == 'xy2':
                tiers = [lambda q: q // 2 == esc // 2]
            elif mode == 'yx':
                tiers = [lambda q: q == ch(u, yx(u, d), 1), lambda q: q == esc]
            elif mode == 'romm':
                # two-phase XY: XY to the intermediate on VC1, then XY to the destination on VC1;
                # escape hop if blocked
                if mid is not None and u == mid: pk[4] = mid = None
                tgt = mid if mid is not None else d
                tiers = [lambda q: q == ch(u, xy(u, tgt), 1), lambda q: q == esc]
            elif mode == 'oracle':
                tiers = None
                if free:
                    best = min(pathcost(u, d, q // 2 % 5) for q in free)
                    free = [q for q in free if pathcost(u, d, q // 2 % 5) == best]
            else:   # rand, wf
                tiers = None
            if tiers is not None:
                for tr in tiers:
                    if any(tr(q) for q in free):
                        free = [q for q in free if tr(q)]; break
                else:
                    free = []
            if free:
                q = rnd.choice(free)
                pk[5] = 0
                occ[q] = occ.pop(c); moved.add(q)
                if mode == 'romm' and pk[4] is not None and head(q) == pk[4]: pk[4] = None
            else:
                pk[5] += 1
        if scheme == 'portfolio':
            # a controller switches the mode of newly injected packets: each epoch it measures
            # the packets delivered in its second half; every `R` epochs it tries every mode
            ep, pos = divmod(t, E)
            if pos == 0:
                if ep > 0: score[cur[0]] = 0.5 * score.get(cur[0], dl[0]) + 0.5 * dl[0] if cur[0] in score else dl[0]
                rnd_ = ep % (R + len(PORT))
                cur[0] = PORT[rnd_] if rnd_ < len(PORT) else max(PORT, key=lambda m: score.get(m, 0))
                dl[0] = 0
        for s in range(n):
            if rnd.random() < rate:
                d = destination(pattern, s, k, rnd)
                if d != s: queues[s].append((d, t))
            if queues[s] and ch(s, 4, 0) not in occ:
                d, born = queues[s].popleft()
                mid = None
                if scheme == 'learn':
                    kk = key(s, d)
                    tried = [a for a in ARMS if (s, kk, a) not in est]
                    if tried: mode = rnd.choice(tried)
                    elif rnd.random() < eps: mode = rnd.choice(ARMS)
                    else: mode = min(ARMS, key=lambda a: est[(s, kk, a)])
                elif scheme == 'portfolio':
                    mode = cur[0]
                elif scheme.startswith('dist'):
                    D = int(scheme[4:])
                    mode = ('xy2', 0) if abs(X(s) - X(d)) + abs(Y(s) - Y(d)) >= D else ('tiered_wf', 4)
                else:
                    mode = scheme
                gg = g
                if isinstance(mode, tuple): mode, gg = mode
                if mode == 'romm':
                    xs = sorted((X(s), X(d))); ys = sorted((Y(s), Y(d)))
                    mid = rnd.randint(*ys) * k + rnd.randint(*xs)
                    if mid in (s, d): mid = None
                occ[ch(s, 4, 0)] = [d, born, mode, (t, s), mid, 0, gg]
    return len(lat) / ((cycles - warmup) * n)

def run(job):
    k, scheme, r, p, sd = job
    return sim(k, scheme, r, p, seed=sd)

if __name__ == '__main__':
    from multiprocessing import Pool
    k = int(sys.argv[1]); schemes = sys.argv[2].split(',')
    rates = [float(x) for x in sys.argv[3].split(',')]; seeds = int(sys.argv[4])
    jobs = [(k, s, r, p, sd) for s in schemes for r in rates for p in PATTERNS for sd in range(seeds)]
    with Pool() as pool: res = dict(zip(jobs, pool.map(run, jobs)))
    print(f'{k}x{k} peak accepted throughput over rates {rates}')
    print(f'{"scheme":<10}' + ''.join(f'{p:>10}' for p in PATTERNS))
    for s in schemes:
        print(f'{s:<10}' + ''.join(f'{max(sum(res[(k,s,r,p,sd)] for sd in range(seeds))/seeds for r in rates):>10.3f}' for p in PATTERNS))
