#!/usr/bin/env python3
"""Flow control at equal storage on the 8 x 8 mesh (simulation; nothing here is proved).

Same mechanics as `routing_sim.py` (one-packet slots, random move order every cycle, unbounded
source queues). Every directed link has 2 slots in the baseline; the experiments reallocate them:

* `alloc`: the two slots of a link shared between the virtual channels (escape may take both,
  adaptive at most one: `shared`), or used as one lane of depth 2 (`deep1`), against one slot per
  virtual channel (`split`); `split3` (3 slots) is the more-storage reference.
* `lanes`: the same total number of slots moved towards the middle of each row and column
  (lanes per link position along its dimension; lane 0 the XY escape, the rest adaptive).

Findings (accepted throughput at offered 0.8, mean of 2 seeds): sharing slots or deepening one
lane loses at equal storage (head-of-line blocking; escape packets hog shared slots); moving lanes
to the middle trades (+17 % uniform, +12 % shuffle, +80 % bit complement, +24 % hotspot against
-7 % transpose, -20 % bit reversal for 1,2,2,4,2,2,1); only more storage wins everywhere.

Usage: python3 scripts/flow_control_experiments.py [alloc|lanes]
"""
import random
import sys
from collections import deque
from routing_sim import destination

PATTERNS = ['uniform', 'transpose', 'shuffle', 'bitrev', 'bitcomp', 'hotspot']

def run_alloc(k, scheme, alloc, rate, pattern, cycles=5000, warmup=1500, seed=1):
    rnd = random.Random(seed); n = k*k
    # link id: (u, dir) dir 0..3 E W N S; head node
    def nb(u, dr):
        x, y = u % k, u // k
        if dr == 0 and x < k-1: return u+1
        if dr == 1 and x > 0: return u-1
        if dr == 2 and y < k-1: return u+k
        if dr == 3 and y > 0: return u-k
        return None
    q = {}  # (u,dr) -> [deque vc0, deque vc1]
    for u in range(n):
        for dr in range(4):
            if nb(u, dr) is not None: q[(u, dr)] = [deque(), deque()]
    inj = [None]*n; srcq = [deque() for _ in range(n)]
    def caps(vc):  # max slots for vc, total
        if alloc == 'split': return (1, 1)[vc], 2          # one slot per VC
        if alloc == 'shared': return (2, 1)[vc], 2          # escape may take both, adaptive <= 1
        if alloc == 'deep1': return (2, 0)[vc], 2           # one lane, depth 2
        if alloc == 'split3': return (2, 1)[vc], 3          # 3 slots (more storage) reference
    def has_room(link, vc):
        a, b = q[link]; m, tot = caps(vc)
        return len(q[link][vc]) < m and len(a)+len(b) < tot
    def xy(u, d):
        x, y, dx, dy = u % k, u//k, d % k, d//k
        return 0 if x < dx else 1 if x > dx else 2 if y < dy else 3
    def yx(u, d):
        x, y, dx, dy = u % k, u//k, d % k, d//k
        return 2 if y < dy else 3 if y > dy else xy(u, d)
    def prod(u, d):
        x, y, dx, dy = u % k, u//k, d % k, d//k
        r = []
        if x < dx: r.append(0)
        if x > dx: r.append(1)
        if y < dy: r.append(2)
        if y > dy: r.append(3)
        return r
    def cands(u, d, cur_vc, src):
        esc = ((u, xy(u, d)), 0)
        if scheme == 'xy':        # deterministic XY; on 'split' both VCs usable (dualXY)
            return [esc] + ([((u, xy(u, d)), 1)] if alloc != 'deep1' else [])
        if scheme == 'duato':     # escape XY on vc0 + any productive on vc1, random among free
            return [esc] + [((u, dr), 1) for dr in prod(u, d)]
        if scheme == 'tiered':
            pref = esc if (cur_vc == 0 and not src) else ((u, yx(u, d)), 1)
            return [[pref] + ([esc] if src else []), [esc], [((u, dr), 1) for dr in prod(u, d)]]
    lat = []
    for t in range(cycles):
        # eject
        for link, qs in q.items():
            h = nb(*link)
            for vc in (0, 1):
                while qs[vc] and qs[vc][0][0] == h:
                    d, born = qs[vc].popleft()
                    if t >= warmup: lat.append(t-born)
                    break
        movers = [(link, vc) for link, qs in q.items() for vc in (0, 1) if qs[vc]]
        movers += [('inj', u) for u in range(n) if inj[u] is not None]
        rnd.shuffle(movers); moved = set()
        for m in movers:
            if m[0] == 'inj':
                u = m[1]; pkt = inj[u]
                if pkt is None: continue
                src, cur_vc = True, 0
            else:
                link, vc = m; qs = q[link]
                if not qs[vc] or id(qs[vc][0]) in moved: continue
                pkt = qs[vc][0]; u = nb(*link); src, cur_vc = False, vc
            d = pkt[0]
            if u == d: continue
            cs = cands(u, d, cur_vc, src)
            if scheme == 'tiered':
                choice = []
                for tier in cs:
                    f = [c for c in tier if has_room(*c)]
                    if f: choice = f; break
            else:
                choice = [c for c in cs if has_room(*c)]
            if not choice: continue
            tl, tv = rnd.choice(choice)
            if m[0] == 'inj': inj[u] = None
            else: q[link][vc].popleft()
            q[tl][tv].append(pkt); moved.add(id(pkt))
        for s in range(n):
            if rnd.random() < rate:
                d = destination(pattern, s, k, rnd)
                if d != s: srcq[s].append((d, t))
            if inj[s] is None and srcq[s]: inj[s] = srcq[s].popleft()
    return len(lat)/((cycles-warmup)*n)


def run_lanes(k, profile, rate, pattern, cycles=5000, warmup=1500, seed=1):
    rnd = random.Random(seed); n = k*k
    def nb(u, dr):
        x, y = u % k, u // k
        if dr == 0 and x < k-1: return u+1
        if dr == 1 and x > 0: return u-1
        if dr == 2 and y < k-1: return u+k
        if dr == 3 and y > 0: return u-k
    occ = {}; lanes = {}
    for u in range(n):
        for dr in range(4):
            v = nb(u, dr)
            if v is None: continue
            pos = min(u % k, v % k) if dr < 2 else min(u // k, v // k)
            lanes[(u, dr)] = profile[pos]
    def xy(u, d):
        x, y, dx, dy = u % k, u//k, d % k, d//k
        return 0 if x < dx else 1 if x > dx else 2 if y < dy else 3
    def prod(u, d):
        x, y, dx, dy = u % k, u//k, d % k, d//k
        return [dr for dr, ok in ((0, x < dx), (1, x > dx), (2, y < dy), (3, y > dy)) if ok]
    inj = [None]*n; srcq = [deque() for _ in range(n)]; lat = []
    for t in range(cycles):
        for c in [c for c, p in occ.items() if nb(c[0], c[1]) == p[0]]:
            d, born = occ.pop(c)
            if t >= warmup: lat.append(t-born)
        movers = list(occ) + [('inj', u) for u in range(n) if inj[u] is not None]
        rnd.shuffle(movers); moved = set()
        for c in movers:
            if c[0] == 'inj':
                u = c[1]; pkt = inj[u]
            else:
                if c not in occ or c in moved: continue
                pkt = occ[c]; u = nb(c[0], c[1])
            d = pkt[0]
            if u == d: continue
            cs = [(u, xy(u, d), 0)] + [(u, dr, l) for dr in prod(u, d) for l in range(1, lanes[(u, dr)])]
            free = [x for x in cs if x not in occ]
            if not free: continue
            c2 = rnd.choice(free)
            if c[0] == 'inj': inj[u] = None
            else: del occ[c]
            occ[c2] = pkt; moved.add(c2)
        for s in range(n):
            if rnd.random() < rate:
                d = destination(pattern, s, k, rnd)
                if d != s: srcq[s].append((d, t))
            if inj[s] is None and srcq[s]: inj[s] = srcq[s].popleft()
    return len(lat)/((cycles-warmup)*n)


def main():
    from multiprocessing import Pool
    mode = sys.argv[1] if len(sys.argv) > 1 else 'alloc'
    if mode == 'alloc':
        rows = {f'{s}/{a}': (s, a) for s, a in [('xy', 'split'), ('xy', 'deep1'), ('duato', 'split'),
                ('duato', 'shared'), ('tiered', 'split'), ('tiered', 'shared'), ('duato', 'split3')]}
        fn = run_alloc
        jobs = [(8, *v, 0.8, p, 5000, 1500, sd) for v in rows.values() for p in PATTERNS for sd in (1, 2)]
    else:
        rows = {'even 2222222': (2,) * 7, 'mid 1224221': (1, 2, 2, 4, 2, 2, 1),
                'mid 1232321': (1, 2, 3, 2, 3, 2, 1), 'mid 1233321 (+1)': (1, 2, 3, 3, 3, 2, 1),
                'even 3333333 (+7)': (3,) * 7}
        fn = run_lanes
        jobs = [(8, v, 0.8, p, 5000, 1500, sd) for v in rows.values() for p in PATTERNS for sd in (1, 2)]
    with Pool() as pool:
        res = dict(zip(jobs, pool.starmap(fn, jobs)))
    print(f'{mode:<20}' + ''.join(f'{p:>11}' for p in PATTERNS))
    for name, v in rows.items():
        vs = v if isinstance(v, tuple) and isinstance(v[0], str) else (v,)
        cells = []
        for p in PATTERNS:
            xs = [r for j, r in res.items() if j[1:1 + len(vs)] == vs and j[1 + len(vs) + 1] == p]
            cells.append(sum(xs) / len(xs))
        print(f'{name:<20}' + ''.join(f'{c:>11.3f}' for c in cells))


if __name__ == '__main__':
    main()
