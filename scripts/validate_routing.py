#!/usr/bin/env python3
"""Independent checks of the mesh routing results (not part of the Lean development).

The Lean proofs are the authority; this script re-checks their constructions and their
consequences on concrete meshes, with the same channel encoding as `AsyncLean.Examples.Routing`:
channel `ch(u, dir, vc) = (u * 5 + dir) * 2 + vc`, directions 0 east, 1 west, 2 north, 3 south,
4 injection; node `u` is at column `u % k`, row `u // k`.

1. `maximality` : for every mesh size up to `--kmax`, every hop that a minimal routing function
   can add to a turn-model mesh, every pair where a packet can take it, and every point where the
   proof's induction can stop, the deadlock the proof builds (`MeshMaximal.lean`,
   `MeshMetrics.lean`) is replayed: the run is checked step by step and the final configuration
   is checked to be blocked.  This covers the west-first and north-last meshes on two virtual
   channels and on one.
2. `acyclic` : the channel dependency graph of the escape hops (XY) on the legal pairs is
   acyclic for the two-channel meshes, and the full dependency graph is acyclic for the
   one-channel ones (the deadlock freedom arguments).
3. `hops` : every route of every packet has exactly the Manhattan length.
4. `tables` : the number of different routing decisions per router (XY: 4 at inner routers, the
   turn-model meshes: at most 8).
5. `tiered` : the tiered, source-throttled selection of `MeshTiered.lean` (`tieredMesh`), on
   Duato's mesh and the two-channel west-first and north-last meshes up to 4 x 4 and every
   threshold `g <= 8`: long
   random runs of single steps (inject, hop to an offered free channel, eject) never reach a
   configuration that holds a packet but where none can move, and the selection only offers
   permitted free hops.

Usage: python3 scripts/validate_routing.py [--kmax 8] [--walks 60]
"""
import argparse
import sys
from collections import deque


def ch(u, dr, vc):
    return (u * 5 + dr) * 2 + vc


def node(c):
    return c // 10


def dirc(c):
    return c // 2 % 5


class Mesh:
    def __init__(self, k):
        self.k = k

    def head(self, c):
        u, dr, k = node(c), dirc(c), self.k
        return [u + 1, u - 1, u + k, u - k, u][dr]

    def productive(self, u, d):
        k = self.k
        r = []
        if u % k < d % k: r.append(0)
        if d % k < u % k: r.append(1)
        if u // k < d // k: r.append(2)
        if d // k < u // k: r.append(3)
        return r

    def xy(self, u, d):
        return self.productive(u, d)[0]

    def west_first(self, u, d):
        p = self.productive(u, d)
        return [1] if 1 in p else p

    def north_last(self, u, d):
        p = self.productive(u, d)
        return [2] if p == [2] else [x for x in p if x != 2]

    # routing functions: (channel, destination) -> list of next channels
    def two_vc(self, turn):
        def route(c, d):
            u = self.head(c)
            x = self.xy(u, d)
            return ([ch(u, x, 0)] + [ch(u, e, 0) for e in turn(u, d) if e != x]
                    + [ch(u, e, 1) for e in self.productive(u, d)])
        return route

    def one_vc(self, turn):
        return lambda c, d: [ch(self.head(c), e, 0) for e in turn(self.head(c), d)]

    def minimal(self, vcs):
        return lambda c, d: [ch(self.head(c), e, vc) for vc in vcs
                             for e in self.productive(self.head(c), d)]

    def injections(self):
        n = self.k * self.k
        return [(ch(s, 4, 0), d) for s in range(n) for d in range(n) if d != s]


def reachable_pairs(m, route):
    seen = set(m.injections())
    todo = deque(seen)
    while todo:
        c, d = todo.popleft()
        if m.head(c) == d:
            continue
        for c2 in route(c, d):
            if (c2, d) not in seen:
                seen.add((c2, d))
                todo.append((c2, d))
    return seen


# ---------------------------------------------------------------- 1. maximality

class Run:
    """A configuration of single-packet channels and a checked run under a routing function."""

    def __init__(self, m, route, injections):
        self.m, self.route, self.inj = m, route, set(injections)
        self.occ = {}

    def inject(self, c, d):
        assert (c, d) in self.inj, ('not an injection', c, d)
        assert c not in self.occ, ('injection channel busy', c)
        self.occ[c] = d

    def hop(self, c, c2):
        d = self.occ[c]
        assert self.m.head(c) != d, ('arrived', c)
        assert c2 in self.route(c, d), ('hop not permitted', c, c2, d)
        assert c2 not in self.occ, ('target busy', c2)
        del self.occ[c]
        self.occ[c2] = d

    def blocked(self, hi):
        """Every packet has not arrived and all its hops under `hi` lead to busy channels."""
        return self.occ and all(self.m.head(c) != d and all(c2 in self.occ for c2 in hi(c, d))
                                for c, d in self.occ.items())


def place(m, run, pairs):
    """Inject each packet at the tail node of its channel and hop it there."""
    for c2, d in pairs:
        run.inject(ch(node(c2), 4, 0), d)
        run.hop(ch(node(c2), 4, 0), c2)


def square(m, cx, cy, side, vert, two_vc, extra):
    """The packets the proof places around the frozen packet, which sits in the channel going
    `vert` (+1 north, -1 south) into node C = (cx, cy), with its destination on side `side`
    (-1 west, +1 east).  `extra`: the blocking group for a vertical hop left on virtual channel 1
    (`caseB`, two virtual channels only)."""
    k = m.k
    at = lambda x, y: y * k + x
    C, B = at(cx, cy), at(cx, cy - vert)
    D, A = at(cx + side, cy), at(cx + side, cy - vert)
    hdir = {-1: 1, 1: 0}[side]          # horizontal direction from C to D
    back = {-1: 0, 1: 1}[side]          # from A to B
    vdir = {1: 2, -1: 3}[vert]          # from B to C
    vback = {1: 3, -1: 2}[vert]         # from D to A
    vcs = [0, 1] if two_vc else [0]
    pairs = []
    pairs += [(ch(A, back, v), C) for v in vcs]           # A -> B, then towards C
    if two_vc:
        pairs += [(ch(B, vdir, 1), D)]                    # B -> C beside the frozen packet
    pairs += [(ch(C, hdir, v), A) for v in vcs]           # C -> D, then towards A
    pairs += [(ch(D, vback, v), B) for v in vcs]          # D -> A, then towards B
    if extra:
        E2, F = at(cx, cy + vert), at(cx + side, cy + vert)
        pairs += [(ch(C, vdir, 1), F)]                    # C -> E2 on virtual channel 1
        pairs += [(ch(E2, hdir, v), D) for v in vcs]      # E2 -> F, then towards D
        pairs += [(ch(F, vback, v), A) for v in vcs]      # F -> D, then on towards A
    return pairs


def check_maximality(k, two_vc, turn_name):
    m = Mesh(k)
    turn = m.west_first if turn_name == 'west-first' else m.north_last
    lo = m.two_vc(turn) if two_vc else m.one_vc(turn)
    hi = m.minimal([0, 1] if two_vc else [0])
    checked = 0
    for c, d in sorted(reachable_pairs(m, lo)):
        u = m.head(c)
        if u == d:
            continue
        for c2 in hi(c, d):
            if c2 in lo(c, d):
                continue
            # an extra hop: on virtual channel 0, vertical
            e, vc = dirc(c2), c2 % 2
            assert vc == 0 and e in (2, 3), ('unexpected extra hop', c, c2, d)
            if turn_name == 'west-first':
                assert d % k < u % k
            else:
                assert e == 2 and d % k != u % k
            vert = 1 if e == 2 else -1
            side = -1 if d % k < u % k else 1
            x = u % k
            # find a route of the packet alone to `c` in the turn-model mesh (breadth first)
            prevs = {q: None for q in m.injections() if q[1] == d}
            todo = deque(prevs)
            while todo:
                q = todo.popleft()
                if q == (c, d):
                    break
                if m.head(q[0]) == d:
                    continue
                for b in lo(q[0], d):
                    if (b, d) not in prevs:
                        prevs[(b, d)] = q
                        todo.append((b, d))
            trail, q = [], (c, d)
            while q is not None:
                trail.append(q[0])
                q = prevs[q]
            trail.reverse()
            # the packet climbs on virtual channel 0 to row `y`, where the induction stops: in its
            # destination's row (top), or because the next vertical hop on virtual channel 0 is
            # not permitted
            x, y, path = u % k, u // k + vert, [c2]
            while True:
                chain = set(zip([c] + path, path))
                lo_ext = lambda a, dd, chain=chain: lo(a, dd) + [b for (p, b) in chain
                                                                 if p == a and dd == d]
                run = Run(m, lo_ext, m.injections())
                run.inject(trail[0], d)
                for a, b in zip(trail, trail[1:]):
                    run.hop(a, b)
                for a, b in zip([c] + path, path):
                    run.hop(a, b)
                top = y == d // k
                place(m, run, square(m, x, y, side, vert, two_vc, two_vc and not top))
                nxt = ch(m.head(path[-1]), e, 0)
                hi_stop = lambda a, dd: [b for b in hi(a, dd)
                                         if not (a == path[-1] and dd == d and b == nxt)]
                assert run.blocked(hi_stop), ('not blocked', k, c, c2, d, y)
                checked += 1
                if top:
                    break
                path.append(nxt)
                y += vert
    return checked


# ---------------------------------------------------------------- 2. acyclic dependencies

def legal_pairs(m, route):
    return reachable_pairs(m, route)


def acyclic(m, route, esc):
    deps = {}
    for c, d in legal_pairs(m, route):
        if m.head(c) == d:
            continue
        for c2 in esc(c, d):
            deps.setdefault(c, set()).add(c2)
    state = {}

    def visit(c):
        stack = [(c, iter(deps.get(c, ())))]
        state[c] = 1
        while stack:
            v, it = stack[-1]
            for w in it:
                if state.get(w) == 1:
                    return False
                if w not in state:
                    state[w] = 1
                    stack.append((w, iter(deps.get(w, ()))))
                    break
            else:
                state[v] = 2
                stack.pop()
        return True

    return all(visit(c) for c in list(deps) if c not in state)


# ---------------------------------------------------------------- 5. tiered selection

def tiered_offers(m, route, occ, c, d, g):
    """The hops `tieredMesh` offers the packet with destination `d` in channel `c` (the Lean
    definition: the free permitted hops of the first tier that admits one)."""
    k, u = m.k, m.head(c)
    yx = 2 if u // k < d // k else 3 if d // k < u // k else m.xy(u, d)
    src = dirc(c) == 4
    esc = ch(u, m.xy(u, d), 0)
    pref = esc if c % 2 == 0 and not src else ch(u, yx, 1)

    def free_out(v):
        return sum(1 for dr in range(4) for vc in (0, 1) if ch(v, dr, vc) not in occ)

    def open_(q):
        return not src or g <= free_out(m.head(q))
    tiers = [lambda q: q == pref or (src and q == esc), lambda q: q == esc, lambda q: q % 2 == 1]
    for t in tiers:
        offered = [q for q in route(c, d) if q not in occ and open_(q) and t(q)]
        if offered:
            return offered
    return []


def check_tiered(k, turn_name, g, walks, steps, rnd):
    m = Mesh(k)
    turn = {'west-first': m.west_first, 'north-last': m.north_last,
            'duato': lambda u, d: [m.xy(u, d)]}[turn_name]
    route = m.two_vc(turn)
    inj = m.injections()
    for _ in range(walks):
        occ = {}
        for _ in range(steps):
            moves = []
            for c, d in occ.items():
                if m.head(c) == d:
                    moves.append(('eject', c, None))
                    continue
                offered = tiered_offers(m, route, occ, c, d, g)
                assert all(q in route(c, d) and q not in occ for q in offered), (c, d, offered)
                moves += [('hop', c, q) for q in offered]
            if occ and not moves:
                raise AssertionError(('deadlock', k, turn_name, g, sorted(occ.items())))
            injects = [(c, d) for c, d in inj if c not in occ]
            # fill the network: inject with probability 0.7 when possible
            if injects and (not moves or rnd.random() < 0.7):
                c, d = rnd.choice(injects)
                occ[c] = d
            elif moves:
                kind, c, q = rnd.choice(moves)
                d = occ.pop(c)
                if kind == 'hop':
                    occ[q] = d
    return walks


# ---------------------------------------------------------------- 3, 4. hops and tables

def check_hops(m, route):
    k = m.k
    for s in range(k * k):
        for d in range(k * k):
            if s == d:
                continue
            dist = abs(s % k - d % k) + abs(s // k - d // k)
            frontier = {ch(s, 4, 0)}
            for _ in range(dist):
                assert all(m.head(c) != d for c in frontier)
                frontier = {c2 for c in frontier for c2 in route(c, d)}
            assert frontier and all(m.head(c) == d for c in frontier), (s, d)


def table_size(m, route, u):
    return len({tuple(route(ch(u, 4, 0), d)) for d in range(m.k * m.k) if d != u})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--kmax', type=int, default=8)
    ap.add_argument('--walks', type=int, default=60)
    args = ap.parse_args()
    ok = True
    for k in range(2, args.kmax + 1):
        m = Mesh(k)
        line = [f'k={k}']
        for two_vc in (True, False):
            for name in ('west-first', 'north-last'):
                n = check_maximality(k, two_vc, name)
                line.append(f'{name} {2 if two_vc else 1}VC maximal ({n} deadlocks replayed)')
        schemes = {
            'xy': m.one_vc(lambda u, d: [m.xy(u, d)]),
            'wf1': m.one_vc(m.west_first), 'nl1': m.one_vc(m.north_last),
            'wf2': m.two_vc(m.west_first), 'nl2': m.two_vc(m.north_last),
        }
        xyesc = lambda c, d: [ch(m.head(c), m.xy(m.head(c), d), 0)]
        for name, r in schemes.items():
            esc = xyesc if name in ('wf2', 'nl2') else r
            if not acyclic(m, r, esc):
                ok = False
                line.append(f'{name}: CYCLE')
            check_hops(m, r)
        if k >= 3:
            inner = [u for u in range(k * k) if 0 < u % k < k - 1 and 0 < u // k < k - 1]
            sizes = {name: max(table_size(m, r, u) for u in inner) for name, r in schemes.items()}
            assert sizes['xy'] == 4 and all(v <= 8 for v in sizes.values()), sizes
            line.append('tables ' + ' '.join(f'{n}={v}' for n, v in sizes.items()))
        print(line[0] + ': ' + '; '.join(line[1:]))
    import random
    rnd = random.Random(1)
    for k in (2, 3, 4):
        walks = args.walks // 3 if k == 4 else args.walks
        for name in ('duato', 'west-first', 'north-last'):
            for g in range(9):
                check_tiered(k, name, g, walks, 400, rnd)
        print(f'k={k}: tiered selection, g = 0..8: no deadlock in {walks} random runs of 400 '
              'steps per threshold, on Duato\'s, the west-first and the north-last mesh')
    print('all checks passed' if ok else 'FAILED')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
