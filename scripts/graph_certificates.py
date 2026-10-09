#!/usr/bin/env python3
"""Exact fluid-model certificates for traffic patterns on the 8 x 8 torus and the 6-dimensional
hypercube (generates the data of `AsyncLean/Flow/GraphPatterns/Data.lean`, checked and proved
sound in Lean by `AsyncLean/Flow/GraphCert.lean`; the theorems are in
`AsyncLean/Flow/GraphPatterns.lean`).

The fluid model is the one of `scripts/routing_bounds.py` (`lp`) and
`scripts/fluid_certificates.py`, on a general port graph: capacity 2 on every directed link, one
commodity per destination, the largest theta such that theta * dem is routable, over minimal
paths only (every link brings the commodity strictly closer in hop distance) or over any paths.
For every certificate:

* the dual (upper bound): HiGHS's capacity duals give link lengths `len`; they are rounded to
  rationals and scaled to integers, the potentials `phi[d][v]` are the exact shortest distances
  from v to d under `len` (over the links that bring d closer, for the minimal-only bound), and
  theta* = 2 * sum(len) / sum(dem * phi) exactly.  Any nonnegative `len` gives a valid bound, so
  the rounding only has to be good enough to be tight.
* the primal (lower bound): a flow at theta = theta* (minimising the total flow), from HiGHS,
  rounded to rationals and verified EXACTLY (conservation, capacity, minimality).  The script
  stops if a check fails or the two bounds differ.

Graphs (vertex indices 0..63, as in the Lean file `GraphPatterns.lean`):

* torus: s = x + 8 y; ports 0: x + 1, 1: x - 1, 2: y + 1, 3: y - 1 (mod 8); the port back from
  the end of port i is 1, 0, 3, 2.
* hypercube: coordinate i of the vertex is bit i of s; port i (0 <= i < 6) flips bit i and is
  its own way back.

Patterns (on indices, the same on both graphs; `routing_bounds.matrix(8, p)` for the six
simulator patterns): uniform, transpose (x + 8 y -> y + 8 x), shuffle (rotate the 6 bits left),
bitrev (reverse the 6 bits), bitcomp (complement the 6 bits), hotspot (centre 36), tornado
(x -> x + 3 mod 8, same y), neighbor (x -> x + 1 mod 8, same y).

Results (theta per active source; minimal-only / any routing; the script prints them):

  torus      tornado    2/3   / 16/15  (+60 %)    hypercube  shuffle    12/5 / 108/31  (+45 %)
             shuffle    1     / 8/5    (+60 %)               transpose  4
             transpose  4/3   / 20/11  (+36 %)               bitrev     4
             neighbor   2     / 16/7   (+14 %)               bitcomp    2
             bitrev     16/9  / 40/21  (+7 %)                tornado    2
             bitcomp    1

When the two optima agree, one minimal flow with a dual over all routings certifies both.  The
primal is first tried as the exact flow that splits every commodity evenly over its minimal ports
(`split_flow`; it is optimal for bit complement on the hypercube, where the LP's flow is not a
vertex and does not round), then from HiGHS.

Tables are packed per commodity into one natural number, digit P j + i (base 2^b) = the rate of
the commodity leaving node j through port i, times D (P = 4 on the torus, 6 on the hypercube).

Usage: python3 scripts/graph_certificates.py [--out AsyncLean/Flow/GraphPatterns/Data.lean]
       [--only torusTornado,cubeShuffle,...]   (testing: writes only those certificates)
Requires scipy (HiGHS).
"""
import argparse
import heapq
import os
import sys
from collections import deque
from fractions import Fraction as Fr
from math import lcm

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from routing_bounds import matrix  # noqa: E402

K = 8
N = K * K
CAP = 2


class Graph:
    """A port graph on the indices 0..N-1: `step(j, i)` is the end of port i of j (None: no
    port), `back(j, i)` the port at that end leading back, `dist` the hop distance (closed form,
    checked against breadth-first search)."""

    def __init__(self, name, ports, step, back, dist):
        self.name, self.P, self.step, self.back = name, ports, step, back
        self.links = [(j, i, step(j, i)) for j in range(N) for i in range(ports)
                      if step(j, i) is not None]
        self.D = [[dist(a, b) for b in range(N)] for a in range(N)]
        for s in range(N):                       # the closed form is the hop distance
            seen = {s: 0}
            q = deque([s])
            while q:
                u = q.popleft()
                for (_, _, v) in self.links_from(u):
                    if v not in seen:
                        seen[v] = seen[u] + 1
                        q.append(v)
            assert all(seen[v] == self.D[s][v] for v in range(N)), name
        for (j, i, v) in self.links:             # the conditions of `PortGraph.wfCheck`
            b = back(j, i)
            assert 0 <= b < ports and step(v, b) == j and back(v, b) == i
            assert all(i2 == i or step(j, i2) != v for i2 in range(ports))

    def links_from(self, u):
        return [(u, i, self.step(u, i)) for i in range(self.P) if self.step(u, i) is not None]


def torus_step(j, i):
    x, y = j % K, j // K
    return [(x + 1) % K + K * y, (x + K - 1) % K + K * y, x + K * ((y + 1) % K),
            x + K * ((y + K - 1) % K)][i]


def ring(a, b):
    return min((a + K - b) % K, (b + K - a) % K)


TORUS = Graph('torus', 4, torus_step, lambda j, i: [1, 0, 3, 2][i],
              lambda a, b: ring(a % K, b % K) + ring(a // K, b // K))
CUBE = Graph('cube', 6, lambda j, i: j ^ (1 << i), lambda j, i: i,
             lambda a, b: bin(a ^ b).count('1'))


def tornado(s):
    return (s % K + 3) % K + K * (s // K)


def neighbor(s):
    return (s % K + 1) % K + K * (s // K)


def perm_demand(p):
    return [[Fr(1) if d == p(s) and d != s else Fr(0) for d in range(N)] for s in range(N)]


def demands():
    out = {}
    for p in ['uniform', 'transpose', 'shuffle', 'bitrev', 'bitcomp', 'hotspot']:
        lam = matrix(K, p)
        if p == 'uniform':
            dem = [[Fr(1, N - 1) if s != d else Fr(0) for d in range(N)] for s in range(N)]
        elif p == 'hotspot':
            h = 4 + K * 4
            dem = [[(Fr(4, 5 * (N - 1)) if s != d else Fr(0)) +
                    (Fr(1, 5) if d == h and s != h else Fr(0)) for d in range(N)]
                   for s in range(N)]
        else:
            dem = [[Fr(int(round(lam[s][d]))) for d in range(N)] for s in range(N)]
        assert all(abs(float(dem[s][d]) - lam[s][d]) < 1e-12 for s in range(N) for d in range(N))
        out[p] = dem
    out['tornado'] = perm_demand(tornado)
    out['neighbor'] = perm_demand(neighbor)
    return out


def lp_vars(g, dem, minimal):
    act = [d for d in range(N) if any(dem[s][d] for s in range(N))]
    return [(d, l) for d in act for l, (u, _, v) in enumerate(g.links)
            if u != d and (not minimal or g.D[v][d] < g.D[u][d])]


def lp_system(g, var):
    rows, cols, vals, eq = [], [], [], {}
    for c, (d, l) in enumerate(var):
        u, _, v = g.links[l]
        for node, sgn in ((u, 1), (v, -1)):
            if node != d:
                rows.append(eq.setdefault((d, node), len(eq)))
                cols.append(c)
                vals.append(sgn)
    a_ub = coo_matrix((np.ones(len(var)), ([l for _, l in var], list(range(len(var))))),
                      shape=(len(g.links), len(var)))
    return rows, cols, vals, eq, a_ub


def lp_dual(g, dem, minimal):
    """Max theta (HiGHS); returns the float link lengths (capacity duals)."""
    var = lp_vars(g, dem, minimal)
    rows, cols, vals, eq, a_ub = lp_system(g, var)
    nv = len(var) + 1
    for (d, node), r in eq.items():
        rows.append(r)
        cols.append(nv - 1)
        vals.append(-float(dem[node][d]))
    a_eq = coo_matrix((vals, (rows, cols)), shape=(len(eq), nv)).tocsr()
    a_ub = coo_matrix((a_ub.data, (a_ub.row, a_ub.col)), shape=(len(g.links), nv)).tocsr()
    c = np.zeros(nv)
    c[-1] = -1
    res = linprog(c, A_ub=a_ub, b_ub=np.full(len(g.links), float(CAP)), A_eq=a_eq,
                  b_eq=np.zeros(len(eq)), bounds=(0, None), method='highs-ds')
    assert res.status == 0, res.message
    return res.x[-1], -res.ineqlin.marginals


def exact_dual(g, lens, minimal, den):
    """Integer lengths and exact potentials (shortest distances)."""
    fr = [max(Fr(x).limit_denominator(den), Fr(0)) for x in lens]
    scale = lcm(*[x.denominator for x in fr])
    length = {(u, i): int(x * scale) for (u, i, _), x in zip(g.links, fr)}
    into = {v: [] for v in range(N)}
    for (u, i, w) in g.links:
        into[w].append((u, i))
    phi = []
    for d in range(N):
        best = {d: 0}
        pq = [(0, d)]
        done = set()
        while pq:
            dv, v = heapq.heappop(pq)
            if v in done:
                continue
            done.add(v)
            for (u, i) in into[v]:
                if not minimal or g.D[v][d] < g.D[u][d]:
                    nd = dv + length[(u, i)]
                    if nd < best.get(u, nd + 1):
                        best[u] = nd
                        heapq.heappush(pq, (nd, u))
        phi.append([best[v] for v in range(N)])
    return length, phi


def check_dual(g, dem, length, phi, minimal):
    """The checks of `dualCheck` and the bound of `boundCheck`, exactly; returns the bound."""
    for d in range(N):
        assert phi[d][d] == 0
        for (u, i, v) in g.links:
            if not minimal or g.D[v][d] < g.D[u][d]:
                assert phi[d][u] <= phi[d][v] + length[(u, i)]
    a = sum(dem[s][d] * phi[d][s] for s in range(N) for d in range(N))
    assert a > 0
    return CAP * sum(length.values()) / a


def lp_primal(g, dem, theta, minimal, den):
    """A flow at the exact theta (HiGHS, minimising the total flow), rounded to rationals."""
    var = lp_vars(g, dem, minimal)
    rows, cols, vals, eq, a_ub = lp_system(g, var)
    b = np.zeros(len(eq))
    for (d, node), r in eq.items():
        b[r] = float(theta * dem[node][d])
    a_eq = coo_matrix((vals, (rows, cols)), shape=(len(eq), len(var))).tocsr()
    res = linprog(np.ones(len(var)), A_ub=a_ub.tocsr(), b_ub=np.full(len(g.links), float(CAP)),
                  A_eq=a_eq, b_eq=b, bounds=(0, None), method='highs-ds')
    if res.status != 0:                       # the rounded dual is not tight
        return None
    flow = {}
    for c, (d, l) in enumerate(var):
        x = Fr(res.x[c]).limit_denominator(den)
        if x:
            u, i, _ = g.links[l]
            flow[(d, u, i)] = x
    return flow


def split_flow(g, dem, theta):
    """The minimal flow that splits every commodity evenly over the ports bringing it closer,
    exactly."""
    flow = {}
    for d in range(N):
        load = {v: theta * dem[v][d] for v in range(N)}
        for v in sorted(range(N), key=lambda v: -g.D[v][d]):
            if v == d or not load[v]:
                continue
            outs = [(i, w) for (_, i, w) in g.links_from(v) if g.D[w][d] < g.D[v][d]]
            for (i, w) in outs:
                x = load[v] / len(outs)
                flow[(d, v, i)] = x
                load[w] += x
    return flow


def check_primal(g, dem, flow, theta, minimal):
    """Conservation, capacity and minimality, exactly (the checks of `consCheck`, `capCheck`,
    `minCheck`)."""
    net = {}
    load = {}
    for (d, u, i), x in flow.items():
        v = g.step(u, i)
        assert x >= 0 and v is not None
        if minimal:
            assert g.D[v][d] < g.D[u][d]
        net[(d, u)] = net.get((d, u), 0) + x
        net[(d, v)] = net.get((d, v), 0) - x
        load[(u, i)] = load.get((u, i), 0) + x
    for d in range(N):
        for v in range(N):
            if v != d and net.get((d, v), 0) != theta * dem[v][d]:
                return False
    return all(x <= CAP for x in load.values())


def pack(values, b):
    return sum(x << (b * j) for j, x in enumerate(values))


def width(values):
    return max(1, max(values).bit_length())


def lean_list(nums):
    return '[' + ',\n  '.join(hex(x) for x in nums) + ']'


def certificate(name, g, dem, minimal_flow, minimal_dual):
    """Compute and verify one certificate; returns its Lean data."""
    _, lens = lp_dual(g, dem, minimal_dual)
    for den in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        length, phi = exact_dual(g, lens, minimal_dual, den)
        theta = check_dual(g, dem, length, phi, minimal_dual)
        flow = None
        f = split_flow(g, dem, theta)
        if minimal_flow and check_primal(g, dem, f, theta, True):
            flow = f
            break
        for pden in (10 ** 4, 10 ** 5, 10 ** 6):
            f = lp_primal(g, dem, theta, minimal_flow, pden)
            if f is None:
                break
            if check_primal(g, dem, f, theta, minimal_flow):
                flow = f
                break
        if flow is not None:
            break
    else:
        raise AssertionError(f'{name}: no exact certificate')
    scale = lcm(*[x.denominator for x in flow.values()])
    P = g.P
    rows = [[int(flow.get((d, j, i), 0) * scale) for j in range(N) for i in range(P)]
            for d in range(N)]
    bg = width([x for r in rows for x in r])
    lens_flat = [length.get((j, i), 0) for j in range(N) for i in range(P)]
    bp = width([x for r in phi for x in r])
    bl = width(lens_flat)
    print(f'{name:<16} theta = {str(theta):<8} (flow {"minimal" if minimal_flow else "any"}, '
          f'dual {"minimal" if minimal_dual else "any"}): D = {scale}, '
          f'{len(flow)} flow entries', file=sys.stderr)
    return dict(name=name, theta=theta, D=scale, bg=bg, rows=[pack(r, bg) for r in rows],
                bp=bp, phi=[pack(r, bp) for r in phi], bl=bl, len=pack(lens_flat, bl), P=P)


def emit(certs, path):
    out = ['/-',
           'Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.',
           '-/',
           'import AsyncLean.Flow.GraphCert',
           '',
           '/-!',
           '# Certificate data for the torus and hypercube patterns',
           '',
           'Generated by `scripts/graph_certificates.py` (do not edit).  For each certificate `c`',
           '(on a graph with `P` ports per vertex, `4` on the torus and `6` on the hypercube):',
           '',
           '* `c.flow` : per commodity `d`, a natural number whose digit `P j + i` in base `2 ^ c.bg`',
           '  is `D` times the rate of commodity `d` leaving vertex `j` through port `i`;',
           '* `c.phi` : per destination `d`, digit `j` in base `2 ^ c.bp` is the potential of `j`;',
           '* `c.len` : digit `P j + i` in base `2 ^ c.bl` is the length of port `i` of vertex `j`;',
           '* `c.G`, `c.P`, `c.L` : the tables as functions of the indices, `c.D` : the scale.',
           '',
           'Also the three index permutations that are not in `AsyncLean.Flow.MeshPatterns`.  The',
           'certificates are checked by the kernel in `AsyncLean.Flow.GraphPatterns.TorusAny`,',
           '`TorusMin` and `Cube`, and used in `AsyncLean.Flow.GraphPatterns`.',
           '-/',
           '',
           'namespace AsyncLean',
           '',
           'namespace Fluid',
           '',
           'namespace GraphPatternData',
           '',
           'open MeshCert',
           '',
           '/-- Tornado on indices: `x + 8 y ↦ (x + 3 mod 8) + 8 y` (`tornado` in the script). -/',
           'def tornadoIdx (j : ℕ) : ℕ := (j % 8 + 3) % 8 + 8 * (j / 8)',
           '',
           '/-- Neighbour on indices: `x + 8 y ↦ (x + 1 mod 8) + 8 y` (`neighbor` in the script). -/',
           'def neighborIdx (j : ℕ) : ℕ := (j % 8 + 1) % 8 + 8 * (j / 8)',
           '',
           '/-- Bit complement on indices: `j ↦ 63 - j` (`bitcomp`). -/',
           'def bitcompIdx (j : ℕ) : ℕ := 63 - j',
           '']
    for c in certs:
        n, P = c['name'], c['P']
        out += [f'/-- `{n}`: the flow table (base `2 ^ {c["bg"]}`, scaled by `{c["D"]}`). -/',
                f'def {n}Flow : List ℕ := {lean_list(c["rows"])}',
                '',
                f'/-- `{n}`: the potentials (base `2 ^ {c["bp"]}`). -/',
                f'def {n}Phi : List ℕ := {lean_list(c["phi"])}',
                '',
                f'/-- `{n}`: the link lengths (base `2 ^ {c["bl"]}`). -/',
                f'def {n}Len : ℕ := {hex(c["len"])}',
                '',
                f'/-- `{n}`: the scale `D` of the flow table. -/',
                f'def {n}D : ℕ := {c["D"]}',
                '',
                f'/-- `{n}`: `D` times the rate of commodity `d` on port `i` of `j`. -/',
                f'def {n}G (d j i : ℕ) : ℕ := digit {c["bg"]} (getN {n}Flow d) ({P} * j + i)',
                '',
                f'/-- `{n}`: the potential of `j` towards `d`. -/',
                f'def {n}P (d j : ℕ) : ℕ := digit {c["bp"]} (getN {n}Phi d) j',
                '',
                f'/-- `{n}`: the length of port `i` of `j`. -/',
                f'def {n}L (j i : ℕ) : ℕ := digit {c["bl"]} {n}Len ({P} * j + i)',
                '']
    out += ['end GraphPatternData', '', 'end Fluid', '', 'end AsyncLean', '']
    with open(path, 'w') as f:
        f.write('\n'.join(out))


# (Lean name, graph, pattern, compute the any-routing pair, compute the minimal pair).
# When the two optima agree, one minimal flow and an any-routing dual suffice ('same').
PLAN = [
    ('torusTornado', TORUS, 'tornado', 'split'),
    ('torusShuffle', TORUS, 'shuffle', 'split'),
    ('torusTranspose', TORUS, 'transpose', 'split'),
    ('torusNeighbor', TORUS, 'neighbor', 'split'),
    ('torusBitrev', TORUS, 'bitrev', 'split'),
    ('torusBitcomp', TORUS, 'bitcomp', 'same'),
    ('cubeShuffle', CUBE, 'shuffle', 'split'),
    ('cubeTranspose', CUBE, 'transpose', 'same'),
    ('cubeBitrev', CUBE, 'bitrev', 'same'),
    ('cubeBitcomp', CUBE, 'bitcomp', 'same'),
    ('cubeTornado', CUBE, 'tornado', 'same'),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  '..', 'AsyncLean', 'Flow', 'GraphPatterns',
                                                  'Data.lean'))
    ap.add_argument('--only', default='')
    args = ap.parse_args()
    only = set(filter(None, args.only.split(',')))
    pats = demands()
    certs = []
    for name, g, p, kind in PLAN:
        if only and name not in only:
            continue
        dem = pats[p]
        if kind == 'same':
            c = certificate(name, g, dem, True, False)
            certs.append(c)
        else:
            a = certificate(name + 'Any', g, dem, False, False)
            m = certificate(name + 'Min', g, dem, True, True)
            assert m['theta'] < a['theta'], name
            certs += [a, m]
    for c in certs:
        print(f"{c['name']:<20} theta* = {str(c['theta']):<8} D = {c['D']}  bits {c['bg']}/"
              f"{c['bp']}/{c['bl']}")
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    emit(certs, args.out)
    print('wrote', os.path.normpath(args.out))


if __name__ == '__main__':
    main()
