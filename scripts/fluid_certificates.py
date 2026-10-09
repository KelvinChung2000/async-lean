#!/usr/bin/env python3
"""Exact fluid-model certificates for traffic patterns on the 8 x 8 mesh (generates the data of
`AsyncLean/Flow/MeshPatterns/Data.lean`, checked and proved sound in Lean by
`AsyncLean/Flow/Certificate.lean`; the theorems are in `AsyncLean/Flow/MeshPatterns.lean`).

The fluid model is the one of `scripts/routing_bounds.py` (`lp`): capacity 2 on every directed
mesh link, one commodity per destination, the largest theta such that theta * dem is routable,
over minimal paths only or over any paths.  For every certificate:

* the dual (upper bound): HiGHS's capacity duals give link lengths `len`; they are rounded to
  rationals and scaled to integers, the potentials `phi[d][v]` are the exact shortest distances
  from v to d under `len` (over the links that bring d closer, for the minimal-only bound), and
  theta* = 2 * sum(len) / sum(dem * phi) exactly.  Any nonnegative `len` gives a valid bound, so
  the rounding only has to be good enough to be tight.
* the primal (lower bound): a flow at theta = theta* (minimising the total flow), from HiGHS,
  rounded to rationals and verified EXACTLY (conservation, capacity, minimality).  The script
  stops if a check fails or the two bounds differ.

Results (theta per active source):
  transpose   10/11      (minimal = any; minimal flow, dual over any routing)
  shuffle     1          (minimal = any)
  bitrev      20/21      (minimal = any)
  hotspot     840/1471 minimal, 40/67 any (+4.5 %)

Index conventions (as in `routing_sim.py` and the Lean files): node s = x + 8 y; ports
0: s + 1 (east), 1: s - 1 (west), 2: s + 8 (north), 3: s - 8 (south).  Tables are packed per
commodity into one natural number, digit 4 j + i (base 2^b) = the rate of the commodity leaving
node j through port i, times D.

Usage: python3 scripts/fluid_certificates.py [--out AsyncLean/Flow/MeshPatterns/Data.lean]
Requires scipy (HiGHS).
"""
import argparse
import heapq
import os
import sys
from fractions import Fraction as Fr
from math import lcm

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from routing_bounds import matrix  # noqa: E402

K = 8
N = K * K
HOT = 4 + K * 4                      # (x, y) = (4, 4)


def port_target(j, i):
    """The node at the end of port i of node j, or None."""
    x, y = j % K, j // K
    if i == 0:
        return j + 1 if x + 1 < K else None
    if i == 1:
        return j - 1 if x > 0 else None
    if i == 2:
        return j + K if y + 1 < K else None
    return j - K if y > 0 else None


LINKS = [(j, i, port_target(j, i)) for j in range(N) for i in range(4)
         if port_target(j, i) is not None]


def dist(a, b):
    return abs(a % K - b % K) + abs(a // K - b // K)


def transpose(s):
    return s // K + K * (s % K)


def shuffle(s):
    return ((s << 1) | (s >> 5)) & 63


def bitrev(s):
    return sum(((s >> b) & 1) << (5 - b) for b in range(6))


def perm_demand(p):
    return [[Fr(1) if d == p(s) and d != s else Fr(0) for d in range(N)] for s in range(N)]


def hotspot_demand():
    return [[(Fr(4, 315) if s != d else Fr(0)) + (Fr(1, 5) if d == HOT and s != HOT else Fr(0))
             for d in range(N)] for s in range(N)]


def lp_vars(dem, minimal):
    act = [d for d in range(N) if any(dem[s][d] for s in range(N))]
    return [(d, l) for d in act for l, (u, _, v) in enumerate(LINKS)
            if u != d and (not minimal or dist(v, d) < dist(u, d))]


def lp_system(dem, var):
    rows, cols, vals, eq = [], [], [], {}
    for c, (d, l) in enumerate(var):
        u, _, v = LINKS[l]
        for node, sgn in ((u, 1), (v, -1)):
            if node != d:
                rows.append(eq.setdefault((d, node), len(eq)))
                cols.append(c)
                vals.append(sgn)
    a_ub = coo_matrix((np.ones(len(var)), ([l for _, l in var], list(range(len(var))))),
                      shape=(len(LINKS), len(var)))
    return rows, cols, vals, eq, a_ub


def lp_dual(dem, minimal):
    """Max theta (HiGHS); returns the float link lengths (capacity duals)."""
    var = lp_vars(dem, minimal)
    rows, cols, vals, eq, a_ub = lp_system(dem, var)
    nv = len(var) + 1
    for (d, node), r in eq.items():
        rows.append(r)
        cols.append(nv - 1)
        vals.append(-float(dem[node][d]))
    a_eq = coo_matrix((vals, (rows, cols)), shape=(len(eq), nv)).tocsr()
    a_ub = coo_matrix((a_ub.data, (a_ub.row, a_ub.col)), shape=(len(LINKS), nv)).tocsr()
    c = np.zeros(nv)
    c[-1] = -1
    res = linprog(c, A_ub=a_ub, b_ub=np.full(len(LINKS), 2.0), A_eq=a_eq,
                  b_eq=np.zeros(len(eq)), bounds=(0, None), method='highs-ds')
    assert res.status == 0, res.message
    return res.x[-1], -res.ineqlin.marginals


def exact_dual(dem, lens, minimal):
    """Integer lengths, exact potentials (shortest distances) and the exact bound."""
    fr = [max(Fr(x).limit_denominator(10 ** 4), Fr(0)) for x in lens]
    scale = lcm(*[x.denominator for x in fr])
    length = {(u, i): int(x * scale) for (u, i, _), x in zip(LINKS, fr)}
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
            for (u, i, w) in LINKS:
                if w == v and (not minimal or dist(w, d) < dist(u, d)):
                    nd = dv + length[(u, i)]
                    if nd < best.get(u, nd + 1):
                        best[u] = nd
                        heapq.heappush(pq, (nd, u))
        phi.append([best[v] for v in range(N)])
    return length, phi


def check_dual(dem, length, phi, minimal):
    """The checks of `dualCheck` and the bound of `boundCheck`, exactly; returns the bound."""
    for d in range(N):
        assert phi[d][d] == 0
        for (u, i, v) in LINKS:
            if not minimal or dist(v, d) < dist(u, d):
                assert phi[d][u] <= phi[d][v] + length[(u, i)]
    a = sum(dem[s][d] * phi[d][s] for s in range(N) for d in range(N))
    assert a > 0
    return 2 * sum(length.values()) / a


def lp_primal(dem, theta, minimal):
    """A flow at the exact theta (HiGHS, minimising the total flow), rounded to rationals."""
    var = lp_vars(dem, minimal)
    rows, cols, vals, eq, a_ub = lp_system(dem, var)
    b = np.zeros(len(eq))
    for (d, node), r in eq.items():
        b[r] = float(theta * dem[node][d])
    a_eq = coo_matrix((vals, (rows, cols)), shape=(len(eq), len(var))).tocsr()
    res = linprog(np.ones(len(var)), A_ub=a_ub.tocsr(), b_ub=np.full(len(LINKS), 2.0),
                  A_eq=a_eq, b_eq=b, bounds=(0, None), method='highs-ds')
    assert res.status == 0, res.message
    flow = {}
    for c, (d, l) in enumerate(var):
        x = Fr(res.x[c]).limit_denominator(10 ** 5)
        if x:
            u, i, _ = LINKS[l]
            flow[(d, u, i)] = x
    return flow


def check_primal(dem, flow, theta, minimal):
    """Conservation, capacity and minimality, exactly (the checks of `consCheck`, `capCheck`,
    `minCheck`)."""
    net = {}
    load = {}
    for (d, u, i), x in flow.items():
        v = port_target(u, i)
        assert x >= 0 and v is not None
        if minimal:
            assert dist(v, d) < dist(u, d)
        net[(d, u)] = net.get((d, u), 0) + x
        net[(d, v)] = net.get((d, v), 0) - x
        load[(u, i)] = load.get((u, i), 0) + x
    for d in range(N):
        for v in range(N):
            if v != d:
                assert net.get((d, v), 0) == theta * dem[v][d], (d, v)
    assert all(x <= 2 for x in load.values())


def pack(values, b):
    return sum(x << (b * j) for j, x in enumerate(values))


def width(values):
    return max(1, max(values).bit_length())


def lean_list(nums):
    return '[' + ',\n  '.join(hex(x) for x in nums) + ']'


def certificate(name, dem, minimal_flow, minimal_dual):
    """Compute and verify one certificate; returns its Lean data."""
    _, lens = lp_dual(dem, minimal_dual)
    length, phi = exact_dual(dem, lens, minimal_dual)
    theta = check_dual(dem, length, phi, minimal_dual)
    flow = lp_primal(dem, theta, minimal_flow)
    check_primal(dem, flow, theta, minimal_flow)
    scale = lcm(*[x.denominator for x in flow.values()])
    rows = []
    for d in range(N):
        rows.append([int(flow.get((d, j, i), 0) * scale) for j in range(N) for i in range(4)])
    bg = width([x for r in rows for x in r])
    lens_flat = [length.get((j, i), 0) for j in range(N) for i in range(4)]
    bp = width([x for r in phi for x in r])
    bl = width(lens_flat)
    print(f'{name:<12} theta = {theta} (flow {"minimal" if minimal_flow else "any"}, '
          f'dual {"minimal" if minimal_dual else "any"}): D = {scale}, '
          f'{len(flow)} flow entries', file=sys.stderr)
    return dict(name=name, theta=theta, D=scale, bg=bg, rows=[pack(r, bg) for r in rows],
                bp=bp, phi=[pack(r, bp) for r in phi], bl=bl, len=pack(lens_flat, bl))


def emit(certs, path):
    out = ['/-',
           'Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.',
           '-/',
           'import AsyncLean.Flow.Certificate',
           '',
           '/-!',
           '# Certificate data for the `8 × 8` mesh patterns',
           '',
           'Generated by `scripts/fluid_certificates.py` (do not edit).  For each certificate `c`:',
           '',
           '* `c.flow` : per commodity `d`, a natural number whose digit `4 j + i` in base `2 ^ c.bg`',
           '  is `D` times the rate of commodity `d` leaving vertex `j` through port `i`;',
           '* `c.phi` : per destination `d`, digit `j` in base `2 ^ c.bp` is the potential of `j`;',
           '* `c.len` : digit `4 j + i` in base `2 ^ c.bl` is the length of port `i` of vertex `j`;',
           '* `c.G`, `c.P`, `c.L` : the tables as functions of the indices, `c.D` : the scale.',
           '',
           'The certificates are checked and used in `AsyncLean.Flow.MeshPatterns`.',
           '-/',
           '',
           'namespace AsyncLean',
           '',
           'namespace Fluid',
           '',
           'namespace MeshPatternData',
           '']
    for c in certs:
        n = c['name']
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
                f'def {n}G (d j i : ℕ) : ℕ :=\n  MeshCert.digit {c["bg"]} (MeshCert.getN {n}Flow d) (4 * j + i)',
                '',
                f'/-- `{n}`: the potential of `j` towards `d`. -/',
                f'def {n}P (d j : ℕ) : ℕ :=\n  MeshCert.digit {c["bp"]} (MeshCert.getN {n}Phi d) j',
                '',
                f'/-- `{n}`: the length of port `i` of `j`. -/',
                f'def {n}L (j i : ℕ) : ℕ :=\n  MeshCert.digit {c["bl"]} {n}Len (4 * j + i)',
                '']
    out += ['end MeshPatternData', '', 'end Fluid', '', 'end AsyncLean', '']
    with open(path, 'w') as f:
        f.write('\n'.join(out))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  '..', 'AsyncLean', 'Flow', 'MeshPatterns',
                                                  'Data.lean'))
    out = ap.parse_args().out
    pats = {'transpose': perm_demand(transpose), 'shuffle': perm_demand(shuffle),
            'bitrev': perm_demand(bitrev), 'hotspot': hotspot_demand()}
    for p, dem in pats.items():           # the demands agree with routing_bounds.matrix
        lam = matrix(K, p)
        assert all(abs(float(dem[s][d]) - lam[s][d]) < 1e-12 for s in range(N) for d in range(N))
    certs = [certificate('transpose', pats['transpose'], True, False),
             certificate('shuffle', pats['shuffle'], True, False),
             certificate('bitrev', pats['bitrev'], True, False),
             certificate('hotspotAny', pats['hotspot'], False, False),
             certificate('hotspotMin', pats['hotspot'], True, True)]
    for c in certs:
        print(f"{c['name']:<12} theta* = {c['theta']}  D = {c['D']}  bits {c['bg']}/{c['bp']}/"
              f"{c['bl']}")
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    emit(certs, out)
    print('wrote', os.path.normpath(out))


if __name__ == '__main__':
    main()
