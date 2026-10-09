#!/usr/bin/env python3
"""Throughput bounds for routing on the k x k mesh (fluid model).

The 8 x 8 optima and the worst-case bounds below are proved in Lean (`Flow/MeshPatterns.lean`,
`Flow/MeshWorst.lean`, `Flow/MeshOdd.lean`); this script computes them numerically.

Every directed link carries at most 2 packets per cycle (two virtual channels, one packet each).

* `lp(k, lam, minimal)` : the largest per-node rate theta such that the traffic matrix theta * lam
  can be routed (maximum concurrent multicommodity flow, one commodity per destination), over
  shortest paths only (`minimal`) or over any paths (detours allowed).
* `worst(fracs)` : the worst-case load of an oblivious routing over all permutations
  (Towles & Dally): for every link, the maximum-weight matching of source-destination pairs by
  the fraction of their traffic on that link.

Usage: python3 scripts/routing_bounds.py [--k 8]

Findings (8 x 8): detours raise the optimum by 0 % on uniform, transpose, shuffle, bit-reversal
and bit-complement traffic and by 4.5 % on hotspot traffic -- the binding cuts (bisection,
diagonal, the hotspot's links) cannot be bypassed.  Over all permutations, XY routing has a
worst case of 2 / (k - 1) and O1TURN of 4 / k, the bisection bound that no routing exceeds.
Requires scipy.
"""
import argparse
import random
import numpy as np
from scipy.optimize import linear_sum_assignment, linprog
from scipy.sparse import coo_matrix
from routing_sim import PATTERNS, destination


def matrix(k, pattern):
    n = k * k
    lam = np.zeros((n, n))
    if pattern == 'uniform':
        lam[:] = 1 / (n - 1)
        np.fill_diagonal(lam, 0)
    elif pattern == 'hotspot':
        h = (k // 2) * k + k // 2
        lam[:] = 0.8 / (n - 1)
        np.fill_diagonal(lam, 0)
        for s in range(n):
            if s != h:
                lam[s, h] += 0.2
    else:
        rnd = random.Random(0)
        for s in range(n):
            d = destination(pattern, s, k, rnd)
            if d != s:
                lam[s, d] = 1
    return lam


def links_of(k):
    n = k * k
    return [(u, v) for u in range(n) for v in (u + 1, u - 1, u + k, u - k)
            if 0 <= v < n and abs(u % k - v % k) + abs(u // k - v // k) == 1]


def lp(k, lam, minimal):
    n = k * k
    dist = lambda a, b: abs(a % k - b % k) + abs(a // k - b // k)
    links = links_of(k)
    var = [(d, i) for d in range(n) if lam[:, d].sum() > 0 for i, (u, v) in enumerate(links)
           if u != d and (not minimal or dist(v, d) < dist(u, d))]
    nv = len(var) + 1                        # the last variable is theta
    rows, cols, vals, eq = [], [], [], {}
    for j, (d, i) in enumerate(var):
        u, v = links[i]
        for node, sgn in ((u, 1), (v, -1)):
            if node != d:
                rows.append(eq.setdefault((d, node), len(eq)))
                cols.append(j)
                vals.append(sgn)
    for (d, node), r in eq.items():
        rows.append(r)
        cols.append(nv - 1)
        vals.append(-lam[node, d])
    a_eq = coo_matrix((vals, (rows, cols)), shape=(len(eq), nv)).tocsr()
    a_ub = coo_matrix((np.ones(len(var)), ([i for _, i in var], list(range(len(var))))),
                      shape=(len(links), nv)).tocsr()
    c = np.zeros(nv)
    c[-1] = -1
    res = linprog(c, A_ub=a_ub, b_ub=np.full(len(links), 2.0), A_eq=a_eq, b_eq=np.zeros(len(eq)),
                  bounds=(0, None), method='highs')
    return res.x[-1]


def dor_path(k, s, d, order):
    path, u = [], s
    for dim in order:
        while (u % k if dim == 'x' else u // k) != (d % k if dim == 'x' else d // k):
            if dim == 'x':
                v = u + 1 if u % k < d % k else u - 1
            else:
                v = u + k if u // k < d // k else u - k
            path.append((u, v))
            u = v
    return path


def worst(k, fracs):
    n = k * k
    load = {}
    for (s, d), fl in fracs.items():
        for e, w in fl.items():
            load.setdefault(e, np.zeros((n, n)))[s, d] += w
    best = 0
    for m in load.values():
        r, c = linear_sum_assignment(m, maximize=True)
        best = max(best, m[r, c].sum())
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--k', type=int, default=8)
    k = ap.parse_args().k
    print(f'== {k} x {k} mesh: optimal per-node rate (active nodes), shortest paths vs any paths')
    for p in PATTERNS:
        lam = matrix(k, p)
        a, b = lp(k, lam, True), lp(k, lam, False)
        print(f'{p:<10} minimal {a:.3f}  any {b:.3f}  detour gain {b / a - 1:+.1%}')
    n = k * k
    pairs = [(s, d) for s in range(n) for d in range(n) if s != d]
    xy = {p: {e: 1.0 for e in dor_path(k, *p, 'xy')} for p in pairs}
    o1 = {}
    for p in pairs:
        fl = {}
        for order in ('xy', 'yx'):
            for e in dor_path(k, *p, order):
                fl[e] = fl.get(e, 0) + 0.5
        o1[p] = fl
    print(f'== worst case over all permutations (bisection bound for any routing: {4 / k:.3f})')
    for name, f in (('XY', xy), ('O1TURN', o1)):
        print(f'{name:<7} {2 / worst(k, f):.3f}')


if __name__ == '__main__':
    main()
