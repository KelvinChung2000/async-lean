#!/usr/bin/env python3
"""The packet-level throughput ceiling of the simulators' packet model (an experiment; only the
statements marked "proved" in `AsyncLean/Packet/` are theorems).

The packet model of `routing_sim.py`, `routing_graph_sim.py`, `torus_experiments.py` and
`flow_control_experiments.py`: every lane (virtual channel) is a FIFO buffer of depth N (N = 1 in
all of them except `flow_control_experiments.py`); every cycle, arrived packets are ejected (one
per lane), then the head of every non-empty lane tries ONE hop, the lanes taking turns in a
uniformly random order (a lane freed earlier in the cycle can be refilled), then sources inject.
On a chain of lanes (no branching) this is the totally asymmetric exclusion process with site
capacity N (K-exclusion, Seppalainen 1999) under the *random shuffle* update (Woelki,
Schadschneider & Schreckenberg 2006).  A site i moves its head iff it is non-empty and either its
successor had room at the start of the cycle or the successor is full, moved earlier in the
cycle and so made room:

    m_i = a_i and (b_i or (c_i and m_{i+1})),  a_i = n_i > 0, b_i = n_{i+1} < N,
                                               c_i = (i+1 takes its turn before i)

(the random order enters only through c), a boolean affine recurrence solved for a whole batch
of rings by pointer doubling (numpy).  The other update rules: parallel (c = 0), ordered
backward (downstream first: c = 1 on a chain), random sequential (continuous time, rate 1 per
site: the time unit is one attempt per site, as in one cycle).

Findings (simulation unless marked proved):

* Maximal current J(N) per lane and cycle (exact small rings agree; L = 200 rings, open chains
  with alpha = beta = 1 of length 128):
      N               1      2      4      8
      shuffle        1/2    1      1      1     (ring: proved <= 1/2 for N = 1 from every
      parallel       1/2    1      1      1      configuration, `Packet.Ring.half_bound`; N >= 2:
      ordered bwd    1/2*   1      1      1      every lane moves every cycle once each lane holds
      random seq.   0.25   0.42   0.60   0.76    1..N-1 packets, `Packet.Ring.all_move`)
  (* ring with one seam; an open chain under ordered-backward update carries 1.)  Open chains of
  one-packet lanes, alpha = beta = 1: 1 (L = 2), 2/3 (L = 3), 0.566 (4), 0.523 (6), 0.512 (8),
  0.503 (16), 0.500 (64): the README's 0.50 to 0.57.  With N >= 2 every length carries 1.
* Phase diagram (N = 1, L = 100, eject with prob. beta at the start of a cycle, inject with prob.
  alpha at its end): low density J ~ rho ~ alpha - (0.413 at alpha = 0.5), high density set by
  beta (0.422 at beta = 0.5, density 0.69), maximal current 1/2 at bulk occupancy 1/2 reached
  only near alpha, beta >= 0.8 to 0.9 (0.497 at 0.8, 0.500 at 0.9).  Above occupancy 1/2 the
  current falls (0.69 -> 0.42, 0.81 -> 0.28): a throttle should hold lanes about half full (the
  `g = 4` of 8 free channels of `tieredMesh`).  N = 2: J = alpha up to 1.
* Networks (tiered selection, g = 4; mesh: XY escape; torus: tree escape, B = 2; peak over
  offered 0.5 / 0.7 / 1.0), against the fluid optimum per node (theta times the fraction of
  nodes that send) and its half:
      mesh   uniform transpose shuffle bitrev hotspot bitcomp   torus  uniform transp shuffle bitrev bitcomp tornado
      fluid    0.984  0.795   0.969  0.833   0.595  0.500       (*)   1.000  1.000  1.000  1.000  1.000  1.000
      half     0.492  0.398   0.484  0.417   0.298  0.250              0.984  0.795  0.775  0.833  0.500  0.533
      N = 1    0.495  0.380   0.601  0.360   0.380  0.248              0.753  0.570  0.650  0.660  0.444  0.359
      N = 2    0.752  0.566   0.760  0.534   0.449  0.355              0.992  0.786  0.828  0.870  0.617  0.539
      N = 4    0.838  0.593   0.779  0.583   0.452  0.342              1.000  0.807  0.856  0.875  0.632  0.572
      N = 8    0.880  0.594   0.786  0.591   0.457  0.323              1.000  0.808  0.860  0.875  0.627  0.584
  (* capped by the injection limit of 1 packet per node and cycle.)  With N = 1 the busiest
  lanes carry 0.6 to 0.75 (up to 0.99 next to the hotspot): the half estimate is not a ceiling
  (mesh shuffle, hotspot exceed it; the README's best mesh schemes exceed it by 3 to 30 % on
  uniform, transpose, shuffle, hotspot, bit complement).  With N >= 2 the busiest lanes run at
  1.00: what remains is the load balance of the routing, not exclusion.

Subcommands (each runs in one process; keep runs short):

  exact   [--L 6] [--N 1,2,3]   exact stationary currents of small rings (Fraction arithmetic),
                                all update rules, maximised over the number of packets
  ring    [--Ns 1,...,8]        long rings (L = 400), density sweep: J(N) per update rule
  chain                         open chains, alpha = beta = 1 (the network's sources and sinks):
                                current against length L
  phase   [--N 1]               open-chain phase diagram (injection alpha, ejection beta)
  network [--N 1,2,4,8]         8 x 8 mesh / torus with depth-N lanes against the scaled fluid
                                optimum J(N) * theta_fluid
"""
import argparse
import itertools
import math
import random
import sys
from collections import deque
from fractions import Fraction as Fr

import numpy as np

# ------------------------------------------------------------------------------------------
# exact rings


def ring_states(L, N, M):
    """All occupation vectors of a ring of L sites of capacity N with M packets."""
    out = []

    def rec(i, left, acc):
        if i == L - 1:
            if left <= N:
                out.append(tuple(acc + [left]))
            return
        for x in range(min(N, left) + 1):
            rec(i + 1, left - x, acc + [x])
    rec(0, M, [])
    return out


def cyclic_patterns(L):
    """Distribution of c (c_i = site i+1 mod L takes its turn before site i) under a uniformly
    random order of the L sites: {c: Fraction}."""
    cnt = {}
    for perm in itertools.permutations(range(L)):
        c = tuple(perm[(i + 1) % L] < perm[i] for i in range(L))
        cnt[c] = cnt.get(c, 0) + 1
    tot = math.factorial(L)
    return {c: Fr(v, tot) for c, v in cnt.items()}


def moves(n, N, c, ring=True):
    """Which sites move (shuffle recurrence with the given c), as a tuple of booleans."""
    L = len(n)
    a = [x > 0 for x in n]
    b = [n[(i + 1) % L] < N if (ring or i < L - 1) else False for i in range(L)]
    m = [False] * L
    for _ in range(L + 1):             # least fixed point; unique since not every c_i holds
        m = [a[i] and (b[i] or (c[i] and m[(i + 1) % L] if (ring or i < L - 1) else False))
             for i in range(L)]
    return m


def apply(n, m):
    L = len(n)
    return tuple(n[i] - m[i] + m[(i - 1) % L] for i in range(L))


def transition(n, N, rule, pats):
    """Distribution of the next state and of the number of moves: {(state', moves): prob}."""
    L = len(n)
    if rule == 'parallel':
        cs = {tuple([False] * L): Fr(1)}
    elif rule == 'backward':           # site L-1 first, then L-2, ..., 0
        cs = {tuple([True] * (L - 1) + [False]): Fr(1)}
    else:
        cs = pats
    out = {}
    for c, p in cs.items():
        m = moves(n, N, c)
        key = (apply(n, m), sum(m))
        out[key] = out.get(key, 0) + p
    return out


def solve_stationary(states, rows):
    """pi P = pi, sum pi = 1, exact.  rows[s] = {t: P(s, t)} (or generator rates if `gen`)."""
    idx = {s: i for i, s in enumerate(states)}
    n = len(states)
    # equations: for each t: sum_s pi_s (P_st - [s = t]) = 0; replace the last by sum pi = 1
    A = [[Fr(0)] * (n + 1) for _ in range(n)]
    for s, row in rows.items():
        for t, p in row.items():
            A[idx[t]][idx[s]] += p
        A[idx[s]][idx[s]] -= 1
    A.append([Fr(1)] * n + [Fr(1)])
    # Gaussian elimination, pivots from every remaining row (the n + 1 equations have rank n
    # exactly when the stationary distribution is unique)
    rows_left = list(range(n + 1))
    piv_of = {}
    for col in range(n):
        piv = next((r for r in rows_left if A[r][col] != 0), None)
        if piv is None:
            raise ValueError('stationary distribution not unique')
        rows_left.remove(piv)
        inv = 1 / A[piv][col]
        A[piv] = [x * inv for x in A[piv]]
        for r in range(n + 1):
            if r != piv and A[r][col] != 0:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[piv])]
        piv_of[col] = piv
    assert all(A[r][n] == 0 for r in rows_left)
    return {s: A[piv_of[idx[s]]][n] for s in states}


def canon(s):
    return min(s[i:] + s[:i] for i in range(len(s)))


def exact_current(L, N, M, rule, pats=None):
    """Stationary current per bond of a ring (L sites, capacity N, M packets), exact."""
    states = ring_states(L, N, M)
    if rule == 'rsu':                  # continuous time: generator, every movable site rate 1
        lump = sorted(set(canon(s) for s in states))
        rows = {}
        for s in lump:
            row = {}
            for i in range(L):
                if s[i] > 0 and s[(i + 1) % L] < N:
                    m = [False] * L
                    m[i] = True
                    t = canon(apply(s, m))
                    row[t] = row.get(t, 0) + Fr(1)
            tot = sum(row.values())
            # uniformise with rate L: P = I + Q / L
            row = {t: v / L for t, v in row.items()}
            row[s] = row.get(s, 0) + 1 - tot / L
            rows[s] = row
        pi = solve_stationary(lump, rows)
        flux = {s: Fr(sum(1 for i in range(L) if s[i] > 0 and s[(i + 1) % L] < N)) for s in lump}
        return sum(pi[s] * flux[s] for s in lump) / L
    if rule in ('backward', 'parallel'):
        # deterministic: follow every initial state to its cycle; the long-run current is the
        # mean number of moves on the cycle (reported: the smallest and the largest over the
        # initial states, equal when every state reaches the same current)
        js = set()
        for s0 in states:
            seen, s, path = {}, s0, []
            while s not in seen:
                seen[s] = len(path)
                ((t, k), _), = transition(s, N, rule, pats).items()
                path.append(k)
                s = t
            cyc = path[seen[s]:]
            js.add(Fr(sum(cyc), len(cyc) * L))
        return min(js) if min(js) == max(js) else (min(js), max(js))
    lump, key = sorted(set(canon(s) for s in states)), canon
    rows, flux = {}, {}
    for s in lump:
        tr = transition(s, N, rule, pats)
        row = {}
        f = Fr(0)
        for (t, k), p in tr.items():
            row[key(t)] = row.get(key(t), 0) + p
            f += p * k
        rows[s], flux[s] = row, f
    js = set()
    for cls in recurrent_classes(lump, rows):
        pi = solve_stationary(cls, {s: rows[s] for s in cls})
        js.add(sum(pi[s] * flux[s] for s in cls) / L)
    return min(js) if len(js) == 1 else (min(js), max(js))


def recurrent_classes(states, rows):
    """The closed communicating classes of a finite chain (each carries one stationary
    distribution; the current from any initial state is a mixture of theirs)."""
    reach = {}
    for s in states:
        seen, todo = {s}, [s]
        while todo:
            u = todo.pop()
            for t, p in rows[u].items():
                if p and t not in seen:
                    seen.add(t)
                    todo.append(t)
        reach[s] = seen
    out, done = [], set()
    for s in states:
        if s in done:
            continue
        if all(s in reach[t] for t in reach[s]):        # s recurrent
            cls = sorted(reach[s])
            out.append(cls)
            done |= set(cls)
    return out


def cmd_exact(args):
    for L in [int(x) for x in args.L.split(',')]:
        pats = cyclic_patterns(L)
        for N in [int(x) for x in args.N.split(',')]:
            print(f'== ring L = {L}, capacity N = {N}: J(M) per bond and cycle (exact)', flush=True)
            print(f'{"M":>4} ' + ''.join(f'{r:>26}' for r in ('shuffle', 'parallel', 'backward', 'rsu')))
            best = {}
            for M in range(1, L * N):
                cells = []
                for r in ('shuffle', 'parallel', 'backward', 'rsu'):
                    j = exact_current(L, N, M, r, pats)
                    if isinstance(j, tuple):
                        best[r] = max(best.get(r, (Fr(0), 0)), (j[1], M))
                        cells.append(f'{j[0]}..{j[1]}')
                        continue
                    best[r] = max(best.get(r, (Fr(0), 0)), (j, M))
                    cells.append(f'{str(j)[:16]} = {float(j):.4f}')
                print(f'{M:>4} ' + ''.join(f'{c:>26}' for c in cells), flush=True)
            print('max: ' + ', '.join(f'{r} {float(j):.4f} at M = {M} ({j})' if len(str(j)) < 40
                                      else f'{r} {float(j):.4f} at M = {M}'
                                      for r, (j, M) in best.items()), flush=True)


# ------------------------------------------------------------------------------------------
# long rings and chains, batched (numpy)


def shift_up(x, s, ring):
    """y_i = x_{i+s} (wrapping on a ring, zero past the end of a chain)."""
    if ring:
        return np.roll(x, -s, axis=1)
    y = np.zeros_like(x)
    if s < x.shape[1]:
        y[:, :x.shape[1] - s] = x[:, s:]
    return y


def solve_moves(a, b, c, ring):
    """m_i = a_i & (b_i | (c_i & m_{i+1})) by pointer doubling (m_{L} = 0 on a chain)."""
    P = a & b
    Q = a & c
    s = 1
    L = a.shape[1]
    while s < L:
        P = P | (Q & shift_up(P, s, ring))
        Q = Q & shift_up(Q, s, ring)
        s *= 2
    return P


def step(n, N, rule, rng, ring=True):
    """One cycle of the move phase on a batch of rings or chains (n: B x L ints, in place);
    returns m.  On a chain the last site does not move (its packets leave by ejection)."""
    B, L = n.shape
    a = n > 0
    b = shift_up(n, 1, True) < N
    if not ring:
        a[:, L - 1] = False
    if rule == 'parallel':
        m = a & b
    elif rule == 'backward':
        c = np.ones_like(a)
        if ring:
            c[:, L - 1] = False
        m = solve_moves(a, b, c, ring)
    elif rule == 'shuffle':
        sig = rng.random((B, L))
        c = shift_up(sig, 1, True) < sig
        m = solve_moves(a, b, c, ring)
    elif rule == 'rsu':
        m = rsu_sweep(n, N, rng, ring)
        return m
    mi = m.astype(n.dtype)
    n -= mi
    if ring:
        n += np.roll(mi, 1, axis=1)
    else:
        n[:, 1:] += mi[:, :-1]
    return m


def rsu_sweep(n, N, rng, ring):
    """Random sequential update, one time unit = L independent single-site attempts per ring
    (sites chosen with replacement; continuous time in the limit).  Vectorised over the batch:
    the attempt t picks one site per ring."""
    B, L = n.shape
    cnt = np.zeros((B, L), dtype=np.int64)
    rows = np.arange(B)
    for _ in range(L):
        i = rng.integers(0, L, B)
        j = (i + 1) % L
        ok = (n[rows, i] > 0) & (n[rows, j] < N)
        if not ring:
            ok &= i < L - 1
        n[rows[ok], i[ok]] -= 1
        n[rows[ok], j[ok]] += 1
        cnt[rows[ok], i[ok]] += 1
    return cnt


def ring_current(L, N, M, rule, B=16, cycles=3000, warm=600, seed=1):
    rng = np.random.default_rng(seed)
    n = np.zeros((B, L), dtype=np.int64)
    for r in range(B):                 # M packets placed at random
        pos = rng.choice(L * N, M, replace=False) // N
        np.add.at(n[r], pos, 1)
    tot = 0
    per = []
    for t in range(cycles):
        m = step(n, N, rule, rng)
        if t >= warm:
            per.append(m.sum() / (B * L))
    per = np.array(per)
    k = len(per) // 10
    blocks = per[:k * 10].reshape(10, k).mean(axis=1)
    return per.mean(), blocks.std(ddof=1) / math.sqrt(10)


def cmd_ring(args):
    L = args.ringL
    print(f'== long ring, L = {L} lanes: maximal current J(N) over the density (per cycle)')
    rules = args.rules.split(',')
    for N in [int(x) for x in args.Ns.split(',')]:
        cells = []
        for rule in rules:
            # coarse sweep, then refine around the best density
            cyc = 1500 if rule != 'rsu' else 300
            B = 16 if rule != 'rsu' else 8
            Lr = L if rule != 'rsu' else 200
            grid = [0.1 * i for i in range(2, 9)]
            res = {r: ring_current(Lr, N, int(r * Lr * N), rule, B, cyc, cyc // 5)[0] for r in grid}
            r0 = max(res, key=res.get)
            for r in (r0 - 0.06, r0 - 0.03, r0 + 0.03, r0 + 0.06):
                if 0 < r < 1:
                    res[r] = ring_current(Lr, N, int(r * Lr * N), rule, B, cyc, cyc // 5)[0]
            r0 = max(res, key=res.get)
            j, se = ring_current(Lr, N, int(r0 * Lr * N), rule, B, 2 * cyc, cyc // 2, seed=7)
            cells.append(f'{j:.4f}±{se:.4f} @{r0:.2f}')
        print(f'N = {N}: ' + '   '.join(f'{r} {c}' for r, c in zip(rules, cells)), flush=True)


# ------------------------------------------------------------------------------------------
# open chains


def chain_run(L, N, alpha, beta, rule='shuffle', B=32, cycles=3000, warm=1000, seed=1):
    """Open chain of L lanes: every cycle the last lane ejects its head with probability beta,
    the lanes move (the last one only by ejection), then a packet is injected into lane 0 with
    probability alpha if it has room (the network's order: eject, move, inject).  Returns the
    current (ejections per cycle) and the density profile (mean occupancy / N)."""
    rng = np.random.default_rng(seed)
    n = np.zeros((B, L), dtype=np.int64)
    out = 0
    prof = np.zeros(L)
    for t in range(cycles):
        ej = (n[:, L - 1] > 0) & (rng.random(B) < beta)
        n[:, L - 1] -= ej
        step(n, N, rule, rng, ring=False)
        inj = (n[:, 0] < N) & (rng.random(B) < alpha)
        n[:, 0] += inj
        if t >= warm:
            out += ej.sum()
            prof += n.mean(axis=0)
    T = cycles - warm
    return out / (B * T), prof / (T * N)


def cmd_chain(args):
    print('== open chain, alpha = beta = 1 (source always ready, destination ejects every cycle):'
          ' current per cycle against the number of lanes L')
    Ls = [2, 3, 4, 6, 8, 12, 16, 32, 64, 128]
    for N in [int(x) for x in args.Ns.split(',')]:
        cells = []
        for L in Ls:
            j, _ = chain_run(L, N, 1.0, 1.0, 'shuffle', B=32, cycles=2500, warm=800)
            cells.append(f'{j:.3f}')
        print(f'N = {N}: ' + ' '.join(f'L={L}:{c}' for L, c in zip(Ls, cells)), flush=True)


def cmd_phase(args):
    N = args.N1
    L = 100
    print(f'== open chain, N = {N}, L = {L}, shuffle update: current (bulk density) over alpha, beta')
    grid = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
    print('beta\\alpha ' + ''.join(f'{a:>13}' for a in grid))
    for beta in grid:
        cells = []
        for alpha in grid:
            j, prof = chain_run(L, N, alpha, beta, 'shuffle', B=16, cycles=1500, warm=600)
            cells.append(f'{j:.3f}({prof[L // 3:2 * L // 3].mean():.2f})')
        print(f'{beta:>10} ' + ''.join(f'{c:>13}' for c in cells), flush=True)


def cmd_phase1d(args):
    """beta = 1, fine alpha sweep: where the max-current phase starts."""
    L = 100
    for N in [int(x) for x in args.Ns.split(',')]:
        rows = []
        for alpha in [0.2, 0.3, 0.4, 0.45, 0.5, 0.55, 0.6, 0.65, 0.7, 0.8, 0.9, 1.0]:
            j, prof = chain_run(L, N, alpha, 1.0, 'shuffle', B=16, cycles=2000, warm=800)
            rows.append(f'a={alpha}:{j:.3f}/{prof[L // 3:2 * L // 3].mean():.2f}')
        print(f'N = {N} (beta = 1, current/bulk density): ' + ' '.join(rows), flush=True)



# ------------------------------------------------------------------------------------------
# networks with depth-N lanes

FLUID = {   # exact fluid optima (proved: Flow/MeshWire, MeshPatterns, MeshWorst, Symmetric,
            # GraphPatterns), link capacity 2 = two lanes of capacity 1, 8 x 8
    'mesh': {'uniform': Fr(63, 64), 'transpose': Fr(10, 11), 'shuffle': Fr(1),
             'bitrev': Fr(20, 21), 'hotspot': Fr(40, 67), 'bitcomp': Fr(1, 2)},
    'torus': {'uniform': Fr(63, 32), 'transpose': Fr(20, 11), 'shuffle': Fr(8, 5),
              'bitrev': Fr(40, 21), 'bitcomp': Fr(1), 'tornado': Fr(16, 15)},
}


def net_sim(net, N, rate, pattern, g=4, budget=2, cycles=3000, warmup=1000, seed=1, k=8,
            stats=False):
    """`routing_graph_sim.simulate` (tiered selection, source throttle g, return budget B) with
    lanes of depth N: every network lane is a FIFO of N packets (the injection channel keeps
    one); a lane ejects at most its head per cycle; every other lane non-empty at the start of
    the move phase moves at most its head (so a lane passes at most one packet per cycle), in a random order, into a permitted lane with room;
    'free' in the throttle means 'has room'.  N = 1 is `routing_graph_sim.simulate`."""
    from routing_graph_sim import RANDPERM
    from routing_sim import destination
    head, esc, vc1, out = net.head, net.esc, net.vc1, net.out
    n = net.n
    rnd = random.Random(seed)
    lanes = {}                                   # channel -> deque of packets
    cap = lambda c: 1 if c // 2 % 5 == 4 else N
    room = lambda c: len(lanes.get(c, ())) < cap(c)
    queues = [deque() for _ in range(n)]
    done = 0
    thr = [g * 2 * net.deg[v] / 8 for v in range(n)]
    dep = {}
    for t in range(cycles):
        ejected = [c for c, q in lanes.items() if q and head[c] == q[0][0]]
        for c in ejected:
            lanes[c].popleft()
            if t >= warmup:
                done += 1
                dep[c] = dep.get(c, 0) + 1
        ejected = set(ejected)                   # a lane passes at most one packet per cycle
        movers = [c for c, q in lanes.items() if q and c not in ejected]
        rnd.shuffle(movers)
        for c in movers:
            q = lanes[c]
            if not q:
                continue
            pk = q[0]
            d = pk[0]
            u = head[c]
            if u == d:
                continue
            e = esc[c][d]
            src = c // 2 % 5 == 4
            if budget is not None and c % 2 == 0 and not src and pk[2] >= budget:
                hops = [e]
            else:
                hops = [e] + vc1[u][d]
            free = [x for x in hops if room(x)]
            if g and src and free:
                free = [x for x in free if sum(1 for o in out[head[x]] if room(o)) >= thr[head[x]]]
            if free:
                f1 = [x for x in free if x % 2 == 1]
                free = f1 if f1 else free
                x = rnd.choice(free)
                if c % 2 == 0 and not src and x % 2 == 1:
                    pk[2] += 1
                q.popleft()
                lanes.setdefault(x, deque()).append(pk)
                if t >= warmup:
                    dep[c] = dep.get(c, 0) + 1
        for s in range(n):
            if rnd.random() < rate:
                d = RANDPERM[s] if pattern == 'randperm' else (
                    (s % k + k // 2 - 1) % k + s // k * k if pattern == 'tornado' else
                    destination(pattern, s, k, rnd))
                if d != s:
                    queues[s].append(d)
            c = s * 10 + 8
            if queues[s] and room(c):
                lanes.setdefault(c, deque()).append([queues[s].popleft(), t, 0])
    T = cycles - warmup
    thru = done / (T * n)
    if not stats:
        return thru
    rates = sorted((v / T for c, v in dep.items() if c // 2 % 5 != 4), reverse=True)
    top = rates[:max(1, len(rates) // 10)]
    return thru, rates[0], sum(top) / len(top)


def cmd_network(args):
    import routing_graph_sim as G
    nets = {'mesh': lambda: G.Net(G.mesh_adj(8), escape='xy', k=8),
            'torus': lambda: G.Net(G.torus_adj(8), root=27)}
    rates = [float(r) for r in args.rates.split(',')] if args.rates else [0.5, 0.7, 1.0]
    for name in args.net.split(','):
        net = nets[name]()
        print(f'== 8 x 8 {name} ({"XY escape" if name == "mesh" else "spanning-tree escape, B = 2"},'
              f' tiered, g = 4): peak accepted throughput over offered {rates} '
              f'[max lane rate / mean of the busiest 10 % of lanes]', flush=True)
        for pat in args.patterns.split(','):
            fl = FLUID[name].get(pat)
            cells = []
            for N in [int(x) for x in args.N.split(',')]:
                best = max((net_sim(net, N, r, pat, cycles=args.cycles, warmup=args.cycles // 3,
                                    stats=True) for r in rates), key=lambda x: x[0])
                cells.append(f'N={N}: {best[0]:.3f} [{best[1]:.2f}/{best[2]:.2f}]')
            est = (f'fluid {float(fl):.3f}, J(1)*fluid {float(fl) / 2:.3f}, '
                   f'min(1, fluid) {min(1, float(fl)):.3f}' if fl else '')
            print(f'{pat:<10} ' + '  '.join(cells) + f'   ({est})', flush=True)

# ------------------------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd')
    ap.add_argument('--L', default='4,5,6')
    ap.add_argument('--N', default='1,2')
    ap.add_argument('--Ns', default='1,2,3,4,5,6,7,8')
    ap.add_argument('--rules', default='shuffle,parallel,backward,rsu')
    ap.add_argument('--ringL', type=int, default=400)
    ap.add_argument('--N1', type=int, default=1)
    ap.add_argument('--net', default='mesh,torus')
    ap.add_argument('--patterns', default='uniform,transpose,bitcomp')
    ap.add_argument('--rates', default='')
    ap.add_argument('--cycles', type=int, default=3000)
    args = ap.parse_args()
    {'exact': cmd_exact, 'ring': cmd_ring, 'chain': cmd_chain, 'phase': cmd_phase,
     'phase1d': cmd_phase1d,
     'network': lambda a: cmd_network(a)}[args.cmd](args)


if __name__ == '__main__':
    main()
