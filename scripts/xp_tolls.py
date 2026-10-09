#!/usr/bin/env python3
"""Selfish versus system-optimal source route choice on the 8 x 8 torus (and mesh), and
marginal-cost tolls (simulation and fluid model; nothing here is proved -- the safety of every
choice among the listed detour options is `Routing/GraphDetour.lean`).

Route options of a packet s -> d at its source (as in `torus_experiments.py`'s `bandit*`):
0 minimal, 1 / 2 the long way round the x / y ring (via an intermediate), 3 a uniformly
random intermediate (Valiant).  Inside an option the route is minimal (adaptive).

  fluid  <pattern,...>     Wardrop (selfish) versus system-optimal splits in the fluid model with
                           M/M/1 link latencies l(x) = 1 / (1 - x / c), c = 2 (Frank-Wolfe), and
                           the option-restricted max-throughput LP with its capacity duals.
  sim    <scheme,...> <pattern,...> <rates> <seeds>
                           packet simulation (one process, sequential), mean +- s.e. of the peak.

Packet schemes (all are `bandit` sources: 2 % exploration, flow gate f = 0.5 on the long way,
the random intermediate only for concentrated sources (k), as `bandit2m7f5k`) differ in the
PRICE each option is ranked by (L = smoothed in-network latency of the option, h = its hops):
  sel        L                                (selfish; `bandit2f5k`)
  m<r>       L^2 / h^(r/10)                   (`bandit2m<r>f5k`; r = 10 is the M/M/1 Pigou toll)
  sq         sum over the hops of l_hop^2      (per-hop M/M/1 Pigou toll, carried by the packet)
  tel<k>     L + k/10 * sum_e rho_e/(1-rho_e)^2 (latency + Pigou toll x l'(x) per link, the link
                                               utilisation rho_e measured from flow counts and
                                               carried by the packet, c_eff = 1.5 packets/cycle, rho <= 0.9)
  dual<t>    L + t * sum_e len_e               (oracle: the LP capacity duals of the pattern,
                                               mean 1 per link, summed by the packet)
  dlex[m<r>] options whose oracle dual price exceeds the cheapest by > 1 % are not offered;
             among the others, by L^2 / h^(r/10) (r = 7 by default)
  slex<t>m<r> the same with ESTIMATED duals: a link's price is 1 while it carries at least
             t/10 packets per cycle (smoothed flow count), packets sum it along their path; a
             detour is offered only when its smoothed sum is at most the minimal option's
             + SLACK (environment, default 0.5); then L^2 / h^(r/10)
  split      oracle: the LP's optimal option split, drawn at random (no learning)
Oracles exist for the permutations only; under uniform and hotspot traffic dual/dlex/split
fall back to L^2 / h^(r/10).  `T:<scheme>` runs `torus_experiments.py`'s scheme.

Usage: python3 scripts/xp_tolls.py fluid tornado,bitcomp,randperm      (LEVELS=, ITERS= env)
       python3 scripts/xp_tolls.py sim dlexm10,slex10m10,m7 tornado,bitcomp 0.6,0.8,1.0 11-14
       python3 scripts/xp_tolls.py check     (m7 reproduces bandit2m7f5k exactly)
"""
import os, sys, random, math, time
from collections import deque
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import torus_experiments as T
import routing_graph_sim as G

K, N = T.K, T.N
NET = T.NET
ADJ = NET.adj
DIST = NET.dist
CAP = 2.0
LINKS = [(u, p, ADJ[u][p]) for u in range(N) for p in range(4) if ADJ[u][p] >= 0]
LID = {(u, p): i for i, (u, p, _) in enumerate(LINKS)}
L = len(LINKS)


def longway(s, d, dim):
    """The long-way intermediate of `torus_experiments.sim` (same formula)."""
    if T.TOPO == 'mesh': return None
    x, dx = (s % K, d % K) if dim == 0 else (s // K, d // K)
    r = (dx - x) % K
    if r == 0 or 2*r == K: return None
    short = 1 if r < K - r else -1
    delta = min(r, K - r); m = K//2 - delta + 1
    nx = (x - short*m) % K
    w = nx + (s // K)*K if dim == 0 else (s % K) + nx*K
    port = (1 if short == 1 else 0) if dim == 0 else (3 if short == 1 else 2)
    return w, port, K - delta + (DIST[s][d] - delta)


def perm(pattern):
    rnd = random.Random(0)
    return [T.tdest(pattern, s, rnd) for s in range(N)]


def options(s, d, valiant=True):
    """[(option, segments [(a, b, weight)], hops)] as the bandit sources offer them."""
    opts = [(0, [(s, d, 1.0)], DIST[s][d])]
    if DIST[s][d] <= 1: return opts
    for dim in (0, 1):
        lw = longway(s, d, dim)
        if lw: opts.append((1 + dim, [(s, lw[0], 1.0), (lw[0], d, 1.0)], lw[2]))
    if valiant:
        segs = [(s, w, 1.0 / N) for w in range(N) if w != s] + [(w, d, 1.0 / N) for w in range(N) if w != d]
        opts.append((3, segs, sum(DIST[s][w] + DIST[w][d] for w in range(N)) / N))
    return opts


# --------------------------------------------------------------------------- fluid model
MINOUT = [[[LID[(u, p)] for p in range(4) if ADJ[u][p] >= 0 and DIST[ADJ[u][p]][b] == DIST[u][b] - 1]
           for b in range(N)] for u in range(N)]
ORDER = [sorted(range(N), key=lambda u: DIST[u][b]) for b in range(N)]
HEADL = [v for (_, _, v) in LINKS]


def sp(cost):
    """D[u][b]: cheapest minimal path u -> b under link costs; nxt[b][u] its first link."""
    D = np.zeros((N, N)); nxt = [[-1] * N for _ in range(N)]
    for b in range(N):
        for u in ORDER[b][1:]:
            best, bl = 1e300, -1
            for l in MINOUT[u][b]:
                c = cost[l] + D[HEADL[l]][b]
                if c < best: best, bl = c, l
            D[u][b] = best; nxt[b][u] = bl
    return D, nxt


def load_aon(M, nxt):
    """Link loads when segment demand M[a][b] follows the trees nxt."""
    y = np.zeros(L)
    for b in range(N):
        acc = M[:, b].copy()
        for u in reversed(ORDER[b][1:]):
            if acc[u]:
                l = nxt[b][u]; y[l] += acc[u]; acc[HEADL[l]] += acc[u]
    return y


def lat(x):           # M/M/1 sojourn, service time 1/c normalised to 1; linear past rho 0.99
    r = x / CAP
    return np.where(r < 0.99, 1 / (1 - np.minimum(r, 0.99)), 100 + 1e4 * (r - 0.99))


def dlat(x):
    r = x / CAP
    return np.where(r < 0.99, 1 / CAP / (1 - np.minimum(r, 0.99)) ** 2, 1e4 / CAP)


def frank_wolfe(dem, theta, so, allowed=(0, 1, 2, 3), iters=400):
    """Wardrop equilibrium (so=False) or system optimum (so=True) over the option sets.
    dem: list of (s, d, rate).  Returns option shares per commodity and link loads."""
    OPTS = [[o for o in options(s, d) if o[0] in allowed] for (s, d, _) in dem]
    def target(x):
        c = lat(x) + (x * dlat(x) if so else 0)
        D, nxt = sp(c)
        M = np.zeros((N, N)); choice = []
        for (s, d, r), opts in zip(dem, OPTS):
            o = min(opts, key=lambda o: sum(w * D[a][b] for a, b, w in o[1]))
            choice.append(o[0])
            for a, b, w in o[1]: M[a][b] += theta * r * w
        return load_aon(M, nxt), choice, c, D
    x, ch, _, _ = target(np.zeros(L))
    share = [{c: 1.0} for c in ch]
    for it in range(iters):
        y, ch, c, D = target(x)
        dvec = y - x
        obj = (lambda a: np.dot(dvec, lat(x + a*dvec) + ((x + a*dvec) * dlat(x + a*dvec) if so else 0)))
        lo, hi = 0.0, 1.0
        if obj(1.0) <= 0: a = 1.0
        else:
            for _ in range(40):
                m = (lo + hi) / 2
                if obj(m) > 0: hi = m
                else: lo = m
            a = lo
        if it > 5 and a < 1e-7: break
        x = x + a * dvec
        for sh, cc in zip(share, ch):
            for k in sh: sh[k] *= (1 - a)
            sh[cc] = sh.get(cc, 0) + a
    return share, x


def total_delay(x):
    return float(np.dot(x, lat(x)))


def lp_options(dem, allowed=(0, 1, 2, 3)):
    """Max theta such that theta * dem is routable when each commodity splits over its options
    and every segment is routed minimally.  Returns theta, option shares, link duals (len)."""
    from scipy.optimize import linprog
    from scipy.sparse import coo_matrix
    OPTS = [[o for o in options(s, d) if o[0] in allowed] for (s, d, _) in dem]
    qv = [(i, o[0]) for i, opts in enumerate(OPTS) for o in opts]
    fv = [(b, l) for b in range(N) for u in range(N) for l in MINOUT[u][b]]
    nq, nf = len(qv), len(fv)
    nv = nq + nf + 1
    rows, cols, vals = [], [], []
    r = 0
    qidx = {}
    for j, (i, o) in enumerate(qv): qidx[(i, o)] = j
    for i, opts in enumerate(OPTS):          # sum of option rates = theta * rate
        for o in opts: rows.append(r); cols.append(qidx[(i, o[0])]); vals.append(1.0)
        rows.append(r); cols.append(nv - 1); vals.append(-dem[i][2]); r += 1
    eq = {}
    for (b, u) in ((b, u) for b in range(N) for u in range(N) if u != b): eq[(b, u)] = r; r += 1
    for j, (b, l) in enumerate(fv):
        u, _, v = LINKS[l]
        rows.append(eq[(b, u)]); cols.append(nq + j); vals.append(1.0)
        if v != b: rows.append(eq[(b, v)]); cols.append(nq + j); vals.append(-1.0)
    for i, opts in enumerate(OPTS):
        for o in opts:
            for a, b, w in o[1]:
                if a != b: rows.append(eq[(b, a)]); cols.append(qidx[(i, o[0])]); vals.append(-w)
    Aeq = coo_matrix((vals, (rows, cols)), shape=(r, nv)).tocsr()
    Aub = coo_matrix((np.ones(nf), ([l for _, l in fv], [nq + j for j in range(nf)])), shape=(L, nv)).tocsr()
    c = np.zeros(nv); c[-1] = -1
    res = linprog(c, A_ub=Aub, b_ub=np.full(L, CAP), A_eq=Aeq, b_eq=np.zeros(r), bounds=(0, None),
                  method='highs')
    assert res.status == 0, res.message
    th = res.x[-1]
    share = [{} for _ in dem]
    for j, (i, o) in enumerate(qv):
        share[i][o] = res.x[j] / (th * dem[i][2]) if th > 0 else 0
    return th, share, -res.ineqlin.marginals


def option_price(dem, lens):
    """Each commodity's options priced by the cheapest minimal-segment paths under `lens`."""
    D, _ = sp(lens)
    return [{o[0]: sum(w * D[a][b] for a, b, w in o[1]) for o in options(s, d)} for (s, d, _) in dem]


LEVELS = [float(x) for x in os.environ.get('LEVELS', '0.5,0.7,0.8,0.9').split(',')]
ITERS = int(os.environ.get('ITERS', '400'))


def fluid(pats):
    for p in pats:
        pm = perm(p)
        dem = [(s, pm[s], 1.0) for s in range(N) if pm[s] != s]
        t0 = time.time()
        thmin, _, _ = lp_options(dem, allowed=(0,))
        th, share, lens = lp_options(dem)
        det = sum(1 - sh.get(0, 0) for sh in share) / len(dem)
        lens = lens / lens.mean()
        pr = option_price(dem, lens)
        gap = [min(v for k, v in q.items() if k) - q[0] for q in pr if len(q) > 1]
        print(f'\n== {p}: option LP theta* = {th:.4f} (minimal only {thmin:.4f}); optimum detours '
              f'{100*det:.1f} % of packets; dual price of the best detour minus minimal: '
              f'min {min(gap):+.2f} mean {np.mean(gap):+.2f} (links with len > 0: {int((lens > 1e-9).sum())}/{L})')
        print(f'{"theta/th*":>9} {"UE detour%":>10} {"SO detour%":>10} {"UE delay":>9} {"SO delay":>9} {"PoA":>6} '
              f'{"UE(min only)":>12} {"UE maxrho":>9} {"SO maxrho":>9}')
        for f in LEVELS:
            theta = f * th
            sU, xU = frank_wolfe(dem, theta, False, iters=ITERS)
            sS, xS = frank_wolfe(dem, theta, True, iters=ITERS)
            dU = sum(1 - sh.get(0, 0) for sh in sU) / len(dem)
            dS = sum(1 - sh.get(0, 0) for sh in sS) / len(dem)
            if theta < thmin * 0.995:
                _, xM = frank_wolfe(dem, theta, False, allowed=(0,))
                tm = f'{total_delay(xM):12.1f}'
            else: tm = f'{"infeasible":>12}'
            print(f'{f:9.2f} {100*dU:10.1f} {100*dS:10.1f} {total_delay(xU):9.1f} {total_delay(xS):9.1f} '
                  f'{total_delay(xU)/total_delay(xS):6.3f} {tm} {xU.max()/CAP:9.3f} {xS.max()/CAP:9.3f}', flush=True)
        print(f'({time.time()-t0:.0f} s)')



# --------------------------------------------------------------------------- packet simulation
ORACLE = {}
SLACK = float(os.environ.get('SLACK', '0.5'))


def oracle(pattern):
    """LP capacity duals (mean 1 per link) and optimal option shares for a permutation."""
    if pattern not in ORACLE:
        pm = perm(pattern)
        dem = [(s, pm[s], 1.0) for s in range(N) if pm[s] != s]
        th, share, lens = lp_options(dem)
        lens = np.maximum(lens, 0); lens = lens / max(lens.mean(), 1e-12)
        lam = [0.0] * (N * 5)
        for i, (u, p, _) in enumerate(LINKS): lam[u * 5 + p] = float(lens[i])
        sh = {s: share[i] for i, (s, _, _) in enumerate(dem)}
        pr = {s: q for (s, _, _), q in zip(dem, option_price(dem, lens))}
        ORACLE[pattern] = (lam, sh, pr)
    return ORACLE[pattern]


def sim(scheme, rate, pattern, g=4, budget=2, cycles=4000, warmup=1000, seed=1, eps=0.02,
        fgate=0.5, mexp=0.7):
    """`torus_experiments.sim` for `bandit2m7f5k`-style sources (identical mechanics and random
    stream), with the option price chosen by `scheme` (see the module docstring)."""
    net = NET; head, esc, vc1, out, dist, adj = net.head, net.esc, net.vc1, net.out, net.dist, net.adj
    rnd = random.Random(seed); occ = {}; queues = [deque() for _ in range(N)]; lat = []
    thr = [g * 2 * net.deg[v] / 8 for v in range(N)]
    import re
    mm = re.fullmatch(r'(slex|dlex)(\d*)m(\d+)', scheme)
    if mm:                  # admissible set by (oracle / estimated) duals, then L^2 / h^(r/10)
        mode = mm.group(1); par = float(mm.group(2)) / 10 if mm.group(2) else None
        mexp = float(mm.group(3)) / 10
    else:
        mode = scheme.rstrip('0123456789.')
        par = float(scheme[len(mode):]) if scheme[len(mode):] else None
        if mode == 'm': mexp = par / 10
    perm_pat = pattern not in ('uniform', 'hotspot')
    lam = shr = dpr = None
    if mode in ('dual', 'dlex', 'split'):
        if perm_pat: lam, shr, dpr = oracle(pattern)
        else: mode = 'm'                 # no oracle for random traffic: fall back to m7
    if mode == "tel": ceff = 1.5; kt = par / 10 if par is not None else 1.0
    est = [[0.0] * 4 for _ in range(N)]     # smoothed in-network latency per source and option
    est2 = [[0.0] * 4 for _ in range(N)]    # smoothed telemetry (toll) per source and option
    flow = [[0.0] * 4 for _ in range(N)]
    moves = [[0] * 4 for _ in range(N)]
    toll = [0.0] * (N * 5)                  # per-link toll carried by packets (tel / dual)
    if lam is not None and mode == 'dual': toll = lam
    recent = [deque(maxlen=8) for _ in range(N)]
    cur = [0] * N
    nopt = [0] * 4; ndet = [0, 0]
    sqmode = mode == 'sq'
    usetel = mode in ('tel', 'dual', 'slex')
    for t in range(cycles):
        for c in [c for c, p in occ.items() if head[c] == p[0]]:
            pk = occ.pop(c)
            if t >= warmup: lat.append(t-pk[1])
            e0 = est[pk[9]][pk[7]]
            if sqmode: x = pk[10] + (t - pk[11]) ** 2
            else: x = t - pk[8]
            est[pk[9]][pk[7]] = 0.9 * e0 + 0.1 * x if e0 else float(x)
            if usetel:
                e1 = est2[pk[9]][pk[7]]
                est2[pk[9]][pk[7]] = 0.9 * e1 + 0.1 * pk[10] if e0 else float(pk[10])
        moved = set(); pks = list(occ); rnd.shuffle(pks)
        for c in pks:
            if c in moved: continue
            pk = occ[c]; d = pk[0]; u = head[c]
            if u == d: continue
            src = c // 2 % 5 == 4
            if pk[6] >= 0 and u == pk[6]: pk[6] = -1
            tgt = pk[6] if pk[6] >= 0 else d
            e = esc[c][d]
            onesc = c % 2 == 0 and not src
            canret = not (onesc and pk[4] >= budget)
            tiers = []
            if canret: tiers.append(vc1[u][tgt])
            tiers.append([e])
            q = None
            for tier in tiers:
                free = [x for x in tier if x not in occ]
                if g and src: free = [x for x in free if sum(1 for o in out[head[x]] if o not in occ) >= thr[head[x]]]
                if free:
                    q = rnd.choice(free); break
            if q is None: continue
            if q % 2 == 0 and not (c % 2 == 0): pk[6] = -1
            pk[2] += 1
            if onesc and q % 2 == 1: pk[4] += 1
            if sqmode: pk[10] += (t - pk[11]) ** 2; pk[11] = t
            elif usetel: pk[10] += toll[q // 2]
            occ[q] = occ.pop(c); moved.add(q)
            if (q // 2) % 5 < 4: moves[q // 10][(q // 2) % 5] += 1
        for u in range(N):
            for p in range(4):
                flow[u][p] = 0.98 * flow[u][p] + 0.02 * moves[u][p]; moves[u][p] = 0
                if mode == 'slex':     # estimated dual: 1 on a link carrying >= par packets/cycle
                    toll[u * 5 + p] = 1.0 if flow[u][p] >= par else 0.0
                if mode == 'tel':
                    r = min(flow[u][p] / ceff, 0.9)
                    toll[u * 5 + p] = kt * r / (1 - r) ** 2
        for s in range(N):
            if rnd.random() < rate:
                d = T.tdest(pattern, s, rnd)
                if d != s: queues[s].append((d, t))
            c = s*10 + 8
            if queues[s] and c not in occ:
                d, born = queues[s].popleft()
                inter = -1; opt = 0
                if dist[s][d] > 1:
                    opts = [(0, -1, dist[s][d])]
                    for dim in (0, 1):
                        lw = longway(s, d, dim)
                        if lw and flow[s][lw[1]] <= fgate * min(flow[s][(c2 // 2) % 5] for c2 in vc1[s][d]):
                            opts.append((1 + dim, lw[0], lw[2]))
                    recent[s].append(d)
                    w = rnd.randrange(N)
                    if len(set(recent[s])) > 2: w = s
                    if w not in (s, d):
                        opts.append((3, w, dist[s][w] + dist[w][d]))
                    if mode == 'split':
                        sh = shr[s]
                        r = rnd.random(); acc = 0.0; pick = 0
                        for o in (0, 1, 2, 3):
                            acc += sh.get(o, 0.0)
                            if r < acc: pick = o; break
                        if pick == 3:
                            w2 = rnd.randrange(N)
                            bo = (3, w2, 0)
                        else:
                            lw = longway(s, d, pick - 1) if pick else None
                            bo = (pick, lw[0], 0) if lw else opts[0]
                        opt, inter, _ = bo
                    else:
                        if mode == 'dlex':
                            best = min(dpr[s].values())
                            opts = [o for o in opts if dpr[s].get(o[0], 0) <= best + 0.01 * max(best, 1e-9) + 1e-9] or opts[:1]
                        if mode == 'slex':
                            b0 = est2[s][0]
                            opts = [o for o in opts if o[0] == 0 or est2[s][o[0]] <= b0 + SLACK]
                        if mode in ('sel',): price = lambda o: est[s][o[0]]
                        elif mode == 'sq': price = lambda o: est[s][o[0]]
                        elif mode in ('dlex', 'slex'): price = lambda o: est[s][o[0]] ** 2 / o[2] ** mexp
                        elif usetel: price = lambda o: est[s][o[0]] + (par if mode == 'dual' else 1.0) * est2[s][o[0]]
                        else: price = lambda o: est[s][o[0]] ** 2 / o[2] ** mexp
                        if rnd.random() < eps: opt, inter, _ = rnd.choice(opts)
                        else:
                            bo = min(opts, key=price)
                            co = [o for o in opts if o[0] == cur[s]]
                            if co and price(bo) >= price(co[0]): bo = co[0]
                            cur[s] = bo[0]; opt, inter, _ = bo
                if inter in (s, d): inter = -1
                if t >= warmup: nopt[opt] += 1
                occ[c] = [d, born, 0, dist[s][d], 0, 0, inter, opt, t, s, 0.0, t]
    tot = max(1, sum(nopt))
    global LASTFLOW; LASTFLOW = flow
    return len(lat)/((cycles-warmup)*N), (nopt[1] + nopt[2]) / tot, nopt[3] / tot


def run(scheme, rate, pattern, seed):
    """(accepted, long-way share, Valiant share); `T:<name>` runs torus_experiments' scheme."""
    if scheme.startswith('T:'):
        return T.job((scheme[2:], rate, pattern, seed)), float('nan'), float('nan')
    return sim(scheme, rate, pattern, seed=seed)


def table(schemes, pats, rates, seeds):
    print(f'rates {rates} seeds {list(seeds)}  (peak over rates of the seed mean; +- s.e. x 1e4; '
          f'[detour % at the peak: long way / random intermediate])', flush=True)
    print(f'{"scheme":<16}' + ''.join(f'{p[:9]:>22}' for p in pats), flush=True)
    for sc in schemes:
        cells = []
        for p in pats:
            res = {(r, sd): run(sc, r, p, sd) for r in rates for sd in seeds}
            means = {r: np.mean([res[(r, x)][0] for x in seeds]) for r in rates}
            r = max(rates, key=means.get); m = means[r]
            v = [res[(r, x)][0] for x in seeds]
            se = np.std(v, ddof=1) / len(v) ** .5 if len(v) > 1 else 0
            lw = np.mean([res[(r, x)][1] for x in seeds]); va = np.mean([res[(r, x)][2] for x in seeds])
            det = '' if sc.startswith('T:') else f'[{100*lw:.0f}/{100*va:.0f}]'
            cells.append(f'{m:.4f}±{1e4*se:<3.0f}{det}')
        print(f'{sc:<16}' + ''.join(f'{c:>22}' for c in cells), flush=True)


if __name__ == '__main__':
    if sys.argv[1] == 'fluid':
        fluid(sys.argv[2].split(','))
    elif sys.argv[1] == 'sim':
        rates = [float(x) for x in sys.argv[4].split(',')]
        a, b = sys.argv[5].split('-')
        table(sys.argv[2].split(','), sys.argv[3].split(','), rates, range(int(a), int(b) + 1))
    elif sys.argv[1] == 'check':     # identical to torus_experiments' bandit2m7f5k
        for p in ('tornado', 'uniform'):
            print(p, T.sim('bandit2m7f5k', 0.5, p, seed=3, cycles=1500, warmup=500)[0],
                  sim('m7', 0.5, p, seed=3, cycles=1500, warmup=500)[0])
