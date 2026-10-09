#!/usr/bin/env python3
"""Physarum (slime-mould) dynamics as a self-organising routing rule (experiment; nothing here
is proved).

1. Fluid check (`fluid`): multi-commodity Physarum on the 8 x 8 torus of
   `graph_certificates.py` (capacity 2 per directed link, one commodity per destination).
   Every undirected edge e has conductance D_e (shared by all commodities, or one per commodity
   with `percom`); commodity d is routed as the electrical flow of its demand
   (Q^d_e = D_e (phi^d_u - phi^d_v), unit lengths), and
       dD_e/dt = f(Q_e) - D_e.
   `classic`: f(Q) = sum_d |Q^d_e|, Bonifaci-Mehlhorn-Varma / Tero (converges to shortest paths);
   `mu<x>`  : f(Q) = Q^x (Tero's exponent; x < 1 spreads, steady state minimises sum |Q|^(2-x));
   `cap<m>` : capacity-saturating growth f(Q) = Q for Q <= c, c (c/Q)^m beyond (Q = the larger of
              the two directed loads, c = 2): the steady-state potential drop on an edge is
              (Q/c)^(m+1) above capacity, a price that only appears on saturated links, like the
              dual of max concurrent flow.
   `dcap<m>`: the same, but commodity d's growth on an edge is priced by the load of the arc it
              uses (the direction of Q^d_e): an undirected tube is not penalised for traffic in
              the opposite direction (with `cap`, tornado stays on its shortest paths, because
              the long way uses the reverse arcs of the same saturated edges).
   Findings (8 x 8 torus): with one conductance per edge (shared), translation-symmetric
   traffic keeps the conductances symmetric and the flow never concentrates (tornado: the
   uniform electrical flow, 16/15 by symmetry, 5.5 hops); with one conductance per commodity
   (`percom`), `classic` reaches exactly the shortest paths (tornado 2/3, transpose 1.22 < 4/3,
   shuffle 0.90 < 1: minimal, not even the minimal optimum), and `dcap<m>` approaches the
   optimum over all routings as m grows (m = 32: tornado 1.0605 of 16/15; m = 16: transpose
   1.775 of 20/11, shuffle 1.583 of 8/5), never exactly: the price is paid as overload.
   The demand is scaled by lambda (swept); the resulting flow, rescaled to unit demand, routes at
   theta = 2 / (max directed load); the best over lambda is reported next to the exact optima.

2. Packet level (`sim`): the mechanics of `torus_experiments.py` (`min`: VC1 minimal adaptive
   towards the current target, VC0 up*/down* tree escape, B = 2 returns, throttle g = 4, random
   move order, unbounded source queues) with Physarum choices:
   * at the source, among the options of `bandit` (minimal, the long way round in x or in y, a
     random intermediate); each source keeps a conductance D[s][o] per option and splits its
     packets with probability q_o = (D_o / L_o) / sum_o' (D_o' / L_o') (Physarum's flow split over
     parallel tubes with pressure drop proportional to L), then D_o <- D_o + h (f(q_o) - D_o),
     with a floor D_min so that an option can regrow.  L_o is the option's measured cost (the
     smoothed in-network latency, or its marginal cost latency^2 / hops^r as in `bandit2m7`).
   * per hop (`H`): among the free minimal hops, choose with probability proportional to a
     per-(router, port) conductance that grows with the useful (minimal) flow it carries and is
     divided by its congestion (smoothed occupancy).
   Physarum's random draws use their own generator, so a scheme that always picks the minimal
   option reproduces `min` exactly.

Usage:
  python3 scripts/xp_physarum.py fluid
  python3 scripts/xp_physarum.py screen SCHEMES PATTERNS RATES SEEDS
  python3 scripts/xp_physarum.py sig SCHEMES PATTERNS RATES SEEDS   (peak of the seed mean, se)
One process, no pool (shared machine).
"""
import os, random, sys
from collections import deque

for _v in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_v, '1')          # one core: the machine is shared
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


# ------------------------------------------------------------------------------- fluid model
def fluid_setup():
    import graph_certificates as GC
    g = GC.TORUS
    edges = sorted({(min(u, v), max(u, v)) for (u, _, v) in g.links})
    dem = GC.demands()
    return g, edges, dem


def fluid_run(edges, dem, mode, lam, iters=int(os.environ.get("ITERS", 1500)), h=0.3, percom=False, seed=0):
    n = 64; m = len(edges)
    U = np.array([a for a, _ in edges]); V = np.array([b for _, b in edges])
    act = [d for d in range(n) if any(dem[s][d] for s in range(n))]
    # B[d] : net injection of commodity d (sources +, sink -)
    B = np.zeros((len(act), n))
    for i, d in enumerate(act):
        for s in range(n):
            B[i, s] = float(dem[s][d]) * lam
        B[i, d] = -B[i].sum()
    rng = np.random.default_rng(seed)
    nc = len(act)
    D = np.ones((nc, m)) if percom else np.ones(m)
    D *= 1 + 0.01 * rng.random(D.shape)
    c = 2.0
    inc = np.zeros((m, n)); inc[np.arange(m), U] = 1; inc[np.arange(m), V] = -1
    for it in range(iters):
        if percom:
            Ls = np.matmul(inc.T[None] * D[:, None, :], inc)       # one Laplacian per commodity
            Ls[:, 0, :] = 0; Ls[:, :, 0] = 0; Ls[:, 0, 0] = 1       # ground node 0
            rhs = B.copy(); rhs[:, 0] = 0
            phi = np.linalg.solve(Ls, rhs[:, :, None])[:, :, 0]
            Q = D * (phi[:, U] - phi[:, V])                         # (commodity, edge)
        else:
            L = inc.T @ (D[:, None] * inc)
            phi = np.zeros((nc, n))
            phi[:, 1:] = np.linalg.solve(L[1:, 1:], B[:, 1:].T).T     # ground node 0
            Q = D[None, :] * (phi[:, U] - phi[:, V])
        fwd = np.clip(Q, 0, None).sum(0); bwd = np.clip(-Q, 0, None).sum(0)
        tot = np.abs(Q).sum(0); dirl = np.maximum(fwd, bwd)
        if mode == 'classic':
            F = np.abs(Q) if percom else tot
        elif mode.startswith('mu'):
            F = (np.abs(Q) if percom else tot) ** float(mode[2:])
        elif mode.startswith('dcap'):
            # direction-aware: commodity d is priced by the load of the arc it uses (Q^d > 0:
            # u -> v), so a tube is not penalised for traffic flowing the other way
            mm = float(mode[4:])
            ld = np.where(Q >= 0, fwd[None, :], bwd[None, :])
            F = np.abs(Q) * np.where(ld <= c, 1.0, (c / np.maximum(ld, 1e-12)) ** (mm + 1))
            if not percom: F = F.sum(0)
        elif mode.startswith('cap'):
            mm = float(mode[3:])
            sat = np.where(dirl <= c, 1.0, (c / np.maximum(dirl, 1e-12)) ** (mm + 1))
            # per edge: grow with the flow, capped at capacity (c (c/Q)^m = Q * (c/Q)^(m+1))
            F = (np.abs(Q) * sat[None, :]) if percom else tot * sat
        D = D + h * (F - D)
        D = np.maximum(D, 1e-9)
    theta = 2 * lam / dirl.max()
    used = (tot > 1e-3 * tot.max()).sum()
    hops = tot.sum() / max(1e-12, -B[np.arange(nc), act].sum())
    return theta, used, hops


def fluid_main():
    g, edges, dem = fluid_setup()
    opt = {'tornado': (2/3, 16/15), 'transpose': (4/3, 20/11), 'shuffle': (1, 8/5),
           'bitrev': (16/9, 40/21), 'neighbor': (2, 16/7), 'bitcomp': (1, 1)}
    pats = sys.argv[2].split(',') if len(sys.argv) > 2 else ['tornado', 'transpose']
    modes = sys.argv[3].split(',') if len(sys.argv) > 3 else ['classic', 'mu0.5', 'cap1', 'cap4', 'cap16']
    lams = [float(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 else [0.5, 0.8, 1.0, 1.2, 1.5, 2.0]
    percoms = [False, True] if (len(sys.argv) <= 5 or sys.argv[5] == 'both') else [sys.argv[5] == 'percom']
    for p in pats:
        mn, an = opt.get(p, (None, None))
        print(f'== {p}: exact optimum minimal {mn:.4f}, any {an:.4f}' if mn else f'== {p}', flush=True)
        for pc in percoms:
            for mode in modes:
                res = []
                for lam in lams:
                    th, used, hops = fluid_run(edges, dem[p], mode, lam, percom=pc)
                    res.append((th, lam, used, hops))
                best = max(res)
                print(f'  {"percom" if pc else "shared":<7}{mode:<8} best theta {best[0]:.4f} at lambda {best[1]}'
                      f' (edges used {best[2]}, mean hops {best[3]:.2f});  all: ' +
                      ' '.join(f'{r[1]}:{r[0]:.3f}' for r in res), flush=True)


if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'fluid':
    fluid_main()
    sys.exit()


# ------------------------------------------------------------------------------- packet level
import torus_experiments as T          # NET (TOPO=mesh selects the mesh), tdest, PATS, sim

K, N = T.K, T.N
NET = T.NET


def longway(s, d, dim, dist):
    """As `torus_experiments.sim.longway`: an intermediate on the long way round the ring of
    dimension dim, the source's output port towards it, and the route's hop count."""
    if T.TOPO == 'mesh': return None
    x, dx = (s % K, d % K) if dim == 0 else (s // K, d // K)
    r = (dx - x) % K
    if r == 0 or 2*r == K: return None
    short = 1 if r < K - r else -1
    delta = min(r, K - r); m = K//2 - delta + 1
    nx = (x - short*m) % K
    w = nx + (s // K)*K if dim == 0 else (s % K) + nx*K
    port = (1 if short == 1 else 0) if dim == 0 else (3 if short == 1 else 2)
    return w, port, K - delta + (dist[s][d] - delta)


def psim(rate, pattern, seed=1, cycles=4000, warmup=1000, g=4, budget=2,
         src=None, h=0.05, cost='M', mexp=0.7, floor=0.02, fgate=None, focus=False,
         sat=None, hop=None, hopb=1.0, vopt=True, lopt=True, gamma=1.0, mu=1.0):
    """src=None: `min`.  src='phys': Physarum conductances per source over the options (see the
    module doc).  cost: 'L' smoothed latency (selfish), 'M' latency^2 / hops^mexp (marginal),
    'H' hop count (classic Physarum on lengths: converges to the minimal option).  h: step of
    the conductance update per injected packet; gamma: decay; mu: flux exponent f(q) = q^mu;
    floor: least conductance.  fgate: the long way only when the smoothed packet flow leaving
    the source in that direction is at most fgate x the minimal direction's.  focus: the random
    intermediate only for a source whose last 8 destinations include at most 2 nodes.
    sat: capacity-saturating growth, f(q) * min(1, (sat / flow of the option's first hop))^2
    (an option whose first link already carries `sat` packets per cycle stops gaining).
    hop: per-hop Physarum among the free minimal VC1 hops, weight (0.05 + flow) /
    (0.05 + occupancy)^hopb (flow, occupancy: smoothed per output port)."""
    net = NET; head, esc, vc1, out, dist, adj = net.head, net.esc, net.vc1, net.out, net.dist, net.adj
    rnd = random.Random(seed); prng = random.Random(seed * 7919 + 13)
    occ = {}; queues = [deque() for _ in range(N)]; lat = []
    thr = [g * 2 * net.deg[v] / 8 for v in range(N)]
    hopsum = 0
    est = [[0.0] * 4 for _ in range(N)]
    D = [[1.0, floor, floor, floor] for _ in range(N)]
    flow = [[0.0] * 4 for _ in range(N)]; moves = [[0] * 4 for _ in range(N)]
    occema = [[0.0] * 4 for _ in range(N)]
    recent = [deque(maxlen=8) for _ in range(N)]
    nopt = [0] * 4
    for t in range(cycles):
        if hop is not None:
            for u in range(N):
                for p in range(4):
                    if adj[u][p] >= 0:
                        b = 1.0 if (u*5+p)*2+1 in occ else 0.0
                        occema[u][p] = 0.9*occema[u][p] + 0.1*b
        for c in [c for c, p in occ.items() if head[c] == p[0]]:
            pk = occ.pop(c)
            if t >= warmup: lat.append(t-pk[1]); hopsum += pk[2]
            e0 = est[pk[9]][pk[7]]; x = t - pk[8]
            est[pk[9]][pk[7]] = 0.9 * e0 + 0.1 * x if e0 else float(x)
        moved = set(); pks = list(occ); rnd.shuffle(pks)
        for c in pks:
            if c in moved: continue
            pk = occ[c]; d = pk[0]; u = head[c]
            if u == d: continue
            issrc = c // 2 % 5 == 4
            if pk[6] >= 0 and u == pk[6]: pk[6] = -1
            tgt = pk[6] if pk[6] >= 0 else d
            e = esc[c][d]
            onesc = c % 2 == 0 and not issrc
            canret = not (onesc and pk[4] >= budget)
            tiers = []
            if canret: tiers.append(vc1[u][tgt])
            tiers.append([e])
            q = None
            for ti, tier in enumerate(tiers):
                free = [x for x in tier if x not in occ]
                if g and issrc: free = [x for x in free if sum(1 for o in out[head[x]] if o not in occ) >= thr[head[x]]]
                if free:
                    if hop is not None and len(free) > 1 and free[0] % 2 == 1:
                        ws = [(0.05 + flow[u][(x // 2) % 5]) / (0.05 + occema[u][(x // 2) % 5]) ** hopb for x in free]
                        q = prng.choices(free, ws)[0]
                    else:
                        q = rnd.choice(free)
                    break
            if q is None: continue
            if q % 2 == 0 and not (c % 2 == 0): pk[6] = -1
            pk[2] += 1
            if onesc and q % 2 == 1: pk[4] += 1
            occ[q] = occ.pop(c); moved.add(q)
            if (q // 2) % 5 < 4: moves[q // 10][(q // 2) % 5] += 1
        for u in range(N):
            fu, mu_ = flow[u], moves[u]
            for p in range(4):
                fu[p] = 0.98 * fu[p] + 0.02 * mu_[p]; mu_[p] = 0
        for s in range(N):
            if rnd.random() < rate:
                d = T.tdest(pattern, s, rnd)
                if d != s: queues[s].append((d, t))
            c = s*10 + 8
            if queues[s] and c not in occ:
                d, born = queues[s].popleft()
                inter, opt = -1, 0
                if src == 'phys' and dist[s][d] > 1:
                    mports = [(c2 // 2) % 5 for c2 in vc1[s][d]]
                    fmin = min(flow[s][p] for p in mports)
                    opts = [(0, -1, dist[s][d], fmin)]
                    if lopt:
                        for dim in (0, 1):
                            lw = longway(s, d, dim, dist)
                            if lw and (fgate is None or flow[s][lw[1]] <= fgate * fmin):
                                opts.append((1 + dim, lw[0], lw[2], flow[s][lw[1]]))
                    recent[s].append(d)
                    if vopt and not (focus and len(set(recent[s])) > 2):
                        w = prng.randrange(N)
                        if w not in (s, d):
                            opts.append((3, w, dist[s][w] + dist[w][d],
                                         min(flow[s][(c2 // 2) % 5] for c2 in vc1[s][w])))
                    Ds = D[s]; es = est[s]; e0 = es[0] or 4.0 * dist[s][d]
                    def L(o):
                        lat_o = es[o[0]] or e0 * o[2] / dist[s][d]
                        if cost == 'L': return lat_o
                        if cost == 'H': return o[2]
                        return lat_o ** 2 / o[2] ** mexp
                    wts = [Ds[o[0]] / L(o) for o in opts]
                    tot = sum(wts)
                    qs = [x / tot for x in wts]
                    k = prng.choices(range(len(opts)), wts)[0]
                    opt, inter = opts[k][0], opts[k][1]
                    # Physarum update of the offered options' conductances
                    for o, qo in zip(opts, qs):
                        f = qo ** mu
                        if sat is not None and o[3] > sat: f *= (sat / o[3]) ** 2
                        Ds[o[0]] = max(floor, Ds[o[0]] + h * (f - gamma * Ds[o[0]]))
                    nopt[opt] += 1
                if inter in (s, d): inter = -1
                occ[c] = [d, born, 0, dist[s][d], 0, 0, inter, opt, t, s]
    return len(lat)/((cycles-warmup)*N), hopsum/max(1, len(lat)), nopt


SCHEMES = {
    'min': {},
}


def scheme_kwargs(name):
    """Scheme names: 'min' or 'phys' followed by options separated by '_':
    h<x> step, c<L|M|H> cost, e<x> marginal exponent, fl<x> floor, f<x> long-way gate (x/10),
    k focus gate, s<x> saturation flow (x/100), H<b> hop-level rule with exponent b/10,
    V no random intermediate, X no long way, g<x> decay, u<x> flux exponent (x/10)."""
    if name == 'min': return {}
    kw = {}
    parts = name.split('_')
    if parts[0] == 'phys': kw['src'] = 'phys'
    elif parts[0] != 'hop': raise ValueError(name)
    for p in parts[1:]:
        if p.startswith('fl'): kw['floor'] = float(p[2:])
        elif p.startswith('h'): kw['h'] = float(p[1:])
        elif p.startswith('c'): kw['cost'] = p[1:]
        elif p.startswith('e'): kw['mexp'] = float(p[1:])
        elif p.startswith('f'): kw['fgate'] = float(p[1:]) / 10
        elif p == 'k': kw['focus'] = True
        elif p.startswith('s'): kw['sat'] = float(p[1:]) / 100
        elif p.startswith('H'): kw['hop'] = True; kw['hopb'] = float(p[1:] or 10) / 10
        elif p == 'V': kw['vopt'] = False
        elif p == 'X': kw['lopt'] = False
        elif p.startswith('g'): kw['gamma'] = float(p[1:])
        elif p.startswith('u'): kw['mu'] = float(p[1:]) / 10
        else: raise ValueError(p)
    return kw


def run(name, rate, pattern, seed):
    if name.startswith('T:'):          # a scheme of torus_experiments.py (for paired comparisons)
        return T.job((name[2:], rate, pattern, seed))
    return psim(rate, pattern, seed=seed, **scheme_kwargs(name))[0]


def table(mode):
    schemes = sys.argv[2].split(','); pats = sys.argv[3].split(',')
    rates = [float(x) for x in sys.argv[4].split(',')]
    seeds = [int(x) for x in sys.argv[5].split(',')]
    print(f'{"scheme":<26}' + ''.join(f'{p[:9]:>17}' for p in pats), flush=True)
    for s in schemes:
        cells = []
        for p in pats:
            res = {(r, x): run(s, r, p, x) for r in rates for x in seeds}
            means = {r: sum(res[(r, x)] for x in seeds) / len(seeds) for r in rates}
            r = max(rates, key=means.get); m = means[r]
            v = [res[(r, x)] for x in seeds]
            se = (sum((a - m) ** 2 for a in v) / (len(v) - 1)) ** .5 / len(v) ** .5 if len(v) > 1 else 0
            cells.append(f'{m:.4f}±{se:.4f}@{r:g}')
        print(f'{s:<26}' + ''.join(f'{c:>17}' for c in cells), flush=True)


if __name__ == '__main__':
    if sys.argv[1] in ('screen', 'sig'):
        table(sys.argv[1])
