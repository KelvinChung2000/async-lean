#!/usr/bin/env python3
"""The mesh portfolio of `xp_portfolio.py` with mode X (XY on both virtual channels, = `dualXY`)
replaced by the XY mode of `xp_bitcomp.py` (simulation only; nothing here is proved).

X' = `B:c0=fary+srcwf:fd=5:fs=3` of `xp_bitcomp.py`, re-expressed as a tier list of the
west-first mesh in `xp_combo2.msim` (the base of the portfolio):

    tiers = [xyc, esc], g = 0          (spec `route=wf:tiers=xyc+esc:thr=g0`)

  esc  the XY hop on VC0 (`escTier k 0`)
  xyc  the XY hop on VC0, and the XY hop on VC1 unless the packet is `restricted`:
         fary   it is more than fd = 5 hops from its destination and a nearer packet waits at
                its router for the same output direction: a packet in a link into the router
                (at most fd hops to go) or in the router's injection channel (at most fs = 3
                hops to go);
         srcwf  it is in its injection channel, more than fs = 3 hops from its destination, and
                a packet in a link into the router waits for the same output direction.
       Both read only the configuration (the channels holding packets and their destinations)
       and the packet's own channel and destination: `xyc` is a predicate
       `Config -> chan -> dest -> hop -> Bool`, i.e. a tier in the sense of `tieredSel`.
Every XY hop (either VC) is a permitted hop of `westFirstMesh` (XY escape on VC0, any productive
VC1 hop), the list contains `escTier k 0`, so X' alone is `westFirstTiers_correct`, and the
portfolio that switches among B, W, X', P (each containing `escTier k g`, g <= 8) by any
history-dependent rule is `westFirstMesh_modes_safe`.  `xp_bitcomp.bsim` itself runs on
`xp_combo2.tables(8, 'wf')`, i.e. it was already defined on the west-first mesh; `check` shows
the re-expression reproduces `bsim` bit for bit.

Mode sets (added to xp_portfolio.MSETS):
  x4  [B, W, X', P]        (= m4 with X -> X'; the congestion gate's default d=2 is X')
  x5  [B, W, X, X', P]     (both XY modes; default d=3 is X')
  x3  [B, W, X']           (no price mode)
  x4g [B, WF, X', P]       (W without its throttle: the published west-first random)

Specs: `PM:<set>[:learner opts]` (xp_portfolio), `MX:<msim spec>` (msim with the xyc tier; fd /
fs keys), `B:...` (xp_bitcomp), anything else xp_combo2.run_one (`A:`, `M:`).

Usage:
  python3 scripts/xp_portfolio2.py check
  python3 scripts/xp_portfolio2.py jobs FILE    (lines 'specs|pats|rates|seeds|chains|cycles')
  python3 scripts/xp_portfolio2.py report MAIN OTHERS PLAN CHAINS CYCLES
          PLAN: 'pat=r1/r2/..@seeds;pat=...' (per-pattern offered loads and seeds)
          OTHERS: comma-separated, '~' prefix = reference (shown, not in "best of")
Cache: XP_PF2_CACHE (default xp_portfolio2.json in the system temporary directory);
XP_PF2_PROCS processes (default 3).
"""
import inspect
import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import xp_combo2 as X2
import xp_backpressure as XP
import xp_portfolio as PF
import xp_bitcomp as BC

X2.MDEF.setdefault('fd', 5.0)
X2.MDEF.setdefault('fs', 3.0)

XPRIME = 'route=wf:tiers=xyc+esc:thr=g0'
XPRIME_B = 'c0=fary+srcwf:fd=5:fs=3'
MODE_X = 'route=wf:tiers=xy+esc:thr=g0'
MODE_W = 'route=wf:tiers=all+esc:thr=g2'
MODE_P = 'route=wf:tiers=pref+esc+vc1:sel=price'
PF.MSETS['x4'] = [PF.MESH_B, MODE_W, XPRIME, MODE_P]
PF.MSETS['x5'] = [PF.MESH_B, MODE_W, MODE_X, XPRIME, MODE_P]
PF.MSETS['x3'] = [PF.MESH_B, MODE_W, XPRIME]
PF.MSETS['x1'] = [XPRIME]
# W without its throttle (= the published west-first random, `A:R:westFirstMesh:random`)
MODE_WF = 'route=wf:tiers=all+esc:thr=g0'
PF.MSETS['x4g'] = [PF.MESH_B, MODE_WF, XPRIME, MODE_P]

# the xyc tier, inserted into msim's tier_fn
_XYC_SETUP_OLD = "    moves = chained = 0\n\n    def useful(q, d):\n"
_XYC_SETUP_NEW = (
    "    moves = chained = 0\n"
    "    _fd, _fs = int(o['fd']), int(o['fs'])\n"
    "    _xyd = _BCT()[6]\n"
    "    _dist = lambda u, d: abs(u % k - d % k) + abs(u // k - d // k)\n"
    "\n"
    "    def _restricted(c, u, d, q, src):\n"
    "        # xp_bitcomp klass(...) & {'fary', 'srcwf'}: configuration + own channel/destination\n"
    "        dr = q // 2 % 5\n"
    "        du = _dist(u, d)\n"
    "        if src and du > _fs:\n"
    "            for vv, dd in ((u - 1, 0), (u + 1, 1), (u - k, 2), (u + k, 3)):\n"
    "                if 0 <= vv < n and (dd > 1 or vv // k == u // k):\n"
    "                    for vc in (0, 1):\n"
    "                        pq = occ.get(ch(vv, dd, vc))\n"
    "                        if pq is not None and pq is not GHOST and pq[0] != u and \\\n"
    "                                _xyd[u][pq[0]] == dr:\n"
    "                            return True\n"
    "        if du > _fd:\n"
    "            for vv, dd in ((u - 1, 0), (u + 1, 1), (u - k, 2), (u + k, 3), (u, 4)):\n"
    "                if 0 <= vv < n and (dd > 1 or vv // k == u // k):\n"
    "                    for vc in ((0, 1) if dd < 4 else (0,)):\n"
    "                        q2 = ch(vv, dd, vc)\n"
    "                        if q2 == c:\n"
    "                            continue\n"
    "                        pq = occ.get(q2)\n"
    "                        if pq is not None and pq is not GHOST and pq[0] != u and \\\n"
    "                                _xyd[u][pq[0]] == dr and \\\n"
    "                                _dist(u, pq[0]) <= (_fs if dd == 4 and _fs >= 0 else _fd):\n"
    "                            return True\n"
    "        return False\n"
    "\n"
    "    def useful(q, d):\n")
_XYC_TIER_OLD = "        raise ValueError(name)\n"
_XYC_TIER_NEW = (
    "        if name == 'xyc':\n"
    "            if _restricted(c, u, d, esc, src):\n"
    "                return lambda q: q == esc\n"
    "            x1 = XY1[u][d]\n"
    "            return lambda q: q == esc or q == x1\n"
    "        raise ValueError(name)\n")


def _patched(src, extra, name):
    for old, new in [(_XYC_SETUP_OLD, _XYC_SETUP_NEW), (_XYC_TIER_OLD, _XYC_TIER_NEW)] + extra:
        assert src.count(old) == 1, old
        src = src.replace(old, new)
    ns = dict(vars(X2))
    ns['_BCT'] = BC.tabs
    ns['_PF'] = {}
    return PF._exec(src, ns, name), ns


_XMSIM = None


def xmsim_fn():
    global _XMSIM
    if _XMSIM is None:
        _XMSIM = _patched(inspect.getsource(X2.msim), [], 'msim')[0]
    return _XMSIM


_PMSIM2 = None


def pmsim2_fn():
    """xp_portfolio.pmsim_fn with the xyc tier available to the modes."""
    global _PMSIM2
    if _PMSIM2 is not None:
        return _PMSIM2
    extra = [
        ("def msim(spec, rate, pattern, seed=1, chain='seq', cycles=2000, warmup=None, k=8):",
         "def pmsim(spec, rate, pattern, seed=1, chain='seq', cycles=2000, warmup=None, k=8):"),
        ("    useprice = sel == 'price'\n", "    useprice = _PF['useprice']\n"),
        (PF._HOOK_OLD,
         "    for t in range(cycles):\n"
         "        _m = _PF['L'].step(t, [_s for _s in range(n) if ch(_s, 4, 0) in occ])\n"
         "        if _m is not None:\n"
         "            tiers_n, stiers_n, sx, sel, delta, gdev, devset, gfix = _PF['modes'][_m]\n"
         "        if ctrl is not None:\n            ctrl.tick(t, occ)\n"),
        ("            _, born = take(c)\n",
         "            _, born = take(c)\n            _PF['L'].n += 1\n"),
    ]
    _PMSIM2 = _patched(inspect.getsource(X2.msim), extra, 'pmsim')
    return _PMSIM2


_ORIG_PMSIM_FN = PF.pmsim_fn
PF.pmsim_fn = pmsim2_fn          # xp_portfolio.pm_run now runs modes that may use xyc


def run_one(spec, rate, pattern, seed, chain='seq', cycles=2000):
    kind, _, sp = spec.partition(':')
    if kind == 'PM':
        return PF.run_one(spec, rate, pattern, seed, chain, cycles)
    if kind == 'MX':
        return list(xmsim_fn()(sp, rate, pattern, seed=seed, chain=chain, cycles=cycles))
    if kind == 'B':
        return BC.run_one(spec, rate, pattern, seed, chain, cycles)
    return list(X2.run_one(spec, rate, pattern, seed, chain, cycles))


def check():
    ok = True
    for chn in ('seq', 'none'):
        for p, r, sd in (('bitcomp', 0.3, 3), ('randperm', 0.9, 4), ('uniform', 0.6, 5),
                         ('transpose', 0.7, 6), ('hotspot', 0.5, 7), ('tornado', 0.6, 8)):
            a = BC.bsim(XPRIME_B, r, p, seed=sd, chain=chn, cycles=900)
            b = xmsim_fn()(XPRIME, r, p, seed=sd, chain=chn, cycles=900)
            c = PF.pm_run('x1', r, p, sd, chn, 900)
            e = a[:2] == b[:2] == tuple(c[:2])
            ok &= e
            print("X' bsim / msim-xyc / 1-mode portfolio", chn, p, a[:2], b[:2], c[:2], e)
        # the unpatched modes are unchanged by the patch
        for sp in (PF.MESH_B, MODE_X, MODE_P):
            a = X2.msim(sp, 0.6, 'shuffle', seed=2, chain=chn, cycles=600)
            b = xmsim_fn()(sp, 0.6, 'shuffle', seed=2, chain=chn, cycles=600)
            ok &= a == b
            print('msim / msim-xyc', chn, sp, a[:2], b[:2], a == b)
        # the m4 portfolio is unchanged by the new pmsim
        ok_m4 = True
        for p, r in (('transpose', 1.0), ('bitcomp', 0.3)):
            b = PF.pm_run('m4:th=0.7:d=2', r, p, 3, chn, 1500)
            PF.pmsim_fn = _ORIG_PMSIM_FN
            a = PF.pm_run('m4:th=0.7:d=2', r, p, 3, chn, 1500)
            PF.pmsim_fn = pmsim2_fn
            ok_m4 &= a == b
            print('PM:m4 old/new pmsim', chn, p, a[:2], b[:2], a == b)
        ok &= ok_m4
    print('PM:x4', PF.pm_run('x4:th=0.7:d=2', 1.0, 'transpose', 3, 'seq', 3000))
    print('ALL OK' if ok else 'MISMATCH')


# ------------------------------------------------------------------ driver
CACHE = os.environ.get('XP_PF2_CACHE', os.path.join(tempfile.gettempdir(), 'xp_portfolio2.json'))


def _job(a):
    return a, run_one(*a)


def load(path=None):
    try:
        with open(path or CACHE) as f:
            return {tuple(json.loads(kk)): v for kk, v in json.load(f).items()}
    except (OSError, ValueError):
        return {}


def save(new):
    res = load()
    res.update(new)
    tmp = CACHE + f'.tmp{os.getpid()}'
    with open(tmp, 'w') as f:
        json.dump({json.dumps(list(kk)): v for kk, v in res.items()}, f)
    os.replace(tmp, CACHE)


def cost(j):
    sp = j[0]
    return (j[5], sp.startswith('PM'), 'price' in sp)


def compute(jobs):
    from multiprocessing import Pool
    res = load()
    todo = [j for j in dict.fromkeys(jobs) if j not in res]
    print(len(todo), 'to run', file=sys.stderr, flush=True)
    if todo:
        todo.sort(key=cost, reverse=True)       # longest first
        with Pool(int(os.environ.get('XP_PF2_PROCS', 3))) as pool:
            new = {}
            for i, (a, r) in enumerate(pool.imap_unordered(_job, todo, chunksize=1)):
                new[a] = list(r)
                if i % 10 == 9:
                    save(new)
                    new = {}
                    print(f'{i + 1}/{len(todo)}', file=sys.stderr, flush=True)
        save(new)
    return load()


def jobs_of(specs, pats, rates, seeds, chains, cycles):
    return [(sp, float(r), p, sd, ch, int(cycles)) for ch in chains.split(',')
            for sp in specs.split(',') for p in X2.pats_of(pats) for r in rates.split(',')
            for sd in X2.seedlist(seeds)]


def parse_plan(plan):
    """'pat=r1/r2/..@seeds;...' -> {pat: (rates, seeds)}"""
    out = {}
    for tok in plan.split(';'):
        if tok:
            p, rest = tok.split('=')
            rs, sd = rest.split('@')
            out[p] = ([float(x) for x in rs.split('/')], X2.seedlist(sd))
    return out


def cell(res, sp, p, rates, seeds, ch, cyc, full=False):
    best = None
    for r in rates:
        v = [res.get((sp, r, p, sd, ch, cyc)) for sd in seeds]
        v = [x for x in v if x is not None]
        if len(v) < len(seeds):       # complete cells only
            continue
        m, se = XP.stats([x[0] for x in v])
        if best is None or m > best[0]:
            best = (m, se, r, len(v), v)
    return best


def report(argv):
    main, others, plan, chains, cyc = argv[:5]
    cyc = int(cyc)
    plan = parse_plan(plan)
    pats = list(plan)
    others = others.split(',')
    refs = {o.lstrip('~') for o in others if o.startswith('~')}
    names = [main] + [o.lstrip('~') for o in others]
    res = load()
    z = lambda a, b: (a[0] - b[0]) / max(1e-12, (a[1] ** 2 + b[1] ** 2) ** .5)
    out = {}
    for ch in chains.split(','):
        tab = {sp: [cell(res, sp, p, plan[p][0], plan[p][1], ch, cyc) for p in pats]
               for sp in names}
        out[ch] = tab
        print(f'\n== chain={ch}, {cyc} cycles: peak mean ± se (x1e-4) @offered [seeds]')
        print(f'{"":<44}' + ''.join(f'{p[:9]:>22}' for p in pats))
        for sp in names:
            print(f'{("~" if sp in refs else "") + sp[:43]:<44}' + ''.join(
                f'{c[0]:>9.4f}±{c[1] * 1e4:<3.0f}@{c[2]:<4g}[{c[3]}]' if c else f'{"-":>22}'
                for c in tab[sp]))
        m = tab[main]
        if main.startswith('PM'):
            print(f'{"MAIN mode share % at peak (switches)":<44}' + ''.join(
                f'{"/".join(f"{100 * sum(x[5 + i] for x in c[4]) / len(c[4]):.0f}" for i in range(len(c[4][0]) - 5)) + " (" + str(round(sum(x[4] for x in c[4]) / len(c[4]))) + ")":>22}'
                if c else f'{"-":>22}' for c in m))
        oth = [s for s in names[1:] if s not in refs]
        bestrow = []
        for i in range(len(pats)):
            cand = [s for s in oth if tab[s][i]]
            bestrow.append(max(cand, key=lambda s: tab[s][i][0]) if cand else None)
        print(f'{"best of the others":<44}' + ''.join(
            f'{tab[b][i][0]:>22.4f}' if b else f'{"-":>22}' for i, b in enumerate(bestrow)))
        print(f'{"  by":<44}' + ''.join(f'{(b or "-")[-21:]:>22}' for b in bestrow))
        print(f'{"MAIN vs best: %, z":<44}' + ''.join(
            f'{100 * (m[i][0] / tab[b][i][0] - 1):>+14.2f}%{z(m[i], tab[b][i]):>+6.1f}z'
            if b and m[i] else f'{"-":>22}' for i, b in enumerate(bestrow)))
        for r in names[1:]:
            print(f'{"vs " + r[:41]:<44}' + ''.join(
                f'{100 * (m[i][0] / tab[r][i][0] - 1):>+14.2f}%{z(m[i], tab[r][i]):>+6.1f}z'
                if m[i] and tab[r][i] else f'{"-":>22}' for i in range(len(pats))))
    return out


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'check':
        check()
    elif cmd == 'jobs':
        jobs = []
        with open(sys.argv[2]) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith('#'):
                    jobs += jobs_of(*line.split('|'))
        print(len(jobs), 'jobs', file=sys.stderr)
        compute(jobs)
    elif cmd == 'report':
        report(sys.argv[2:])
