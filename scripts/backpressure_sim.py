#!/usr/bin/env python3
"""Backpressure with integer packets (nothing here is proved; the queueing model with divisible
traffic, `Fluid.Run` in AsyncLean/Flow/Backpressure.lean, is: there backpressure is stable at
every load below the fluid optimum, and no scheduler is stable above it).

The network: the k x k mesh or torus, every directed link with m connections, each carrying 2
packets per slot (the 2 virtual channels of a connection in scripts/lane_scaling.py, the
capacity 2 of `meshNet` / `torusNet`).  Every vertex keeps an unbounded queue per destination.
In every slot:

  1. every link u -> v picks a destination d of largest backlog difference Q[u,d] - Q[v,d]
     (ties at random) and, if the difference is positive, requests its full capacity 2m
     (the rates `bpRates`);
  2. a vertex serves the requests for one destination in random order until its backlog is
     used up (integer packets; `sendAll` is the divisible version);
  3. packets reaching their destination leave; then every vertex receives Poisson(rho) new
     packets, each for a uniformly random other vertex.

The script prints, per offered load rho (packets per vertex per slot), the accepted throughput
and the mean backlog per vertex in the second half of the run (stable loads keep it flat), and
the largest load accepted in full (delivered >= 99 % of the offered load), per connection,
next to the fluid optimum per connection (mesh 8 (k^2 - 1) / k^3, torus
16 (k^2 - 1) / k^3 for even k; `mesh_opt`, `torus_uniform_opt`).
"""
import argparse

import numpy as np


def links(k, torus):
    us, vs = [], []
    for y in range(k):
        for x in range(k):
            u = y * k + x
            for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                nx, ny = x + dx, y + dy
                if torus:
                    nx, ny = nx % k, ny % k
                elif not (0 <= nx < k and 0 <= ny < k):
                    continue
                us.append(u)
                vs.append(ny * k + nx)
    return np.array(us), np.array(vs)


def simulate(k, torus, m, rho, slots, seed, cap_q=None):
    rng = np.random.default_rng(seed)
    n = k * k
    lu, lv = links(k, torus)
    E = len(lu)
    cap = 2 * m
    Q = np.zeros((n, n), dtype=np.int64)
    delivered = 0
    half = slots // 2
    backlog_mid = backlog_end = 0
    arrived = 0
    qmax = 0
    for t in range(slots):
        # 1. every link picks a destination of largest backlog difference
        diff = Q[lu, :] - Q[lv, :] + rng.random((E, n)) * 0.5   # random tie break
        d = diff.argmax(axis=1)
        w = Q[lu, d] - Q[lv, d]
        req = np.where(w > 0, cap, 0)
        # 2. serve the requests in random order until the backlog is used up
        order = rng.permutation(E)
        key = lu[order] * n + d[order]
        srt = np.argsort(key, kind='stable')
        idx = order[srt]
        keys = key[srt]
        r = req[idx]
        cum = np.cumsum(r)
        start = np.r_[0, np.flatnonzero(keys[1:] != keys[:-1]) + 1]
        grp = np.repeat(np.arange(len(start)), np.diff(np.r_[start, len(keys)]))
        before = cum - r - (cum[start] - r[start])[grp]
        avail = Q[lu[idx], d[idx]]
        send = np.clip(avail - before, 0, r)
        if cap_q is not None:
            # finite buffers: a link sends only into free room of the receiver's queue
            key2 = lv[idx] * n + d[idx]
            srt2 = np.argsort(key2, kind='stable')
            k2 = key2[srt2]
            s2 = send[srt2]
            cum2 = np.cumsum(s2)
            st2 = np.r_[0, np.flatnonzero(k2[1:] != k2[:-1]) + 1]
            g2 = np.repeat(np.arange(len(st2)), np.diff(np.r_[st2, len(k2)]))
            before2 = cum2 - s2 - (cum2[st2] - s2[st2])[g2]
            dest = lv[idx][srt2] == d[idx][srt2]
            room = np.where(dest, 1 << 40, cap_q - Q[lv[idx][srt2], d[idx][srt2]])
            s2 = np.clip(room - before2, 0, s2)
            send = np.empty_like(send)
            send[srt2] = s2
        np.subtract.at(Q, (lu[idx], d[idx]), send)
        np.add.at(Q, (lv[idx], d[idx]), send)
        # 3. delivery and arrivals
        if t >= half:
            delivered += Q[np.arange(n), np.arange(n)].sum()
        Q[np.arange(n), np.arange(n)] = 0
        cnt = rng.poisson(rho, n)
        src = np.repeat(np.arange(n), cnt)
        dst = rng.integers(0, n - 1, len(src))
        dst = dst + (dst >= src)
        if cap_q is not None:
            keep = []
            for a, b in zip(src, dst):
                if Q[a, b] < cap_q:
                    Q[a, b] += 1
                    keep.append(a)
            src = keep
        else:
            np.add.at(Q, (src, dst), 1)
        if t >= half:
            arrived += len(src)
            qmax = max(qmax, int(Q.max()))
        if t == half + (slots - half) // 2:
            backlog_mid = Q.sum()
    backlog_end = Q.sum()
    simulate.qmax = qmax
    simulate.accepted = arrived / ((slots - half) * n)
    return delivered / ((slots - half) * n), backlog_mid / n, backlog_end / n


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--k', type=int, default=8)
    ap.add_argument('--topologies', default='mesh,torus')
    ap.add_argument('--ms', default='1,2,4')
    ap.add_argument('--fracs', default='0.5,0.7,0.8,0.85,0.9,0.95,1.0,1.05',
                    help='offered loads as fractions of the fluid optimum')
    ap.add_argument('--slots', type=int, default=20000)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--cap', type=int, default=0,
                    help='with --buffers: per-destination buffers of cap * m packets (blocking)')
    ap.add_argument('--buffers', action='store_true',
                    help='largest per-destination queue against the slack delta = 1 - load/opt')
    args = ap.parse_args()
    if args.buffers:
        k = args.k
        print(f'mesh {k}x{k}: ' + ('delivered / fluid optimum, finite buffers' if args.cap else 'largest per-destination queue (second half of the run)'))
        print(f'{"m":>3}' + ''.join(f'{"d=" + str(d):>9}' for d in (0.4, 0.2, 0.1, 0.05, 0.02)))
        for m in [int(x) for x in args.ms.split(',')]:
            opt = 8 * (k * k - 1) / k ** 3
            row = []
            for d in (0.4, 0.2, 0.1, 0.05, 0.02):
                if args.cap:
                    acc, _, _ = simulate(k, False, m, (1 - d) * opt * m, args.slots, args.seed,
                                         cap_q=args.cap * m)
                    row.append(f'{acc / (opt * m):.3f}')
                else:
                    simulate(k, False, m, (1 - d) * opt * m, args.slots, args.seed)
                    row.append(simulate.qmax)
            print(f'{m:>3}' + ''.join(f'{q:>9}' for q in row), flush=True)
        if args.cap:
            print(f'(delivered throughput / fluid optimum, buffers of {args.cap} m packets per '
                  f'destination; offered 1 - d)')
        return
    k = args.k
    for topo in args.topologies.split(','):
        torus = topo == 'torus'
        opt = (16 if torus else 8) * (k * k - 1) / k ** 3 if k % 2 == 0 else None
        print(f'{topo} {k}x{k}, fluid optimum per vertex per connection {opt:.4f}')
        print(f'{"m":>3}{"load/opt":>10}{"offered/m":>11}{"accepted/m":>12}'
              f'{"backlog mid":>13}{"backlog end":>13}{"delay":>8}')
        for m in [int(x) for x in args.ms.split(',')]:
            best = 0.0
            for f in [float(x) for x in args.fracs.split(',')]:
                rho = f * opt * m
                acc, bmid, bend = simulate(k, torus, m, rho, args.slots, args.seed)
                ok = acc >= 0.99 * rho
                if ok:
                    best = max(best, rho / m)
                delay = (bmid + bend) / 2 / acc   # Little's law, slots
                print(f'{m:>3}{f:>10.2f}{rho / m:>11.4f}{acc / m:>12.4f}{bmid:>13.1f}{bend:>13.1f}'
                      f'{delay:>8.0f}{"" if ok else "   (overloaded)"}', flush=True)
            print(f'  m={m}: largest offered load accepted in full, per connection: {best:.4f} '
                  f'= {best / opt:.0%} of the fluid optimum', flush=True)


if __name__ == '__main__':
    main()
