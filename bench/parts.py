#!/usr/bin/env python3
"""Time the fast explicit check whole (`async_fast`) against split into parts
(`async_fast (parts := k)`).

usage: bench/parts.py NAME "STATEMENT" TACTIC

Writes the goal to bench/out/, checks it with `lake env lean`, and prints wall
time, CPU time (user + system) and peak resident memory.  Times include loading the library.
"""
import os, resource, subprocess, sys, time

HEADER = r'''import AsyncLean.Checker.Tactic
open AsyncLean
set_option maxHeartbeats 0

def handshakes (k : ℕ) : PNet where
  places := 4 * k
  trans := (List.range k).flatMap fun i =>
    let a0 := 4 * i; let a1 := 4 * i + 1; let r0 := 4 * i + 2; let r1 := 4 * i + 3
    [ { name := "req+", pre := [a0, r0], post := [a0, r1] },
      { name := "ack+", pre := [a0, r1], post := [a1, r1], internal := true },
      { name := "req-", pre := [a1, r1], post := [a1, r0] },
      { name := "ack-", pre := [a1, r0], post := [a0, r0], internal := true } ]
  init := (List.range k).flatMap fun _ => [1, 0, 1, 0]

def benchBarrier (n : ℕ) : PNet where
  places := 3 * n
  trans := (List.range n).flatMap (fun i =>
      [{ name := "begin", pre := [3 * i], post := [3 * i + 1] },
       { name := "finish", pre := [3 * i + 1], post := [3 * i + 2], internal := true }]) ++
    [{ name := "barrier", pre := (List.range n).map (3 * · + 2), post := (List.range n).map (3 * ·) }]
  init := (List.range n).flatMap fun _ => [1, 0, 0]

def philosophers (n : ℕ) (ordered : Bool) : PNet :=
  let think i := 3 * i
  let holding i := 3 * i + 1
  let eat i := 3 * i + 2
  let fork j := 3 * n + j
  let swap i := ordered && i + 1 == n
  let first i := if swap i then fork 0 else fork i
  let second i := if swap i then fork i else fork ((i + 1) % n)
  { places := 4 * n
    trans := (List.range n).flatMap fun i =>
      [ { name := s!"take₁ {i}", pre := [think i, first i], post := [holding i] },
        { name := s!"take₂ {i}", pre := [holding i, second i], post := [eat i] },
        { name := s!"release {i}", pre := [eat i], post := [think i, fork i, fork ((i + 1) % n)] } ]
    init := (List.range n).flatMap (fun _ => [1, 0, 0]) ++ List.replicate n 1 }
'''

def run(root, name, stmt, tac, timeout=1800):
    out = os.path.join(root, 'bench', 'out')
    os.makedirs(out, exist_ok=True)
    tag = ''.join(ch for ch in tac if ch.isalnum())
    f = os.path.join(out, f'{name}_{tag}.lean')
    with open(f, 'w') as h:
        h.write(HEADER + f'\ntheorem t : {stmt} := by {tac}\n')
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.time()
    try:
        p = subprocess.run(['lake', 'env', 'lean', f], cwd=root, capture_output=True, text=True,
                           timeout=timeout)
        st = 'ok' if p.returncode == 0 and 'error' not in p.stdout else 'FAIL'
        msg = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        st, msg = 'timeout', ''
    wall = time.time() - t0
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
    # ru_maxrss of children is the largest child so far: run one benchmark per process
    rss = r1.ru_maxrss / 1024
    print(f'{name:<10} {tac:<28} {st:<7} wall {wall:7.1f} s  cpu {cpu:7.1f} s  rss {rss:7.0f} MB',
          flush=True)
    if st == 'FAIL':
        print('\n'.join(msg.splitlines()[:6]))

if __name__ == '__main__':
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    run(root, sys.argv[1], sys.argv[2], sys.argv[3])
