#!/bin/bash
cd /home/user/async-lean
run() { bench/run.sh "$@"; }
for n in 10 20; do
  for tac in async_bitmap async_decide async_bdd; do run fifo${n}_correct "(fifo $n \"in\" \"out\").Correct" $tac 600; done
done
for n in 6 8 10; do
  for tac in async_bitmap async_decide async_bdd; do run phil${n}_correct "(philosophers $n true).Correct" $tac 600; done
done
for n in 8 10 12; do
  for tac in async_bitmap async_decide; do run phil${n}_dl "(philosophers $n true).toNet.lts.DeadlockFree (philosophers $n true).M₀" $tac 600; done
done
for n in 12; do
  for tac in async_bitmap async_decide async_bdd; do run hs${n}_correct "(handshakes $n).Correct" $tac 900; done
done
