#!/bin/bash
# Compare the original async_decide (checkout in $OLD) with the new one and async_bitmap
# (checkout in $NEW).  Times include about 6 s of loading the library.
OLD=${OLD:-/home/user/bench-old}
NEW=${NEW:-/home/user/bench-new}
R=$(dirname $0)/run2.sh
goal() {  # name statement
  $R $OLD old "$1" "$2" async_decide ${TO:-600}
  $R $NEW new "$1" "$2" async_decide ${TO:-600}
  $R $NEW new "$1" "$2" async_bitmap ${TO:-600}
}
for n in 6 8 10 12; do goal hs${n} "(handshakes $n).Correct"; done
for n in 8 10 12; do goal barrier${n} "(benchBarrier $n).Correct"; done
for n in 10 20 30; do goal fifo${n} "(fifo $n \"in\" \"out\").Correct"; done
for n in 6 8 10; do goal phil${n} "(philosophers $n true).Correct"; done
for n in 10 12; do goal phil${n}_dl "(philosophers $n true).toNet.lts.DeadlockFree (philosophers $n true).M₀"; done
