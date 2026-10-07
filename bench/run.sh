#!/bin/bash
# usage: run.sh NAME "THEOREM STATEMENT" TACTIC [timeout]
export PATH=$HOME/.elan/bin:$PATH
name=$1; stmt=$2; tac=$3; to=${4:-600}
f=bench/out/$name.lean
mkdir -p bench/out
cat > $f <<EOT
import AsyncLean
open AsyncLean AsyncLean.Examples
set_option maxHeartbeats 0
theorem t : $stmt := by $tac
EOT
start=$(date +%s.%N)
out=$(timeout $to lake env lean $f 2>&1)
rc=$?
end=$(date +%s.%N)
el=$(echo "$end - $start" | bc)
if [ $rc -eq 0 ] && ! echo "$out" | grep -q "error"; then st=ok; elif [ $rc -eq 124 ]; then st=timeout; else st=FAIL; fi
printf "%-28s %-14s %-8s %6.1fs\n" "$name" "$tac" "$st" "$el"
if [ "$st" = FAIL ]; then echo "$out" | grep -m3 error; fi
