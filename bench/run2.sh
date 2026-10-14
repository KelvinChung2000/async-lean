#!/bin/bash
# usage: run2.sh DIR LABEL NAME "STATEMENT" TACTIC [timeout]
# Proves one goal in the checkout DIR and prints one row: label, goal, tactic, status, seconds.
export PATH=$HOME/.elan/bin:$PATH
dir=$1; label=$2; name=$3; stmt=$4; tac=$5; to=${6:-600}
mkdir -p $dir/bench/out
f=$dir/bench/out/${name}_$(echo $tac | tr -dc 'a-z_').lean
cat > $f <<EOT
import AsyncLean
open AsyncLean AsyncLean.Examples
set_option maxHeartbeats 0

/-- \`n\` processes meeting at a barrier: each starts, works (internal) and is done; the
barrier fires when all are done. -/
def benchBarrier (n : ℕ) : PNet where
  places := 3 * n
  trans := (List.range n).flatMap (fun i =>
      [{ name := "begin", pre := [3 * i], post := [3 * i + 1] },
       { name := "finish", pre := [3 * i + 1], post := [3 * i + 2], internal := true }]) ++
    [{ name := "barrier", pre := (List.range n).map (3 * · + 2), post := (List.range n).map (3 * ·) }]
  init := (List.range n).flatMap fun _ => [1, 0, 0]

theorem t : $stmt := by $tac
EOT
start=$(date +%s.%N)
out=$(cd $dir && timeout $to lake env lean $f 2>&1)
rc=$?
end=$(date +%s.%N)
el=$(echo "$end - $start" | bc)
if [ $rc -eq 0 ] && ! echo "$out" | grep -q "error"; then st=ok; elif [ $rc -eq 124 ]; then st=timeout; else st=FAIL; fi
printf "%-6s %-16s %-14s %-8s %7.1f\n" "$label" "$name" "$tac" "$st" "$el"
if [ "$st" = FAIL ]; then echo "$out" | grep -m2 error | cut -c1-200; fi
