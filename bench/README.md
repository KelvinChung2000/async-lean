# Benchmarks

Scripts behind the timings in the main README.

* `run2.sh DIR LABEL NAME "STATEMENT" TACTIC [timeout]` proves one goal in the checkout `DIR`
  and prints one row: label, goal, tactic, status (`ok`, `FAIL`, `timeout`) and wall-clock
  seconds. The time includes about 6 s of loading the library.
* `suite.sh` compares the original `async_decide` (a checkout of the base commit in `$OLD`)
  with the new `async_decide` and `async_bitmap` (a checkout of this branch in `$NEW`), on
  handshakes, barriers, FIFOs and dining philosophers:

  ```
  git worktree add ../bench-old 4324944 && (cd ../bench-old && lake build)
  git worktree add ../bench-new HEAD    && (cd ../bench-new && lake build)
  OLD=$PWD/../bench-old NEW=$PWD/../bench-new bench/suite.sh
  ```

  Run it on an otherwise idle machine: the goals are checked one after the other, each by a
  single Lean process.
* `external.sh` writes the same nets as PNML (`#export_pnml`) to `bench/pnml/` and runs LoLA
  and TAPAAL's `verifypn` on them if they are on the `PATH`, for a comparison with model
  checkers that produce no proof. Adjust the command lines to your installation.
* `parts.py NAME "STATEMENT" TACTIC` times one goal with `async_fast` (the fast explicit check
  `PNet.checkFast` as one kernel goal) or `async_fast (parts := k)` (the states cut into `k`
  key ranges, each its own kernel goal, glued by `Fast.checkPart_split`), and reports wall
  time, CPU time and peak memory.
* `xfile.py NET K JOBS` splits the same check across files (`Cert`, `Part0`…, `Glue`) and
  checks the parts with `JOBS` Lean processes at once.  Within one file the kernel checks
  declarations one after another, so files are the only way to check parts in parallel.

  Split versus whole on 4 cores, `Correct`, end to end (about 2.9 s and 1.9 GB of it is
  loading the library):

  | Goal | states | whole | 1 part | 16 parts | 16 files, 4 jobs |
  |---|---|---|---|---|---|
  | 6 handshakes | 4096 | 36 s, 4.1 GB | 35 s, 4.1 GB | 24 s, 2.1 GB | |
  | barrier of 8 | 6561 | 49–51 s, 4.6 GB | 48 s, 4.6 GB | 30–33 s, 2.1 GB | |
  | 7 handshakes | 16384 | 177 s, 12.8 GB | | 135 s, 2.7 GB | 63 s |
