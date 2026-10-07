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
