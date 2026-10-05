/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
import AsyncLean.AxiomAudit

/-!
# Example: dining philosophers with `async_decide`

`n` philosophers share `n` forks.  Philosopher `i` takes a first fork, then a second, eats,
and releases both.

* `philosophers n false` : everybody takes the left fork first — the classic deadlock.
* `philosophers n true` : the last philosopher takes the forks in the opposite order — the
  resource-ordering fix.

The `async_decide` tactic proves the fixed design correct; for the broken one it reports a
counterexample, which a refutation theorem turns into a proof of the negation.
-/

namespace AsyncLean.Examples

/-- Places `3i`, `3i+1`, `3i+2`: philosopher `i` thinking / holding one fork / eating;
place `3n+j`: fork `j` on the table. -/
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

/-- With resource ordering, five philosophers never deadlock, never starve, and never
livelock. -/
theorem philosophers_correct : (philosophers 5 true).Correct := by
  async_decide

/-- Without it, they deadlock when everybody holds one fork. -/
theorem philosophers_deadlock :
    ¬ (philosophers 5 false).toNet.lts.DeadlockFree (philosophers 5 false).M₀ :=
  PNet.not_deadlockFree_of_refute (ts := [0, 3, 6, 9, 12]) (by decide +kernel)

-- The counterexample search behind `async_decide`'s error message:
/--
info: "DEADLOCK reachable by firing [take₁ 0(#0), take₁ 1(#3), take₁ 2(#6)].\nProve it with: PNet.not_deadlockFree_of_refute (ts := [0, 3, 6]) (by decide +kernel)"
-/
#guard_msgs in
#eval (philosophers 3 false).diagnose

#assert_standard_axioms philosophers_correct philosophers_deadlock

end AsyncLean.Examples
