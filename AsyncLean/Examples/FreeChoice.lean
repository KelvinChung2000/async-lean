/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Auto.Structural
import AsyncLean.AxiomAudit
import Mathlib.Data.Fin.VecNotation

/-!
# Example: liveness of a free-choice controller by Commoner's theorem

A request forks into an acknowledgement branch and a *choice* between two operations `A` and
`B` (resolved by the environment, hence free choice); both branches join before the next
request.  The net is neither a marked graph (it has a choice) nor a state machine (it has a
fork), so neither of the simpler structural theorems applies; Commoner's free-choice theorem
proves it live without exploring its state space.

Places: `0` idle, `1` choice, `2` ack pending, `3` doing A, `4` doing B, `5` done.
Transitions: `0` req (`0 → 1, 2`), `1` pickA (`1 → 3`), `2` pickB (`1 → 4`),
`3` doA (`3 → 5`), `4` doB (`4 → 5`), `5` join (`5, 2 → 0`).
-/

namespace AsyncLean.Examples.FreeChoice

def ctrl : Net (Fin 6) (Fin 6) where
  pre := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]]
  post := ![![0, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]]

def ctrlInit : Marking (Fin 6) := ![1, 0, 0, 0, 0, 0]

theorem ctrl_freeChoice : ctrl.Ordinary ∧ ctrl.FreeChoice := by decide

/-- Every transition can always fire again. -/
theorem ctrl_live : ctrl.lts.Live ctrlInit := by async_structural

theorem ctrl_deadlockFree : ctrl.lts.DeadlockFree ctrlInit := by async_structural

/-- The same controller with a *non*-free choice: `pickB` also needs the ack-pending token,
which it does not consume.  The net is no longer free choice, so Commoner's theorem does not
apply to it (use `async_decide` on a `PNet` version instead). -/
def ctrlNFC : Net (Fin 6) (Fin 6) where
  pre := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]]
  post := ![![0, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]]

theorem ctrlNFC_not_freeChoice : ¬ ctrlNFC.FreeChoice := by decide

#assert_standard_axioms ctrl_live ctrl_deadlockFree

end AsyncLean.Examples.FreeChoice
