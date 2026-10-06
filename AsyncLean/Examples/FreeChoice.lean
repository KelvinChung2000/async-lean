/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Auto.Structural
import AsyncLean.Petri.FreeChoiceNecessity
import AsyncLean.Examples.Compositional
import AsyncLean.Examples.Philosophers
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

/-! ### Refuting liveness

By the converse of Commoner's theorem (`Net.live_iff_siphonTrap`), a free-choice net in which
some siphon contains no initially marked trap is *not* live.  Here a request either completes
(`a`, then `c` returns to the start) or leaks into a sink (`b`): the siphon `{0, 1}` contains
no trap at all. -/

def leak : Net (Fin 3) (Fin 3) where
  pre := ![![1, 0, 0], ![1, 0, 0], ![0, 1, 0]]
  post := ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]

theorem leak_not_live : ¬ leak.lts.Live ![1, 0, 0] := by
  rw [Net.live_iff_siphonTrap (by decide) (by decide) (by decide)]
  decide

/-! ### Larger nets

The siphon–trap property is checked from a branching certificate on bit masks, not by
enumerating subsets of places, so nets far beyond explicit state exploration are in reach. -/

/-- A 20-stage FIFO (40 places, about a million reachable markings) is live. -/
theorem fifo20_live : (fifo 20 "in" "out").toNet.lts.Live (fifo 20 "in" "out").M₀ := by
  async_structural

/-- Eight dining philosophers with resource ordering (32 places) never deadlock: the
siphon–trap theorem for ordinary nets, which need not be free choice. -/
theorem philosophers8_deadlockFree :
    (philosophers 8 true).toNet.lts.DeadlockFree (philosophers 8 true).M₀ := by
  async_structural

/-- A ring of `k` stages, each forking into a free choice between `a` and `b` in parallel with
a second branch, joined before the next stage.  It has `2 ^ k` minimal siphons, so siphon–trap
certificates grow exponentially (the property is co-NP-complete in general). -/
def fcRing (k : ℕ) : PNet where
  places := 4 * k
  trans := (List.range k).flatMap fun i =>
    let c := 4 * i; let p := 4 * i + 1; let q := 4 * i + 2; let s := 4 * i + 3
    let c' := 4 * ((i + 1) % k)
    [ { name := s!"fork{i}", pre := [c], post := [p, q] },
      { name := s!"a{i}", pre := [p], post := [s] },
      { name := s!"b{i}", pre := [p], post := [s] },
      { name := s!"join{i}", pre := [s, q], post := [c'] } ]
  init := (List.range (4 * k)).map fun j => if j = 0 then 1 else 0

/-- `async_structural` gives up on the certificate once it exceeds its size budget and
falls back on the (here small) state space. -/
theorem fcRing20_live : (fcRing 20).toNet.lts.Live (fcRing 20).M₀ := by
  async_structural

#assert_standard_axioms ctrl_live ctrl_deadlockFree leak_not_live fifo20_live
  philosophers8_deadlockFree fcRing20_live

end AsyncLean.Examples.FreeChoice
