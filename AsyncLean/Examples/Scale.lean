/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Auto.Structural
import AsyncLean.Examples.Philosophers
import AsyncLean.Examples.Compositional
import AsyncLean.AxiomAudit

/-!
# Example: deadlock freedom at scale, by partial-order reduction

For a deadlock-freedom goal, `async_decide` explores a *reduced* state space: at each
marking only the enabled transitions of a stubborn set fire (`Net.Stubborn`), and the
kernel checks, marking by marking, that the sets are stubborn.  `Net.reachable_red_of_dead`
shows that every reachable deadlock is then reachable in the reduced state space, so a
reduced state space without deadlocks proves the whole net deadlock free.

* A 40-stage FIFO has `2^40` reachable markings; the reduced state space has 821.
* Twelve dining philosophers (resource ordering) have 33 461 reachable markings; the reduced
  state space has 245.

`async_structural` proves the same kind of result without exploring any state: every
reachable marking satisfies the state equation `M = M₀ + C · x`, and a Farkas certificate
found by linear programming shows that no solution of it is dead
(`Net.deadlockFree_of_stateEq`).  The bounds that the argument needs come from place
invariants, all checked at once by packing them into one number per place
(`PNet.bounded_of_checkPInv`).
-/

namespace AsyncLean.Examples

theorem fifo40_deadlockFree :
    (fifo 40 "in" "out").toNet.lts.DeadlockFree (fifo 40 "in" "out").M₀ := by
  async_decide

theorem philosophers12_deadlockFree :
    (philosophers 12 true).toNet.lts.DeadlockFree (philosophers 12 true).M₀ := by
  async_decide

/-- The same, from the state equation: no state is explored. -/
theorem philosophers12_deadlockFree' :
    (philosophers 12 true).toNet.lts.DeadlockFree (philosophers 12 true).M₀ := by
  async_structural

/-- Safeness of the 40-stage FIFO from 40 place invariants, checked together. -/
theorem fifo40_safe : (fifo 40 "in" "out").Safe := by
  async_structural

#assert_standard_axioms fifo40_deadlockFree philosophers12_deadlockFree
  philosophers12_deadlockFree' fifo40_safe

end AsyncLean.Examples
