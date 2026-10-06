/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
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
-/

namespace AsyncLean.Examples

theorem fifo40_deadlockFree :
    (fifo 40 "in" "out").toNet.lts.DeadlockFree (fifo 40 "in" "out").M₀ := by
  async_decide

theorem philosophers12_deadlockFree :
    (philosophers 12 true).toNet.lts.DeadlockFree (philosophers 12 true).M₀ := by
  async_decide

#assert_standard_axioms fifo40_deadlockFree philosophers12_deadlockFree

end AsyncLean.Examples
