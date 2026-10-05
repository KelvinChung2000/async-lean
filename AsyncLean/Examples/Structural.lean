/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Auto.Structural
import AsyncLean.Examples.Arbiter
import AsyncLean.Examples.Counterexamples
import AsyncLean.Examples.Compositional
import AsyncLean.AxiomAudit
import Mathlib.Data.Fin.VecNotation

/-!
# Example: automatic structural proofs

`async_structural` proves properties without exploring states, so it scales to designs far
beyond explicit model checking.
-/

namespace AsyncLean.Examples.Structural

/-- The arbiter is 1-safe, by place invariants found by linear programming. -/
theorem arbiter_safe' : arbiter.Safe := by async_structural

/-- The bounded-retry protocol is livelock free *from every initial marking*, by a linear
ranking function found by linear programming. -/
theorem retryBounded_livelockFree (M₀ : Marking (Fin 6)) :
    retryBounded.toNet.lts.LivelockFree retryBounded.Internal M₀ := by
  async_structural

/-- A 20-stage FIFO has more than a million reachable markings; it is nevertheless proved
1-safe and livelock free instantly. -/
theorem fifo20_safe : (fifo 20 "in" "out").Safe := by async_structural

theorem fifo20_livelockFree :
    (fifo 20 "in" "out").toNet.lts.LivelockFree (fifo 20 "in" "out").Internal
      (fifo 20 "in" "out").M₀ := by
  async_structural

/-- A four-stage Muller ring with two tokens, as a marked graph: forward places `0 … 3`
(stage `i` to `i+1`), backward places `4 … 7`. -/
def ring4 : MarkedGraph (Fin 8) (Fin 4) where
  src := ![0, 1, 2, 3, 1, 2, 3, 0]
  dst := ![1, 2, 3, 0, 0, 1, 2, 3]

def ring4Init : Marking (Fin 8) := ![1, 1, 0, 0, 0, 0, 1, 1]

theorem ring4_live : ring4.toNet.lts.Live ring4Init := by async_structural
theorem ring4_deadlockFree : ring4.toNet.lts.DeadlockFree ring4Init := by async_structural

#assert_standard_axioms arbiter_safe' retryBounded_livelockFree fifo20_safe fifo20_livelockFree
  ring4_live ring4_deadlockFree

end AsyncLean.Examples.Structural
