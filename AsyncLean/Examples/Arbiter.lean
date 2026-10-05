/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Petri
import AsyncLean.Petri.Invariant
import AsyncLean.AxiomAudit
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Example: concrete designs verified by the kernel-checked model checker

1. A four-phase handshake channel whose consumer performs internal (silent) computation.
2. A two-client mutual-exclusion element (arbiter) with internal grant decisions.

For each design we prove `PNet.Correct` — deadlock freedom, livelock freedom and liveness of
every transition — by running the verified checker in the kernel (`decide +kernel`).  For
the arbiter we additionally prove the safety property *mutual exclusion* structurally, by a
place invariant.
-/

namespace AsyncLean.Examples

/-! ### 1. Four-phase handshake with internal computation -/

/-- Places: `0` idle, `1` request received, `2` result computed, `3` acknowledged,
`4` request withdrawn. -/
def handshake : PNet where
  places := 5
  trans := [
    { name := "req+",    pre := [0], post := [1] },
    { name := "compute", pre := [1], post := [2], internal := true },
    { name := "ack+",    pre := [2], post := [3] },
    { name := "req-",    pre := [3], post := [4] },
    { name := "ack-",    pre := [4], post := [0] }]
  init := [1, 0, 0, 0, 0]

theorem handshake_correct : handshake.Correct :=
  PNet.correct_of_checkAll (fuel := 1000) (by decide +kernel)

/-! ### 2. A mutual-exclusion element -/

/-- Places: `0` client 1 idle, `1` client 1 requesting, `2` client 1 in critical section,
`3`–`5` the same for client 2, `6` the shared resource (mutex token).
The grants `g1`, `g2` are internal arbitration decisions. -/
abbrev arbiter : PNet where
  places := 7
  trans := [
    { name := "r1+", pre := [0],    post := [1] },
    { name := "g1",  pre := [1, 6], post := [2], internal := true },
    { name := "r1-", pre := [2],    post := [0, 6] },
    { name := "r2+", pre := [3],    post := [4] },
    { name := "g2",  pre := [4, 6], post := [5], internal := true },
    { name := "r2-", pre := [5],    post := [3, 6] }]
  init := [1, 0, 0, 1, 0, 0, 1]

/-- The arbiter never deadlocks, never livelocks, and never starves a client. -/
theorem arbiter_correct : arbiter.Correct :=
  PNet.correct_of_checkAll (fuel := 1000) (by decide +kernel)

/-- `cs₁ + cs₂ + mutex` is a place invariant. -/
theorem arbiter_pinv : arbiter.toNet.IsPInvariant ![0, 0, 1, 0, 0, 1, 1] := by
  decide +kernel

/-- **Mutual exclusion**: the two clients are never in their critical sections together. -/
theorem arbiter_mutex {M : Marking (Fin 7)} (hr : arbiter.toNet.lts.Reachable arbiter.M₀ M) :
    M 2 + M 5 ≤ 1 := by
  have h := arbiter_pinv.weight_reachable hr
  simp only [Net.weight, Fin.sum_univ_seven] at h
  simp at h
  have e₂ : arbiter.M₀ 2 = 0 := rfl
  have e₅ : arbiter.M₀ 5 = 0 := rfl
  have e₆ : arbiter.M₀ 6 = 1 := rfl
  rw [e₂, e₅, e₆] at h
  omega

#assert_standard_axioms handshake_correct arbiter_correct arbiter_mutex

end AsyncLean.Examples
