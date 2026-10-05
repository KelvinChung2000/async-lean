/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Petri
import AsyncLean.Petri.Invariant
import AsyncLean.AxiomAudit
import Mathlib.Data.Fin.VecNotation

/-!
# Example: buggy designs, certified counterexamples, and a fix

The three properties are genuinely different:

1. `lockOrder` — two processes taking two locks in opposite orders: **deadlocks**.
2. `retry` — a sender that may be refused and retry forever: deadlock free and live, yet it
   **livelocks** (an infinite run of internal retries).
3. `retryBounded` — the fix: a retry budget.  Livelock freedom now follows *structurally*
   from a linear ranking function (for every initial marking), and the design is fully
   correct.
4. `stuck` — a design that never deadlocks but in which one transition can never fire:
   it is **not live** (partial deadlock / starvation).

Each negative result is a *proof of the negation*, obtained from a counterexample trace that
is checked by the kernel.
-/

namespace AsyncLean.Examples

/-! ### 1. Deadlock: inconsistent lock ordering -/

/-- Places: `0`–`2` process P (idle, holds A, holds A and B), `3`–`5` process Q (idle,
holds B, holds B and A), `6` lock A, `7` lock B. -/
def lockOrder : PNet where
  places := 8
  trans := [
    { name := "P.takeA",   pre := [0, 6], post := [1] },
    { name := "P.takeB",   pre := [1, 7], post := [2] },
    { name := "P.release", pre := [2],    post := [0, 6, 7] },
    { name := "Q.takeB",   pre := [3, 7], post := [4] },
    { name := "Q.takeA",   pre := [4, 6], post := [5] },
    { name := "Q.release", pre := [5],    post := [3, 6, 7] }]
  init := [1, 0, 0, 1, 0, 0, 1, 1]

/-- P takes A, Q takes B: both wait forever. -/
theorem lockOrder_deadlocks : ¬ lockOrder.toNet.lts.DeadlockFree lockOrder.M₀ :=
  PNet.not_deadlockFree_of_refute (ts := [0, 3]) (by decide +kernel)

/-! ### 2. Livelock: unbounded retry -/

/-- Places: `0` idle, `1` waiting for a reply, `2` refused (will retry), `3` done.
The refusal `nack` and the retry `resend` are internal. -/
def retry : PNet where
  places := 4
  trans := [
    { name := "send",   pre := [0], post := [1] },
    { name := "nack",   pre := [1], post := [2], internal := true },
    { name := "resend", pre := [2], post := [1], internal := true },
    { name := "ack",    pre := [1], post := [3] },
    { name := "reset",  pre := [3], post := [0] }]
  init := [1, 0, 0, 0]

theorem retry_deadlockFree : retry.toNet.lts.DeadlockFree retry.M₀ :=
  PNet.deadlockFree_of_check (fuel := 100) (by decide +kernel)

theorem retry_live : retry.toNet.lts.Live retry.M₀ :=
  PNet.live_of_check (fuel := 100) (by decide +kernel)

/-- After `send`, the cycle `nack; resend` can repeat forever. -/
theorem retry_livelocks : ¬ retry.toNet.lts.LivelockFree retry.Internal retry.M₀ :=
  PNet.not_livelockFree_of_refute (ts := [0]) (cyc := [1, 2]) (by decide +kernel)

/-! ### 3. The fix: a retry budget -/

/-- As `retry`, plus `4` the remaining retry budget and `5` the spent budget, which is
refilled once the transfer is done. -/
abbrev retryBounded : PNet where
  places := 6
  trans := [
    { name := "send",   pre := [0],    post := [1] },
    { name := "nack",   pre := [1, 4], post := [2, 5], internal := true },
    { name := "resend", pre := [2],    post := [1], internal := true },
    { name := "ack",    pre := [1],    post := [3] },
    { name := "refill", pre := [3, 5], post := [3, 4] },
    { name := "reset",  pre := [3],    post := [0] }]
  init := [1, 0, 0, 0, 2, 0]

/-- **Structural** livelock freedom, for *every* initial marking: the weights
`(0, 0, 1, 0, 2, 0)` strictly decrease on both internal transitions. -/
theorem retryBounded_livelockFree_structural (M₀ : Marking (Fin 6)) :
    retryBounded.toNet.lts.LivelockFree retryBounded.Internal M₀ :=
  Net.livelockFree_of_linearRanking ![0, 0, 1, 0, 2, 0] (by decide +kernel) M₀

theorem retryBounded_correct : retryBounded.Correct :=
  PNet.correct_of_checkAll (fuel := 1000) (by decide +kernel)

/-! ### 4. Partial deadlock: deadlock free but not live -/

/-- A free-running oscillator (places `0`, `1`) next to a transition `t2` waiting on the
never-marked place `2`. -/
def stuck : PNet where
  places := 3
  trans := [
    { name := "t0", pre := [0], post := [1] },
    { name := "t1", pre := [1], post := [0] },
    { name := "t2", pre := [2], post := [0] }]
  init := [1, 0, 0]

theorem stuck_deadlockFree : stuck.toNet.lts.DeadlockFree stuck.M₀ :=
  PNet.deadlockFree_of_check (fuel := 100) (by decide +kernel)

theorem stuck_not_live : ¬ stuck.toNet.lts.Live stuck.M₀ :=
  fun h => PNet.not_liveLabel_of_refute (ts := []) (t := ⟨2, by decide⟩) (fuel := 100)
    (by decide +kernel) (h _)

#assert_standard_axioms lockOrder_deadlocks retry_deadlockFree retry_live retry_livelocks
  retryBounded_livelockFree_structural retryBounded_correct stuck_deadlockFree stuck_not_live

end AsyncLean.Examples
