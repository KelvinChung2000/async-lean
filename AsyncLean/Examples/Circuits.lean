/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Circuit.Basic
import AsyncLean.Checker.Tactic
import AsyncLean.AxiomAudit

/-!
# Example: gate-level netlists

1. A ring of five Muller C-elements (a self-timed ring / Muller pipeline in a loop), each
   stage computing `cᵢ := C(cᵢ₋₁, ¬cᵢ₊₁)`.  With one token it is proved deadlock free,
   livelock free (the three middle stages are internal), live, and speed independent
   (hazard free).
2. The same ring started with no token is proved to deadlock.
3. An AND gate whose input may be withdrawn before the gate switches is proved to have a
   hazard (it is not speed independent).
-/

namespace AsyncLean.Examples

open BExpr

/-- Muller C-element ring of five stages with signal `i` driven by stage `i`. -/
def cRing (init : List Bool) : Circuit where
  signals := 5
  gates := [
    { name := "c0", out := 0, fn := celemInv 4 1 0 },
    { name := "c1", out := 1, fn := celemInv 0 2 1, internal := true },
    { name := "c2", out := 2, fn := celemInv 1 3 2, internal := true },
    { name := "c3", out := 3, fn := celemInv 2 4 3, internal := true },
    { name := "c4", out := 4, fn := celemInv 3 0 4 }]
  init := init

/-- With one token, the ring runs forever: no deadlock, no livelock, every stage live. -/
theorem cRing_correct : (cRing [true, false, false, false, false]).Correct :=
  Circuit.correct_of_checkAll (fuel := 1000) (by decide +kernel)

/-- ... and it is speed independent: correct for arbitrary gate delays. -/
theorem cRing_speedIndependent : (cRing [true, false, false, false, false]).SpeedIndependent :=
  Circuit.speedIndependent_of_check (fuel := 1000) (by decide +kernel)

/-- Without a token every stage is stable: the ring deadlocks immediately. -/
theorem cRing_empty_deadlocks :
    ¬ (cRing [false, false, false, false, false]).lts.DeadlockFree
      (cRing [false, false, false, false, false]).s₀ :=
  Circuit.not_deadlockFree_of_refute (gs := []) (by decide +kernel)

/-- An environment toggling `a` (signal 0), a constant `b` (signal 1) and `z := a ∧ b`
(signal 2). -/
def glitchy : Circuit where
  signals := 3
  gates := [
    { name := "env", out := 0, fn := inv 0 },
    { name := "b",   out := 1, fn := const true },
    { name := "and", out := 2, fn := and (var 0) (var 1) }]
  init := [false, true, false]

/-- After `a` rises, the AND gate is excited, but `a` may fall again before it switches:
a hazard. -/
theorem glitchy_hazard : ¬ glitchy.SpeedIndependent :=
  Circuit.not_speedIndependent_of_refute (gs := [0]) (g := ⟨2, by decide⟩) (g' := ⟨0, by decide⟩)
    (by decide +kernel)

/-! The same results with the `async_decide` tactic (certificate computed at elaboration time,
checked by the kernel). -/

theorem cRing_correct' : (cRing [true, false, false, false, false]).Correct := by
  async_decide

theorem cRing_speedIndependent' :
    (cRing [true, false, false, false, false]).SpeedIndependent := by
  async_decide

theorem cRing_deadlockFree' :
    (cRing [true, false, false, false, false]).lts.DeadlockFree
      (cRing [true, false, false, false, false]).s₀ := by
  async_decide

/--
info: "HAZARD: after firing [env(#0)], firing env(#0) disables the excited gate and(#2).\nProve it with: Circuit.not_speedIndependent_of_refute (gs := [0]) (g := ⟨2, by decide⟩) (g' := ⟨0, by decide⟩) (by decide +kernel)"
-/
#guard_msgs in
#eval glitchy.diagnoseSpeedIndependent

#assert_standard_axioms cRing_correct cRing_speedIndependent cRing_empty_deadlocks glitchy_hazard
  cRing_correct' cRing_speedIndependent' cRing_deadlockFree'

end AsyncLean.Examples
