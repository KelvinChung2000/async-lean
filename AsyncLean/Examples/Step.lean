/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.Step
import AsyncLean.Circuit.Step
import AsyncLean.Examples.Arbiter
import AsyncLean.Examples.Circuits

/-!
# Example: concurrent firing

1. The arbiter net is correct when any number of enabled transitions fire at once.
2. The C-element ring is correct when any set of excited gates switches at once, because it
   is speed independent.
3. Two cross-coupled inverters started at `00` race.  Switching one at a time, the first to
   switch wins and the circuit stops; switching both together reaches `11`, which no
   interleaving reaches.  The circuit is not speed independent, so the step semantics need
   not agree with the interleaving one, and here it does not.
-/

namespace AsyncLean.Examples

open BExpr

/-- The arbiter is deadlock free, livelock free and live under concurrent firing. -/
theorem arbiter_stepCorrect :
    arbiter.toNet.stepLts.DeadlockFree arbiter.M₀ ∧
      arbiter.toNet.stepLts.LivelockFree (Net.StepInternal arbiter.Internal) arbiter.M₀ ∧
      arbiter.toNet.StepLive arbiter.M₀ := by
  obtain ⟨hd, hl, hv⟩ := arbiter_correct
  exact ⟨Net.stepLts_deadlockFree_iff.2 hd, Net.stepLts_livelockFree_iff.2 hl,
    Net.stepLive_iff.2 hv⟩

/-- The C-element ring is correct under simultaneous switching. -/
theorem cRing_stepCorrect : (cRing [true, false, false, false, false]).StepCorrect :=
  (Circuit.correct_iff_stepCorrect cRing_speedIndependent).1 cRing_correct

/-- Two cross-coupled inverters, `a := ¬b` and `b := ¬a`, both low. -/
def race : Circuit where
  signals := 2
  gates := [{ name := "a", out := 0, fn := inv 1 }, { name := "b", out := 1, fn := inv 0 }]
  init := [false, false]

theorem race_hazard : ¬ race.SpeedIndependent :=
  Circuit.not_speedIndependent_of_refute (gs := []) (g := ⟨1, by decide⟩) (g' := ⟨0, by decide⟩)
    (by decide +kernel)

/-- Switching both inverters together reaches `11`... -/
theorem race_step_reaches : race.stepLts.Reachable race.s₀ (fun _ => true) := by
  refine LTS.Reachable.of_step (l := Finset.univ)
    ⟨⟨⟨⟨0, by decide⟩, Finset.mem_univ _⟩, ?_, ?_⟩, ?_⟩
  · simp only [Circuit.Excited]; decide
  · decide
  · funext j; revert j; decide

/-- ... which no interleaving reaches. -/
theorem race_not_reaches : ¬ race.lts.Reachable race.s₀ (fun _ => true) := by
  intro h
  let I : (Fin race.signals → Bool) → Prop := fun s =>
    ¬ (s ⟨0, by decide⟩ = true ∧ s ⟨1, by decide⟩ = true)
  have key : ∀ s g, I s → race.Excited s g → I (race.fire s g) := by
    simp only [I, Circuit.Excited]; decide
  have := h.invariant (I := I) (by decide) fun s g s' hs ⟨hex, he⟩ => he ▸ key s g hs hex
  exact this ⟨rfl, rfl⟩

#assert_standard_axioms arbiter_stepCorrect cRing_stepCorrect race_hazard race_step_reaches
  race_not_reaches

end AsyncLean.Examples
