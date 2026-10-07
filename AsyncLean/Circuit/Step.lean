/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Circuit.Basic
import Mathlib.Data.Finset.Card

/-!
# Simultaneous switching of gates

Muller's semantics `Circuit.lts` switches one excited gate at a time.  Real gates switch
concurrently: in the *step* semantics `Circuit.stepLts` any non-empty set of excited gates
driving distinct signals switches at once, each gate taking the value its function had
before the step.

For a **speed-independent** circuit the two semantics agree
(`Circuit.stepLts_reachable_iff`): every simultaneous switch can be replayed one gate at a
time, because switching one gate never disables another excited gate.  Consequently
deadlock freedom, livelock freedom and liveness are the same in both semantics
(`Circuit.correct_iff_stepCorrect`).  Without speed independence this fails: switching two
gates together can reach a state that no interleaving reaches — precisely the hazards that
speed independence excludes.
-/

namespace AsyncLean

namespace Circuit

variable (C : Circuit)

/-- The set of gates `G` can switch together in `s`: it is non-empty, every gate in it is
excited, and no two gates drive the same signal. -/
def StepEnabled (s : Fin C.signals → Bool) (G : Finset (Fin C.gates.length)) : Prop :=
  G.Nonempty ∧ (∀ g ∈ G, C.Excited s g) ∧
    ∀ g ∈ G, ∀ g' ∈ G, (C.gate g).out = (C.gate g').out → g = g'

/-- All the gates of `G` switch at once.  An excited gate switches to the value of its
function, which is the negation of its current output (`fire_eq_of_excited`). -/
def fireSet (s : Fin C.signals → Bool) (G : Finset (Fin C.gates.length)) :
    Fin C.signals → Bool :=
  fun j => if ∃ g ∈ G, (C.gate g).out = j.val then !s j else s j

/-- Step semantics: labels are sets of gates switching together. -/
def stepLts : LTS (Fin C.signals → Bool) (Finset (Fin C.gates.length)) where
  step s G s' := C.StepEnabled s G ∧ s' = C.fireSet s G

/-- A step is internal when all its gates are. -/
def StepInternal (G : Finset (Fin C.gates.length)) : Prop := ∀ g ∈ G, C.Internal g

/-- Liveness in the step semantics: every gate can always eventually switch again. -/
def StepLive : Prop :=
  ∀ g s, C.stepLts.Reachable C.s₀ s →
    ∃ s', C.stepLts.Reachable s s' ∧ ∃ G, g ∈ G ∧ C.stepLts.Enabled s' G

/-- Correctness in the step semantics. -/
def StepCorrect : Prop :=
  C.stepLts.DeadlockFree C.s₀ ∧ C.stepLts.LivelockFree C.StepInternal C.s₀ ∧ C.StepLive

variable {C}

theorem lts_enabled_iff {s : Fin C.signals → Bool} {g : Fin C.gates.length} :
    C.lts.Enabled s g ↔ C.Excited s g :=
  ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

theorem fire_eq_of_excited {s : Fin C.signals → Bool} {g : Fin C.gates.length}
    (h : C.Excited s g) :
    C.fire s g = fun j => if j.val = (C.gate g).out then !s j else s j := by
  funext j
  simp only [fire]
  split
  · rename_i hj
    have hv : C.val s (C.gate g).out = s j := by
      simp only [val, ← hj, j.isLt, ↓reduceDIte]
    unfold Excited at h
    rw [hv] at h
    revert h; cases (C.gate g).fn.eval (C.val s) <;> cases s j <;> simp
  · rfl

theorem fireSet_singleton {s : Fin C.signals → Bool} {g : Fin C.gates.length}
    (h : C.Excited s g) : C.fireSet s {g} = C.fire s g := by
  rw [fire_eq_of_excited h]
  funext j
  simp only [fireSet, Finset.mem_singleton, exists_eq_left]
  by_cases hj : (C.gate g).out = j.val
  · simp [hj]
  · simp [hj, Ne.symm hj]

theorem stepLts_step_single {s s' : Fin C.signals → Bool} {g : Fin C.gates.length}
    (h : C.lts.step s g s') : C.stepLts.step s {g} s' :=
  ⟨⟨⟨g, Finset.mem_singleton_self g⟩, by simpa using h.1, by simp⟩,
    h.2.trans (fireSet_singleton h.1).symm⟩

theorem fireSet_fire {s : Fin C.signals → Bool} {G : Finset (Fin C.gates.length)}
    {g : Fin C.gates.length} (hg : g ∈ G) (hex : C.Excited s g)
    (hd : ∀ g ∈ G, ∀ g' ∈ G, (C.gate g).out = (C.gate g').out → g = g') :
    C.fireSet (C.fire s g) (G.erase g) = C.fireSet s G := by
  rw [fire_eq_of_excited hex]
  funext j
  simp only [fireSet, Finset.mem_erase]
  by_cases hj : j.val = (C.gate g).out
  · have h1 : ¬ ∃ g', (g' ≠ g ∧ g' ∈ G) ∧ (C.gate g').out = j.val := by
      rintro ⟨g', ⟨hne, hg'⟩, ho⟩
      exact hne (hd g' hg' g hg (ho.trans hj))
    have h2 : ∃ g' ∈ G, (C.gate g').out = j.val := ⟨g, hg, hj.symm⟩
    simp only [hj] at h1 h2 ⊢
    simp only [h1, h2, ↓reduceIte]
  · have : (∃ g', (g' ≠ g ∧ g' ∈ G) ∧ (C.gate g').out = j.val) ↔
        ∃ g' ∈ G, (C.gate g').out = j.val := by
      constructor
      · rintro ⟨g', ⟨-, hg'⟩, ho⟩; exact ⟨g', hg', ho⟩
      · rintro ⟨g', hg', ho⟩
        refine ⟨g', ⟨?_, hg'⟩, ho⟩
        rintro rfl; exact hj ho.symm
    simp only [this, hj, ↓reduceIte]

theorem fireSet_empty (s : Fin C.signals → Bool) : C.fireSet s ∅ = s := by
  funext j; simp [fireSet]

/-- **Replaying a simultaneous switch one gate at a time.**  In a speed-independent circuit,
switching a set of excited gates together reaches the same state as switching them one after
the other. -/
theorem transGen_of_stepEnabled (hsi : C.SpeedIndependent) {Q : Fin C.gates.length → Prop} :
    ∀ (n : ℕ) (G : Finset (Fin C.gates.length)) (s : Fin C.signals → Bool), G.card = n →
      C.lts.Reachable C.s₀ s → C.StepEnabled s G → (∀ g ∈ G, Q g) →
      Relation.TransGen (fun s s' => ∃ g, Q g ∧ C.lts.step s g s') s (C.fireSet s G) := by
  intro n
  induction n with
  | zero =>
    intro G s hn _ hen
    exact absurd (Finset.card_pos.2 hen.1) (by omega)
  | succ n ih =>
    intro G s hn hs ⟨⟨g, hg⟩, hex, hd⟩ hQ
    have hstep : C.lts.step s g (C.fire s g) := ⟨hex g hg, rfl⟩
    have hs' : C.lts.Reachable C.s₀ (C.fire s g) := hs.tail ⟨g, hstep⟩
    rw [← fireSet_fire hg (hex g hg) hd]
    by_cases hG : (G.erase g).Nonempty
    · refine .head ⟨g, hQ g hg, hstep⟩ (ih _ _ ?_ hs' ⟨hG, fun g' hg' => ?_, ?_⟩ ?_)
      · rw [Finset.card_erase_of_mem hg]; omega
      · obtain ⟨hne, hg''⟩ := Finset.mem_erase.1 hg'
        exact lts_enabled_iff.1
          (hsi s hs g' g _ hne (lts_enabled_iff.2 (hex g' hg'')) hstep)
      · exact fun a ha b hb => hd a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
      · exact fun a ha => hQ a (Finset.mem_of_mem_erase ha)
    · rw [Finset.not_nonempty_iff_eq_empty.1 hG, fireSet_empty]
      exact .single ⟨g, hQ g hg, hstep⟩

theorem reachable_fireSet (hsi : C.SpeedIndependent) {s : Fin C.signals → Bool}
    {G : Finset (Fin C.gates.length)} (hs : C.lts.Reachable C.s₀ s) (hen : C.StepEnabled s G) :
    C.lts.Reachable s (C.fireSet s G) :=
  (Relation.TransGen.mono (fun _ _ ⟨g, _, h⟩ => ⟨g, h⟩) _ _
    (transGen_of_stepEnabled hsi (Q := fun _ => True) _ G s rfl hs hen fun _ _ => trivial)
    ).to_reflTransGen

theorem stepLts_reachable_of_reachable {s s' : Fin C.signals → Bool}
    (h : C.lts.Reachable s s') : C.stepLts.Reachable s s' :=
  Relation.ReflTransGen.mono (fun _ _ ⟨_, hst⟩ => ⟨_, stepLts_step_single hst⟩) _ _ h

theorem reachable_of_stepLts_reachable (hsi : C.SpeedIndependent) {s s' : Fin C.signals → Bool}
    (hs : C.lts.Reachable C.s₀ s) (h : C.stepLts.Reachable s s') : C.lts.Reachable s s' := by
  induction h with
  | refl => exact LTS.Reachable.refl _
  | tail _ hst ih =>
    obtain ⟨G, hen, rfl⟩ := hst
    exact ih.trans (reachable_fireSet hsi (hs.trans ih) hen)

/-- **For a speed-independent circuit, simultaneous switching reaches exactly the states of
Muller's interleaving semantics.** -/
theorem stepLts_reachable_iff (hsi : C.SpeedIndependent) {s : Fin C.signals → Bool} :
    C.stepLts.Reachable C.s₀ s ↔ C.lts.Reachable C.s₀ s :=
  ⟨reachable_of_stepLts_reachable hsi (LTS.Reachable.refl _), stepLts_reachable_of_reachable⟩

theorem stepLts_isDeadlock_iff {s : Fin C.signals → Bool} :
    C.stepLts.IsDeadlock s ↔ C.lts.IsDeadlock s := by
  constructor
  · intro h g s' hst; exact h _ _ (stepLts_step_single hst)
  · rintro h G s' ⟨⟨⟨g, hg⟩, hex, -⟩, -⟩
    exact h g _ ⟨hex g hg, rfl⟩

theorem stepLts_deadlockFree_iff (hsi : C.SpeedIndependent) :
    C.stepLts.DeadlockFree C.s₀ ↔ C.lts.DeadlockFree C.s₀ := by
  simp only [LTS.DeadlockFree, stepLts_reachable_iff hsi, stepLts_isDeadlock_iff]

theorem stepLts_livelockFree_iff (hsi : C.SpeedIndependent) :
    C.stepLts.LivelockFree C.StepInternal C.s₀ ↔ C.lts.LivelockFree C.Internal C.s₀ := by
  simp only [LTS.livelockFree_iff_acc, stepLts_reachable_iff hsi]
  constructor
  · intro h s hs
    refine Subrelation.accessible (fun {a b} ⟨g, hg, hst⟩ => ?_) (h s hs)
    exact ⟨{g}, by simpa [StepInternal] using hg, stepLts_step_single hst⟩
  · intro h s hs
    have key : ∀ s, Acc (Relation.TransGen (C.lts.IRel C.Internal)) s →
        C.lts.Reachable C.s₀ s → Acc (C.stepLts.IRel C.StepInternal) s := by
      intro s hacc
      induction hacc with
      | intro s _ ih =>
        intro hs
        refine Acc.intro s fun s' ⟨G, hG, hen, he⟩ => ?_
        have ht := transGen_of_stepEnabled hsi _ G s rfl hs hen hG
        rw [← he] at ht
        exact ih s' (Relation.TransGen.swap _ _ ht)
          (hs.trans (Relation.TransGen.mono (fun _ _ ⟨g, _, h⟩ => ⟨g, h⟩) _ _ ht).to_reflTransGen)
    exact key s (h s hs).transGen hs

theorem stepLts_enabled_iff {s : Fin C.signals → Bool} {g : Fin C.gates.length} :
    (∃ G, g ∈ G ∧ C.stepLts.Enabled s G) ↔ C.lts.Enabled s g := by
  constructor
  · rintro ⟨G, hg, _, ⟨-, hex, -⟩, -⟩
    exact lts_enabled_iff.2 (hex g hg)
  · rintro ⟨s', hst⟩
    exact ⟨{g}, Finset.mem_singleton_self g, s', stepLts_step_single hst⟩

theorem stepLive_iff (hsi : C.SpeedIndependent) : C.StepLive ↔ C.lts.Live C.s₀ := by
  simp only [StepLive, LTS.Live, LTS.LiveLabel, stepLts_reachable_iff hsi, stepLts_enabled_iff]
  refine forall_congr' fun g => forall₂_congr fun s hs => ?_
  constructor
  · rintro ⟨s', hss', hen⟩
    exact ⟨s', reachable_of_stepLts_reachable hsi hs hss', hen⟩
  · rintro ⟨s', hss', hen⟩
    exact ⟨s', stepLts_reachable_of_reachable hss', hen⟩

/-- **Correctness does not depend on the switching semantics** for a speed-independent
circuit: deadlock freedom, livelock freedom and liveness hold under simultaneous switching
iff they hold in Muller's interleaving semantics. -/
theorem correct_iff_stepCorrect (hsi : C.SpeedIndependent) : C.Correct ↔ C.StepCorrect := by
  rw [Correct, StepCorrect, stepLts_deadlockFree_iff hsi, stepLts_livelockFree_iff hsi,
    stepLive_iff hsi]

end Circuit

end AsyncLean
