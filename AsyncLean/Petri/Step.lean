/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Step semantics of Petri nets

The interleaving semantics `Net.lts` fires one transition at a time.  In the *step*
semantics several transitions fire at once: a step is a multiset `X : T → ℕ` of
transitions (`X t` occurrences of `t`), enabled when the marking holds enough tokens for all
of them together, and firing it consumes and produces all their tokens at once.

This file shows that, for the properties studied here, the two semantics agree:

* `Net.stepLts_reachable_iff` : the reachable markings are the same;
* `Net.stepLts_deadlockFree_iff`, `Net.stepLts_livelockFree_iff`, `Net.stepLive_iff` :
  deadlock freedom, livelock freedom (a step is internal when all its transitions are) and
  liveness of every transition are the same in both semantics.

So results proved with the interleaving semantics hold for truly concurrent firing too.
-/

namespace AsyncLean

namespace Net

open Finset

variable {P T : Type*} [Fintype T] [DecidableEq T] (N : Net P T)

/-- The step `X` (a multiset of transitions) is enabled in `M`. -/
def StepEnabled (M : Marking P) (X : T → ℕ) : Prop := ∀ p, ∑ t, X t * N.pre t p ≤ M p

/-- The marking reached by firing all the transitions of the step `X` at once. -/
def fireStep (M : Marking P) (X : T → ℕ) : Marking P :=
  fun p => M p - ∑ t, X t * N.pre t p + ∑ t, X t * N.post t p

/-- Step semantics: an LTS whose labels are non-empty steps. -/
def stepLts : LTS (Marking P) (T → ℕ) where
  step M X M' := X ≠ 0 ∧ N.StepEnabled M X ∧ M' = N.fireStep M X

/-- A step is internal when all its transitions are. -/
def StepInternal (internal : T → Prop) (X : T → ℕ) : Prop := ∀ t, X t ≠ 0 → internal t

/-- Liveness in the step semantics: from every reachable marking, a step containing `t` can
eventually fire. -/
def StepLive (M₀ : Marking P) : Prop :=
  ∀ t M, N.stepLts.Reachable M₀ M →
    ∃ M', N.stepLts.Reachable M M' ∧ ∃ X, 0 < X t ∧ N.stepLts.Enabled M' X

variable {N}

/-- `X` with one occurrence of `t₀` removed. -/
private def dec (X : T → ℕ) (t₀ : T) : T → ℕ := Function.update X t₀ (X t₀ - 1)

private theorem sum_dec {X : T → ℕ} {t₀ : T} (h : 0 < X t₀) (f : T → ℕ) :
    ∑ t, X t * f t = ∑ t, dec X t₀ t * f t + f t₀ := by
  rw [← Finset.add_sum_erase _ _ (mem_univ t₀), ← Finset.add_sum_erase _ _ (mem_univ t₀)]
  have : ∑ t ∈ univ.erase t₀, dec X t₀ t * f t = ∑ t ∈ univ.erase t₀, X t * f t :=
    Finset.sum_congr rfl fun t ht => by
      rw [dec, Function.update_of_ne (Finset.ne_of_mem_erase ht)]
  rw [this, dec, Function.update_self]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
  rw [hk]
  simp only [Nat.zero_add, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
  omega

private theorem sum_mul_le {X : T → ℕ} {t₀ : T} (h : 0 < X t₀) (f : T → ℕ) :
    f t₀ ≤ ∑ t, X t * f t := by
  rw [sum_dec h f]; omega

/-- Firing a step one transition at a time: every non-empty enabled step is a non-empty
sequence of interleaved firings of its transitions. -/
theorem transGen_of_stepEnabled {Q : T → Prop} :
    ∀ (n : ℕ) (X : T → ℕ) (M : Marking P), ∑ t, X t = n → X ≠ 0 → N.StepEnabled M X →
      (∀ t, X t ≠ 0 → Q t) →
      Relation.TransGen (fun M M' => ∃ t, Q t ∧ N.lts.step M t M') M (N.fireStep M X) := by
  intro n
  induction n with
  | zero =>
    intro X M hn hX
    exact absurd (funext fun t => Nat.eq_zero_of_le_zero
      (hn ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ t))) hX
  | succ n ih =>
    intro X M hn hX hen hQ
    obtain ⟨t₀, ht₀⟩ : ∃ t₀, X t₀ ≠ 0 := by
      by_contra h; push Not at h; exact hX (funext h)
    have hpos : 0 < X t₀ := Nat.pos_of_ne_zero ht₀
    have hent : N.Enabled M t₀ := fun p => (sum_mul_le hpos _).trans (hen p)
    have hfire : N.fireStep (N.fire M t₀) (dec X t₀) = N.fireStep M X := by
      funext p
      have h1 := sum_dec hpos (N.pre · p)
      have h2 := sum_dec hpos (N.post · p)
      have h3 := hen p
      simp only [fireStep, fire_apply] at *
      omega
    have hstep : ∃ t, Q t ∧ N.lts.step M t (N.fire M t₀) := ⟨t₀, hQ t₀ ht₀, hent, rfl⟩
    by_cases hX' : dec X t₀ = 0
    · have : N.fireStep (N.fire M t₀) (dec X t₀) = N.fire M t₀ := by
        funext p; simp [fireStep, hX']
      rw [← hfire, this]
      exact .single hstep
    · have hn' : ∑ t, dec X t₀ t = n := by
        have := sum_dec hpos (fun _ => 1)
        simp only [Nat.mul_one] at this
        omega
      have hen' : N.StepEnabled (N.fire M t₀) (dec X t₀) := fun p => by
        have h1 := sum_dec hpos (N.pre · p)
        have h3 := hen p
        simp only [fire_apply]
        omega
      have hQ' : ∀ t, dec X t₀ t ≠ 0 → Q t := fun t ht => by
        by_cases h : t = t₀
        · subst h; exact hQ _ ht₀
        · rw [dec, Function.update_of_ne h] at ht; exact hQ t ht
      rw [← hfire]
      exact .head hstep (ih _ _ hn' hX' hen' hQ')

theorem reachable_fireStep {M : Marking P} {X : T → ℕ} (hen : N.StepEnabled M X) :
    N.lts.Reachable M (N.fireStep M X) := by
  by_cases hX : X = 0
  · have : N.fireStep M X = M := by funext p; simp [fireStep, hX]
    rw [this]
  · have := transGen_of_stepEnabled (Q := fun _ => True) _ X M rfl hX hen fun _ _ => trivial
    exact (Relation.TransGen.mono (fun _ _ ⟨t, _, h⟩ => ⟨t, h⟩) _ _ this).to_reflTransGen

theorem stepEnabled_single {M : Marking P} {t : T} :
    N.StepEnabled M (Pi.single t 1) ↔ N.Enabled M t := by
  simp [StepEnabled, Enabled, Pi.single_apply, Finset.sum_ite_eq']

theorem fireStep_single (M : Marking P) (t : T) : N.fireStep M (Pi.single t 1) = N.fire M t := by
  funext p; simp [fireStep, fire_apply, Pi.single_apply, Finset.sum_ite_eq']

theorem stepLts_step_single {M M' : Marking P} {t : T} (h : N.lts.step M t M') :
    N.stepLts.step M (Pi.single t 1) M' :=
  ⟨by simp, stepEnabled_single.2 h.1, h.2.trans (fireStep_single M t).symm⟩

theorem stepLts_reachable_of_reachable {M M' : Marking P} (h : N.lts.Reachable M M') :
    N.stepLts.Reachable M M' :=
  Relation.ReflTransGen.mono (fun _ _ ⟨_, hst⟩ => ⟨_, stepLts_step_single hst⟩) _ _ h

theorem reachable_of_stepLts_reachable {M M' : Marking P} (h : N.stepLts.Reachable M M') :
    N.lts.Reachable M M' := by
  induction h with
  | refl => exact LTS.Reachable.refl _
  | tail _ hst ih =>
    obtain ⟨X, -, hen, rfl⟩ := hst
    exact ih.trans (reachable_fireStep hen)

/-- **The step semantics reaches exactly the markings of the interleaving semantics.** -/
theorem stepLts_reachable_iff {M M' : Marking P} :
    N.stepLts.Reachable M M' ↔ N.lts.Reachable M M' :=
  ⟨reachable_of_stepLts_reachable, stepLts_reachable_of_reachable⟩

theorem stepLts_isDeadlock_iff {M : Marking P} : N.stepLts.IsDeadlock M ↔ N.IsDead M := by
  constructor
  · intro h t ht
    exact h _ _ (stepLts_step_single (M' := N.fire M t) ⟨ht, rfl⟩)
  · rintro h X M' ⟨hX, hen, -⟩
    obtain ⟨t, ht⟩ : ∃ t, X t ≠ 0 := by
      by_contra h'; push Not at h'; exact hX (funext h')
    exact h t fun p => (sum_mul_le (Nat.pos_of_ne_zero ht) _).trans (hen p)

/-- Deadlock freedom is the same in both semantics. -/
theorem stepLts_deadlockFree_iff {M₀ : Marking P} :
    N.stepLts.DeadlockFree M₀ ↔ N.lts.DeadlockFree M₀ := by
  simp only [LTS.DeadlockFree, stepLts_reachable_iff, stepLts_isDeadlock_iff,
    lts_isDeadlock_iff]

/-- Livelock freedom is the same in both semantics, a step being internal when all its
transitions are. -/
theorem stepLts_livelockFree_iff {internal : T → Prop} {M₀ : Marking P} :
    N.stepLts.LivelockFree (StepInternal internal) M₀ ↔ N.lts.LivelockFree internal M₀ := by
  simp only [LTS.livelockFree_iff_acc, stepLts_reachable_iff]
  refine forall₂_congr fun M _ => ⟨fun h => ?_, fun h => ?_⟩
  · refine Subrelation.accessible (fun {a b} ⟨t, ht, hst⟩ => ?_) h
    refine ⟨Pi.single t 1, fun u hu => ?_, stepLts_step_single hst⟩
    by_cases h : u = t
    · exact h ▸ ht
    · simp [h] at hu
  · refine Subrelation.accessible (fun {a b} ⟨X, hX, hX0, hen, he⟩ => ?_) h.transGen
    refine Relation.TransGen.swap _ _ ?_
    rw [he]
    exact transGen_of_stepEnabled _ X b rfl hX0 hen hX

theorem stepLts_enabled_iff {M : Marking P} {t : T} :
    (∃ X, 0 < X t ∧ N.stepLts.Enabled M X) ↔ N.Enabled M t := by
  constructor
  · rintro ⟨X, hX, _, -, hen, -⟩
    exact fun p => (sum_mul_le hX _).trans (hen p)
  · intro h
    exact ⟨Pi.single t 1, by simp, _, stepLts_step_single (M' := N.fire M t) ⟨h, rfl⟩⟩

/-- Liveness of every transition is the same in both semantics. -/
theorem stepLive_iff {M₀ : Marking P} : N.StepLive M₀ ↔ N.lts.Live M₀ := by
  simp only [StepLive, LTS.Live, LTS.LiveLabel, stepLts_reachable_iff, stepLts_enabled_iff,
    lts_enabled_iff]

end Net

end AsyncLean
