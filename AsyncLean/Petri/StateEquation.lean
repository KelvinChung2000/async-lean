/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deadlock freedom from the state equation

Every reachable marking satisfies the *state equation* `M = M₀ + C · x`, where `C` is the
incidence matrix and `x ≥ 0` counts how often each transition fired
(`Net.stateEq_of_reachable`).  If moreover every reachable marking is bounded by `K`, a dead
marking satisfies, for every transition `t`, a linear inequality: one of `t`'s input places
lacks tokens, so the tokens on `t`'s input places add up to at most some `D t`.

A *Farkas certificate* — weights `y` on the places and `z ≥ 0` on the transitions — shows
that no marking satisfies all of these linear constraints at once
(`Net.deadlockFree_of_stateEq`):

* `y · C t ≥ 0` for every transition (so `y · M ≥ y · M₀` on reachable markings);
* `y p ≤ Σ_t z t · [p is an input of t]` for every place;
* `Σ_t z t · D t < y · M₀`.

The certificate is found by linear programming and checked in time linear in the size of the
net, without exploring any state.  This is the state-equation method of model checkers such
as LoLA and Sara, with a checked certificate.
-/

namespace AsyncLean

namespace Net

open Finset

variable {P T : Type*} [Fintype P] [Fintype T] (N : Net P T)

/-- The effect of `t` on `p`. -/
def effect (t : T) (p : P) : ℤ := (N.post t p : ℤ) - N.pre t p

variable {N}

omit [Fintype P] in
/-- **The state equation**: a reachable marking is the initial one plus the effects of the
fired transitions. -/
theorem stateEq_of_reachable [DecidableEq T] {M₀ M : Marking P} (h : N.lts.Reachable M₀ M) :
    ∃ x : T → ℕ, ∀ p, (M p : ℤ) = M₀ p + ∑ t, (x t : ℤ) * N.effect t p := by
  induction h with
  | refl => exact ⟨fun _ => 0, fun p => by simp⟩
  | tail _ hst ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨t, hen, rfl⟩ := hst
    refine ⟨Function.update x t (x t + 1), fun p => ?_⟩
    have hsplit : ∀ y : T → ℕ, ∑ t', (y t' : ℤ) * N.effect t' p =
        (y t : ℤ) * N.effect t p + ∑ t' ∈ univ.erase t, (y t' : ℤ) * N.effect t' p :=
      fun y => (Finset.add_sum_erase _ _ (mem_univ t)).symm
    rw [hsplit]
    have hxp := hx p
    rw [hsplit x] at hxp
    have : ∑ t' ∈ univ.erase t, ((Function.update x t (x t + 1) t' : ℕ) : ℤ) * N.effect t' p =
        ∑ t' ∈ univ.erase t, (x t' : ℤ) * N.effect t' p :=
      Finset.sum_congr rfl fun t' ht' => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase ht')]
    rw [this, Function.update_self, fire_apply, effect]
    have h1 := hen p
    simp only [effect] at hxp ⊢
    push_cast
    rw [Nat.cast_sub h1]
    have e : ((x t : ℤ) + 1) * ((N.post t p : ℤ) - N.pre t p) =
        (x t : ℤ) * ((N.post t p : ℤ) - N.pre t p) + ((N.post t p : ℤ) - N.pre t p) := by ring
    rw [e]
    linarith

/-- **Deadlock freedom from the state equation.**  `K` bounds every reachable marking (place
by place), and `D t` bounds the tokens on `t`'s input places whenever `t` is disabled at a
marking below `K`; the weights `y` and `z` form a Farkas certificate. -/
theorem deadlockFree_of_stateEq [DecidableEq T] {M₀ : Marking P} (K : P → ℕ)
    (hK : ∀ M, N.lts.Reachable M₀ M → ∀ p, M p ≤ K p) (D : T → ℕ)
    (hD : ∀ t (M : Marking P), (∀ p, M p ≤ K p) → ¬ N.Enabled M t →
      ∑ p, (if N.pre t p ≠ 0 then M p else 0) ≤ D t)
    (y : P → ℤ) (z : T → ℕ)
    (h₁ : ∀ t, 0 ≤ ∑ p, y p * N.effect t p)
    (h₂ : ∀ p, y p ≤ ∑ t, if N.pre t p ≠ 0 then (z t : ℤ) else 0)
    (h₃ : ∑ t, (z t : ℤ) * D t < ∑ p, y p * M₀ p) : N.lts.DeadlockFree M₀ := by
  rw [deadlockFree_iff]
  intro M hM
  by_contra hdead
  push Not at hdead
  obtain ⟨x, hx⟩ := stateEq_of_reachable hM
  -- `y · M ≥ y · M₀`
  have hge : ∑ p, y p * M₀ p ≤ ∑ p, y p * M p := by
    have : ∑ p, y p * M p = ∑ p, y p * M₀ p + ∑ t, (x t : ℤ) * ∑ p, y p * N.effect t p := by
      simp only [hx, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p _ => by ring
    rw [this]
    have : 0 ≤ ∑ t, (x t : ℤ) * ∑ p, y p * N.effect t p :=
      Finset.sum_nonneg fun t _ => mul_nonneg (Nat.cast_nonneg _) (h₁ t)
    linarith
  -- `y · M ≤ Σ_t z t · D t`
  have hle : ∑ p, y p * M p ≤ ∑ t, (z t : ℤ) * D t := by
    calc ∑ p, y p * (M p : ℤ)
        ≤ ∑ p, (∑ t, if N.pre t p ≠ 0 then (z t : ℤ) else 0) * M p :=
          Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (h₂ p) (Nat.cast_nonneg _)
      _ = ∑ t, (z t : ℤ) * ∑ p, ((if N.pre t p ≠ 0 then M p else 0 : ℕ) : ℤ) := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p _ => ?_
          split_ifs <;> simp
      _ ≤ ∑ t, (z t : ℤ) * D t := by
          refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have := hD t M (hK M hM) (hdead t)
          exact_mod_cast this
  linarith

end Net

end AsyncLean
