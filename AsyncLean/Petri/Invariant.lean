/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-!
# Structural invariants of Petri nets

* **Place invariants** (P-semiflows): integer weightings `y` of the places such that every
  transition preserves the weighted token count.  The weighted token count is then
  constant on all reachable markings (`IsPInvariant.weight_reachable`), which yields
  bounds and safeness (`IsPInvariant.bound`).
* **Linear ranking functions** for livelock freedom: a non-negative place weighting that
  strictly decreases under every internal transition rules out infinite internal runs
  (`livelockFree_of_linearRanking`).  The side condition is purely structural and is
  checked by `decide` on concrete nets.
-/

namespace AsyncLean

namespace Net

open Finset

variable {P T : Type*} [Fintype P] {N : Net P T}

/-- Weighted token count of a marking. -/
def weight (y : P → ℤ) (M : Marking P) : ℤ := ∑ p, y p * (M p : ℤ)

variable (N) in
/-- The effect of transition `t` on the weighted token count. -/
def weightEffect (y : P → ℤ) (t : T) : ℤ := ∑ p, y p * ((N.post t p : ℤ) - N.pre t p)

variable (N) in
/-- `y` is a place invariant: no transition changes the `y`-weighted token count. -/
def IsPInvariant (y : P → ℤ) : Prop := ∀ t, N.weightEffect y t = 0

instance [Fintype T] (y : P → ℤ) : Decidable (N.IsPInvariant y) := by
  unfold IsPInvariant; infer_instance

theorem weight_fire (y : P → ℤ) {M : Marking P} {t : T} (h : N.Enabled M t) :
    weight y (N.fire M t) = weight y M + N.weightEffect y t := by
  simp only [weight, weightEffect, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [fire_cast h]
  ring

theorem IsPInvariant.weight_fire {y : P → ℤ} (hy : N.IsPInvariant y) {M : Marking P} {t : T}
    (h : N.Enabled M t) : weight y (N.fire M t) = weight y M := by
  rw [Net.weight_fire y h, hy t, add_zero]

/-- **Conservation law**: a place invariant is constant on all reachable markings. -/
theorem IsPInvariant.weight_reachable {y : P → ℤ} (hy : N.IsPInvariant y) {M₀ M : Marking P}
    (hr : N.lts.Reachable M₀ M) : weight y M = weight y M₀ := by
  refine hr.invariant (I := fun M => weight y M = weight y M₀) rfl ?_
  rintro M t M' hM ⟨hen, rfl⟩
  rw [hy.weight_fire hen, hM]

/-- **Bound from a non-negative place invariant**: `y p * M p ≤ y · M₀` on every reachable
marking. -/
theorem IsPInvariant.bound {y : P → ℤ} (hy : N.IsPInvariant y) (hnn : ∀ p, 0 ≤ y p)
    {M₀ M : Marking P} (hr : N.lts.Reachable M₀ M) (p : P) :
    y p * (M p : ℤ) ≤ weight y M₀ := by
  rw [← hy.weight_reachable hr]
  exact Finset.single_le_sum (f := fun q => y q * (M q : ℤ))
    (fun q _ => mul_nonneg (hnn q) (Nat.cast_nonneg _)) (Finset.mem_univ p)

/-- **Safeness from a place invariant**: if `y p = 1`, `y ≥ 0` and the initial weighted
count is `1`, then `p` never holds more than one token. -/
theorem IsPInvariant.safe {y : P → ℤ} (hy : N.IsPInvariant y) (hnn : ∀ p, 0 ≤ y p)
    {M₀ : Marking P} (h₀ : weight y M₀ ≤ 1) {p : P} (hp : 1 ≤ y p) {M : Marking P}
    (hr : N.lts.Reachable M₀ M) : M p ≤ 1 := by
  have h := hy.bound hnn hr p
  have : (M p : ℤ) ≤ y p * (M p : ℤ) := le_mul_of_one_le_left (Nat.cast_nonneg _) hp
  omega

/-! ### Livelock freedom by a linear ranking function -/

/-- **Livelock freedom by a linear ranking function.**  If some non-negative place weighting
`w` strictly decreases under every internal transition (i.e. each internal transition
consumes more weight than it produces), then there is no infinite run of internal
transitions from any marking. -/
theorem livelockFree_of_linearRanking {internal : T → Prop} (w : P → ℕ)
    (hw : ∀ t, internal t → ∑ p, w p * N.post t p < ∑ p, w p * N.pre t p) (M₀ : Marking P) :
    N.lts.LivelockFree internal M₀ := by
  refine LTS.LivelockFree.of_ranking (fun _ => True) trivial (fun _ _ _ _ _ => trivial)
    (fun M => ∑ p, w p * M p) ?_
  rintro M t M' - hint ⟨hen, rfl⟩
  have key := Net.weight_fire (fun p => (w p : ℤ)) hen
  have hlt := hw t hint
  simp only [weight, weightEffect] at key
  have e1 : ((∑ p, w p * N.fire M t p : ℕ) : ℤ) = ∑ p, (w p : ℤ) * (N.fire M t p : ℤ) := by
    push_cast; rfl
  have e2 : ((∑ p, w p * M p : ℕ) : ℤ) = ∑ p, (w p : ℤ) * (M p : ℤ) := by push_cast; rfl
  have e3 : ∑ p, (w p : ℤ) * ((N.post t p : ℤ) - N.pre t p) =
      ((∑ p, w p * N.post t p : ℕ) : ℤ) - ((∑ p, w p * N.pre t p : ℕ) : ℤ) := by
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have : ((∑ p, w p * N.fire M t p : ℕ) : ℤ) < ((∑ p, w p * M p : ℕ) : ℤ) := by
    rw [e1, e2, key, e3]
    omega
  exact_mod_cast this

/-- Linear-ranking criterion relative to a labelling of transitions: transitions whose
label is the silent label are internal. -/
theorem livelockFree_of_linearRanking_label {Λ : Type*} (label : T → Option Λ) (w : P → ℕ)
    (hw : ∀ t, label t = none → ∑ p, w p * N.post t p < ∑ p, w p * N.pre t p)
    (M₀ : Marking P) : N.lts.LivelockFree (fun t => label t = none) M₀ :=
  livelockFree_of_linearRanking w hw M₀

end Net

end AsyncLean
