/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Valiant
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.BigOperators

/-!
# Symmetric networks: minimal routing is optimal for uniform traffic, part 1: minimal routing on arc-transitive networks

Part 1 of 3 of `AsyncLean.Flow.Symmetric`; that module has the overview.
-/

namespace AsyncLean

namespace Fluid

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `dist` is a **hop distance** for `N`: `dist d d = 0`, and along every link of positive
capacity the distance to any destination drops by at most `1`. -/
def IsHopDistance (N : Net V) (dist : V → V → ℚ) : Prop :=
  (∀ d, dist d d = 0) ∧ ∀ u v d, 0 < N.cap u v → dist u d - dist v d ≤ 1

/-- The traffic times the hop distance it must travel, `∑ s d, dem s d * dist s d`. -/
def hopDemand (dem dist : V → V → ℚ) : ℚ := ∑ s, ∑ d, dem s d * dist s d

/-- **The hop bound.**  For a hop distance `dist`, any routing (adaptive, with detours, split over
many paths) of `θ * dem` has `θ * ∑ s d, dem s d * dist s d ≤ ∑ u v, cap u v`: every unit of
traffic crosses at least `dist s d` links. -/
theorem hop_bound {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (h : Routable N dem θ)
    {dist : V → V → ℚ} (hd : IsHopDistance N dist) :
    θ * hopDemand dem dist ≤ ∑ u, ∑ v, N.cap u v := by
  have := potential_bound h (fun _ _ => 1) (fun _ _ => zero_le_one) (fun d v => dist v d)
    hd.1 (fun d u v hc => hd.2 u v d hc)
  simpa [hopDemand] using this

/-- The potential drop telescopes, for any function satisfying the conservation law of a flow
(the capacities play no role): `∑ u v, f u v * (φ u - φ v) = θ * ∑ s, dem s d * φ s`. -/
theorem telescope_fun (f : V → V → ℚ) (dem : V → V → ℚ) (θ : ℚ) (d : V)
    (hc : ∀ v, v ≠ d → ∑ w, f v w - ∑ u, f u v = θ * dem v d) (φ : V → ℚ) (hφ : φ d = 0) :
    ∑ u, ∑ v, f u v * (φ u - φ v) = θ * ∑ s, dem s d * φ s := by
  have h1 : ∑ u, ∑ v, f u v * (φ u - φ v) = ∑ u, φ u * (∑ w, f u w - ∑ x, f x u) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => mul_comm _ _
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => mul_comm _ _
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s = d
  · subst hs; simp [hφ]
  · rw [hc s hs]; ring

/-- **The total load of a geodesic flow.**  If every link that commodity `d` uses brings it
exactly one step closer to `d` (`dist v d + 1 = dist u d`) and `dist d d = 0`, the total load of
the flow over all links is `∑ s d, dem s d * dist s d` per unit of throughput. -/
theorem total_load_eq (f : V → V → V → ℚ) (dem : V → V → ℚ) (θ : ℚ) (dist : V → V → ℚ)
    (hnn : ∀ d u v, 0 ≤ f d u v)
    (hc : ∀ d v, v ≠ d → ∑ w, f d v w - ∑ u, f d u v = θ * dem v d)
    (hdd : ∀ d, dist d d = 0) (hF : ∀ d u v, 0 < f d u v → dist v d + 1 = dist u d) :
    ∑ u, ∑ v, ∑ d, f d u v = θ * hopDemand dem dist := by
  have key : ∀ d, ∑ u, ∑ v, f d u v = θ * ∑ s, dem s d * dist s d := by
    intro d
    rw [← telescope_fun (f d) dem θ d (hc d) (fun v => dist v d) (hdd d)]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    rcases (hnn d u v).lt_or_eq with hp | hz
    · rw [← hF d u v hp]; ring
    · rw [← hz]; ring
  have e : ∑ u, ∑ v, ∑ d, f d u v = ∑ d, ∑ u, ∑ v, f d u v := by
    rw [sum_congr rfl fun u _ => sum_comm]; exact sum_comm
  unfold hopDemand
  rw [e, sum_comm (f := fun s d => dem s d * dist s d), mul_sum]
  exact sum_congr rfl fun d _ => key d

/-- **The total load of a minimal flow** (`F.Minimal`, with every used link one hop closer):
`∑ u v, ∑ d, F.f d u v = θ * ∑ s d, dem s d * dist s d`. -/
theorem minimal_load_total {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (F : Flow N dem θ)
    {dist : V → V → ℚ} (hdd : ∀ d, dist d d = 0)
    (hF : F.SupportedOn fun d u v => dist v d + 1 = dist u d) :
    ∑ u, ∑ v, ∑ d, F.f d u v = θ * hopDemand dem dist :=
  total_load_eq F.f dem θ dist F.nonneg F.conserve hdd hF

omit [DecidableEq V] in
/-- For a distance with natural values and the hop property, a minimal flow steps exactly one
hop closer on every link it uses. -/
theorem Flow.Minimal.drop_one {N : Net V} {dem : V → V → ℚ} {θ : ℚ} {F : Flow N dem θ}
    {Dn : V → V → ℕ} (hF : F.Minimal fun u d => (Dn u d : ℚ))
    (hhop : ∀ u v d, 0 < N.cap u v → Dn u d ≤ Dn v d + 1) :
    F.SupportedOn fun d u v => ((Dn v d : ℕ) : ℚ) + 1 = (Dn u d : ℕ) := by
  intro d u v hp
  have h1 : Dn v d < Dn u d := by have := hF d u v hp; simp only at this; exact_mod_cast this
  have hc : 0 < N.cap u v := by
    by_contra hc
    rw [F.eq_zero_of_cap (not_lt.1 hc) d] at hp
    exact lt_irrefl _ hp
  have h2 := hhop u v d hc
  exact_mod_cast (show Dn v d + 1 = Dn u d by omega)

/-- **Balanced geodesic flows are optimal.**  Let `dist` be a hop distance, and `F` a flow at
throughput `θ` in which every used link brings its commodity one hop closer and every link of
positive capacity is loaded to exactly its capacity.  If `∑ dem * dist > 0`, then `θ` is the
largest routable throughput, by any routing, and it equals `∑ cap / ∑ dem * dist`. -/
theorem balanced_opt {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (F : Flow N dem θ)
    {dist : V → V → ℚ} (hd : IsHopDistance N dist)
    (hF : F.SupportedOn fun d u v => dist v d + 1 = dist u d)
    (hsat : ∀ u v, 0 < N.cap u v → ∑ d, F.f d u v = N.cap u v)
    (hD : 0 < hopDemand dem dist) :
    IsGreatest {θ' : ℚ | Routable N dem θ'} θ ∧
      θ = (∑ u, ∑ v, N.cap u v) / hopDemand dem dist := by
  have htot : ∑ u, ∑ v, N.cap u v = θ * hopDemand dem dist := by
    rw [← minimal_load_total F hd.1 hF]
    refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
    rcases (N.cap_nonneg u v).lt_or_eq with hp | hz
    · exact (hsat u v hp).symm
    · rw [← hz]; exact (sum_eq_zero fun d _ => F.eq_zero_of_cap hz.symm.le d).symm
  refine ⟨⟨⟨F⟩, fun θ' h' => ?_⟩, ?_⟩
  · have := hop_bound h' hd
    rw [htot] at this
    exact le_of_mul_le_mul_right this hD
  · rw [htot, mul_div_cancel_right₀ _ hD.ne']

/-- A **free flow** of `dem` in `N`: a flow at throughput `1` that uses only links of positive
capacity, but ignores how much capacity they have. -/
structure FreeFlow (N : Net V) (dem : V → V → ℚ) where
  /-- The rate of commodity `d` on the link `u → v`. -/
  f : V → V → V → ℚ
  nonneg : ∀ d u v, 0 ≤ f d u v
  /-- Conservation at throughput `1`. -/
  conserve : ∀ d v, v ≠ d → ∑ w, f d v w - ∑ u, f d u v = dem v d
  /-- Only links of positive capacity are used. -/
  support : ∀ d u v, 0 < f d u v → 0 < N.cap u v

section Geodesic

variable {N : Net V} {Dn : V → V → ℕ} (nh : V → V → V)

/-- The walk from `s` that follows the next hop `nh · d` towards `d`: its `i`-th vertex. -/
def walk (d s : V) (i : ℕ) : V := (fun v => nh v d)^[i] s

/-- The walk as a unit flow: the number of steps `i < len` of the walk that cross `u → v`. -/
def walkFlow (d s : V) (len : ℕ) (u v : V) : ℚ :=
  ∑ i ∈ range len, if walk nh d s i = u ∧ walk nh d s (i + 1) = v then 1 else 0

omit [Fintype V] [DecidableEq V] in
/-- One more step of the walk: the next hop of the current vertex. -/
theorem walk_succ (d s : V) (i : ℕ) : walk nh d s (i + 1) = nh (walk nh d s i) d :=
  Function.iterate_succ_apply' _ _ _

/-- Conservation of a walk: it leaves its start once more than it enters it, and enters its
end once more than it leaves it. -/
theorem walkFlow_conserve (d s : V) (len : ℕ) (v : V) :
    ∑ w, walkFlow nh d s len v w - ∑ u, walkFlow nh d s len u v =
      (if walk nh d s 0 = v then 1 else 0) - (if walk nh d s len = v then 1 else 0) := by
  unfold walkFlow
  rw [sum_comm, sum_comm (f := fun u i => if walk nh d s i = u ∧ walk nh d s (i + 1) = v
    then (1 : ℚ) else 0), ← sum_range_sub' (fun i => if walk nh d s i = v then (1 : ℚ) else 0),
    ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  simp only [ite_and]
  by_cases h : walk nh d s i = v
  · simp only [h, ite_true, sum_ite_eq, mem_univ]
  · simp only [h, ite_false, sum_const_zero, sum_ite_eq, mem_univ, ite_true]

omit [Fintype V] [DecidableEq V] in
/-- Along the greedy walk the distance drops by one at every step, until it reaches `0`. -/
theorem walk_dist (hzero : ∀ v d, Dn v d = 0 ↔ v = d)
    (hnh : ∀ v d, v ≠ d → 0 < N.cap v (nh v d) ∧ Dn (nh v d) d + 1 = Dn v d)
    (d s : V) (i : ℕ) (hi : i ≤ Dn s d) : Dn (walk nh d s i) d + i = Dn s d := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h := ih (by omega)
    have hne : walk nh d s i ≠ d := by
      intro he; rw [he, (hzero d d).2 rfl] at h; omega
    rw [walk_succ]
    have := (hnh _ d hne).2
    omega

omit [Fintype V] [DecidableEq V] in
/-- The greedy walk from `s` reaches `d` after `Dn s d` steps. -/
theorem walk_end (hzero : ∀ v d, Dn v d = 0 ↔ v = d)
    (hnh : ∀ v d, v ≠ d → 0 < N.cap v (nh v d) ∧ Dn (nh v d) d + 1 = Dn v d) (d s : V) :
    walk nh d s (Dn s d) = d := by
  have := walk_dist nh hzero hnh d s (Dn s d) le_rfl
  exact (hzero _ d).1 (by omega)

omit [Fintype V] [DecidableEq V] in
/-- A step of the greedy walk is a link of positive capacity bringing it one hop closer. -/
theorem walk_step (hzero : ∀ v d, Dn v d = 0 ↔ v = d)
    (hnh : ∀ v d, v ≠ d → 0 < N.cap v (nh v d) ∧ Dn (nh v d) d + 1 = Dn v d)
    (d s : V) (i : ℕ) (hi : i < Dn s d) :
    0 < N.cap (walk nh d s i) (walk nh d s (i + 1)) ∧
      Dn (walk nh d s (i + 1)) d + 1 = Dn (walk nh d s i) d := by
  have h := walk_dist nh hzero hnh d s i hi.le
  have hne : walk nh d s i ≠ d := by
    intro he; rw [he, (hzero d d).2 rfl] at h; omega
  rw [walk_succ]
  exact hnh _ d hne

end Geodesic

/-- **Geodesic routing exists.**  Let `Dn` be a distance with natural values, `Dn v d = 0` only
for `v = d`, such that every `v ≠ d` has a neighbour (a link of positive capacity) one hop closer
to `d`.  Then every nonnegative traffic matrix has a free flow in which every link a commodity
uses brings it one hop closer to its destination: send each source along a greedy walk. -/
theorem exists_geodesic_freeFlow (N : Net V) (dem : V → V → ℚ) (hdem : ∀ s d, 0 ≤ dem s d)
    (Dn : V → V → ℕ) (hzero : ∀ v d, Dn v d = 0 ↔ v = d)
    (hstep : ∀ v d, v ≠ d → ∃ w, 0 < N.cap v w ∧ Dn w d + 1 = Dn v d) :
    ∃ R : FreeFlow N dem, ∀ d u v, 0 < R.f d u v → Dn v d + 1 = Dn u d := by
  classical
  choose! nh hnh using hstep
  have hpos : ∀ d s u v, walkFlow nh d s (Dn s d) u v ≠ 0 →
      0 < N.cap u v ∧ Dn v d + 1 = Dn u d := by
    intro d s u v h
    obtain ⟨i, hi, hne⟩ := exists_ne_zero_of_sum_ne_zero h
    by_cases hc : walk nh d s i = u ∧ walk nh d s (i + 1) = v
    · rw [← hc.1, ← hc.2]; exact walk_step nh hzero hnh d s i (mem_range.1 hi)
    · exact absurd (by simp [hc]) hne
  have hwnn : ∀ d s u v, 0 ≤ walkFlow nh d s (Dn s d) u v := fun d s u v =>
    sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hsupp : ∀ d u v, 0 < ∑ s, dem s d * walkFlow nh d s (Dn s d) u v →
      0 < N.cap u v ∧ Dn v d + 1 = Dn u d := by
    intro d u v h
    obtain ⟨s, _, hs⟩ := exists_ne_zero_of_sum_ne_zero h.ne'
    exact hpos d s u v (right_ne_zero_of_mul hs)
  refine ⟨{ f := fun d u v => ∑ s, dem s d * walkFlow nh d s (Dn s d) u v
            nonneg := fun d u v => sum_nonneg fun s _ => mul_nonneg (hdem s d) (hwnn d s u v)
            conserve := fun d v hv => ?_
            support := fun d u v h => (hsupp d u v h).1 }, fun d u v h => (hsupp d u v h).2⟩
  rw [sum_comm, sum_comm (f := fun u s => dem s d * walkFlow nh d s (Dn s d) u v),
    ← sum_sub_distrib]
  calc ∑ s, (∑ w, dem s d * walkFlow nh d s (Dn s d) v w -
        ∑ u, dem s d * walkFlow nh d s (Dn s d) u v)
      = ∑ s, dem s d * ((if s = v then 1 else 0) - (if d = v then 1 else 0)) := by
        refine sum_congr rfl fun s _ => ?_
        rw [← mul_sum, ← mul_sum, ← mul_sub, walkFlow_conserve, walk_end nh hzero hnh]
        rfl
    _ = dem v d := by simp [Ne.symm hv]

/-- An **automorphism** of the network, the traffic and the distance: a permutation of the
vertices preserving the capacities, the demands and the distances. -/
def IsAut (N : Net V) (dem dist : V → V → ℚ) (σ : Equiv.Perm V) : Prop :=
  (∀ u v, N.cap (σ u) (σ v) = N.cap u v) ∧ (∀ s d, dem (σ s) (σ d) = dem s d) ∧
    ∀ u d, dist (σ u) (σ d) = dist u d

namespace IsAut

variable {N : Net V} {dem dist : V → V → ℚ}

omit [Fintype V] [DecidableEq V] in
/-- The identity is an automorphism. -/
theorem refl : IsAut N dem dist (Equiv.refl V) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

omit [Fintype V] [DecidableEq V] in
/-- Automorphisms compose: `σ` then `τ`. -/
theorem trans {σ τ : Equiv.Perm V} (hσ : IsAut N dem dist σ) (hτ : IsAut N dem dist τ) :
    IsAut N dem dist (σ.trans τ) :=
  ⟨fun u v => by simp only [Equiv.trans_apply]; rw [hτ.1, hσ.1],
    fun u v => by simp only [Equiv.trans_apply]; rw [hτ.2.1, hσ.2.1],
    fun u v => by simp only [Equiv.trans_apply]; rw [hτ.2.2, hσ.2.2]⟩

omit [Fintype V] [DecidableEq V] in
/-- The inverse of an automorphism is an automorphism. -/
theorem symm {σ : Equiv.Perm V} (hσ : IsAut N dem dist σ) : IsAut N dem dist σ.symm :=
  ⟨fun u v => by rw [← hσ.1 (σ.symm u) (σ.symm v)]; simp only [Equiv.apply_symm_apply],
    fun u v => by rw [← hσ.2.1 (σ.symm u) (σ.symm v)]; simp only [Equiv.apply_symm_apply],
    fun u v => by rw [← hσ.2.2 (σ.symm u) (σ.symm v)]; simp only [Equiv.apply_symm_apply]⟩

end IsAut

/-- The automorphisms act **transitively on the links**: every link of positive capacity is
mapped to every other one by some automorphism. -/
def ArcTransitive (N : Net V) (dem dist : V → V → ℚ) : Prop :=
  ∀ u v u' v', 0 < N.cap u v → 0 < N.cap u' v' →
    ∃ σ : Equiv.Perm V, IsAut N dem dist σ ∧ σ u = u' ∧ σ v = v'

omit [Fintype V] [DecidableEq V] in
/-- Arc-transitivity from a base link: it suffices that every link of positive capacity can be
mapped to one fixed link `u₀ → v₀`. -/
theorem ArcTransitive.of_base {N : Net V} {dem dist : V → V → ℚ} (u₀ v₀ : V)
    (h : ∀ u v, 0 < N.cap u v → ∃ σ : Equiv.Perm V, IsAut N dem dist σ ∧ σ u = u₀ ∧ σ v = v₀) :
    ArcTransitive N dem dist := by
  intro u v u' v' huv hu'v'
  obtain ⟨σ, hσ, h1, h2⟩ := h u v huv
  obtain ⟨τ, hτ, h3, h4⟩ := h u' v' hu'v'
  refine ⟨σ.trans τ.symm, hσ.trans hτ.symm, ?_, ?_⟩
  · rw [Equiv.trans_apply, h1, ← h3, Equiv.symm_apply_apply]
  · rw [Equiv.trans_apply, h2, ← h4, Equiv.symm_apply_apply]

/-- **Symmetrization.**  If the automorphisms act transitively on the links, averaging a geodesic
free flow over all automorphisms loads every link equally; scaled to the throughput
`∑ cap / ∑ dem * dist`, it is a geodesic flow loading every link of positive capacity to exactly
its capacity. -/
theorem symmetric_balanced {N : Net V} {dem dist : V → V → ℚ} (R : FreeFlow N dem)
    (hR : ∀ d u v, 0 < R.f d u v → dist v d + 1 = dist u d) (hdd : ∀ d, dist d d = 0)
    (hT : ArcTransitive N dem dist) (hD : 0 < hopDemand dem dist) :
    ∃ F : Flow N dem ((∑ u, ∑ v, N.cap u v) / hopDemand dem dist),
      F.SupportedOn (fun d u v => dist v d + 1 = dist u d) ∧
      ∀ u v, 0 < N.cap u v → ∑ d, F.f d u v = N.cap u v := by
  classical
  let _ : Fintype (Equiv.Perm V) :=
    Fintype.ofInjective (fun σ : Equiv.Perm V => (σ : V → V)) Equiv.coe_fn_injective
  set A : Finset (Equiv.Perm V) := univ.filter (IsAut N dem dist) with hA
  have hmem : ∀ σ, σ ∈ A ↔ IsAut N dem dist σ := fun σ => by simp [hA]
  have hAc : (0 : ℚ) < A.card := by
    exact_mod_cast card_pos.2 ⟨Equiv.refl V, (hmem _).2 IsAut.refl⟩
  have hι : (0 : ℚ) < (A.card : ℚ)⁻¹ := inv_pos.2 hAc
  -- the average over the automorphisms
  set g : V → V → V → ℚ := fun d u v => (A.card : ℚ)⁻¹ * ∑ σ ∈ A, R.f (σ d) (σ u) (σ v) with hg
  have gnn : ∀ d u v, 0 ≤ g d u v := fun d u v =>
    mul_nonneg hι.le (sum_nonneg fun σ _ => R.nonneg _ _ _)
  have gcons : ∀ d v, v ≠ d → ∑ w, g d v w - ∑ u, g d u v = 1 * dem v d := by
    intro d v hv
    simp only [hg, ← mul_sum, ← mul_sub]
    have e2 : ∑ i, ∑ σ ∈ A, R.f (σ d) (σ i) (σ v) = ∑ σ ∈ A, ∑ i, R.f (σ d) (σ i) (σ v) :=
      sum_comm
    rw [sum_comm, e2, ← sum_sub_distrib,
      sum_congr rfl (g := fun _ => dem v d) fun σ hσ => ?_]
    · rw [sum_const, nsmul_eq_mul, inv_mul_cancel_left₀ hAc.ne', one_mul]
    · have hσ' := (hmem σ).1 hσ
      rw [Equiv.sum_comp σ (fun w => R.f (σ d) (σ v) w),
        Equiv.sum_comp σ (fun u => R.f (σ d) u (σ v)), R.conserve _ _ (σ.injective.ne hv),
        hσ'.2.1]
  have gsupp : ∀ d u v, 0 < g d u v → 0 < N.cap u v ∧ dist v d + 1 = dist u d := by
    intro d u v h
    have hs : 0 < ∑ σ ∈ A, R.f (σ d) (σ u) (σ v) := (mul_pos_iff_of_pos_left hι).1 h
    obtain ⟨σ, hσ, hne⟩ := exists_ne_zero_of_sum_ne_zero hs.ne'
    have hp : 0 < R.f (σ d) (σ u) (σ v) := lt_of_le_of_ne (R.nonneg _ _ _) (Ne.symm hne)
    have hσ' := (hmem σ).1 hσ
    refine ⟨?_, ?_⟩
    · rw [← hσ'.1]; exact R.support _ _ _ hp
    · rw [← hσ'.2.2 v d, ← hσ'.2.2 u d]; exact hR _ _ _ hp
  have gzero : ∀ d u v, ¬ 0 < N.cap u v → g d u v = 0 := fun d u v hc =>
    le_antisymm (not_lt.1 fun h => hc (gsupp d u v h).1) (gnn d u v)
  -- the load of the average is invariant under the automorphisms
  set L : V → V → ℚ := fun u v => ∑ d, g d u v with hL
  have eL : ∀ x y, L x y = (A.card : ℚ)⁻¹ * ∑ σ ∈ A, ∑ d, R.f d (σ x) (σ y) := by
    intro x y
    simp only [hL, hg, ← mul_sum]
    rw [sum_comm]
    congr 1
    exact sum_congr rfl fun σ _ => Equiv.sum_comp σ (fun d => R.f d (σ x) (σ y))
  have Linv : ∀ τ, IsAut N dem dist τ → ∀ u v, L (τ u) (τ v) = L u v := by
    intro τ hτ u v
    rw [eL, eL]
    congr 1
    refine sum_nbij' (fun σ => τ.trans σ) (fun σ => τ.symm.trans σ) (fun σ hσ => (hmem _).2
      (hτ.trans ((hmem σ).1 hσ))) (fun σ hσ => (hmem _).2 (hτ.symm.trans ((hmem σ).1 hσ)))
      (fun σ _ => Equiv.ext fun x => by simp) (fun σ _ => Equiv.ext fun x => by simp)
      (fun σ _ => rfl)
  have hLtot : ∑ u, ∑ v, L u v = hopDemand dem dist := by
    rw [← one_mul (hopDemand dem dist)]
    exact total_load_eq g dem 1 dist gnn gcons hdd fun d u v h => (gsupp d u v h).2
  have hLzero : ∀ u v, ¬ 0 < N.cap u v → L u v = 0 := fun u v hc =>
    sum_eq_zero fun d _ => gzero d u v hc
  -- a link of positive capacity
  obtain ⟨u₀, v₀, h₀⟩ : ∃ u₀ v₀, 0 < N.cap u₀ v₀ := by
    by_contra hc
    have : ∑ u, ∑ v, L u v = 0 :=
      sum_eq_zero fun u _ => sum_eq_zero fun v _ => hLzero u v fun h => hc ⟨u, v, h⟩
    rw [hLtot] at this
    exact hD.ne' this
  have hLc : ∀ u v, 0 < N.cap u v → L u v = L u₀ v₀ ∧ N.cap u v = N.cap u₀ v₀ := by
    intro u v huv
    obtain ⟨τ, hτ, h1, h2⟩ := hT u₀ v₀ u v h₀ huv
    rw [← h1, ← h2]
    exact ⟨Linv τ hτ u₀ v₀, hτ.1 u₀ v₀⟩
  set A' : ℚ := ∑ u, ∑ v, if 0 < N.cap u v then (1 : ℚ) else 0 with hA'
  have hcapsum : ∑ u, ∑ v, N.cap u v = N.cap u₀ v₀ * A' := by
    rw [hA', mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun v _ => ?_
    by_cases hc : 0 < N.cap u v
    · rw [ite_eq_left hc, mul_one, (hLc u v hc).2]
    · rw [ite_eq_right hc, mul_zero]
      exact le_antisymm (not_lt.1 hc) (N.cap_nonneg u v)
  have hLsum : hopDemand dem dist = L u₀ v₀ * A' := by
    rw [← hLtot, hA', mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun v _ => ?_
    by_cases hc : 0 < N.cap u v
    · rw [ite_eq_left hc, mul_one, (hLc u v hc).1]
    · rw [ite_eq_right hc, mul_zero, hLzero u v hc]
  have hA'pos : A' ≠ 0 := by
    intro h; rw [h, mul_zero] at hLsum; exact hD.ne' hLsum
  have hc0 : L u₀ v₀ ≠ 0 := by
    intro h; rw [h, zero_mul] at hLsum; exact hD.ne' hLsum
  set θ := (∑ u, ∑ v, N.cap u v) / hopDemand dem dist with hθ
  have hθpos : 0 < θ := div_pos (by rw [hcapsum]; exact lt_of_lt_of_le h₀ (by
    have : (1 : ℚ) ≤ A' := by
      rw [hA']
      calc (1 : ℚ) = if 0 < N.cap u₀ v₀ then (1 : ℚ) else 0 := by rw [ite_eq_left h₀]
        _ ≤ ∑ v, if 0 < N.cap u₀ v then (1 : ℚ) else 0 :=
            single_le_sum (f := fun v => if 0 < N.cap u₀ v then (1 : ℚ) else 0)
              (fun v _ => by split_ifs <;> norm_num) (mem_univ v₀)
        _ ≤ ∑ u, ∑ v, if 0 < N.cap u v then (1 : ℚ) else 0 :=
            single_le_sum (f := fun u => ∑ v, if 0 < N.cap u v then (1 : ℚ) else 0)
              (fun u _ => sum_nonneg fun v _ => by split_ifs <;> norm_num) (mem_univ u₀)
    nlinarith)) hD
  have hθc : θ * L u₀ v₀ = N.cap u₀ v₀ := by
    rw [hθ, hcapsum, hLsum, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hc0 hA'pos)]
    ring
  have hload : ∀ u v, ∑ d, θ * g d u v = θ * L u v := fun u v => by rw [← mul_sum]
  clear_value g L θ
  refine ⟨{ f := fun d u v => θ * g d u v
            nonneg := fun d u v => mul_nonneg hθpos.le (gnn d u v)
            conserve := fun d v hv => by
              rw [← mul_sum, ← mul_sum, ← mul_sub, gcons d v hv, one_mul]
            capacity := fun u v => ?_ }, fun d u v h => ?_, fun u v huv => ?_⟩
  · show ∑ d, θ * g d u v ≤ N.cap u v
    rw [hload]
    by_cases hc : 0 < N.cap u v
    · rw [(hLc u v hc).1, (hLc u v hc).2, hθc]
    · rw [hLzero u v hc, mul_zero]; exact N.cap_nonneg u v
  · exact (gsupp d u v ((mul_pos_iff_of_pos_left hθpos).1 h)).2
  · show ∑ d, θ * g d u v = N.cap u v
    rw [hload, (hLc u v huv).1, (hLc u v huv).2, hθc]

/-- **Minimal routing is optimal on arc-transitive networks.**  Let `Dn` be a hop distance with
natural values (`Dn v d = 0` only for `v = d`, dropping by at most one along every link of
positive capacity, and by exactly one along some link out of every `v ≠ d`), and suppose the
automorphisms of the network, the traffic and the distance act transitively on the links.  Then
the largest throughput at which the nonnegative traffic `dem` is routable, by any routing, is
`∑ cap / ∑ dem * dist`, and it is reached by a minimal flow, which loads every link to exactly its
capacity. -/
theorem symmetric_opt (N : Net V) (dem : V → V → ℚ) (hdem : ∀ s d, 0 ≤ dem s d)
    (Dn : V → V → ℕ) (hzero : ∀ v d, Dn v d = 0 ↔ v = d)
    (hhop : ∀ u v d, 0 < N.cap u v → Dn u d ≤ Dn v d + 1)
    (hstep : ∀ v d, v ≠ d → ∃ w, 0 < N.cap v w ∧ Dn w d + 1 = Dn v d)
    (hT : ArcTransitive N dem fun u d => (Dn u d : ℚ))
    (hD : 0 < hopDemand dem fun u d => (Dn u d : ℚ)) :
    IsGreatest {θ : ℚ | Routable N dem θ}
        ((∑ u, ∑ v, N.cap u v) / hopDemand dem fun u d => (Dn u d : ℚ)) ∧
      ∃ F : Flow N dem ((∑ u, ∑ v, N.cap u v) / hopDemand dem fun u d => (Dn u d : ℚ)),
        F.Minimal fun u d => (Dn u d : ℚ) := by
  obtain ⟨R, hR⟩ := exists_geodesic_freeFlow N dem hdem Dn hzero hstep
  have hdd : ∀ d, ((Dn d d : ℕ) : ℚ) = 0 := fun d => by rw [(hzero d d).2 rfl]; rfl
  obtain ⟨F, hF, hsat⟩ := symmetric_balanced (dist := fun u d => (Dn u d : ℚ)) R
    (fun d u v h => by have := hR d u v h; exact_mod_cast this) hdd hT hD
  have hhd : IsHopDistance N fun u d => (Dn u d : ℚ) := ⟨hdd, fun u v d hc => by
    have := hhop u v d hc
    simp only
    have : ((Dn u d : ℕ) : ℚ) ≤ (Dn v d : ℕ) + 1 := by exact_mod_cast this
    linarith⟩
  refine ⟨(balanced_opt F hhd hF hsat hD).1, F, fun d u v h => ?_⟩
  have := hF d u v h
  simp only at this ⊢
  linarith

omit [DecidableEq V] in
/-- A smaller nonnegative throughput is routable too. -/
theorem Routable.of_le {N : Net V} {dem : V → V → ℚ} {θ θ' : ℚ} (h : Routable N dem θ)
    (hθ : 0 < θ) (h0 : 0 ≤ θ') (hle : θ' ≤ θ) : Routable N dem θ' := by
  obtain ⟨F⟩ := h
  have hr : 0 ≤ θ' / θ := div_nonneg h0 hθ.le
  have hr1 : θ' / θ ≤ 1 := (div_le_one₀ hθ).2 hle
  refine ⟨{ f := fun d u v => θ' / θ * F.f d u v
            nonneg := fun d u v => mul_nonneg hr (F.nonneg d u v)
            conserve := fun d v hv => ?_
            capacity := fun u v => ?_ }⟩
  · rw [← mul_sum, ← mul_sum, ← mul_sub, F.conserve d v hv, ← mul_assoc,
      div_mul_cancel₀ _ hθ.ne']
  · rw [← mul_sum]
    have hl : 0 ≤ ∑ d, F.f d u v := sum_nonneg fun d _ => F.nonneg d u v
    calc θ' / θ * ∑ d, F.f d u v ≤ 1 * ∑ d, F.f d u v := mul_le_mul_of_nonneg_right hr1 hl
      _ = ∑ d, F.f d u v := one_mul _
      _ ≤ N.cap u v := F.capacity u v

/-- The traffic times the distance for a demand constant off the diagonal (`dist d d = 0`). -/
theorem hopDemand_offdiag (c : ℚ) (dist : V → V → ℚ) (hdd : ∀ d, dist d d = 0) :
    hopDemand (fun s d => if s = d then 0 else c) dist = c * ∑ s, ∑ d, dist s d := by
  unfold hopDemand
  rw [mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun d _ => ?_
  by_cases h : s = d
  · subst h; simp [hdd]
  · simp [h]

omit [DecidableEq V] in
/-- The traffic times the distance for a constant demand. -/
theorem hopDemand_const (c : ℚ) (dist : V → V → ℚ) :
    hopDemand (fun _ _ => c) dist = c * ∑ s, ∑ d, dist s d := by
  unfold hopDemand
  simp only [mul_sum]

end General

end Fluid

end AsyncLean
