/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Valiant
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.BigOperators

/-!
# Symmetric networks: minimal routing is optimal for uniform traffic

On a network whose automorphisms act transitively on the links (the torus, the hypercube),
traffic invariant under the automorphisms is routed optimally by a **minimal** flow (no
detours), and the optimum is the total capacity divided by the traffic times the hop distance.

**General theory** (any network `N`, traffic `dem`, distance `dist`):

* `IsHopDistance N dist` : `dist d d = 0` and `dist u d - dist v d ≤ 1` on every link of positive
  capacity; `hopDemand dem dist = ∑ s d, dem s d * dist s d`.
* `hop_bound` : any routing has `θ * ∑ dem * dist ≤ ∑ cap` (the potential bound, length `1`).
* `minimal_load_total` : a flow in which every used link brings its commodity one hop closer
  (`Flow.Minimal.drop_one`: true of every minimal flow for a distance with natural values) has
  total load exactly `θ * ∑ dem * dist` (telescoping).
* `balanced_opt` : **a geodesic flow loading every link of positive capacity to exactly its
  capacity is optimal** (`IsGreatest`), with value `∑ cap / ∑ dem * dist`.
* `FreeFlow`, `exists_geodesic_freeFlow` : if every `v ≠ d` has a neighbour one hop closer to `d`,
  greedy walks give a geodesic flow ignoring capacities.
* `IsAut`, `ArcTransitive` : automorphisms of `(N, dem, dist)` and transitivity on the links.
  `symmetric_balanced` : averaging a geodesic free flow over all automorphisms loads every link
  equally, so scaled to `∑ cap / ∑ dem * dist` it saturates every link.
* `symmetric_opt` : **on an arc-transitive network, minimal routing is optimal**: the optimum is
  `∑ cap / ∑ dem * dist`, reached by a minimal flow.

**The torus** `torusNet k` (`torus_symmetric_opt`, for every permutation-invariant traffic): its
automorphisms (rotations `torusShift`, the reflection `torusNeg`, the exchange `torusSwap`) are
transitive on the links (`torus_arcTransitive`); `torus_sum_cap`, `torus_sum_dist` (via
`ringTotal`: `m²` for `k = 2m`, `m (m + 1)` for `k = 2m + 1`).

* `torus_uniform_opt` : uniform traffic (`uniform k`, `k ≥ 3`): the optimum is `16 (k² - 1) / k³`
  for even `k` and `16 / k` for odd `k`, reached by a minimal flow; `63/32` for `k = 8`
  (`torus_uniform_opt_eight`); `3` for `k = 2` (`torus_uniform_opt_two`: the two links between
  the positions of a ring of length `2` coincide).
* `torus_self_opt` : uniform traffic including self (`1 / k²` for every pair): `16 / k` for even
  `k ≥ 4`, `16 k / (k² - 1)` for odd `k`; `torus_self_routable` : routable at `16 / k` for every
  `k ≥ 3`; `4` for `k = 2` (`torus_self_opt_two`).

**The hypercube** `cubeNet n` (`cube_symmetric_opt`): translations `cubeXor` and permutations of
the coordinates `cubePerm` (`cube_arcTransitive`); `cube_sum_cap = 2 n 2ⁿ`,
`cube_sum_dist = n 2ⁿ 2ⁿ / 2`.

* `cube_uniform_opt` : uniform traffic (`cubeUniform n`, `n ≥ 1`): the optimum is
  `4 (2ⁿ - 1) / 2ⁿ`, reached by a minimal flow; `63/16` for `n = 6` (`cube_uniform_opt_six`).
* `cube_self_opt`, `cube_self_routable` : uniform traffic including self (`1 / 2ⁿ`): the optimum
  is `4`.

**Worst case** (with `AsyncLean.Flow.Valiant`): `torus_worst_opt'` (even `k ≥ 4`: `8 / k`) and
`cube_worst_opt'` (`n ≥ 1`: `2`), unconditionally.

All results are over `ℚ`.
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

/-! ### The torus -/

section Ring

variable {k : ℕ}

/-- Reducing a number below `2k` modulo `k`. -/
theorem mod_of_lt_two {x k : ℕ} (h : x < 2 * k) : x % k = if x < k then x else x - k := by
  split_ifs with hx
  · exact Nat.mod_eq_of_lt hx
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The value of a sum on the ring. -/
theorem ring_val_add (a c : Fin k) :
    ((a + c : Fin k) : ℕ) = if (a : ℕ) + c < k then (a : ℕ) + c else (a : ℕ) + c - k := by
  rw [Fin.val_add, mod_of_lt_two (by omega)]

/-- The value of a difference on the ring. -/
theorem ring_val_sub (a c : Fin k) :
    ((a - c : Fin k) : ℕ) = if (c : ℕ) ≤ a then (a : ℕ) - c else k - c + a := by
  rw [Fin.val_sub, mod_of_lt_two (by omega)]
  split_ifs <;> omega

/-- The value of a negation on the ring. -/
theorem ring_val_neg (a : Fin k) : ((-a : Fin k) : ℕ) = if (a : ℕ) = 0 then 0 else k - a := by
  rw [Fin.val_neg', mod_of_lt_two (by omega)]
  split_ifs <;> omega

/-- The ring distance in terms of the values. -/
theorem ringDist_val (a b : Fin k) :
    ringDist a b = min (if (b : ℕ) ≤ a then (a : ℕ) - b else (a : ℕ) + k - b)
      (if (a : ℕ) ≤ b then (b : ℕ) - a else (b : ℕ) + k - a) := by
  unfold ringDist
  rw [mod_of_lt_two (by omega), mod_of_lt_two (by omega)]
  congr 1 <;> split_ifs <;> omega

/-- Ring adjacency in terms of the values. -/
theorem ringAdj_iff (a b : Fin k) :
    RingAdj a b ↔ ((a : ℕ) + 1 = b ∨ ((a : ℕ) + 1 = k ∧ (b : ℕ) = 0)) ∨
      ((b : ℕ) + 1 = a ∨ ((b : ℕ) + 1 = k ∧ (a : ℕ) = 0)) := by
  unfold RingAdj
  rw [mod_of_lt_two (by omega), mod_of_lt_two (by omega)]
  constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

/-- Rotations are injective. -/
theorem ring_add_right_inj (a b c : Fin k) : a + c = b + c ↔ a = b := by
  rw [Fin.ext_iff, Fin.ext_iff, ring_val_add, ring_val_add]
  split_ifs <;> omega

/-- The reflection is injective. -/
theorem ring_neg_inj (a b : Fin k) : -a = -b ↔ a = b := by
  rw [Fin.ext_iff, Fin.ext_iff, ring_val_neg, ring_val_neg]
  split_ifs <;> omega

/-- The rotation `a ↦ a + c` of the ring. -/
def ringShift (c : Fin k) : Equiv.Perm (Fin k) where
  toFun a := a + c
  invFun a := a - c
  left_inv a := Fin.ext (by rw [ring_val_sub, ring_val_add]; split_ifs <;> omega)
  right_inv a := Fin.ext (by rw [ring_val_add, ring_val_sub]; split_ifs <;> omega)

/-- The reflection `a ↦ -a` of the ring. -/
def ringNeg : Equiv.Perm (Fin k) where
  toFun a := -a
  invFun a := -a
  left_inv a := Fin.ext (by rw [ring_val_neg, ring_val_neg]; split_ifs <;> omega)
  right_inv a := Fin.ext (by rw [ring_val_neg, ring_val_neg]; split_ifs <;> omega)

/-- Rotations preserve adjacency. -/
theorem ringAdj_shift (a b c : Fin k) : RingAdj (a + c) (b + c) ↔ RingAdj a b := by
  rw [ringAdj_iff, ringAdj_iff, ring_val_add, ring_val_add]
  constructor <;> intro h <;> split_ifs at h ⊢ <;> omega

/-- Rotations preserve the distance. -/
theorem ringDist_shift (a b c : Fin k) : ringDist (a + c) (b + c) = ringDist a b := by
  rw [ringDist_val, ringDist_val, ring_val_add, ring_val_add]
  split_ifs <;> omega

/-- The reflection preserves adjacency. -/
theorem ringAdj_neg (a b : Fin k) : RingAdj (-a) (-b) ↔ RingAdj a b := by
  rw [ringAdj_iff, ringAdj_iff]
  have ha := ring_val_neg a
  have hb := ring_val_neg b
  generalize ((-a : Fin k) : ℕ) = x at *
  generalize ((-b : Fin k) : ℕ) = y at *
  split_ifs at ha hb <;> constructor <;> intro h <;> omega

/-- The reflection preserves the distance. -/
theorem ringDist_neg (a b : Fin k) : ringDist (-a) (-b) = ringDist a b := by
  rw [ringDist_val, ringDist_val, ring_val_neg, ring_val_neg]
  split_ifs <;> omega

/-- The ring distance vanishes only on the diagonal. -/
theorem ringDist_eq_zero (a b : Fin k) : ringDist a b = 0 ↔ a = b := by
  rw [ringDist_val, Fin.ext_iff]
  split_ifs <;> omega

/-- Along a link of the ring the distance drops by at most one. -/
theorem ringDist_le_of_adj {a b : Fin k} (h : RingAdj a b) (t : Fin k) :
    ringDist a t ≤ ringDist b t + 1 := by
  rw [ringAdj_iff] at h
  rw [ringDist_val, ringDist_val]
  split_ifs <;> omega

/-- Every position other than `t` has a neighbour one step closer to `t`. -/
theorem ring_step {a t : Fin k} (h : a ≠ t) :
    ∃ b, RingAdj a b ∧ ringDist b t + 1 = ringDist a t := by
  have h' : (a : ℕ) ≠ t := fun e => h (Fin.ext e)
  by_cases hx : (if (t : ℕ) ≤ a then (a : ℕ) - t else (a : ℕ) + k - t) ≤
      (if (a : ℕ) ≤ t then (t : ℕ) - a else (t : ℕ) + k - a)
  · refine ⟨⟨if (a : ℕ) = 0 then k - 1 else (a : ℕ) - 1, by split_ifs <;> omega⟩, ?_, ?_⟩
    · rw [ringAdj_iff]; simp only; split_ifs <;> omega
    · rw [ringDist_val, ringDist_val]; simp only; split_ifs at hx ⊢ <;> omega
  · refine ⟨⟨if (a : ℕ) + 1 = k then 0 else (a : ℕ) + 1, by split_ifs <;> omega⟩, ?_, ?_⟩
    · rw [ringAdj_iff]; simp only; split_ifs <;> omega
    · rw [ringDist_val, ringDist_val]; simp only; split_ifs at hx ⊢ <;> omega

end Ring

section Torus

variable {k : ℕ}

/-- The hop distance of the torus with natural values. -/
def torusHops (u v : Fin k × Fin k) : ℕ := ringDist u.1 v.1 + ringDist u.2 v.2

/-- The torus distance is the cast of `torusHops`. -/
theorem torusDist_eq : (torusDist : Fin k × Fin k → Fin k × Fin k → ℚ) =
    fun u v => (torusHops u v : ℚ) := rfl

/-- The links of the torus are its neighbours. -/
theorem torus_cap_pos {u v : Fin k × Fin k} : 0 < (torusNet k).cap u v ↔ TorusAdj u v := by
  show 0 < ite _ _ _ ↔ _
  split_ifs with h <;> simp [h]

/-- The rotation of the torus by `c`. -/
def torusShift (c : Fin k × Fin k) : Equiv.Perm (Fin k × Fin k) :=
  Equiv.prodCongr (ringShift c.1) (ringShift c.2)

/-- The reflection of the first coordinate of the torus. -/
def torusNeg : Equiv.Perm (Fin k × Fin k) := Equiv.prodCongr ringNeg (Equiv.refl _)

/-- The exchange of the coordinates of the torus. -/
def torusSwap : Equiv.Perm (Fin k × Fin k) := Equiv.prodComm _ _

/-- The rotation, applied. -/
theorem torusShift_apply (c u : Fin k × Fin k) : torusShift c u = (u.1 + c.1, u.2 + c.2) := rfl

/-- The reflection, applied. -/
theorem torusNeg_apply (u : Fin k × Fin k) : torusNeg u = (-u.1, u.2) := rfl

/-- The exchange of coordinates, applied. -/
theorem torusSwap_apply (u : Fin k × Fin k) : torusSwap u = u.swap := rfl

/-- A permutation preserving adjacency and hop distance of the torus is an automorphism for any
traffic matrix invariant under all permutations. -/
theorem torus_isAut {dem : Fin k × Fin k → Fin k × Fin k → ℚ}
    (hdem : ∀ σ : Equiv.Perm (Fin k × Fin k), ∀ s d, dem (σ s) (σ d) = dem s d)
    (σ : Equiv.Perm (Fin k × Fin k)) (hA : ∀ u v, TorusAdj (σ u) (σ v) ↔ TorusAdj u v)
    (hD : ∀ u v, torusHops (σ u) (σ v) = torusHops u v) :
    IsAut (torusNet k) dem torusDist σ :=
  ⟨fun u v => by show ite _ _ _ = ite _ _ _; simp only [hA], hdem σ,
    fun u v => by simp only [torusDist_eq, hD]⟩

/-- Rotations are automorphisms of the torus. -/
theorem torusShift_isAut {dem : Fin k × Fin k → Fin k × Fin k → ℚ}
    (hdem : ∀ σ : Equiv.Perm (Fin k × Fin k), ∀ s d, dem (σ s) (σ d) = dem s d)
    (c : Fin k × Fin k) : IsAut (torusNet k) dem torusDist (torusShift c) :=
  torus_isAut hdem _ (fun u v => by
      simp only [torusShift_apply, TorusAdj, ringAdj_shift, ring_add_right_inj])
    (fun u v => by simp only [torusShift_apply, torusHops, ringDist_shift])

/-- The reflection is an automorphism of the torus. -/
theorem torusNeg_isAut {dem : Fin k × Fin k → Fin k × Fin k → ℚ}
    (hdem : ∀ σ : Equiv.Perm (Fin k × Fin k), ∀ s d, dem (σ s) (σ d) = dem s d) :
    IsAut (torusNet k) dem torusDist torusNeg :=
  torus_isAut hdem _ (fun u v => by simp only [torusNeg_apply, TorusAdj, ringAdj_neg, ring_neg_inj])
    (fun u v => by simp only [torusNeg_apply, torusHops, ringDist_neg])

/-- The exchange of coordinates is an automorphism of the torus. -/
theorem torusSwap_isAut {dem : Fin k × Fin k → Fin k × Fin k → ℚ}
    (hdem : ∀ σ : Equiv.Perm (Fin k × Fin k), ∀ s d, dem (σ s) (σ d) = dem s d) :
    IsAut (torusNet k) dem torusDist torusSwap :=
  torus_isAut hdem _ (fun u v => by
      show TorusAdj u.swap v.swap ↔ TorusAdj u v
      unfold TorusAdj
      simp only [Prod.fst_swap, Prod.snd_swap]
      exact or_comm)
    (fun u v => by simp only [torusSwap_apply, torusHops, Prod.fst_swap, Prod.snd_swap]; omega)

/-- **The torus is arc-transitive** (`k ≥ 2`): rotations, the reflection and the exchange of the
coordinates map every link to the link `(0, 0) → (1, 0)`. -/
theorem torus_arcTransitive (hk : 2 ≤ k) {dem : Fin k × Fin k → Fin k × Fin k → ℚ}
    (hdem : ∀ σ : Equiv.Perm (Fin k × Fin k), ∀ s d, dem (σ s) (σ d) = dem s d) :
    ArcTransitive (torusNet k) dem torusDist := by
  set z : Fin k := ⟨0, by omega⟩ with hz
  set o : Fin k := ⟨1, by omega⟩ with ho
  have horiz : ∀ u v : Fin k × Fin k, u.2 = v.2 → RingAdj u.1 v.1 →
      ∃ σ, IsAut (torusNet k) dem torusDist σ ∧ σ u = (z, z) ∧ σ v = (o, z) := by
    intro u v h2 h1
    have h2' : (u.2 : ℕ) = v.2 := congrArg _ h2
    rw [ringAdj_iff] at h1
    by_cases hf : (u.1 : ℕ) + 1 = v.1 ∨ ((u.1 : ℕ) + 1 = k ∧ (v.1 : ℕ) = 0)
    · refine ⟨torusShift (-u.1, -u.2), torusShift_isAut hdem _, ?_, ?_⟩ <;>
        simp only [torusShift_apply, Prod.ext_iff, Fin.ext_iff, ring_val_add, ring_val_neg,
          hz, ho] <;> split_ifs <;> omega
    · refine ⟨(torusShift (-u.1, -u.2)).trans torusNeg,
        (torusShift_isAut hdem _).trans (torusNeg_isAut hdem), ?_, ?_⟩ <;>
        simp only [Equiv.trans_apply, torusShift_apply, torusNeg_apply, Prod.ext_iff,
          Fin.ext_iff, ring_val_add, ring_val_neg, hz, ho] <;> split_ifs <;> omega
  refine ArcTransitive.of_base (z, z) (o, z) fun u v h => ?_
  rcases torus_cap_pos.1 h with ⟨h2, h1⟩ | ⟨h2, h1⟩
  · exact horiz u v h2 h1
  · obtain ⟨σ, hσ, hu, hv⟩ := horiz u.swap v.swap h2 h1
    exact ⟨torusSwap.trans σ, (torusSwap_isAut hdem).trans hσ, hu, hv⟩

/-- The torus hop distance vanishes only on the diagonal. -/
theorem torusHops_eq_zero (u v : Fin k × Fin k) : torusHops u v = 0 ↔ u = v := by
  unfold torusHops
  rw [Prod.ext_iff, ← ringDist_eq_zero, ← ringDist_eq_zero]
  omega

/-- Along a link of the torus the hop distance drops by at most one. -/
theorem torusHops_le_of_cap {u v : Fin k × Fin k} (h : 0 < (torusNet k).cap u v)
    (d : Fin k × Fin k) : torusHops u d ≤ torusHops v d + 1 := by
  unfold torusHops
  rcases torus_cap_pos.1 h with ⟨h2, h1⟩ | ⟨h2, h1⟩
  · have := ringDist_le_of_adj h1 d.1; rw [h2]; omega
  · have := ringDist_le_of_adj h1 d.2; rw [h2]; omega

/-- Every vertex other than `d` has a neighbour one hop closer to `d`. -/
theorem torus_step {v d : Fin k × Fin k} (h : v ≠ d) :
    ∃ w, 0 < (torusNet k).cap v w ∧ torusHops w d + 1 = torusHops v d := by
  unfold torusHops
  by_cases h1 : v.1 = d.1
  · have h2 : v.2 ≠ d.2 := fun e => h (Prod.ext h1 e)
    obtain ⟨b, hb, hd⟩ := ring_step h2
    exact ⟨(v.1, b), torus_cap_pos.2 (Or.inr ⟨rfl, hb⟩), by simp only; omega⟩
  · obtain ⟨b, hb, hd⟩ := ring_step h1
    exact ⟨(b, v.2), torus_cap_pos.2 (Or.inl ⟨rfl, hb⟩), by simp only; omega⟩

/-- **Minimal routing is optimal on the torus** (`k ≥ 2`), for every nonnegative traffic matrix
invariant under all permutations of the vertices: the optimum is `∑ cap / ∑ dem * dist`, reached
by a minimal flow. -/
theorem torus_symmetric_opt (hk : 2 ≤ k) (dem : Fin k × Fin k → Fin k × Fin k → ℚ)
    (hnn : ∀ s d, 0 ≤ dem s d)
    (hdem : ∀ σ : Equiv.Perm (Fin k × Fin k), ∀ s d, dem (σ s) (σ d) = dem s d)
    (hD : 0 < hopDemand dem torusDist) :
    IsGreatest {θ : ℚ | Routable (torusNet k) dem θ}
        ((∑ u, ∑ v, (torusNet k).cap u v) / hopDemand dem torusDist) ∧
      ∃ F : Flow (torusNet k) dem ((∑ u, ∑ v, (torusNet k).cap u v) / hopDemand dem torusDist),
        F.Minimal torusDist :=
  symmetric_opt (torusNet k) dem hnn torusHops torusHops_eq_zero
    (fun _ _ d h => torusHops_le_of_cap h d) (fun _ _ h => torus_step h)
    (torus_arcTransitive hk hdem) hD

/-- `∑ j < k, min (k - j) j`: the total ring distance from one position. -/
def ringTotal (k : ℕ) : ℚ := ∑ j ∈ range k, ((min (k - j) j : ℕ) : ℚ)

/-- The total ring distance from any position is `ringTotal k`. -/
theorem ring_sum (a : Fin k) : ∑ b, (ringDist a b : ℚ) = ringTotal k := by
  have hk : 0 < k := Fin.pos a
  set z : Fin k := ⟨0, hk⟩
  have hza : z + a = a := Fin.ext (by rw [ring_val_add]; split_ifs <;> simp_all [z])
  rw [← Equiv.sum_comp (ringShift a) (fun b => (ringDist a b : ℚ))]
  have e : ∀ b, ringDist a (ringShift a b) = min (k - b) b := fun b => by
    show ringDist a (b + a) = _
    have h := ringDist_shift z b a
    rw [hza] at h
    rw [h, ringDist_val]
    simp only [z]
    split_ifs <;> omega
  simp only [e]
  exact Fin.sum_univ_eq_sum_range (fun j => ((min (k - j) j : ℕ) : ℚ)) k

/-- `ringTotal (2m) = m²`. -/
theorem ringTotal_even (m : ℕ) : ringTotal (m + m) = m * m := by
  unfold ringTotal
  rw [sum_range_add]
  have e1 : ∀ j ∈ range m, ((min (m + m - j) j : ℕ) : ℚ) = j := fun j hj => by
    simp at hj; congr 1; omega
  have e2 : ∀ j ∈ range m, ((min (m + m - (m + j)) (m + j) : ℕ) : ℚ) = m - j := fun j hj => by
    simp at hj; rw [show min (m + m - (m + j)) (m + j) = m - j by omega, Nat.cast_sub hj.le]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_sub_distrib, sum_range_cast]
  simp only [sum_const, card_range, nsmul_eq_mul]; ring

/-- `ringTotal (2m + 1) = m (m + 1)`. -/
theorem ringTotal_odd (m : ℕ) : ringTotal (m + m + 1) = m * m + m := by
  unfold ringTotal
  rw [show m + m + 1 = (m + 1) + m by omega, sum_range_add]
  have e1 : ∀ j ∈ range (m + 1), ((min (m + 1 + m - j) j : ℕ) : ℚ) = j := fun j hj => by
    simp at hj; congr 1; omega
  have e2 : ∀ j ∈ range m, ((min (m + 1 + m - (m + 1 + j)) (m + 1 + j) : ℕ) : ℚ) = m - j :=
    fun j hj => by
      simp at hj
      rw [show min (m + 1 + m - (m + 1 + j)) (m + 1 + j) = m - j by omega, Nat.cast_sub hj.le]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_sub_distrib, sum_range_cast, sum_range_cast]
  simp only [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-- Summing a function of the second coordinate over the grid. -/
theorem sum_snd' (g : Fin k → ℚ) : ∑ s : Fin k × Fin k, g s.2 = k * ∑ i, g i := by
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The total hop distance of the torus over all ordered pairs: `2 k³ ringTotal k`. -/
theorem torus_sum_dist :
    ∑ s : Fin k × Fin k, ∑ d : Fin k × Fin k, torusDist s d = 2 * k ^ 3 * ringTotal k := by
  have e : ∀ s : Fin k × Fin k, ∑ d : Fin k × Fin k, torusDist s d = 2 * k * ringTotal k := by
    intro s
    simp only [torusDist, Nat.cast_add, sum_add_distrib]
    rw [sum_fst (fun i => (ringDist s.1 i : ℚ)), sum_snd' (fun i => (ringDist s.2 i : ℚ)),
      ring_sum, ring_sum]
    ring
  simp only [e, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- The number of ring neighbours of a position: `1` for `k = 2`, `2` for `k ≥ 3`. -/
theorem ring_deg (hk : 2 ≤ k) (a : Fin k) :
    ∑ b, (if RingAdj a b then (1 : ℚ) else 0) = if k = 2 then 1 else 2 := by
  set s₁ := if (a : ℕ) + 1 = k then 0 else (a : ℕ) + 1
  set s₂ := if (a : ℕ) = 0 then k - 1 else (a : ℕ) - 1
  have h1 : s₁ < k := by simp only [s₁]; split_ifs <;> omega
  have h2 : s₂ < k := by simp only [s₂]; split_ifs <;> omega
  have e : ∀ b : Fin k, RingAdj a b ↔ ((b : ℕ) = s₁ ∨ (b : ℕ) = s₂) := fun b => by
    rw [ringAdj_iff]; simp only [s₁, s₂]
    constructor <;> intro h <;> split_ifs at h ⊢ <;> omega
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun j => if j = s₁ ∨ j = s₂ then (1 : ℚ) else 0) k]
  by_cases h2k : k = 2
  · have hs : s₁ = s₂ := by simp only [s₁, s₂]; split_ifs <;> omega
    rw [ite_eq_left h2k]
    simp only [hs, or_self, sum_ite_eq', mem_range, h2, ite_true]
  · have hs : s₁ ≠ s₂ := by simp only [s₁, s₂]; split_ifs <;> omega
    rw [ite_eq_right h2k]
    have : ∀ j, (if j = s₁ ∨ j = s₂ then (1 : ℚ) else 0) =
        (if j = s₁ then 1 else 0) + (if j = s₂ then 1 else 0) := fun j => by
      by_cases j1 : j = s₁ <;> by_cases j2 : j = s₂ <;> simp [j1, j2] <;> omega
    simp only [this, sum_add_distrib, sum_ite_eq', mem_range, h1, h2, ite_true]
    norm_num

/-- The total capacity of the torus (`k ≥ 2`): `4 k² r` with `r = 2` (`r = 1` for `k = 2`, where
the two links between two positions of a ring coincide). -/
theorem torus_sum_cap (hk : 2 ≤ k) :
    ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k, (torusNet k).cap u v =
      4 * k ^ 2 * (if k = 2 then 1 else 2) := by
  have hne : ∀ a b : Fin k, RingAdj a b → a ≠ b := fun a b h e => by
    subst e; rw [ringAdj_iff] at h; omega
  have e : ∀ u v : Fin k × Fin k, (torusNet k).cap u v =
      2 * ((if u.2 = v.2 then 1 else 0) * (if RingAdj u.1 v.1 then (1 : ℚ) else 0)) +
        2 * ((if u.1 = v.1 then 1 else 0) * (if RingAdj u.2 v.2 then (1 : ℚ) else 0)) := by
    intro u v
    have p : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
        (if P then (1 : ℚ) else 0) * (if Q then 1 else 0) = if P ∧ Q then 1 else 0 := by
      intro P Q _ _; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
    show ite _ _ _ = _
    rw [p, p]
    by_cases hA : u.2 = v.2 ∧ RingAdj u.1 v.1 <;> by_cases hB : u.1 = v.1 ∧ RingAdj u.2 v.2
    · exact absurd hB.1 (hne _ _ hA.2)
    · rw [ite_eq_left (show TorusAdj u v from Or.inl hA), ite_eq_left hA, ite_eq_right hB]
      norm_num
    · rw [ite_eq_left (show TorusAdj u v from Or.inr hB), ite_eq_right hA, ite_eq_left hB]
      norm_num
    · rw [ite_eq_right (fun h : TorusAdj u v => Or.elim h hA hB), ite_eq_right hA,
        ite_eq_right hB]
      norm_num
  have hu : ∀ u : Fin k × Fin k, ∑ v : Fin k × Fin k, (torusNet k).cap u v =
      4 * (if k = 2 then 1 else 2) := by
    intro u
    simp only [e, sum_add_distrib, ← mul_sum, Fintype.sum_prod_type]
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    rw [sum_comm (f := fun x y => if u.1 = x then (if RingAdj u.2 y then (1 : ℚ) else 0) else 0)]
    simp only [sum_ite_eq, mem_univ, ite_true, ring_deg hk]
    ring
  simp only [hu, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- The optimum of a permutation-invariant traffic matrix on the torus, given its value `θ`:
`θ * ∑ dem * dist = ∑ cap`. -/
theorem torus_opt_of (hk : 2 ≤ k) (dem : Fin k × Fin k → Fin k × Fin k → ℚ)
    (hnn : ∀ s d, 0 ≤ dem s d)
    (hdem : ∀ σ : Equiv.Perm (Fin k × Fin k), ∀ s d, dem (σ s) (σ d) = dem s d)
    (hD : 0 < hopDemand dem torusDist) (θ : ℚ)
    (hθ : θ * hopDemand dem torusDist = 4 * k ^ 2 * (if k = 2 then 1 else 2)) :
    IsGreatest {θ : ℚ | Routable (torusNet k) dem θ} θ ∧
      ∃ F : Flow (torusNet k) dem θ, F.Minimal torusDist := by
  have e : (∑ u, ∑ v, (torusNet k).cap u v) / hopDemand dem torusDist = θ := by
    rw [torus_sum_cap hk, ← hθ, mul_div_cancel_right₀ _ hD.ne']
  rw [← e]
  exact torus_symmetric_opt hk dem hnn hdem hD

/-- Uniform traffic is invariant under all permutations. -/
theorem uniform_perm (σ : Equiv.Perm (Fin k × Fin k)) (s d : Fin k × Fin k) :
    uniform k (σ s) (σ d) = uniform k s d := by
  unfold uniform; simp only [σ.injective.eq_iff]

/-- `ringTotal k > 0` for `k ≥ 2`. -/
theorem ringTotal_pos (hk : 2 ≤ k) : 0 < ringTotal k := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [ringTotal_even]
    have : (1 : ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    nlinarith
  · rw [show 2 * m + 1 = m + m + 1 by ring, ringTotal_odd]
    have : (1 : ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    nlinarith

/-- Uniform traffic on the torus: `∑ dem * dist = 2 k³ ringTotal k / (k² - 1)`. -/
theorem torus_hop_uniform :
    hopDemand (uniform k) torusDist = 2 * k ^ 3 * ringTotal k / ((k : ℚ) ^ 2 - 1) := by
  rw [show uniform k = fun s d => if s = d then 0 else 1 / ((k : ℚ) ^ 2 - 1) from rfl,
    hopDemand_offdiag _ _ (fun d => by
      rw [torusDist_eq]; simp only [Nat.cast_eq_zero]; exact (torusHops_eq_zero d d).2 rfl),
    torus_sum_dist, one_div_mul_eq_div]

/-- Uniform traffic including self on the torus: `∑ dem * dist = 2 k³ ringTotal k / k²`. -/
theorem torus_hop_self :
    hopDemand (fun _ _ : Fin k × Fin k => 1 / (k ^ 2 : ℚ)) torusDist =
      2 * k ^ 3 * ringTotal k / (k : ℚ) ^ 2 := by
  rw [hopDemand_const, torus_sum_dist, one_div_mul_eq_div]

/-- **Uniform traffic on the torus** (`k ≥ 3`): the optimal throughput, over all routings, is
`16 (k² - 1) / k³` for even `k` and `16 / k` for odd `k`, and it is reached by a minimal flow
(no detours) loading every link to exactly its capacity. -/
theorem torus_uniform_opt (k : ℕ) (hk : 3 ≤ k) :
    IsGreatest {θ : ℚ | Routable (torusNet k) (uniform k) θ}
        (if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / k) ∧
      ∃ F : Flow (torusNet k) (uniform k)
          (if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / k), F.Minimal torusDist := by
  have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hD : 0 < hopDemand (uniform k) torusDist := by
    rw [torus_hop_uniform]
    exact div_pos (mul_pos (by positivity) (ringTotal_pos (by omega))) hK
  refine torus_opt_of (by omega) _ (fun s d => by
      unfold uniform; split_ifs
      · exact le_rfl
      · exact div_nonneg zero_le_one hK.le) uniform_perm hD _ ?_
  rw [torus_hop_uniform, ite_eq_right (show k ≠ 2 by omega)]
  split_ifs with he
  · obtain ⟨m, rfl⟩ := he
    rw [ringTotal_even, div_mul_div_comm, div_eq_iff (mul_ne_zero (by positivity) hK.ne')]
    push_cast; ring
  · obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.1 he
    rw [show 2 * m + 1 = m + m + 1 by ring, ringTotal_odd] at *
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero (by positivity) hK.ne')]
    push_cast; ring

/-- **Uniform traffic on the `2 × 2` torus**: the optimum is `3` (the two links between two
positions of a ring of length `2` coincide, so the torus has only half the links). -/
theorem torus_uniform_opt_two :
    IsGreatest {θ : ℚ | Routable (torusNet 2) (uniform 2) θ} 3 ∧
      ∃ F : Flow (torusNet 2) (uniform 2) 3, F.Minimal torusDist := by
  have hD : 0 < hopDemand (uniform 2) torusDist := by
    rw [torus_hop_uniform]
    exact div_pos (mul_pos (by positivity) (ringTotal_pos le_rfl)) (by norm_num)
  refine torus_opt_of le_rfl _ (fun s d => by unfold uniform; split_ifs <;> norm_num)
    uniform_perm hD 3 ?_
  rw [torus_hop_uniform, show (2 : ℕ) = 1 + 1 from rfl, ringTotal_even]
  norm_num

/-- **The `8 × 8` torus under uniform traffic**: the optimum is `63/32`. -/
theorem torus_uniform_opt_eight :
    IsGreatest {θ : ℚ | Routable (torusNet 8) (uniform 8) θ} (63 / 32) ∧
      ∃ F : Flow (torusNet 8) (uniform 8) (63 / 32), F.Minimal torusDist := by
  have := torus_uniform_opt 8 (by norm_num)
  rw [ite_eq_left (show Even 8 from ⟨4, rfl⟩),
    show (16 * (((8 : ℕ) : ℚ) ^ 2 - 1) / ((8 : ℕ) : ℚ) ^ 3 : ℚ) = 63 / 32 by norm_num] at this
  exact this

/-- **Uniform traffic including self on the torus** (demand `1 / k²` for every pair, `k ≥ 3`):
the optimal throughput is `16 / k` for even `k` and `16 k / (k² - 1)` for odd `k`, reached by a
minimal flow. -/
theorem torus_self_opt (k : ℕ) (hk : 3 ≤ k) :
    IsGreatest {θ : ℚ | Routable (torusNet k) (fun _ _ => 1 / (k ^ 2 : ℚ)) θ}
        (if Even k then 16 / k else 16 * k / ((k : ℚ) ^ 2 - 1)) ∧
      ∃ F : Flow (torusNet k) (fun _ _ => 1 / (k ^ 2 : ℚ))
          (if Even k then 16 / k else 16 * k / ((k : ℚ) ^ 2 - 1)), F.Minimal torusDist := by
  have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hD : 0 < hopDemand (fun _ _ : Fin k × Fin k => 1 / (k ^ 2 : ℚ)) torusDist := by
    rw [torus_hop_self]
    exact div_pos (mul_pos (by positivity) (ringTotal_pos (by omega))) (by positivity)
  refine torus_opt_of (by omega) _ (fun _ _ => div_nonneg zero_le_one (sq_nonneg _))
    (fun _ _ _ => rfl) hD _ ?_
  rw [torus_hop_self, ite_eq_right (show k ≠ 2 by omega)]
  split_ifs with he
  · obtain ⟨m, rfl⟩ := he
    rw [ringTotal_even, div_mul_div_comm, div_eq_iff (by positivity)]
    push_cast; ring
  · obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.1 he
    rw [show 2 * m + 1 = m + m + 1 by ring, ringTotal_odd] at *
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hK.ne' (by positivity))]
    push_cast; ring

/-- **Uniform traffic including self on the `2 × 2` torus**: the optimum is `4`. -/
theorem torus_self_opt_two :
    IsGreatest {θ : ℚ | Routable (torusNet 2) (fun _ _ => 1 / (2 ^ 2 : ℚ)) θ} 4 ∧
      ∃ F : Flow (torusNet 2) (fun _ _ => 1 / (2 ^ 2 : ℚ)) 4, F.Minimal torusDist := by
  have hD : 0 < hopDemand (fun _ _ : Fin 2 × Fin 2 => 1 / ((2 : ℕ) ^ 2 : ℚ)) torusDist := by
    rw [torus_hop_self]
    exact div_pos (mul_pos (by positivity) (ringTotal_pos le_rfl)) (by positivity)
  have := torus_opt_of le_rfl _ (fun _ _ => div_nonneg zero_le_one (sq_nonneg _))
    (fun _ _ _ => rfl) hD 4 (by
    rw [torus_hop_self, show (2 : ℕ) = 1 + 1 from rfl, ringTotal_even]
    norm_num)
  norm_num at this ⊢
  exact this

/-- **Uniform traffic including self is routable on the torus at `16 / k`** (`k ≥ 3`; optimal for
even `k`, below the optimum `16 k / (k² - 1)` for odd `k`).  For `k = 2` the optimum is `4 < 16 / 2`
(`torus_self_opt_two`). -/
theorem torus_self_routable (k : ℕ) (hk : 3 ≤ k) :
    Routable (torusNet k) (fun _ _ => 1 / (k ^ 2 : ℚ)) (16 / k) := by
  have h := (torus_self_opt k hk).1.1
  have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
  split_ifs at h with he
  · exact h
  · have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
    refine Routable.of_le h (div_pos (by linarith) hK)
      (div_nonneg (by norm_num) (Nat.cast_nonneg k)) ?_
    rw [div_le_div_iff₀ (by linarith) hK]
    nlinarith

end Torus

/-! ### The hypercube -/

section Cube

variable {n : ℕ}

/-- **Uniform traffic** on the hypercube: every vertex sends at rate `1` in total, spread evenly
over the `2ⁿ - 1` other vertices. -/
def cubeUniform (n : ℕ) (s d : Fin n → Bool) : ℚ := if s = d then 0 else 1 / ((2 : ℚ) ^ n - 1)

/-- The hop distance of the hypercube with natural values. -/
def cubeHops (u v : Fin n → Bool) : ℕ := (cubeDiff u v).card

/-- The hypercube distance is the cast of `cubeHops`. -/
theorem cubeDist_eq : (cubeDist : (Fin n → Bool) → (Fin n → Bool) → ℚ) =
    fun u v => (cubeHops u v : ℚ) := rfl

/-- The links of the hypercube are its neighbours. -/
theorem cube_cap_pos {u v : Fin n → Bool} : 0 < (cubeNet n).cap u v ↔ CubeAdj u v := by
  show 0 < ite _ _ _ ↔ _
  split_ifs with h <;> simp [h]

/-- Membership in `cubeDiff`. -/
theorem mem_cubeDiff {u v : Fin n → Bool} {i : Fin n} : i ∈ cubeDiff u v ↔ u i ≠ v i := by
  simp [cubeDiff]

/-- Flipping coordinate `i`. -/
def cubeFlip (u : Fin n → Bool) (i : Fin n) : Fin n → Bool := Function.update u i (!u i)

/-- The neighbour `cubeFlip u i` differs from `u` exactly in `i`, and every vertex differing
from `u` exactly in `i` is that neighbour. -/
theorem cubeDiff_eq_single (u v : Fin n → Bool) (i : Fin n) :
    cubeDiff u v = {i} ↔ v = cubeFlip u i := by
  constructor
  · intro h
    funext j
    have hj := congrArg (j ∈ ·) h
    simp only [mem_cubeDiff, mem_singleton, eq_iff_iff] at hj
    by_cases hji : j = i
    · subst hji; simp only [cubeFlip, Function.update_self]
      have := hj.2 rfl; revert this; cases u j <;> cases v j <;> simp
    · simp only [cubeFlip, Function.update_of_ne hji]
      by_contra hc; exact hji (hj.1 (Ne.symm hc))
  · rintro rfl
    ext j
    simp only [mem_cubeDiff, cubeFlip, mem_singleton]
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]

/-- Adjacency in the hypercube: `v` is `u` with one coordinate flipped. -/
theorem cubeAdj_iff (u v : Fin n → Bool) : CubeAdj u v ↔ ∃ i, v = cubeFlip u i := by
  unfold CubeAdj
  rw [card_eq_one]
  simp only [cubeDiff_eq_single]

/-- The translation `u ↦ u xor c` of the hypercube. -/
def cubeXor (c : Fin n → Bool) : Equiv.Perm (Fin n → Bool) where
  toFun u i := xor (u i) (c i)
  invFun u i := xor (u i) (c i)
  left_inv u := funext fun i => by simp
  right_inv u := funext fun i => by simp

/-- The permutation `u ↦ u ∘ π` of the coordinates. -/
def cubePerm (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → Bool) where
  toFun u := u ∘ π
  invFun u := u ∘ π.symm
  left_inv u := funext fun i => by simp
  right_inv u := funext fun i => by simp

/-- A permutation preserving the hop distance of the hypercube is an automorphism, for any
traffic invariant under all permutations. -/
theorem cube_isAut {dem : (Fin n → Bool) → (Fin n → Bool) → ℚ}
    (hdem : ∀ σ : Equiv.Perm (Fin n → Bool), ∀ s d, dem (σ s) (σ d) = dem s d)
    (σ : Equiv.Perm (Fin n → Bool)) (hD : ∀ u v, cubeHops (σ u) (σ v) = cubeHops u v) :
    IsAut (cubeNet n) dem cubeDist σ :=
  ⟨fun u v => by
      show ite _ _ _ = ite _ _ _
      have h' : CubeAdj (σ u) (σ v) ↔ CubeAdj u v := by
        have := hD u v
        unfold cubeHops at this
        unfold CubeAdj; rw [this]
      simp only [h'], hdem σ, fun u v => by simp only [cubeDist_eq, hD]⟩

/-- Translations are automorphisms of the hypercube. -/
theorem cubeXor_isAut {dem : (Fin n → Bool) → (Fin n → Bool) → ℚ}
    (hdem : ∀ σ : Equiv.Perm (Fin n → Bool), ∀ s d, dem (σ s) (σ d) = dem s d)
    (c : Fin n → Bool) : IsAut (cubeNet n) dem cubeDist (cubeXor c) :=
  cube_isAut hdem _ fun u v => by
    unfold cubeHops cubeDiff
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    show xor (u i) (c i) ≠ xor (v i) (c i) ↔ _
    cases u i <;> cases v i <;> cases c i <;> simp

/-- Permutations of the coordinates are automorphisms of the hypercube. -/
theorem cubePerm_isAut {dem : (Fin n → Bool) → (Fin n → Bool) → ℚ}
    (hdem : ∀ σ : Equiv.Perm (Fin n → Bool), ∀ s d, dem (σ s) (σ d) = dem s d)
    (π : Equiv.Perm (Fin n)) : IsAut (cubeNet n) dem cubeDist (cubePerm π) :=
  cube_isAut hdem _ fun u v => by
    unfold cubeHops cubeDiff
    rw [card_filter, card_filter]
    exact Equiv.sum_comp π (fun i => if u i ≠ v i then 1 else 0)

/-- **The hypercube is arc-transitive** (`n ≥ 1`): translations and permutations of the
coordinates map every link to the link `0 → e₀`. -/
theorem cube_arcTransitive (hn : 1 ≤ n) {dem : (Fin n → Bool) → (Fin n → Bool) → ℚ}
    (hdem : ∀ σ : Equiv.Perm (Fin n → Bool), ∀ s d, dem (σ s) (σ d) = dem s d) :
    ArcTransitive (cubeNet n) dem cubeDist := by
  set i₀ : Fin n := ⟨0, by omega⟩
  refine ArcTransitive.of_base (fun _ => false) (fun j => decide (j = i₀)) fun u v h => ?_
  obtain ⟨i, rfl⟩ := (cubeAdj_iff u v).1 (cube_cap_pos.1 h)
  refine ⟨(cubeXor u).trans (cubePerm (Equiv.swap i₀ i)),
    (cubeXor_isAut hdem u).trans (cubePerm_isAut hdem _), funext fun j => ?_,
    funext fun j => ?_⟩
  · show xor (u _) (u _) = false
    simp
  · show xor (cubeFlip u i _) (u _) = decide (j = i₀)
    by_cases hj : j = i₀
    · subst hj; simp [cubeFlip]
    · have h1 : Equiv.swap i₀ i j ≠ i := by
        rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]; exact hj
      simp [cubeFlip, Function.update_of_ne h1, hj]

/-- The hypercube hop distance vanishes only on the diagonal. -/
theorem cubeHops_eq_zero (u v : Fin n → Bool) : cubeHops u v = 0 ↔ u = v := by
  unfold cubeHops cubeDiff
  rw [card_eq_zero, filter_eq_empty_iff]
  simp only [mem_univ, true_implies, not_not]
  exact ⟨fun h => funext h, fun h _ => h ▸ rfl⟩

/-- Along a link of the hypercube the hop distance drops by at most one. -/
theorem cubeHops_le_of_cap {u v : Fin n → Bool} (h : 0 < (cubeNet n).cap u v)
    (d : Fin n → Bool) : cubeHops u d ≤ cubeHops v d + 1 := by
  obtain ⟨i, rfl⟩ := (cubeAdj_iff u v).1 (cube_cap_pos.1 h)
  unfold cubeHops
  refine (card_le_card fun j hj => ?_).trans (card_insert_le i _)
  rw [mem_insert]
  by_cases hji : j = i
  · exact Or.inl hji
  · right
    rw [mem_cubeDiff] at hj ⊢
    simpa only [cubeFlip, Function.update_of_ne hji] using hj

/-- Every vertex other than `d` has a neighbour one hop closer to `d`. -/
theorem cube_step {v d : Fin n → Bool} (h : v ≠ d) :
    ∃ w, 0 < (cubeNet n).cap v w ∧ cubeHops w d + 1 = cubeHops v d := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  refine ⟨cubeFlip v i, cube_cap_pos.2 ((cubeAdj_iff _ _).2 ⟨i, rfl⟩), ?_⟩
  have hmem : i ∈ cubeDiff v d := mem_cubeDiff.2 hi
  have e : cubeDiff (cubeFlip v i) d = (cubeDiff v d).erase i := by
    ext j
    simp only [mem_cubeDiff, cubeFlip, mem_erase]
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self, ne_eq, not_true_eq_false, false_and, iff_false]
      revert hi; cases v j <;> cases d j <;> simp
    · simp [hji]
  unfold cubeHops
  rw [e, card_erase_of_mem hmem]
  have := card_pos.2 ⟨i, hmem⟩
  omega

/-- **Minimal routing is optimal on the hypercube** (`n ≥ 1`), for every nonnegative traffic
invariant under all permutations: the optimum `∑ cap / ∑ dem * dist` is reached by a minimal
flow. -/
theorem cube_symmetric_opt (hn : 1 ≤ n) (dem : (Fin n → Bool) → (Fin n → Bool) → ℚ)
    (hnn : ∀ s d, 0 ≤ dem s d)
    (hdem : ∀ σ : Equiv.Perm (Fin n → Bool), ∀ s d, dem (σ s) (σ d) = dem s d)
    (hD : 0 < hopDemand dem cubeDist) :
    IsGreatest {θ : ℚ | Routable (cubeNet n) dem θ}
        ((∑ u, ∑ v, (cubeNet n).cap u v) / hopDemand dem cubeDist) ∧
      ∃ F : Flow (cubeNet n) dem ((∑ u, ∑ v, (cubeNet n).cap u v) / hopDemand dem cubeDist),
        F.Minimal cubeDist :=
  symmetric_opt (cubeNet n) dem hnn cubeHops cubeHops_eq_zero
    (fun _ _ d h => cubeHops_le_of_cap h d) (fun _ _ h => cube_step h)
    (cube_arcTransitive hn hdem) hD

/-- Flips of different coordinates are different. -/
theorem cubeFlip_inj (u : Fin n → Bool) (i j : Fin n) : cubeFlip u i = cubeFlip u j ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h1 := (cubeDiff_eq_single u (cubeFlip u j) i).2 h.symm
  have h2 := (cubeDiff_eq_single u (cubeFlip u j) j).2 rfl
  rw [h1] at h2
  exact singleton_inj.1 h2

/-- The hypercube has `2ⁿ` vertices. -/
theorem cube_card : (Fintype.card (Fin n → Bool) : ℚ) = 2 ^ n := by simp

/-- The total capacity of the hypercube: `2 n 2ⁿ` (`n 2ⁿ` directed links of capacity `2`). -/
theorem cube_sum_cap :
    ∑ u : Fin n → Bool, ∑ v : Fin n → Bool, (cubeNet n).cap u v = 2 * n * 2 ^ n := by
  have hu : ∀ u : Fin n → Bool, ∑ v, (cubeNet n).cap u v = 2 * n := by
    intro u
    have e : ∀ v, (cubeNet n).cap u v = 2 * ∑ i, if v = cubeFlip u i then (1 : ℚ) else 0 := by
      intro v
      show ite _ _ _ = _
      by_cases h : CubeAdj u v
      · obtain ⟨i, rfl⟩ := (cubeAdj_iff u _).1 h
        rw [ite_eq_left h]
        simp only [cubeFlip_inj, sum_ite_eq, mem_univ, ite_true]
        norm_num
      · rw [ite_eq_right h, sum_eq_zero fun i _ => ite_eq_right fun hv =>
          h ((cubeAdj_iff u v).2 ⟨i, hv⟩), mul_zero]
    simp only [e, ← mul_sum]
    rw [sum_comm]
    simp only [sum_ite_eq', mem_univ, ite_true, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  simp only [hu, sum_const, card_univ, nsmul_eq_mul, cube_card]
  ring

/-- The total hop distance of the hypercube over all ordered pairs: `n 2ⁿ 2ⁿ / 2`. -/
theorem cube_sum_dist :
    ∑ s : Fin n → Bool, ∑ d : Fin n → Bool, cubeDist s d = n * 2 ^ n * 2 ^ n / 2 := by
  have e : ∀ s d : Fin n → Bool, cubeDist s d = ∑ i, if s i ≠ d i then (1 : ℚ) else 0 := by
    intro s d
    simp only [cubeDist, cubeDiff, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
  have half : ∀ (i : Fin n) (s : Fin n → Bool),
      ∑ d : Fin n → Bool, (if s i ≠ d i then (1 : ℚ) else 0) = 2 ^ n / 2 := by
    intro i s
    have hX : ∑ d : Fin n → Bool, (if s i ≠ d i then (1 : ℚ) else 0) =
        ∑ d : Fin n → Bool, (if s i = d i then (1 : ℚ) else 0) := by
      rw [← Equiv.sum_comp (cubeXor fun j => decide (j = i))]
      refine sum_congr rfl fun d _ => ?_
      show (if s i ≠ xor (d i) (decide (i = i)) then (1 : ℚ) else 0) = _
      cases s i <;> cases d i <;> simp
    have hXY : ∑ d : Fin n → Bool, (if s i ≠ d i then (1 : ℚ) else 0) +
        ∑ d : Fin n → Bool, (if s i = d i then (1 : ℚ) else 0) = 2 ^ n := by
      rw [← sum_add_distrib, sum_congr rfl (g := fun _ => (1 : ℚ)) fun d _ => by
        by_cases h : s i = d i <;> simp [h]]
      rw [sum_const, card_univ, nsmul_eq_mul, mul_one, cube_card]
    linarith
  have hs : ∀ s : Fin n → Bool, ∑ d : Fin n → Bool, ∑ i, (if s i ≠ d i then (1 : ℚ) else 0) =
      n * (2 ^ n / 2) := by
    intro s
    rw [sum_comm]
    simp only [half, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [e, hs, sum_const, card_univ, nsmul_eq_mul, cube_card]
  ring

/-- The optimum of a permutation-invariant traffic matrix on the hypercube, given its value `θ`:
`θ * ∑ dem * dist = ∑ cap`. -/
theorem cube_opt_of (hn : 1 ≤ n) (dem : (Fin n → Bool) → (Fin n → Bool) → ℚ)
    (hnn : ∀ s d, 0 ≤ dem s d)
    (hdem : ∀ σ : Equiv.Perm (Fin n → Bool), ∀ s d, dem (σ s) (σ d) = dem s d)
    (hD : 0 < hopDemand dem cubeDist) (θ : ℚ)
    (hθ : θ * hopDemand dem cubeDist = 2 * n * 2 ^ n) :
    IsGreatest {θ : ℚ | Routable (cubeNet n) dem θ} θ ∧
      ∃ F : Flow (cubeNet n) dem θ, F.Minimal cubeDist := by
  have e : (∑ u, ∑ v, (cubeNet n).cap u v) / hopDemand dem cubeDist = θ := by
    rw [cube_sum_cap, ← hθ, mul_div_cancel_right₀ _ hD.ne']
  rw [← e]
  exact cube_symmetric_opt hn dem hnn hdem hD

/-- Uniform traffic on the hypercube: `∑ dem * dist = n 2ⁿ 2ⁿ / (2 (2ⁿ - 1))`. -/
theorem cube_hop_uniform :
    hopDemand (cubeUniform n) cubeDist = n * 2 ^ n * 2 ^ n / (2 * ((2 : ℚ) ^ n - 1)) := by
  rw [show cubeUniform n = fun s d => if s = d then 0 else 1 / ((2 : ℚ) ^ n - 1) from rfl,
    hopDemand_offdiag _ _ (fun d => by
      rw [cubeDist_eq]; simp only [Nat.cast_eq_zero]; exact (cubeHops_eq_zero d d).2 rfl),
    cube_sum_dist, one_div_mul_eq_div, div_div, mul_comm (2 : ℚ)]

/-- Uniform traffic including self on the hypercube: `∑ dem * dist = n 2ⁿ 2ⁿ / (2 · 2ⁿ)`. -/
theorem cube_hop_self :
    hopDemand (fun _ _ : Fin n → Bool => 1 / (2 ^ n : ℚ)) cubeDist =
      n * 2 ^ n * 2 ^ n / (2 * (2 : ℚ) ^ n) := by
  rw [hopDemand_const, cube_sum_dist, one_div_mul_eq_div, div_div, mul_comm (2 : ℚ)]

/-- **Uniform traffic on the hypercube** (`n ≥ 1`): the optimal throughput, over all routings,
is `4 (2ⁿ - 1) / 2ⁿ`, reached by a minimal flow (no detours) loading every link to exactly its
capacity. -/
theorem cube_uniform_opt (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest {θ : ℚ | Routable (cubeNet n) (cubeUniform n) θ} (4 * (2 ^ n - 1) / 2 ^ n) ∧
      ∃ F : Flow (cubeNet n) (cubeUniform n) (4 * (2 ^ n - 1) / 2 ^ n), F.Minimal cubeDist := by
  have hP : (2 : ℚ) ≤ 2 ^ n := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hP1 : (0 : ℚ) < 2 ^ n - 1 := by linarith
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hD : 0 < hopDemand (cubeUniform n) cubeDist := by
    rw [cube_hop_uniform]
    exact div_pos (by positivity) (by positivity)
  refine cube_opt_of hn _ (fun s d => by
      unfold cubeUniform; split_ifs
      · exact le_rfl
      · exact div_nonneg zero_le_one hP1.le)
    (fun σ s d => by unfold cubeUniform; simp only [σ.injective.eq_iff]) hD _ ?_
  rw [cube_hop_uniform, div_mul_div_comm, div_eq_iff (by positivity)]
  ring

/-- **The `6`-cube under uniform traffic**: the optimum is `63/16`. -/
theorem cube_uniform_opt_six :
    IsGreatest {θ : ℚ | Routable (cubeNet 6) (cubeUniform 6) θ} (63 / 16) ∧
      ∃ F : Flow (cubeNet 6) (cubeUniform 6) (63 / 16), F.Minimal cubeDist := by
  have := cube_uniform_opt 6 (by norm_num)
  rw [show (4 * (2 ^ 6 - 1) / 2 ^ 6 : ℚ) = 63 / 16 by norm_num] at this
  exact this

/-- **Uniform traffic including self on the hypercube** (demand `1 / 2ⁿ` for every pair,
`n ≥ 1`): the optimal throughput is `4`, reached by a minimal flow. -/
theorem cube_self_opt (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest {θ : ℚ | Routable (cubeNet n) (fun _ _ => 1 / (2 ^ n : ℚ)) θ} 4 ∧
      ∃ F : Flow (cubeNet n) (fun _ _ => 1 / (2 ^ n : ℚ)) 4, F.Minimal cubeDist := by
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hD : 0 < hopDemand (fun _ _ : Fin n → Bool => 1 / (2 ^ n : ℚ)) cubeDist := by
    rw [cube_hop_self]
    exact div_pos (by positivity) (by positivity)
  refine cube_opt_of hn _ (fun _ _ => div_nonneg zero_le_one (pow_nonneg zero_le_two n))
    (fun _ _ _ => rfl) hD 4 ?_
  rw [cube_hop_self, ← mul_div_assoc, div_eq_iff (by positivity)]
  ring

/-- **Uniform traffic including self is routable on the hypercube at `4`** (`n ≥ 1`). -/
theorem cube_self_routable (n : ℕ) (hn : 1 ≤ n) :
    Routable (cubeNet n) (fun _ _ => 1 / (2 ^ n : ℚ)) 4 :=
  (cube_self_opt n hn).1.1

end Cube

/-! ### Worst-case traffic: Valiant's routing is optimal -/

/-- **Valiant is worst-case optimal on the torus** (even `k ≥ 4`): the best worst-case throughput
over admissible traffic is `8 / k`, unconditionally (`torus_worst_opt` with
`torus_self_routable`). -/
theorem torus_worst_opt' (k : ℕ) (hk : 4 ≤ k) (he : Even k) :
    IsGreatest {θ : ℚ | ∀ T, AdmissibleGen T → Routable (torusNet k) T θ} (8 / k) :=
  torus_worst_opt k (by omega) he (torus_self_routable k (by omega))

/-- **Valiant is worst-case optimal on the hypercube** (`n ≥ 1`): the best worst-case throughput
over admissible traffic is `2`, unconditionally (`cube_worst_opt` with `cube_self_routable`). -/
theorem cube_worst_opt' (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest {θ : ℚ | ∀ T, AdmissibleGen T → Routable (cubeNet n) T θ} 2 :=
  cube_worst_opt n hn (cube_self_routable n hn)

end Fluid

end AsyncLean
