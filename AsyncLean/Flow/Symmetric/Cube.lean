/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Symmetric.Torus

/-!
# Symmetric networks: minimal routing is optimal for uniform traffic, part 3: the hypercube and worst-case traffic

Part 3 of 3 of `AsyncLean.Flow.Symmetric`; that module has the overview.
-/

namespace AsyncLean

namespace Fluid

open Finset

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

/-- The optimum of uniform traffic on the `n`-cube times its hop demand is the total
capacity: the hop bound is tight. -/
theorem cube_uniform_hop (n : ℕ) (hn : 1 ≤ n) :
    4 * (2 ^ n - 1) / 2 ^ n * hopDemand (cubeUniform n) cubeDist = 2 * n * 2 ^ n := by
  have hP : (2 : ℚ) ≤ 2 ^ n := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hP1 : (0 : ℚ) < 2 ^ n - 1 := by linarith
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  rw [cube_hop_uniform, div_mul_div_comm, div_eq_iff (by positivity)]
  ring

/-- **Uniform traffic on the hypercube** (`n ≥ 1`): the optimal throughput, over all routings,
is `4 (2ⁿ - 1) / 2ⁿ`, reached by a minimal flow (minimal) loading every link to exactly its
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
    (fun σ s d => by unfold cubeUniform; simp only [σ.injective.eq_iff]) hD _
    (cube_uniform_hop n hn)

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
