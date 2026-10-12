/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Symmetric.General

/-!
# Symmetric networks: minimal routing is optimal for uniform traffic, part 2: the torus

Part 2 of 3 of `AsyncLean.Flow.Symmetric`; that module has the overview.
-/

namespace AsyncLean

namespace Fluid

open Finset

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

/-- The optimum of uniform traffic on the torus (`k ≥ 3`) times its hop demand is the total
capacity: the hop bound is tight. -/
theorem torus_uniform_hop (k : ℕ) (hk : 3 ≤ k) :
    (if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / (k : ℚ)) *
        hopDemand (uniform k) torusDist = 4 * (k : ℚ) ^ 2 * (if k = 2 then 1 else 2) := by
  have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  rw [torus_hop_uniform, ite_eq_right (show k ≠ 2 by omega)]
  split_ifs with he
  · obtain ⟨m, rfl⟩ := he
    rw [ringTotal_even, div_mul_div_comm, div_eq_iff (mul_ne_zero (by positivity) hK.ne')]
    push_cast; ring
  · obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.1 he
    rw [show 2 * m + 1 = m + m + 1 by ring, ringTotal_odd] at *
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero (by positivity) hK.ne')]
    push_cast; ring

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
  exact torus_opt_of (by omega) _ (fun s d => by
      unfold uniform; split_ifs
      · exact le_rfl
      · exact div_nonneg zero_le_one hK.le) uniform_perm hD _ (torus_uniform_hop k hk)

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

end Fluid

end AsyncLean
