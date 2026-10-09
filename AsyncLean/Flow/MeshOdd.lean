/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.MeshWire

/-!
# The mesh's exact throughput for odd `k`, and minimal routing

`AsyncLean.Flow.MeshWire` finds the exact fluid throughput of the `k × k` mesh under uniform
traffic for even `k`: `8 (k² - 1) / k³`.  For odd `k = 2m + 1` the answer is `8 / k`: the middle
links of a line carry `m (m + 1) = (k² - 1) / 4` rather than `k² / 4`, so XY routing does better,
and the cut between columns `m - 1` and `m` matches it.

* `lineFlow_load_odd` : for odd `k`, the total load of a line link is at most `(k² - 1) / 4`.
* `xyRoutingOdd`, `mesh_routable_odd` : for odd `k ≥ 3`, XY routing at rate
  `8 / (k (k² - 1))` per pair routes uniform traffic at throughput `8 / k`.
* `mesh_cut` : the cut bound for the first `c` columns (`1 ≤ c < k`):
  `θ * (k c) (k (k - c)) ≤ 2 k (k² - 1)`.
* `mesh_upper_odd`, `mesh_opt_odd` : for odd `k ≥ 3`, **the mesh's exact fluid throughput** is
  `8 / k` (`IsGreatest`); `mesh_opt_all` : for every `k ≥ 2` it is
  `if Even k then 8 (k² - 1) / k³ else 8 / k`.
* `xyFlow_minimal`, `xyRouting_minimal`, `xyRoutingOdd_minimal` : XY routing is **minimal**
  (`Flow.Minimal`): every link a commodity uses brings it one step closer, in Manhattan distance,
  to its destination.
* `uniform_minimal_opt` : **detours add nothing on uniform traffic.**  For every `k ≥ 2` the
  mesh's optimum is reached by a minimal flow.
-/

namespace AsyncLean

namespace Fluid

open Finset

/-- The exact total load of a line link over all destinations: `(a + 1) (k - b)` on a link
`a → a + 1 = b`, `(k - 1 - b) (b + 1)` on a link `a = b + 1 → b`, `0` otherwise. -/
theorem lineFlowN_load_eq (k a b : ℕ) (hb : b < k) :
    ∑ t ∈ range k, lineFlowN k t a b =
      (if a + 1 = b then ((a : ℚ) + 1) * (k - b) else 0) +
        (if b + 1 = a then ((k : ℚ) - 1 - b) * (b + 1) else 0) := by
  unfold lineFlowN
  rw [sum_add_distrib]
  congr 1
  · by_cases h : a + 1 = b
    · have : ∀ t, (if a + 1 = b ∧ b ≤ t then ((a : ℚ) + 1) else 0) =
          ((a : ℚ) + 1) * (if b ≤ t then 1 else 0) := fun t => by
        by_cases h' : b ≤ t <;> simp [h, h']
      rw [sum_congr rfl (fun t _ => this t), ← mul_sum, sum_range_ge k b hb.le, ite_eq_left h]
    · rw [sum_eq_zero (fun t _ => by simp [h]), ite_eq_right h]
  · by_cases h : b + 1 = a
    · have : ∀ t, (if b + 1 = a ∧ t ≤ b then ((k : ℚ) - 1 - b) else 0) =
          ((k : ℚ) - 1 - b) * (if t < b + 1 then 1 else 0) := fun t => by
        by_cases h' : t ≤ b
        · rw [ite_eq_left ⟨h, h'⟩, ite_eq_left (show t < b + 1 by omega), mul_one]
        · rw [ite_eq_right (fun hc => h' hc.2), ite_eq_right (show ¬ t < b + 1 by omega), mul_zero]
      rw [sum_congr rfl (fun t _ => this t), ← mul_sum, sum_range_lt k (b + 1) (by omega),
        ite_eq_left h]
      push_cast; ring
    · rw [sum_eq_zero (fun t _ => by simp [h]), ite_eq_right h]

/-- Two naturals summing to the odd number `2m + 1` have product at most `m (m + 1)`. -/
theorem odd_prod_le (m x : ℕ) : (x : ℚ) * (2 * m + 1 - x) ≤ m * (m + 1) := by
  rcases Nat.lt_or_ge m x with h | h
  · have h1 : (m : ℚ) + 1 ≤ x := by exact_mod_cast h
    nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ x - m) (by linarith : (0 : ℚ) ≤ x - m - 1)]
  · have h1 : (x : ℚ) ≤ m := by exact_mod_cast h
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (by linarith : (0 : ℚ) ≤ m + 1 - x)]

/-- For odd `k`, the load of a line link summed over all destinations is at most `(k² - 1) / 4`,
and `0` on a non-link. -/
theorem lineFlowN_load_odd (k a b : ℕ) (hb : b < k) (ho : Odd k) :
    ∑ t ∈ range k, lineFlowN k t a b ≤
      if a + 1 = b ∨ b + 1 = a then ((k : ℚ) ^ 2 - 1) / 4 else 0 := by
  obtain ⟨m, hm⟩ := ho
  have hk : (k : ℚ) = 2 * m + 1 := by exact_mod_cast hm
  rw [lineFlowN_load_eq k a b hb]
  by_cases h1 : a + 1 = b
  · have h2 : ¬ b + 1 = a := by omega
    have hab : (b : ℚ) = a + 1 := by exact_mod_cast h1.symm
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left (Or.inl h1), hab, hk]
    have := odd_prod_le m (a + 1)
    push_cast at this
    nlinarith
  · by_cases h2 : b + 1 = a
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (Or.inr h2), hk]
      have := odd_prod_le m (b + 1)
      push_cast at this
      nlinarith
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega)]; simp

/-- For odd `k`, the total load of a line link over all destinations is at most `(k² - 1) / 4`
on neighbours and `0` otherwise. -/
theorem lineFlow_load_odd {k : ℕ} (ho : Odd k) (a b : Fin k) :
    ∑ t, lineFlow t a b ≤ if LineAdj a b then ((k : ℚ) ^ 2 - 1) / 4 else 0 := by
  have h1 : ∑ t, lineFlow t a b = ∑ t ∈ range k, lineFlowN k t a b :=
    Fin.sum_univ_eq_sum_range (fun t => lineFlowN k t a b) k
  rw [h1]
  exact lineFlowN_load_odd k a b b.2 ho

/-- XY routing at rate `r ≥ 0` fits in the mesh whenever every line link carries at most `L`
in total and `r * (k * L) ≤ 2`. -/
theorem xyFlow_capacity_of (k : ℕ) {r L : ℚ} (hr : 0 ≤ r)
    (hL : ∀ a b : Fin k, ∑ t, lineFlow t a b ≤ if LineAdj a b then L else 0)
    (hrL : r * (k * L) ≤ 2) (u v : Fin k × Fin k) :
    ∑ d, xyFlow k r d u v ≤ (meshNet k).cap u v := by
  rw [xyFlow_load]
  have hk' : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have l1 := hL u.1 v.1
  have l2 := hL u.2 v.2
  have n1 : 0 ≤ ∑ t, lineFlow t u.1 v.1 := sum_nonneg fun t _ => lineFlow_nonneg _ _ _
  have n2 : 0 ≤ ∑ t, lineFlow t u.2 v.2 := sum_nonneg fun t _ => lineFlow_nonneg _ _ _
  show _ ≤ ite _ _ _
  by_cases ha : MeshAdj u v
  · rw [ite_eq_left ha]
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ite_eq_left h1, ite_eq_right h2.ne, add_zero]
      rw [ite_eq_left h2] at l1
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left l1 hk') hr).trans hrL
    · rw [ite_eq_left h1, ite_eq_right h2.ne, zero_add]
      rw [ite_eq_left h2] at l2
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left l2 hk') hr).trans hrL
  · rw [ite_eq_right ha]
    have z1 : (if u.2 = v.2 then (k : ℚ) * ∑ t, lineFlow t u.1 v.1 else 0) = 0 := by
      by_cases h1 : u.2 = v.2
      · rw [ite_eq_right (fun h2 => ha (Or.inl ⟨h1, h2⟩))] at l1
        rw [ite_eq_left h1, le_antisymm l1 n1, mul_zero]
      · exact ite_eq_right h1
    have z2 : (if u.1 = v.1 then (k : ℚ) * ∑ t, lineFlow t u.2 v.2 else 0) = 0 := by
      by_cases h1 : u.1 = v.1
      · rw [ite_eq_right (fun h2 => ha (Or.inr ⟨h1, h2⟩))] at l2
        rw [ite_eq_left h1, le_antisymm l2 n2, mul_zero]
      · exact ite_eq_right h1
    rw [z1, z2]; simp

/-- **XY routing for odd `k`** as a fluid flow: at rate `8 / (k (k² - 1))` per pair it routes
uniform traffic at throughput `8 / k` in the mesh; the middle links of the rows and columns carry
exactly their capacity `2`. -/
def xyRoutingOdd (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) :
    Flow (meshNet k) (uniform k) (8 / (k : ℚ)) where
  f := xyFlow k (8 / ((k : ℚ) * ((k : ℚ) ^ 2 - 1)))
  nonneg := by
    have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
    exact xyFlow_nonneg k (div_nonneg (by norm_num) (mul_nonneg (by linarith) (by nlinarith)))
  conserve d v hv := by
    rw [xyFlow_conserve, ite_eq_right hv]
    unfold uniform
    rw [ite_eq_right hv, sub_zero, mul_one, div_mul_div_comm, mul_one]
  capacity u v := by
    have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
    have hc : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
    refine xyFlow_capacity_of k (div_nonneg (by norm_num) (by positivity))
      (lineFlow_load_odd ho) (le_of_eq ?_) u v
    rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]; ring

/-- **Lower bound** (odd `k ≥ 3`): uniform traffic is routable in the `k × k` mesh at throughput
`8 / k`. -/
theorem mesh_routable_odd (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) :
    Routable (meshNet k) (uniform k) (8 / (k : ℚ)) := ⟨xyRoutingOdd k hk ho⟩

/-- **The cut bound for the first `c` columns** (`1 ≤ c < k`, any routing): the `k c` vertices left
of the cut send `θ * (k c) (k (k - c)) / (k² - 1)` across it, through `k` links of capacity `2`, so
`θ * ((k c) (k (k - c))) ≤ 2 k (k² - 1)`. -/
theorem mesh_cut (k c : ℕ) (hc : 1 ≤ c) (hck : c < k) {θ : ℚ}
    (h : Routable (meshNet k) (uniform k) θ) :
    θ * (((k : ℚ) * c) * (k * ((k : ℚ) - c))) ≤ 2 * k * ((k : ℚ) ^ 2 - 1) := by
  have key := cut_bound h (fun u : Fin k × Fin k => (u.1 : ℕ) < c)
  -- the traffic across the cut
  have hA : ∑ s : Fin k × Fin k, (if (s.1 : ℕ) < c then (1 : ℚ) else 0) = k * c := by
    rw [sum_fst (fun i : Fin k => if (i : ℕ) < c then (1 : ℚ) else 0),
      Fin.sum_univ_eq_sum_range (fun i => if i < c then (1 : ℚ) else 0) k,
      sum_range_lt k c hck.le]
  have hB : ∑ d : Fin k × Fin k, (if ¬ (d.1 : ℕ) < c then (1 : ℚ) else 0) = k * (k - c) := by
    rw [sum_fst (fun i : Fin k => if ¬ (i : ℕ) < c then (1 : ℚ) else 0),
      Fin.sum_univ_eq_sum_range (fun i => if ¬ i < c then (1 : ℚ) else 0) k,
      sum_congr rfl (g := fun i => if c ≤ i then (1 : ℚ) else 0)
        (fun i _ => by simp only [not_lt]),
      sum_range_ge k c hck.le]
  have hL : ∑ s : Fin k × Fin k, ∑ d : Fin k × Fin k,
      (if (s.1 : ℕ) < c ∧ ¬ (d.1 : ℕ) < c then uniform k s d else 0) =
        1 / ((k : ℚ) ^ 2 - 1) * ((k * c) * (k * (k - c))) := by
    have e : ∀ s d : Fin k × Fin k,
        (if (s.1 : ℕ) < c ∧ ¬ (d.1 : ℕ) < c then uniform k s d else 0) =
          1 / ((k : ℚ) ^ 2 - 1) * ((if (s.1 : ℕ) < c then (1 : ℚ) else 0) *
            (if ¬ (d.1 : ℕ) < c then (1 : ℚ) else 0)) := by
      intro s d
      by_cases hs : (s.1 : ℕ) < c
      · by_cases hd : (d.1 : ℕ) < c
        · simp [hs, hd]
        · have hsd : s ≠ d := by rintro rfl; exact hd hs
          simp [hs, hd, uniform, hsd]
      · simp [hs]
    simp only [e, ← mul_sum]
    rw [← sum_mul, hA, hB]
  -- the capacity of the cut
  have hR : ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
      (if (u.1 : ℕ) < c ∧ ¬ (v.1 : ℕ) < c then (meshNet k).cap u v else 0) ≤ 2 * k := by
    have p : ∀ u v : Fin k × Fin k,
        (if (u.1 : ℕ) < c ∧ ¬ (v.1 : ℕ) < c then (meshNet k).cap u v else 0) ≤
          if v = (⟨c, hck⟩, u.2) then (if (u.1 : ℕ) + 1 = c then (2 : ℚ) else 0) else 0 := by
      intro u v
      show (if _ then ite _ _ _ else _) ≤ _
      by_cases hcut : ((u.1 : ℕ) < c ∧ ¬ (v.1 : ℕ) < c) ∧ MeshAdj u v
      · obtain ⟨⟨hu, hv⟩, hadj⟩ := hcut
        rw [ite_eq_left ⟨hu, hv⟩, ite_eq_left hadj]
        rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, _⟩
        · have hv' : v = (⟨c, hck⟩, u.2) := Prod.ext (Fin.ext (by simp; omega)) h1.symm
          rw [ite_eq_left hv', ite_eq_left (by omega)]
        · omega
        · rw [h1] at hu; exact absurd hu hv
      · have : (if (u.1 : ℕ) < c ∧ ¬ (v.1 : ℕ) < c then
            (if MeshAdj u v then (2 : ℚ) else 0) else 0) = 0 := by
          by_cases h1 : (u.1 : ℕ) < c ∧ ¬ (v.1 : ℕ) < c
          · rw [ite_eq_left h1, ite_eq_right (fun h2 => hcut ⟨h1, h2⟩)]
          · exact ite_eq_right h1
        rw [this]
        split_ifs <;> norm_num
    calc _ ≤ ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
          (if v = (⟨c, hck⟩, u.2) then (if (u.1 : ℕ) + 1 = c then (2 : ℚ) else 0) else 0) :=
          sum_le_sum fun u _ => sum_le_sum fun v _ => p u v
      _ = ∑ u : Fin k × Fin k, (if (u.1 : ℕ) + 1 = c then (2 : ℚ) else 0) := by
          simp only [sum_ite_eq', mem_univ, ite_true]
      _ = 2 * k := by
          rw [sum_fst (fun i : Fin k => if (i : ℕ) + 1 = c then (2 : ℚ) else 0),
            Fin.sum_univ_eq_sum_range (fun i => if i + 1 = c then (2 : ℚ) else 0) k,
            sum_range_single k (c - 1) (fun _ => (2 : ℚ)) (fun i => i + 1 = c)
              (fun i hi => by omega), ite_eq_left ⟨by omega, by omega⟩]
          ring
  rw [hL] at key
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hpos : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have := mul_le_mul_of_nonneg_right (key.trans hR) hpos.le
  rwa [show θ * (1 / ((k : ℚ) ^ 2 - 1) * ((k * c) * (k * (k - c)))) * ((k : ℚ) ^ 2 - 1) =
    θ * ((k * c) * (k * (k - c))) * (1 / ((k : ℚ) ^ 2 - 1) * ((k : ℚ) ^ 2 - 1)) by ring,
    one_div_mul_cancel hpos.ne', mul_one] at this

/-- **Upper bound** (odd `k = 2m + 1 ≥ 3`, any routing): by the cut bound for the first `m`
columns (`(m k) ((m + 1) k) / (k² - 1) * θ = k² θ / 4 ≤ 2k`), uniform traffic is routable in the
`k × k` mesh only at `θ ≤ 8 / k`. -/
theorem mesh_upper_odd (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) {θ : ℚ}
    (h : Routable (meshNet k) (uniform k) θ) : θ ≤ 8 / (k : ℚ) := by
  obtain ⟨m, hm⟩ := ho
  have key := mesh_cut k m (by omega) (by omega) h
  have hkm : (k : ℚ) = 2 * m + 1 := by exact_mod_cast hm
  have hm' : (1 : ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  rw [hkm] at key ⊢
  rw [le_div_iff₀ (by positivity)]
  have hp : (0 : ℚ) < (2 * m + 1) * m * (m + 1) := by positivity
  have e1 : θ * (((2 * (m : ℚ) + 1) * m) * ((2 * m + 1) * (2 * m + 1 - m))) =
      θ * (2 * m + 1) * ((2 * m + 1) * m * (m + 1)) := by ring
  have e2 : 2 * (2 * (m : ℚ) + 1) * ((2 * m + 1) ^ 2 - 1) = 8 * ((2 * m + 1) * m * (m + 1)) := by
    ring
  rw [e1, e2] at key
  exact le_of_mul_le_mul_right key hp

/-- **The mesh's exact fluid throughput** (odd `k ≥ 3`): the largest throughput at which uniform
traffic is routable in the `k × k` mesh is `8 / k`. -/
theorem mesh_opt_odd (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) :
    IsGreatest {θ : ℚ | Routable (meshNet k) (uniform k) θ} (8 / (k : ℚ)) :=
  ⟨mesh_routable_odd k hk ho, fun _ h => mesh_upper_odd k hk ho h⟩

/-- An odd `k ≥ 2` is at least `3`. -/
theorem three_le_of_odd {k : ℕ} (hk : 2 ≤ k) (ho : Odd k) : 3 ≤ k := by
  obtain ⟨m, hm⟩ := ho; omega

/-- **The mesh's exact fluid throughput, every `k ≥ 2`**: `8 (k² - 1) / k³` for even `k`, `8 / k`
for odd `k`. -/
theorem mesh_opt_all (k : ℕ) (hk : 2 ≤ k) :
    IsGreatest {θ : ℚ | Routable (meshNet k) (uniform k) θ}
      (if Even k then 8 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 8 / (k : ℚ)) := by
  by_cases he : Even k
  · rw [ite_eq_left he]; exact mesh_opt k hk he
  · rw [ite_eq_right he]
    have ho : Odd k := Nat.not_even_iff_odd.1 he
    exact mesh_opt_odd k (three_le_of_odd hk ho) ho

/-- A link carrying line flow towards `t` is a step towards `t`. -/
theorem lineFlowN_pos {k t a b : ℕ} (h : 0 < lineFlowN k t a b) :
    (a + 1 = b ∧ b ≤ t) ∨ (b + 1 = a ∧ t ≤ b) := by
  unfold lineFlowN at h
  by_contra hn
  rw [not_or] at hn
  rw [ite_eq_right hn.1, ite_eq_right hn.2] at h
  norm_num at h

/-- A link carrying line flow towards `t` brings the traffic one step closer to `t`. -/
theorem lineFlow_closer {k : ℕ} {t a b : Fin k} (h : 0 < lineFlow t a b) :
    |((b : ℕ) : ℚ) - (t : ℕ)| < |((a : ℕ) : ℚ) - (t : ℕ)| := by
  rcases lineFlowN_pos (k := k) (t := t) (a := a) (b := b) h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e : ((b : ℕ) : ℚ) = (a : ℕ) + 1 := by exact_mod_cast h1.symm
    have l : ((b : ℕ) : ℚ) ≤ (t : ℕ) := by exact_mod_cast h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have e : ((a : ℕ) : ℚ) = (b : ℕ) + 1 := by exact_mod_cast h1.symm
    have l : ((t : ℕ) : ℚ) ≤ (b : ℕ) := by exact_mod_cast h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

/-- **XY routing is minimal**, at any rate `r`: a link `u → v` carrying commodity `d` brings it
strictly closer to `d` in Manhattan distance (along the row to the column of `d`, then along that
column). -/
theorem xyFlow_minimal (k : ℕ) (r : ℚ) (d u v : Fin k × Fin k) (h : 0 < xyFlow k r d u v) :
    manhattan (gridPos v) (gridPos d) < manhattan (gridPos u) (gridPos d) := by
  unfold xyFlow at h
  have nA : 0 ≤ (if u.2 = v.2 then lineFlow d.1 u.1 v.1 else 0) := by
    split_ifs
    · exact lineFlow_nonneg _ _ _
    · exact le_rfl
  have nB : 0 ≤ (if u.1 = d.1 ∧ v.1 = d.1 then (k : ℚ) * lineFlow d.2 u.2 v.2 else 0) := by
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg k) (lineFlow_nonneg _ _ _)
    · exact le_rfl
  have hAB : 0 < (if u.2 = v.2 then lineFlow d.1 u.1 v.1 else 0) +
      (if u.1 = d.1 ∧ v.1 = d.1 then (k : ℚ) * lineFlow d.2 u.2 v.2 else 0) := by
    by_contra hc
    rw [le_antisymm (not_lt.1 hc) (add_nonneg nA nB), mul_zero] at h
    exact lt_irrefl _ h
  unfold manhattan gridPos
  simp only [Int.cast_natCast]
  by_cases hA : 0 < (if u.2 = v.2 then lineFlow d.1 u.1 v.1 else 0)
  · by_cases h2 : u.2 = v.2
    · rw [ite_eq_left h2] at hA
      have := lineFlow_closer hA
      rw [h2]; linarith
    · rw [ite_eq_right h2] at hA; exact absurd hA (lt_irrefl 0)
  · have hB : 0 < (if u.1 = d.1 ∧ v.1 = d.1 then (k : ℚ) * lineFlow d.2 u.2 v.2 else 0) := by
      linarith
    by_cases h1 : u.1 = d.1 ∧ v.1 = d.1
    · rw [ite_eq_left h1] at hB
      have hl : 0 < lineFlow d.2 u.2 v.2 := by
        by_contra hc
        rw [le_antisymm (not_lt.1 hc) (lineFlow_nonneg _ _ _), mul_zero] at hB
        exact lt_irrefl _ hB
      have := lineFlow_closer hl
      rw [h1.1, h1.2]; linarith
    · rw [ite_eq_right h1] at hB; exact absurd hB (lt_irrefl 0)

/-- **XY routing is minimal** (every `k ≥ 2`): the optimal flow of `mesh_routable` takes no
detour. -/
theorem xyRouting_minimal (k : ℕ) (hk : 2 ≤ k) :
    (xyRouting k hk).Minimal (fun u v => manhattan (gridPos u) (gridPos v)) :=
  fun d u v h => xyFlow_minimal k _ d u v h

/-- **XY routing is minimal** (odd `k ≥ 3`): the optimal flow of `mesh_routable_odd` takes no
detour. -/
theorem xyRoutingOdd_minimal (k : ℕ) (hk : 3 ≤ k) (ho : Odd k) :
    (xyRoutingOdd k hk ho).Minimal (fun u v => manhattan (gridPos u) (gridPos v)) :=
  fun d u v h => xyFlow_minimal k _ d u v h

/-- **Detours add nothing on uniform traffic** (every `k ≥ 2`): the mesh's optimal throughput
(`8 (k² - 1) / k³` for even `k`, `8 / k` for odd `k`) is reached by a minimal flow, one in which
every link a commodity uses brings it strictly closer to its destination. -/
theorem uniform_minimal_opt (k : ℕ) (hk : 2 ≤ k) :
    IsGreatest {θ : ℚ | Routable (meshNet k) (uniform k) θ}
        (if Even k then 8 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 8 / (k : ℚ)) ∧
      ∃ F : Flow (meshNet k) (uniform k)
          (if Even k then 8 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 8 / (k : ℚ)),
        F.Minimal (fun u v => manhattan (gridPos u) (gridPos v)) := by
  refine ⟨mesh_opt_all k hk, ?_⟩
  by_cases he : Even k
  · rw [ite_eq_left he]; exact ⟨xyRouting k hk, xyRouting_minimal k hk⟩
  · rw [ite_eq_right he]
    have ho : Odd k := Nat.not_even_iff_odd.1 he
    have h3 := three_le_of_odd hk ho
    exact ⟨xyRoutingOdd k h3 ho, xyRoutingOdd_minimal k h3 ho⟩

end Fluid

end AsyncLean
