/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Fluid
import Mathlib.Algebra.BigOperators.Fin

/-!
# No topology beats the mesh per unit of wire by more than `3k / (2(k + 1))`

The `k × k` grid of vertices `Fin k × Fin k`, vertex `(x, y)` placed at the integer point
`(x, y)` (`gridPos`), under **uniform traffic** (`uniform k`: every vertex sends at rate `θ` in
total, spread evenly over the `k² - 1` others).  Links have capacity at most `2` (two lanes of
capacity `1`, as in the simulator) and a wire length at least the Manhattan distance of their
ends; the **wire** of a network is the total length of its directed links of positive capacity,
halved (`wire`).

* `sum_manhattan` : `∑ s d, dist s d = 2 k² (k³ - k) / 3`, so the average uniform-traffic
  distance gives `∑ s d, uniform k s d * dist s d = 2 k³ / 3` (`uniform_dist`).
* `uniform_wire_bound`, `throughput_le_wire` : **every topology**:
  `θ * (2 k³ / 3) ≤ ∑ cap * len ≤ 4 * wire`, hence `θ ≤ 6 * wire / k³`.
* `meshNet` : the mesh, capacity `2` both ways between grid neighbours; `mesh_wire` : its wire is
  `2 k (k - 1)` with unit lengths (`mesh_len`, `mesh_cap_le`: it satisfies the hypotheses).
* `mesh_upper` : for even `k ≥ 2`, any routing of uniform traffic in the mesh has
  `θ ≤ 8 (k² - 1) / k³` (cut bound across the middle: `(k²/2)² / (k² - 1) * θ ≤ 2k`).
* `mesh_routable` : for **every** `k ≥ 2`, XY routing (`xyFlow`, `xyRouting`, a closed-form flow:
  row then column) routes uniform traffic at `θ = 8 (k² - 1) / k³`; the busiest link, at the
  middle of a row or column, carries exactly `2`.
* `mesh_opt` : for even `k ≥ 2`, **the mesh's exact fluid throughput** is `8 (k² - 1) / k³`
  (`IsGreatest`).
* `wire_ceiling` : **headline.**  For every `k ≥ 2` and every topology with capacities `≤ 2`,
  Manhattan-respecting lengths and at most the mesh's wire `2 k (k - 1)`:
  `θ ≤ (3k / (2(k + 1))) * (8 (k² - 1) / k³) = 12 (k - 1) / k²`.  With `mesh_opt`
  (`wire_ceiling_opt`): for even `k`, no such topology beats the mesh by more than the factor
  `3k / (2(k + 1))`, below `3/2` for every `k` (`ceiling_factor_lt`) and `4/3` at `k = 8`
  (`mesh_opt_eight`, `wire_ceiling_eight`).
* `mesh_per_wire` : per unit of wire the mesh reaches `4 (k + 1) / k⁴`, against the ceiling
  `6 / k³` of `throughput_le_wire`; their ratio is again `3k / (2(k + 1))`.

All results are over `ℚ` and general in `k` except the two `k = 8` instances.
-/

namespace AsyncLean

namespace Fluid

open Finset

/-- Counting `i < n` with `i < m`: there are `m` of them (for `m ≤ n`). -/
theorem sum_range_lt (n m : ℕ) (h : m ≤ n) :
    ∑ i ∈ range n, (if i < m then (1 : ℚ) else 0) = m := by
  induction n with
  | zero => simp at h; simp [h]
  | succ n ih =>
    rw [sum_range_succ]
    rcases Nat.lt_or_ge n m with h' | h'
    · have : m = n + 1 := by omega
      subst this
      rw [sum_congr rfl (g := fun _ => (1 : ℚ)) (fun i hi => by
        simp at hi; simp [show i < n + 1 by omega])]
      simp
    · rw [ih h']; simp [show ¬ n < m by omega]

/-- Counting `i < n` with `m ≤ i`: there are `n - m` of them (for `m ≤ n`). -/
theorem sum_range_ge (n m : ℕ) (h : m ≤ n) :
    ∑ i ∈ range n, (if m ≤ i then (1 : ℚ) else 0) = n - m := by
  have e : ∀ i ∈ range n, (if m ≤ i then (1 : ℚ) else 0) = 1 - (if i < m then 1 else 0) :=
    fun i _ => by split_ifs <;> first | omega | simp
  rw [sum_congr rfl e, sum_sub_distrib, sum_range_lt n m h]; simp

/-- A sum over `range n` of a term supported on the single index `c`. -/
theorem sum_range_single (n c : ℕ) (F : ℕ → ℚ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ b, P b → b = c) :
    ∑ b ∈ range n, (if P b then F b else 0) = if c < n ∧ P c then F c else 0 := by
  by_cases hc : c < n
  · rw [sum_eq_single_of_mem c (mem_range.2 hc)]
    · simp [hc]
    · intro b _ hb; split_ifs with hp
      · exact absurd (hP b hp) hb
      · rfl
  · rw [sum_eq_zero]
    · simp [hc]
    · intro b hb; split_ifs with hp
      · exact absurd (hP b hp ▸ mem_range.1 hb) hc
      · rfl

/-- Gauss: `∑ i < n, i = n (n - 1) / 2`. -/
theorem sum_range_cast (n : ℕ) : ∑ i ∈ range n, (i : ℚ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `∑ a, b < n, |a - b| = (n³ - n) / 3`. -/
theorem sum_range_abs (n : ℕ) :
    ∑ a ∈ range n, ∑ b ∈ range n, |(a : ℚ) - b| = (n ^ 3 - n) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ∑ a ∈ range n, |(a : ℚ) - n| = ∑ a ∈ range n, ((n : ℚ) - a) :=
      sum_congr rfl fun a ha => by
        simp at ha
        rw [abs_sub_comm, abs_of_nonneg (by
          have : (a : ℚ) ≤ n := by exact_mod_cast ha.le
          linarith)]
    have h2 : ∑ b ∈ range n, |(n : ℚ) - b| = ∑ a ∈ range n, ((n : ℚ) - a) :=
      sum_congr rfl fun a ha => by
        simp at ha
        rw [abs_of_nonneg (by
          have : (a : ℚ) ≤ n := by exact_mod_cast ha.le
          linarith)]
    simp only [sum_range_succ, sum_add_distrib, h1, h2, ih, sub_self, abs_zero, add_zero]
    rw [sum_sub_distrib, sum_range_cast]
    simp; ring


/-- Vertex `(x, y)` of the `k × k` grid is placed at the integer point `(x, y)`. -/
def gridPos {k : ℕ} (v : Fin k × Fin k) : ℤ × ℤ := (((v.1 : ℕ) : ℤ), ((v.2 : ℕ) : ℤ))

/-- **Uniform traffic** on the `k × k` grid: every vertex sends at rate `1` in total, spread
evenly over the `k² - 1` other vertices. -/
def uniform (k : ℕ) (s d : Fin k × Fin k) : ℚ := if s = d then 0 else 1 / ((k : ℚ) ^ 2 - 1)

/-- The **total wire** of a network with link lengths `len`: the sum of the lengths of the
directed links of positive capacity, halved (so that each undirected link of a symmetric network
is counted once). -/
def wire {V : Type*} [Fintype V] (N : Net V) (len : V → V → ℚ) : ℚ :=
  (∑ u, ∑ v, if 0 < N.cap u v then len u v else 0) / 2

/-- `∑ a, b : Fin k, |a - b| = (k³ - k) / 3`. -/
theorem sum_abs_fin (k : ℕ) :
    ∑ a : Fin k, ∑ b : Fin k, |((a : ℕ) : ℚ) - (b : ℕ)| = (k ^ 3 - k) / 3 := by
  calc ∑ a : Fin k, ∑ b : Fin k, |((a : ℕ) : ℚ) - (b : ℕ)|
      = ∑ a : Fin k, ∑ b ∈ range k, |((a : ℕ) : ℚ) - b| :=
        sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun b => |((a : ℕ) : ℚ) - b|) k
    _ = ∑ a ∈ range k, ∑ b ∈ range k, |(a : ℚ) - b| :=
        Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range k, |(a : ℚ) - b|) k
    _ = _ := sum_range_abs k

/-- **The total Manhattan distance** over all ordered pairs of grid vertices:
`∑ s d, dist s d = 2 k² (k³ - k) / 3`. -/
theorem sum_manhattan (k : ℕ) :
    ∑ s : Fin k × Fin k, ∑ d : Fin k × Fin k, manhattan (gridPos s) (gridPos d) =
      2 * k ^ 2 * (k ^ 3 - k) / 3 := by
  unfold manhattan gridPos
  simp only [Int.cast_natCast, Fintype.sum_prod_type, sum_add_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
  rw [sum_abs_fin]; ring

/-- The average distance under uniform traffic: `∑ s d, uniform k s d * dist s d = 2 k³ / 3`. -/
theorem uniform_dist (k : ℕ) (hk : 2 ≤ k) :
    ∑ s : Fin k × Fin k, ∑ d : Fin k × Fin k, uniform k s d * manhattan (gridPos s) (gridPos d) =
      2 * k ^ 3 / 3 := by
  have e : ∀ s d : Fin k × Fin k, uniform k s d * manhattan (gridPos s) (gridPos d) =
      1 / ((k : ℚ) ^ 2 - 1) * manhattan (gridPos s) (gridPos d) := by
    intro s d; unfold uniform; split_ifs with h
    · subst h; simp [manhattan_self]
    · rfl
  simp only [e, ← mul_sum, sum_manhattan]
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have : (k : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [show (2 * k ^ 2 * (k ^ 3 - k) / 3 : ℚ) = (k ^ 2 - 1) * (2 * k ^ 3 / 3) by ring, one_div,
    inv_mul_cancel_left₀ this]

/-- **The wire bound for uniform traffic**, for every topology on the `k × k` grid whose links
have capacity at most `2` and length at least their Manhattan length:
`θ * (2 k³ / 3) ≤ ∑ u v, cap u v * len u v ≤ 2 * ∑ (directed links of positive capacity) len`. -/
theorem uniform_wire_bound {k : ℕ} (hk : 2 ≤ k) (N : Net (Fin k × Fin k))
    (len : Fin k × Fin k → Fin k × Fin k → ℚ) (hlen : ∀ u v, 0 ≤ len u v)
    (hwire : ∀ u v, 0 < N.cap u v → manhattan (gridPos u) (gridPos v) ≤ len u v)
    (hcap : ∀ u v, N.cap u v ≤ 2) {θ : ℚ} (h : Routable N (uniform k) θ) :
    θ * (2 * k ^ 3 / 3) ≤ ∑ u, ∑ v, N.cap u v * len u v ∧
      ∑ u, ∑ v, N.cap u v * len u v ≤ 2 * ∑ u, ∑ v, (if 0 < N.cap u v then len u v else 0) := by
  constructor
  · have := wire_bound h gridPos len hlen hwire
    rwa [uniform_dist k hk] at this
  · rw [mul_sum]
    refine sum_le_sum fun u _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun v _ => ?_
    split_ifs with hc
    · nlinarith [hcap u v, hlen u v]
    · have : N.cap u v = 0 := le_antisymm (not_lt.1 hc) (N.cap_nonneg u v)
      simp [this]

/-- **Throughput per unit of wire**: under the hypotheses of `uniform_wire_bound`, uniform traffic
is routable only at `θ ≤ 6 * wire / k³`. -/
theorem throughput_le_wire {k : ℕ} (hk : 2 ≤ k) (N : Net (Fin k × Fin k))
    (len : Fin k × Fin k → Fin k × Fin k → ℚ) (hlen : ∀ u v, 0 ≤ len u v)
    (hwire : ∀ u v, 0 < N.cap u v → manhattan (gridPos u) (gridPos v) ≤ len u v)
    (hcap : ∀ u v, N.cap u v ≤ 2) {θ : ℚ} (h : Routable N (uniform k) θ) :
    θ ≤ 6 * wire N len / k ^ 3 := by
  obtain ⟨h1, h2⟩ := uniform_wire_bound hk N len hlen hwire hcap h
  have hk' : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [le_div_iff₀ (by positivity)]
  unfold wire
  linarith

/-- Two positions on a line of length `k` are neighbours. -/
def LineAdj {k : ℕ} (a b : Fin k) : Prop := (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a

/-- Decidability of the adjacency relation. -/
instance {k : ℕ} : DecidableRel (@LineAdj k) := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Two vertices of the `k × k` grid are mesh neighbours: same row and neighbouring columns, or
same column and neighbouring rows. -/
def MeshAdj {k : ℕ} (u v : Fin k × Fin k) : Prop :=
  (u.2 = v.2 ∧ LineAdj u.1 v.1) ∨ (u.1 = v.1 ∧ LineAdj u.2 v.2)

/-- Decidability of the adjacency relation. -/
instance {k : ℕ} : DecidableRel (@MeshAdj k) := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- **The `k × k` mesh**: capacity `2` (two lanes of capacity `1`) in both directions between grid
neighbours, `0` otherwise. -/
def meshNet (k : ℕ) : Net (Fin k × Fin k) where
  cap u v := if MeshAdj u v then 2 else 0
  cap_nonneg u v := by by_cases h : MeshAdj u v <;> simp [h]

/-- Neighbours are distinct. -/
theorem LineAdj.ne {k : ℕ} {a b : Fin k} (h : LineAdj a b) : a ≠ b := by
  rintro rfl; unfold LineAdj at h; omega

/-- The flow on a line `0, …, k-1` towards the destination `t` when every position sends rate `1`
to `t` (and `t` itself is not counted as a source on the line): the link `a → a+1` (left of
`t`) carries the `a + 1` positions `≤ a`, the link `b+1 → b` (right of `t`) the `k - 1 - b`
positions `> b`. -/
def lineFlowN (k t a b : ℕ) : ℚ :=
  (if a + 1 = b ∧ b ≤ t then ((a : ℚ) + 1) else 0) +
    (if b + 1 = a ∧ t ≤ b then ((k : ℚ) - 1 - b) else 0)

/-- The rate leaving position `a` in `lineFlowN`. -/
theorem lineFlowN_out (k t a : ℕ) (ha : a < k) (ht : t < k) :
    ∑ b ∈ range k, lineFlowN k t a b =
      (if a < t then (a : ℚ) + 1 else 0) + (if t < a then (k : ℚ) - a else 0) := by
  unfold lineFlowN
  rw [sum_add_distrib, sum_range_single k (a + 1) (fun _ => (a : ℚ) + 1) _ (fun b h => h.1.symm),
    sum_range_single k (a - 1) (fun b => (k : ℚ) - 1 - b) _ (fun b h => by omega)]
  congr 1
  · by_cases h : a < t
    · rw [ite_eq_left ⟨by omega, rfl, by omega⟩, ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  · by_cases h : t < a
    · rw [ite_eq_left ⟨by omega, by omega, by omega⟩, ite_eq_left h]
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      simp; ring
    · rw [ite_eq_right (by omega), ite_eq_right h]

/-- The rate entering position `a` in `lineFlowN`. -/
theorem lineFlowN_in (k t a : ℕ) (ha : a < k) :
    ∑ b ∈ range k, lineFlowN k t b a =
      (if a ≤ t then (a : ℚ) else 0) + (if t ≤ a then (k : ℚ) - 1 - a else 0) := by
  unfold lineFlowN
  rw [sum_add_distrib, sum_range_single k (a - 1) (fun b => (b : ℚ) + 1) _ (fun b h => by omega),
    sum_range_single k (a + 1) (fun _ => (k : ℚ) - 1 - a) _ (fun b h => h.1.symm)]
  congr 1
  · by_cases h : a ≤ t
    · rw [ite_eq_left h]
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0; simp
      · rw [ite_eq_left ⟨by omega, by omega, h⟩]
        obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        simp
    · rw [ite_eq_right (by omega), ite_eq_right h]
  · by_cases h : t ≤ a
    · rw [ite_eq_left h]
      by_cases h' : a + 1 < k
      · rw [ite_eq_left ⟨h', rfl, h⟩]
      · rw [ite_eq_right (by omega)]
        have : (k : ℚ) = a + 1 := by exact_mod_cast (show k = a + 1 by omega)
        rw [this]; ring
    · rw [ite_eq_right (by omega), ite_eq_right h]

/-- Conservation of the line flow: every position sends `1` more than it receives, except the
destination, which absorbs `k - 1`. -/
theorem lineFlowN_conserve (k t a : ℕ) (ha : a < k) (ht : t < k) :
    ∑ b ∈ range k, lineFlowN k t a b - ∑ b ∈ range k, lineFlowN k t b a =
      1 - if a = t then (k : ℚ) else 0 := by
  rw [lineFlowN_out k t a ha ht, lineFlowN_in k t a ha]
  rcases lt_trichotomy a t with h | h | h
  · simp [h, h.le, h.ne, not_lt.2 h.le, show ¬ t ≤ a by omega]
  · subst h; simp
  · simp [h, h.le, h.ne', not_lt.2 h.le, show ¬ a ≤ t by omega]

/-- The load of a line link summed over all destinations is at most `k² / 4`, and `0` on a
non-link. -/
theorem lineFlowN_load (k a b : ℕ) (hb : b < k) :
    ∑ t ∈ range k, lineFlowN k t a b ≤ if a + 1 = b ∨ b + 1 = a then (k : ℚ) ^ 2 / 4 else 0 := by
  unfold lineFlowN
  rw [sum_add_distrib]
  have e1 : ∑ t ∈ range k, (if a + 1 = b ∧ b ≤ t then ((a : ℚ) + 1) else 0) =
      if a + 1 = b then ((a : ℚ) + 1) * (k - b) else 0 := by
    by_cases h : a + 1 = b
    · have : ∀ t, (if a + 1 = b ∧ b ≤ t then ((a : ℚ) + 1) else 0) =
          ((a : ℚ) + 1) * (if b ≤ t then 1 else 0) := fun t => by
        by_cases h' : b ≤ t <;> simp [h, h']
      rw [sum_congr rfl (fun t _ => this t), ← mul_sum, sum_range_ge k b hb.le, ite_eq_left h]
    · rw [sum_eq_zero (fun t _ => by simp [h]), ite_eq_right h]
  have e2 : ∑ t ∈ range k, (if b + 1 = a ∧ t ≤ b then ((k : ℚ) - 1 - b) else 0) =
      if b + 1 = a then ((k : ℚ) - 1 - b) * (b + 1) else 0 := by
    by_cases h : b + 1 = a
    · have : ∀ t, (if b + 1 = a ∧ t ≤ b then ((k : ℚ) - 1 - b) else 0) =
          ((k : ℚ) - 1 - b) * (if t < b + 1 then 1 else 0) := fun t => by
        by_cases h' : t ≤ b
        · rw [ite_eq_left ⟨h, h'⟩, ite_eq_left (show t < b + 1 by omega), mul_one]
        · rw [ite_eq_right (fun hc => h' hc.2), ite_eq_right (show ¬ t < b + 1 by omega),
            mul_zero]
      rw [sum_congr rfl (fun t _ => this t), ← mul_sum, sum_range_lt k (b + 1) (by omega),
        ite_eq_left h]
      push_cast; ring
    · rw [sum_eq_zero (fun t _ => by simp [h]), ite_eq_right h]
  rw [e1, e2]
  have hbk : (b : ℚ) + 1 ≤ k := by exact_mod_cast hb
  by_cases h1 : a + 1 = b
  · have h2 : ¬ b + 1 = a := by omega
    have hab : (b : ℚ) = a + 1 := by exact_mod_cast h1.symm
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left (Or.inl h1), hab]
    nlinarith [sq_nonneg ((k : ℚ) - 2 * (a + 1))]
  · by_cases h2 : b + 1 = a
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (Or.inr h2)]
      nlinarith [sq_nonneg ((k : ℚ) - 2 * (b + 1))]
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega)]; simp

/-- The line flow `lineFlowN` indexed by `Fin k`. -/
def lineFlow {k : ℕ} (t a b : Fin k) : ℚ := lineFlowN k t a b

/-- The line flow is nonnegative. -/
theorem lineFlow_nonneg {k : ℕ} (t a b : Fin k) : 0 ≤ lineFlow t a b := by
  unfold lineFlow lineFlowN
  have hb : (b : ℚ) + 1 ≤ k := by exact_mod_cast b.2
  split_ifs <;> first | positivity | linarith

/-- Conservation of the line flow: `out - in = 1 - k * [a = t]`. -/
theorem lineFlow_conserve {k : ℕ} (t a : Fin k) :
    ∑ b, lineFlow t a b - ∑ b, lineFlow t b a = 1 - if a = t then (k : ℚ) else 0 := by
  have h1 : ∑ b, lineFlow t a b = ∑ b ∈ range k, lineFlowN k t a b :=
    Fin.sum_univ_eq_sum_range (fun b => lineFlowN k t a b) k
  have h2 : ∑ b, lineFlow t b a = ∑ b ∈ range k, lineFlowN k t b a :=
    Fin.sum_univ_eq_sum_range (fun b => lineFlowN k t b a) k
  rw [h1, h2, lineFlowN_conserve k t a a.2 t.2]
  by_cases h : a = t
  · simp [h]
  · simp [h, Fin.val_inj]

/-- The total load of a line link over all destinations is at most `k² / 4` on neighbours and `0`
otherwise. -/
theorem lineFlow_load {k : ℕ} (a b : Fin k) :
    ∑ t, lineFlow t a b ≤ if LineAdj a b then (k : ℚ) ^ 2 / 4 else 0 := by
  have h1 : ∑ t, lineFlow t a b = ∑ t ∈ range k, lineFlowN k t a b :=
    Fin.sum_univ_eq_sum_range (fun t => lineFlowN k t a b) k
  rw [h1]
  exact lineFlowN_load k a b b.2

/-- **XY routing** of uniform traffic at rate `r` per pair, commodity `d`: the traffic of every
source first runs along its row to the column of `d` (one line flow per row), then down the
column of `d` (a line flow carrying the `k` sources of each row, weight `k`). -/
def xyFlow (k : ℕ) (r : ℚ) (d u v : Fin k × Fin k) : ℚ :=
  r * ((if u.2 = v.2 then lineFlow d.1 u.1 v.1 else 0) +
    (if u.1 = d.1 ∧ v.1 = d.1 then (k : ℚ) * lineFlow d.2 u.2 v.2 else 0))

/-- Conservation of XY routing: every vertex sends `r` more than it receives, except the
destination, which absorbs `r * (k² - 1)`. -/
theorem xyFlow_conserve (k : ℕ) (r : ℚ) (d v : Fin k × Fin k) :
    ∑ w, xyFlow k r d v w - ∑ u, xyFlow k r d u v = r * (1 - if v = d then (k : ℚ) ^ 2 else 0) := by
  unfold xyFlow
  simp only [← mul_sum, ← mul_sub, sum_add_distrib, Fintype.sum_prod_type]
  congr 1
  by_cases h : v.1 = d.1
  · simp [h, ← mul_sum]
    rw [show ∀ A B C D : ℚ, A + k * B - (C + k * D) = (A - C) + k * (B - D) by intros; ring,
      lineFlow_conserve, lineFlow_conserve, ite_eq_left rfl]
    by_cases h2 : v.2 = d.2
    · rw [ite_eq_left (Prod.ext h h2), ite_eq_left h2]; ring
    · rw [ite_eq_right (fun e => h2 (congrArg Prod.snd e)), ite_eq_right h2]; ring
  · simp [h]
    rw [lineFlow_conserve, ite_eq_right h, ite_eq_right (fun e => h (congrArg Prod.fst e))]

/-- The load of a link under XY routing, summed over all destinations. -/
theorem xyFlow_load (k : ℕ) (r : ℚ) (u v : Fin k × Fin k) :
    ∑ d, xyFlow k r d u v = r * ((if u.2 = v.2 then (k : ℚ) * ∑ t, lineFlow t u.1 v.1 else 0) +
      (if u.1 = v.1 then (k : ℚ) * ∑ t, lineFlow t u.2 v.2 else 0)) := by
  unfold xyFlow
  simp only [← mul_sum, sum_add_distrib, Fintype.sum_prod_type]
  congr 2
  · by_cases h : u.2 = v.2 <;> simp [h, ← mul_sum]
  · by_cases h : u.1 = v.1
    · simp [h, ← mul_sum]
    · rw [ite_eq_right h]
      refine sum_eq_zero fun a _ => sum_eq_zero fun b _ => ite_eq_right ?_
      rintro ⟨h1, h2⟩; exact h (h1.trans h2.symm)

/-- XY routing is nonnegative. -/
theorem xyFlow_nonneg (k : ℕ) {r : ℚ} (hr : 0 ≤ r) (d u v : Fin k × Fin k) :
    0 ≤ xyFlow k r d u v := by
  unfold xyFlow
  have h1 := lineFlow_nonneg d.1 u.1 v.1
  have h2 := mul_nonneg (Nat.cast_nonneg (α := ℚ) k) (lineFlow_nonneg d.2 u.2 v.2)
  apply mul_nonneg hr
  split_ifs <;> linarith

/-- At rate `r = 8 / k³` per pair, XY routing loads every mesh link by at most its capacity `2`. -/
theorem xyFlow_capacity (k : ℕ) (hk : 1 ≤ k) (u v : Fin k × Fin k) :
    ∑ d, xyFlow k (8 / (k : ℚ) ^ 3) d u v ≤ (meshNet k).cap u v := by
  rw [xyFlow_load]
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  have l1 := lineFlow_load u.1 v.1
  have l2 := lineFlow_load u.2 v.2
  have n1 : 0 ≤ ∑ t, lineFlow t u.1 v.1 := sum_nonneg fun t _ => lineFlow_nonneg _ _ _
  have n2 : 0 ≤ ∑ t, lineFlow t u.2 v.2 := sum_nonneg fun t _ => lineFlow_nonneg _ _ _
  have e : 8 / (k : ℚ) ^ 3 * (k * (k ^ 2 / 4)) = 2 := by
    rw [div_mul_eq_mul_div, div_eq_iff (pow_pos hk' 3).ne']; ring
  have hr : 0 ≤ 8 / (k : ℚ) ^ 3 := div_nonneg (by norm_num) (pow_nonneg hk'.le 3)
  show _ ≤ ite _ _ _
  by_cases ha : MeshAdj u v
  · rw [ite_eq_left ha]
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ite_eq_left h1, ite_eq_right h2.ne, add_zero, ← e]
      rw [ite_eq_left h2] at l1
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left l1 hk'.le) hr
    · rw [ite_eq_left h1, ite_eq_right h2.ne, zero_add, ← e]
      rw [ite_eq_left h2] at l2
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left l2 hk'.le) hr
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

/-- **XY routing as a fluid flow** of uniform traffic at throughput `8 (k² - 1) / k³` in the
mesh. -/
def xyRouting (k : ℕ) (hk : 2 ≤ k) :
    Flow (meshNet k) (uniform k) (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) where
  f := xyFlow k (8 / (k : ℚ) ^ 3)
  nonneg := xyFlow_nonneg k (div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg k) 3))
  conserve d v hv := by
    rw [xyFlow_conserve, ite_eq_right hv]
    unfold uniform
    rw [ite_eq_right hv]
    have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have : (k : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
    rw [sub_zero, mul_one, mul_one_div, eq_div_iff this]; ring
  capacity u v := xyFlow_capacity k (by omega) u v

/-- **Lower bound** (every `k ≥ 2`): uniform traffic is routable in the `k × k` mesh at throughput
`8 (k² - 1) / k³`. -/
theorem mesh_routable (k : ℕ) (hk : 2 ≤ k) :
    Routable (meshNet k) (uniform k) (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) := ⟨xyRouting k hk⟩

/-- Summing a function of the first coordinate over the grid. -/
theorem sum_fst {k : ℕ} (g : Fin k → ℚ) : ∑ s : Fin k × Fin k, g s.1 = k * ∑ i, g i := by
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]

/-- **Upper bound** (even `k ≥ 2`, any routing): by the cut bound for the left half of the mesh,
uniform traffic is routable in the `k × k` mesh only at `θ ≤ 8 (k² - 1) / k³`. -/
theorem mesh_upper (k : ℕ) (hk : 2 ≤ k) (he : Even k) {θ : ℚ}
    (h : Routable (meshNet k) (uniform k) θ) : θ ≤ 8 * ((k : ℚ) ^ 2 - 1) / k ^ 3 := by
  obtain ⟨m, hm⟩ := he
  have hmk : m < k := by omega
  have key := cut_bound h (fun u : Fin k × Fin k => 2 * (u.1 : ℕ) < k)
  -- the traffic across the cut
  have hA : ∑ s : Fin k × Fin k, (if 2 * (s.1 : ℕ) < k then (1 : ℚ) else 0) = k * m := by
    rw [sum_fst (fun i : Fin k => if 2 * (i : ℕ) < k then (1 : ℚ) else 0)]
    rw [Fin.sum_univ_eq_sum_range (fun i => if 2 * i < k then (1 : ℚ) else 0) k,
      sum_congr rfl (g := fun i => if i < m then (1 : ℚ) else 0)
        (fun i _ => by simp only [show 2 * i < k ↔ i < m by omega]),
      sum_range_lt k m hmk.le]
  have hB : ∑ d : Fin k × Fin k, (if ¬ 2 * (d.1 : ℕ) < k then (1 : ℚ) else 0) = k * m := by
    rw [sum_fst (fun i : Fin k => if ¬ 2 * (i : ℕ) < k then (1 : ℚ) else 0)]
    rw [Fin.sum_univ_eq_sum_range (fun i => if ¬ 2 * i < k then (1 : ℚ) else 0) k,
      sum_congr rfl (g := fun i => if m ≤ i then (1 : ℚ) else 0)
        (fun i _ => by simp only [show ¬ 2 * i < k ↔ m ≤ i by omega]),
      sum_range_ge k m hmk.le]
    have : (k : ℚ) = m + m := by exact_mod_cast hm
    rw [this]; ring
  have hL : ∑ s : Fin k × Fin k, ∑ d : Fin k × Fin k,
      (if 2 * (s.1 : ℕ) < k ∧ ¬ 2 * (d.1 : ℕ) < k then uniform k s d else 0) =
        1 / ((k : ℚ) ^ 2 - 1) * ((k * m) * (k * m)) := by
    have e : ∀ s d : Fin k × Fin k,
        (if 2 * (s.1 : ℕ) < k ∧ ¬ 2 * (d.1 : ℕ) < k then uniform k s d else 0) =
          1 / ((k : ℚ) ^ 2 - 1) * ((if 2 * (s.1 : ℕ) < k then (1 : ℚ) else 0) *
            (if ¬ 2 * (d.1 : ℕ) < k then (1 : ℚ) else 0)) := by
      intro s d
      by_cases hs : 2 * (s.1 : ℕ) < k
      · by_cases hd : 2 * (d.1 : ℕ) < k
        · simp [hs, hd]
        · have hsd : s ≠ d := by rintro rfl; exact hd hs
          simp [hs, hd, uniform, hsd]
      · simp [hs]
    simp only [e, ← mul_sum]
    rw [← sum_mul, hA, hB]
  -- the capacity of the cut
  have hR : ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
      (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then (meshNet k).cap u v else 0) ≤
        2 * k := by
    have p : ∀ u v : Fin k × Fin k,
        (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then (meshNet k).cap u v else 0) ≤
          if v = (⟨m, hmk⟩, u.2) then (if (u.1 : ℕ) + 1 = m then (2 : ℚ) else 0) else 0 := by
      intro u v
      show (if _ then ite _ _ _ else _) ≤ _
      by_cases hc : (2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k) ∧ MeshAdj u v
      · obtain ⟨⟨hu, hv⟩, hadj⟩ := hc
        rw [ite_eq_left ⟨hu, hv⟩, ite_eq_left hadj]
        rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, _⟩
        · have hv' : v = (⟨m, hmk⟩, u.2) := Prod.ext (Fin.ext (by simp; omega)) h1.symm
          rw [ite_eq_left hv', ite_eq_left (by omega)]
        · omega
        · rw [h1] at hu; exact absurd hu hv
      · have : (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then
            (if MeshAdj u v then (2 : ℚ) else 0) else 0) = 0 := by
          by_cases h1 : 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k
          · rw [ite_eq_left h1, ite_eq_right (fun h2 => hc ⟨h1, h2⟩)]
          · exact ite_eq_right h1
        rw [this]
        split_ifs <;> norm_num
    calc _ ≤ ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
          (if v = (⟨m, hmk⟩, u.2) then (if (u.1 : ℕ) + 1 = m then (2 : ℚ) else 0) else 0) :=
          sum_le_sum fun u _ => sum_le_sum fun v _ => p u v
      _ = ∑ u : Fin k × Fin k, (if (u.1 : ℕ) + 1 = m then (2 : ℚ) else 0) := by
          simp only [sum_ite_eq', mem_univ, ite_true]
      _ = 2 * k := by
          rw [sum_fst (fun i : Fin k => if (i : ℕ) + 1 = m then (2 : ℚ) else 0)]
          rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 = m then (2 : ℚ) else 0) k,
            sum_range_single k (m - 1) (fun _ => (2 : ℚ)) (fun i => i + 1 = m)
              (fun i hi => by omega), ite_eq_left ⟨by omega, by omega⟩]
          ring
  rw [hL] at key
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hc : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hkm : (k : ℚ) = m + m := by exact_mod_cast hm
  have hm' : (0 : ℚ) < m := by linarith
  have k2 : θ * ((k * m) * (k * m)) ≤ 2 * k * ((k : ℚ) ^ 2 - 1) := by
    have := mul_le_mul_of_nonneg_right (key.trans hR) hc.le
    rwa [show θ * (1 / ((k : ℚ) ^ 2 - 1) * ((k * m) * (k * m))) * ((k : ℚ) ^ 2 - 1) =
      θ * ((k * m) * (k * m)) * (1 / ((k : ℚ) ^ 2 - 1) * ((k : ℚ) ^ 2 - 1)) by ring,
      one_div_mul_cancel hc.ne', mul_one] at this
  rw [hkm] at k2 ⊢
  rw [le_div_iff₀ (by positivity)]
  have k3 : 4 * m * (θ * m ^ 3) ≤ 4 * m * ((m + m) ^ 2 - 1) := by nlinarith
  have k4 := le_of_mul_le_mul_left k3 (by linarith)
  nlinarith

/-- **The mesh's exact fluid throughput** (even `k ≥ 2`): the largest throughput at which uniform
traffic is routable in the `k × k` mesh is `8 (k² - 1) / k³`. -/
theorem mesh_opt (k : ℕ) (hk : 2 ≤ k) (he : Even k) :
    IsGreatest {θ : ℚ | Routable (meshNet k) (uniform k) θ} (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) :=
  ⟨mesh_routable k hk, fun _ h => mesh_upper k hk he h⟩

/-- Mesh links have capacity at most `2`. -/
theorem mesh_cap_le (k : ℕ) (u v : Fin k × Fin k) : (meshNet k).cap u v ≤ 2 := by
  show ite _ _ _ ≤ _; split_ifs <;> norm_num

/-- Mesh links have Manhattan length `1`. -/
theorem mesh_len (k : ℕ) (u v : Fin k × Fin k) (h : 0 < (meshNet k).cap u v) :
    manhattan (gridPos u) (gridPos v) ≤ 1 := by
  have hadj : MeshAdj u v := by
    by_contra hn; exact absurd h (by show ¬ 0 < ite _ _ _; rw [ite_eq_right hn]; exact lt_irrefl 0)
  unfold manhattan gridPos
  simp only [Int.cast_natCast]
  rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have : ((v.1 : ℕ) : ℚ) = (u.1 : ℕ) + 1 := by exact_mod_cast h2.symm
    rw [h1, this, sub_self, abs_zero]; norm_num
  · have : ((u.1 : ℕ) : ℚ) = (v.1 : ℕ) + 1 := by exact_mod_cast h2.symm
    rw [h1, this, sub_self, abs_zero]; norm_num
  · have : ((v.2 : ℕ) : ℚ) = (u.2 : ℕ) + 1 := by exact_mod_cast h2.symm
    rw [h1, this, sub_self, abs_zero]; norm_num
  · have : ((u.2 : ℕ) : ℚ) = (v.2 : ℕ) + 1 := by exact_mod_cast h2.symm
    rw [h1, this, sub_self, abs_zero]; norm_num

/-- The number of neighbours of position `a` on a line of length `k`. -/
theorem lineAdj_count_row (k a : ℕ) (ha : a < k) :
    ∑ b ∈ range k, (if a + 1 = b ∨ b + 1 = a then (1 : ℚ) else 0) =
      (if a + 1 < k then 1 else 0) + (if 1 ≤ a then 1 else 0) := by
  have e : ∀ b, (if a + 1 = b ∨ b + 1 = a then (1 : ℚ) else 0) =
      (if a + 1 = b then 1 else 0) + (if b + 1 = a then 1 else 0) := by
    intro b
    by_cases h1 : a + 1 = b
    · rw [ite_eq_left (Or.inl h1), ite_eq_left h1, ite_eq_right (by omega)]; norm_num
    · by_cases h2 : b + 1 = a
      · rw [ite_eq_left (Or.inr h2), ite_eq_right h1, ite_eq_left h2]; norm_num
      · rw [ite_eq_right (by omega), ite_eq_right h1, ite_eq_right h2]; norm_num
  rw [sum_congr rfl (fun b _ => e b), sum_add_distrib,
    sum_range_single k (a + 1) (fun _ => (1 : ℚ)) (fun b => a + 1 = b) (fun b h => h.symm),
    sum_range_single k (a - 1) (fun _ => (1 : ℚ)) (fun b => b + 1 = a) (fun b h => by omega)]
  congr 1
  · by_cases h : a + 1 < k
    · rw [ite_eq_left ⟨h, rfl⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h h'.1), ite_eq_right h]
  · by_cases h : 1 ≤ a
    · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (by omega)), ite_eq_right h]

/-- A line of length `k ≥ 1` has `2 (k - 1)` ordered pairs of neighbours. -/
theorem lineAdj_count (k : ℕ) (hk : 1 ≤ k) :
    ∑ a : Fin k, ∑ b : Fin k, (if LineAdj a b then (1 : ℚ) else 0) = 2 * ((k : ℚ) - 1) := by
  have h1 : ∀ a : Fin k, ∑ b : Fin k, (if LineAdj a b then (1 : ℚ) else 0) =
      (if (a : ℕ) + 1 < k then 1 else 0) + (if 1 ≤ (a : ℕ) then 1 else 0) := by
    intro a
    rw [← lineAdj_count_row k a a.2]
    exact Fin.sum_univ_eq_sum_range (fun b => if (a : ℕ) + 1 = b ∨ b + 1 = (a : ℕ)
      then (1 : ℚ) else 0) k
  rw [sum_congr rfl (fun a _ => h1 a),
    Fin.sum_univ_eq_sum_range (fun a => (if a + 1 < k then (1 : ℚ) else 0) +
      (if 1 ≤ a then 1 else 0)) k, sum_add_distrib,
    sum_congr rfl (g := fun a => if a < k - 1 then (1 : ℚ) else 0)
      (fun a _ => by simp only [show a + 1 < k ↔ a < k - 1 by omega]),
    sum_range_lt k (k - 1) (by omega), sum_range_ge k 1 hk]
  rw [Nat.cast_sub hk]; push_cast; ring

/-- The `k × k` mesh has `4 k (k - 1)` directed links. -/
theorem mesh_link_count (k : ℕ) (hk : 1 ≤ k) :
    ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
      (if 0 < (meshNet k).cap u v then (1 : ℚ) else 0) = 4 * k * ((k : ℚ) - 1) := by
  have e : ∀ u v : Fin k × Fin k, (if 0 < (meshNet k).cap u v then (1 : ℚ) else 0) =
      (if u.2 = v.2 then (if LineAdj u.1 v.1 then 1 else 0) else 0) +
        (if u.1 = v.1 then (if LineAdj u.2 v.2 then 1 else 0) else 0) := by
    intro u v
    show (if 0 < ite (MeshAdj u v) (2 : ℚ) 0 then (1 : ℚ) else 0) = _
    by_cases hA : u.2 = v.2 ∧ LineAdj u.1 v.1
    · have hB : ¬ u.1 = v.1 := hA.2.ne
      have hadj : MeshAdj u v := Or.inl hA
      simp [hadj, hA, hB]
    · by_cases hB : u.1 = v.1 ∧ LineAdj u.2 v.2
      · have hA' : ¬ u.2 = v.2 := hB.2.ne
        have hadj : MeshAdj u v := Or.inr hB
        simp [hadj, hB, hA']
      · have : ¬ MeshAdj u v := by unfold MeshAdj; tauto
        rw [ite_eq_right this]
        by_cases h1 : u.2 = v.2 <;> by_cases h2 : u.1 = v.1 <;> simp_all
  simp only [e, sum_add_distrib, Fintype.sum_prod_type]
  have s1 : ∀ (x : Fin k) (x1 : Fin k), ∑ x2 : Fin k, ∑ x3 : Fin k,
      (if x1 = x3 then (if LineAdj x x2 then (1 : ℚ) else 0) else 0) =
        ∑ x2 : Fin k, (if LineAdj x x2 then (1 : ℚ) else 0) := by
    intro x x1; simp only [sum_ite_eq, mem_univ, ite_true]
  have s2 : ∀ (x : Fin k) (x1 : Fin k), ∑ x2 : Fin k, ∑ x3 : Fin k,
      (if x = x2 then (if LineAdj x1 x3 then (1 : ℚ) else 0) else 0) =
        ∑ x3 : Fin k, (if LineAdj x1 x3 then (1 : ℚ) else 0) := by
    intro x x1; rw [sum_comm]; simp only [sum_ite_eq, mem_univ, ite_true]
  simp only [s1, s2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum,
    lineAdj_count k hk]
  ring

/-- **The mesh's wire**: with unit link lengths, `wire (meshNet k) 1 = 2 k (k - 1)`. -/
theorem mesh_wire (k : ℕ) (hk : 1 ≤ k) :
    wire (meshNet k) (fun _ _ => 1) = 2 * k * ((k : ℚ) - 1) := by
  unfold wire
  rw [mesh_link_count k hk]; ring

/-- **The wire ceiling** (headline): on the `k × k` grid (`k ≥ 2`), every topology with capacities
at most `2`, link lengths at least Manhattan, and at most the mesh's wire `2 k (k - 1)`, routes
uniform traffic only at `θ ≤ (3k / (2(k + 1))) * (8 (k² - 1) / k³) = 12 (k - 1) / k²`: at most
`3k / (2(k + 1))` times the mesh's optimum (`mesh_opt`). -/
theorem wire_ceiling {k : ℕ} (hk : 2 ≤ k) (N : Net (Fin k × Fin k))
    (len : Fin k × Fin k → Fin k × Fin k → ℚ) (hlen : ∀ u v, 0 ≤ len u v)
    (hwire : ∀ u v, 0 < N.cap u v → manhattan (gridPos u) (gridPos v) ≤ len u v)
    (hcap : ∀ u v, N.cap u v ≤ 2) (hW : wire N len ≤ 2 * k * ((k : ℚ) - 1))
    {θ : ℚ} (h : Routable N (uniform k) θ) :
    θ ≤ 3 * k / (2 * (k + 1)) * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) := by
  have h1 := throughput_le_wire hk N len hlen hwire hcap h
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have e : 3 * k / (2 * (k + 1)) * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) =
      6 * (2 * k * ((k : ℚ) - 1)) / k ^ 3 := by
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]; ring
  rw [e]
  exact h1.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-- **The wire ceiling, relative form** (even `k ≥ 2`): if `θm` is the mesh's optimal throughput for
uniform traffic, every topology with capacities at most `2`, Manhattan-respecting lengths and no
more wire than the mesh routes uniform traffic only at `θ ≤ 3k / (2(k + 1)) * θm`. -/
theorem wire_ceiling_opt {k : ℕ} (hk : 2 ≤ k) (he : Even k) {θm : ℚ}
    (hm : IsGreatest {θ : ℚ | Routable (meshNet k) (uniform k) θ} θm)
    (N : Net (Fin k × Fin k))
    (len : Fin k × Fin k → Fin k × Fin k → ℚ) (hlen : ∀ u v, 0 ≤ len u v)
    (hwire : ∀ u v, 0 < N.cap u v → manhattan (gridPos u) (gridPos v) ≤ len u v)
    (hcap : ∀ u v, N.cap u v ≤ 2) (hW : wire N len ≤ wire (meshNet k) (fun _ _ => 1))
    {θ : ℚ} (h : Routable N (uniform k) θ) :
    θ ≤ 3 * k / (2 * (k + 1)) * θm := by
  rw [hm.unique (mesh_opt k hk he)]
  rw [mesh_wire k (by omega)] at hW
  exact wire_ceiling hk N len hlen hwire hcap hW h

/-- **The mesh per unit of wire**: its throughput `8 (k² - 1) / k³` divided by its wire `2k(k - 1)`
is `4 (k + 1) / k⁴`; compare `6 / k³` per unit of wire for any topology (`throughput_le_wire`). -/
theorem mesh_per_wire (k : ℕ) (hk : 2 ≤ k) :
    8 * ((k : ℚ) ^ 2 - 1) / k ^ 3 / wire (meshNet k) (fun _ _ => 1) = 4 * (k + 1) / k ^ 4 := by
  rw [mesh_wire k (by omega)]
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  rw [div_div, div_eq_div_iff (by
    have : (0 : ℚ) < k ^ 3 * (2 * k * (k - 1)) := by
      apply mul_pos (by positivity); apply mul_pos (by positivity); linarith
    exact this.ne') (by positivity)]
  ring

/-- The ceiling factor `3k / (2(k + 1))` is below `3/2` for every `k`. -/
theorem ceiling_factor_lt (k : ℕ) : 3 * (k : ℚ) / (2 * (k + 1)) < 3 / 2 := by
  rw [div_lt_iff₀ (by positivity)]; linarith

/-- The `8 × 8` mesh: its exact fluid throughput under uniform traffic is `63/64`. -/
theorem mesh_opt_eight :
    IsGreatest {θ : ℚ | Routable (meshNet 8) (uniform 8) θ} (63 / 64) := by
  have := mesh_opt 8 (by norm_num) ⟨4, rfl⟩
  norm_num at this
  exact this

/-- On the `8 × 8` grid, every topology with capacities at most `2`, Manhattan-respecting lengths
and at most the mesh's wire `112` routes uniform traffic only at `θ ≤ 21/16 = (4/3) * (63/64)`. -/
theorem wire_ceiling_eight (N : Net (Fin 8 × Fin 8))
    (len : Fin 8 × Fin 8 → Fin 8 × Fin 8 → ℚ) (hlen : ∀ u v, 0 ≤ len u v)
    (hwire : ∀ u v, 0 < N.cap u v → manhattan (gridPos u) (gridPos v) ≤ len u v)
    (hcap : ∀ u v, N.cap u v ≤ 2) (hW : wire N len ≤ 112)
    {θ : ℚ} (h : Routable N (uniform 8) θ) : θ ≤ 21 / 16 := by
  have := wire_ceiling (k := 8) (by norm_num) N len hlen hwire hcap (by norm_num; linarith) h
  norm_num at this
  linarith

end Fluid

end AsyncLean
