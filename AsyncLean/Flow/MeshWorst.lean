/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.MeshWire

/-!
# Worst-case throughput of the mesh: O1TURN is optimal, XY loses a factor `2 (k - 1) / k`

The `k × k` mesh (`meshNet k`, capacity `2` on every directed link) under **admissible** traffic
(`Admissible T`: doubly substochastic, every source sends and every destination receives at most
rate `1`; permutations are admissible).  The **worst-case throughput** of a routing is the largest
`θ` at which it routes `θ * T` for every admissible `T`.

Routings are built from unit paths (`xyPath`, `yxPath`, `o1Path`: one path per source and
destination, conservation `out - in = [v = s] - [v = d]`), and a path flow `routeFlow P T θ` sends
`θ * T s d` along the path from `s` to `d`.  For XY this is, in every row, a weighted line flow
towards the column of `d`, then a weighted line flow in that column.  Every path only steps towards
its destination (`MeshStep`), so the flows are **minimal** (`Flow.Minimal` for the Manhattan
distance).

* `xy_load`, `o1_load` : **load bounds.**  On a row link `(a, y) → (a + 1, y)` the XY paths carry at
  most the row sums of the sources `(i, y)`, `i ≤ a`, so at most `a + 1`; the YX paths carry at
  most the column sums of the destinations `(j, y)`, `j ≥ a + 1`, so at most `k - 1 - a`
  (`Admissible.load_le`).  XY loads a link with at most `k - 1`, O1TURN (half XY, half YX) with at
  most `k / 2`; symmetrically for the other directions and the columns.
* `o1turn_admissible` (`o1Routing`) : **every admissible matrix is routable at `4 / k`** by a
  minimal flow, O1TURN.
* `bitcomp`, `bitcomp_upper` : **bit-complement** `(x, y) ↦ (k - 1 - x, k - 1 - y)`: for even `k`,
  any routing has `θ ≤ 4 / k` (cut bound for the left half: `k² / 2` vertices send across `k` links
  of capacity `2`).
* `worst_opt` : **no routing beats O1TURN in the worst case** (even `k ≥ 2`): the best worst-case
  throughput over all routings, adaptive or with detours, is exactly `4 / k` (`IsGreatest`); at
  `k = 8` it is `1/2` (`worst_opt_eight`).
* `bitcomp_opt`, `bitcomp_minimal` : bit-complement's exact throughput is `4 / k`, reached by a
  minimal flow: detours add nothing.
* `xy_admissible` (`xyRoutingT`) : XY routes every admissible matrix at `2 / (k - 1)`, minimally;
  `xy_worst` : this is tight: in `xyWorst k`, the vertices `(i, 0)`, `i < k - 1`, all send to the
  last column, through the link `(k - 2, 0) → (k - 1, 0)`.  `xy_worst_opt` : XY's exact
  worst-case throughput is `2 / (k - 1)`, `2/7` at `k = 8` (`xy_worst_opt_eight`).
* `o1turn_xy_ratio` : `4 / k = (2 (k - 1) / k) * (2 / (k - 1))`, and `2 / (k - 1) ≤ 4 / k`.

All results are over `ℚ` and general in `k` except the two `k = 8` instances.
-/

namespace AsyncLean

namespace Fluid

open Finset

/-- The straight path from `i` to `t` on a line, as a unit flow: `1` on the link `a → b` if it
is a step from `i` towards `t` (`a → a + 1` with `i ≤ a < t`, or `a → a - 1` with `t < a ≤ i`),
`0` otherwise. -/
def segN (i t a b : ℕ) : ℚ :=
  (if a + 1 = b ∧ i ≤ a ∧ b ≤ t then 1 else 0) + (if b + 1 = a ∧ t ≤ b ∧ a ≤ i then 1 else 0)

/-- Conservation of the straight path: a position sends `1` more than it receives if it is the
start `i`, `1` less if it is the end `t` (nothing if `i = t`). -/
theorem segN_conserve (k i t a : ℕ) (ha : a < k) (hi : i < k) (ht : t < k) :
    ∑ b ∈ range k, segN i t a b - ∑ b ∈ range k, segN i t b a =
      (if a = i then 1 else 0) - (if a = t then 1 else 0) := by
  unfold segN
  rw [sum_add_distrib, sum_add_distrib,
    sum_range_single k (a + 1) (fun _ => (1 : ℚ)) _ (fun b h => h.1.symm),
    sum_range_single k (a - 1) (fun _ => (1 : ℚ)) _ (fun b h => by omega),
    sum_range_single k (a - 1) (fun _ => (1 : ℚ)) _ (fun b h => by omega),
    sum_range_single k (a + 1) (fun _ => (1 : ℚ)) _ (fun b h => h.1.symm)]
  split_ifs <;> first | omega | norm_num

variable {k : ℕ}

/-- An **admissible** traffic matrix on the `k × k` grid (doubly substochastic): no source sends
more than `1` in total and no destination receives more than `1` in total.  Every permutation
(and every partial permutation) is admissible.  The entries `T d d` play no role: a flow's
conservation ignores them. -/
structure Admissible (T : Fin k × Fin k → Fin k × Fin k → ℚ) : Prop where
  /-- Every rate is nonnegative. -/
  nonneg : ∀ s d, 0 ≤ T s d
  /-- Every source sends at most `1`. -/
  row : ∀ s, ∑ d, T s d ≤ 1
  /-- Every destination receives at most `1`. -/
  col : ∀ d, ∑ s, T s d ≤ 1

/-- The straight path `segN` indexed by `Fin k`: the unit flow from `i` to `t` along a line. -/
def seg (i t a b : Fin k) : ℚ := segN i t a b

/-- Conservation of the straight path: `out - in = [a = i] - [a = t]`. -/
theorem seg_conserve (i t a : Fin k) :
    ∑ b, seg i t a b - ∑ b, seg i t b a = (if a = i then 1 else 0) - (if a = t then 1 else 0) := by
  have h1 : ∑ b, seg i t a b = ∑ b ∈ range k, segN i t a b :=
    Fin.sum_univ_eq_sum_range (fun b => segN i t a b) k
  have h2 : ∑ b, seg i t b a = ∑ b ∈ range k, segN i t b a :=
    Fin.sum_univ_eq_sum_range (fun b => segN i t b a) k
  rw [h1, h2, segN_conserve k i t a a.2 i.2 t.2]
  simp only [Fin.val_inj]

/-- The straight path is nonnegative. -/
theorem seg_nonneg (i t a b : Fin k) : 0 ≤ seg i t a b := by
  unfold seg segN; split_ifs <;> norm_num

/-- The link `a → b` of a line is a step towards `t`: `a + 1 = b ≤ t` or `t ≤ b = a - 1`. -/
def LineStep (a b t : Fin k) : Prop :=
  ((a : ℕ) + 1 = b ∧ (b : ℕ) ≤ t) ∨ ((b : ℕ) + 1 = a ∧ (t : ℕ) ≤ b)

/-- The straight path uses only steps towards its end. -/
theorem seg_step {i t a b : Fin k} (h : seg i t a b ≠ 0) : LineStep a b t := by
  by_contra hs
  unfold LineStep at hs
  apply h
  unfold seg segN
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]; norm_num

/-- The position `x` is on `a`'s side of the link `a → b`: `x ≤ a` if `a < b`, `x ≥ a` if
`a > b`. -/
def Near (a b x : Fin k) : Prop := ((a : ℕ) < b ∧ (x : ℕ) ≤ a) ∨ ((b : ℕ) < a ∧ (a : ℕ) ≤ x)

/-- Decidability of `Near`. -/
instance (a b x : Fin k) : Decidable (Near a b x) := inferInstanceAs (Decidable (_ ∨ _))

/-- The straight path from `i` uses the link `a → b` only if `i` is on `a`'s side. -/
theorem seg_le_near (i t a b : Fin k) : seg i t a b ≤ if Near a b i then 1 else 0 := by
  by_cases hn : Near a b i
  · rw [ite_eq_left hn]; unfold seg segN; split_ifs <;> first | omega | norm_num
  · rw [ite_eq_right hn]; unfold Near at hn; unfold seg segN; split_ifs <;> first | omega | norm_num

/-- The straight path to `t` uses the link `a → b` only if `t` is on `b`'s side. -/
theorem seg_le_far (i t a b : Fin k) : seg i t a b ≤ if ¬ Near a b t then 1 else 0 := by
  by_cases hn : ¬ Near a b t
  · rw [ite_eq_left hn]; unfold seg segN; split_ifs <;> first | omega | norm_num
  · rw [ite_eq_right hn]; unfold Near at hn; unfold seg segN; split_ifs <;> first | omega | norm_num

/-- A step is a link of the line. -/
theorem LineStep.adj {a b t : Fin k} (h : LineStep a b t) : LineAdj a b := by
  unfold LineStep at h; unfold LineAdj; omega

/-- A step towards `t` brings the position strictly closer to `t`. -/
theorem LineStep.abs_lt {a b t : Fin k} (h : LineStep a b t) :
    |((b : ℕ) : ℚ) - (t : ℕ)| < |((a : ℕ) : ℚ) - (t : ℕ)| := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e : ((b : ℕ) : ℚ) = (a : ℕ) + 1 := by exact_mod_cast h1.symm
    have h2' : ((b : ℕ) : ℚ) ≤ (t : ℕ) := by exact_mod_cast h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have e : ((a : ℕ) : ℚ) = (b : ℕ) + 1 := by exact_mod_cast h1.symm
    have h2' : ((t : ℕ) : ℚ) ≤ (b : ℕ) := by exact_mod_cast h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

/-- The link `u → v` of the mesh is a step towards `d`: along a row or a column, towards the
corresponding coordinate of `d`. -/
def MeshStep (u v d : Fin k × Fin k) : Prop :=
  (u.2 = v.2 ∧ LineStep u.1 v.1 d.1) ∨ (u.1 = v.1 ∧ LineStep u.2 v.2 d.2)

/-- A step is a mesh link. -/
theorem MeshStep.adj {u v d : Fin k × Fin k} (h : MeshStep u v d) : MeshAdj u v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2.adj⟩
  · exact Or.inr ⟨h1, h2.adj⟩

/-- A step towards `d` brings the Manhattan distance to `d` down (by one). -/
theorem MeshStep.closer {u v d : Fin k × Fin k} (h : MeshStep u v d) :
    manhattan (gridPos v) (gridPos d) < manhattan (gridPos u) (gridPos d) := by
  unfold manhattan gridPos
  simp only [Int.cast_natCast]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]; linarith [h2.abs_lt]
  · rw [h1]; linarith [h2.abs_lt]

/-- **The XY path** from `s` to `d`, as a unit flow: along the row of `s` to the column of `d`,
then along the column of `d` to `d`. -/
def xyPath (s d u v : Fin k × Fin k) : ℚ :=
  (if u.2 = s.2 ∧ v.2 = s.2 then seg s.1 d.1 u.1 v.1 else 0) +
    (if u.1 = d.1 ∧ v.1 = d.1 then seg s.2 d.2 u.2 v.2 else 0)

/-- **The YX path** from `s` to `d`, as a unit flow: along the column of `s` to the row of `d`,
then along the row of `d` to `d`. -/
def yxPath (s d u v : Fin k × Fin k) : ℚ :=
  (if u.1 = s.1 ∧ v.1 = s.1 then seg s.2 d.2 u.2 v.2 else 0) +
    (if u.2 = d.2 ∧ v.2 = d.2 then seg s.1 d.1 u.1 v.1 else 0)

/-- The YX path is the XY path with the coordinates swapped. -/
theorem yxPath_eq (s d u v : Fin k × Fin k) :
    yxPath s d u v = xyPath s.swap d.swap u.swap v.swap := rfl

/-- Conservation of the XY path: `out - in = [v = s] - [v = d]`. -/
theorem xyPath_conserve (s d v : Fin k × Fin k) :
    ∑ w, xyPath s d v w - ∑ u, xyPath s d u v =
      (if v = s then 1 else 0) - (if v = d then 1 else 0) := by
  unfold xyPath
  simp only [sum_add_distrib, Fintype.sum_prod_type]
  have hA : ∑ x : Fin k, ∑ y : Fin k, (if v.2 = s.2 ∧ y = s.2 then seg s.1 d.1 v.1 x else 0) =
      if v.2 = s.2 then ∑ x, seg s.1 d.1 v.1 x else 0 := by
    by_cases h : v.2 = s.2 <;> simp [h]
  have hB : ∑ x : Fin k, ∑ y : Fin k, (if v.1 = d.1 ∧ x = d.1 then seg s.2 d.2 v.2 y else 0) =
      if v.1 = d.1 then ∑ y, seg s.2 d.2 v.2 y else 0 := by
    by_cases h : v.1 = d.1 <;> simp [h]
  have hC : ∑ x : Fin k, ∑ y : Fin k, (if y = s.2 ∧ v.2 = s.2 then seg s.1 d.1 x v.1 else 0) =
      if v.2 = s.2 then ∑ x, seg s.1 d.1 x v.1 else 0 := by
    by_cases h : v.2 = s.2 <;> simp [h]
  have hD : ∑ x : Fin k, ∑ y : Fin k, (if x = d.1 ∧ v.1 = d.1 then seg s.2 d.2 y v.2 else 0) =
      if v.1 = d.1 then ∑ y, seg s.2 d.2 y v.2 else 0 := by
    by_cases h : v.1 = d.1 <;> simp [h]
  rw [hA, hB, hC, hD]
  have e1 := seg_conserve s.1 d.1 v.1
  have e2 := seg_conserve s.2 d.2 v.2
  by_cases h1 : v.2 = s.2 <;> by_cases h2 : v.1 = d.1 <;>
    simp only [h1, h2, ↓reduceIte, Prod.ext_iff, and_true, true_and, and_false, false_and]
      at e1 e2 ⊢ <;>
    linarith

/-- Conservation of the YX path: `out - in = [v = s] - [v = d]`. -/
theorem yxPath_conserve (s d v : Fin k × Fin k) :
    ∑ w, yxPath s d v w - ∑ u, yxPath s d u v =
      (if v = s then 1 else 0) - (if v = d then 1 else 0) := by
  have e := xyPath_conserve s.swap d.swap v.swap
  have h1 : ∑ w, yxPath s d v w = ∑ w, xyPath s.swap d.swap v.swap w :=
    (Equiv.prodComm (Fin k) (Fin k)).sum_comp (fun w => xyPath s.swap d.swap v.swap w)
  have h2 : ∑ u, yxPath s d u v = ∑ u, xyPath s.swap d.swap u v.swap :=
    (Equiv.prodComm (Fin k) (Fin k)).sum_comp (fun u => xyPath s.swap d.swap u v.swap)
  rw [h1, h2, e]
  simp only [Prod.swap_inj]

/-- **The O1TURN path** from `s` to `d`: half of the traffic on the XY path, half on the YX path. -/
def o1Path (s d u v : Fin k × Fin k) : ℚ := (xyPath s d u v + yxPath s d u v) / 2

/-- Conservation of the O1TURN path: `out - in = [v = s] - [v = d]`. -/
theorem o1Path_conserve (s d v : Fin k × Fin k) :
    ∑ w, o1Path s d v w - ∑ u, o1Path s d u v =
      (if v = s then 1 else 0) - (if v = d then 1 else 0) := by
  unfold o1Path
  simp only [div_eq_mul_inv, ← sum_mul, sum_add_distrib]
  have e1 := xyPath_conserve s d v
  have e2 := yxPath_conserve s d v
  linarith

/-- The XY path is nonnegative. -/
theorem xyPath_nonneg (s d u v : Fin k × Fin k) : 0 ≤ xyPath s d u v := by
  unfold xyPath
  have := seg_nonneg s.1 d.1 u.1 v.1
  have := seg_nonneg s.2 d.2 u.2 v.2
  split_ifs <;> linarith

/-- The YX path is nonnegative. -/
theorem yxPath_nonneg (s d u v : Fin k × Fin k) : 0 ≤ yxPath s d u v :=
  xyPath_nonneg s.swap d.swap u.swap v.swap

/-- The O1TURN path is nonnegative. -/
theorem o1Path_nonneg (s d u v : Fin k × Fin k) : 0 ≤ o1Path s d u v := by
  unfold o1Path; linarith [xyPath_nonneg s d u v, yxPath_nonneg s d u v]

/-- The XY path to `d` uses only steps towards `d`. -/
theorem xyPath_step {s d u v : Fin k × Fin k} (h : xyPath s d u v ≠ 0) : MeshStep u v d := by
  unfold xyPath at h
  by_cases h1 : u.2 = s.2 ∧ v.2 = s.2
  · by_cases hs : seg s.1 d.1 u.1 v.1 = 0
    · rw [ite_eq_left h1, hs, zero_add] at h
      by_cases h2 : u.1 = d.1 ∧ v.1 = d.1
      · rw [ite_eq_left h2] at h
        exact Or.inr ⟨h2.1.trans h2.2.symm, seg_step h⟩
      · exact absurd (ite_eq_right h2) h
    · exact Or.inl ⟨h1.1.trans h1.2.symm, seg_step hs⟩
  · rw [ite_eq_right h1, zero_add] at h
    by_cases h2 : u.1 = d.1 ∧ v.1 = d.1
    · rw [ite_eq_left h2] at h
      exact Or.inr ⟨h2.1.trans h2.2.symm, seg_step h⟩
    · exact absurd (ite_eq_right h2) h

/-- The YX path to `d` uses only steps towards `d`. -/
theorem yxPath_step {s d u v : Fin k × Fin k} (h : yxPath s d u v ≠ 0) : MeshStep u v d :=
  (xyPath_step (s := s.swap) (d := d.swap) (u := u.swap) (v := v.swap) h).symm

/-- The O1TURN path to `d` uses only steps towards `d`. -/
theorem o1Path_step {s d u v : Fin k × Fin k} (h : o1Path s d u v ≠ 0) : MeshStep u v d := by
  by_cases h1 : xyPath s d u v = 0
  · refine yxPath_step (s := s) fun h2 => h ?_
    unfold o1Path; rw [h1, h2]; norm_num
  · exact xyPath_step h1

/-- The flow of the traffic matrix `θ * T` along the paths `P`: commodity `d` carries
`θ * ∑ s, T s d * P s d u v` on the link `u → v`.  For the XY paths, this is in every row a
weighted line flow towards the column of `d` (weights `T (x, y) d`), followed by a weighted line
flow in the column of `d` (weights `∑ x, T (x, y) d`). -/
def routeFlow (P : Fin k × Fin k → Fin k × Fin k → Fin k × Fin k → Fin k × Fin k → ℚ)
    (T : Fin k × Fin k → Fin k × Fin k → ℚ) (θ : ℚ) (d u v : Fin k × Fin k) : ℚ :=
  θ * ∑ s, T s d * P s d u v

section route

variable {P : Fin k × Fin k → Fin k × Fin k → Fin k × Fin k → Fin k × Fin k → ℚ}
  {T : Fin k × Fin k → Fin k × Fin k → ℚ} {θ : ℚ}

/-- Conservation of a path flow: if every path sends `1` from `s` to `d`, the flow of commodity
`d` leaves every `v ≠ d` at `θ * T v d` more than it enters. -/
theorem routeFlow_conserve
    (hP : ∀ s d v, ∑ w, P s d v w - ∑ u, P s d u v =
      (if v = s then 1 else 0) - (if v = d then 1 else 0))
    (d v : Fin k × Fin k) (hv : v ≠ d) :
    ∑ w, routeFlow P T θ d v w - ∑ u, routeFlow P T θ d u v = θ * T v d := by
  unfold routeFlow
  rw [← mul_sum, ← mul_sum, ← mul_sub]
  congr 1
  rw [sum_comm, sum_comm (f := fun x s => T s d * P s d x v), ← sum_sub_distrib]
  calc ∑ s, (∑ w, T s d * P s d v w - ∑ u, T s d * P s d u v)
      = ∑ s, T s d * ((if v = s then 1 else 0) - (if v = d then 1 else 0)) :=
        sum_congr rfl fun s _ => by rw [← mul_sum, ← mul_sum, ← mul_sub, hP]
    _ = T v d := by simp [hv]

/-- A path flow of nonnegative paths and traffic is nonnegative. -/
theorem routeFlow_nonneg (hT : ∀ s d, 0 ≤ T s d) (hP : ∀ s d u v, 0 ≤ P s d u v) (hθ : 0 ≤ θ)
    (d u v : Fin k × Fin k) : 0 ≤ routeFlow P T θ d u v :=
  mul_nonneg hθ (sum_nonneg fun s _ => mul_nonneg (hT s d) (hP s d u v))

/-- A path flow along steps only is minimal: every link it uses brings its commodity strictly
closer to the destination. -/
theorem routeFlow_minimal (hP : ∀ s d u v, P s d u v ≠ 0 → MeshStep u v d)
    {d u v : Fin k × Fin k} (h : 0 < routeFlow P T θ d u v) :
    manhattan (gridPos v) (gridPos d) < manhattan (gridPos u) (gridPos d) := by
  by_contra hc
  have h0 : ∀ s, P s d u v = 0 := fun s => by
    by_contra hs; exact hc (hP s d u v hs).closer
  simp [routeFlow, h0] at h

/-- A path flow along steps uses only mesh links, so it respects the capacities of the mesh as soon
as its load on every mesh link is at most `2`. -/
theorem routeFlow_capacity (hP : ∀ s d u v, P s d u v ≠ 0 → MeshStep u v d)
    (hL : ∀ u v, MeshAdj u v → θ * ∑ d, ∑ s, T s d * P s d u v ≤ 2) (u v : Fin k × Fin k) :
    ∑ d, routeFlow P T θ d u v ≤ (meshNet k).cap u v := by
  unfold routeFlow
  rw [← mul_sum]
  show _ ≤ ite _ _ _
  by_cases h : MeshAdj u v
  · rw [ite_eq_left h]; exact hL u v h
  · rw [ite_eq_right h]
    have h0 : ∀ s d, P s d u v = 0 := fun s d => by
      by_contra hs; exact h (hP s d u v hs).adj
    simp [h0]

/-- **The load of an admissible matrix.**  If a path uses a link only when the source is in `p`
(weight `α`) or the destination is in `q` (weight `β`), the link carries at most
`α #p + β #q`: every source sends at most `1`, every destination receives at most `1`. -/
theorem Admissible.load_le (hT : Admissible T) (Q : Fin k × Fin k → Fin k × Fin k → ℚ)
    (p q : Fin k × Fin k → Prop) [DecidablePred p] [DecidablePred q] {α β : ℚ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hQ : ∀ s d, Q s d ≤ α * (if p s then 1 else 0) + β * (if q d then 1 else 0)) :
    ∑ d, ∑ s, T s d * Q s d ≤
      α * ∑ s, (if p s then 1 else 0) + β * ∑ d, (if q d then 1 else 0) := by
  calc ∑ d, ∑ s, T s d * Q s d
      ≤ ∑ d, ∑ s, (α * ((if p s then 1 else 0) * T s d) +
          β * ((if q d then 1 else 0) * T s d)) :=
        sum_le_sum fun d _ => sum_le_sum fun s _ => by
          have := mul_le_mul_of_nonneg_left (hQ s d) (hT.nonneg s d)
          linarith
    _ = α * ∑ s, (if p s then 1 else 0) * ∑ d, T s d +
          β * ∑ d, (if q d then 1 else 0) * ∑ s, T s d := by
        rw [sum_comm]
        simp only [sum_add_distrib, mul_sum]
        rw [sum_comm (f := fun s d => β * ((if q d then 1 else 0) * T s d))]
    _ ≤ α * ∑ s, (if p s then 1 else 0) + β * ∑ d, (if q d then 1 else 0) := by
        gcongr with s _ d _
        · split_ifs <;> simp [hT.row s]
        · split_ifs <;> simp [hT.col d]

end route

/-- On a row link `u → v`, the XY path is used only by sources in the row of `u` on `u`'s side. -/
theorem xyPath_le_row {s d u v : Fin k × Fin k} (hne : u.1 ≠ v.1) :
    xyPath s d u v ≤ if s.2 = u.2 ∧ Near u.1 v.1 s.1 then 1 else 0 := by
  unfold xyPath
  have h0 : (if u.1 = d.1 ∧ v.1 = d.1 then seg s.2 d.2 u.2 v.2 else 0) = 0 :=
    ite_eq_right (fun h => hne (h.1.trans h.2.symm))
  rw [h0, add_zero]
  by_cases h1 : u.2 = s.2 ∧ v.2 = s.2
  · rw [ite_eq_left h1]
    have := seg_le_near s.1 d.1 u.1 v.1
    by_cases hn : Near u.1 v.1 s.1
    · rw [ite_eq_left hn] at this; rwa [ite_eq_left ⟨h1.1.symm, hn⟩]
    · rw [ite_eq_right hn] at this; rwa [ite_eq_right (fun h => hn h.2)]
  · rw [ite_eq_right h1]; split_ifs <;> norm_num

/-- On a column link `u → v`, the XY path is used only by destinations in the column of `u` on
`v`'s side. -/
theorem xyPath_le_col {s d u v : Fin k × Fin k} (hne : u.2 ≠ v.2) :
    xyPath s d u v ≤ if d.1 = u.1 ∧ ¬ Near u.2 v.2 d.2 then 1 else 0 := by
  unfold xyPath
  have h0 : (if u.2 = s.2 ∧ v.2 = s.2 then seg s.1 d.1 u.1 v.1 else 0) = 0 :=
    ite_eq_right (fun h => hne (h.1.trans h.2.symm))
  rw [h0, zero_add]
  by_cases h1 : u.1 = d.1 ∧ v.1 = d.1
  · rw [ite_eq_left h1]
    have := seg_le_far s.2 d.2 u.2 v.2
    by_cases hn : ¬ Near u.2 v.2 d.2
    · rw [ite_eq_left hn] at this; rwa [ite_eq_left ⟨h1.1.symm, hn⟩]
    · rw [ite_eq_right hn] at this; rwa [ite_eq_right (fun h => hn h.2)]
  · rw [ite_eq_right h1]; split_ifs <;> norm_num

/-- On a row link `u → v`, the YX path is used only by destinations in the row of `u` on `v`'s
side. -/
theorem yxPath_le_row {s d u v : Fin k × Fin k} (hne : u.1 ≠ v.1) :
    yxPath s d u v ≤ if d.2 = u.2 ∧ ¬ Near u.1 v.1 d.1 then 1 else 0 :=
  xyPath_le_col (s := s.swap) (d := d.swap) (u := u.swap) (v := v.swap) hne

/-- On a column link `u → v`, the YX path is used only by sources in the column of `u` on `u`'s
side. -/
theorem yxPath_le_col {s d u v : Fin k × Fin k} (hne : u.2 ≠ v.2) :
    yxPath s d u v ≤ if s.1 = u.1 ∧ Near u.2 v.2 s.2 then 1 else 0 :=
  xyPath_le_row (s := s.swap) (d := d.swap) (u := u.swap) (v := v.swap) hne

/-- The positions satisfying `P` and those not satisfying it number `k` together. -/
theorem fin_count_compl (P : Fin k → Prop) [DecidablePred P] :
    ∑ x, (if P x then (1 : ℚ) else 0) + ∑ x, (if ¬ P x then (1 : ℚ) else 0) = k := by
  rw [← sum_add_distrib]
  rw [sum_congr rfl (g := fun _ => (1 : ℚ)) (fun x _ => by by_cases h : P x <;> simp [h])]
  simp

/-- If one position fails `P`, at most `k - 1` satisfy it. -/
theorem fin_count_le_of_not (P : Fin k → Prop) [DecidablePred P] (x₀ : Fin k) (h : ¬ P x₀) :
    ∑ x, (if P x then (1 : ℚ) else 0) ≤ k - 1 := by
  have e := fin_count_compl P
  have : (1 : ℚ) ≤ ∑ x, (if ¬ P x then (1 : ℚ) else 0) := by
    have := single_le_sum (f := fun x => if ¬ P x then (1 : ℚ) else 0)
      (fun x _ => by split_ifs <;> norm_num) (mem_univ x₀)
    rwa [ite_eq_left h] at this
  linarith

/-- If one position satisfies `P`, at most `k - 1` fail it. -/
theorem fin_count_not_le_of (P : Fin k → Prop) [DecidablePred P] (x₀ : Fin k) (h : P x₀) :
    ∑ x, (if ¬ P x then (1 : ℚ) else 0) ≤ k - 1 := by
  have e := fin_count_compl P
  have : (1 : ℚ) ≤ ∑ x, (if P x then (1 : ℚ) else 0) := by
    have := single_le_sum (f := fun x => if P x then (1 : ℚ) else 0)
      (fun x _ => by split_ifs <;> norm_num) (mem_univ x₀)
    rwa [ite_eq_left h] at this
  linarith

/-- Counting the grid vertices of one row by their column. -/
theorem grid_count_row (c : Fin k) (P : Fin k → Prop) [DecidablePred P] :
    ∑ s : Fin k × Fin k, (if s.2 = c ∧ P s.1 then (1 : ℚ) else 0) =
      ∑ x, if P x then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  by_cases h : P x <;> simp [h]

/-- Counting the grid vertices of one column by their row. -/
theorem grid_count_col (c : Fin k) (P : Fin k → Prop) [DecidablePred P] :
    ∑ s : Fin k × Fin k, (if s.1 = c ∧ P s.2 then (1 : ℚ) else 0) =
      ∑ y, if P y then 1 else 0 := by
  rw [Fintype.sum_prod_type, sum_eq_single c]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- The tail `a` of a link `a → b` is on its own side. -/
theorem near_self {a b : Fin k} (h : a ≠ b) : Near a b a := by
  have : (a : ℕ) ≠ b := fun e => h (Fin.ext e)
  unfold Near; omega

/-- The head `b` of a link `a → b` is not on `a`'s side. -/
theorem not_near_right (a b : Fin k) : ¬ Near a b b := by
  unfold Near; omega

/-- **The O1TURN load bound.**  On every mesh link, the O1TURN paths of an admissible matrix carry
at most `k / 2`: XY is limited by the sources on one side of the link, YX by the destinations on
the other side, and the two sides together hold the `k` positions of the line. -/
theorem o1_load {T : Fin k × Fin k → Fin k × Fin k → ℚ} (hT : Admissible T)
    {u v : Fin k × Fin k} (h : MeshAdj u v) :
    ∑ d, ∑ s, T s d * o1Path s d u v ≤ k / 2 := by
  rcases h with ⟨-, hl⟩ | ⟨-, hl⟩
  · have := hT.load_le (fun s d => o1Path s d u v) (fun s => s.2 = u.2 ∧ Near u.1 v.1 s.1)
      (fun d => d.2 = u.2 ∧ ¬ Near u.1 v.1 d.1) (α := 1 / 2) (β := 1 / 2) (by norm_num)
      (by norm_num) (fun s d => by
        unfold o1Path
        linarith [xyPath_le_row (s := s) (d := d) hl.ne,
          yxPath_le_row (s := s) (d := d) hl.ne])
    rw [grid_count_row u.2 (Near u.1 v.1), grid_count_row u.2 (fun x => ¬ Near u.1 v.1 x)] at this
    linarith [fin_count_compl (Near u.1 v.1)]
  · have := hT.load_le (fun s d => o1Path s d u v) (fun s => s.1 = u.1 ∧ Near u.2 v.2 s.2)
      (fun d => d.1 = u.1 ∧ ¬ Near u.2 v.2 d.2) (α := 1 / 2) (β := 1 / 2) (by norm_num)
      (by norm_num) (fun s d => by
        unfold o1Path
        linarith [xyPath_le_col (s := s) (d := d) hl.ne,
          yxPath_le_col (s := s) (d := d) hl.ne])
    rw [grid_count_col u.1 (Near u.2 v.2), grid_count_col u.1 (fun y => ¬ Near u.2 v.2 y)] at this
    linarith [fin_count_compl (Near u.2 v.2)]

/-- **The XY load bound.**  On every mesh link, the XY paths of an admissible matrix carry at most
`k - 1`: the sources on one side of a row link, or the destinations on one side of a column link. -/
theorem xy_load {T : Fin k × Fin k → Fin k × Fin k → ℚ} (hT : Admissible T)
    {u v : Fin k × Fin k} (h : MeshAdj u v) :
    ∑ d, ∑ s, T s d * xyPath s d u v ≤ k - 1 := by
  rcases h with ⟨-, hl⟩ | ⟨-, hl⟩
  · have := hT.load_le (fun s d => xyPath s d u v) (fun s => s.2 = u.2 ∧ Near u.1 v.1 s.1)
      (fun _ => False) (α := 1) (β := 0) (by norm_num) (by norm_num) (fun s d => by
        simpa using xyPath_le_row (s := s) (d := d) hl.ne)
    rw [grid_count_row u.2 (Near u.1 v.1)] at this
    linarith [fin_count_le_of_not (Near u.1 v.1) v.1 (not_near_right _ _)]
  · have := hT.load_le (fun s d => xyPath s d u v) (fun _ => False)
      (fun d => d.1 = u.1 ∧ ¬ Near u.2 v.2 d.2) (α := 0) (β := 1) (by norm_num) (by norm_num)
      (fun s d => by simpa using xyPath_le_col (s := s) (d := d) hl.ne)
    rw [grid_count_col u.1 (fun y => ¬ Near u.2 v.2 y)] at this
    linarith [fin_count_not_le_of (Near u.2 v.2) u.2 (near_self hl.ne)]

/-- **XY routing** of the traffic matrix `θ * T`. -/
def xyFlowT (k : ℕ) (T : Fin k × Fin k → Fin k × Fin k → ℚ) (θ : ℚ) :
    Fin k × Fin k → Fin k × Fin k → Fin k × Fin k → ℚ :=
  routeFlow xyPath T θ

/-- **YX routing** of the traffic matrix `θ * T`. -/
def yxFlowT (k : ℕ) (T : Fin k × Fin k → Fin k × Fin k → ℚ) (θ : ℚ) :
    Fin k × Fin k → Fin k × Fin k → Fin k × Fin k → ℚ :=
  routeFlow yxPath T θ

/-- **O1TURN routing** of the traffic matrix `θ * T`: half XY, half YX (`o1FlowT_eq`). -/
def o1FlowT (k : ℕ) (T : Fin k × Fin k → Fin k × Fin k → ℚ) (θ : ℚ) :
    Fin k × Fin k → Fin k × Fin k → Fin k × Fin k → ℚ :=
  routeFlow o1Path T θ

/-- O1TURN routing is the average of XY and YX routing. -/
theorem o1FlowT_eq (T : Fin k × Fin k → Fin k × Fin k → ℚ) (θ : ℚ) (d u v : Fin k × Fin k) :
    o1FlowT k T θ d u v = (xyFlowT k T θ d u v + yxFlowT k T θ d u v) / 2 := by
  unfold o1FlowT xyFlowT yxFlowT routeFlow o1Path
  have e : ∀ s, T s d * ((xyPath s d u v + yxPath s d u v) / 2) =
      (T s d * xyPath s d u v + T s d * yxPath s d u v) * (1 / 2) := fun s => by ring
  rw [sum_congr rfl fun s _ => e s, ← sum_mul, sum_add_distrib]
  ring

/-- **O1TURN routes every admissible matrix at throughput `4 / k`** in the `k × k` mesh. -/
def o1Routing {T : Fin k × Fin k → Fin k × Fin k → ℚ} (hT : Admissible T) :
    Flow (meshNet k) T (4 / k) where
  f := o1FlowT k T (4 / k)
  nonneg := routeFlow_nonneg hT.nonneg o1Path_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg k))
  conserve := routeFlow_conserve o1Path_conserve
  capacity := routeFlow_capacity (fun _ _ _ _ h => o1Path_step h) fun u v h => by
    have hk : (0 : ℚ) < k := by exact_mod_cast u.1.pos
    calc 4 / (k : ℚ) * ∑ d, ∑ s, T s d * o1Path s d u v ≤ 4 / k * (k / 2) :=
          mul_le_mul_of_nonneg_left (o1_load hT h) (div_nonneg (by norm_num) hk.le)
      _ = 2 := by rw [div_mul_div_comm, div_eq_iff (by positivity)]; ring

/-- O1TURN routing is minimal. -/
theorem o1Routing_minimal {T : Fin k × Fin k → Fin k × Fin k → ℚ} (hT : Admissible T) :
    (o1Routing hT).Minimal (fun u v => manhattan (gridPos u) (gridPos v)) :=
  fun _ _ _ h => routeFlow_minimal (fun _ _ _ _ h => o1Path_step h) h

/-- **Lower bound** (every `k`): every admissible traffic matrix is routable in the `k × k` mesh
at throughput `4 / k` by a minimal flow (O1TURN). -/
theorem o1turn_admissible (k : ℕ) (T : Fin k × Fin k → Fin k × Fin k → ℚ) (hT : Admissible T) :
    ∃ F : Flow (meshNet k) T (4 / k), F.Minimal (fun u v => manhattan (gridPos u) (gridPos v)) :=
  ⟨o1Routing hT, o1Routing_minimal hT⟩

/-- **XY routing of every admissible matrix at throughput `2 / (k - 1)`** in the `k × k` mesh. -/
def xyRoutingT {T : Fin k × Fin k → Fin k × Fin k → ℚ} (hT : Admissible T) :
    Flow (meshNet k) T (2 / ((k : ℚ) - 1)) where
  f := xyFlowT k T (2 / ((k : ℚ) - 1))
  nonneg d u v := by
    have hk : (1 : ℚ) ≤ k := by exact_mod_cast u.1.pos
    exact routeFlow_nonneg hT.nonneg xyPath_nonneg (div_nonneg (by norm_num) (by linarith)) d u v
  conserve := routeFlow_conserve xyPath_conserve
  capacity := routeFlow_capacity (fun _ _ _ _ h => xyPath_step h) fun u v h => by
    have hk : (1 : ℚ) ≤ k := by exact_mod_cast u.1.pos
    by_cases h1 : (k : ℚ) - 1 = 0
    · rw [h1, div_zero, zero_mul]; norm_num
    · calc 2 / ((k : ℚ) - 1) * ∑ d, ∑ s, T s d * xyPath s d u v ≤ 2 / ((k : ℚ) - 1) * (k - 1) :=
            mul_le_mul_of_nonneg_left (xy_load hT h) (div_nonneg (by norm_num) (by linarith))
        _ = 2 := div_mul_cancel₀ 2 h1

/-- XY routing is minimal. -/
theorem xyRoutingT_minimal {T : Fin k × Fin k → Fin k × Fin k → ℚ} (hT : Admissible T) :
    (xyRoutingT hT).Minimal (fun u v => manhattan (gridPos u) (gridPos v)) :=
  fun _ _ _ h => routeFlow_minimal (fun _ _ _ _ h => xyPath_step h) h

/-- Every admissible traffic matrix is routed by the minimal XY flow at throughput `2 / (k - 1)`. -/
theorem xy_admissible (k : ℕ) (T : Fin k × Fin k → Fin k × Fin k → ℚ) (hT : Admissible T) :
    ∃ F : Flow (meshNet k) T (2 / ((k : ℚ) - 1)), F.f = xyFlowT k T (2 / ((k : ℚ) - 1)) ∧
      F.Minimal (fun u v => manhattan (gridPos u) (gridPos v)) :=
  ⟨xyRoutingT hT, rfl, xyRoutingT_minimal hT⟩

/-- **Bit-complement** traffic: `(x, y)` sends rate `1` to `(k - 1 - x, k - 1 - y)`. -/
def bitcomp (k : ℕ) (s d : Fin k × Fin k) : ℚ := if d = (s.1.rev, s.2.rev) then 1 else 0

/-- Bit-complement is a permutation, hence admissible. -/
theorem bitcomp_admissible (k : ℕ) : Admissible (bitcomp k) where
  nonneg s d := by unfold bitcomp; split_ifs <;> norm_num
  row s := by simp [bitcomp]
  col d := by
    have e : ∀ s : Fin k × Fin k, (d = (s.1.rev, s.2.rev)) ↔ (s = (d.1.rev, d.2.rev)) := by
      intro s; constructor <;> rintro rfl <;> simp
    simp [bitcomp, e]

/-- The links leaving the left half (the first `m` columns, `k = 2m`) of the mesh have total
capacity `2 k`. -/
theorem mesh_half_cap (k m : ℕ) (hm : k = m + m) (hmk : m < k) :
    ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
      (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then (meshNet k).cap u v else 0) ≤ 2 * k := by
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

/-- **Upper bound** (even `k ≥ 2`, any routing): by the cut bound for the left half, whose
`k² / 2` vertices all send across the `k` links of capacity `2`, bit-complement is routable only
at `θ ≤ 4 / k`. -/
theorem bitcomp_upper (k : ℕ) (hk : 2 ≤ k) (he : Even k) {θ : ℚ}
    (h : Routable (meshNet k) (bitcomp k) θ) : θ ≤ 4 / k := by
  obtain ⟨m, hm⟩ := he
  have hmk : m < k := by omega
  have key := cut_bound h (fun u : Fin k × Fin k => 2 * (u.1 : ℕ) < k)
  have hA : ∑ s : Fin k × Fin k, (if 2 * (s.1 : ℕ) < k then (1 : ℚ) else 0) = k * m := by
    rw [sum_fst (fun i : Fin k => if 2 * (i : ℕ) < k then (1 : ℚ) else 0)]
    rw [Fin.sum_univ_eq_sum_range (fun i => if 2 * i < k then (1 : ℚ) else 0) k,
      sum_congr rfl (g := fun i => if i < m then (1 : ℚ) else 0)
        (fun i _ => by simp only [show 2 * i < k ↔ i < m by omega]),
      sum_range_lt k m hmk.le]
  have hL : ∑ s : Fin k × Fin k, ∑ d : Fin k × Fin k,
      (if 2 * (s.1 : ℕ) < k ∧ ¬ 2 * (d.1 : ℕ) < k then bitcomp k s d else 0) = k * m := by
    rw [← hA]
    refine sum_congr rfl fun s _ => ?_
    have e : ∀ d : Fin k × Fin k,
        (if 2 * (s.1 : ℕ) < k ∧ ¬ 2 * (d.1 : ℕ) < k then bitcomp k s d else 0) =
          if d = (s.1.rev, s.2.rev) then (if 2 * (s.1 : ℕ) < k then (1 : ℚ) else 0) else 0 := by
      intro d
      unfold bitcomp
      by_cases hd : d = (s.1.rev, s.2.rev)
      · subst hd
        have : (s.1.rev : ℕ) = k - (s.1 + 1) := Fin.val_rev s.1
        by_cases hs : 2 * (s.1 : ℕ) < k
        · rw [ite_eq_left ⟨hs, by simp only [this]; omega⟩]; simp [hs]
        · rw [ite_eq_right (fun h => hs h.1)]; simp [hs]
      · simp [hd]
    rw [sum_congr rfl fun d _ => e d, sum_ite_eq']
    simp
  have hR := mesh_half_cap k m hm hmk
  rw [hL] at key
  have hkm : (k : ℚ) = m + m := by exact_mod_cast hm
  have hm' : (0 : ℚ) < m := by
    have : (1 : ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    linarith
  have h1 : m * (θ * k) ≤ m * 4 := by
    have := key.trans hR
    rw [hkm] at this ⊢
    linarith
  have h2 := le_of_mul_le_mul_left h1 hm'
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Bit-complement's exact fluid throughput** in the `k × k` mesh (even `k ≥ 2`) is `4 / k`. -/
theorem bitcomp_opt (k : ℕ) (hk : 2 ≤ k) (he : Even k) :
    IsGreatest {θ : ℚ | Routable (meshNet k) (bitcomp k) θ} (4 / k) :=
  ⟨⟨o1Routing (bitcomp_admissible k)⟩, fun _ h => bitcomp_upper k hk he h⟩

/-- **Detours add nothing on bit-complement**: its optimum `4 / k` is reached by a minimal flow. -/
theorem bitcomp_minimal (k : ℕ) :
    ∃ F : Flow (meshNet k) (bitcomp k) (4 / k),
      F.Minimal (fun u v => manhattan (gridPos u) (gridPos v)) :=
  o1turn_admissible k (bitcomp k) (bitcomp_admissible k)

/-- **No routing has a better worst case than O1TURN** (even `k ≥ 2`): the largest throughput at
which every admissible traffic matrix is routable in the `k × k` mesh, by any routing (adaptive,
with detours), is `4 / k`, and O1TURN reaches it. -/
theorem worst_opt (k : ℕ) (hk : 2 ≤ k) (he : Even k) :
    IsGreatest {θ : ℚ | ∀ T, Admissible T → Routable (meshNet k) T θ} (4 / k) :=
  ⟨fun _ hT => ⟨o1Routing hT⟩, fun _ h => bitcomp_upper k hk he (h _ (bitcomp_admissible k))⟩

/-- An indicator true at most at one point sums to at most `1`. -/
theorem sum_indicator_le_one {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (h : ∀ x y, P x → P y → x = y) : ∑ x, (if P x then (1 : ℚ) else 0) ≤ 1 := by
  by_cases hx : ∃ x, P x
  · obtain ⟨x, hx⟩ := hx
    rw [sum_eq_single x (fun y _ hy => ite_eq_right (fun hp => hy (h y x hp hx))) (by simp),
      ite_eq_left hx]
  · rw [sum_eq_zero fun y _ => ite_eq_right (fun hp => hx ⟨y, hp⟩)]; norm_num

/-- A worst case for XY routing: the vertex `(i, 0)` of the bottom row sends rate `1` to
`(k - 1, i)` in the last column.  For `i < k - 1`, all these paths share the link
`(k - 2, 0) → (k - 1, 0)`. -/
def xyWorst (k : ℕ) (s d : Fin k × Fin k) : ℚ :=
  if (s.2 : ℕ) = 0 ∧ (d.1 : ℕ) = k - 1 ∧ d.2 = s.1 then 1 else 0

/-- The XY worst case is a partial permutation, hence admissible. -/
theorem xyWorst_admissible (k : ℕ) : Admissible (xyWorst k) where
  nonneg s d := by unfold xyWorst; split_ifs <;> norm_num
  row s := sum_indicator_le_one _ fun x y hx hy =>
    Prod.ext (Fin.ext (by omega)) (hx.2.2.trans hy.2.2.symm)
  col d := sum_indicator_le_one _ fun x y hx hy =>
    Prod.ext (hx.2.2.symm.trans hy.2.2) (Fin.ext (by omega))

/-- **XY's worst case** (`k ≥ 2`): if XY routing of `xyWorst k` at throughput `θ` respects the
capacities of the mesh, then `θ ≤ 2 / (k - 1)`: the link `(k - 2, 0) → (k - 1, 0)` carries the
`k - 1` sources `(i, 0)`, `i < k - 1`. -/
theorem xy_worst (k : ℕ) (hk : 2 ≤ k) {θ : ℚ}
    (h : ∀ u v, ∑ d, xyFlowT k (xyWorst k) θ d u v ≤ (meshNet k).cap u v) :
    θ ≤ 2 / ((k : ℚ) - 1) := by
  obtain ⟨a, ha⟩ : ∃ a : Fin k, (a : ℕ) = k - 2 := ⟨⟨k - 2, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin k, (b : ℕ) = k - 1 := ⟨⟨k - 1, by omega⟩, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : Fin k, (z : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  have hc := h (a, z) (b, z)
  have hcap : (meshNet k).cap (a, z) (b, z) = 2 := by
    have hadj : MeshAdj (a, z) (b, z) := Or.inl ⟨rfl, Or.inl (show (a : ℕ) + 1 = b by omega)⟩
    show ite _ _ _ = _
    rw [ite_eq_left hadj]
  have e1 : ∀ s d : Fin k × Fin k, xyWorst k s d * xyPath s d (a, z) (b, z) =
      if d = (b, s.1) then (if s.2 = z ∧ (s.1 : ℕ) < k - 1 then 1 else 0) else 0 := by
    intro s d
    by_cases hd : d = (b, s.1)
    · subst hd
      rw [ite_eq_left rfl]
      unfold xyWorst xyPath seg segN
      simp only [Fin.ext_iff, and_true]
      split_ifs <;> first | omega | norm_num
    · unfold xyWorst
      rw [ite_eq_right (fun h => hd (Prod.ext (Fin.ext (show (d.1 : ℕ) = b by omega)) h.2.2)),
        zero_mul,
        ite_eq_right hd]
  have hL : ∑ d, ∑ s, xyWorst k s d * xyPath s d (a, z) (b, z) = (k : ℚ) - 1 := by
    simp only [e1]
    rw [sum_comm]
    simp only [sum_ite_eq', mem_univ, ite_true]
    rw [grid_count_row z (fun x : Fin k => (x : ℕ) < k - 1),
      Fin.sum_univ_eq_sum_range (fun i => if i < k - 1 then (1 : ℚ) else 0) k,
      sum_range_lt k (k - 1) (by omega)]
    rw [Nat.cast_sub (by omega)]; norm_num
  unfold xyFlowT routeFlow at hc
  rw [← mul_sum, hL, hcap] at hc
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  rw [le_div_iff₀ (by linarith)]
  exact hc

/-- **XY's exact worst-case throughput** (`k ≥ 2`): the largest `θ` at which XY routing of every
admissible matrix respects the capacities of the mesh is `2 / (k - 1)`. -/
theorem xy_worst_opt (k : ℕ) (hk : 2 ≤ k) :
    IsGreatest {θ : ℚ | ∀ T, Admissible T →
      ∀ u v, ∑ d, xyFlowT k T θ d u v ≤ (meshNet k).cap u v} (2 / ((k : ℚ) - 1)) :=
  ⟨fun _ hT => (xyRoutingT hT).capacity, fun _ h => xy_worst k hk (h _ (xyWorst_admissible k))⟩

/-- O1TURN's worst case is `2 (k - 1) / k` times XY's, never below it (`k ≥ 2`). -/
theorem o1turn_xy_ratio (k : ℕ) (hk : 2 ≤ k) :
    4 / (k : ℚ) = 2 * ((k : ℚ) - 1) / k * (2 / ((k : ℚ) - 1)) ∧ 2 / ((k : ℚ) - 1) ≤ 4 / k := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  constructor
  · rw [div_mul_div_comm, eq_div_iff (by
      have : (0 : ℚ) < k * (k - 1) := mul_pos (by linarith) (by linarith)
      exact this.ne')]
    have : (k : ℚ) - 1 ≠ 0 := by linarith
    rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]
    ring
  · rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith

/-- The `8 × 8` mesh: the best worst-case throughput of any routing is `1/2` (O1TURN). -/
theorem worst_opt_eight :
    IsGreatest {θ : ℚ | ∀ T, Admissible T → Routable (meshNet 8) T θ} (1 / 2) := by
  have := worst_opt 8 (by norm_num) ⟨4, rfl⟩
  rwa [show (4 : ℚ) / ((8 : ℕ) : ℚ) = 1 / 2 by norm_num] at this

/-- The `8 × 8` mesh: XY's worst-case throughput is `2/7`. -/
theorem xy_worst_opt_eight :
    IsGreatest {θ : ℚ | ∀ T, Admissible T →
      ∀ u v, ∑ d, xyFlowT 8 T θ d u v ≤ (meshNet 8).cap u v} (2 / 7) := by
  have := xy_worst_opt 8 (by norm_num)
  rwa [show (2 : ℚ) / (((8 : ℕ) : ℚ) - 1) = 2 / 7 by norm_num] at this

end Fluid

end AsyncLean
