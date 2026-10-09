/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.MeshWire

/-!
# Checkable certificates for the fluid throughput of the `k × k` mesh

The exact fluid optimum of a traffic pattern on the mesh is a linear program; its value is
certified by a primal flow (a lower bound) and a dual potential (an upper bound).  This file turns
both into Boolean checkers over natural numbers that the kernel evaluates (`decide +kernel`), and
proves them sound.

Vertex `v = (x, y)` of the `k × k` grid has the index `idx v = x + k * y` (the simulator's
numbering), and port `i` of a vertex is the link to its neighbour `nb v i`: `0` east (`x + 1`),
`1` west (`x - 1`), `2` north (`y + 1`), `3` south (`y - 1`).  At the level of indices the port
exists if `valid k j i` and leads to `step k j i` (`j ± 1`, `j ± k`).

* `certFlow` : **primal certificate.**  A table `g d j i : ℕ` (the rate of commodity `d` leaving
  vertex `j` through port `i`, scaled by `D`) passing `consCheck` (conservation at every vertex
  other than the destination, against the scaled demand `demN`) and `capCheck` (every link carries
  at most `2 D`) is a flow of `θ * dem` with `θ = p / q` in `meshNet k`; with `minCheck`
  (every used port brings the commodity closer to its destination) it is minimal
  (`certFlow_minimal`).
* `upper_of_check` : **dual certificate.**  Link lengths `lenT j i : ℕ` and potentials
  `phi d j : ℕ` passing `dualCheck` (`phi d d = 0`, and `phi` drops by at most the length along
  every link, or every minimal link when `minimal`) and `boundCheck`
  (`2 ∑ len * R * q ≤ p * ∑ demN * phi`) bound every flow by `θ ≤ p / q` (every minimal flow when
  `minimal`), by `Fluid.Flow.potential_bound_on`.

The checkers loop with `allBelow` and `sumBelow` (plain recursion on `ℕ`) and use only `ℕ`
arithmetic, which the kernel evaluates with GMP.
-/

namespace AsyncLean

namespace Fluid

namespace MeshCert

open Finset

/-! ### Loops over natural numbers -/

/-- `allBelow n p`: `p j` holds for every `j < n`. -/
def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allBelow n p && p n

/-- `sumBelow n G = ∑ j < n, G j`. -/
def sumBelow : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, G => sumBelow n G + G n

/-- The `n`-th element of a list of naturals, `0` past its end. -/
def getN : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, n + 1 => getN l n

/-- Digit `j` of `x` in base `2 ^ b`. -/
def digit (b x j : ℕ) : ℕ := (x >>> (b * j)) % 2 ^ b

/-- `allBelow` checks a bounded universal statement. -/
theorem allBelow_iff {n : ℕ} {p : ℕ → Bool} : allBelow n p = true ↔ ∀ j < n, p j = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_or_ge j n with hj' | hj'
      · exact h1 j hj'
      · obtain rfl : j = n := by omega
        exact h2
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩

/-- `sumBelow` is a finite sum. -/
theorem sumBelow_eq (n : ℕ) (G : ℕ → ℕ) : sumBelow n G = ∑ j ∈ range n, G j := by
  induction n with
  | zero => simp [sumBelow]
  | succ n ih => rw [sumBelow, ih, sum_range_succ]

/-- Dividing a sum. -/
theorem sum_div_q {ι : Type*} (s : Finset ι) (f : ι → ℚ) (c : ℚ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp only [div_eq_mul_inv, sum_mul]

variable {k : ℕ}

/-! ### Indices -/

/-- The index `x + k * y` of the vertex `(x, y)`. -/
def idx (v : Fin k × Fin k) : ℕ := (v.1 : ℕ) + k * (v.2 : ℕ)

/-- The `x` coordinate is the index mod `k`. -/
theorem idx_mod (v : Fin k × Fin k) : idx v % k = v.1 := by
  unfold idx; rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt v.1.isLt

/-- The `y` coordinate is the index divided by `k`. -/
theorem idx_div (v : Fin k × Fin k) : idx v / k = v.2 := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) v.1.isLt
  unfold idx
  rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt v.1.isLt, zero_add]

/-- Indices are below `k * k`. -/
theorem idx_lt (v : Fin k × Fin k) : idx v < k * k := by
  have h1 := v.1.isLt
  have h2 := v.2.isLt
  unfold idx
  calc (v.1 : ℕ) + k * v.2 < k + k * v.2 := by omega
    _ = k * (v.2 + 1) := by ring
    _ ≤ k * k := Nat.mul_le_mul_left _ h2

/-- Distinct vertices have distinct indices. -/
theorem idx_inj {u v : Fin k × Fin k} (h : idx u = idx v) : u = v := by
  have h1 := idx_mod u
  have h2 := idx_div u
  rw [h, idx_mod] at h1
  rw [h, idx_div] at h2
  exact Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm)

/-- A sum over the vertices is a sum over their indices `< k * k`. -/
theorem sum_idx {M : Type*} [AddCommMonoid M] (G : ℕ → M) :
    ∑ v : Fin k × Fin k, G (idx v) = ∑ j ∈ range (k * k), G j := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv ((Equiv.prodComm _ _).trans finProdFinEquiv) _ _ fun v => by
    simp [idx, finProdFinEquiv_apply_val]

/-! ### Ports -/

/-- Port `i` exists at the vertex of index `j`: `0` east, `1` west, `2` north, `3` south. -/
def valid (k j : ℕ) : ℕ → Bool
  | 0 => decide (j % k + 1 < k)
  | 1 => decide (0 < j % k)
  | 2 => decide (j / k + 1 < k)
  | _ => decide (0 < j / k)

/-- The index of the neighbour through port `i` of the vertex of index `j`. -/
def step (k j : ℕ) : ℕ → ℕ
  | 0 => j + 1
  | 1 => j - 1
  | 2 => j + k
  | _ => j - k

/-- The opposite port. -/
def opp : Fin 4 → Fin 4
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 3
  | ⟨_ + 3, _⟩ => 2

/-- The neighbour of `u` through port `i`, if any. -/
def nb (u : Fin k × Fin k) (i : Fin 4) : Option (Fin k × Fin k) :=
  match i with
  | ⟨0, _⟩ => if h : (u.1 : ℕ) + 1 < k then some (⟨u.1 + 1, h⟩, u.2) else none
  | ⟨1, _⟩ => if h : 0 < (u.1 : ℕ) then some (⟨u.1 - 1, by omega⟩, u.2) else none
  | ⟨2, _⟩ => if h : (u.2 : ℕ) + 1 < k then some (u.1, ⟨u.2 + 1, h⟩) else none
  | ⟨_ + 3, _⟩ => if h : 0 < (u.2 : ℕ) then some (u.1, ⟨u.2 - 1, by omega⟩) else none

/-- Port `i` of `u` exists iff `valid` says so. -/
theorem nb_isSome (u : Fin k × Fin k) (i : Fin 4) :
    (nb u i).isSome = valid k (idx u) i := by
  rcases u with ⟨a, b⟩
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals simp only [nb, valid, idx_mod, idx_div]; split_ifs <;> simp_all

/-- The neighbour through port `i` has the index `step k (idx u) i`. -/
theorem idx_nb {u v : Fin k × Fin k} {i : Fin 4} (h : nb u i = some v) :
    idx v = step k (idx u) i := by
  rcases u with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals simp only [nb] at h; split_ifs at h with hc; cases h; simp only [idx, step]
  · ring
  · omega
  · ring
  · rw [Nat.mul_sub, Nat.mul_one]
    have : k ≤ k * b := Nat.le_mul_of_pos_right k hc
    omega

/-- `v` is the neighbour of `u` through port `i` iff `u` is the neighbour of `v` through the
opposite port. -/
theorem nb_symm {u v : Fin k × Fin k} {i : Fin 4} : nb u i = some v ↔ nb v (opp i) = some u := by
  rcases u with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rcases v with ⟨⟨c, hc⟩, ⟨e, he⟩⟩
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals simp only [nb, opp]; simp; constructor <;> intro h <;> omega

/-- Distinct ports lead to distinct neighbours. -/
theorem nb_inj {u v : Fin k × Fin k} {i i' : Fin 4} (h : nb u i = some v)
    (h' : nb u i' = some v) : i = i' := by
  rcases u with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rcases v with ⟨⟨c, hc⟩, ⟨e, he⟩⟩
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> rcases i' with ⟨_ | _ | _ | _ | n', hi'⟩ <;>
    try omega
  all_goals simp only [nb] at h h'; split_ifs at h h'; simp [Prod.ext_iff] at h h'; omega

/-- Port neighbours are mesh neighbours. -/
theorem adj_of_nb {u v : Fin k × Fin k} {i : Fin 4} (h : nb u i = some v) : MeshAdj u v := by
  rcases u with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rcases v with ⟨⟨c, hc⟩, ⟨e, he⟩⟩
  unfold MeshAdj LineAdj
  simp only [Fin.ext_iff]
  rcases i with ⟨_ | _ | _ | _ | n, hi⟩ <;> try omega
  all_goals simp only [nb] at h; split_ifs at h; simp [Prod.ext_iff] at h; omega

/-- Every mesh neighbour is reached through a port. -/
theorem nb_of_adj {u v : Fin k × Fin k} (h : MeshAdj u v) : ∃ i, nb u i = some v := by
  rcases u with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rcases v with ⟨⟨c, hc⟩, ⟨e, he⟩⟩
  unfold MeshAdj LineAdj at h
  simp only [Fin.ext_iff] at h
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · have h0 : a + 1 < k := by omega
    exact ⟨0, by simp [nb, h0, Prod.ext_iff]; omega⟩
  · have h0 : 0 < a := by omega
    exact ⟨1, by simp [nb, h0, Prod.ext_iff]; omega⟩
  · have h0 : b + 1 < k := by omega
    exact ⟨2, by simp [nb, h0, Prod.ext_iff]; omega⟩
  · have h0 : 0 < b := by omega
    exact ⟨3, by simp [nb, h0, Prod.ext_iff]; omega⟩

/-- Every port is a link of capacity `2`. -/
theorem cap_nb {u v : Fin k × Fin k} {i : Fin 4} (h : nb u i = some v) :
    (meshNet k).cap u v = 2 := by
  show ite _ _ _ = _
  simp [adj_of_nb h]

/-- Summing a port-indexed quantity over the targets. -/
theorem sum_some {α : Type*} [Fintype α] [DecidableEq α] (o : Option α) (c : ℚ) :
    ∑ w, (if o = some w then c else 0) = if o.isSome then c else 0 := by
  cases o <;> simp

/-- The value at the end of port `i`, as a function of the index. -/
theorem elim_nb (u : Fin k × Fin k) (i : Fin 4) (H : ℕ → ℚ) :
    (∑ w, if nb u i = some w then H (idx w) else 0) =
      if valid k (idx u) i then H (step k (idx u) i) else 0 := by
  rw [← nb_isSome]
  cases h : nb u i with
  | none => simp
  | some w => simp [idx_nb h]

/-- Summing over the sources of the links into `v` through port `i`. -/
theorem sum_in_port (v : Fin k × Fin k) (i : Fin 4) (H : ℕ → ℚ) :
    (∑ u, if nb u i = some v then H (idx u) else 0) =
      if valid k (idx v) (opp i) then H (step k (idx v) (opp i)) else 0 := by
  rw [← elim_nb]
  refine sum_congr rfl fun u _ => ?_
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (nb_symm.1 h1) h2
  · exact absurd (nb_symm.2 h2) h1
  · rfl

/-- `sum_in_port` for a port table. -/
theorem sum_in_table (v : Fin k × Fin k) (i : Fin 4) (T : ℕ → ℕ → ℕ) (D : ℕ) :
    (∑ u, if nb u i = some v then (T (idx u) i : ℚ) / D else 0) =
      if valid k (idx v) (opp i) then (T (step k (idx v) (opp i)) i : ℚ) / D else 0 :=
  sum_in_port v i fun j => (T j i : ℚ) / D

/-! ### Port tables -/

/-- The rate a port table puts on the link `u → v`: `T (idx u) i` if `u → v` is port `i`. -/
def portVal (T : ℕ → ℕ → ℕ) (D : ℕ) (u v : Fin k × Fin k) : ℚ :=
  ∑ i : Fin 4, if nb u i = some v then (T (idx u) i : ℚ) / D else 0

/-- The total over the existing ports of the vertex of index `j`. -/
def outN (k : ℕ) (T : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  (if valid k j 0 then T j 0 else 0) + (if valid k j 1 then T j 1 else 0) +
    (if valid k j 2 then T j 2 else 0) + (if valid k j 3 then T j 3 else 0)

/-- The total over the links into the vertex of index `j`. -/
def inN (k : ℕ) (T : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  (if valid k j 1 then T (j - 1) 0 else 0) + (if valid k j 0 then T (j + 1) 1 else 0) +
    (if valid k j 3 then T (j - k) 2 else 0) + (if valid k j 2 then T (j + k) 3 else 0)

/-- Port tables are nonnegative. -/
theorem portVal_nonneg (T : ℕ → ℕ → ℕ) (D : ℕ) (u v : Fin k × Fin k) : 0 ≤ portVal T D u v :=
  sum_nonneg fun _ _ => by
    split_ifs
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact le_refl 0

/-- The rate leaving `u` is the total over its existing ports. -/
theorem sum_portVal_out (T : ℕ → ℕ → ℕ) (D : ℕ) (u : Fin k × Fin k) :
    ∑ v, portVal T D u v = (outN k T (idx u) : ℚ) / D := by
  unfold portVal
  rw [sum_comm]
  simp only [sum_some, nb_isSome, Fin.sum_univ_four, outN]
  push_cast
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [h3]
  split_ifs <;> ring

/-- The rate entering `v` is the total over the ports of its neighbours that point at `v`. -/
theorem sum_portVal_in (T : ℕ → ℕ → ℕ) (D : ℕ) (v : Fin k × Fin k) :
    ∑ u, portVal T D u v = (inN k T (idx v) : ℚ) / D := by
  unfold portVal
  rw [sum_comm]
  simp only [sum_in_table, Fin.sum_univ_four, inN]
  have e0 : opp 0 = 1 := rfl
  have e1 : opp 1 = 0 := rfl
  have e2 : opp 2 = 3 := rfl
  have e3 : opp 3 = 2 := rfl
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  simp only [e0, e1, e2, e3, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, h3, step]
  push_cast
  split_ifs <;> ring

/-- With at most one port per link, the rate on a link is that of its port. -/
theorem portVal_eq {T : ℕ → ℕ → ℕ} {D : ℕ} {u v : Fin k × Fin k} {i : Fin 4}
    (h : nb u i = some v) : portVal T D u v = (T (idx u) i : ℚ) / D := by
  unfold portVal
  rw [sum_eq_single i (fun i' _ hi' => ite_eq_right fun h' => hi' (nb_inj h' h)) (by simp), ite_eq_left h]

/-! ### The Manhattan distance on indices -/

/-- The Manhattan distance of the vertices of indices `a` and `b`. -/
def ndist (k a b : ℕ) : ℕ :=
  (a % k - b % k) + (b % k - a % k) + ((a / k - b / k) + (b / k - a / k))

/-- The Manhattan distance of two vertices of the grid. -/
def mdist (u v : Fin k × Fin k) : ℚ := manhattan (gridPos u) (gridPos v)

/-- `|a - b|` for naturals, without subtraction in `ℚ`. -/
theorem abs_natCast_sub (a b : ℕ) : |(a : ℚ) - b| = ((a - b : ℕ) : ℚ) + ((b - a : ℕ) : ℚ) := by
  have hc : ∀ {x y : ℕ}, x ≤ y → (x : ℚ) ≤ y := fun h => Nat.cast_le.2 h
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h, abs_of_nonpos (by linarith [hc h])]
    push_cast; ring
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h, abs_of_nonneg (by linarith [hc h])]
    push_cast; ring

/-- The Manhattan distance of two vertices is `ndist` of their indices. -/
theorem mdist_eq (u v : Fin k × Fin k) : mdist u v = ndist k (idx u) (idx v) := by
  unfold mdist manhattan gridPos ndist
  rw [idx_mod, idx_mod, idx_div, idx_div]
  push_cast
  rw [abs_natCast_sub, abs_natCast_sub]

/-! ### The primal certificate -/

/-- Conservation of every commodity `d` at every vertex `j ≠ d`, with throughput `p / q` and the
demand `demN j d / R`, for the port table `g d j i / D`. -/
def consCheck (k : ℕ) (g : ℕ → ℕ → ℕ → ℕ) (D : ℕ) (demN : ℕ → ℕ → ℕ) (R p q : ℕ) : Bool :=
  allBelow (k * k) fun d => allBelow (k * k) fun j =>
    j == d || q * R * outN k (g d) j == q * R * inN k (g d) j + p * D * demN j d

/-- Every port carries at most `2 D` in total over the commodities. -/
def capCheck (k : ℕ) (g : ℕ → ℕ → ℕ → ℕ) (D : ℕ) : Bool :=
  allBelow (k * k) fun j => allBelow 4 fun i => decide (sumBelow (k * k) (fun d => g d j i) ≤ 2 * D)

/-- Every used port brings its commodity strictly closer to its destination. -/
def minCheck (k : ℕ) (g : ℕ → ℕ → ℕ → ℕ) : Bool :=
  allBelow (k * k) fun d => allBelow (k * k) fun j => allBelow 4 fun i =>
    !(valid k j i) || g d j i == 0 || decide (ndist k (step k j i) d < ndist k j d)

/-- The rate of commodity `d` on the link `u → v` given by the port table `g / D`. -/
def certRate (g : ℕ → ℕ → ℕ → ℕ) (D : ℕ) (d u v : Fin k × Fin k) : ℚ :=
  portVal (g (idx d)) D u v

/-- **The primal certificate.**  A port table passing `consCheck` and `capCheck` is a flow of
`θ * dem` in the mesh, for `θ = p / q` and `dem s d = demN (idx s) (idx d) / R`. -/
def certFlow (dem : Fin k × Fin k → Fin k × Fin k → ℚ) (demN : ℕ → ℕ → ℕ) (R : ℕ)
    (hdem : ∀ s d, dem s d = (demN (idx s) (idx d) : ℚ) / R) (g : ℕ → ℕ → ℕ → ℕ) (D p q : ℕ)
    {θ : ℚ} (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D) (hq : 0 < q)
    (hc : consCheck k g D demN R p q = true) (hcap : capCheck k g D = true) :
    Flow (meshNet k) dem θ where
  f := certRate g D
  nonneg d u v := portVal_nonneg _ _ _ _
  conserve d v hv := by
    simp only [certRate]
    rw [sum_portVal_out, sum_portVal_in, hdem, hθ]
    have := allBelow_iff.1 (allBelow_iff.1 hc (idx d) (idx_lt d)) (idx v) (idx_lt v)
    have hne : idx v ≠ idx d := fun h => hv (idx_inj h)
    simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or] at this
    have hQ : ((q * R * outN k (g (idx d)) (idx v) : ℕ) : ℚ) =
        ((q * R * inN k (g (idx d)) (idx v) + p * D * demN (idx v) (idx d) : ℕ) : ℚ) := by
      rw [this]
    push_cast at hQ
    have hR' : (0 : ℚ) < R := by exact_mod_cast hR
    have hD' : (0 : ℚ) < D := by exact_mod_cast hD
    have hq' : (0 : ℚ) < q := by exact_mod_cast hq
    have hdiff : (outN k (g (idx d)) (idx v) : ℚ) - inN k (g (idx d)) (idx v) =
        p * D * demN (idx v) (idx d) / (q * R) := by
      rw [eq_div_iff (mul_pos hq' hR').ne']; linarith
    rw [div_sub_div_same, hdiff, div_eq_iff hD'.ne']
    ring
  capacity u v := by
    simp only [certRate, portVal]
    rw [sum_comm]
    by_cases hex : ∃ i, nb u i = some v
    · obtain ⟨i, hi⟩ := hex
      rw [sum_eq_single i (fun i' _ hi' => sum_eq_zero fun d _ =>
        ite_eq_right fun h' => hi' (nb_inj h' hi)) (by simp), cap_nb hi]
      simp only [hi, ↓reduceIte]
      rw [← sum_div_q, sum_idx (fun j => ((g j (idx u) i : ℕ) : ℚ)), ← Nat.cast_sum,
        ← sumBelow_eq]
      have := allBelow_iff.1 (allBelow_iff.1 hcap (idx u) (idx_lt u)) i i.isLt
      simp only [decide_eq_true_eq] at this
      have hD' : (0 : ℚ) < D := by exact_mod_cast hD
      rw [div_le_iff₀ hD']
      exact_mod_cast this
    · simp only [not_exists] at hex
      simp only [hex, ↓reduceIte, sum_const_zero]
      exact (meshNet k).cap_nonneg u v

/-- **The primal certificate is minimal** when it passes `minCheck`. -/
theorem certFlow_minimal (dem : Fin k × Fin k → Fin k × Fin k → ℚ) (demN : ℕ → ℕ → ℕ) (R : ℕ)
    (hdem : ∀ s d, dem s d = (demN (idx s) (idx d) : ℚ) / R) (g : ℕ → ℕ → ℕ → ℕ) (D p q : ℕ)
    {θ : ℚ} (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D) (hq : 0 < q)
    (hc : consCheck k g D demN R p q = true) (hcap : capCheck k g D = true)
    (hm : minCheck k g = true) :
    (certFlow dem demN R hdem g D p q hθ hR hD hq hc hcap).Minimal mdist := by
  intro d u v hpos
  change 0 < portVal (g (idx d)) D u v at hpos
  by_cases hex : ∃ i, nb u i = some v
  · obtain ⟨i, hi⟩ := hex
    rw [portVal_eq hi] at hpos
    have hg : g (idx d) (idx u) i ≠ 0 := by
      intro h0; rw [h0] at hpos; simp at hpos
    have := allBelow_iff.1 (allBelow_iff.1 (allBelow_iff.1 hm (idx d) (idx_lt d)) (idx u)
      (idx_lt u)) i i.isLt
    have hval : valid k (idx u) i = true := by rw [← nb_isSome, hi]; rfl
    simp only [hval, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, hg,
      false_or, decide_eq_true_eq] at this
    rw [mdist_eq, mdist_eq, idx_nb hi]
    exact_mod_cast this
  · simp only [not_exists] at hex
    have : portVal (g (idx d)) D u v = 0 := sum_eq_zero fun i _ => ite_eq_right (hex i)
    rw [this] at hpos
    exact absurd hpos (lt_irrefl 0)

/-! ### The dual certificate -/

/-- The potentials `phi d j` vanish at the destination and drop by at most `lenT j i` along every
port `i` (every port that brings `d` closer, when `minimal`). -/
def dualCheck (k : ℕ) (phi lenT : ℕ → ℕ → ℕ) (minimal : Bool) : Bool :=
  allBelow (k * k) (fun d => phi d d == 0) &&
  allBelow (k * k) fun d => allBelow (k * k) fun j => allBelow 4 fun i =>
    !(valid k j i) || (minimal && !decide (ndist k (step k j i) d < ndist k j d)) ||
      decide (phi d j ≤ phi d (step k j i) + lenT j i)

/-- `∑ cap * len / 2`: the total length of the links. -/
def lenSum (k : ℕ) (lenT : ℕ → ℕ → ℕ) : ℕ := sumBelow (k * k) (outN k lenT)

/-- `R * ∑ dem * phi`. -/
def demPhi (k : ℕ) (demN phi : ℕ → ℕ → ℕ) : ℕ :=
  sumBelow (k * k) fun s => sumBelow (k * k) fun d => demN s d * phi d s

/-- The bound `2 * lenSum * R / demPhi ≤ p / q`. -/
def boundCheck (k : ℕ) (demN phi lenT : ℕ → ℕ → ℕ) (R p q : ℕ) : Bool :=
  decide (0 < demPhi k demN phi) && decide (2 * lenSum k lenT * R * q ≤ p * demPhi k demN phi)

/-- **The dual certificate.**  If `dualCheck` and `boundCheck` pass, every flow of `θ * dem` in
the mesh (every minimal one, when `minimal`) has `θ ≤ p / q`. -/
theorem upper_of_check (dem : Fin k × Fin k → Fin k × Fin k → ℚ) (demN : ℕ → ℕ → ℕ) (R : ℕ)
    (hdem : ∀ s d, dem s d = (demN (idx s) (idx d) : ℚ) / R) (phi lenT : ℕ → ℕ → ℕ)
    (minimal : Bool) (p q : ℕ) (hR : 0 < R) (hq : 0 < q)
    (hd : dualCheck k phi lenT minimal = true) (hb : boundCheck k demN phi lenT R p q = true)
    {θ : ℚ} (F : Flow (meshNet k) dem θ) (hF : minimal = true → F.Minimal mdist) :
    θ ≤ (p : ℚ) / q := by
  simp only [dualCheck, Bool.and_eq_true] at hd
  obtain ⟨hd0, hd1⟩ := hd
  simp only [boundCheck, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hA, hCA⟩ := hb
  have hsupp : F.SupportedOn fun d u v => minimal = false ∨ mdist v d < mdist u d := by
    intro d u v h
    cases minimal with
    | false => exact Or.inl rfl
    | true => exact Or.inr (hF rfl d u v h)
  have key := F.potential_bound_on hsupp (portVal lenT 1) (portVal_nonneg _ _)
    (fun d v => (phi (idx d) (idx v) : ℚ))
    (fun d => by
      have := allBelow_iff.1 hd0 (idx d) (idx_lt d)
      simp only [beq_iff_eq] at this
      simp [this])
    (fun d u v hS hcap => by
      have hadj : MeshAdj u v := by
        by_contra hn
        exact absurd hcap (by show ¬ 0 < ite _ _ _; rw [ite_eq_right hn]; exact lt_irrefl 0)
      obtain ⟨i, hi⟩ := nb_of_adj hadj
      rw [portVal_eq hi, Nat.cast_one, div_one]
      have := allBelow_iff.1 (allBelow_iff.1 (allBelow_iff.1 hd1 (idx d) (idx_lt d)) (idx u)
        (idx_lt u)) i i.isLt
      have hval : valid k (idx u) i = true := by rw [← nb_isSome, hi]; rfl
      have hcl : ¬ (minimal = true ∧ ¬ ndist k (step k (idx u) i) (idx d) < ndist k (idx u) (idx d))
          := by
        rintro ⟨hm, hn⟩
        rcases hS with h | h
        · rw [hm] at h; exact Bool.noConfusion h
        · rw [mdist_eq, mdist_eq, idx_nb hi] at h
          exact hn (by exact_mod_cast h)
      simp only [hval, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at this
      rw [← idx_nb hi] at this
      rcases this with h | h
      · exact absurd ⟨h.1, by rw [← idx_nb hi]; exact h.2⟩ hcl
      · have : ((phi (idx d) (idx u) : ℕ) : ℚ) ≤ ((phi (idx d) (idx v) + lenT (idx u) i : ℕ) : ℚ)
          := by exact_mod_cast h
        push_cast at this
        linarith)
  -- evaluate the two sides
  have hL : ∑ s, ∑ d, dem s d * (phi (idx d) (idx s) : ℚ) = (demPhi k demN phi : ℚ) / R := by
    simp only [hdem, demPhi, sumBelow_eq]
    push_cast
    rw [sum_div_q]
    rw [sum_idx (fun j => ∑ d : Fin k × Fin k,
      (demN j (idx d) : ℚ) / R * (phi (idx d) j : ℚ))]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_idx (fun e => (demN j e : ℚ) / R * (phi e j : ℚ)), sum_div_q]
    exact sum_congr rfl fun _ _ => by ring
  have hC : ∑ u, ∑ v, (meshNet k).cap u v * portVal lenT 1 u v = 2 * (lenSum k lenT : ℚ) := by
    have : ∀ u v : Fin k × Fin k, (meshNet k).cap u v * portVal lenT 1 u v =
        2 * portVal lenT 1 u v := by
      intro u v
      by_cases hex : ∃ i, nb u i = some v
      · obtain ⟨i, hi⟩ := hex; rw [cap_nb hi]
      · simp only [not_exists] at hex
        have : portVal lenT 1 u v = 0 := sum_eq_zero fun i _ => ite_eq_right (hex i)
        rw [this]; ring
    simp only [this, ← mul_sum, sum_portVal_out, Nat.cast_one, div_one, lenSum, sumBelow_eq]
    push_cast
    rw [sum_idx (fun j => (outN k lenT j : ℚ))]
  rw [hL, hC] at key
  have hR' : (0 : ℚ) < R := by exact_mod_cast hR
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hA' : (0 : ℚ) < demPhi k demN phi := by exact_mod_cast hA
  have hCA' : 2 * (lenSum k lenT : ℚ) * R * q ≤ p * demPhi k demN phi := by exact_mod_cast hCA
  rw [le_div_iff₀ hq']
  have h1 : θ * demPhi k demN phi ≤ 2 * lenSum k lenT * R := by
    have := mul_le_mul_of_nonneg_right key hR'.le
    rwa [mul_assoc, div_mul_cancel₀ _ hR'.ne'] at this
  nlinarith

/-! ### Exact optima -/

/-- **The exact optimum over all routings**: a primal certificate and a dual certificate for the
same `θ = p / q` show that `θ` is the largest throughput at which `dem` is routable. -/
theorem isGreatest_routable (dem : Fin k × Fin k → Fin k × Fin k → ℚ) (demN : ℕ → ℕ → ℕ)
    (R : ℕ) (hdem : ∀ s d, dem s d = (demN (idx s) (idx d) : ℚ) / R) (g : ℕ → ℕ → ℕ → ℕ)
    (D : ℕ) (phi lenT : ℕ → ℕ → ℕ) (p q : ℕ) {θ : ℚ} (hθ : θ = (p : ℚ) / q) (hR : 0 < R)
    (hD : 0 < D) (hq : 0 < q) (hc : consCheck k g D demN R p q = true)
    (hcap : capCheck k g D = true) (hd : dualCheck k phi lenT false = true)
    (hb : boundCheck k demN phi lenT R p q = true) :
    IsGreatest {θ | Routable (meshNet k) dem θ} θ :=
  ⟨⟨certFlow dem demN R hdem g D p q hθ hR hD hq hc hcap⟩, fun _ ⟨F⟩ =>
    hθ ▸ upper_of_check dem demN R hdem phi lenT false p q hR hq hd hb F
      (fun h => Bool.noConfusion h)⟩

/-- **A minimal flow** from a primal certificate passing `minCheck`. -/
theorem exists_minimal (dem : Fin k × Fin k → Fin k × Fin k → ℚ) (demN : ℕ → ℕ → ℕ)
    (R : ℕ) (hdem : ∀ s d, dem s d = (demN (idx s) (idx d) : ℚ) / R) (g : ℕ → ℕ → ℕ → ℕ)
    (D p q : ℕ) {θ : ℚ} (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D) (hq : 0 < q)
    (hc : consCheck k g D demN R p q = true) (hcap : capCheck k g D = true)
    (hm : minCheck k g = true) :
    ∃ F : Flow (meshNet k) dem θ, F.Minimal mdist :=
  ⟨_, certFlow_minimal dem demN R hdem g D p q hθ hR hD hq hc hcap hm⟩

/-- **The exact optimum over minimal routings**: a minimal primal certificate and a dual
certificate on the minimal links for the same `θ = p / q`. -/
theorem isGreatest_minimal (dem : Fin k × Fin k → Fin k × Fin k → ℚ) (demN : ℕ → ℕ → ℕ)
    (R : ℕ) (hdem : ∀ s d, dem s d = (demN (idx s) (idx d) : ℚ) / R) (g : ℕ → ℕ → ℕ → ℕ)
    (D : ℕ) (phi lenT : ℕ → ℕ → ℕ) (p q : ℕ) {θ : ℚ} (hθ : θ = (p : ℚ) / q) (hR : 0 < R)
    (hD : 0 < D) (hq : 0 < q) (hc : consCheck k g D demN R p q = true)
    (hcap : capCheck k g D = true) (hm : minCheck k g = true)
    (hd : dualCheck k phi lenT true = true) (hb : boundCheck k demN phi lenT R p q = true) :
    IsGreatest {θ | ∃ F : Flow (meshNet k) dem θ, F.Minimal mdist} θ :=
  ⟨exists_minimal dem demN R hdem g D p q hθ hR hD hq hc hcap hm, fun _ ⟨F, hF⟩ =>
    hθ ▸ upper_of_check dem demN R hdem phi lenT true p q hR hq hd hb F (fun _ => hF)⟩

end MeshCert

end Fluid

end AsyncLean
