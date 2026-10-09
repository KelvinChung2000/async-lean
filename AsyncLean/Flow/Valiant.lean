/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.MeshWorst
import AsyncLean.Flow.Topologies

/-!
# Valiant's two-phase routing: half the uniform throughput for every admissible matrix

**Valiant's routing** sends every packet first to a random intermediate vertex, then on to its
destination.  In the fluid model the random intermediate becomes an even split, and the bound needs
no path decomposition: from a flow `g` of the **uniform demand including self** (rate `1 / |V|`
from every vertex to every vertex, itself included) at throughput `θ`, commodity `d` of Valiant's
flow is (`valiantFlow`)

* phase 1: for every source `s`, the **reversal** of `g`'s commodity `s` (`g s v u` on `u → v`),
  weighted by `T s d / 2`.  On a symmetric network it is a flow out of `s` delivering
  `θ T s d / (2 |V|)` to every vertex;
* phase 2: `g`'s commodity `d`, weighted by the column sum `∑ s, T s d / 2`: every vertex forwards
  its share `θ (∑ s, T s d) / (2 |V|)` to `d`.

At `v ≠ d` the net outflow is `θ T v d / 2` (`uniform_net`: commodity `s` of `g` has net outflow
`θ / |V|` away from `s`, and `θ / |V| - θ` at `s`).  A link `u → v` carries at most
`(∑ s, g s v u + ∑ d, g d u v) / 2 ≤ (cap v u + cap u v) / 2 = cap u v`, using row and column sums
at most `1`.

* `AdmissibleGen` : doubly substochastic traffic on any vertex set (`Admissible.gen`,
  `AdmissibleGen.grid`: on the grid it is `Admissible`).
* `valiant` : **Valiant's bound.**  With symmetric capacities, if the uniform demand including self
  is routable at `θ`, every admissible matrix is routable at `θ / 2` (no hypothesis on `θ`).
  `valiant_grid` : the same on `Fin k × Fin k`, with the demand written `1 / k²`.
* `Routable.congr` : a flow serves any demand with the same off-diagonal rates `θ * dem s d`.
* `mesh_uniform_self`, `valiant_mesh`, `valiant_mesh_opt` : on the `k × k` mesh (`k ≥ 2`) the
  uniform demand including self is routable at `8 / k` (`mesh_routable`), so Valiant routes every
  admissible matrix at `4 / k`; for even `k` this is the best worst case of any routing
  (`worst_opt`): Valiant is worst-case optimal on the mesh, though not minimal.
* `torus_bitcomp_upper`, `torus_worst_upper` : on the torus (even `k ≥ 2`, any routing),
  bit-complement is routable only at `θ ≤ 8 / k` (cut bound for the left half: `k² / 2` units
  cross links of capacity at most `4 k`, `torus_half_cap`).  `valiant_torus`, `torus_worst_opt` :
  given the uniform demand including self at `16 / k`, Valiant reaches `8 / k`, the optimum.
* `cubeComp`, `cube_comp_upper`, `cube_worst_upper` : on the hypercube (`n ≥ 1`, any routing),
  complement is routable only at `θ ≤ 2` (cut by the first coordinate: every vertex on one side
  sends `1` across, and has one link of capacity `2` across).  `valiant_cube`, `cube_worst_opt` :
  given the uniform demand including self at `4`, Valiant reaches `2`, the optimum.

All results are over `ℚ` and general in `k` and `n`.
-/

namespace AsyncLean

namespace Fluid

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An **admissible** traffic matrix on any vertex set (doubly substochastic): every rate is
nonnegative, no source sends more than `1` in total and no destination receives more than `1` in
total.  On the `k × k` grid this is `Admissible` (`Admissible.gen`, `AdmissibleGen.grid`). -/
structure AdmissibleGen (T : V → V → ℚ) : Prop where
  /-- Every rate is nonnegative. -/
  nonneg : ∀ s d, 0 ≤ T s d
  /-- Every source sends at most `1`. -/
  row : ∀ s, ∑ d, T s d ≤ 1
  /-- Every destination receives at most `1`. -/
  col : ∀ d, ∑ s, T s d ≤ 1

omit [DecidableEq V] in
/-- The net outflow of any rate function sums to zero over the vertices. -/
theorem sum_net_zero (f : V → V → ℚ) : ∑ v, (∑ w, f v w - ∑ u, f u v) = 0 := by
  have : ∑ v, ∑ u, f u v = ∑ u, ∑ v, f u v := sum_comm
  rw [sum_sub_distrib, this, sub_self]

/-- In a flow of the uniform demand including self (`1 / |V|` from every vertex to every vertex),
commodity `s` has net outflow `θ / |V|` at every vertex except its destination `s`, where it has
net outflow `θ / |V| - θ` (it absorbs everything the others send). -/
theorem uniform_net {N : Net V} {θ : ℚ}
    (g : Flow N (fun _ _ => 1 / (Fintype.card V : ℚ)) θ) (s v : V) :
    ∑ w, g.f s v w - ∑ u, g.f s u v =
      θ / (Fintype.card V : ℚ) - (if v = s then θ else 0) := by
  have hn : (Fintype.card V : ℚ) ≠ 0 := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
    exact_mod_cast this.ne'
  set e : V → ℚ := fun x => (∑ w, g.f s x w - ∑ u, g.f s u x) -
    (θ / (Fintype.card V : ℚ) - (if x = s then θ else 0)) with he
  have hz : ∀ x, x ≠ s → e x = 0 := fun x hx => by
    simp only [he, g.conserve s x hx, ite_eq_right hx]; ring
  have hsum : ∑ x, e x = 0 := by
    simp only [he]
    rw [sum_sub_distrib, sum_net_zero, sum_sub_distrib]
    simp only [sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true]
    rw [mul_div_cancel₀ _ hn]; ring
  rw [sum_eq_single s (fun x _ hx => hz x hx) (by simp)] at hsum
  have hes : e s = 0 := hsum
  by_cases hv : v = s
  · subst hv; simp only [he] at hes; linarith
  · have := hz v hv
    simp only [he] at this
    linarith

/-- **Valiant's flow** for the traffic matrix `T`, from a flow `g` of the uniform demand including
self.  Commodity `d` is the sum of
* phase 1: for every source `s`, the reversal of `g`'s commodity `s` (`g s v u` on the link
  `u → v`), weighted by `T s d / 2`: it spreads the traffic `s` sends to `d` evenly over all
  vertices;
* phase 2: `g`'s commodity `d`, weighted by the column sum `∑ s, T s d / 2`: every vertex
  forwards to `d` its even share of the traffic for `d`. -/
def valiantFlow (g : V → V → V → ℚ) (T : V → V → ℚ) (d u v : V) : ℚ :=
  (∑ s, T s d * g s v u + (∑ s, T s d) * g d u v) / 2

omit [DecidableEq V] in
/-- Net outflow of Valiant's flow, in terms of the net outflows of `g`. -/
theorem valiantFlow_net (g : V → V → V → ℚ) (T : V → V → ℚ) (d v : V) :
    ∑ w, valiantFlow g T d v w - ∑ u, valiantFlow g T d u v =
      (∑ s, T s d * -(∑ w, g s v w - ∑ u, g s u v) +
        (∑ s, T s d) * (∑ w, g d v w - ∑ u, g d u v)) / 2 := by
  unfold valiantFlow
  simp only [div_eq_mul_inv, ← sum_mul, sum_add_distrib, ← mul_sum, mul_neg, mul_sub,
    sum_sub_distrib, sum_neg_distrib]
  rw [sum_comm (f := fun w s => T s d * g s w v), sum_comm (f := fun u s => T s d * g s v u)]
  simp only [← mul_sum]
  ring

/-- **Valiant's routing as a flow**: if the uniform demand including self is routable at `θ` in a
network with symmetric capacities, then every admissible matrix is routable at `θ / 2`. -/
def valiantRouting {N : Net V} (hsym : ∀ u v, N.cap u v = N.cap v u) {θ : ℚ}
    (g : Flow N (fun _ _ => 1 / (Fintype.card V : ℚ)) θ) {T : V → V → ℚ}
    (hT : AdmissibleGen T) : Flow N T (θ / 2) where
  f := valiantFlow g.f T
  nonneg d u v := by
    unfold valiantFlow
    have h1 : 0 ≤ ∑ s, T s d * g.f s v u :=
      sum_nonneg fun s _ => mul_nonneg (hT.nonneg s d) (g.nonneg s v u)
    have h2 : 0 ≤ (∑ s, T s d) * g.f d u v :=
      mul_nonneg (sum_nonneg fun s _ => hT.nonneg s d) (g.nonneg d u v)
    linarith
  conserve d v hv := by
    rw [valiantFlow_net]
    simp only [uniform_net g, ite_eq_right hv, sub_zero]
    have e : ∑ s, T s d * -(θ / (Fintype.card V : ℚ) - (if v = s then θ else 0)) =
        T v d * θ - (∑ s, T s d) * (θ / (Fintype.card V : ℚ)) := by
      simp only [neg_sub, mul_sub, mul_ite, mul_zero, sum_sub_distrib, sum_ite_eq, mem_univ,
        ite_true, ← sum_mul]
    rw [e]; ring
  capacity u v := by
    unfold valiantFlow
    simp only [div_eq_mul_inv]
    rw [← sum_mul, sum_add_distrib]
    have h1 : ∑ d, ∑ s, T s d * g.f s v u ≤ N.cap v u := by
      rw [sum_comm]
      calc ∑ s, ∑ d, T s d * g.f s v u = ∑ s, (∑ d, T s d) * g.f s v u :=
            sum_congr rfl fun s _ => (sum_mul ..).symm
        _ ≤ ∑ s, g.f s v u := sum_le_sum fun s _ => by
            have := mul_le_mul_of_nonneg_right (hT.row s) (g.nonneg s v u)
            linarith
        _ ≤ N.cap v u := g.capacity v u
    have h2 : ∑ d, (∑ s, T s d) * g.f d u v ≤ N.cap u v :=
      calc ∑ d, (∑ s, T s d) * g.f d u v ≤ ∑ d, g.f d u v := sum_le_sum fun d _ => by
            have := mul_le_mul_of_nonneg_right (hT.col d) (g.nonneg d u v)
            linarith
        _ ≤ N.cap u v := g.capacity u v
    rw [hsym v u] at h1
    linarith

/-- **Valiant's bound.**  In a network with symmetric capacities (`cap u v = cap v u`), if the
uniform demand including self (rate `1 / |V|` from every vertex to every vertex) is routable at
throughput `θ`, then every admissible traffic matrix is routable at `θ / 2`, by two-phase
routing: first spread every source's traffic evenly over all vertices, then deliver it. -/
theorem valiant {N : Net V} (hsym : ∀ u v, N.cap u v = N.cap v u) {θ : ℚ}
    (h : Routable N (fun _ _ => 1 / (Fintype.card V : ℚ)) θ) (T : V → V → ℚ)
    (hT : AdmissibleGen T) : Routable N T (θ / 2) := by
  obtain ⟨g⟩ := h
  exact ⟨valiantRouting hsym g hT⟩

omit [DecidableEq V] in
/-- Change of demand: a flow routes `θ * dem` as soon as it routes `θ' * dem'` with the same
off-diagonal rates. -/
theorem Routable.congr {N : Net V} {dem dem' : V → V → ℚ} {θ θ' : ℚ} (h : Routable N dem θ)
    (e : ∀ s d, s ≠ d → θ * dem s d = θ' * dem' s d) : Routable N dem' θ' := by
  obtain ⟨F⟩ := h
  exact ⟨⟨F.f, F.nonneg, fun d v hv => (F.conserve d v hv).trans (e v d hv), F.capacity⟩⟩

/-- A capacity `2` between related vertices is symmetric if the relation is. -/
theorem ite_two_symm {α : Type*} (A : α → α → Prop) [DecidableRel A]
    (hA : ∀ u v, A u v → A v u) (u v : α) :
    (if A u v then (2 : ℚ) else 0) = if A v u then 2 else 0 := by
  by_cases h : A u v
  · rw [ite_eq_left h, ite_eq_left (hA u v h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hA v u h'))]

end General

section Grid

variable {k : ℕ}

/-- An admissible matrix on the grid is admissible in the general sense. -/
theorem Admissible.gen {T : Fin k × Fin k → Fin k × Fin k → ℚ} (h : Admissible T) :
    AdmissibleGen T := ⟨h.nonneg, h.row, h.col⟩

/-- On the grid, the general notion is `Admissible`. -/
theorem AdmissibleGen.grid {T : Fin k × Fin k → Fin k × Fin k → ℚ} (h : AdmissibleGen T) :
    Admissible T := ⟨h.nonneg, h.row, h.col⟩

/-- The grid has `k²` vertices. -/
theorem card_grid (k : ℕ) : (Fintype.card (Fin k × Fin k) : ℚ) = (k : ℚ) ^ 2 := by
  simp [Fintype.card_prod, sq]

/-- Valiant's bound on the `k × k` grid, with the uniform demand including self written
`1 / k²`. -/
theorem valiant_grid {N : Net (Fin k × Fin k)} (hsym : ∀ u v, N.cap u v = N.cap v u) {θ : ℚ}
    (h : Routable N (fun _ _ => 1 / (k ^ 2 : ℚ)) θ) (T : Fin k × Fin k → Fin k × Fin k → ℚ)
    (hT : AdmissibleGen T) : Routable N T (θ / 2) := by
  rw [← card_grid] at h
  exact valiant hsym h T hT

/-- Mesh neighbours are symmetric. -/
theorem MeshAdj.symm {u v : Fin k × Fin k} (h : MeshAdj u v) : MeshAdj v u := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩

/-- The mesh has symmetric capacities. -/
theorem mesh_symm (k : ℕ) (u v : Fin k × Fin k) : (meshNet k).cap u v = (meshNet k).cap v u :=
  ite_two_symm MeshAdj (fun _ _ h => h.symm) u v

/-- The uniform demand including self is routable in the `k × k` mesh at `8 / k` (`k ≥ 2`):
XY routing of `uniform k` (`mesh_routable`) at `8 (k² - 1) / k³` delivers the same rates
`8 / k³` between distinct vertices. -/
theorem mesh_uniform_self (k : ℕ) (hk : 2 ≤ k) :
    Routable (meshNet k) (fun _ _ => 1 / (k ^ 2 : ℚ)) (8 / k) := by
  refine (mesh_routable k hk).congr fun s d hsd => ?_
  unfold uniform
  rw [ite_eq_right hsd]
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have h1 : (k : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (k : ℚ) ≠ 0 := by linarith
  rw [div_mul_div_comm, div_mul_div_comm, mul_one, mul_one,
    div_eq_div_iff (mul_ne_zero (pow_ne_zero _ h2) h1) (mul_ne_zero h2 (pow_ne_zero _ h2))]
  ring

/-- **Valiant on the mesh** (`k ≥ 2`): two-phase routing routes every admissible matrix at
`4 / k`. -/
theorem valiant_mesh (k : ℕ) (hk : 2 ≤ k) :
    ∀ T, AdmissibleGen T → Routable (meshNet k) T (4 / k) := by
  intro T hT
  have := valiant_grid (mesh_symm k) (mesh_uniform_self k hk) T hT
  rwa [show (8 : ℚ) / k / 2 = 4 / k by ring] at this

/-- **Valiant is worst-case optimal on the mesh** (even `k ≥ 2`): its guarantee `4 / k` is the
best worst-case throughput of any routing (`worst_opt`; bit-complement attains it). -/
theorem valiant_mesh_opt (k : ℕ) (hk : 2 ≤ k) (he : Even k) :
    IsGreatest {θ : ℚ | ∀ T, AdmissibleGen T → Routable (meshNet k) T θ} (4 / k) :=
  ⟨valiant_mesh k hk, fun _ h => bitcomp_upper k hk he (h _ (bitcomp_admissible k).gen)⟩

/-- `(a + 1) % k` for `a < k`: either `a + 1` or, at the end of the ring, `0`. -/
theorem succ_mod_cases {a k : ℕ} (ha : a < k) :
    (a + 1 < k ∧ (a + 1) % k = a + 1) ∨ (a + 1 = k ∧ (a + 1) % k = 0) := by
  rcases Nat.lt_or_ge (a + 1) k with h | h
  · exact Or.inl ⟨h, Nat.mod_eq_of_lt h⟩
  · have e : a + 1 = k := by omega
    exact Or.inr ⟨e, by rw [e, Nat.mod_self]⟩

/-- Torus neighbours are symmetric. -/
theorem TorusAdj.symm {u v : Fin k × Fin k} (h : TorusAdj u v) : TorusAdj v u := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩

/-- The torus has symmetric capacities. -/
theorem torus_symm (k : ℕ) (u v : Fin k × Fin k) : (torusNet k).cap u v = (torusNet k).cap v u :=
  ite_two_symm TorusAdj (fun _ _ h => h.symm) u v

/-- The links leaving the left half (the first `m` columns, `k = 2m`) of the torus have total
capacity at most `4 k`: in every row the link from column `m - 1` to `m` and the wrap-around link
from column `0` to `k - 1` (the same link if `k = 2`). -/
theorem torus_half_cap (k m : ℕ) (hm : k = m + m) (hm1 : 1 ≤ m) :
    ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
      (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then (torusNet k).cap u v else 0) ≤ 4 * k := by
  have hmk : m < k := by omega
  have hlk : k - 1 < k := by omega
  have h0 : ∀ (P : Prop) [Decidable P] (Q : Prop) [Decidable Q],
      (0 : ℚ) ≤ if P then (if Q then 2 else 0) else 0 := by
    intros; split_ifs <;> norm_num
  have p : ∀ u v : Fin k × Fin k,
      (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then (torusNet k).cap u v else 0) ≤
        (if v = (⟨m, hmk⟩, u.2) then (if (u.1 : ℕ) + 1 = m then (2 : ℚ) else 0) else 0) +
        (if v = (⟨k - 1, hlk⟩, u.2) then (if (u.1 : ℕ) = 0 then (2 : ℚ) else 0) else 0) := by
    intro u v
    have hA := h0 (v = (⟨m, hmk⟩, u.2)) ((u.1 : ℕ) + 1 = m)
    have hB := h0 (v = (⟨k - 1, hlk⟩, u.2)) ((u.1 : ℕ) = 0)
    show (if _ then ite _ _ _ else _) ≤ _
    by_cases hc : (2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k) ∧ TorusAdj u v
    · obtain ⟨⟨hu, hv⟩, hadj⟩ := hc
      rw [ite_eq_left ⟨hu, hv⟩, ite_eq_left hadj]
      rcases hadj with ⟨h1, h2 | h2⟩ | ⟨h1, _⟩
      · rcases succ_mod_cases u.1.2 with ⟨_, hq⟩ | ⟨_, _⟩
        · rw [hq] at h2
          have hv' : v = (⟨m, hmk⟩, u.2) := Prod.ext (Fin.ext (by simp; omega)) h1.symm
          rw [ite_eq_left hv', ite_eq_left (by omega)]
          linarith
        · omega
      · rcases succ_mod_cases v.1.2 with ⟨_, hq⟩ | ⟨_, hq⟩
        · rw [hq] at h2; omega
        · rw [hq] at h2
          have hv' : v = (⟨k - 1, hlk⟩, u.2) := Prod.ext (Fin.ext (by simp; omega)) h1.symm
          rw [ite_eq_left hv', ite_eq_left h2.symm]
          linarith
      · rw [h1] at hu; exact absurd hu hv
    · have : (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then
          (if TorusAdj u v then (2 : ℚ) else 0) else 0) = 0 := by
        by_cases h1 : 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k
        · rw [ite_eq_left h1, ite_eq_right (fun h2 => hc ⟨h1, h2⟩)]
        · exact ite_eq_right h1
      rw [this]
      linarith
  calc _ ≤ ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
        ((if v = (⟨m, hmk⟩, u.2) then (if (u.1 : ℕ) + 1 = m then (2 : ℚ) else 0) else 0) +
        (if v = (⟨k - 1, hlk⟩, u.2) then (if (u.1 : ℕ) = 0 then (2 : ℚ) else 0) else 0)) :=
        sum_le_sum fun u _ => sum_le_sum fun v _ => p u v
    _ = ∑ u : Fin k × Fin k, ((if (u.1 : ℕ) + 1 = m then (2 : ℚ) else 0) +
          (if (u.1 : ℕ) = 0 then (2 : ℚ) else 0)) := by
        simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    _ = 4 * k := by
        rw [sum_fst (fun i : Fin k =>
          (if (i : ℕ) + 1 = m then (2 : ℚ) else 0) + (if (i : ℕ) = 0 then (2 : ℚ) else 0))]
        rw [Fin.sum_univ_eq_sum_range
            (fun i => (if i + 1 = m then (2 : ℚ) else 0) + (if i = 0 then (2 : ℚ) else 0)) k,
          sum_add_distrib,
          sum_range_single k (m - 1) (fun _ => (2 : ℚ)) (fun i => i + 1 = m)
            (fun i hi => by omega),
          sum_range_single k 0 (fun _ => (2 : ℚ)) (fun i => i = 0) (fun i hi => hi),
          ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, rfl⟩]
        ring

/-- Bit-complement sends all `k² / 2` units of the left half (the first `m` columns, `k = 2m`)
to the right half. -/
theorem bitcomp_half (k m : ℕ) (hm : k = m + m) (hmk : m < k) :
    ∑ s : Fin k × Fin k, ∑ d : Fin k × Fin k,
      (if 2 * (s.1 : ℕ) < k ∧ ¬ 2 * (d.1 : ℕ) < k then bitcomp k s d else 0) = k * m := by
  have hA : ∑ s : Fin k × Fin k, (if 2 * (s.1 : ℕ) < k then (1 : ℚ) else 0) = k * m := by
    rw [sum_fst (fun i : Fin k => if 2 * (i : ℕ) < k then (1 : ℚ) else 0)]
    rw [Fin.sum_univ_eq_sum_range (fun i => if 2 * i < k then (1 : ℚ) else 0) k,
      sum_congr rfl (g := fun i => if i < m then (1 : ℚ) else 0)
        (fun i _ => by simp only [show 2 * i < k ↔ i < m by omega]),
      sum_range_lt k m hmk.le]
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

/-- **Bit-complement on the torus** (even `k ≥ 2`, any routing): by the cut bound for the left
half, whose `k² / 2` vertices all send across links of total capacity at most `4 k`,
bit-complement is routable in the torus only at `θ ≤ 8 / k`. -/
theorem torus_bitcomp_upper (k : ℕ) (hk : 2 ≤ k) (he : Even k) {θ : ℚ}
    (h : Routable (torusNet k) (bitcomp k) θ) : θ ≤ 8 / k := by
  obtain ⟨m, hm⟩ := he
  have hmk : m < k := by omega
  have key := cut_bound h (fun u : Fin k × Fin k => 2 * (u.1 : ℕ) < k)
  rw [bitcomp_half k m hm hmk] at key
  have hR := torus_half_cap k m hm (by omega)
  have hkm : (k : ℚ) = m + m := by exact_mod_cast hm
  have hk' : (0 : ℚ) < k := by
    have : (2 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  have h1 : (k : ℚ) * (θ * m) ≤ k * 4 := by
    have := key.trans hR
    linarith
  have h2 := le_of_mul_le_mul_left h1 hk'
  rw [le_div_iff₀ hk', hkm]
  linarith

/-- **No routing has a worst case above `8 / k` on the torus** (even `k ≥ 2`). -/
theorem torus_worst_upper (k : ℕ) (hk : 2 ≤ k) (he : Even k) {θ : ℚ}
    (h : ∀ T, AdmissibleGen T → Routable (torusNet k) T θ) : θ ≤ 8 / k :=
  torus_bitcomp_upper k hk he (h _ (bitcomp_admissible k).gen)

/-- **Valiant on the torus**: if the uniform demand including self is routable at `16 / k`,
two-phase routing routes every admissible matrix at `8 / k`. -/
theorem valiant_torus (k : ℕ) (h : Routable (torusNet k) (fun _ _ => 1 / (k ^ 2 : ℚ)) (16 / k)) :
    ∀ T, AdmissibleGen T → Routable (torusNet k) T (8 / k) := by
  intro T hT
  have := valiant_grid (torus_symm k) h T hT
  rwa [show (16 : ℚ) / k / 2 = 8 / k by ring] at this

/-- **Valiant is worst-case optimal on the torus** (even `k ≥ 2`), given that the uniform demand
including self is routable at `16 / k`: the best worst-case throughput is `8 / k`. -/
theorem torus_worst_opt (k : ℕ) (hk : 2 ≤ k) (he : Even k)
    (h : Routable (torusNet k) (fun _ _ => 1 / (k ^ 2 : ℚ)) (16 / k)) :
    IsGreatest {θ : ℚ | ∀ T, AdmissibleGen T → Routable (torusNet k) T θ} (8 / k) :=
  ⟨valiant_torus k h, fun _ hθ => torus_worst_upper k hk he hθ⟩

end Grid

section Cube

variable {n : ℕ}

/-- **Complement** traffic on the hypercube: `s` sends rate `1` to the vertex differing from it
in every coordinate. -/
def cubeComp (n : ℕ) (s d : Fin n → Bool) : ℚ := if d = (fun i => !s i) then 1 else 0

/-- Complement is a permutation, hence admissible. -/
theorem cubeComp_admissible (n : ℕ) : AdmissibleGen (cubeComp n) where
  nonneg s d := by unfold cubeComp; split_ifs <;> norm_num
  row s := by simp [cubeComp]
  col d := by
    have e : ∀ s : Fin n → Bool, (d = fun i => !s i) ↔ (s = fun i => !d i) := by
      intro s; constructor <;> rintro rfl <;> funext i <;> simp
    simp [cubeComp, e]

/-- Hypercube neighbours are symmetric. -/
theorem CubeAdj.symm {u v : Fin n → Bool} (h : CubeAdj u v) : CubeAdj v u := by
  unfold CubeAdj at h ⊢
  rwa [show cubeDiff v u = cubeDiff u v from filter_congr fun i _ => ne_comm]

/-- The hypercube has symmetric capacities. -/
theorem cube_symm (n : ℕ) (u v : Fin n → Bool) : (cubeNet n).cap u v = (cubeNet n).cap v u :=
  ite_two_symm CubeAdj (fun _ _ h => h.symm) u v

/-- The hypercube has `2ⁿ` vertices. -/
theorem card_cube (n : ℕ) : (Fintype.card (Fin n → Bool) : ℚ) = (2 : ℚ) ^ n := by
  simp

/-- A neighbour of `u` across the first coordinate cut is `u` with that coordinate flipped. -/
theorem cube_cut_adj (hn : 1 ≤ n) {u v : Fin n → Bool} (hu : u ⟨0, hn⟩ = false)
    (hv : ¬ v ⟨0, hn⟩ = false) (h : CubeAdj u v) : v = Function.update u ⟨0, hn⟩ true := by
  have hmem : (⟨0, hn⟩ : Fin n) ∈ cubeDiff u v := by
    simp only [cubeDiff, mem_filter, mem_univ, true_and, hu]
    exact fun h' => hv h'.symm
  obtain ⟨a, ha⟩ := card_eq_one.1 h
  rw [ha, mem_singleton] at hmem
  funext i
  by_cases hi : i = ⟨0, hn⟩
  · subst hi
    rw [Function.update_self]
    simpa using hv
  · rw [Function.update_of_ne hi]
    have : i ∉ cubeDiff u v := by
      rw [ha, mem_singleton, ← hmem]; exact hi
    simp only [cubeDiff, mem_filter, mem_univ, true_and, not_not] at this
    exact this.symm

/-- **Complement on the hypercube** (`n ≥ 1`, any routing): by the cut bound across the first
coordinate, whose `2ⁿ⁻¹` vertices on one side all send across, each through at most one link of
capacity `2`, complement is routable only at `θ ≤ 2`. -/
theorem cube_comp_upper (n : ℕ) (hn : 1 ≤ n) {θ : ℚ}
    (h : Routable (cubeNet n) (cubeComp n) θ) : θ ≤ 2 := by
  set i0 : Fin n := ⟨0, hn⟩
  have key := cut_bound h (fun u : Fin n → Bool => u i0 = false)
  set A := ∑ s : Fin n → Bool, (if s i0 = false then (1 : ℚ) else 0) with hA
  have hL : ∑ s : Fin n → Bool, ∑ d : Fin n → Bool,
      (if s i0 = false ∧ ¬ d i0 = false then cubeComp n s d else 0) = A := by
    refine sum_congr rfl fun s _ => ?_
    have e : ∀ d : Fin n → Bool,
        (if s i0 = false ∧ ¬ d i0 = false then cubeComp n s d else 0) =
          if d = (fun i => !s i) then (if s i0 = false then (1 : ℚ) else 0) else 0 := by
      intro d
      unfold cubeComp
      by_cases hd : d = (fun i => !s i)
      · subst hd
        by_cases hs : s i0 = false <;> simp [hs]
      · simp [hd]
    rw [sum_congr rfl fun d _ => e d, sum_ite_eq']
    simp
  have hR : ∑ u : Fin n → Bool, ∑ v : Fin n → Bool,
      (if u i0 = false ∧ ¬ v i0 = false then (cubeNet n).cap u v else 0) ≤ 2 * A := by
    have p : ∀ u v : Fin n → Bool,
        (if u i0 = false ∧ ¬ v i0 = false then (cubeNet n).cap u v else 0) ≤
          if v = Function.update u i0 true then (if u i0 = false then (2 : ℚ) else 0) else 0 := by
      intro u v
      show (if _ then ite _ _ _ else _) ≤ _
      by_cases hc : (u i0 = false ∧ ¬ v i0 = false) ∧ CubeAdj u v
      · obtain ⟨⟨hu, hv⟩, hadj⟩ := hc
        rw [ite_eq_left ⟨hu, hv⟩, ite_eq_left hadj, ite_eq_left (cube_cut_adj hn hu hv hadj),
          ite_eq_left hu]
      · have : (if u i0 = false ∧ ¬ v i0 = false then
            (if CubeAdj u v then (2 : ℚ) else 0) else 0) = 0 := by
          by_cases h1 : u i0 = false ∧ ¬ v i0 = false
          · rw [ite_eq_left h1, ite_eq_right (fun h2 => hc ⟨h1, h2⟩)]
          · exact ite_eq_right h1
        rw [this]
        split_ifs <;> norm_num
    calc _ ≤ ∑ u : Fin n → Bool, ∑ v : Fin n → Bool,
          (if v = Function.update u i0 true then (if u i0 = false then (2 : ℚ) else 0) else 0) :=
          sum_le_sum fun u _ => sum_le_sum fun v _ => p u v
      _ = 2 * A := by
          simp only [sum_ite_eq', mem_univ, ite_true, hA, mul_sum]
          refine sum_congr rfl fun u _ => ?_
          split_ifs <;> norm_num
  rw [hL] at key
  have hpos : 0 < A := by
    have h1 : (if (fun _ => false : Fin n → Bool) i0 = false then (1 : ℚ) else 0) ≤ A :=
      single_le_sum (f := fun s : Fin n → Bool => if s i0 = false then (1 : ℚ) else 0)
        (fun s _ => by split_ifs <;> norm_num) (mem_univ (fun _ => false))
    simp only [ite_true] at h1
    linarith
  have := key.trans hR
  exact le_of_mul_le_mul_right (by linarith) hpos

/-- **No routing has a worst case above `2` on the hypercube** (`n ≥ 1`). -/
theorem cube_worst_upper (n : ℕ) (hn : 1 ≤ n) {θ : ℚ}
    (h : ∀ T, AdmissibleGen T → Routable (cubeNet n) T θ) : θ ≤ 2 :=
  cube_comp_upper n hn (h _ (cubeComp_admissible n))

/-- **Valiant on the hypercube**: if the uniform demand including self is routable at `4`,
two-phase routing routes every admissible matrix at `2`. -/
theorem valiant_cube (n : ℕ) (h : Routable (cubeNet n) (fun _ _ => 1 / (2 ^ n : ℚ)) 4) :
    ∀ T, AdmissibleGen T → Routable (cubeNet n) T 2 := by
  intro T hT
  rw [← card_cube] at h
  have := valiant (cube_symm n) h T hT
  rwa [show (4 : ℚ) / 2 = 2 by norm_num] at this

/-- **Valiant is worst-case optimal on the hypercube** (`n ≥ 1`), given that the uniform demand
including self is routable at `4`: the best worst-case throughput is `2`. -/
theorem cube_worst_opt (n : ℕ) (hn : 1 ≤ n)
    (h : Routable (cubeNet n) (fun _ _ => 1 / (2 ^ n : ℚ)) 4) :
    IsGreatest {θ : ℚ | ∀ T, AdmissibleGen T → Routable (cubeNet n) T θ} 2 :=
  ⟨valiant_cube n h, fun _ hθ => cube_worst_upper n hn hθ⟩

end Cube

end Fluid

end AsyncLean
