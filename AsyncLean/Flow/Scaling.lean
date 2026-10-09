/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Symmetric
import AsyncLean.Flow.MeshOdd

/-!
# Routing that scales linearly with the connections

How does throughput grow when a network gets more connections?  In the fluid model the answer
is exact, and it says which routing scheme to use.

**No routing grows faster than linearly.**  Throughput is homogeneous in the capacities: with
`m` connections in place of every one (`Net.copies`), a traffic matrix is routable at `θ`
exactly when it is routable at `θ / m` on one connection (`copies_routable_iff`).  So the best
throughput of `m` connections is exactly `m` times the best throughput of one
(`opt_copies`), for a single traffic matrix and for the worst case over any class of matrices
(`worstOpt_copies`).  The hop bound (`hop_bound`) says the same from the other side: the
throughput times the traffic's hop count is at most the total capacity, the number of
connections times their capacity.

**Lanes reach it.**  The routing that reaches the optimum is the simplest one: treat the `m`
connections of every link as `m` **lanes**, each a full copy of the network, let every packet
pick a lane at its source and stay on it, and route inside each lane with the best scheme for
one connection.  Lane `i` carries the flow of that scheme; the flows add (`Flow.add`,
`Flow.sum`).  No other routing on `m` connections does better, adaptive or not, with or without
detours, whatever it does across lanes.

**Unequal connections.**  When the connections are not copies of one network (a mesh plus a
layer of express links, a torus plus a second torus with another wiring), split them into
layers `N i` whose capacities add up to at most the network's, and send a fraction
`θ i / ∑ θ` of every demand into layer `i`, where `θ i` is the throughput of layer `i` on its
own.  Then the network routes the traffic at `∑ θ i` (`layered_routable`): throughput is
**superadditive** in the connections (`opt_superadditive`), every layer added contributes its
own throughput, and the guarantee is linear in the number of layers.  With fewer connections on
some links than on others, the guarantee is linear in the smallest number (`Routable.smul`).

## Main results

* `Net.copies`, `Net.add`, `Net.sum` : `m` connections per link, two layers of connections, a
  finite family of layers.
* `Flow.smul`, `Flow.add`, `Routable.smul`, `Routable.add`, `Routable.mono`, `Routable.zero` :
  flows scale and add.
* `layered_routable` : **the layered scheme**: the sum of the layers' throughputs.
* `copies_routable_iff`, `opt_copies`, `worstOpt_copies` : **exact linear scaling** of the
  optimum, for a matrix and for the worst case over any class of matrices.
* `opt_superadditive` : the optimum of two layers together is at least the sum of their optima.
* Instances, for every number `m ≥ 1` of connections per link: the worst case over admissible
  traffic is exactly `4m / k` on the `k × k` mesh (even `k`, `mesh_copies_worst`), `8m / k` on
  the torus (even `k ≥ 4`, `torus_copies_worst`) and `2m` on the hypercube
  (`cube_copies_worst`), reached by Valiant's routing in every lane; under uniform traffic the
  optimum is `m` times `mesh_opt_all`, `torus_uniform_opt` and `cube_uniform_opt`
  (`mesh_copies_uniform`, `torus_copies_uniform`, `cube_copies_uniform`), reached by minimal
  routing in every lane.

All results are over `ℚ`.
-/

namespace AsyncLean

namespace Fluid

open Finset

section General

variable {V : Type*} [Fintype V]

/-! ### More connections -/

/-- **`m` connections per link**: every link of `N` replaced by `m` connections of the same
capacity. -/
def Net.copies (N : Net V) (m : ℕ) : Net V where
  cap u v := m * N.cap u v
  cap_nonneg u v := mul_nonneg (Nat.cast_nonneg m) (N.cap_nonneg u v)

/-- Two layers of connections on the same vertices: the capacities add. -/
def Net.add (N₁ N₂ : Net V) : Net V where
  cap u v := N₁.cap u v + N₂.cap u v
  cap_nonneg u v := add_nonneg (N₁.cap_nonneg u v) (N₂.cap_nonneg u v)

/-- A finite family of layers of connections: the capacities add. -/
def Net.sum {ι : Type*} (s : Finset ι) (N : ι → Net V) : Net V where
  cap u v := ∑ i ∈ s, (N i).cap u v
  cap_nonneg u v := sum_nonneg fun i _ => (N i).cap_nonneg u v

omit [Fintype V] in
@[simp] theorem Net.copies_cap (N : Net V) (m : ℕ) (u v : V) :
    (N.copies m).cap u v = m * N.cap u v := rfl

omit [Fintype V] in
@[simp] theorem Net.add_cap (N₁ N₂ : Net V) (u v : V) :
    (N₁.add N₂).cap u v = N₁.cap u v + N₂.cap u v := rfl

omit [Fintype V] in
@[simp] theorem Net.sum_cap {ι : Type*} (s : Finset ι) (N : ι → Net V) (u v : V) :
    (Net.sum s N).cap u v = ∑ i ∈ s, (N i).cap u v := rfl

/-! ### Flows scale and add -/

/-- A flow scaled by `c ≥ 0` routes `c * θ` in any network with `c` times the capacity. -/
def Flow.smul {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (F : Flow N dem θ) (c : ℚ) (hc : 0 ≤ c)
    {N' : Net V} (hcap : ∀ u v, c * N.cap u v ≤ N'.cap u v) : Flow N' dem (c * θ) where
  f d u v := c * F.f d u v
  nonneg d u v := mul_nonneg hc (F.nonneg d u v)
  conserve d v hv := by
    rw [← mul_sum, ← mul_sum, ← mul_sub, F.conserve d v hv, mul_assoc]
  capacity u v := by
    rw [← mul_sum]
    exact (mul_le_mul_of_nonneg_left (F.capacity u v) hc).trans (hcap u v)

/-- Two flows of the same traffic on two layers route the sum of their throughputs on any
network with at least the sum of the capacities: each layer carries its own flow. -/
def Flow.add {N₁ N₂ N' : Net V} {dem : V → V → ℚ} {θ₁ θ₂ : ℚ} (F₁ : Flow N₁ dem θ₁)
    (F₂ : Flow N₂ dem θ₂) (hcap : ∀ u v, N₁.cap u v + N₂.cap u v ≤ N'.cap u v) :
    Flow N' dem (θ₁ + θ₂) where
  f d u v := F₁.f d u v + F₂.f d u v
  nonneg d u v := add_nonneg (F₁.nonneg d u v) (F₂.nonneg d u v)
  conserve d v hv := by
    simp only [sum_add_distrib]
    have h1 := F₁.conserve d v hv
    have h2 := F₂.conserve d v hv
    linarith
  capacity u v := by
    rw [sum_add_distrib]
    linarith [F₁.capacity u v, F₂.capacity u v, hcap u v]

/-- The empty flow routes any traffic at throughput `0`. -/
theorem Routable.zero (N : Net V) (dem : V → V → ℚ) : Routable N dem 0 :=
  ⟨{ f := fun _ _ _ => 0
     nonneg := fun _ _ _ => le_rfl
     conserve := fun _ _ _ => by simp
     capacity := fun u v => by simpa using N.cap_nonneg u v }⟩

/-- Throughput scales with the capacity: `c` times the capacity routes `c` times the
throughput. -/
theorem Routable.smul {N N' : Net V} {dem : V → V → ℚ} {θ : ℚ} (h : Routable N dem θ) (c : ℚ)
    (hc : 0 ≤ c) (hcap : ∀ u v, c * N.cap u v ≤ N'.cap u v) : Routable N' dem (c * θ) := by
  obtain ⟨F⟩ := h
  exact ⟨F.smul c hc hcap⟩

/-- More capacity routes at least as much. -/
theorem Routable.mono {N N' : Net V} {dem : V → V → ℚ} {θ : ℚ} (h : Routable N dem θ)
    (hcap : ∀ u v, N.cap u v ≤ N'.cap u v) : Routable N' dem θ := by
  have := h.smul (N' := N') 1 zero_le_one fun u v => by rw [one_mul]; exact hcap u v
  rwa [one_mul] at this

/-- Two layers route the sum of their throughputs. -/
theorem Routable.add {N₁ N₂ N' : Net V} {dem : V → V → ℚ} {θ₁ θ₂ : ℚ}
    (h₁ : Routable N₁ dem θ₁) (h₂ : Routable N₂ dem θ₂)
    (hcap : ∀ u v, N₁.cap u v + N₂.cap u v ≤ N'.cap u v) : Routable N' dem (θ₁ + θ₂) := by
  obtain ⟨F₁⟩ := h₁
  obtain ⟨F₂⟩ := h₂
  exact ⟨F₁.add F₂ hcap⟩

/-! ### The layered scheme -/

/-- The layers together, `Net.sum s N`, route the sum of the layers' throughputs. -/
theorem routable_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (N : ι → Net V)
    {dem : V → V → ℚ} {θ : ι → ℚ} (h : ∀ i ∈ s, Routable (N i) dem (θ i)) :
    Routable (Net.sum s N) dem (∑ i ∈ s, θ i) := by
  induction s using Finset.induction_on with
  | empty => simpa using Routable.zero (Net.sum ∅ N) dem
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))
      fun u v => by simp [sum_insert ha]

/-- **The layered scheme.**  Split the connections into layers `N i` (`i ∈ s`) whose capacities
add up to at most those of `N'`.  If layer `i` on its own routes the traffic at `θ i`, then `N'`
routes it at `∑ i ∈ s, θ i`: send the fraction `θ i / ∑ θ` of every demand into layer `i` and
route it there as on its own.  The guarantee grows linearly with the layers. -/
theorem layered_routable {ι : Type*} [DecidableEq ι] (s : Finset ι) (N : ι → Net V)
    {N' : Net V} {dem : V → V → ℚ} {θ : ι → ℚ} (h : ∀ i ∈ s, Routable (N i) dem (θ i))
    (hcap : ∀ u v, ∑ i ∈ s, (N i).cap u v ≤ N'.cap u v) :
    Routable N' dem (∑ i ∈ s, θ i) :=
  (routable_sum s N h).mono hcap

/-- `m` lanes, each routing the traffic at `θ` on one connection per link, route it at
`m * θ` on `m` connections per link: lane `i` carries the flow of one connection. -/
theorem Routable.copies {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (h : Routable N dem θ) (m : ℕ) :
    Routable (N.copies m) dem (m * θ) :=
  h.smul m (Nat.cast_nonneg m) fun _ _ => le_rfl

/-! ### Exact linear scaling of the optimum -/

/-- **No routing on `m` connections beats `m` lanes**: on `m ≥ 1` connections per link the
traffic is routable at `θ` exactly when it is routable at `θ / m` on one. -/
theorem copies_routable_iff {N : Net V} {dem : V → V → ℚ} {θ : ℚ} {m : ℕ} (hm : 0 < m) :
    Routable (N.copies m) dem θ ↔ Routable N dem (θ / m) := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  constructor
  · intro h
    have := h.smul (N' := N) ((1 : ℚ) / m) (div_nonneg zero_le_one hm'.le) fun u v => by
      simp only [Net.copies_cap]
      rw [← mul_assoc, one_div_mul_cancel hm'.ne', one_mul]
    rwa [one_div_mul_eq_div] at this
  · intro h
    have := h.copies m
    rwa [mul_div_cancel₀ _ hm'.ne'] at this

/-- **The optimum scales exactly linearly**: if `θ` is the best throughput of `dem` on one
connection per link, `m * θ` is the best on `m ≥ 1` connections, reached by `m` lanes. -/
theorem opt_copies {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (h : IsGreatest {x | Routable N dem x} θ)
    {m : ℕ} (hm : 0 < m) : IsGreatest {x | Routable (N.copies m) dem x} (m * θ) := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  refine ⟨h.1.copies m, fun x hx => ?_⟩
  have := h.2 ((copies_routable_iff hm).1 hx)
  rw [div_le_iff₀ hm'] at this
  linarith

/-- **The worst case scales exactly linearly**: for any class `D` of traffic matrices, if `w`
is the best throughput guaranteed for every matrix of `D` on one connection per link, `m * w` is
the best on `m ≥ 1` connections, reached by `m` lanes running the same scheme. -/
theorem worstOpt_copies {N : Net V} {D : (V → V → ℚ) → Prop} {w : ℚ}
    (h : IsGreatest {x | ∀ T, D T → Routable N T x} w) {m : ℕ} (hm : 0 < m) :
    IsGreatest {x | ∀ T, D T → Routable (N.copies m) T x} (m * w) := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  refine ⟨fun T hT => (h.1 T hT).copies m, fun x hx => ?_⟩
  have := h.2 fun T hT => (copies_routable_iff hm).1 (hx T hT)
  rw [div_le_iff₀ hm'] at this
  linarith

/-- **The optimum is superadditive in the connections**: two layers together route at least
the sum of their optima. -/
theorem opt_superadditive {N₁ N₂ : Net V} {dem : V → V → ℚ} {θ₁ θ₂ : ℚ}
    (h₁ : IsGreatest {x | Routable N₁ dem x} θ₁) (h₂ : IsGreatest {x | Routable N₂ dem x} θ₂) :
    θ₁ + θ₂ ∈ {x | Routable (N₁.add N₂) dem x} :=
  h₁.1.add h₂.1 fun _ _ => le_rfl

end General

/-! ### Instances: the mesh, the torus and the hypercube with `m` connections per link -/

section Instances

/-- **The mesh with `m` connections per link** (even `k ≥ 2`, `m ≥ 1`): the best worst case over
admissible traffic is `m * (4 / k)`, reached by Valiant's routing in every lane. -/
theorem mesh_copies_worst (k : ℕ) (hk : 2 ≤ k) (he : Even k) {m : ℕ} (hm : 0 < m) :
    IsGreatest {θ : ℚ | ∀ T, AdmissibleGen T → Routable ((meshNet k).copies m) T θ}
      (m * (4 / k)) :=
  worstOpt_copies (valiant_mesh_opt k hk he) hm

/-- **The torus with `m` connections per link** (even `k ≥ 4`, `m ≥ 1`): the best worst case over
admissible traffic is `m * (8 / k)`, reached by Valiant's routing in every lane. -/
theorem torus_copies_worst (k : ℕ) (hk : 4 ≤ k) (he : Even k) {m : ℕ} (hm : 0 < m) :
    IsGreatest {θ : ℚ | ∀ T, AdmissibleGen T → Routable ((torusNet k).copies m) T θ}
      (m * (8 / k)) :=
  worstOpt_copies (torus_worst_opt' k hk he) hm

/-- **The hypercube with `m` connections per link** (`n ≥ 1`, `m ≥ 1`): the best worst case over
admissible traffic is `2 m`, reached by Valiant's routing in every lane. -/
theorem cube_copies_worst (n : ℕ) (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m) :
    IsGreatest {θ : ℚ | ∀ T, AdmissibleGen T → Routable ((cubeNet n).copies m) T θ} (m * 2) :=
  worstOpt_copies (cube_worst_opt' n hn) hm

/-- **Uniform traffic on the mesh with `m` connections per link** (`k ≥ 2`, `m ≥ 1`): `m` times
the optimum of one connection, reached by XY routing in every lane. -/
theorem mesh_copies_uniform (k : ℕ) (hk : 2 ≤ k) {m : ℕ} (hm : 0 < m) :
    IsGreatest {θ : ℚ | Routable ((meshNet k).copies m) (uniform k) θ}
      (m * if Even k then 8 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 8 / (k : ℚ)) :=
  opt_copies (mesh_opt_all k hk) hm

/-- **Uniform traffic on the torus with `m` connections per link** (`k ≥ 3`, `m ≥ 1`): `m` times
the optimum of one connection, reached by minimal routing in every lane. -/
theorem torus_copies_uniform (k : ℕ) (hk : 3 ≤ k) {m : ℕ} (hm : 0 < m) :
    IsGreatest {θ : ℚ | Routable ((torusNet k).copies m) (uniform k) θ}
      (m * if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / (k : ℚ)) :=
  opt_copies (torus_uniform_opt k hk).1 hm

/-- **Uniform traffic on the hypercube with `m` connections per link** (`n ≥ 1`, `m ≥ 1`): `m`
times the optimum of one connection, reached by minimal routing in every lane. -/
theorem cube_copies_uniform (n : ℕ) (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m) :
    IsGreatest {θ : ℚ | Routable ((cubeNet n).copies m) (cubeUniform n) θ}
      (m * (4 * (2 ^ n - 1) / 2 ^ n)) :=
  opt_copies (cube_uniform_opt n hn).1 hm

/-- On the `8 × 8` torus every additional connection per link adds exactly `1` to the
guaranteed worst-case throughput: `m` connections guarantee `m` and no routing guarantees
more. -/
theorem torus_eight_copies_worst {m : ℕ} (hm : 0 < m) :
    IsGreatest {θ : ℚ | ∀ T, AdmissibleGen T → Routable ((torusNet 8).copies m) T θ} m := by
  have := torus_copies_worst 8 (by norm_num) ⟨4, rfl⟩ hm
  rwa [show ((8 : ℕ) : ℚ) = 8 by norm_num, div_self (by norm_num : (8 : ℚ) ≠ 0), mul_one]
    at this

end Instances

end Fluid

end AsyncLean
