/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Certificate
import AsyncLean.Flow.Topologies

/-!
# Checkable certificates for the fluid throughput of any port graph

The checkers of `AsyncLean.Flow.Certificate`, generalised from the mesh to any finite graph
given by a **port table**: vertices are the indices `j < n`, port `i < P` of vertex `j` leads to
the vertex `step j i` (no port if `step j i ≥ n`), and `back j i` is the port at that end leading
back to `j` (`GraphCert.PortGraph`).  The graph's hop distance is given as a table `dist` too,
and `near d j i` says cheaply whether port `i` of `j` brings `d` closer.
Everything is first proved on the graph's own network `G.net C` on `Fin n` (capacity `C` on every
port), and then transported to any network isomorphic to it (`GraphCert.Model`).

* `GraphCert.PortGraph.wfCheck` : the port table is well formed: the port back leads back, and
  distinct ports lead to distinct vertices.  `GraphCert.PortGraph.adjCheck` : the vertices joined
  by a port are those at distance `1`.  `GraphCert.PortGraph.nearCheck` : `near` is right.
* `GraphCert.PortGraph.certFlow` : **primal certificate.**  A table `g d j i : ℕ` (the rate of
  commodity `d` leaving `j` through port `i`, scaled by `D`) passing `consCheck` and `capCheck`
  is a flow of `θ * dem`, `θ = p / q`, in `G.net C`; with `minCheck` it is minimal
  (`certFlow_minimal`).
* `GraphCert.PortGraph.upper_of_check` : **dual certificate.**  Port lengths and potentials
  passing `dualCheck` and `boundCheck` bound every flow (every minimal one, when `minimal`) by
  `θ ≤ p / q`, by `Fluid.Flow.potential_bound_on`.
* `Fluid.Flow.comap`, `Fluid.routable_congr`, `Fluid.minimal_congr` : flows, routability and
  minimality are invariant under relabelling the vertices by a bijection;
  `Fluid.isGreatest_minimal_of_routable` : a minimal flow at the optimum over all routings is
  also optimal over minimal routings.
* `GraphCert.Model` : a network `N` on `V` with a distance, isomorphic to `G.net C` with its
  distance `G.dq` through a bijection `V ≃ Fin n`, for a port graph passing `wfCheck` and
  `nearCheck`; `Model.isGreatest_routable`, `Model.exists_minimal`, `Model.isGreatest_minimal` :
  **the exact optima on `N`** from certificates passing the checks.
* `GraphCert.torusModel` : the `8 × 8` torus `torusNet 8` with `torusDist` is a model of the port
  graph `torusGraph 8` (vertex `(x, y)` has index `x + 8 y`; ports `0`–`3`: `x + 1`, `x - 1`,
  `y + 1`, `y - 1` mod `8`).
* `GraphCert.cubeModel` : the hypercube `cubeNet 6` with `cubeDist` is a model of `cubeGraph 6`
  (vertex `u` has the index `∑ i, u i 2^i`: **coordinate `i` is bit `i`**; port `i` flips bit `i`).

The checkers loop with `allBelow`, `anyBelow` and `sumBelow` and use only `ℕ` arithmetic, which
the kernel evaluates with GMP (`decide +kernel`).
-/

namespace AsyncLean

namespace Fluid

open Finset MeshCert

/-! ### Relabelling the vertices -/

section transport

variable {V W : Type*} [Fintype V] [Fintype W]
  {N : Net V} {N' : Net W} {dem : V → V → ℚ} {dem' : W → W → ℚ} {θ : ℚ}

/-- A flow pulled back along a bijection `e` of the vertices that matches the capacities and the
demands. -/
def Flow.comap (e : V ≃ W) (hcap : ∀ u v, N.cap u v = N'.cap (e u) (e v))
    (hdem : ∀ s d, dem s d = dem' (e s) (e d)) (F : Flow N' dem' θ) : Flow N dem θ where
  f d u v := F.f (e d) (e u) (e v)
  nonneg d u v := F.nonneg _ _ _
  conserve d v hv := by
    rw [hdem, ← F.conserve (e d) (e v) (fun h => hv (e.injective h)),
      e.sum_comp (fun w => F.f (e d) (e v) w), e.sum_comp (fun u => F.f (e d) u (e v))]
  capacity u v := by
    rw [hcap, e.sum_comp (fun d => F.f d (e u) (e v))]
    exact F.capacity _ _

/-- The pulled-back flow is minimal if the flow is, for a matching distance. -/
theorem Flow.comap_minimal (e : V ≃ W) (hcap : ∀ u v, N.cap u v = N'.cap (e u) (e v))
    (hdem : ∀ s d, dem s d = dem' (e s) (e d)) (F : Flow N' dem' θ) {dist : V → V → ℚ}
    {dist' : W → W → ℚ} (hdist : ∀ u v, dist u v = dist' (e u) (e v))
    (hF : F.Minimal dist') : (F.comap e hcap hdem).Minimal dist := fun d u v h => by
  show dist v d < dist u d
  rw [hdist, hdist]
  exact hF _ _ _ h

omit [Fintype V] [Fintype W] in
/-- The capacities seen through the inverse bijection. -/
theorem cap_symm (e : V ≃ W) (hcap : ∀ u v, N.cap u v = N'.cap (e u) (e v)) (a b : W) :
    N'.cap a b = N.cap (e.symm a) (e.symm b) := by
  rw [hcap]; simp

/-- **Routability is invariant under relabelling the vertices.** -/
theorem routable_congr (e : V ≃ W) (hcap : ∀ u v, N.cap u v = N'.cap (e u) (e v))
    (hdem : ∀ s d, dem s d = dem' (e s) (e d)) : Routable N dem θ ↔ Routable N' dem' θ :=
  ⟨fun ⟨F⟩ => ⟨F.comap e.symm (cap_symm e hcap) (fun a b => by rw [hdem]; simp)⟩,
    fun ⟨F⟩ => ⟨F.comap e hcap hdem⟩⟩

/-- **Minimal routability is invariant under relabelling the vertices.** -/
theorem minimal_congr (e : V ≃ W) (hcap : ∀ u v, N.cap u v = N'.cap (e u) (e v))
    (hdem : ∀ s d, dem s d = dem' (e s) (e d)) {dist : V → V → ℚ} {dist' : W → W → ℚ}
    (hdist : ∀ u v, dist u v = dist' (e u) (e v)) :
    (∃ F : Flow N dem θ, F.Minimal dist) ↔ ∃ F : Flow N' dem' θ, F.Minimal dist' :=
  ⟨fun ⟨F, hF⟩ => ⟨_, F.comap_minimal e.symm (cap_symm e hcap)
      (fun a b => by rw [hdem]; simp) (fun a b => by rw [hdist]; simp) hF⟩,
    fun ⟨F, hF⟩ => ⟨_, F.comap_minimal e hcap hdem hdist hF⟩⟩

/-- When a minimal flow reaches the optimum over all routings, it is also the optimum over minimal
routings. -/
theorem isGreatest_minimal_of_routable {dist : V → V → ℚ}
    (h : IsGreatest {θ | Routable N dem θ} θ) (hm : ∃ F : Flow N dem θ, F.Minimal dist) :
    IsGreatest {θ | ∃ F : Flow N dem θ, F.Minimal dist} θ :=
  ⟨hm, fun _ ⟨F, _⟩ => h.2 ⟨F⟩⟩

end transport

namespace GraphCert

/-! ### Port graphs -/

/-- `anyBelow n p`: `p j` holds for some `j < n`. -/
def anyBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | n + 1, p => anyBelow n p || p n

/-- `anyBelow` checks a bounded existential statement. -/
theorem anyBelow_iff {n : ℕ} {p : ℕ → Bool} : anyBelow n p = true ↔ ∃ j < n, p j = true := by
  induction n with
  | zero => simp [anyBelow]
  | succ n ih =>
    simp only [anyBelow, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, Nat.lt_succ_of_lt hj, h⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_or_ge j n with hj' | hj'
      · exact Or.inl ⟨j, hj', h⟩
      · obtain rfl : j = n := by omega
        exact Or.inr h

/-- A finite graph given by a port table: the vertices are the indices `j < n`, port `i < P` of
`j` leads to `step j i` (no port if `step j i ≥ n`), `back j i` is the port at that end leading
back, `dist` is a distance table (the hop distance, by `adjCheck` and the certificates), and
`near d j i` says that port `i` of `j` brings the destination `d` closer (by `nearCheck`; a cheap
test the kernel evaluates in place of two distances). -/
structure PortGraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The number of ports per vertex. -/
  P : ℕ
  /-- The end of port `i` of vertex `j` (no port if `≥ n`). -/
  step : ℕ → ℕ → ℕ
  /-- The port at the end of port `i` of `j` leading back to `j`. -/
  back : ℕ → ℕ → ℕ
  /-- The distance of two vertices. -/
  dist : ℕ → ℕ → ℕ
  /-- Port `i` of `j` brings `d` closer: `near d j i`. -/
  near : ℕ → ℕ → ℕ → Bool

namespace PortGraph

variable (G : PortGraph)

/-- Port `i` of `j` exists. -/
def valid (j i : ℕ) : Bool := decide (G.step j i < G.n)

/-- **The port table is well formed**: the port back from the end of every port `i` of `j`
exists and leads back to `j`, the port back from there is `i` again, and distinct ports of `j`
lead to distinct vertices. -/
def wfCheck : Bool :=
  allBelow G.n fun j => allBelow G.P fun i =>
    !G.valid j i || (decide (G.back j i < G.P) && G.step (G.step j i) (G.back j i) == j &&
      G.back (G.step j i) (G.back j i) == i &&
      allBelow G.P fun i' => i' == i || G.step j i' != G.step j i)

/-- A port of `a` leads to `b`. -/
def adj (a b : ℕ) : Bool := anyBelow G.P fun i => G.step a i == b

/-- The vertices joined by a port are exactly those at distance `1`. -/
def adjCheck : Bool :=
  allBelow G.n fun a => allBelow G.n fun b => G.adj a b == (G.dist a b == 1)

/-- `near` is right: on every port, `near d j i` iff `dist (step j i) d < dist j d`. -/
def nearCheck : Bool :=
  allBelow G.n fun d => allBelow G.n fun j => allBelow G.P fun i =>
    !G.valid j i || G.near d j i == decide (G.dist (G.step j i) d < G.dist j d)

/-- **The network of the port graph**: capacity `C` on every port. -/
def net (C : ℕ) : Net (Fin G.n) where
  cap a b := if G.adj a b then (C : ℚ) else 0
  cap_nonneg a b := by split_ifs <;> simp

/-- The distance table as a distance on the vertices. -/
def dq (a b : Fin G.n) : ℚ := G.dist a b

variable {G}

/-- `adj` is the existence of a port. -/
theorem adj_iff {a b : ℕ} : G.adj a b = true ↔ ∃ i < G.P, G.step a i = b := by
  simp [adj, anyBelow_iff]

/-- `adjCheck` on two vertices. -/
theorem adj_iff_dist (h : G.adjCheck = true) {a b : ℕ} (ha : a < G.n) (hb : b < G.n) :
    G.adj a b = true ↔ G.dist a b = 1 := by
  have := allBelow_iff.1 (allBelow_iff.1 h a ha) b hb
  simp only [beq_iff_eq] at this
  rw [this]; simp

/-- What `nearCheck` says about one port. -/
theorem near_iff (h : G.nearCheck = true) {d j i : ℕ} (hd : d < G.n) (hj : j < G.n)
    (hi : i < G.P) (hv : G.step j i < G.n) :
    G.near d j i = true ↔ G.dist (G.step j i) d < G.dist j d := by
  have := allBelow_iff.1 (allBelow_iff.1 (allBelow_iff.1 h d hd) j hj) i hi
  simp only [valid, hv, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  rw [this, decide_eq_true_iff]

/-- What `wfCheck` says about one port. -/
theorem wf_port (h : G.wfCheck = true) {j i : ℕ} (hj : j < G.n) (hi : i < G.P)
    (hv : G.step j i < G.n) :
    G.back j i < G.P ∧ G.step (G.step j i) (G.back j i) = j ∧
      G.back (G.step j i) (G.back j i) = i ∧
      ∀ i' < G.P, G.step j i' = G.step j i → i' = i := by
  have := allBelow_iff.1 (allBelow_iff.1 h j hj) i hi
  simp only [valid, hv, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, allBelow_iff, Bool.or_eq_true, bne_iff_ne, ne_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  exact ⟨h1, h2, h3, fun i' hi' he => (h4 i' hi').resolve_right (not_not.2 he)⟩

/-! ### Port tables -/

variable (G)

/-- The total of a port table over the ports of `j` leading to `t`. -/
def linkN (T : ℕ → ℕ → ℕ) (j t : ℕ) : ℕ := ∑ i ∈ range G.P, if G.step j i = t then T j i else 0

/-- The total over the existing ports of `j`. -/
def outN (T : ℕ → ℕ → ℕ) (j : ℕ) : ℕ := sumBelow G.P fun i => if G.valid j i then T j i else 0

/-- The total over the ports leading into `j` (the ports back from the ends of its ports). -/
def inN (T : ℕ → ℕ → ℕ) (j : ℕ) : ℕ :=
  sumBelow G.P fun i => if G.valid j i then T (G.step j i) (G.back j i) else 0

/-- The rate a port table puts on the link `u → v`, scaled down by `D`. -/
def portVal (T : ℕ → ℕ → ℕ) (D : ℕ) (u v : Fin G.n) : ℚ := (G.linkN T u v : ℚ) / D

variable {G}

/-- Port tables are nonnegative. -/
theorem portVal_nonneg (T : ℕ → ℕ → ℕ) (D : ℕ) (u v : Fin G.n) : 0 ≤ G.portVal T D u v :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Everything leaving `j`. -/
theorem sum_linkN_out (T : ℕ → ℕ → ℕ) (j : ℕ) :
    ∑ t ∈ range G.n, G.linkN T j t = G.outN T j := by
  unfold linkN outN
  rw [sumBelow_eq, sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_ite_eq]
  simp [valid]

/-- Everything entering `t`: the ports into `t` are the ports back from the ends of its ports. -/
theorem sum_linkN_in (hwf : G.wfCheck = true) (T : ℕ → ℕ → ℕ) {t : ℕ} (ht : t < G.n) :
    ∑ j ∈ range G.n, G.linkN T j t = G.inN T t := by
  unfold linkN inN
  rw [sumBelow_eq, ← sum_product' (f := fun j i => if G.step j i = t then T j i else 0),
    ← sum_filter, ← sum_filter]
  refine sum_nbij' (fun p => G.back p.1 p.2) (fun i => (G.step t i, G.back t i)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ hp
    simp only [mem_filter, mem_product, mem_range] at hp
    obtain ⟨⟨hj, hi⟩, hs⟩ := hp
    obtain ⟨h1, h2, -, -⟩ := wf_port hwf hj hi (hs ▸ ht)
    simp only [mem_filter, mem_range, valid, decide_eq_true_eq]
    exact ⟨h1, by rw [← hs, h2]; exact hj⟩
  · intro i hi
    simp only [mem_filter, mem_range, valid, decide_eq_true_eq] at hi
    obtain ⟨h1, h2, -, -⟩ := wf_port hwf ht hi.1 hi.2
    simp only [mem_filter, mem_product, mem_range]
    exact ⟨⟨hi.2, h1⟩, h2⟩
  · rintro ⟨j, i⟩ hp
    simp only [mem_filter, mem_product, mem_range] at hp
    obtain ⟨⟨hj, hi⟩, hs⟩ := hp
    obtain ⟨-, h2, h3, -⟩ := wf_port hwf hj hi (hs ▸ ht)
    subst hs
    simp only [h2, h3]
  · intro i hi
    simp only [mem_filter, mem_range, valid, decide_eq_true_eq] at hi
    exact (wf_port hwf ht hi.1 hi.2).2.2.1
  · rintro ⟨j, i⟩ hp
    simp only [mem_filter, mem_product, mem_range] at hp
    obtain ⟨⟨hj, hi⟩, hs⟩ := hp
    obtain ⟨-, h2, h3, -⟩ := wf_port hwf hj hi (hs ▸ ht)
    subst hs
    simp only [h2, h3]

/-- On a link that is port `i`, the total is the value of port `i`. -/
theorem linkN_port (hwf : G.wfCheck = true) (T : ℕ → ℕ → ℕ) {j i : ℕ} (hj : j < G.n)
    (hi : i < G.P) (hv : G.step j i < G.n) : G.linkN T j (G.step j i) = T j i := by
  unfold linkN
  rw [sum_eq_single_of_mem i (mem_range.2 hi) fun i' hi' hne =>
    ite_eq_right fun he => hne ((wf_port hwf hj hi hv).2.2.2 i' (mem_range.1 hi') he)]
  simp

/-- Off the ports, the total is zero. -/
theorem linkN_eq_zero (T : ℕ → ℕ → ℕ) {j t : ℕ} (h : G.adj j t = false) :
    G.linkN T j t = 0 := by
  unfold linkN
  refine sum_eq_zero fun i hi => ite_eq_right fun he => ?_
  have : G.adj j t = true := adj_iff.2 ⟨i, mem_range.1 hi, he⟩
  rw [h] at this; exact Bool.noConfusion this

/-- The rate leaving `u`. -/
theorem sum_portVal_out (T : ℕ → ℕ → ℕ) (D : ℕ) (u : Fin G.n) :
    ∑ v, G.portVal T D u v = (G.outN T u : ℚ) / D := by
  unfold portVal
  rw [← sum_div_q, Fin.sum_univ_eq_sum_range (fun v => (G.linkN T u v : ℚ)), ← Nat.cast_sum,
    sum_linkN_out]

/-- The rate entering `v`. -/
theorem sum_portVal_in (hwf : G.wfCheck = true) (T : ℕ → ℕ → ℕ) (D : ℕ) (v : Fin G.n) :
    ∑ u, G.portVal T D u v = (G.inN T v : ℚ) / D := by
  unfold portVal
  rw [← sum_div_q, Fin.sum_univ_eq_sum_range (fun u => (G.linkN T u v : ℚ)), ← Nat.cast_sum,
    sum_linkN_in hwf T v.isLt]

/-! ### The primal certificate -/

variable (G)

/-- Conservation of every commodity `d` at every vertex `j ≠ d`, with throughput `p / q` and the
demand `demN j d / R`, for the port table `g d j i / D`. -/
def consCheck (g : ℕ → ℕ → ℕ → ℕ) (D : ℕ) (demN : ℕ → ℕ → ℕ) (R p q : ℕ) : Bool :=
  allBelow G.n fun d => allBelow G.n fun j =>
    j == d || q * R * G.outN (g d) j == q * R * G.inN (g d) j + p * D * demN j d

/-- Every port carries at most `C D` in total over the commodities. -/
def capCheck (C : ℕ) (g : ℕ → ℕ → ℕ → ℕ) (D : ℕ) : Bool :=
  allBelow G.n fun j => allBelow G.P fun i =>
    !G.valid j i || decide (sumBelow G.n (fun d => g d j i) ≤ C * D)

/-- Every used port brings its commodity strictly closer to its destination. -/
def minCheck (g : ℕ → ℕ → ℕ → ℕ) : Bool :=
  allBelow G.n fun d => allBelow G.n fun j => allBelow G.P fun i =>
    g d j i == 0 || !G.valid j i || G.near d j i

variable {G}

/-- **The primal certificate.**  A port table passing `consCheck` and `capCheck` is a flow of
`θ * dem` in `G.net C`, for `θ = p / q` and `dem s d = demN s d / R`. -/
def certFlow (C : ℕ) (hwf : G.wfCheck = true) (dem : Fin G.n → Fin G.n → ℚ)
    (demN : ℕ → ℕ → ℕ) (R : ℕ) (hdem : ∀ s d, dem s d = (demN s d : ℚ) / R)
    (g : ℕ → ℕ → ℕ → ℕ) (D p q : ℕ) {θ : ℚ} (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D)
    (hq : 0 < q) (hc : G.consCheck g D demN R p q = true) (hcap : G.capCheck C g D = true) :
    Flow (G.net C) dem θ where
  f d u v := G.portVal (g d) D u v
  nonneg d u v := portVal_nonneg _ _ _ _
  conserve d v hv := by
    rw [sum_portVal_out, sum_portVal_in hwf, hdem, hθ]
    have := allBelow_iff.1 (allBelow_iff.1 hc d d.isLt) v v.isLt
    have hne : (v : ℕ) ≠ d := fun h => hv (Fin.ext h)
    simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or] at this
    have hQ : ((q * R * G.outN (g d) v : ℕ) : ℚ) =
        ((q * R * G.inN (g d) v + p * D * demN v d : ℕ) : ℚ) := by
      rw [this]
    push_cast at hQ
    have hR' : (0 : ℚ) < R := by exact_mod_cast hR
    have hD' : (0 : ℚ) < D := by exact_mod_cast hD
    have hq' : (0 : ℚ) < q := by exact_mod_cast hq
    have hdiff : (G.outN (g d) v : ℚ) - G.inN (g d) v = p * D * demN v d / (q * R) := by
      rw [eq_div_iff (mul_pos hq' hR').ne']; linarith
    rw [div_sub_div_same, hdiff, div_eq_iff hD'.ne']
    ring
  capacity u v := by
    show _ ≤ ite _ _ _
    split_ifs with hadj
    · obtain ⟨i, hi, hs⟩ := adj_iff.1 hadj
      have hv : G.step u i < G.n := hs ▸ v.isLt
      simp only [portVal, ← hs, linkN_port hwf _ u.isLt hi hv]
      rw [← sum_div_q, Fin.sum_univ_eq_sum_range (fun d => ((g d u i : ℕ) : ℚ)), ← Nat.cast_sum,
        ← sumBelow_eq]
      have := allBelow_iff.1 (allBelow_iff.1 hcap u u.isLt) i hi
      simp only [valid, hv, decide_true, Bool.not_true, Bool.false_or,
        decide_eq_true_eq] at this
      have hD' : (0 : ℚ) < D := by exact_mod_cast hD
      rw [div_le_iff₀ hD']
      exact_mod_cast this
    · simp only [Bool.not_eq_true] at hadj
      simp [portVal, linkN_eq_zero _ hadj]

/-- **The primal certificate is minimal** when it passes `minCheck`. -/
theorem certFlow_minimal (C : ℕ) (hwf : G.wfCheck = true) (dem : Fin G.n → Fin G.n → ℚ)
    (demN : ℕ → ℕ → ℕ) (R : ℕ) (hdem : ∀ s d, dem s d = (demN s d : ℚ) / R)
    (g : ℕ → ℕ → ℕ → ℕ) (D p q : ℕ) {θ : ℚ} (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D)
    (hq : 0 < q) (hc : G.consCheck g D demN R p q = true) (hcap : G.capCheck C g D = true)
    (hnear : G.nearCheck = true) (hm : G.minCheck g = true) :
    (certFlow C hwf dem demN R hdem g D p q hθ hR hD hq hc hcap).Minimal G.dq := by
  intro d u v hpos
  change 0 < G.portVal (g d) D u v at hpos
  have hl : G.linkN (g d) u v ≠ 0 := by
    intro h0; simp [portVal, h0] at hpos
  obtain ⟨i, hi, hne⟩ := exists_ne_zero_of_sum_ne_zero hl
  have hs : G.step u i = v := by
    by_contra h; exact hne (by simp [h])
  have hg : g d u i ≠ 0 := by
    intro h0; exact hne (by simp [h0])
  have hv : G.step u i < G.n := hs ▸ v.isLt
  have := allBelow_iff.1 (allBelow_iff.1 (allBelow_iff.1 hm d d.isLt) u u.isLt) i
    (mem_range.1 hi)
  simp only [valid, hv, decide_true, Bool.not_true, Bool.or_false, Bool.or_eq_true, beq_iff_eq,
    hg, false_or] at this
  have h := (near_iff hnear d.isLt u.isLt (mem_range.1 hi) hv).1 this
  rw [hs] at h
  show (G.dist v d : ℚ) < G.dist u d
  exact_mod_cast h

/-! ### The dual certificate -/

variable (G)

/-- The potentials `phi d j` vanish at the destination and drop by at most `lenT j i` along every
port `i` (every port that brings `d` closer, when `minimal`). -/
def dualCheck (phi lenT : ℕ → ℕ → ℕ) (minimal : Bool) : Bool :=
  allBelow G.n (fun d => phi d d == 0) &&
  allBelow G.n fun d => allBelow G.n fun j => allBelow G.P fun i =>
    !G.valid j i || (minimal && !G.near d j i) ||
      decide (phi d j ≤ phi d (G.step j i) + lenT j i)

/-- The total length of the ports. -/
def lenSum (lenT : ℕ → ℕ → ℕ) : ℕ := sumBelow G.n (G.outN lenT)

/-- `R * ∑ dem * phi`. -/
def demPhi (demN phi : ℕ → ℕ → ℕ) : ℕ :=
  sumBelow G.n fun s => sumBelow G.n fun d => demN s d * phi d s

/-- The bound `C * lenSum * R / demPhi ≤ p / q`. -/
def boundCheck (C : ℕ) (demN phi lenT : ℕ → ℕ → ℕ) (R p q : ℕ) : Bool :=
  decide (0 < G.demPhi demN phi) && decide (C * G.lenSum lenT * R * q ≤ p * G.demPhi demN phi)

variable {G}

/-- **The dual certificate, for anything respecting the potential bounds.**  If `dualCheck` and
`boundCheck` pass, every `θ` such that `θ * dem` respects the potential bounds of `G.net C` (on
the minimal links, when `minimal`; `Fluid.PotentialFeasibleOn`) has `θ ≤ p / q`.  Flows do; so
do stable queueing runs. -/
theorem upper_of_check' (C : ℕ) (hwf : G.wfCheck = true) (hnear : G.nearCheck = true)
    (dem : Fin G.n → Fin G.n → ℚ) (demN : ℕ → ℕ → ℕ) (R : ℕ)
    (hdem : ∀ s d, dem s d = (demN s d : ℚ) / R) (phi lenT : ℕ → ℕ → ℕ) (minimal : Bool) (p q : ℕ) (hR : 0 < R) (hq : 0 < q)
    (hd : G.dualCheck phi lenT minimal = true) (hb : G.boundCheck C demN phi lenT R p q = true)
    {θ : ℚ}
    (hP : PotentialFeasibleOn (G.net C) (fun d u v => minimal = false ∨ G.dq v d < G.dq u d)
      dem θ) :
    θ ≤ (p : ℚ) / q := by
  simp only [dualCheck, Bool.and_eq_true] at hd
  obtain ⟨hd0, hd1⟩ := hd
  simp only [boundCheck, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hA, hCA⟩ := hb
  have key := hP (G.portVal lenT 1) (fun d v => (phi d v : ℚ)) (portVal_nonneg _ _)
    (fun d => by
      have := allBelow_iff.1 hd0 d d.isLt
      simp only [beq_iff_eq] at this
      simp [this])
    (fun d u v hS hcap => by
      have hadj : G.adj u v = true := by
        by_contra hn
        exact absurd hcap (by show ¬ 0 < ite _ _ _; simp [hn])
      obtain ⟨i, hi, hs⟩ := adj_iff.1 hadj
      have hv : G.step u i < G.n := hs ▸ v.isLt
      simp only [portVal, ← hs, linkN_port hwf _ u.isLt hi hv, Nat.cast_one, div_one]
      have := allBelow_iff.1 (allBelow_iff.1 (allBelow_iff.1 hd1 d d.isLt) u u.isLt) i hi
      have hcl : ¬ (minimal = true ∧ G.near d u i = false) := by
        rintro ⟨hm, hn⟩
        rcases hS with h | h
        · rw [hm] at h; exact Bool.noConfusion h
        · simp only [dq, ← hs] at h
          have := (near_iff hnear d.isLt u.isLt hi hv).2 (by exact_mod_cast h)
          rw [hn] at this; exact Bool.noConfusion this
      simp only [valid, hv, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
      rcases this with h | h
      · exact absurd h hcl
      · have : ((phi d u : ℕ) : ℚ) ≤ ((phi d (G.step u i) + lenT u i : ℕ) : ℚ) := by
          exact_mod_cast h
        push_cast at this
        linarith) (fun d v => Nat.cast_nonneg _)
  -- evaluate the two sides
  have hL : ∑ s, ∑ d, dem s d * (phi d s : ℚ) = (G.demPhi demN phi : ℚ) / R := by
    simp only [hdem, demPhi, sumBelow_eq]
    push_cast
    rw [sum_div_q,
      Fin.sum_univ_eq_sum_range (fun s => ∑ d : Fin G.n, (demN s d : ℚ) / R * (phi d s : ℚ))]
    refine sum_congr rfl fun j _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun e => (demN j e : ℚ) / R * (phi e j : ℚ)), sum_div_q]
    exact sum_congr rfl fun _ _ => by ring
  have hC : ∑ u, ∑ v, (G.net C).cap u v * G.portVal lenT 1 u v = C * (G.lenSum lenT : ℚ) := by
    have : ∀ u v : Fin G.n, (G.net C).cap u v * G.portVal lenT 1 u v =
        C * G.portVal lenT 1 u v := by
      intro u v
      show ite _ _ _ * _ = _
      split_ifs with hadj
      · rfl
      · simp only [Bool.not_eq_true] at hadj
        simp [portVal, linkN_eq_zero _ hadj]
    simp only [this, ← mul_sum, sum_portVal_out, Nat.cast_one, div_one, lenSum, sumBelow_eq]
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun j => (G.outN lenT j : ℚ))]
  rw [hL, hC] at key
  have hR' : (0 : ℚ) < R := by exact_mod_cast hR
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hA' : (0 : ℚ) < G.demPhi demN phi := by exact_mod_cast hA
  have hCA' : (C : ℚ) * G.lenSum lenT * R * q ≤ p * G.demPhi demN phi := by exact_mod_cast hCA
  rw [le_div_iff₀ hq']
  have h1 : θ * G.demPhi demN phi ≤ C * G.lenSum lenT * R := by
    have := mul_le_mul_of_nonneg_right key hR'.le
    rwa [mul_assoc, div_mul_cancel₀ _ hR'.ne'] at this
  nlinarith

/-- **The dual certificate.**  If `dualCheck` and `boundCheck` pass, every flow of `θ * dem`
(every minimal one, when `minimal`) has `θ ≤ p / q`. -/
theorem upper_of_check (C : ℕ) (hwf : G.wfCheck = true) (hnear : G.nearCheck = true)
    (dem : Fin G.n → Fin G.n → ℚ) (demN : ℕ → ℕ → ℕ) (R : ℕ)
    (hdem : ∀ s d, dem s d = (demN s d : ℚ) / R) (phi lenT : ℕ → ℕ → ℕ) (minimal : Bool)
    (p q : ℕ) (hR : 0 < R) (hq : 0 < q)
    (hd : G.dualCheck phi lenT minimal = true) (hb : G.boundCheck C demN phi lenT R p q = true)
    {θ : ℚ} (F : Flow (G.net C) dem θ) (hF : minimal = true → F.Minimal G.dq) :
    θ ≤ (p : ℚ) / q :=
  upper_of_check' C hwf hnear dem demN R hdem phi lenT minimal p q hR hq hd hb
    (F.potentialFeasibleOn fun d u v h => by
      cases minimal with
      | false => exact Or.inl rfl
      | true => exact Or.inr (hF rfl d u v h))

/-! ### Exact optima on the port graph's network -/

/-- **The exact optimum over all routings** on `G.net C`: a primal and a dual certificate for the
same `θ = p / q`. -/
theorem isGreatest_routable (C : ℕ) (hwf : G.wfCheck = true) (hnear : G.nearCheck = true)
    (dem : Fin G.n → Fin G.n → ℚ)
    (demN : ℕ → ℕ → ℕ) (R : ℕ) (hdem : ∀ s d, dem s d = (demN s d : ℚ) / R)
    (g : ℕ → ℕ → ℕ → ℕ) (D : ℕ) (phi lenT : ℕ → ℕ → ℕ) (p q : ℕ) {θ : ℚ}
    (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D) (hq : 0 < q)
    (hc : G.consCheck g D demN R p q = true) (hcap : G.capCheck C g D = true)
    (hd : G.dualCheck phi lenT false = true) (hb : G.boundCheck C demN phi lenT R p q = true) :
    IsGreatest {θ | Routable (G.net C) dem θ} θ :=
  ⟨⟨certFlow C hwf dem demN R hdem g D p q hθ hR hD hq hc hcap⟩, fun _ ⟨F⟩ =>
    hθ ▸ upper_of_check C hwf hnear dem demN R hdem phi lenT false p q hR hq hd hb F
      (fun h => Bool.noConfusion h)⟩

/-- **The exact optimum over minimal routings** on `G.net C`: a minimal primal certificate and a
dual certificate on the minimal links for the same `θ = p / q`. -/
theorem isGreatest_minimal (C : ℕ) (hwf : G.wfCheck = true) (hnear : G.nearCheck = true)
    (dem : Fin G.n → Fin G.n → ℚ)
    (demN : ℕ → ℕ → ℕ) (R : ℕ) (hdem : ∀ s d, dem s d = (demN s d : ℚ) / R)
    (g : ℕ → ℕ → ℕ → ℕ) (D : ℕ) (phi lenT : ℕ → ℕ → ℕ) (p q : ℕ) {θ : ℚ}
    (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D) (hq : 0 < q)
    (hc : G.consCheck g D demN R p q = true) (hcap : G.capCheck C g D = true)
    (hm : G.minCheck g = true) (hd : G.dualCheck phi lenT true = true)
    (hb : G.boundCheck C demN phi lenT R p q = true) :
    IsGreatest {θ | ∃ F : Flow (G.net C) dem θ, F.Minimal G.dq} θ :=
  ⟨⟨_, certFlow_minimal C hwf dem demN R hdem g D p q hθ hR hD hq hc hcap hnear hm⟩,
    fun _ ⟨F, hF⟩ =>
      hθ ▸ upper_of_check C hwf hnear dem demN R hdem phi lenT true p q hR hq hd hb F
        (fun _ => hF)⟩

end PortGraph

/-! ### Networks isomorphic to a port graph's -/

open PortGraph

/-- A **model** of the port graph `G` (with capacity `C`): a network `N` on `V` with a distance
`dist`, isomorphic to `G.net C` with the distance `G.dq` through the bijection `e`. -/
structure Model {V : Type*} [Fintype V] (G : PortGraph) (C : ℕ) (N : Net V)
    (dist : V → V → ℚ) where
  /-- The index of every vertex. -/
  e : V ≃ Fin G.n
  cap_eq : ∀ u v, N.cap u v = (G.net C).cap (e u) (e v)
  dist_eq : ∀ u v, dist u v = G.dq (e u) (e v)
  wf : G.wfCheck = true
  near : G.nearCheck = true

namespace Model

variable {V : Type*} [Fintype V] {G : PortGraph} {C : ℕ} {N : Net V} {dist : V → V → ℚ}

/-- **The exact optimum over all routings** on a model: a primal and a dual certificate for the
same `θ = p / q`, for a demand given on the indices. -/
theorem isGreatest_routable (M : Model G C N dist)
    (dem : V → V → ℚ) (demN : ℕ → ℕ → ℕ) (R : ℕ)
    (hdem : ∀ s d, dem s d = (demN (M.e s) (M.e d) : ℚ) / R)
    (g : ℕ → ℕ → ℕ → ℕ) (D : ℕ) (phi lenT : ℕ → ℕ → ℕ) (p q : ℕ) {θ : ℚ}
    (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D) (hq : 0 < q)
    (hc : G.consCheck g D demN R p q = true) (hcap : G.capCheck C g D = true)
    (hd : G.dualCheck phi lenT false = true) (hb : G.boundCheck C demN phi lenT R p q = true) :
    IsGreatest {θ | Routable N dem θ} θ := by
  have h := PortGraph.isGreatest_routable C M.wf M.near (fun a b => (demN a b : ℚ) / R) demN R
    (fun _ _ => rfl) g D phi lenT p q hθ hR hD hq hc hcap hd hb
  have e : {θ | Routable N dem θ} = {θ | Routable (G.net C) (fun a b => (demN a b : ℚ) / R) θ} :=
    Set.ext fun _ => routable_congr M.e M.cap_eq hdem
  rwa [e]

/-- **A minimal flow** on a model from a primal certificate passing `minCheck`. -/
theorem exists_minimal (M : Model G C N dist)
    (dem : V → V → ℚ) (demN : ℕ → ℕ → ℕ) (R : ℕ)
    (hdem : ∀ s d, dem s d = (demN (M.e s) (M.e d) : ℚ) / R)
    (g : ℕ → ℕ → ℕ → ℕ) (D p q : ℕ) {θ : ℚ} (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D)
    (hq : 0 < q) (hc : G.consCheck g D demN R p q = true) (hcap : G.capCheck C g D = true)
    (hm : G.minCheck g = true) :
    ∃ F : Flow N dem θ, F.Minimal dist :=
  (minimal_congr M.e M.cap_eq hdem M.dist_eq).2
    ⟨_, certFlow_minimal C M.wf (fun a b => (demN a b : ℚ) / R) demN R (fun _ _ => rfl) g D p
      q hθ hR hD hq hc hcap M.near hm⟩

/-- **The exact optimum over minimal routings** on a model: a minimal primal certificate and a
dual certificate on the minimal links for the same `θ = p / q`. -/
theorem isGreatest_minimal (M : Model G C N dist)
    (dem : V → V → ℚ) (demN : ℕ → ℕ → ℕ) (R : ℕ)
    (hdem : ∀ s d, dem s d = (demN (M.e s) (M.e d) : ℚ) / R)
    (g : ℕ → ℕ → ℕ → ℕ) (D : ℕ) (phi lenT : ℕ → ℕ → ℕ) (p q : ℕ) {θ : ℚ}
    (hθ : θ = (p : ℚ) / q) (hR : 0 < R) (hD : 0 < D) (hq : 0 < q)
    (hc : G.consCheck g D demN R p q = true) (hcap : G.capCheck C g D = true)
    (hm : G.minCheck g = true) (hd : G.dualCheck phi lenT true = true)
    (hb : G.boundCheck C demN phi lenT R p q = true) :
    IsGreatest {θ | ∃ F : Flow N dem θ, F.Minimal dist} θ := by
  have h := PortGraph.isGreatest_minimal C M.wf M.near (fun a b => (demN a b : ℚ) / R) demN R
    (fun _ _ => rfl) g D phi lenT p q hθ hR hD hq hc hcap hm hd hb
  have e : {θ | ∃ F : Flow N dem θ, F.Minimal dist} =
      {θ | ∃ F : Flow (G.net C) (fun a b => (demN a b : ℚ) / R) θ, F.Minimal G.dq} :=
    Set.ext fun _ => minimal_congr M.e M.cap_eq hdem M.dist_eq
  rwa [e]

end Model

/-! ### The torus -/

/-- The end of port `i` of the vertex of index `j = x + k y` of the `k × k` torus: `0`: `x + 1`,
`1`: `x - 1`, `2`: `y + 1`, `3`: `y - 1`, mod `k`. -/
def torusStep (k j : ℕ) : ℕ → ℕ
  | 0 => (j % k + 1) % k + k * (j / k)
  | 1 => (j % k + (k - 1)) % k + k * (j / k)
  | 2 => j % k + k * ((j / k + 1) % k)
  | _ => j % k + k * ((j / k + (k - 1)) % k)

/-- The port back on the torus: the opposite direction. -/
def torusBack : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | _ => 2

/-- On a ring of length `k`, moving `a` forward brings it closer to `b`: `b - a - 1 mod k` is
below `k / 2` (for `a, b < k`). -/
def ringNear (k a b : ℕ) : Bool := decide ((b + 2 * k - 1 - a) % k < k / 2)

/-- Port `i` of the vertex of index `j` brings the destination `d` closer on the torus. -/
def torusNear (k d j : ℕ) : ℕ → Bool
  | 0 => ringNear k (j % k) (d % k)
  | 1 => ringNear k (d % k) (j % k)
  | 2 => ringNear k (j / k) (d / k)
  | _ => ringNear k (d / k) (j / k)

/-- The ring distance of `a` and `b` mod `k`. -/
def ringN (k a b : ℕ) : ℕ := min ((a + k - b) % k) ((b + k - a) % k)

/-- The hop distance of the torus on indices. -/
def torusDistN (k a b : ℕ) : ℕ := ringN k (a % k) (b % k) + ringN k (a / k) (b / k)

/-- **The `k × k` torus as a port graph.** -/
def torusGraph (k : ℕ) : PortGraph where
  n := k * k
  P := 4
  step := torusStep k
  back _ := torusBack
  dist := torusDistN k
  near := torusNear k

/-- The index `x + k y` of the vertex `(x, y)` of the torus. -/
def torusEquiv (k : ℕ) : Fin k × Fin k ≃ Fin (k * k) :=
  (Equiv.prodComm _ _).trans finProdFinEquiv

/-- The index of `(x, y)` is `x + k y`. -/
theorem torusEquiv_val {k : ℕ} (v : Fin k × Fin k) : (torusEquiv k v : ℕ) = idx v := by
  simp [torusEquiv, idx, finProdFinEquiv_apply_val]

/-- The distance table of `torusGraph k` is the hop distance of the torus. -/
theorem torusDistN_idx {k : ℕ} (u v : Fin k × Fin k) :
    torusDistN k (idx u) (idx v) = ringDist u.1 v.1 + ringDist u.2 v.2 := by
  simp only [torusDistN, idx_mod, idx_div]
  rfl

/-- Kernel check: the port table of the `8 × 8` torus is well formed. -/
theorem torusGraph8_wf : (torusGraph 8).wfCheck = true := by decide +kernel

/-- Kernel check: `torusNear` says which ports of the `8 × 8` torus bring a vertex closer. -/
theorem torusGraph8_near : (torusGraph 8).nearCheck = true := by decide +kernel

/-- Kernel check: the ports of the `8 × 8` torus join the vertices at distance `1`. -/
theorem torusGraph8_adj : (torusGraph 8).adjCheck = true := by decide +kernel

/-- Torus neighbours are the vertices at distance `1` (for `k = 8`, by evaluation). -/
theorem torusAdj8_iff (u v : Fin 8 × Fin 8) :
    TorusAdj u v ↔ ringDist u.1 v.1 + ringDist u.2 v.2 = 1 := by
  revert u v
  decide +kernel

/-- The distance table of `torusGraph k` on the indices of two vertices. -/
theorem torusGraph_dist {k : ℕ} (u v : Fin k × Fin k) :
    (torusGraph k).dist (torusEquiv k u) (torusEquiv k v) =
      ringDist u.1 v.1 + ringDist u.2 v.2 := by
  have h1 := torusEquiv_val u
  have h2 := torusEquiv_val v
  show torusDistN k _ _ = _
  rw [h1, h2]
  exact torusDistN_idx u v

/-- **The `8 × 8` torus is a model of `torusGraph 8`**: `torusNet 8` with `torusDist`, vertex
`(x, y)` having the index `x + 8 y`. -/
def torusModel : Model (torusGraph 8) 2 (torusNet 8) torusDist where
  e := torusEquiv 8
  cap_eq u v := by
    have h : TorusAdj u v ↔ (torusGraph 8).adj (torusEquiv 8 u) (torusEquiv 8 v) = true :=
      (torusAdj8_iff u v).trans ((torusGraph_dist u v).symm ▸
        (adj_iff_dist torusGraph8_adj (torusEquiv 8 u).isLt (torusEquiv 8 v).isLt).symm)
    exact if_congr h (by norm_num) rfl
  dist_eq u v := by
    simp only [torusDist, dq]
    exact congrArg _ (torusGraph_dist u v).symm
  wf := torusGraph8_wf
  near := torusGraph8_near

/-! ### The hypercube -/

/-- The index `∑ i, u i 2^i` of the vertex `u` of the hypercube: **coordinate `i` is bit `i`**. -/
def cubeEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- Bit `i` of the index of `u` is `u i`. -/
theorem cubeEquiv_bit {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    (cubeEquiv n u : ℕ) / 2 ^ (i : ℕ) % 2 = if u i then 1 else 0 := by
  have h := congrArg (fun f => ((f i : Fin 2) : ℕ))
    (finFunctionFinEquiv.symm_apply_apply ((Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm) u))
  simp only [finFunctionFinEquiv_symm_apply_val] at h
  rw [cubeEquiv, Equiv.trans_apply, h]
  simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Function.comp_apply, Equiv.refl_apply]
  cases u i <;> rfl

/-- The hop distance of the hypercube on indices: the number of bits in which they differ. -/
def cubeDistN (n a b : ℕ) : ℕ := sumBelow n fun i => (a / 2 ^ i + b / 2 ^ i) % 2

/-- **The `n`-dimensional hypercube as a port graph**: port `i` flips bit `i`, and brings `d`
closer if bit `i` of the vertex differs from that of `d`. -/
def cubeGraph (n : ℕ) : PortGraph where
  n := 2 ^ n
  P := n
  step j i := j ^^^ 2 ^ i
  back _ i := i
  dist := cubeDistN n
  near d j i := decide ((j / 2 ^ i + d / 2 ^ i) % 2 = 1)

/-- The distance table of `cubeGraph n` counts the coordinates in which the vertices differ. -/
theorem cubeDistN_equiv {n : ℕ} (u v : Fin n → Bool) :
    cubeDistN n (cubeEquiv n u) (cubeEquiv n v) = (cubeDiff u v).card := by
  rw [cubeDistN, sumBelow_eq, cubeDiff, card_filter, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  have key : ((cubeEquiv n u : ℕ) / 2 ^ (i : ℕ) + (cubeEquiv n v : ℕ) / 2 ^ (i : ℕ)) % 2 =
      if u i = v i then 0 else 1 := by
    rw [Nat.add_mod, cubeEquiv_bit, cubeEquiv_bit]
    cases u i <;> cases v i <;> rfl
  rw [key]
  by_cases h : u i = v i <;> simp [h]

/-- Kernel check: the port table of the 6-dimensional hypercube is well formed. -/
theorem cubeGraph6_wf : (cubeGraph 6).wfCheck = true := by decide +kernel

/-- Kernel check: the ports of the 6-dimensional hypercube that bring a vertex closer. -/
theorem cubeGraph6_near : (cubeGraph 6).nearCheck = true := by decide +kernel

/-- Kernel check: the ports of the 6-dimensional hypercube join the vertices at distance `1`. -/
theorem cubeGraph6_adj : (cubeGraph 6).adjCheck = true := by decide +kernel

/-- **The 6-dimensional hypercube is a model of `cubeGraph 6`**: `cubeNet 6` with `cubeDist`,
vertex `u` having the index `∑ i, u i 2^i`. -/
def cubeModel : Model (cubeGraph 6) 2 (cubeNet 6) cubeDist where
  e := cubeEquiv 6
  cap_eq u v := by
    have h : CubeAdj u v ↔ (cubeGraph 6).adj (cubeEquiv 6 u) (cubeEquiv 6 v) = true :=
      (cubeDistN_equiv u v ▸ Iff.rfl :
        CubeAdj u v ↔ cubeDistN 6 (cubeEquiv 6 u) (cubeEquiv 6 v) = 1).trans
        (adj_iff_dist cubeGraph6_adj (cubeEquiv 6 u).isLt (cubeEquiv 6 v).isLt).symm
    exact if_congr h (by norm_num) rfl
  dist_eq u v := by
    simp only [cubeDist, dq]
    exact congrArg _ (cubeDistN_equiv u v).symm
  wf := cubeGraph6_wf
  near := cubeGraph6_near

end GraphCert

end Fluid

end AsyncLean
