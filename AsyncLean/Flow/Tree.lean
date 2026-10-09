/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Topologies
import Mathlib.Logic.Relation

/-!
# Detours never help for any traffic if and only if the network is a tree

A finite simple graph (`UGraph`) gives a network in the fluid model (`UGraph.net c`): capacity
`c > 0` in both directions of every edge.  A routing is **minimal** (`Flow.Minimal`) for the hop
distance `D` of the graph (`UGraph.IsHopDist`: the Bellman–Ford equations; `UGraph.hopDist`, the
length of a shortest walk, satisfies them on a connected graph, `isHopDist_hopDist`) if every
link it uses brings the traffic one hop closer to its destination.  Detours never help for a
traffic matrix `dem` if every throughput routable for `dem` is reached by a minimal flow.

A **tree** (`UGraph.IsTree`) is a connected graph whose every edge is a bridge (`AllBridges`:
removing the edge `{u, v}` disconnects `u` from `v`; equivalently, no edge lies on a cycle).

* `UGraph.AllBridges.minimal_of_routable` (and `UGraph.IsTree.minimal_of_routable`) :
  **trees: detours never help.**  For every nonnegative traffic matrix and every `θ ≥ 0`
  routable in a tree, the **tree flow** (`treeFlowF`: every vertex forwards each commodity to its
  unique next hop) routes it at `θ`, minimally.  On the link `a → b` it carries `θ` times the
  traffic from `a`'s side of the edge to `b`'s side; that side's only outgoing link is `a → b`
  (`AllBridges.cut_unique`), so the cut bound (`cut_bound`) keeps it within `c`.  The local
  facts behind it: the two ends of an edge are never at the same distance from a vertex
  (`AllBridges.ne_of_adj`), and every vertex has a unique next hop towards every other
  (`AllBridges.unique_desc`); both hold because two different descents would close a cycle.
* `UGraph.IsHopDist.detour_helps` : **cycles: detours help.**  If the edge `u — v` lies on a
  cycle, the single-pair traffic `u → v` (`pairDem`) is routable at `2c` (`c` on the edge, `c`
  around the cycle along a path, `exists_pathFlow`), but every minimal flow reaches at most `c`
  (`minimal_pair_le`: the edge is the only shortest path).
* `UGraph.IsHopDist.minimal_optimal_iff`, `UGraph.minimal_optimal_iff_isTree` : **the
  characterisation.**  For a connected graph with its hop distance:
  `(∀ dem ≥ 0, ∀ θ ≥ 0, Routable dem θ → ∃ minimal flow at θ) ↔ IsTree`.
* Examples: the path on `Fin k` is a tree (`pathGraph_isTree`, `path_minimal_optimal`); the
  4-cycle is not (`cycle4_not_isTree`), and on it the traffic `0 → 1` is routable at `2c` while
  minimal flows reach only `c` (`cycle4_detour`).

All results are over `ℚ` and general in the graph, the capacity and the traffic matrix.
-/

namespace AsyncLean

namespace Fluid

open Finset

variable {V : Type*}

/-- A finite simple graph: a symmetric, irreflexive adjacency relation. -/
structure UGraph (V : Type*) where
  /-- The adjacency relation. -/
  Adj : V → V → Prop
  /-- Edges are undirected. -/
  symm : ∀ u v, Adj u v → Adj v u
  /-- There are no loops. -/
  irrefl : ∀ v, ¬ Adj v v

namespace UGraph

variable (G : UGraph V)

/-- The graph is connected: every two vertices are joined by a walk. -/
def Connected : Prop := ∀ u v, Relation.ReflTransGen G.Adj u v

/-- The graph with the edge `{u, v}` removed. -/
def del (u v : V) (x y : V) : Prop := G.Adj x y ∧ ¬ (x = u ∧ y = v) ∧ ¬ (x = v ∧ y = u)

/-- Every edge is a bridge: removing the edge `{u, v}` disconnects `u` from `v`.  Equivalently,
no edge lies on a cycle: the graph is acyclic (a forest). -/
def AllBridges : Prop := ∀ u v, G.Adj u v → ¬ Relation.ReflTransGen (G.del u v) u v

/-- **A tree**: a connected graph in which every edge is a bridge (a minimally connected graph;
equivalently a connected acyclic graph). -/
def IsTree : Prop := G.Connected ∧ G.AllBridges

/-- `D` is the **hop distance** of the graph (`D v d`: the number of hops from `v` to `d`), given
by the Bellman–Ford equations: `D d d = 0`, `D v d ≤ D w d + 1` for every neighbour `w` of `v`,
and for `v ≠ d` some neighbour attains it. -/
structure IsHopDist (D : V → V → ℕ) : Prop where
  /-- A vertex is at distance `0` from itself. -/
  self : ∀ d, D d d = 0
  /-- One hop increases the distance by at most one. -/
  step : ∀ u v d, G.Adj u v → D u d ≤ D v d + 1
  /-- Away from `d`, some neighbour is one hop closer to `d`. -/
  descend : ∀ v d, v ≠ d → ∃ w, G.Adj v w ∧ D w d + 1 = D v d

variable {G}

/-- Removing an edge keeps the graph symmetric. -/
theorem del_symm {u v x y : V} (h : G.del u v x y) : G.del u v y x :=
  ⟨G.symm _ _ h.1, fun h' => h.2.2 ⟨h'.2, h'.1⟩, fun h' => h.2.1 ⟨h'.2, h'.1⟩⟩

/-- A walk of a symmetric relation can be reversed. -/
theorem rtg_symm {r : V → V → Prop} (hr : ∀ x y, r x y → r y x) {a b : V}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact .head (hr _ _ hbc) ih

/-- A walk of a relation is a walk of every larger relation. -/
theorem rtg_mono {r s : V → V → Prop} (hrs : ∀ x y, r x y → s x y) {a b : V}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen s a b := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (hrs _ _ hbc)

/-- A property preserved by every step holds all along a walk. -/
theorem rtg_invariant {r : V → V → Prop} (P : V → Prop) (hP : ∀ x y, r x y → P x → P y)
    {a b : V} (h : Relation.ReflTransGen r a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hP _ _ hbc ih

namespace IsHopDist

variable {D : V → V → ℕ} (hD : G.IsHopDist D)
include hD

/-- Only `d` is at distance `0` from `d`. -/
theorem eq_of_zero {x d : V} (h : D x d = 0) : x = d := by
  by_contra hx
  obtain ⟨w, -, hw⟩ := hD.descend x d hx
  omega

/-- The hop distance is symmetric (one inequality): walking down from `d` to `u` takes
`D d u` hops, and each hop moves at most one away from `d`. -/
theorem symm_le (u d : V) : D u d ≤ D d u := by
  suffices key : ∀ n x, D x u = n → D u d ≤ D x d + n by
    have := key _ d rfl; rw [hD.self] at this; omega
  intro n
  induction n with
  | zero => intro x hx; rw [hD.eq_of_zero hx]; omega
  | succ n ih =>
    intro x hx
    have hxu : x ≠ u := by rintro rfl; rw [hD.self] at hx; omega
    obtain ⟨w, hw, hwd⟩ := hD.descend x u hxu
    have := ih w (by omega)
    have := hD.step w x d (G.symm _ _ hw)
    omega

/-- The hop distance is symmetric. -/
theorem symm (u d : V) : D u d = D d u := le_antisymm (hD.symm_le u d) (hD.symm_le d u)

/-- Walking down the distance to `x`, staying below `m`, reaches `x`. -/
theorem reach_desc (x : V) (m : ℕ) : ∀ a, D a x < m →
    Relation.ReflTransGen (fun p q => G.Adj p q ∧ D q x < D p x ∧ D p x < m) a x := by
  intro a
  induction h : D a x using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    intro ha
    by_cases hax : a = x
    · subst hax; exact .refl
    · obtain ⟨w, hw, hwd⟩ := hD.descend a x hax
      exact .head ⟨hw, by omega, by omega⟩ (ih (D w x) (by omega) w rfl (by omega))

/-- The hop distance makes the graph connected. -/
theorem connected : G.Connected := by
  intro u v
  exact rtg_mono (fun p q h => h.1) (hD.reach_desc v (D u v + 1) u (by omega))

end IsHopDist

/-! ### The hop distance in a graph whose every edge is a bridge -/

namespace AllBridges

variable {D : V → V → ℕ} (hT : G.AllBridges) (hD : G.IsHopDist D)
include hT hD

/-- In a forest, the two ends of an edge are never at the same distance from a vertex (else the
two descents and the edge would close a cycle). -/
theorem ne_of_adj {u v : V} (h : G.Adj u v) (x : V) : D u x ≠ D v x := by
  intro he
  apply hT u v h
  have hsub : ∀ p q, (G.Adj p q ∧ D q x < D p x ∧ D p x < D u x + 1) → G.del u v p q := by
    rintro p q ⟨h1, h2, -⟩
    refine ⟨h1, ?_, ?_⟩
    · rintro ⟨rfl, rfl⟩; omega
    · rintro ⟨rfl, rfl⟩; omega
  exact (rtg_mono hsub (hD.reach_desc x (D u x + 1) u (by omega))).trans
    (rtg_symm (fun _ _ => del_symm) (rtg_mono hsub (hD.reach_desc x (D u x + 1) v (by omega))))

/-- In a forest, every vertex `v ≠ x` has exactly one neighbour closer to `x` (else the two
descents would close a cycle through `v`). -/
theorem unique_desc {v x w₁ w₂ : V} (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂) (d₁ : D w₁ x < D v x)
    (d₂ : D w₂ x < D v x) : w₁ = w₂ := by
  by_contra hne
  apply hT v w₁ h₁
  have hsub : ∀ p q, (G.Adj p q ∧ D q x < D p x ∧ D p x < D v x) → G.del v w₁ p q := by
    rintro p q ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rintro ⟨rfl, -⟩; omega
    · rintro ⟨-, rfl⟩; omega
  have hvw : G.del v w₁ v w₂ := ⟨h₂, fun h => hne h.2.symm, fun h => by
    obtain ⟨rfl, -⟩ := h; exact G.irrefl _ h₁⟩
  exact .head hvw ((rtg_mono hsub (hD.reach_desc x (D v x) w₂ d₂)).trans
    (rtg_symm (fun _ _ => del_symm) (rtg_mono hsub (hD.reach_desc x (D v x) w₁ d₁))))

/-- In a forest, the distances of the two ends of an edge differ by exactly one. -/
theorem adj_dist {u v : V} (h : G.Adj u v) (x : V) :
    D u x = D v x + 1 ∨ D v x = D u x + 1 := by
  have := hT.ne_of_adj hD h x
  have := hD.step u v x h
  have := hD.step v u x (G.symm _ _ h)
  omega

/-- **The only link leaving a side of a tree edge.**  For an edge `a → b`, let `S` be the
vertices closer to `a` than to `b` (`a`'s side).  The only link from `S` to its complement is
`a → b`. -/
theorem cut_unique {a b x y : V} (hab : G.Adj a b) (hxy : G.Adj x y) (hx : D a x < D b x)
    (hy : ¬ D a y < D b y) : x = a ∧ y = b := by
  have f1 := hT.adj_dist hD hab x
  have f2 := hT.adj_dist hD hab y
  have f3 := hT.adj_dist hD hxy a
  have f4 := hT.adj_dist hD hxy b
  have s1 := hD.symm a x
  have s2 := hD.symm b x
  have s3 := hD.symm a y
  have s4 := hD.symm b y
  by_cases hxa : x = a
  · subst hxa
    refine ⟨rfl, hD.eq_of_zero ?_⟩
    have := hD.self x
    omega
  · exfalso
    obtain ⟨z, hz, hzd⟩ := hD.descend x a hxa
    have f5 := hT.adj_dist hD hab z
    have f6 := hT.adj_dist hD hz b
    have s5 := hD.symm a z
    have s6 := hD.symm b z
    have hzy : z = y := hT.unique_desc hD (x := b) hz hxy (by omega) (by omega)
    subst hzy
    omega

end AllBridges


/-! ### Walks of bounded length and the hop distance of a connected graph -/

/-- `Reach R b n a`: there is an `R`-walk of length at most `n` from `a` to `b`. -/
def Reach (R : V → V → Prop) (b : V) : ℕ → V → Prop
  | 0, a => a = b
  | n + 1, a => Reach R b n a ∨ ∃ c, R a c ∧ Reach R b n c

/-- Every walk has a length. -/
theorem exists_reach {R : V → V → Prop} {a b : V} (h : Relation.ReflTransGen R a b) :
    ∃ n, Reach R b n a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hac _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, Or.inr ⟨_, hac, hn⟩⟩

open Classical in
variable (G) in
/-- **The hop distance** of the graph: the length of a shortest walk from `u` to `d` (`0` if
there is none). -/
noncomputable def hopDist (u d : V) : ℕ :=
  if h : ∃ n, Reach G.Adj d n u then Nat.find h else 0

open Classical in
/-- The hop distance is the length of a walk. -/
theorem hopDist_spec {u d : V} (h : ∃ n, Reach G.Adj d n u) :
    Reach G.Adj d (G.hopDist u d) u := by
  unfold hopDist; rw [dite_eq_left h]; exact Nat.find_spec h

open Classical in
/-- The hop distance is at most the length of every walk. -/
theorem hopDist_le {u d : V} {n : ℕ} (h : Reach G.Adj d n u) : G.hopDist u d ≤ n := by
  unfold hopDist; rw [dite_eq_left ⟨n, h⟩]; exact Nat.find_min' _ h

/-- The hop distance of a connected graph satisfies the Bellman–Ford equations. -/
theorem isHopDist_hopDist (hG : G.Connected) : G.IsHopDist G.hopDist := by
  have hex : ∀ u d, ∃ n, Reach G.Adj d n u := fun u d => exists_reach (hG u d)
  have hstep : ∀ u v d, G.Adj u v → G.hopDist u d ≤ G.hopDist v d + 1 := fun u v d h =>
    hopDist_le (Or.inr ⟨v, h, hopDist_spec (hex v d)⟩)
  refine ⟨fun d => Nat.le_zero.1 (hopDist_le (n := 0) rfl), hstep, fun v d hvd => ?_⟩
  have hs := hopDist_spec (hex v d)
  generalize hn : G.hopDist v d = n at hs
  cases n with
  | zero => exact absurd hs hvd
  | succ m =>
    rcases hs with hs | ⟨w, hw, hs⟩
    · have := hopDist_le hs; omega
    · refine ⟨w, hw, ?_⟩
      have := hopDist_le hs
      have := hstep v w d hw
      omega

/-! ### The network of a graph and the tree flow -/

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

variable (G) in
/-- The network of the graph: capacity `c` in both directions of every edge, `0` elsewhere. -/
def net (c : ℚ) (hc : 0 ≤ c) : Net V where
  cap u v := if G.Adj u v then c else 0
  cap_nonneg u v := by by_cases h : G.Adj u v <;> simp [h, hc]

variable (G) in
/-- **The tree flow**: commodity `d` crosses the link `a → b` only if `b` is the next hop from
`a` towards `d`, and then carries everything sent to `d` from `a`'s side of the edge (the
vertices closer to `a` than to `b`).  In a tree this is the flow in which every vertex forwards
everything it holds for `d` to its unique next hop towards `d`. -/
def treeFlowF (D : V → V → ℕ) (dem : V → V → ℚ) (θ : ℚ) (d a b : V) : ℚ :=
  if G.Adj a b ∧ D b d < D a d then θ * ∑ s, (if D a s < D b s then dem s d else 0) else 0

namespace AllBridges

variable {D : V → V → ℕ} (hT : G.AllBridges) (hD : G.IsHopDist D)
include hT hD

/-- The per-source bookkeeping behind the conservation of the tree flow at `v ≠ d`, with `w₀`
the next hop from `v` towards `d`: a source is on `v`'s side of `v → w₀` iff it is `v` or on the
side of exactly one link `u → v` that commodity `d` crosses. -/
theorem side_split {v d w₀ : V} (hvd : v ≠ d) (hw : G.Adj v w₀) (hwd : D w₀ d < D v d)
    (s : V) (q : ℚ) :
    (if D v s < D w₀ s then q else 0) = (if s = v then q else 0) +
      ∑ u, (if (G.Adj u v ∧ D v d < D u d) ∧ D u s < D v s then q else 0) := by
  by_cases hsv : s = v
  · subst hsv
    have h0 : D w₀ s ≠ 0 := fun h => G.irrefl _ (hD.eq_of_zero h ▸ hw)
    rw [ite_eq_left (by rw [hD.self]; omega), ite_eq_left rfl, Finset.sum_eq_zero]
    · ring
    · intro u _; rw [ite_eq_right]; rw [hD.self]; omega
  · obtain ⟨us, hus, husd⟩ := hD.descend v s (Ne.symm hsv)
    rw [ite_eq_right hsv, zero_add, Finset.sum_eq_single us]
    · by_cases hu0 : us = w₀
      · subst hu0
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      · have e1 : D v d < D us d := by
          rcases hT.adj_dist hD hus d with h | h
          · exact absurd (hT.unique_desc hD (x := d) hus hw (by omega) hwd) hu0
          · omega
        have e2 : D v s < D w₀ s := by
          rcases hT.adj_dist hD hw s with h | h
          · exact absurd (hT.unique_desc hD (x := s) hus hw (by omega) (by omega)) hu0
          · omega
        rw [ite_eq_left e2, ite_eq_left ⟨⟨G.symm _ _ hus, e1⟩, by omega⟩]
    · intro u _ hu
      rw [ite_eq_right]
      rintro ⟨⟨h1, -⟩, h2⟩
      exact hu (hT.unique_desc hD (G.symm _ _ h1) hus h2 (by omega))
    · intro h; exact absurd (Finset.mem_univ us) h

/-- **Conservation of the tree flow.** -/
theorem treeFlow_conserve (dem : V → V → ℚ) (θ : ℚ) (d v : V) (hvd : v ≠ d) :
    ∑ w, G.treeFlowF D dem θ d v w - ∑ u, G.treeFlowF D dem θ d u v = θ * dem v d := by
  obtain ⟨w₀, hw, hwd⟩ := hD.descend v d hvd
  have hout : ∑ w, G.treeFlowF D dem θ d v w =
      θ * ∑ s, (if D v s < D w₀ s then dem s d else 0) := by
    rw [Finset.sum_eq_single w₀]
    · unfold treeFlowF; rw [ite_eq_left ⟨hw, by omega⟩]
    · intro w _ hne
      unfold treeFlowF
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      exact hne (hT.unique_desc hD h1 hw h2 (by omega))
    · intro h; exact absurd (Finset.mem_univ w₀) h
  have hin : ∑ u, G.treeFlowF D dem θ d u v =
      θ * ∑ s, ∑ u, (if (G.Adj u v ∧ D v d < D u d) ∧ D u s < D v s then dem s d else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold treeFlowF
    by_cases hc : G.Adj u v ∧ D v d < D u d
    · rw [ite_eq_left hc]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by simp [hc]
    · rw [ite_eq_right hc]
      simp [hc]
  rw [hout, hin]
  have hs : ∑ s, (if D v s < D w₀ s then dem s d else 0) =
      dem v d +
        ∑ s, ∑ u, (if (G.Adj u v ∧ D v d < D u d) ∧ D u s < D v s then dem s d else 0) := by
    rw [Finset.sum_congr rfl fun s _ => hT.side_split hD hvd hw (by omega) s (dem s d),
      Finset.sum_add_distrib]
    simp
  rw [hs]; ring

/-- **The tree flow respects the capacities**: on a link `a → b` it carries `θ` times the
traffic from `a`'s side to `b`'s side, which the cut bound for `a`'s side (whose only outgoing
link is `a → b`) keeps within `c`. -/
theorem treeFlow_capacity {c : ℚ} (hc : 0 ≤ c) {dem : V → V → ℚ} (hdem : ∀ s d, 0 ≤ dem s d)
    {θ : ℚ} (hθ : 0 ≤ θ) (h : Routable (G.net c hc) dem θ) (a b : V) :
    ∑ d, G.treeFlowF D dem θ d a b ≤ (G.net c hc).cap a b := by
  by_cases hab : G.Adj a b
  · let S : V → Prop := fun x => D a x < D b x
    have h1 : ∑ d, G.treeFlowF D dem θ d a b ≤
        θ * ∑ s, ∑ d, (if S s ∧ ¬ S d then dem s d else 0) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_le_sum fun d _ => ?_
      unfold treeFlowF
      by_cases hd : D b d < D a d
      · rw [ite_eq_left ⟨hab, hd⟩]
        refine le_of_eq (congrArg _ (Finset.sum_congr rfl fun s _ => ?_))
        have : ¬ (D a d < D b d) := by omega
        simp [S, this]
      · rw [ite_eq_right (fun h' => hd h'.2)]
        exact mul_nonneg hθ (Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hdem])
    have h2 := cut_bound h S
    have h3 : ∑ x, ∑ y, (if S x ∧ ¬ S y then (G.net c hc).cap x y else 0) ≤
        ∑ x, ∑ y, (if x = a ∧ y = b then c else 0) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
      by_cases hs : S x ∧ ¬ S y
      · rw [ite_eq_left hs]
        simp only [net]
        by_cases hxy : G.Adj x y
        · rw [ite_eq_left hxy, ite_eq_left (hT.cut_unique hD hab hxy hs.1 hs.2)]
        · rw [ite_eq_right hxy]; split_ifs <;> simp [hc]
      · rw [ite_eq_right hs]; split_ifs <;> simp [hc]
    have h4 : ∑ x, ∑ y, (if x = a ∧ y = b then c else 0) = c := by
      simp only [ite_and]; simp
    have h5 : (G.net c hc).cap a b = c := by simp [net, hab]
    linarith
  · have h0 : ∀ d, G.treeFlowF D dem θ d a b = 0 := fun d => by
      unfold treeFlowF; rw [ite_eq_right (fun h' => hab h'.1)]
    simp [h0, net, hab]

/-- **Trees: detours never help.**  In a graph whose every edge is a bridge (with its hop
distance `D`; the graph is then a tree), every nonnegative traffic matrix routable at `θ ≥ 0` is
routed at `θ` by a minimal flow: the tree flow, in which every vertex forwards each commodity to
its unique next hop. -/
theorem minimal_of_routable {c : ℚ} (hc : 0 ≤ c) {dem : V → V → ℚ}
    (hdem : ∀ s d, 0 ≤ dem s d) {θ : ℚ} (hθ : 0 ≤ θ) (h : Routable (G.net c hc) dem θ) :
    ∃ F : Flow (G.net c hc) dem θ, F.Minimal (fun a b => (D a b : ℚ)) := by
  refine ⟨⟨G.treeFlowF D dem θ, fun d a b => ?_, hT.treeFlow_conserve hD dem θ,
    hT.treeFlow_capacity hD hc hdem hθ h⟩, fun d a b hp => ?_⟩
  · unfold treeFlowF
    split_ifs
    · exact mul_nonneg hθ (Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hdem])
    · exact le_refl _
  · simp only at hp ⊢
    unfold treeFlowF at hp
    split_ifs at hp with hc'
    · exact_mod_cast hc'.2
    · exact absurd hp (lt_irrefl _)

end AllBridges


/-! ### Graphs with a cycle: a detour doubles the throughput of an edge -/

/-- **A path from a walk**: an `R`-walk of length at most `n` from `a` to `b` yields a unit
flow from `a` to `b` on the links of `R`, at most `1` on every link (a path, not a walk: it
never comes back to a vertex). -/
theorem exists_pathFlow (R : V → V → Prop) (b : V) : ∀ n a, Reach R b n a →
    ∃ p : V → V → ℚ, (∀ x y, 0 ≤ p x y ∧ p x y ≤ 1) ∧
      (∀ x y, p x y ≠ 0 → R x y ∧ Reach R b n x) ∧
      ∀ x, ∑ y, p x y - ∑ y, p y x = (if x = a then 1 else 0) - (if x = b then 1 else 0) := by
  intro n
  induction n with
  | zero =>
    intro a ha
    have hab : a = b := ha
    subst hab
    exact ⟨fun _ _ => 0, fun _ _ => ⟨le_refl _, zero_le_one⟩, fun _ _ h => absurd rfl h,
      fun x => by simp⟩
  | succ n ih =>
    intro a ha
    by_cases hn : Reach R b n a
    · obtain ⟨p, h1, h2, h3⟩ := ih a hn
      exact ⟨p, h1, fun x y h => ⟨(h2 x y h).1, Or.inl (h2 x y h).2⟩, h3⟩
    · obtain ⟨c, hac, hc⟩ := ha.resolve_left hn
      obtain ⟨p, h1, h2, h3⟩ := ih c hc
      have hpa : ∀ y, p a y = 0 := fun y => by
        by_contra h; exact hn (h2 a y h).2
      refine ⟨fun x y => p x y + if x = a ∧ y = c then 1 else 0, fun x y => ?_,
        fun x y h => ?_, fun x => ?_⟩
      · by_cases hxy : x = a ∧ y = c
        · obtain ⟨rfl, rfl⟩ := hxy; simp [hpa]
        · simp only; rw [ite_eq_right hxy, add_zero]; exact h1 x y
      · by_cases hxy : x = a ∧ y = c
        · obtain ⟨rfl, rfl⟩ := hxy; exact ⟨hac, Or.inr ⟨_, hac, hc⟩⟩
        · have : p x y ≠ 0 := by simpa [ite_eq_right hxy] using h
          exact ⟨(h2 x y this).1, Or.inl (h2 x y this).2⟩
      · have e1 : ∑ y, (if x = a ∧ y = c then (1 : ℚ) else 0) = if x = a then 1 else 0 := by
          by_cases hx : x = a <;> simp [hx]
        have e2 : ∑ y, (if y = a ∧ x = c then (1 : ℚ) else 0) = if x = c then 1 else 0 := by
          by_cases hx : x = c <;> simp [hx]
        simp only [Finset.sum_add_distrib, e1, e2]
        linarith [h3 x]

end UGraph

/-- The **single-pair traffic**: rate `1` from `u` to `v`, nothing else. -/
def pairDem [DecidableEq V] (u v : V) (s d : V) : ℚ := if s = u ∧ d = v then 1 else 0

/-- The single-pair traffic is nonnegative. -/
theorem pairDem_nonneg [DecidableEq V] (u v s d : V) : 0 ≤ pairDem u v s d := by
  unfold pairDem; split_ifs <;> norm_num

namespace UGraph

variable {G : UGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

namespace IsHopDist

variable {D : V → V → ℕ} (hD : G.IsHopDist D)
include hD

/-- **Without detours, an edge carries at most its capacity**: a minimal flow of the
single-pair traffic between the ends of an edge `u — v` reaches at most `θ ≤ c`.  Its only
shortest path is the edge itself (`D u v = 1`), so commodity `v` leaves `u` only on `u → v`. -/
theorem minimal_pair_le {u v : V} (huv : G.Adj u v) {c : ℚ} (hc : 0 ≤ c) {θ : ℚ}
    (F : Flow (G.net c hc) (pairDem u v) θ) (hF : F.Minimal (fun a b => (D a b : ℚ))) :
    θ ≤ c := by
  have hφd : ∀ d, (fun d x => if d = v ∧ x = u then (1 : ℚ) else 0) d d = 0 := by
    intro d
    simp only
    rw [ite_eq_right]
    rintro ⟨rfl, h⟩
    subst h
    exact G.irrefl _ huv
  have hφ : ∀ d a b, (D b d : ℚ) < D a d → 0 < (G.net c hc).cap a b →
      (fun d x => if d = v ∧ x = u then (1 : ℚ) else 0) d a -
        (fun d x => if d = v ∧ x = u then (1 : ℚ) else 0) d b ≤
      (fun a b => if a = u ∧ b = v then (1 : ℚ) else 0) a b := by
    intro d a b hab _
    simp only
    have hab' : D b d < D a d := by exact_mod_cast hab
    by_cases h : d = v ∧ a = u
    · obtain ⟨rfl, rfl⟩ := h
      have h1 := hD.step a d d huv
      rw [hD.self] at h1
      have hb : b = d := hD.eq_of_zero (by omega)
      subst hb
      have : b ≠ a := fun h' => G.irrefl _ (h' ▸ huv)
      simp [this]
    · rw [ite_eq_right h]
      have : (0 : ℚ) ≤ if d = v ∧ b = u then 1 else 0 := by split_ifs <;> norm_num
      have : (0 : ℚ) ≤ if a = u ∧ b = v then 1 else 0 := by split_ifs <;> norm_num
      linarith
  have key := F.potential_bound_on hF (fun a b => if a = u ∧ b = v then (1 : ℚ) else 0)
    (fun a b => by split_ifs <;> norm_num) _ hφd hφ
  have e1 : ∑ s, ∑ d, pairDem u v s d * (if d = v ∧ s = u then (1 : ℚ) else 0) = 1 := by
    simp only [pairDem, ite_and]; simp
  have e2 : ∑ a, ∑ b, (G.net c hc).cap a b * (if a = u ∧ b = v then (1 : ℚ) else 0) = c := by
    simp only [ite_and]; simp [net, huv]
  rw [e1, e2] at key
  linarith

end IsHopDist

/-- **With a detour, an edge carries twice its capacity**: if the ends of the edge `u — v` are
still joined after removing it (the edge lies on a cycle), the single-pair traffic `u → v` is
routable at `2c`: `c` on the edge, `c` on a path around the cycle. -/
theorem routable_pair_two {c : ℚ} (hc : 0 ≤ c) {u v : V} (huv : G.Adj u v)
    (hcyc : Relation.ReflTransGen (G.del u v) u v) :
    Routable (G.net c hc) (pairDem u v) (2 * c) := by
  obtain ⟨n, hn⟩ := exists_reach hcyc
  obtain ⟨p, hp1, hp2, hp3⟩ := exists_pathFlow (G.del u v) v n u hn
  have hpuv : p u v = 0 := by
    by_contra h; exact (hp2 u v h).1.2.1 ⟨rfl, rfl⟩
  refine ⟨⟨fun d x y => if d = v then c * ((if x = u ∧ y = v then 1 else 0) + p x y) else 0,
    fun d x y => ?_, fun d x hxd => ?_, fun x y => ?_⟩⟩
  · by_cases hd : d = v
    · rw [ite_eq_left hd]
      exact mul_nonneg hc (add_nonneg (by split_ifs <;> norm_num) (hp1 x y).1)
    · rw [ite_eq_right hd]
  · by_cases hd : d = v
    · subst hd
      have e1 : ∑ y, (if x = u ∧ y = d then (1 : ℚ) else 0) = if x = u then 1 else 0 := by
        by_cases hx : x = u <;> simp [hx]
      have e2 : ∑ y, (if y = u ∧ x = d then (1 : ℚ) else 0) = 0 := by simp [hxd]
      have h3 := hp3 x
      rw [ite_eq_right hxd] at h3
      simp only [ite_true, ← Finset.mul_sum, Finset.sum_add_distrib, e1, e2, pairDem, and_true]
      have hA : ∑ y, p x y = ∑ y, p y x + (if x = u then 1 else 0) := by linarith
      rw [hA]; ring
    · simp [hd, pairDem]
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hxy : G.Adj x y
    · have hcap : (G.net c hc).cap x y = c := by simp [net, hxy]
      rw [hcap]
      refine mul_le_of_le_one_right hc ?_
      by_cases h : x = u ∧ y = v
      · obtain ⟨rfl, rfl⟩ := h; simp [hpuv]
      · rw [ite_eq_right h, zero_add]; exact (hp1 x y).2
    · have hcap : (G.net c hc).cap x y = 0 := by simp [net, hxy]
      have h0 : (if x = u ∧ y = v then (1 : ℚ) else 0) = 0 := by
        rw [ite_eq_right]; rintro ⟨rfl, rfl⟩; exact hxy huv
      have hp0 : p x y = 0 := by
        by_contra h; exact hxy (hp2 x y h).1.1
      rw [hcap, h0, hp0]; simp

namespace IsHopDist

variable {D : V → V → ℕ} (hD : G.IsHopDist D)
include hD

/-- **Cycles: detours help.**  If the edge `u — v` lies on a cycle (its ends are still joined
after removing it), the single-pair traffic `u → v` is routable at `2c`, while every minimal
flow of it reaches at most `c`. -/
theorem detour_helps {c : ℚ} (hc : 0 < c) {u v : V} (huv : G.Adj u v)
    (hcyc : Relation.ReflTransGen (G.del u v) u v) :
    Routable (G.net c hc.le) (pairDem u v) (2 * c) ∧
      ∀ θ (F : Flow (G.net c hc.le) (pairDem u v) θ),
        F.Minimal (fun a b => (D a b : ℚ)) → θ ≤ c :=
  ⟨routable_pair_two hc.le huv hcyc, fun _ F hF => hD.minimal_pair_le huv hc.le F hF⟩

/-- On an edge lying on a cycle, minimal routing is not optimal for the single-pair traffic. -/
theorem not_minimal_optimal {c : ℚ} (hc : 0 < c) {u v : V} (huv : G.Adj u v)
    (hcyc : Relation.ReflTransGen (G.del u v) u v) :
    ¬ ∀ θ, 0 ≤ θ → Routable (G.net c hc.le) (pairDem u v) θ →
      ∃ F : Flow (G.net c hc.le) (pairDem u v) θ, F.Minimal (fun a b => (D a b : ℚ)) := by
  intro h
  obtain ⟨hr, hmin⟩ := hD.detour_helps hc huv hcyc
  obtain ⟨F, hF⟩ := h (2 * c) (by linarith) hr
  have := hmin _ F hF
  linarith

/-- **Detours never help for any traffic iff the network is a tree.**  For a graph with hop
distance `D` (so a connected graph) and links of capacity `c > 0` both ways: every nonnegative
traffic matrix routable at a throughput `θ ≥ 0` is routed at `θ` by a minimal flow if and only
if the graph is a tree. -/
theorem minimal_optimal_iff {c : ℚ} (hc : 0 < c) :
    (∀ dem : V → V → ℚ, (∀ s d, 0 ≤ dem s d) → ∀ θ, 0 ≤ θ → Routable (G.net c hc.le) dem θ →
      ∃ F : Flow (G.net c hc.le) dem θ, F.Minimal (fun a b => (D a b : ℚ))) ↔ G.IsTree := by
  constructor
  · intro h
    exact ⟨hD.connected, fun u v huv hcyc =>
      hD.not_minimal_optimal hc huv hcyc (h _ (pairDem_nonneg u v))⟩
  · intro hT dem hdem θ hθ hr
    exact hT.2.minimal_of_routable hD hc.le hdem hθ hr

end IsHopDist

/-- **Detours never help for any traffic iff the network is a tree**, for a connected graph
with its hop distance `hopDist`. -/
theorem minimal_optimal_iff_isTree (hG : G.Connected) {c : ℚ} (hc : 0 < c) :
    (∀ dem : V → V → ℚ, (∀ s d, 0 ≤ dem s d) → ∀ θ, 0 ≤ θ → Routable (G.net c hc.le) dem θ →
      ∃ F : Flow (G.net c hc.le) dem θ, F.Minimal (fun a b => (G.hopDist a b : ℚ))) ↔
      G.IsTree :=
  (isHopDist_hopDist hG).minimal_optimal_iff hc

/-- **Trees: detours never help** (with the tree's hop distance `hopDist`). -/
theorem IsTree.minimal_of_routable (hT : G.IsTree) {c : ℚ} (hc : 0 ≤ c) {dem : V → V → ℚ}
    (hdem : ∀ s d, 0 ≤ dem s d) {θ : ℚ} (hθ : 0 ≤ θ) (h : Routable (G.net c hc) dem θ) :
    ∃ F : Flow (G.net c hc) dem θ, F.Minimal (fun a b => (G.hopDist a b : ℚ)) :=
  hT.2.minimal_of_routable (isHopDist_hopDist hT.1) hc hdem hθ h

end UGraph


/-! ### Examples: the path is a tree, the 4-cycle is not -/

/-- **The path** on `Fin k`: `i — i + 1`. -/
def pathGraph (k : ℕ) : UGraph (Fin k) where
  Adj := LineAdj
  symm _ _ h := by unfold LineAdj at *; omega
  irrefl _ h := by unfold LineAdj at h; omega

/-- Decidability of the adjacency of the path. -/
instance (k : ℕ) : DecidableRel (pathGraph k).Adj := fun a b =>
  inferInstanceAs (Decidable (LineAdj a b))

/-- The hop distance of the path: `|a - b|`. -/
def pathDist {k : ℕ} (a b : Fin k) : ℕ := (a : ℕ) - b + ((b : ℕ) - a)

/-- `|a - b|` is the hop distance of the path. -/
theorem pathDist_isHopDist (k : ℕ) : (pathGraph k).IsHopDist pathDist := by
  refine ⟨fun d => by simp [pathDist], fun u v d h => ?_, fun v d hvd => ?_⟩
  · change LineAdj u v at h; unfold LineAdj at h; unfold pathDist; omega
  · have hvd' : (v : ℕ) ≠ d := fun h => hvd (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hvd' with hlt | hlt
    · refine ⟨⟨(v : ℕ) + 1, by omega⟩, Or.inl rfl, ?_⟩
      unfold pathDist; simp only; omega
    · refine ⟨⟨(v : ℕ) - 1, by omega⟩, Or.inr (by simp only; omega), ?_⟩
      unfold pathDist; simp only; omega

/-- **The path is a tree.** -/
theorem pathGraph_isTree (k : ℕ) : (pathGraph k).IsTree := by
  constructor
  · have up : ∀ m (a b : Fin k), (a : ℕ) + m = b →
        Relation.ReflTransGen (pathGraph k).Adj a b := by
      intro m
      induction m with
      | zero =>
        intro a b h
        have : a = b := Fin.ext (by omega)
        subst this; exact .refl
      | succ m ih =>
        intro a b h
        exact (ih a ⟨(a : ℕ) + m, by omega⟩ rfl).tail (Or.inl (by simp only; omega))
    intro a b
    rcases le_total (a : ℕ) b with hab | hab
    · exact up ((b : ℕ) - a) a b (by omega)
    · exact UGraph.rtg_symm (pathGraph k).symm (up ((a : ℕ) - b) b a (by omega))
  · intro u v huv hcyc
    change LineAdj u v at huv
    unfold LineAdj at huv
    rcases huv with huv | huv
    · have := UGraph.rtg_invariant (fun x : Fin k => (x : ℕ) ≤ u) (fun x y hxy hx => by
        obtain ⟨hxy, h1, h2⟩ := hxy
        change LineAdj x y at hxy
        unfold LineAdj at hxy
        simp only [Fin.ext_iff] at h1 h2 ⊢ hx
        omega) hcyc (le_refl _)
      omega
    · have := UGraph.rtg_invariant (fun x : Fin k => (u : ℕ) ≤ x) (fun x y hxy hx => by
        obtain ⟨hxy, h1, h2⟩ := hxy
        change LineAdj x y at hxy
        unfold LineAdj at hxy
        simp only [Fin.ext_iff] at h1 h2 ⊢ hx
        omega) hcyc (le_refl _)
      omega

/-- **On a path, detours never help**: every nonnegative traffic matrix routable at `θ ≥ 0` is
routed at `θ` by a minimal flow. -/
theorem path_minimal_optimal (k : ℕ) {c : ℚ} (hc : 0 ≤ c) {dem : Fin k → Fin k → ℚ}
    (hdem : ∀ s d, 0 ≤ dem s d) {θ : ℚ} (hθ : 0 ≤ θ)
    (h : Routable ((pathGraph k).net c hc) dem θ) :
    ∃ F : Flow ((pathGraph k).net c hc) dem θ, F.Minimal (fun a b => (pathDist a b : ℚ)) :=
  (pathGraph_isTree k).2.minimal_of_routable (pathDist_isHopDist k) hc hdem hθ h

/-- **The 4-cycle** on `Fin 4`. -/
def cycle4 : UGraph (Fin 4) where
  Adj := RingAdj
  symm := by decide
  irrefl := by decide

/-- Decidability of the adjacency of the 4-cycle. -/
instance : DecidableRel cycle4.Adj := fun a b => inferInstanceAs (Decidable (RingAdj a b))

/-- The ring distance is the hop distance of the 4-cycle. -/
theorem cycle4_isHopDist : cycle4.IsHopDist ringDist := ⟨by decide, by decide, by decide⟩

/-- The edge `0 — 1` of the 4-cycle lies on a cycle: `0 — 3 — 2 — 1` avoids it. -/
theorem cycle4_cycle : Relation.ReflTransGen (cycle4.del 0 1) 0 1 :=
  .head (b := 3) (by unfold UGraph.del; decide) (.head (b := 2) (by unfold UGraph.del; decide)
    (.single (by unfold UGraph.del; decide)))

/-- **The 4-cycle is not a tree.** -/
theorem cycle4_not_isTree : ¬ cycle4.IsTree := fun h => h.2 0 1 (by decide) cycle4_cycle

/-- **On the 4-cycle, detours help**: the traffic `0 → 1` is routable at `2c` (half of it around
the cycle), while every minimal flow of it reaches at most `c`. -/
theorem cycle4_detour {c : ℚ} (hc : 0 < c) :
    Routable (cycle4.net c hc.le) (pairDem 0 1) (2 * c) ∧
      ∀ θ (F : Flow (cycle4.net c hc.le) (pairDem 0 1) θ),
        F.Minimal (fun a b => (ringDist a b : ℚ)) → θ ≤ c :=
  cycle4_isHopDist.detour_helps hc (by decide) cycle4_cycle

end Fluid

end AsyncLean
