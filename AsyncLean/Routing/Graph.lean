/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Source

/-!
# Safe adaptive routing on arbitrary topologies

The mesh networks of `AsyncLean.Examples` encode their channels as numbers and use the
geometry of the mesh (XY routing, turn models) to find an acyclic escape layer.  This file
does the same for **every finite connected undirected graph**: a torus, a circulant, a random
regular graph, a dragonfly, a fat tree, an irregular chip floor plan.

## The graph

A `GraphData V` gives, on a vertex type `V` with decidable equality:

* a list `verts` of all vertices (the graph is finite);
* the neighbour lists `nbrs`, symmetric (an undirected graph);
* a function `dist`, read as an estimate of the distance between two vertices.  Any function
  is allowed (safety does not depend on it); with the true graph distance the adaptive layer is
  minimal adaptive routing;
* a **rooted spanning tree**: a root, a parent function `par` whose edges are edges of the
  graph, and a depth `dep` with `dep root = 0` and `dep (par u) + 1 = dep u` off the root.

Every connected graph has one: `GraphData.ofConnected` builds a breadth-first spanning tree
from symmetric neighbour lists and a proof that every vertex is reachable from the root.

## The network (`GraphData.net`)

Each directed link `u → v` carries two virtual channels (`GChan.link u v vc`), and each vertex
has an injection channel (`GChan.inj u`); a packet carries its destination.

* **Virtual channel 1 (adaptive)**: every neighbour `v` of the current vertex `u` with
  `dist v d < dist u d` (minimal adaptive routing when `dist` is the graph distance).
* **Virtual channel 0 (escape)**: **tree routing** along the spanning tree: if the
  destination lies below `u` in the tree (`anc u d`), go down to the child towards it
  (`down u d`), otherwise go up to the parent.  This is up*/down* routing restricted to tree
  edges: a packet goes up to the lowest common ancestor and then down.
* The escape is **absorbing**: from a virtual channel 0 channel only the escape hop is
  permitted.  Tree paths are not shortest paths, so a packet allowed to return from the escape
  layer could bounce for ever between an escape hop that moves it away from its destination
  and an adaptive hop that brings it back; with an absorbing escape, the distance on virtual
  channel 1 and the tree distance on virtual channel 0 combine to a ranking function.

The phase of the escape route (up, or down only) is recovered from the channel: a packet in
virtual channel 0 of a link from a parent to its child has its destination below that child
(`GraphData.legal`).  The escape dependencies go up the tree, then down it, never back up
(`GraphData.escRank`), so they are acyclic.

## Main results

For every `G : GraphData V`:

* `GraphData.correct` : `G.net` is deadlock free and livelock free under every valid
  selection function (`Network.Correct`), and starvation free under strongly fair scheduling
  (`Network.StarvationFree`).  Strong fairness is demanding: with finitely many configurations
  it makes a run revisit every reachable configuration, the empty network included, so the
  starvation statement says nothing about a network kept saturated.  The adaptive layer is
  minimal when `dist` is the graph distance (`GraphData.adaptive_ne_nil`); safety holds for
  any `dist`.
* `GraphData.correct_of_escapeSel` : the same under every selection that never refuses a
  free escape hop (`Network.EscapeSel`), which may decline adaptive hops.
* `GraphData.correct_of_sourceSel` : the same under every selection that may in addition
  throttle the sources (`Network.SourceSel`, with the injection channels as sources).
* `GraphData.route_adj` : every hop follows an edge of the graph;
  `GraphData.adaptive_ne_nil` : when `dist` is the graph distance, the adaptive layer offers a
  hop to every packet that has not arrived.
* `GraphData.exists_correct` : **every finite connected undirected graph**, with any distance
  estimate, carries such a network (from a breadth-first spanning tree) that is deadlock,
  livelock and starvation free.
-/

namespace AsyncLean

open Network

/-- The channels of a network on the vertices `V`: an injection channel at each vertex, and two
virtual channels on each directed link (`vc = false`: the escape layer, virtual channel 0;
`vc = true`: the adaptive layer, virtual channel 1). -/
inductive GChan (V : Type*) where
  /-- The injection channel of vertex `u`. -/
  | inj (u : V)
  /-- The virtual channel `vc` of the link from `u` to `v`. -/
  | link (u v : V) (vc : Bool)
  deriving DecidableEq

namespace GChan

variable {V : Type*}

/-- The vertex a packet in the channel has reached. -/
def head : GChan V → V
  | inj u => u
  | link _ v _ => v

/-- The channel belongs to the escape layer (virtual channel 0 of a link). -/
def isEsc : GChan V → Bool
  | link _ _ vc => !vc
  | inj _ => false

/-- The channel is an injection channel. -/
def isInj : GChan V → Bool
  | inj _ => true
  | link _ _ _ => false

/-- Every channel on the vertices of `vs`. -/
def all (vs : List V) : List (GChan V) :=
  vs.map inj ++ vs.flatMap fun u => vs.flatMap fun v => [link u v false, link u v true]

/-- Every channel on the vertices is listed by `all`. -/
theorem mem_all {vs : List V} (h : ∀ v, v ∈ vs) (c : GChan V) : c ∈ all vs := by
  rcases c with u | ⟨u, v, _ | _⟩ <;> simp [all, h]

end GChan

/-- **A finite undirected graph with a rooted spanning tree** and a distance estimate. -/
structure GraphData (V : Type*) where
  /-- The vertices (the graph is finite). -/
  verts : List V
  /-- Every vertex is listed. -/
  mem_verts : ∀ v, v ∈ verts
  /-- The neighbours of each vertex. -/
  nbrs : V → List V
  /-- The graph is undirected. -/
  symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v
  /-- A distance estimate, used by the adaptive layer (any function is safe). -/
  dist : V → V → ℕ
  /-- The root of the spanning tree. -/
  root : V
  /-- The parent of each vertex in the spanning tree (the root is its own parent). -/
  par : V → V
  /-- The depth of each vertex in the spanning tree. -/
  dep : V → ℕ
  /-- The root has depth 0. -/
  dep_root : dep root = 0
  /-- The root is its own parent. -/
  par_root : par root = root
  /-- The parent of a vertex other than the root is one level up. -/
  dep_par : ∀ u, u ≠ root → dep (par u) + 1 = dep u
  /-- The tree edges are edges of the graph. -/
  par_adj : ∀ u, u ≠ root → par u ∈ nbrs u

namespace GraphData

variable {V : Type*} [DecidableEq V] (G : GraphData V)

/-! ### The spanning tree -/

omit [DecidableEq V] in
/-- A vertex other than the root has positive depth. -/
theorem dep_pos {u : V} (h : u ≠ G.root) : 0 < G.dep u := by
  have := G.dep_par u h; omega

/-- The root is the only vertex of depth 0. -/
theorem eq_root_of_dep {u : V} (h : G.dep u = 0) : u = G.root := by
  by_contra hne; have := G.dep_pos hne; omega

/-- Going up `n` steps decreases the depth by `n` (until the root). -/
theorem dep_iterate (n : ℕ) (d : V) : G.dep (G.par^[n] d) = G.dep d - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : G.par^[n] d = G.root
    · rw [h, G.par_root, G.dep_root]; rw [h, G.dep_root] at ih; omega
    · have := G.dep_par _ h; omega

/-- `u` is an ancestor of `d` in the spanning tree (or `d` itself): `d` lies below `u`. -/
def anc (u d : V) : Prop := G.par^[G.dep d - G.dep u] d = u

/-- Being an ancestor is decidable. -/
instance (u d : V) : Decidable (G.anc u d) := inferInstanceAs (Decidable (_ = _))

/-- The root is an ancestor of every vertex. -/
theorem anc_root (d : V) : G.anc G.root d :=
  G.eq_root_of_dep (by rw [G.dep_root, Nat.sub_zero, G.dep_iterate]; omega)

/-- A vertex that is not an ancestor of `d` is not the root. -/
theorem ne_root_of_not_anc {u d : V} (h : ¬ G.anc u d) : u ≠ G.root := by
  rintro rfl; exact h (G.anc_root d)

omit [DecidableEq V] in
/-- A proper ancestor is strictly shallower. -/
theorem dep_lt_of_anc {u d : V} (h : G.anc u d) (hne : u ≠ d) : G.dep u < G.dep d := by
  by_contra hle
  unfold anc at h
  rw [show G.dep d - G.dep u = 0 by omega, Function.iterate_zero_apply] at h
  exact hne h.symm

/-- The child of `u` towards `d`, when `d` lies strictly below `u`. -/
def down (u d : V) : V := G.par^[G.dep d - G.dep u - 1] d

omit [DecidableEq V] in
/-- `down u d` is a child of `u`. -/
theorem par_down {u d : V} (h : G.anc u d) (hne : u ≠ d) : G.par (G.down u d) = u := by
  have := G.dep_lt_of_anc h hne
  unfold down
  rw [← Function.iterate_succ_apply' G.par, show (G.dep d - G.dep u - 1).succ =
    G.dep d - G.dep u by omega]
  exact h

/-- `down u d` is one level deeper than `u`. -/
theorem dep_down {u d : V} (h : G.anc u d) (hne : u ≠ d) : G.dep (G.down u d) = G.dep u + 1 := by
  have := G.dep_lt_of_anc h hne
  unfold down; rw [G.dep_iterate]; omega

/-- `d` still lies below `down u d`. -/
theorem anc_down {u d : V} (h : G.anc u d) (hne : u ≠ d) : G.anc (G.down u d) d := by
  have := G.dep_lt_of_anc h hne
  unfold anc; rw [G.dep_down h hne]; unfold down
  rw [show G.dep d - (G.dep u + 1) = G.dep d - G.dep u - 1 by omega]

/-- `down u d` is not the root. -/
theorem down_ne_root {u d : V} (h : G.anc u d) (hne : u ≠ d) : G.down u d ≠ G.root := by
  intro h'; have := G.dep_down h hne; rw [h', G.dep_root] at this; omega

/-- The next vertex of tree routing from `u` to `d`: down towards `d` if `d` lies below `u`,
up to the parent otherwise. -/
def next (u d : V) : V := if G.anc u d then G.down u d else G.par u

/-- The length of the tree path from `v` to `d` (an upper bound when `d` is not below `v`). -/
def treeDist (v d : V) : ℕ := if G.anc v d then G.dep d - G.dep v else G.dep v + G.dep d

/-- Every tree hop brings the packet closer in the tree. -/
theorem treeDist_next {u d : V} (hne : u ≠ d) : G.treeDist (G.next u d) d < G.treeDist u d := by
  unfold next
  by_cases h : G.anc u d
  · have := G.dep_lt_of_anc h hne
    simp only [treeDist, h, ite_true, G.anc_down h hne, G.dep_down h hne]
    omega
  · have hr := G.ne_root_of_not_anc h
    have h1 := G.dep_par u hr
    simp only [treeDist, h, ite_false]
    split_ifs <;> omega

/-- The tree hop follows an edge of the graph. -/
theorem next_adj {u d : V} (hne : u ≠ d) : G.next u d ∈ G.nbrs u := by
  unfold next
  split_ifs with h
  · have := G.par_adj _ (G.down_ne_root h hne)
    rw [G.par_down h hne] at this
    exact G.symm _ _ this
  · exact G.par_adj u (G.ne_root_of_not_anc h)

/-- The maximal depth of the spanning tree. -/
def height : ℕ := G.verts.foldr (fun v m => max (G.dep v) m) 0

omit [DecidableEq V] in
/-- Every depth is at most the height. -/
theorem dep_le (v : V) : G.dep v ≤ G.height := by
  have : ∀ l : List V, v ∈ l → G.dep v ≤ l.foldr (fun v m => max (G.dep v) m) 0 := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons a l ih =>
      rcases List.mem_cons.1 hl with rfl | hl
      · exact le_max_left _ _
      · exact (ih hl).trans (le_max_right _ _)
  exact this _ (G.mem_verts v)

/-- Every tree distance is at most twice the height. -/
theorem treeDist_le (v d : V) : G.treeDist v d ≤ 2 * G.height := by
  have := G.dep_le v; have := G.dep_le d
  unfold treeDist; split_ifs <;> omega

/-! ### The network -/

/-- The escape hop: tree routing on virtual channel 0. -/
def escHop (c : GChan V) (d : V) : GChan V × V := (.link c.head (G.next c.head d) false, d)

/-- The escape subfunction: the single escape hop. -/
def escape (c : GChan V) (d : V) : List (GChan V × V) := [G.escHop c d]

/-- The adaptive hops: every neighbour closer to the destination, on virtual channel 1. -/
def adaptiveHops (c : GChan V) (d : V) : List (GChan V × V) :=
  ((G.nbrs c.head).filter fun v => G.dist v d < G.dist c.head d).map fun v =>
    (.link c.head v true, d)

/-- **The network on the graph**: minimal adaptive routing on virtual channel 1, with an
absorbing tree-routing escape layer on virtual channel 0.  Every vertex injects packets for
every destination. -/
def net : Network (GChan V) V where
  arrived c d := decide (c.head = d)
  route c d := if c.isEsc then G.escape c d else G.escape c d ++ G.adaptiveHops c d
  inject := G.verts.flatMap fun s => G.verts.map fun d => (.inj s, d)

/-- A packet that has not arrived is not at its destination. -/
theorem arrived_false {c : GChan V} {d : V} (h : G.net.arrived c d = false) : c.head ≠ d := by
  simpa [net] using h

/-- The permitted hops: the escape hop, and (outside the escape layer) the adaptive hops. -/
theorem mem_route {c : GChan V} {d : V} {q : GChan V × V} (h : q ∈ G.net.route c d) :
    q = G.escHop c d ∨ c.isEsc = false ∧
      ∃ v ∈ G.nbrs c.head, G.dist v d < G.dist c.head d ∧ q = (.link c.head v true, d) := by
  simp only [net] at h
  split_ifs at h with hc
  · simp only [escape, List.mem_singleton] at h; exact Or.inl h
  · simp only [escape, adaptiveHops, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
      List.mem_map, List.mem_filter, decide_eq_true_eq] at h
    rcases h with h | ⟨v, ⟨hv, hd⟩, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨by simpa using hc, v, hv, hd, rfl⟩

/-- **Every hop follows an edge of the graph.** -/
theorem route_adj {c : GChan V} {d : V} {q : GChan V × V} (ha : G.net.arrived c d = false)
    (h : q ∈ G.net.route c d) : ∃ v ∈ G.nbrs c.head, ∃ vc, q.1 = .link c.head v vc ∧ q.2 = d := by
  rcases G.mem_route h with rfl | ⟨-, v, hv, -, rfl⟩
  · exact ⟨_, G.next_adj (G.arrived_false ha), false, rfl, rfl⟩
  · exact ⟨v, hv, true, rfl, rfl⟩

/-- When `dist` is the graph distance (every vertex other than the destination has a neighbour
one step closer), the adaptive layer offers a hop to every packet that has not arrived. -/
theorem adaptive_ne_nil
    (hdist : ∀ u d, u ≠ d → ∃ v ∈ G.nbrs u, G.dist v d + 1 = G.dist u d)
    {c : GChan V} {d : V} (ha : G.net.arrived c d = false) : G.adaptiveHops c d ≠ [] := by
  obtain ⟨v, hv, hd⟩ := hdist _ _ (G.arrived_false ha)
  have : (GChan.link c.head v true, d) ∈ G.adaptiveHops c d :=
    List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hv, by simp; omega⟩, rfl⟩
  exact List.ne_nil_of_mem this

/-! ### Legal pairs and the escape dependencies -/

/-- The pairs a packet can occupy: in virtual channel 0 of a link from a parent down to its
child, the destination lies below that child (the packet is in the *down* phase of its tree
route). -/
def legal : GChan V → V → Prop
  | .link u v false, d => v ≠ G.root → G.par v = u → G.anc v d
  | _, _ => True

omit [DecidableEq V] in
/-- The legality condition on an escape channel. -/
theorem legal_link_false {u v d : V} :
    G.legal (.link u v false) d ↔ (v ≠ G.root → G.par v = u → G.anc v d) := Iff.rfl

/-- The legal pairs contain the injections and are closed under routing. -/
theorem closed : G.net.Closed G.legal where
  inject q hq := by
    simp only [net, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨s, -, d, -, rfl⟩ := hq
    trivial
  route c d q _ ha hq := by
    rcases G.mem_route hq with rfl | ⟨-, v, -, -, rfl⟩
    · show G.legal (.link c.head (G.next c.head d) false) d
      rw [legal_link_false]
      intro hr hp
      unfold next at hr hp ⊢
      have hne := G.arrived_false ha
      split_ifs at hr hp ⊢ with h
      · exact G.anc_down h hne
      · have h1 := G.dep_par _ (G.ne_root_of_not_anc h)
        have h2 := G.dep_par _ hr
        rw [hp] at h2
        omega
    · trivial

/-- A position of every channel in the order of the escape dependencies: first the links down
the tree (deepest first), then the links up the tree (shallowest first), then the injection and
adaptive channels. -/
def escRank : GChan V → ℕ × ℕ
  | .link u v false => if v ≠ G.root ∧ G.par v = u then (0, G.height - G.dep v) else (1, G.dep v)
  | _ => (2, 0)

/-- The position of an escape channel. -/
theorem escRank_link_false (u v : V) : G.escRank (.link u v false) =
    if v ≠ G.root ∧ G.par v = u then (0, G.height - G.dep v) else (1, G.dep v) := rfl

/-- The position of an adaptive channel. -/
theorem escRank_link_true (u v : V) : G.escRank (.link u v true) = (2, 0) := rfl

/-- The position of an injection channel. -/
theorem escRank_inj (u : V) : G.escRank (.inj u) = (2, 0) := rfl

/-- **The escape dependencies are acyclic**: `escRank` decreases along every one of them.  An
escape hop goes up the tree (towards the root) or down it; a packet in a down channel has its
destination below, so it never turns back up. -/
theorem escRank_lt {c c' : GChan V} (h : G.net.Dep G.legal G.escape c c') :
    Prod.Lex (· < ·) (· < ·) (G.escRank c') (G.escRank c) := by
  obtain ⟨d, d', hl, ha, hq⟩ := h
  have hne := G.arrived_false ha
  simp only [escape, escHop, List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, -⟩ := hq
  by_cases han : G.anc c.head d
  · -- the escape hop goes down the tree
    have hn : G.next c.head d = G.down c.head d := by simp [next, han]
    have hdn := G.dep_down han hne
    have hle := G.dep_le (G.down c.head d)
    have hr' : escRank G (.link c.head (G.next c.head d) false) =
        (0, G.height - G.dep (G.down c.head d)) := by
      rw [hn, escRank_link_false]; simp [G.down_ne_root han hne, G.par_down han hne]
    rw [hr']
    rcases c with u | ⟨x, u, _ | _⟩
    · rw [escRank_inj]; exact Prod.Lex.left _ _ (by omega)
    · simp only [GChan.head] at hdn hle ⊢
      rw [escRank_link_false]
      split_ifs with h1
      · rw [Prod.lex_def]; right; refine ⟨rfl, ?_⟩; omega
      · exact Prod.Lex.left _ _ (by omega)
    · rw [escRank_link_true]; exact Prod.Lex.left _ _ (by omega)
  · -- the escape hop goes up the tree
    have hn : G.next c.head d = G.par c.head := by simp [next, han]
    have hr := G.ne_root_of_not_anc han
    have h1 := G.dep_par _ hr
    have hr' : escRank G (.link c.head (G.next c.head d) false) = (1, G.dep (G.par c.head)) := by
      rw [hn, escRank_link_false]
      split_ifs with h2
      · have := G.dep_par _ h2.1
        rw [h2.2] at this; omega
      · rfl
    rw [hr']
    rcases c with u | ⟨x, u, _ | _⟩
    · rw [escRank_inj]; exact Prod.Lex.left _ _ (by omega)
    · simp only [GChan.head] at h1 hr han ⊢
      rw [escRank_link_false]
      split_ifs with h2
      · exact absurd ((G.legal_link_false.1 hl) h2.1 h2.2) han
      · rw [Prod.lex_def]; right; refine ⟨rfl, ?_⟩; omega
    · rw [escRank_link_true]; exact Prod.Lex.left _ _ (by omega)

/-- The escape dependency graph is well-founded. -/
theorem esc_wf : WellFounded (flip (G.net.Dep G.legal G.escape)) :=
  Network.wf_of_lexRank G.escRank fun _ _ h => G.escRank_lt h

/-- The escape subfunction offers a hop to every packet. -/
theorem esc_conn : ∀ c d, G.legal c d → G.net.arrived c d = false → G.escape c d ≠ [] :=
  fun _ _ _ _ => List.cons_ne_nil _ _

/-- The escape hop is a permitted hop. -/
theorem esc_sub : ∀ c d q, G.legal c d → G.net.arrived c d = false → q ∈ G.escape c d →
    q ∈ G.net.route c d := by
  intro c d q _ _ hq
  simp only [net]
  split_ifs
  · exact hq
  · exact List.mem_append_left _ hq

/-- No escape hop leads into an injection channel. -/
theorem esc_not_inj : ∀ c d q, G.legal c d → G.net.arrived c d = false → q ∈ G.escape c d →
    ¬ q.1.isInj := by
  intro c d q _ _ hq
  simp only [escape, escHop, List.mem_singleton] at hq
  subst hq; simp [GChan.isInj]

/-! ### The ranking function -/

/-- The ranking of a packet: in the escape layer, its tree distance; elsewhere, a multiple of
its distance estimate large enough to exceed every tree distance. -/
def rank : GChan V → V → ℕ
  | .link _ v false, d => G.treeDist v d
  | c, d => (2 * G.height + 1) * (G.dist c.head d + 1)

/-- **The ranking decreases on every hop**: on virtual channel 1 the distance estimate drops, an
escape hop from virtual channel 1 lands below every multiple of `2 * height + 1`, and on virtual
channel 0 (absorbing) the tree distance drops. -/
theorem rank_lt : ∀ c d q, G.legal c d → G.net.arrived c d = false → q ∈ G.net.route c d →
    G.rank q.1 q.2 < G.rank c d := by
  intro c d q _ ha hq
  have hne := G.arrived_false ha
  have hesc : G.rank (G.escHop c d).1 (G.escHop c d).2 = G.treeDist (G.next c.head d) d := rfl
  have hB : ∀ c', c'.isEsc = false → G.rank c' d = (2 * G.height + 1) * (G.dist c'.head d + 1) := by
    rintro (_ | ⟨_, _, _ | _⟩) h <;> simp_all [rank, GChan.isEsc]
  rcases G.mem_route hq with rfl | ⟨hc, v, -, hv, rfl⟩
  · rw [hesc]
    have hlt := G.treeDist_next hne
    by_cases hc : c.isEsc
    · rcases c with _ | ⟨_, u, _ | _⟩ <;> simp_all [GChan.isEsc, rank, GChan.head]
    · rw [hB c (by simpa using hc)]
      have := G.treeDist_le (G.next c.head d) d
      have : 2 * G.height + 1 ≤ (2 * G.height + 1) * (G.dist c.head d + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
  · rw [hB c hc, hB _ rfl]
    exact Nat.mul_lt_mul_of_pos_left (by simpa [GChan.head] using hv) (by omega)

/-- There are finitely many legal pairs. -/
theorem pairs_finite : {q : GChan V × V | G.legal q.1 q.2}.Finite :=
  (Finset.finite_toSet ((GChan.all G.verts).product G.verts).toFinset).subset fun q _ => by
    obtain ⟨c, d⟩ := q
    simpa using List.pair_mem_product.2 ⟨GChan.mem_all G.mem_verts c, G.mem_verts d⟩

/-- Finitely many channels carry legal pairs. -/
theorem chans_finite : {c | ∃ d, G.legal c d}.Finite :=
  (G.pairs_finite.image Prod.fst).subset fun c ⟨d, hl⟩ => ⟨(c, d), hl, rfl⟩

/-! ### Correctness -/

/-- **Adaptive routing on every graph is correct**: deadlock free and livelock free under every
valid selection function, and starvation free under strongly fair scheduling (which, see the
module docstring, makes a run revisit the empty network). -/
theorem correct : G.net.Correct ∧ G.net.StarvationFree :=
  ⟨⟨G.net.deadlockFree_of_escape G.closed G.escape G.esc_sub G.esc_conn G.esc_wf,
    G.net.livelockFree_of_ranking G.closed G.chans_finite G.rank G.rank_lt⟩,
    G.net.starvationFree_of_escape_ranking G.closed G.pairs_finite G.escape G.esc_sub G.esc_conn
      G.esc_wf G.rank G.rank_lt⟩

/-- **Correct under selections that may decline adaptive hops**: under every selection that
never refuses a free escape hop, the network is deadlock, livelock and starvation free. -/
theorem correct_of_escapeSel {sel : Selection (GChan V) V} (hsel : G.net.EscapeSel G.escape sel) :
    G.net.DeadlockFreeWith sel ∧ G.net.LivelockFreeWith sel ∧ G.net.StarvationFreeWith sel :=
  ⟨G.net.deadlockFreeWith_of_escape G.closed G.escape G.esc_conn G.esc_wf hsel,
    G.net.livelockFreeWith_of_ranking G.closed G.chans_finite G.rank G.rank_lt hsel.sub,
    G.net.starvationFreeWith_of_source G.closed G.pairs_finite G.escape G.esc_conn G.esc_wf
      G.esc_not_inj G.rank G.rank_lt (EscapeSel.sourceSel G.net hsel fun c => c.isInj = true)⟩

/-- **Correct under throttled sources**: under every selection that never refuses a free escape
hop outside the injection channels, and lets a packet leave its injection channel once the rest
of the network is empty, the network is deadlock, livelock and starvation free. -/
theorem correct_of_sourceSel {sel : Selection (GChan V) V}
    (hsel : G.net.SourceSel G.escape (fun c => c.isInj) sel) :
    G.net.DeadlockFreeWith sel ∧ G.net.LivelockFreeWith sel ∧ G.net.StarvationFreeWith sel :=
  ⟨G.net.deadlockFreeWith_of_source G.closed G.escape G.esc_conn G.esc_wf G.esc_not_inj hsel,
    G.net.livelockFreeWith_of_ranking G.closed G.chans_finite G.rank G.rank_lt hsel.sub,
    G.net.starvationFreeWith_of_source G.closed G.pairs_finite G.escape G.esc_conn G.esc_wf
      G.esc_not_inj G.rank G.rank_lt hsel⟩

end GraphData

/-! ### Every connected graph has a spanning tree -/

section OfConnected

variable {V : Type*}

/-- `u` is reached from `r` by a walk of exactly `n` edges. -/
def WalkLen (nbrs : V → List V) (r : V) : ℕ → V → Prop
  | 0, u => u = r
  | n + 1, u => ∃ v, WalkLen nbrs r n v ∧ u ∈ nbrs v

/-- A walk of `n + 1` edges is a walk of `n` edges and one more edge. -/
theorem walkLen_succ {nbrs : V → List V} {r : V} {n : ℕ} {u : V} :
    WalkLen nbrs r (n + 1) u ↔ ∃ v, WalkLen nbrs r n v ∧ u ∈ nbrs v := Iff.rfl

/-- In a connected graph every vertex is reached by a walk of some length. -/
theorem exists_walkLen {nbrs : V → List V} {r : V}
    (conn : ∀ u, Relation.ReflTransGen (fun a b => b ∈ nbrs a) r u) (u : V) :
    ∃ n, WalkLen nbrs r n u := by
  induction conn u with
  | refl => exact ⟨0, rfl⟩
  | tail _ hab ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, walkLen_succ.2 ⟨_, hn, hab⟩⟩

open Classical in
/-- The breadth-first depth: the length of a shortest walk from the root. -/
noncomputable def bfsDep {nbrs : V → List V} {r : V}
    (conn : ∀ u, Relation.ReflTransGen (fun a b => b ∈ nbrs a) r u) (u : V) : ℕ :=
  Nat.find (exists_walkLen conn u)

open Classical in
/-- Every vertex other than the root has a neighbour one level closer to the root. -/
theorem exists_bfsPar {nbrs : V → List V} (symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v) {r : V}
    (conn : ∀ u, Relation.ReflTransGen (fun a b => b ∈ nbrs a) r u) (u : V) (hu : u ≠ r) :
    ∃ v, v ∈ nbrs u ∧ bfsDep conn v + 1 = bfsDep conn u := by
  have hspec := Nat.find_spec (exists_walkLen conn u)
  have hmin := fun m (hm : WalkLen nbrs r m u) => Nat.find_min' (exists_walkLen conn u) hm
  unfold bfsDep
  generalize Nat.find (exists_walkLen conn u) = n at hspec hmin ⊢
  cases n with
  | zero => exact absurd hspec hu
  | succ m =>
    obtain ⟨v, hv, huv⟩ := walkLen_succ.1 hspec
    refine ⟨v, symm _ _ huv, ?_⟩
    have h1 : Nat.find (exists_walkLen conn v) ≤ m := Nat.find_min' _ hv
    have h2 := hmin _ (walkLen_succ.2 ⟨v, Nat.find_spec (exists_walkLen conn v), huv⟩)
    omega

open Classical in
/-- **The breadth-first spanning tree of a connected graph**: from symmetric neighbour lists in
which every vertex is reachable from the root `r`, and any distance estimate. -/
noncomputable def GraphData.ofConnected (verts : List V) (mem_verts : ∀ v, v ∈ verts)
    (nbrs : V → List V)
    (symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v) (dist : V → V → ℕ) (r : V)
    (conn : ∀ u, Relation.ReflTransGen (fun a b => b ∈ nbrs a) r u) : GraphData V where
  verts := verts
  mem_verts := mem_verts
  nbrs := nbrs
  symm := symm
  dist := dist
  root := r
  par u := if h : u = r then r else Classical.choose (exists_bfsPar symm conn u h)
  dep := bfsDep conn
  dep_root := by
    classical
    exact Nat.find_eq_zero (exists_walkLen conn r) |>.2 rfl
  par_root := by simp
  dep_par u hu := by simp only [hu, ↓reduceDIte]; exact (Classical.choose_spec (exists_bfsPar symm conn u hu)).2
  par_adj u hu := by simp only [hu, ↓reduceDIte]; exact (Classical.choose_spec (exists_bfsPar symm conn u hu)).1

/-- **Every finite connected undirected graph carries a correct adaptive network**: with any
distance estimate `dist` for its adaptive layer, minimal adaptive routing on virtual channel 1
with tree routing along a breadth-first spanning tree as the absorbing escape layer on virtual
channel 0 is deadlock free and livelock free under every valid selection function and
starvation free under strongly fair scheduling. -/
theorem GraphData.exists_correct [DecidableEq V] (verts : List V) (mem_verts : ∀ v, v ∈ verts)
    (nbrs : V → List V) (symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v)
    (dist : V → V → ℕ) (r : V)
    (conn : ∀ u, Relation.ReflTransGen (fun a b => b ∈ nbrs a) r u) :
    ∃ G : GraphData V, G.nbrs = nbrs ∧ G.dist = dist ∧ G.net.Correct ∧ G.net.StarvationFree :=
  ⟨GraphData.ofConnected verts mem_verts nbrs symm dist r conn, rfl, rfl,
    (GraphData.ofConnected verts mem_verts nbrs symm dist r conn).correct⟩

end OfConnected

end AsyncLean
