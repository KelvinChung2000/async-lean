/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Graph
import AsyncLean.Routing.Reduce
import AsyncLean.Routing.Saturation

/-!
# Adaptive routing on every graph with a bounded number of returns from the escape layer

`AsyncLean.Routing.Graph` makes minimal adaptive routing safe on every finite connected graph
with tree routing along a spanning tree as the escape layer, but its escape layer is
**absorbing**: once a packet has entered virtual channel 0 it may only take escape hops, along
the (generally much longer) tree path.  That costs throughput.  Letting packets return from
virtual channel 0 to virtual channel 1 without limit is not livelock free in general: an escape
hop may move a packet away from its destination (tree paths are not shortest paths) and an
adaptive hop bring it back, for ever.

This file allows a **bounded number of returns**.  A packet header `(d, b)` carries the
destination `d` and a **return budget** `b`; packets are injected with the budget `B`, a
parameter of the network.

* From an injection channel or a virtual channel 1 channel: the escape hop and the adaptive hops
  (to every neighbour closer to `d` by `dist`, on virtual channel 1), header unchanged.
* From a virtual channel 0 channel: the escape hop, header unchanged; and, **if `b > 0`**, the
  adaptive hops, with the header `(d, b - 1)`: returning to virtual channel 1 spends one unit of
  budget.

With `B = 0` this is the absorbing network of `AsyncLean.Routing.Graph`, with every header
`d` written `(d, 0)` (`GraphData.budgetNet_route_zero`).

## The proofs

* **Deadlock freedom.**  The escape layer is the one of `GraphData.net`, and so are its channel
  dependencies: every dependency of `budgetEscape` on the legal pairs `budgetLegal` (the legal
  pairs of `GraphData.legal` for the destination, with a budget at most `B`) is a dependency of
  `GraphData.escape` on `GraphData.legal`, so the dependency graph is well-founded by
  `GraphData.esc_wf` and `Network.wf_dep_of_reduction` (`GraphData.budget_esc_wf`).
* **Livelock freedom.**  The ranking `budgetRank c (d, b) = b * rankBound + rank c d`, where
  `rank` is the ranking of `AsyncLean.Routing.Graph` and `rankBound` exceeds every value of it
  (`GraphData.rank_lt_rankBound`: `rankBound = (2 * height + 1) * (maxDist + 1) + 1`, where
  `maxDist` is the largest value of `dist` on the vertices).  A hop that keeps the header
  decreases `rank` (it is a hop of `GraphData.net`); a return lowers the budget by one, which
  outweighs any increase of `rank`.

## Main results

For every `G : GraphData V` and every budget `B`:

* `GraphData.budget_correct` : `G.budgetNet B` is deadlock free and livelock free under every
  valid selection function (`Network.Correct`), and starvation free under strongly fair
  scheduling (`Network.StarvationFree`).
* `GraphData.budget_correct_of_escapeSel` : deadlock, livelock and starvation free under every
  selection that never refuses a free escape hop (`Network.EscapeSel`).
* `GraphData.budget_correct_of_sourceSel` : the same under every selection that may in addition
  throttle the injection channels (`Network.SourceSel`).
* `GraphData.budget_underLoad_of_escapeSel`, `GraphData.budget_underLoad` : under every
  selection that never refuses a free escape hop (in particular every valid selection), every
  packet is delivered along every channel-fair run, with injections going on for ever
  (`Network.StarvationFreeUnderLoad`).
* `GraphData.budget_underLoad_of_sourceSel` : under a throttling selection, every packet outside
  the injection channels is delivered along every channel-fair run.
* `GraphData.budget_hops_le` : a packet injected at `s` for `d` takes at most
  `B * rankBound + (2 * height + 1) * (dist s d + 1)` hops.
* `GraphData.budget_route_adj` : every hop follows an edge of the graph;
  `GraphData.return_mem_route` : from virtual channel 0, a packet with a positive budget may
  take every adaptive hop, with one unit of budget less.
* `GraphData.budgetNet_route_zero` : with budget `0` the network is the absorbing one.
* `GraphData.exists_budget_correct` : every finite connected undirected graph, with any distance
  estimate and any return budget, carries such a network that is deadlock, livelock and
  starvation free, and delivers every packet under saturation.

## What is not covered

The hop bound grows linearly with `B`; nothing is said about throughput.  The starvation
statements inherit the caveats of `AsyncLean.Routing.Fairness` (strong fairness revisits the
empty network) and `AsyncLean.Routing.Saturation` (packets held back by a throttling source may
wait for ever under saturation).
-/

namespace AsyncLean

open Network

namespace GraphData

variable {V : Type*} [DecidableEq V] (G : GraphData V)

/-! ### The network -/

/-- The header a packet carries after an adaptive hop from `c`: unchanged from an injection or
virtual channel 1 channel, one unit of return budget less from a virtual channel 0 channel. -/
def retHdr (c : GChan V) (p : V × ℕ) : V × ℕ := if c.isEsc then (p.1, p.2 - 1) else p

/-- The adaptive hops are permitted: always outside the escape layer, and in the escape layer
while the return budget is positive. -/
def mayReturn (c : GChan V) (p : V × ℕ) : Bool := !c.isEsc || decide (p.2 ≠ 0)

/-- The escape subfunction: the tree-routing escape hop of `GraphData.net`, header unchanged. -/
def budgetEscape (c : GChan V) (p : V × ℕ) : List (GChan V × (V × ℕ)) :=
  [((G.escHop c p.1).1, p)]

/-- The adaptive hops of `GraphData.net`, carrying the header `retHdr c p`. -/
def budgetAdaptive (c : GChan V) (p : V × ℕ) : List (GChan V × (V × ℕ)) :=
  (G.adaptiveHops c p.1).map fun q => (q.1, retHdr c p)

/-- **The network with bounded returns**: headers `(d, b)` carry the destination and the
remaining return budget, packets are injected with budget `B`.  From every channel the escape
hop is permitted; the adaptive hops are permitted outside the escape layer, and from the escape
layer while the budget is positive, at the cost of one unit of budget. -/
def budgetNet (B : ℕ) : Network (GChan V) (V × ℕ) where
  arrived c p := decide (c.head = p.1)
  route c p := G.budgetEscape c p ++ if mayReturn c p then G.budgetAdaptive c p else []
  inject := G.verts.flatMap fun s => G.verts.map fun d => (.inj s, (d, B))

/-- A packet has arrived in `budgetNet` iff it has arrived in `net` (for its destination). -/
theorem budgetNet_arrived (B : ℕ) (c : GChan V) (p : V × ℕ) :
    (G.budgetNet B).arrived c p = G.net.arrived c p.1 := rfl

/-- The permitted hops of `budgetNet`: the escape hop with the header unchanged; an adaptive hop
from outside the escape layer with the header unchanged; an adaptive hop from the escape layer,
when the budget is positive, with one unit of budget less. -/
theorem mem_budgetRoute {B : ℕ} {c : GChan V} {p : V × ℕ} {q : GChan V × (V × ℕ)}
    (h : q ∈ (G.budgetNet B).route c p) :
    q = ((G.escHop c p.1).1, p) ∨
      ∃ v ∈ G.nbrs c.head, G.dist v p.1 < G.dist c.head p.1 ∧
        ((c.isEsc = false ∧ q = (.link c.head v true, p)) ∨
          (c.isEsc = true ∧ p.2 ≠ 0 ∧ q = (.link c.head v true, (p.1, p.2 - 1)))) := by
  simp only [budgetNet, budgetEscape, List.mem_append, List.mem_singleton] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    split_ifs at h with hm
    · simp only [budgetAdaptive, adaptiveHops, List.map_map, List.mem_map, List.mem_filter,
        decide_eq_true_eq, Function.comp_apply] at h
      obtain ⟨v, ⟨hv, hd⟩, rfl⟩ := h
      refine ⟨v, hv, hd, ?_⟩
      cases hc : c.isEsc
      · exact Or.inl ⟨rfl, by simp [retHdr, hc]⟩
      · refine Or.inr ⟨rfl, ?_, by simp [retHdr, hc]⟩
        simpa [mayReturn, hc] using hm
    · simp at h

/-- The escape hop is a permitted hop of `GraphData.net`. -/
theorem escHop_mem_route (c : GChan V) (d : V) : G.escHop c d ∈ G.net.route c d := by
  simp only [net]
  split_ifs
  · exact List.mem_singleton_self _
  · exact List.mem_append_left _ (List.mem_singleton_self _)

/-- An adaptive hop from outside the escape layer is a permitted hop of `GraphData.net`. -/
theorem adaptive_mem_route {c : GChan V} {d v : V} (hc : c.isEsc = false) (hv : v ∈ G.nbrs c.head)
    (hd : G.dist v d < G.dist c.head d) : (GChan.link c.head v true, d) ∈ G.net.route c d := by
  simp only [net, hc, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_append_right _
    (List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hv, by simpa using hd⟩, rfl⟩)

/-- **Returns are permitted**: from virtual channel 0 of a link into `w`, a packet with a positive
budget `b` may take every adaptive hop of `w` (to a neighbour closer to its destination), on
virtual channel 1, with budget `b - 1`. -/
theorem return_mem_route {B : ℕ} {u w v d : V} {b : ℕ} (hb : b ≠ 0) (hv : v ∈ G.nbrs w)
    (hd : G.dist v d < G.dist w d) :
    (GChan.link w v true, (d, b - 1)) ∈ (G.budgetNet B).route (.link u w false) (d, b) := by
  simp only [budgetNet, mayReturn, GChan.isEsc, Bool.not_false, Bool.not_true, ne_eq, hb,
    not_false_eq_true, decide_true, Bool.false_or, ↓reduceIte]
  exact List.mem_append_right _ (List.mem_map.2 ⟨(GChan.link w v true, d),
    List.mem_map.2 ⟨v, List.mem_filter.2 ⟨hv, decide_eq_true hd⟩, rfl⟩, by simp [retHdr, GChan.isEsc]⟩)

/-- **Every hop follows an edge of the graph.** -/
theorem budget_route_adj {B : ℕ} {c : GChan V} {p : V × ℕ} {q : GChan V × (V × ℕ)}
    (ha : (G.budgetNet B).arrived c p = false) (h : q ∈ (G.budgetNet B).route c p) :
    ∃ v ∈ G.nbrs c.head, ∃ vc, q.1 = .link c.head v vc := by
  rcases G.mem_budgetRoute h with rfl | ⟨v, hv, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩
  · exact ⟨_, G.next_adj (G.arrived_false ha), false, rfl⟩
  · exact ⟨v, hv, true, rfl⟩
  · exact ⟨v, hv, true, rfl⟩

/-- **With budget `0` the network is the absorbing network** `GraphData.net`: from a packet with
header `(d, 0)` the permitted hops are those of `GraphData.net` for `d`, with header `(d, 0)`;
and the injected packets are those of `GraphData.net`, with budget `0`. -/
theorem budgetNet_route_zero (c : GChan V) (d : V) :
    (G.budgetNet 0).route c (d, 0) = (G.net.route c d).map (fun q => (q.1, (q.2, 0))) ∧
      (G.budgetNet 0).inject = G.net.inject.map fun q => (q.1, (q.2, 0)) := by
  constructor
  · cases hc : c.isEsc
    · simp [budgetNet, net, hc, mayReturn, budgetEscape, budgetAdaptive, escape, escHop, retHdr,
        adaptiveHops, List.map_map, Function.comp_def]
    · simp [budgetNet, net, hc, mayReturn, budgetEscape, escape, escHop]
  · simp [budgetNet, net, List.map_flatMap, List.map_map, Function.comp_def]

/-! ### Legal pairs and the escape dependencies -/

/-- The pairs a packet can occupy: the legal pairs of `GraphData.legal` for its destination,
with a return budget at most `B`. -/
def budgetLegal (B : ℕ) (c : GChan V) (p : V × ℕ) : Prop := G.legal c p.1 ∧ p.2 ≤ B

/-- The legal pairs contain the injections and are closed under routing. -/
theorem budget_closed (B : ℕ) : (G.budgetNet B).Closed (G.budgetLegal B) where
  inject q hq := by
    simp only [budgetNet, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨s, -, d, -, rfl⟩ := hq
    exact ⟨trivial, le_rfl⟩
  route c p q hl ha hq := by
    rcases G.mem_budgetRoute hq with rfl | ⟨v, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩
    · exact ⟨G.closed.route c p.1 (G.escHop c p.1) hl.1 ha (G.escHop_mem_route c p.1), hl.2⟩
    · exact ⟨trivial, hl.2⟩
    · exact ⟨trivial, by have := hl.2; simp only; omega⟩

/-- **The escape dependencies of `budgetNet` are those of `GraphData.net`**: every dependency
of `budgetEscape` on the legal pairs is a dependency of `GraphData.escape`. -/
theorem budget_dep {B : ℕ} {c c' : GChan V}
    (h : (G.budgetNet B).Dep (G.budgetLegal B) G.budgetEscape c c') :
    G.net.Dep G.legal G.escape c c' := by
  obtain ⟨p, p', hl, ha, hq⟩ := h
  simp only [budgetEscape, List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, -⟩ := hq
  exact ⟨p.1, p.1, hl.1, ha, List.mem_singleton_self _⟩

/-- **The escape dependency graph is well-founded** (acyclic), by reduction to that of
`GraphData.net` (`GraphData.esc_wf`). -/
theorem budget_esc_wf (B : ℕ) :
    WellFounded (flip ((G.budgetNet B).Dep (G.budgetLegal B) G.budgetEscape)) :=
  (G.budgetNet B).wf_dep_of_reduction G.net id
    (fun _ _ h => Relation.TransGen.single (G.budget_dep h)) G.esc_wf

/-- The escape subfunction offers a hop to every packet. -/
theorem budget_esc_conn (B : ℕ) : ∀ c p, G.budgetLegal B c p →
    (G.budgetNet B).arrived c p = false → G.budgetEscape c p ≠ [] :=
  fun _ _ _ _ => List.cons_ne_nil _ _

/-- The escape hop is a permitted hop. -/
theorem budgetEscape_sub {B : ℕ} {c : GChan V} {p : V × ℕ} {q : GChan V × (V × ℕ)}
    (hq : q ∈ G.budgetEscape c p) : q ∈ (G.budgetNet B).route c p :=
  List.mem_append_left _ hq

/-- The escape hop is a permitted hop (in the form of Duato's theorem). -/
theorem budget_esc_sub (B : ℕ) : ∀ c p q, G.budgetLegal B c p →
    (G.budgetNet B).arrived c p = false → q ∈ G.budgetEscape c p → q ∈ (G.budgetNet B).route c p :=
  fun _ _ _ _ _ hq => G.budgetEscape_sub hq

/-- No hop of `budgetNet` leads into an injection channel. -/
theorem budget_route_not_inj {B : ℕ} {c : GChan V} {p : V × ℕ} {q : GChan V × (V × ℕ)}
    (hq : q ∈ (G.budgetNet B).route c p) : ¬ q.1.isInj := by
  rcases G.mem_budgetRoute hq with rfl | ⟨v, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ <;>
    simp [escHop, GChan.isInj]

/-- No escape hop leads into an injection channel. -/
theorem budget_esc_not_inj (B : ℕ) : ∀ c p q, G.budgetLegal B c p →
    (G.budgetNet B).arrived c p = false → q ∈ G.budgetEscape c p → ¬ q.1.isInj :=
  fun _ _ _ _ _ hq => G.budget_route_not_inj (B := B) (G.budgetEscape_sub hq)

/-! ### The ranking function -/

/-- The largest value of the distance estimate on the vertices. -/
def maxDist : ℕ := (G.verts.flatMap fun u => G.verts.map fun v => G.dist u v).foldr max 0

omit [DecidableEq V] in
/-- Every value of the distance estimate is at most `maxDist`. -/
theorem dist_le_maxDist (u v : V) : G.dist u v ≤ G.maxDist := by
  have key : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0 := by
    intro l x hx
    induction l with
    | nil => simp at hx
    | cons a l ih =>
      rcases List.mem_cons.1 hx with rfl | hx
      · exact le_max_left _ _
      · exact (ih hx).trans (le_max_right _ _)
  exact key _ _ (List.mem_flatMap.2 ⟨u, G.mem_verts u, List.mem_map.2 ⟨v, G.mem_verts v, rfl⟩⟩)

/-- A bound exceeding every value of the ranking `GraphData.rank`. -/
def rankBound : ℕ := (2 * G.height + 1) * (G.maxDist + 1) + 1

/-- **Every value of the ranking of `GraphData.net` is below `rankBound`.** -/
theorem rank_lt_rankBound (c : GChan V) (d : V) : G.rank c d < G.rankBound := by
  have hmul : (2 * G.height + 1) * (G.dist c.head d + 1) ≤
      (2 * G.height + 1) * (G.maxDist + 1) :=
    Nat.mul_le_mul_left _ (by have := G.dist_le_maxDist c.head d; omega)
  have h1 : 2 * G.height + 1 ≤ (2 * G.height + 1) * (G.maxDist + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold rankBound
  rcases c with u | ⟨x, u, _ | _⟩
  · exact Nat.lt_succ_of_le hmul
  · have := G.treeDist_le u d
    show G.treeDist u d < _
    omega
  · exact Nat.lt_succ_of_le hmul

/-- The ranking of a packet: its remaining return budget times `rankBound`, plus its ranking in
`GraphData.net`. -/
def budgetRank (c : GChan V) (p : V × ℕ) : ℕ := p.2 * G.rankBound + G.rank c p.1

/-- **The ranking decreases on every hop**: a hop that keeps the header is a hop of
`GraphData.net`, on which `GraphData.rank` decreases; a return from the escape layer lowers the
budget by one, which outweighs any increase of `GraphData.rank` (below `rankBound`). -/
theorem budget_rank_lt (B : ℕ) : ∀ c p q, G.budgetLegal B c p →
    (G.budgetNet B).arrived c p = false → q ∈ (G.budgetNet B).route c p →
    G.budgetRank q.1 q.2 < G.budgetRank c p := by
  intro c p q hl ha hq
  rcases G.mem_budgetRoute hq with rfl | ⟨v, hv, hd, ⟨hc, rfl⟩ | ⟨-, hb, rfl⟩⟩
  · have := G.rank_lt c p.1 _ hl.1 ha (G.escHop_mem_route c p.1)
    unfold budgetRank
    exact Nat.add_lt_add_left this _
  · have := G.rank_lt c p.1 _ hl.1 ha (G.adaptive_mem_route hc hv hd)
    unfold budgetRank
    exact Nat.add_lt_add_left this _
  · have h1 := G.rank_lt_rankBound (.link c.head v true) p.1
    unfold budgetRank
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hb
    simp only [hk, Nat.succ_sub_one, Nat.succ_mul]
    omega

/-- There are finitely many legal pairs. -/
theorem budget_pairs_finite (B : ℕ) :
    {q : GChan V × (V × ℕ) | G.budgetLegal B q.1 q.2}.Finite :=
  (Finset.finite_toSet ((GChan.all G.verts).product
      (G.verts.product (List.range (B + 1)))).toFinset).subset fun q hq => by
    obtain ⟨c, d, b⟩ := q
    have hb : b < B + 1 := Nat.lt_succ_of_le hq.2
    simpa using List.pair_mem_product.2 ⟨GChan.mem_all G.mem_verts c,
      List.pair_mem_product.2 ⟨G.mem_verts d, List.mem_range.2 hb⟩⟩

/-- Finitely many channels carry legal pairs. -/
theorem budget_chans_finite (B : ℕ) : {c | ∃ p, G.budgetLegal B c p}.Finite :=
  ((G.budget_pairs_finite B).image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩

/-- **Hop bound**: a packet injected at `s` for `d` reaches its destination within
`B * rankBound + (2 * height + 1) * (dist s d + 1)` hops, along every route. -/
theorem budget_hops_le {B : ℕ} {s d : V} {ls : List Unit} {q' : GChan V × (V × ℕ)}
    (h : (G.budgetNet B).packetLTS.Path (.inj s, (d, B)) ls q') :
    ls.length ≤ B * G.rankBound + (2 * G.height + 1) * (G.dist s d + 1) := by
  have := (G.budgetNet B).packet_hops_le (G.budget_closed B) G.budgetRank (G.budget_rank_lt B)
    (q := (.inj s, (d, B))) ⟨trivial, le_rfl⟩ h
  change _ + _ ≤ G.budgetRank (.inj s) (d, B) at this
  have e : G.budgetRank (.inj s) (d, B) = B * G.rankBound + (2 * G.height + 1) * (G.dist s d + 1) :=
    rfl
  omega

/-! ### Correctness -/

/-- **Adaptive routing with bounded returns on every graph is correct**: for every return budget
`B`, deadlock free and livelock free under every valid selection function, and starvation free
under strongly fair scheduling (which makes a run revisit the empty network; see
`budget_underLoad` for delivery under saturation). -/
theorem budget_correct (B : ℕ) : (G.budgetNet B).Correct ∧ (G.budgetNet B).StarvationFree :=
  ⟨⟨(G.budgetNet B).deadlockFree_of_escape (G.budget_closed B) G.budgetEscape (G.budget_esc_sub B)
      (G.budget_esc_conn B) (G.budget_esc_wf B),
    (G.budgetNet B).livelockFree_of_ranking (G.budget_closed B) (G.budget_chans_finite B)
      G.budgetRank (G.budget_rank_lt B)⟩,
    (G.budgetNet B).starvationFree_of_escape_ranking (G.budget_closed B) (G.budget_pairs_finite B)
      G.budgetEscape (G.budget_esc_sub B) (G.budget_esc_conn B) (G.budget_esc_wf B) G.budgetRank
      (G.budget_rank_lt B)⟩

/-- **Correct under selections that may decline adaptive hops**: under every selection that
never refuses a free escape hop, the network with return budget `B` is deadlock, livelock and
starvation free. -/
theorem budget_correct_of_escapeSel {B : ℕ} {sel : Selection (GChan V) (V × ℕ)}
    (hsel : (G.budgetNet B).EscapeSel G.budgetEscape sel) :
    (G.budgetNet B).DeadlockFreeWith sel ∧ (G.budgetNet B).LivelockFreeWith sel ∧
      (G.budgetNet B).StarvationFreeWith sel :=
  ⟨(G.budgetNet B).deadlockFreeWith_of_escape (G.budget_closed B) G.budgetEscape
      (G.budget_esc_conn B) (G.budget_esc_wf B) hsel,
    (G.budgetNet B).livelockFreeWith_of_ranking (G.budget_closed B) (G.budget_chans_finite B)
      G.budgetRank (G.budget_rank_lt B) hsel.sub,
    (G.budgetNet B).starvationFreeWith_of_source (G.budget_closed B) (G.budget_pairs_finite B)
      G.budgetEscape (G.budget_esc_conn B) (G.budget_esc_wf B) (G.budget_esc_not_inj B)
      G.budgetRank (G.budget_rank_lt B)
      (EscapeSel.sourceSel (G.budgetNet B) hsel fun c => c.isInj = true)⟩

/-- **Correct under throttled sources**: under every selection that never refuses a free escape
hop outside the injection channels, and lets a packet leave its injection channel once the rest
of the network is empty, the network with return budget `B` is deadlock, livelock and starvation
free. -/
theorem budget_correct_of_sourceSel {B : ℕ} {sel : Selection (GChan V) (V × ℕ)}
    (hsel : (G.budgetNet B).SourceSel G.budgetEscape (fun c => c.isInj) sel) :
    (G.budgetNet B).DeadlockFreeWith sel ∧ (G.budgetNet B).LivelockFreeWith sel ∧
      (G.budgetNet B).StarvationFreeWith sel :=
  ⟨(G.budgetNet B).deadlockFreeWith_of_source (G.budget_closed B) G.budgetEscape
      (G.budget_esc_conn B) (G.budget_esc_wf B) (G.budget_esc_not_inj B) hsel,
    (G.budgetNet B).livelockFreeWith_of_ranking (G.budget_closed B) (G.budget_chans_finite B)
      G.budgetRank (G.budget_rank_lt B) hsel.sub,
    (G.budgetNet B).starvationFreeWith_of_source (G.budget_closed B) (G.budget_pairs_finite B)
      G.budgetEscape (G.budget_esc_conn B) (G.budget_esc_wf B) (G.budget_esc_not_inj B)
      G.budgetRank (G.budget_rank_lt B) hsel⟩

/-! ### Delivery under saturation -/

/-- **Every packet is delivered under saturation**: under every selection that never refuses a
free escape hop, along every channel-fair run, with injections going on for ever. -/
theorem budget_underLoad_of_escapeSel {B : ℕ} {sel : Selection (GChan V) (V × ℕ)}
    (hsel : (G.budgetNet B).EscapeSel G.budgetEscape sel) :
    (G.budgetNet B).StarvationFreeUnderLoad sel (fun _ => False) :=
  (G.budgetNet B).starvationFreeUnderLoad_of_escape (G.budget_closed B) G.budgetEscape
    (G.budget_esc_conn B) (G.budget_esc_wf B) G.budgetRank (G.budget_rank_lt B) hsel

/-- **Every packet is delivered under saturation**, under every valid selection. -/
theorem budget_underLoad {B : ℕ} {sel : Selection (GChan V) (V × ℕ)}
    (hsel : (G.budgetNet B).ValidSel sel) :
    (G.budgetNet B).StarvationFreeUnderLoad sel (fun _ => False) :=
  G.budget_underLoad_of_escapeSel (ValidSel.escapeSel _ hsel fun _ _ _ hq => G.budgetEscape_sub hq)

/-- **Delivery under saturation with throttled sources**: under every selection that never
refuses a free escape hop outside the injection channels and releases a source's packet once the
rest of the network is empty, every packet outside the injection channels is delivered along
every channel-fair run.  A packet held back by the throttle may wait for ever under
saturation. -/
theorem budget_underLoad_of_sourceSel {B : ℕ} {sel : Selection (GChan V) (V × ℕ)}
    (hsel : (G.budgetNet B).SourceSel G.budgetEscape (fun c => c.isInj) sel) :
    (G.budgetNet B).StarvationFreeUnderLoad sel (fun c => c.isInj) :=
  (G.budgetNet B).starvationFreeUnderLoad_of_source (G.budget_closed B) G.budgetEscape
    (G.budget_esc_conn B) (G.budget_esc_wf B) (G.budget_esc_not_inj B)
    (fun _ _ _ _ _ hq => G.budget_route_not_inj hq) G.budgetRank (G.budget_rank_lt B) hsel

/-- **Every finite connected undirected graph carries a correct adaptive network with bounded
returns**: with any distance estimate `dist` and any return budget `B`, minimal adaptive
routing on virtual channel 1, with tree routing along a breadth-first spanning tree as the escape
layer on virtual channel 0 and at most `B` returns from it, is deadlock and livelock free under
every valid selection, starvation free under strongly fair scheduling, and delivers every packet
along every channel-fair run under every valid selection. -/
theorem exists_budget_correct (verts : List V) (mem_verts : ∀ v, v ∈ verts)
    (nbrs : V → List V) (symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v) (dist : V → V → ℕ) (r : V)
    (conn : ∀ u, Relation.ReflTransGen (fun a b => b ∈ nbrs a) r u) (B : ℕ) :
    ∃ G : GraphData V, G.nbrs = nbrs ∧ G.dist = dist ∧ (G.budgetNet B).Correct ∧
      (G.budgetNet B).StarvationFree ∧
      ∀ sel, (G.budgetNet B).ValidSel sel →
        (G.budgetNet B).StarvationFreeUnderLoad sel (fun _ => False) :=
  ⟨GraphData.ofConnected verts mem_verts nbrs symm dist r conn, rfl, rfl,
    (GraphData.ofConnected verts mem_verts nbrs symm dist r conn).budget_correct B |>.1,
    (GraphData.ofConnected verts mem_verts nbrs symm dist r conn).budget_correct B |>.2,
    fun _ hsel => (GraphData.ofConnected verts mem_verts nbrs symm dist r conn).budget_underLoad hsel⟩

end GraphData

end AsyncLean
