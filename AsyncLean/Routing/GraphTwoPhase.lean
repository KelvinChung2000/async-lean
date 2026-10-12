/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.GraphBudget

/-!
# Adaptive routing on every graph with two-phase routing through an intermediate vertex

`AsyncLean.Routing.GraphBudget` makes minimal adaptive routing with a bounded number of returns
from the escape subnetwork safe on every finite connected graph.  This file adds **two-phase
routing**: a packet may be sent first to an **intermediate vertex** `w`, chosen at the source
(Valiant's randomised routing, or a deterministic "long way round" on a torus), and only then to its
destination.  A packet header `(d, w, b)` carries

* the destination `d`;
* the intermediate `w : Option V` (`none`: no intermediate, or the first phase is over);
* the return budget `b` of `AsyncLean.Routing.GraphBudget`, `B` at injection.

The **target** of a packet is `w` while it is set, `d` otherwise (`GraphData.target`).

* From an injection or a virtual channel 1 channel: the escape hop (tree routing along the
  spanning tree towards the **final destination** `d`, on virtual channel 0), which **drops the
  intermediate** (`w := none`); and the adaptive hops, to every neighbour closer to the
  **target** by `dist`, on virtual channel 1, with the same budget.
* From a virtual channel 0 channel: the escape hop, header `(d, none, b)`; and, if `b > 0`, the
  adaptive hops with budget `b - 1`, as in `AsyncLean.Routing.GraphBudget`.
* An adaptive hop **into** the intermediate `w` drops it: the packet carries on with `w := none`
  (`GraphData.dropAt`).  Headers change only along hops, so dropping the intermediate is part of
  the hop into it, exactly as spending budget is part of a return hop.

Which intermediates a source may choose is a parameter `W : V → V → List (Option V)` of the
network (`W s d` lists the choices for a packet from `s` to `d`): `GraphData.anyIntermediate` allows
every intermediate other than the source, or none (Valiant's routing); `fun _ _ => [none]`
allows none, and then the network is exactly the one of `AsyncLean.Routing.GraphBudget`
(`GraphData.twoPhaseNet_route_none`, `GraphData.twoPhaseNet_inject_none`).  Every theorem holds for
every `W`.

A packet is delivered when it reaches its destination `d`, whether or not it has visited its
intermediate yet (it never has to leave its destination again); the escape subnetwork routes towards
`d` throughout.

## The proofs

* **Deadlock freedom.**  The escape hop is the escape hop of `GraphData.net` for the destination
  `d`, whatever the intermediate: every dependency of `twoPhaseEscape` on the legal pairs is a
  dependency of `GraphData.escape`, which is acyclic (`GraphData.esc_wf`), so the dependency
  graph is well-founded by `Network.wf_dep_of_reduction` (`GraphData.twoPhase_esc_wf`).
* **Livelock freedom.**  The ranking `twoPhaseRank` is `budgetRank` (`b * rankBound + rank`) once
  the intermediate is dropped, and `(b + 1) * rankBound + dist c.head w` while it is set.  A hop
  towards `w` decreases `dist · w` and keeps `b` (a packet heading for its intermediate is never
  in the escape subnetwork, but the proof does not need this); the hop into `w`, or an escape hop,
  drops to `b * rankBound + rank < (b + 1) * rankBound` (`GraphData.rank_lt_rankBound`); after
  that the ranking of `AsyncLean.Routing.GraphBudget` decreases.

## Main results

For every `G : GraphData V`, every budget `B` and every choice of intermediates `W`:

* `GraphData.twoPhase_correct` : `G.twoPhaseNet B W` is deadlock free and livelock free under every
  valid selection function (`Network.Correct`), and starvation free under strongly fair
  scheduling (`Network.StarvationFree`).
* `GraphData.twoPhase_correct_of_escapeSel` : deadlock, livelock and starvation free under every
  selection that never refuses a free escape hop (`Network.EscapeSel`).
* `GraphData.twoPhase_correct_of_sourceSel` : the same under every selection that may in addition
  throttle the injection channels (`Network.SourceSel`).
* `GraphData.twoPhase_underLoad_of_escapeSel`, `GraphData.twoPhase_underLoad` : under every
  selection that never refuses a free escape hop (in particular every valid selection), every packet
  is delivered along every channel-fair run, with injections going on for ever
  (`Network.StarvationFreeUnderLoad`); `GraphData.twoPhase_underLoad_of_sourceSel` : under a
  throttling selection, every packet outside the injection channels is.
* `GraphData.twoPhase_hops_le_some` : a packet injected at `s` for `d` with intermediate `w` takes
  at most `dist s w + (B + 1) * rankBound` hops; `GraphData.twoPhase_hops_le_none` : without an
  intermediate, at most the bound `B * rankBound + (2 * height + 1) * (dist s d + 1)` of
  `GraphData.budget_hops_le`; `GraphData.twoPhase_phase_hops_le` : while heading for its
  intermediate a packet takes at most `dist s w` hops (each one brings it closer to `w`).
* `GraphData.twoPhase_route_adj` : every hop follows an edge of the graph;
  `GraphData.twoPhaseAdaptive_ne_nil` : when `dist` is the graph distance, the adaptive layer offers
  a hop towards the target to every packet not at its target.
* `GraphData.twoPhaseNet_route_none`, `GraphData.twoPhaseNet_inject_none` : a packet without an
  intermediate is routed exactly as in `GraphData.budgetNet`, and with `W = fun _ _ => [none]`
  the injections are those of `GraphData.budgetNet`.
* `GraphData.exists_twoPhase_correct` : every finite connected undirected graph, with any distance
  estimate, any return budget and any choice of intermediates, carries such a network that is
  deadlock, livelock and starvation free, and delivers every packet under saturation.

## What is not covered

Nothing is said about throughput or load balance, the purpose of the intermediate; only safety and
the hop bounds.  The starvation statements inherit the caveats of `AsyncLean.Routing.Fairness` and
`AsyncLean.Routing.Saturation`.
-/

namespace AsyncLean

open Network

namespace GraphData

variable {V : Type*} [DecidableEq V] (G : GraphData V)

/-! ### The network -/

/-- The intermediate after a hop into `v`: dropped if it is `v`, unchanged otherwise. -/
def dropAt (v : V) (w : Option V) : Option V := if w = some v then none else w

/-- The target of a packet with header `(d, w, b)`: the intermediate `w` while it is set, the
destination `d` otherwise. -/
def target (p : V × Option V × ℕ) : V := p.2.1.getD p.1

/-- The escape subfunction: the tree-routing escape hop of `GraphData.net` towards the
destination, dropping the intermediate. -/
def twoPhaseEscape (c : GChan V) (p : V × Option V × ℕ) : List (GChan V × (V × Option V × ℕ)) :=
  [((G.escHop c p.1).1, (p.1, none, p.2.2))]

/-- The adaptive hops of `GraphData.net` towards the target, on virtual channel 1: the
intermediate is dropped on the hop into it, and a hop from the escape subnetwork spends one unit of
return budget. -/
def twoPhaseAdaptive (c : GChan V) (p : V × Option V × ℕ) : List (GChan V × (V × Option V × ℕ)) :=
  (G.adaptiveHops c (target p)).map fun q =>
    (q.1, (p.1, dropAt q.1.head p.2.1, (retHdr c (p.1, p.2.2)).2))

/-- **The network with two-phase routing and bounded returns**: headers `(d, w, b)` carry the
destination, the intermediate (if any) and the remaining return budget; a packet from `s` to `d` is
injected with an intermediate among `W s d` and budget `B`.  From every channel the escape hop
towards `d` is permitted (dropping the intermediate); the adaptive hops towards the target are
permitted outside the escape subnetwork, and from the escape subnetwork while the budget is
positive, at the cost of one unit of budget. -/
def twoPhaseNet (B : ℕ) (W : V → V → List (Option V)) : Network (GChan V) (V × Option V × ℕ) where
  arrived c p := decide (c.head = p.1)
  route c p := G.twoPhaseEscape c p ++ if mayReturn c (p.1, p.2.2) then G.twoPhaseAdaptive c p else
      []
  inject := G.verts.flatMap fun s => G.verts.flatMap fun d =>
    (W s d).map fun w => (.inj s, (d, w, B))

/-- Valiant's choice of intermediates: any vertex other than the source, or none. -/
def anyIntermediate (s _ : V) : List (Option V) := none :: (G.verts.filter (· ≠ s)).map some

/-- A packet has arrived in `twoPhaseNet` iff it has arrived in `net` (for its destination). -/
theorem twoPhaseNet_arrived (B : ℕ) (W : V → V → List (Option V)) (c : GChan V)
    (p : V × Option V × ℕ) : (G.twoPhaseNet B W).arrived c p = G.net.arrived c p.1 := rfl

/-- The permitted hops of `twoPhaseNet`: the escape hop towards the destination, dropping the
intermediate; an adaptive hop towards the target, from outside the escape subnetwork with the same
budget, from the escape subnetwork (when the budget is positive) with one unit less, dropping the
intermediate on the hop into it. -/
theorem mem_twoPhaseRoute {B : ℕ} {W : V → V → List (Option V)} {c : GChan V}
    {p : V × Option V × ℕ} {q : GChan V × (V × Option V × ℕ)}
    (h : q ∈ (G.twoPhaseNet B W).route c p) :
    q = ((G.escHop c p.1).1, (p.1, none, p.2.2)) ∨
      ∃ v ∈ G.nbrs c.head, G.dist v (target p) < G.dist c.head (target p) ∧
        ((c.isEsc = false ∧ q = (.link c.head v true, (p.1, dropAt v p.2.1, p.2.2))) ∨
          (c.isEsc = true ∧ p.2.2 ≠ 0 ∧
            q = (.link c.head v true, (p.1, dropAt v p.2.1, p.2.2 - 1)))) := by
  simp only [twoPhaseNet, twoPhaseEscape, List.mem_append, List.mem_singleton] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    split_ifs at h with hm
    · simp only [twoPhaseAdaptive, adaptiveHops, List.map_map, List.mem_map, List.mem_filter,
        decide_eq_true_eq, Function.comp_apply] at h
      obtain ⟨v, ⟨hv, hd⟩, rfl⟩ := h
      refine ⟨v, hv, hd, ?_⟩
      cases hc : c.isEsc
      · exact Or.inl ⟨rfl, by simp [retHdr, hc, GChan.head]⟩
      · refine Or.inr ⟨rfl, ?_, by simp [retHdr, hc, GChan.head]⟩
        simpa [mayReturn, hc] using hm
    · simp at h

/-- **Every hop follows an edge of the graph.** -/
theorem twoPhase_route_adj {B : ℕ} {W : V → V → List (Option V)} {c : GChan V}
    {p : V × Option V × ℕ} {q : GChan V × (V × Option V × ℕ)}
    (ha : (G.twoPhaseNet B W).arrived c p = false) (h : q ∈ (G.twoPhaseNet B W).route c p) :
    ∃ v ∈ G.nbrs c.head, ∃ vc, q.1 = .link c.head v vc := by
  rcases G.mem_twoPhaseRoute h with rfl | ⟨v, hv, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩
  · exact ⟨_, G.next_adj (G.arrived_false ha), false, rfl⟩
  · exact ⟨v, hv, true, rfl⟩
  · exact ⟨v, hv, true, rfl⟩

/-- When `dist` is the graph distance, the adaptive layer offers a hop towards the target to
every packet whose channel does not end at its target. -/
theorem twoPhaseAdaptive_ne_nil
    (hdist : ∀ u d, u ≠ d → ∃ v ∈ G.nbrs u, G.dist v d + 1 = G.dist u d)
    {c : GChan V} {p : V × Option V × ℕ} (h : c.head ≠ target p) : G.twoPhaseAdaptive c p ≠ [] := by
  have := G.adaptive_ne_nil hdist (c := c) (d := target p) (by simpa [net] using h)
  simpa [twoPhaseAdaptive] using this

/-- The header of a packet without an intermediate, as a header of `GraphData.budgetNet`
extended with no intermediate. -/
def liftHdr (q : GChan V × (V × ℕ)) : GChan V × (V × Option V × ℕ) := (q.1, (q.2.1, none, q.2.2))

/-- **A packet without an intermediate is routed as in `GraphData.budgetNet`**: its permitted
hops are those of `GraphData.budgetNet` (for any budgets `B`, `B'` at injection), with no
intermediate. -/
theorem twoPhaseNet_route_none (B B' : ℕ) (W : V → V → List (Option V)) (c : GChan V) (d : V)
    (b : ℕ) : (G.twoPhaseNet B W).route c (d, none, b) =
      ((G.budgetNet B').route c (d, b)).map (liftHdr (V := V)) := by
  cases hc : c.isEsc
  · simp [twoPhaseNet, budgetNet, hc, mayReturn, twoPhaseEscape, budgetEscape, twoPhaseAdaptive,
      budgetAdaptive, retHdr, liftHdr, target, dropAt, List.map_map, Function.comp_def]
  · simp only [twoPhaseNet, budgetNet, hc, mayReturn, twoPhaseEscape, budgetEscape,
      twoPhaseAdaptive,
      budgetAdaptive, retHdr, target]
    split_ifs <;> simp [liftHdr, dropAt, List.map_map, Function.comp_def]

/-- **Without intermediates the injections are those of `GraphData.budgetNet`**, with no
intermediate. -/
theorem twoPhaseNet_inject_none (B : ℕ) :
    (G.twoPhaseNet B fun _ _ => [none]).inject = (G.budgetNet B).inject.map (liftHdr (V := V)) := by
  simp [twoPhaseNet, budgetNet, liftHdr, List.map_flatMap, List.map_map, Function.comp_def,
    ← List.map_eq_flatMap]

/-! ### Legal pairs and the escape dependencies -/

/-- The pairs a packet can occupy: the legal pairs of `GraphData.legal` for its destination,
with a return budget at most `B` (any intermediate). -/
def twoPhaseLegal (B : ℕ) (c : GChan V) (p : V × Option V × ℕ) : Prop := G.legal c p.1 ∧ p.2.2 ≤ B

/-- The legal pairs contain the injections and are closed under routing. -/
theorem twoPhase_closed (B : ℕ) (W : V → V → List (Option V)) :
    (G.twoPhaseNet B W).Closed (G.twoPhaseLegal B) where
  inject q hq := by
    simp only [twoPhaseNet, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨s, -, d, -, w, -, rfl⟩ := hq
    exact ⟨trivial, le_rfl⟩
  route c p q hl ha hq := by
    rcases G.mem_twoPhaseRoute hq with rfl | ⟨v, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩
    · exact ⟨G.closed.route c p.1 (G.escHop c p.1) hl.1 ha (G.escHop_mem_route c p.1), hl.2⟩
    · exact ⟨trivial, hl.2⟩
    · exact ⟨trivial, by have := hl.2; simp only; omega⟩

/-- **The escape dependencies of `twoPhaseNet` are those of `GraphData.net`**: every dependency
of `twoPhaseEscape` on the legal pairs is a dependency of `GraphData.escape`. -/
theorem twoPhase_dep {B : ℕ} {W : V → V → List (Option V)} {c c' : GChan V}
    (h : (G.twoPhaseNet B W).Dep (G.twoPhaseLegal B) G.twoPhaseEscape c c') :
    G.net.Dep G.legal G.escape c c' := by
  obtain ⟨p, p', hl, ha, hq⟩ := h
  simp only [twoPhaseEscape, List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, -⟩ := hq
  exact ⟨p.1, p.1, hl.1, ha, List.mem_singleton_self _⟩

/-- **The escape dependency graph is well-founded** (acyclic), by reduction to that of
`GraphData.net` (`GraphData.esc_wf`). -/
theorem twoPhase_esc_wf (B : ℕ) (W : V → V → List (Option V)) :
    WellFounded (flip ((G.twoPhaseNet B W).Dep (G.twoPhaseLegal B) G.twoPhaseEscape)) :=
  (G.twoPhaseNet B W).wf_dep_of_reduction G.net id
    (fun _ _ h => Relation.TransGen.single (G.twoPhase_dep h)) G.esc_wf

/-- The escape subfunction offers a hop to every packet. -/
theorem twoPhase_esc_conn (B : ℕ) (W : V → V → List (Option V)) : ∀ c p, G.twoPhaseLegal B c p →
    (G.twoPhaseNet B W).arrived c p = false → G.twoPhaseEscape c p ≠ [] :=
  fun _ _ _ _ => List.cons_ne_nil _ _

/-- The escape hop is a permitted hop. -/
theorem twoPhaseEscape_sub {B : ℕ} {W : V → V → List (Option V)} {c : GChan V}
    {p : V × Option V × ℕ} {q : GChan V × (V × Option V × ℕ)}
    (hq : q ∈ G.twoPhaseEscape c p) : q ∈ (G.twoPhaseNet B W).route c p :=
  List.mem_append_left _ hq

/-- The escape hop is a permitted hop (in the form of Duato's theorem). -/
theorem twoPhase_esc_sub (B : ℕ) (W : V → V → List (Option V)) : ∀ c p q, G.twoPhaseLegal B c p →
    (G.twoPhaseNet B W).arrived c p = false → q ∈ G.twoPhaseEscape c p →
      q ∈ (G.twoPhaseNet B W).route c p :=
  fun _ _ _ _ _ hq => G.twoPhaseEscape_sub hq

/-- No hop of `twoPhaseNet` leads into an injection channel. -/
theorem twoPhase_route_not_inj {B : ℕ} {W : V → V → List (Option V)} {c : GChan V}
    {p : V × Option V × ℕ} {q : GChan V × (V × Option V × ℕ)}
    (hq : q ∈ (G.twoPhaseNet B W).route c p) : ¬ q.1.isInj := by
  rcases G.mem_twoPhaseRoute hq with rfl | ⟨v, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ <;>
    simp [escHop, GChan.isInj]

/-- No escape hop leads into an injection channel. -/
theorem twoPhase_esc_not_inj (B : ℕ) (W : V → V → List (Option V)) : ∀ c p q, G.twoPhaseLegal B c p
    →
    (G.twoPhaseNet B W).arrived c p = false → q ∈ G.twoPhaseEscape c p → ¬ q.1.isInj :=
  fun _ _ _ _ _ hq => G.twoPhase_route_not_inj (B := B) (W := W) (G.twoPhaseEscape_sub hq)

/-! ### The ranking function -/

/-- The ranking of a packet: without an intermediate, its ranking `budgetRank` in
`GraphData.budgetNet`; while heading for its intermediate `w`, one more unit of budget than it
has, times `rankBound`, plus its distance estimate to `w`. -/
def twoPhaseRank (c : GChan V) (p : V × Option V × ℕ) : ℕ :=
  match p.2.1 with
  | none => G.budgetRank c (p.1, p.2.2)
  | some w => (p.2.2 + 1) * G.rankBound + G.dist c.head w

/-- Without an intermediate, the budget ranking is below one more unit of budget. -/
theorem budgetRank_lt (c : GChan V) (d : V) (b : ℕ) :
    G.budgetRank c (d, b) < (b + 1) * G.rankBound := by
  have := G.rank_lt_rankBound c d
  unfold budgetRank
  simp only [Nat.succ_mul]
  omega

/-- **The ranking decreases on every hop**: without an intermediate the hop is a hop of
`GraphData.budgetNet`, on which `budgetRank` decreases; a hop towards the intermediate `w`
decreases the distance estimate to `w` and does not increase the budget; the hop into `w` and an
escape hop drop the intermediate, landing below `(b + 1) * rankBound`. -/
theorem twoPhase_rank_lt (B : ℕ) (W : V → V → List (Option V)) : ∀ c p q, G.twoPhaseLegal B c p →
    (G.twoPhaseNet B W).arrived c p = false → q ∈ (G.twoPhaseNet B W).route c p →
    G.twoPhaseRank q.1 q.2 < G.twoPhaseRank c p := by
  rintro c ⟨d, w, b⟩ q hl ha hq
  cases w with
  | none =>
    rw [G.twoPhaseNet_route_none B B W c d b, List.mem_map] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    exact G.budget_rank_lt B c (d, b) q₀ hl ha hq₀
  | some w =>
    have hlt : ∀ c' b', b' ≤ b → G.budgetRank c' (d, b') < G.twoPhaseRank c (d, some w, b) := by
      intro c' b' hb'
      have h1 := G.budgetRank_lt c' d b'
      have h2 : (b' + 1) * G.rankBound ≤ (b + 1) * G.rankBound :=
        Nat.mul_le_mul_right _ (by omega)
      show _ < (b + 1) * G.rankBound + _
      omega
    rcases G.mem_twoPhaseRoute hq with rfl | ⟨v, -, hd, ⟨-, rfl⟩ | ⟨-, hb, rfl⟩⟩
    · exact hlt _ b le_rfl
    · simp only [target, Option.getD_some] at hd
      unfold dropAt
      split_ifs with hv
      · exact hlt _ b le_rfl
      · show (b + 1) * G.rankBound + G.dist v w < (b + 1) * G.rankBound + G.dist c.head w
        omega
    · simp only [target, Option.getD_some] at hd
      unfold dropAt
      split_ifs with hv
      · exact hlt _ (b - 1) (by omega)
      · have hb' : b ≠ 0 := hb
        show (b - 1 + 1) * G.rankBound + G.dist v w < (b + 1) * G.rankBound + G.dist c.head w
        have : (b - 1 + 1) * G.rankBound ≤ (b + 1) * G.rankBound :=
          Nat.mul_le_mul_right _ (by omega)
        omega

/-- There are finitely many legal pairs. -/
theorem twoPhase_pairs_finite (B : ℕ) :
    {q : GChan V × (V × Option V × ℕ) | G.twoPhaseLegal B q.1 q.2}.Finite :=
  (Finset.finite_toSet ((GChan.all G.verts).product (G.verts.product
      ((none :: G.verts.map some).product (List.range (B + 1))))).toFinset).subset fun q hq => by
    obtain ⟨c, d, w, b⟩ := q
    have hb : b < B + 1 := Nat.lt_succ_of_le hq.2
    have hw : w ∈ none :: G.verts.map some := by
      cases w <;> simp [G.mem_verts]
    simpa using List.pair_mem_product.2 ⟨GChan.mem_all G.mem_verts c,
      List.pair_mem_product.2 ⟨G.mem_verts d,
        List.pair_mem_product.2 ⟨hw, List.mem_range.2 hb⟩⟩⟩

/-- Finitely many channels carry legal pairs. -/
theorem twoPhase_chans_finite (B : ℕ) : {c | ∃ p, G.twoPhaseLegal B c p}.Finite :=
  ((G.twoPhase_pairs_finite B).image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩

/-! ### Hop bounds -/

/-- **Hop bound**: a packet injected at `s` for `d` with intermediate `w` reaches its
destination within `twoPhaseRank (.inj s) (d, w, B)` hops, along every route. -/
theorem twoPhase_hops_le {B : ℕ} {W : V → V → List (Option V)} {s d : V} {w : Option V}
    {ls : List Unit} {q' : GChan V × (V × Option V × ℕ)}
    (h : (G.twoPhaseNet B W).packetLTS.Path (.inj s, (d, w, B)) ls q') :
    ls.length ≤ G.twoPhaseRank (.inj s) (d, w, B) := by
  have := (G.twoPhaseNet B W).packet_hops_le (G.twoPhase_closed B W) G.twoPhaseRank
      (G.twoPhase_rank_lt B W)
    (q := (.inj s, (d, w, B))) ⟨trivial, le_rfl⟩ h
  exact (Nat.le_add_left _ _).trans this

/-- **Hop bound with an intermediate**: a packet injected at `s` for `d` with intermediate `w`
reaches its destination within `dist s w + (B + 1) * rankBound` hops, along every route: at most
`dist s w` hops towards `w` (`twoPhase_phase_hops_le`), and then less than the bound
`(B + 1) * rankBound` of `GraphData.budgetNet` from any channel. -/
theorem twoPhase_hops_le_some {B : ℕ} {W : V → V → List (Option V)} {s d w : V}
    {ls : List Unit} {q' : GChan V × (V × Option V × ℕ)}
    (h : (G.twoPhaseNet B W).packetLTS.Path (.inj s, (d, some w, B)) ls q') :
    ls.length ≤ G.dist s w + (B + 1) * G.rankBound := by
  have := G.twoPhase_hops_le h
  change _ ≤ (B + 1) * G.rankBound + G.dist s w at this
  omega

/-- **Hop bound without an intermediate**: a packet injected at `s` for `d` without an intermediate
reaches its destination within `B * rankBound + (2 * height + 1) * (dist s d + 1)` hops, the
bound of `GraphData.budget_hops_le`. -/
theorem twoPhase_hops_le_none {B : ℕ} {W : V → V → List (Option V)} {s d : V}
    {ls : List Unit} {q' : GChan V × (V × Option V × ℕ)}
    (h : (G.twoPhaseNet B W).packetLTS.Path (.inj s, (d, none, B)) ls q') :
    ls.length ≤ B * G.rankBound + (2 * G.height + 1) * (G.dist s d + 1) :=
  G.twoPhase_hops_le h

/-- A hop never sets an intermediate: from a packet without one, every hop leads to a packet
without one. -/
theorem route_none {B : ℕ} {W : V → V → List (Option V)} {c : GChan V} {d : V} {b : ℕ}
    {q : GChan V × (V × Option V × ℕ)} (hq : q ∈ (G.twoPhaseNet B W).route c (d, none, b)) :
    q.2.2.1 = none := by
  rw [G.twoPhaseNet_route_none B B W c d b, List.mem_map] at hq
  obtain ⟨q₀, -, rfl⟩ := hq
  rfl

/-- A hop that keeps the intermediate `w` brings the packet closer to `w` by the distance
estimate; every other hop drops it. -/
theorem route_some {B : ℕ} {W : V → V → List (Option V)} {c : GChan V} {d w : V} {b : ℕ}
    {q : GChan V × (V × Option V × ℕ)} (hq : q ∈ (G.twoPhaseNet B W).route c (d, some w, b)) :
    q.2.2.1 = none ∨ q.2.2.1 = some w ∧ G.dist q.1.head w < G.dist c.head w := by
  rcases G.mem_twoPhaseRoute hq with rfl | ⟨v, -, hd, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩
  · exact Or.inl rfl
  all_goals
    simp only [target, Option.getD_some] at hd
    simp only [dropAt]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, hd⟩

/-- Once the intermediate is dropped it stays dropped, along every route. -/
theorem path_none {B : ℕ} {W : V → V → List (Option V)}
    {q q' : GChan V × (V × Option V × ℕ)} {ls : List Unit}
    (h : (G.twoPhaseNet B W).packetLTS.Path q ls q') (hq : q.2.2.1 = none) : q'.2.2.1 = none := by
  induction h with
  | nil => exact hq
  | @cons q₁ q₂ q₃ l ls hst hp ih =>
    obtain ⟨c, d, w, b⟩ := q₁
    simp only at hq; subst hq
    exact ih (G.route_none hst.2)

/-- **Each phase is minimal**: along every route that keeps the intermediate `w`, each hop brings
the packet closer to `w` by the distance estimate, so a packet heading for `w` takes at most
`dist s w` hops before reaching `w` or dropping it (`dist` being the graph distance, a shortest
path to `w`). -/
theorem twoPhase_phase_hops_le {B : ℕ} {W : V → V → List (Option V)} {w : V}
    {q q' : GChan V × (V × Option V × ℕ)} {ls : List Unit}
    (h : (G.twoPhaseNet B W).packetLTS.Path q ls q') (hq : q.2.2.1 = some w)
    (hq' : q'.2.2.1 = some w) : ls.length + G.dist q'.1.head w ≤ G.dist q.1.head w := by
  induction h with
  | nil => simp
  | @cons q₁ q₂ q₃ l ls hst hp ih =>
    obtain ⟨c, d, w₁, b⟩ := q₁
    simp only at hq; subst hq
    obtain ⟨-, hr⟩ := hst
    rcases G.route_some hr with h0 | ⟨h1, h2⟩
    · have := G.path_none hp h0
      rw [hq'] at this; exact absurd this (by simp)
    · have := ih h1 hq'
      have h2' : G.dist q₂.1.head w < G.dist c.head w := h2
      show ls.length + 1 + _ ≤ G.dist c.head w
      omega

/-! ### Correctness -/

/-- **Adaptive two-phase routing and bounded returns on every graph is correct**: for every
return budget `B` and every choice of intermediates `W`, deadlock free and livelock free under
every valid selection function, and starvation free under strongly fair scheduling (which makes a
run revisit the empty network; see `twoPhase_underLoad` for delivery under saturation). -/
theorem twoPhase_correct (B : ℕ) (W : V → V → List (Option V)) :
    (G.twoPhaseNet B W).Correct ∧ (G.twoPhaseNet B W).StarvationFree :=
  ⟨⟨(G.twoPhaseNet B W).deadlockFree_of_escape (G.twoPhase_closed B W) G.twoPhaseEscape
      (G.twoPhase_esc_sub B W) (G.twoPhase_esc_conn B W) (G.twoPhase_esc_wf B W),
    (G.twoPhaseNet B W).livelockFree_of_ranking (G.twoPhase_closed B W) (G.twoPhase_chans_finite B)
      G.twoPhaseRank (G.twoPhase_rank_lt B W)⟩,
    (G.twoPhaseNet B W).starvationFree_of_escape_ranking (G.twoPhase_closed B W)
      (G.twoPhase_pairs_finite B) G.twoPhaseEscape (G.twoPhase_esc_sub B W) (G.twoPhase_esc_conn B
          W)
      (G.twoPhase_esc_wf B W) G.twoPhaseRank (G.twoPhase_rank_lt B W)⟩

/-- **Correct under selections that may decline adaptive hops**: under every selection that
never refuses a free escape hop, the network with two-phase routing and return budget `B` is
deadlock, livelock and starvation free. -/
theorem twoPhase_correct_of_escapeSel {B : ℕ} {W : V → V → List (Option V)}
    {sel : Selection (GChan V) (V × Option V × ℕ)}
    (hsel : (G.twoPhaseNet B W).EscapeSel G.twoPhaseEscape sel) :
    (G.twoPhaseNet B W).DeadlockFreeWith sel ∧ (G.twoPhaseNet B W).LivelockFreeWith sel ∧
      (G.twoPhaseNet B W).StarvationFreeWith sel :=
  ⟨(G.twoPhaseNet B W).deadlockFreeWith_of_escape (G.twoPhase_closed B W) G.twoPhaseEscape
      (G.twoPhase_esc_conn B W) (G.twoPhase_esc_wf B W) hsel,
    (G.twoPhaseNet B W).livelockFreeWith_of_ranking (G.twoPhase_closed B W) (G.twoPhase_chans_finite
        B)
      G.twoPhaseRank (G.twoPhase_rank_lt B W) hsel.sub,
    (G.twoPhaseNet B W).starvationFreeWith_of_source (G.twoPhase_closed B W)
        (G.twoPhase_pairs_finite B)
      G.twoPhaseEscape (G.twoPhase_esc_conn B W) (G.twoPhase_esc_wf B W) (G.twoPhase_esc_not_inj B
          W)
      G.twoPhaseRank (G.twoPhase_rank_lt B W)
      (EscapeSel.sourceSel (G.twoPhaseNet B W) hsel fun c => c.isInj = true)⟩

/-- **Correct under throttled sources**: under every selection that never refuses a free escape
hop outside the injection channels, and lets a packet leave its injection channel once the rest
of the network is empty, the network with two-phase routing and return budget `B` is deadlock,
livelock and starvation free. -/
theorem twoPhase_correct_of_sourceSel {B : ℕ} {W : V → V → List (Option V)}
    {sel : Selection (GChan V) (V × Option V × ℕ)}
    (hsel : (G.twoPhaseNet B W).SourceSel G.twoPhaseEscape (fun c => c.isInj) sel) :
    (G.twoPhaseNet B W).DeadlockFreeWith sel ∧ (G.twoPhaseNet B W).LivelockFreeWith sel ∧
      (G.twoPhaseNet B W).StarvationFreeWith sel :=
  ⟨(G.twoPhaseNet B W).deadlockFreeWith_of_source (G.twoPhase_closed B W) G.twoPhaseEscape
      (G.twoPhase_esc_conn B W) (G.twoPhase_esc_wf B W) (G.twoPhase_esc_not_inj B W) hsel,
    (G.twoPhaseNet B W).livelockFreeWith_of_ranking (G.twoPhase_closed B W) (G.twoPhase_chans_finite
        B)
      G.twoPhaseRank (G.twoPhase_rank_lt B W) hsel.sub,
    (G.twoPhaseNet B W).starvationFreeWith_of_source (G.twoPhase_closed B W)
        (G.twoPhase_pairs_finite B)
      G.twoPhaseEscape (G.twoPhase_esc_conn B W) (G.twoPhase_esc_wf B W) (G.twoPhase_esc_not_inj B
          W)
      G.twoPhaseRank (G.twoPhase_rank_lt B W) hsel⟩

/-! ### Delivery under saturation -/

/-- **Every packet is delivered under saturation**: under every selection that never refuses a
free escape hop, along every channel-fair run, with injections going on for ever. -/
theorem twoPhase_underLoad_of_escapeSel {B : ℕ} {W : V → V → List (Option V)}
    {sel : Selection (GChan V) (V × Option V × ℕ)}
    (hsel : (G.twoPhaseNet B W).EscapeSel G.twoPhaseEscape sel) :
    (G.twoPhaseNet B W).StarvationFreeUnderLoad sel (fun _ => False) :=
  (G.twoPhaseNet B W).starvationFreeUnderLoad_of_escape (G.twoPhase_closed B W) G.twoPhaseEscape
    (G.twoPhase_esc_conn B W) (G.twoPhase_esc_wf B W) G.twoPhaseRank (G.twoPhase_rank_lt B W) hsel

/-- **Every packet is delivered under saturation**, under every valid selection. -/
theorem twoPhase_underLoad {B : ℕ} {W : V → V → List (Option V)}
    {sel : Selection (GChan V) (V × Option V × ℕ)} (hsel : (G.twoPhaseNet B W).ValidSel sel) :
    (G.twoPhaseNet B W).StarvationFreeUnderLoad sel (fun _ => False) :=
  G.twoPhase_underLoad_of_escapeSel
    (ValidSel.escapeSel _ hsel fun _ _ _ hq => G.twoPhaseEscape_sub hq)

/-- **Delivery under saturation with throttled sources**: under every selection that never
refuses a free escape hop outside the injection channels and releases a source's packet once the
rest of the network is empty, every packet outside the injection channels is delivered along
every channel-fair run.  A packet held back by the throttle may wait for ever under
saturation. -/
theorem twoPhase_underLoad_of_sourceSel {B : ℕ} {W : V → V → List (Option V)}
    {sel : Selection (GChan V) (V × Option V × ℕ)}
    (hsel : (G.twoPhaseNet B W).SourceSel G.twoPhaseEscape (fun c => c.isInj) sel) :
    (G.twoPhaseNet B W).StarvationFreeUnderLoad sel (fun c => c.isInj) :=
  (G.twoPhaseNet B W).starvationFreeUnderLoad_of_source (G.twoPhase_closed B W) G.twoPhaseEscape
    (G.twoPhase_esc_conn B W) (G.twoPhase_esc_wf B W) (G.twoPhase_esc_not_inj B W)
    (fun _ _ _ _ _ hq => G.twoPhase_route_not_inj hq) G.twoPhaseRank (G.twoPhase_rank_lt B W) hsel

/-- **Every finite connected undirected graph carries a correct adaptive network with two-phase
routing and bounded returns**: with any distance estimate `dist`, any return budget `B` and any
choice of intermediates `W`, minimal adaptive routing towards the intermediate and then the
destination on virtual channel 1, with tree routing towards the destination along a breadth-first
spanning tree as the escape subnetwork on virtual channel 0 and at most `B` returns from it, is
deadlock and livelock free under every valid selection, starvation free under strongly fair
scheduling, and delivers every packet along every channel-fair run under every valid selection. -/
theorem exists_twoPhase_correct (verts : List V) (mem_verts : ∀ v, v ∈ verts)
    (nbrs : V → List V) (symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v) (dist : V → V → ℕ) (r : V)
    (conn : ∀ u, Relation.ReflTransGen (fun a b => b ∈ nbrs a) r u) (B : ℕ)
    (W : V → V → List (Option V)) :
    ∃ G : GraphData V, G.nbrs = nbrs ∧ G.dist = dist ∧ (G.twoPhaseNet B W).Correct ∧
      (G.twoPhaseNet B W).StarvationFree ∧
      ∀ sel, (G.twoPhaseNet B W).ValidSel sel →
        (G.twoPhaseNet B W).StarvationFreeUnderLoad sel (fun _ => False) :=
  ⟨GraphData.ofConnected verts mem_verts nbrs symm dist r conn, rfl, rfl,
    (GraphData.ofConnected verts mem_verts nbrs symm dist r conn).twoPhase_correct B W |>.1,
    (GraphData.ofConnected verts mem_verts nbrs symm dist r conn).twoPhase_correct B W |>.2,
    fun _ hsel =>
      (GraphData.ofConnected verts mem_verts nbrs symm dist r conn).twoPhase_underLoad hsel⟩

end GraphData

end AsyncLean
