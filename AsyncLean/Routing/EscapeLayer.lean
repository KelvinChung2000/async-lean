/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.StrategyDetour

/-!
# The detour network of any graph with an abstract escape layer

`AsyncLean.Routing.GraphDetour` and `AsyncLean.Routing.StrategyDetour` prove the detour network
(minimal adaptive routing on virtual channel 1, a source-chosen intermediate, at most `B`
returns from virtual channel 0) safe with **tree routing** along a spanning tree as the escape
layer on virtual channel 0.  The proofs only use a few properties of that escape; this file
states them as a structure, `GraphData.EscapeLayer G`, and proves every theorem of those two
files for every escape layer.  `GraphData.treeEscape` is the tree escape (and its network is
literally `GraphData.detourNet`, `GraphData.treeEscape_net`); `AsyncLean.Routing.UpDown` gives
up*/down* routing over all the links of the graph.

## The escape layer

An escape layer `E : G.EscapeLayer` gives, for a packet in channel `c` with destination `d`:

* the next vertex `E.next c d` of its escape hop, into virtual channel 0 of the link
  `c.head → E.next c d` (`E.escCh c d`).  It may depend on the **whole channel**, not only on
  its head: the phase of an up*/down* route is read from the channel the packet occupies;
* a set of **legal pairs** `E.legal c d` (the pairs the escape can be in), containing every
  injection channel and every virtual channel 1 channel, closed under escape hops, on which the
  escape hop follows a link of the graph;
* an **order of the channels** `E.ord` (lexicographic on `ℕ × ℕ`) decreasing along every escape
  hop from a legal pair: the escape dependencies are acyclic;
* an **escape distance** `E.edist` decreasing along every escape hop from a legal virtual
  channel 0 pair, and below `E.bound` on legal virtual channel 0 pairs: the escape layer is
  connected (from every legal pair, escape hops reach the destination).

## The network (`E.net B W`)

Headers `(d, w, b)` as in `GraphData.detourNet`: the escape hop `E.escCh c d` towards the
destination `d` (dropping the intermediate), and the adaptive hops of `GraphData.detAdaptive`
towards the target, from virtual channel 0 only while the return budget `b` is positive, at the
cost of one unit.  With `W = fun _ _ => [none]` and `B = 0` it is the absorbing network.

## Main results

For every graph `G`, escape layer `E`, budget `B` and choice of intermediates `W`:

* `EscapeLayer.esc_wf` : the escape dependency graph is well-founded;
* `EscapeLayer.correct`, `EscapeLayer.correct_of_escapeSel`, `EscapeLayer.correct_of_sourceSel` :
  deadlock, livelock and starvation free under every valid selection, every selection that never
  refuses a free escape hop, every selection that may in addition throttle the sources;
* `EscapeLayer.underLoad`, `EscapeLayer.underLoad_of_escapeSel`,
  `EscapeLayer.underLoad_of_sourceSel` : delivery under saturation along every channel-fair run;
* `EscapeLayer.hops_le_some`, `EscapeLayer.hops_le_none` : hop bounds;
* `EscapeLayer.throttleSel_sourceSel`, `EscapeLayer.openSel_escapeSel`,
  `EscapeLayer.throttleSel_sourceSelOn`, `EscapeLayer.lxSel_sourceSel` : the selections of the
  simulation (`GraphData.throttleTiers`: the source gate, the `lx` escape-share throttle) satisfy
  the hypotheses of the safety theorems;
* `EscapeLayer.strategy_safe_of_escapeSel`, `EscapeLayer.strategy_safe_of_sourceSel`,
  `EscapeLayer.strategy_safe_of_sourceSelOn` : every history-dependent strategy whose selections
  satisfy them is safe (`Network.StrategySafe`, through `Network.Strategy.safe`).
* `GraphData.treeEscape`, `GraphData.treeEscape_net` : the tree escape is an escape layer, and
  its network is `GraphData.detourNet`.

## What is not covered

As in `AsyncLean.Routing.GraphDetour`: nothing about throughput; the starvation statements
inherit the caveats of `AsyncLean.Routing.Fairness` and `AsyncLean.Routing.Saturation`.
-/

namespace AsyncLean

open Network

namespace GraphData

variable {V : Type*} [DecidableEq V]

/-- **An escape layer on the graph `G`**: the escape hop of a packet in channel `c` for the
destination `d` goes to `next c d` on virtual channel 0; from the legal pairs it follows a link,
stays legal, decreases the order `ord` of the channels (acyclic dependencies) and, from virtual
channel 0, the escape distance `edist` (below `bound`). -/
structure EscapeLayer (G : GraphData V) where
  /-- The next vertex of the escape hop of a packet in `c` for `d`. -/
  next : GChan V → V → V
  /-- The pairs a packet can occupy. -/
  legal : GChan V → V → Prop
  /-- Injection channels are legal. -/
  legal_inj : ∀ s d, legal (.inj s) d
  /-- Virtual channel 1 channels are legal. -/
  legal_adapt : ∀ u v d, legal (.link u v true) d
  /-- The escape hop follows a link of the graph. -/
  next_adj : ∀ c d, legal c d → c.head ≠ d → next c d ∈ G.nbrs c.head
  /-- The escape hop leads to a legal pair. -/
  legal_next : ∀ c d, legal c d → c.head ≠ d → legal (.link c.head (next c d) false) d
  /-- The order of the channels. -/
  ord : GChan V → ℕ × ℕ
  /-- The escape hop decreases the order: the escape dependencies are acyclic. -/
  ord_lt : ∀ c d, legal c d → c.head ≠ d →
    Prod.Lex (· < ·) (· < ·) (ord (.link c.head (next c d) false)) (ord c)
  /-- The escape distance. -/
  edist : GChan V → V → ℕ
  /-- The escape hop from virtual channel 0 decreases the escape distance. -/
  edist_lt : ∀ c d, c.isEsc = true → legal c d → c.head ≠ d →
    edist (.link c.head (next c d) false) d < edist c d
  /-- A bound on the escape distance. -/
  bound : ℕ
  /-- The escape distance of a legal virtual channel 0 pair is below the bound. -/
  edist_lt_bound : ∀ u v d, legal (.link u v false) d → edist (.link u v false) d < bound

namespace EscapeLayer

variable {G : GraphData V} (E : G.EscapeLayer)

/-! ### The network -/

/-- The escape channel of a packet in `c` for `d`: virtual channel 0 of the link to `next c d`. -/
def escCh (c : GChan V) (d : V) : GChan V := .link c.head (E.next c d) false

/-- The escape subfunction: the escape hop towards the destination, dropping the
intermediate. -/
def escape (c : GChan V) (p : DetHdr V) : List (GChan V × DetHdr V) :=
  [(E.escCh c p.1, (p.1, none, p.2.2))]

/-- **The detour network with the escape layer `E`**: headers `(d, w, b)`; from every channel
the escape hop towards `d` (dropping the intermediate); the adaptive hops towards the target
outside the escape layer, and from the escape layer while the budget is positive, at the cost
of one unit of budget.  A packet from `s` to `d` is injected with an intermediate among `W s d`
and budget `B`. -/
def net (B : ℕ) (W : V → V → List (Option V)) : Network (GChan V) (DetHdr V) where
  arrived c p := decide (c.head = p.1)
  route c p := E.escape c p ++ if mayReturn c (p.1, p.2.2) then G.detAdaptive c p else []
  inject := G.verts.flatMap fun s => G.verts.flatMap fun d =>
    (W s d).map fun w => (.inj s, (d, w, B))

variable {E}

/-- A packet that has not arrived is not at its destination. -/
theorem arrived_false {B : ℕ} {W : V → V → List (Option V)} {c : GChan V} {p : DetHdr V}
    (h : (E.net B W).arrived c p = false) : c.head ≠ p.1 := by
  simpa [net] using h

/-- The permitted hops: the escape hop towards the destination, dropping the intermediate; an
adaptive hop towards the target, from outside the escape layer with the same budget, from the
escape layer (when the budget is positive) with one unit less, dropping the intermediate on the
hop into it. -/
theorem mem_route {B : ℕ} {W : V → V → List (Option V)} {c : GChan V} {p : DetHdr V}
    {q : GChan V × DetHdr V} (h : q ∈ (E.net B W).route c p) :
    q = (E.escCh c p.1, (p.1, none, p.2.2)) ∨
      ∃ v ∈ G.nbrs c.head, G.dist v (target p) < G.dist c.head (target p) ∧
        ((c.isEsc = false ∧ q = (.link c.head v true, (p.1, dropAt v p.2.1, p.2.2))) ∨
          (c.isEsc = true ∧ p.2.2 ≠ 0 ∧
            q = (.link c.head v true, (p.1, dropAt v p.2.1, p.2.2 - 1)))) := by
  simp only [net, escape, List.mem_append, List.mem_singleton] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    split_ifs at h with hm
    · simp only [detAdaptive, adaptiveHops, List.map_map, List.mem_map, List.mem_filter,
        decide_eq_true_eq, Function.comp_apply] at h
      obtain ⟨v, ⟨hv, hd⟩, rfl⟩ := h
      refine ⟨v, hv, hd, ?_⟩
      cases hc : c.isEsc
      · exact Or.inl ⟨rfl, by simp [retHdr, hc, GChan.head]⟩
      · refine Or.inr ⟨rfl, ?_, by simp [retHdr, hc, GChan.head]⟩
        simpa [mayReturn, hc] using hm
    · simp at h

/-- The legal pairs of the network: legal for the escape layer and the destination, with a
return budget at most `B`. -/
def detLegal (E : G.EscapeLayer) (B : ℕ) (c : GChan V) (p : DetHdr V) : Prop :=
  E.legal c p.1 ∧ p.2.2 ≤ B

/-- **Every hop from a legal pair follows an edge of the graph.** -/
theorem route_adj {B : ℕ} {W : V → V → List (Option V)} {c : GChan V} {p : DetHdr V}
    {q : GChan V × DetHdr V} (hl : E.legal c p.1) (ha : (E.net B W).arrived c p = false)
    (h : q ∈ (E.net B W).route c p) : ∃ v ∈ G.nbrs c.head, ∃ vc, q.1 = .link c.head v vc := by
  rcases mem_route h with rfl | ⟨v, hv, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩
  · exact ⟨_, E.next_adj c p.1 hl (arrived_false ha), false, rfl⟩
  · exact ⟨v, hv, true, rfl⟩
  · exact ⟨v, hv, true, rfl⟩

/-- The legal pairs contain the injections and are closed under routing. -/
theorem closed (B : ℕ) (W : V → V → List (Option V)) : (E.net B W).Closed (E.detLegal B) where
  inject q hq := by
    simp only [net, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨s, -, d, -, w, -, rfl⟩ := hq
    exact ⟨E.legal_inj s d, le_rfl⟩
  route c p q hl ha hq := by
    rcases mem_route hq with rfl | ⟨v, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩
    · exact ⟨E.legal_next c p.1 hl.1 (arrived_false ha), hl.2⟩
    · exact ⟨E.legal_adapt _ _ _, hl.2⟩
    · exact ⟨E.legal_adapt _ _ _, by have := hl.2; simp only; omega⟩

/-! ### The escape dependencies -/

/-- **The escape dependency graph is well-founded** (acyclic): the order `ord` decreases along
every dependency. -/
theorem esc_wf (B : ℕ) (W : V → V → List (Option V)) :
    WellFounded (flip ((E.net B W).Dep (E.detLegal B) E.escape)) :=
  Network.wf_of_lexRank E.ord fun c _ ⟨p, _, hl, ha, hq⟩ => by
    simp only [escape, List.mem_singleton, Prod.mk.injEq] at hq
    obtain ⟨rfl, -⟩ := hq
    exact E.ord_lt c p.1 hl.1 (arrived_false ha)

/-- The escape subfunction offers a hop to every packet. -/
theorem esc_conn (B : ℕ) (W : V → V → List (Option V)) : ∀ c p, E.detLegal B c p →
    (E.net B W).arrived c p = false → E.escape c p ≠ [] :=
  fun _ _ _ _ => List.cons_ne_nil _ _

/-- The escape hop is a permitted hop. -/
theorem escape_sub {B : ℕ} {W : V → V → List (Option V)} {c : GChan V} {p : DetHdr V}
    {q : GChan V × DetHdr V} (hq : q ∈ E.escape c p) : q ∈ (E.net B W).route c p :=
  List.mem_append_left _ hq

/-- The escape hop is a permitted hop (in the form of Duato's theorem). -/
theorem esc_sub (B : ℕ) (W : V → V → List (Option V)) : ∀ c p q, E.detLegal B c p →
    (E.net B W).arrived c p = false → q ∈ E.escape c p → q ∈ (E.net B W).route c p :=
  fun _ _ _ _ _ hq => escape_sub hq

/-- No hop leads into an injection channel. -/
theorem route_not_inj {B : ℕ} {W : V → V → List (Option V)} {c : GChan V} {p : DetHdr V}
    {q : GChan V × DetHdr V} (hq : q ∈ (E.net B W).route c p) : ¬ q.1.isInj := by
  rcases mem_route hq with rfl | ⟨v, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ <;>
    simp [escCh, GChan.isInj]

/-- No escape hop leads into an injection channel. -/
theorem esc_not_inj (B : ℕ) (W : V → V → List (Option V)) : ∀ c p q, E.detLegal B c p →
    (E.net B W).arrived c p = false → q ∈ E.escape c p → ¬ q.1.isInj :=
  fun _ _ _ _ _ hq => route_not_inj (B := B) (W := W) (escape_sub hq)

/-! ### The ranking function -/

variable (E)

/-- The ranking of a packet without an intermediate: its escape distance in the escape layer,
elsewhere a multiple of its distance estimate exceeding every escape distance. -/
def rank (c : GChan V) (d : V) : ℕ :=
  if c.isEsc then E.edist c d else (E.bound + 1) * (G.dist c.head d + 1)

/-- A bound exceeding every value of `rank` on the legal pairs. -/
def rankBound : ℕ := (E.bound + 1) * (G.maxDist + 1) + 1

/-- The ranking of a packet: without an intermediate, its remaining return budget times
`rankBound` plus `rank`; while heading for its intermediate `w`, one more unit of budget than it
has, times `rankBound`, plus its distance estimate to `w`. -/
def detRank (c : GChan V) (p : DetHdr V) : ℕ :=
  match p.2.1 with
  | none => p.2.2 * E.rankBound + E.rank c p.1
  | some w => (p.2.2 + 1) * E.rankBound + G.dist c.head w

variable {E}

omit [DecidableEq V] in
theorem rank_link_true (u v d : V) :
    E.rank (.link u v true) d = (E.bound + 1) * (G.dist v d + 1) := rfl

omit [DecidableEq V] in
theorem rank_of_not_esc {c : GChan V} (hc : c.isEsc = false) (d : V) :
    E.rank c d = (E.bound + 1) * (G.dist c.head d + 1) := by
  simp [rank, hc]

omit [DecidableEq V] in
theorem rank_escCh (c : GChan V) (d : V) : E.rank (E.escCh c d) d = E.edist (E.escCh c d) d :=
  rfl

omit [DecidableEq V] in
/-- **Every value of the ranking on a legal pair is below `rankBound`.** -/
theorem rank_lt_rankBound {c : GChan V} {d : V} (hl : E.legal c d) : E.rank c d < E.rankBound := by
  have hmul : (E.bound + 1) * (G.dist c.head d + 1) ≤ (E.bound + 1) * (G.maxDist + 1) :=
    Nat.mul_le_mul_left _ (by have := G.dist_le_maxDist c.head d; omega)
  have h1 : E.bound + 1 ≤ (E.bound + 1) * (G.maxDist + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold rankBound
  rcases c with u | ⟨x, u, _ | _⟩
  · rw [rank_of_not_esc rfl]; omega
  · have := E.edist_lt_bound x u d hl
    show E.edist _ d < _
    omega
  · rw [rank_link_true]; exact Nat.lt_succ_of_le hmul

/-- **The ranking decreases on every hop**: a hop that keeps the header decreases the escape
distance (escape layer) or the distance estimate (virtual channel 1), an escape hop from virtual
channel 1 lands below every multiple of `bound + 1`, a return lowers the budget, and the hop into
the intermediate or an escape hop drops the intermediate, landing below `(b + 1) * rankBound`. -/
theorem rank_lt (B : ℕ) (W : V → V → List (Option V)) : ∀ c p q, E.detLegal B c p →
    (E.net B W).arrived c p = false → q ∈ (E.net B W).route c p →
    E.detRank q.1 q.2 < E.detRank c p := by
  rintro c ⟨d, w, b⟩ q hl ha hq
  have hne : c.head ≠ d := arrived_false ha
  have hl1 : E.legal c d := hl.1
  have hesc : E.legal (E.escCh c d) d := E.legal_next c d hl1 hne
  have hRb : E.bound < E.rankBound := by
    have : E.bound + 1 ≤ (E.bound + 1) * (G.maxDist + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold rankBound; omega
  have hsucc : (b + 1) * E.rankBound = b * E.rankBound + E.rankBound := Nat.succ_mul b _
  rcases mem_route hq with rfl | ⟨v, -, hd, ⟨hc, rfl⟩ | ⟨hc, hb, rfl⟩⟩
  · -- the escape hop
    have h1 := E.edist_lt_bound _ _ d hesc
    cases w with
    | none =>
      show b * E.rankBound + E.rank (E.escCh c d) d < b * E.rankBound + E.rank c d
      rw [rank_escCh]
      cases hc : c.isEsc
      · rw [rank_of_not_esc hc]
        have : E.bound + 1 ≤ (E.bound + 1) * (G.dist c.head d + 1) :=
          Nat.le_mul_of_pos_right _ (by omega)
        have : E.edist (E.escCh c d) d < E.bound := h1
        omega
      · have := E.edist_lt c d hc hl1 hne
        simp only [rank, hc, ↓reduceIte]
        exact Nat.add_lt_add_left this _
    | some w =>
      show b * E.rankBound + E.rank (E.escCh c d) d < (b + 1) * E.rankBound + G.dist c.head w
      rw [rank_escCh]
      have : E.edist (E.escCh c d) d < E.bound := h1
      omega
  · -- an adaptive hop from outside the escape layer
    have hR := rank_lt_rankBound (E := E) (E.legal_adapt c.head v d)
    cases w with
    | none =>
      simp only [target, Option.getD_none] at hd
      show b * E.rankBound + E.rank (.link c.head v true) d < b * E.rankBound + E.rank c d
      rw [rank_link_true, rank_of_not_esc hc]
      have := Nat.mul_lt_mul_of_pos_left (show G.dist v d + 1 < G.dist c.head d + 1 by omega)
        (show 0 < E.bound + 1 by omega)
      omega
    | some w =>
      simp only [target, Option.getD_some] at hd
      simp only [dropAt]
      split_ifs with hv
      · show b * E.rankBound + E.rank (.link c.head v true) d < (b + 1) * E.rankBound + _
        omega
      · show (b + 1) * E.rankBound + G.dist v w < (b + 1) * E.rankBound + G.dist c.head w
        omega
  · -- a return from the escape layer
    have hR := rank_lt_rankBound (E := E) (E.legal_adapt c.head v d)
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := Nat.exists_eq_succ_of_ne_zero hb
    have hk : (k + 1) * E.rankBound = k * E.rankBound + E.rankBound := Nat.succ_mul k _
    cases w with
    | none =>
      show (k + 1 - 1) * E.rankBound + E.rank (.link c.head v true) d <
        (k + 1) * E.rankBound + E.rank c d
      simp only [Nat.add_sub_cancel]
      omega
    | some w =>
      simp only [target, Option.getD_some] at hd
      simp only [dropAt]
      split_ifs with hv
      · show (k + 1 - 1) * E.rankBound + E.rank (.link c.head v true) d <
          (k + 1 + 1) * E.rankBound + _
        simp only [Nat.add_sub_cancel]
        omega
      · show (k + 1 - 1 + 1) * E.rankBound + G.dist v w <
          (k + 1 + 1) * E.rankBound + G.dist c.head w
        simp only [Nat.add_sub_cancel]
        omega

/-- There are finitely many legal pairs. -/
theorem pairs_finite (B : ℕ) : {q : GChan V × DetHdr V | E.detLegal B q.1 q.2}.Finite :=
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
theorem chans_finite (B : ℕ) : {c | ∃ p, E.detLegal B c p}.Finite :=
  ((pairs_finite (E := E) B).image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩

/-! ### Hop bounds -/

/-- **Hop bound**: a packet injected at `s` for `d` with intermediate `w` reaches its
destination within `detRank (.inj s) (d, w, B)` hops, along every route. -/
theorem hops_le {B : ℕ} {W : V → V → List (Option V)} {s d : V} {w : Option V}
    {ls : List Unit} {q' : GChan V × DetHdr V}
    (h : (E.net B W).packetLTS.Path (.inj s, (d, w, B)) ls q') :
    ls.length ≤ E.detRank (.inj s) (d, w, B) := by
  have := (E.net B W).packet_hops_le (closed B W) E.detRank (rank_lt B W)
    (q := (.inj s, (d, w, B))) ⟨E.legal_inj s d, le_rfl⟩ h
  exact (Nat.le_add_left _ _).trans this

/-- **Hop bound with a detour**: at most `dist s w + (B + 1) * rankBound` hops. -/
theorem hops_le_some {B : ℕ} {W : V → V → List (Option V)} {s d w : V}
    {ls : List Unit} {q' : GChan V × DetHdr V}
    (h : (E.net B W).packetLTS.Path (.inj s, (d, some w, B)) ls q') :
    ls.length ≤ G.dist s w + (B + 1) * E.rankBound := by
  have := hops_le h
  change _ ≤ (B + 1) * E.rankBound + G.dist s w at this
  omega

/-- **Hop bound without a detour**: at most `B * rankBound + (bound + 1) * (dist s d + 1)`
hops. -/
theorem hops_le_none {B : ℕ} {W : V → V → List (Option V)} {s d : V}
    {ls : List Unit} {q' : GChan V × DetHdr V}
    (h : (E.net B W).packetLTS.Path (.inj s, (d, none, B)) ls q') :
    ls.length ≤ B * E.rankBound + (E.bound + 1) * (G.dist s d + 1) :=
  hops_le h

/-! ### Correctness -/

variable (E)

/-- **The detour network with any escape layer is correct**: for every return budget `B` and
every choice of intermediates `W`, deadlock free and livelock free under every valid selection
function, and starvation free under strongly fair scheduling. -/
theorem correct (B : ℕ) (W : V → V → List (Option V)) :
    (E.net B W).Correct ∧ (E.net B W).StarvationFree :=
  ⟨⟨(E.net B W).deadlockFree_of_escape (closed B W) E.escape (esc_sub B W) (esc_conn B W)
      (esc_wf B W),
    (E.net B W).livelockFree_of_ranking (closed B W) (chans_finite B) E.detRank (rank_lt B W)⟩,
    (E.net B W).starvationFree_of_escape_ranking (closed B W) (pairs_finite B) E.escape
      (esc_sub B W) (esc_conn B W) (esc_wf B W) E.detRank (rank_lt B W)⟩

variable {E}

/-- **Correct under selections that may decline adaptive hops**. -/
theorem correct_of_escapeSel {B : ℕ} {W : V → V → List (Option V)}
    {sel : Selection (GChan V) (DetHdr V)} (hsel : (E.net B W).EscapeSel E.escape sel) :
    (E.net B W).DeadlockFreeWith sel ∧ (E.net B W).LivelockFreeWith sel ∧
      (E.net B W).StarvationFreeWith sel :=
  ⟨(E.net B W).deadlockFreeWith_of_escape (closed B W) E.escape (esc_conn B W) (esc_wf B W) hsel,
    (E.net B W).livelockFreeWith_of_ranking (closed B W) (chans_finite B) E.detRank
      (rank_lt B W) hsel.sub,
    (E.net B W).starvationFreeWith_of_source (closed B W) (pairs_finite B) E.escape
      (esc_conn B W) (esc_wf B W) (esc_not_inj B W) E.detRank (rank_lt B W)
      (EscapeSel.sourceSel (E.net B W) hsel fun c => c.isInj = true)⟩

/-- **Correct under throttled sources**. -/
theorem correct_of_sourceSel {B : ℕ} {W : V → V → List (Option V)}
    {sel : Selection (GChan V) (DetHdr V)}
    (hsel : (E.net B W).SourceSel E.escape (fun c => c.isInj) sel) :
    (E.net B W).DeadlockFreeWith sel ∧ (E.net B W).LivelockFreeWith sel ∧
      (E.net B W).StarvationFreeWith sel :=
  ⟨(E.net B W).deadlockFreeWith_of_source (closed B W) E.escape (esc_conn B W) (esc_wf B W)
      (esc_not_inj B W) hsel,
    (E.net B W).livelockFreeWith_of_ranking (closed B W) (chans_finite B) E.detRank
      (rank_lt B W) hsel.sub,
    (E.net B W).starvationFreeWith_of_source (closed B W) (pairs_finite B) E.escape
      (esc_conn B W) (esc_wf B W) (esc_not_inj B W) E.detRank (rank_lt B W) hsel⟩

/-- **Every packet is delivered under saturation**: under every selection that never refuses a
free escape hop, along every channel-fair run, with injections going on for ever. -/
theorem underLoad_of_escapeSel {B : ℕ} {W : V → V → List (Option V)}
    {sel : Selection (GChan V) (DetHdr V)} (hsel : (E.net B W).EscapeSel E.escape sel) :
    (E.net B W).StarvationFreeUnderLoad sel (fun _ => False) :=
  (E.net B W).starvationFreeUnderLoad_of_escape (closed B W) E.escape (esc_conn B W) (esc_wf B W)
    E.detRank (rank_lt B W) hsel

/-- **Every packet is delivered under saturation**, under every valid selection. -/
theorem underLoad {B : ℕ} {W : V → V → List (Option V)} {sel : Selection (GChan V) (DetHdr V)}
    (hsel : (E.net B W).ValidSel sel) : (E.net B W).StarvationFreeUnderLoad sel (fun _ => False) :=
  underLoad_of_escapeSel (ValidSel.escapeSel _ hsel fun _ _ _ hq => escape_sub hq)

/-- **Delivery under saturation with throttled sources**: every packet outside the injection
channels is delivered along every channel-fair run. -/
theorem underLoad_of_sourceSel {B : ℕ} {W : V → V → List (Option V)}
    {sel : Selection (GChan V) (DetHdr V)}
    (hsel : (E.net B W).SourceSel E.escape (fun c => c.isInj) sel) :
    (E.net B W).StarvationFreeUnderLoad sel (fun c => c.isInj) :=
  (E.net B W).starvationFreeUnderLoad_of_source (closed B W) E.escape (esc_conn B W) (esc_wf B W)
    (esc_not_inj B W) (fun _ _ _ _ _ hq => route_not_inj hq) E.detRank (rank_lt B W) hsel

/-! ### The selections of the simulation -/

variable (E)

/-- **The throttled two-tier selection** (`GraphData.throttleTiers`): the free minimal hops on
virtual channel 1 that pass the source gate, else the escape hop if it passes the gate. -/
def throttleSel (B : ℕ) (W : V → V → List (Option V)) (thr : Config (GChan V) (DetHdr V) → V → ℕ)
    (block : Config (GChan V) (DetHdr V) → V → Bool) : Selection (GChan V) (DetHdr V) :=
  (E.net B W).tieredSel (G.throttleTiers thr block)

/-- The two tiers without throttling: the free minimal hops on virtual channel 1, else the
escape hop. -/
def openSel (B : ℕ) (W : V → V → List (Option V)) : Selection (GChan V) (DetHdr V) :=
  E.throttleSel B W (fun _ _ => 0) (fun _ _ => false)

/-- **The `lx` throttle**, evaluated on the current configuration. -/
def lxSel (B : ℕ) (W : V → V → List (Option V)) (ball : V → List V) (o lo hi : ℕ) :
    Selection (GChan V) (DetHdr V) :=
  E.throttleSel B W (G.lxThr ball o lo hi) (G.lxBlock ball o)

variable {E}

omit [DecidableEq V] in
theorem escape_isEsc {c : GChan V} {p : DetHdr V} {q : GChan V × DetHdr V}
    (hq : q ∈ E.escape c p) : q.1.isEsc = true := by
  simp only [escape, List.mem_singleton] at hq
  subst hq; rfl

omit [DecidableEq V] in
/-- The escape tier admits the escape hop from every channel outside the sources. -/
theorem escTier_non {thr : Config (GChan V) (DetHdr V) → V → ℕ}
    {block : Config (GChan V) (DetHdr V) → V → Bool} {f : Config (GChan V) (DetHdr V)}
    {c : GChan V} {p : DetHdr V} {q : GChan V × DetHdr V} (hc : ¬ c.isInj = true)
    (hq : q ∈ E.escape c p) :
    (G.srcGate (thr f c.head) (block f c.head) f c q && q.1.isEsc) = true := by
  simp [srcGate, hc, escape_isEsc hq]

/-- **The throttled selection satisfies Duato's condition with throttled sources**, for
thresholds at most twice the degree of every router and a blocking rule that is off when every
link channel is empty. -/
theorem throttleSel_sourceSel {B : ℕ} {W : V → V → List (Option V)}
    {thr : Config (GChan V) (DetHdr V) → V → ℕ} {block : Config (GChan V) (DetHdr V) → V → Bool}
    (hthr : ∀ f s v, thr f s ≤ 2 * (G.nbrs v).length)
    (hblock : ∀ f s, (∀ c, ¬ c.isInj = true → f c = none) → block f s = false) :
    (E.net B W).SourceSel E.escape (fun c => c.isInj) (E.throttleSel B W thr block) :=
  (E.net B W).tieredSel_sourceSel (fun _ _ _ hq => escape_sub hq)
    (List.mem_cons_of_mem _ List.mem_cons_self) (fun _ _ _ _ hc hq => escTier_non hc hq)
    (fun f c p q _ he hq => by
      simp [srcGate, G.freeOut_of_empty he, hthr, hblock f c.head he, escape_isEsc hq])

/-- **Without throttling, the two tiers never refuse a free escape hop.** -/
theorem openSel_escapeSel {B : ℕ} {W : V → V → List (Option V)} :
    (E.net B W).EscapeSel E.escape (E.openSel B W) :=
  (E.net B W).tieredSel_escapeSel (fun _ _ _ hq => escape_sub hq)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun _ _ _ _ hq => by simp [srcGate, escape_isEsc hq])

/-- **Any admissible choice among the free hops of the open tiers** never refuses a free escape
hop. -/
theorem refine_openSel_escapeSel {B : ℕ} {W : V → V → List (Option V)}
    {choose : Config (GChan V) (DetHdr V) → GChan V → DetHdr V →
      List (GChan V × DetHdr V) → List (GChan V × DetHdr V)} (hch : ChoiceOK choose) :
    (E.net B W).EscapeSel E.escape (refineSel (E.openSel B W) choose) :=
  refineSel_escapeSel openSel_escapeSel ((E.net B W).tieredSel_freeOnly _) hch

/-- The `lx` throttle satisfies Duato's condition with throttled sources. -/
theorem lxSel_sourceSel {B : ℕ} {W : V → V → List (Option V)} {ball : V → List V}
    {o lo hi : ℕ} (hlo : ∀ v, lo ≤ 2 * (G.nbrs v).length) (hhi : ∀ v, hi ≤ 2 * (G.nbrs v).length) :
    (E.net B W).SourceSel E.escape (fun c => c.isInj) (E.lxSel B W ball o lo hi) :=
  throttleSel_sourceSel (fun f s v => G.lxThr_le (hlo v) (hhi v) f s)
    (fun _ s hf => G.lxBlock_of_empty hf s)

/-! ### Blocking read from a snapshot -/

/-- The legal pairs, refined: a packet in the injection channel of `s` does not have `s` as its
intermediate. -/
def srcLegal (E : G.EscapeLayer) (B : ℕ) (c : GChan V) (p : DetHdr V) : Prop :=
  E.detLegal B c p ∧ ∀ s, c = .inj s → p.2.1 ≠ some s

/-- The refined legal pairs are closed when no source is its own intermediate. -/
theorem srcLegal_closed (B : ℕ) {W : V → V → List (Option V)}
    (hW : ∀ s d w, some w ∈ W s d → w ≠ s) : (E.net B W).Closed (E.srcLegal B) where
  inject q hq := by
    refine ⟨(closed B W).inject q hq, ?_⟩
    simp only [net, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨s, -, d, -, w, hw, rfl⟩ := hq
    rintro s' hs' rfl
    cases hs'
    exact hW s d s hw rfl
  route c p q hl ha hq := by
    refine ⟨(closed B W).route c p q hl.1 ha hq, ?_⟩
    intro s hs
    exact absurd (by rw [hs]; rfl) (route_not_inj hq)

theorem srcLegal_wf (B : ℕ) (W : V → V → List (Option V)) :
    WellFounded (flip ((E.net B W).Dep (E.srcLegal B) E.escape)) :=
  Subrelation.wf (fun ⟨p, p', hl, ha, hq⟩ => ⟨p, p', hl.1, ha, hq⟩) (esc_wf B W)

theorem srcLegal_finite (B : ℕ) : {q : GChan V × DetHdr V | E.srcLegal B q.1 q.2}.Finite :=
  (pairs_finite B).subset fun _ hq => hq.1

omit [DecidableEq V] in
/-- A packet that has not arrived, in the injection channel of `s`, in a refined legal pair, has
a target other than `s`. -/
theorem target_ne_of_srcLegal {B : ℕ} {s : V} {p : DetHdr V} (hl : E.srcLegal B (.inj s) p)
    (ha : s ≠ p.1) : s ≠ target p := by
  obtain ⟨d, w, b⟩ := p
  cases w with
  | none => simpa [target] using ha
  | some w =>
    simp only [target, Option.getD_some]
    exact fun h => hl.2 s rfl (by rw [h])

/-- **The throttled selection with any blocking rule** (read from a snapshot, from history)
satisfies Duato's condition with throttled sources on the refined legal pairs, when `dist` is a
distance (every vertex other than `t` has a neighbour closer to `t`). -/
theorem throttleSel_sourceSelOn {B : ℕ} {W : V → V → List (Option V)}
    (hdist : ∀ u t, u ≠ t → ∃ v ∈ G.nbrs u, G.dist v t < G.dist u t)
    {thr : Config (GChan V) (DetHdr V) → V → ℕ} {block : Config (GChan V) (DetHdr V) → V → Bool}
    (hthr : ∀ f s v, thr f s ≤ 2 * (G.nbrs v).length) :
    (E.net B W).SourceSelOn (E.srcLegal B) E.escape (fun c => c.isInj)
      (E.throttleSel B W thr block) where
  sub _ _ _ _ h := ((E.net B W).mem_tieredSel h).1
  conserving f c p _ _ hc _ := fun ⟨q, hq, hfree⟩ =>
    (E.net B W).tieredSel_conserving (List.mem_cons_of_mem _ List.mem_cons_self)
      (escape_sub hq) hfree (escTier_non hc hq)
  source f c p hl ha hc _ he := fun ⟨q, hq, hfree⟩ => by
    cases hb : block f c.head with
    | false =>
      refine (E.net B W).tieredSel_conserving (List.mem_cons_of_mem _ List.mem_cons_self)
        (escape_sub hq) hfree ?_
      simp [srcGate, G.freeOut_of_empty he, hthr, hb, escape_isEsc hq]
    | true =>
      obtain ⟨s, rfl⟩ : ∃ s, c = .inj s := by
        cases c with
        | inj s => exact ⟨s, rfl⟩
        | link _ _ _ => simp [GChan.isInj] at hc
      have hs : s ≠ target p :=
        target_ne_of_srcLegal hl (fun h => by simp [net, GChan.head, h] at ha)
      obtain ⟨v, hv, hd⟩ := hdist s (target p) hs
      have hmem : (GChan.link s v true, (p.1, dropAt v p.2.1, (retHdr (.inj s) (p.1, p.2.2)).2)) ∈
          (E.net B W).route (.inj s) p := by
        simp only [net, List.mem_append]
        right
        simp only [mayReturn, GChan.isEsc, Bool.not_false, Bool.true_or, ↓reduceIte, detAdaptive,
          adaptiveHops, GChan.head, List.map_map, List.mem_map, List.mem_filter]
        exact ⟨v, ⟨hv, decide_eq_true hd⟩, rfl⟩
      refine (E.net B W).tieredSel_conserving List.mem_cons_self hmem
        (he _ (by simp [GChan.isInj])) ?_
      simp [srcGate, G.freeOut_of_empty he, hthr, GChan.isEsc]

/-! ### Strategies -/

variable {H : Type*}

/-- **Every strategy whose selections never refuse a free escape hop is safe**, with no
throttled source. -/
theorem strategy_safe_of_escapeSel {B : ℕ} {W : V → V → List (Option V)}
    {σ : Strategy (GChan V) (DetHdr V) H} (hσ : ∀ h, (E.net B W).EscapeSel E.escape (σ.sel h)) :
    (E.net B W).StrategySafe σ (fun _ => False) :=
  Strategy.safe (closed B W) (pairs_finite B) E.escape (esc_conn B W) (esc_wf B W)
    (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h) E.detRank (rank_lt B W)
    (fun h => (hσ h).sourceSelOn _ _)

/-- **Every throttling strategy whose selections satisfy Duato's condition with throttled
sources is safe.** -/
theorem strategy_safe_of_sourceSel {B : ℕ} {W : V → V → List (Option V)}
    {σ : Strategy (GChan V) (DetHdr V) H}
    (hσ : ∀ h, (E.net B W).SourceSel E.escape (fun c => c.isInj) (σ.sel h)) :
    (E.net B W).StrategySafe σ (fun c => c.isInj) :=
  Strategy.safe (closed B W) (pairs_finite B) E.escape (esc_conn B W) (esc_wf B W)
    (esc_not_inj B W) (fun _ _ _ _ _ hq => route_not_inj hq) E.detRank (rank_lt B W)
    (fun h => (hσ h).sourceSelOn _)

/-- **Every throttling strategy on the refined legal pairs is safe**, when no source is its own
intermediate. -/
theorem strategy_safe_of_sourceSelOn {B : ℕ} {W : V → V → List (Option V)}
    (hW : ∀ s d w, some w ∈ W s d → w ≠ s) {σ : Strategy (GChan V) (DetHdr V) H}
    (hσ : ∀ h, (E.net B W).SourceSelOn (E.srcLegal B) E.escape (fun c => c.isInj) (σ.sel h)) :
    (E.net B W).StrategySafe σ (fun c => c.isInj) :=
  Strategy.safe (srcLegal_closed B hW) (srcLegal_finite B) E.escape
    (fun c p hl ha => esc_conn B W c p hl.1 ha) (srcLegal_wf B W)
    (fun c p q hl ha hq => esc_not_inj B W c p q hl.1 ha hq)
    (fun _ _ _ _ _ hq => route_not_inj hq) E.detRank
    (fun c p q hl ha hq => rank_lt B W c p q hl.1 ha hq) hσ

/-- **Every history-dependent choice is safe**: any admissible choice among the free minimal
hops (the escape hop as fallback), any intermediate. -/
theorem choice_safe {B : ℕ} {W : V → V → List (Option V)} {σ : Strategy (GChan V) (DetHdr V) H}
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧ σ.sel h = refineSel (E.openSel B W) choose) :
    (E.net B W).StrategySafe σ (fun _ => False) :=
  strategy_safe_of_escapeSel fun h => by
    obtain ⟨choose, hch, he⟩ := hσ h
    rw [he]
    exact refine_openSel_escapeSel hch

/-- **Every history-dependent throttle is safe**: thresholds at most twice the least degree and
any escape-blocking rule (both read from anything), any admissible choice among the free hops,
when `dist` is a distance and no source is its own intermediate. -/
theorem throttle_safe {B : ℕ} {W : V → V → List (Option V)}
    (hW : ∀ s d w, some w ∈ W s d → w ≠ s)
    (hdist : ∀ u t, u ≠ t → ∃ v ∈ G.nbrs u, G.dist v t < G.dist u t)
    {σ : Strategy (GChan V) (DetHdr V) H}
    (thr : H → Config (GChan V) (DetHdr V) → V → ℕ)
    (block : H → Config (GChan V) (DetHdr V) → V → Bool)
    (hthr : ∀ h f s v, thr h f s ≤ 2 * (G.nbrs v).length)
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧
      σ.sel h = refineSel (E.throttleSel B W (thr h) (block h)) choose) :
    (E.net B W).StrategySafe σ (fun c => c.isInj) :=
  strategy_safe_of_sourceSelOn hW fun h => by
    obtain ⟨choose, hch, he⟩ := hσ h
    rw [he]
    exact refineSel_sourceSelOn (throttleSel_sourceSelOn hdist (hthr h))
      ((E.net B W).tieredSel_freeOnly _) hch

end EscapeLayer

/-! ### The tree escape -/

/-- **Tree routing along the spanning tree is an escape layer**: legal pairs `GraphData.legal`,
order `GraphData.escRank`, escape distance the tree distance. -/
def treeEscape (G : GraphData V) : G.EscapeLayer where
  next c d := G.next c.head d
  legal := G.legal
  legal_inj _ _ := trivial
  legal_adapt _ _ _ := trivial
  next_adj _ _ _ h := G.next_adj h
  legal_next c d hl h :=
    G.closed.route c d (G.escHop c d) hl (by simp [net, h]) (G.escHop_mem_route c d)
  ord := G.escRank
  ord_lt c d hl h := G.escRank_lt ⟨d, d, hl, by simp [net, h], List.mem_singleton_self _⟩
  edist c d := G.treeDist c.head d
  edist_lt _ _ _ _ h := G.treeDist_next h
  bound := 2 * G.height + 1
  edist_lt_bound _ v d _ := Nat.lt_succ_of_le (G.treeDist_le v d)

/-- **The network of the tree escape is the detour network** `GraphData.detourNet`, so every
theorem of `EscapeLayer` applies to it (and its throttled selections are those of
`AsyncLean.Routing.StrategyDetour`, `GraphData.treeEscape_throttleSel`). -/
theorem treeEscape_net (G : GraphData V) (B : ℕ) (W : V → V → List (Option V)) :
    G.treeEscape.net B W = G.detourNet B W := rfl

/-- The escape subfunction of the tree escape is `GraphData.detEscape`. -/
theorem treeEscape_escape (G : GraphData V) : G.treeEscape.escape = G.detEscape := rfl

/-- The throttled selections of the tree escape are those of `GraphData.throttleSel`. -/
theorem treeEscape_throttleSel (G : GraphData V) (B : ℕ) (W : V → V → List (Option V))
    (thr : Config (GChan V) (DetHdr V) → V → ℕ) (block : Config (GChan V) (DetHdr V) → V → Bool) :
    G.treeEscape.throttleSel B W thr block = G.throttleSel B W thr block := rfl

end GraphData

end AsyncLean
