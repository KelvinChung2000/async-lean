/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Lanes

/-!
# Shared lanes: escapes per lane, adaptive hops on every lane

`AsyncLean.Routing.Lanes` keeps a packet in the lane it was injected into, which makes `m` lanes
exactly `m` copies of one network.  With packets that leaves throughput unused: a packet blocked
in its own lane cannot take a free channel of another lane going the same way.
`scripts/lane_scaling.py` measures that letting packets use the adaptive channels of every lane
gains 7 to 13 % per connection over the lanes on the 8 × 8 torus.  This file proves that this
**shared** use of the lanes stays safe on every graph, for every number of lanes.

## The network (`GraphData.sharedNet`)

Each lane `i` of `ls` has its own graph data `Gs i` (the same graph with a different spanning
tree, for example), and every directed link carries, in every lane, the two virtual channels of
`GraphData.budgetNet`.  A packet header `(L, d, b)` carries the lane `L` chosen at the source,
the destination and the remaining return budget.

* The **escape hop** is the spanning-tree hop of the packet's own lane `L`, on lane `L`'s
  virtual channel 0: the escapes of different lanes never mix.
* The **adaptive hops** are the minimal adaptive hops of `Gs L`, on virtual channel 1 of
  **every** lane.
* Returns from an escape channel to an adaptive channel cost one unit of budget, as in
  `GraphData.budgetNet`.

Every hop of the lane network of `budgetNet`s (`Network.lanes`) is a hop of `sharedNet`, so the
shared network is at least as adaptive.

## Main results

* `GraphData.shared_dep`, `GraphData.shared_esc_wf` : an escape dependency of `sharedNet` lands
  on an escape channel, and from an escape channel of lane `L` it is an escape dependency of lane
  `L`'s `budgetNet`; so the escape dependency graph is well founded (the adaptive channels have
  no incoming escape dependencies).
* `GraphData.sharedCert` : the safety certificate (`Network.SafeCert`).
* `GraphData.shared_correct` : for every finite connected graph data, every list of lanes and
  every return budget, deadlock and livelock free under every valid selection, starvation free
  under strong fairness, and every packet delivered under saturation along every channel-fair
  run.
* `GraphData.shared_sourceSel` : the same under every selection that never refuses a free escape
  hop outside the injection channels and may throttle the sources.
-/

namespace AsyncLean

open Network

namespace GraphData

variable {V : Type*} [DecidableEq V] {ι : Type*}

/-! ### The network -/

/-- The channels a hop of lane `L`'s `budgetNet` may use: an escape hop stays in lane `L`, an
adaptive hop may use every lane of `ls`.  The header records the lane `L`. -/
def spread (ls : List ι) (L : ι) (q : GChan V × (V × ℕ)) :
    List ((ι × GChan V) × (ι × (V × ℕ))) :=
  if q.1.isEsc then [((L, q.1), (L, q.2))] else ls.map fun j => ((j, q.1), (L, q.2))

/-- **Shared lanes**: a packet of lane `L` is routed by `(Gs L).budgetNet B`, its escape hops on
lane `L`, its adaptive hops on every lane of `ls`. -/
def sharedNet (ls : List ι) (Gs : ι → GraphData V) (B : ℕ) :
    Network (ι × GChan V) (ι × (V × ℕ)) where
  arrived x p := decide (x.2.head = p.2.1)
  route x p := (((Gs p.1).budgetNet B).route x.2 p.2).flatMap (spread ls p.1)
  inject := ls.flatMap fun i => ((Gs i).budgetNet B).inject.map fun q => ((i, q.1), (i, q.2))

variable {ls : List ι} {Gs : ι → GraphData V} {B : ℕ}

theorem sharedNet_arrived (x : ι × GChan V) (p : ι × (V × ℕ)) :
    (sharedNet ls Gs B).arrived x p = ((Gs p.1).budgetNet B).arrived x.2 p.2 := rfl

omit [DecidableEq V] in
theorem mem_spread {L : ι} {q0 : GChan V × (V × ℕ)} {q : (ι × GChan V) × (ι × (V × ℕ))}
    (h : q ∈ spread ls L q0) :
    q.1.2 = q0.1 ∧ q.2 = (L, q0.2) ∧ (q0.1.isEsc = true → q.1.1 = L) ∧ q.1.1 ∈ L :: ls := by
  unfold spread at h
  split_ifs at h with hc
  · simp only [List.mem_singleton] at h
    subst h
    simp
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
    simp [hc, hj]

theorem mem_sharedRoute {x : ι × GChan V} {p : ι × (V × ℕ)}
    {q : (ι × GChan V) × (ι × (V × ℕ))} :
    q ∈ (sharedNet ls Gs B).route x p ↔
      ∃ q0 ∈ ((Gs p.1).budgetNet B).route x.2 p.2, q ∈ spread ls p.1 q0 := by
  simp [sharedNet]

/-- An escape hop lands on an escape channel. -/
theorem escHop_isEsc (G : GraphData V) (c : GChan V) (d : V) : (G.escHop c d).1.isEsc = true :=
  rfl

theorem budgetEscape_isEsc (G : GraphData V) {c : GChan V} {p : V × ℕ} {q : GChan V × (V × ℕ)}
    (h : q ∈ G.budgetEscape c p) : q.1.isEsc = true := by
  simp only [budgetEscape, List.mem_singleton] at h
  subst h
  rfl

/-! ### Legal pairs and the escape -/

/-- The legal pairs: lanes of `ls`, a legal pair of the packet's lane, and a packet on an escape
channel belongs to that channel's lane. -/
def sharedLegal (ls : List ι) (Gs : ι → GraphData V) (B : ℕ) (x : ι × GChan V)
    (p : ι × (V × ℕ)) : Prop :=
  x.1 ∈ ls ∧ p.1 ∈ ls ∧ (Gs p.1).budgetLegal B x.2 p.2 ∧ (x.2.isEsc = true → x.1 = p.1)

/-- The escape subfunction: the escape hop of the packet's lane, in that lane. -/
def sharedEsc (Gs : ι → GraphData V) (x : ι × GChan V) (p : ι × (V × ℕ)) :
    List ((ι × GChan V) × (ι × (V × ℕ))) :=
  ((Gs p.1).budgetEscape x.2 p.2).map fun q => ((p.1, q.1), (p.1, q.2))

theorem shared_closed : (sharedNet ls Gs B).Closed (sharedLegal ls Gs B) where
  inject q hq := by
    simp only [sharedNet, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨i, hi, q0, hq0, rfl⟩ := hq
    exact ⟨hi, hi, ((Gs i).budget_closed B).inject q0 hq0, fun _ => rfl⟩
  route x p q hl ha hq := by
    obtain ⟨q0, hq0, hs⟩ := mem_sharedRoute.1 hq
    obtain ⟨h1, h2, h3, h4⟩ := mem_spread hs
    obtain ⟨⟨j, c'⟩, L', p'⟩ := q
    simp only at h1 h2 h3 h4
    subst h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    refine ⟨?_, hl.2.1, ((Gs p.1).budget_closed B).route x.2 p.2 q0 hl.2.2.1 ha hq0, h3⟩
    rcases List.mem_cons.1 h4 with rfl | hj
    · exact hl.2.1
    · exact hj

/-- **The escape dependencies**: an escape dependency lands on an escape channel, and from an
escape channel of lane `j` it stays in lane `j` and is an escape dependency of lane `j`'s
`budgetNet`. -/
theorem shared_dep {j j' : ι} {c c' : GChan V}
    (h : (sharedNet ls Gs B).Dep (sharedLegal ls Gs B) (sharedEsc Gs) (j, c) (j', c')) :
    c'.isEsc = true ∧ (c.isEsc = true → j' = j ∧
      ((Gs j).budgetNet B).Dep ((Gs j).budgetLegal B) (Gs j).budgetEscape c c') := by
  obtain ⟨p, p', hl, ha, hq⟩ := h
  obtain ⟨q0, hq0, he⟩ := List.mem_map.1 hq
  simp only [Prod.mk.injEq] at he
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
  refine ⟨(Gs p.1).budgetEscape_isEsc hq0, fun hc => ?_⟩
  have hj : j = p.1 := hl.2.2.2 hc
  subst hj
  exact ⟨rfl, p.2, q0.2, hl.2.2.1, ha, hq0⟩

/-- **The escape dependency graph is well founded**: from an escape channel the dependencies are
those of its lane, and an adaptive or injection channel only leads to escape channels. -/
theorem shared_esc_wf :
    WellFounded (flip ((sharedNet ls Gs B).Dep (sharedLegal ls Gs B) (sharedEsc Gs))) := by
  have hesc : ∀ j c, c.isEsc = true →
      Acc (flip ((sharedNet ls Gs B).Dep (sharedLegal ls Gs B) (sharedEsc Gs))) (j, c) := by
    intro j c hc
    have hacc := ((Gs j).budget_esc_wf B).apply c
    induction hacc with
    | intro c _ ih =>
      refine ⟨_, fun y hy => ?_⟩
      obtain ⟨j', c'⟩ := y
      obtain ⟨hc', h2⟩ := shared_dep hy
      obtain ⟨rfl, hd⟩ := h2 hc
      exact ih c' hd hc'
  refine ⟨fun x => ⟨_, fun y hy => ?_⟩⟩
  obtain ⟨j, c⟩ := x
  obtain ⟨j', c'⟩ := y
  exact hesc j' c' (shared_dep hy).1

/-- **The safety certificate of shared lanes.** -/
def sharedCert (ls : List ι) (Gs : ι → GraphData V) (B : ℕ) : SafeCert (sharedNet ls Gs B) where
  legal := sharedLegal ls Gs B
  closed := shared_closed
  finite := by
    refine (Set.Finite.biUnion (List.finite_toSet ls) fun j _ =>
      Set.Finite.biUnion (List.finite_toSet ls) fun L _ =>
        ((Gs L).budget_pairs_finite B).image fun q => ((j, q.1), (L, q.2))).subset ?_
    rintro ⟨⟨j, c⟩, L, p⟩ ⟨hj, hL, hl, -⟩
    exact Set.mem_biUnion hj (Set.mem_biUnion hL ⟨(c, p), hl, rfl⟩)
  esc := sharedEsc Gs
  esc_sub x p q hq := by
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 hq
    refine mem_sharedRoute.2 ⟨q0, (Gs p.1).budgetEscape_sub hq0, ?_⟩
    simp [spread, (Gs p.1).budgetEscape_isEsc hq0]
  esc_conn x p _ _ := by simp [sharedEsc, budgetEscape]
  esc_wf := shared_esc_wf
  rank x p := (Gs p.1).budgetRank x.2 p.2
  rank_lt x p q hl ha hq := by
    obtain ⟨q0, hq0, hs⟩ := mem_sharedRoute.1 hq
    obtain ⟨h1, h2, -, -⟩ := mem_spread hs
    rw [h1, h2]
    exact (Gs p.1).budget_rank_lt B x.2 p.2 q0 hl.2.2.1 ha hq0

/-- **Shared lanes are at least as adaptive as lanes**: every hop of the lane network of
`budgetNet`s, with the lane recorded in the header, is a hop of the shared network. -/
theorem lanes_route_sub {i : ι} (hi : i ∈ ls) {c : GChan V} {p : V × ℕ}
    {q : (ι × GChan V) × (V × ℕ)}
    (hq : q ∈ (Network.lanes ls fun i => (Gs i).budgetNet B).route (i, c) p) :
    (q.1, (i, q.2)) ∈ (sharedNet ls Gs B).route (i, c) (i, p) := by
  obtain ⟨q0, hq0, rfl⟩ := mem_lanes_route.1 hq
  refine mem_sharedRoute.2 ⟨q0, hq0, ?_⟩
  unfold spread
  split_ifs
  · exact List.mem_singleton_self _
  · exact List.mem_map.2 ⟨i, hi, rfl⟩

/-! ### Correctness -/

variable [DecidableEq ι]

/-- **Shared lanes are correct on every graph**: for every list of lanes, every graph data per
lane and every return budget, deadlock and livelock free under every valid selection, starvation
free under strong fairness, and every packet delivered under saturation along every channel-fair
run. -/
theorem shared_correct (ls : List ι) (Gs : ι → GraphData V) (B : ℕ) :
    (sharedNet ls Gs B).Correct ∧ (sharedNet ls Gs B).StarvationFree ∧
      ∀ sel, (sharedNet ls Gs B).ValidSel sel →
        (sharedNet ls Gs B).StarvationFreeUnderLoad sel (fun _ => False) :=
  ⟨(sharedCert ls Gs B).correct.1, (sharedCert ls Gs B).correct.2,
    fun _ hsel => ((sharedCert ls Gs B).underLoad_of_valid hsel).2.2⟩

/-- **Shared lanes with throttled sources are correct**: under every selection that never refuses
a free escape hop outside the injection channels and releases a source once the rest of the
network is empty, deadlock and livelock free, and every packet outside the injection channels is
delivered along every channel-fair run. -/
theorem shared_sourceSel (ls : List ι) (Gs : ι → GraphData V) (B : ℕ)
    {sel : Selection (ι × GChan V) (ι × (V × ℕ))}
    (hsel : (sharedNet ls Gs B).SourceSel (sharedEsc Gs) (fun x => x.2.isInj = true) sel) :
    (sharedNet ls Gs B).DeadlockFreeWith sel ∧ (sharedNet ls Gs B).LivelockFreeWith sel ∧
      (sharedNet ls Gs B).StarvationFreeUnderLoad sel (fun x => x.2.isInj = true) :=
  (sharedCert ls Gs B).sourceSel (fun x p q _ _ hq => by
    obtain ⟨q0, hq0, hs⟩ := mem_sharedRoute.1 hq
    obtain ⟨h1, -, -, -⟩ := mem_spread hs
    rw [h1]
    exact (Gs p.1).budget_route_not_inj hq0) hsel

end GraphData

end AsyncLean
