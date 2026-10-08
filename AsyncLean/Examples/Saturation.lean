/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshTiered
import AsyncLean.Routing.Graph
import AsyncLean.Routing.Saturation

/-!
# Delivery under saturation: the meshes and every connected graph

Instances of `Network.starvationFreeUnderLoad_of_source` and
`Network.starvationFreeUnderLoad_of_escape` (`AsyncLean.Routing.Saturation`): along every
**channel-fair** run (`Network.ChannelFair`, fairness of each channel's departures, not of whole
configurations), with injections that may never stop, packets are delivered.

## Main results

The meshes, for every size `k`:

* `duatoTiers_underLoad k hg ht`, `westFirstTiers_underLoad`, `northLastTiers_underLoad` : under
  every tiered selection containing the throttled escape tier (`Mesh.escTier`; in particular the
  tiered, source-throttled selection of `AsyncLean.Examples.MeshTiered`), every packet outside
  the injection channels (`dir c = 4`) is delivered.  A packet held back in its injection channel
  by the throttle may wait for ever when the network stays saturated: the throttle need only open
  once the rest of the network is empty.
* `duatoMesh_underLoad k`, `westFirstMesh_underLoad k`, `northLastMesh_underLoad k` : under
  every valid (work-conserving) selection, *every* packet is delivered, those in their injection
  channels included.

Every finite connected graph (`AsyncLean.Routing.Graph`):

* `GraphData.underLoad_of_escapeSel` : under every selection that never refuses a free escape
  hop, every packet is delivered; `GraphData.underLoad` : in particular under every valid
  selection.
* `GraphData.underLoad_of_sourceSel` : under a selection that throttles the injection channels,
  every packet outside them is delivered.
* `GraphData.exists_underLoad` : every finite connected undirected graph, with any distance
  estimate, carries an adaptive network in which every packet is delivered along every
  channel-fair run under every valid selection, with continuous injection.
-/

namespace AsyncLean.Examples

open Network Mesh

namespace Mesh

/-- No hop of a turn-model mesh leads into an injection channel. -/
theorem turnDuato_not_source {turn : ℕ → ℕ → ℕ → List ℕ}
    (hturn : ∀ k u d dr, dr ∈ turn k u d → dr ∈ productive k u d) {k c d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ (turnDuatoMesh turn k).route c d) : ¬ dir q.1 = 4 := by
  simp only [turnDuatoMesh, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter] at hq
  rcases hq with (rfl | ⟨dr, ⟨hdr, -⟩, rfl⟩) | ⟨dr, hdr, rfl⟩
  · have := xy_lt_four k (head k c) d
    rw [dir_ch (by omega) (by omega)]; omega
  · have := productive_lt (hturn _ _ _ _ hdr)
    rw [dir_ch (by omega) (by omega)]; omega
  · have := productive_lt hdr
    rw [dir_ch (by omega) (by omega)]; omega

/-- No hop of Duato's mesh leads into an injection channel. -/
theorem duato_not_source {k c d : ℕ} {q : ℕ × ℕ} (hq : q ∈ (duatoMesh k).route c d) :
    ¬ dir q.1 = 4 := by
  simp only [duatoMesh, List.mem_cons, List.mem_map] at hq
  rcases hq with rfl | ⟨dr, hdr, rfl⟩
  · have := xy_lt_four k (head k c) d
    rw [dir_ch (by omega) (by omega)]; omega
  · have := productive_lt hdr
    rw [dir_ch (by omega) (by omega)]; omega

/-- The XY escape hop is a permitted hop of every turn-model mesh. -/
theorem xyEscape_sub_turn {turn : ℕ → ℕ → ℕ → List ℕ} {k c d : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ xyEscape k c d) : q ∈ (turnDuatoMesh turn k).route c d := by
  simp only [xyEscape, List.mem_singleton] at hq
  subst hq; simp [turnDuatoMesh]

/-- The XY escape hop is a permitted hop of Duato's mesh. -/
theorem xyEscape_sub_duato {k c d : ℕ} {q : ℕ × ℕ} (hq : q ∈ xyEscape k c d) :
    q ∈ (duatoMesh k).route c d := by
  simp only [xyEscape, List.mem_singleton] at hq
  subst hq; simp [duatoMesh]

/-- Duato's mesh is closed on the legal pairs of the west-first mesh. -/
theorem duato_closed (k : ℕ) : (duatoMesh k).Closed (wfLegal k) :=
  have ext := duatoMesh_extends westFirst k
  ⟨(wf_closed k).inject, fun c d q hl ha hq => (wf_closed k).route c d q hl ha
    (ext.route c d q ha hq)⟩

/-- On Duato's mesh, the distance to the destination decreases on every hop. -/
theorem duato_dist {k c d : ℕ} {q : ℕ × ℕ} (hl : wfLegal k c d)
    (ha : (duatoMesh k).arrived c d = false) (hq : q ∈ (duatoMesh k).route c d) :
    wfDist k q.1 q.2 < wfDist k c d := by
  have := wf_dist hl ha ((duatoMesh_extends westFirst k).route _ _ _ ha hq); omega

end Mesh

/-- **Duato's mesh under saturation, with throttled sources**: for every size, under every tiered
selection containing the throttled escape tier, every packet outside the injection channels is
delivered along every channel-fair run, however the sources inject. -/
theorem duatoTiers_underLoad (k : ℕ) {g : ℕ} (hg : g ≤ 8)
    {tiers : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)} (ht : escTier k g ∈ tiers) :
    (duatoMesh k).StarvationFreeUnderLoad ((duatoMesh k).tieredSel tiers) (fun c => dir c = 4) :=
  (duatoMesh k).starvationFreeUnderLoad_of_source (duato_closed k) (xyEscape k)
    (fun _ _ _ _ => by simp [xyEscape]) (wf_wf k) (fun _ _ _ _ _ hq => esc_not_source hq)
    (fun _ _ _ _ _ hq => duato_not_source hq) (wfDist k) (fun _ _ _ hl ha hq => duato_dist hl ha hq)
    (tieredSel_sourceSel (duatoMesh k) (k := k) (fun _ _ => by simp [duatoMesh]) hg ht)

/-- **The west-first mesh under saturation, with throttled sources**: every packet outside the
injection channels is delivered along every channel-fair run. -/
theorem westFirstTiers_underLoad (k : ℕ) {g : ℕ} (hg : g ≤ 8)
    {tiers : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)} (ht : escTier k g ∈ tiers) :
    (westFirstMesh k).StarvationFreeUnderLoad ((westFirstMesh k).tieredSel tiers)
      (fun c => dir c = 4) :=
  (westFirstMesh k).starvationFreeUnderLoad_of_source (wf_closed k) (xyEscape k) wf_esc_conn
    (wf_wf k) (fun _ _ _ _ _ hq => esc_not_source hq)
    (fun _ _ _ _ _ hq => turnDuato_not_source (fun _ _ _ _ h => westFirst_sub h) hq) (wfDist k)
    (fun _ _ _ hl ha hq => by have := wf_dist hl ha hq; omega)
    (tieredSel_sourceSel (westFirstMesh k) (k := k)
      (fun _ _ => by simp [westFirstMesh, turnDuatoMesh]) hg ht)

/-- **The north-last mesh under saturation, with throttled sources**: every packet outside the
injection channels is delivered along every channel-fair run. -/
theorem northLastTiers_underLoad (k : ℕ) {g : ℕ} (hg : g ≤ 8)
    {tiers : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)} (ht : escTier k g ∈ tiers) :
    (northLastMesh k).StarvationFreeUnderLoad ((northLastMesh k).tieredSel tiers)
      (fun c => dir c = 4) :=
  (northLastMesh k).starvationFreeUnderLoad_of_source (nl_closed k) (xyEscape k) nl_esc_conn
    (nl_wf k) (fun _ _ _ _ _ hq => esc_not_source hq)
    (fun _ _ _ _ _ hq => turnDuato_not_source (fun _ _ _ _ h => northLast_sub h) hq) (meshDist k)
    (fun _ _ _ hl ha hq => nl_dist hl ha hq)
    (tieredSel_sourceSel (northLastMesh k) (k := k)
      (fun _ _ => by simp [northLastMesh, turnDuatoMesh]) hg ht)

/-- **The tiered, source-throttled selection on Duato's mesh under saturation**: every packet
outside the injection channels is delivered along every channel-fair run. -/
theorem duatoTiered_underLoad (k : ℕ) {g : ℕ} (hg : g ≤ 8) :
    (duatoMesh k).StarvationFreeUnderLoad ((duatoMesh k).tieredSel (meshTiers k g))
      (fun c => dir c = 4) :=
  duatoTiers_underLoad k hg (escTier_mem_meshTiers k g)

/-- **Duato's mesh under saturation**: for every size, under every valid selection, every packet
(including those in their injection channels) is delivered along every channel-fair run, with
injections going on for ever. -/
theorem duatoMesh_underLoad (k : ℕ) {sel : Selection ℕ ℕ} (hsel : (duatoMesh k).ValidSel sel) :
    (duatoMesh k).StarvationFreeUnderLoad sel (fun _ => False) :=
  (duatoMesh k).starvationFreeUnderLoad_of_escape (duato_closed k) (xyEscape k)
    (fun _ _ _ _ => by simp [xyEscape]) (wf_wf k) (wfDist k)
    (fun _ _ _ hl ha hq => duato_dist hl ha hq)
    (ValidSel.escapeSel _ hsel fun _ _ _ hq => xyEscape_sub_duato hq)

/-- **The west-first mesh under saturation**: under every valid selection, every packet is
delivered along every channel-fair run. -/
theorem westFirstMesh_underLoad (k : ℕ) {sel : Selection ℕ ℕ}
    (hsel : (westFirstMesh k).ValidSel sel) :
    (westFirstMesh k).StarvationFreeUnderLoad sel (fun _ => False) :=
  (westFirstMesh k).starvationFreeUnderLoad_of_escape (wf_closed k) (xyEscape k) wf_esc_conn
    (wf_wf k) (wfDist k) (fun _ _ _ hl ha hq => by have := wf_dist hl ha hq; omega)
    (ValidSel.escapeSel _ hsel fun _ _ _ hq => xyEscape_sub_turn hq)

/-- **The north-last mesh under saturation**: under every valid selection, every packet is
delivered along every channel-fair run. -/
theorem northLastMesh_underLoad (k : ℕ) {sel : Selection ℕ ℕ}
    (hsel : (northLastMesh k).ValidSel sel) :
    (northLastMesh k).StarvationFreeUnderLoad sel (fun _ => False) :=
  (northLastMesh k).starvationFreeUnderLoad_of_escape (nl_closed k) (xyEscape k) nl_esc_conn
    (nl_wf k) (meshDist k) (fun _ _ _ hl ha hq => nl_dist hl ha hq)
    (ValidSel.escapeSel _ hsel fun _ _ _ hq => xyEscape_sub_turn hq)

end AsyncLean.Examples

namespace AsyncLean

open Network

namespace GraphData

variable {V : Type*} [DecidableEq V] (G : GraphData V)

/-- The escape hop is always a permitted hop. -/
theorem escape_sub {c : GChan V} {d : V} {q : GChan V × V} (hq : q ∈ G.escape c d) :
    q ∈ G.net.route c d := by
  simp only [net]
  split_ifs
  · exact hq
  · exact List.mem_append_left _ hq

/-- No hop leads into an injection channel. -/
theorem route_not_inj {c : GChan V} {d : V} {q : GChan V × V} (hq : q ∈ G.net.route c d) :
    ¬ q.1.isInj := by
  rcases G.mem_route hq with rfl | ⟨-, v, -, -, rfl⟩ <;> simp [escHop, GChan.isInj]

/-- **Every packet is delivered under saturation**: under every selection that never refuses a
free escape hop, along every channel-fair run, with injections going on for ever. -/
theorem underLoad_of_escapeSel {sel : Selection (GChan V) V} (hsel : G.net.EscapeSel G.escape sel) :
    G.net.StarvationFreeUnderLoad sel (fun _ => False) :=
  G.net.starvationFreeUnderLoad_of_escape G.closed G.escape G.esc_conn G.esc_wf G.rank G.rank_lt
    hsel

/-- **Every packet is delivered under saturation**, under every valid selection. -/
theorem underLoad {sel : Selection (GChan V) V} (hsel : G.net.ValidSel sel) :
    G.net.StarvationFreeUnderLoad sel (fun _ => False) :=
  G.underLoad_of_escapeSel (ValidSel.escapeSel _ hsel fun _ _ _ hq => G.escape_sub hq)

/-- **Delivery under saturation with throttled sources**: under every selection that never refuses
a free escape hop outside the injection channels and releases a source's packet once the rest of
the network is empty, every packet outside the injection channels is delivered along every
channel-fair run.  A packet held back by the throttle may wait for ever under saturation. -/
theorem underLoad_of_sourceSel {sel : Selection (GChan V) V}
    (hsel : G.net.SourceSel G.escape (fun c => c.isInj) sel) :
    G.net.StarvationFreeUnderLoad sel (fun c => c.isInj) :=
  G.net.starvationFreeUnderLoad_of_source G.closed G.escape G.esc_conn G.esc_wf G.esc_not_inj
    (fun _ _ _ _ _ hq => G.route_not_inj hq) G.rank G.rank_lt hsel

/-- **Every finite connected undirected graph carries an adaptive network that delivers every
packet under saturation**: with any distance estimate for its adaptive layer, under every valid
selection, along every channel-fair run, with injections going on for ever. -/
theorem exists_underLoad (verts : List V) (mem_verts : ∀ v, v ∈ verts)
    (nbrs : V → List V) (symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v) (dist : V → V → ℕ) (r : V)
    (conn : ∀ u, Relation.ReflTransGen (fun a b => b ∈ nbrs a) r u) :
    ∃ G : GraphData V, G.nbrs = nbrs ∧ G.dist = dist ∧ G.net.Correct ∧
      ∀ sel, G.net.ValidSel sel → G.net.StarvationFreeUnderLoad sel (fun _ => False) :=
  ⟨GraphData.ofConnected verts mem_verts nbrs symm dist r conn, rfl, rfl,
    (GraphData.ofConnected verts mem_verts nbrs symm dist r conn).correct.1,
    fun _ hsel => (GraphData.ofConnected verts mem_verts nbrs symm dist r conn).underLoad hsel⟩

end GraphData

#assert_standard_axioms GraphData.underLoad_of_escapeSel GraphData.underLoad
#assert_standard_axioms GraphData.underLoad_of_sourceSel GraphData.exists_underLoad

end AsyncLean

namespace AsyncLean.Examples

#assert_standard_axioms duatoTiers_underLoad westFirstTiers_underLoad northLastTiers_underLoad
#assert_standard_axioms duatoTiered_underLoad duatoMesh_underLoad westFirstMesh_underLoad
#assert_standard_axioms northLastMesh_underLoad

end AsyncLean.Examples
