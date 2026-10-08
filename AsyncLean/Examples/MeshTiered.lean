/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshNorthLast
import AsyncLean.Routing.Source

/-!
# A tiered, source-throttled selection for the mesh

The routing function says which hops a packet may take; the selection function says which one it
takes, and that choice decides how the network performs under load.  On the two-virtual-channel
meshes, a random choice among the free permitted hops collapses under heavy load: in the
cycle-level simulation (`scripts/routing_sim.py --bench`) Duato's mesh accepts 0.14 packets per
node and cycle under uniform traffic on a 16 × 16 mesh offered 0.3, and the west-first mesh 0.08.

`tieredMesh` is a selection under which the network does better.  Each packet is offered the
free permitted hops of the first tier that admits one:

1. its **preferred hop**, which keeps its dimension order: XY on virtual channel 0, YX on
   virtual channel 1 (from an injection channel, either);
2. the **escape hop** (XY on virtual channel 0);
3. any productive hop on **virtual channel 1**;

and a packet in its injection channel leaves only towards a router with at least `g` of its 8
outgoing channels free (**source throttling**), so the network drains before it fills up.

It only takes hops of Duato's mesh.  The extra hops of the maximally adaptive meshes do not
pay off here: a fourth tier taking them (straight on) made transpose and shuffle traffic faster on
8 × 8 meshes but made hotspot and bit-reversal traffic collapse on 16 × 16 meshes.

In the simulation (README, "A selection that performs"; measurements, not theorems), with
`g = 4`, it has the highest peak throughput of the schemes compared (Duato's mesh with a random
or a throttled random selection, XY on both virtual channels, O1TURN, the west-first mesh with a
random selection) under uniform, shuffle, bit-reversal and hotspot traffic on 8 × 8 and 16 × 16
meshes, and the best worst case over the six patterns: at least 87 % (8 × 8) and 90 %
(16 × 16) of the best scheme on each.  It is about 10 % behind the west-first mesh under
transpose traffic and behind XY on both virtual channels under bit-complement traffic, and on
4 × 4 meshes the throttling costs it 3 to 5 % against the random selections.

What is proved is that it is safe.  The throttling refuses free escape hops, so Duato's condition
for selection functions (`Network.EscapeSel`) fails.  It holds with throttled sources
(`Network.SourceSel`): injection channels are never the target of a hop, and a source lets its
packet go once the rest of the network is empty.  So, for every mesh size and every `g ≤ 8`:

* `duatoTiered_correct k g` : Duato's mesh under the tiered selection is deadlock free, livelock
  free and starvation free (every packet of every strongly fair run is delivered, those held back
  at their sources too).
* `westFirstTiered_correct k g`, `northLastTiered_correct k g` : the same on the maximally
  adaptive meshes.
-/

namespace AsyncLean.Examples

open Network Mesh

namespace Mesh

/-- Dimension order YX: correct the row first, then the column. -/
def yx (k u d : ℕ) : ℕ :=
  if u / k < d / k then 2 else if d / k < u / k then 3 else xy k u d

/-- The preferred next channel of a packet: it keeps its dimension order, XY on virtual channel 0
and YX on virtual channel 1. -/
def prefCh (k c d : ℕ) : ℕ :=
  if c % 2 = 0 ∧ dir c ≠ 4 then ch (head k c) (xy k (head k c) d) 0
  else ch (head k c) (yx k (head k c) d) 1

/-- Source throttling: a packet in its injection channel may only go towards a router with at
least `g` of its 8 outgoing channels free. -/
def sourceOpen (k g : ℕ) (f : Config ℕ ℕ) (c : ℕ) (q : ℕ × ℕ) : Bool :=
  dir c != 4 || decide (g ≤ freeOut f (head k q.1))

/-- The tiers: the preferred hop (from an injection channel: either dimension order), the escape
hop, then any productive hop on virtual channel 1. -/
def meshTiers (k g : ℕ) : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool) :=
  [fun f c d q => sourceOpen k g f c q &&
      (q.1 == prefCh k c d || (dir c == 4 && q.1 == ch (head k c) (xy k (head k c) d) 0)),
   fun f c d q => sourceOpen k g f c q && q.1 == ch (head k c) (xy k (head k c) d) 0,
   fun f c _ q => sourceOpen k g f c q && q.1 % 2 == 1]

end Mesh

/-- **The tiered, source-throttled selection** on Duato's mesh with the turn model `turn` on its
escape layer. -/
def tieredMesh (turn : ℕ → ℕ → ℕ → List ℕ) (k g : ℕ) : Selection ℕ ℕ :=
  (turnDuatoMesh turn k).tieredSel (meshTiers k g)

namespace Mesh

theorem xy_lt_four (k u d : ℕ) : xy k u d < 4 := by
  unfold xy; split_ifs <;> omega

/-- When only injection channels are occupied, every router has all 8 outgoing channels free. -/
theorem freeOut_eq {f : Config ℕ ℕ} (hf : ∀ c, ¬ dir c = 4 → f c = none) (v : ℕ) :
    freeOut f v = 8 := by
  unfold freeOut
  rw [List.countP_eq_length.2]
  · rfl
  · intro c hc
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hc
    obtain ⟨dr, hdr, rfl | rfl⟩ := hc
    · rw [hf _ (by rw [dir_ch (by omega) (by omega)]; omega)]; rfl
    · rw [hf _ (by rw [dir_ch (by omega) (by omega)]; omega)]; rfl

theorem esc_not_source {k c d : ℕ} {q : ℕ × ℕ} (hq : q ∈ xyEscape k c d) : ¬ dir q.1 = 4 := by
  simp only [xyEscape, List.mem_singleton] at hq
  subst hq
  have := xy_lt_four k (head k c) d
  rw [dir_ch (by omega) (by omega)]
  omega

/-- The tiered selection satisfies Duato's condition with throttled sources on every network
whose permitted hops include the XY escape hop, for every throttling threshold up to 8. -/
theorem tieredSel_sourceSel {k : ℕ} (N : Network ℕ ℕ)
    (hesc : ∀ c d, (ch (head k c) (xy k (head k c) d) 0, d) ∈ N.route c d) {g : ℕ} (hg : g ≤ 8) :
    N.SourceSel (xyEscape k) (fun c => dir c = 4) (N.tieredSel (meshTiers k g)) where
  sub _ _ _ _ h := (N.mem_tieredSel h).1
  conserving f c d hs _ := by
    rintro ⟨q, hq, hfree⟩
    simp only [xyEscape, List.mem_singleton] at hq
    subst hq
    exact N.tieredSel_conserving (List.mem_cons_of_mem _ List.mem_cons_self) (hesc c d) hfree
      (by simp [sourceOpen, hs])
  source f c d _ _ hempty := by
    rintro ⟨q, hq, hfree⟩
    simp only [xyEscape, List.mem_singleton] at hq
    subst hq
    exact N.tieredSel_conserving (List.mem_cons_of_mem _ List.mem_cons_self) (hesc c d) hfree
      (by simp [sourceOpen, freeOut_eq hempty, hg])

theorem tiered_sourceSel (turn : ℕ → ℕ → ℕ → List ℕ) (k : ℕ) {g : ℕ} (hg : g ≤ 8) :
    (turnDuatoMesh turn k).SourceSel (xyEscape k) (fun c => dir c = 4) (tieredMesh turn k g) :=
  tieredSel_sourceSel _ (fun _ _ => by simp [turnDuatoMesh]) hg

end Mesh

/-- **The west-first mesh of every size under the tiered, source-throttled selection** is
deadlock free, livelock free and starvation free. -/
theorem westFirstTiered_correct (k : ℕ) {g : ℕ} (hg : g ≤ 8) :
    (westFirstMesh k).DeadlockFreeWith (tieredMesh westFirst k g) ∧
      (westFirstMesh k).LivelockFreeWith (tieredMesh westFirst k g) ∧
      (westFirstMesh k).StarvationFreeWith (tieredMesh westFirst k g) :=
  have hsel := tiered_sourceSel westFirst k hg
  have hR : ∀ c d q, wfLegal k c d → (westFirstMesh k).arrived c d = false →
      q ∈ xyEscape k c d → ¬ dir q.1 = 4 := fun _ _ _ _ _ hq => esc_not_source hq
  have hrk : ∀ c d q, wfLegal k c d → (westFirstMesh k).arrived c d = false →
      q ∈ (westFirstMesh k).route c d → wfDist k q.1 q.2 < wfDist k c d :=
    fun _ _ _ hl ha hq => by have := wf_dist hl ha hq; omega
  ⟨(westFirstMesh k).deadlockFreeWith_of_source (wf_closed k) (xyEscape k) wf_esc_conn (wf_wf k)
      hR hsel,
    (westFirstMesh k).livelockFreeWith_of_ranking (wf_closed k) (wf_chans_finite k) (wfDist k)
      hrk hsel.sub,
    (westFirstMesh k).starvationFreeWith_of_source (wf_closed k) (wf_pairs_finite k) (xyEscape k)
      wf_esc_conn (wf_wf k) hR (wfDist k) hrk hsel⟩

/-- **The north-last mesh of every size under the tiered, source-throttled selection** is
deadlock free, livelock free and starvation free. -/
theorem northLastTiered_correct (k : ℕ) {g : ℕ} (hg : g ≤ 8) :
    (northLastMesh k).DeadlockFreeWith (tieredMesh northLast k g) ∧
      (northLastMesh k).LivelockFreeWith (tieredMesh northLast k g) ∧
      (northLastMesh k).StarvationFreeWith (tieredMesh northLast k g) :=
  have hsel := tiered_sourceSel northLast k hg
  have hR : ∀ c d q, nlLegal k c d → (northLastMesh k).arrived c d = false →
      q ∈ xyEscape k c d → ¬ dir q.1 = 4 := fun _ _ _ _ _ hq => esc_not_source hq
  ⟨(northLastMesh k).deadlockFreeWith_of_source (nl_closed k) (xyEscape k) nl_esc_conn (nl_wf k)
      hR hsel,
    (northLastMesh k).livelockFreeWith_of_ranking (nl_closed k) (nl_chans_finite k) (meshDist k)
      (fun _ _ _ hl ha hq => nl_dist hl ha hq) hsel.sub,
    (northLastMesh k).starvationFreeWith_of_source (nl_closed k) (nl_pairs_finite k)
      (xyEscape k) nl_esc_conn (nl_wf k) hR (meshDist k) (fun _ _ _ hl ha hq => nl_dist hl ha hq)
      hsel⟩

/-- The tiered selection only takes hops of Duato's mesh (the preferred, escape and virtual
channel 1 hops), so it can run on Duato's mesh itself: **Duato's mesh of every size under the
tiered, source-throttled selection** is deadlock free, livelock free and starvation free. -/
theorem duatoTiered_correct (k : ℕ) {g : ℕ} (hg : g ≤ 8) :
    (duatoMesh k).DeadlockFreeWith ((duatoMesh k).tieredSel (meshTiers k g)) ∧
      (duatoMesh k).LivelockFreeWith ((duatoMesh k).tieredSel (meshTiers k g)) ∧
      (duatoMesh k).StarvationFreeWith ((duatoMesh k).tieredSel (meshTiers k g)) :=
  have ext := duatoMesh_extends westFirst k
  have hsel := tieredSel_sourceSel (duatoMesh k) (k := k) (fun _ _ => by simp [duatoMesh]) hg
  have hcl : (duatoMesh k).Closed (wfLegal k) :=
    ⟨(wf_closed k).inject, fun c d q hl ha hq => (wf_closed k).route c d q hl ha
      (ext.route c d q ha hq)⟩
  have hwf : WellFounded (flip ((duatoMesh k).Dep (wfLegal k) (xyEscape k))) := wf_wf k
  have hconn : ∀ c d, wfLegal k c d → (duatoMesh k).arrived c d = false → xyEscape k c d ≠ [] :=
    fun _ _ _ _ => by simp [xyEscape]
  have hR : ∀ c d q, wfLegal k c d → (duatoMesh k).arrived c d = false →
      q ∈ xyEscape k c d → ¬ dir q.1 = 4 := fun _ _ _ _ _ hq => esc_not_source hq
  have hrk : ∀ c d q, wfLegal k c d → (duatoMesh k).arrived c d = false →
      q ∈ (duatoMesh k).route c d → wfDist k q.1 q.2 < wfDist k c d :=
    fun _ _ _ hl ha hq => by have := wf_dist hl ha (ext.route _ _ _ ha hq); omega
  ⟨(duatoMesh k).deadlockFreeWith_of_source hcl (xyEscape k) hconn hwf hR hsel,
    (duatoMesh k).livelockFreeWith_of_ranking hcl (wf_chans_finite k) (wfDist k) hrk hsel.sub,
    (duatoMesh k).starvationFreeWith_of_source hcl (wf_pairs_finite k) (xyEscape k) hconn hwf hR
      (wfDist k) hrk hsel⟩

#assert_standard_axioms duatoTiered_correct westFirstTiered_correct northLastTiered_correct Mesh.tiered_sourceSel

end AsyncLean.Examples
