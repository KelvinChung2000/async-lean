/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshNorthLast
import AsyncLean.Routing.Source

/-!
# A priority, source-throttled selection for the mesh

The routing function says which hops a packet may take; the selection function says which one it
takes, and that choice decides how the network performs under load.  On the two-virtual-channel
meshes, a random choice among the free permitted hops collapses under heavy load: in the
cycle-level simulation (`scripts/routing_sim.py --bench`) Duato's mesh accepts 0.14 packets per
node and cycle under uniform traffic on a 16 × 16 mesh offered 0.3, and the west-first mesh 0.08.

`priorityMesh` is a selection under which the network does better.  Each packet is offered the
free permitted hops of the first priority level that admits one:

1. its **preferred hop**, which keeps its dimension order: XY on virtual channel 0, YX on
   virtual channel 1 (from an injection channel, either);
2. the **escape hop** (XY on virtual channel 0);
3. any productive hop on **virtual channel 1**;

and a packet in its injection channel leaves only towards a router with at least `g` of its 8
outgoing channels free (**source throttling**; channels leaving the mesh count as free), so the
network drains before it fills up.

It only takes hops of Duato's mesh.  The extra hops of the maximally adaptive meshes do not
pay off here: a fourth level taking them (straight on) made transpose and shuffle traffic faster on
8 × 8 meshes but made hotspot and bit-reversal traffic collapse on 16 × 16 meshes.

In the simulation (`docs/routing-adaptivity.md`, "A selection that performs"; measurements, not
theorems), with `g = 4`, it has the highest peak throughput of the schemes compared (Duato's mesh
with a random or a throttled random selection, XY on both virtual channels, O1TURN, the west-first
mesh with a random selection) under uniform, shuffle, bit-reversal and hotspot traffic on 8 × 8 and
16 × 16 meshes, and the best worst case over the six patterns: at least 87 % (8 × 8) and 90 %
(16 × 16) of the best scheme on each.  It is about 10 % behind the west-first mesh under
transpose traffic and behind XY on both virtual channels under bit-complement traffic, and on
4 × 4 meshes the throttling costs it 3 to 5 % against the random selections.

What is proved is that it is safe.  The throttling refuses free escape hops, so Duato's condition
for selection functions (`Network.EscapeSel`) fails.  It holds with throttled sources
(`Network.SourceSel`): injection channels are never the target of a hop, and a source lets its
packet go once the rest of the network is empty.  So, for every mesh size and every `g ≤ 8`:

* `duatoPriority_correct k g` : Duato's mesh under the priority selection is deadlock free, livelock
  free and starvation free (every packet of every strongly fair run is delivered, those held back
  in their injection channels too; strong fairness makes such a run revisit the empty network,
  so this is not a statement about sustained saturation).
* `westFirstPriority_correct k g`, `northLastPriority_correct k g` : the same on the maximally
  adaptive meshes.
* `duatoPriorities_correct`, `westFirstPriorities_correct`, `northLastPriorities_correct` : the same
  for **every** level list containing the throttled escape level `escPriority k g`; the other levels
  may prefer any permitted hops and read the whole configuration.
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

/-- The throttled escape level: the XY hop on virtual channel 0, from a source only towards a
router with at least `g` free outgoing channels.  Every level list containing it is safe
(`prioritySel_sourceSel`), whatever the other levels prefer. -/
def escPriority (k g : ℕ) : Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool :=
  fun f c d q => sourceOpen k g f c q && q.1 == ch (head k c) (xy k (head k c) d) 0

/-- The levels: the preferred hop (from an injection channel: either dimension order), the escape
hop, then any productive hop on virtual channel 1. -/
def meshPriorities (k g : ℕ) : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool) :=
  [fun f c d q => sourceOpen k g f c q &&
      (q.1 == prefCh k c d || (dir c == 4 && q.1 == ch (head k c) (xy k (head k c) d) 0)),
   escPriority k g,
   fun f c _ q => sourceOpen k g f c q && q.1 % 2 == 1]

theorem escPriority_mem_meshPriorities (k g : ℕ) : escPriority k g ∈ meshPriorities k g :=
  List.mem_cons_of_mem _ List.mem_cons_self

end Mesh

/-- **The priority, source-throttled selection** on Duato's mesh with the turn model `turn` on its
escape subnetwork. -/
def priorityMesh (turn : ℕ → ℕ → ℕ → List ℕ) (k g : ℕ) : Selection ℕ ℕ :=
  (turnDuatoMesh turn k).prioritySel (meshPriorities k g)

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

/-- **Every level list containing the throttled escape level** gives a selection satisfying
Duato's condition with throttled sources, on every network whose permitted hops include the XY
escape hop, for every throttling threshold up to 8.  The other levels are arbitrary: they may
prefer any hops, in any order, and read the whole configuration. -/
theorem prioritySel_sourceSel {k : ℕ} (N : Network ℕ ℕ)
    (hesc : ∀ c d, (ch (head k c) (xy k (head k c) d) 0, d) ∈ N.route c d) {g : ℕ} (hg : g ≤ 8)
    {levels : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)} (ht : escPriority k g ∈ levels) :
    N.SourceSel (xyEscape k) (fun c => dir c = 4) (N.prioritySel levels) where
  sub _ _ _ _ h := (N.mem_prioritySel h).1
  conserving f c d hs _ := by
    rintro ⟨q, hq, hfree⟩
    simp only [xyEscape, List.mem_singleton] at hq
    subst hq
    exact N.prioritySel_conserving ht (hesc c d) hfree (by simp [escPriority, sourceOpen, hs])
  source f c d _ _ hempty := by
    rintro ⟨q, hq, hfree⟩
    simp only [xyEscape, List.mem_singleton] at hq
    subst hq
    exact N.prioritySel_conserving ht (hesc c d) hfree
      (by simp [escPriority, sourceOpen, freeOut_eq hempty, hg])

theorem priority_sourceSel (turn : ℕ → ℕ → ℕ → List ℕ) (k : ℕ) {g : ℕ} (hg : g ≤ 8) :
    (turnDuatoMesh turn k).SourceSel (xyEscape k) (fun c => dir c = 4) (priorityMesh turn k g) :=
  prioritySel_sourceSel _ (fun _ _ => by simp [turnDuatoMesh]) hg (escPriority_mem_meshPriorities k
      g)

end Mesh

/-- **The west-first mesh of every size under every priority selection containing the throttled
escape level** is deadlock free, livelock free and starvation free. -/
theorem westFirstPriorities_correct (k : ℕ) {g : ℕ} (hg : g ≤ 8)
    {levels : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)} (ht : escPriority k g ∈ levels) :
    (westFirstMesh k).DeadlockFreeWith ((westFirstMesh k).prioritySel levels) ∧
      (westFirstMesh k).LivelockFreeWith ((westFirstMesh k).prioritySel levels) ∧
      (westFirstMesh k).StarvationFreeWith ((westFirstMesh k).prioritySel levels) :=
  have hsel := prioritySel_sourceSel (westFirstMesh k) (k := k)
    (fun _ _ => by simp [westFirstMesh, turnDuatoMesh]) hg ht
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

/-- **The north-last mesh of every size under every priority selection containing the throttled
escape level** is deadlock free, livelock free and starvation free. -/
theorem northLastPriorities_correct (k : ℕ) {g : ℕ} (hg : g ≤ 8)
    {levels : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)} (ht : escPriority k g ∈ levels) :
    (northLastMesh k).DeadlockFreeWith ((northLastMesh k).prioritySel levels) ∧
      (northLastMesh k).LivelockFreeWith ((northLastMesh k).prioritySel levels) ∧
      (northLastMesh k).StarvationFreeWith ((northLastMesh k).prioritySel levels) :=
  have hsel := prioritySel_sourceSel (northLastMesh k) (k := k)
    (fun _ _ => by simp [northLastMesh, turnDuatoMesh]) hg ht
  have hR : ∀ c d q, nlLegal k c d → (northLastMesh k).arrived c d = false →
      q ∈ xyEscape k c d → ¬ dir q.1 = 4 := fun _ _ _ _ _ hq => esc_not_source hq
  ⟨(northLastMesh k).deadlockFreeWith_of_source (nl_closed k) (xyEscape k) nl_esc_conn (nl_wf k)
      hR hsel,
    (northLastMesh k).livelockFreeWith_of_ranking (nl_closed k) (nl_chans_finite k) (meshDist k)
      (fun _ _ _ hl ha hq => nl_dist hl ha hq) hsel.sub,
    (northLastMesh k).starvationFreeWith_of_source (nl_closed k) (nl_pairs_finite k)
      (xyEscape k) nl_esc_conn (nl_wf k) hR (meshDist k) (fun _ _ _ hl ha hq => nl_dist hl ha hq)
      hsel⟩

/-- **Duato's mesh of every size under every priority selection containing the throttled escape
level** is deadlock free, livelock free and starvation free. -/
theorem duatoPriorities_correct (k : ℕ) {g : ℕ} (hg : g ≤ 8)
    {levels : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)} (ht : escPriority k g ∈ levels) :
    (duatoMesh k).DeadlockFreeWith ((duatoMesh k).prioritySel levels) ∧
      (duatoMesh k).LivelockFreeWith ((duatoMesh k).prioritySel levels) ∧
      (duatoMesh k).StarvationFreeWith ((duatoMesh k).prioritySel levels) :=
  have ext := duatoMesh_extends westFirst k
  have hsel := prioritySel_sourceSel (duatoMesh k) (k := k) (fun _ _ => by simp [duatoMesh]) hg ht
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

/-- **The west-first mesh of every size under the priority, source-throttled selection** is
deadlock free, livelock free and starvation free. -/
theorem westFirstPriority_correct (k : ℕ) {g : ℕ} (hg : g ≤ 8) :
    (westFirstMesh k).DeadlockFreeWith (priorityMesh westFirst k g) ∧
      (westFirstMesh k).LivelockFreeWith (priorityMesh westFirst k g) ∧
      (westFirstMesh k).StarvationFreeWith (priorityMesh westFirst k g) :=
  westFirstPriorities_correct k hg (escPriority_mem_meshPriorities k g)

/-- **The north-last mesh of every size under the priority, source-throttled selection** is
deadlock free, livelock free and starvation free. -/
theorem northLastPriority_correct (k : ℕ) {g : ℕ} (hg : g ≤ 8) :
    (northLastMesh k).DeadlockFreeWith (priorityMesh northLast k g) ∧
      (northLastMesh k).LivelockFreeWith (priorityMesh northLast k g) ∧
      (northLastMesh k).StarvationFreeWith (priorityMesh northLast k g) :=
  northLastPriorities_correct k hg (escPriority_mem_meshPriorities k g)

/-- The priority selection only takes hops of Duato's mesh (the preferred, escape and virtual
channel 1 hops), so it can run on Duato's mesh itself: **Duato's mesh of every size under the
priority, source-throttled selection** is deadlock free, livelock free and starvation free. -/
theorem duatoPriority_correct (k : ℕ) {g : ℕ} (hg : g ≤ 8) :
    (duatoMesh k).DeadlockFreeWith ((duatoMesh k).prioritySel (meshPriorities k g)) ∧
      (duatoMesh k).LivelockFreeWith ((duatoMesh k).prioritySel (meshPriorities k g)) ∧
      (duatoMesh k).StarvationFreeWith ((duatoMesh k).prioritySel (meshPriorities k g)) :=
  duatoPriorities_correct k hg (escPriority_mem_meshPriorities k g)

#assert_standard_axioms duatoPriorities_correct westFirstPriorities_correct
  northLastPriorities_correct
#assert_standard_axioms duatoPriority_correct westFirstPriority_correct northLastPriority_correct
  Mesh.priority_sourceSel

end AsyncLean.Examples
