/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.GraphRouting
import AsyncLean.Routing.Lanes
import AsyncLean.Routing.SharedLanes
import AsyncLean.Routing.Widen
import AsyncLean.Flow.Scaling
import AsyncLean.AxiomAudit

/-!
# Example: the torus with `m` connections per link, as `m` lanes

`torusLanes k m B` is the `(k + 1) × (k + 1)` torus `torus k` of
`AsyncLean.Examples.GraphRouting` with `m` connections per link, used as `m` lanes
(`Network.lanes`): each lane runs the detour network with Valiant's intermediates and at most `B`
returns (`GraphData.detourNet`, the network behind the simulated `bandit2m7f5k`), on its own two
virtual channels; a packet picks its lane at the source and stays on it.  For **every size `k`,
every number of lanes `m` and every budget `B`**:

* `torusLanes_correct` : deadlock and livelock free under every valid selection (which may
  compare lanes), starvation free under strong fairness, and every packet delivered under
  saturation along every channel-fair run;
* `torusLanes_sourceSel` : the same under every selection that never refuses a free escape hop
  outside the injection channels and may throttle the sources, for every packet outside them;
* `torusLanes_parallel` : any run of one lane is achieved by all `m` lanes at once, and
  delivers `m` times the packets;
* `torusLanes_reachable` : the reachable configurations are exactly the `m`-tuples of reachable
  configurations of one lane.

`torusShared k m B` shares the lanes (`GraphData.sharedNet`): escapes per lane, adaptive hops on
the adaptive channels of every lane; `torusShared_correct` proves it deadlock, livelock and
starvation free and delivering under saturation for every `k`, `m` and `B`.

`torusWide k m B` widens the detour network instead (`Network.widen`): one escape channel,
`2m - 1` adaptive channels per link and `m` injection channels per node, every copy usable by
every packet — the best performing use of the connections in simulation; `torusWide_correct`.

With `Fluid.torus_copies_worst` (the best worst case of `m` connections on the torus of even
side `k ≥ 4` is `m · 8 / k`, reached by Valiant in every lane) this is the scheme that scales
linearly with the connections, proved safe for every `m`.
-/

namespace AsyncLean.Examples

open Network

/-- The vertices of the torus `torus k`. -/
abbrev TV (k : ℕ) := Fin (k + 1) × Fin (k + 1)

/-- The packet headers of the detour network on `torus k`. -/
abbrev THdr (k : ℕ) := TV k × Option (TV k) × ℕ

/-- **The torus with `m` lanes**: `m` copies of the detour network with Valiant's intermediates
and at most `B` returns, side by side. -/
abbrev torusLanes (k m B : ℕ) :=
  lanes (List.finRange m) fun _ : Fin m => (torus k).detourNet B (torus k).anyDetour

/-- **The torus with `m` lanes is correct** for every size, number of lanes and budget. -/
theorem torusLanes_correct (k m B : ℕ) :
    (torusLanes k m B).Correct ∧ (torusLanes k m B).StarvationFree ∧
      ∀ sel, (torusLanes k m B).ValidSel sel →
        (torusLanes k m B).StarvationFreeUnderLoad sel (fun _ => False) :=
  GraphData.lanes_detour_correct (fun _ => torus k) B (fun _ => (torus k).anyDetour) _

/-- **The torus with `m` lanes and throttled sources is correct**: under every selection that
never refuses a free escape hop outside the injection channels and releases a source once the
rest of the network is empty. -/
theorem torusLanes_sourceSel (k m B : ℕ)
    {sel : Selection (Fin m × GChan (TV k)) (THdr k)}
    (hsel : (torusLanes k m B).SourceSel
      (SafeCert.lanes (fun _ => (torus k).detourCert B (torus k).anyDetour)
        (List.finRange m)).esc
      (fun x => x.2.isInj = true) sel) :
    (torusLanes k m B).DeadlockFreeWith sel ∧ (torusLanes k m B).LivelockFreeWith sel ∧
      (torusLanes k m B).StarvationFreeUnderLoad sel (fun x => x.2.isInj = true) :=
  GraphData.lanes_detour_sourceSel (fun _ => torus k) B (fun _ => (torus k).anyDetour) _ hsel

/-- **`m` lanes deliver `m` times the packets of one**: any run of the detour network on the
torus, run in each of the `m` lanes, is one run of `torusLanes k m B` delivering `m` times the
packets. -/
theorem torusLanes_parallel (k m B : ℕ) {g g' : Config (GChan (TV k)) (THdr k)}
    {as : List (Act (GChan (TV k)) (THdr k))}
    (h : ((torus k).detourNet B (torus k).anyDetour).lts.Path g as g') :
    ∃ bs, (torusLanes k m B).lts.Path (combine fun _ => g) bs (combine fun _ => g') ∧
      bs.countP (fun a => a.isEject) = m * as.countP (fun a => a.isEject) :=
  copies_path h

/-- The reachable configurations of the torus with `m` lanes are the `m`-tuples of reachable
configurations of one lane. -/
theorem torusLanes_reachable (k m B : ℕ) {f : Config (Fin m × GChan (TV k)) (THdr k)} :
    (torusLanes k m B).lts.Reachable empty f ↔
      ∀ i, ((torus k).detourNet B (torus k).anyDetour).lts.Reachable empty (lane f i) := by
  rw [lanes_reachable_iff]
  simp [List.mem_finRange]

/-- **The torus with `m` shared lanes**: escape hops in the packet's lane, adaptive hops on the
adaptive channels of every lane, at most `B` returns. -/
abbrev torusShared (k m B : ℕ) := GraphData.sharedNet (List.finRange m) (fun _ => torus k) B

/-- **The torus with `m` shared lanes is correct** for every size, number of lanes and budget. -/
theorem torusShared_correct (k m B : ℕ) :
    (torusShared k m B).Correct ∧ (torusShared k m B).StarvationFree ∧
      ∀ sel, (torusShared k m B).ValidSel sel →
        (torusShared k m B).StarvationFreeUnderLoad sel (fun _ => False) :=
  GraphData.shared_correct _ _ B

/-- **The torus with `m` connections per link, widened**: the detour network with Valiant's
intermediates and one escape channel, `2m - 1` adaptive channels per link and `m` injection
channels per node, every copy usable by every packet. -/
abbrev torusWide (k m B : ℕ) (hm : 0 < m) :=
  ((torus k).detourNet B (torus k).anyDetour).widen
    (slots (GraphData.sharedSlots m) (GraphData.sharedSlots_pos hm))

/-- **The widened torus is correct** for every size, number of connections and budget. -/
theorem torusWide_correct (k m B : ℕ) (hm : 0 < m) :
    (torusWide k m B hm).Correct ∧ (torusWide k m B hm).StarvationFree ∧
      ∀ sel, (torusWide k m B hm).ValidSel sel →
        (torusWide k m B hm).StarvationFreeUnderLoad sel (fun _ => False) :=
  (torus k).wide_detour_correct B _ _ _

#assert_standard_axioms torusShared_correct torusWide_correct
#assert_standard_axioms torusLanes_correct torusLanes_sourceSel torusLanes_parallel
#assert_standard_axioms torusLanes_reachable

end AsyncLean.Examples
