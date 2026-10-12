/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.GraphRouting
import AsyncLean.Routing.Planes
import AsyncLean.Routing.SharedPlanes
import AsyncLean.Routing.Replicate
import AsyncLean.Flow.Scaling
import AsyncLean.AxiomAudit

/-!
# Example: the torus with `m` connections per link, as `m` planes

`torusPlanes k m B` is the `(k + 1) × (k + 1)` torus `torus k` of
`AsyncLean.Examples.GraphRouting` with `m` connections per link, used as `m` planes
(`Network.planes`): each plane runs the detour network with Valiant's intermediates and at most `B`
returns (`GraphData.detourNet`, the network behind the simulated `bandit2m7f5k`), on its own two
virtual channels; a packet picks its plane at the source and stays on it.  For **every size `k`,
every number of planes `m` and every budget `B`**:

* `torusPlanes_correct` : deadlock and livelock free under every valid selection (which may
  compare planes), starvation free under strong fairness, and every packet delivered under
  saturation along every channel-fair run;
* `torusPlanes_sourceSel` : the same under every selection that never refuses a free escape hop
  outside the injection channels and may throttle the sources, for every packet outside them;
* `torusPlanes_parallel` : any run of one plane is achieved by all `m` planes at once, and
  delivers `m` times the packets;
* `torusPlanes_reachable` : the reachable configurations are exactly the `m`-tuples of reachable
  configurations of one plane.

`torusShared k m B` shares the planes (`GraphData.sharedNet`): escapes per plane, adaptive hops on
the adaptive channels of every plane; `torusShared_correct` proves it deadlock, livelock and
starvation free and delivering under saturation for every `k`, `m` and `B`.

`torusReplicated k m B` replicates the detour network instead (`Network.replicate`): one escape
channel, `2m - 1` adaptive channels per link and `m` injection channels per node, every copy usable
by every packet — the best performing use of the connections in simulation;
`torusReplicated_correct`.

With `Fluid.torus_copies_worst` (the best worst case of `m` connections on the torus of even
side `k ≥ 4` is `m · 8 / k`, reached by Valiant in every plane) this is the scheme that scales
linearly with the connections, proved safe for every `m`.
-/

namespace AsyncLean.Examples

open Network

/-- The vertices of the torus `torus k`. -/
abbrev TV (k : ℕ) := Fin (k + 1) × Fin (k + 1)

/-- The packet headers of the detour network on `torus k`. -/
abbrev THdr (k : ℕ) := TV k × Option (TV k) × ℕ

/-- **The torus with `m` planes**: `m` copies of the detour network with Valiant's intermediates
and at most `B` returns, side by side. -/
abbrev torusPlanes (k m B : ℕ) :=
  planes (List.finRange m) fun _ : Fin m => (torus k).detourNet B (torus k).anyDetour

/-- **The torus with `m` planes is correct** for every size, number of planes and budget. -/
theorem torusPlanes_correct (k m B : ℕ) :
    (torusPlanes k m B).Correct ∧ (torusPlanes k m B).StarvationFree ∧
      ∀ sel, (torusPlanes k m B).ValidSel sel →
        (torusPlanes k m B).StarvationFreeUnderLoad sel (fun _ => False) :=
  GraphData.planes_detour_correct (fun _ => torus k) B (fun _ => (torus k).anyDetour) _

/-- **The torus with `m` planes and throttled sources is correct**: under every selection that
never refuses a free escape hop outside the injection channels and releases a source once the
rest of the network is empty. -/
theorem torusPlanes_sourceSel (k m B : ℕ)
    {sel : Selection (Fin m × GChan (TV k)) (THdr k)}
    (hsel : (torusPlanes k m B).SourceSel
      (SafeCert.planes (fun _ => (torus k).detourCert B (torus k).anyDetour)
        (List.finRange m)).esc
      (fun x => x.2.isInj = true) sel) :
    (torusPlanes k m B).DeadlockFreeWith sel ∧ (torusPlanes k m B).LivelockFreeWith sel ∧
      (torusPlanes k m B).StarvationFreeUnderLoad sel (fun x => x.2.isInj = true) :=
  GraphData.planes_detour_sourceSel (fun _ => torus k) B (fun _ => (torus k).anyDetour) _ hsel

/-- **`m` planes deliver `m` times the packets of one**: any run of the detour network on the
torus, run in each of the `m` planes, is one run of `torusPlanes k m B` delivering `m` times the
packets. -/
theorem torusPlanes_parallel (k m B : ℕ) {g g' : Config (GChan (TV k)) (THdr k)}
    {as : List (Act (GChan (TV k)) (THdr k))}
    (h : ((torus k).detourNet B (torus k).anyDetour).lts.Path g as g') :
    ∃ bs, (torusPlanes k m B).lts.Path (combine fun _ => g) bs (combine fun _ => g') ∧
      bs.countP (fun a => a.isEject) = m * as.countP (fun a => a.isEject) :=
  copies_path h

/-- The reachable configurations of the torus with `m` planes are the `m`-tuples of reachable
configurations of one plane. -/
theorem torusPlanes_reachable (k m B : ℕ) {f : Config (Fin m × GChan (TV k)) (THdr k)} :
    (torusPlanes k m B).lts.Reachable empty f ↔
      ∀ i, ((torus k).detourNet B (torus k).anyDetour).lts.Reachable empty (plane f i) := by
  rw [planes_reachable_iff]
  simp [List.mem_finRange]

/-- **The torus with `m` shared planes**: escape hops in the packet's plane, adaptive hops on the
adaptive channels of every plane, at most `B` returns. -/
abbrev torusShared (k m B : ℕ) := GraphData.sharedNet (List.finRange m) (fun _ => torus k) B

/-- **The torus with `m` shared planes is correct** for every size, number of planes and budget. -/
theorem torusShared_correct (k m B : ℕ) :
    (torusShared k m B).Correct ∧ (torusShared k m B).StarvationFree ∧
      ∀ sel, (torusShared k m B).ValidSel sel →
        (torusShared k m B).StarvationFreeUnderLoad sel (fun _ => False) :=
  GraphData.shared_correct _ _ B

/-- **The torus with `m` connections per link, replicated**: the detour network with Valiant's
intermediates and one escape channel, `2m - 1` adaptive channels per link and `m` injection
channels per node, every copy usable by every packet. -/
abbrev torusReplicated (k m B : ℕ) (hm : 0 < m) :=
  ((torus k).detourNet B (torus k).anyDetour).replicate
    (slots (GraphData.sharedSlots m) (GraphData.sharedSlots_pos hm))

/-- **The replicated torus is correct** for every size, number of connections and budget. -/
theorem torusReplicated_correct (k m B : ℕ) (hm : 0 < m) :
    (torusReplicated k m B hm).Correct ∧ (torusReplicated k m B hm).StarvationFree ∧
      ∀ sel, (torusReplicated k m B hm).ValidSel sel →
        (torusReplicated k m B hm).StarvationFreeUnderLoad sel (fun _ => False) :=
  (torus k).replicated_detour_correct B _ _ _

#assert_standard_axioms torusShared_correct torusReplicated_correct
#assert_standard_axioms torusPlanes_correct torusPlanes_sourceSel torusPlanes_parallel
#assert_standard_axioms torusPlanes_reachable

end AsyncLean.Examples
