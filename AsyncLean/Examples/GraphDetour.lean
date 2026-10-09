/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.GraphRouting
import AsyncLean.Routing.GraphDetour
import AsyncLean.AxiomAudit

/-!
# Example: the torus with detours through an intermediate vertex

Instances of `AsyncLean.Routing.GraphDetour` on the `(k + 1) × (k + 1)` torus `torus k` of
`AsyncLean.Examples.GraphRouting`: a packet header `(d, w, b)` carries the destination, an
optional intermediate vertex `w` chosen at the source and a return budget.  Minimal adaptive
routing with the wraparound distance towards `w` (while it is set) and then towards `d` on
virtual channel 1; tree routing towards `d` along a comb spanning tree on virtual channel 0,
which drops the intermediate; at most `B` returns from virtual channel 0 to virtual channel 1.
For **every size `k`, every budget `B` and every choice of intermediates `W`** (Valiant's
`anyDetour`, a fixed "long way round", or none at all):

* `torus_detour_correct k B W` : deadlock free and livelock free under every valid selection
  function, and starvation free under strongly fair scheduling;
* `torus_detour_correct_of_sourceSel k B W` : deadlock, livelock and starvation free under every
  selection that never refuses a free escape hop outside the injection channels and may
  throttle the sources;
* `torus_detour_underLoad k B W` : under every valid selection, every packet is delivered along
  every channel-fair run, with injections going on for ever;
* `torus_detour_hops_le k B W` : a packet injected at `s` for `d` with intermediate `w` takes at
  most `dist s w + (B + 1) * rankBound` hops;
* `torus_valiant_correct k B` : the instance `W = anyDetour` (every intermediate other than the
  source, or none), with delivery under saturation.
-/

namespace AsyncLean.Examples

open Network

/-- **The torus of every size with detours and at most `B` returns is correct**: deadlock free
and livelock free under every valid selection function, and starvation free under strongly fair
scheduling, for every choice of intermediates. -/
theorem torus_detour_correct (k B : ℕ)
    (W : Fin (k + 1) × Fin (k + 1) → Fin (k + 1) × Fin (k + 1) →
      List (Option (Fin (k + 1) × Fin (k + 1)))) :
    ((torus k).detourNet B W).Correct ∧ ((torus k).detourNet B W).StarvationFree :=
  (torus k).detour_correct B W

/-- **The torus of every size with detours and at most `B` returns is correct under throttled
sources**. -/
theorem torus_detour_correct_of_sourceSel (k B : ℕ)
    (W : Fin (k + 1) × Fin (k + 1) → Fin (k + 1) × Fin (k + 1) →
      List (Option (Fin (k + 1) × Fin (k + 1))))
    {sel : Selection (GChan (Fin (k + 1) × Fin (k + 1)))
      ((Fin (k + 1) × Fin (k + 1)) × Option (Fin (k + 1) × Fin (k + 1)) × ℕ)}
    (hsel : ((torus k).detourNet B W).SourceSel (torus k).detEscape (fun c => c.isInj) sel) :
    ((torus k).detourNet B W).DeadlockFreeWith sel ∧
      ((torus k).detourNet B W).LivelockFreeWith sel ∧
      ((torus k).detourNet B W).StarvationFreeWith sel :=
  (torus k).detour_correct_of_sourceSel hsel

/-- **Delivery under saturation on the torus with detours and at most `B` returns**: under every
valid selection, every packet is delivered along every channel-fair run. -/
theorem torus_detour_underLoad (k B : ℕ)
    (W : Fin (k + 1) × Fin (k + 1) → Fin (k + 1) × Fin (k + 1) →
      List (Option (Fin (k + 1) × Fin (k + 1))))
    {sel : Selection (GChan (Fin (k + 1) × Fin (k + 1)))
      ((Fin (k + 1) × Fin (k + 1)) × Option (Fin (k + 1) × Fin (k + 1)) × ℕ)}
    (hsel : ((torus k).detourNet B W).ValidSel sel) :
    ((torus k).detourNet B W).StarvationFreeUnderLoad sel (fun _ => False) :=
  (torus k).detour_underLoad hsel

/-- **Hop bound on the torus with detours and at most `B` returns**: at most `dist s w` hops
towards the intermediate, then less than `(B + 1) * rankBound`. -/
theorem torus_detour_hops_le (k B : ℕ)
    (W : Fin (k + 1) × Fin (k + 1) → Fin (k + 1) × Fin (k + 1) →
      List (Option (Fin (k + 1) × Fin (k + 1))))
    {s d w : Fin (k + 1) × Fin (k + 1)} {ls : List Unit}
    {q' : GChan (Fin (k + 1) × Fin (k + 1)) ×
      ((Fin (k + 1) × Fin (k + 1)) × Option (Fin (k + 1) × Fin (k + 1)) × ℕ)}
    (h : ((torus k).detourNet B W).packetLTS.Path (.inj s, (d, some w, B)) ls q') :
    ls.length ≤ (torus k).dist s w + (B + 1) * (torus k).rankBound :=
  (torus k).detour_hops_le_some h

/-- **Valiant's routing on the torus of every size is correct**: with every intermediate other
than the source (or none) allowed, deadlock and livelock free under every valid selection,
starvation free under strongly fair scheduling, and every packet is delivered under saturation
along every channel-fair run. -/
theorem torus_valiant_correct (k B : ℕ) :
    ((torus k).detourNet B (torus k).anyDetour).Correct ∧
      ((torus k).detourNet B (torus k).anyDetour).StarvationFree ∧
      ∀ sel, ((torus k).detourNet B (torus k).anyDetour).ValidSel sel →
        ((torus k).detourNet B (torus k).anyDetour).StarvationFreeUnderLoad sel (fun _ => False) :=
  ⟨((torus k).detour_correct B _).1, ((torus k).detour_correct B _).2,
    fun _ hsel => (torus k).detour_underLoad hsel⟩

#assert_standard_axioms torus_detour_correct torus_detour_correct_of_sourceSel
#assert_standard_axioms torus_detour_underLoad torus_detour_hops_le torus_valiant_correct

end AsyncLean.Examples
