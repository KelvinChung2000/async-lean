/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.GraphRouting
import AsyncLean.Routing.GraphBudget
import AsyncLean.AxiomAudit

/-!
# Example: the torus with a bounded number of returns from the escape layer

Instances of `AsyncLean.Routing.GraphBudget` on the `(k + 1) × (k + 1)` torus `torus k` of
`AsyncLean.Examples.GraphRouting` (minimal adaptive routing with the wraparound distance on
virtual channel 1, tree routing along a comb spanning tree on virtual channel 0), where a packet
may return from virtual channel 0 to virtual channel 1 at most `B` times.  For **every size `k`
and every budget `B`**:

* `torus_budget_correct k B` : deadlock free and livelock free under every valid selection
  function, and starvation free under strongly fair scheduling;
* `torus_budget_correct_of_sourceSel k B` : deadlock, livelock and starvation free under every
  selection that never refuses a free escape hop outside the injection channels and may
  throttle the sources;
* `torus_budget_underLoad k B` : under every valid selection, every packet is delivered along
  every channel-fair run, with injections going on for ever;
* `torus_budget_hops_le k B` : a packet injected at `s` for `d` takes at most
  `B * rankBound + (2 * height + 1) * (dist s d + 1)` hops.
-/

namespace AsyncLean.Examples

open Network

/-- **The torus of every size with at most `B` returns is correct**: deadlock free and livelock
free under every valid selection function, and starvation free under strongly fair scheduling. -/
theorem torus_budget_correct (k B : ℕ) :
    ((torus k).budgetNet B).Correct ∧ ((torus k).budgetNet B).StarvationFree :=
  (torus k).budget_correct B

/-- **The torus of every size with at most `B` returns is correct under throttled sources**. -/
theorem torus_budget_correct_of_sourceSel (k B : ℕ)
    {sel : Selection (GChan (Fin (k + 1) × Fin (k + 1))) ((Fin (k + 1) × Fin (k + 1)) × ℕ)}
    (hsel : ((torus k).budgetNet B).SourceSel (torus k).budgetEscape (fun c => c.isInj) sel) :
    ((torus k).budgetNet B).DeadlockFreeWith sel ∧ ((torus k).budgetNet B).LivelockFreeWith sel ∧
      ((torus k).budgetNet B).StarvationFreeWith sel :=
  (torus k).budget_correct_of_sourceSel hsel

/-- **Delivery under saturation on the torus with at most `B` returns**: under every valid
selection, every packet is delivered along every channel-fair run. -/
theorem torus_budget_underLoad (k B : ℕ)
    {sel : Selection (GChan (Fin (k + 1) × Fin (k + 1))) ((Fin (k + 1) × Fin (k + 1)) × ℕ)}
    (hsel : ((torus k).budgetNet B).ValidSel sel) :
    ((torus k).budgetNet B).StarvationFreeUnderLoad sel (fun _ => False) :=
  (torus k).budget_underLoad hsel

/-- **Hop bound on the torus with at most `B` returns.** -/
theorem torus_budget_hops_le (k B : ℕ) {s d : Fin (k + 1) × Fin (k + 1)} {ls : List Unit}
    {q' : GChan (Fin (k + 1) × Fin (k + 1)) × ((Fin (k + 1) × Fin (k + 1)) × ℕ)}
    (h : ((torus k).budgetNet B).packetLTS.Path (.inj s, (d, B)) ls q') :
    ls.length ≤ B * (torus k).rankBound + (2 * (torus k).height + 1) * ((torus k).dist s d + 1) :=
  (torus k).budget_hops_le h

#assert_standard_axioms torus_budget_correct torus_budget_correct_of_sourceSel
#assert_standard_axioms torus_budget_underLoad torus_budget_hops_le

end AsyncLean.Examples
