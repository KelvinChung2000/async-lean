/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure
import AsyncLean.Flow.GraphPatterns

/-!
# Adaptivity is necessary: shortest paths alone lose throughput

Backpressure reaches the fluid optimum (`Fluid.Run.backpressure_optimal`) because it may move
traffic along any link, detours included.  This file proves that this freedom is needed: a
scheduler that moves every packet only along shortest paths — whatever else it does, however it
uses the backlogs — is bounded by the fluid optimum *over minimal routings*, which can be far
below the optimum.

* `GraphCert.Model.run_minimal_ceiling` : on a network certified by a port graph
  (`GraphCert.Model`), a stable queueing run whose transmissions all bring their traffic
  strictly closer to its destination is bounded by every dual certificate on the minimal links
  (the ones the library checks in the kernel).  The bridge is `Fluid.PotentialFeasibleOn`: a
  stable run respects every potential bound on the links it uses
  (`Fluid.Run.potentialFeasibleOn`), as a flow does.
* `torusTornado_adaptivity` : **tornado traffic on the `8 × 8` torus.**  Backpressure is stable
  at every load below `16/15`; no scheduler moving traffic only along shortest paths keeps a
  bounded backlog above `2/3`.  Between `2/3` and `16/15` only adaptive, non-minimal scheduling
  is stable.
-/

namespace AsyncLean

namespace Fluid

open Finset GraphCert GraphPatternData

namespace GraphCert

namespace Model

variable {V : Type*} [Fintype V] [DecidableEq V] {G : PortGraph} {C : ℕ} {N : Net V}
  {dist : V → V → ℚ}

omit [DecidableEq V] in
/-- **Potential bounds transfer along a model**: respecting the potential bounds of `N` on the
links `S` is respecting those of the port graph's network on the image of `S`. -/
theorem potentialFeasibleOn_transfer (M : Model G C N dist) {dem : V → V → ℚ}
    {demN : ℕ → ℕ → ℕ} {R : ℕ} (hdem : ∀ s d, dem s d = (demN (M.e s) (M.e d) : ℚ) / R)
    {S : Fin G.n → Fin G.n → Fin G.n → Prop} {θ : ℚ}
    (h : PotentialFeasibleOn N (fun d u v => S (M.e d) (M.e u) (M.e v)) dem θ) :
    PotentialFeasibleOn (G.net C) S (fun a b => (demN a b : ℚ) / R) θ := by
  intro len φ hlen hφd hφ hφ0
  have key := h (fun u v => len (M.e u) (M.e v)) (fun d v => φ (M.e d) (M.e v))
    (fun u v => hlen _ _) (fun d => hφd _)
    (fun d u v hS hc => hφ _ _ _ hS (by rw [← M.cap_eq]; exact hc)) (fun d v => hφ0 _ _)
  simp only [hdem, M.cap_eq] at key
  have e1 : ∑ s, ∑ d, (demN (M.e s) (M.e d) : ℚ) / R * φ (M.e d) (M.e s) =
      ∑ a : Fin G.n, ∑ b : Fin G.n, (demN a b : ℚ) / R * φ b a := by
    rw [M.e.sum_comp (fun a : Fin G.n => ∑ d, (demN a (M.e d) : ℚ) / R * φ (M.e d) a)]
    exact sum_congr rfl fun a _ =>
      M.e.sum_comp (fun b : Fin G.n => (demN a b : ℚ) / R * φ b a)
  have e2 : ∑ u, ∑ v, (G.net C).cap (M.e u) (M.e v) * len (M.e u) (M.e v) =
      ∑ a : Fin G.n, ∑ b : Fin G.n, (G.net C).cap a b * len a b := by
    rw [M.e.sum_comp (fun a : Fin G.n => ∑ v, (G.net C).cap a (M.e v) * len a (M.e v))]
    exact sum_congr rfl fun a _ =>
      M.e.sum_comp (fun b : Fin G.n => (G.net C).cap a b * len a b)
  rw [e1, e2] at key
  exact key

/-- **Shortest paths only: the minimal ceiling for runs.**  On a network certified by a port
graph, a queueing run with arrivals `ρ * dem` and a bounded backlog, whose transmissions all
bring their traffic strictly closer to its destination, has `ρ ≤ p / q` for every dual
certificate on the minimal links. -/
theorem run_minimal_ceiling (M : Model G C N dist) (dem : V → V → ℚ) (demN : ℕ → ℕ → ℕ)
    (R : ℕ) (hdem : ∀ s d, dem s d = (demN (M.e s) (M.e d) : ℚ) / R) (phi lenT : ℕ → ℕ → ℕ)
    (p q : ℕ) (hR : 0 < R) (hq : 0 < q) (hd : G.dualCheck phi lenT true = true)
    (hb : G.boundCheck C demN phi lenT R p q = true) (r : Run N) {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hbd : r.BoundedBacklog)
    (hmin : ∀ t d u v, 0 < r.x t d u v → dist v d < dist u d) :
    ρ ≤ (p : ℚ) / q := by
  refine PortGraph.upper_of_check' C M.wf M.near (fun a b => (demN a b : ℚ) / R) demN R
    (fun _ _ => rfl) phi lenT true p q hR hq hd hb (M.potentialFeasibleOn_transfer hdem ?_)
  refine r.potentialFeasibleOn harr hbd fun t d u v h => Or.inr ?_
  have := hmin t d u v h
  rwa [M.dist_eq, M.dist_eq] at this

end Model

end GraphCert

/-- Tornado traffic is nonnegative. -/
theorem tornado8_nonneg (s d : Fin 8 × Fin 8) : 0 ≤ tornado8 s d := by
  rw [torusTornado_dem]; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Adaptivity is necessary: tornado traffic on the `8 × 8` torus.**  Backpressure keeps a
bounded backlog and delivers everything at every load `0 ≤ ρ < 16/15` (the fluid optimum,
`torusTornado_opt`); no scheduler whose transmissions all follow shortest paths keeps a bounded
backlog at a load above `2/3` (the optimum over minimal routings, `torusTornado_minimal_opt`). -/
theorem torusTornado_adaptivity (r : Run (torusNet 8)) {ρ : ℚ} :
    (r.Backpressure → 0 ≤ ρ → ρ < 16 / 15 →
        (∀ t v d, v ≠ d → r.a t v d ≤ ρ * tornado8 v d) → r.Stable) ∧
      ((∀ t v d, v ≠ d → r.a t v d = ρ * tornado8 v d) → r.BoundedBacklog →
        (∀ t d u v, 0 < r.x t d u v → torusDist v d < torusDist u d) → ρ ≤ 2 / 3) := by
  refine ⟨fun hr hρ hρθ harr => ?_, fun harr hbd hmin => ?_⟩
  · obtain ⟨hunn, hunc⟩ := uniform_props (k := 8) (by norm_num)
    exact r.backpressure_optimal hr torusTornado_opt.1 torus_uniform_opt_eight.1.1
      tornado8_nonneg hunn (c := 1 / (((8 : ℕ) : ℚ) ^ 2 - 1)) (by norm_num) hunc (by norm_num)
      hρ hρθ harr
  · have h := torusModel.run_minimal_ceiling tornado8 _ 1 torusTornado_dem torusTornadoMinP
      torusTornadoMinL 2 3 one_pos (by norm_num) torusTornadoMin_dual torusTornadoMin_bound r
      harr hbd hmin
    norm_num at h ⊢
    exact h

/-- Between `2/3` and `16/15` only non-minimal scheduling is stable. -/
theorem torusTornado_gap : (2 / 3 : ℚ) < 16 / 15 := by norm_num

end Fluid

end AsyncLean
