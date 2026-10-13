/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.MeshPatterns
import AsyncLean.Flow.MeshWorst
import AsyncLean.Flow.Symmetric
import AsyncLean.Flow.GraphPatterns

/-!
# Fluid optima with scaled lane capacities

The fluid model (`AsyncLean.Fluid`) gives every directed link the capacity `2`: two lanes
(virtual channels) of capacity `1` each.  A lane of the packet model passes at most one packet per
cycle, so the fluid optimum bounds every packet routing.  If every lane can carry at most `J`
packets per cycle in a saturated regime, the natural packet-level ceiling is the fluid optimum
with link capacity `2 J`, which is `J` times the fluid optimum: the maximum concurrent flow is
homogeneous in the capacities.

* `Packet.routable_scale`, `Packet.routable_unscale` : a flow scales with the capacities.
* `Packet.isGreatest_scale` : **the optimum scales**: if `θ*` is the fluid optimum of `N`, then
  `J * θ*` is the optimum of `N` with every capacity multiplied by `J > 0`.
* `Packet.mesh8_half`, `Packet.torus8_half` : the optima of the `8 × 8` mesh and torus under the
  standard patterns with lanes of capacity `1/2` (the exclusion limit of a ring of one-packet
  lanes, `Packet.Ring.half_bound`): exactly half of the fluid optima.

**What is a theorem and what is an estimate.**  The scaling is a theorem about the fluid model.
`Packet.Ring.half_bound` proves that lanes forming a ring (each lane fed by one lane and feeding
one lane) carry at most `1/2` per cycle on average under the random-shuffle update.  A lane of a
network is in general not in such a ring: a lane next to an ejection port, a lane with several
permitted successors, or a lane fed by several lanes can carry up to `1` per cycle (in the
simulations busy lanes carry up to 0.6 to 0.7 with one-packet lanes).  So `J * θ*` with
`J = 1/2` is an *estimate* of the packet throughput of one-packet lanes, not a bound; the only
proved packet bound is the fluid optimum itself (`J = 1`).
-/

namespace AsyncLean

namespace Packet

open Fluid

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The network `N` with every capacity multiplied by `c ≥ 0`. -/
def scaleNet (c : ℚ) (hc : 0 ≤ c) (N : Net V) : Net V where
  cap u v := c * N.cap u v
  cap_nonneg u v := mul_nonneg hc (N.cap_nonneg u v)

omit [DecidableEq V] in
/-- A flow at `θ` in `N` is a flow at `c * θ` in `N` scaled by `c`. -/
theorem routable_scale {N : Net V} {dem : V → V → ℚ} {θ c : ℚ} (hc : 0 ≤ c)
    (h : Routable N dem θ) : Routable (scaleNet c hc N) dem (c * θ) := by
  obtain ⟨F⟩ := h
  exact ⟨{ f := fun d u v => c * F.f d u v
           nonneg := fun d u v => mul_nonneg hc (F.nonneg d u v)
           conserve := fun d v hv => by
             rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, F.conserve d v hv]; ring
           capacity := fun u v => by
             rw [← Finset.mul_sum]
             exact mul_le_mul_of_nonneg_left (F.capacity u v) hc }⟩

omit [DecidableEq V] in
/-- A flow at `θ` in `N` scaled by `c > 0` is a flow at `θ / c` in `N`. -/
theorem routable_unscale {N : Net V} {dem : V → V → ℚ} {θ c : ℚ} (hc : 0 < c)
    (h : Routable (scaleNet c hc.le N) dem θ) : Routable N dem (θ / c) := by
  obtain ⟨F⟩ := h
  exact ⟨{ f := fun d u v => F.f d u v * c⁻¹
           nonneg := fun d u v => mul_nonneg (F.nonneg d u v) (inv_nonneg.2 hc.le)
           conserve := fun d v hv => by
             rw [← Finset.sum_mul, ← Finset.sum_mul, ← sub_mul, F.conserve d v hv, div_eq_mul_inv]
             ring
           capacity := fun u v => by
             rw [← Finset.sum_mul]
             have h1 : ∑ d, F.f d u v ≤ c * N.cap u v := F.capacity u v
             calc (∑ d, F.f d u v) * c⁻¹ ≤ (c * N.cap u v) * c⁻¹ :=
                   mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hc.le)
               _ = N.cap u v := by
                   rw [mul_comm c, mul_assoc, mul_inv_cancel₀ hc.ne', mul_one] }⟩

omit [DecidableEq V] in
/-- **The fluid optimum scales with the capacities.** -/
theorem isGreatest_scale {N : Net V} {dem : V → V → ℚ} {θs c : ℚ} (hc : 0 < c)
    (h : IsGreatest {θ | Routable N dem θ} θs) :
    IsGreatest {θ | Routable (scaleNet c hc.le N) dem θ} (c * θs) := by
  refine ⟨routable_scale hc.le h.1, fun θ hθ => ?_⟩
  have := h.2 (routable_unscale hc hθ)
  have h2 : θ / c ≤ θs := this
  rw [div_le_iff₀ hc] at h2
  linarith

/-- Lanes of capacity `1/2`: link capacity `1` instead of `2`. -/
abbrev half (N : Net V) : Net V := scaleNet (1 / 2) (by norm_num) N

omit [DecidableEq V] in
theorem half_opt {N : Net V} {dem : V → V → ℚ} {θs : ℚ}
    (h : IsGreatest {θ | Routable N dem θ} θs) :
    IsGreatest {θ | Routable (half N) dem θ} (θs / 2) := by
  have := isGreatest_scale (c := 1 / 2) (by norm_num) h
  rwa [show (1 / 2 : ℚ) * θs = θs / 2 by ring] at this

/-- **The `8 × 8` mesh with lanes of capacity `1/2`**: the optima are half the fluid optima:
uniform `63/128`, transpose `5/11`, shuffle `1/2`, bit reversal `10/21`, hotspot `20/67`,
bit complement `1/4`. -/
theorem mesh8_half :
    IsGreatest {θ | Routable (half (meshNet 8)) (uniform 8) θ} (63 / 128) ∧
    IsGreatest {θ | Routable (half (meshNet 8)) transpose8 θ} (5 / 11) ∧
    IsGreatest {θ | Routable (half (meshNet 8)) shuffle8 θ} (1 / 2) ∧
    IsGreatest {θ | Routable (half (meshNet 8)) bitrev8 θ} (10 / 21) ∧
    IsGreatest {θ | Routable (half (meshNet 8)) hotspot8 θ} (20 / 67) ∧
    IsGreatest {θ | Routable (half (meshNet 8)) (bitcomp 8) θ} (1 / 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := half_opt mesh_opt_eight; norm_num at this ⊢; exact this
  · have := half_opt transpose8_opt; norm_num at this ⊢; exact this
  · have := half_opt shuffle8_opt; norm_num at this ⊢; exact this
  · have := half_opt bitrev8_opt; norm_num at this ⊢; exact this
  · have := half_opt hotspot8_opt; norm_num at this ⊢; exact this
  · have := half_opt (bitcomp_opt 8 (by norm_num) ⟨4, rfl⟩); norm_num at this ⊢; exact this

/-- **The `8 × 8` torus with lanes of capacity `1/2`**: uniform `63/64`, transpose `10/11`,
shuffle `4/5`, bit reversal `20/21`, bit complement `1/2`, tornado `8/15`. -/
theorem torus8_half :
    IsGreatest {θ | Routable (half (torusNet 8)) (uniform 8) θ} (63 / 64) ∧
    IsGreatest {θ | Routable (half (torusNet 8)) transpose8 θ} (10 / 11) ∧
    IsGreatest {θ | Routable (half (torusNet 8)) shuffle8 θ} (4 / 5) ∧
    IsGreatest {θ | Routable (half (torusNet 8)) bitrev8 θ} (20 / 21) ∧
    IsGreatest {θ | Routable (half (torusNet 8)) (bitcomp 8) θ} (1 / 2) ∧
    IsGreatest {θ | Routable (half (torusNet 8)) tornado8 θ} (8 / 15) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := half_opt torus_uniform_opt_eight.1; norm_num at this ⊢; exact this
  · have := half_opt torusTranspose_opt; norm_num at this ⊢; exact this
  · have := half_opt torusShuffle_opt; norm_num at this ⊢; exact this
  · have := half_opt torusBitrev_opt; norm_num at this ⊢; exact this
  · have := half_opt torusBitcomp_opt; norm_num at this ⊢; exact this
  · have := half_opt torusTornado_opt; norm_num at this ⊢; exact this

end Packet

end AsyncLean
