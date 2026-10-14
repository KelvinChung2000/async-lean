/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure.Stability

/-!
# Backpressure, part 3: finite buffers suffice

Started empty, a backpressure run whose load stays `ε` below a routable traffic never holds more
than `driftConst / (2 ε) + ε` in any per-destination queue (`Run.backpressure_fitsIn`): buffers of
that size are never exceeded (`Run.FitsIn`).
-/

namespace AsyncLean

namespace Fluid

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Run

variable {N : Net V} (r : Run N)

/-- The run **fits in buffers of size `b`**: no per-destination queue ever holds more than
`b`.  A network with buffers of size `b` per destination at every vertex, which blocks or drops
on overflow, then behaves exactly like the run: the overflow never happens. -/
def FitsIn (b : ℚ) : Prop := ∀ t v d, r.Q t v d ≤ b

omit [DecidableEq V] in
/-- A queue is at most `x + ε` when the Lyapunov function is at most `x² + 2 x ε`. -/
theorem queue_le_of_lyapunov {Q : V → V → ℚ} {x ε : ℚ} (hx : 0 ≤ x)
    (hε : 0 < ε) (hE : lyapunov Q ≤ x ^ 2 + 2 * x * ε) (v d : V) : Q v d ≤ x + ε := by
  have h1 : Q v d ^ 2 ≤ lyapunov Q :=
    (single_le_sum (f := fun v => Q v d ^ 2) (fun v _ => sq_nonneg _) (mem_univ v)).trans
      (single_le_sum (f := fun d => ∑ v, Q v d ^ 2) (fun d _ => sum_nonneg fun v _ => sq_nonneg _)
        (mem_univ d))
  nlinarith

/-- **Finite buffers suffice.**  Started empty, a backpressure run whose arrivals stay `ε > 0`
below a traffic `dem` routable at throughput `1` never holds more than
`driftConst N dem / (2 ε) + ε` in any per-destination queue: buffers of that size are never
exceeded, and the run delivers everything that arrives except what those buffers hold.  The
buffer grows like `1 / ε` as the load approaches the fluid optimum. -/
theorem backpressure_fitsIn (hr : r.Backpressure) {dem : V → V → ℚ} (F : Flow N dem 1)
    (hdem : ∀ v d, 0 ≤ dem v d) {ε : ℚ} (hε : 0 < ε)
    (harr : ∀ t v d, v ≠ d → r.a t v d + ε ≤ dem v d) (h0 : ∀ v d, r.Q 0 v d = 0) :
    r.FitsIn (driftConst N dem / (2 * ε) + ε) ∧
      ∀ t, ∑ s ∈ range t, r.arrived s -
          (Fintype.card V : ℚ) ^ 2 * (driftConst N dem / (2 * ε) + ε) ≤
        ∑ s ∈ range t, r.delivered s := by
  set B := driftConst N dem
  have hB := driftConst_nonneg N dem
  set x := B / (2 * ε) with hxdef
  have hx : 0 ≤ x := div_nonneg hB (by positivity)
  have hE0 : lyapunov (r.Q 0) = 0 := by simp [lyapunov, h0]
  have hfit : r.FitsIn (x + ε) := fun t v d => by
    have h := r.lyapunov_bounded hr F hdem hε harr t
    rw [hE0, max_eq_right (by positivity)] at h
    have e : B = 2 * x * ε := by
      rw [hxdef, show (2 : ℚ) * (B / (2 * ε)) * ε = B / (2 * ε) * (2 * ε) by ring,
        div_mul_cancel₀ B (by positivity)]
    have e' : (B / (2 * ε)) ^ 2 + B = x ^ 2 + 2 * x * ε := by rw [← e]
    exact queue_le_of_lyapunov hx hε (h.trans e'.le) v d
  refine ⟨hfit, fun t => ?_⟩
  have hb : backlog (r.Q t) ≤ (Fintype.card V : ℚ) ^ 2 * (x + ε) := by
    calc backlog (r.Q t) ≤ ∑ _d : V, ∑ _v : V, (x + ε) :=
          sum_le_sum fun d _ => sum_le_sum fun v _ => hfit t v d
      _ = (Fintype.card V : ℚ) ^ 2 * (x + ε) := by
          simp only [sum_const, card_univ, nsmul_eq_mul]; ring
  have h1 := r.delivered_sum t
  have h2 : backlog (r.Q 0) = 0 := by simp [backlog, h0]
  linarith

end Run

end General

end Fluid

end AsyncLean
