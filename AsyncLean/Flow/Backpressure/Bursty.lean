/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure.Stability

/-!
# Backpressure, part 4: bursty arrivals

Stability for arrivals within a leaky bucket (at most `W (dem - ε) + σ` over every window of `W`
slots, at most `A` per slot): the drift over a frame of slots (`Run.frame_drift`) and
`Run.backpressure_stable_bursty`.  This covers whole packets arriving at fractional rates.
-/

namespace AsyncLean

namespace Fluid

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Run

variable {N : Net V} (r : Run N)

/-! ### Bursty arrivals: integer packets at fractional rates -/

/-- **The drift for arbitrary arrivals** (at most `A` per queue and slot): the energy of a
backpressure run grows by at most a constant less twice the backlog times the slack
`dem - a` of the slot. -/
theorem drift_gen (hr : r.Backpressure) {dem : V → V → ℚ} (F : Flow N dem 1) {A : ℚ}
    (t : ℕ) (hA : ∀ v d, r.a t v d ≤ A) :
    energy (r.Q (t + 1)) ≤ energy (r.Q t) + driftConst N (fun _ _ => A) -
      2 * ∑ d, ∑ v, r.Q t v d * (dem v d - r.a t v d) := by
  set Q := r.Q t with hQdef
  set μ := r.μ t
  have hb : ∀ d v, ∑ w, μ d v w ≤ ∑ w, N.cap v w := fun d v =>
    sum_le_sum fun w _ => (single_le_sum (f := fun d => μ d v w)
      (fun d _ => (r.μ_feasible t).1 d v w) (mem_univ d)).trans ((r.μ_feasible t).2 v w)
  have hc : ∀ d v, ∑ u, μ d u v ≤ ∑ u, N.cap u v := fun d v =>
    sum_le_sum fun u _ => (single_le_sum (f := fun d => μ d u v)
      (fun d _ => (r.μ_feasible t).1 d u v) (mem_univ d)).trans ((r.μ_feasible t).2 u v)
  have hb0 : ∀ d v, 0 ≤ ∑ w, μ d v w := fun d v =>
    sum_nonneg fun w _ => (r.μ_feasible t).1 d v w
  have hc0 : ∀ d v, 0 ≤ ∑ u, μ d u v := fun d v =>
    sum_nonneg fun u _ => (r.μ_feasible t).1 d u v
  have hq : ∀ d v, r.Q (t + 1) v d ^ 2 ≤
      Q v d ^ 2 + ((∑ w, N.cap v w) ^ 2 + (∑ u, N.cap u v + A) ^ 2) -
        2 * Q v d * (∑ w, μ d v w - ∑ u, μ d u v) + 2 * Q v d * r.a t v d := by
    intro d v
    have hbb : (∑ w, μ d v w) ^ 2 ≤ (∑ w, N.cap v w) ^ 2 :=
      pow_le_pow_left₀ (hb0 d v) (hb d v) 2
    have hcc : (∑ u, μ d u v + r.a t v d) ^ 2 ≤ (∑ u, N.cap u v + A) ^ 2 :=
      pow_le_pow_left₀ (add_nonneg (hc0 d v) (r.a_nonneg t v d))
        (add_le_add (hc d v) (hA v d)) 2
    by_cases h : v = d
    · subst h
      rw [r.Q_dest, hQdef, r.Q_dest]
      nlinarith [sq_nonneg (∑ w, μ v v w), sq_nonneg (∑ u, μ v u v + r.a t v v)]
    · rw [r.update t v d h]
      have key := queue_sq (Q := Q v d) (b := ∑ w, μ d v w) (out := ∑ w, r.x t d v w)
        (inn := ∑ u, r.x t d u v) (c := ∑ u, μ d u v) (a := r.a t v d)
        (r.Q_nonneg t v d) (hb0 d v) (r.x_avail t d v) (hr.2 t d v)
        (sum_nonneg fun u _ => r.x_nonneg t d u v)
        (sum_le_sum fun u _ => r.x_le t d u v) (r.a_nonneg t v d)
      nlinarith
  have hw : weight Q F.f ≤ weight Q μ := hr.1 t F.f F.feasible
  rw [F.weight_eq Q (r.Q_dest t), weight_eq] at hw
  calc energy (r.Q (t + 1)) = ∑ d, ∑ v, r.Q (t + 1) v d ^ 2 := rfl
    _ ≤ ∑ d, ∑ v, (Q v d ^ 2 + ((∑ w, N.cap v w) ^ 2 + (∑ u, N.cap u v + A) ^ 2) -
        2 * Q v d * (∑ w, μ d v w - ∑ u, μ d u v) + 2 * Q v d * r.a t v d) :=
        sum_le_sum fun d _ => sum_le_sum fun v _ => hq d v
    _ = energy Q + driftConst N (fun _ _ => A) -
        2 * ∑ d, ∑ u, Q u d * (∑ w, μ d u w - ∑ x, μ d x u) +
        2 * ∑ d, ∑ v, Q v d * r.a t v d := by
        rw [show energy Q + driftConst N (fun _ _ => A) = ∑ d, ∑ v, (Q v d ^ 2 +
            ((∑ w, N.cap v w) ^ 2 + (∑ u, N.cap u v + A) ^ 2)) by
          simp only [energy, driftConst, ← sum_add_distrib]]
        simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun d _ => sum_congr rfl fun v _ => ?_
        ring_nf
    _ ≤ energy Q + driftConst N (fun _ _ => A) - 2 * ∑ d, (1 : ℚ) * ∑ s, dem s d * Q s d +
        2 * ∑ d, ∑ v, Q v d * r.a t v d := by linarith
    _ = energy Q + driftConst N (fun _ _ => A) -
        2 * ∑ d, ∑ v, Q v d * (dem v d - r.a t v d) := by
        simp only [one_mul, mul_sub, sum_sub_distrib]
        have : ∑ d, ∑ s, dem s d * Q s d = ∑ d, ∑ v, Q v d * dem v d :=
          sum_congr rfl fun d _ => sum_congr rfl fun v _ => mul_comm _ _
        rw [this]; ring

/-- The total capacity of the network. -/
def capTot (N : Net V) : ℚ := ∑ u, ∑ w, N.cap u w

omit [DecidableEq V] in
theorem capTot_nonneg (N : Net V) : 0 ≤ capTot N :=
  sum_nonneg fun u _ => sum_nonneg fun w _ => N.cap_nonneg u w

/-- In one slot a queue changes by at most twice the total capacity plus the arrivals. -/
theorem step_change {A : ℚ} (hA0 : 0 ≤ A) (hA : ∀ t v d, r.a t v d ≤ A) (t : ℕ) (v d : V) :
    |r.Q (t + 1) v d - r.Q t v d| ≤ 2 * capTot N + A := by
  by_cases h : v = d
  · subst h; rw [r.Q_dest, r.Q_dest, sub_zero, abs_zero]
    linarith [capTot_nonneg N]
  · rw [r.update t v d h]
    have hout0 : 0 ≤ ∑ w, r.x t d v w := sum_nonneg fun w _ => r.x_nonneg t d v w
    have hin0 : 0 ≤ ∑ u, r.x t d u v := sum_nonneg fun u _ => r.x_nonneg t d u v
    have ha0 := r.a_nonneg t v d
    have hrow : ∀ u, ∑ w, N.cap u w ≤ capTot N := fun u =>
      single_le_sum (f := fun u => ∑ w, N.cap u w)
        (fun u _ => sum_nonneg fun w _ => N.cap_nonneg u w) (mem_univ u)
    have hout : ∑ w, r.x t d v w ≤ capTot N :=
      (sum_le_sum fun w _ => (r.x_le t d v w).trans ((single_le_sum (f := fun d => r.μ t d v w)
        (fun d _ => (r.μ_feasible t).1 d v w) (mem_univ d)).trans
          ((r.μ_feasible t).2 v w))).trans (hrow v)
    have hin : ∑ u, r.x t d u v ≤ capTot N := by
      calc ∑ u, r.x t d u v ≤ ∑ u, N.cap u v :=
            sum_le_sum fun u _ => (r.x_le t d u v).trans ((single_le_sum
              (f := fun d => r.μ t d u v) (fun d _ => (r.μ_feasible t).1 d u v)
                (mem_univ d)).trans ((r.μ_feasible t).2 u v))
        _ ≤ ∑ u, ∑ w, N.cap u w :=
            sum_le_sum fun u _ => single_le_sum (f := fun w => N.cap u w)
              (fun w _ => N.cap_nonneg u w) (mem_univ v)
    rw [abs_le]
    constructor <;> linarith [hA t v d]

/-- Over `s` slots a queue changes by at most `s` times the one-slot bound. -/
theorem frame_change {A : ℚ} (hA0 : 0 ≤ A) (hA : ∀ t v d, r.a t v d ≤ A) (t s : ℕ) (v d : V) :
    |r.Q (t + s) v d - r.Q t v d| ≤ s * (2 * capTot N + A) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := r.step_change hA0 hA (t + s) v d
    have h2 : r.Q (t + (s + 1)) v d - r.Q t v d =
        (r.Q (t + s + 1) v d - r.Q (t + s) v d) + (r.Q (t + s) v d - r.Q t v d) := by
      rw [← add_assoc]; ring
    rw [h2]
    calc |(r.Q (t + s + 1) v d - r.Q (t + s) v d) + (r.Q (t + s) v d - r.Q t v d)|
        ≤ |r.Q (t + s + 1) v d - r.Q (t + s) v d| + |r.Q (t + s) v d - r.Q t v d| :=
          abs_add_le _ _
      _ ≤ (2 * capTot N + A) + s * (2 * capTot N + A) := add_le_add h1 ih
      _ = ((s + 1 : ℕ) : ℚ) * (2 * capTot N + A) := by push_cast; ring

/-- **The drift over a frame** of `W` slots, for arrivals within a leaky bucket: at most
`W ε - σ` below the demand on average, with bursts of at most `σ`. -/
theorem frame_drift (hr : r.Backpressure) {dem : V → V → ℚ} (F : Flow N dem 1)
    (hdem : ∀ v d, 0 ≤ dem v d) {D : ℚ} (hD0 : 0 ≤ D) (hD : ∀ v d, dem v d ≤ D) {A : ℚ}
    (hA0 : 0 ≤ A) (hA : ∀ t v d, r.a t v d ≤ A) {ε σ : ℚ}
    (hburst : ∀ t W v d, v ≠ d → ∑ s ∈ range W, r.a (t + s) v d ≤ W * (dem v d - ε) + σ)
    (t W : ℕ) :
    energy (r.Q (t + W)) ≤ energy (r.Q t) +
      (W * driftConst N (fun _ _ => A) +
        2 * (Fintype.card V : ℚ) ^ 2 * W ^ 2 * ((2 * capTot N + A) * (D + A))) -
      2 * (W * ε - σ) * backlog (r.Q t) := by
  set Δ := 2 * capTot N + A
  have hΔ : 0 ≤ Δ := by have := capTot_nonneg N; positivity
  have hDA : 0 ≤ D + A := by linarith
  -- one slot at a time, comparing the backlogs with those at the start of the frame
  have hslot : ∀ s, energy (r.Q (t + s + 1)) ≤ energy (r.Q (t + s)) +
      driftConst N (fun _ _ => A) - 2 * ∑ d, ∑ v, r.Q t v d * (dem v d - r.a (t + s) v d) +
      2 * (Fintype.card V : ℚ) ^ 2 * (s * Δ * (D + A)) := by
    intro s
    have h1 := r.drift_gen hr F (t + s) (fun v d => hA (t + s) v d)
    have h2 : ∀ d v, r.Q t v d * (dem v d - r.a (t + s) v d) - s * Δ * (D + A) ≤
        r.Q (t + s) v d * (dem v d - r.a (t + s) v d) := fun d v => by
      have hc := r.frame_change hA0 hA t s v d
      have hx : |dem v d - r.a (t + s) v d| ≤ D + A := by
        rw [abs_le]; constructor <;> linarith [hdem v d, hD v d, hA (t + s) v d,
          r.a_nonneg (t + s) v d]
      obtain ⟨hc1, hc2⟩ := abs_le.1 hc
      obtain ⟨hx1, hx2⟩ := abs_le.1 hx
      have hsΔ : 0 ≤ (s : ℚ) * Δ := by positivity
      nlinarith [mul_nonneg (sub_nonneg.2 hc2) (sub_nonneg.2 hx2),
        mul_nonneg (by linarith : (0 : ℚ) ≤ s * Δ + (r.Q (t + s) v d - r.Q t v d))
          (by linarith : (0 : ℚ) ≤ D + A + (dem v d - r.a (t + s) v d))]
    have h3 : ∑ d, ∑ v, r.Q t v d * (dem v d - r.a (t + s) v d) -
        (Fintype.card V : ℚ) ^ 2 * (s * Δ * (D + A)) ≤
        ∑ d, ∑ v, r.Q (t + s) v d * (dem v d - r.a (t + s) v d) := by
      have e : (Fintype.card V : ℚ) ^ 2 * (s * Δ * (D + A)) =
          ∑ _d : V, ∑ _v : V, (s * Δ * (D + A)) := by
        simp only [sum_const, card_univ, nsmul_eq_mul]; ring
      rw [e, ← sum_sub_distrib]
      exact sum_le_sum fun d _ => by rw [← sum_sub_distrib]; exact sum_le_sum fun v _ => h2 d v
    rw [show t + s + 1 = t + s + 1 from rfl]
    linarith
  -- the frame
  have hsum : energy (r.Q (t + W)) ≤ energy (r.Q t) + W * driftConst N (fun _ _ => A) -
      2 * ∑ d, ∑ v, r.Q t v d * (W * dem v d - ∑ s ∈ range W, r.a (t + s) v d) +
      2 * (Fintype.card V : ℚ) ^ 2 * (W ^ 2 * Δ * (D + A)) := by
    induction W with
    | zero => simp
    | succ W ih =>
      have h := hslot W
      rw [← add_assoc]
      have e : ∑ d, ∑ v, r.Q t v d * (((W + 1 : ℕ) : ℚ) * dem v d -
          ∑ s ∈ range (W + 1), r.a (t + s) v d) =
          ∑ d, ∑ v, r.Q t v d * (W * dem v d - ∑ s ∈ range W, r.a (t + s) v d) +
          ∑ d, ∑ v, r.Q t v d * (dem v d - r.a (t + W) v d) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun d _ => ?_
        rw [← sum_add_distrib]
        refine sum_congr rfl fun v _ => ?_
        rw [sum_range_succ]; push_cast; ring
      rw [e]
      have hW : (W : ℚ) * Δ * (D + A) ≤ ((W : ℚ) + 1) ^ 2 * Δ * (D + A) -
          (W : ℚ) ^ 2 * Δ * (D + A) := by
        have : (0 : ℚ) ≤ Δ * (D + A) := mul_nonneg hΔ hDA
        nlinarith
      have hc0 : (0 : ℚ) ≤ (Fintype.card V : ℚ) ^ 2 := by positivity
      have hp := mul_le_mul_of_nonneg_left hW hc0
      push_cast at h ⊢
      linarith
  -- the slack over the frame
  have hslack : (W * ε - σ) * backlog (r.Q t) ≤
      ∑ d, ∑ v, r.Q t v d * (W * dem v d - ∑ s ∈ range W, r.a (t + s) v d) := by
    rw [backlog, mul_sum]
    refine sum_le_sum fun d _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun v _ => ?_
    by_cases h : v = d
    · subst h; rw [r.Q_dest]; simp
    · have := hburst t W v d h
      have := r.Q_nonneg t v d
      nlinarith
  have e2 : 2 * (Fintype.card V : ℚ) ^ 2 * (W ^ 2 * Δ * (D + A)) =
      2 * (Fintype.card V : ℚ) ^ 2 * W ^ 2 * ((2 * capTot N + A) * (D + A)) := by ring
  linarith

/-- **Backpressure is stable under bursty arrivals**, in particular for whole packets arriving
at fractional rates.  If `dem` is routable at throughput `1`, the arrivals are at most `A` per
queue and slot, and over every window of `W` slots at most `W (dem - ε) + σ` (a leaky bucket:
rate `ε` below the demand, bursts up to `σ`), the backlog of a backpressure run stays bounded
and the run delivers everything that arrives, up to a constant. -/
theorem backpressure_stable_bursty (hr : r.Backpressure) {dem : V → V → ℚ}
    (hR : Routable N dem 1) (hdem : ∀ v d, 0 ≤ dem v d) {D : ℚ} (hD0 : 0 ≤ D)
    (hD : ∀ v d, dem v d ≤ D) {A : ℚ} (hA0 : 0 ≤ A) (hA : ∀ t v d, r.a t v d ≤ A) {ε σ : ℚ} (hε : 0 < ε) (hσ : 0 ≤ σ)
    (hburst : ∀ t W v d, v ≠ d → ∑ s ∈ range W, r.a (t + s) v d ≤ W * (dem v d - ε) + σ) :
    r.Stable := by
  obtain ⟨F⟩ := hR
  -- a frame long enough for the slack to beat the bursts
  obtain ⟨W, hW⟩ := exists_nat_gt_rat ((σ + ε) / ε)
  have hWε : ε < W * ε - σ := by
    rw [div_lt_iff₀ hε] at hW; linarith
  set ε' := W * ε - σ
  have hε' : 0 < ε' := by linarith
  set B := (W : ℚ) * driftConst N (fun _ _ => A) +
    2 * (Fintype.card V : ℚ) ^ 2 * W ^ 2 * ((2 * capTot N + A) * (D + A))
  -- the energy at the frame boundaries
  have hframe : ∀ j, energy (r.Q (j * W)) ≤ max (energy (r.Q 0)) ((B / (2 * ε')) ^ 2 + B) := by
    intro j
    have := bounded_of_drift (E := fun j => energy (r.Q (j * W)))
      (S := fun j => backlog (r.Q (j * W))) (B := B) hε'
      (fun j => r.backlog_nonneg _) (fun j => energy_le_backlog_sq fun v d => r.Q_nonneg _ v d)
      (fun j => by
        have h := r.frame_drift hr F hdem hD0 hD hA0 hA hburst (j * W) W
        show energy (r.Q ((j + 1) * W)) ≤ energy (r.Q (j * W)) + B - 2 * ε' * backlog (r.Q (j * W))
        rw [show (j + 1) * W = j * W + W by ring]
        exact h) j
    simpa using this
  set K := max (energy (r.Q 0)) ((B / (2 * ε')) ^ 2 + B)
  set Δ := 2 * capTot N + A
  have hΔ : 0 ≤ Δ := by have := capTot_nonneg N; positivity
  have hb : ∀ t, backlog (r.Q t) ≤ (Fintype.card V : ℚ) ^ 2 + K +
      (Fintype.card V : ℚ) ^ 2 * (W * Δ) := by
    intro t
    have hWpos : 0 < W := by
      have : (0 : ℚ) < W := lt_of_le_of_lt (div_nonneg (by linarith) hε.le) hW
      exact_mod_cast this
    obtain ⟨j, s, hs, rfl⟩ : ∃ j s, s < W ∧ t = j * W + s :=
      ⟨t / W, t % W, Nat.mod_lt _ hWpos, by rw [mul_comm]; exact (Nat.div_add_mod t W).symm⟩
    have h1 : backlog (r.Q (j * W)) ≤ (Fintype.card V : ℚ) ^ 2 + K :=
      (backlog_le_energy _).trans (by linarith [hframe j])
    have h2 : backlog (r.Q (j * W + s)) ≤ backlog (r.Q (j * W)) +
        (Fintype.card V : ℚ) ^ 2 * (W * Δ) := by
      have e : (Fintype.card V : ℚ) ^ 2 * (W * Δ) = ∑ _d : V, ∑ _v : V, (W * Δ) := by
        simp only [sum_const, card_univ, nsmul_eq_mul]; ring
      rw [e, backlog, backlog, ← sum_add_distrib]
      refine sum_le_sum fun d _ => ?_
      rw [← sum_add_distrib]
      refine sum_le_sum fun v _ => ?_
      have hc := r.frame_change hA0 hA (j * W) s v d
      have hsW : (s : ℚ) * Δ ≤ W * Δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hs.le) hΔ
      have := (abs_le.1 hc).2
      linarith
    linarith
  refine ⟨(Fintype.card V : ℚ) ^ 2 + K + (Fintype.card V : ℚ) ^ 2 * (W * Δ), fun t =>
    ⟨hb t, ?_⟩⟩
  rw [r.delivered_sum t]
  linarith [r.backlog_nonneg 0, hb t]

end Run

end General

end Fluid

end AsyncLean
