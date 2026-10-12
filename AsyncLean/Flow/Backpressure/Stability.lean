/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure.Model

/-!
# Backpressure, part 2: stability below the fluid optimum

The quadratic drift (`Run.drift`, `Run.drift_of`): the energy of a backpressure run drops by
`2 ε` times its backlog, up to a constant, because the max-weight rates beat any flow of the
traffic.  Hence bounded energy (`Run.energy_bounded`), stability (`Run.backpressure_stable`,
`Run.stable_of`) and throughput optimality (`Run.backpressure_optimal`): every load strictly
below a routable traffic is carried in full.
-/

namespace AsyncLean

namespace Fluid

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Run

variable {N : Net V} (r : Run N)

/-! ### The drift of backpressure -/

/-- The constant of the drift bound: the squares of the capacities out of and into every
vertex, the latter plus the demand. -/
def driftConst (N : Net V) (dem : V → V → ℚ) : ℚ :=
  ∑ d, ∑ v, ((∑ w, N.cap v w) ^ 2 + (∑ u, N.cap u v + dem v d) ^ 2)

/-- **The drift bound**, for any rates that beat the flow `F` in weight and are served in a
work-conserving way.  If `dem` is routable at throughput `1` and the arrivals stay `ε > 0`
below it, the energy of a backpressure run drops by `2 ε` times the backlog, up to the
constant `driftConst N dem`. -/
theorem drift_of {dem : V → V → ℚ} (F : Flow N dem 1)
    (hw' : ∀ t, weight (r.Q t) F.f ≤ weight (r.Q t) (r.μ t)) (hwc : r.WorkConserving)
    (hdem : ∀ v d, 0 ≤ dem v d) {ε : ℚ} (hε : 0 < ε)
    (harr : ∀ t v d, v ≠ d → r.a t v d + ε ≤ dem v d) (t : ℕ) :
    energy (r.Q (t + 1)) ≤ energy (r.Q t) + driftConst N dem - 2 * ε * backlog (r.Q t) := by
  set Q := r.Q t with hQdef
  set μ := r.μ t
  -- the arrivals are below the demand
  have ha : ∀ v d, r.a t v d ≤ dem v d := fun v d => by
    by_cases h : v = d
    · subst h; rw [r.a_dest]; exact hdem v v
    · linarith [harr t v d h]
  -- the rates out of and into a vertex are within the capacities
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
  -- one queue at a time
  have hq : ∀ d v, r.Q (t + 1) v d ^ 2 ≤
      Q v d ^ 2 + ((∑ w, N.cap v w) ^ 2 + (∑ u, N.cap u v + dem v d) ^ 2) -
        2 * Q v d * (∑ w, μ d v w - ∑ u, μ d u v) + 2 * Q v d * r.a t v d := by
    intro d v
    have hbb : (∑ w, μ d v w) ^ 2 ≤ (∑ w, N.cap v w) ^ 2 :=
      pow_le_pow_left₀ (hb0 d v) (hb d v) 2
    have hcc : (∑ u, μ d u v + r.a t v d) ^ 2 ≤ (∑ u, N.cap u v + dem v d) ^ 2 :=
      pow_le_pow_left₀ (add_nonneg (hc0 d v) (r.a_nonneg t v d))
        (add_le_add (hc d v) (ha v d)) 2
    by_cases h : v = d
    · subst h
      rw [r.Q_dest, hQdef, r.Q_dest]
      nlinarith [sq_nonneg (∑ w, μ v v w), sq_nonneg (∑ u, μ v u v + r.a t v v)]
    · rw [r.update t v d h]
      have key := queue_sq (Q := Q v d) (b := ∑ w, μ d v w) (out := ∑ w, r.x t d v w)
        (inn := ∑ u, r.x t d u v) (c := ∑ u, μ d u v) (a := r.a t v d)
        (r.Q_nonneg t v d) (hb0 d v) (r.x_avail t d v) (hwc t d v)
        (sum_nonneg fun u _ => r.x_nonneg t d u v)
        (sum_le_sum fun u _ => r.x_le t d u v) (r.a_nonneg t v d)
      nlinarith
  -- the weight of the schedule beats the weight of the flow
  have hw : weight Q F.f ≤ weight Q μ := hw' t
  rw [F.weight_eq Q (r.Q_dest t), weight_eq] at hw
  -- the backlog times the slack
  have hslack : ∀ d v, ε * Q v d ≤ Q v d * (dem v d - r.a t v d) := fun d v => by
    by_cases h : v = d
    · subst h; rw [hQdef, r.Q_dest]; simp
    · have := harr t v d h
      nlinarith [r.Q_nonneg t v d]
  calc energy (r.Q (t + 1)) = ∑ d, ∑ v, r.Q (t + 1) v d ^ 2 := rfl
    _ ≤ ∑ d, ∑ v, (Q v d ^ 2 + ((∑ w, N.cap v w) ^ 2 + (∑ u, N.cap u v + dem v d) ^ 2) -
        2 * Q v d * (∑ w, μ d v w - ∑ u, μ d u v) + 2 * Q v d * r.a t v d) :=
        sum_le_sum fun d _ => sum_le_sum fun v _ => hq d v
    _ = energy Q + driftConst N dem - 2 * ∑ d, ∑ u, Q u d * (∑ w, μ d u w - ∑ x, μ d x u) +
        2 * ∑ d, ∑ v, Q v d * r.a t v d := by
        rw [show energy Q + driftConst N dem = ∑ d, ∑ v, (Q v d ^ 2 +
            ((∑ w, N.cap v w) ^ 2 + (∑ u, N.cap u v + dem v d) ^ 2)) by
          simp only [energy, driftConst, ← sum_add_distrib]]
        simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun d _ => sum_congr rfl fun v _ => ?_
        ring_nf
    _ ≤ energy Q + driftConst N dem - 2 * ∑ d, (1 : ℚ) * ∑ s, dem s d * Q s d +
        2 * ∑ d, ∑ v, Q v d * r.a t v d := by linarith
    _ = energy Q + driftConst N dem - 2 * ∑ d, ∑ v, Q v d * (dem v d - r.a t v d) := by
        simp only [one_mul, mul_sub, sum_sub_distrib]
        have : ∑ d, ∑ s, dem s d * Q s d = ∑ d, ∑ v, Q v d * dem v d :=
          sum_congr rfl fun d _ => sum_congr rfl fun v _ => mul_comm _ _
        rw [this]; ring
    _ ≤ energy Q + driftConst N dem - 2 * ε * backlog Q := by
        have : ε * backlog Q ≤ ∑ d, ∑ v, Q v d * (dem v d - r.a t v d) := by
          rw [backlog, mul_sum]
          exact sum_le_sum fun d _ => by rw [mul_sum]; exact sum_le_sum fun v _ => hslack d v
        linarith

/-- **The drift bound.**  If `dem` is routable at throughput `1` and the arrivals stay `ε > 0`
below it, the energy of a backpressure run drops by `2 ε` times the backlog, up to the
constant `driftConst N dem`. -/
theorem drift (hr : r.Backpressure) {dem : V → V → ℚ} (F : Flow N dem 1)
    (hdem : ∀ v d, 0 ≤ dem v d) {ε : ℚ} (hε : 0 < ε)
    (harr : ∀ t v d, v ≠ d → r.a t v d + ε ≤ dem v d) (t : ℕ) :
    energy (r.Q (t + 1)) ≤ energy (r.Q t) + driftConst N dem - 2 * ε * backlog (r.Q t) :=
  r.drift_of F (fun t => hr.1 t F.f F.feasible) hr.2 hdem hε harr t

omit [DecidableEq V] in
theorem driftConst_nonneg (N : Net V) (dem : V → V → ℚ) : 0 ≤ driftConst N dem :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by positivity

/-- A sequence whose drift is `B - 2 ε S` for `S ≥ 0` with `E ≤ S²` stays at most
`max (E 0) ((B / (2 ε))² + B)`. -/
theorem bounded_of_drift {E S : ℕ → ℚ} {B ε : ℚ} (hε : 0 < ε)
    (hS : ∀ t, 0 ≤ S t) (hES : ∀ t, E t ≤ S t ^ 2)
    (hd : ∀ t, E (t + 1) ≤ E t + B - 2 * ε * S t) (t : ℕ) :
    E t ≤ max (E 0) ((B / (2 * ε)) ^ 2 + B) := by
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih =>
    have hd := hd t
    have hS := hS t
    rcases le_or_gt (B / (2 * ε)) (S t) with h | h
    · have : B ≤ 2 * ε * S t := by
        rw [div_le_iff₀ (by positivity)] at h; linarith
      linarith
    · have h2 : S t ^ 2 ≤ (B / (2 * ε)) ^ 2 := pow_le_pow_left₀ hS h.le 2
      have h3 : 0 ≤ 2 * ε * S t := by positivity
      exact le_max_of_le_right (by linarith [hES t])

/-- **The energy of a backpressure run stays bounded** below the fluid optimum. -/
theorem energy_bounded (hr : r.Backpressure) {dem : V → V → ℚ} (F : Flow N dem 1)
    (hdem : ∀ v d, 0 ≤ dem v d) {ε : ℚ} (hε : 0 < ε)
    (harr : ∀ t v d, v ≠ d → r.a t v d + ε ≤ dem v d) (t : ℕ) :
    energy (r.Q t) ≤
      max (energy (r.Q 0)) ((driftConst N dem / (2 * ε)) ^ 2 + driftConst N dem) := by
  have hd : ∀ t, energy (r.Q (t + 1)) ≤
      energy (r.Q t) + driftConst N dem - 2 * ε * backlog (r.Q t) :=
    r.drift hr F hdem hε harr
  have hES : ∀ t, energy (r.Q t) ≤ backlog (r.Q t) ^ 2 :=
    fun t => energy_le_backlog_sq fun v d => r.Q_nonneg t v d
  exact bounded_of_drift (E := fun t => energy (r.Q t)) (S := fun t => backlog (r.Q t))
    (B := driftConst N dem) hε r.backlog_nonneg hES hd t

/-- **Backpressure is stable** below the fluid optimum: if `dem` is routable at throughput `1`
and the arrivals stay `ε > 0` below it, the backlog of a backpressure run stays bounded and the
run delivers everything that arrives, up to a constant. -/
theorem backpressure_stable (hr : r.Backpressure) {dem : V → V → ℚ}
    (hR : Routable N dem 1) (hdem : ∀ v d, 0 ≤ dem v d) {ε : ℚ} (hε : 0 < ε)
    (harr : ∀ t v d, v ≠ d → r.a t v d + ε ≤ dem v d) : r.Stable := by
  obtain ⟨F⟩ := hR
  obtain ⟨K, hK⟩ : ∃ K, ∀ t, energy (r.Q t) ≤ K :=
    ⟨_, r.energy_bounded hr F hdem hε harr⟩
  refine ⟨(Fintype.card V : ℚ) ^ 2 + K, fun t => ⟨?_, ?_⟩⟩
  · have h1 := backlog_le_energy (r.Q t)
    have h2 := hK t
    linarith
  · have h1 := backlog_le_energy (r.Q t)
    have h2 := hK t
    have h3 := r.delivered_sum t
    have h4 := r.backlog_nonneg 0
    linarith

/-- **Stability for any rates that beat a flow in weight**: if `dem` is routable at throughput
`1` by the flow `F`, the run's rates beat `F` in weight in every slot and are served in a
work-conserving way, and the arrivals stay `ε > 0` below `dem`, the run is stable. -/
theorem stable_of {dem : V → V → ℚ} (F : Flow N dem 1)
    (hw : ∀ t, weight (r.Q t) F.f ≤ weight (r.Q t) (r.μ t)) (hwc : r.WorkConserving)
    (hdem : ∀ v d, 0 ≤ dem v d) {ε : ℚ} (hε : 0 < ε)
    (harr : ∀ t v d, v ≠ d → r.a t v d + ε ≤ dem v d) : r.Stable := by
  have hE : ∀ t, energy (r.Q t) ≤
      max (energy (r.Q 0)) ((driftConst N dem / (2 * ε)) ^ 2 + driftConst N dem) :=
    fun t => bounded_of_drift (E := fun t => energy (r.Q t)) (S := fun t => backlog (r.Q t))
      (B := driftConst N dem) hε r.backlog_nonneg
      (fun t => energy_le_backlog_sq fun v d => r.Q_nonneg t v d)
      (r.drift_of F hw hwc hdem hε harr) t
  set K := max (energy (r.Q 0)) ((driftConst N dem / (2 * ε)) ^ 2 + driftConst N dem)
  refine ⟨(Fintype.card V : ℚ) ^ 2 + K, fun t => ⟨?_, ?_⟩⟩
  · linarith [backlog_le_energy (r.Q t), hE t]
  · linarith [backlog_le_energy (r.Q t), hE t, r.delivered_sum t, r.backlog_nonneg 0]

/-- **Backpressure is throughput optimal.**  If `dem ≥ 0` is routable at `θ` and some traffic
`J` reaching every pair (`J v d ≥ c > 0` for `v ≠ d`) is routable at `η > 0`, then under every
load `ρ * dem` with `0 ≤ ρ < θ` (arrivals at most `ρ * dem v d` in every slot) a backpressure
run keeps its backlog bounded and delivers everything that arrives, up to a constant.  The
scheduler uses only the backlogs: not `dem`, `θ`, `J` or any flow. -/
theorem backpressure_optimal (hr : r.Backpressure) {dem J : V → V → ℚ} {θ η c ρ : ℚ}
    (hR : Routable N dem θ) (hJ : Routable N J η) (hdem : ∀ v d, 0 ≤ dem v d)
    (hJnn : ∀ v d, 0 ≤ J v d) (hc : 0 < c) (hJc : ∀ v d, v ≠ d → c ≤ J v d) (hη : 0 < η)
    (hρ : 0 ≤ ρ) (hρθ : ρ < θ) (harr : ∀ t v d, v ≠ d → r.a t v d ≤ ρ * dem v d) :
    r.Stable := by
  obtain ⟨F₁⟩ := hR
  obtain ⟨F₂⟩ := hJ
  have hθ : 0 < θ := hρ.trans_lt hρθ
  have hα : 0 ≤ ρ / θ := div_nonneg hρ hθ.le
  have hα1 : ρ / θ < 1 := (div_lt_iff₀ hθ).2 (by linarith)
  have hβ : 0 < 1 - ρ / θ := by linarith
  let F := F₁.mix F₂ hα hβ.le (by linarith)
  have he : ∀ v d, ρ / θ * θ * dem v d = ρ * dem v d := fun v d => by
    rw [div_mul_cancel₀ ρ hθ.ne']
  refine r.backpressure_stable hr (dem := fun v d => ρ / θ * θ * dem v d +
      (1 - ρ / θ) * η * J v d) ⟨F⟩
    (fun v d => by have := hdem v d; have := hJnn v d; positivity)
    (ε := (1 - ρ / θ) * η * c) (by positivity) fun t v d hvd => ?_
  rw [he]
  have h1 := harr t v d hvd
  have h2 : (1 - ρ / θ) * η * c ≤ (1 - ρ / θ) * η * J v d :=
    mul_le_mul_of_nonneg_left (hJc v d hvd) (by positivity)
  linarith

end Run

end General

end Fluid

end AsyncLean
