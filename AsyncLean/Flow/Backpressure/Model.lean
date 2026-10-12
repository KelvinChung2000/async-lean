/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Scaling

/-!
# Backpressure, part 1: the queueing model

The discrete-time queueing network of the fluid model (`Fluid.Run`): per-destination backlogs at
every vertex, rates offered within the capacities, traffic carried, arrivals.  The definitions of
the scheduler (`Run.MaxWeight`, `Run.WorkConserving`, `Run.Backpressure`) and of stability
(`Run.BoundedBacklog`, `Run.Stable`), conservation (`Run.backlog_succ`, `Run.delivered_sum`), the
energy `∑ Q²` and the algebra of flows the later parts use (`Flow.normalize`, `Flow.mix`).

See `AsyncLean.Flow.Backpressure` for the overview.
-/

namespace AsyncLean

namespace Fluid

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rates `μ d u v` for commodity `d` on the link `u → v` are **feasible** in `N`: nonnegative
and within the capacity of every link. -/
def Feasible (N : Net V) (μ : V → V → V → ℚ) : Prop :=
  (∀ d u v, 0 ≤ μ d u v) ∧ ∀ u v, ∑ d, μ d u v ≤ N.cap u v

/-- The **weight** of rates `μ` for the backlogs `Q`: the rate times the backlog difference
across the link, summed over commodities and links. -/
def weight (Q : V → V → ℚ) (μ : V → V → V → ℚ) : ℚ :=
  ∑ d, ∑ u, ∑ v, μ d u v * (Q u d - Q v d)

/-- The total backlog. -/
def backlog (Q : V → V → ℚ) : ℚ := ∑ d, ∑ v, Q v d

/-- The energy `∑ Q²` of the backlogs, the Lyapunov function of backpressure. -/
def energy (Q : V → V → ℚ) : ℚ := ∑ d, ∑ v, Q v d ^ 2

omit [DecidableEq V] in
/-- A flow is feasible as rates. -/
theorem Flow.feasible {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (F : Flow N dem θ) :
    Feasible N F.f :=
  ⟨F.nonneg, F.capacity⟩

omit [DecidableEq V] in
/-- The weight is the backlog times the net rate out of every vertex. -/
theorem weight_eq (Q : V → V → ℚ) (μ : V → V → V → ℚ) :
    weight Q μ = ∑ d, ∑ u, Q u d * (∑ w, μ d u w - ∑ x, μ d x u) := by
  unfold weight
  refine sum_congr rfl fun d _ => ?_
  simp only [mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  · exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => mul_comm _ _
  · rw [sum_comm]
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => mul_comm _ _

/-- The weight of a flow of `θ * dem` is `θ` times the demand weighted by the backlogs. -/
theorem Flow.weight_eq {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (F : Flow N dem θ)
    (Q : V → V → ℚ) (hQ : ∀ d, Q d d = 0) :
    weight Q F.f = ∑ d, θ * ∑ s, dem s d * Q s d :=
  sum_congr rfl fun d _ => F.telescope d (fun v => Q v d) (hQ d)

omit [DecidableEq V] in
/-- For nonnegative backlogs the energy is at most the square of the total backlog. -/
theorem energy_le_backlog_sq {Q : V → V → ℚ} (hQ : ∀ v d, 0 ≤ Q v d) :
    energy Q ≤ backlog Q ^ 2 := by
  have hle : ∀ v d, Q v d ≤ backlog Q := fun v d =>
    (single_le_sum (f := fun v => Q v d) (fun v _ => hQ v d) (mem_univ v)).trans
      (single_le_sum (f := fun d => ∑ v, Q v d) (fun d _ => sum_nonneg fun v _ => hQ v d)
        (mem_univ d))
  calc energy Q = ∑ d, ∑ v, Q v d * Q v d := by simp only [energy, sq]
    _ ≤ ∑ d, ∑ v, Q v d * backlog Q :=
        sum_le_sum fun d _ => sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hle v d) (hQ v d)
    _ = backlog Q ^ 2 := by simp only [← sum_mul, sq, backlog]

omit [DecidableEq V] in
/-- The total backlog is at most `|V|² + energy`. -/
theorem backlog_le_energy (Q : V → V → ℚ) :
    backlog Q ≤ (Fintype.card V : ℚ) ^ 2 + energy Q := by
  have h : ∀ v d, Q v d ≤ 1 + Q v d ^ 2 := fun v d => by nlinarith [sq_nonneg (Q v d - 1)]
  calc backlog Q ≤ ∑ d : V, ∑ v : V, (1 + Q v d ^ 2) :=
        sum_le_sum fun d _ => sum_le_sum fun v _ => h v d
    _ = (Fintype.card V : ℚ) ^ 2 + energy Q := by
        simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, energy]
        ring

/-- **One queue for one slot.**  A queue `Q ≥ 0` offered the rate `b ≥ 0` sends `out`, at most
its backlog and at least `min Q b`, and receives `inn ≤ c` plus `a`: the square of its new
backlog is at most `Q² + b² + (c + a)² - 2 Q b + 2 Q (c + a)`. -/
theorem queue_sq {Q b out inn c a : ℚ} (hQ : 0 ≤ Q) (hb : 0 ≤ b) (hout : out ≤ Q)
    (hwork : min Q b ≤ out) (hinn : 0 ≤ inn) (hc : inn ≤ c) (ha : 0 ≤ a) :
    (Q - out + inn + a) ^ 2 ≤ Q ^ 2 + b ^ 2 + (c + a) ^ 2 - 2 * Q * b + 2 * Q * (c + a) := by
  have hr0 : 0 ≤ Q - out := by linarith
  have hout0 : 0 ≤ out := (le_min hQ hb).trans hwork
  have hrQ : Q - out ≤ Q := by linarith
  have hr2 : (Q - out) ^ 2 ≤ (Q - b) ^ 2 := by
    rcases le_total Q b with h | h
    · have : out ≥ Q := by rw [min_eq_left h] at hwork; exact hwork
      have : Q - out = 0 := by linarith
      rw [this]; positivity
    · have : out ≥ b := by rw [min_eq_right h] at hwork; exact hwork
      have h1 : Q - out ≤ Q - b := by linarith
      nlinarith
  have hc0 : 0 ≤ inn + a := by linarith
  have hcc : inn + a ≤ c + a := by linarith
  have h1 : (Q - out) * (inn + a) ≤ Q * (c + a) := mul_le_mul hrQ hcc hc0 hQ
  have h2 : (inn + a) * (inn + a) ≤ (c + a) * (c + a) := mul_self_le_mul_self hc0 hcc
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- Every rational is below some natural number. -/
theorem exists_nat_gt_rat (q : ℚ) : ∃ n : ℕ, q < n := by
  refine ⟨q.num.natAbs + 1, ?_⟩
  rcases le_or_gt q 0 with h | h
  · exact lt_of_le_of_lt h (by positivity)
  have h1 : q ≤ q * q.den :=
    le_mul_of_one_le_right h.le (by exact_mod_cast q.den_pos)
  rw [Rat.mul_den_eq_num] at h1
  have h2 : (q.num : ℚ) ≤ (q.num.natAbs : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]; exact le_abs_self _
  push_cast
  linarith

/-- A **queueing run** of the network `N` (see the module docstring): backlogs `Q`, arrivals
`a`, offered rates `μ` and carried traffic `x`, slot by slot. -/
structure Run (N : Net V) where
  /-- The backlog at `v` for the destination `d` at the start of slot `t`. -/
  Q : ℕ → V → V → ℚ
  /-- The traffic arriving at `v` for `d` in slot `t`. -/
  a : ℕ → V → V → ℚ
  /-- The rate offered to commodity `d` on the link `u → v` in slot `t`. -/
  μ : ℕ → V → V → V → ℚ
  /-- The traffic of commodity `d` the link `u → v` carries in slot `t`. -/
  x : ℕ → V → V → V → ℚ
  Q_zero_nonneg : ∀ v d, 0 ≤ Q 0 v d
  /-- Traffic at its destination has left the network. -/
  Q_dest : ∀ t d, Q t d d = 0
  a_nonneg : ∀ t v d, 0 ≤ a t v d
  a_dest : ∀ t d, a t d d = 0
  μ_feasible : ∀ t, Feasible N (μ t)
  x_nonneg : ∀ t d u v, 0 ≤ x t d u v
  x_le : ∀ t d u v, x t d u v ≤ μ t d u v
  /-- A vertex sends at most its backlog of every commodity. -/
  x_avail : ∀ t d u, ∑ v, x t d u v ≤ Q t u d
  /-- The backlog changes by what is sent, what is received and what arrives. -/
  update : ∀ t v d, v ≠ d →
    Q (t + 1) v d = Q t v d - ∑ w, x t d v w + ∑ u, x t d u v + a t v d

namespace Run

variable {N : Net V} (r : Run N)

/-- The traffic delivered in slot `t`. -/
def delivered (t : ℕ) : ℚ := ∑ d, ∑ u, r.x t d u d

/-- The traffic arriving in slot `t`. -/
def arrived (t : ℕ) : ℚ := ∑ d, ∑ v, r.a t v d

/-- The rates are **max-weight** in every slot. -/
def MaxWeight : Prop := ∀ t μ', Feasible N μ' → weight (r.Q t) μ' ≤ weight (r.Q t) (r.μ t)

/-- Every vertex sends of every commodity at least the smaller of its backlog and the rate it
is offered. -/
def WorkConserving : Prop := ∀ t d u, min (r.Q t u d) (∑ v, r.μ t d u v) ≤ ∑ v, r.x t d u v

/-- A **backpressure** run: max-weight and work conserving. -/
def Backpressure : Prop := r.MaxWeight ∧ r.WorkConserving

/-- The backlog stays bounded. -/
def BoundedBacklog : Prop := ∃ C, ∀ t, backlog (r.Q t) ≤ C

/-- The run is **stable**: its backlog stays at most a constant `C`, and it delivers everything
that arrives up to `C`. -/
def Stable : Prop :=
  ∃ C, ∀ t, backlog (r.Q t) ≤ C ∧ ∑ s ∈ range t, r.arrived s - C ≤ ∑ s ∈ range t, r.delivered s

omit [DecidableEq V] in
theorem Stable.boundedBacklog {r : Run N} (h : r.Stable) : r.BoundedBacklog := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun t => (hC t).1⟩

theorem Q_nonneg (t : ℕ) (v d : V) : 0 ≤ r.Q t v d := by
  cases t with
  | zero => exact r.Q_zero_nonneg v d
  | succ t =>
    by_cases h : v = d
    · subst h; rw [r.Q_dest]
    · rw [r.update t v d h]
      have h1 := r.x_avail t d v
      have h2 : 0 ≤ ∑ u, r.x t d u v := sum_nonneg fun u _ => r.x_nonneg t d u v
      have h3 := r.a_nonneg t v d
      linarith

omit [DecidableEq V] in
/-- Nothing leaves a destination for itself. -/
theorem x_from_dest (t : ℕ) (d w : V) : r.x t d d w = 0 := by
  have h := r.x_avail t d d
  rw [r.Q_dest] at h
  have hs : ∑ v, r.x t d d v = 0 := le_antisymm h (sum_nonneg fun v _ => r.x_nonneg t d d v)
  exact (sum_eq_zero_iff_of_nonneg fun v _ => r.x_nonneg t d d v).1 hs w (mem_univ w)

/-- The update at every vertex, the destination included. -/
theorem update' (t : ℕ) (v d : V) :
    r.Q (t + 1) v d = (r.Q t v d - ∑ w, r.x t d v w + ∑ u, r.x t d u v + r.a t v d) -
      if v = d then ∑ u, r.x t d u d else 0 := by
  by_cases h : v = d
  · subst h
    rw [r.Q_dest, r.Q_dest, r.a_dest, ite_eq_left rfl]
    simp [r.x_from_dest]
  · rw [r.update t v d h, ite_eq_right h, sub_zero]

/-- **Conservation**: the backlog grows by what arrives and shrinks by what is delivered. -/
theorem backlog_succ (t : ℕ) :
    backlog (r.Q (t + 1)) = backlog (r.Q t) - r.delivered t + r.arrived t := by
  unfold backlog delivered arrived
  rw [← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun d _ => ?_
  simp only [r.update' t, sum_sub_distrib, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
  have : ∑ v, ∑ u, r.x t d u v = ∑ v, ∑ w, r.x t d v w := sum_comm
  linarith

/-- The traffic delivered in the first `T` slots is what arrived less the growth of the
backlog. -/
theorem delivered_sum (T : ℕ) :
    ∑ t ∈ range T, r.delivered t =
      backlog (r.Q 0) - backlog (r.Q T) + ∑ t ∈ range T, r.arrived t := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, sum_range_succ, ih, r.backlog_succ T]
    ring

theorem backlog_nonneg (t : ℕ) : 0 ≤ backlog (r.Q t) :=
  sum_nonneg fun d _ => sum_nonneg fun v _ => r.Q_nonneg t v d

end Run

/-- A flow of `θ * dem` is a flow of the traffic `θ * dem` at throughput `1`. -/
def Flow.normalize {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (F : Flow N dem θ) :
    Flow N (fun v d => θ * dem v d) 1 where
  f := F.f
  nonneg := F.nonneg
  conserve d v hv := by rw [one_mul]; exact F.conserve d v hv
  capacity := F.capacity

/-- Two flows of two traffic matrices, scaled by `α, β ≥ 0` with `α + β ≤ 1`, route the
mixture at throughput `1`. -/
def Flow.mix {N : Net V} {dem₁ dem₂ : V → V → ℚ} {θ₁ θ₂ : ℚ} (F₁ : Flow N dem₁ θ₁)
    (F₂ : Flow N dem₂ θ₂) {α β : ℚ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β ≤ 1) :
    Flow N (fun v d => α * θ₁ * dem₁ v d + β * θ₂ * dem₂ v d) 1 where
  f d u v := α * F₁.f d u v + β * F₂.f d u v
  nonneg d u v := add_nonneg (mul_nonneg hα (F₁.nonneg d u v)) (mul_nonneg hβ (F₂.nonneg d u v))
  conserve d v hv := by
    simp only [sum_add_distrib, ← mul_sum]
    have h1 := F₁.conserve d v hv
    have h2 := F₂.conserve d v hv
    rw [one_mul]
    calc _ = α * (∑ w, F₁.f d v w - ∑ u, F₁.f d u v) +
          β * (∑ w, F₂.f d v w - ∑ u, F₂.f d u v) := by ring
      _ = _ := by rw [h1, h2]; ring
  capacity u v := by
    simp only [sum_add_distrib, ← mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (F₁.capacity u v) hα
    have h2 := mul_le_mul_of_nonneg_left (F₂.capacity u v) hβ
    have h3 := N.cap_nonneg u v
    nlinarith

end General

end Fluid

end AsyncLean
