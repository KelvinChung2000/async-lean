/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Scaling

/-!
# Backpressure reaches the fluid optimum

The fluid model (`Fluid.Routable`) says which throughputs a network can carry at best.  This
file proves that one scheduler, **backpressure** (max-weight scheduling, Tassiulas and
Ephremides), carries every one of them: every load strictly inside the fluid optimum keeps its
backlog bounded and is delivered in full.  Conversely no scheduler whatever keeps its backlog
bounded above any fluid upper bound (`Run.potential_ceiling`).  So the fluid optimum is exactly
the throughput of backpressure.

## The model

A **queueing run** (`Fluid.Run N`) runs in slots `t = 0, 1, …`.  Every vertex `v` keeps a
backlog `Q t v d ≥ 0` for every destination `d` (`Q t d d = 0`: a packet at its destination has
left).  In slot `t` the scheduler offers commodity `d` the rate `μ t d u v` on the link
`u → v`, within the capacities (`Feasible`); the link carries `x t d u v ≤ μ t d u v`, and no
vertex sends more of a commodity than it holds.  Then `a t v d ≥ 0` new traffic arrives:

  `Q (t+1) v d = Q t v d - (sent by v) + (received by v) + a t v d`   (`v ≠ d`).

Quantities are rational: the run is the queueing network of the fluid model in discrete time,
with packets as divisible as the fluid's.  The backpressure scheduler (`Run.Backpressure`):

* **max-weight** : the rates maximise `∑ d u v, μ d u v * (Q u d - Q v d)` (`weight`) among all
  feasible rates.  Giving every link, in full, to a commodity of largest backlog difference
  across it, when that difference is positive, is such a choice (`bpRates_maxWeight`).
* **work conserving** : a vertex sends of each commodity `min (backlog, offered rate)`.

## Main results

* `Run.backlog_succ`, `Run.delivered_sum` : conservation: the delivered traffic is what arrived
  less what is still queued.
* `Run.drift` : **the drift bound.**  If `dem` is routable at throughput `1` and the arrivals
  stay `ε` below it (`a t v d + ε ≤ dem v d`), the energy `∑ Q²` of a backpressure run obeys
  `E (t+1) ≤ E t + B - 2 ε ∑ Q`, for a constant `B` of the network and the traffic.
* `Run.backpressure_stable` : the backlog of a backpressure run stays bounded, and it delivers
  all its arrivals up to a constant.
* `Run.backpressure_optimal` : **backpressure is throughput optimal.**  If `dem` is routable at
  `θ`, every load `ρ * dem` with `0 ≤ ρ < θ` (any arrivals below it, slot by slot) keeps the
  backlog bounded and is delivered in full.  Only some traffic reaching every pair is needed
  (for instance the uniform traffic): no knowledge of `dem`, `θ` or the flow is used by the
  scheduler.
* `Run.backpressure_fitsIn` : **finite buffers suffice.**  Started empty, the run never holds
  more than `B / (2 ε) + ε` in any per-destination queue (`Run.FitsIn`), so buffers of that size
  are never exceeded; the size grows like `1 / ε` as the load approaches the optimum.
  `mesh_buffer` : on the mesh with `m` connections per link, under a load `(1 - δ)` times the
  optimum, buffers of `145 m k⁷ / (16 δ) + m` packets per destination suffice (a loose constant).
* `Run.backpressure_stable_bursty` : **bursty arrivals**: the same for arrivals within a leaky
  bucket (at most `W (dem - ε) + σ` over every window of `W` slots), by the drift over frames
  (`Run.frame_drift`); this covers whole packets arriving at fractional rates.
  `Run.ofArrivalsSeq` : backpressure with sequential sends (`sendSeq`), which moves whole packets
  only (`Run.ofArrivalsSeq_int`); `mesh_backpressure_packets` : on the mesh with `m` connections
  it is stable for whole packets at every leaky-bucket rate below `m` times the optimum.
* `Run.potential_ceiling` : **the ceiling**, for every scheduler: a run that keeps its backlog
  bounded under the load `ρ * dem` respects every potential bound of the fluid model
  (`potential_bound`); `Run.cut_ceiling`, `Run.hop_ceiling` are the cut and hop forms.
* Instances, with `m` connections per link: on the `k × k` mesh (even `k`) under uniform traffic
  backpressure is stable at every load below `m * 8 (k² - 1) / k³`, no scheduler is stable
  above it (`mesh_backpressure`); likewise on the torus (`torus_backpressure`, `m` times
  `torus_uniform_opt`) and the hypercube (`cube_backpressure`).
* `Run.ofArrivals`, `Run.ofArrivals_backpressure` : for every arrival sequence there is a
  backpressure run (the greedy rates `bpRates`, proportional transmissions `sendAll`);
  `mesh_backpressure_exists` : on the mesh it is stable at every load below the optimum.

All results are over `ℚ`.
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

/-- The run **fits in buffers of size `b`**: no per-destination queue ever holds more than
`b`.  A network with buffers of size `b` per destination at every vertex, which blocks or drops
on overflow, then behaves exactly like the run: the overflow never happens. -/
def FitsIn (b : ℚ) : Prop := ∀ t v d, r.Q t v d ≤ b

omit [DecidableEq V] in
/-- A queue is at most `x + ε` when the energy is at most `x² + 2 x ε`. -/
theorem queue_le_of_energy {Q : V → V → ℚ} {x ε : ℚ} (hx : 0 ≤ x)
    (hε : 0 < ε) (hE : energy Q ≤ x ^ 2 + 2 * x * ε) (v d : V) : Q v d ≤ x + ε := by
  have h1 : Q v d ^ 2 ≤ energy Q :=
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
  have hE0 : energy (r.Q 0) = 0 := by simp [energy, h0]
  have hfit : r.FitsIn (x + ε) := fun t v d => by
    have h := r.energy_bounded hr F hdem hε harr t
    rw [hE0, max_eq_right (by positivity)] at h
    have e : B = 2 * x * ε := by
      rw [hxdef, show (2 : ℚ) * (B / (2 * ε)) * ε = B / (2 * ε) * (2 * ε) by ring,
        div_mul_cancel₀ B (by positivity)]
    have e' : (B / (2 * ε)) ^ 2 + B = x ^ 2 + 2 * x * ε := by rw [← e]
    exact queue_le_of_energy hx hε (h.trans e'.le) v d
  refine ⟨hfit, fun t => ?_⟩
  have hb : backlog (r.Q t) ≤ (Fintype.card V : ℚ) ^ 2 * (x + ε) := by
    calc backlog (r.Q t) ≤ ∑ _d : V, ∑ _v : V, (x + ε) :=
          sum_le_sum fun d _ => sum_le_sum fun v _ => hfit t v d
      _ = (Fintype.card V : ℚ) ^ 2 * (x + ε) := by
          simp only [sum_const, card_univ, nsmul_eq_mul]; ring
  have h1 := r.delivered_sum t
  have h2 : backlog (r.Q 0) = 0 := by simp [backlog, h0]
  linarith

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

namespace Run

variable {N : Net V} (r : Run N)

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

/-! ### The ceiling: no scheduler beats the fluid model -/

/-- The traffic carried in the first `T` slots is a flow, in `T` copies of the network, of what
arrived less the growth of the backlog. -/
def totalFlow (T : ℕ) :
    Flow (N.copies T) (fun v d => ∑ t ∈ range T, r.a t v d - (r.Q T v d - r.Q 0 v d)) 1 where
  f d u v := ∑ t ∈ range T, r.x t d u v
  nonneg d u v := sum_nonneg fun t _ => r.x_nonneg t d u v
  conserve d v hv := by
    show _ = 1 * (∑ t ∈ range T, r.a t v d - (r.Q T v d - r.Q 0 v d))
    rw [one_mul]
    have e1 : ∑ w, ∑ t ∈ range T, r.x t d v w = ∑ t ∈ range T, ∑ w, r.x t d v w := sum_comm
    have e2 : ∑ u, ∑ t ∈ range T, r.x t d u v = ∑ t ∈ range T, ∑ u, r.x t d u v := sum_comm
    have h : ∀ t, ∑ w, r.x t d v w - ∑ u, r.x t d u v =
        (r.Q t v d - r.Q (t + 1) v d) + r.a t v d := fun t => by
      rw [r.update t v d hv]; ring
    rw [e1, e2, ← sum_sub_distrib]
    simp only [h, sum_add_distrib, sum_range_sub']
    ring
  capacity u v := by
    rw [sum_comm, Net.copies_cap]
    calc ∑ t ∈ range T, ∑ d, r.x t d u v ≤ ∑ _t ∈ range T, N.cap u v :=
          sum_le_sum fun t _ =>
            (sum_le_sum fun d _ => r.x_le t d u v).trans ((r.μ_feasible t).2 u v)
      _ = T * N.cap u v := by rw [sum_const, card_range, nsmul_eq_mul]

omit [DecidableEq V] in
/-- A positive sum over the slots has a positive term. -/
theorem exists_pos_of_sum_pos {T : ℕ} (d u v : V)
    (h : 0 < (r.totalFlow T).f d u v) : ∃ t ∈ range T, 0 < r.x t d u v := by
  by_contra hn
  simp only [not_exists, not_and, not_lt] at hn
  have : (r.totalFlow T).f d u v ≤ 0 := sum_nonpos fun t ht => hn t ht
  linarith

/-- **The potential ceiling**, for every scheduler: if the arrivals are `ρ * dem` in every slot
and the backlog stays at most `C`, the load respects every potential bound of the fluid model
with a bounded potential `0 ≤ φ ≤ M`: `ρ * ∑ s d, dem s d * φ d s ≤ ∑ u v, cap u v * len u v`. -/
theorem potential_ceiling_on {dem : V → V → ℚ} {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    {S : V → V → V → Prop} (hS : ∀ t d u v, 0 < r.x t d u v → S d u v)
    (len : V → V → ℚ) (hlen : ∀ u v, 0 ≤ len u v)
    (φ : V → V → ℚ) (hφd : ∀ d, φ d d = 0)
    (hφ : ∀ d u v, S d u v → 0 < N.cap u v → φ d u - φ d v ≤ len u v)
    (hφ0 : ∀ d v, 0 ≤ φ d v) {M : ℚ} (hM : ∀ d v, φ d v ≤ M) :
    ρ * ∑ s, ∑ d, dem s d * φ d s ≤ ∑ u, ∑ v, N.cap u v * len u v := by
  obtain ⟨C, hC⟩ := hb
  set Φ := ∑ s, ∑ d, dem s d * φ d s with hΦ
  set K := ∑ u, ∑ v, N.cap u v * len u v with hK
  set M' := max M 0
  have hM' : ∀ d v, φ d v ≤ M' := fun d v => (hM d v).trans (le_max_left _ _)
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hT : ∀ T : ℕ, (T : ℚ) * (ρ * Φ) ≤ T * K + M' * C := by
    intro T
    have hsupp : (r.totalFlow T).SupportedOn S := fun d u v h => by
      obtain ⟨t, -, ht⟩ := r.exists_pos_of_sum_pos d u v h
      exact hS t d u v ht
    have key := (r.totalFlow T).potential_bound_on hsupp len hlen φ hφd (fun d u v hS' hc => by
      apply hφ d u v hS'
      simp only [Net.copies_cap] at hc
      exact pos_of_mul_pos_right hc (Nat.cast_nonneg T))
    simp only [Net.copies_cap, one_mul] at key
    -- the arrivals
    have hA : ∑ s, ∑ d, (∑ t ∈ range T, r.a t s d) * φ d s = T * (ρ * Φ) := by
      have e : ∀ s d, (∑ t ∈ range T, r.a t s d) * φ d s = T * ρ * (dem s d * φ d s) := by
        intro s d
        by_cases h : s = d
        · subst h; rw [hφd]; simp
        · simp only [harr _ s d h, sum_const, card_range, nsmul_eq_mul]; ring
      simp only [e, ← mul_sum, hΦ]
      ring
    -- the backlog
    have hB : ∑ s, ∑ d, (r.Q T s d - r.Q 0 s d) * φ d s ≤ M' * C := by
      calc ∑ s, ∑ d, (r.Q T s d - r.Q 0 s d) * φ d s ≤ ∑ s, ∑ d, r.Q T s d * M' :=
            sum_le_sum fun s _ => sum_le_sum fun d _ => by
              have := r.Q_nonneg 0 s d
              have := r.Q_nonneg T s d
              have := hφ0 d s
              have := hM' d s
              nlinarith
        _ = M' * backlog (r.Q T) := by
            rw [backlog, mul_sum]
            rw [sum_comm (f := fun s d => r.Q T s d * M')]
            exact sum_congr rfl fun d _ => by
              rw [mul_sum]; exact sum_congr rfl fun s _ => mul_comm _ _
        _ ≤ M' * C := mul_le_mul_of_nonneg_left (hC T) hM0
    have e : ∑ s, ∑ d, (∑ t ∈ range T, r.a t s d - (r.Q T s d - r.Q 0 s d)) * φ d s =
        ∑ s, ∑ d, (∑ t ∈ range T, r.a t s d) * φ d s -
          ∑ s, ∑ d, (r.Q T s d - r.Q 0 s d) * φ d s := by
      simp only [sub_mul, sum_sub_distrib]
    have e2 : ∑ u, ∑ v, (T : ℚ) * N.cap u v * len u v = T * K := by
      simp only [hK, mul_sum, mul_assoc]
    rw [e, hA, e2] at key
    linarith
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hT'⟩ := exists_nat_gt_rat (M' * C / (ρ * Φ - K))
  have hpos : 0 < ρ * Φ - K := by linarith
  have := hT T
  rw [div_lt_iff₀ hpos] at hT'
  have := mul_sub (T : ℚ) (ρ * Φ) K
  linarith

/-- **The potential ceiling**, for every scheduler: if the arrivals are `ρ * dem` in every slot
and the backlog stays bounded, the load respects every potential bound of the fluid model with
a bounded potential `0 ≤ φ ≤ M`: `ρ * ∑ s d, dem s d * φ d s ≤ ∑ u v, cap u v * len u v`. -/
theorem potential_ceiling {dem : V → V → ℚ} {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    (len : V → V → ℚ) (hlen : ∀ u v, 0 ≤ len u v)
    (φ : V → V → ℚ) (hφd : ∀ d, φ d d = 0)
    (hφ : ∀ d u v, 0 < N.cap u v → φ d u - φ d v ≤ len u v)
    (hφ0 : ∀ d v, 0 ≤ φ d v) {M : ℚ} (hM : ∀ d v, φ d v ≤ M) :
    ρ * ∑ s, ∑ d, dem s d * φ d s ≤ ∑ u, ∑ v, N.cap u v * len u v :=
  r.potential_ceiling_on harr hb (S := fun _ _ _ => True) (fun _ _ _ _ _ => trivial) len hlen φ
    hφd (fun d u v _ hc => hφ d u v hc) hφ0 hM

/-- **A stable run moving traffic only on `S` respects every potential bound on `S`**, as a flow
supported on `S` does: every dual certificate of the fluid model bounds it. -/
theorem potentialFeasibleOn {dem : V → V → ℚ} {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    {S : V → V → V → Prop} (hS : ∀ t d u v, 0 < r.x t d u v → S d u v) :
    PotentialFeasibleOn N S dem ρ := fun len φ hlen hφd hφ hφ0 =>
  r.potential_ceiling_on harr hb hS len hlen φ hφd hφ hφ0 (M := ∑ a, ∑ b, φ a b) fun d v =>
    (single_le_sum (f := fun b => φ d b) (fun b _ => hφ0 d b) (mem_univ v)).trans
      (single_le_sum (f := fun a => ∑ b, φ a b) (fun a _ => sum_nonneg fun b _ => hφ0 a b)
        (mem_univ d))

/-- **The cut ceiling**, for every scheduler: a run that keeps its backlog bounded under the load
`ρ * dem` carries across every cut at most the cut's capacity. -/
theorem cut_ceiling {dem : V → V → ℚ} {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    (S : V → Prop) [DecidablePred S] :
    ρ * ∑ s, ∑ d, (if S s ∧ ¬ S d then dem s d else 0) ≤
      ∑ u, ∑ v, if S u ∧ ¬ S v then N.cap u v else 0 := by
  have key := r.potential_ceiling harr hb (fun u v => if S u ∧ ¬ S v then 1 else 0)
    (fun u v => by split_ifs <;> norm_num)
    (fun d v => if S v ∧ ¬ S d then 1 else 0) (fun d => by simp)
    (fun _ u v _ => by
      by_cases hu : S u <;> by_cases hv : S v <;> split_ifs <;> simp_all)
    (fun d v => by split_ifs <;> norm_num) (M := 1) (fun d v => by split_ifs <;> norm_num)
  have e1 : ∑ s, ∑ d, dem s d * (if S s ∧ ¬ S d then (1 : ℚ) else 0) =
      ∑ s, ∑ d, (if S s ∧ ¬ S d then dem s d else 0) :=
    sum_congr rfl fun s _ => sum_congr rfl fun d _ => by split_ifs <;> simp
  have e2 : ∑ u, ∑ v, N.cap u v * (if S u ∧ ¬ S v then (1 : ℚ) else 0) =
      ∑ u, ∑ v, (if S u ∧ ¬ S v then N.cap u v else 0) :=
    sum_congr rfl fun u _ => sum_congr rfl fun v _ => by split_ifs <;> simp
  rw [e1, e2] at key
  exact key

/-- **The hop ceiling**, for every scheduler: a run that keeps its backlog bounded under the load
`ρ * dem` has `ρ * ∑ s d, dem s d * dist s d ≤ ∑ u v, cap u v` for every nonnegative hop
distance. -/
theorem hop_ceiling {dem : V → V → ℚ} {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    {dist : V → V → ℚ} (hd : IsHopDistance N dist) (hd0 : ∀ u v, 0 ≤ dist u v) :
    ρ * hopDemand dem dist ≤ ∑ u, ∑ v, N.cap u v := by
  have hM : ∀ d v, dist v d ≤ ∑ a, ∑ b, dist a b := fun d v =>
    (single_le_sum (f := fun b => dist v b) (fun b _ => hd0 v b) (mem_univ d)).trans
      (single_le_sum (f := fun a => ∑ b, dist a b) (fun a _ => sum_nonneg fun b _ => hd0 a b)
        (mem_univ v))
  have := r.potential_ceiling harr hb (fun _ _ => 1) (fun _ _ => zero_le_one)
    (fun d v => dist v d) hd.1 (fun d u v hc => hd.2 u v d hc) (fun d v => hd0 v d) hM
  simpa [hopDemand] using this

end Run

omit [Fintype V] [DecidableEq V] in
/-- A hop distance of a network is a hop distance of its copies. -/
theorem IsHopDistance.copies {N : Net V} {dist : V → V → ℚ} (h : IsHopDistance N dist)
    (m : ℕ) : IsHopDistance (N.copies m) dist :=
  ⟨h.1, fun u v d hc => h.2 u v d (by
    rw [Net.copies_cap] at hc; exact pos_of_mul_pos_right hc (Nat.cast_nonneg m))⟩

namespace Run

variable {N : Net V} (r : Run N)

/-- **The hop ceiling is the optimum on symmetric networks.**  If the hop bound is tight for
`dem` (`θ * hopDemand dem dist = ∑ cap`, as on the torus and the hypercube), a run on `m` copies
of the network that keeps its backlog bounded under `ρ * dem` has `ρ ≤ m * θ`. -/
theorem copies_hop_ceiling {m : ℕ} (r : Run (N.copies m)) {dem : V → V → ℚ} {ρ θ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    {dist : V → V → ℚ} (hd : IsHopDistance N dist) (hd0 : ∀ u v, 0 ≤ dist u v)
    (hD : 0 < hopDemand dem dist) (htight : θ * hopDemand dem dist = ∑ u, ∑ v, N.cap u v) :
    ρ ≤ m * θ := by
  have h := r.hop_ceiling harr hb (hd.copies m) hd0
  simp only [Net.copies_cap, ← mul_sum] at h
  rw [← htight] at h
  have : ρ * hopDemand dem dist ≤ (m * θ) * hopDemand dem dist := by linarith
  exact le_of_mul_le_mul_right this hD

end Run


/-! ### The backpressure scheduler exists -/

section Construct

variable [Nonempty V] (N : Net V)

/-- A commodity of largest backlog difference across the link `u → v`. -/
noncomputable def best (Q : V → V → ℚ) (u v : V) : V :=
  (exists_max_image univ (fun d => Q u d - Q v d) univ_nonempty).choose

omit [DecidableEq V] in
theorem best_spec (Q : V → V → ℚ) (u v d : V) :
    Q u d - Q v d ≤ Q u (best Q u v) - Q v (best Q u v) :=
  (exists_max_image univ (fun d => Q u d - Q v d) univ_nonempty).choose_spec.2 d (mem_univ d)

/-- **The backpressure rates**: every link, in full, to a commodity of largest backlog
difference across it, when that difference is positive. -/
noncomputable def bpRates (Q : V → V → ℚ) : V → V → V → ℚ := fun d u v =>
  if d = best Q u v ∧ 0 < Q u d - Q v d then N.cap u v else 0

/-- The rate the backpressure rates give a link, weighted: the capacity times the positive
part of the largest backlog difference. -/
theorem bpRates_link (Q : V → V → ℚ) (u v : V) :
    ∑ d, bpRates N Q d u v * (Q u d - Q v d) =
      N.cap u v * max (Q u (best Q u v) - Q v (best Q u v)) 0 := by
  have e : ∀ d, bpRates N Q d u v * (Q u d - Q v d) =
      if d = best Q u v then
        (if 0 < Q u (best Q u v) - Q v (best Q u v) then
          N.cap u v * (Q u (best Q u v) - Q v (best Q u v)) else 0) else 0 := fun d => by
    unfold bpRates
    by_cases h : d = best Q u v
    · subst h; split_ifs <;> simp_all
    · simp [h]
  simp only [e, sum_ite_eq', mem_univ, ite_true]
  split_ifs with h
  · rw [max_eq_left h.le]
  · rw [max_eq_right (not_lt.1 h), mul_zero]

theorem bpRates_feasible (Q : V → V → ℚ) : Feasible N (bpRates N Q) := by
  refine ⟨fun d u v => ?_, fun u v => ?_⟩
  · unfold bpRates; split_ifs
    · exact N.cap_nonneg u v
    · exact le_rfl
  · have e : ∀ d, bpRates N Q d u v =
        if d = best Q u v then
          (if 0 < Q u (best Q u v) - Q v (best Q u v) then N.cap u v else 0) else 0 :=
      fun d => by
        unfold bpRates
        by_cases h : d = best Q u v
        · subst h; split_ifs <;> simp_all
        · simp [h]
    simp only [e, sum_ite_eq', mem_univ, ite_true]
    split_ifs
    · exact le_rfl
    · exact N.cap_nonneg u v

omit [DecidableEq V] [Nonempty V] in
/-- Reordering the triple sum of the weight. -/
theorem weight_comm (Q : V → V → ℚ) (μ : V → V → V → ℚ) :
    weight Q μ = ∑ u, ∑ v, ∑ d, μ d u v * (Q u d - Q v d) := by
  unfold weight
  rw [sum_comm]
  exact sum_congr rfl fun u _ => sum_comm

/-- **The backpressure rates are max-weight.** -/
theorem bpRates_maxWeight (Q : V → V → ℚ) (μ : V → V → V → ℚ) (hμ : Feasible N μ) :
    weight Q μ ≤ weight Q (bpRates N Q) := by
  rw [weight_comm, weight_comm]
  simp only [bpRates_link]
  refine sum_le_sum fun u _ => sum_le_sum fun v _ => ?_
  set M := max (Q u (best Q u v) - Q v (best Q u v)) 0
  calc ∑ d, μ d u v * (Q u d - Q v d) ≤ ∑ d, μ d u v * M :=
        sum_le_sum fun d _ => mul_le_mul_of_nonneg_left
          ((best_spec Q u v d).trans (le_max_left _ _)) (hμ.1 d u v)
    _ = (∑ d, μ d u v) * M := by rw [sum_mul]
    _ ≤ N.cap u v * M := mul_le_mul_of_nonneg_right (hμ.2 u v) (le_max_right _ _)

omit [Nonempty V] in
/-- The share of the offered rates a vertex can serve: all of them if its backlog suffices,
else its backlog's fraction. -/
noncomputable def share (Q : V → V → ℚ) (μ : V → V → V → ℚ) (d u : V) : ℚ :=
  if ∑ v, μ d u v ≤ Q u d then 1 else max (Q u d) 0 / ∑ v, μ d u v

omit [Nonempty V] in
/-- **Proportional transmissions**: every link carries the vertex's share of its rate. -/
noncomputable def sendAll (Q : V → V → ℚ) (μ : V → V → V → ℚ) : V → V → V → ℚ :=
  fun d u v => μ d u v * share Q μ d u

section

omit [Nonempty V]

variable {Q : V → V → ℚ} {μ : V → V → V → ℚ}

omit [DecidableEq V] in
theorem share_nonneg (hμ : ∀ d u v, 0 ≤ μ d u v) (d u : V) : 0 ≤ share Q μ d u := by
  unfold share; split_ifs
  · exact zero_le_one
  · exact div_nonneg (le_max_right _ _) (sum_nonneg fun v _ => hμ d u v)

omit [DecidableEq V] in
theorem share_le_one (d u : V) : share Q μ d u ≤ 1 := by
  unfold share; split_ifs with h
  · exact le_rfl
  · rw [not_le] at h
    rcases le_total (Q u d) 0 with hq | hq
    · rw [max_eq_right hq, zero_div]; exact zero_le_one
    · rw [max_eq_left hq, div_le_one₀ (lt_of_le_of_lt hq h)]; exact h.le

omit [DecidableEq V] in
/-- With a nonnegative backlog a vertex sends exactly `min (backlog, offered rate)`. -/
theorem sendAll_sum {d u : V} (hQ : 0 ≤ Q u d) :
    ∑ v, sendAll Q μ d u v = min (Q u d) (∑ v, μ d u v) := by
  unfold sendAll
  rw [← sum_mul]
  unfold share
  split_ifs with h
  · rw [mul_one, min_eq_right h]
  · rw [not_le] at h
    have hpos : 0 < ∑ v, μ d u v := lt_of_le_of_lt hQ h
    rw [max_eq_left hQ, mul_div_cancel₀ _ hpos.ne', min_eq_left h.le]

end

variable (a : ℕ → V → V → ℚ) (Q₀ : V → V → ℚ)

/-- The backlogs of the backpressure run with arrivals `a` from `Q₀`. -/
noncomputable def bpQ : ℕ → V → V → ℚ
  | 0 => Q₀
  | t + 1 => fun v d =>
    if v = d then 0 else
      bpQ t v d - ∑ w, sendAll (bpQ t) (bpRates N (bpQ t)) d v w +
        ∑ u, sendAll (bpQ t) (bpRates N (bpQ t)) d u v + a t v d

variable {a Q₀}

theorem bpQ_nonneg (ha : ∀ t v d, 0 ≤ a t v d) (hQ₀ : ∀ v d, 0 ≤ Q₀ v d) :
    ∀ t v d, 0 ≤ bpQ N a Q₀ t v d
  | 0, v, d => hQ₀ v d
  | t + 1, v, d => by
    have ih := bpQ_nonneg ha hQ₀ t
    have hμ := (bpRates_feasible N (bpQ N a Q₀ t)).1
    simp only [bpQ]
    split_ifs
    · exact le_rfl
    · have h1 := sendAll_sum (μ := bpRates N (bpQ N a Q₀ t)) (ih v d)
      have h2 : 0 ≤ ∑ u, sendAll (bpQ N a Q₀ t) (bpRates N (bpQ N a Q₀ t)) d u v :=
        sum_nonneg fun u _ => mul_nonneg (hμ d u v) (share_nonneg hμ d u)
      have h3 := min_le_left (bpQ N a Q₀ t v d) (∑ w, bpRates N (bpQ N a Q₀ t) d v w)
      have h4 := ha t v d
      linarith

/-- **A backpressure run exists** for every arrival sequence (nonnegative, none for a vertex
itself) and every initial backlog: the backpressure rates (`bpRates`) with proportional
transmissions (`sendAll`). -/
noncomputable def Run.ofArrivals (ha : ∀ t v d, 0 ≤ a t v d) (had : ∀ t d, a t d d = 0)
    (hQ₀ : ∀ v d, 0 ≤ Q₀ v d) (hQ₀d : ∀ d, Q₀ d d = 0) : Run N where
  Q := bpQ N a Q₀
  a := a
  μ t := bpRates N (bpQ N a Q₀ t)
  x t := sendAll (bpQ N a Q₀ t) (bpRates N (bpQ N a Q₀ t))
  Q_zero_nonneg := hQ₀
  Q_dest t d := by
    cases t with
    | zero => exact hQ₀d d
    | succ t => simp [bpQ]
  a_nonneg := ha
  a_dest := had
  μ_feasible t := bpRates_feasible N _
  x_nonneg t d u v := mul_nonneg ((bpRates_feasible N _).1 d u v)
    (share_nonneg (bpRates_feasible N _).1 d u)
  x_le t d u v := mul_le_of_le_one_right ((bpRates_feasible N _).1 d u v)
    (share_le_one d u)
  x_avail t d u := by
    rw [sendAll_sum (bpQ_nonneg N ha hQ₀ t u d)]
    exact min_le_left _ _
  update t v d h := by
    show (if v = d then _ else _) = _
    rw [ite_eq_right h]

theorem Run.ofArrivals_backpressure (ha : ∀ t v d, 0 ≤ a t v d) (had : ∀ t d, a t d d = 0)
    (hQ₀ : ∀ v d, 0 ≤ Q₀ v d) (hQ₀d : ∀ d, Q₀ d d = 0) :
    (Run.ofArrivals N ha had hQ₀ hQ₀d).Backpressure :=
  ⟨fun t μ' hμ' => bpRates_maxWeight N _ μ' hμ', fun t d u => by
    show _ ≤ ∑ v, sendAll _ _ d u v
    rw [sendAll_sum (bpQ_nonneg N ha hQ₀ t u d)]
    exact le_rfl⟩


/-! ### Whole packets: the sequential backpressure scheduler -/

omit [Nonempty V] in
/-- The rate a vertex offers the `j`-th of its out-links (in a fixed numbering of the vertices)
for commodity `d`. -/
noncomputable def seqRate (μ : V → V → V → ℚ) (d u : V) (j : ℕ) : ℚ :=
  if h : j < Fintype.card V then μ d u ((Fintype.equivFin V).symm ⟨j, h⟩) else 0

omit [Nonempty V] in
/-- The rate offered to the out-links numbered below `k`. -/
noncomputable def seqPre (μ : V → V → V → ℚ) (d u : V) (k : ℕ) : ℚ :=
  ∑ j ∈ range k, seqRate μ d u j

omit [Nonempty V] in
/-- **Sequential sends**: a vertex serves its out-links one after the other, in a fixed order,
each with its full rate until its backlog is used up.  With whole-packet backlogs and rates, it
sends whole packets. -/
noncomputable def sendSeq (Q : V → V → ℚ) (μ : V → V → V → ℚ) : V → V → V → ℚ :=
  fun d u v => min (μ d u v) (max 0 (Q u d - seqPre μ d u (Fintype.equivFin V v)))

omit [Fintype V] [DecidableEq V] [Nonempty V] in
/-- The share of a link in sequential service is a difference of the served amounts. -/
theorem clamp_eq {Q P m : ℚ} (hm : 0 ≤ m) :
    min m (max 0 (Q - P)) = min Q (P + m) - min Q P := by
  rcases le_total Q P with h1 | h1
  · rw [max_eq_left (by linarith), min_eq_right hm, min_eq_left (by linarith), min_eq_left h1]
    ring
  · rw [max_eq_right (by linarith), min_eq_right h1]
    rcases le_total Q (P + m) with h2 | h2
    · rw [min_eq_right (by linarith), min_eq_left h2]
    · rw [min_eq_left (by linarith), min_eq_right h2]; ring

section

omit [Nonempty V]

variable {Q : V → V → ℚ} {μ : V → V → V → ℚ}

omit [DecidableEq V] in
theorem seqPre_nonneg (hμ : ∀ d u v, 0 ≤ μ d u v) (d u : V) (k : ℕ) : 0 ≤ seqPre μ d u k :=
  sum_nonneg fun j _ => by
    unfold seqRate; split_ifs
    · exact hμ _ _ _
    · exact le_rfl

omit [DecidableEq V] in
theorem seqPre_total (d u : V) : seqPre μ d u (Fintype.card V) = ∑ v, μ d u v := by
  unfold seqPre
  rw [← Fin.sum_univ_eq_sum_range (fun j => seqRate μ d u j)]
  rw [← (Fintype.equivFin V).symm.sum_comp]
  refine sum_congr rfl fun i _ => ?_
  simp [seqRate, i.isLt]

omit [DecidableEq V] in
theorem sendSeq_nonneg (hμ : ∀ d u v, 0 ≤ μ d u v) (d u v : V) : 0 ≤ sendSeq Q μ d u v :=
  le_min (hμ d u v) (le_max_left _ _)

omit [DecidableEq V] in
theorem sendSeq_le (d u v : V) : sendSeq Q μ d u v ≤ μ d u v := min_le_left _ _

omit [DecidableEq V] in
/-- **Sequential sends serve `min (backlog, offered rate)`.** -/
theorem sendSeq_sum (hμ : ∀ d u v, 0 ≤ μ d u v) {d u : V} (hQ : 0 ≤ Q u d) :
    ∑ v, sendSeq Q μ d u v = min (Q u d) (∑ v, μ d u v) := by
  set g := fun y : ℚ => min (Q u d) y
  have hpt : ∀ v, sendSeq Q μ d u v =
      g (seqPre μ d u ((Fintype.equivFin V v : ℕ) + 1)) -
        g (seqPre μ d u (Fintype.equivFin V v)) := fun v => by
    have e : seqPre μ d u ((Fintype.equivFin V v : ℕ) + 1) =
        seqPre μ d u (Fintype.equivFin V v) + μ d u v := by
      unfold seqPre
      rw [sum_range_succ]
      simp [seqRate, (Fintype.equivFin V v).isLt]
    rw [e]
    exact clamp_eq (hμ d u v)
  simp only [hpt]
  rw [(Fintype.equivFin V).sum_comp (fun i => g (seqPre μ d u ((i : ℕ) + 1)) -
    g (seqPre μ d u i))]
  rw [Fin.sum_univ_eq_sum_range (fun j => g (seqPre μ d u (j + 1)) - g (seqPre μ d u j)),
    sum_range_sub (fun j => g (seqPre μ d u j)), seqPre_total]
  simp [g, seqPre, min_eq_right hQ]

end

/-- A rational is a whole number. -/
def IsInt (q : ℚ) : Prop := ∃ z : ℤ, q = z

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem IsInt.add {p q : ℚ} : IsInt p → IsInt q → IsInt (p + q) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by push_cast; ring⟩

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem IsInt.sub {p q : ℚ} : IsInt p → IsInt q → IsInt (p - q) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a - b, by push_cast; ring⟩

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem IsInt.min {p q : ℚ} : IsInt p → IsInt q → IsInt (min p q) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨Min.min a b, by push_cast; rfl⟩

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem IsInt.max {p q : ℚ} : IsInt p → IsInt q → IsInt (max p q) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨Max.max a b, by push_cast; rfl⟩

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem IsInt.zero : IsInt 0 := ⟨0, by simp⟩

omit [DecidableEq V] [Nonempty V] in
theorem IsInt.sum {ι : Type*} (s : Finset ι) {f : ι → ℚ} (h : ∀ i ∈ s, IsInt (f i)) :
    IsInt (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsInt.zero
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact (h i (mem_insert_self i s)).add (ih fun j hj => h j (mem_insert_of_mem hj))

variable (a Q₀) in
/-- The backlogs of the backpressure run with sequential sends. -/
noncomputable def bpQSeq : ℕ → V → V → ℚ
  | 0 => Q₀
  | t + 1 => fun v d =>
    if v = d then 0 else
      bpQSeq t v d - ∑ w, sendSeq (bpQSeq t) (bpRates N (bpQSeq t)) d v w +
        ∑ u, sendSeq (bpQSeq t) (bpRates N (bpQSeq t)) d u v + a t v d

theorem bpQSeq_nonneg (ha : ∀ t v d, 0 ≤ a t v d) (hQ₀ : ∀ v d, 0 ≤ Q₀ v d) :
    ∀ t v d, 0 ≤ bpQSeq N a Q₀ t v d
  | 0, v, d => hQ₀ v d
  | t + 1, v, d => by
    have ih := bpQSeq_nonneg ha hQ₀ t
    have hμ := (bpRates_feasible N (bpQSeq N a Q₀ t)).1
    simp only [bpQSeq]
    split_ifs
    · exact le_rfl
    · have h1 := sendSeq_sum (Q := bpQSeq N a Q₀ t) hμ (ih v d)
      have h2 : 0 ≤ ∑ u, sendSeq (bpQSeq N a Q₀ t) (bpRates N (bpQSeq N a Q₀ t)) d u v :=
        sum_nonneg fun u _ => sendSeq_nonneg hμ d u v
      have h3 := min_le_left (bpQSeq N a Q₀ t v d) (∑ w, bpRates N (bpQSeq N a Q₀ t) d v w)
      have h4 := ha t v d
      linarith

/-- **A backpressure run with sequential sends exists** for every arrival sequence and initial
backlog. -/
noncomputable def Run.ofArrivalsSeq (ha : ∀ t v d, 0 ≤ a t v d) (had : ∀ t d, a t d d = 0)
    (hQ₀ : ∀ v d, 0 ≤ Q₀ v d) (hQ₀d : ∀ d, Q₀ d d = 0) : Run N where
  Q := bpQSeq N a Q₀
  a := a
  μ t := bpRates N (bpQSeq N a Q₀ t)
  x t := sendSeq (bpQSeq N a Q₀ t) (bpRates N (bpQSeq N a Q₀ t))
  Q_zero_nonneg := hQ₀
  Q_dest t d := by
    cases t with
    | zero => exact hQ₀d d
    | succ t => simp [bpQSeq]
  a_nonneg := ha
  a_dest := had
  μ_feasible t := bpRates_feasible N _
  x_nonneg t d u v := sendSeq_nonneg (bpRates_feasible N _).1 d u v
  x_le t d u v := sendSeq_le d u v
  x_avail t d u := by
    rw [sendSeq_sum (bpRates_feasible N _).1 (bpQSeq_nonneg N ha hQ₀ t u d)]
    exact min_le_left _ _
  update t v d h := by
    show (if v = d then _ else _) = _
    rw [ite_eq_right h]

theorem Run.ofArrivalsSeq_backpressure (ha : ∀ t v d, 0 ≤ a t v d) (had : ∀ t d, a t d d = 0)
    (hQ₀ : ∀ v d, 0 ≤ Q₀ v d) (hQ₀d : ∀ d, Q₀ d d = 0) :
    (Run.ofArrivalsSeq N ha had hQ₀ hQ₀d).Backpressure :=
  ⟨fun t μ' hμ' => bpRates_maxWeight N _ μ' hμ', fun t d u => by
    show _ ≤ ∑ v, sendSeq _ _ d u v
    rw [sendSeq_sum (bpRates_feasible N _).1 (bpQSeq_nonneg N ha hQ₀ t u d)]
    exact le_rfl⟩

/-- **Whole packets**: with whole-number capacities, initial backlogs and arrivals, every backlog
and every transmission of the sequential backpressure run is a whole number of packets. -/
theorem Run.ofArrivalsSeq_int (ha : ∀ t v d, 0 ≤ a t v d) (had : ∀ t d, a t d d = 0)
    (hQ₀ : ∀ v d, 0 ≤ Q₀ v d) (hQ₀d : ∀ d, Q₀ d d = 0) (hcap : ∀ u v, IsInt (N.cap u v))
    (haI : ∀ t v d, IsInt (a t v d)) (hQ₀I : ∀ v d, IsInt (Q₀ v d)) :
    ∀ t, (∀ v d, IsInt ((Run.ofArrivalsSeq N ha had hQ₀ hQ₀d).Q t v d)) ∧
      ∀ d u v, IsInt ((Run.ofArrivalsSeq N ha had hQ₀ hQ₀d).x t d u v) := by
  have hrate : ∀ Q : V → V → ℚ, ∀ d u v, IsInt (bpRates N Q d u v) := fun Q d u v => by
    unfold bpRates; split_ifs
    · exact hcap u v
    · exact IsInt.zero
  have hsend : ∀ Q : V → V → ℚ, (∀ v d, IsInt (Q v d)) →
      ∀ d u v, IsInt (sendSeq Q (bpRates N Q) d u v) := fun Q hQ d u v => by
    unfold sendSeq
    refine (hrate Q d u v).min (IsInt.zero.max ((hQ u d).sub ?_))
    unfold seqPre
    refine IsInt.sum _ fun j _ => ?_
    unfold seqRate; split_ifs
    · exact hrate Q _ _ _
    · exact IsInt.zero
  intro t
  induction t with
  | zero => exact ⟨hQ₀I, hsend _ hQ₀I⟩
  | succ t ih =>
    have hQ : ∀ v d, IsInt ((Run.ofArrivalsSeq N ha had hQ₀ hQ₀d).Q (t + 1) v d) := by
      intro v d
      show IsInt (bpQSeq N a Q₀ (t + 1) v d)
      simp only [bpQSeq]
      split_ifs
      · exact IsInt.zero
      · exact (((ih.1 v d).sub (IsInt.sum _ fun w _ => ih.2 d v w)).add
          (IsInt.sum _ fun u _ => ih.2 d u v)).add (haI t v d)
    exact ⟨hQ, hsend _ hQ⟩

end Construct

end General


/-! ### Instances: the mesh, the torus and the hypercube with `m` connections per link -/

section Instances

/-- Every pair of a grid shares in uniform traffic. -/
theorem uniform_props {k : ℕ} (hk : 2 ≤ k) :
    (∀ v d, 0 ≤ uniform k v d) ∧ ∀ v d, v ≠ d → 1 / ((k : ℚ) ^ 2 - 1) ≤ uniform k v d := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  refine ⟨fun v d => ?_, fun v d hvd => ?_⟩
  · unfold uniform; split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one hK.le
  · unfold uniform; rw [ite_eq_right hvd]

/-- **Backpressure on the mesh with `m` connections per link** (even `k ≥ 2`, uniform
traffic).  Let `θ = m · 8 (k² - 1) / k³`, the fluid optimum (`mesh_copies_uniform`).  A
backpressure run is stable under every load `ρ < θ`; no run of any scheduler keeps its backlog
bounded under a load `ρ > θ`. -/
theorem mesh_backpressure (k : ℕ) (hk : 2 ≤ k) (he : Even k) {m : ℕ} (hm : 0 < m)
    (r : Run ((meshNet k).copies m)) {ρ : ℚ} :
    (r.Backpressure → 0 ≤ ρ → ρ < m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) →
        (∀ t v d, v ≠ d → r.a t v d ≤ ρ * uniform k v d) → r.Stable) ∧
      ((∀ t v d, v ≠ d → r.a t v d = ρ * uniform k v d) → r.BoundedBacklog →
        ρ ≤ m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3)) := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  obtain ⟨hunn, hunc⟩ := uniform_props hk
  have hR := (mesh_routable k hk).copies m
  refine ⟨fun hr hρ hρθ harr => r.backpressure_optimal hr hR hR hunn hunn
    (div_pos one_pos hK) hunc (mul_pos hm' (div_pos (by linarith) (by positivity))) hρ hρθ harr,
    fun harr hb => ?_⟩
  have h := r.cut_ceiling harr hb (fun u : Fin k × Fin k => 2 * (u.1 : ℕ) < k)
  beta_reduce at h
  have e : ∀ u v : Fin k × Fin k,
      (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then ((meshNet k).copies m).cap u v else 0) =
        m * (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then (meshNet k).cap u v else 0) :=
    fun u v => by split_ifs <;> simp
  simp only [e, ← mul_sum] at h
  set D := ∑ s : Fin k × Fin k, ∑ d : Fin k × Fin k,
    (if 2 * (s.1 : ℕ) < k ∧ ¬ 2 * (d.1 : ℕ) < k then uniform k s d else 0)
  set Cc := ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
    (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then (meshNet k).cap u v else 0)
  have key : ρ / m * D ≤ Cc := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm']; linarith
  have := mesh_upper_of_cut k hk he key
  rw [div_le_iff₀ hm'] at this
  linarith

/-- The hop distance of the torus. -/
theorem torus_isHopDistance (k : ℕ) : IsHopDistance (torusNet k) torusDist :=
  ⟨fun d => by rw [torusDist_eq]; simp only [Nat.cast_eq_zero]; exact (torusHops_eq_zero d d).2 rfl,
    fun u v d hc => by
      have h := torusHops_le_of_cap hc d
      have : ((torusHops u d : ℕ) : ℚ) ≤ (torusHops v d : ℕ) + 1 := by exact_mod_cast h
      rw [torusDist_eq]; linarith⟩

/-- **Backpressure on the torus with `m` connections per link** (`k ≥ 3`, uniform traffic).
Let `θ` be `m` times `torus_uniform_opt`.  A backpressure run is stable under every load
`ρ < θ`; no run of any scheduler keeps its backlog bounded under a load `ρ > θ`. -/
theorem torus_backpressure (k : ℕ) (hk : 3 ≤ k) {m : ℕ} (hm : 0 < m)
    (r : Run ((torusNet k).copies m)) {ρ : ℚ} :
    (r.Backpressure → 0 ≤ ρ →
        ρ < m * (if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / (k : ℚ)) →
        (∀ t v d, v ≠ d → r.a t v d ≤ ρ * uniform k v d) → r.Stable) ∧
      ((∀ t v d, v ≠ d → r.a t v d = ρ * uniform k v d) → r.BoundedBacklog →
        ρ ≤ m * (if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / (k : ℚ))) := by
  have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  obtain ⟨hunn, hunc⟩ := uniform_props (k := k) (by omega)
  have hopt := (torus_uniform_opt k hk).1.1
  have hR := hopt.copies m
  have hθ : 0 < (if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / (k : ℚ)) := by
    split_ifs
    · exact div_pos (by linarith) (by positivity)
    · exact div_pos (by norm_num) (by linarith)
  refine ⟨fun hr hρ hρθ harr => r.backpressure_optimal hr hR hR hunn hunn
    (div_pos one_pos hK) hunc (mul_pos hm' hθ) hρ hρθ harr, fun harr hb => ?_⟩
  have hD : 0 < hopDemand (uniform k) torusDist := by
    rw [torus_hop_uniform]
    exact div_pos (mul_pos (by positivity) (ringTotal_pos (by omega))) hK
  exact r.copies_hop_ceiling harr hb (torus_isHopDistance k)
    (fun u v => by rw [torusDist_eq]; positivity) hD
    (by rw [torus_sum_cap (by omega)]; exact torus_uniform_hop k hk)

/-- The hop distance of the hypercube. -/
theorem cube_isHopDistance (n : ℕ) : IsHopDistance (cubeNet n) cubeDist :=
  ⟨fun d => by rw [cubeDist_eq]; simp only [Nat.cast_eq_zero]; exact (cubeHops_eq_zero d d).2 rfl,
    fun u v d hc => by
      have h := cubeHops_le_of_cap hc d
      have : ((cubeHops u d : ℕ) : ℚ) ≤ (cubeHops v d : ℕ) + 1 := by exact_mod_cast h
      rw [cubeDist_eq]; linarith⟩

/-- **Backpressure on the `n`-cube with `m` connections per link** (`n ≥ 1`, uniform traffic).
Let `θ = m · 4 (2ⁿ - 1) / 2ⁿ` (`cube_uniform_opt`).  A backpressure run is stable under every
load `ρ < θ`; no run of any scheduler keeps its backlog bounded under a load `ρ > θ`. -/
theorem cube_backpressure (n : ℕ) (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m)
    (r : Run ((cubeNet n).copies m)) {ρ : ℚ} :
    (r.Backpressure → 0 ≤ ρ → ρ < m * (4 * (2 ^ n - 1) / 2 ^ n) →
        (∀ t v d, v ≠ d → r.a t v d ≤ ρ * cubeUniform n v d) → r.Stable) ∧
      ((∀ t v d, v ≠ d → r.a t v d = ρ * cubeUniform n v d) → r.BoundedBacklog →
        ρ ≤ m * (4 * (2 ^ n - 1) / 2 ^ n)) := by
  have hP : (2 : ℚ) ≤ 2 ^ n := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hP1 : (0 : ℚ) < 2 ^ n - 1 := by linarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hunn : ∀ v d, 0 ≤ cubeUniform n v d := fun v d => by
    unfold cubeUniform; split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one hP1.le
  have hunc : ∀ v d, v ≠ d → 1 / ((2 : ℚ) ^ n - 1) ≤ cubeUniform n v d := fun v d hvd => by
    unfold cubeUniform; rw [ite_eq_right hvd]
  have hR := (cube_uniform_opt n hn).1.1.copies m
  refine ⟨fun hr hρ hρθ harr => r.backpressure_optimal hr hR hR hunn hunn
    (div_pos one_pos hP1) hunc (mul_pos hm' (div_pos (by linarith) (by positivity))) hρ hρθ harr,
    fun harr hb => ?_⟩
  have hD : 0 < hopDemand (cubeUniform n) cubeDist := by
    rw [cube_hop_uniform]
    have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
    exact div_pos (by positivity) (by positivity)
  exact r.copies_hop_ceiling harr hb (cube_isHopDistance n)
    (fun u v => by rw [cubeDist_eq]; positivity) hD
    (by rw [cube_sum_cap]; exact cube_uniform_hop n hn)

theorem meshAdj_symm {k : ℕ} (u v : Fin k × Fin k) : MeshAdj u v ↔ MeshAdj v u := by
  simp only [MeshAdj, LineAdj, Fin.ext_iff]; omega

/-- A vertex of the mesh has at most four neighbours: its capacity out is at most `8`. -/
theorem mesh_out_cap (k : ℕ) (v : Fin k × Fin k) : ∑ w, (meshNet k).cap v w ≤ 8 := by
  have one : ∀ (P : Fin k × Fin k → Prop) [DecidablePred P], (∀ a b, P a → P b → a = b) →
      ∑ w, (if P w then (1 : ℚ) else 0) ≤ 1 := by
    intro P _ hP
    rw [sum_boole]
    exact_mod_cast card_le_one.2 fun a ha b hb =>
      hP a b (by simpa using ha) (by simpa using hb)
  have hcap : ∀ w : Fin k × Fin k, (meshNet k).cap v w ≤ 2 *
      ((if (w.2 : ℕ) = v.2 ∧ (v.1 : ℕ) + 1 = w.1 then (1 : ℚ) else 0) +
        (if (w.2 : ℕ) = v.2 ∧ (w.1 : ℕ) + 1 = v.1 then (1 : ℚ) else 0) +
        (if (w.1 : ℕ) = v.1 ∧ (v.2 : ℕ) + 1 = w.2 then (1 : ℚ) else 0) +
        (if (w.1 : ℕ) = v.1 ∧ (w.2 : ℕ) + 1 = v.2 then (1 : ℚ) else 0)) := by
    intro w
    show (if MeshAdj v w then (2 : ℚ) else 0) ≤ _
    by_cases h : MeshAdj v w
    · rw [ite_eq_left h]
      simp only [MeshAdj, LineAdj, Fin.ext_iff] at h
      split_ifs <;> first | (exfalso; omega) | norm_num
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  calc ∑ w, (meshNet k).cap v w ≤ ∑ w : Fin k × Fin k, 2 *
        ((if (w.2 : ℕ) = v.2 ∧ (v.1 : ℕ) + 1 = w.1 then (1 : ℚ) else 0) +
          (if (w.2 : ℕ) = v.2 ∧ (w.1 : ℕ) + 1 = v.1 then (1 : ℚ) else 0) +
          (if (w.1 : ℕ) = v.1 ∧ (v.2 : ℕ) + 1 = w.2 then (1 : ℚ) else 0) +
          (if (w.1 : ℕ) = v.1 ∧ (w.2 : ℕ) + 1 = v.2 then (1 : ℚ) else 0)) :=
        sum_le_sum fun w _ => hcap w
    _ ≤ 2 * (1 + 1 + 1 + 1) := by
        rw [← mul_sum]
        simp only [sum_add_distrib]
        have h1 := one (fun w => (w.2 : ℕ) = v.2 ∧ (v.1 : ℕ) + 1 = w.1)
          fun a b ⟨h1, h2⟩ ⟨h3, h4⟩ => Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
        have h2 := one (fun w => (w.2 : ℕ) = v.2 ∧ (w.1 : ℕ) + 1 = v.1)
          fun a b ⟨h1, h2⟩ ⟨h3, h4⟩ => Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
        have h3 := one (fun w => (w.1 : ℕ) = v.1 ∧ (v.2 : ℕ) + 1 = w.2)
          fun a b ⟨h1, h2⟩ ⟨h3, h4⟩ => Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
        have h4 := one (fun w => (w.1 : ℕ) = v.1 ∧ (w.2 : ℕ) + 1 = v.2)
          fun a b ⟨h1, h2⟩ ⟨h3, h4⟩ => Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
        linarith
    _ = 8 := by norm_num

/-- The capacity into a vertex of the mesh is at most `8`. -/
theorem mesh_in_cap (k : ℕ) (v : Fin k × Fin k) : ∑ u, (meshNet k).cap u v ≤ 8 := by
  have e : ∀ u, (meshNet k).cap u v = (meshNet k).cap v u := fun u => by
    show (if MeshAdj u v then (2 : ℚ) else 0) = if MeshAdj v u then 2 else 0
    rw [if_congr (meshAdj_symm u v) rfl rfl]
  simp only [e]
  exact mesh_out_cap k v

/-- **Buffers for backpressure on the mesh** with `m` connections per link (`k ≥ 2`, uniform
traffic).  Let `θ = m · 8 (k² - 1) / k³` (the fluid optimum for even `k`).  Started empty, under
any load at most `(1 - δ) θ` (`0 < δ ≤ 1`) a backpressure run never holds more than
`b = 145 m k⁷ / (16 δ) + m` packets in any per-destination queue, and it delivers everything that
arrives except at most `k⁴ b`.  The buffer is linear in the number of connections and in
`1 / δ`; the constant is that of the drift argument, far above what simulation needs. -/
theorem mesh_buffer (k : ℕ) (hk : 2 ≤ k) {m : ℕ} (hm : 0 < m) {δ : ℚ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (r : Run ((meshNet k).copies m)) (hr : r.Backpressure)
    (h0 : ∀ v d, r.Q 0 v d = 0)
    (harr : ∀ t v d, v ≠ d →
      r.a t v d ≤ (1 - δ) * (m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3)) * uniform k v d) :
    r.FitsIn (145 * m * k ^ 7 / (16 * δ) + m) ∧
      ∀ t, ∑ s ∈ range t, r.arrived s - (k : ℚ) ^ 4 * (145 * m * k ^ 7 / (16 * δ) + m) ≤
        ∑ s ∈ range t, r.delivered s := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hk3 : (8 : ℚ) ≤ (k : ℚ) ^ 3 := by nlinarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hk3' : (0 : ℚ) < (k : ℚ) ^ 3 := by linarith
  set θ := (m : ℚ) * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]; exact mul_nonneg hm'.le (div_nonneg (by linarith) hk3'.le)
  obtain ⟨F⟩ := (mesh_routable k hk).copies m
  have F' := F.normalize
  set dem := fun v d => θ * uniform k v d with hdemdef
  -- the demand of a pair
  have hθu : ∀ v d : Fin k × Fin k, v ≠ d → θ * uniform k v d = 8 * m / k ^ 3 := fun v d hvd => by
    unfold uniform; rw [ite_eq_right hvd, hθdef]
    rw [show (m : ℚ) * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) * (1 / ((k : ℚ) ^ 2 - 1)) =
        8 * m / k ^ 3 * (((k : ℚ) ^ 2 - 1) * (1 / ((k : ℚ) ^ 2 - 1))) by ring,
      mul_one_div_cancel hK.ne', mul_one]
  have hdem0 : ∀ v d, 0 ≤ dem v d := fun v d => by
    simp only [hdemdef]
    exact mul_nonneg hθ0 ((uniform_props hk).1 v d)
  have hdemm : ∀ v d, dem v d ≤ m := fun v d => by
    simp only [hdemdef]
    by_cases hvd : v = d
    · subst hvd; simp [uniform]
    · rw [hθu v d hvd, div_le_iff₀ hk3']; nlinarith
  -- the slack
  set ε := 8 * m * δ / (k : ℚ) ^ 3 with hεdef
  have hε : 0 < ε := div_pos (by positivity) hk3'
  have harr' : ∀ t v d, v ≠ d → r.a t v d + ε ≤ dem v d := fun t v d hvd => by
    have h := harr t v d hvd
    simp only [hdemdef]
    rw [hθu v d hvd]
    rw [show (1 - δ) * θ * uniform k v d = (1 - δ) * (θ * uniform k v d) by ring,
      hθu v d hvd] at h
    rw [hεdef]
    have : (1 - δ) * (8 * m / k ^ 3) + 8 * m * δ / k ^ 3 = 8 * m / (k : ℚ) ^ 3 := by
      ring
    linarith
  obtain ⟨hfit, hdel⟩ := r.backpressure_fitsIn hr F' hdem0 hε harr' h0
  -- the drift constant
  have hout : ∀ v, ∑ w, ((meshNet k).copies m).cap v w ≤ 8 * m := fun v => by
    simp only [Net.copies_cap, ← mul_sum]
    nlinarith [mesh_out_cap k v]
  have hin : ∀ v, ∑ u, ((meshNet k).copies m).cap u v ≤ 8 * m := fun v => by
    simp only [Net.copies_cap, ← mul_sum]
    nlinarith [mesh_in_cap k v]
  have hB : Run.driftConst ((meshNet k).copies m) dem ≤ 145 * (m : ℚ) ^ 2 * (k : ℚ) ^ 4 := by
    calc Run.driftConst ((meshNet k).copies m) dem ≤
          ∑ _d : Fin k × Fin k, ∑ _v : Fin k × Fin k, (145 * (m : ℚ) ^ 2) := by
          refine sum_le_sum fun d _ => sum_le_sum fun v _ => ?_
          have h1 : 0 ≤ ∑ w, ((meshNet k).copies m).cap v w :=
            sum_nonneg fun w _ => ((meshNet k).copies m).cap_nonneg v w
          have h2 : 0 ≤ ∑ u, ((meshNet k).copies m).cap u v :=
            sum_nonneg fun u _ => ((meshNet k).copies m).cap_nonneg u v
          have h3 := hout v
          have h4 := hin v
          have h5 := hdemm v d
          have h6 := hdem0 v d
          nlinarith
      _ = 145 * (m : ℚ) ^ 2 * (k : ℚ) ^ 4 := by
          simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- the buffer
  have hb : Run.driftConst ((meshNet k).copies m) dem / (2 * ε) + ε ≤
      145 * m * k ^ 7 / (16 * δ) + m := by
    have e1 : 145 * (m : ℚ) ^ 2 * k ^ 4 / (2 * ε) = 145 * m * k ^ 7 / (16 * δ) := by
      rw [hεdef, show (2 : ℚ) * (8 * m * δ / k ^ 3) = 16 * m * δ / k ^ 3 by ring,
        div_div_eq_mul_div, div_eq_div_iff (mul_pos (mul_pos (by norm_num) hm') hδ).ne'
          (mul_pos (by norm_num) hδ).ne']
      ring
    have e2 : ε ≤ m := by
      rw [hεdef, div_le_iff₀ hk3']; nlinarith
    have e3 := div_le_div_of_nonneg_right hB (show (0 : ℚ) ≤ 2 * ε by linarith)
    linarith
  refine ⟨fun t v d => (hfit t v d).trans hb, fun t => ?_⟩
  have h := hdel t
  have hc : ((Fintype.card (Fin k × Fin k) : ℕ) : ℚ) ^ 2 = (k : ℚ) ^ 4 := by
    simp only [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  rw [hc] at h
  have := mul_le_mul_of_nonneg_left hb (show (0 : ℚ) ≤ (k : ℚ) ^ 4 by positivity)
  linarith

/-- **Whole packets on the mesh with `m` connections per link** (`k ≥ 2`, uniform traffic).
Let `θ = m · 8 (k² - 1) / k³`.  For every arrival sequence of whole packets at most `A` per
queue and slot, within a leaky bucket of rate `ρ < θ` times the uniform traffic and burst `σ`
(over every window of `W` slots at most `W ρ / (k² - 1) + σ` packets from `v` for `d`), the
backpressure run with sequential sends moves whole packets only, keeps its backlog bounded and
delivers everything that arrives, up to a constant. -/
theorem mesh_backpressure_packets (k : ℕ) (hk : 2 ≤ k) {m : ℕ} (hm : 0 < m)
    (a : ℕ → Fin k × Fin k → Fin k × Fin k → ℚ) (ha : ∀ t v d, 0 ≤ a t v d)
    (had : ∀ t d, a t d d = 0) (haI : ∀ t v d, IsInt (a t v d)) {A : ℚ}
    (hA : ∀ t v d, a t v d ≤ A) {ρ σ : ℚ} (hρθ : ρ < m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3))
    (hσ : 0 ≤ σ)
    (hburst : ∀ t W v d, v ≠ d → ∑ s ∈ range W, a (t + s) v d ≤ W * ρ * uniform k v d + σ) :
    ∃ r : Run ((meshNet k).copies m), r.Backpressure ∧ (∀ t v d, r.a t v d = a t v d) ∧
      (∀ t, (∀ v d, IsInt (r.Q t v d)) ∧ ∀ d u v, IsInt (r.x t d u v)) ∧ r.Stable := by
  have : Nonempty (Fin k × Fin k) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  set θ := (m : ℚ) * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]; exact mul_nonneg hm'.le (div_nonneg (by linarith) (by positivity))
  obtain ⟨hunn, -⟩ := uniform_props hk
  have hA0 : 0 ≤ A := (ha 0 (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨0, by omega⟩)).trans
    (hA _ _ _)
  let r := Run.ofArrivalsSeq ((meshNet k).copies m) (a := a) (Q₀ := fun _ _ => 0) ha had
    (fun _ _ => le_rfl) (fun _ => rfl)
  have hr := Run.ofArrivalsSeq_backpressure ((meshNet k).copies m) (a := a) (Q₀ := fun _ _ => 0)
    ha had (fun _ _ => le_rfl) (fun _ => rfl)
  have hint := Run.ofArrivalsSeq_int ((meshNet k).copies m) (a := a) (Q₀ := fun _ _ => 0) ha had
    (fun _ _ => le_rfl) (fun _ => rfl) (fun u v => by
      show IsInt ((m : ℚ) * (if MeshAdj u v then 2 else 0))
      split_ifs
      · exact ⟨2 * m, by push_cast; ring⟩
      · exact ⟨0, by simp⟩) haI (fun _ _ => IsInt.zero)
  refine ⟨r, hr, fun _ _ _ => rfl, hint, ?_⟩
  obtain ⟨F⟩ := (mesh_routable k hk).copies m
  have hu : ∀ v d : Fin k × Fin k, v ≠ d → uniform k v d = 1 / ((k : ℚ) ^ 2 - 1) :=
    fun v d hvd => by unfold uniform; rw [ite_eq_right hvd]
  refine r.backpressure_stable_bursty hr (dem := fun v d => θ * uniform k v d) ⟨F.normalize⟩
    (fun v d => mul_nonneg hθ0 (hunn v d)) (D := θ / ((k : ℚ) ^ 2 - 1))
    (div_nonneg hθ0 hK.le) (fun v d => ?_) hA0 hA (ε := (θ - ρ) / ((k : ℚ) ^ 2 - 1))
    (div_pos (by linarith) hK) hσ (fun t W v d hvd => ?_)
  · by_cases hvd : v = d
    · subst hvd; simp only [uniform, ite_true, mul_zero]; exact div_nonneg hθ0 hK.le
    · rw [hu v d hvd, mul_one_div]
  · have h := hburst t W v d hvd
    rw [hu v d hvd] at h
    show ∑ s ∈ range W, a (t + s) v d ≤ W * (θ * uniform k v d - (θ - ρ) / ((k : ℚ) ^ 2 - 1)) + σ
    rw [hu v d hvd]
    have e : (W : ℚ) * (θ * (1 / ((k : ℚ) ^ 2 - 1)) - (θ - ρ) / ((k : ℚ) ^ 2 - 1)) =
        W * ρ * (1 / ((k : ℚ) ^ 2 - 1)) := by ring
    linarith

/-- **Not vacuous**: on the mesh with `m` connections per link, for every load
`0 ≤ ρ < m · 8 (k² - 1) / k³` there is a backpressure run, from the empty network, with
arrivals exactly `ρ` times the uniform traffic in every slot, and it is stable. -/
theorem mesh_backpressure_exists (k : ℕ) (hk : 2 ≤ k) (he : Even k) {m : ℕ} (hm : 0 < m)
    {ρ : ℚ} (hρ : 0 ≤ ρ) (hρθ : ρ < m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3)) :
    ∃ r : Run ((meshNet k).copies m), r.Backpressure ∧
      (∀ t v d, r.a t v d = ρ * uniform k v d) ∧ r.Stable := by
  have : Nonempty (Fin k × Fin k) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨hunn, -⟩ := uniform_props hk
  let r := Run.ofArrivals ((meshNet k).copies m) (a := fun _ v d => ρ * uniform k v d)
    (Q₀ := fun _ _ => 0) (fun _ v d => mul_nonneg hρ (hunn v d))
    (fun _ d => by simp [uniform]) (fun _ _ => le_rfl) (fun _ => rfl)
  have hr := Run.ofArrivals_backpressure ((meshNet k).copies m)
    (a := fun _ v d => ρ * uniform k v d) (Q₀ := fun _ _ => 0)
    (fun _ v d => mul_nonneg hρ (hunn v d)) (fun _ d => by simp [uniform]) (fun _ _ => le_rfl)
    (fun _ => rfl)
  exact ⟨r, hr, fun _ _ _ => rfl,
    (mesh_backpressure k hk he hm r).1 hr hρ hρθ fun _ _ _ _ => le_rfl⟩

end Instances

end Fluid

end AsyncLean
