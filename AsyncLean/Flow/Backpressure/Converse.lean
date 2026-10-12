/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure.Model

/-!
# Backpressure, part 5: the converse for every scheduler

The traffic a run carries in `T` slots is a flow in `T` copies of the network (`Run.totalFlow`),
so a run with a bounded backlog respects every potential bound of the fluid model
(`Run.potential_bound`, `Run.cut_bound`, `Run.hop_bound`, and `Run.potentialFeasibleOn`
for runs restricted to some links): no scheduler beats the fluid optimum.
-/

namespace AsyncLean

namespace Fluid

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Run

variable {N : Net V} (r : Run N)

/-! ### The converse: no scheduler beats the fluid model -/

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

/-- **The potential bound**, for every scheduler: if the arrivals are `ρ * dem` in every slot
and the backlog stays at most `C`, the load respects every potential bound of the fluid model
with a bounded potential `0 ≤ φ ≤ M`: `ρ * ∑ s d, dem s d * φ d s ≤ ∑ u v, cap u v * len u v`. -/
theorem potential_bound_on {dem : V → V → ℚ} {ρ : ℚ}
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

/-- **The potential bound**, for every scheduler: if the arrivals are `ρ * dem` in every slot
and the backlog stays bounded, the load respects every potential bound of the fluid model with
a bounded potential `0 ≤ φ ≤ M`: `ρ * ∑ s d, dem s d * φ d s ≤ ∑ u v, cap u v * len u v`. -/
theorem potential_bound {dem : V → V → ℚ} {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    (len : V → V → ℚ) (hlen : ∀ u v, 0 ≤ len u v)
    (φ : V → V → ℚ) (hφd : ∀ d, φ d d = 0)
    (hφ : ∀ d u v, 0 < N.cap u v → φ d u - φ d v ≤ len u v)
    (hφ0 : ∀ d v, 0 ≤ φ d v) {M : ℚ} (hM : ∀ d v, φ d v ≤ M) :
    ρ * ∑ s, ∑ d, dem s d * φ d s ≤ ∑ u, ∑ v, N.cap u v * len u v :=
  r.potential_bound_on harr hb (S := fun _ _ _ => True) (fun _ _ _ _ _ => trivial) len hlen φ
    hφd (fun d u v _ hc => hφ d u v hc) hφ0 hM

/-- **A stable run moving traffic only on `S` respects every potential bound on `S`**, as a flow
supported on `S` does: every dual certificate of the fluid model bounds it. -/
theorem potentialFeasibleOn {dem : V → V → ℚ} {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    {S : V → V → V → Prop} (hS : ∀ t d u v, 0 < r.x t d u v → S d u v) :
    PotentialFeasibleOn N S dem ρ := fun len φ hlen hφd hφ hφ0 =>
  r.potential_bound_on harr hb hS len hlen φ hφd hφ hφ0 (M := ∑ a, ∑ b, φ a b) fun d v =>
    (single_le_sum (f := fun b => φ d b) (fun b _ => hφ0 d b) (mem_univ v)).trans
      (single_le_sum (f := fun a => ∑ b, φ a b) (fun a _ => sum_nonneg fun b _ => hφ0 a b)
        (mem_univ d))

/-- **The cut bound**, for every scheduler: a run that keeps its backlog bounded under the load
`ρ * dem` carries across every cut at most the cut's capacity. -/
theorem cut_bound {dem : V → V → ℚ} {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    (S : V → Prop) [DecidablePred S] :
    ρ * ∑ s, ∑ d, (if S s ∧ ¬ S d then dem s d else 0) ≤
      ∑ u, ∑ v, if S u ∧ ¬ S v then N.cap u v else 0 := by
  have key := r.potential_bound harr hb (fun u v => if S u ∧ ¬ S v then 1 else 0)
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

/-- **The hop bound**, for every scheduler: a run that keeps its backlog bounded under the load
`ρ * dem` has `ρ * ∑ s d, dem s d * dist s d ≤ ∑ u v, cap u v` for every nonnegative hop
distance. -/
theorem hop_bound {dem : V → V → ℚ} {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    {dist : V → V → ℚ} (hd : IsHopDistance N dist) (hd0 : ∀ u v, 0 ≤ dist u v) :
    ρ * hopDemand dem dist ≤ ∑ u, ∑ v, N.cap u v := by
  have hM : ∀ d v, dist v d ≤ ∑ a, ∑ b, dist a b := fun d v =>
    (single_le_sum (f := fun b => dist v b) (fun b _ => hd0 v b) (mem_univ d)).trans
      (single_le_sum (f := fun a => ∑ b, dist a b) (fun a _ => sum_nonneg fun b _ => hd0 a b)
        (mem_univ v))
  have := r.potential_bound harr hb (fun _ _ => 1) (fun _ _ => zero_le_one)
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

/-- **The hop bound is the optimum on symmetric networks.**  If the hop bound is tight for
`dem` (`θ * hopDemand dem dist = ∑ cap`, as on the torus and the hypercube), a run on `m` copies
of the network that keeps its backlog bounded under `ρ * dem` has `ρ ≤ m * θ`. -/
theorem copies_hop_bound {m : ℕ} (r : Run (N.copies m)) {dem : V → V → ℚ} {ρ θ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hb : r.BoundedBacklog)
    {dist : V → V → ℚ} (hd : IsHopDistance N dist) (hd0 : ∀ u v, 0 ≤ dist u v)
    (hD : 0 < hopDemand dem dist) (htight : θ * hopDemand dem dist = ∑ u, ∑ v, N.cap u v) :
    ρ ≤ m * θ := by
  have h := r.hop_bound harr hb (hd.copies m) hd0
  simp only [Net.copies_cap, ← mul_sum] at h
  rw [← htight] at h
  have : ρ * hopDemand dem dist ≤ (m * θ) * hopDemand dem dist := by linarith
  exact le_of_mul_le_mul_right this hD

end Run

end General

end Fluid

end AsyncLean
