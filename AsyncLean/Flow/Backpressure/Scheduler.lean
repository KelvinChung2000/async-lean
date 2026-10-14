/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure.Model

/-!
# Backpressure, part 6: the scheduler exists

The greedy rates (`bpRates`: every link, in full, to a destination of largest backlog
difference) are max-weight (`bpRates_maxWeight`).  With proportional sends (`sendAll`) they give
a backpressure run for every arrival sequence (`Run.ofArrivals`); with sequential sends
(`sendSeq`) a run that moves whole packets only (`Run.ofArrivalsSeq`, `Run.ofArrivalsSeq_int`).
-/

namespace AsyncLean

namespace Fluid

open Finset

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

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

end Fluid

end AsyncLean
