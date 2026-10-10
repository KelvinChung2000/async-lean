/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure

/-!
# Backpressure under random arrivals

`Fluid.Run.backpressure_stable_bursty` covers every arrival sequence within a leaky bucket.  Random
arrivals such as Poisson ones have unbounded bursts, so their sample paths need not stay in any
bucket; their stability is a statement in expectation.  This file proves it: **under random
arrivals whose mean, given the past, stays `ε` below a traffic routable at throughput `1`, and
whose total per slot has a finite second moment, the expected backlog of backpressure stays
bounded on average over time** (`Fluid.backpressure_strongly_stable`), the standard notion of
stochastic stability (strong stability).

## The model

* A random run is a family `R : Ω → Run N` of backpressure runs, one per outcome `ω`; the
  scheduler acts on each sample path.
* An **expectation** (`Fluid.Expect Ω K`) is a functional `E` on the random quantities `Ω → ℚ`,
  with values in an ordered field `K` (the reals, for instance), that is linear, monotone and
  normalised on a class of integrable quantities closed under sums and scalar multiples.  The
  Lebesgue expectation of a probability space is one; nothing else about it is used.
* The arrivals given the past (`hmean`): `E[Q t v d * a t v d] ≤ (dem v d - ε) E[Q t v d]` — what
  arrivals independent of the backlogs with mean at most `dem v d - ε` give (Poisson arrivals of
  rate `dem v d - ε`, for instance); and `E[(∑ a t)²] ≤ A₂` (a finite second moment of the total
  arrivals of a slot, as Poisson arrivals have).

## Main results

* `Run.drift_random` : the drift of one sample path, with the total arrivals of the slot in place
  of a bound on them.
* `expected_drift` : **the expected drift**: `E[energy (t + 1)] ≤ E[energy t] + B - 2 ε E[backlog t]`.
* `backpressure_strongly_stable` : `2 ε ∑_{t < T} E[backlog t] ≤ E[energy 0] + T B`: the
  time-average expected backlog is at most `B / (2 ε)` plus a term vanishing in `T`.
-/

namespace AsyncLean

namespace Fluid

open Finset

/-- An **expectation** on the outcomes `Ω`, with values in the ordered field `K`: linear,
monotone and normalised on the integrable random quantities `Int`. -/
structure Expect (Ω K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The integrable random quantities. -/
  Int : (Ω → ℚ) → Prop
  /-- The expectation. -/
  E : (Ω → ℚ) → K
  int_add : ∀ {f g : Ω → ℚ}, Int f → Int g → Int fun ω => f ω + g ω
  int_smul : ∀ (c : ℚ) {f : Ω → ℚ}, Int f → Int fun ω => c * f ω
  int_const : ∀ c : ℚ, Int fun _ => c
  E_add : ∀ {f g : Ω → ℚ}, Int f → Int g → E (fun ω => f ω + g ω) = E f + E g
  E_smul : ∀ (c : ℚ) {f : Ω → ℚ}, Int f → E (fun ω => c * f ω) = c * E f
  E_const : ∀ c : ℚ, E (fun _ => c) = c
  E_mono : ∀ {f g : Ω → ℚ}, Int f → Int g → (∀ ω, f ω ≤ g ω) → E f ≤ E g

namespace Expect

variable {Ω K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (X : Expect Ω K)

theorem int_sum {ι : Type*} (s : Finset ι) {f : ι → Ω → ℚ} (h : ∀ i ∈ s, X.Int (f i)) :
    X.Int (fun ω => ∑ i ∈ s, f i ω) ∧ X.E (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, X.E (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    exact ⟨X.int_const 0, by rw [X.E_const]; simp⟩
  | insert i s hi ih =>
    obtain ⟨h1, h2⟩ := ih fun j hj => h j (mem_insert_of_mem hj)
    have hfi := h i (mem_insert_self i s)
    simp only [sum_insert hi]
    exact ⟨X.int_add hfi h1, by rw [X.E_add hfi h1, h2]⟩

theorem int_sub {f g : Ω → ℚ} (hf : X.Int f) (hg : X.Int g) :
    X.Int (fun ω => f ω - g ω) ∧ X.E (fun ω => f ω - g ω) = X.E f - X.E g := by
  have hg' := X.int_smul (-1) hg
  have e : (fun ω => f ω - g ω) = fun ω => f ω + (-1) * g ω := funext fun ω => by ring
  rw [e]
  refine ⟨X.int_add hf hg', ?_⟩
  rw [X.E_add hf hg', X.E_smul (-1) hg]
  push_cast; ring

theorem E_zero_of {f : Ω → ℚ} (h : ∀ ω, f ω = 0) : X.E f = 0 := by
  have : f = fun _ => (0 : ℚ) := funext h
  rw [this, X.E_const]; simp

theorem E_nonneg {f : Ω → ℚ} (hf : X.Int f) (h : ∀ ω, 0 ≤ f ω) : 0 ≤ X.E f := by
  have := X.E_mono (X.int_const 0) hf h
  rwa [X.E_const, Rat.cast_zero] at this

/-- **The expectation of a finite probability space**: weights `p ω ≥ 0` summing to `1`, every
quantity integrable.  (Not vacuous: for instance arrivals that are `0` or `2` with probability
`1/2` each, independently of the past, have mean `1` and second moment `2`.) -/
def ofWeights [Fintype Ω] (p : Ω → ℚ) (hp : ∀ ω, 0 ≤ p ω) (h1 : ∑ ω, p ω = 1) : Expect Ω ℚ where
  Int _ := True
  E f := ∑ ω, p ω * f ω
  int_add _ _ := trivial
  int_smul _ _ _ := trivial
  int_const _ := trivial
  E_add _ _ := by simp only [mul_add, sum_add_distrib]
  E_smul c f _ := by
    simp only [Rat.cast_id, mul_sum]
    exact sum_congr rfl fun ω _ => by ring
  E_const c := by rw [← sum_mul, h1, one_mul, Rat.cast_id]
  E_mono _ _ h := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hp ω)

end Expect

namespace Run

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Net V} (r : Run N)

/-- The total arrivals of slot `t`. -/
def totalArr (t : ℕ) : ℚ := ∑ d, ∑ v, r.a t v d

/-- The capacity part of the drift constant. -/
def capConst (N : Net V) : ℚ :=
  ∑ _d : V, ∑ v : V, ((∑ w, N.cap v w) ^ 2 + 2 * (∑ u, N.cap u v) ^ 2)

/-- **The drift of one sample path**, with the total arrivals of the slot in place of a bound on
the arrivals. -/
theorem drift_random (hr : r.Backpressure) {dem : V → V → ℚ} (F : Flow N dem 1) (t : ℕ) :
    energy (r.Q (t + 1)) ≤ energy (r.Q t) + capConst N +
      2 * (Fintype.card V : ℚ) ^ 2 * r.totalArr t ^ 2 -
      2 * ∑ d, ∑ v, (r.Q t v d * dem v d - r.Q t v d * r.a t v d) := by
  have hA : ∀ v d, r.a t v d ≤ r.totalArr t := fun v d =>
    (single_le_sum (f := fun v => r.a t v d) (fun v _ => r.a_nonneg t v d) (mem_univ v)).trans
      (single_le_sum (f := fun d => ∑ v, r.a t v d)
        (fun d _ => sum_nonneg fun v _ => r.a_nonneg t v d) (mem_univ d))
  have h := r.drift_gen hr F t hA
  have hA0 : 0 ≤ r.totalArr t := sum_nonneg fun d _ => sum_nonneg fun v _ => r.a_nonneg t v d
  have hc : driftConst N (fun _ _ => r.totalArr t) ≤
      capConst N + 2 * (Fintype.card V : ℚ) ^ 2 * r.totalArr t ^ 2 := by
    have e : 2 * (Fintype.card V : ℚ) ^ 2 * r.totalArr t ^ 2 =
        ∑ _d : V, ∑ _v : V, 2 * r.totalArr t ^ 2 := by
      simp only [sum_const, card_univ, nsmul_eq_mul]; ring
    rw [e, capConst, ← sum_add_distrib]
    refine sum_le_sum fun d _ => ?_
    rw [← sum_add_distrib]
    refine sum_le_sum fun v _ => ?_
    nlinarith [sq_nonneg (∑ u, N.cap u v - r.totalArr t)]
  have e2 : ∑ d, ∑ v, r.Q t v d * (dem v d - r.a t v d) =
      ∑ d, ∑ v, (r.Q t v d * dem v d - r.Q t v d * r.a t v d) :=
    sum_congr rfl fun d _ => sum_congr rfl fun v _ => by ring
  linarith

end Run

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Net V}
  {Ω K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The expected drift** of backpressure under random arrivals whose mean given the past stays
`ε` below `dem` (routable at throughput `1`) and whose total per slot has second moment at most
`A₂`. -/
theorem expected_drift (X : Expect Ω K) (R : Ω → Run N) (hr : ∀ ω, (R ω).Backpressure)
    {dem : V → V → ℚ} (F : Flow N dem 1) {ε : ℚ} {A₂ : K}
    (hQ : ∀ t v d, X.Int fun ω => (R ω).Q t v d)
    (hQa : ∀ t v d, X.Int fun ω => (R ω).Q t v d * (R ω).a t v d)
    (hE : ∀ t, X.Int fun ω => energy ((R ω).Q t))
    (hA : ∀ t, X.Int fun ω => (R ω).totalArr t ^ 2)
    (hA₂ : ∀ t, X.E (fun ω => (R ω).totalArr t ^ 2) ≤ A₂)
    (hmean : ∀ t v d, v ≠ d →
      X.E (fun ω => (R ω).Q t v d * (R ω).a t v d) ≤ ((dem v d - ε : ℚ) : K) *
        X.E (fun ω => (R ω).Q t v d)) (t : ℕ) :
    X.E (fun ω => energy ((R ω).Q (t + 1))) ≤ X.E (fun ω => energy ((R ω).Q t)) +
      ((Run.capConst N : ℚ) : K) + 2 * (Fintype.card V : K) ^ 2 * A₂ -
      2 * (ε : K) * X.E (fun ω => backlog ((R ω).Q t)) := by
  -- the integrable pieces
  set G : Ω → ℚ := fun ω => ∑ d, ∑ v, ((R ω).Q t v d * dem v d - (R ω).Q t v d * (R ω).a t v d)
  have hterm : ∀ d v, X.Int (fun ω => (R ω).Q t v d * dem v d - (R ω).Q t v d * (R ω).a t v d) ∧
      X.E (fun ω => (R ω).Q t v d * dem v d - (R ω).Q t v d * (R ω).a t v d) =
        (dem v d : K) * X.E (fun ω => (R ω).Q t v d) -
          X.E (fun ω => (R ω).Q t v d * (R ω).a t v d) := fun d v => by
    have h1 : X.Int fun ω => (R ω).Q t v d * dem v d := by
      have := X.int_smul (dem v d) (hQ t v d)
      simpa [mul_comm] using this
    have e1 : X.E (fun ω => (R ω).Q t v d * dem v d) = (dem v d : K) * X.E (fun ω => (R ω).Q t v d) := by
      rw [← X.E_smul (dem v d) (hQ t v d)]
      congr 1; funext ω; ring
    obtain ⟨hi, he⟩ := X.int_sub h1 (hQa t v d)
    exact ⟨hi, by rw [he, e1]⟩
  have hinner : ∀ d, X.Int (fun ω => ∑ v, ((R ω).Q t v d * dem v d -
      (R ω).Q t v d * (R ω).a t v d)) ∧
      X.E (fun ω => ∑ v, ((R ω).Q t v d * dem v d - (R ω).Q t v d * (R ω).a t v d)) =
        ∑ v, X.E (fun ω => (R ω).Q t v d * dem v d - (R ω).Q t v d * (R ω).a t v d) :=
    fun d => X.int_sum univ fun v _ => (hterm d v).1
  obtain ⟨hG, hGE⟩ := X.int_sum univ (f := fun d ω => ∑ v, ((R ω).Q t v d * dem v d -
      (R ω).Q t v d * (R ω).a t v d)) fun d _ => (hinner d).1
  -- the right-hand side of the sample-path drift
  set C := Run.capConst N
  set n2 := (Fintype.card V : ℚ) ^ 2
  have hR1 := X.int_add (hE t) (X.int_const C)
  have hR2 := X.int_add hR1 (X.int_smul (2 * n2) (hA t))
  obtain ⟨hR3, hR3E⟩ := X.int_sub hR2 (X.int_smul 2 hG)
  have hmono := X.E_mono (hE (t + 1)) hR3 fun ω => by
    have := (R ω).drift_random (hr ω) F t
    simp only [n2, C]
    linarith
  rw [hR3E, X.E_add hR1 (X.int_smul (2 * n2) (hA t)), X.E_add (hE t) (X.int_const C),
    X.E_const, X.E_smul (2 * n2) (hA t), X.E_smul 2 hG] at hmono
  -- the backlog
  obtain ⟨hS, hSE⟩ : X.Int (fun ω => backlog ((R ω).Q t)) ∧
      X.E (fun ω => backlog ((R ω).Q t)) = ∑ d, ∑ v, X.E (fun ω => (R ω).Q t v d) := by
    have hin : ∀ d, X.Int (fun ω => ∑ v, (R ω).Q t v d) ∧
        X.E (fun ω => ∑ v, (R ω).Q t v d) = ∑ v, X.E (fun ω => (R ω).Q t v d) :=
      fun d => X.int_sum univ fun v _ => hQ t v d
    obtain ⟨h1, h2⟩ := X.int_sum univ (f := fun d ω => ∑ v, (R ω).Q t v d) fun d _ => (hin d).1
    refine ⟨h1, ?_⟩
    simp only [backlog]
    rw [h2]
    exact sum_congr rfl fun d _ => (hin d).2
  -- the slack
  have hslack : (ε : K) * X.E (fun ω => backlog ((R ω).Q t)) ≤ X.E G := by
    rw [hSE, hGE, mul_sum]
    refine sum_le_sum fun d _ => ?_
    rw [(hinner d).2, mul_sum]
    refine sum_le_sum fun v _ => ?_
    rw [(hterm d v).2]
    by_cases hvd : v = d
    · subst hvd
      have h0 : X.E (fun ω => (R ω).Q t v v) = 0 := X.E_zero_of fun ω => (R ω).Q_dest t v
      have h0' : X.E (fun ω => (R ω).Q t v v * (R ω).a t v v) = 0 :=
        X.E_zero_of fun ω => by rw [(R ω).Q_dest, zero_mul]
      rw [h0, h0']; simp
    · have := hmean t v d hvd
      push_cast at this ⊢
      linarith
  have hA2 := hA₂ t
  have hn : (0 : K) ≤ 2 * (Fintype.card V : K) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hA2 hn
  have hGdef : X.E G = X.E (fun ω => ∑ d, ∑ v, ((R ω).Q t v d * dem v d -
      (R ω).Q t v d * (R ω).a t v d)) := rfl
  rw [hGdef] at hslack
  simp only [n2, C] at hmono
  have hc : ∀ x : ℚ, ((x ^ 2 : ℚ) : K) = (x : K) ^ 2 := fun x => by
    rw [sq, Rat.cast_mul, sq]
  simp only [hc, Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat] at hmono
  linarith

/-- **Backpressure is strongly stable under random arrivals.**  Under the hypotheses of
`expected_drift` (arrivals with mean, given the past, `ε > 0` below a traffic routable at
throughput `1`, and total arrivals per slot with second moment at most `A₂`, Poisson arrivals for
instance), `2 ε ∑_{t < T} E[backlog t] ≤ E[energy 0] + T B` with
`B = capConst N + 2 |V|² A₂`: the expected backlog, averaged over time, is at most `B / (2 ε)`
up to a term vanishing as `T` grows. -/
theorem backpressure_strongly_stable (X : Expect Ω K) (R : Ω → Run N)
    (hr : ∀ ω, (R ω).Backpressure) {dem : V → V → ℚ} (hRt : Routable N dem 1) {ε : ℚ} {A₂ : K}
    (hQ : ∀ t v d, X.Int fun ω => (R ω).Q t v d)
    (hQa : ∀ t v d, X.Int fun ω => (R ω).Q t v d * (R ω).a t v d)
    (hE : ∀ t, X.Int fun ω => energy ((R ω).Q t))
    (hA : ∀ t, X.Int fun ω => (R ω).totalArr t ^ 2)
    (hA₂ : ∀ t, X.E (fun ω => (R ω).totalArr t ^ 2) ≤ A₂)
    (hmean : ∀ t v d, v ≠ d →
      X.E (fun ω => (R ω).Q t v d * (R ω).a t v d) ≤ ((dem v d - ε : ℚ) : K) *
        X.E (fun ω => (R ω).Q t v d)) (T : ℕ) :
    2 * (ε : K) * ∑ t ∈ range T, X.E (fun ω => backlog ((R ω).Q t)) ≤
      X.E (fun ω => energy ((R ω).Q 0)) +
        T * (((Run.capConst N : ℚ) : K) + 2 * (Fintype.card V : K) ^ 2 * A₂) := by
  obtain ⟨F⟩ := hRt
  set B : K := ((Run.capConst N : ℚ) : K) + 2 * (Fintype.card V : K) ^ 2 * A₂
  have hstep := expected_drift X R hr F hQ hQa hE hA hA₂ hmean
  have hT : ∀ T, X.E (fun ω => energy ((R ω).Q T)) + 2 * (ε : K) *
      ∑ t ∈ range T, X.E (fun ω => backlog ((R ω).Q t)) ≤
      X.E (fun ω => energy ((R ω).Q 0)) + T * B := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have := hstep T
      rw [sum_range_succ]
      push_cast
      linarith
  have h0 : 0 ≤ X.E (fun ω => energy ((R ω).Q T)) :=
    X.E_nonneg (hE T) fun ω => sum_nonneg fun d _ => sum_nonneg fun v _ => sq_nonneg _
  linarith [hT T]

end Fluid

end AsyncLean
