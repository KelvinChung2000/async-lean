/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fairness: from "can" to "will"

`LTS.Live` says every action *can* always happen again.  Under a *fair* scheduler it *will*
happen, infinitely often.  This file formalises infinite runs and strong fairness, and proves:

* `Run.infOften_label_of_live` — in a system with finitely many reachable states, every live
  action is performed infinitely often along every strongly fair run;
* `Run.infOften_external_of_progress` — if an external action can always eventually be
  performed, every strongly fair run performs infinitely many external actions: under
  fairness there is no livelock, even when internal cycles exist;
* `Run.infOften_external_of_livelockFree` — livelock freedom gives infinitely many external
  actions along *every* run, fair or not.

A run is *strongly fair* when every transition `s —l→ s'` whose source is visited
infinitely often is itself taken infinitely often (strong fairness over transitions, the
standard assumption for finite-state systems).
-/

namespace AsyncLean

namespace LTS

variable {S L : Type*} {A : LTS S L}

/-- An infinite run from `s₀`. -/
structure Run (A : LTS S L) (s₀ : S) where
  /-- The `n`-th state. -/
  st : ℕ → S
  /-- The `n`-th label. -/
  lab : ℕ → L
  start : st 0 = s₀
  step : ∀ n, A.step (st n) (lab n) (st (n + 1))

/-- `p` holds infinitely often. -/
def InfOften (p : ℕ → Prop) : Prop := ∀ N, ∃ n, N ≤ n ∧ p n

namespace Run

variable {s₀ : S} (r : A.Run s₀)

/-- Strong fairness over transitions. -/
def StronglyFair : Prop :=
  ∀ s l s', InfOften (fun n => r.st n = s) → A.step s l s' →
    InfOften (fun n => r.st n = s ∧ r.lab n = l ∧ r.st (n + 1) = s')

theorem reachable (n : ℕ) : A.Reachable s₀ (r.st n) := by
  induction n with
  | zero => rw [r.start]
  | succ n ih => exact ih.tail ⟨r.lab n, r.step n⟩

/-- In a system with finitely many reachable states, some state is visited infinitely often. -/
theorem exists_infOften (hfin : {s | A.Reachable s₀ s}.Finite) :
    ∃ s, InfOften (fun n => r.st n = s) := by
  have := hfin.to_subtype
  let f : ℕ → {s | A.Reachable s₀ s} := fun n => ⟨r.st n, r.reachable n⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  refine ⟨y.1, fun N => ?_⟩
  have hinf : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  have : ∃ n ∈ f ⁻¹' {y}, N ≤ n := by
    by_contra hc
    push Not at hc
    exact hinf ((Set.finite_lt_nat N).subset fun n hn => hc n hn)
  obtain ⟨n, hn, hNn⟩ := this
  exact ⟨n, hNn, by simpa [f, Subtype.ext_iff] using hn⟩

variable {r}

/-- Under strong fairness, the states visited infinitely often are closed under steps. -/
theorem infOften_of_step (hfair : r.StronglyFair) {s s' : S} {l : L}
    (hs : InfOften (fun n => r.st n = s)) (hst : A.step s l s') :
    InfOften (fun n => r.st n = s') := by
  intro N
  obtain ⟨n, hn, -, -, h⟩ := hfair s l s' hs hst N
  exact ⟨n + 1, by omega, h⟩

theorem infOften_of_reachable (hfair : r.StronglyFair) {s s' : S}
    (hs : InfOften (fun n => r.st n = s)) (hr : A.Reachable s s') :
    InfOften (fun n => r.st n = s') := by
  induction hr with
  | refl => exact hs
  | tail _ hst ih =>
    obtain ⟨l, hl⟩ := hst
    exact infOften_of_step hfair ih hl

/-- **Fair liveness.**  In a finite-state system, a live label is performed infinitely often
along every strongly fair run. -/
theorem infOften_label_of_live (hfin : {s | A.Reachable s₀ s}.Finite) (hfair : r.StronglyFair)
    {l : L} (hlive : A.LiveLabel s₀ l) : InfOften (fun n => r.lab n = l) := by
  obtain ⟨s, hs⟩ := r.exists_infOften hfin
  obtain ⟨n₀, -, rfl⟩ := hs 0
  obtain ⟨s₁, hr, s₂, hst⟩ := hlive _ (r.reachable n₀)
  have h₁ := infOften_of_reachable hfair hs hr
  intro N
  obtain ⟨n, hn, -, hl, -⟩ := hfair _ l s₂ h₁ hst N
  exact ⟨n, hn, hl⟩

/-- **Fair progress.**  In a finite-state system where an external action can always
eventually be performed, every strongly fair run performs external actions infinitely
often: fairness excludes livelock. -/
theorem infOften_external_of_progress {internal : L → Prop}
    (hfin : {s | A.Reachable s₀ s}.Finite) (hfair : r.StronglyFair)
    (hprog : ∀ s, A.Reachable s₀ s → ∃ s', A.Reachable s s' ∧ A.ExternalEnabled internal s') :
    InfOften (fun n => ¬ internal (r.lab n)) := by
  obtain ⟨s, hs⟩ := r.exists_infOften hfin
  obtain ⟨n₀, -, rfl⟩ := hs 0
  obtain ⟨s₁, hr, l, s₂, hl, hst⟩ := hprog _ (r.reachable n₀)
  have h₁ := infOften_of_reachable hfair hs hr
  intro N
  obtain ⟨n, hn, -, hlab, -⟩ := hfair _ l s₂ h₁ hst N
  exact ⟨n, hn, by show ¬ internal (r.lab n); rw [hlab]; exact hl⟩

/-- **Progress without fairness.**  In a livelock-free system, every run performs external
actions infinitely often. -/
theorem infOften_external_of_livelockFree {internal : L → Prop}
    (hl : A.LivelockFree internal s₀) (r : A.Run s₀) :
    InfOften (fun n => ¬ internal (r.lab n)) := by
  intro N
  by_contra h
  push Not at h
  apply hl (r.st N) (r.reachable N)
  refine ⟨fun n => r.st (N + n), by simp, fun n => ⟨r.lab (N + n), ?_, r.step (N + n)⟩⟩
  exact h (N + n) (by omega)

end Run

/-- From any reachable state of a deadlock-free, livelock-free system an external action can
eventually be performed (the hypothesis of `Run.infOften_external_of_progress`). -/
theorem progress_of_dfLf {internal : L → Prop} {s₀ : S} (hD : A.DeadlockFree s₀)
    (hL : A.LivelockFree internal s₀) :
    ∀ s, A.Reachable s₀ s → ∃ s', A.Reachable s s' ∧ A.ExternalEnabled internal s' := by
  intro s hs
  obtain ⟨s', h1, h2⟩ := (inevitablyExternal hD hL hs).exists_external
  exact ⟨s', Reachable.of_iStep_rtc h1, h2⟩

/-- From liveness of one external label. -/
theorem progress_of_liveLabel {internal : L → Prop} {s₀ : S} {l : L} (hl : ¬ internal l)
    (hlive : A.LiveLabel s₀ l) :
    ∀ s, A.Reachable s₀ s → ∃ s', A.Reachable s s' ∧ A.ExternalEnabled internal s' := by
  intro s hs
  obtain ⟨s', h1, s'', h2⟩ := hlive s hs
  exact ⟨s', h1, l, s'', hl, h2⟩

end LTS

end AsyncLean
