/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.Basic

/-!
# Stubborn sets: partial-order reduction for deadlocks

Concurrent systems have many interleavings of the same independent events, and their state
spaces grow exponentially with the number of concurrent components.  Valmari's *stubborn
sets* explore, at each marking, only the enabled transitions of a set `S` chosen so that
every deadlock remains reachable.  For a Petri net, `S` is stubborn at `M`
(`Net.Stubborn`) when

* every enabled `t ∈ S` shares no input place with a transition outside `S` (transitions
  outside `S` can neither disable `t` nor be disabled by it);
* every disabled `t ∈ S` has a *scapegoat* place `p`, holding fewer tokens than `t` needs,
  into which no transition outside `S` puts tokens (so `t` stays disabled until some
  transition of `S` fires);
* if any transition is enabled, some transition of `S` is.

All three conditions are local: they are checked at one marking, from the net's structure.

**Main theorem** (`Net.reachable_red_of_dead`): if stubborn sets are used at every marking
of the reduced state space, every reachable dead marking is reachable in the reduced state
space.  Hence (`Net.deadlockFree_of_stubborn`) a reduced state space in which every
marking has a successor proves the whole net deadlock free.
-/

namespace AsyncLean

namespace Net

variable {P T : Type*} (N : Net P T)

/-- `t'` takes no token from an input place of `t`. -/
def NoConsume (t t' : T) : Prop := ∀ p, N.pre t p ≠ 0 → N.pre t' p = 0

/-- `S` is a stubborn set at `M` (for deadlocks). -/
structure Stubborn (M : Marking P) (S : T → Prop) : Prop where
  enabled : ∀ t, S t → N.Enabled M t → ∀ t', ¬ S t' → N.NoConsume t t'
  disabled : ∀ t, S t → ¬ N.Enabled M t →
    ∃ p, M p < N.pre t p ∧ ∀ t', ¬ S t' → N.post t' p = 0
  key : (∃ t, N.Enabled M t) → ∃ t, S t ∧ N.Enabled M t

/-- The reduced semantics: at `M`, only the enabled transitions of `S M` fire. -/
def redLts (S : Marking P → T → Prop) : LTS (Marking P) T where
  step M t M' := S M t ∧ N.lts.step M t M'

variable {N}

/-- An enabled transition stays enabled when a transition that consumes none of its input
tokens fires. -/
theorem enabled_fire_of_noConsume {M : Marking P} {t t' : T} (ht : N.Enabled M t)
    (hnc : N.NoConsume t t') : N.Enabled (N.fire M t') t := by
  intro p
  rw [fire_apply]
  by_cases hp : N.pre t p = 0
  · rw [hp]; exact Nat.zero_le _
  · rw [hnc p hp]; have := ht p; omega

/-- Two transitions, the second consuming none of the first's input tokens, commute. -/
theorem fire_comm {M : Marking P} {t t' : T} (ht : N.Enabled M t) (ht' : N.Enabled M t')
    (hnc : N.NoConsume t t') :
    N.Enabled (N.fire M t) t' ∧ N.fire (N.fire M t) t' = N.fire (N.fire M t') t := by
  refine ⟨fun p => ?_, funext fun p => ?_⟩
  · rw [fire_apply]
    by_cases hp : N.pre t p = 0
    · rw [hp]; have := ht' p; omega
    · rw [hnc p hp]; exact Nat.zero_le _
  · simp only [fire_apply]
    have h1 := ht p
    have h2 := ht' p
    by_cases hp : N.pre t p = 0
    · rw [hp]; omega
    · rw [hnc p hp]; omega

/-- A transition consuming none of the tokens of the sequence's other transitions can be
moved to the front: `M -u-> M' -t-> M''` becomes `M -t-> . -u-> M''`. -/
theorem path_push {t : T} :
    ∀ {M M' : Marking P} {u : List T}, N.Enabled M t → (∀ t' ∈ u, N.NoConsume t t') →
      N.lts.Path M u M' → N.lts.step M' t (N.fire M' t) →
      N.lts.Path M (t :: u) (N.fire M' t) := by
  intro M M' u ht hnc hp hst
  induction hp with
  | nil => exact .cons ⟨ht, rfl⟩ (.nil _)
  | @cons M Ma M' t₁ u' h₁ hrest ih =>
    obtain ⟨he₁, rfl⟩ := h₁
    have hnc₁ := hnc t₁ List.mem_cons_self
    have ih' := ih (enabled_fire_of_noConsume ht hnc₁)
      (fun t' ht' => hnc t' (List.mem_cons_of_mem _ ht')) hst
    cases ih' with
    | cons hb hrest' =>
      obtain ⟨-, rfl⟩ := hb
      obtain ⟨hen, heq⟩ := fire_comm ht he₁ hnc₁
      exact .cons ⟨ht, rfl⟩ (.cons ⟨hen, rfl⟩ (heq ▸ hrest'))

/-- An enabled transition stays enabled along a sequence of transitions consuming none of
its input tokens. -/
theorem enabled_of_path {t : T} :
    ∀ {M M' : Marking P} {u : List T}, N.Enabled M t → (∀ t' ∈ u, N.NoConsume t t') →
      N.lts.Path M u M' → N.Enabled M' t := by
  intro M M' u ht hnc hp
  induction hp with
  | nil => exact ht
  | cons h₁ _ ih =>
    obtain ⟨-, rfl⟩ := h₁
    exact ih (enabled_fire_of_noConsume ht (hnc _ List.mem_cons_self))
      (fun t' ht' => hnc t' (List.mem_cons_of_mem _ ht'))

/-- A place that no transition of the sequence puts tokens into does not gain tokens. -/
theorem le_of_path {p : P} :
    ∀ {M M' : Marking P} {u : List T}, (∀ t' ∈ u, N.post t' p = 0) →
      N.lts.Path M u M' → M' p ≤ M p := by
  intro M M' u hpost hp
  induction hp with
  | nil => exact le_rfl
  | cons h₁ _ ih =>
    obtain ⟨-, rfl⟩ := h₁
    refine (ih fun t' ht' => hpost t' (List.mem_cons_of_mem _ ht')).trans ?_
    rw [fire_apply, hpost _ List.mem_cons_self]
    omega

/-- Split a path at the first transition satisfying `q`. -/
theorem path_split {q : T → Prop} [DecidablePred q] :
    ∀ {M M' : Marking P} {w : List T}, N.lts.Path M w M' → (∃ t ∈ w, q t) →
      ∃ u t v M₁ M₂, w = u ++ t :: v ∧ (∀ t' ∈ u, ¬ q t') ∧ q t ∧ N.lts.Path M u M₁ ∧
        N.lts.step M₁ t M₂ ∧ N.lts.Path M₂ v M' := by
  intro M M' w hp hex
  induction hp with
  | nil => simp at hex
  | @cons M Ma M' t₁ w' h₁ hrest ih =>
    by_cases hq : q t₁
    · exact ⟨[], t₁, w', M, Ma, rfl, by simp, hq, .nil _, h₁, hrest⟩
    · obtain ⟨t, ht, hqt⟩ := hex
      rcases List.mem_cons.1 ht with rfl | ht
      · exact absurd hqt hq
      obtain ⟨u, t₂, v, M₁, M₂, rfl, hu, hq₂, hpu, hst, hpv⟩ := ih ⟨t, ht, hqt⟩
      refine ⟨t₁ :: u, t₂, v, M₁, M₂, rfl, ?_, hq₂, .cons h₁ hpu, hst, hpv⟩
      intro t' ht'
      rcases List.mem_cons.1 ht' with rfl | ht'
      · exact hq
      · exact hu t' ht'

/-- **Stubborn sets preserve deadlocks.**  If the sets `S M` are stubborn at every marking
reachable in the reduced semantics, every dead marking reachable from such a marking is
reachable in the reduced semantics too. -/
theorem reachable_red_of_dead (S : Marking P → T → Prop) {M₀ : Marking P}
    (hst : ∀ M, (N.redLts S).Reachable M₀ M → N.Stubborn M (S M)) :
    ∀ (n : ℕ) (M D : Marking P) (w : List T), w.length = n → (N.redLts S).Reachable M₀ M →
      N.lts.Path M w D → N.IsDead D → (N.redLts S).Reachable M D := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M D w hn hM hp hdead
    cases hp with
    | nil => exact LTS.Reachable.refl _
    | @cons _ Ma _ t₁ w' h₁ hrest =>
      have hS := hst M hM
      -- some transition of `S M` occurs in the path: otherwise the key transition would
      -- still be enabled at the dead marking
      obtain ⟨tk, hSk, henk⟩ := hS.key ⟨t₁, h₁.1⟩
      have hp : N.lts.Path M (t₁ :: w') D := .cons h₁ hrest
      have hex : ∃ t ∈ t₁ :: w', S M t := by
        by_contra hno
        push Not at hno
        exact hdead tk (enabled_of_path henk
          (fun t' ht' => hS.enabled tk hSk henk t' (hno t' ht')) hp)
      obtain ⟨u, t, v, M₁, M₂, hw, hu, hSt, hpu, hstep, hpv⟩ := path_split hp hex
      -- the first such transition is enabled at `M` (its scapegoat would stay unmarked)
      have hent : N.Enabled M t := by
        by_contra hdis
        obtain ⟨p, hlt, hpost⟩ := hS.disabled t hSt hdis
        have := le_of_path (fun t' ht' => hpost t' (hu t' ht')) hpu
        have := hstep.1 p
        omega
      -- move it to the front
      obtain ⟨hen₁, rfl⟩ := hstep
      have hpush := path_push hent (fun t' ht' => hS.enabled t hSt hent t' (hu t' ht')) hpu
        ⟨hen₁, rfl⟩
      cases hpush with
      | cons h₀ hrest₀ =>
        obtain ⟨-, rfl⟩ := h₀
        have hred : (N.redLts S).step M t (N.fire M t) := ⟨hSt, hent, rfl⟩
        have hlen : (u ++ v).length < n := by
          rw [← hn, hw]; simp
        exact LTS.Reachable.head ⟨t, hred⟩
          (ih _ hlen _ D (u ++ v) rfl (hM.tail ⟨t, hred⟩) (hrest₀.append hpv) hdead)

/-- **Deadlock freedom by partial-order reduction.**  If `Inv` holds initially, is
preserved by the reduced semantics, and at every marking satisfying it `S M` is stubborn
and contains an enabled transition, the net is deadlock free. -/
theorem deadlockFree_of_stubborn (S : Marking P → T → Prop) (Inv : Marking P → Prop)
    {M₀ : Marking P} (h₀ : Inv M₀)
    (hstep : ∀ M t, Inv M → S M t → N.Enabled M t → Inv (N.fire M t))
    (hst : ∀ M, Inv M → N.Stubborn M (S M))
    (hprog : ∀ M, Inv M → ∃ t, S M t ∧ N.Enabled M t) : N.lts.DeadlockFree M₀ := by
  have hinv : ∀ M, (N.redLts S).Reachable M₀ M → Inv M := fun M hM =>
    hM.invariant h₀ fun M t M' hI ⟨hS, hen, he⟩ => he ▸ hstep M t hI hS hen
  rw [deadlockFree_iff]
  intro D hD
  by_contra hno
  push Not at hno
  have hdead : N.IsDead D := hno
  obtain ⟨w, hw⟩ := hD.exists_path
  have := reachable_red_of_dead S (fun M hM => hst M (hinv M hM)) _ M₀ D w rfl
    (LTS.Reachable.refl _) hw hdead
  obtain ⟨t, -, hen⟩ := hprog D (hinv D this)
  exact hdead t hen

end Net

end AsyncLean
