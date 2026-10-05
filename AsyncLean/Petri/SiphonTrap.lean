/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Siphons, traps and structural deadlock freedom

A *siphon* is a set of places that, once empty, stays empty forever; a *trap* is a set of
places that, once marked, stays marked forever.  For ordinary nets (all `pre` weights at
most one) the set of empty places of a dead marking is a siphon.  This gives the classical
structural sufficient condition for deadlock freedom (Commoner's siphon–trap property):

> if every non-empty siphon contains a trap that is marked initially, the net is
> deadlock free  (`deadlockFree_of_siphonTrap`).

The property is decidable for finite nets (`SiphonTrapProperty` has a `Decidable`
instance), so for small concrete nets it can be discharged with `decide`.
-/

namespace AsyncLean

namespace Net

variable {P T : Type*} {N : Net P T}

variable (N) in
/-- `S` is a siphon: every transition that puts tokens into `S` also takes tokens from `S`. -/
def IsSiphon (S : Finset P) : Prop :=
  ∀ t, (∃ p ∈ S, 0 < N.post t p) → ∃ p ∈ S, 0 < N.pre t p

variable (N) in
/-- `Q` is a trap: every transition that takes tokens from `Q` also puts tokens into `Q`. -/
def IsTrap (Q : Finset P) : Prop :=
  ∀ t, (∃ p ∈ Q, 0 < N.pre t p) → ∃ p ∈ Q, 0 < N.post t p

/-- Some place of `Q` is marked in `M`. -/
def Marked (M : Marking P) (Q : Finset P) : Prop := ∃ p ∈ Q, 0 < M p

variable (N) in
/-- Every non-empty siphon contains a trap that is marked in `M₀`. -/
def SiphonTrapProperty (M₀ : Marking P) : Prop :=
  ∀ S : Finset P, S.Nonempty → N.IsSiphon S → ∃ Q ∈ S.powerset, N.IsTrap Q ∧ Marked M₀ Q

section Decidable

variable [Fintype P] [DecidableEq P] [Fintype T]

instance (S : Finset P) : Decidable (N.IsSiphon S) := by unfold IsSiphon; infer_instance
instance (Q : Finset P) : Decidable (N.IsTrap Q) := by unfold IsTrap; infer_instance
instance (M : Marking P) (Q : Finset P) : Decidable (Marked M Q) := by
  unfold Marked; infer_instance
instance (M₀ : Marking P) : Decidable (N.SiphonTrapProperty M₀) := by
  unfold SiphonTrapProperty; infer_instance

end Decidable

/-- A marked trap stays marked after firing any transition. -/
theorem IsTrap.marked_fire {Q : Finset P} (hQ : N.IsTrap Q) {M : Marking P} {t : T}
    (hm : Marked M Q) : Marked (N.fire M t) Q := by
  classical
  by_cases hc : ∃ p ∈ Q, 0 < N.pre t p
  · obtain ⟨q, hq, hpos⟩ := hQ t hc
    exact ⟨q, hq, by rw [fire_apply]; omega⟩
  · push Not at hc
    obtain ⟨p, hp, hpos⟩ := hm
    have := hc p hp
    exact ⟨p, hp, by rw [fire_apply]; omega⟩

/-- A trap marked initially is marked in every reachable marking. -/
theorem IsTrap.marked_reachable {Q : Finset P} (hQ : N.IsTrap Q) {M₀ M : Marking P}
    (hm : Marked M₀ Q) (hr : N.lts.Reachable M₀ M) : Marked M Q :=
  hr.invariant hm fun _ _ _ hM ⟨_, he⟩ => he ▸ hQ.marked_fire hM

/-- An empty siphon stays empty after firing an enabled transition. -/
theorem IsSiphon.empty_fire {S : Finset P} (hS : N.IsSiphon S) {M : Marking P} {t : T}
    (he : ∀ p ∈ S, M p = 0) (hen : N.Enabled M t) : ∀ p ∈ S, N.fire M t p = 0 := by
  intro p hp
  have hpost : N.post t p = 0 := by
    by_contra hne
    obtain ⟨q, hq, hpre⟩ := hS t ⟨p, hp, Nat.pos_of_ne_zero hne⟩
    have := hen q
    rw [he q hq] at this
    omega
  rw [fire_apply, he p hp, hpost]
  simp

/-- An initially empty siphon stays empty forever; in particular every transition with an
input place in it is dead. -/
theorem IsSiphon.empty_reachable {S : Finset P} (hS : N.IsSiphon S) {M₀ M : Marking P}
    (he : ∀ p ∈ S, M₀ p = 0) (hr : N.lts.Reachable M₀ M) : ∀ p ∈ S, M p = 0 :=
  hr.invariant (I := fun M => ∀ p ∈ S, M p = 0) he
    fun _ _ _ hM ⟨hen, h⟩ => h ▸ hS.empty_fire hM hen

/-- In an ordinary net, the empty places of a dead marking form a siphon. -/
theorem isSiphon_empty_of_dead [Fintype P] [DecidableEq P] (hord : ∀ t p, N.pre t p ≤ 1)
    {M : Marking P} (hdead : N.IsDead M) :
    N.IsSiphon (Finset.univ.filter fun p => M p = 0) := by
  intro t _
  have := hdead t
  unfold Enabled at this
  push Not at this
  obtain ⟨p, hp⟩ := this
  have := hord t p
  exact ⟨p, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, by omega⟩

/-- **Commoner's siphon–trap theorem (deadlock freedom).**  In an ordinary net with at
least one transition, if every non-empty siphon contains an initially marked trap, then no
reachable marking is dead. -/
theorem deadlockFree_of_siphonTrap [Fintype P] [DecidableEq P] [Nonempty T]
    (hord : ∀ t p, N.pre t p ≤ 1) {M₀ : Marking P} (h : N.SiphonTrapProperty M₀) :
    N.lts.DeadlockFree M₀ := by
  intro M hr hdl
  have hdead : N.IsDead M := lts_isDeadlock_iff.1 hdl
  set S := Finset.univ.filter fun p => M p = 0 with hSdef
  have hS : N.IsSiphon S := isSiphon_empty_of_dead hord hdead
  have hne : S.Nonempty := by
    have := hdead (Classical.arbitrary T)
    unfold Enabled at this
    push Not at this
    obtain ⟨p, hp⟩ := this
    have := hord (Classical.arbitrary T) p
    exact ⟨p, by simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
  obtain ⟨Q, hQS, hQ, hm⟩ := h S hne hS
  rw [Finset.mem_powerset] at hQS
  obtain ⟨q, hq, hpos⟩ := hQ.marked_reachable hm hr
  have := hQS hq
  simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at this
  omega

end Net

end AsyncLean
