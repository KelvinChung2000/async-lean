/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Basic.Defs

/-!
# Interconnection networks with dynamic routing, part 2: selection functions and basic facts

Part 2 of 5 of `AsyncLean.Routing.Basic`; that module has the overview.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*}

variable (N : Network C P)

section Semantics

variable [DecidableEq C]

/-! ### Selection functions -/

omit [DecidableEq C] in
theorem adaptive_valid : N.ValidSel N.adaptive :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- Offer only the permitted channels that are free now (a packet waits if none is). -/
def freeOnly : Selection C P := fun f c p => (N.route c p).filter fun q => (f q.1).isNone

omit [DecidableEq C] in
theorem freeOnly_valid : N.ValidSel N.freeOnly where
  sub _ _ _ _ h := (List.mem_filter.1 h).1
  conserving _ _ _ _ := fun ⟨q, hq, hfree⟩ =>
    ⟨q, List.mem_filter.2 ⟨hq, by simp [hfree]⟩, hfree⟩

/-- Take the first permitted channel that is free now (a deterministic, congestion-aware
policy: the order of `route` is a priority order). -/
def firstFree : Selection C P := fun f c p =>
  ((N.route c p).find? fun q => (f q.1).isNone).toList

omit [DecidableEq C] in
theorem firstFree_valid : N.ValidSel N.firstFree where
  sub f c p q h := by
    simp only [firstFree, Option.mem_toList] at h
    exact List.mem_of_find?_eq_some h
  conserving f c p _ := fun ⟨q, hq, hfree⟩ => by
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1
      (List.find?_isSome.2 ⟨q, hq, by simp [hfree]⟩ :
        ((N.route c p).find? fun q => (f q.1).isNone).isSome)
    refine ⟨q', by simp [firstFree, hq'], ?_⟩
    simpa using List.find?_some hq'

/-! ### Basic facts -/

omit [DecidableEq C] in
theorem exists_of_ne_empty {f : Config C P} (h : f ≠ empty) : ∃ c p, f c = some p := by
  by_contra hc
  push Not at hc
  exact h (funext fun c => by
    cases hfc : f c with
    | none => rfl
    | some p => exact absurd hfc (hc c p))

/-- The legal pairs are an invariant of every selection that only offers permitted hops. -/
theorem legal_step {legal : C → P → Prop} (hcl : N.Closed legal) {sel : Selection C P}
    (hsel : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p) {f f' : Config C P} {a : Act C P}
    (hf : Legal legal f) (h : N.StepWith sel f a f') : Legal legal f' := by
  intro x px hx
  cases h with
  | @inject c p hinj _ =>
    by_cases hxc : x = c
    · subst hxc
      simp only [Function.update_self, Option.some.injEq] at hx
      cases hx
      exact hcl.inject _ hinj
    · rw [Function.update_of_ne hxc] at hx
      exact hf x px hx
  | @hop c c' p p' hp harr hq _ =>
    by_cases hxc' : x = c'
    · subst hxc'
      simp only [Function.update_self, Option.some.injEq] at hx
      cases hx
      exact hcl.route c p _ (hf c p hp) harr (hsel _ _ _ _ hq)
    · rw [Function.update_of_ne hxc'] at hx
      by_cases hxc : x = c
      · subst hxc; simp at hx
      · rw [Function.update_of_ne hxc] at hx
        exact hf x px hx
  | @eject c p _ _ =>
    by_cases hxc : x = c
    · subst hxc; simp at hx
    · rw [Function.update_of_ne hxc] at hx
      exact hf x px hx

theorem legal_of_reachable_sub {legal : C → P → Prop} (hcl : N.Closed legal)
    {sel : Selection C P} (hsel : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p) {f : Config C P}
    (h : (N.ltsWith sel).Reachable empty f) : Legal legal f :=
  h.invariant (fun _ _ h => by simp [empty] at h)
    (fun _ _ _ hf hst => N.legal_step hcl hsel hf hst)

theorem legal_of_reachable {legal : C → P → Prop} (hcl : N.Closed legal) {sel : Selection C P}
    (hsel : N.ValidSel sel) {f : Config C P} (h : (N.ltsWith sel).Reachable empty f) :
    Legal legal f :=
  N.legal_of_reachable_sub hcl hsel.sub h

/-- Every hop of the network is a routing step of the packet that moves. -/
theorem StepWith.packetStep {sel : Selection C P} (hsel : N.ValidSel sel)
    {f f' : Config C P} {c c' : C} {p' : P} (h : N.StepWith sel f (.hop c c' p') f') :
    ∃ p, f c = some p ∧ N.PacketStep (c, p) (c', p') := by
  cases h with
  | hop hp harr hq _ => exact ⟨_, hp, harr, hsel.sub _ _ _ _ hq⟩

/-! ### Every selection behaves like the adaptive one -/

theorem StepWith.to_adaptive {sel : Selection C P} (hsel : N.ValidSel sel)
    {f f' : Config C P} {a : Act C P} (h : N.StepWith sel f a f') :
    N.StepWith N.adaptive f a f' := by
  cases h with
  | inject h₁ h₂ => exact .inject h₁ h₂
  | hop h₁ h₂ h₃ h₄ => exact .hop h₁ h₂ (hsel.sub _ _ _ _ h₃) h₄
  | eject h₁ h₂ => exact .eject h₁ h₂

theorem reachable_to_adaptive {sel : Selection C P} (hsel : N.ValidSel sel)
    {f f' : Config C P} (h : (N.ltsWith sel).Reachable f f') : N.lts.Reachable f f' := by
  induction h with
  | refl => exact LTS.Reachable.refl _
  | tail _ hst ih => obtain ⟨a, ha⟩ := hst; exact ih.tail ⟨a, StepWith.to_adaptive N hsel ha⟩

/-- A configuration that can move under adaptive routing can move under every valid
selection (by work conservation). -/
theorem Movable.of_adaptive {sel : Selection C P} (hsel : N.ValidSel sel) {f : Config C P}
    (h : N.Movable N.adaptive f) : N.Movable sel f := by
  obtain ⟨a, f', ha, hst⟩ := h
  cases hst with
  | inject => simp [Act.IsMove] at ha
  | @hop c c' p p' hp harr hq hfree =>
    obtain ⟨⟨c'', p''⟩, hq', hfree'⟩ := hsel.conserving _ c p hp ⟨(c', p'), hq, hfree⟩
    exact ⟨.hop c c'' p'', _, rfl, StepWith.hop hp harr hq' hfree'⟩
  | @eject c p hp harr => exact ⟨.eject c, _, rfl, StepWith.eject hp harr⟩

/-- **Deadlock freedom for all selections reduces to adaptive routing.** -/
theorem deadlockFree_iff_adaptive : N.DeadlockFree ↔ N.DeadlockFreeWith N.adaptive :=
  ⟨fun h => h _ N.adaptive_valid, fun h _ hsel f hf hne =>
    Movable.of_adaptive N hsel (h f (N.reachable_to_adaptive hsel hf) hne)⟩

/-- **Livelock freedom for all selections reduces to adaptive routing.** -/
theorem livelockFree_iff_adaptive : N.LivelockFree ↔ N.LivelockFreeWith N.adaptive :=
  ⟨fun h => h _ N.adaptive_valid, fun h _ hsel =>
    LTS.LivelockFree.of_sub (fun _ _ _ hst => StepWith.to_adaptive N hsel hst) h⟩

end Semantics

end Network

end AsyncLean
