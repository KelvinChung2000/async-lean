/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Basic

/-!
# Deadlock, livelock and liveness

This file defines the three behavioural correctness properties of an (asynchronous)
system modelled as an LTS, and proves the generic proof rules used to establish them.

## Definitions

* `IsDeadlock s` : no step at all leaves `s`.
* `DeadlockFree s₀` : no reachable state is a deadlock.
* `Diverges internal s` : there is an *infinite* run of internal steps starting at `s`.
* `LivelockFree internal s₀` : no reachable state diverges, i.e. the system can never
  spin forever doing only internal (silent) work.
* `LiveLabel s₀ l` : from every reachable state, `l` can eventually become enabled again
  (the classical L4-liveness of Petri net theory).  `Live s₀` : every label is live.
  Liveness rules out *partial* deadlock / starvation of any individual action.

## Proof rules

* `DeadlockFree.of_invariant` : inductive invariant + progress.
* `LivelockFree.of_ranking` / `LivelockFree.of_ranking_wf` : a ranking function that
  strictly decreases on every internal step.
* `LiveLabel.of_ranking` : a distance function guiding the system to enable `l`.
* `livelockFree_iff_acc` : livelock freedom is exactly well-foundedness of the internal
  step relation on the reachable states.
* `inevitablyExternal` : deadlock freedom + livelock freedom imply that along *every*
  internal path an external (observable) action eventually becomes enabled.

## Refutation rules

* `not_deadlockFree_of_path` : a trace to a dead state.
* `not_livelockFree_of_cycle` : a reachable internal cycle.
* `not_liveLabel_of_dead` : a reachable state from which a label is never enabled.

## Transfer

* `FunBisim` : a functional bisimulation between two LTSs; all properties transfer
  along it (used to connect the abstract semantics of Petri nets to the executable
  semantics checked by the verified model checker).
-/

namespace AsyncLean

namespace LTS

variable {S L : Type*} (A : LTS S L)

/-! ### Definitions -/

/-- A deadlock: no step leaves `s`. -/
def IsDeadlock (s : S) : Prop := ∀ l s', ¬ A.step s l s'

/-- No reachable state is a deadlock. -/
def DeadlockFree (s₀ : S) : Prop := ∀ s, A.Reachable s₀ s → ¬ A.IsDeadlock s

/-- `s` admits an infinite run consisting only of internal steps. -/
def Diverges (internal : L → Prop) (s : S) : Prop :=
  ∃ f : ℕ → S, f 0 = s ∧ ∀ n, A.IStep internal (f n) (f (n + 1))

/-- No reachable state admits an infinite run of internal steps. -/
def LivelockFree (internal : L → Prop) (s₀ : S) : Prop :=
  ∀ s, A.Reachable s₀ s → ¬ A.Diverges internal s

/-- `l` can always eventually be enabled again, whatever has happened so far. -/
def LiveLabel (s₀ : S) (l : L) : Prop :=
  ∀ s, A.Reachable s₀ s → ∃ s', A.Reachable s s' ∧ A.Enabled s' l

/-- Every label is live (no partial deadlock / starvation). -/
def Live (s₀ : S) : Prop := ∀ l, A.LiveLabel s₀ l

/-- **Persistence** (semi-modularity, speed independence): an enabled action is never
disabled by performing a *different* action — it stays enabled until it is performed.  For
gate-level circuits this is the absence of hazards (Muller's semi-modularity); for Petri
nets it is the absence of conflicts (persistent nets). -/
def Persistent (s₀ : S) : Prop :=
  ∀ s, A.Reachable s₀ s → ∀ l l' s', l ≠ l' → A.Enabled s l → A.step s l' s' → A.Enabled s' l

/-- An external action is enabled in `s`. -/
def ExternalEnabled (internal : L → Prop) (s : S) : Prop :=
  ∃ l s', ¬ internal l ∧ A.step s l s'

/-- `InevitablyExternal internal s` : every maximal run of internal steps from `s` is finite
and ends in (or passes through) a state where an external action is enabled.  This is the
branching-time property `A[τ U external-enabled]`. -/
inductive InevitablyExternal (internal : L → Prop) : S → Prop
  | now {s : S} : A.ExternalEnabled internal s → InevitablyExternal internal s
  | later {s : S} : (∃ s', A.IStep internal s s') →
      (∀ s', A.IStep internal s s' → InevitablyExternal internal s') →
      InevitablyExternal internal s

variable {A}

/-! ### Deadlock freedom -/

theorem deadlockFree_iff {s₀ : S} :
    A.DeadlockFree s₀ ↔ ∀ s, A.Reachable s₀ s → ∃ l s', A.step s l s' := by
  unfold DeadlockFree IsDeadlock
  simp only [not_forall, not_not]

theorem DeadlockFree.exists_step {s₀ s : S} (h : A.DeadlockFree s₀) (hs : A.Reachable s₀ s) :
    ∃ l s', A.step s l s' :=
  deadlockFree_iff.1 h s hs

/-- **Deadlock freedom by inductive invariant.** -/
theorem DeadlockFree.of_invariant {s₀ : S} (I : S → Prop) (h₀ : I s₀)
    (hstep : ∀ s l s', I s → A.step s l s' → I s')
    (hprog : ∀ s, I s → ∃ l s', A.step s l s') : A.DeadlockFree s₀ :=
  deadlockFree_iff.2 fun _ hs => hprog _ (hs.invariant h₀ hstep)

/-- Deadlock freedom is preserved when moving to a reachable state. -/
theorem DeadlockFree.of_reachable {s₀ s : S} (h : A.DeadlockFree s₀) (hs : A.Reachable s₀ s) :
    A.DeadlockFree s :=
  fun s' hs' => h s' (hs.trans hs')

/-- **Refuting deadlock freedom**: exhibit a trace leading to a deadlock. -/
theorem not_deadlockFree_of_path {s₀ s : S} {ls : List L} (hp : A.Path s₀ ls s)
    (hd : A.IsDeadlock s) : ¬ A.DeadlockFree s₀ :=
  fun h => h s hp.reachable hd

/-! ### Livelock freedom -/

/-- The converse internal step relation: `IRel internal s' s` iff `s → s'` internally.
Well-foundedness (accessibility) of this relation is the absence of infinite internal runs. -/
def IRel (A : LTS S L) (internal : L → Prop) (s' s : S) : Prop := A.IStep internal s s'

theorem not_diverges_of_acc {internal : L → Prop} {s : S} (h : Acc (A.IRel internal) s) :
    ¬ A.Diverges internal s := by
  induction h with
  | intro s _ ih =>
    rintro ⟨f, hf0, hf⟩
    refine ih (f 1) (hf0 ▸ hf 0) ⟨fun n => f (n + 1), rfl, fun n => hf (n + 1)⟩

theorem exists_iStep_not_acc {internal : L → Prop} {s : S} (h : ¬ Acc (A.IRel internal) s) :
    ∃ s', A.IStep internal s s' ∧ ¬ Acc (A.IRel internal) s' := by
  by_contra hc
  push Not at hc
  exact h (Acc.intro s fun s' hs' => hc s' hs')

theorem diverges_of_not_acc {internal : L → Prop} {s : S} (h : ¬ Acc (A.IRel internal) s) :
    A.Diverges internal s := by
  classical
  let T := {x : S // ¬ Acc (A.IRel internal) x}
  have hnext : ∀ x : T, ∃ y : T, A.IStep internal x.1 y.1 := fun x =>
    let ⟨y, hy, hy'⟩ := exists_iStep_not_acc x.2
    ⟨⟨y, hy'⟩, hy⟩
  choose next hnext using hnext
  let g : ℕ → T := fun n => Nat.rec ⟨s, h⟩ (fun _ x => next x) n
  exact ⟨fun n => (g n).1, rfl, fun n => hnext (g n)⟩

theorem diverges_iff_not_acc {internal : L → Prop} {s : S} :
    A.Diverges internal s ↔ ¬ Acc (A.IRel internal) s :=
  ⟨fun h hacc => not_diverges_of_acc hacc h, diverges_of_not_acc⟩

/-- Livelock freedom is exactly accessibility (well-foundedness) of the internal step
relation from every reachable state. -/
theorem livelockFree_iff_acc {internal : L → Prop} {s₀ : S} :
    A.LivelockFree internal s₀ ↔ ∀ s, A.Reachable s₀ s → Acc (A.IRel internal) s := by
  unfold LivelockFree
  simp only [diverges_iff_not_acc, not_not]

theorem LivelockFree.acc {internal : L → Prop} {s₀ s : S} (h : A.LivelockFree internal s₀)
    (hs : A.Reachable s₀ s) : Acc (A.IRel internal) s :=
  livelockFree_iff_acc.1 h s hs

/-- **Livelock freedom by a well-founded ranking function** on an inductive invariant. -/
theorem LivelockFree.of_ranking_wf {internal : L → Prop} {s₀ : S} (I : S → Prop) (h₀ : I s₀)
    (hstep : ∀ s l s', I s → A.step s l s' → I s')
    {α : Type*} (r : α → α → Prop) (hwf : WellFounded r) (V : S → α)
    (hV : ∀ s l s', I s → internal l → A.step s l s' → r (V s') (V s)) :
    A.LivelockFree internal s₀ := by
  have key : ∀ a, ∀ s, V s = a → I s → Acc (A.IRel internal) s := by
    intro a
    induction a using hwf.induction with
    | _ a ih =>
      intro s hsa hs
      refine Acc.intro s fun s' ⟨l, hl, hst⟩ => ?_
      exact ih (V s') (hsa ▸ hV s l s' hs hl hst) s' rfl (hstep s l s' hs hst)
  exact livelockFree_iff_acc.2 fun s hs => key _ s rfl (hs.invariant h₀ hstep)

/-- **Livelock freedom by a natural-number ranking function** on an inductive invariant:
every internal step strictly decreases `V`. -/
theorem LivelockFree.of_ranking {internal : L → Prop} {s₀ : S} (I : S → Prop) (h₀ : I s₀)
    (hstep : ∀ s l s', I s → A.step s l s' → I s') (V : S → ℕ)
    (hV : ∀ s l s', I s → internal l → A.step s l s' → V s' < V s) :
    A.LivelockFree internal s₀ :=
  LivelockFree.of_ranking_wf I h₀ hstep (· < ·) wellFounded_lt V hV

/-- If no label is internal, the system is trivially livelock free. -/
theorem LivelockFree.of_no_internal {internal : L → Prop} {s₀ : S}
    (h : ∀ l, ¬ internal l) : A.LivelockFree internal s₀ :=
  LivelockFree.of_ranking (fun _ => True) trivial (fun _ _ _ _ _ => trivial) (fun _ => 0)
    (fun _ l _ _ hl _ => absurd hl (h l))

/-- Accessibility forbids a loop. -/
theorem acc_not_rel_self {α : Type*} {r : α → α → Prop} {a : α} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro x _ ih => exact fun hx => ih x hx hx

theorem not_acc_of_transGen_self {internal : L → Prop} {s : S}
    (h : Relation.TransGen (A.IStep internal) s s) : ¬ Acc (A.IRel internal) s := by
  intro hacc
  have h' : Relation.TransGen (A.IRel internal) s s := by
    rw [← Relation.transGen_swap]; exact h
  exact acc_not_rel_self hacc.transGen h'

/-- **Refuting livelock freedom**: a reachable state lying on a non-empty cycle of internal
steps diverges. -/
theorem not_livelockFree_of_cycle {internal : L → Prop} {s₀ s : S} (hs : A.Reachable s₀ s)
    (hc : Relation.TransGen (A.IStep internal) s s) : ¬ A.LivelockFree internal s₀ :=
  fun h => not_acc_of_transGen_self hc (h.acc hs)

/-! ### Persistence -/

/-- **Refuting persistence**: a reachable state where performing `l'` disables `l`. -/
theorem not_persistent_of {s₀ s s' : S} {l l' : L} (hs : A.Reachable s₀ s) (hne : l ≠ l')
    (hen : A.Enabled s l) (hst : A.step s l' s') (hdis : ¬ A.Enabled s' l) :
    ¬ A.Persistent s₀ :=
  fun h => hdis (h s hs l l' s' hne hen hst)

/-! ### Liveness -/

theorem LiveLabel.of_reachable {s₀ s : S} {l : L} (h : A.LiveLabel s₀ l)
    (hs : A.Reachable s₀ s) : A.LiveLabel s l :=
  fun s' hs' => h s' (hs.trans hs')

/-- **Liveness by a distance function**: on an inductive invariant, either `l` is enabled or
some step strictly decreases the distance `d`. -/
theorem LiveLabel.of_ranking {s₀ : S} (I : S → Prop) (h₀ : I s₀)
    (hstep : ∀ s l s', I s → A.step s l s' → I s') (l : L) (d : S → ℕ)
    (hd : ∀ s, I s → A.Enabled s l ∨ ∃ l' s', A.step s l' s' ∧ d s' < d s) :
    A.LiveLabel s₀ l := by
  have key : ∀ n, ∀ s, d s = n → I s → ∃ s', A.Reachable s s' ∧ A.Enabled s' l := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hsn hs
      rcases hd s hs with he | ⟨l', s', hst, hlt⟩
      · exact ⟨s, Reachable.refl s, he⟩
      · obtain ⟨s'', h1, h2⟩ := ih (d s') (hsn ▸ hlt) s' rfl (hstep s l' s' hs hst)
        exact ⟨s'', Reachable.head ⟨l', hst⟩ h1, h2⟩
  exact fun s hs => key _ s rfl (hs.invariant h₀ hstep)

/-- A label that is never enabled from some reachable state is not live. -/
theorem not_liveLabel_of_dead {s₀ s : S} {l : L} (hs : A.Reachable s₀ s)
    (hdead : ∀ s', A.Reachable s s' → ¬ A.Enabled s' l) : ¬ A.LiveLabel s₀ l := by
  intro h
  obtain ⟨s', h1, h2⟩ := h s hs
  exact hdead s' h1 h2

/-- Liveness of all labels implies deadlock freedom (when there is at least one label). -/
theorem Live.deadlockFree [Nonempty L] {s₀ : S} (h : A.Live s₀) : A.DeadlockFree s₀ := by
  intro s hs hdead
  obtain ⟨s', hss', s'', hs''⟩ := h (Classical.arbitrary L) s hs
  -- the first step from `s` along `hss'` (or the enabled step itself) contradicts `hdead`
  rcases Relation.ReflTransGen.cases_head hss' with rfl | ⟨s₁, ⟨l₁, h₁⟩, _⟩
  · exact hdead _ _ hs''
  · exact hdead _ _ h₁

/-! ### Progress: deadlock freedom + livelock freedom -/

/-- **Progress theorem.**  In a deadlock-free and livelock-free system, from every reachable
state, *every* run of internal steps inevitably reaches a state offering an external action:
the system can neither get stuck nor chatter forever without observable progress. -/
theorem inevitablyExternal {internal : L → Prop} {s₀ : S} (hD : A.DeadlockFree s₀)
    (hL : A.LivelockFree internal s₀) {s : S} (hs : A.Reachable s₀ s) :
    A.InevitablyExternal internal s := by
  classical
  have hacc := hL.acc hs
  induction hacc with
  | intro s _ ih =>
    obtain ⟨l, s', hst⟩ := hD.exists_step hs
    by_cases hl : internal l
    · refine InevitablyExternal.later ⟨s', l, hl, hst⟩ fun s'' hs'' => ?_
      exact ih s'' hs'' (hs.tail hs''.step)
    · exact InevitablyExternal.now ⟨l, s', hl, hst⟩

/-- From `InevitablyExternal`, some external action is reachable by internal steps only. -/
theorem InevitablyExternal.exists_external {internal : L → Prop} {s : S}
    (h : A.InevitablyExternal internal s) :
    ∃ s', Relation.ReflTransGen (A.IStep internal) s s' ∧ A.ExternalEnabled internal s' := by
  induction h with
  | now he => exact ⟨_, Relation.ReflTransGen.refl, he⟩
  | later hex _ ih =>
    obtain ⟨s', hs'⟩ := hex
    obtain ⟨s'', h1, h2⟩ := ih s' hs'
    exact ⟨s'', Relation.ReflTransGen.head hs' h1, h2⟩

/-- An `InevitablyExternal` state is never a deadlock. -/
theorem InevitablyExternal.not_deadlock {internal : L → Prop} {s : S}
    (h : A.InevitablyExternal internal s) : ¬ A.IsDeadlock s := by
  cases h with
  | now he => obtain ⟨l, s', -, h⟩ := he; exact fun hd => hd l s' h
  | later hex _ => obtain ⟨s', l, -, h⟩ := hex; exact fun hd => hd l s' h

/-! ### Functional bisimulation and transfer of properties -/

variable {S' : Type*}

/-- `f` is a *functional bisimulation* from `A` to `B`: the `B`-steps out of `f s` are
exactly the images of the `A`-steps out of `s`. -/
structure FunBisim (A : LTS S L) (B : LTS S' L) (f : S → S') : Prop where
  step_iff : ∀ s l t, B.step (f s) l t ↔ ∃ s', A.step s l s' ∧ f s' = t

namespace FunBisim

variable {B : LTS S' L} {f : S → S'} (hf : FunBisim A B f)
include hf

theorem step_map {s s' : S} {l : L} (h : A.step s l s') : B.step (f s) l (f s') :=
  (hf.step_iff _ _ _).2 ⟨s', h, rfl⟩

theorem enabled_iff {s : S} {l : L} : B.Enabled (f s) l ↔ A.Enabled s l := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨s', hs', -⟩ := (hf.step_iff _ _ _).1 ht
    exact ⟨s', hs'⟩
  · rintro ⟨s', hs'⟩
    exact ⟨_, hf.step_map hs'⟩

theorem reachable_map {s₀ s : S} (h : A.Reachable s₀ s) : B.Reachable (f s₀) (f s) := by
  induction h with
  | refl => exact Reachable.refl _
  | tail _ hst ih => obtain ⟨l, hl⟩ := hst; exact ih.tail ⟨l, hf.step_map hl⟩

theorem reachable_lift {s₀ : S} {t : S'} (h : B.Reachable (f s₀) t) :
    ∃ s, A.Reachable s₀ s ∧ f s = t := by
  induction h with
  | refl => exact ⟨s₀, Reachable.refl _, rfl⟩
  | tail _ hst ih =>
    obtain ⟨s, hs, rfl⟩ := ih
    obtain ⟨l, hl⟩ := hst
    obtain ⟨s', hs', rfl⟩ := (hf.step_iff _ _ _).1 hl
    exact ⟨s', hs.tail ⟨l, hs'⟩, rfl⟩

theorem isDeadlock_iff {s : S} : B.IsDeadlock (f s) ↔ A.IsDeadlock s := by
  constructor
  · intro h l s' hs'; exact h l _ (hf.step_map hs')
  · intro h l t ht
    obtain ⟨s', hs', -⟩ := (hf.step_iff _ _ _).1 ht
    exact h l s' hs'

theorem deadlockFree_iff {s₀ : S} : B.DeadlockFree (f s₀) ↔ A.DeadlockFree s₀ := by
  constructor
  · intro h s hs hd
    exact h _ (hf.reachable_map hs) (hf.isDeadlock_iff.2 hd)
  · intro h t ht hd
    obtain ⟨s, hs, rfl⟩ := hf.reachable_lift ht
    exact h s hs (hf.isDeadlock_iff.1 hd)

theorem acc_iff {internal : L → Prop} {s : S} :
    Acc (B.IRel internal) (f s) ↔ Acc (A.IRel internal) s := by
  constructor
  · intro h
    generalize ht : f s = t at h
    induction h generalizing s with
    | intro t _ ih =>
      subst ht
      exact Acc.intro s fun s' ⟨l, hl, hst⟩ => ih (f s') ⟨l, hl, hf.step_map hst⟩ rfl
  · intro h
    induction h with
    | intro s _ ih =>
      refine Acc.intro (f s) fun t ⟨l, hl, hst⟩ => ?_
      obtain ⟨s', hs', rfl⟩ := (hf.step_iff _ _ _).1 hst
      exact ih s' ⟨l, hl, hs'⟩

theorem livelockFree_iff {internal : L → Prop} {s₀ : S} :
    B.LivelockFree internal (f s₀) ↔ A.LivelockFree internal s₀ := by
  simp only [livelockFree_iff_acc]
  constructor
  · intro h s hs; exact hf.acc_iff.1 (h _ (hf.reachable_map hs))
  · intro h t ht
    obtain ⟨s, hs, rfl⟩ := hf.reachable_lift ht
    exact hf.acc_iff.2 (h s hs)

theorem liveLabel_iff {s₀ : S} {l : L} : B.LiveLabel (f s₀) l ↔ A.LiveLabel s₀ l := by
  constructor
  · intro h s hs
    obtain ⟨t, ht, hen⟩ := h _ (hf.reachable_map hs)
    obtain ⟨s', hs', rfl⟩ := hf.reachable_lift ht
    exact ⟨s', hs', hf.enabled_iff.1 hen⟩
  · intro h t ht
    obtain ⟨s, hs, rfl⟩ := hf.reachable_lift ht
    obtain ⟨s', hs', hen⟩ := h s hs
    exact ⟨f s', hf.reachable_map hs', hf.enabled_iff.2 hen⟩

theorem live_iff {s₀ : S} : B.Live (f s₀) ↔ A.Live s₀ :=
  forall_congr' fun _ => hf.liveLabel_iff

theorem persistent_iff {s₀ : S} : B.Persistent (f s₀) ↔ A.Persistent s₀ := by
  constructor
  · intro h s hs l l' s' hne hen hst
    exact hf.enabled_iff.1 (h _ (hf.reachable_map hs) l l' _ hne (hf.enabled_iff.2 hen)
      (hf.step_map hst))
  · intro h t ht l l' t' hne hen hst
    obtain ⟨s, hs, rfl⟩ := hf.reachable_lift ht
    obtain ⟨s', hs', rfl⟩ := (hf.step_iff _ _ _).1 hst
    exact hf.enabled_iff.2 (h s hs l l' s' hne (hf.enabled_iff.1 hen) hs')

end FunBisim

end LTS

end AsyncLean
