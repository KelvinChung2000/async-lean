/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties
import Mathlib.Data.Fintype.Pi

/-!
# Place/transition Petri nets

Petri nets are the standard behavioural model of asynchronous (self-timed) control:
signal transition graphs, handshake protocols, Muller pipelines and arbiters are all
Petri nets whose transitions are labelled by signal events.

## Main definitions

* `Net P T` : a place/transition net with places `P`, transitions `T` and arc weights
  `pre t p` (tokens consumed from `p` by `t`) and `post t p` (tokens produced).
* `Marking P = P → ℕ`.
* `Net.Enabled M t`, `Net.fire M t`.
* `Net.lts` : the interleaving semantics of the net as an LTS whose labels are transitions.
  All the generic properties of `AsyncLean.LTS` (deadlock freedom, livelock freedom,
  liveness) therefore apply to nets; e.g. `N.lts.DeadlockFree M₀`.
* `Net.fireSeq` : executable firing of a sequence, used to *refute* properties.
-/

namespace AsyncLean

/-- A marking assigns a number of tokens to every place. -/
abbrev Marking (P : Type*) := P → ℕ

/-- A place/transition Petri net. -/
structure Net (P T : Type*) where
  /-- `pre t p` : weight of the arc from place `p` to transition `t`. -/
  pre : T → P → ℕ
  /-- `post t p` : weight of the arc from transition `t` to place `p`. -/
  post : T → P → ℕ

namespace Net

variable {P T : Type*} (N : Net P T)

/-- Transition `t` is enabled in marking `M`. -/
def Enabled (M : Marking P) (t : T) : Prop := ∀ p, N.pre t p ≤ M p

instance [Fintype P] (M : Marking P) (t : T) : Decidable (N.Enabled M t) :=
  inferInstanceAs (Decidable (∀ p, N.pre t p ≤ M p))

/-- The marking reached by firing `t` in `M`. -/
def fire (M : Marking P) (t : T) : Marking P := fun p => M p - N.pre t p + N.post t p

/-- Interleaving semantics: an LTS whose labels are the transitions of the net. -/
def lts : LTS (Marking P) T where
  step M t M' := N.Enabled M t ∧ M' = N.fire M t

/-- A marking in which no transition is enabled. -/
def IsDead (M : Marking P) : Prop := ∀ t, ¬ N.Enabled M t

variable {N}

@[simp] theorem lts_step {M M' : Marking P} {t : T} :
    N.lts.step M t M' ↔ N.Enabled M t ∧ M' = N.fire M t := Iff.rfl

theorem lts_enabled_iff {M : Marking P} {t : T} : N.lts.Enabled M t ↔ N.Enabled M t :=
  ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

theorem lts_isDeadlock_iff {M : Marking P} : N.lts.IsDeadlock M ↔ N.IsDead M := by
  constructor
  · intro h t ht; exact h t _ ⟨ht, rfl⟩
  · intro h t M' ⟨ht, _⟩; exact h t ht

theorem deadlockFree_iff {M₀ : Marking P} :
    N.lts.DeadlockFree M₀ ↔ ∀ M, N.lts.Reachable M₀ M → ∃ t, N.Enabled M t := by
  unfold LTS.DeadlockFree
  simp only [lts_isDeadlock_iff, IsDead, not_forall, not_not]

theorem fire_apply (M : Marking P) (t : T) (p : P) : N.fire M t p = M p - N.pre t p + N.post t p :=
  rfl

/-- Integer form of the firing rule (valid when `t` is enabled). -/
theorem fire_cast {M : Marking P} {t : T} (h : N.Enabled M t) (p : P) :
    ((N.fire M t p : ℕ) : ℤ) = M p - N.pre t p + N.post t p := by
  have := h p
  simp only [fire_apply]
  omega

/-! ### Monotonicity -/

theorem Enabled.mono {M M' : Marking P} {t : T} (h : N.Enabled M t) (hle : M ≤ M') :
    N.Enabled M' t :=
  fun p => (h p).trans (hle p)

theorem fire_add {M D : Marking P} {t : T} (h : N.Enabled M t) :
    N.fire (M + D) t = N.fire M t + D := by
  funext p
  have := h p
  simp only [fire_apply, Pi.add_apply]
  omega

/-! ### Executable firing sequences -/

section FireSeq

variable [Fintype P]

/-- Fire a sequence of transitions, failing (`none`) if some transition is not enabled. -/
def fireSeq (N : Net P T) : Marking P → List T → Option (Marking P)
  | M, [] => some M
  | M, t :: ts => if N.Enabled M t then N.fireSeq (N.fire M t) ts else none

theorem path_of_fireSeq {M M' : Marking P} {ts : List T} (h : N.fireSeq M ts = some M') :
    N.lts.Path M ts M' := by
  induction ts generalizing M with
  | nil => cases h; exact LTS.Path.nil _
  | cons t ts ih =>
    simp only [fireSeq] at h
    split_ifs at h with hen
    exact LTS.Path.cons ⟨hen, rfl⟩ (ih h)

theorem reachable_of_fireSeq {M M' : Marking P} {ts : List T} (h : N.fireSeq M ts = some M') :
    N.lts.Reachable M M' :=
  (path_of_fireSeq h).reachable

theorem fireSeq_of_path {M M' : Marking P} {ts : List T} (h : N.lts.Path M ts M') :
    N.fireSeq M ts = some M' := by
  induction h with
  | nil => rfl
  | cons hst _ ih =>
    obtain ⟨hen, rfl⟩ := hst
    simp only [fireSeq, hen, ↓reduceIte, ih]

/-- **Refuting deadlock freedom of a net**: a firing sequence reaching a dead marking. -/
theorem not_deadlockFree_of_fireSeq {M₀ M : Marking P} {ts : List T}
    (h : N.fireSeq M₀ ts = some M) (hdead : N.IsDead M) : ¬ N.lts.DeadlockFree M₀ :=
  LTS.not_deadlockFree_of_path (path_of_fireSeq h) (lts_isDeadlock_iff.2 hdead)

theorem transGen_iStep_of_fireSeq {internal : T → Prop} {M M' : Marking P} {t : T}
    {ts : List T} (h : N.fireSeq M (t :: ts) = some M') (hint : ∀ u ∈ t :: ts, internal u) :
    Relation.TransGen (N.lts.IStep internal) M M' := by
  induction ts generalizing M t with
  | nil =>
    simp only [fireSeq] at h
    split_ifs at h with hen
    cases h
    exact Relation.TransGen.single ⟨t, hint t (by simp), hen, rfl⟩
  | cons u us ih =>
    rw [fireSeq] at h
    split_ifs at h with hen
    refine Relation.TransGen.head ⟨t, hint t (by simp), hen, rfl⟩ (ih h ?_)
    intro v hv; exact hint v (List.mem_cons_of_mem _ hv)

/-- **Refuting livelock freedom of a net**: a firing sequence reaching a marking `M` from
which a non-empty sequence of internal transitions leads back to `M`. -/
theorem not_livelockFree_of_fireSeq {internal : T → Prop} {M₀ M : Marking P} {ts : List T}
    {t : T} {cyc : List T} (h : N.fireSeq M₀ ts = some M) (hcyc : N.fireSeq M (t :: cyc) = some M)
    (hint : ∀ u ∈ t :: cyc, internal u) : ¬ N.lts.LivelockFree internal M₀ :=
  LTS.not_livelockFree_of_cycle (reachable_of_fireSeq h) (transGen_iStep_of_fireSeq hcyc hint)

/-- **Refuting liveness of a transition**: a firing sequence reaching a marking from which
`t` can never fire again, certified by an inductive invariant `I` that excludes `t`. -/
theorem not_liveLabel_of_fireSeq {M₀ M : Marking P} {ts : List T} {t : T}
    (h : N.fireSeq M₀ ts = some M) (I : Marking P → Prop) (hI : I M)
    (hstep : ∀ M u, I M → N.Enabled M u → I (N.fire M u))
    (hdead : ∀ M, I M → ¬ N.Enabled M t) : ¬ N.lts.LiveLabel M₀ t := by
  refine LTS.not_liveLabel_of_dead (reachable_of_fireSeq h) fun M' hM' hen => ?_
  have : I M' := hM'.invariant hI fun M u M'' hM ⟨hu, he⟩ => he ▸ hstep M u hM hu
  exact hdead M' this (lts_enabled_iff.1 hen)

end FireSeq

end Net

end AsyncLean
