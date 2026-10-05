/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

/-!
# Labelled transition systems

Every behavioural model in this library (Petri nets, marked graphs, signal
transition graphs, explicit finite state spaces) is given a semantics as a
*labelled transition system* (LTS).  All the correctness notions — deadlock
freedom, livelock freedom, liveness — are defined once, here and in
`AsyncLean.LTS.Properties`, and then transported to the concrete models.

## Main definitions

* `LTS S L` : a transition relation `S → L → S → Prop`.
* `LTS.Step` : the unlabelled one-step relation.
* `LTS.Reachable s₀ s` : `s` is reachable from `s₀` (reflexive–transitive closure).
* `LTS.Enabled s l` : some `l`-labelled step leaves `s`.
* `LTS.IStep internal` : one step whose label satisfies the predicate `internal`
  (the silent / τ / dummy steps of the model).
-/

namespace AsyncLean

/-- A labelled transition system with states `S` and labels (actions) `L`. -/
structure LTS (S : Type*) (L : Type*) where
  /-- `step s l s'` : the system can move from `s` to `s'` performing `l`. -/
  step : S → L → S → Prop

namespace LTS

variable {S L : Type*} (A : LTS S L)

/-- Unlabelled one-step relation. -/
def Step (s s' : S) : Prop := ∃ l, A.step s l s'

/-- `s` is reachable from `s₀` in zero or more steps. -/
def Reachable (s₀ s : S) : Prop := Relation.ReflTransGen A.Step s₀ s

/-- The label `l` is enabled in state `s`. -/
def Enabled (s : S) (l : L) : Prop := ∃ s', A.step s l s'

/-- One step whose label is *internal* (silent). -/
def IStep (internal : L → Prop) (s s' : S) : Prop := ∃ l, internal l ∧ A.step s l s'

variable {A}

namespace Reachable

@[refl] theorem refl (s : S) : A.Reachable s s := Relation.ReflTransGen.refl

theorem tail {s₀ s s' : S} (h : A.Reachable s₀ s) (h' : A.Step s s') : A.Reachable s₀ s' :=
  Relation.ReflTransGen.tail h h'

theorem head {s₀ s s' : S} (h : A.Step s₀ s) (h' : A.Reachable s s') : A.Reachable s₀ s' :=
  Relation.ReflTransGen.head h h'

theorem trans {s₁ s₂ s₃ : S} (h₁ : A.Reachable s₁ s₂) (h₂ : A.Reachable s₂ s₃) :
    A.Reachable s₁ s₃ :=
  Relation.ReflTransGen.trans h₁ h₂

theorem single {s s' : S} (h : A.Step s s') : A.Reachable s s' :=
  Relation.ReflTransGen.single h

theorem of_step {s s' : S} {l : L} (h : A.step s l s') : A.Reachable s s' :=
  single ⟨l, h⟩

/-- Reachable states satisfy every predicate that holds initially and is preserved by
every step (an *inductive invariant*). -/
theorem invariant {I : S → Prop} {s₀ s : S} (h : A.Reachable s₀ s) (h₀ : I s₀)
    (hstep : ∀ s l s', I s → A.step s l s' → I s') : I s := by
  induction h with
  | refl => exact h₀
  | tail _ hst ih => obtain ⟨l, hl⟩ := hst; exact hstep _ _ _ ih hl

end Reachable

theorem IStep.step {internal : L → Prop} {s s' : S} (h : A.IStep internal s s') :
    A.Step s s' := by
  obtain ⟨l, -, hl⟩ := h; exact ⟨l, hl⟩

theorem Reachable.of_iStep_rtc {internal : L → Prop} {s s' : S}
    (h : Relation.ReflTransGen (A.IStep internal) s s') : A.Reachable s s' :=
  Relation.ReflTransGen.mono (fun _ _ h => IStep.step h) _ _ h


/-- Reachability via an explicit list of labelled steps (a *trace*).  `Path s ls s'` says
that performing the labels `ls` in order leads from `s` to `s'`. -/
inductive Path (A : LTS S L) : S → List L → S → Prop
  | nil (s : S) : Path A s [] s
  | cons {s s' s'' : S} {l : L} {ls : List L} :
      A.step s l s' → Path A s' ls s'' → Path A s (l :: ls) s''

theorem Path.reachable {s s' : S} {ls : List L} (h : A.Path s ls s') : A.Reachable s s' := by
  induction h with
  | nil => exact Reachable.refl _
  | cons hst _ ih => exact Reachable.head ⟨_, hst⟩ ih

theorem Reachable.exists_path {s s' : S} (h : A.Reachable s s') : ∃ ls, A.Path s ls s' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], Path.nil _⟩
  | head hst _ ih =>
    obtain ⟨l, hl⟩ := hst
    obtain ⟨ls, hls⟩ := ih
    exact ⟨l :: ls, Path.cons hl hls⟩

theorem reachable_iff_exists_path {s s' : S} : A.Reachable s s' ↔ ∃ ls, A.Path s ls s' :=
  ⟨Reachable.exists_path, fun ⟨_, h⟩ => h.reachable⟩

theorem Path.append {s s' s'' : S} {ls ls' : List L} (h : A.Path s ls s')
    (h' : A.Path s' ls' s'') : A.Path s (ls ++ ls') s'' := by
  induction h with
  | nil => exact h'
  | cons hst _ ih => exact Path.cons hst (ih h')

end LTS

end AsyncLean
