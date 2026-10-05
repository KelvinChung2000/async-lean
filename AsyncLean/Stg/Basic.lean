/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.Basic

/-!
# Signal transition graphs and their circuit implementations

A *signal transition graph* (STG) is a Petri net whose transitions are labelled by signal
edges `z+` / `z-` or are dummies.  It is the standard specification formalism for
speed-independent asynchronous control circuits: input signals are driven by the
environment, output and internal signals by the circuit.

## Specification-level properties

* `StgModel.sg` — the *state graph*: states are pairs (marking, signal valuation).
* `Consistent` — rising and falling edges of every signal alternate.
* `CSC` — *complete state coding*: reachable states with the same signal valuation enable the
  same non-input edges, so the circuit can tell what to do from the signal values alone.
* `OutputPersistent` — an enabled non-input edge is never disabled by another edge.
* `Correct` — deadlock freedom, livelock freedom (no infinite run of dummies and internal
  edges) and liveness of the state graph.

## Implementations

An implementation assigns to every non-input signal `z` a *next-state function*
`F z : Val → Bool` (the Boolean function of the gate driving `z`).  The closed loop formed by
the circuit and the environment prescribed by the STG is `impl F`.  The circuit
**conforms** (`Conformant`) when, in every reachable state,

* (C1) every excited gate switches in a way the STG allows, and
* (C2) every non-input edge the STG expects is produced by an excited gate.

Main results:

* `impl_stepEqOn` / `impl_correct_iff` — a conforming circuit behaves exactly like the
  specification, so the closed loop is deadlock free, livelock free and live (and persistent)
  iff the STG is;
* `gate_switch_allowed` — the circuit never produces an output the specification forbids;
* `gate_persistent` — if the STG is output-persistent, the circuit is semi-modular (hazard
  free): an excited gate stays excited until it switches;
* `csc_iff_exists_conformant` — **a consistent STG has an implementation by next-state
  functions if and only if it has complete state coding.**
-/

namespace AsyncLean

/-- The role of a signal. -/
inductive SigKind where
  | input
  | output
  | internal
  deriving DecidableEq, Repr, Inhabited

/-- Signal valuations. -/
abbrev Val := ℕ → Bool

/-- An STG over a Petri net, with signals `0 … nsig-1`. -/
structure StgModel (P T : Type*) where
  /-- The underlying Petri net. -/
  net : Net P T
  /-- The label of a transition: a signal edge `(z, b)` (`z` becomes `b`) or a dummy. -/
  lab : T → Option (ℕ × Bool)
  /-- Number of signals. -/
  nsig : ℕ
  /-- The role of each signal. -/
  kind : ℕ → SigKind
  /-- Initial marking. -/
  M₀ : Marking P
  /-- Initial signal values. -/
  v₀ : Val

namespace StgModel

variable {P T : Type*} (N : StgModel P T)

/-- Update a valuation by a label. -/
def upd (v : Val) : Option (ℕ × Bool) → Val
  | none => v
  | some (z, b) => fun i => if i = z then b else v i

/-- The state graph. -/
def sg : LTS (Marking P × Val) T where
  step s t s' := N.net.Enabled s.1 t ∧ s' = (N.net.fire s.1 t, upd s.2 (N.lab t))

/-- The initial state. -/
def s₀ : Marking P × Val := (N.M₀, N.v₀)

/-- `z` is not an input (it is driven by the circuit). -/
def NonInput (z : ℕ) : Prop := N.kind z ≠ .input

/-- Dummies and edges of internal signals are not observable. -/
def Internal (t : T) : Prop :=
  N.lab t = none ∨ ∃ z b, N.lab t = some (z, b) ∧ N.kind z = .internal

/-- Every label refers to an existing signal. -/
def WellLabelled : Prop := ∀ t z b, N.lab t = some (z, b) → z < N.nsig

/-- Deadlock freedom, livelock freedom and liveness of the state graph. -/
def Correct : Prop :=
  N.sg.DeadlockFree N.s₀ ∧ N.sg.LivelockFree N.Internal N.s₀ ∧ N.sg.Live N.s₀

/-- Rising and falling edges alternate: an enabled edge `(z, b)` always changes `z`. -/
def Consistent : Prop :=
  ∀ s, N.sg.Reachable N.s₀ s → ∀ t z b, N.net.Enabled s.1 t → N.lab t = some (z, b) →
    s.2 z = !b

/-- The edge `(z, b)` is enabled in `s`. -/
def EnabledEdge (s : Marking P × Val) (z : ℕ) (b : Bool) : Prop :=
  ∃ t, N.net.Enabled s.1 t ∧ N.lab t = some (z, b)

/-- Complete state coding. -/
def CSC : Prop :=
  ∀ s₁ s₂, N.sg.Reachable N.s₀ s₁ → N.sg.Reachable N.s₀ s₂ → s₁.2 = s₂.2 →
    ∀ z b, N.NonInput z → (N.EnabledEdge s₁ z b ↔ N.EnabledEdge s₂ z b)

/-- Output persistence: an enabled non-input edge stays enabled when a transition not
changing its signal fires. -/
def OutputPersistent : Prop :=
  ∀ s, N.sg.Reachable N.s₀ s → ∀ z b, N.NonInput z → N.EnabledEdge s z b →
    ∀ u s', N.sg.step s u s' → (∀ b', N.lab u ≠ some (z, b')) → N.EnabledEdge s' z b

/-! ### Implementations -/

/-- Gate `z` is excited: its function disagrees with the current value. -/
def Excited (F : ℕ → Val → Bool) (v : Val) (z : ℕ) : Prop := F z v ≠ v z

/-- The closed loop of the circuit `F` with the environment prescribed by the STG: input edges
and dummies happen as the STG allows; a non-input edge happens when the STG allows it *and*
the gate driving the signal switches that way. -/
def impl (F : ℕ → Val → Bool) : LTS (Marking P × Val) T where
  step s t s' := N.sg.step s t s' ∧
    ∀ z b, N.lab t = some (z, b) → N.NonInput z → F z s.2 = b ∧ s.2 z ≠ b

/-- **Conformance** of the circuit `F` to the STG. -/
def Conformant (F : ℕ → Val → Bool) : Prop :=
  ∀ s, N.sg.Reachable N.s₀ s →
    (∀ z, z < N.nsig → N.NonInput z → Excited F s.2 z → N.EnabledEdge s z (F z s.2)) ∧
    (∀ t z b, N.net.Enabled s.1 t → N.lab t = some (z, b) → N.NonInput z →
      F z s.2 = b ∧ s.2 z ≠ b)

variable {N}

theorem upd_apply_of_ne {v : Val} {z : ℕ} {l : Option (ℕ × Bool)}
    (h : ∀ b, l ≠ some (z, b)) : upd v l z = v z := by
  cases l with
  | none => rfl
  | some p =>
    obtain ⟨z', b⟩ := p
    have : z ≠ z' := fun hz => h b (by rw [hz])
    simp [upd, this]

/-- A conforming circuit has exactly the steps of the specification in every reachable
state. -/
theorem impl_stepEqOn {F : ℕ → Val → Bool} (hc : N.Conformant F) :
    LTS.StepEqOn N.sg (N.impl F) N.s₀ := by
  intro s hs t s'
  constructor
  · intro hst
    refine ⟨hst, fun z b hl hz => (hc s hs).2 t z b hst.1 hl hz⟩
  · exact fun h => h.1

/-- **Implementation theorem.**  The closed loop of a conforming circuit and its
environment is deadlock free, livelock free and live exactly when the specification is. -/
theorem impl_correct_iff {F : ℕ → Val → Bool} (hc : N.Conformant F) :
    ((N.impl F).DeadlockFree N.s₀ ∧ (N.impl F).LivelockFree N.Internal N.s₀ ∧
      (N.impl F).Live N.s₀) ↔ N.Correct := by
  have h := impl_stepEqOn hc
  unfold Correct
  rw [h.deadlockFree_iff, h.livelockFree_iff, h.live_iff]

theorem impl_persistent_iff {F : ℕ → Val → Bool} (hc : N.Conformant F) :
    (N.impl F).Persistent N.s₀ ↔ N.sg.Persistent N.s₀ :=
  (impl_stepEqOn hc).persistent_iff.symm

/-- **No illegal output**: whenever a gate of a conforming circuit is excited, its switching
is a step allowed by the specification. -/
theorem gate_switch_allowed {F : ℕ → Val → Bool} (hc : N.Conformant F) {s : Marking P × Val}
    (hs : (N.impl F).Reachable N.s₀ s) {z : ℕ} (hz : z < N.nsig) (hni : N.NonInput z)
    (hex : Excited F s.2 z) :
    ∃ t s', (N.impl F).step s t s' ∧ N.lab t = some (z, F z s.2) ∧ s'.2 z = F z s.2 := by
  have hsA := (impl_stepEqOn hc).reachable_iff.2 hs
  obtain ⟨t, hen, hl⟩ := (hc s hsA).1 z hz hni hex
  refine ⟨t, _, ⟨⟨hen, rfl⟩, fun z' b hl' hz' => (hc s hsA).2 t z' b hen hl' hz'⟩, hl, ?_⟩
  simp [hl, upd]

/-- **Semi-modularity**: for an output-persistent specification, an excited gate of a
conforming circuit stays excited until its own signal changes — the circuit is hazard free. -/
theorem gate_persistent {F : ℕ → Val → Bool} (hc : N.Conformant F) (hp : N.OutputPersistent)
    {s s' : Marking P × Val} (hs : (N.impl F).Reachable N.s₀ s) {z : ℕ} (hz : z < N.nsig)
    (hni : N.NonInput z) (hex : Excited F s.2 z) {u : T} (hst : (N.impl F).step s u s')
    (hu : ∀ b', N.lab u ≠ some (z, b')) : Excited F s'.2 z := by
  have hsA := (impl_stepEqOn hc).reachable_iff.2 hs
  have hen := (hc s hsA).1 z hz hni hex
  have hen' := hp s hsA z _ hni hen u s' hst.1 hu
  have hs'A : N.sg.Reachable N.s₀ s' := hsA.tail ⟨u, hst.1⟩
  obtain ⟨t', ht', hl'⟩ := hen'
  obtain ⟨hF, -⟩ := (hc s' hs'A).2 t' z _ ht' hl' hni
  have hv : s'.2 z = s.2 z := by
    rw [hst.1.2]; exact upd_apply_of_ne hu
  unfold Excited at hex ⊢
  rw [hF, hv]
  exact hex

/-! ### Complete state coding characterises implementability -/

/-- A conforming implementation forces complete state coding. -/
theorem csc_of_conformant (hw : N.WellLabelled) {F : ℕ → Val → Bool} (hc : N.Conformant F) :
    N.CSC := by
  have key : ∀ s₁ s₂, N.sg.Reachable N.s₀ s₁ → N.sg.Reachable N.s₀ s₂ → s₁.2 = s₂.2 →
      ∀ z b, N.NonInput z → N.EnabledEdge s₁ z b → N.EnabledEdge s₂ z b := by
    intro s₁ s₂ h₁ h₂ hv z b hni ⟨t, hen, hl⟩
    obtain ⟨hF, hne⟩ := (hc s₁ h₁).2 t z b hen hl hni
    have hex : Excited F s₂.2 z := by
      unfold Excited; rw [← hv, hF]; exact fun h => hne h.symm
    have := (hc s₂ h₂).1 z (hw t z b hl) hni hex
    rwa [← hv, hF] at this
  intro s₁ s₂ h₁ h₂ hv z b hni
  exact ⟨key s₁ s₂ h₁ h₂ hv z b hni, key s₂ s₁ h₂ h₁ hv.symm z b hni⟩

open Classical in
/-- The next-state function determined by the specification: a non-input signal flips when
some reachable state with the current valuation enables one of its edges. -/
noncomputable def nextState (N : StgModel P T) (z : ℕ) (v : Val) : Bool :=
  if ∃ s, N.sg.Reachable N.s₀ s ∧ s.2 = v ∧ ∃ b, N.EnabledEdge s z b then !v z else v z

/-- With consistency and complete state coding, the next-state functions conform. -/
theorem nextState_conformant (hcons : N.Consistent) (hcsc : N.CSC) :
    N.Conformant N.nextState := by
  intro s hs
  refine ⟨fun z hz hni hex => ?_, fun t z b hen hl hni => ?_⟩
  · unfold Excited nextState at hex
    split_ifs at hex with h
    · obtain ⟨s', hs', hv, b, t, hen, hl⟩ := h
      have hb := hcons s' hs' t z b hen hl
      have : N.EnabledEdge s z b := (hcsc s' s hs' hs hv z b hni).1 ⟨t, hen, hl⟩
      unfold nextState
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨s', hs', hv, b, t, hen, hl⟩), ← hv, hb, Bool.not_not]
      exact this
    · exact absurd rfl hex
  · have hb := hcons s hs t z b hen hl
    unfold nextState
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨s, hs, rfl, b, t, hen, hl⟩), hb, Bool.not_not]
    exact ⟨rfl, by cases b <;> simp⟩

/-- **Implementability theorem.**  A consistent, well-labelled STG can be implemented by
next-state functions (one gate per non-input signal, depending only on the signal values)
if and only if it has complete state coding. -/
theorem csc_iff_exists_conformant (hw : N.WellLabelled) (hcons : N.Consistent) :
    N.CSC ↔ ∃ F, N.Conformant F :=
  ⟨fun hcsc => ⟨_, nextState_conformant hcons hcsc⟩,
    fun ⟨_, hc⟩ => csc_of_conformant hw hc⟩

end StgModel

end AsyncLean
