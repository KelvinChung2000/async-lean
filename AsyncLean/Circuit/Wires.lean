/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Circuit.Basic

/-!
# Wire delays: quasi-delay-insensitive circuits

Speed independence (`Circuit.SpeedIndependent`) assumes arbitrary *gate* delays but zero
*wire* delays: when a signal forks to several gates, all of them see a transition at the same
instant (every fork is *isochronic*).  A circuit is **quasi-delay-insensitive** (QDI) when it
stays correct with arbitrary delays on every wire branch as well, except on the forks that
are explicitly declared isochronic.

`Circuit.withWires C iso` makes wire delays explicit: every *branch* — a gate `k` reading a
signal `i` other than its own output — gets its own internal buffer gate (a wire) whose output
replaces `i` in the function of gate `k`.  Each wire is an independent delay, so the forks of
`i` are no longer isochronic.  Isochronic forks are declared by `iso : Forks`, either for all
branches of a signal (no wire at all; a plain list of signals coerces to `Forks`) or for a
group of branches of a signal (the group shares one wire).  QDI is then speed independence (and
correctness) of the transformed circuit, decided by the same verified checker:

* `Circuit.QDI C iso` — hazard freedom under arbitrary gate *and* wire delays;
* `Circuit.QDICorrect C iso` — no deadlock, no livelock, every gate live under arbitrary
  gate and wire delays.

A gate's feedback from its own output (as in a C-element) is internal to the gate and gets no
wire.
-/

namespace AsyncLean

namespace BExpr

/-- The signals read by an expression. -/
def vars : BExpr → List ℕ
  | var i => [i]
  | const _ => []
  | not e => e.vars
  | and a b => a.vars ++ b.vars
  | or a b => a.vars ++ b.vars
  | xor a b => a.vars ++ b.vars

/-- Rename the signals read by an expression. -/
def rename (f : ℕ → ℕ) : BExpr → BExpr
  | var i => var (f i)
  | const b => const b
  | not e => not (e.rename f)
  | and a b => and (a.rename f) (b.rename f)
  | or a b => or (a.rename f) (b.rename f)
  | xor a b => xor (a.rename f) (b.rename f)

theorem eval_rename (f : ℕ → ℕ) (v : ℕ → Bool) (e : BExpr) :
    (e.rename f).eval v = e.eval (v ∘ f) := by
  induction e <;> simp_all [rename, eval]

end BExpr

/-- Which forks are *isochronic*: the gates reading them see a transition at the same time. -/
structure Forks where
  /-- Signals all of whose branches are isochronic: every gate reads them directly, without a
  wire delay. -/
  signals : List ℕ := []
  /-- Groups of isochronic branches `(gate, signal)` of the same signal: the branches of a group
  share one wire, so they see each transition at the same time — but possibly later than the
  other branches of the signal and than the driving gate itself. -/
  groups : List (List (ℕ × ℕ)) := []
  deriving Repr, Inhabited

/-- A list of signals declares all their forks isochronic. -/
instance : Coe (List ℕ) Forks := ⟨fun l => { signals := l }⟩

/-- The wire used by the branch `(k, i)`: itself, or the first branch of signal `i` in its
isochronic group. -/
def Forks.key (F : Forks) (k i : ℕ) : ℕ × ℕ :=
  match F.groups.find? (·.contains (k, i)) with
  | some g => (((g.find? (·.2 == i)).map Prod.fst).getD k, i)
  | none => (k, i)

@[simp] theorem Forks.key_snd (F : Forks) (k i : ℕ) : (F.key k i).2 = i := by
  unfold Forks.key; split <;> rfl

namespace Circuit

variable (C : Circuit)

/-- The wires: one per wire branch `(k, i)` — gate `k` reading signal `i ≠ out k` — except
that the branches of an isochronic signal have none, and the branches of an isochronic group
share one (named by `Forks.key`). -/
def branches (iso : Forks := {}) : List (ℕ × ℕ) :=
  (C.gates.zipIdx.flatMap fun (g, k) =>
    (g.fn.vars.eraseDups.filter fun i =>
        i != g.out && decide (i < C.signals) && !iso.signals.contains i)
      |>.map (iso.key k ·)).eraseDups

/-- The signal that gate `k` reads in place of `i`: its wire, if it has one (a non-existent
signal, reading `false`, stays non-existent). -/
def wireOf (iso : Forks) (k i : ℕ) : ℕ :=
  if i < C.signals then
    match (C.branches iso).idxOf? (iso.key k i) with
    | some j => C.signals + j
    | none => i
  else C.signals + (C.branches iso).length

/-- The circuit with an independent delay (an internal buffer gate) on every wire branch not
declared isochronic.  Gates keep their indices; the wires come after them. -/
def withWires (iso : Forks := {}) : Circuit where
  signals := C.signals + (C.branches iso).length
  gates :=
    (C.gates.zipIdx.map fun (g, k) => { g with fn := g.fn.rename (C.wireOf iso k) }) ++
      ((C.branches iso).zipIdx.map fun ((k, i), j) =>
        { name := s!"wire {i}→{(C.gates[k]?.map (·.name)).getD ""}", out := C.signals + j,
          fn := .var i, internal := true })
  init := C.init ++ (C.branches iso).map fun (_, i) => C.init.getD i false

/-- **Quasi-delay-insensitivity**: hazard freedom under arbitrary gate and wire delays (only the
forks declared in `iso` are assumed isochronic). -/
def QDI (iso : Forks := {}) : Prop := (C.withWires iso).SpeedIndependent

/-- Correctness (no deadlock, no livelock, liveness) under arbitrary gate and wire delays. -/
def QDICorrect (iso : Forks := {}) : Prop := (C.withWires iso).Correct

end Circuit

end AsyncLean
