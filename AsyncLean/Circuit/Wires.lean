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
signal `i` other than its own output, with `i ∉ iso` — gets its own internal buffer gate (a
wire) whose output replaces `i` in the function of gate `k`.  Each wire is an independent
delay, so the forks of `i` are no longer isochronic.  QDI is then speed independence (and
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

namespace Circuit

variable (C : Circuit)

/-- The wire branches `(k, i)`: gate `k` reads signal `i ≠ out k`, `i ∉ iso`. -/
def branches (iso : List ℕ := []) : List (ℕ × ℕ) :=
  C.gates.zipIdx.flatMap fun (g, k) =>
    (g.fn.vars.eraseDups.filter fun i => i != g.out && decide (i < C.signals) && !iso.contains i)
      |>.map (k, ·)

/-- The signal that gate `k` reads in place of `i`: its wire, if it has one (a non-existent
signal, reading `false`, stays non-existent). -/
def wireOf (iso : List ℕ) (k i : ℕ) : ℕ :=
  if i < C.signals then
    match (C.branches iso).idxOf? (k, i) with
    | some j => C.signals + j
    | none => i
  else C.signals + (C.branches iso).length

/-- The circuit with an independent delay (an internal buffer gate) on every wire branch not
declared isochronic.  Gates keep their indices; the wires come after them. -/
def withWires (iso : List ℕ := []) : Circuit where
  signals := C.signals + (C.branches iso).length
  gates :=
    (C.gates.zipIdx.map fun (g, k) => { g with fn := g.fn.rename (C.wireOf iso k) }) ++
      ((C.branches iso).zipIdx.map fun ((k, i), j) =>
        { name := s!"wire {i}→{(C.gates[k]?.map (·.name)).getD ""}", out := C.signals + j,
          fn := .var i, internal := true })
  init := C.init ++ (C.branches iso).map fun (_, i) => C.init.getD i false

/-- **Quasi-delay-insensitivity**: hazard freedom under arbitrary gate and wire delays (only the
forks of the signals in `iso` are assumed isochronic). -/
def QDI (iso : List ℕ := []) : Prop := (C.withWires iso).SpeedIndependent

/-- Correctness (no deadlock, no livelock, liveness) under arbitrary gate and wire delays. -/
def QDICorrect (iso : List ℕ := []) : Prop := (C.withWires iso).Correct

end Circuit

end AsyncLean
