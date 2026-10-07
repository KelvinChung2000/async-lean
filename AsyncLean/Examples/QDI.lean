/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Circuit.QDI
import AsyncLean.Checker.Tactic
import AsyncLean.AxiomAudit

/-!
# Example: wire delays and isochronic forks

1. A four-stage Muller C-element ring is **quasi-delay-insensitive**: it stays hazard free
   and correct with arbitrary delays on every wire.  By `Circuit.speedIndependent_of_qdi` and
   `Circuit.correct_of_qdi`, this re-proves its speed independence and correctness.
2. A circuit that is speed independent but **not** QDI, because it relies on isochronic forks.
   Signal `c` drives an inverter `b := ¬c`, and an AND gate `a := ¬c ∧ b` reads both `c` and
   `b`; `c` is a C-element of `a` and `b`.  With zero wire delays the AND gate sees `c` and
   `¬c` change together.  With wire delays, a transition of `c` on the wire to the AND gate is
   never acknowledged and can be overtaken by the next one: a glitch.  Declaring the forks of
   `c` and `b` isochronic (`iso := [0, 2]`) restores hazard freedom.  It is enough to declare
   two isochronic *groups of branches*: `c` to `a` and `b`, and `b` to `a` and `c`.  Each group
   then shares one wire, whose delay is still arbitrary.
-/

namespace AsyncLean.Examples.QDI

open BExpr

/-- A ring of `n` C-elements, stage `i` computing `cᵢ := C(cᵢ₋₁, ¬cᵢ₊₁)`; stage `0` is
observable, the others internal. -/
def cRingN (n : ℕ) (init : List Bool) : Circuit where
  signals := n
  gates := (List.range n).map fun i =>
    { name := s!"c{i}", out := i, fn := celemInv ((i + n - 1) % n) ((i + 1) % n) i,
      internal := decide (i ≠ 0) }
  init := init

/-- Four stages, one token (192 states once the eight wires are added). -/
def ring := cRingN 4 [true, false, false, false]

theorem ring_qdi : ring.QDI := by async_decide

theorem ring_qdiCorrect : ring.QDICorrect := by async_decide

/-- Speed independence follows from QDI (here it was also checked directly). -/
example : ring.SpeedIndependent := Circuit.speedIndependent_of_qdi (by decide) ring_qdi

example : ring.Correct := Circuit.correct_of_qdi (by decide) ring_qdi ring_qdiCorrect

/-- Signals: `c` (0), `a` (1), `b` (2). -/
def forkC : Circuit where
  signals := 3
  gates := [
    { name := "c", out := 0, fn := celem 1 2 0 },
    { name := "a", out := 1, fn := and (not (var 0)) (var 2) },
    { name := "b", out := 2, fn := inv 0 }]
  init := [false, false, false]

theorem forkC_correct : forkC.Correct := by async_decide

theorem forkC_speedIndependent : forkC.SpeedIndependent := by async_decide

/-- Even with wire delays it never deadlocks or livelocks… -/
theorem forkC_qdiCorrect : forkC.QDICorrect := by async_decide

/-- …but it has a hazard.  After `b+`, the wires from `b`, `a+`, the wire from `a`, `c+`, the
wire from `c` to `b`, `b-`, the wires from `b`, `a-` and the wire from `a`, the wire from `c`
to the AND gate still carries the old value `0` of `c` (it is excited to switch to `1`), when
`c-` makes it stable again: a glitch on the wire. -/
theorem forkC_not_qdi : ¬ forkC.QDI :=
  Circuit.not_speedIndependent_of_refute (gs := [2, 4, 6, 1, 3, 0, 7, 2, 4, 6, 1, 3])
    (g := ⟨5, by decide⟩) (g' := ⟨0, by decide⟩) (by decide +kernel)

/-- With the forks of `c` and `b` isochronic, it is hazard free. -/
theorem forkC_qdi_iso : forkC.QDI [0, 2] := by async_decide

/-- Finer: only the branches from `c` to gates `a` (1) and `b` (2) are isochronic, and so are the
branches from `b` to gates `c` (0) and `a` (1); each pair shares a wire with arbitrary delay. -/
theorem forkC_qdi_groups : forkC.QDI { groups := [[(1, 0), (2, 0)], [(0, 2), (1, 2)]] } := by
  async_decide

/-- One isochronic fork is not enough: the AND gate can still see a stale `b`. -/
theorem forkC_not_qdi_one_group : ¬ forkC.QDI { groups := [[(1, 0), (2, 0)]] } :=
  Circuit.not_speedIndependent_of_refute (gs := [2, 4, 6, 1, 3, 0, 5, 1, 2, 3, 4, 0, 5])
    (g := ⟨1, by decide⟩) (g' := ⟨6, by decide⟩) (by decide +kernel)

#assert_standard_axioms ring_qdi ring_qdiCorrect forkC_correct forkC_speedIndependent
  forkC_qdiCorrect forkC_not_qdi forkC_qdi_iso forkC_qdi_groups
  forkC_not_qdi_one_group

end AsyncLean.Examples.QDI
