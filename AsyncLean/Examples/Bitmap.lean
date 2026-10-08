/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
import AsyncLean.Examples.Symbolic
import AsyncLean.AxiomAudit

/-!
# Example: bit-parallel certificates

`async_bitmap` (and `async_decide`, when it estimates them cheaper than a reduced state space)
checks sets of markings as bitmaps: markings are packed by a *layout* — a component of places
of which exactly one is marked takes the bits of its marked place's index — and the markings
that agree on their high bits form a *chunk*, one number with a bit per marking.  The kernel
fires a transition on a whole chunk with one shift (`AsyncLean.Checker.Bitmap`).

These designs are *tightly coupled*: partial-order reduction gains little on them (every
handshake has internal steps next to external ones, and all processes meet at the barrier),
but their packed reachable markings are dense, which is where bitmaps shine.

* `handshakes 8`: eight independent four-phase handshakes, `4^8 = 65 536` markings.
* `barrier 8`: eight processes that start, work (internal) and finish, then meet at a barrier:
  `3^8 = 6 561` markings.
* `logger`: a handshake that also logs every request to a place that nothing consumes.  The
  log is unbounded, so the net has infinitely many reachable markings, yet the layout leaves
  the log out — no transition reads it — and the check is exact.
* Bounds come with the layout: every place of a component holds at most one token.
-/

namespace AsyncLean.Examples

/-- `n` processes meeting at a barrier: each starts, works (internal) and is done; the barrier
fires when all are done. -/
def barrier (n : ℕ) : PNet where
  places := 3 * n
  trans := (List.range n).flatMap (fun i =>
      [{ name := "begin", pre := [3 * i], post := [3 * i + 1] },
       { name := "finish", pre := [3 * i + 1], post := [3 * i + 2], internal := true }]) ++
    [{ name := "barrier", pre := (List.range n).map (3 * · + 2),
       post := (List.range n).map (3 * ·) }]
  init := (List.range n).flatMap fun _ => [1, 0, 0]

theorem handshakes8_correct : (handshakes 8).Correct := by async_bitmap

theorem barrier8_correct : (barrier 8).Correct := by async_bitmap

theorem barrier8_safe : (barrier 8).Safe := by async_bitmap

/-- A four-phase handshake that logs every request in place 4. -/
def logger : PNet where
  places := 5
  trans := [{ name := "req+", pre := [0, 2], post := [0, 3, 4] },
            { name := "ack+", pre := [0, 3], post := [1, 3], internal := true },
            { name := "req-", pre := [1, 3], post := [1, 2] },
            { name := "ack-", pre := [1, 2], post := [0, 2], internal := true }]
  init := [1, 0, 1, 0, 0]

/-- Infinitely many reachable markings, checked exactly: the log is not in the layout. -/
theorem logger_correct : logger.Correct := by async_bitmap

/-! ### Gate-level circuits

A circuit state is a valuation of its signals, so its packed states are bit vectors and need
no layout: the rise and the fall of each gate are transitions whose guard is a Boolean
expression, evaluated on a whole chunk by bitwise operations (`Circuit.of_checkBitmap`). -/

/-- A Muller pipeline ring of `n` C-elements: stage `i` follows its predecessor and the inverse
of its successor; `init` gives the initial outputs. -/
def mullerRing (n : ℕ) (init : List Bool) : Circuit where
  signals := n
  gates := (List.range n).map fun i =>
    { name := s!"c{i}", out := i, fn := BExpr.celemInv ((i + n - 1) % n) ((i + 1) % n) i,
      internal := i != 0 }
  init := init

theorem mullerRing12_correct :
    (mullerRing 12 [true, true, false, false, true, true, false, false, true, true, false,
      false]).Correct := by
  async_bitmap

#assert_standard_axioms handshakes8_correct barrier8_correct barrier8_safe logger_correct
  mullerRing12_correct

end AsyncLean.Examples
