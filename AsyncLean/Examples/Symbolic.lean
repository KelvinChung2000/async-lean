/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
import AsyncLean.Examples.Philosophers
import AsyncLean.Examples.Compositional
import AsyncLean.AxiomAudit

/-!
# Example: symbolic certificates

`async_bdd` proves properties of a safe net from decision diagrams, without enumerating the
reachable markings: a diagram of an inductive invariant, closed under every transition, and a
diagram of witness transitions.  For liveness and livelock freedom, weights on the places that
the witnesses (respectively the internal transitions) decrease replace distances and ranks
when they exist; otherwise the measure is lexicographic, and the diagrams of distances and
ranks only count the steps that keep the weights unchanged.  The kernel checks each diagram by joint walks before and after firing
(`PNet.of_checkBDD`).  The certificate grows with the structure of the reachable markings
rather than with their number.  `async_decide` falls back on it for safe nets whose state
space is too large to explore.
-/

namespace AsyncLean.Examples

/-- Ten dining philosophers never put two tokens on a place (`3^10`-scale state space). -/
theorem philosophers10_safe : (philosophers 10 true).Safe := by
  async_bdd

/-- A 20-stage FIFO is deadlock free, from a symbolic invariant and witnesses. -/
theorem fifo20_deadlockFree_bdd :
    (fifo 20 "in" "out").toNet.lts.DeadlockFree (fifo 20 "in" "out").M₀ := by
  async_bdd

/-- Full correctness of a 20-stage FIFO (about a million markings): the moves and the output
decrease a linear potential down to the empty FIFO, and the moves a linear rank. -/
theorem fifo20_correct_bdd : (fifo 20 "in" "out").Correct := by
  async_bdd

/-- Twelve dining philosophers with resource ordering are deadlock free, live, and safe. -/
theorem philosophers12_correct_bdd : (philosophers 12 true).Correct := by
  async_bdd

/-- `k` independent four-phase handshakes: the request rises (`x`), is acknowledged (`u`,
internal), falls (`y`), and the acknowledgement falls (`v`, internal).  Places `4 i` and
`4 i + 1`: acknowledgement low or high; `4 i + 2` and `4 i + 3`: request low or high. -/
def handshakes (k : ℕ) : PNet where
  places := 4 * k
  trans := (List.range k).flatMap fun i =>
    let a0 := 4 * i; let a1 := 4 * i + 1; let r0 := 4 * i + 2; let r1 := 4 * i + 3
    [ { name := "req+", pre := [a0, r0], post := [a0, r1] },
      { name := "ack+", pre := [a0, r1], post := [a1, r1], internal := true },
      { name := "req-", pre := [a1, r1], post := [a1, r0] },
      { name := "ack-", pre := [a1, r0], post := [a0, r0], internal := true } ]
  init := (List.range k).flatMap fun _ => [1, 0, 1, 0]

/-- Four handshakes are `Correct`.  The acknowledgements rise and fall, so no weights decrease
both, neither as witnesses nor as internal transitions: the weights decrease the falling
requests, and the diagrams of distances and ranks count the acknowledgements. -/
theorem handshakes4_correct_bdd : (handshakes 4).Correct := by
  async_bdd

#assert_standard_axioms philosophers10_safe fifo20_deadlockFree_bdd fifo20_correct_bdd
  philosophers12_correct_bdd handshakes4_correct_bdd

end AsyncLean.Examples
