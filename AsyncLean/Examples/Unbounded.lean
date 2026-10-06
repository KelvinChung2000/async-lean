/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
import AsyncLean.Checker.Abstract
import AsyncLean.Auto.Structural
import AsyncLean.AxiomAudit

/-!
# Example: unbounded nets

These nets have infinitely many reachable markings, so the explicit model checker cannot
enumerate them.  `async_decide` notices that the state space does not close and checks the
counter abstraction instead (`PNet.of_checkAbs`): places are tracked exactly up to a cap,
and "cap or more" above it.

1. A producer filling an unbounded buffer read by a consumer.
2. A server with an unbounded request queue that serves one or two requests at a time (an
   arc of weight two, so the cap must be at least two).
3. A producer that may kill the consumer: a deadlock, found and refuted.
4. A buffer drained by an internal transition.  The abstraction cannot prove livelock
   freedom (at the cap, draining may leave the abstract count unchanged), but a linear
   ranking function can: `async_structural` proves it for every initial marking.
-/

namespace AsyncLean.Examples

/-- Producer (place 0), unbounded buffer (place 1), consumer (place 2). -/
def prodCons : PNet where
  places := 3
  trans := [{ name := "produce", pre := [0], post := [0, 1] },
            { name := "consume", pre := [1, 2], post := [2] }]
  init := [1, 0, 1]

theorem prodCons_correct : prodCons.Correct := by async_decide

/-- Request queue (place 0), idle server (place 1), busy server (place 2). -/
def server : PNet where
  places := 3
  trans := [{ name := "request", pre := [], post := [0] },
            { name := "serve1", pre := [0, 1], post := [2] },
            { name := "serve2", pre := [0, 0, 1], post := [2] },
            { name := "done", pre := [2], post := [1], internal := true }]
  init := [0, 1, 0]

theorem server_correct : server.Correct := by async_decide

/-- A larger cap gives a finer abstraction. -/
theorem server_live : server.toNet.lts.Live server.M₀ := by async_decide (cap := 4)

/-- The producer may kill the consumer. -/
def killer : PNet where
  places := 3
  trans := [{ name := "produce", pre := [0], post := [0, 1] },
            { name := "kill", pre := [0, 2], post := [] },
            { name := "consume", pre := [1, 2], post := [2] }]
  init := [1, 0, 1]

/--
error: async_decide: DEADLOCK reachable by firing [kill(#1)].
Prove it with: PNet.not_deadlockFree_of_refute (ts := [1]) (by decide +kernel)
-/
#guard_msgs in
example : killer.Correct := by async_decide

theorem killer_deadlocks : ¬ killer.toNet.lts.DeadlockFree killer.M₀ :=
  PNet.not_deadlockFree_of_refute (ts := [1]) (by decide +kernel)

/-- Producer (place 0) and a buffer (place 1) drained internally. -/
def drain : PNet where
  places := 2
  trans := [{ name := "produce", pre := [0], post := [0, 1] },
            { name := "drain", pre := [1], post := [], internal := true }]
  init := [1, 0]

theorem drain_deadlockFree : drain.toNet.lts.DeadlockFree drain.M₀ := by async_decide
theorem drain_live : drain.toNet.lts.Live drain.M₀ := by async_decide
theorem drain_livelockFree : drain.toNet.lts.LivelockFree drain.Internal drain.M₀ := by
  async_structural

#assert_standard_axioms prodCons_correct server_correct server_live killer_deadlocks
  drain_deadlockFree drain_live drain_livelockFree

end AsyncLean.Examples
