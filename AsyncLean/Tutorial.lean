/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
import AsyncLean.Auto.Structural
import AsyncLean.Import.G
import AsyncLean.Circuit.QDI
import AsyncLean.LTS.Fairness
import AsyncLean.Checker.Abstract
import AsyncLean.Circuit.Step
import AsyncLean.Examples.Philosophers
import AsyncLean.Examples.Compositional
import AsyncLean.Examples.Symbolic
import AsyncLean.AxiomAudit
import Mathlib.Data.Fin.VecNotation

/-!
# Tutorial: proving that an asynchronous design never deadlocks or livelocks

This file is a walkthrough of the library.  It is compiled with the rest of the project, so
every step is checked.  Read it top to bottom; each section is independent of the later ones.

1. A Petri-net protocol, proved correct by `async_decide`.
2. A broken variant: reading a counterexample and proving the negation.
3. Structural proofs that need no state exploration (`async_structural`).
4. From an STG specification to a gate-level implementation.
5. Gate delays and wire delays: speed independence and quasi-delay-insensitivity.
6. From "can" to "will": fairness.
7. Unbounded nets and concurrent firing.
8. Large state spaces: partial-order reduction and the state equation.
9. Networks with dynamic routing: routing deadlock and livelock.

Every theorem below is audited at the end with `#assert_standard_axioms`: the build fails if
any of them depends on `sorry`, `native_decide` or an axiom other than `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace AsyncLean.Tutorial

open BExpr

/-! ## 1. A protocol as a Petri net

A `PNet` lists its places (by index), its transitions (input places `pre`, output places
`post`; repeat a place for a weight above one) and its initial marking.  Transitions marked
`internal` are silent; livelock is about them.

Here a client sends a request, a server computes internally and acknowledges, and both return
to their initial state (a four-phase handshake). -/

def handshake : PNet where
  places := 5
  trans := [
    { name := "req+",    pre := [0], post := [1] },
    { name := "compute", pre := [1], post := [2], internal := true },
    { name := "ack+",    pre := [2], post := [3] },
    { name := "req-",    pre := [3], post := [4] },
    { name := "ack-",    pre := [4], post := [0] }]
  init := [1, 0, 0, 0, 0]

/-- `Correct` = deadlock free ∧ livelock free ∧ every transition live.  `async_decide`
explores the state space at elaboration time (untrusted), builds a certificate, and the
kernel checks it with a verified checker. -/
theorem handshake_correct : handshake.Correct := by async_decide

/-- The individual properties are ordinary `LTS` predicates about the abstract net. -/
example : handshake.toNet.lts.DeadlockFree handshake.M₀ := handshake_correct.1

/-- Boundedness and safeness are checked the same way. -/
theorem handshake_safe : handshake.Safe := by async_decide

/-! ## 2. When something is wrong

Two clients share a server through a lock; the second client forgets to release it.  The
design deadlocks.  `async_decide` would fail with the message below, which is also what
`#eval N.diagnose` prints. -/

def sharedServer : PNet where
  places := 5
  trans := [
    { name := "lock₁",   pre := [0, 4], post := [1] },
    { name := "unlock₁", pre := [1],    post := [0, 4] },
    { name := "lock₂",   pre := [2, 4], post := [3] },
    { name := "done₂",   pre := [3],    post := [2] }]   -- bug: the lock is not returned
  init := [1, 0, 1, 0, 1]

/--
info: "DEADLOCK reachable by firing [lock₂(#2), done₂(#3)].\nProve it with: PNet.not_deadlockFree_of_refute (ts := [2, 3]) (by decide +kernel)"
-/
#guard_msgs in
#eval sharedServer.diagnose

/-- The suggested refutation proves the negation, again checked by the kernel. -/
theorem sharedServer_deadlocks :
    ¬ sharedServer.toNet.lts.DeadlockFree sharedServer.M₀ :=
  PNet.not_deadlockFree_of_refute (ts := [2, 3]) (by decide +kernel)

/-! ## 3. Structural proofs

Model checking needs a finite and reasonably small state space.  `async_structural` instead
finds *structural certificates* by linear programming or graph search — place invariants for
safeness, linear ranking functions for livelock freedom, Commoner's theorems for liveness —
and the kernel checks them.  No state is explored. -/

/-- Safeness from place invariants. -/
example : handshake.Safe := by async_structural

/-- Livelock freedom from a linear ranking function, for *every* initial marking. -/
example (M₀ : Marking (Fin 5)) :
    handshake.toNet.lts.LivelockFree handshake.Internal M₀ := by
  async_structural

/-- Liveness of a free-choice net (here written as an abstract `Net`): a request forks into
an acknowledgement and an environment-resolved choice, which join again.  Commoner's
siphon–trap theorem applies (`Net.live_iff_siphonTrap`; it also refutes liveness). -/
def choiceNet : Net (Fin 6) (Fin 6) where
  pre := ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 1]]
  post := ![![0, 1, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]]

theorem choiceNet_live : choiceNet.lts.Live ![1, 0, 0, 0, 0, 0] := by async_structural

/-! ## 4. From an STG specification to gates

A *signal transition graph* is a Petri net whose transitions are rising and falling edges of
signals.  STGs are usually written in the `.g` format of Petrify and Workcraft;
`stg_from_g` reads a file and `stg_from_g_text` reads text. -/

stg_from_g_text spec "
.model celement
.inputs a b
.outputs c
.graph
a+ c+
b+ c+
c+ a- b-
a- c-
b- c-
c- a+ b+
.marking { <c-,a+> <c-,b+> }
.initial_state !a !b !c
.end"

/-- The specification itself is correct, consistent (edges alternate), has complete state
coding (so it is implementable), and never withdraws an enabled output. -/
theorem spec_ok :
    spec.model.Correct ∧ spec.model.Consistent ∧ spec.model.CSC ∧
      spec.model.OutputPersistent :=
  ⟨by async_decide, by async_decide, by async_decide, by async_decide⟩

/-- An implementation is a list of gates driving the non-input signals (signals are numbered
in declaration order: `a = 0`, `b = 1`, `c = 2`).  `gates_from_verilog` reads them from a
Verilog netlist instead. -/
def celemGates : List Gate := [{ name := "C", out := 2, fn := celem 0 1 2 }]

/-- *Conformance*: every output edge the gates can produce is allowed by the specification.
By `Stg.implementation_correct`, the closed loop of gates and environment then inherits the
correctness of the specification, and every gate switching is allowed by it; `async_decide`
also checks the closed loop directly. -/
theorem impl_ok :
    spec.model.Conformant (spec.gateFn celemGates) ∧
      (spec.model.impl (spec.gateFn celemGates)).DeadlockFree spec.model.s₀ :=
  ⟨by async_decide, by async_decide⟩

/-! ## 5. Gate delays and wire delays

A `Circuit` is a closed netlist: one gate per driven signal, the environment included.
`SpeedIndependent` is hazard freedom under arbitrary *gate* delays.  `QDI` adds an
independent delay on every wire branch (except forks declared isochronic), and
`Circuit.speedIndependent_of_qdi` shows QDI implies speed independence.

Below, `c` drives an inverter `b := ¬c`, an AND gate `a := ¬c ∧ b` reads both `c` and `b`,
and `c` is a C-element of `a` and `b`.  It is speed independent, but only because the AND
gate sees `c` and `¬c` change at the same time. -/

def forkCircuit : Circuit where
  signals := 3
  gates := [
    { name := "c", out := 0, fn := celem 1 2 0 },
    { name := "a", out := 1, fn := and (not (var 0)) (var 2) },
    { name := "b", out := 2, fn := inv 0 }]
  init := [false, false, false]

theorem forkCircuit_si : forkCircuit.Correct ∧ forkCircuit.SpeedIndependent :=
  ⟨by async_decide, by async_decide⟩

/-- With wire delays it glitches (the trace comes from `async_decide`'s error message)… -/
theorem forkCircuit_not_qdi : ¬ forkCircuit.QDI :=
  Circuit.not_speedIndependent_of_refute (gs := [2, 4, 6, 1, 3, 0, 7, 2, 4, 6, 1, 3])
    (g := ⟨5, by decide⟩) (g' := ⟨0, by decide⟩) (by decide +kernel)

/-- …unless the forks of `c` (signal 0) and `b` (signal 2) are isochronic. -/
theorem forkCircuit_qdi_iso : forkCircuit.QDI [0, 2] := by async_decide

/-- Finer: only the fork from `c` to gates `a` (1) and `b` (2), and the fork from `b` to gates
`c` (0) and `a` (1), are isochronic; each shares one wire whose delay is still arbitrary. -/
theorem forkCircuit_qdi_groups :
    forkCircuit.QDI { groups := [[(1, 0), (2, 0)], [(0, 2), (1, 2)]] } := by
  async_decide

/-! ## 6. Fairness

`Live` says every action *can* always happen again.  Under a strongly fair scheduler it
*will* happen infinitely often (`LTS.Run.infOften_label_of_live`), provided the reachable
state space is finite — which boundedness gives. -/

theorem handshake_fair (r : handshake.toNet.lts.Run handshake.M₀) (hfair : r.StronglyFair)
    (t : Fin handshake.trans.length) : LTS.InfOften (fun n => r.lab n = t) :=
  r.infOften_label_of_live (PNet.reachable_finite_of_bounded handshake_safe) hfair
    (handshake_correct.2.2 t)

/-! ## 7. Unbounded nets and concurrent firing

A net whose places can grow without bound has infinitely many reachable markings.
`async_decide` then checks its *counter abstraction*, which tracks each place exactly up to
a cap and as "cap or more" above it; the result transfers to the net (`PNet.of_checkAbs`). -/

/-- A requester that may run ahead of its server: the request queue (place 1) is unbounded. -/
def queue : PNet where
  places := 4
  trans := [
    { name := "req", pre := [0], post := [0, 1] },
    { name := "start", pre := [1, 2], post := [3] },
    { name := "finish", pre := [3], post := [2], internal := true }]
  init := [1, 0, 1, 0]

theorem queue_correct : queue.Correct := by async_decide

/-! At the cap, an internal transition that removes tokens may leave the abstract marking
unchanged, so no rank on abstract markings can show livelock freedom.  *Weights on the places*
see what the cap hides: if an internal transition decreases the weighted token count, it
cannot fire forever, whatever the abstraction says.  `async_decide` combines such linear
potentials with the abstract ranks and must-distances lexicographically
(`PNet.of_checkAbsP`). -/

/-- A buffer (place 1), filled by a producer and drained by an internal transition. -/
def drained : PNet where
  places := 2
  trans := [
    { name := "produce", pre := [0], post := [0, 1] },
    { name := "drain", pre := [1], post := [], internal := true }]
  init := [1, 0]

theorem drained_correct : drained.Correct := by async_decide

/-- The results hold when gates switch simultaneously, too: for a speed-independent circuit,
the step semantics reaches exactly the same states (`Circuit.correct_iff_stepCorrect`). -/
theorem forkCircuit_stepCorrect : forkCircuit.StepCorrect :=
  (Circuit.correct_iff_stepCorrect forkCircuit_si.2).1 forkCircuit_si.1

/-! ## 8. Large state spaces

For deadlock freedom, `async_decide` does not explore every interleaving: at each marking it
fires only the enabled transitions of a *stubborn set*, and the kernel checks that the sets
are stubborn.  Every reachable deadlock stays reachable (`Net.reachable_red_of_dead`), so a
reduced state space without deadlocks proves the whole net deadlock free.  For a pipeline,
whose stages move independently, one interleaving per state is enough. -/

/-- A 30-stage FIFO (`Examples.fifo`) has `2^30` reachable markings; the reduced state
space has a few hundred. -/
theorem fifo30_deadlockFree :
    (Examples.fifo 30 "in" "out").toNet.lts.DeadlockFree (Examples.fifo 30 "in" "out").M₀ := by
  async_decide

/-! `async_structural` proves the same kind of result with no exploration at all: every
reachable marking solves the state equation `M = M₀ + C · x`, and a Farkas certificate shows
that no solution is dead (`Net.deadlockFree_of_stateEq`). -/

/-- Twelve philosophers sharing forks, with resource ordering: deadlock free, by the state
equation. -/
theorem twelvePhilosophers_deadlockFree :
    (Examples.philosophers 12 true).toNet.lts.DeadlockFree (Examples.philosophers 12 true).M₀ := by
  async_structural

/-! The same reduction works for livelock freedom and liveness once the stubborn sets also
satisfy the *cycle proviso* (no transition is ignored forever round a cycle of the reduced
state space) and, for livelocks, *visibility* conditions on the external transitions
(`Net.live_of_stubborn`, `Net.livelockFree_of_stubborn`).  `async_decide` checks them
marking by marking, so whole `Correct` goals scale too. -/

/-- The 30-stage FIFO is deadlock free, livelock free and live. -/
theorem fifo30_correct : (Examples.fifo 30 "in" "out").Correct := by
  async_decide

/-! For safe nets there is also a *symbolic* route: `async_bdd` describes the reachable
markings by a decision diagram, an inductive invariant that the kernel checks transition by
transition without enumerating a single marking (`PNet.of_checkBDD`).  It proves safety and
deadlock freedom from a second diagram of witness transitions, and liveness and livelock
freedom from weights on the places that the witnesses and the internal transitions decrease,
completed where needed by diagrams of distances and ranks that count only the steps keeping
the weights unchanged. -/

/-- Ten philosophers never put two tokens on a place, from a symbolic invariant. -/
theorem tenPhilosophers_safe : (Examples.philosophers 10 true).Safe := by
  async_bdd

/-- Seven philosophers are deadlock free, live and safe, symbolically. -/
theorem sevenPhilosophers_correct : (Examples.philosophers 7 true).Correct := by
  async_bdd

/-! Some designs defeat both: every component synchronises with its neighbours, or internal
transitions sit next to external ones, so stubborn sets stay large, yet the reachable
markings are many.  When they are *dense* once packed, `async_bitmap` checks them in bulk.  A
*layout* packs a marking into a number, a component of places (exactly one of them marked)
taking the bits of its marked place's index; the markings that agree on their high bits form
one bitmap, a number with a bit per marking; and the kernel fires a transition on a whole
bitmap with one shift (`PNet.of_checkBitmap`).  Ranks and distances are computed by the
kernel in rounds, shortened by linear potentials.  `async_decide` uses bitmaps when it
estimates them cheaper than a reduced state space. -/

/-- Six independent four-phase handshakes, each acknowledged by an internal transition:
`4^6 = 4 096` markings in one bitmap. -/
theorem sixHandshakes_correct : (Examples.handshakes 6).Correct := by
  async_bitmap

/-! ## 9. Networks with dynamic routing

An interconnection network (a network on chip, a router mesh) is a `Network C P`: channels
`C` with one-packet buffers (a virtual channel is a channel of its own) and packet headers `P`.
`route c p` lists the hops a packet with header `p` in channel `c` may take; with *adaptive*
routing there are several, and which one is taken is decided at run time by a *selection
function*, typically the least congested free channel.  `N.Correct` says: for **every**
work-conserving selection function, the network is deadlock free (whenever it holds a packet,
some packet can move) and livelock free (no packet keeps moving forever without arriving).

No configuration of the network is explored: `async_decide` checks the routing function
locally — an acyclic channel dependency graph (Dally and Seitz) or acyclic *escape* channels
(Duato), and a ranking function that decreases on every hop.

A ring of four nodes, where channel `i` leads from node `i` to node `i + 1` and the header is
the destination, deadlocks: -/

def ring4 : Network ℕ ℕ where
  arrived c d := (c + 1) % 4 == d
  route c d := [((c + 1) % 4, d)]
  inject := [(0, 2), (1, 3), (2, 0), (3, 1)]

/--
info: "DEADLOCK: the channel dependency cycle 0 → 1 → 2 → 3 → 0 can be filled with blocked packets by the run [.inject 1 3, .inject 2 0, .inject 3 1, .inject 0 2].\nProve it with: Network.not_deadlockFree_of_refuteB (as := [.inject 1 3, .inject 2 0, .inject 3 1, .inject 0 2]) (by decide +kernel)"
-/
#guard_msgs in
#eval ring4.explain

theorem ring4_deadlocks : ¬ ring4.DeadlockFree :=
  Network.not_deadlockFree_of_refuteB (as := [.inject 1 3, .inject 2 0, .inject 3 1, .inject 0 2])
    (by decide +kernel)

/-- A second virtual channel per link (channels `4 + i`), used after crossing the dateline
from node 3 to node 0, breaks the cycle. -/
def datelineRing4 : Network ℕ ℕ where
  arrived c d := (c % 4 + 1) % 4 == d
  route c d := let i := (c % 4 + 1) % 4; [(if i = 0 then 4 else i + 4 * (c / 4), d)]
  inject := [(0, 2), (1, 3), (2, 0), (3, 1)]

theorem datelineRing4_correct : datelineRing4.Correct := by async_decide

/-- Whatever the selection function, every reachable configuration drains: once injection
stops, all packets are delivered. -/
example {sel : Network.Selection ℕ ℕ} (hsel : datelineRing4.ValidSel sel) {f}
    (hf : (datelineRing4.ltsWith sel).Reachable Network.empty f) :
    Relation.ReflTransGen ((datelineRing4.ltsWith sel).IStep Network.Act.IsMove) f
      Network.empty :=
  datelineRing4_correct.drain hsel hf

/-- Under a strongly fair scheduler no packet starves, even with injection going on forever. -/
theorem datelineRing4_starvationFree : datelineRing4.StarvationFree := by async_decide

/-- Under wormhole switching packets span several channels; the dateline ring stays correct for
packets of every length. -/
theorem datelineRing4_wormhole : datelineRing4.WormholeCorrect := by async_decide

/-! Adaptive meshes with Duato's escape channels (also under wormhole switching), bounded
misrouting (livelock freedom from a misrouting budget), deflection routing (a livelock) and
proofs for dateline rings of every size are in `Examples/Routing.lean`.

In hardware the routing decision is made by the router's routing logic.
`comb_from_verilog` imports it as a combinational netlist (`Comb`), and an `RtlRouter` says
which input bits it reads for a packet and how its output bits name the next hop.  The kernel
evaluates the netlist on every packet it handles and compares with `route`
(`Network.implementedBy`); the theorems about the network then hold for the network routed
by the netlist (`Network.correct_of_rtl`), and `Comb.unique` makes its outputs independent of
gate delays.  `Examples/RTL.lean` does this for the XY routing logic of a 4×4 mesh.

## Where next

* `Examples/Compositional.lean`: `async_minimize` replaces components by minimal quotients so
  that compositions far too large to explore can be checked.
* `Examples/Imported.lean`: designs read from `.g`, PNML and Verilog files.
* `Examples/MullerRing.lean`: a proof for Muller rings of *every* size, using the theory
  directly.
* `Examples/Routing.lean`: dynamically routed meshes and rings.
* `Examples/Bitmap.lean`: dense and tightly coupled designs, and an unbounded log, by
  bit-parallel certificates.
* `Examples/RTL.lean`: a mesh routed by its Verilog routing logic.
-/

#assert_standard_axioms handshake_correct handshake_safe sharedServer_deadlocks choiceNet_live
  spec_ok impl_ok forkCircuit_si forkCircuit_not_qdi forkCircuit_qdi_iso
  forkCircuit_qdi_groups handshake_fair queue_correct forkCircuit_stepCorrect
  fifo30_deadlockFree twelvePhilosophers_deadlockFree fifo30_correct tenPhilosophers_safe
  sevenPhilosophers_correct sixHandshakes_correct ring4_deadlocks datelineRing4_correct datelineRing4_starvationFree
  datelineRing4_wormhole

end AsyncLean.Tutorial
