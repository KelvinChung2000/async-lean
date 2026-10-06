# Changelog

## Unreleased

* **Interconnection networks with dynamic routing** (`Routing/Basic.lean`). `Network` models
  packet-switched networks with one-packet channel buffers, adaptive routing functions and
  run-time selection functions. `Network.Correct` is routing deadlock freedom and routing
  livelock freedom under *every* work-conserving selection function. The new results:
  * Duato's theorem (`Network.deadlockFree_of_escape`) and Dally and Seitz's theorem
    (`Network.deadlockFree_of_cdg`);
  * livelock freedom from a ranking function, for minimal or bounded non-minimal routing
    (`Network.livelockFree_of_ranking`), with per-packet hop bounds
    (`Network.packet_hops_le`);
  * the drain theorem (`Network.Correct.drain`);
  * the reduction of every selection policy to fully adaptive routing;
  * refutations from counterexample runs.
* `async_decide` proves `Network.Correct` by kernel-checked local certificates
  (`Network.checkCert`), with no exploration of network configurations. On failure it reports
  a deadlock or livelock counterexample and the theorem that proves it. `async_routing
  (escape := R₁)` names the escape channels. `#eval N.explain` prints the same report.
* **Duato's condition is necessary** (`Network.staticDeadlockFree_iff_exists_escape`,
  `Network.deadlockFree_iff_exists_escape`): an equivalence when finitely many channels carry
  legal packets.
* **Starvation freedom** (`Routing/Fairness.lean`): `Network.StarvationFree`, every packet is
  delivered along every strongly fair run (`Network.delivered_of_ranking`,
  `Network.starvationFree_of_escape_ranking`); `async_decide` proves it.
* **Wormhole switching** (`Routing/Wormhole.lean`, `Routing/WormholeCheck.lean`): packets
  spanning several channels, Duato's theorem with the extended dependency graph
  (`Network.wormholeDeadlockFree_of_escape`), Dally and Seitz's theorem, livelock freedom by
  ranking and the drain theorem, for packets of every length. Kernel-checked certificates
  through `async_decide` and `async_routing (escape := E)`, refutations and diagnosis
  (`#eval N.explainWormhole`).
* `LTS.LivelockFree.mono`, `LTS.LivelockFree.of_sub`, `LTS.Path.iStep_rtc`,
  `LTS.Path.iStep_transGen`.
* Examples (`Examples/Routing.lean`): rings with and without a dateline, with proofs for
  dateline rings of every size (correct, starvation free, wormhole correct); XY, fully
  adaptive, Duato, bounded-misrouting and deflection meshes, under store-and-forward and
  wormhole switching. A tutorial section on routing.

## 0.2.0

Latest additions:

* **Partial-order reduction.** Stubborn sets preserve deadlocks (`Net.reachable_red_of_dead`);
  `async_decide` checks deadlock freedom on a reduced state space whose stubborn sets the
  kernel verifies marking by marking (`PNet.deadlockFree_of_checkPOR`).
* **The state equation.** Deadlock freedom from a Farkas certificate refuting every dead
  solution of `M = M₀ + C · x` (`Net.deadlockFree_of_stateEq`), found by linear programming,
  with no exploration; used by `async_structural`, and by `async_decide` when the reduced
  state space is too large.
* **Fast kernel checking.** A checker on natural-number states with recursor-based inner
  loops (`Fast.of_check`), and its instance for nets packed into bit fields
  (`PNet.checkFast`): about 7× faster than before. Bounds from place invariants are checked
  all at once, packed into one number per place (`PNet.bounded_of_checkPInv`).
* **Concurrent firing.** Step semantics for Petri nets (any multiset of enabled transitions
  fires at once) and circuits (any set of excited gates switches at once), with proofs that
  they agree with the interleaving semantics: always for nets, and for speed-independent
  circuits (`Circuit.correct_iff_stepCorrect`).
* **Unbounded nets.** Checking through finite over-approximations (`ExplicitLTS.Abstracts`,
  with must-distances for liveness) and the counter abstraction of Petri nets
  (`PNet.of_checkAbs`); `async_decide` uses it when the state space does not close, and
  `async_decide (cap := k)` refines it.
* **No dead end on hard siphon–trap instances.** The certificate search has a size budget;
  beyond it `async_structural` falls back on model checking.
* Faster untrusted search: AVL trees for explored states (sorted insertions no longer
  degrade), and counterexample search in linear space.
* **Commoner's theorem for free-choice nets, both directions** (`Net.live_iff_siphonTrap`);
  the necessity direction refutes liveness.
* **Siphon–trap certificates.** The siphon–trap property is checked from a kernel-verified
  branching certificate on bit masks instead of enumerating sets of places;
  `async_structural` also proves deadlock freedom of ordinary nets this way.
* **Isochronic forks per branch.** `Forks` declares isochronic signals or groups of branches
  sharing one wire.
* **Faster circuit checking.** Bit-packed circuit states, recursor-based gate evaluation,
  circuits evaluated to literals once, and labelled-successor certificates for persistence
  (about 3× faster on wired circuits).
* **Design files tracked by Lake** through an `input_dir` target.

New models and theory:

* **STGs.** Signal transition graphs (`StgModel`, `Stg`) with consistency, complete state
  coding and output persistence. Conformance of a gate-level implementation implies the
  correctness of the closed loop (`Stg.implementation_correct`) and its hazard freedom.
  Complete state coding is exactly implementability (`StgModel.csc_iff_exists_conformant`).
* **Composition.** Parallel composition, hiding and divergence-preserving weak bisimulation,
  which is a congruence preserving deadlock and livelock freedom (`LTS/Compose.lean`).
* **Fairness.** Infinite runs and strong fairness: live actions happen infinitely often, and
  fair runs make progress (`LTS/Fairness.lean`).
* **Free-choice nets.** Commoner's liveness theorem (`Net.live_of_siphonTrap`).
* **Wire delays.** `Circuit.withWires`, `Circuit.QDI`, and the proof that QDI implies speed
  independence (`Circuit.speedIndependent_of_qdi`, `Circuit.correct_of_qdi`).

Tools:

* `async_decide` handles STG goals (specification, consistency, CSC, output persistence,
  conformance, closed-loop properties), QDI goals, boundedness and safeness, and generic
  explicit transition systems.
* `async_minimize` replaces a component of a parallel composition by a certified minimal
  quotient.
* `async_structural` proves safeness, boundedness, livelock freedom for every initial
  marking, and liveness of marked graphs and free-choice nets, from certificates found by
  linear programming and graph search.
* Importers: `stg_from_g` (Petrify / Workcraft `.g`), `pnet_from_pnml` (PNML),
  `gates_from_verilog` and `circuit_from_verilog` (structural Verilog).
* Faster kernel checking: literal successor lists, home-state certificates, and bit-packed
  markings for safe nets, about 6× faster on the dining philosophers.

Documentation: a checked tutorial (`AsyncLean/Tutorial.lean`) and a doc-gen4 setup
(`docbuild/`, `.github/workflows/docs.yml`).

## 0.1.0

* Labelled transition systems and the properties deadlock freedom, livelock freedom,
  liveness and persistence, with proof and refutation rules and the progress theorem.
* Petri nets, P-invariants, siphons and traps, linear ranking functions.
* Marked graphs: Commoner's theorem, token conservation, safeness; parametric Muller rings.
* Gate-level circuits with Muller semantics and speed independence.
* A verified certificate checker and the `async_decide` tactic, with counterexample
  diagnosis.
* Axiom audit (`#assert_standard_axioms`).
