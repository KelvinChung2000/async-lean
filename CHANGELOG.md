# Changelog

## 0.2.0

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
