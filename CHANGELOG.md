# Changelog

## Unreleased

* **Bit-parallel certificates** (`Checker/Bitmap.lean`, `Checker/BitmapPetri.lean`). Sets of
  packed markings are bitmaps — one number with a bit per marking — grouped into chunks by
  their high bits, and the kernel fires a transition on a whole chunk with one shift, after
  checking with two more shifts that no marking borrows from or carries into the high bits
  (`Bitmap.fire_chunk`). Closure, deadlock freedom, and rounds of ranks (livelock freedom)
  and of distances to hubs (liveness) are computed by the kernel, lexicographically with
  linear potentials found by linear programming (`Bitmap.of_check`, `PNet.of_checkBitmap`,
  `PNet.bounded_of_checkBitmap`). New tactic `async_bitmap`; `async_decide` uses it when it
  estimates it cheaper than a reduced state space. On tightly coupled designs whose reduced
  state space stays large it is an order of magnitude faster: ten four-phase handshakes
  (`4^10` markings) are `Correct` in 12 s instead of 127 s end to end (24 s with
  `async_decide`), and twelve (`4^12`), out of reach before, in about two minutes.
  `async_decide` tries bitmaps only beyond 2000 reduced markings, on dense nets, and within
  4 GB of estimated kernel memory, and is no slower than before on the other benchmarks.
* **Bitmaps for gate-level circuits** (`Checker/BitmapCircuit.lean`). A circuit state is a bit
  vector; the rise and the fall of every gate are transitions whose guard is a Boolean
  expression, evaluated on a whole chunk by bitwise operations (`Bitmap.bmaskE`), and
  `Circuit.of_checkBitmap` transfers the result from rises and falls to gates. `async_bitmap`
  proves `Correct`, deadlock freedom, livelock freedom and liveness of circuits;
  `async_decide` tries it for circuits of 14 signals or more.
* **Layouts** (`Checker/Affine.lean`, `Checker/AffineK.lean`). A marking is packed by fields:
  a component of places of which exactly one is marked takes the bits of its marked place's
  index, a counter place its count, and a place that no transition consumes from no bits at
  all. The packing is linear in the marking, so firing adds and subtracts constants, and
  enabledness is a conjunction of tests on fields (`PNet.encodesL`). The structural check
  (`PNet.layoutOkK`) and the transition table (`PNet.katable`) are written with recursors, for
  the kernel, and proved equal to their list-library definitions.
* **Linear potentials for unbounded nets** (`Checker/AbstractPot.lean`). The counter
  abstraction combines weights on the places with its ranks and must-distances
  lexicographically (`PNet.of_checkAbsP`), so an internal transition that drains a buffer at
  the cap no longer defeats livelock freedom; `async_decide` tries it when the plain
  abstraction fails.
* **Routing logic from RTL.** `comb_from_verilog` imports a combinational netlist (`Comb`,
  `Circuit/Comb.lean`), now with buses and bit selects; `Comb.unique` shows that every settled
  state of the gates agrees with its evaluation. `Routing/RTL.lean` connects a router's
  routing logic to a network: `Network.implementedBy` (checked by evaluating the netlist on
  every handled packet) gives `N.withRtl r = N`, so every theorem about `N` holds for the
  network routed by the netlist (`Network.correct_of_rtl`); `Network.coveredBy` shows that the
  netlist handles every packet the network can carry. Example: the XY routing logic of a 4×4
  mesh (`Examples/RTL.lean`).
* `#export_pnml N "file.pnml"` writes a net as PNML, to compare with other model checkers;
  `bench/` has the scripts behind the timings of the README.
* Examples (`Examples/Bitmap.lean`): handshakes, a barrier, an unbounded log, a ring of
  C-elements; tutorial
  paragraphs on potentials, bitmaps and routing logic.

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

* **Partial-order reduction.** Stubborn sets preserve deadlocks (`Net.reachable_red_of_dead`);
  `async_decide` checks deadlock freedom on a reduced state space whose stubborn sets the
  kernel verifies marking by marking (`PNet.deadlockFree_of_checkPOR`).
* **Partial-order reduction for liveness and livelock freedom.** The cycle proviso makes a
  reduced state space decide liveness (`Net.catchUp`, `Net.live_of_stubborn`); visibility
  and a rank on internal steps decide livelock freedom (`Net.livelockFree_of_stubborn`).
  `async_decide` proves `Correct`, livelock freedom and liveness this way
  (`PNet.correct_of_checkPORc`): a 40-stage FIFO is `Correct` in 4.4 s, a 12-stage one in
  0.25 s instead of 13 s.
* **Symbolic certificates.** Decision diagrams of an inductive invariant, of witnesses, and of
  distances and ranks, checked by the kernel through joint walks before and after each
  transition without enumerating any marking (`PNet.of_checkBDD`); computed by a small
  untrusted decision-diagram package (`PNet.BDDGen.mkBDDCert`). New tactic `async_bdd`;
  `async_decide` falls back on it for large safe nets.
* **Linear potentials in symbolic certificates.** Liveness from weights on the places that
  every witness decreases, down to hubs, and livelock freedom from weights that every
  internal transition decreases (`PNet.phiL_lt`); both are found by linear programming and
  replace the diagrams of distances and ranks when they exist. Witnesses are chosen over the
  whole space, which makes their diagram up to 15× smaller.
* **Shorter joint walks.** Each level of the diagrams reads one place (`PNet.vars_inj`), so a
  walk on the invariant starts at the cut of the first level a transition touches
  (`PNet.cut_reach`, checked once for all transitions), stops below the last one
  (`PNet.Reach.congr`), and a coverage walk stops at the first data leaf. Together with
  hub traces from shared forward layers, seven philosophers are proved `Correct`
  symbolically in 1.4 s instead of 47 s; a 20-stage FIFO and twelve philosophers, out of
  reach before, in 1.9 s and 3.8 s.
* **Saturation.** The untrusted search computes reachable markings by saturation, and
  backward closures by saturation constrained by them; traces from hubs come from chained
  rounds of images. The search for a 40-stage FIFO takes 1.2 s instead of 21 s, and an
  80-stage FIFO and forty philosophers are proved `Correct` symbolically in 11 and 13 s.
* **Cheaper symbolic checks.** Diagram nodes are packed into one number per field, so the
  kernel reads a node with a few shifts instead of a search (`PNet.nget`); the decrease of
  the potential is checked once per witness transition instead of once per leaf; the search
  finds the rank and the potential with one linear program when it can, and walks traces
  back by galloping search. Symbolic proofs are 5–25% faster.
* **Lexicographic measures.** When no linear potential decreases every witness (or every
  internal transition), each may decrease it or keep it while decreasing a distance (or rank)
  diagram (`PNet.phiL_le`). The diagrams then count only the steps keeping the potential, and
  livelock freedom is decided completely: a cycle of internal steps keeps every potential.
* **Faster kernel lookups.** `Fast.kfind` compares with `Nat.ble` instead of `Nat.blt`,
  which halves the cost of a lookup in the kernel and speeds up every fast checker.
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
