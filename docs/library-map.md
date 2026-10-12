# Library map

[← back to the README](../README.md) · [all guides](README.md)

Every file under `AsyncLean/` (paths below are relative to it), grouped by topic. Folders such as `Flow/Backpressure/` and
`Routing/Throughput/` are split into parts; the module of the same name imports them all.

## Transition systems

| File | Contents |
|---|---|
| `Tutorial.lean` | a checked walkthrough of the library |
| `LTS/Basic.lean` | transition systems, reachability, traces |
| `LTS/Properties.lean` | deadlock, livelock, liveness, persistence; proof and refutation rules; progress theorem; transfer along bisimulations |
| `LTS/Compose.lean` | parallel composition, hiding, divergence-preserving weak bisimulation |
| `LTS/Fairness.lean` | infinite runs, strong fairness, "will happen" theorems |

## Petri nets, STGs and circuits

| File | Contents |
|---|---|
| `Petri/Basic.lean`, `Invariant.lean`, `SiphonTrap.lean` | Petri nets, P-invariants, bounds, ranking functions, siphons and traps |
| `Petri/FreeChoice.lean`, `FreeChoiceNecessity.lean` | free-choice nets, Commoner's theorem (both directions) |
| `Petri/SiphonCheck.lean` | kernel-checked branching certificates for the siphon–trap property |
| `Petri/Step.lean`, `Circuit/Step.lean` | step semantics (concurrent firing and switching) and their agreement with interleaving |
| `Petri/Stubborn.lean`, `Petri/StubbornLive.lean` | stubborn sets: deadlocks preserved; cycle proviso and visibility for liveness and livelock freedom |
| `Petri/StateEquation.lean` | the state equation and Farkas certificates for deadlock freedom |
| `MarkedGraph/Basic.lean` | Commoner's theorem for marked graphs, circuit tokens, safeness, rank certificates |
| `Stg/Basic.lean` | STGs: state graph, consistency, CSC, output persistence, implementation by gates, CSC ⇔ implementable |
| `Stg/Concrete.lean` | concrete STGs `Stg`, checkers and refutations for all STG properties |
| `Circuit/Basic.lean` | gate netlists (`BExpr`, C-elements), Muller semantics, speed independence |
| `Circuit/Wires.lean`, `Circuit/QDI.lean` | wire delays, isochronic forks, QDI, proof that QDI implies speed independence |
| `Circuit/Packed.lean` | bit-packed circuit states for fast checking |
| `Circuit/Comb.lean` | combinational netlists as functions: evaluation, well-formedness, uniqueness of settled states |

## Networks with dynamic routing

| File | Contents |
|---|---|
| `Routing/Basic.lean` | networks with dynamic routing, selection functions, Duato's theorem (sufficient and necessary), Dally–Seitz, livelock by ranking, drain theorem, refutations |
| `Routing/Fairness.lean` | starvation freedom: every packet is delivered along every strongly fair run |
| `Routing/Wormhole.lean` | wormhole switching, Duato's extended dependency graph, livelock, drain, refutations |
| `Routing/WormholeFairness.lean`, `WormholeHold.lean` | starvation freedom under wormhole switching; blocking sets, a deadlock condition beyond Duato's |
| `Routing/RTL.lean` | routing functions implemented by netlists: `RtlRouter`, `implementedBy`, `coveredBy`, transfer of correctness |
| `Routing/Check.lean`, `Routing/WormholeCheck.lean` | trusted routing checkers, untrusted certificate search and diagnosis |
| `Routing/Optimal.lean` | comparing routing functions by adaptivity, maximally adaptive routing, refutations for intervals of routing functions |
| `Routing/Embed.lean` | carrying a deadlock of a small network into every network that contains a copy of it |
| `Routing/Source.lean` | Duato's theorem and starvation freedom for selections that throttle the sources; tiered selections |
| `Routing/Reduce.lean` | reducing one routing function to another: acyclic channel dependencies transfer along a map of channels |
| `Routing/Graph.lean` | safe adaptive routing on every finite connected graph: minimal adaptive routing with a spanning-tree escape |
| `Routing/GraphBudget.lean` | routing on every graph with bounded returns from the escape layer: a packet may leave the escape layer `B` times |
| `Routing/GraphDetour.lean` | source-chosen intermediate nodes (Valiant, long way round) on top of bounded returns: safe on every graph |
| `Routing/Saturation.lean` | delivery under sustained load: channel fairness, Duato's theorem for liveness with injections never stopping |

## The fluid model: throughput bounds

| File | Contents |
|---|---|
| `Flow/Fluid.lean`, `Flow/MeshWire.lean` | fluid throughput bounds: weak duality, the wire and cut bounds; the mesh's optimum and the wire ceiling on the k × k grid |
| `Flow/MeshOdd.lean`, `Flow/MeshWorst.lean` | the mesh's uniform optimum for odd k; minimality of XY; admissible traffic, O1TURN and XY flows for any demand, the worst-case optimum 4/k and the bit-complement optimum |
| `Flow/Certificate.lean`, `Flow/MeshPatterns.lean` | kernel-checked LP certificates (primal flow, dual lengths) for the k × k mesh; exact optima of transpose, shuffle, bit reversal and hotspot on the 8 × 8 mesh |
| `Flow/Topologies.lean`, `Flow/Tree.lean`, `Flow/Symmetric.lean`, `Flow/Valiant.lean` | the torus and the hypercube; minimal routing optimal for every traffic iff tree; uniform traffic on arc-transitive networks; Valiant's half-capacity bound and the worst cases of mesh, torus and hypercube |
| `Flow/GraphCert.lean`, `Flow/GraphPatterns.lean` | graph-generic kernel-checked LP certificates; exact minimal and any-routing optima on the 8 × 8 torus and the 6-cube |

## Scaling with the connections ([guide](scaling.md))

| File | Contents |
|---|---|
| `Flow/Scaling.lean` | throughput scales exactly linearly with the connections: flows scale and add, the layered scheme, exact optima with `m` connections per link on the mesh, torus and hypercube |
| `Routing/Lanes.lean` | the lane network: `m` copies of a network side by side; safety certificates and their transfer to every number of lanes; lanes run in parallel and deliver the sum of their packets |
| `Routing/SharedLanes.lean`, `Routing/Widen.lean` | sharing the connections: escapes per lane with adaptive hops on every lane; widening any network to any number of copies of every channel, every copy usable, with every guarantee kept |
| `Flow/Backpressure/` | backpressure (max-weight) scheduling in a queueing model of the fluid network, in seven parts: `Model` (runs, the scheduler, stability), `Stability` (drift, throughput optimality), `Buffers` (finite buffers suffice), `Bursty` (leaky-bucket arrivals), `Ceiling` (no scheduler beats the fluid model), `Scheduler` (the greedy scheduler, whole packets), `Instances` (mesh, torus, hypercube with `m` connections) |
| `Routing/Throughput/` | packet networks in time, in four parts: `Timed` (placements, timed runs, the fluid ceiling for every selection, delivery), `Lanes` (lanes add their throughput), `Select` (score-based selections are safe), `Graph` (the graph networks placed on their graph) |
| `Flow/Necessity.lean` | what is necessary: shortest-path-only scheduling loses (tornado on the torus); restricted backpressure; backpressure never deadlocks and fits in finite buffers; a single FIFO per node does not scale |
| `Flow/Stochastic.lean` | backpressure under random arrivals (Poisson, for instance): strong stability for every expectation operator |

## Checkers and tactics

| File | Contents |
|---|---|
| `Checker/Explicit.lean` | the **trusted checker** and its soundness proofs; certificates; counterexample traces |
| `Checker/BTree.lean`, `Invariant.lean`, `Packed.lean`, `Quotient.lean` | search trees, invariant certificates, bit-packed safe nets, quotient certificates |
| `Checker/Petri.lean` | concrete nets `PNet`, executable semantics, bisimilarity with the abstract net |
| `Checker/Abstract.lean` | checking through finite over-approximations; the counter abstraction of unbounded nets |
| `Checker/Diagnose.lean`, `Minimize.lean` | untrusted counterexample search, certificate and quotient computation |
| `Checker/Affine.lean`, `AffineK.lean` | layouts: markings packed by components and counters, a linear encoding (`PNet.encodesL`), kernel-friendly structural checks |
| `Checker/Bitmap.lean`, `BitmapPetri.lean`, `BitmapGen.lean` | bit-parallel certificates: the trusted checker and its soundness, its instance for nets with linear potentials, the untrusted generator |
| `Checker/AbstractPot.lean` | counter abstractions with linear potentials (lexicographic ranks and must-distances) |
| `Checker/Fast.lean`, `FastPetri.lean` | the fast kernel checker on numeric states, and its instance for nets packed into bit fields |
| `Checker/FastPOR.lean`, `FastPORLive.lean` | kernel checks of reduced state spaces |
| `Checker/BDD.lean`, `BDDGen.lean` | symbolic certificates: decision diagrams checked by joint walks; their untrusted computation |
| `Checker/Tactic.lean` | the `async_decide`, `async_bitmap`, `async_bdd`, `async_routing` and `async_minimize` tactics |
| `Auto/Simplex.lean`, `Auto/Structural.lean`, `Auto/StateEq.lean` | exact rational simplex (untrusted), `async_structural`, state-equation certificates and packed place-invariant bounds |

## Importers, audit and examples

| File | Contents |
|---|---|
| `Import/G.lean`, `Pnml.lean`, `Verilog.lean` | importers: `stg_from_g`, `pnet_from_pnml`, `gates_from_verilog`, `circuit_from_verilog`, `comb_from_verilog`; `#export_pnml` writes a net for other model checkers |
| `AxiomAudit.lean`, `Audit.lean` | `#assert_standard_axioms` and the library-wide audit |
| `Examples/` | Muller rings, arbiter, dining philosophers, counterexamples, circuits, STG implementation, composition, imported designs, structural proofs, fairness, free choice, QDI, concurrent firing, unbounded nets, scale, symbolic certificates, routing, maximally adaptive routing (on every mesh size), optimal routing per cost, a tiered source-throttled selection, safe routing on the torus and the Petersen graph, the torus with `m` lanes and its packet throughput (`Examples/Lanes.lean`, `Examples/Throughput.lean`), bitmaps, routing logic from RTL |
