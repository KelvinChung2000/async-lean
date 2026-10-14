# Glossary: the library's names and the literature

[← back to the README](../README.md) · [all guides](README.md)

The library uses the standard name of a concept wherever one exists. This page maps its names
to the terms and references of each field, and lists the few names that are the library's own.

## Transition systems (`LTS/`)

| Here | In the literature |
|---|---|
| `LTS`, `Step`, `Reachable` | labelled transition system, reachability (Keller, 1976) |
| `DeadlockFree`, `IsDeadlock` | deadlock freedom: every reachable state has a successor |
| `Diverges`, `LivelockFree` | divergence (an infinite run of internal steps, as in CSP and CCS), and its absence |
| `LiveLabel`, `Live` | liveness of a transition: from every reachable state it can still occur (L4-liveness, Murata, 1989) |
| `Persistent` | persistence: an enabled action stays enabled until it occurs (Landweber and Robertson, 1978) |
| `StronglyFair` | strong fairness (compassion): an action enabled infinitely often occurs infinitely often (Francez, 1986) |
| `par`, `DivBisim` | parallel composition with synchronisation; divergence-preserving weak bisimulation (Milner, 1989) |
| `FunBisim` | functional bisimulation: a bisimulation that is the graph of a function |
| `InevitablyExternal` | progress: every run eventually performs an external action |

## Petri nets and marked graphs (`Petri/`, `MarkedGraph/`)

| Here | In the literature |
|---|---|
| `Marking`, `Enabled`, `fire`, `IsPInvariant`, `effect` | markings, the firing rule, P-invariants and the state equation (Murata, *Petri nets: properties, analysis and applications*, 1989) |
| `IsSiphon`, `IsTrap`, `SiphonTrapProperty` | siphons, traps and Commoner's siphon–trap property |
| `FreeChoice`, `live_iff_siphonTrap` | free-choice nets and Commoner's theorem (Hack, 1972; Desel and Esparza, *Free Choice Petri Nets*, 1995) |
| `MarkedGraph`, `CircuitsMarked` | marked graphs: live iff every directed circuit carries a token (Commoner, Holt, Even and Pnueli, 1971) |
| `Stubborn`, `Proviso` | stubborn sets and the cycle (ignoring) proviso of partial-order reduction (Valmari, 1990) |
| `StepEnabled`, `fireStep` | step semantics: a set of concurrently enabled transitions fires at once |
| `HomeCert`, `checkCertHome` | home states (home markings): reachable from every reachable state |
| `Bounded`, `Safe` | `k`-boundedness and safeness (1-boundedness) |

## Signal transition graphs (`Stg/`)

| Here | In the literature |
|---|---|
| `StgModel`, `sg` | signal transition graphs and their state graphs (Rosenblum and Yakovlev, 1985; Chu, 1987) |
| `Consistent`, `CSC`, `OutputPersistent` | consistency, complete state coding and output persistency (Cortadella, Kishinevsky, Kondratyev, Lavagno and Yakovlev, *Logic Synthesis for Asynchronous Controllers and Interfaces*, 2002) |
| `Conformant` | conformance of an implementation to its specification (Dill, 1989) |

## Gate-level circuits (`Circuit/`)

| Here | In the literature |
|---|---|
| `celem`, `Excited`, `SpeedIndependent` | the Muller C-element, excited gates, speed independence (Muller and Bartky, 1959) |
| `QDI`, `Forks`, `withWires` | quasi-delay-insensitivity and isochronic forks (Martin, 1990): wires get delays, forks marked isochronic do not |

## Routing in interconnection networks (`Routing/`)

| Here | In the literature |
|---|---|
| `Network`, `route`, `Selection` | a routing function and a selection function (Duato, 1993); channels are physical or virtual alike |
| `Dep`, `deadlockFree_of_cdg` | the channel dependency graph and the Dally–Seitz condition (Dally and Seitz, 1987) |
| `EscapeSel`, the escape subnetwork, `ExtDep` | Duato's theorem: a connected routing subfunction (the escape channels) with an acyclic (extended) channel dependency graph (Duato, 1993, 1995) |
| `Worm`, `Wormhole*` | wormhole switching; the default model is virtual cut-through (Kermani and Kleinrock, 1979) |
| `StarvationFree`, `ChannelFair` | starvation freedom; fairness of channel arbitration |
| `MaximallyAdaptive`, `westFirst`, `northLast` | maximal adaptivity and the turn model (Glass and Ni, 1992) |
| `datelineRing`, `misrouteMesh`, `deflectionMesh` | datelines on rings and tori (Dally and Seitz, 1987); misrouting; deflection (hot-potato) routing |
| `SourceSel`, throttled sources | source throttling (injection limitation) |
| `prioritySel`, `priorityMesh` | a priority-based selection function: the free hops of the highest priority level that has one |
| `GraphData.net`: tree routing as escape | routing along a spanning tree, the tree-only case of up\*/down\* routing (Schroeder et al., Autonet, 1991) |
| two-phase routing, `twoPhaseNet`, `anyIntermediate` | routing through an intermediate node chosen at the source, minimally to it and then to the destination: Valiant's two-phase routing (Valiant and Brebner, 1981), or a deterministic choice such as the long way round a ring |
| non-minimal routing, `nonminimal_helps`, `*_nonminimal_gain` | routes that do not always bring a packet closer to its destination; misrouting (`misrouteMesh`) when hop by hop |
| planes, `Network.planes` | multiple physical networks (Yoon, Jiang, Becker and Dally, 2010), network planes. Not *lanes*: Dally (1992) uses *lane* for a virtual channel, as the guides here do |
| replication, `Network.replicate` | more channels per link, physical or virtual |

## Throughput: the fluid model (`Flow/`)

| Here | In the literature |
|---|---|
| fluid optimum, `Routable dem θ` | maximum concurrent multicommodity flow (Shahrokhi and Matula, 1990); the *ideal throughput* of Dally and Towles, *Principles and Practices of Interconnection Networks* (2004) |
| `potential_bound`, `cut_bound`, `hop_bound` | LP duality for multicommodity flow (dual edge lengths and node potentials); the cut (bisection) bound and the hop-count bound on channel load (Dally and Towles) |
| `IsHopPotential`, `UGraph.IsHopDist` | a potential that drops by at most one per link (a feasible LP dual for unit lengths), and the exact hop distance (the Bellman–Ford equations) |
| `Minimal`, `minimal_optimal_iff` | minimal routing: every packet takes a shortest path (optimal for every traffic iff the graph is a tree) |
| `Admissible` | admissible traffic: no node sends or receives more than its injection rate (Towles and Dally, 2002) |
| `uniform`, `transpose8`, `shuffle8`, `bitrev8`, `bitcomp`, `tornado8`, `neighbor8`, `hotspot8` | the standard synthetic traffic patterns (Dally and Towles) |
| `xyRouting`, `o1Routing`, `valiantRouting` | dimension-order (XY) routing; O1TURN (Seo et al., 2005); Valiant's two-phase routing |

## Scheduling: backpressure (`Flow/Backpressure/`, `Flow/Necessity.lean`, `Flow/Stochastic.lean`)

| Here | In the literature |
|---|---|
| backpressure, `Run.Backpressure`, `MaxWeight` | back-pressure / max-weight scheduling (Tassiulas and Ephremides, 1992) |
| `Run.backpressure_optimal`, `Run.potential_bound` | throughput optimality: stable inside the capacity region (achievability), and no policy stable outside it (the converse) |
| `lyapunov`, `Run.drift`, `Run.frame_drift` | the quadratic Lyapunov function `∑ Q²`, its one-slot drift and its `T`-slot (frame) drift (Neely, *Stochastic Network Optimization*, 2010) |
| leaky-bucket arrivals | `(σ, ρ)`-constrained arrivals (Cruz, 1991) |
| `backpressure_strongly_stable` | strong stability: bounded time-averaged expected backlog (Neely) |
| per-destination queues | the per-commodity queues of back-pressure routing |
| `SingleFifo`, `mesh_headOfLine` | head-of-line blocking of a single FIFO (Karol, Hluchyj and Morgan, 1987, the 58.6 % limit) |
| `scoreSel` | choosing by a congestion score: congestion-aware adaptive selection |

## The library's own names

These have no standard counterpart; each is defined where it is introduced.

| Name | Meaning |
|---|---|
| legal pairs (`Legal`) | the (channel, header) pairs a reachable configuration can hold, on which the routing function is required to behave |
| `SafeCert` | the safety recipe packaged once: closed legal pairs, a connected escape subnetwork with a well-founded dependency graph, a ranking |
| return budget (`Routing/GraphBudget.lean`) | at most `B` hops from the escape subnetwork back to the adaptive channels |
| `wire_bound`, `grid_wire_bound` | total wire length times capacity bounds the traffic-weighted Manhattan distance; on the `k × k` grid no network with the mesh's wiring beats it by more than `3k / (2(k + 1))` |
| timed run (`Network.TimedRun`) | a synchronous, cycle-by-cycle execution of a packet network |
| placement (`Network.Placement`) | a map of a packet network's channels onto the links of a graph |
