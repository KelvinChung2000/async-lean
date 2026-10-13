# Beyond the mesh: graphs, topologies and the fluid model

[← back to the README](../README.md) · [all guides](README.md)

This guide covers safe routing on every finite connected graph, how much throughput a
topology can give (the fluid model, where results are theorems), and what packets actually
reach (simulation). It ends with the torus experiments that led to the two-phase network
`twoPhaseNet`, which is proved deadlock, livelock and starvation free on every graph.

**In short.**

* Minimal adaptive routing with a spanning-tree escape, with bounded returns and with two-phase routing, are
  safe on every finite connected graph (theorems).
* In the fluid model the optimum of a topology is computable and often exact: on the mesh,
  routing has no room left; on the torus and the hypercube, non-minimal routing can gain up to 60 %
  (theorems, kernel-checked certificates).
* With one-packet buffers, packets reach 35 to 75 % of those optima depending on the topology
  (simulation): the gap is flow control, which [the scaling guide](scaling.md) closes.

## Safe routing on every graph

`Routing/Graph.lean` makes minimal adaptive routing safe on **every finite connected graph**:
virtual channel 1 takes any shortest-path hop, virtual channel 0 routes along a spanning tree
(`GraphData.correct`, `exists_correct`; the torus of every size and the Petersen graph as
instances). With an absorbing escape a packet that enters virtual channel 0 stays there; in
simulation that costs up to 45 % of the throughput, and unbounded returns to virtual channel 1
can livelock (a packet took 95 hops on a 14-hop route). `Routing/GraphBudget.lean` lets a
packet return `B` times, counted in its header, and is safe for every graph and every `B`
(`budget_correct`). Two returns keep 96 to 100 % of the unbounded throughput, with at most 26
hops.

## Is the mesh the right topology?

Is the mesh the right topology? At the same router radix (4 ports) and two virtual channels,
`scripts/routing_graph_sim.py` (peak throughput, mean of 2 seeds; spanning-tree escape rooted
in the centre, `B = 2`, priority selection, `g = 4`) and the exact LP of the fluid model give:

| 8 × 8, 64 routers | wire | LP uniform | uniform | transpose | shuffle | bit reversal | hotspot | bit complement | random permutation |
|---|---|---|---|---|---|---|---|---|---|
| mesh, XY escape | 112 | 0.984 | 0.495 | 0.394 | 0.578 | 0.365 | 0.381 | **0.257** | 0.433 |
| mesh, tree escape | 112 | 0.984 | 0.450 | 0.391 | 0.580 | 0.374 | 0.378 | 0.184 | 0.418 |
| `CA_112`: mesh wire moved to the middle cuts | 112 | 1.148 | 0.449 | 0.344 | 0.650 | 0.384 | 0.407 | 0.190 | 0.399 |
| `D_128`: mesh + 8 express links of length 2 | 128 | 1.313 | 0.517 | 0.397 | 0.643 | 0.427 | 0.411 | 0.215 | 0.469 |
| `DF_156`: `D_128` + 4 folded rows/columns | 156 | 1.575 | **0.550** | **0.461** | **0.698** | **0.443** | **0.456** | 0.212 | **0.463** |

Uniform traffic loads the seven vertical cuts of the mesh in the ratio 7:12:15:16:15:12:7 while
the mesh gives each the same 8 links; summing over the cuts, no radix-4 graph with the mesh's
wire beats it by more than 33 % in the fluid model, and `CA_112`, which moves wire to the middle,
gets half of that (+17 %). With packets, the gain at equal wire disappears: `CA_112` matches
the mesh under uniform traffic (with the same kind of escape), wins under shuffle traffic and
loses under transpose traffic. Extra wire buys throughput roughly in proportion: `D_128`
(+14 % wire) gains 2 to 19 % except under bit-complement traffic; the torus and random 4-regular
graphs (twice and six times the wire) gain 40 to 90 % with packets, and 1.0 and 0.47 times the
mesh's fluid throughput per unit of wire. Under uniform traffic packets reach 50 % of the fluid
optimum on the mesh but only 35 to 40 % on the new designs: their extra capacity sits in a few
links that one-packet channels and a spanning-tree escape cannot keep busy. Over a wider set of radix-4 graphs (torus, folded and twisted torus, circulants, de
Bruijn, random and search-optimised 4-regular graphs, laid out to minimise wire) the fluid model
gives 2 to 3.8 times the mesh's uniform throughput at 64 and 256 routers, and 0.83 to 1.00 times
per unit of wire; a wire bound (total wire over the mean Manhattan distance of the traffic) caps
any graph at 1.33 (64 routers) and 1.41 (256) times the mesh per unit of wire under uniform
traffic. The folded torus is the cleanest trade: twice the throughput for twice the wire, no
link longer than 2.

### The grid wire bound

The grid wire bound is a theorem (`Flow/Fluid.lean`, `Flow/MeshWire.lean`, fluid model, uniform
traffic, every k): for every network on the k × k grid with links of capacity at most 2 and wire
lengths at least the Manhattan length — any topology, any radix, any routing —
`θ ≤ 6 · wire / k³` (`throughput_le_wire`); the mesh's optimum is exactly `8(k² − 1)/k³` for
even k (`mesh_opt`: an XY flow reaches it for every k, the cut through the middle bounds every
routing); so no network with the mesh's wire beats it by more than `3k / (2(k + 1)) < 3/2`
(`grid_wire_bound`; 4/3 on the 8 × 8 grid, `grid_wire_bound_eight`). Both bounds come from one weak
duality argument, `Fluid.potential_bound`.

## Routing optima in the fluid model

### Routing on the mesh has no room left (fluid model, proved)

In the fluid model routing is a
choice of flow, so the optimum below bounds every routing — oblivious, adaptive, non-minimal,
with global knowledge — and a minimal flow (`Flow.Minimal`: every hop gets closer) reaching it
shows that non-minimal routing adds nothing:

| traffic | optimum (per source) | reached minimally | theorem |
|---|---|---|---|
| uniform, every k ≥ 2 | 8(k² − 1)/k³ (even k), 8/k (odd k) | yes, XY | `uniform_minimal_opt`, `mesh_opt_all` |
| bit complement, every even k | 4/k | yes, XY or O1TURN | `bitcomp_opt`, `bitcomp_minimal` |
| transpose, 8 × 8 | 10/11 | yes | `transpose8_opt`, `transpose8_minimal` |
| shuffle, 8 × 8 | 1 | yes | `shuffle8_opt`, `shuffle8_minimal` |
| bit reversal, 8 × 8 | 20/21 | yes | `bitrev8_opt`, `bitrev8_minimal` |
| hotspot, 8 × 8 | 40/67 (the hotspot's four input links) | no: minimal flows reach 840/1471, 4.5 % less | `hotspot8_opt`, `hotspot8_minimal_opt` |
| worst case over admissible traffic, every even k | 4/k | yes, O1TURN (XY: 2/(k − 1), `xy_worst_opt`) | `worst_opt`, `o1turn_admissible` |

Admissible traffic (`Admissible`) is every matrix in which no node sends or receives more than 1,
permutations included: O1TURN routes all of them at 4/k minimally, and the bit complement
shows no routing does better (`Flow/MeshWorst.lean`). The 8 × 8 rows are exact LP solutions
(`scripts/fluid_certificates.py`) checked by the kernel: a flow at the optimum, and link lengths
whose potential bound (`Flow.potential_bound_on` for the minimal-only hotspot bound) matches it
(`Flow/Certificate.lean`, `Flow/MeshPatterns.lean`). What remains between these optima and the
simulated throughput (35 to 60 %) is flow control, not routing.

### Other topologies: when non-minimal routing helps

When non-minimal routing helps is a property of the topology and the traffic together.
The bounds above hold on every network; what is special about the mesh is that minimal routing
already meets them. In general (`Flow/Tree.lean`, `Flow/Symmetric.lean`, `Flow/Valiant.lean`,
`Flow/GraphPatterns.lean`):

* **For every traffic matrix: only trees.** On a connected network, minimal routing reaches the
  optimum for every traffic matrix iff the network is a tree (`minimal_optimal_iff_isTree`): on a
  tree every link is a cut that the unique route crosses; on any edge of a cycle, traffic between
  its ends gets twice as much with non-minimal routing (`nonminimal_helps`). So a topology class on which
  minimal routing suffices has to be stated for a traffic class.
* **Uniform traffic: every arc-transitive network.** If automorphisms preserving the traffic map
  every link to every other, averaging any minimal routing over them loads all links equally, so
  minimal routing is optimal at `∑ cap / ∑ traffic × distance` (`symmetric_opt`). Instances: the
  torus, 16(k² − 1)/k³ for even k ≥ 4 and 16/k for odd k (`torus_uniform_opt`), and the
  n-cube, 4(2ⁿ − 1)/2ⁿ (`cube_uniform_opt`).
* **Worst case over admissible traffic: Valiant on every symmetric network.** If uniform traffic
  (including each node itself) is routable at θ, every admissible matrix is routable at θ/2 by
  routing through a random intermediate node (`valiant`). With the bisection cut this is exact
  on the mesh (4/k, `valiant_mesh_opt`), the torus (8/k for even k ≥ 4, `torus_worst_opt'`) and
  the hypercube (2, `cube_worst_opt'`). On the mesh minimal routing (O1TURN) also reaches it; on
  the 8 × 8 torus it cannot: tornado traffic allows only 2/3 to minimal flows against 16/15 with
  non-minimal flows, below the worst-case optimum 1 (`torusTornado_minimal_opt`).

### Exact optima on 64 routers

Exact optima on 64 routers (kernel-checked LP certificates, `scripts/graph_certificates.py`):

| traffic | 8 × 8 torus: minimal / any | 6-cube: minimal / any |
|---|---|---|
| tornado | 2/3 / 16/15 (+60 %) | 2 / 2 |
| shuffle | 1 / 8/5 (+60 %) | 12/5 / 108/31 (+45 %) |
| transpose | 4/3 / 20/11 (+36 %) | 4 / 4 |
| neighbour | 2 / 16/7 (+14 %) | — |
| bit reversal | 16/9 / 40/21 (+7 %) | 4 / 4 |
| bit complement | 1 / 1 | 2 / 2 |

On the torus and the hypercube there is room left for routing: a deadlock-free routing that
takes bounded non-minimal hops (as `Routing/GraphBudget.lean` allows) could gain up to 60 % in
the fluid model where every minimal scheme is stuck.

## What packets reach (simulation)

### Flow control at equal storage (simulation)

The gap between these fluid optima and the
packet throughput comes from one-packet channels. `scripts/flow_control_experiments.py` keeps
the mesh's 2 slots per directed link and reallocates them (8 × 8, offered 0.8, Duato's
routing):

| slots | uniform | transpose | shuffle | bit reversal | bit complement | hotspot |
|---|---|---|---|---|---|---|
| one per virtual channel (baseline) | 0.449 | 0.420 | 0.528 | 0.327 | 0.180 | 0.373 |
| shared, escape may take both | 0.391 | 0.399 | 0.476 | 0.292 | 0.147 | 0.323 |
| moved to the middle (1,2,2,4,2,2,1 lanes per position) | 0.526 | 0.390 | 0.593 | 0.261 | 0.325 | 0.464 |
| 3 per link (+50 % storage) | 0.660 | 0.478 | 0.634 | 0.437 | 0.269 | 0.440 |

Sharing slots or deepening one lane (one lane of depth 2 under XY: 0.353 against 0.493 for
two lanes) loses: head-of-line blocking, and escape packets hold the shared slots. Moving lanes
to the middle trades, like moving wire there: large gains under uniform, shuffle, bit complement
and hotspot traffic, losses under transpose and bit reversal. Only more storage gains
everywhere. No equal-storage allocation tried beats the existing schemes on every pattern.

### Non-minimal routing on the torus with packets (simulation)

`scripts/torus_experiments.py`, 8 × 8
torus, 2 virtual channels of one-packet buffers, peak accepted throughput (mean of 2 seeds):

| scheme | uniform | transpose | shuffle | bit rev. | bit comp. | hotspot | tornado | neighbour | random perm. |
|---|---|---|---|---|---|---|---|---|---|
| dimension order, dateline VCs | 0.249 | 0.162 | 0.226 | 0.126 | 0.284 | 0.162 | 0.099 | **1.000** | 0.311 |
| Valiant | 0.476 | 0.457 | 0.470 | 0.442 | 0.402 | 0.397 | **0.436** | 0.826 | 0.475 |
| UGAL | 0.711 | 0.562 | 0.625 | 0.626 | 0.448 | 0.514 | 0.400 | 0.978 | 0.643 |
| `GraphData.net` (minimal adaptive, tree escape) | 0.752 | 0.569 | **0.651** | 0.657 | 0.445 | 0.522 | 0.371 | **1.000** | **0.684** |
| + source picks minimal / Valiant (`ringvx10`) | **0.753** | **0.572** | 0.643 | **0.659** | **0.449** | 0.525 | 0.411 | 0.992 | 0.674 |
| + long way round a ring (`ringvd30`) | 0.751 | 0.571 | 0.634 | 0.658 | 0.443 | **0.528** | 0.431 | 0.990 | 0.668 |

Dimension order with datelines uses one virtual channel per hop, which halves its lanes;
the tree-escape schemes use both. The minimal adaptive network already beats the existing
schemes on every pattern but tornado (Valiant +17 %) and bit complement (UGAL +0.7 %). Letting
the source pick an intermediate by congestion recovers tornado to within 1 % of Valiant (`ringvd30`)
at a cost of about 1 % on bit complement and neighbour traffic, or keeps every pattern but
tornado and neighbour at or above the existing schemes (`ringvx10`). No variant tried is at least as good as every
existing scheme on every pattern: the non-minimal routes that tornado needs cost a little where none are
needed, the same trade-off as on the mesh, now at the 1 % level.

Sources that learn the in-network latency of each option (`bandit2`: minimal, long way in x
or y, random intermediate; 2 % exploration) do better (4 seeds): tornado 0.441 (Valiant 0.436),
transpose 0.569, shuffle 0.650, bit reversal 0.651, hotspot 0.521, random permutation 0.678,
uniform 0.746, neighbour 1.000 — ahead of every existing scheme on seven patterns and tied on
neighbour — but bit complement 0.440 against UGAL's 0.448. Every rule tried (congestion
weights, gates, hysteresis, pricing extra hops) moves along one frontier between tornado and
bit complement (for example 0.404 / 0.447 with hop pricing): latency-greedy sources reach an
equilibrium in which the long way is as slow as the short one, which is right for tornado and
slightly too much detouring for bit complement — the gap between selfish and system-optimal
routing. Closing it needs a signal about the cost a non-minimal route imposes on others; none was found,
and no impossibility is proved (in the fluid model an adaptive routing can reach every
pattern's optimum).

### A torus scheme ahead of every existing one on every pattern (simulation)

Three local
signals separate the patterns: a marginal-cost price (latency² / hops^0.7, system-optimal
rather than selfish choices), smoothed flow counts per output port (the long way only when it
carries at most half the packets of the minimal direction — at saturation occupancy is 1
everywhere, flow counts still differ), and the source's own recent destinations (Valiant only
for a source whose last 8 packets went to at most 2 nodes: concentrated traffic, where
spreading helps). `bandit2m7f5k`, `scripts/torus_final.py` (peak over offered loads 0.3 to
1.0, mean of 4 seeds):

| scheme | uniform | transpose | shuffle | bit rev. | bit comp. | hotspot | tornado | neighbour | random perm. |
|---|---|---|---|---|---|---|---|---|---|
| dimension order, datelines | 0.254 | 0.162 | 0.226 | 0.126 | 0.284 | 0.162 | 0.100 | 1.000 | 0.311 |
| Valiant | 0.475 | 0.457 | 0.470 | 0.443 | 0.403 | 0.398 | 0.436 | 0.825 | 0.476 |
| UGAL | 0.711 | 0.561 | 0.625 | 0.625 | 0.448 | 0.517 | 0.401 | 0.978 | 0.644 |
| **`bandit2m7f5k`** | **0.753** | **0.567** | **0.646** | **0.646** | **0.450** | **0.523** | **0.442** | **1.000** | **0.672** |

It is ahead of the best existing scheme on eight patterns (+0.4 % on bit complement, +1.4 % on
tornado, +6 % on uniform) and at the injection limit of one packet per node per cycle, with
dimension order, on neighbour traffic. It is a selection of `twoPhaseNet` (`Routing/GraphTwoPhase.lean`):
the source picks an intermediate (none, a node on the long way round, or a random node) from
`anyIntermediate`, adaptive hops are minimal towards it, the escape is the spanning tree, returns are
bounded (`B = 2`) and injection is throttled — so it is deadlock free, livelock free, starvation
free and delivers under sustained load (`torus_valiant_correct`, `twoPhase_underLoad_of_sourceSel`).
The margins on bit complement and tornado are a few standard errors of the simulation; they
are measurements, not theorems, and our own minimal adaptive `GraphData.net` is still slightly
ahead of it on transpose, shuffle, bit reversal and random permutation.
Lower exploration (0 to 1 %), margins a non-minimal route must beat the minimal route by (5 to 25 %),
and a larger margin for the random intermediate do not close that last gap (at best 0.568 /
0.651 / 0.656 / 0.679 against 0.570 / 0.652 / 0.658 / 0.684) without giving up tornado: under
those permutations the learning sources still send 2 to 4 % of packets on non-minimal routes, about the
1 % of throughput that minimal routing keeps. Being ahead of the existing schemes and also of
our own minimal network on every pattern remains open. Picking, among the free minimal hops,
the one into the router with the most free channels (`C`) helps the minimal network a little
(transpose 0.573, bit reversal 0.660, random permutation 0.686) and the two-phase scheme on bit
complement and tornado (0.454, 0.445), but not enough on shuffle, bit reversal, hotspot and
random permutation; dropping the random intermediate (`Y`) keeps the permutations at the
minimal network's level but loses tornado (0.400) and bit complement (0.444).

### Significance

With 8 fresh seeds and standard errors (`scripts/torus_significance.py`), `bandit2m7f5k` is
ahead of the best published scheme on every pattern but neighbour, where every scheme that
reaches it is at the injection limit:

| | uniform | transpose | shuffle | bit rev. | bit comp. | hotspot | tornado | neighbour | random perm. |
|---|---|---|---|---|---|---|---|---|---|
| best of DOR / Valiant / UGAL | 0.7109 ±3 | 0.5613 ±2 | 0.6244 ±2 | 0.6255 ±3 | 0.4476 ±5 | 0.5166 ±6 | 0.4352 ±4 | 1.0000 | 0.6438 ±4 |
| `bandit2m7f5k` | **0.7522 ±3** | **0.5664 ±4** | **0.6458 ±7** | **0.6462 ±5** | **0.4506 ±7** | **0.5231 ±13** | **0.4416 ±4** | 1.0000 | **0.6729 ±6** |

(± in units of 10⁻⁴.) The narrowest margins, bit complement and hotspot, are 3.5 and 4.5
combined standard errors. Our own variants disagree with each other by real margins (the
minimal network beats its congestion-aware version on hotspot, 0.5231 against 0.5178, and loses
on transpose, 0.5684 against 0.5716), so no scheme can be expected to be ahead of every variant;
the bar is the published schemes.

How much of the torus's lead over the mesh is the scheme and how much the links? In the fluid
model the torus's optimum is 1.6 to 2 times the mesh's (1.0 under hotspot traffic); with packets
the torus scheme reaches 1.2 to 1.6 times the best mesh scheme, i.e. 31 to 45 % of the torus's
fluid optimum against 42 to 65 % on the mesh (88 % against 65 % under hotspot traffic). The
torus's lead is the extra links, and less than they allow; the detour scheme itself adds over
minimal routing on the same torus only under tornado (+19 %) and bit complement (+1 %). On the
mesh (`TOPO=mesh`, same tree escape, 4 seeds) the same scheme matches minimal routing under
uniform, hotspot and tornado traffic (+1 %) and loses 4 to 5 % under shuffle, bit reversal and
random permutation: the fluid model leaves the mesh no room for detours, and the learning
still takes some.

## The two-phase network is safe on every graph

These two-phase schemes are safe on every graph: `Routing/GraphTwoPhase.lean` adds to the header
`(d, b)` of `GraphBudget` an intermediate node `w` chosen at the source from any list `W s d`
(Valiant, the long way round a ring, or none); adaptive hops head for `w` and drop it on
arrival, the escape heads for `d` and drops it. For every finite connected graph, every budget
and every `W` the network is deadlock free, livelock free (at most `dist s w + (B + 1) ·
rankBound` hops), starvation free and delivers under sustained load (`twoPhase_correct`,
`twoPhase_underLoad`, `twoPhase_hops_le_some`; torus instances in `Examples/GraphTwoPhase.lean`), and
with `w = none` it is exactly `GraphBudget`'s network (`twoPhaseNet_route_none`). Since the source
may pick any element of `W s d`, the congestion-based choices of `ringvx` and `ringvd` are
covered.
