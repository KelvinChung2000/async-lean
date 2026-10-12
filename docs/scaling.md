# Scaling with the connections

[← back to the README](../README.md) · [all guides](README.md)

What happens to a network's throughput when every link gets `m` physical connections instead of
one? This guide answers in four steps, each a set of theorems with simulations alongside:

1. **The ceiling.** No routing can do better than `m` times one connection.
2. **Planes reach it.** Splitting the connections into `m` independent copies of the network
   (*planes*, or multiple physical networks) is optimal, safe, and scales exactly linearly, with packets too.
3. **The flow-control gap, and backpressure.** With one-packet buffers, packets reach only part
   of the optimum. Backpressure scheduling reaches all of it, at the cost of per-destination
   queues.
4. **What is necessary.** Adaptive (non-minimal) routing and per-destination queues are both
   required; each is proved with a concrete instance.

A table at the end lists which claims are theorems, which are measurements and what is open.

## Contents

* [In one page](#in-one-page)
* [1. The ceiling: linear is the most any routing gets](#1-the-ceiling-linear-is-the-most-any-routing-gets)
* [2. Planes: optimal, safe, linear with packets](#2-planes-optimal-safe-linear-with-packets)
* [3. Sharing the connections](#3-sharing-the-connections)
* [4. Closing the flow-control gap: backpressure](#4-closing-the-flow-control-gap-backpressure)
* [5. What is necessary](#5-what-is-necessary)
* [6. What is proved, measured and open](#6-what-is-proved-measured-and-open)
* [7. Where everything is](#7-where-everything-is)
* [8. Terminology and the literature](#8-terminology-and-the-literature)

## In one page

| Question | Answer | Kind |
|---|---|---|
| Can routing beat linear scaling? | No: `m` connections give exactly `m` times the fluid optimum of one. | theorem |
| Which scheme reaches it? | `m` planes, each a copy of the best one-connection scheme. | theorem |
| Is the plane network safe? | Yes: deadlock, livelock and starvation free for every `m`, on every graph. | theorem |
| Does it scale linearly with packets? | Yes: planes add their packet throughput exactly, up to `m` times the optimum. | theorem |
| How close do packets get to the optimum? | 46 to 65 % with one-packet buffers (8 × 8 mesh, uniform traffic). | simulation |
| Can any scheduler close that gap? | Backpressure reaches every load below the optimum; no scheduler goes above it. | theorem |
| What does that cost? | Per-destination queues: about `24 m` packets per destination in simulation; a finite (loose) bound is proved. | both |
| Is adaptive routing needed? | Yes: on the torus, shortest-path-only scheduling stops at 2/3 of the 16/15 optimum. | theorem |
| Are per-destination queues needed? | Yes: one first-in first-out queue per node caps throughput at 1 packet per node per slot, whatever `m`. | theorem |
| Can one network have both the escape-channel safety and the optimum? | Open for one-packet buffers. | open |

## 1. The ceiling: linear is the most any routing gets

In the fluid model (`Flow/Fluid.lean`) a network is a set of link capacities, and a traffic
matrix is *routable at throughput θ* if some multicommodity flow carries `θ` times it within
the capacities. Routing, adaptive or not, with or without detours, is a choice of flow, so the
fluid optimum bounds every routing scheme.

`Flow/Scaling.lean` proves that this optimum is homogeneous in the capacities:

| Theorem | Statement |
|---|---|
| `copies_routable_iff` | with `m` connections per link (`Net.copies`), traffic is routable at `θ` iff it is routable at `θ / m` on one connection |
| `opt_copies`, `worstOpt_copies` | the optimum of `m` connections is exactly `m` times that of one, for one matrix and for the worst case over any class |
| `layered_routable`, `opt_superadditive` | unequal connections (a mesh plus express links, say) add: each layer contributes at least its own throughput |
| `mesh_copies_worst`, `torus_copies_worst`, `cube_copies_worst` | worst case over admissible traffic with `m` connections: exactly `4m/k` (mesh), `8m/k` (torus), `2m` (hypercube) |
| `mesh_copies_uniform`, `torus_copies_uniform`, `cube_copies_uniform` | uniform traffic: `m` times the one-connection optimum |

## 2. Planes: optimal, safe, linear with packets

**The scheme.** Treat the `m` connections of every link as `m` planes, each a full copy of the
network. A packet picks a plane when it is injected and stays on it; inside the plane it uses the
best one-connection scheme. The planes' flows add (`Routable.copies`), so in the fluid model this
simple scheme is optimal.

**Safety** (`Routing/Planes.lean`). `Network.planes` puts networks side by side. The library's
safety proofs all follow one recipe (a closed set of legal packet positions, a connected escape
subfunction with a well-founded dependency graph, a ranking), which `Network.SafeCert`
packages; `SafeCert.planes` lifts it to any number of planes, because dependencies never cross
planes.

| Theorem | Statement |
|---|---|
| `Network.planes_correct`, `planes_underLoad` | deadlock and livelock free under every valid selection, starvation free, every packet delivered under sustained load |
| `GraphData.planes_correct`, `planes_budget_correct`, `planes_detour_correct` | the same for planes of the graph networks, on every finite connected graph |
| `torusPlanes_correct` (`Examples/Planes.lean`) | the torus of every size with `m` planes of the detour network |
| `planes_reachable_iff`, `planes_path`, `copies_path` | the planes do not interfere: their runs combine, and `m` copies deliver `m` times the packets |

**Packets in time** (`Routing/Throughput/`). The packet model says which moves are possible,
not when, so it has no throughput of its own. A *timed run* (`Network.TimedRun`) adds time:
rounds in which every channel receives at most one packet. A *placement* says where each
channel sits on a graph, which gives the packet network a fluid network.

| Theorem | Statement |
|---|---|
| `TimedRun.potential_bound` (+ `cut_bound`, `hop_bound`) | under any routing and any selection, a timed run sustaining `ρ · dem` respects every bound of its fluid network |
| `TimedRun.ejected_ge` | everything injected is delivered, except at most what the network holds |
| `planesTimed_injected` | timed runs of the planes combine round by round, injecting the sum |
| `torusPlanes_bound`, `torusPlanes_sustains` (`Examples/Throughput.lean`) | the torus with `m` planes never sustains uniform traffic above `m` times the optimum, and sustains `m` times whatever one plane sustains |

So plane throughput with packets is exactly linear in `m`, up to the fluid optimum it can never
pass.

## 3. Sharing the connections

Planes are the scheme whose scaling is a theorem. With packets, letting a packet use the free
channels of other planes does better. Two ways of sharing are proved safe for every `m`:

* **Shared planes** (`Routing/SharedPlanes.lean`, `GraphData.sharedNet`): each packet keeps its
  escape on its own plane; its adaptive hops may use the adaptive channel of every plane
  (`shared_correct`).
* **Replication** (`Routing/Replicate.lean`, `Network.replicate`): every channel of *any* certified network
  becomes any number of copies, all usable (`replicate_correct`; on the torus `torusReplicated_correct`).

*Simulation* (`scripts/plane_scaling.py`, 8 × 8 torus, two one-packet virtual channels per
connection). Peak accepted throughput **per node and per connection**; a constant column means
linear scaling:

| scheme | m | uniform | transpose | shuffle | bit rev. | hotspot | bit comp. | random perm. |
|---|---|---|---|---|---|---|---|---|
| one connection | 1 | 0.753 | 0.570 | 0.652 | 0.659 | 0.525 | 0.444 | 0.685 |
| planes | 4 | 0.759 | 0.570 | 0.655 | 0.661 | 0.523 | 0.443 | 0.684 |
| shared planes | 4 | 0.877 | 0.632 | 0.726 | 0.757 | 0.549 | 0.544 | 0.774 |
| replicated: 1 escape + `2m − 1` adaptive | 4 | **0.939** | **0.690** | **0.804** | **0.835** | **0.554** | **0.723** | **0.867** |

Planes stay within 0.006 of one connection per connection. Sharing does better than linearly
*relative to one connection with packets*, because one connection with packets reaches only part
of its fluid optimum and more channels recover some of it; nothing exceeds `m` times the fluid
optimum. The 8 × 8 mesh behaves the same way (planes within 0.01; replication 0.643 uniform per
connection at `m = 4`).

## 4. Closing the flow-control gap: backpressure

On the 8 × 8 mesh under uniform traffic the fluid optimum is `63/64 ≈ 0.98` packets per node per
cycle (`mesh_opt`), and the schemes above reach 0.45 to 0.64. The routing paths are not the
problem (XY routing already reaches 99 % of the bisection bound under bit complement); the
buffers are. `Flow/Backpressure/` proves that one scheduler closes the gap completely.

**The model** (`Backpressure/Model.lean`, `Fluid.Run`). Time runs in slots. Every node keeps a
backlog per destination; each slot the scheduler offers every destination a rate on every link
within the capacities, a node sends at most what it holds, and traffic arrives.
**Backpressure** (`Run.Backpressure`) chooses rates maximising `∑ rate × backlog difference`
and serves them in a work-conserving way; the simple rule "give every link, in full, to the
destination whose backlog drops most across it" is such a scheduler (`bpRates_maxWeight`).

| Theorem | Statement | File |
|---|---|---|
| `Run.backpressure_optimal` | every load strictly below a routable traffic keeps the backlog bounded and is delivered in full; the scheduler needs no knowledge of the traffic | `Stability.lean` |
| `Run.potential_bound` (+ cut, hop forms) | no scheduler keeps a bounded backlog above any fluid bound | `Converse.lean` |
| `mesh_backpressure`, `torus_backpressure`, `cube_backpressure` | with `m` connections and uniform traffic the threshold is exactly `m` times the optimum | `Instances.lean` |
| `Run.backpressure_fitsIn`, `mesh_buffer` | finite per-destination buffers suffice (an explicit, loose bound, linear in `m` and `1/δ`) | `Buffers.lean`, `Instances.lean` |
| `Run.backpressure_stable_bursty` | stable for any arrivals within a leaky bucket (whole packets at fractional rates) | `Bursty.lean` |
| `Run.ofArrivalsSeq_int`, `mesh_backpressure_packets` | a whole-packet version exists and is stable on the mesh | `Scheduler.lean`, `Instances.lean` |
| `backpressure_strongly_stable` | under random arrivals (Poisson, for instance) the time-averaged expected backlog is bounded | `Flow/Stochastic.lean` |
| `Run.backpressure_progress`, `mesh_finite_buffer_network` | it never deadlocks; on the mesh it fits in finite buffers, never deadlocks and is stable | `Flow/Necessity.lean` |

The stability proof is the classical quadratic drift argument (Tassiulas and Ephremides): the
sum of squared backlogs falls by `2ε` times the backlog, up to a constant, because the
max-weight rates beat any flow of the traffic.

*Simulation* (`scripts/backpressure_sim.py`, whole packets, Poisson arrivals, 40 000 slots).
Accepted load as a fraction of the fluid optimum:

| network | m | offered 0.90 | 0.95 | 0.98 | 0.99 | 1.01 | delay at 0.95 (slots) |
|---|---|---|---|---|---|---|---|
| mesh (optimum 0.984) | 1 | 0.894 | 0.950 | 0.980 | 0.990 | 1.004 (overloaded) | 662 |
| mesh | 4 | 0.902 | 0.950 | 0.980 | 0.990 | 1.004 (overloaded) | 723 |
| torus (optimum 1.969) | 1 | 0.899 | 0.950 | 0.980 | 0.990 | 1.002 (overloaded) | 271 |

Every load up to 99 % of the optimum gets through, for every `m`. The price is storage and
delay: hundreds of packets queued per node, and delays of hundreds of slots.

*How much buffer* (`backpressure_sim.py --buffers --cap c`, blocking buffers of `c · m`
packets per destination, 8 × 8 mesh, `m = 1`, offered `1 − δ` of the optimum):

| buffer per destination | δ = 0.4 | 0.2 | 0.1 | 0.05 | 0.02 |
|---|---|---|---|---|---|
| `4 m` | 0.42 | 0.50 | 0.54 | 0.55 | 0.56 |
| `16 m` | 0.57 | 0.72 | 0.83 | 0.88 | 0.91 |
| `24 m` | 0.60 | 0.80 | 0.91 | 0.95 | 0.98 |

The threshold is sharp: about `24 m` packets per destination reach the optimum within 2 %, and
less loses far more than the missing storage would suggest.

## 5. What is necessary

| Theorem | What it shows |
|---|---|
| `torusTornado_adaptivity` | on the 8 × 8 torus under tornado traffic, backpressure is stable below 16/15, but no scheduler that moves traffic only along shortest paths keeps a bounded backlog above 2/3: adaptive, non-minimal routing is needed |
| `torusTornado_minimal_backpressure`, `Run.backpressureOn_optimal` | backpressure restricted to some permitted links (for example a certified packet network's hops) reaches exactly the optimum over those links |
| `mesh_headOfLine`, `Run.singleFifo_bound` | a node with a single first-in first-out queue sends at most one packet per slot, so it is never stable above one packet per node per slot whatever `m`: per-destination queues are needed for linear scaling |
| `Network.scoreSel_valid`, `torusPlanes_scoreSel`, `torusReplicated_scoreSel` | choosing among the free permitted hops by any score (backlog differences included) keeps every certified network deadlock and livelock free |

The bridge that makes the first row possible is `Fluid.PotentialFeasibleOn`: a stable run
respects every potential bound on the links it uses, so the library's kernel-checked dual
certificates bound runs exactly as they bound flows (`GraphCert.Model.run_minimal_bound`).

## 6. What is proved, measured and open

| Claim | Status |
|---|---|
| linear scaling is the ceiling; planes reach it; planes are safe | proved |
| planes scale exactly linearly with packets, up to the optimum | proved (timed runs) |
| no packet network exceeds its fluid optimum | proved (timed runs) |
| backpressure reaches the optimum: fluid, bursty, whole-packet, random arrivals | proved |
| finite per-destination buffers suffice for backpressure | proved (loose bound) |
| adaptivity and per-destination queues are necessary | proved (concrete instances) |
| 46–65 % for the proved-safe networks, 99 % for backpressure, the `24 m` threshold | simulation measurements |
| the 58.6 % head-of-line limit of a large switch under random traffic | literature; the deterministic counterpart above is proved |
| random arrivals: the expectation is abstract | proved for every operator with the laws of expectation; that Lebesgue expectation satisfies them needs Mathlib's measure theory |
| the escape-channel packet networks with one-packet buffers under backpressure-style selection reach the optimum | **open**: safety and the ceiling are proved, the throughput is not known |

## 7. Where everything is

| Topic | Lean | Scripts |
|---|---|---|
| fluid scaling | `Flow/Scaling.lean` | |
| planes, shared planes, replication | `Routing/Planes.lean`, `Routing/SharedPlanes.lean`, `Routing/Replicate.lean`, `Examples/Planes.lean` | `plane_scaling.py` |
| packets in time | `Routing/Throughput/` (`Timed`, `Planes`, `Select`, `Graph`), `Examples/Throughput.lean` | |
| backpressure | `Flow/Backpressure/` (`Model`, `Stability`, `Buffers`, `Bursty`, `Converse`, `Scheduler`, `Instances`) | `backpressure_sim.py` |
| necessity | `Flow/Necessity.lean` | |
| random arrivals | `Flow/Stochastic.lean` | |

Reproduce the tables:

```
python3 scripts/plane_scaling.py                       # section 3
python3 scripts/backpressure_sim.py                   # section 4, throughput
python3 scripts/backpressure_sim.py --buffers --cap 24   # section 4, buffers
```

## 8. Terminology and the literature

The names in the library follow the standard terms where one exists:

| Here | In the literature |
|---|---|
| fluid optimum, `Routable dem θ` | maximum concurrent multicommodity flow (Shahrokhi and Matula, 1990); the *ideal throughput* of Dally and Towles, *Principles and Practices of Interconnection Networks* (2004) |
| `potential_bound`, `cut_bound`, `hop_bound` | LP duality for multicommodity flow (dual edge lengths and node potentials); the cut (bisection) bound and the hop-count bound on channel load (Dally and Towles) |
| planes, `Network.planes` | multiple physical networks (Yoon, Jiang, Becker and Dally, 2010), network planes. Not *lanes*: Dally (1992) uses *lane* for a virtual channel, as the older guides here do |
| replication, `Network.replicate` | more channels per link, physical or virtual: in Duato's model every copy is a channel of its own |
| escape channels, `SafeCert` | Duato's theorem: a connected routing subfunction with an acyclic extended channel dependency graph (Duato, 1993) |
| backpressure, `Run.Backpressure`, `MaxWeight` | back-pressure / max-weight scheduling (Tassiulas and Ephremides, 1992) |
| `Run.backpressure_optimal`, `Run.potential_bound` | throughput optimality: stable inside the capacity region (achievability), and no policy stable outside it (the converse) |
| `lyapunov`, `Run.drift` | the quadratic Lyapunov function `∑ Q²` and its one-slot drift (Neely, *Stochastic Network Optimization*, 2010) |
| `Run.frame_drift` | the `T`-slot (frame) drift |
| leaky-bucket arrivals | `(σ, ρ)`-constrained arrivals (Cruz, 1991) |
| `backpressure_strongly_stable` | strong stability: bounded time-averaged expected backlog (Neely) |
| per-destination queues | per-commodity queues of back-pressure routing |
| `SingleFifo`, `mesh_headOfLine` | head-of-line blocking of a single FIFO (Karol, Hluchyj and Morgan, 1987, the 58.6 % limit) |
| selection function, `scoreSel` | Duato's selection function; choosing by a congestion score is congestion-aware adaptive selection |

Two terms are the library's own: a *timed run* (`Network.TimedRun`) is a synchronous,
cycle-by-cycle execution of a packet network, and a *placement* (`Network.Placement`) maps its
channels onto the links of a graph.
