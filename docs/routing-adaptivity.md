# How adaptive can routing be, and which selection performs?

[← back to the README](../README.md) · [all guides](README.md)

This guide continues section 7 of the README. It covers two questions about deadlock-free
routing on meshes: how many hops a routing function can permit (maximal adaptivity, proved for
every mesh size) and which run-time selection among those hops gives the best throughput
(simulation), then the packet-level ceiling and ideas from other fields. Everything marked
*simulation* is a measurement from the scripts in [`scripts/`](../scripts/README.md), not a
theorem.

## How adaptive can routing be?

More permitted hops give the selection function more free channels to choose from. Can a
deadlock-free routing function always be made more adaptive? Fix the hops you allow, `U`
(for minimal routing on a mesh with two virtual channels: every productive hop on either
virtual channel, `minimalHops k`). Then:

| Statement | Meaning |
|---|---|
| `N.Extends N'` | `N'` permits every hop of `N` (same arrivals and injections) |
| `N.Within U` | every hop of `N` is a hop of `U` |
| `N.MaximallyAdaptive U` | every deadlock-free network within `U` that extends `N` permits no other hop at any pair a packet of `N` can occupy: adding **any** set of hops of `U` introduces a deadlock |

`async_decide` proves `N.MaximallyAdaptive U` for a concrete network. For every hop of `U` that
`N` does not permit, it finds a run of `N` with that hop into a configuration that is
deadlocked whatever else is added. When there is no such configuration, it splits on whether
the hop that would free a packet is permitted. The kernel re-checks every run
(`Network.maximallyAdaptive_of_maxCheck`).

[`Examples/OptimalRouting.lean`](../AsyncLean/Examples/OptimalRouting.lean) answers the question
for meshes:

```lean
open AsyncLean.Examples Mesh

-- Duato's mesh (XY escape on virtual channel 0) can be improved…
example : ¬ (duatoMesh 3).MaximallyAdaptive (minimalHops 3) := duatoMesh_not_maximal
-- …by letting virtual channel 0 also follow the west-first turn model. The result is correct
-- for every mesh size, also under wormhole switching, and every packet takes a shortest path.
example (k : ℕ) : (westFirstMesh k).Correct := westFirstMesh_correct k
example (k : ℕ) : (westFirstMesh k).WormholeCorrect := westFirstMesh_wormholeCorrect k
-- After that, no productive hop can be added without a deadlock, on any mesh.
example (k : ℕ) : (westFirstMesh k).MaximallyAdaptive (minimalHops k) :=
  westFirstMesh_maximal_all k
example (k : ℕ) : (northLastMesh k).MaximallyAdaptive (minimalHops k) :=
  northLastMesh_maximal_all k
-- The two maximal meshes are incomparable: no deadlock-free routing contains both.
example (k : ℕ) (hk : 2 ≤ k) (N : Network ℕ ℕ) (h₁ : (westFirstMesh k).Extends N)
    (h₂ : (northLastMesh k).Extends N) (hU : N.Within (minimalHops k)) : ¬ N.DeadlockFree :=
  no_common_improvement_all hk N h₁ h₂ hU
```

On a concrete mesh `async_decide` finds the deadlocks itself
(`example : (westFirstMesh 3).MaximallyAdaptive (minimalHops 3) := by async_decide`). The proof
for every size ([`Examples/MeshMaximal.lean`](../AsyncLean/Examples/MeshMaximal.lean)) follows a
packet that took an extra hop: either it keeps going vertically on virtual channel 0, or it
stops next to a group of 8 or 13 packets that deadlock with it. Eight such groups are checked
by the kernel in a 3 × 3 mesh and carried into the `k × k` mesh by a generic embedding theorem
(`Network.not_deadlockFree_of_runGoodB`, [`Routing/Embed.lean`](../AsyncLean/Routing/Embed.lean)).
The north-last mesh is correct for every size as well
([`Examples/MeshNorthLast.lean`](../AsyncLean/Examples/MeshNorthLast.lean)); under wormhole
switching Duato's condition fails for it, while it holds for the west-first mesh.

### One yardstick per cost

"Most adaptive" depends on what you allow; fixing the yardstick by
the cost to minimise gives these results, all for every mesh size
([`Examples/MeshMetrics.lean`](../AsyncLean/Examples/MeshMetrics.lean)):

| Cost | Optimum, proved | Reached by |
|---|---|---|
| Hops (zero-load latency) | no routing that moves between neighbours takes fewer hops than the distance (`hops_lower_bound`) | every scheme below takes exactly that many (`family_latency_optimal`) |
| Buffers: 1 virtual channel | maximally adaptive among minimal routing on one virtual channel (`westFirst1_maximal_all`, `northLast1_maximal_all`); XY is not (`xyMesh_not_maximal_all`) | `westFirst1`, `northLast1`, correct also under wormhole switching |
| Buffers: 2 virtual channels | maximally adaptive among minimal routing on two virtual channels | `westFirstMesh`, `northLastMesh` |
| Routing table | at least 4 decisions per inner router for any deadlock-free minimal routing (`table_lower_bound`) | XY: exactly 4 (`xy_table`); turn-model meshes: at most 8 on every size |

No routing function is best for every cost: the table is a set of Pareto points.
[`scripts/validate_routing.py`](../scripts/validate_routing.py) replays every deadlock the
maximality proofs build on meshes up to 8 × 8 and re-checks acyclicity, hop counts and table
sizes; it is a cross-check, not part of the proofs.

### More adaptive is not always faster

In a cycle-level simulation
([`scripts/routing_sim.py`](../scripts/routing_sim.py), 8 × 8 mesh, not part of the proofs) the
west-first mesh with a random choice among free hops matches Duato's mesh under uniform traffic
below saturation and has half its latency under transpose traffic near saturation. Under
bit-complement traffic, though, it saturates at about 0.11 packets per node and cycle against
0.18: the extra hops crowd the escape channels. Duato's theorem only needs the selection never
to refuse a free *escape* hop (`Network.EscapeSel`, `Network.deadlockFreeWith_of_escape`), so a
router may use the extra hops only towards lightly loaded routers (`westFirstGated`, proved
correct for every size by `westFirstGated_correct`). That policy matches Duato's mesh under
uniform and bit-complement traffic and has a third of its latency under transpose traffic.
On one virtual channel there is no such free lunch: west-first beats XY under transpose
traffic (throughput 0.17 against 0.13 at an offered 0.3) but XY saturates later under uniform
(0.19 against 0.12) and bit-complement traffic (0.10 against 0.07), with or without gating.

So there is no single most adaptive deadlock-free routing function to look for. There are
several maximal ones, and `MaximallyAdaptive` certifies that a design is one of them. Wormhole
deadlock freedom implies store-and-forward deadlock freedom
(`Network.deadlockFree_of_wormholeDeadlockFree`), so maximality also holds under wormhole
switching (`Network.MaximallyAdaptive.wormhole`).
`#eval N.explainMaximal StateOrd.cmp StateOrd.cmp U` reports the search, or a hop that can be
added.

## A selection that performs

Maximal adaptivity says which hops a packet *may* take; throughput under load depends on which
one it *does* take. `priorityMesh` (`Examples/MeshPriority.lean`) offers each packet the free hops
of the first priority level that has one: its dimension-order hop (XY on virtual channel 0, YX on virtual
channel 1, so flows in different orders share no channel), then the escape hop, then any hop on
virtual channel 1. It also throttles the sources: a packet leaves its injection channel only
towards a router with at least `g` of its 8 outgoing channels free (channels leaving the mesh count as free). Throttling refuses free
escape hops, so Duato's condition for selections fails; `Network.deadlockFreeWith_of_source`
(`Routing/Source.lean`) proves Duato's theorem for selections that may hold packets back at
their sources as long as a source lets its packet go once the rest of the network is empty.
Duato's mesh, the west-first and the north-last mesh are deadlock, livelock and starvation free
under `priorityMesh` for every size and every `g ≤ 8` (`duatoPriority_correct`,
`westFirstPriority_correct`, `northLastPriority_correct`). Only the throttled escape level
(`Mesh.escPriority`) matters for this: the same holds for **every** level list containing it,
whatever the other levels prefer and whatever they read of the network (`duatoPriorities_correct`,
`westFirstPriorities_correct`, `northLastPriorities_correct`), so a new preference costs no new proof.

Peak accepted throughput (packets per node and cycle, the largest over a sweep of offered
loads; `python3 scripts/routing_sim.py --bench` prints the underlying tables):

| 16 × 16 mesh | uniform | transpose | shuffle | bit reversal | hotspot | bit complement | worst / best |
|---|---|---|---|---|---|---|---|
| Duato's mesh, random selection | 0.199 | 0.197 | 0.149 | 0.138 | 0.114 | 0.089 | 0.75 |
| Duato's mesh, random, throttled (`g = 4`) | 0.228 | 0.196 | 0.155 | 0.138 | 0.114 | 0.104 | 0.78 |
| XY on both virtual channels | 0.227 | 0.133 | 0.125 | 0.096 | 0.082 | **0.120** | 0.60 |
| O1TURN | 0.174 | 0.125 | 0.107 | 0.087 | 0.090 | 0.100 | 0.54 |
| west-first mesh, random selection | 0.200 | **0.221** | 0.198 | 0.113 | 0.080 | 0.080 | 0.67 |
| **`priorityMesh`, `g = 4`** | **0.237** | 0.202 | **0.199** | **0.140** | **0.118** | 0.108 | **0.90** |

On 8 × 8 meshes the picture is the same (`priorityMesh` first under uniform, shuffle, bit-reversal
and hotspot traffic, worst case 0.87 of the best against 0.84 for the next scheme); the
west-first mesh with a random selection is 15 % faster under transpose traffic and XY on both
virtual channels 12 % faster under bit-complement traffic. Past saturation `priorityMesh` keeps
its throughput, where Duato's mesh with a random selection loses up to half of it (16 × 16,
uniform: 0.14 at an offered 0.3). On 4 × 4 meshes, which saturate late, the throttling costs it
3 to 5 % against the random selections. No selection among those tried was best on every
pattern: taking the extra hops of the west-first mesh helps transpose traffic and makes hotspot
traffic collapse, and bit-complement traffic favours keeping every packet on its XY path.

### What is left, and why

`scripts/routing_experiments.py` tries further selections (8 × 8 mesh, peak over a load sweep, mean of 2 seeds):

| 8 × 8 mesh | uniform | transpose | shuffle | bit reversal | hotspot | bit complement |
|---|---|---|---|---|---|---|
| best existing scheme | 0.492 | **0.447** (west-first) | 0.524 | 0.345 | 0.373 | **0.298** (XY on both) |
| `priorityMesh` | 0.506 | 0.399 | 0.527 | 0.374 | **0.386** | 0.265 |
| ... with the west-first hops last | 0.507 | 0.429 | 0.543 | 0.369 | 0.379 | 0.250 |
| global view (least occupied path) | **0.508** | 0.402 | 0.540 | 0.376 | 0.382 | 0.263 |
| sources learning their mode | 0.495 | 0.418 | **0.546** | **0.399** | 0.374 | 0.249 |
| controller switching modes | 0.506 | 0.410 | 0.531 | 0.357 | 0.378 | 0.282 |
| two-phase XY (via a random node) | 0.448 | 0.330 | 0.449 | 0.260 | 0.327 | 0.235 |

Only the global-view row and the west-first row are selections the theorems above cover (they
read nothing but the configuration); learning sources, the mode-switching controller, two-phase
XY, patience and distance rules keep per-packet or global state, which a `Selection` cannot
read. Each of them always admits the free escape hop, so the same argument should apply, but
that is not proved. Seeing the whole network does not help (the global-view row matches `priorityMesh`), so the gaps
are not for lack of information. Under bit-complement traffic every packet crosses both
bisections; XY on both virtual channels pushes about 0.6 packets per cycle through each
bisection channel, which is what a saturated chain of one-packet channels carries in this model
(0.50 to 0.57), so in this model it is at the limit (a simulation measurement; in the fluid model the bisection bound 4/k is a theorem for every even k, `bitcomp_opt`) and can be matched but not beaten, and every deviation
from XY loses there. Transpose traffic needs the deviations and no throttling. Rules that trade
between the two (waiting before deviating, choosing the mode by distance, a controller
switching modes) move along that trade-off without reaching both ends.

## The packet-level ceiling

Why do packets reach only about half of the fluid optimum? A chain of one-packet lanes under
our update (every packet tries one hop per cycle, in random order) is an exclusion process
(TASEP with shuffled update). `Packet/Exclusion.lean` models one cycle on a ring of lanes of
depth `N` for every order of moves and proves: for one-packet lanes the expected number of
moves per lane per cycle is at most 1/2 for every ring length and every configuration
(`half_bound`, tight: `alternating_moves`); with lanes of depth `N ≥ 2` holding 1 to `N − 1`
packets every lane moves every cycle (`all_move`). `scripts/xp_ceiling.py` computes the current
exactly (rings of 4 to 8 lanes) and by simulation:

| update rule | N = 1 | N = 2 | N = 4 | N = 8 |
|---|---|---|---|---|
| random order (ours), parallel | 1/2 | 1 | 1 | 1 |
| random sequential (one attempt per lane) | 0.25 | 0.42 | 0.60 | 0.76 |

An open chain fed and drained every cycle carries 1, 2/3, 0.566, 0.512 and 0.500 with 2, 3, 4,
8 and 64 lanes (the 0.50 to 0.57 measured earlier); above half occupancy the current falls
(0.42 at 0.69), so a throttle should keep lanes about half full — which is what `g = 4` does.
`Packet/Ceiling.lean` scales the fluid optima: with half capacity they are exactly 63/128,
5/11, 1/2, 10/21, 20/67, 1/4 on the 8 × 8 mesh (`mesh8_half`) and 63/64, 10/11, 4/5, 20/21,
1/2, 8/15 on the 8 × 8 torus (`torus8_half`).

Half the fluid optimum is an estimate, not a theorem for networks: lanes that feed an ejection
port or have several successors are not in a saturated ring and beat 1/2 (the busiest 10 % of
lanes carry 0.53 to 0.75). The best mesh schemes are at or 3 to 30 % above it; on the torus
packets reach 71 to 90 % of it, so there is room. Deeper lanes remove the exclusion limit
altogether (8 × 8 mesh, uniform: 0.495, 0.752, 0.838, 0.880 for N = 1, 2, 4, 8; the busiest lanes
then run at 1 and what remains is load balance). The only proved packet-level bound for whole
networks is still the fluid optimum. (Simulators count throughput per node and the fluid
optimum per sending node: for transpose and bit reversal multiply the fluid figures by 56/64,
for shuffle by 62/64, before comparing.)

## Six ideas from other fields (simulation)

Each idea was tried at equal resources on the 8 × 8 torus and mesh (`scripts/xp_*.py`, 4 seeds,
peak over offered loads; numbers are packets per node and cycle):

| idea | script | best result | safety |
|---|---|---|---|
| ramp metering (traffic engineering) | `xp_ramp.py` | feedback on occupancy fails: the critical occupancy depends on the pattern. A configuration-only throttle switched by the share of escape channels among occupied ones (`lx2_4_36_2`) beats the torus `min` by 2 to 10 % on seven patterns, −1.2 % on shuffle; on the mesh nothing beats `g = 4` | configuration-only, opens when the network is empty: needs a short instance proof |
| link prices (multiplicative weights) | `xp_prices.py` | converges to the fluid optima (within 0.5 to 5 %); with packets, choosing the adaptive hop by price + propagated route cost (`H`) beats `min` and `bandit2m7f5k` on seven torus patterns by 1.5 to 3.5 %; price-chosen detours (`P`) win tornado and bit complement but lose shuffle; small gains on the mesh | choices covered by `twoPhaseNet`; prices are history |
| backpressure, arbitration (queueing) | `xp_backpressure.py`, `xp_arbiter.py` | in-network packets before the injection lane, then oldest first, looked like +2 to +23 %, but see below | arbitration is the schedule; injection-last is not fair |
| Physarum (biology) | `xp_physarum.py` | plain dynamics find shortest paths only; a direction-aware saturating variant gets within 0.6 to 2.4 % of the fluid optima; with packets it lands on the tornado / bit-complement frontier | at the source: covered |
| Braess, tolls (game theory) | `xp_tolls.py` | the M/M/1 Pigou toll is latency² / hops; it lifts tornado to 0.452 to 0.459 (best published 0.436) with bit complement ≥ 0.450; random permutation and shuffle stay 0.8 to 1.7 % below `min`; the fluid-optimal split is the wrong target for packets | covered |
| exclusion processes (physics) | `xp_ceiling.py` | the packet-level ceiling above | proved for rings |

**A modelling caveat that affects every packet-level number.** The simulators let a packet
enter a channel vacated earlier in the same cycle (28 to 46 % of moves). `xp_arbiter.py`
re-runs with no such chaining (a move may only enter a channel free at the start of the cycle,
as with credits delayed by a cycle) and with maximal chaining. The arbitration gain only partly
survives (tornado, bit complement, hotspot; on uniform, transpose and random permutation it
turns into losses of 2 to 9 %), part of the hotspot gain is sources being starved (the worst
source injects 1 to 2 % of the mean), and when the published schemes get the same arbiter they
gain as much: without chaining no scheme of ours is ahead on every pattern (torus `min/P/l:io`
loses transpose by 6 % and tornado by 1.1 %; on the mesh west-first with the same arbiter is
best on four of six patterns). The packet-level comparisons in this README are therefore
specific to the sequential-move model; which scheme is best depends on how moves within a
cycle are resolved, and only the safety results are independent of it.

With random arbitration for every scheme, the torus ranking does survive the no-chaining model
(`xp_arbiter.py run torus ... none`, 4 seeds, peak over offered 0.2 to 1.0):

| no chaining | uniform | transpose | shuffle | bit rev. | bit comp. | hotspot | tornado | neighbour | random perm. |
|---|---|---|---|---|---|---|---|---|---|
| dimension order | 0.1998 | 0.1230 | 0.1884 | 0.1002 | 0.2134 | 0.1342 | 0.0783 | 1.0 | 0.2521 |
| Valiant | 0.3484 | 0.3467 | 0.3503 | 0.3296 | 0.2914 | 0.2962 | 0.3106 | 0.7115 | 0.3518 |
| UGAL | 0.5288 | 0.4244 | 0.4696 | 0.4622 | 0.3092 | 0.4150 | 0.2982 | 0.9531 | 0.4714 |
| `min` | 0.5763 | 0.4318 | 0.4959 | 0.4999 | 0.3026 | 0.4355 | 0.2545 | 1.0 | 0.5112 |
| **`bandit2m7f5k`** | **0.5757** | **0.4299** | **0.4828** | **0.4843** | **0.3145** | **0.4339** | **0.3187** | 1.0 | **0.4952** |

`bandit2m7f5k` is ahead of the best published scheme on every pattern but neighbour (tied at
the injection limit) in this model too, by 1.3 % (transpose) to 9 % (uniform), and
2.6 % on tornado (Valiant). Throughput is about 20 to 30 % lower than with chaining for every
scheme. What does not survive is a comparison in which the arbitration order is also a design
choice for everyone: with injection-last arbitration the published schemes gain more on some
patterns than ours (above).

**One torus scheme at least as good as every other, in both move models (simulation).**
`scripts/xp_combo.py`, `C:hop=price:src=toll:pm=0.2:thr=lx2_4_32_2:thr2=lx2_4_35_2`, combines
three of the ideas above: adaptive hops chosen by link price plus propagated route cost (`H`);
source detours priced by the marginal-cost toll L²/h with an estimated-dual filter (`slex`),
offered only when the price table puts the detour 20 % below the minimal route (which cuts
needless detours under random permutation and transpose to 0 to 1 %); and the escape-share
throttle (`lx`), with 32 % for sources sending to at most 2 destinations and 35 % otherwise.
Tuned on seeds 1 to 4, evaluated on fresh seeds 11 to 18 (11 to 26 for transpose and hotspot),
1600 cycles, peak over offered 0.8 and 1.0:

| | uniform | transpose | shuffle | bit rev. | bit comp. | hotspot | tornado | neighbour | random perm. |
|---|---|---|---|---|---|---|---|---|---|
| sequential moves: combined | **0.7687** | **0.5971** | **0.6677** | **0.6731** | **0.4783** | **0.5421** | **0.4719** | 1.0 | **0.7102** |
| best other (any of `dor`, `val`, `ugal`, `min`, `minC`, `min/P`, `bandit2m7f5k`, `H`, `P`, `slex10m10`, `dlexm10`) | 0.7575 | 0.5816 | 0.6637 | 0.6673 | 0.4562 | 0.5395 | 0.4584 | 1.0 | 0.7057 |
| no chaining: combined | **0.5871** | **0.4379** | **0.5167** | **0.5145** | **0.3314** | **0.4597** | **0.3294** | 1.0 | **0.5322** |
| best other | 0.5810 | 0.4375 | 0.5100 | 0.5077 | 0.3180 | 0.4525 | 0.3246 | 1.0 | 0.5301 |

It is ahead on eight patterns in each model (by 0.4 to 4.9 %, mostly 5 to 48 standard errors)
and tied on neighbour traffic at the injection limit; hotspot with sequential moves (+0.5 %,
z = 1.4) and transpose without chaining (+0.1 %, z = 1.8) are within noise. It is not ahead of
every configuration built while tuning it: the same parts with a single throttle threshold, or
`min` with the throttle alone, edge it by 0.1 to 0.6 % on uniform, transpose, bit reversal or
random permutation — the throttle's threshold trades uniform against tornado and bit
complement. Safety: the intermediate choice, the minimal hops, the tree escape and bounded
returns are `twoPhaseNet` (`Routing/GraphTwoPhase.lean`); the throttle reads only the configuration
and opens when the network is empty (an instance proof is still to be written); the prices,
learned latencies and the per-source threshold choice are history, outside the
configuration-only selection theorems, as for the bandit.

**History-dependent routing, proved safe.** `Routing/Strategy.lean` closes that gap. A
`Strategy` may keep any state (prices, learned latencies, controller state, recent
destinations) and use a different selection at every step; if every selection it can use
satisfies the existing condition (`EscapeSel`, `SourceSel`, or the weaker `SourceSelOn`), the
network under the strategy is deadlock free (`Strategy.movable`), livelock free
(`Strategy.livelockFree`), delivers under sustained load for runs that are channel fair with
respect to the selection in force (`SelRun.delivered_of_channelFair`) and is starvation free for
strongly fair runs (`SelRun.delivered_of_stronglyFair`; bundled as `Strategy.safe`).
`Routing/StrategyTwoPhase.lean` proves the injection throttles of the simulations on any graph
(`throttleSel_sourceSel`, `throttleSel_sourceSelOn`), and `Examples/Strategy.lean` instantiates
everything on the torus of every size: any history-dependent choice of hop and intermediate
(`torus_choice_safe`, `torus_price_safe`), the escape-share throttle as a configuration-only
selection (`torus_lx_correct`) and with history (`torus_throttle_safe`), and the combined
scheme exactly as `xp_combo.py` runs it, with link prices, tolls, learned latencies, the
snapshot-based throttle mode and the per-source threshold chosen from recent destinations
(`torus_combo_safe`); on the mesh, history-dependent choices within `priorityMesh` and gated
levels (`duatoMesh_strategy_safe`, `duatoMesh_gated_safe`, `duatoMesh_lx_safe`). Still outside:
the no-chaining move model is a different scheduling of the same moves (each cycle is a valid
interleaving, so deadlock and livelock freedom carry over), but the theorems are stated for the
step-by-step semantics; thresholds must stay at most twice the router degree.

**Pushing further (simulation, `scripts/xp_combo2.py`).** *Torus:* choosing each source's
throttle threshold three ways (32 % for sources whose smoothed detour share is at least 1 %,
34 % for concentrated, 36 % for spread-out sources) beats the threshold variants that edged
the combined scheme on uniform, transpose, bit reversal and random permutation, but gives up
1 to 2 % on hotspot and 0.7 % on bit complement: hotspot wants a lower threshold for spread-out
sources and uniform a higher one, and no local signal tried separates the two. *Mesh:* the
best configuration (west-first mesh; a deviation level taking a hop whose next router offers
at least 2 more free usable hops; then straight on; then the XY escape; then any VC1 hop;
within a level the hop into the freest router; `g = 4`) is ahead of every published and own
scheme on uniform, shuffle (+9 to 11 %) and bit reversal (+15 to 17 %) in both move models
(not on random permutation, as first reported: XY on both virtual channels at offered load 1.0,
beyond the first sweep, gives 0.4657 / 0.3605 against 0.4598 / 0.3392), but loses transpose to west-first (−2.4 to −4.6 %) and bit complement to XY on
both virtual channels (−9 to −13 %): bit complement needs packets held on their XY path, and any
adaptive fallback costs it, while transpose needs adaptive west-first hops; every rule tried
moves along that trade-off. It reads only the configuration and is covered by
`westFirstPriorities_correct`.

**Switching modes by learning (simulation, `scripts/xp_portfolio.py`).** A network-wide
learner runs one of several proved modes at a time, measures delivered packets per epoch,
re-probes the others at growing intervals and keeps the best. On the mesh the modes are level
lists of the west-first mesh (the best configuration, west-first with a weak throttle, XY on
both virtual channels — identical to the published `dualXY` — and price-chosen hops), learning
only once the sources saturate (below saturation exploration leaves a backlog that never
drains); on the torus the modes are throttle thresholds of the combined scheme. Switching is
proved safe: `westFirstMesh_modes_safe` (any history-dependent choice among west-first priority level
lists containing the throttled escape level) and `torus_throttle_safe`. The learner ties the
published schemes it contains and beats those it does not (west-first with a weak throttle
alone gives transpose 0.4756, above published west-first at offered 0.6 but about 1 % below it at
offered 1.0, 0.4819), but it loses 0.1 to 4 % to its own
best mode on most patterns (6000 cycles; 0.3 to 0.5 % at 12000 cycles once far-worse modes are
no longer probed): the cost of finding the right mode — exploration, re-probing, and confusing
modes within 1 % of each other under 1 % per-epoch noise — does not vanish at these run lengths.

**Beating XY on both virtual channels (simulation, `scripts/xp_bitcomp.py`).** Under bit
complement the binding links are the X bisection; the links upstream of it are 85 % occupied
and mostly blocked by packets waiting to turn into their column. For XY routing the two lanes
of a link lead to the same next hops, so any lane preference with fallback leaves throughput
exactly unchanged (reproduced bit for bit); only confining some packets to one lane changes
anything. The mode `B:c0=fary+srcwf:fd=5:fs=3` — a packet more than 5 hops from its destination,
or a source more than 3 hops from it, uses only virtual channel 0 while a nearer packet waits
for the same output — beats XY on both virtual channels on bit complement (+0.4 %, z = 2.0,
sequential; +1.7 %, z = 10, no chaining) and random permutation (+3.2 % and +8.4 %), 12 fresh
seeds. It is a level list with the escape level (`duatoPriorities_correct`, `westFirstPriorities_correct`).
Without chaining a lane accepts at most one packet every two cycles, so no minimal scheme can
exceed 0.25 under bit complement; XY on both lanes is at 90 % of that.

With this mode in place of XY in the mode-switching learner (`scripts/xp_portfolio2.py`, modes
on the west-first mesh, 8 to 12 fresh seeds, 6000 and 12000 cycles) the learner is strictly ahead
of every published mesh scheme on six of eight patterns in both move models — uniform +4 to +6 %,
shuffle +14 to +21 %, bit reversal +20 to +23 %, hotspot +3 to +5 %, bit complement +0.8 to
+1.9 %, random permutation +2.7 to +8.3 % — ties tornado up to 0.1 to 0.4 % (every scheme but
O1TURN gives the same throughput there), and loses transpose to west-first random at offered
load 1.0 (−1.2 to −2.3 %; with unthrottled west-first as a mode and 12000 cycles it ties it). It
trails its own best mode by 0.06 to 0.7 % at 12000 cycles; below saturation under hotspot traffic
the gate keeps it in the XY mode, which delivers less than the others at offered 0.4. Switching
is covered by `westFirstMesh_modes_safe`.

**Transpose and tornado (simulation, `scripts/xp_transpose.py`).** Under transpose the two
halves of the traffic use disjoint links and every packet enters one diagonal node; west-first
lets packets heading west and north use only one lane north into the diagonal, so without
chaining no west-first scheme exceeds (10.5 + 14) / 64 ≈ 0.383, and west-first random is at 95 %
of that. The mode `route=wf:levels=all+esc:thr=g0:sel=Pd_balL0` (within the first priority level: the hop
into the router with the most free usable directions, then the dimension with more distance
left, then virtual channel 0 when both lanes are free) fills the under-used lanes into the
corner diagonal nodes and beats west-first random on transpose by 3.2 % (sequential) and 1.5 %
(no chaining), 12 fresh seeds; `westFirstPriorities_correct` covers it. With it in place of the
throttled west-first mode, the learner (`PX:t4:th=0.7:d=2:elim=0.1`, 12000 cycles) is ahead of
every published mesh scheme on seven of eight patterns in both move models (transpose +3.2 % /
+1.4 %) and ties tornado (−0.03 % / −0.4 %). Under tornado every minimal route stays in its row,
so every minimal scheme routes identically and a source threshold `g ≤ 4` never binds (the
north and south lanes stay free); detours lose (Valiant, UGAL, row spreading on the mesh: −2 to
−24 %). A stronger throttle (`g = 6`) binds and gains +1.1 % / +5.1 % by letting source rates
differ (with unequal rates a row carries 3 packets per cycle without chaining, against 8/3 with
equal rates) — throughput bought with unfairness between sources.

**A mesh scheme ahead of every published one on every pattern (simulation).** Adding the
`g = 6` mode to that learner (`PX:t5b:th=0.7:d=2:elim=0.1`: the best configuration, the
transpose mode, the new XY mode, price-chosen hops and the `g = 6` mode, all level lists of the
west-first mesh with the throttled escape level) gives, against every published mesh scheme at its
own peak (12000 cycles, fresh seeds 1401 to 1412; O1TURN was never within 6 % of the best):

| | uniform | transpose | shuffle | bit rev. | hotspot | bit comp. | tornado | random perm. |
|---|---|---|---|---|---|---|---|---|
| sequential: learner | **0.5217** | **0.4972** | **0.6765** | **0.4322** | **0.3931** | **0.3026** | **0.4296** | **0.4783** |
| best published | 0.5037 | 0.4819 | 0.5907 | 0.3626 | 0.3799 | 0.3004 | 0.4269 | 0.4652 |
| lead (z) | +3.6 % (37) | +3.2 % (84) | +14.5 % (102) | +19.2 % | +3.5 % (13) | +0.7 % (7.8) | +0.6 % (16) | +2.8 % (42) |
| no chaining: learner | **0.3836** | **0.3693** | **0.5276** | **0.3218** | **0.3026** | **0.2296** | **0.3315** | **0.3906** |
| best published | 0.3729 | 0.3643 | 0.4363 | 0.2693 | 0.2921 | 0.2254 | 0.3180 | 0.3604 |
| lead (z) | +2.9 % (22) | +1.4 % (37) | +20.9 % (126) | +19.5 % | +3.6 % (14) | +1.8 % (21) | +4.3 % (80) | +8.4 % (56) |

(The best published scheme per pattern is XY on both virtual channels, west-first random, or
Duato's mesh random or throttled.) It is strictly ahead on all eight patterns in both move
models. The `g = 6` mode is used 56 to 88 % of the time under tornado, 5 to 7 % under hotspot,
never otherwise. Per-source fairness (min / mean injection rate, Jain's index) is comparable to
the best published scheme on most patterns; under tornado without chaining it is less even than
XY on both virtual channels at that scheme's own peak (Jain 0.92 against 0.98), though its
worst-served source is not worse off (0.66 against 0.60 of the mean). Safety:
`westFirstMesh_modes_safe` (any history-dependent switching among west-first priority level lists
containing the throttled escape level, `g ≤ 8`).

**Validation (`scripts/xp_validate.py`).** *8 × 8 torus, 10000 cycles:* the combined scheme's
throughputs match the shorter runs within 0.1 % and it is ahead of dimension order, Valiant and
UGAL on eight patterns by 3 to 13 % in both move models (tied on neighbour). *Fairness, 8 × 8:* the
mesh learner is as fair as or fairer than the best published scheme on most patterns; under
tornado a `g = 5` mode in place of `g = 6` keeps the lead (+1.1 %) and is fairer than XY on both
virtual channels with sequential moves, while without chaining no variant is both ahead and at
least as even as XY at its own (sub-saturation) peak unless loads are restricted to equally fair
ones (+1.0 to +1.3 %). *16 × 16 (3 seeds, settings tuned for 8 × 8, as a generalisation test):* the
mesh learner is ahead of every published scheme on transpose, shuffle, bit reversal, tornado and
random permutation (+0.7 to +29 %), ties uniform without chaining, but loses hotspot (−14 to −15 %:
its modes route around the hotspot worse than Duato's fully adaptive channel) and bit complement
(−1.6 to −4.2 %: the XY mode's distance thresholds were tuned for 8 × 8; scaled to the network,
`fd = 10`, `fs = 6`, it edges XY on both lanes in a quick check); its learning epochs are also too
short for 16 × 16 latencies, and at saturation it is less even than published schemes at their
knees. A 16 × 16 torus screen was not conclusive. So the all-pattern results hold at 8 × 8; at
16 × 16 the parameters need to scale with the network size before the claim can be made. A first scaling
(`scripts/xp_scale.py`: Duato's mesh added as a mode — on the west-first mesh, whose second
virtual channel allows every productive hop, it is a level list; the XY mode's thresholds scaled
`fd = 5k/8`, `fs = 3k/8`; learning epochs and settle times scaled with k) keeps the 8 × 8 result
(ahead on all sixteen pattern/model cells, fresh seeds) and at 16 × 16 is ahead on six of eight
patterns in both models, bit complement included (+0.8 % / +1.5 %), but loses hotspot (−2.4 % /
−4.3 %: every mode switch leaves tree saturation for thousands of cycles, so the learner
misjudges the price mode, which alone beats Duato there) and uniform (−2.3 % / −4.2 %: the scaled
gate makes it explore below saturation). At 16 × 16 that version did not yet make the all-pattern claim.

**16 × 16 mesh: ahead of every published scheme on every pattern (simulation,
`scripts/xp_scale2.py`).** The learner `SQX:s6:d=2:elim=0.1:xs=1` keeps the scaled thresholds and
timing, keeps the congestion gate at 0.7, and adds two rules that read only history: if one
destination receives at least 10 % of the injected packets (hotspot; under any permutation the
largest share stays below 0.07 at the benchmark loads) it locks the price mode, and if most
sources send to more than one destination it starts from the best configuration instead of the
XY mode. At 16 × 16 (learner 18000 cycles, published schemes at their own peaks, fresh seeds) it
is ahead on all eight patterns in both move models — uniform +5.1 % / +2.3 %, transpose +2.3 % /
+0.9 %, shuffle +26 % / +30 %, bit reversal +13 % / +21 %, hotspot +5.1 % / +5.0 %, bit complement
+1.1 % / +1.6 % (8 seeds), tornado +6.5 % / +5.9 %, random permutation +18 % / +19 % (z ≥ 10
everywhere) — and at 8 × 8 still on all sixteen cells (smallest lead tornado +0.42 %, z = 7). Its
fairness at the peak is better than XY's under uniform traffic and comparable elsewhere. Caveats:
the two new rules detect traffic signatures rather than learn; one timing fix (`xs=1`) was added
after a first run on the same seeds; the destination lock assumes stationary traffic; the
learner runs 18000 cycles against 6000 for the published schemes; three far-behind published
schemes keep 3 seeds. Safety: every mode is a west-first priority level list with the throttled escape
level and the rules read only deliveries, occupancy and injected destinations, so
`westFirstMesh_modes_safe` covers it.

**16 × 16 torus (simulation, `scripts/xp_torus16.py`).** The combined scheme with its throttle
scaled to the network (ball radius `k/4`, high thresholds `min(8, 2 + k/4)` and `min(8, k/2)`) and a
network-wide learner choosing the concentrated sources' escape-share threshold (32 % or
`28 + k/2` %; at k = 8 both are equal and the scheme is the published 8 × 8 one, bit for bit) is
ahead of dimension order, Valiant and UGAL — each at its own knee — on the eight non-trivial
patterns in both move models: uniform +23 % / +28 %, transpose +8.6 % / +6.2 %, shuffle +56 % /
+48 %, bit reversal +26 % / +28 %, bit complement +24 % / +33 %, hotspot +4.5 % / +6.2 %, tornado
+19 % / +11 %, random permutation +27 % / +31 % (fresh seeds 11 to 14, 3000 cycles, z ≥ 7), and
ties dimension order at the injection limit under neighbour traffic (UGAL and Valiant stay
below it). At 8 × 8 it is ahead on the same eight patterns in both models. Caveats: its peaks are
past saturation where the published schemes peak at their knees, so its injection is less even
on most patterns (bit complement Jain 0.75 against UGAL's 0.997); parameters were chosen on one
seed at the evaluated loads; runs are short. Safety: price and toll choices and throttles with
thresholds up to 8 are covered by `torus_choice_safe`, `torus_combo_safe` and
`torus_throttle_safe`, and for the simulator's own escape by the up*/down* results below.

**The simulated escape, proved.** The torus simulations escape by up*/down* routing over all
links from a central root (BFS levels, the first hop of a shortest legal path), not by the tree
escape of `Routing/Graph.lean`. `Routing/EscapeLayer.lean` abstracts the escape of the detour
network (a next hop, legality, an acyclicity order and a ranking) and re-proves every result of
`GraphTwoPhase.lean`, the throttles and the history-dependent strategies for any escape subnetwork, with
the tree escape as an instance; `Routing/UpDown.lean` builds the up*/down* layer on any finite
connected graph (connectivity up the tree and down, acyclicity of the phased escape dependencies,
any shortest legal next hop including the lowest-port tie-break; `exists_updown_correct`);
`Examples/UpDown.lean` instantiates it on the torus of every size with any root and checks it
against the simulator (up iff lower (level, index); the escape hop is the first hop of a shortest
legal path; the centre root is node 27 at 8 × 8 and 119 at 16 × 16), giving `simUD_twoPhase_correct`,
`simUD_throttle_safe` and `simUD_combo_safe` for exactly the simulated escape.

**The simulators' cycle models and the injection limit, proved.** `Routing/Cycle.lean` defines a
cycle (ejections, hops, injections) in both simulated move models: sequential moves (`seq`) and
no chaining (`none`: simultaneous hops into channels free at the start of the move phase, distinct
sources and targets). Every no-chaining cycle is a sequence of single steps of the step semantics
(moves into channels free at the start commute: `NoChainCycle.path`), so for every network and
strategy covered above, runs of cycles keep legal configurations and the hop bounds, never
deadlock (a work-conserving cycle in a non-empty legal configuration moves a packet), and drain
once injections stop (`cycleSafe`; mesh `westFirstMesh_modes_cycles`, torus `simUD_combo_cycles`).
Delivery while injections continue needs fairness: the step-level theorems apply to sequential
cycles (`seq_delivered_of_*`), and without chaining a cycle-level fairness hypothesis gives
delivery outside the injection channels (`CycleRun.delivered_of_channelFair`). The injection
limit: in either model a channel injects at most once per cycle, so a node injects at most K
packets in K cycles and the network delivers at most (number of nodes) × K
(`sum_count_inject_le`, `throughput_le`, `westFirstMesh_throughput`, `simUD_throughput`), and
the bound is reached (`SatCycle.run`). So under neighbour traffic, where dimension order and our
schemes reach one packet per node per cycle in simulation, no scheme can do better: that tie is
an optimum.

**Fairness on the torus (simulation, `scripts/xp_fairtorus.py`).** Counting each scheme only at
loads where its per-source fairness is at least the best published scheme's at that scheme's
peak, a fair-share admission rule (a source's next packet enters its injection lane only while
its injection count is at most the mean plus a margin; a source well below the mean gets an
unthrottled first hop) keeps the torus scheme ahead on 14 of 16 pattern/model cells at
16 × 16 (+3 to +26 %, with min/mean 0.94 to 0.95 against UGAL's 0.44 to 0.90) but ties transpose
(+0.6 % / −0.7 %), and at 8 × 8 a looser margin is ahead on 14 of 16 cells but loses shuffle
(−3.4 % / −6.9 %); the margins differ by size. So under this stricter fairness-constrained
comparison no single torus scheme is ahead everywhere; the unconstrained comparison above stands.
The admission rule is covered by `simUD_combo_safe` (any injection rule) and the relaxations by
`simUD_throttle_safe`.
