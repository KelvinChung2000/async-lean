# How adaptive can routing be, and which selection performs?

[← back to the README](../README.md) · [all guides](README.md)

This guide continues section 7 of the README. It covers two questions about deadlock-free
routing on meshes: how many hops a routing function can permit (maximal adaptivity, proved for
every mesh size) and which run-time selection among those hops gives the best throughput
(simulation). Everything marked *simulation* is a measurement from the scripts in
[`scripts/`](../scripts/README.md), not a theorem.

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
