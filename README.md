# async-lean

A Lean 4 / Mathlib library for **proving that an asynchronous design never deadlocks and never
livelocks**. It covers handshake protocols, asynchronous controllers, gate-level circuits and
packet-switched networks with **dynamic (adaptive) routing**. Every result is machine-checked,
with **no `sorry` and no axioms** beyond Lean's three standard ones (`propext`,
`Classical.choice`, `Quot.sound`).

You describe a design as a Lean definition, state the property, and in most cases close the
goal with one tactic. When the design is wrong, the tactic shows you a counterexample and the
exact line that proves the negation.

```lean
theorem handshake_correct : handshake.Correct := by async_decide
```

This README is a guide. It shows how to set up a project, the workflow every proof follows,
one walkthrough per kind of design, how to use a result inside a larger proof, how to prove
statements about whole families of designs, and what to do when something goes wrong. The
reference material (properties, trust, library map, limits) is at the end. For a checked,
read-top-to-bottom version of the same material, see
[`AsyncLean/Tutorial.lean`](AsyncLean/Tutorial.lean).

## Contents

1. [Set up](#1-set-up)
2. [The workflow](#2-the-workflow)
3. [Which model fits my design?](#3-which-model-fits-my-design)
4. [Petri nets: protocols and controllers](#4-petri-nets-protocols-and-controllers)
5. [STGs: from specification to gates](#5-stgs-from-specification-to-gates)
6. [Gate-level circuits](#6-gate-level-circuits)
7. [Networks with dynamic routing](#7-networks-with-dynamic-routing)
8. [Which tactic when?](#8-which-tactic-when)
9. [Using a result in a larger proof](#9-using-a-result-in-a-larger-proof)
10. [Proving a whole family of designs](#10-proving-a-whole-family-of-designs)
11. [Troubleshooting](#11-troubleshooting)
12. [Reference](#12-reference)

## 1. Set up

**Work inside this repository.** Clone it and build it:

```
lake exe cache get   # download prebuilt Mathlib
lake build
```

Then add your own file under `AsyncLean/` and start it with `import AsyncLean`.

**Use it from your own project.** Add the dependency to your `lakefile.toml` and use the same
toolchain (`lean-toolchain`: `leanprover/lean4:v4.34.1`):

```toml
[[require]]
name = "AsyncLean"
git = "https://github.com/KelvinChung2000/async-lean"
rev = "main"
```

Run `lake update AsyncLean`, then `lake exe cache get` (Mathlib comes with it) and
`lake build`. Every file then starts with:

```lean
import AsyncLean
open AsyncLean
```

## 2. The workflow

Every proof follows the same four steps.

1. **Describe the design** as a Lean definition, or import it from a `.g`, PNML or Verilog
   file.
2. **Ask the tool what it thinks**, before writing a theorem: `#eval N.diagnose` for nets,
   STGs and circuits; `#eval N.explain` (or `N.explainWormhole`) for networks.
3. **State the property and close it with a tactic**, usually `async_decide`.
4. **If it fails, read the message.** It names the counterexample and gives the refutation
   theorem. Fix the design, or paste the refutation to prove that the property does not
   hold.

Finish each file with `#assert_standard_axioms`, which makes the build fail if a theorem
depends on `sorry`, `native_decide` or a user-declared axiom:

```lean
#assert_standard_axioms handshake_correct handshake_safe
```

## 3. Which model fits my design?

| You have… | Use | Main goals |
|---|---|---|
| a protocol, arbiter or controller as places and transitions | `PNet` (section 4) | `N.Correct`, `N.Safe`, `N.Bounded k` |
| a signal transition graph (Petrify / Workcraft `.g`) and maybe its gates | `Stg` (section 5) | `spec.model.Correct`, `.CSC`, `.Consistent`, `.OutputPersistent`, `.Conformant gates` |
| a closed gate-level netlist (C-elements, Boolean gates) | `Circuit` (section 6) | `C.Correct`, `C.SpeedIndependent`, `C.QDI` |
| routers, channels and a routing function | `Network` (section 7) | `N.Correct`, `N.StarvationFree`, `N.WormholeCorrect` |
| any other finite system with a computable successor function | `ExplicitLTS` | `E.toLTS.DeadlockFree s₀`, `E.toLTS.LivelockFree internal s₀` |

All of them are given a semantics as a labelled transition system, so the same properties
(section 12) apply to every model.

## 4. Petri nets: protocols and controllers

**Write the net.** A transition lists its input places (`pre`) and output places (`post`), by
index; repeat a place for an arc weight above one. Mark silent steps with
`internal := true`. Livelock means an infinite run of these internal steps.

```lean
/-- A four-phase handshake whose consumer computes internally. -/
def handshake : PNet where
  places := 5
  trans := [
    { name := "req+",    pre := [0], post := [1] },
    { name := "compute", pre := [1], post := [2], internal := true },
    { name := "ack+",    pre := [2], post := [3] },
    { name := "req-",    pre := [3], post := [4] },
    { name := "ack-",    pre := [4], post := [0] }]
  init := [1, 0, 0, 0, 0]
```

**Prove it.** `Correct` is deadlock freedom ∧ livelock freedom ∧ liveness (every transition
can always fire again).

```lean
theorem handshake_correct : handshake.Correct := by async_decide
theorem handshake_safe : handshake.Safe := by async_structural   -- at most one token per place

-- each part on its own
example : handshake.toNet.lts.DeadlockFree handshake.M₀ := by async_decide
-- livelock freedom from every initial marking, without exploring states
example (M₀ : Marking (Fin 5)) : handshake.toNet.lts.LivelockFree handshake.Internal M₀ := by
  async_structural
```

**When it fails.** Here two internal steps can repeat forever:

```lean
def busyWait : PNet where
  places := 2
  trans := [
    { name := "poll",  pre := [0], post := [1], internal := true },
    { name := "retry", pre := [1], post := [0], internal := true }]
  init := [1, 0]

#eval busyWait.diagnose
-- "LIVELOCK: after firing [], the internal transitions [poll(#0), retry(#1)] can repeat forever.
--  Prove it with: PNet.not_livelockFree_of_refute (ts := []) (cyc := [0, 1]) (by decide +kernel)"
```

`async_decide` on `busyWait.Correct` fails with the same message. Paste the suggested line to
prove the negation:

```lean
theorem busyWait_livelocks :
    ¬ busyWait.toNet.lts.LivelockFree busyWait.Internal busyWait.M₀ :=
  PNet.not_livelockFree_of_refute (ts := []) (cyc := [0, 1]) (by decide +kernel)
```

Deadlocks are reported as `DEADLOCK reachable by firing [...]` with
`PNet.not_deadlockFree_of_refute`. A transition that can never fire again is reported as
`NOT LIVE` with `PNet.not_liveLabel_of_refute`.

**From a file.** `pnet_from_pnml arbiter "designs/arbiter.pnml" (internal := ["g1", "g2"])`
defines `arbiter : PNet`. Paths are relative to the Lean file.

**Unbounded nets.** When the state space does not close (a place can grow without bound),
`async_decide` checks the *counter abstraction* instead: every place is tracked exactly up
to a cap `K`, at least every arc weight, and as "`K` or more" above it
(`Checker/Abstract.lean`). The abstraction over-approximates the net, so deadlock freedom
and livelock freedom transfer directly; liveness uses *must*-distances, where every
abstract successor of the chosen step gets closer, so it transfers too (`PNet.of_checkAbs`).
This is sound for every net but can be too coarse; `async_decide (cap := k)` refines it.

```lean
def prodCons : PNet where     -- the buffer (place 1) is unbounded
  places := 3
  trans := [{ name := "produce", pre := [0], post := [0, 1] },
            { name := "consume", pre := [1, 2], post := [2] }]
  init := [1, 0, 1]

theorem prodCons_correct : prodCons.Correct := by async_decide
```

**Large nets.** `async_decide` does not explore every interleaving: it checks a reduced state
space (partial-order reduction), and falls back on the state equation or on symbolic
certificates when that is still too large. Section 8 explains the methods and how far they
go.

## 5. STGs: from specification to gates

An STG is a Petri net whose transitions are signal edges. Read one from a file with
`stg_from_g spec "designs/celement.g"`, or inline:

```lean
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

theorem spec_ok : spec.model.Correct ∧ spec.model.CSC := ⟨by async_decide, by async_decide⟩
```

`Consistent` (edges alternate), `CSC` (complete state coding, which is exactly
implementability) and `OutputPersistent` (an enabled output is never withdrawn) are proved the
same way.

**Check an implementation.** List the gates that drive the non-input signals. Signals are
numbered in declaration order, so here `a = 0`, `b = 1`, `c = 2`. You can also read them from
Verilog with `gates_from_verilog gates "designs/celement.v" for spec`.

```lean
open BExpr in
def celemGates : List Gate := [{ name := "C", out := 2, fn := celem 0 1 2 }]

theorem impl_ok : spec.model.Conformant (spec.gateFn celemGates) := by async_decide
```

*Conformance* means every output edge the gates can produce is allowed by the specification.
By `Stg.implementation_correct`, the closed loop of gates and environment then inherits
deadlock freedom, livelock freedom and liveness, and it is hazard free
(`StgModel.gate_persistent`).

## 6. Gate-level circuits

A `Circuit` is a closed netlist: one gate per signal, with the environment modelled by gates
too. A deadlock is a stable state; a livelock is endless switching of `internal` gates.

```lean
open BExpr in
def cRing : Circuit where
  signals := 5
  gates := [
    { name := "c0", out := 0, fn := celemInv 4 1 0 },
    { name := "c1", out := 1, fn := celemInv 0 2 1, internal := true },
    { name := "c2", out := 2, fn := celemInv 1 3 2, internal := true },
    { name := "c3", out := 3, fn := celemInv 2 4 3, internal := true },
    { name := "c4", out := 4, fn := celemInv 3 0 4 }]
  init := [true, false, false, false, false]

theorem cRing_ok : cRing.Correct ∧ cRing.SpeedIndependent := ⟨by async_decide, by async_decide⟩
theorem cRing_qdi : cRing.QDI := by async_decide
```

* `SpeedIndependent` means hazard freedom under arbitrary gate delays.
* `QDI iso` also puts an independent delay on every wire branch, except on the isochronic
  forks declared in `iso : Forks`: whole signals (`C.QDI [0, 2]`), or groups of branches of a
  signal that share one wire (`C.QDI { groups := [[(1, 0), (2, 0)]] }`, gate `1` and gate
  `2` reading signal `0`). `QDI` with no argument means no isochronic forks.
* `Circuit.speedIndependent_of_qdi` proves that QDI implies speed independence.
* `circuit_from_verilog ring "designs/ring.v"` reads a closed netlist.
* Gates may also switch simultaneously: for a speed-independent circuit the step semantics
  reaches exactly Muller's interleaving states, so correctness is the same in both
  (`Circuit.correct_iff_stepCorrect`). Without speed independence it is not:
  `Examples/Step.lean` shows a race whose simultaneous switch reaches a state no interleaving
  reaches. For Petri nets the two semantics always agree (`Net.stepLts_deadlockFree_iff`, …).

A failing speed-independence check reports the glitching gates and the trace, with
`Circuit.not_speedIndependent_of_refute`.

## 7. Networks with dynamic routing

### Describe the network

A `Network ℕ ℕ` has numbered channels, each holding one packet, and a numeric header, usually
the packet's destination. A virtual channel is a channel of its own. You give three fields:

```lean
open Network

-- A 4-node ring with two virtual channels per link: channels 0..3 are VC0, 4..7 are VC1.
-- A packet switches to VC1 when it crosses the dateline from node 3 to node 0.
def myRing : Network ℕ ℕ where
  arrived c d := (c % 4 + 1) % 4 == d          -- the packet in c has reached destination d
  route c d := let i := (c % 4 + 1) % 4         -- the hops it may take next
    [(if i = 0 then 4 else i + 4 * (c / 4), d)]
  inject := [(0, 2), (1, 3), (2, 0), (3, 1)]    -- the packets the sources may inject
```

* `route c p` lists **every** permitted next hop, as (next channel, new header). For adaptive
  routing, list several. If you use escape channels (Duato's scheme), **list the escape hop
  first**: the tactic then finds it on its own.
* The header can carry routing state, such as a virtual-channel class or a misrouting budget
  that each detour decreases.
* `Examples/Routing.lean` has ready-made encodings for meshes (`Mesh.ch`, `Mesh.head`,
  `Mesh.xy`, `Mesh.productive`) and rings.

### What you can prove

Each result holds for **every work-conserving selection function**, i.e. for every run-time
policy that picks among the permitted hops and never leaves a packet waiting while a
permitted channel is free.

| Goal | Meaning |
|---|---|
| `N.Correct` | `N.DeadlockFree ∧ N.LivelockFree`: whenever the network holds a packet some packet can move, and there is no infinite run without new injections |
| `N.StarvationFree` | along every strongly fair run, every packet is eventually delivered. Strong fairness is demanding here: with finitely many configurations it makes a run of a deadlock- and livelock-free network revisit every reachable configuration, the empty one included, so this is no guarantee for a network kept saturated |
| `N.StarvationFreeUnderLoad sel src` | along every **channel-fair** run (each channel that is offered a way out infinitely often gets its packet out infinitely often), every packet outside `src` is eventually delivered, **with injections never stopping**; channel fairness does not force the network to drain (`Routing/Saturation.lean`) |
| `N.WormholeCorrect` | deadlock and livelock freedom under **wormhole switching** (a packet spans several channels), for packets of every length; also `N.WormholeDeadlockFree`, `N.WormholeLivelockFree` |

### Ask, prove, refute

```lean
#eval myRing.explain
-- "deadlock and livelock free: acyclic channel dependency graph (Dally–Seitz) and a ranking"

theorem myRing_ok   : myRing.Correct         := by async_decide
theorem myRing_fair : myRing.StarvationFree  := by async_decide
theorem myRing_wh   : myRing.WormholeCorrect := by async_decide
```

No configuration of the network is explored. The tactic checks the routing function locally:

* that the channel dependency graph is acyclic (Dally and Seitz);
* or that some escape channels have an acyclic dependency graph, while the other channels
  are used adaptively (Duato);
* and that a ranking such as the distance decreases on every hop.

The kernel then re-checks the certificate.

The same ring with a single virtual channel deadlocks:

```lean
def badRing : Network ℕ ℕ where
  arrived c d := (c + 1) % 4 == d
  route c d := [((c + 1) % 4, d)]
  inject := [(0, 2), (1, 3), (2, 0), (3, 1)]

#eval badRing.explain
-- "DEADLOCK: the channel dependency cycle 0 → 1 → 2 → 3 → 0 can be filled with blocked packets
--  by the run [.inject 1 3, .inject 2 0, .inject 3 1, .inject 0 2].
--  Prove it with: Network.not_deadlockFree_of_refuteB (as := [...]) (by decide +kernel)"

theorem badRing_deadlocks : ¬ badRing.DeadlockFree :=
  Network.not_deadlockFree_of_refuteB (as := [.inject 1 3, .inject 2 0, .inject 3 1, .inject 0 2])
    (by decide +kernel)
```

The tactic reports other failures in the same format:

* **`LIVELOCK`**: a packet can be routed around a cycle forever. Proved with
  `Network.not_livelockFree_of_refuteB (pre := …) (cyc := …)`. The fix is usually a minimal
  route or a misrouting budget in the header.
* **Wormhole counterexamples** use `not_wormholeDeadlockFree_of_refuteB (tail := …)`, which also
  fixes the packet length.
* **`POTENTIAL DEADLOCK`**: there is a dependency cycle, but the checker could not fill it with
  blocked packets. With adaptive routing this need not be a real deadlock. Name escape channels
  explicitly:

```lean
open AsyncLean.Examples Mesh   -- `duatoMesh` and the mesh helpers from `Examples/Routing.lean`

-- store-and-forward: the escape subfunction (here XY routing on virtual channel 0)
example : (duatoMesh 3).DeadlockFree := by
  async_routing (escape := fun c d => [(ch (head 3 c) (xy 3 (head 3 c) d) 0, d)])
-- wormhole switching: the set of escape channels
example : (duatoMesh 3).WormholeDeadlockFree := by
  async_routing (escape := fun c => c % 2 == 0)
```

### How adaptive can routing be?

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

[`Examples/OptimalRouting.lean`](AsyncLean/Examples/OptimalRouting.lean) answers the question
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
for every size ([`Examples/MeshMaximal.lean`](AsyncLean/Examples/MeshMaximal.lean)) follows a
packet that took an extra hop: either it keeps going vertically on virtual channel 0, or it
stops next to a group of 8 or 13 packets that deadlock with it. Eight such groups are checked
by the kernel in a 3 × 3 mesh and carried into the `k × k` mesh by a generic embedding theorem
(`Network.not_deadlockFree_of_runGoodB`, [`Routing/Embed.lean`](AsyncLean/Routing/Embed.lean)).
The north-last mesh is correct for every size as well
([`Examples/MeshNorthLast.lean`](AsyncLean/Examples/MeshNorthLast.lean)); under wormhole
switching Duato's condition fails for it, while it holds for the west-first mesh.

**One yardstick per cost.** "Most adaptive" depends on what you allow; fixing the yardstick by
the cost to minimise gives these results, all for every mesh size
([`Examples/MeshMetrics.lean`](AsyncLean/Examples/MeshMetrics.lean)):

| Cost | Optimum, proved | Reached by |
|---|---|---|
| Hops (zero-load latency) | no routing that moves between neighbours takes fewer hops than the distance (`hops_lower_bound`) | every scheme below takes exactly that many (`family_latency_optimal`) |
| Buffers: 1 virtual channel | maximally adaptive among minimal routing on one virtual channel (`westFirst1_maximal_all`, `northLast1_maximal_all`); XY is not (`xyMesh_not_maximal_all`) | `westFirst1`, `northLast1`, correct also under wormhole switching |
| Buffers: 2 virtual channels | maximally adaptive among minimal routing on two virtual channels | `westFirstMesh`, `northLastMesh` |
| Routing table | at least 4 decisions per inner router for any deadlock-free minimal routing (`table_lower_bound`) | XY: exactly 4 (`xy_table`); turn-model meshes: at most 8 on every size |

No routing function is best for every cost: the table is a set of Pareto points.
[`scripts/validate_routing.py`](scripts/validate_routing.py) replays every deadlock the
maximality proofs build on meshes up to 8 × 8 and re-checks acyclicity, hop counts and table
sizes; it is a cross-check, not part of the proofs.

**More adaptive is not always faster.** In a cycle-level simulation
([`scripts/routing_sim.py`](scripts/routing_sim.py), 8 × 8 mesh, not part of the proofs) the
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

### A selection that performs

Maximal adaptivity says which hops a packet *may* take; throughput under load depends on which
one it *does* take. `tieredMesh` (`Examples/MeshTiered.lean`) offers each packet the free hops
of the first tier that has one: its dimension-order hop (XY on virtual channel 0, YX on virtual
channel 1, so flows in different orders share no channel), then the escape hop, then any hop on
virtual channel 1. It also throttles the sources: a packet leaves its injection channel only
towards a router with at least `g` of its 8 outgoing channels free (channels leaving the mesh count as free). Throttling refuses free
escape hops, so Duato's condition for selections fails; `Network.deadlockFreeWith_of_source`
(`Routing/Source.lean`) proves Duato's theorem for selections that may hold packets back at
their sources as long as a source lets its packet go once the rest of the network is empty.
Duato's mesh, the west-first and the north-last mesh are deadlock, livelock and starvation free
under `tieredMesh` for every size and every `g ≤ 8` (`duatoTiered_correct`,
`westFirstTiered_correct`, `northLastTiered_correct`). Only the throttled escape tier
(`Mesh.escTier`) matters for this: the same holds for **every** tier list containing it,
whatever the other tiers prefer and whatever they read of the network (`duatoTiers_correct`,
`westFirstTiers_correct`, `northLastTiers_correct`), so a new preference costs no new proof.

Peak accepted throughput (packets per node and cycle, the largest over a sweep of offered
loads; `python3 scripts/routing_sim.py --bench` prints the underlying tables):

| 16 × 16 mesh | uniform | transpose | shuffle | bit reversal | hotspot | bit complement | worst / best |
|---|---|---|---|---|---|---|---|
| Duato's mesh, random selection | 0.199 | 0.197 | 0.149 | 0.138 | 0.114 | 0.089 | 0.75 |
| Duato's mesh, random, throttled (`g = 4`) | 0.228 | 0.196 | 0.155 | 0.138 | 0.114 | 0.104 | 0.78 |
| XY on both virtual channels | 0.227 | 0.133 | 0.125 | 0.096 | 0.082 | **0.120** | 0.60 |
| O1TURN | 0.174 | 0.125 | 0.107 | 0.087 | 0.090 | 0.100 | 0.54 |
| west-first mesh, random selection | 0.200 | **0.221** | 0.198 | 0.113 | 0.080 | 0.080 | 0.67 |
| **`tieredMesh`, `g = 4`** | **0.237** | 0.202 | **0.199** | **0.140** | **0.118** | 0.108 | **0.90** |

On 8 × 8 meshes the picture is the same (`tieredMesh` first under uniform, shuffle, bit-reversal
and hotspot traffic, worst case 0.87 of the best against 0.84 for the next scheme); the
west-first mesh with a random selection is 15 % faster under transpose traffic and XY on both
virtual channels 12 % faster under bit-complement traffic. Past saturation `tieredMesh` keeps
its throughput, where Duato's mesh with a random selection loses up to half of it (16 × 16,
uniform: 0.14 at an offered 0.3). On 4 × 4 meshes, which saturate late, the throttling costs it
3 to 5 % against the random selections. No selection among those tried was best on every
pattern: taking the extra hops of the west-first mesh helps transpose traffic and makes hotspot
traffic collapse, and bit-complement traffic favours keeping every packet on its XY path.

**What is left, and why.** `scripts/routing_experiments.py` tries further selections (8 × 8 mesh, peak over a load sweep, mean of 2 seeds):

| 8 × 8 mesh | uniform | transpose | shuffle | bit reversal | hotspot | bit complement |
|---|---|---|---|---|---|---|
| best existing scheme | 0.492 | **0.447** (west-first) | 0.524 | 0.345 | 0.373 | **0.298** (XY on both) |
| `tieredMesh` | 0.506 | 0.399 | 0.527 | 0.374 | **0.386** | 0.265 |
| ... with the west-first hops last | 0.507 | 0.429 | 0.543 | 0.369 | 0.379 | 0.250 |
| global view (least occupied path) | **0.508** | 0.402 | 0.540 | 0.376 | 0.382 | 0.263 |
| sources learning their mode | 0.495 | 0.418 | **0.546** | **0.399** | 0.374 | 0.249 |
| controller switching modes | 0.506 | 0.410 | 0.531 | 0.357 | 0.378 | 0.282 |
| two-phase XY (via a random node) | 0.448 | 0.330 | 0.449 | 0.260 | 0.327 | 0.235 |

Only the global-view row and the west-first row are selections the theorems above cover (they
read nothing but the configuration); learning sources, the mode-switching controller, two-phase
XY, patience and distance rules keep per-packet or global state, which a `Selection` cannot
read. Each of them always admits the free escape hop, so the same argument should apply, but
that is not proved. Seeing the whole network does not help (the global-view row matches `tieredMesh`), so the gaps
are not for lack of information. Under bit-complement traffic every packet crosses both
bisections; XY on both virtual channels pushes about 0.6 packets per cycle through each
bisection channel, which is what a saturated chain of one-packet channels carries in this model
(0.50 to 0.57), so in this model it is at the limit (a simulation measurement and a bisection argument, not a theorem) and can be matched but not beaten, and every deviation
from XY loses there. Transpose traffic needs the deviations and no throttling. Rules that trade
between the two (waiting before deviating, choosing the mode by distance, a controller
switching modes) move along that trade-off without reaching both ends.

## 8. Which tactic when?

| Tactic | What it does | Use it when |
|---|---|---|
| `async_decide` | explores the reachable states (for nets, a reduced state space; for networks, the routing function), builds a certificate, and has the kernel check it; for nets it falls back on the state equation, symbolic certificates or the counter abstraction | the design is concrete: the default choice |
| `async_decide (fuel := n)` | the same, with a larger bound on explored states (default 100 000) | the error says the state space exceeds the fuel |
| `async_decide (cap := k)` | the counter abstraction with cap `k` | an unbounded net whose abstraction is too coarse |
| `async_bdd` | decision diagrams of an inductive invariant and of witness transitions, checked by the kernel without enumerating markings | large safe nets: `Correct` or safety with up to `2⁸⁰` markings |
| `async_structural` | place invariants, linear ranking functions, state-equation (Farkas) and Commoner certificates; no state exploration | safeness and boundedness, deadlock freedom, livelock freedom for every initial marking, liveness of marked graphs and free-choice nets; huge state spaces |
| `async_minimize` / `async_minimize right` | replaces one component of a parallel composition by its minimal quotient, certified | a composition is too large; then finish with `async_decide` |
| `async_routing (escape := …)` | `async_decide` for networks, with the escape channels named | the default choice of escape channels fails |
| the theorems directly | Commoner, Dally–Seitz, Duato, ranking functions, … | a statement for every size `n` (section 10) |

A 20-stage FIFO with over a million states is proved safe and livelock free by
`async_structural` instantly. `async_minimize` is used like this (see
`Examples/Compositional.lean`):

```lean
theorem twoFifos_ok : <deadlock freedom ∧ livelock freedom of the composition> := by
  async_minimize        -- the first FIFO becomes a small quotient
  async_minimize right  -- and so does the second
  async_decide          -- the remaining composition is small
```

### Large state spaces

* **Partial-order reduction.** At each marking `async_decide` fires only the enabled
  transitions of a *stubborn set*, and the kernel checks marking by marking that the sets are
  stubborn. Every reachable deadlock stays reachable (`Net.reachable_red_of_dead`), so the
  reduced state space proves the net deadlock free (`Net.deadlockFree_of_stubborn`). For
  liveness and livelock freedom the sets also satisfy the *cycle proviso* and *visibility*
  conditions (`Net.live_of_stubborn`, `Net.livelockFree_of_stubborn`,
  `PNet.correct_of_checkPORc`). A pipeline, whose stages move independently, needs one
  interleaving per marking (`Examples/Scale.lean`).
* **The state equation.** Every reachable marking satisfies `M = M₀ + C · x`. With bounds on
  the places, a Farkas certificate found by linear programming shows that no solution is
  dead (`Net.deadlockFree_of_stateEq`), with no exploration at all.
* **Symbolic certificates.** For a safe net, `async_bdd` computes, by saturation, decision
  diagrams of the reachable markings (an inductive invariant) and of a witness transition
  enabled at each of them. The kernel checks every diagram by a *joint walk* before and
  after firing each transition, node pair by node pair, and never enumerates the markings
  (`PNet.of_checkBDD`, which also gives safety). Liveness and livelock freedom come from
  *linear potentials*: weights on the places, found by linear programming, that every
  witness (every internal transition) decreases, down to *hubs* from which a trace enables
  each transition. When there are none, the measure is lexicographic: each witness (internal
  transition) decreases a potential, or keeps it and decreases a diagram of distances
  (ranks), which then counts only those steps (`Examples/Symbolic.lean`).
* **Fast kernel checking.** Markings are packed into one number, a field of bits per place,
  and the kernel's inner loops are written with recursors over natural numbers
  (`Checker/Fast.lean`, `PNet.checkFast`); a check costs a few milliseconds per state.

Measured end to end (search and kernel check), each goal in its own file, on one core
(timings vary by about 10–20% from run to run):

| Goal | Method | Time |
|---|---|---|
| 7 philosophers `Correct` (408 states) | partial-order reduction | 0.5 s |
| 20-stage FIFO `Correct` (~10⁶ states) | partial-order reduction | 1.1 s |
| 40-stage FIFO `Correct` (2⁴⁰ states) | partial-order reduction | 4.7 s |
| 20 philosophers `Correct` | partial-order reduction | 4.4 s |
| 12 philosophers deadlock free | state equation (no exploration) | 1.9 s |
| 60-stage FIFO safe | packed place invariants | 4.7 s |
| 60-stage FIFO safe | symbolic certificate | 3.3 s |
| 12 philosophers `Correct` | symbolic certificate | 2.1 s |
| 40-stage FIFO `Correct` | symbolic certificate | 2.5 s |
| 20 philosophers `Correct` | symbolic certificate | 4.2 s |
| 80-stage FIFO `Correct` (2⁸⁰ markings) | symbolic certificate | 11 s |
| 40 philosophers `Correct` | symbolic certificate | 13 s |
| 4 handshakes `Correct` (lexicographic measures) | symbolic certificate | 2.1 s |

## 9. Using a result in a larger proof

The theorems are ordinary Lean facts, so you can project them and feed them to other
results.

```lean
-- the parts of `Correct`: deadlock free, livelock free, live
example : handshake.toNet.lts.LivelockFree handshake.Internal handshake.M₀ :=
  handshake_correct.2.1

-- from "can" to "will": under a strongly fair scheduler every transition fires infinitely often
theorem handshake_fair (r : handshake.toNet.lts.Run handshake.M₀) (hfair : r.StronglyFair)
    (t : Fin handshake.trans.length) : LTS.InfOften (fun n => r.lab n = t) :=
  r.infOften_label_of_live (PNet.reachable_finite_of_bounded handshake_safe) hfair
    (handshake_correct.2.2 t)

-- networks: under any valid policy, every reachable state drains once injection stops
example {sel : Selection ℕ ℕ} (hsel : myRing.ValidSel sel) {f}
    (hf : (myRing.ltsWith sel).Reachable empty f) :
    Relation.ReflTransGen ((myRing.ltsWith sel).IStep Act.IsMove) f empty :=
  myRing_ok.drain hsel hf
```

Other useful bridges:

* `LTS.inevitablyExternal`: in a deadlock-free, livelock-free system every run of internal
  steps reaches an observable action.
* `Stg.implementation_correct`: conformance transfers correctness to the implementation.
* `Network.DeadlockFree.lts`: the whole network never gets stuck.
* `Network.packet_hops_le`: a bound on the number of hops of every packet.
* `myRing_fair _ hsel r hfair n c hc : myRing.Delivered r n c`: the packet in channel `c` at
  time `n` of a fair run is eventually delivered.

## 10. Proving a whole family of designs

Tactics handle one concrete instance at a time. For a statement about every size, use the
theory directly. The recipe is always the same: give the certificate the tactic would have
computed, in closed form, and apply the matching theorem.

| Property | Certificate you provide | Theorem |
|---|---|---|
| marked graph live | every directed circuit carries a token | `MarkedGraph.live_iff_circuitsMarked` |
| free-choice net live (or not) | every siphon contains a marked trap (or one does not) | `Net.live_iff_siphonTrap` |
| bounded / safe | a P-invariant | `Net.IsPInvariant.bound`, `.safe` |
| livelock free | a ranking that internal steps decrease | `LTS.LivelockFree.of_ranking`, `Net.livelockFree_of_linearRanking` |
| deadlock free | an inductive invariant with progress | `LTS.DeadlockFree.of_invariant` |
| network deadlock free | closed legal pairs + a channel order (`wf_of_rank`) | `Network.deadlockFree_of_cdg`, `deadlockFree_of_escape`, `wormholeDeadlockFree_of_escape` |
| network livelock free | a rank decreasing on every hop | `Network.livelockFree_of_ranking`, `wormholeLivelockFree_of_ranking` |
| network starvation free | both of the above + finitely many legal pairs | `Network.starvationFree_of_escape_ranking` |

Worked examples:

* `Examples/MullerRing.lean`: for all `n` and `k`, a Muller ring with `n` stages and `k`
  tokens is live iff `1 ≤ k ≤ n - 1`, and it is always 1-safe.
* `Examples/Routing.lean`: `datelineRing_correct`, `datelineRing_starvationFree` and
  `datelineRing_wormholeCorrect` hold for **every** ring size. One set of lemmas (`dl_closed`,
  `dl_wf`, `dl_rank`) serves all three theorems.

Duato's condition is also **necessary** (`Network.staticDeadlockFree_iff_exists_escape`). If
finitely many channels carry packets, every configuration of legal packets can move iff some
connected escape subfunction has an acyclic dependency graph. So when a proof by escape
channels is impossible, the network really can be blocked.

## 11. Troubleshooting

| Symptom | What to do |
|---|---|
| `…exceeds the fuel` / `no counterexample found within N states` | raise it: `async_decide (fuel := 1000000)`, or switch to `async_structural`, `async_minimize` or the theory |
| the kernel check is slow | explicit checking costs a few milliseconds per reachable (or reduced) state; for a large safe net try `async_bdd`, and for deadlock freedom `async_structural`. Add `set_option maxHeartbeats 0 in` before the theorem if Lean times out |
| `the goal must be stated for the design's own initial state and internal predicate` | state the goal with `N.M₀` and `N.Internal` (or `C.s₀`, `C.Internal`), or use `N.Correct`; for other initial states use the theory |
| `unsupported goal` | the tactic recognises the goals listed in sections 4–7; unfold your own definitions first, or split a conjunction with `⟨by async_decide, by async_decide⟩` |
| `POTENTIAL DEADLOCK` for a network | list the escape hop first in `route`, or name escape channels with `async_routing (escape := …)` |
| `ill-formed` net or circuit | `init` needs one entry per place or signal, and every arc must refer to an existing place |
| an edited `.g`, `.pnml` or `.v` file has no effect | declare the design directory as an `input_dir` needed by the library that imports it (see `Import/Basic.lean` and this repository's `lakefile.toml`); otherwise rebuild the Lean file that imports it |
| you want to see an imported design | `#print arbiter`: it is an ordinary definition |

## 12. Reference

### The properties

All of these are defined once, for labelled transition systems
(`AsyncLean/LTS/Properties.lean`), and transported to every model:

| Property | Definition |
|---|---|
| `DeadlockFree s₀` | no reachable state is without an outgoing step |
| `LivelockFree internal s₀` | no reachable state starts an *infinite run of internal (silent) steps*, so the system can't chatter forever without observable progress |
| `Live s₀` | every action can always eventually happen again (no partial deadlock or starvation; Petri-net L4-liveness) |
| `Persistent s₀` | an enabled action is never disabled by another one (semi-modularity, i.e. speed independence / hazard freedom for circuits) |

`PNet.Correct`, `StgModel.Correct` and `Circuit.Correct` bundle deadlock freedom, livelock
freedom and liveness. `PNet.Bounded k` and `PNet.Safe` bound the number of tokens per place.
The network properties are listed in section 7.

### Why the results can be trusted

* **No `sorry`, no `axiom`, no `native_decide`.** `AsyncLean/Audit.lean` and every example
  run `#assert_standard_axioms`, which makes the build fail if a result depends on anything
  other than `propext`, `Classical.choice` and `Quot.sound`. That rules out `sorryAx` and
  `Lean.ofReduceBool`.
* **Untrusted search, trusted check.** Exploring states, computing rankings, distances,
  quotients, dependency orders and linear-programming solutions is ordinary unverified code
  run at elaboration time. Only the checkers are trusted, and their soundness is proved
  (`of_checkCert`, `correct_of_checkPacked`, `divBisim_of_checkQuot`,
  `Network.correct_of_checkCert`, `Network.wormholeCorrect_of_wcheckCert`, …). A buggy search
  can only make a check *fail*.
* **The checked model is the specified model.** `PNet.bisim`, `Circuit.bisim` and
  `Stg.bisim` prove the executable semantics bisimilar to the abstract ones, and the
  bisimulation theorems transfer every property. So conclusions are about the abstract
  `Net`, `StgModel` and `Circuit` semantics. Network theorems are stated directly about the
  abstract `Network` semantics.
* **Importers are outside the trusted base too.** An imported design is an ordinary Lean
  definition; the theorems are about that definition.

### Library map

| File | Contents |
|---|---|
| `Tutorial.lean` | a checked walkthrough of the library |
| `LTS/Basic.lean` | transition systems, reachability, traces |
| `LTS/Properties.lean` | deadlock, livelock, liveness, persistence; proof and refutation rules; progress theorem; transfer along bisimulations |
| `LTS/Compose.lean` | parallel composition, hiding, divergence-preserving weak bisimulation |
| `LTS/Fairness.lean` | infinite runs, strong fairness, "will happen" theorems |
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
| `Routing/Basic.lean` | networks with dynamic routing, selection functions, Duato's theorem (sufficient and necessary), Dally–Seitz, livelock by ranking, drain theorem, refutations |
| `Routing/Fairness.lean` | starvation freedom: every packet is delivered along every strongly fair run |
| `Routing/Wormhole.lean` | wormhole switching, Duato's extended dependency graph, livelock, drain, refutations |
| `Routing/Check.lean`, `Routing/WormholeCheck.lean` | trusted routing checkers, untrusted certificate search and diagnosis |
| `Routing/Optimal.lean` | comparing routing functions by adaptivity, maximally adaptive routing, refutations for intervals of routing functions |
| `Routing/Embed.lean` | carrying a deadlock of a small network into every network that contains a copy of it |
| `Routing/Source.lean` | Duato's theorem and starvation freedom for selections that throttle the sources; tiered selections |
| `Routing/Reduce.lean` | reducing one routing function to another: acyclic channel dependencies transfer along a map of channels |
| `Routing/Graph.lean` | safe adaptive routing on every finite connected graph: minimal adaptive routing with a spanning-tree escape |
| `Routing/GraphBudget.lean` | routing on every graph with bounded returns from the escape layer: a packet may leave the escape layer `B` times |
| `Routing/Saturation.lean` | delivery under sustained load: channel fairness, Duato's theorem for liveness with injections never stopping |
| `Checker/Explicit.lean` | the **trusted checker** and its soundness proofs; certificates; counterexample traces |
| `Checker/BTree.lean`, `Invariant.lean`, `Packed.lean`, `Quotient.lean` | search trees, invariant certificates, bit-packed safe nets, quotient certificates |
| `Checker/Petri.lean` | concrete nets `PNet`, executable semantics, bisimilarity with the abstract net |
| `Checker/Abstract.lean` | checking through finite over-approximations; the counter abstraction of unbounded nets |
| `Checker/Diagnose.lean`, `Minimize.lean` | untrusted counterexample search, certificate and quotient computation |
| `Checker/Fast.lean`, `FastPetri.lean` | the fast kernel checker on numeric states, and its instance for nets packed into bit fields |
| `Checker/FastPOR.lean`, `FastPORLive.lean` | kernel checks of reduced state spaces |
| `Checker/BDD.lean`, `BDDGen.lean` | symbolic certificates: decision diagrams checked by joint walks; their untrusted computation |
| `Checker/Tactic.lean` | the `async_decide`, `async_bdd`, `async_routing` and `async_minimize` tactics |
| `Auto/Simplex.lean`, `Auto/Structural.lean`, `Auto/StateEq.lean` | exact rational simplex (untrusted), `async_structural`, state-equation certificates and packed place-invariant bounds |
| `Import/G.lean`, `Pnml.lean`, `Verilog.lean` | importers: `stg_from_g`, `pnet_from_pnml`, `gates_from_verilog`, `circuit_from_verilog` |
| `AxiomAudit.lean`, `Audit.lean` | `#assert_standard_axioms` and the library-wide audit |
| `Examples/` | Muller rings, arbiter, dining philosophers, counterexamples, circuits, STG implementation, composition, imported designs, structural proofs, fairness, free choice, QDI, concurrent firing, unbounded nets, scale, symbolic certificates, routing, maximally adaptive routing (on every mesh size), optimal routing per cost, a tiered source-throttled selection, safe routing on the torus and the Petersen graph |

### Scope and limits

* Semantics are interleaving: one transition, or one gate, at a time. The step semantics
  (concurrent firing) agrees with it for every Petri net and every speed-independent circuit
  (section 6).
* Liveness is L4-liveness. Fairness-based "will happen" properties are derived from it in
  `LTS/Fairness.lean`. Livelock is divergence: an infinite run of internal actions.
* Deciding these properties is hard in general, and no tool avoids that: the siphon–trap
  property is co-NP-complete, and reachability questions for unbounded Petri nets are
  decidable only with non-elementary worst-case cost. `async_structural` checks the
  siphon–trap property from a branching certificate and falls back on model checking when the
  certificate would be too large. The counter abstraction of unbounded nets is sound but
  incomplete, refined by raising the cap.
* Reduction helps most when concurrency is loosely coupled. When the stubborn sets must be
  large (tightly synchronised designs, or many internal transitions next to external ones),
  the reduced state space approaches the full one; for safe nets `async_decide` then turns to
  symbolic certificates. These cost about a millisecond of kernel time per pair of diagram
  nodes walked (a few hundred to a few thousand pairs on the families of section 8), and
  their untrusted search takes a few seconds at most. Liveness and livelock freedom are
  cheapest when linear potentials exist; the diagrams of a lexicographic measure stay
  polynomial on the handshakes of `Examples/Symbolic.lean`, but grow with the number of
  steps keeping the potential that can be pending at once.
* Networks are modelled with store-and-forward / virtual cut-through switching (one channel
  per packet) or wormhole switching (a packet spans up to `tail p + 1` channels, with one-flit
  channel buffers). Routing livelock freedom is "no infinite run without injections".
  Starvation freedom assumes a strongly fair scheduler and is proved for store-and-forward
  switching. Duato's condition is proved necessary and sufficient for store-and-forward
  switching; for wormhole switching the sufficient direction is proved.
* `MaximallyAdaptive` is relative to the hops `U` you allow and compares routing functions
  only at the pairs a packet can occupy. The turn-model meshes are proved maximal for every
  size for minimal routing on one and on two virtual channels; allowing detours or more
  virtual channels changes the yardstick, and the maximal routing functions with it. The
  per-cost optimality results are about hop counts, virtual channels and the number of routing
  decisions; throughput and latency under load are not theorems, and the simulation results
  above are measurements. For `tieredMesh` what is proved is safety (deadlock, livelock and
  starvation freedom), not its speed.

### Building the documentation

API documentation is built with doc-gen4 (`.github/workflows/docs.yml` publishes it to
GitHub Pages):

```
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
lake build AsyncLean:docs      # output in docbuild/.lake/build/doc
```

Toolchain: Lean 4.34.1, Mathlib v4.34.1. See [CHANGELOG.md](CHANGELOG.md) for the history.
