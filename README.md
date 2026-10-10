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
(0.50 to 0.57), so in this model it is at the limit (a simulation measurement; in the fluid model the bisection bound 4/k is a theorem for every even k, `bitcomp_opt`) and can be matched but not beaten, and every deviation
from XY loses there. Transpose traffic needs the deviations and no throttling. Rules that trade
between the two (waiting before deviating, choosing the mode by distance, a controller
switching modes) move along that trade-off without reaching both ends.

### Beyond the mesh

`Routing/Graph.lean` makes minimal adaptive routing safe on **every finite connected graph**:
virtual channel 1 takes any shortest-path hop, virtual channel 0 routes along a spanning tree
(`GraphData.correct`, `exists_correct`; the torus of every size and the Petersen graph as
instances). With an absorbing escape a packet that enters virtual channel 0 stays there; in
simulation that costs up to 45 % of the throughput, and unbounded returns to virtual channel 1
can livelock (a packet took 95 hops on a 14-hop route). `Routing/GraphBudget.lean` lets a
packet return `B` times, counted in its header, and is safe for every graph and every `B`
(`budget_correct`). Two returns keep 96 to 100 % of the unbounded throughput, with at most 26
hops.

Is the mesh the right topology? At the same router radix (4 ports) and two virtual channels,
`scripts/routing_graph_sim.py` (peak throughput, mean of 2 seeds; spanning-tree escape rooted
in the centre, `B = 2`, tiered selection, `g = 4`) and the exact LP of the fluid model give:

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

The wire ceiling is a theorem (`Flow/Fluid.lean`, `Flow/MeshWire.lean`, fluid model, uniform
traffic, every k): for every network on the k × k grid with links of capacity at most 2 and wire
lengths at least the Manhattan length — any topology, any radix, any routing —
`θ ≤ 6 · wire / k³` (`throughput_le_wire`); the mesh's optimum is exactly `8(k² − 1)/k³` for
even k (`mesh_opt`: an XY flow reaches it for every k, the cut through the middle bounds every
routing); so no network with the mesh's wire beats it by more than `3k / (2(k + 1)) < 3/2`
(`wire_ceiling`; 4/3 on the 8 × 8 grid, `wire_ceiling_eight`). Both bounds come from one weak
duality argument, `Fluid.potential_bound`.

**Routing on the mesh has no room left (fluid model, proved).** In the fluid model routing is a
choice of flow, so the optimum below bounds every routing — oblivious, adaptive, with detours,
with global knowledge — and a minimal flow (`Flow.Minimal`: every hop gets closer) reaching it
shows that detours add nothing:

| traffic | optimum (per source) | reached without detours | theorem |
|---|---|---|---|
| uniform, every k ≥ 2 | 8(k² − 1)/k³ (even k), 8/k (odd k) | yes, XY | `uniform_minimal_opt`, `mesh_opt_all` |
| bit complement, every even k | 4/k | yes, XY or O1TURN | `bitcomp_opt`, `bitcomp_minimal` |
| transpose, 8 × 8 | 10/11 | yes | `transpose8_opt`, `transpose8_minimal` |
| shuffle, 8 × 8 | 1 | yes | `shuffle8_opt`, `shuffle8_minimal` |
| bit reversal, 8 × 8 | 20/21 | yes | `bitrev8_opt`, `bitrev8_minimal` |
| hotspot, 8 × 8 | 40/67 (the hotspot's four input links) | no: minimal flows reach 840/1471, 4.5 % less | `hotspot8_opt`, `hotspot8_minimal_opt` |
| worst case over admissible traffic, every even k | 4/k | yes, O1TURN (XY: 2/(k − 1), `xy_worst_opt`) | `worst_opt`, `o1turn_admissible` |

Admissible traffic (`Admissible`) is every matrix in which no node sends or receives more than 1,
permutations included: O1TURN routes all of them at 4/k without detours, and the bit complement
shows no routing does better (`Flow/MeshWorst.lean`). The 8 × 8 rows are exact LP solutions
(`scripts/fluid_certificates.py`) checked by the kernel: a flow at the optimum, and link lengths
whose potential bound (`Flow.potential_bound_on` for the minimal-only hotspot bound) matches it
(`Flow/Certificate.lean`, `Flow/MeshPatterns.lean`). What remains between these optima and the
simulated throughput (35 to 60 %) is flow control, not routing.

**Other topologies: when detours help is a property of the topology and the traffic together.**
The bounds above hold on every network; what is special about the mesh is that minimal routing
already meets them. In general (`Flow/Tree.lean`, `Flow/Symmetric.lean`, `Flow/Valiant.lean`,
`Flow/GraphPatterns.lean`):

* **For every traffic matrix: only trees.** On a connected network, minimal routing reaches the
  optimum for every traffic matrix iff the network is a tree (`minimal_optimal_iff_isTree`): on a
  tree every link is a cut that the unique route crosses; on any edge of a cycle, traffic between
  its ends gets twice as much with the detour (`detour_helps`). So a topology class without
  detours has to be stated for a traffic class.
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
  detours, below the worst-case optimum 1 (`torusTornado_minimal_opt`).

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

**Flow control at equal storage (simulation).** The gap between these fluid optima and the
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

**Detours on the torus with packets (simulation).** `scripts/torus_experiments.py`, 8 × 8
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
the source pick a detour by congestion recovers tornado to within 1 % of Valiant (`ringvd30`)
at a cost of about 1 % on bit complement and neighbour traffic, or keeps every pattern but
tornado and neighbour at or above the existing schemes (`ringvx10`). No variant tried is at least as good as every
existing scheme on every pattern: the detours that tornado needs cost a little where none are
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
routing. Closing it needs a signal about the cost a detour imposes on others; none was found,
and no impossibility is proved (in the fluid model an adaptive routing can reach every
pattern's optimum).

**A torus scheme ahead of every existing one on every pattern (simulation).** Three local
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
dimension order, on neighbour traffic. It is a selection of `detourNet` (`Routing/GraphDetour.lean`):
the source picks an intermediate (none, a node on the long way round, or a random node) from
`anyDetour`, adaptive hops are minimal towards it, the escape is the spanning tree, returns are
bounded (`B = 2`) and injection is throttled — so it is deadlock free, livelock free, starvation
free and delivers under sustained load (`torus_valiant_correct`, `detour_underLoad_of_sourceSel`).
The margins on bit complement and tornado are a few standard errors of the simulation; they
are measurements, not theorems, and our own unthrottled-detour `GraphData.net` is still slightly
ahead of it on transpose, shuffle, bit reversal and random permutation.
Lower exploration (0 to 1 %), margins a detour must beat the minimal route by (5 to 25 %),
and a larger margin for the random intermediate do not close that last gap (at best 0.568 /
0.651 / 0.656 / 0.679 against 0.570 / 0.652 / 0.658 / 0.684) without giving up tornado: under
those permutations the learning sources still send 2 to 4 % of packets on detours, about the
1 % of throughput that minimal routing keeps. Being ahead of the existing schemes and also of
our own minimal network on every pattern remains open. Picking, among the free minimal hops,
the one into the router with the most free channels (`C`) helps the minimal network a little
(transpose 0.573, bit reversal 0.660, random permutation 0.686) and the detour scheme on bit
complement and tornado (0.454, 0.445), but not enough on shuffle, bit reversal, hotspot and
random permutation; dropping the random intermediate (`Y`) keeps the permutations at the
minimal network's level but loses tornado (0.400) and bit complement (0.444).

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

These detour schemes are safe on every graph: `Routing/GraphDetour.lean` adds to the header
`(d, b)` of `GraphBudget` an intermediate node `w` chosen at the source from any list `W s d`
(Valiant, the long way round a ring, or none); adaptive hops head for `w` and drop it on
arrival, the escape heads for `d` and drops it. For every finite connected graph, every budget
and every `W` the network is deadlock free, livelock free (at most `dist s w + (B + 1) ·
rankBound` hops), starvation free and delivers under sustained load (`detour_correct`,
`detour_underLoad`, `detour_hops_le_some`; torus instances in `Examples/GraphDetour.lean`), and
with `w = none` it is exactly `GraphBudget`'s network (`detourNet_route_none`). Since the source
may pick any element of `W s d`, the congestion-based choices of `ringvx` and `ringvd` are
covered.

### Scaling with the connections

How should a router use more connections — two or four physical links where there was one?
The fluid model answers exactly (`Flow/Scaling.lean`, over ℚ, every network):

* **No routing grows faster than linearly.** Throughput is homogeneous in the capacities: with
  `m` connections in place of each one (`Net.copies`), a traffic matrix is routable at `θ` iff
  it is routable at `θ / m` on one connection (`copies_routable_iff`). The best throughput of
  `m` connections is exactly `m` times that of one, for a single matrix (`opt_copies`) and for
  the worst case over any class of matrices (`worstOpt_copies`).
* **Lanes reach it.** Treat the `m` connections of every link as `m` lanes, each a full copy of
  the network; a packet picks a lane at its source and stays on it, and inside its lane uses
  the best scheme for one connection. The lanes' flows add (`Routable.copies`), so this simple
  scheme is optimal on `m` connections: nothing that mixes lanes, adapts across them or detours
  through them does better.
* **Unequal connections.** Split the connections into layers `N i` (a mesh plus a layer of
  express links, say) and send the fraction `θ i / ∑ θ` of every demand into layer `i`, where
  `θ i` is what the layer routes on its own: the network routes at `∑ θ i`
  (`layered_routable`; the optimum is superadditive, `opt_superadditive`).

With `m` connections per link the best worst case over admissible traffic is exactly
`m · 4/k` on the `k × k` mesh (`mesh_copies_worst`), `m · 8/k` on the torus
(`torus_copies_worst`; `m` on the 8 × 8 torus, `torus_eight_copies_worst`) and `2m` on the
hypercube (`cube_copies_worst`), reached by Valiant's routing in every lane; uniform traffic
gets `m` times `mesh_opt_all`, `torus_uniform_opt` and `cube_uniform_opt`.

**The lane network, proved safe for every number of lanes** (`Routing/Lanes.lean`).
`Network.lanes ls N` puts the networks `N i` side by side: channels `(i, c)`, a packet routed by
`N i` and kept in lane `i`, every source free to inject into any lane (round robin, hashing, the
least loaded lane). Each lane keeps its own two virtual channels; none is added. The library's
safety proofs all follow one recipe — a closed legal set, a connected escape with a
well-founded dependency graph, a ranking — which `Network.SafeCert` packages, and
`SafeCert.lanes` lifts it to the lane network: dependencies never cross lanes, so the escape
dependency graph is a disjoint union of well-founded ones. Hence:

* `Network.lanes_correct`, `lanes_underLoad` : deadlock and livelock free under every valid
  selection (which may compare lanes), starvation free under strong fairness, and every packet
  delivered under saturation along every channel-fair run;
* `GraphData.lanes_correct`, `lanes_budget_correct`, `lanes_detour_correct`,
  `lanes_detour_sourceSel` : on every finite connected graph, any number of lanes of the
  minimal adaptive, bounded-return or detour network, with a different spanning tree and detour
  rule per lane if wished, throttled sources included; `Examples/Lanes.lean` : the torus of every
  size with `m` lanes of the detour network behind `bandit2m7f5k` (`torusLanes_correct`,
  `torusLanes_sourceSel`).

The lanes do not interfere, so the packet network keeps the linear scaling:
`lanes_reachable_iff` (the reachable configurations are exactly the tuples of reachable
configurations of the lanes), `lanes_path` (runs of the lanes, one per lane, are together one
run of the lane network: no lane blocks another) and `copies_path` (any run of one network, run
in `m` lanes at once, delivers `m` times its packets).

**Sharing the connections, proved safe too.** Lanes are the scheme whose scaling is a theorem;
with packets, letting a packet use the free channels of other lanes does better (below). Two
ways of sharing are proved safe on every graph for every number of connections:

* `Routing/SharedLanes.lean` : `GraphData.sharedNet` keeps each packet's escape on its own
  lane's spanning tree and lets its adaptive hops use the adaptive channel of every lane
  (`shared_correct`, `shared_sourceSel`); every hop of the lanes is still allowed
  (`lanes_route_sub`). The escape dependencies land on escape channels and stay in one lane.
* `Routing/Widen.lean` : **widening.** `Network.widen` replaces every channel of *any* network
  by any number of copies and lets a packet take any copy of any permitted hop, the escape
  included. An escape dependency between copies is one between the channels they copy, so
  `SafeCert.widen` lifts every certificate of the library (`widen_correct`,
  `widen_sourceSel`; on every graph `GraphData.wide_correct`, `wide_detour_correct`). With one
  escape channel, `2m - 1` adaptive channels and `m` injection channels
  (`GraphData.sharedSlots`, `shared_slots_correct`; the torus `torusWide_correct`) this is the
  `shared` scheme of the simulation.

**Scaling with packets (simulation).** `scripts/lane_scaling.py`, 8 × 8 torus, `m` connections
per link, each with two one-packet virtual channels, `m` injection channels per node, offered
load up to `m` packets per node per cycle; the mechanics and selection of
`scripts/routing_graph_sim.py` (up*/down* escape, tiered selection, `B = 2`, throttle `g = 4`).
Peak accepted throughput **per node and per connection** (mean of 2 seeds; constant means
linear scaling):

| scheme | m | uniform | transpose | shuffle | bit rev. | hotspot | bit comp. | random perm. |
|---|---|---|---|---|---|---|---|---|
| one connection (`GraphData.net`) | 1 | 0.753 | 0.570 | 0.652 | 0.659 | 0.525 | 0.444 | 0.685 |
| lanes (`Network.lanes`) | 2 | 0.755 | 0.569 | 0.653 | 0.660 | 0.521 | 0.445 | 0.683 |
| lanes | 4 | 0.759 | 0.570 | 0.655 | 0.661 | 0.523 | 0.443 | 0.684 |
| lanes, a spanning tree per lane | 4 | 0.759 | 0.579 | 0.663 | 0.662 | 0.494 | 0.442 | 0.670 |
| shared lanes (`GraphData.sharedNet`) | 2 | 0.822 | 0.606 | 0.695 | 0.715 | 0.543 | 0.503 | 0.735 |
| shared lanes | 4 | 0.877 | 0.632 | 0.726 | 0.757 | 0.549 | 0.544 | 0.774 |
| shared lanes, a spanning tree per lane | 4 | 0.879 | 0.649 | 0.746 | 0.768 | 0.547 | 0.548 | 0.774 |
| widened: 1 escape + `2m − 1` adaptive (`sharedSlots`) | 2 | 0.900 | 0.668 | 0.768 | 0.805 | 0.552 | 0.633 | 0.823 |
| widened | 4 | **0.939** | **0.690** | **0.804** | **0.835** | **0.554** | **0.723** | **0.867** |

Lanes scale exactly linearly, as the independence theorems say: the throughput per connection
stays within 0.006 of one connection's on every pattern. Sharing does better than linearly
relative to one connection with packets, because a packet blocked in its own lane can take a
free channel of another: shared lanes gain 5 to 23 % per connection at `m = 4`, and widening,
which spends only one virtual channel per link on the escape and the rest on adaptive hops,
gains 6 to 63 % (bit complement 0.723 against 0.443; uniform 0.939, near the injection limit of
1). That is not a contradiction of `opt_copies`: one connection with packets reaches only part
of its fluid optimum (flow control), and more channels recover some of it; no scheme can exceed
`m` times the fluid optimum of one connection. Hotspot traffic is limited by the links into the
hotspot and scales linearly under every scheme. A spanning tree per lane changes little.

On the 8 × 8 mesh (`--topology mesh` with the up*/down* escape, `mesh_xy` with XY), one seed,
the same holds: lanes stay within 0.01 of one connection per connection (uniform 0.453 / 0.495,
bit complement 0.187 / 0.248 for `m = 1`), widening reaches 0.643 / 0.644 uniform and 0.350 /
0.352 bit complement per connection at `m = 4`.

### Reaching the fluid optimum: backpressure

With packets, one connection reaches only part of its fluid optimum: on the 8 × 8 mesh under
uniform traffic the optimum is `63/64 ≈ 0.98` packets per node per cycle (`mesh_opt`) and the
schemes above reach 0.45 to 0.64. The gap is flow control, not routing (on bit complement XY
already reaches 99 % of its bisection bound). `Flow/Backpressure.lean` proves that one scheduler
closes it completely, in a queueing model of the fluid network:

* **The model** (`Fluid.Run`): discrete slots; every vertex keeps a backlog per destination; a
  scheduler offers every commodity a rate on every link within the capacities, a vertex sends
  at most its backlog, traffic arrives at the sources. Quantities are rational (the traffic is as
  divisible as the fluid's); buffers are unbounded.
* **Backpressure** (`Run.Backpressure`): max-weight rates (maximise
  `∑ rate × backlog difference`) and work-conserving sends. Giving every link, in full, to a
  destination of largest backlog difference across it is such a scheduler (`bpRates_maxWeight`);
  for every arrival sequence it yields a run (`Run.ofArrivals`).
* **Stable below the optimum** (`Run.backpressure_optimal`): if `dem` is routable at `θ`, every
  load `ρ · dem` with `ρ < θ` keeps the backlog bounded and is delivered in full, up to a
  constant. The proof is the quadratic drift bound (`Run.drift`): the energy `∑ Q²` falls by
  `2 ε` times the backlog, up to a constant, because the max-weight rates beat any flow of the
  traffic. The scheduler knows nothing of `dem`, `θ` or the flow.
* **No scheduler above it** (`Run.potential_ceiling`, `cut_ceiling`, `hop_ceiling`): the traffic
  a run carries in `T` slots is a flow in `T` copies of the network (`Run.totalFlow`), so a run
  with a bounded backlog respects every bound of the fluid model.
* **With `m` connections per link**: `mesh_backpressure`, `torus_backpressure`,
  `cube_backpressure`: under uniform traffic backpressure is stable at every load below `m` times
  the fluid optimum of one connection, and no scheduler is stable above it; on the mesh such a
  stable run exists for every load (`mesh_backpressure_exists`). So the throughput of
  backpressure is exactly the fluid optimum, and it scales exactly linearly with the connections.

**With integer packets (simulation).** `scripts/backpressure_sim.py`: integer packets, a queue
per destination at every node, every link carrying `2m` packets per slot to a destination of
largest backlog difference, Poisson arrivals, 40 000 slots. Offered and accepted load per node
per connection, as a fraction of the fluid optimum, and the mean delay (Little's law):

| network | `m` | 0.50 | 0.90 | 0.95 | 0.98 | 0.99 | 1.01 | 1.05 | delay at 0.95 |
|---|---|---|---|---|---|---|---|---|---|
| mesh, optimum 0.984 | 1 | 0.500 | 0.894 | 0.950 | 0.980 | 0.990 | 1.004 | 1.016 | 662 |
| mesh | 4 | 0.500 | 0.902 | 0.950 | 0.980 | 0.990 | 1.004 | 1.016 | 723 |
| torus, optimum 1.969 | 1 | 0.499 | 0.899 | 0.950 | 0.980 | 0.990 | 1.002 | 1.007 | 271 |
| torus | 4 | 0.500 | 0.899 | 0.950 | 0.980 | 0.990 | 1.002 | 1.007 | 302 |

Every load up to 99 % of the optimum is accepted, to within 1 % (sampling noise), for every `m`: on the mesh 0.975
packets per node per connection against 0.453 (lanes) and 0.643 (widening), linearly in `m`.
Above the optimum the backlog grows without bound (and the accepted mix stops being uniform,
which is why it can exceed the uniform optimum slightly). The price is the storage and the delay:
about 600 packets queued per node per connection on the mesh (some 10 per destination) and
delays of 650 slots, where the packet networks above keep two one-packet buffers per link and
deliver in tens of cycles; and backpressure's nodes inject and eject without limit (the packet
networks above inject at most one packet per node per cycle and connection, which caps the torus
at 1, half its optimum). The proved guarantees of the packet networks above (deadlock freedom
with finite buffers) and the throughput of backpressure are not yet one network.

**How much buffer.** Backpressure needs room for backlog differences, and in the queueing model
that room is finite: started empty, a backpressure run whose load stays `ε` below a routable
traffic never holds more than `driftConst / (2 ε) + ε` in any per-destination queue
(`Run.backpressure_fitsIn`), so buffers of that size are never exceeded and the run is exactly
the finite-buffer one. On the mesh with `m` connections at `(1 − δ)` times the optimum this is
`145 m k⁷ / (16 δ) + m` packets per destination (`mesh_buffer`): linear in `m` and in `1 / δ`,
with the loose constant of the drift argument. In simulation (`backpressure_sim.py --buffers`,
with `--cap c` for blocking buffers of `c · m` packets per destination) the largest queue stays
near `26 m` for every slack from `δ = 0.4` down to `0.02`, and the threshold is sharp:

| buffer per destination | δ = 0.4 | 0.2 | 0.1 | 0.05 | 0.02 |
|---|---|---|---|---|---|
| `4 m` | 0.42 | 0.50 | 0.54 | 0.55 | 0.56 |
| `16 m` | 0.57 | 0.72 | 0.83 | 0.88 | 0.91 |
| `24 m` | 0.60 | 0.80 | 0.91 | 0.95 | 0.98 |
| `48 m` | 0.60 | 0.80 | 0.90 | 0.95 | 0.98 |

(delivered throughput over the fluid optimum, 8 × 8 mesh, `m = 1`, offered `1 − δ`; `m = 2`
is within 0.01 at `24 m` and above). So about `24 m` packets per destination, some 1 500 per node
for `m = 1`, reach the optimum within 2 %, and too little buffer loses far more than the shortfall
in storage would suggest.

### Packets in time, whole packets, and why routing must adapt

The statements above about packets are theorems too:

* **Packet networks in time** (`Routing/Throughput.lean`). A *placement* puts a packet network on
  a graph (where each channel's packet is, which link a channel belongs to); a *timed run*
  (`Network.TimedRun`) runs in rounds from the empty network, every channel receiving at most
  one packet per round. The potential of the packets in the network
  (`TimedRun.injected_le`) gives the **packet ceiling** (`TimedRun.ceiling`, `cut_ceiling`,
  `hop_ceiling`): whatever the routing and the selection, a timed run sustaining `ρ · dem`
  respects every bound of the fluid network of its placement. Everything injected is delivered
  but for what the network holds (`ejected_ge`). Timed runs of lanes combine round by round
  (`lanesTimed`), injecting the sum of what the lanes inject. The networks of `GraphData` are
  placed with two channels per link (`GraphData.placement_cap`).
* **The torus with `m` lanes** (`Examples/Throughput.lean`): its fluid network is `m` copies of
  the fluid torus (`torusLanesPlacement_cap`); no timed run sustains uniform traffic above `m`
  times `torus_uniform_opt` (`torusLanes_ceiling`); any load one lane sustains, `m` lanes sustain
  `m` times over (`torusLanes_timed`, `torusLanes_sustains`). So lane throughput with packets is
  exactly linear, up to the fluid optimum it can never pass.
* **Whole packets and bursts** (`Flow/Backpressure.lean`). Backpressure stays stable for arrivals
  in a leaky bucket below a routable traffic, bounded per slot, with bursts `σ`
  (`Run.backpressure_stable_bursty`, by the drift over frames `Run.frame_drift`): whole packets
  at fractional rates. Sequential sends (`sendSeq`) serve `min (backlog, offered)` exactly and
  move whole packets only (`Run.ofArrivalsSeq_int`); on the mesh with `m` connections this
  whole-packet backpressure is stable at every leaky-bucket rate below `m` times the optimum
  (`mesh_backpressure_packets`).
* **Adaptivity is necessary** (`Flow/Necessity.lean`). A stable run respects every potential
  bound on the links it uses (`Run.potentialFeasibleOn`), so the kernel-checked dual
  certificates bound it as they bound flows (`GraphCert.Model.run_minimal_ceiling`). On the 8 × 8
  torus under tornado traffic backpressure is stable below `16/15`, but no scheduler moving
  traffic only along shortest paths keeps a bounded backlog above `2/3`
  (`torusTornado_adaptivity`).
* **Backpressure-style choices are safe**: choosing among the free permitted hops those of
  largest score is a valid selection (`Network.scoreSel_valid`), so the lanes, shared lanes and
  widened networks stay deadlock and livelock free under it (`torusLanes_scoreSel`,
  `torusWide_scoreSel`).

* **Finite buffers, no deadlock, near the optimum** (`Flow/Necessity.lean`). Backpressure
  never deadlocks where every destination is reachable: whenever traffic is queued, some moves
  (`Run.backpressure_progress`). On the mesh with `m` connections at `(1 − δ)` times the
  optimum it fits in buffers of `145 m k⁷ / (16 δ) + m` packets per destination, never
  deadlocks, and is stable (`mesh_finite_buffer_network`).
* **Head-of-line blocking** (`Flow/Necessity.lean`). A vertex with a single first-in first-out
  queue sends at most one packet per slot, so no such run is stable above one packet per vertex
  and slot whatever the capacities (`Run.singleHead_ceiling`); on the mesh with `m` connections
  backpressure with a queue per destination is stable up to `m` times the optimum
  (`mesh_headOfLine`): per-destination queues are necessary for linear scaling.

**What is measurement, not theorem.** The percentages the simulators report (46 to 65 % of the
optimum for the proved-safe networks under random move order, 99 % for backpressure, the
threshold near `24 m` packets per destination) are outcomes of particular random runs on
Poisson traffic. The theorems bound them from above (the ceilings), prove backpressure stable on
every arrival sequence within a leaky bucket (Poisson bursts are unbounded, so a Poisson sample
path is covered only when it stays within some bucket), and give buffer sizes that suffice
(loosely). The 58.6 % of a first-in first-out switch under uniform random traffic is a
probabilistic limit from the literature; its deterministic counterpart above is proved. The
history of the schemes is cited.

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
| `Flow/Fluid.lean`, `Flow/MeshWire.lean` | fluid throughput bounds: weak duality, the wire and cut bounds; the mesh's optimum and the wire ceiling on the k × k grid |
| `Flow/MeshOdd.lean`, `Flow/MeshWorst.lean` | the mesh's uniform optimum for odd k; minimality of XY; admissible traffic, O1TURN and XY flows for any demand, the worst-case optimum 4/k and the bit-complement optimum |
| `Flow/Certificate.lean`, `Flow/MeshPatterns.lean` | kernel-checked LP certificates (primal flow, dual lengths) for the k × k mesh; exact optima of transpose, shuffle, bit reversal and hotspot on the 8 × 8 mesh |
| `Flow/Topologies.lean`, `Flow/Tree.lean`, `Flow/Symmetric.lean`, `Flow/Valiant.lean` | the torus and the hypercube; minimal routing optimal for every traffic iff tree; uniform traffic on arc-transitive networks; Valiant's half-capacity bound and the worst cases of mesh, torus and hypercube |
| `Routing/GraphDetour.lean` | source-chosen intermediate nodes (Valiant, long way round) on top of bounded returns: safe on every graph |
| `Flow/GraphCert.lean`, `Flow/GraphPatterns.lean` | graph-generic kernel-checked LP certificates; exact minimal and any-routing optima on the 8 × 8 torus and the 6-cube |
| `Routing/Saturation.lean` | delivery under sustained load: channel fairness, Duato's theorem for liveness with injections never stopping |
| `Flow/Scaling.lean` | throughput scales exactly linearly with the connections: flows scale and add, the layered scheme, exact optima with `m` connections per link on the mesh, torus and hypercube |
| `Routing/Lanes.lean` | the lane network: `m` copies of a network side by side; safety certificates and their transfer to every number of lanes; lanes run in parallel and deliver the sum of their packets |
| `Routing/SharedLanes.lean`, `Routing/Widen.lean` | sharing the connections: escapes per lane with adaptive hops on every lane; widening any network to any number of copies of every channel, every copy usable, with every guarantee kept |
| `Flow/Backpressure.lean` | backpressure (max-weight) scheduling in a queueing model of the fluid network: stable at every load below the fluid optimum, no scheduler stable above it; the mesh, torus and hypercube with `m` connections per link |
| `Routing/Throughput.lean` | packet networks in time: placements, timed runs, the fluid ceiling for every selection, delivery, lanes adding their throughput, score-based selections |
| `Flow/Necessity.lean` | stable runs respect every certified bound on the links they use; shortest-path-only scheduling loses (tornado on the torus) |
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
| `Examples/` | Muller rings, arbiter, dining philosophers, counterexamples, circuits, STG implementation, composition, imported designs, structural proofs, fairness, free choice, QDI, concurrent firing, unbounded nets, scale, symbolic certificates, routing, maximally adaptive routing (on every mesh size), optimal routing per cost, a tiered source-throttled selection, safe routing on the torus and the Petersen graph, the torus with `m` lanes |

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
