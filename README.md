# async-lean

A Lean 4 / Mathlib formalisation of the theory needed to **prove that an asynchronous design
never deadlocks and never livelocks**, including interconnection networks with **dynamic
(adaptive) routing**. It is fully machine-checked, with **no `sorry` and no
axioms** beyond Lean's three standard foundational ones (`propext`, `Classical.choice`,
`Quot.sound`).

It covers five ways of describing a design:

| Model | Lean type | Typical use |
|---|---|---|
| Place/transition Petri nets | `Net`, `PNet` | handshake protocols, arbiters, controllers |
| Signal transition graphs (STGs) | `StgModel`, `Stg` | specifications of asynchronous controllers, and their gate-level implementations |
| Marked graphs, free-choice nets | `MarkedGraph`, `Net.FreeChoice` | pipelines, rings, choice-free and free-choice control |
| Gate-level netlists | `Circuit` | C-element circuits, hazard analysis, speed independence, QDI |
| Packet-switched networks | `Network` | networks on chip, router meshes and rings with adaptive routing and virtual channels |

Designs can be written in Lean or imported from `.g` (Petrify / Workcraft), PNML and
structural Verilog.

It gives three ways to prove properties:

1. **A verified model checker** for concrete designs. The `async_decide` tactic explores the
   state space at elaboration time and computes a certificate, which the kernel checks with a
   proved-correct checker. Failures come with a counterexample, and the refutation theorems
   turn it into a proof of the negation.
2. **Automatic structural proofs** with no state exploration. `async_structural` finds place
   invariants, linear ranking functions and Commoner certificates by linear programming or
   graph search; the kernel checks them.
3. **Theory for whole families of designs.** Commoner's theorems for marked graphs and
   free-choice nets, invariants, siphons and traps, ranking functions, compositional
   reasoning and fairness. For example, every Muller ring of every size is proved live iff it
   has a token and a bubble.

**New here? Start with [`AsyncLean/Tutorial.lean`](AsyncLean/Tutorial.lean)**, a checked
walkthrough of all of the above.

## The properties

All of these are defined once, for labelled transition systems (`AsyncLean/LTS/Properties.lean`),
and transported to every model:

| Property | Definition |
|---|---|
| `DeadlockFree s₀` | no reachable state is without an outgoing step |
| `LivelockFree internal s₀` | no reachable state starts an *infinite run of internal (silent) steps*, so the system can't chatter forever without observable progress |
| `Live s₀` | every action can always eventually happen again (no partial deadlock or starvation; Petri-net L4-liveness) |
| `Persistent s₀` | an enabled action is never disabled by another one (semi-modularity, i.e. speed independence / hazard freedom for circuits) |

`PNet.Correct`, `StgModel.Correct` and `Circuit.Correct` bundle deadlock freedom, livelock
freedom and liveness. For networks, `Network.Correct` is routing deadlock and livelock freedom
under every dynamic routing policy (see below). `PNet.Bounded k` and `PNet.Safe` bound the number of tokens per place.

The progress theorem `LTS.inevitablyExternal` shows what deadlock freedom plus livelock
freedom buys you: from every reachable state, *every* run of internal steps inevitably
reaches a state offering an observable action. Under a fair scheduler, liveness becomes
"every action *will* happen infinitely often" (`LTS.Run.infOften_label_of_live`).

## Quick start: verify your own design

```lean
import AsyncLean
open AsyncLean

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

-- deadlock free ∧ livelock free ∧ every transition live
theorem handshake_correct : handshake.Correct := by async_decide
-- at most one token per place, by state exploration or by place invariants
theorem handshake_safe : handshake.Safe := by async_structural

#assert_standard_axioms handshake_correct   -- fails the build on sorry / native_decide / axioms
```

A transition lists its input and output places; repeat a place for an arc weight above one.
Mark silent or dummy transitions with `internal := true`; livelock is about these.

When a design is wrong, `async_decide` fails and shows a counterexample plus the theorem
that proves the negation:

```
async_decide: DEADLOCK reachable by firing [take₁ 0(#0), take₁ 1(#3), take₁ 2(#6)].
Prove it with: PNet.not_deadlockFree_of_refute (ts := [0, 3, 6]) (by decide +kernel)
```

`#eval N.diagnose` runs the same search directly.

### Specifications and implementations: STGs

An STG is a Petri net whose transitions are signal edges. Read one from a `.g` file and its
implementation from Verilog:

```lean
stg_from_g celement "designs/celement.g"
gates_from_verilog celementGates "designs/celement.v" for celement

theorem spec_ok : celement.model.Correct ∧ celement.model.Consistent ∧
    celement.model.CSC ∧ celement.model.OutputPersistent :=
  ⟨by async_decide, by async_decide, by async_decide, by async_decide⟩

theorem impl_ok : celement.model.Conformant (celement.gateFn celementGates) := by
  async_decide
```

*Conformance* (every output edge the gates can produce is allowed by the specification)
implies that the closed loop of circuit and environment inherits deadlock freedom, livelock
freedom and liveness (`Stg.implementation_correct`) and is hazard free
(`StgModel.gate_persistent`). `StgModel.csc_iff_exists_conformant` proves that complete state
coding is exactly implementability.

### Gate-level circuits, gate delays and wire delays

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

The environment is modelled by gates too, so the circuit is closed. A deadlock is a stable
state; a livelock is endless switching of internal gates only. `SpeedIndependent` assumes
arbitrary gate delays; `QDI iso` also puts an independent delay on every wire branch except
the forks of the signals in `iso` (isochronic forks). `Circuit.speedIndependent_of_qdi`
proves that QDI implies speed independence.

### Networks with dynamic routing

A `Network C P` has channels `C`, each with a one-packet buffer (store-and-forward or virtual
cut-through switching; a virtual channel is a channel of its own), and packet headers `P` (a
destination, possibly with routing state such as a misrouting budget). `route c p` lists the
hops a packet may take next. With adaptive routing there are several, and a **selection
function** picks one at run time, for example the least congested free channel. `N.Correct`
quantifies over every *work-conserving* selection function, one that never leaves a packet
waiting while a permitted channel is free:

* **routing deadlock freedom** (`Network.DeadlockFree`): whenever the network holds a
  packet, some packet can move;
* **routing livelock freedom** (`Network.LivelockFree`): there is no infinite run without new
  injections, so packets cannot keep moving forever without reaching their destinations.

Together they give the drain theorem `Network.Correct.drain`: from every reachable
configuration, all packets are delivered once injection stops. With injection going on
forever:

* **starvation freedom** (`Network.StarvationFree`): along every strongly fair run, every
  packet in the network is eventually delivered (`Routing/Fairness.lean`).

The model above is store-and-forward or virtual cut-through switching: each packet holds one
channel. **Wormhole switching** (`Routing/Wormhole.lean`) lets a packet span several channels,
and a blocked head blocks the whole packet. `Network.WormholeCorrect` is deadlock and livelock
freedom for packets of every length, under every selection function.

```lean
-- XY routing on virtual channel 0 (the escape channels, listed first) plus fully adaptive
-- minimal routing on virtual channel 1 (mesh helpers from `Examples/Routing.lean`)
def duatoMesh (k : ℕ) : Network ℕ ℕ where
  arrived c d := head k c == d
  route c d := let u := head k c
    (ch u (xy k u d) 0, d) :: (productive k u d).map fun dr => (ch u dr 1, d)
  inject := allPairs (k * k) fun s => ch s 4 0

theorem duatoMesh_correct : (duatoMesh 4).Correct := by async_decide
```

The configurations of the network are never explored. The routing function is checked
locally:

* `Network.deadlockFree_of_cdg` (**Dally and Seitz**): the channel dependency graph is
  acyclic;
* `Network.deadlockFree_of_escape` (**Duato**): a connected routing subfunction (the escape
  channels) has an acyclic dependency graph, even if the full adaptive routing function does
  not. `async_decide` tries the full routing function, then the first-listed hop of every
  packet; `async_routing (escape := R₁)` names the escape subfunction;
* `Network.livelockFree_of_ranking`: a rank that decreases on every permitted hop, such as
  the distance for minimal routing, or distance plus misrouting budget for bounded
  non-minimal routing. `Network.packet_hops_le` bounds the number of hops of every packet;
* `Network.wormholeDeadlockFree_of_escape` (**Duato for wormhole switching**): every legal
  packet may request an escape channel, and the *extended* dependency graph of the escape
  channels, with the indirect dependencies through adaptive channels, is acyclic.
  `async_decide` tries all channels, then the channels of the first-listed hops;
  `async_routing (escape := E)` names them.

Duato's condition is also **necessary** (`Network.staticDeadlockFree_iff_exists_escape`):
when finitely many channels carry legal packets, every configuration of legal packets can
move iff some connected routing subfunction has an acyclic dependency graph. When every legal
configuration is reachable, this makes deadlock freedom itself equivalent to Duato's condition
(`Network.deadlockFree_iff_exists_escape`).

Failures come with counterexamples: a set of injections and hops that fills a dependency
cycle with blocked packets (`Network.not_deadlockFree_of_refuteB`), or a packet that can go
round a cycle forever (`Network.not_livelockFree_of_refuteB`), and their wormhole versions. `Examples/Routing.lean`
proves XY, Duato-adaptive and bounded-misrouting meshes correct and starvation free, and XY
and Duato meshes correct under wormhole switching. It refutes a plain ring (with two long
packets under wormhole switching), a fully adaptive mesh without escape channels and a
deflection-routed mesh. Dateline rings of every size are proved correct, starvation free
and wormhole correct.

### Large designs: structure and composition

* `async_structural` proves safeness and boundedness (place invariants), livelock freedom
  for **every** initial marking (linear ranking functions), and liveness of marked graphs and
  small free-choice nets (Commoner's theorems). A 20-stage FIFO with over a million states is
  proved safe and livelock free instantly.
* `async_minimize` replaces a component of a parallel composition by its minimal quotient
  modulo divergence-preserving weak bisimulation, certified by the kernel. Then
  `async_decide` checks the much smaller composition (`Examples/Compositional.lean`).

### Proving whole families: the theory

* **Marked graphs** (`MarkedGraph/Basic.lean`). Commoner's theorem, `live_iff_circuitsMarked`:
  a marked graph is live **iff every directed circuit carries a token**; token conservation
  on circuits; safeness from circuit covers. `Examples/MullerRing.lean` proves, for all `n`
  and `k`, that a Muller ring with `n` stages and `k` tokens is live iff `1 ≤ k ≤ n - 1`, and
  is always 1-safe.
* **Free-choice nets** (`Petri/FreeChoice.lean`). Commoner's theorem for free-choice nets,
  `live_of_siphonTrap`: an ordinary free-choice net in which every siphon contains an
  initially marked trap is live.
* **P-invariants, linear ranking functions, siphons and traps** (`Petri/`).
* **Composition** (`LTS/Compose.lean`). Parallel composition, hiding and
  divergence-preserving weak bisimulation (a congruence that preserves deadlock and livelock
  freedom).
* **Routing** (`Routing/`). Duato's theorem as an equivalence, Dally and Seitz's theorem,
  ranking functions for livelock freedom and hop bounds, the drain theorem, the reduction of
  every selection policy to fully adaptive routing (`Network.deadlockFree_iff_adaptive`,
  `Network.livelockFree_iff_adaptive`), starvation freedom under fairness, and wormhole
  switching with Duato's extended dependency graph.
* **Fairness** (`LTS/Fairness.lean`). Infinite runs and strong fairness: live actions happen
  infinitely often, and progress holds even when internal cycles exist.
* **Generic rules** (`LTS/Properties.lean`). Inductive invariants, ranking functions into any
  well-founded order, distance functions for liveness, `livelockFree_iff_acc`, and transfer
  of every property along (partial) bisimulations.

## Library map

| File | Contents |
|---|---|
| `Tutorial.lean` | a checked walkthrough of the library |
| `LTS/Basic.lean` | transition systems, reachability, traces |
| `LTS/Properties.lean` | deadlock, livelock, liveness, persistence; proof and refutation rules; progress theorem; transfer along bisimulations |
| `LTS/Compose.lean` | parallel composition, hiding, divergence-preserving weak bisimulation |
| `LTS/Fairness.lean` | infinite runs, strong fairness, "will happen" theorems |
| `Petri/Basic.lean`, `Invariant.lean`, `SiphonTrap.lean` | Petri nets, P-invariants, bounds, ranking functions, siphons and traps |
| `Petri/FreeChoice.lean` | free-choice nets, Commoner's liveness theorem |
| `MarkedGraph/Basic.lean` | Commoner's theorem for marked graphs, circuit tokens, safeness, rank certificates |
| `Stg/Basic.lean` | STGs: state graph, consistency, CSC, output persistence, implementation by gates, CSC ⇔ implementable |
| `Stg/Concrete.lean` | concrete STGs `Stg`, checkers and refutations for all STG properties |
| `Circuit/Basic.lean` | gate netlists (`BExpr`, C-elements), Muller semantics, speed independence |
| `Circuit/Wires.lean`, `Circuit/QDI.lean` | wire delays, QDI, proof that QDI implies speed independence |
| `Routing/Basic.lean` | networks with dynamic routing, selection functions, Duato's theorem (sufficient and necessary) and Dally–Seitz's theorem, livelock by ranking, drain theorem, refutations |
| `Routing/Fairness.lean` | starvation freedom: every packet is delivered along every strongly fair run |
| `Routing/Wormhole.lean` | wormhole switching, Duato's extended dependency graph, livelock, drain, refutations |
| `Routing/Check.lean`, `Routing/WormholeCheck.lean` | trusted routing checkers, untrusted certificate search and diagnosis |
| `Checker/Explicit.lean` | the **trusted checker** and its soundness proofs; certificates; counterexample traces |
| `Checker/BTree.lean`, `Invariant.lean`, `Packed.lean`, `Quotient.lean` | search trees, invariant certificates, bit-packed safe nets, quotient certificates |
| `Checker/Petri.lean` | concrete nets `PNet`, executable semantics, bisimilarity with the abstract net |
| `Checker/Diagnose.lean`, `Minimize.lean` | untrusted counterexample search, certificate and quotient computation |
| `Checker/Tactic.lean` | the `async_decide`, `async_routing` and `async_minimize` tactics |
| `Auto/Simplex.lean`, `Auto/Structural.lean` | exact rational simplex (untrusted) and `async_structural` |
| `Import/G.lean`, `Pnml.lean`, `Verilog.lean` | importers: `stg_from_g`, `pnet_from_pnml`, `gates_from_verilog`, `circuit_from_verilog` |
| `AxiomAudit.lean`, `Audit.lean` | `#assert_standard_axioms` and the library-wide audit |
| `Examples/` | Muller rings, arbiter, dining philosophers, counterexamples, circuits, STG implementation, composition, imported designs, structural proofs, fairness, free choice, QDI, routing |

## Why the results can be trusted

* **No `sorry`, no `axiom`, no `native_decide`.** `AsyncLean/Audit.lean` and every example
  run `#assert_standard_axioms`, which makes the build fail if a result depends on anything
  other than `propext`, `Classical.choice` and `Quot.sound`. That rules out `sorryAx` and
  `Lean.ofReduceBool`.
* **Untrusted search, trusted check.** Exploring the state space, computing rankings,
  distances, quotients and linear-programming solutions is ordinary unverified code that runs
  at elaboration time. Only the checkers are trusted, and their soundness is proved
  (`of_checkCert`, `correct_of_checkPacked`, `divBisim_of_checkQuot`, …). A buggy search can
  only make a check *fail*.
* **The checked model is the specified model.** `PNet.bisim`, `Circuit.bisim` and
  `Stg.bisim` prove the executable semantics bisimilar to the abstract ones, and the
  bisimulation theorems transfer every property. So conclusions are about the abstract
  `Net`, `StgModel` and `Circuit` semantics.
* **Importers are outside the trusted base too.** An imported design is an ordinary Lean
  definition (`#print` it); the theorems are about that definition.

## Scope and limits

* Semantics are interleaving: one transition, or one gate, at a time. For Petri nets, STGs
  and speed-independent circuits this is the standard semantics for these properties.
* Networks are modelled with store-and-forward / virtual cut-through switching (one channel
  per packet) or wormhole switching (a packet spans up to `tail p + 1` channels, with one-flit
  channel buffers). Routing livelock freedom is "no infinite run without injections".
  Starvation freedom assumes a strongly fair scheduler and is proved for store-and-forward
  switching. Duato's condition is proved necessary and sufficient for store-and-forward
  switching; for wormhole switching the sufficient direction is proved.
* Liveness is L4-liveness. Fairness-based "will happen" properties are derived from it in
  `LTS/Fairness.lean`. Livelock is divergence: an infinite run of internal actions.
* Free-choice liveness is proved in the sufficient direction (siphon–trap ⇒ live), which is
  the one needed for verification. `async_structural` enumerates siphons, so it is meant for
  nets with up to a dozen or so places.
* The model checker needs a finite reachable state space. Kernel checking takes roughly
  10–60 ms per reachable state. For example, 7 dining philosophers (408 states) take 8 s,
  and two composed 8-stage FIFOs (65 536 states) take 36 s after minimisation. Designs with
  up to a few thousand states are practical. Beyond that, use the structural tactics, the
  theory, or composition.
* Lake does not track design files read by the importers: after editing a `.g`, `.pnml` or
  `.v` file, rebuild the Lean file that imports it (for example by touching it).

## Building

```
lake exe cache get   # download prebuilt Mathlib
lake build
```

API documentation is built with doc-gen4 (`.github/workflows/docs.yml` publishes it to
GitHub Pages):

```
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
lake build AsyncLean:docs      # output in docbuild/.lake/build/doc
```

Toolchain: Lean 4.34.1, Mathlib v4.34.1. See [CHANGELOG.md](CHANGELOG.md) for the history.
