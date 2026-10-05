# async-lean

A Lean 4 / Mathlib formalisation of the theory needed to **prove that an asynchronous design
never deadlocks and never livelocks**. It is fully machine-checked, with **no `sorry` and no
axioms** beyond Lean's three standard foundational ones (`propext`, `Classical.choice`,
`Quot.sound`).

It covers three ways of describing a design:

| Model | Lean type | Typical use |
|---|---|---|
| Place/transition Petri nets (incl. STG-style labelled nets) | `Net`, `PNet` | handshake protocols, arbiters, controllers |
| Marked graphs | `MarkedGraph` | pipelines, rings, choice-free control |
| Gate-level netlists, speed-independent semantics | `Circuit` | C-element circuits, hazard analysis |

It also gives two ways to prove properties:

1. **Structural theorems that hold for whole families of designs.** Commoner's theorem,
   P-invariants, siphons/traps, linear ranking functions and inductive invariants. For
   example, every Muller ring of every size is proved live iff it has a token and a bubble.
2. **A verified model checker for concrete designs.** The kernel checks a certificate, which
   the `async_decide` tactic computes. Failures come with a counterexample, which the
   refutation theorems turn into a proof of the negation.

## The properties

All of these are defined once, for labelled transition systems (`AsyncLean/LTS/Properties.lean`),
and transported to every model:

| Property | Definition |
|---|---|
| `DeadlockFree s₀` | no reachable state is without an outgoing step |
| `LivelockFree internal s₀` | no reachable state starts an *infinite run of internal (silent) steps*, so the system can't chatter forever without observable progress |
| `Live s₀` | every action can always eventually happen again (no partial deadlock or starvation; Petri-net L4-liveness) |
| `Persistent s₀` | an enabled action is never disabled by another one (semi-modularity, i.e. speed independence / hazard freedom for circuits) |

`PNet.Correct` and `Circuit.Correct` bundle deadlock freedom, livelock freedom and liveness.

The progress theorem `LTS.inevitablyExternal` shows what deadlock freedom plus livelock
freedom buys you. From every reachable state, *every* run of internal steps inevitably reaches
a state offering an observable action.

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

Gate-level netlists work the same way:

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
```

The environment is modelled by gates too, so the circuit is closed. A deadlock is a stable
state; a livelock is endless switching of internal gates only.

### Proving whole families: structural theory

The model checker handles one finite instance at a time. For parameterised designs, use the
theory:

* **Marked graphs** (`AsyncLean/MarkedGraph/Basic.lean`). Commoner's theorem,
  `live_iff_circuitsMarked`: a marked graph is live **iff every directed circuit carries a
  token**. "All circuits marked" is certified by a ranking of transitions that increases
  along every empty place (`circuitsMarked_iff_exists_rank`). Token counts on circuits are
  invariant (`tokens_reachable`), which gives place bounds and safeness
  (`safe_of_circuit_cover`). `Examples/MullerRing.lean` proves, for all `n` and `k`, that a
  Muller ring with `n` stages and `k` tokens is live iff `1 ≤ k ≤ n - 1`, and is always
  1-safe.
* **P-invariants** (`AsyncLean/Petri/Invariant.lean`). Conservation laws, bounds and
  safeness. `Examples/Arbiter.lean` uses one to prove mutual exclusion.
* **Linear ranking functions** (`Net.livelockFree_of_linearRanking`). Place weights that
  strictly decrease under every internal transition prove livelock freedom *for every
  initial marking*. The side condition is decided by `decide`.
* **Siphons and traps** (`AsyncLean/Petri/SiphonTrap.lean`). Commoner's siphon–trap
  property implies deadlock freedom for ordinary nets.
* **Generic rules** (`AsyncLean/LTS/Properties.lean`). Inductive invariants
  (`DeadlockFree.of_invariant`), ranking functions into any well-founded order
  (`LivelockFree.of_ranking_wf`), distance functions for liveness (`LiveLabel.of_ranking`),
  and the characterisation `livelockFree_iff_acc`.

## Library map

| File | Contents |
|---|---|
| `LTS/Basic.lean` | transition systems, reachability, traces |
| `LTS/Properties.lean` | deadlock, livelock, liveness, persistence; proof and refutation rules; progress theorem; functional bisimulations transfer every property |
| `Petri/Basic.lean` | Petri nets, firing, executable firing sequences, counterexamples |
| `Petri/Invariant.lean` | P-invariants, bounds, safeness, linear ranking functions |
| `Petri/SiphonTrap.lean` | siphons, traps, siphon–trap deadlock theorem (decidable) |
| `MarkedGraph/Basic.lean` | Commoner's liveness theorem, circuit token conservation, safeness, rank certificates |
| `Circuit/Basic.lean` | gate netlists (`BExpr`, C-elements), Muller semantics, speed independence |
| `Checker/BTree.lean` | search trees for the kernel-evaluated checker |
| `Checker/Explicit.lean` | the **trusted checker** and its soundness proofs; untrusted search; certificates; counterexample traces |
| `Checker/Petri.lean` | concrete nets `PNet`, executable semantics, proof of bisimilarity with the abstract net |
| `Checker/Diagnose.lean` | untrusted counterexample search |
| `Checker/Tactic.lean` | the `async_decide` tactic |
| `AxiomAudit.lean`, `Audit.lean` | `#assert_standard_axioms` and the library-wide audit |
| `Examples/` | Muller rings (parametric), handshake, arbiter + mutual exclusion, deadlock / livelock / starvation counterexamples and fixes, dining philosophers, C-element ring, hazardous AND gate |

## Why the results can be trusted

* **No `sorry`, no `axiom`, no `native_decide`.** `AsyncLean/Audit.lean` and every example
  run `#assert_standard_axioms`, which makes the build fail if a result depends on anything
  other than `propext`, `Classical.choice` and `Quot.sound`. That rules out `sorryAx` and
  `Lean.ofReduceBool`.
* **Untrusted search, trusted check.** Exploring the state space and computing rankings and
  distances is ordinary unverified code. It runs at elaboration time (`async_decide`) or in
  the kernel (`PNet.checkAll` + `decide +kernel`). Only the small checker in
  `Checker/Explicit.lean` is trusted, and its soundness is proved (`of_checkCert`,
  `deadlockFree_of_check`, …). A buggy search can only make a check *fail*.
* **The checked model is the specified model.** `PNet.bisim` and `Circuit.bisim` prove the
  executable semantics bisimilar to the abstract ones, and `LTS.FunBisim` transfers every
  property, so conclusions are about the abstract `Net` and `Circuit` semantics.

## Scope and limits

* Semantics are interleaving: one transition, or one gate, at a time. For Petri nets and
  speed-independent circuits this is the standard semantics for these properties.
* Liveness is L4-liveness (every action can always be re-enabled), not a fairness-based
  temporal property. Livelock is divergence: an infinite run of internal actions.
* The model checker needs a finite reachable state space. Kernel checking costs roughly
  50–150 ms per reachable state for nets of 15–30 transitions: about 5 s for 70 states and
  about 1 minute for 400. That makes designs with hundreds to a few thousand states
  practical. Beyond that, use the structural theory.

## Building

```
lake exe cache get   # download prebuilt Mathlib
lake build
```

Toolchain: Lean 4.34.1, Mathlib v4.34.1.
