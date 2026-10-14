/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic.Syntax

/-!
# The `async_decide` tactic

This module gathers 5 parts:

1. `Tactic.Diagnosis` — literal certificates and the diagnosis of failures;
2. `Tactic.Goals` — raw literals, goal recognition and the checks behind `async_bdd`;
3. `Tactic.Bitmap` — bitmap certificates and `async_bitmap`;
4. `Tactic.Decide` — routing, explicit and abstract checks;
5. `Tactic.Syntax` — `async_decide` and the tactic syntax.

`async_decide` proves, for a concrete design, goals of the form

* `N.Correct`, `N.toNet.lts.DeadlockFree N.M₀`, `N.toNet.lts.LivelockFree N.Internal N.M₀`,
  `N.toNet.lts.Live N.M₀`, `N.toNet.lts.Persistent N.M₀` for a Petri net `N : PNet`;
* `C.Correct`, `C.lts.DeadlockFree C.s₀`, `C.lts.LivelockFree C.Internal C.s₀`,
  `C.lts.Live C.s₀`, `C.SpeedIndependent` for a gate-level circuit `C : Circuit`;
* `N.Correct`, `N.DeadlockFree`, `N.LivelockFree`, `N.StarvationFree` and
  `N.WormholeCorrect`, `N.WormholeDeadlockFree`, `N.WormholeLivelockFree` for an
  interconnection network `N : Network ℕ ℕ` with dynamic routing.  No configuration of the network is explored: the
  routing function is checked locally (Dally–Seitz with the full routing function, then
  Duato with the first-listed hop of every packet as its escape channel).  `async_routing
  (escape := R₁)` names the escape subfunction explicitly;
* `N.MaximallyAdaptive U` for such a network: every hop of `U` that `N` does not permit is
  refuted by a run into a deadlock (`Network.maximallyAdaptive_of_maxCheck`).

It works in three steps:

1. **search (untrusted)** — the reachable state space, a ranking function and distance
   functions are computed by *compiled code* at elaboration time (`PNet.mkCert`);
2. **certificate** — the result is embedded in the proof as a literal term;
3. **check (trusted)** — the kernel evaluates the verified checker on the literal certificate
   (`decide +kernel`), and `PNet.correct_of_checkCert` turns the result into a proof.

Running code at elaboration time adds nothing to the trusted base: the final proof term only
contains data and a kernel-checked decision, so it depends on no axiom beyond `propext`,
`Classical.choice` and `Quot.sound` (no `Lean.ofReduceBool`, unlike `native_decide`).

If the design is incorrect, the tactic fails with a counterexample and the exact
refutation theorem that proves the negation.  `async_decide (fuel := n)` raises the bound on
the number of explored states (default `100000`).

If the state space of a Petri net does not close (it may be unbounded), the tactic checks the
net's counter abstraction instead (`AsyncLean.Checker.Abstract`), with caps just above the arc
weights; `async_decide (cap := k)` chooses the cap.
-/
