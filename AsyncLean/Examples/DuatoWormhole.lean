/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
import AsyncLean.AxiomAudit

/-!
# Duato's condition is not necessary under wormhole switching

For store-and-forward switching, Duato's condition — a connected escape subfunction whose
dependency graph is acyclic — is necessary as well as sufficient for deadlock freedom
(`Network.staticDeadlockFree_iff_exists_escape`).  Under wormhole switching it is only
sufficient: this network is deadlock free for packets of every length and every selection
function, yet no choice of escape channels has an acyclic extended dependency graph.

Two nodes `0` and `1`; channels `0` and `3` lead from node `0` to node `1`, channels `1`
and `2` back.  A header is the packet's destination node.

* a packet for node `0` injected on channel `0` continues on channel `1`;
* a packet for node `1` injected on channel `1` continues on channel `3` or `0`;
* a packet for node `0` injected on channel `3` continues on channel `2` or `1`.

Any escape set must contain channel `1` (the only hop of the first packet), and channel `0`
or `3` (a hop of the second); either choice closes a cycle (`0 → 1 → 0` or `3 → 1 → 3`).
But no deadlock is reachable: a packet waiting on channel `3` needs channels `1` and `2` held,
and only packets at their destination ever hold channel `2` — they can always leave.  The
blocking-set check of `Network.wormholeDeadlockFree_of_wholdCheck` finds this.

The literature agrees: Duato's condition is sufficient but not necessary for wormhole routing
functions of this generality (Schwiebert and Jayasimha's channel waiting graphs refine it).
-/

namespace AsyncLean.Examples

open Network

/-- The network described above (channels and headers are numbers). -/
def twoNodes : Network ℕ ℕ where
  arrived c d := (d == 0 && (c == 1 || c == 2)) || (d == 1 && (c == 0 || c == 3))
  route c d :=
    if c == 0 && d == 0 then [(1, 0)]
    else if c == 1 && d == 1 then [(3, 1), (0, 1)]
    else if c == 3 && d == 0 then [(2, 0), (1, 0)]
    else []
  inject := [(0, 0), (1, 1), (3, 0)]

/-- The legal pairs: the injected ones and their hops. -/
def twoNodesLegal : List (ℕ × ℕ) := [(0, 0), (1, 1), (3, 0), (1, 0), (3, 1), (0, 1), (2, 0)]

theorem twoNodes_closed : twoNodes.Closed fun c p => (c, p) ∈ twoNodesLegal := by
  refine ⟨fun q hq => ?_, fun c p q hl _ hq => ?_⟩
  · revert q; decide
  · have : ∀ q ∈ twoNodesLegal, ∀ q' ∈ twoNodes.route q.1 q.2, q' ∈ twoNodesLegal := by decide
    exact this (c, p) hl q hq

/-- **Deadlock free under wormhole switching**, for packets of every length and every valid
selection function, by blocking sets. -/
theorem twoNodes_wormholeDeadlockFree : twoNodes.WormholeDeadlockFree := by
  refine twoNodes.wormholeDeadlockFree_of_wholdCheck twoNodes_closed [(0, 0), (1, 1), (3, 0)]
    (fun c p hl ha => ?_) (by decide)
  have : ∀ q ∈ twoNodesLegal, twoNodes.arrived q.1 q.2 = false → q ∈ [(0, 0), (1, 1), (3, 0)] :=
    by decide
  exact this (c, p) hl ha

/-- `async_decide` falls back on blocking sets when no escape channels work. -/
example : twoNodes.WormholeDeadlockFree := by async_decide

/-- **Duato's condition fails**: for every closed set of legal pairs and every set of escape
channels that every waiting packet may request, the extended dependency graph has a cycle. -/
theorem twoNodes_not_escape : ¬ ∃ (legal : ℕ → ℕ → Prop) (E : ℕ → Prop), twoNodes.Closed legal ∧
    (∀ c p, legal c p → twoNodes.arrived c p = false → ∃ q ∈ twoNodes.route c p, E q.1) ∧
    WellFounded (flip (twoNodes.ExtDep legal E)) := by
  rintro ⟨legal, E, hcl, hconn, hwf⟩
  have h00 : legal 0 0 := hcl.inject (0, 0) (by decide)
  have h11 : legal 1 1 := hcl.inject (1, 1) (by decide)
  have h30 : legal 3 0 := hcl.inject (3, 0) (by decide)
  have hE1 : E 1 := by
    obtain ⟨q, hq, hE⟩ := hconn 0 0 h00 rfl
    rw [show twoNodes.route 0 0 = [(1, 0)] from rfl, List.mem_singleton] at hq
    subst hq; exact hE
  have h0or3 : E 3 ∨ E 0 := by
    obtain ⟨q, hq, hE⟩ := hconn 1 1 h11 rfl
    rw [show twoNodes.route 1 1 = [(3, 1), (0, 1)] from rfl] at hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Or.inl hE
    · rw [List.mem_singleton] at hq; subst hq; exact Or.inr hE
  rcases h0or3 with hE3 | hE0
  · have d31 : twoNodes.ExtDep legal E 3 1 :=
      ⟨(3, 0), NE.base h30 hE3, rfl, 0, by decide, hE1⟩
    have d13 : twoNodes.ExtDep legal E 1 3 :=
      ⟨(1, 1), NE.base h11 hE1, rfl, 1, by decide, hE3⟩
    exact hwf.asymmetric 3 1 d13 d31
  · have d01 : twoNodes.ExtDep legal E 0 1 :=
      ⟨(0, 0), NE.base h00 hE0, rfl, 0, by decide, hE1⟩
    have d10 : twoNodes.ExtDep legal E 1 0 :=
      ⟨(1, 1), NE.base h11 hE1, rfl, 1, by decide, hE0⟩
    exact hwf.asymmetric 0 1 d10 d01

/-- **Duato's condition is not necessary for wormhole deadlock freedom.** -/
theorem duato_not_necessary_wormhole : ∃ N : Network ℕ ℕ, N.WormholeDeadlockFree ∧
    ¬ ∃ (legal : ℕ → ℕ → Prop) (E : ℕ → Prop), N.Closed legal ∧
      (∀ c p, legal c p → N.arrived c p = false → ∃ q ∈ N.route c p, E q.1) ∧
      WellFounded (flip (N.ExtDep legal E)) :=
  ⟨twoNodes, twoNodes_wormholeDeadlockFree, twoNodes_not_escape⟩

#assert_standard_axioms twoNodes_wormholeDeadlockFree twoNodes_not_escape
  duato_not_necessary_wormhole

end AsyncLean.Examples
