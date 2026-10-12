/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Throughput.Timed

/-!
# Packet networks in time, part 4: the networks on a graph

The networks of `GraphData` (`net`, `budgetNet`, `twoPhaseNet`) are placed on their graph
(`GraphData.placement`, with the `Fits` lemmas); their fluid network has two channels, capacity
`2`, on every link between neighbours (`GraphData.placement_cap`).
-/

namespace AsyncLean

/-! ### The networks on a graph -/

/-- The channels of a finite graph are finitely many. -/
instance GChan.instFintype {V : Type*} [Fintype V] : Fintype (GChan V) :=
  Fintype.ofEquiv (V ⊕ V × V × Bool)
    { toFun := fun x => match x with
        | .inl u => .inj u
        | .inr (u, v, b) => .link u v b
      invFun := fun c => match c with
        | .inj u => .inl u
        | .link u v b => .inr (u, v, b)
      left_inv := by rintro (u | ⟨u, v, b⟩) <;> rfl
      right_inv := by rintro (u | ⟨u, v, b⟩) <;> rfl }

namespace GraphData

open Network Finset

variable {P V : Type*} [DecidableEq V] (G : GraphData V)

/-- The link of a channel: the link channels between neighbours, none otherwise. -/
def chanLink : GChan V → Option (V × V)
  | .inj _ => none
  | .link u v _ => if v ∈ G.nbrs u then some (u, v) else none

/-- **A network on the graph, placed on it**: a packet is at the head of its channel, and the
links are those between neighbours. -/
def placement {N : Network (GChan V) P} (dest : P → V)
    (harr : ∀ c p, N.arrived c p = true → c.head = dest p) : N.Placement V where
  pos := GChan.head
  dest := dest
  link := G.chanLink
  arrived := harr

/-- The placement fits when every hop follows an edge of the graph and keeps the
destination. -/
theorem placement_fits {N : Network (GChan V) P} (dest : P → V)
    (harr : ∀ c p, N.arrived c p = true → c.head = dest p)
    (hroute : ∀ c p q, N.arrived c p = false → q ∈ N.route c p →
      (∃ v ∈ G.nbrs c.head, ∃ vc, q.1 = .link c.head v vc) ∧ dest q.2 = dest p) :
    (G.placement dest harr).Fits := by
  intro c p q ha hq
  obtain ⟨⟨v, hv, vc, hq1⟩, hd⟩ := hroute c p q ha hq
  refine ⟨?_, hd⟩
  show G.chanLink q.1 = some (c.head, q.1.head)
  rw [hq1]
  exact ite_eq_left hv

/-- **The fluid network of a network on the graph**: two channels, capacity `2`, on every link
between neighbours. -/
theorem placement_cap [Fintype V] {N : Network (GChan V) P} (dest : P → V)
    (harr : ∀ c p, N.arrived c p = true → c.head = dest p) (u v : V) :
    (G.placement dest harr).net.cap u v = if v ∈ G.nbrs u then 2 else 0 := by
  show ((univ.filter fun c => G.chanLink c = some (u, v)).card : ℚ) = _
  have key : ∀ c : GChan V, G.chanLink c = some (u, v) ↔
      v ∈ G.nbrs u ∧ (c = .link u v false ∨ c = .link u v true) := by
    intro c
    rcases c with w | ⟨a, b, vc⟩
    · simp [chanLink]
    · show (if b ∈ G.nbrs a then some (a, b) else none) = some (u, v) ↔ _
      by_cases hb : b ∈ G.nbrs a
      · rw [ite_eq_left hb]
        cases vc <;> simp only [Option.some.injEq, Prod.mk.injEq, GChan.link.injEq] <;>
          constructor <;> (try rintro ⟨rfl, rfl⟩) <;> simp_all
      · rw [ite_eq_right hb]
        simp only [reduceCtorEq, false_iff, not_and, GChan.link.injEq]
        rintro hv (⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩) <;> exact hb hv
  split_ifs with h
  · have e : (univ.filter fun c => G.chanLink c = some (u, v)) =
        {GChan.link u v false, GChan.link u v true} := by
      ext c
      rw [Finset.mem_filter, key]
      simp [h]
    rw [e, card_pair (by simp)]
    norm_num
  · have e : (univ.filter fun c => G.chanLink c = some (u, v)) = ∅ := by
      ext c
      rw [Finset.mem_filter, key]
      simp [h]
    rw [e]; simp

/-- The network `GraphData.net` on its graph. -/
def netPlacement : G.net.Placement V :=
  G.placement id fun c p h => by simpa [net] using h

theorem netPlacement_fits : G.netPlacement.Fits :=
  G.placement_fits id _ fun c p q ha hq => by
    obtain ⟨v, hv, vc, h1, h2⟩ := G.route_adj ha hq
    exact ⟨⟨v, hv, vc, h1⟩, by simp [h2]⟩

/-- The network `GraphData.budgetNet B` on its graph. -/
def budgetPlacement (B : ℕ) : (G.budgetNet B).Placement V :=
  G.placement Prod.fst fun c p h => by simpa [budgetNet] using h

theorem budgetPlacement_fits (B : ℕ) : (G.budgetPlacement B).Fits :=
  G.placement_fits Prod.fst _ fun c p q ha hq => by
    refine ⟨G.budget_route_adj ha hq, ?_⟩
    rcases G.mem_budgetRoute hq with rfl | ⟨v, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ <;> rfl

/-- The network `GraphData.twoPhaseNet B W` on its graph. -/
def twoPhasePlacement (B : ℕ) (W : V → V → List (Option V)) : (G.twoPhaseNet B W).Placement V :=
  G.placement Prod.fst fun c p h => by simpa [twoPhaseNet] using h

theorem twoPhasePlacement_fits (B : ℕ) (W : V → V → List (Option V)) :
    (G.twoPhasePlacement B W).Fits :=
  G.placement_fits Prod.fst _ fun c p q ha hq => by
    refine ⟨G.twoPhase_route_adj ha hq, ?_⟩
    rcases G.mem_twoPhaseRoute hq with rfl | ⟨v, -, -, ⟨-, rfl⟩ | ⟨-, -, rfl⟩⟩ <;> rfl

end GraphData

end AsyncLean
