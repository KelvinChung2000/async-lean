/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.Routing

/-!
# Example: maximally adaptive deadlock-free routing on a mesh

How adaptive can deadlock-free minimal routing on a mesh with two virtual channels be?  Take as
the yardstick `minimalHops k`: every *productive* hop (one that brings the packet closer to its
destination) on either virtual channel.  Every routing function within it is minimal, so every
packet takes a shortest path, and the question is which sets of these hops are deadlock free.

* `duatoMesh` (`AsyncLean.Examples.Routing`) offers every productive hop on virtual channel 1,
  but only the XY hop on virtual channel 0.  It is **not** maximally adaptive
  (`duatoMesh_not_maximal`): virtual channel 0 can carry more.
* `turnDuatoMesh turn k` keeps the XY escape hop and fully adaptive virtual channel 1, and lets
  virtual channel 0 also offer every hop of a *turn model* `turn` (Glass and Ni).  With the
  west-first model (`westFirstMesh`), a packet that does not have to go west may take any
  productive hop on either virtual channel; with north-last (`northLastMesh`), a packet that
  does not have to go north may.  Both strictly extend `duatoMesh` (`duatoMesh_extends`,
  `duatoMesh_lt_westFirstMesh`), are minimal (`turnDuatoMesh_within`), and are deadlock free,
  livelock free and starvation free, under store-and-forward and wormhole switching.
* Both are **maximally adaptive** (`westFirstMesh_maximal`, `northLastMesh_maximal`): adding
  *any* set of productive hops to them, at a pair their packets can occupy, introduces a
  deadlock.  No improvement in adaptivity is possible without giving up deadlock freedom.
* They are incomparable, and **no deadlock-free routing function is at least as adaptive as
  both** (`no_common_improvement`).  So there is no "most adaptive" deadlock-free minimal
  routing to look for: there are several maximal ones, and the turn-model escapes reach them.
* Fully adaptive minimal routing on both virtual channels (`minimalMesh`, the yardstick
  itself) deadlocks (`minimalMesh_deadlocks`).

The maximality proofs are checked by the kernel: `async_decide` finds, for every hop that could
be added, a run into a configuration that is deadlocked whatever else is added
(`Network.maximallyAdaptive_of_maxCheck`).
-/

namespace AsyncLean.Examples

open Network Mesh

namespace Mesh

/-- The west-first turn model: a packet that still has to go west goes west; otherwise it may
take any productive direction. -/
def westFirst (k u d : ℕ) : List ℕ := if d % k < u % k then [1] else productive k u d

/-- The north-last turn model: a packet goes north only when north is the only productive
direction left; until then it may take any other productive direction. -/
def northLast (k u d : ℕ) : List ℕ :=
  if productive k u d = [2] then [2] else (productive k u d).filter (· ≠ 2)

/-- Every productive hop, on either virtual channel. -/
def minimalHops (k c d : ℕ) : List (ℕ × ℕ) :=
  let u := head k c
  (productive k u d).map (fun dr => (ch u dr 0, d)) ++ (productive k u d).map fun dr => (ch u dr 1, d)

theorem xy_mem_productive {k u d : ℕ} (h : u ≠ d) : xy k u d ∈ productive k u d := by
  unfold xy productive
  by_cases h1 : u % k < d % k
  · simp [h1]
  by_cases h2 : d % k < u % k
  · simp [h1, h2]
  by_cases h3 : u / k < d / k
  · simp [h1, h2, h3]
  have h4 : d / k < u / k := by
    refine Nat.lt_of_le_of_ne (by omega) fun he => h ?_
    rw [← Nat.div_add_mod u k, ← Nat.div_add_mod d k, he, show u % k = d % k by omega]
  simp [h1, h2, h3, h4]

theorem westFirst_sub {k u d dr : ℕ} (h : dr ∈ westFirst k u d) : dr ∈ productive k u d := by
  unfold westFirst at h
  split_ifs at h with hw
  · rw [List.mem_singleton] at h
    subst h
    simp [productive, hw]
  · exact h

theorem northLast_sub {k u d dr : ℕ} (h : dr ∈ northLast k u d) : dr ∈ productive k u d := by
  unfold northLast at h
  split_ifs at h with hn
  · rwa [hn]
  · exact (List.mem_filter.1 h).1

end Mesh

/-- Duato's mesh with a turn-model escape layer: virtual channel 0 offers the XY hop (listed
first: the escape hop) and every hop of the turn model `turn`; virtual channel 1 offers every
productive hop. -/
def turnDuatoMesh (turn : ℕ → ℕ → ℕ → List ℕ) (k : ℕ) : Network ℕ ℕ where
  arrived c d := head k c == d
  route c d :=
    let u := head k c
    (ch u (xy k u d) 0, d) :: ((turn k u d).filter (· ≠ xy k u d)).map (fun dr => (ch u dr 0, d))
      ++ (productive k u d).map fun dr => (ch u dr 1, d)
  inject := allPairs (k * k) fun s => ch s 4 0

/-- Duato's mesh with a west-first escape layer. -/
abbrev westFirstMesh (k : ℕ) : Network ℕ ℕ := turnDuatoMesh westFirst k

/-- Duato's mesh with a north-last escape layer. -/
abbrev northLastMesh (k : ℕ) : Network ℕ ℕ := turnDuatoMesh northLast k

/-- Every productive hop on both virtual channels. -/
def minimalMesh (k : ℕ) : Network ℕ ℕ where
  arrived c d := head k c == d
  route := minimalHops k
  inject := allPairs (k * k) fun s => ch s 4 0

/-! ### Correctness -/

/-- Fully adaptive minimal routing on both virtual channels deadlocks: eight packets, two in each
channel of the square of nodes 0, 1, 4 and 3, each with a single productive direction. -/
theorem minimalMesh_deadlocks : ¬ (minimalMesh 3).DeadlockFree :=
  Network.not_deadlockFree_of_refuteB
    (as := [.inject 8 4, .hop 8 1 4, .inject 38 1, .hop 38 37 1, .inject 38 1, .hop 38 36 1,
      .inject 48 0, .hop 48 43 0, .inject 48 0, .hop 48 42 0, .inject 18 3, .hop 18 15 3,
      .inject 18 3, .hop 18 14 3, .inject 8 4, .hop 8 0 4])
    (by decide +kernel)

theorem westFirstMesh_correct : (westFirstMesh 4).Correct := by async_decide
theorem northLastMesh_correct : (northLastMesh 4).Correct := by async_decide
theorem westFirstMesh_starvationFree : (westFirstMesh 4).StarvationFree := by async_decide
theorem westFirstMesh_wormholeCorrect : (westFirstMesh 4).WormholeCorrect := by async_decide

theorem westFirstMesh_correct_3 : (westFirstMesh 3).Correct := by async_decide
theorem northLastMesh_correct_3 : (northLastMesh 3).Correct := by async_decide

/-! ### Comparing adaptivity -/

/-- **Duato's mesh is a sub-routing of every turn-model mesh**, for every size. -/
theorem duatoMesh_extends (turn : ℕ → ℕ → ℕ → List ℕ) (k : ℕ) :
    (duatoMesh k).Extends (turnDuatoMesh turn k) :=
  ⟨rfl, rfl, fun c d q _ hq => by
    simp only [duatoMesh, turnDuatoMesh, List.mem_cons, List.mem_append] at hq ⊢
    tauto⟩

/-- **The turn-model meshes are minimal**, for every size: every hop is productive. -/
theorem turnDuatoMesh_within {turn : ℕ → ℕ → ℕ → List ℕ} (k : ℕ)
    (hturn : ∀ u d dr, dr ∈ turn k u d → dr ∈ productive k u d) :
    (turnDuatoMesh turn k).Within (minimalHops k) := by
  intro c d q ha hq
  have hne : head k c ≠ d := by simpa [turnDuatoMesh] using ha
  simp only [turnDuatoMesh, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter]
    at hq
  simp only [minimalHops, List.mem_append, List.mem_map]
  rcases hq with (rfl | ⟨dr, ⟨hdr, -⟩, rfl⟩) | ⟨dr, hdr, rfl⟩
  · exact Or.inl ⟨_, xy_mem_productive hne, rfl⟩
  · exact Or.inl ⟨dr, hturn _ _ _ hdr, rfl⟩
  · exact Or.inr ⟨dr, hdr, rfl⟩

/-- A packet injected at node 0 for node 4 (one hop east and one north) may go north on
virtual channel 0 in the west-first mesh, but not in Duato's mesh. -/
theorem duatoMesh_lt_westFirstMesh :
    (ch 0 2 0, 4) ∈ (westFirstMesh 3).route (ch 0 4 0) 4 ∧
      (ch 0 2 0, 4) ∉ (duatoMesh 3).route (ch 0 4 0) 4 := by decide

/-- **Duato's mesh is not maximally adaptive**: the west-first mesh is deadlock free and permits
strictly more hops. -/
theorem duatoMesh_not_maximal : ¬ (duatoMesh 3).MaximallyAdaptive (minimalHops 3) :=
  not_maximallyAdaptive_of_extends (duatoMesh_extends westFirst 3)
    (turnDuatoMesh_within 3 fun _ _ _ => westFirst_sub) westFirstMesh_correct_3.1
    (pairReachable_of_mem_inject (by decide)) (by decide) duatoMesh_lt_westFirstMesh.1
    duatoMesh_lt_westFirstMesh.2

/-! ### Maximality -/

/-- **The west-first mesh is maximally adaptive**: any deadlock-free minimal routing function
that permits all its hops permits no other. -/
theorem westFirstMesh_maximal : (westFirstMesh 3).MaximallyAdaptive (minimalHops 3) := by
  async_decide

/-- **The north-last mesh is maximally adaptive** as well. -/
theorem northLastMesh_maximal : (northLastMesh 3).MaximallyAdaptive (minimalHops 3) := by
  async_decide

/-- The two are incomparable: a packet injected at node 4 for node 0 may go south first on
virtual channel 0 in the north-last mesh, but must go west first in the west-first mesh; a
packet injected at node 0 for node 4 may go north first in the west-first mesh, but not in the
north-last mesh. -/
theorem westFirst_northLast_incomparable :
    (ch 4 3 0, 0) ∈ (northLastMesh 3).route (ch 4 4 0) 0 ∧
      (ch 4 3 0, 0) ∉ (westFirstMesh 3).route (ch 4 4 0) 0 ∧
      (ch 0 2 0, 4) ∈ (westFirstMesh 3).route (ch 0 4 0) 4 ∧
      (ch 0 2 0, 4) ∉ (northLastMesh 3).route (ch 0 4 0) 4 := by decide

/-- **No common improvement**: no deadlock-free minimal routing function is at least as adaptive
as both the west-first and the north-last mesh.  There is no most adaptive deadlock-free
routing to be found: the maximal ones are incomparable. -/
theorem no_common_improvement (N : Network ℕ ℕ) (h₁ : (westFirstMesh 3).Extends N)
    (h₂ : (northLastMesh 3).Extends N) (hU : N.Within (minimalHops 3)) : ¬ N.DeadlockFree :=
  westFirstMesh_maximal.not_deadlockFree (pairReachable_of_mem_inject (by decide)) (by decide)
    westFirst_northLast_incomparable.1 westFirst_northLast_incomparable.2.1 h₁ h₂ hU

#assert_standard_axioms minimalMesh_deadlocks westFirstMesh_correct northLastMesh_correct westFirstMesh_starvationFree
  westFirstMesh_wormholeCorrect westFirstMesh_correct_3 northLastMesh_correct_3 duatoMesh_extends
  turnDuatoMesh_within duatoMesh_lt_westFirstMesh duatoMesh_not_maximal westFirstMesh_maximal
  northLastMesh_maximal westFirst_northLast_incomparable no_common_improvement

end AsyncLean.Examples
