/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.EscapeLayer

/-!
# Up*/down* routing over all the links of a graph as the escape layer

The simulations (`scripts/routing_graph_sim.py`, class `Net` with `escape='updown'`) do not
route the escape layer along the spanning tree, as `GraphData.net` does: they use **up*/down*
routing over every link of the graph**.  This file formalises that escape and proves it is an
escape layer (`GraphData.EscapeLayer`), so every theorem of `AsyncLean.Routing.EscapeLayer`
(deadlock, livelock and starvation freedom, delivery under load, history-dependent strategies,
for the detour network with bounded returns) holds for it.

## Up*/down* paths

Fix neighbour lists `nbrs` and a **key** `key : V → ℕ` on the vertices.  A hop `u → v` is **up**
if `key v < key u` and **down** if `key u < key v`.  In the simulations the key is the pair
`(level v, v)` ordered lexicographically, with `level` the breadth-first level from a root
(`GraphData.levelKey`, `GraphData.levelKey_lt_iff`); with an injective key and no self-loops
every link is up in one direction and down in the other, as in the simulation ("down" = "not
up").

* `UDPath nbrs key ph u d n` : a **legal up*/down* path** of `n` hops from `u` to `d`, over
  every link of the graph (not only tree links): zero or more up hops followed by zero or more
  down hops.  The **phase** `ph` is `true` when only down hops are allowed (the packet has
  already gone down).
* `UDReach`, `udDist` : reachability and the length of a shortest legal path.
* `udPhase key u v = decide (key u < key v)` : the phase after the hop `u → v` (down after a
  down hop, a fresh path after an up hop).
* `UDChoice nbrs key nxt` : `nxt ph u d` is a **legal next hop decreasing the up*/down*
  distance**: a neighbour of `u`, a down hop or (in phase `false`) an up hop, from which `d` is
  still reachable in the new phase, strictly closer by `udDist`.  Every first hop of a shortest
  legal path is one (`shortestHop`, `firstHop`); `firstHop` takes the first such neighbour in
  the order of `nbrs u`, the simulator's tie-break (lowest port).

## The escape (`GraphData.UpDown`)

`U : G.UpDown` on a graph `G : GraphData V` gives a key with `key (par u) < key u` off the root
(parent edges of the spanning tree are up hops: true for every breadth-first tree with the key
`(level, index)`) and a choice `nxt` satisfying `UDChoice`.  The **phase is encoded in the
channel** (`UpDown.phase`): a virtual channel 0 channel entered by a down hop allows only down
hops; a virtual channel 0 channel entered by an up hop, a virtual channel 1 channel or an
injection channel starts a fresh up*/down* path.  The escape hop of a packet in `c` for `d` is
`nxt (phase c) c.head d`.

* `UpDown.reach` : **connectivity**: every vertex reaches every destination by a legal up*/down*
  path (up the spanning tree to the root, then down it).  `UpDown.escape_reaches` : from every
  legal pair, the escape hops alone reach the destination.
* `UpDown.legal` : a pair is legal when the destination is reachable from the channel's head in
  the channel's phase (for a down channel: by down hops only).
* `UpDown.escDep_wf` : **the escape dependency relation, with the phase in the channel, is
  well-founded**: up channels by decreasing key of their head, then down channels by increasing
  key (`UpDown.ord`).
* `UpDown.esc` : the escape layer, with the escape distance `udDist` (bounded by `2 * maxKey`).
* `UpDown.ofLevels` : the escape of the simulation on any graph with a rooted tree: key
  `dep v * n + idx v` (the lexicographic order on `(dep v, idx v)` when `idx < n`), next hop the
  first neighbour starting a shortest legal path.
* `GraphData.exists_updown_correct` : **every finite connected undirected graph**, with any
  distance estimate, return budget and choice of intermediates, carries the detour network with
  up*/down* escape over a breadth-first spanning tree from any root, with key
  `(BFS level, position in the vertex list)`, and it is deadlock, livelock and starvation free
  and delivers every packet under saturation.

## What is not covered

Nothing about throughput or path lengths beyond the hop bounds.  The simulator's
`esc_stretch` and the BFS computation of its tables are not formalised; `udDist` is defined as
the length of a shortest legal path (the quantity the simulator's reverse BFS computes).
-/

namespace AsyncLean

open Network

/-! ### Up*/down* paths -/

section Paths

variable {V : Type*} (nbrs : V → List V) (key : V → ℕ)

/-- `UDPath nbrs key ph u d n` : a **legal up*/down* path** of `n` hops from `u` to `d`: up hops
(to a neighbour of smaller key) while the phase is `false`, then down hops (to a neighbour of
larger key), after which the phase is `true` and only down hops follow. -/
inductive UDPath : Bool → V → V → ℕ → Prop
  /-- The empty path, in either phase. -/
  | nil (ph : Bool) (d : V) : UDPath ph d d 0
  /-- An up hop, allowed only in phase `false`; the phase stays `false`. -/
  | up {u v d : V} {n : ℕ} (hv : v ∈ nbrs u) (hk : key v < key u) (h : UDPath false v d n) :
      UDPath false u d (n + 1)
  /-- A down hop, allowed in either phase; the phase becomes `true`. -/
  | down {ph : Bool} {u v d : V} {n : ℕ} (hv : v ∈ nbrs u) (hk : key u < key v)
      (h : UDPath true v d n) : UDPath ph u d (n + 1)

/-- `d` is reachable from `u` in phase `ph` by a legal up*/down* path. -/
def UDReach (ph : Bool) (u d : V) : Prop := ∃ n, UDPath nbrs key ph u d n

open Classical in
/-- The **up*/down* distance**: the length of a shortest legal path from `u` in phase `ph` to
`d` (`0` when there is none). -/
noncomputable def udDist (ph : Bool) (u d : V) : ℕ :=
  if h : UDReach nbrs key ph u d then Nat.find h else 0

/-- The phase after the hop `u → v`: `true` (down only) after a down hop. -/
def udPhase (u v : V) : Bool := decide (key u < key v)

/-- The hop `u → v` is allowed in phase `ph`: a down hop, or an up hop in phase `false`. -/
def UDHop (ph : Bool) (u v : V) : Prop := key u < key v ∨ ph = false ∧ key v < key u

/-- **A choice of escape hops decreasing the up*/down* distance**: for every phase `ph`, vertex
`u` and destination `d ≠ u` reachable from `u` in phase `ph`, `nxt ph u d` is a neighbour of `u`,
the hop is allowed in phase `ph`, and `d` is reachable from it in the new phase, strictly closer
by `udDist`. -/
def UDChoice (nxt : Bool → V → V → V) : Prop :=
  ∀ ph u d, u ≠ d → UDReach nbrs key ph u d →
    nxt ph u d ∈ nbrs u ∧ UDHop key ph u (nxt ph u d) ∧
      UDReach nbrs key (udPhase key u (nxt ph u d)) (nxt ph u d) d ∧
      udDist nbrs key (udPhase key u (nxt ph u d)) (nxt ph u d) d < udDist nbrs key ph u d

variable {nbrs key}

namespace UDPath

/-- A path of no hop ends where it starts. -/
theorem eq_of_zero {ph : Bool} {u d : V} (h : UDPath nbrs key ph u d 0) : u = d := by
  cases h; rfl

/-- A down-only path is legal in either phase. -/
theorem anyPhase {u d : V} {n : ℕ} (h : UDPath nbrs key true u d n) (ph : Bool) :
    UDPath nbrs key ph u d n := by
  cases h with
  | nil => exact .nil _ _
  | down hv hk h => exact .down hv hk h

/-- A down hop appended to a legal path gives a legal path. -/
theorem snoc_down {ph : Bool} {u d v : V} {n : ℕ} (h : UDPath nbrs key ph u d n)
    (hv : v ∈ nbrs d) (hk : key d < key v) : UDPath nbrs key ph u v (n + 1) := by
  induction h with
  | nil ph d => exact .down hv hk (.nil _ _)
  | up hv' hk' _ ih => exact .up hv' hk' (ih hv hk)
  | down hv' hk' _ ih => exact .down hv' hk' (ih hv hk)

/-- The first hop of a legal path is an allowed hop to a neighbour, followed by a legal path in
the new phase. -/
theorem first_hop {ph : Bool} {u d : V} {n : ℕ} (h : UDPath nbrs key ph u d (n + 1)) :
    ∃ v, v ∈ nbrs u ∧ UDHop key ph u v ∧ UDPath nbrs key (udPhase key u v) v d n := by
  cases h with
  | up hv hk h =>
    refine ⟨_, hv, Or.inr ⟨rfl, hk⟩, ?_⟩
    have : udPhase key u _ = false := decide_eq_false (Nat.not_lt.2 (Nat.le_of_lt hk))
    rw [this]; exact h
  | down hv hk h =>
    refine ⟨_, hv, Or.inl hk, ?_⟩
    have : udPhase key u _ = true := decide_eq_true hk
    rw [this]; exact h

/-- **Legal paths are short**: up hops decrease the key, down hops increase it, so a legal path
from `u` has at most `key u + M` hops, and a down-only one at most `M - key u`, when every key
is at most `M`. -/
theorem length_le {M : ℕ} (hM : ∀ v, key v ≤ M) {ph : Bool} {u d : V} {n : ℕ}
    (h : UDPath nbrs key ph u d n) : n ≤ key u + M ∧ (ph = true → n + key u ≤ M) := by
  induction h with
  | nil ph d => exact ⟨Nat.zero_le _, fun _ => by have := hM d; omega⟩
  | up _ hk _ ih => exact ⟨by have := ih.1; omega, fun h => absurd h (by simp)⟩
  | down _ hk _ ih =>
    have := ih.2 rfl
    exact ⟨by omega, fun _ => by omega⟩

end UDPath

open Classical in
/-- A shortest legal path. -/
theorem udDist_spec {ph : Bool} {u d : V} (h : UDReach nbrs key ph u d) :
    UDPath nbrs key ph u d (udDist nbrs key ph u d) := by
  unfold udDist
  rw [dite_eq_left h]
  exact Nat.find_spec h

open Classical in
/-- `udDist` is at most the length of every legal path. -/
theorem udDist_le {ph : Bool} {u d : V} {n : ℕ} (h : UDPath nbrs key ph u d n) :
    udDist nbrs key ph u d ≤ n := by
  unfold udDist
  rw [dite_eq_left ⟨n, h⟩]
  exact Nat.find_min' _ h

/-- A destination other than the start is at positive up*/down* distance. -/
theorem udDist_pos {ph : Bool} {u d : V} (hne : u ≠ d) (h : UDReach nbrs key ph u d) :
    0 < udDist nbrs key ph u d := by
  have hs := udDist_spec h
  rcases hz : udDist nbrs key ph u d with _ | n
  · rw [hz] at hs; exact absurd hs.eq_of_zero hne
  · omega

/-- The up*/down* distance is at most `key u + M` when every key is at most `M`. -/
theorem udDist_le_key {M : ℕ} (hM : ∀ v, key v ≤ M) (ph : Bool) (u d : V) :
    udDist nbrs key ph u d ≤ key u + M := by
  by_cases h : UDReach nbrs key ph u d
  · exact ((udDist_spec h).length_le hM).1
  · simp [udDist, h]

/-! ### Choices of the next hop -/

/-- A neighbour `v` of `u` such that the hop is allowed and starts a shortest legal path. -/
def UDGood (ph : Bool) (u d v : V) : Prop :=
  UDHop key ph u v ∧ UDPath nbrs key (udPhase key u v) v d (udDist nbrs key ph u d - 1)

/-- Every reachable destination other than `u` has a first hop of a shortest legal path. -/
theorem exists_good {ph : Bool} {u d : V} (hne : u ≠ d) (h : UDReach nbrs key ph u d) :
    ∃ v, v ∈ nbrs u ∧ UDGood (nbrs := nbrs) (key := key) ph u d v := by
  have hs := udDist_spec h
  have hp := udDist_pos hne h
  obtain ⟨m, hm⟩ : ∃ m, udDist nbrs key ph u d = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp).symm⟩
  rw [hm] at hs
  obtain ⟨v, hv, hhop, hpath⟩ := hs.first_hop
  exact ⟨v, hv, hhop, by rw [hm]; exact hpath⟩

/-- A first hop of a shortest legal path decreases the up*/down* distance. -/
theorem good_spec {ph : Bool} {u d v : V} (hne : u ≠ d) (h : UDReach nbrs key ph u d)
    (hg : UDGood (nbrs := nbrs) (key := key) ph u d v) :
    UDHop key ph u v ∧ UDReach nbrs key (udPhase key u v) v d ∧
      udDist nbrs key (udPhase key u v) v d < udDist nbrs key ph u d := by
  have hp := udDist_pos hne h
  have := udDist_le hg.2
  exact ⟨hg.1, ⟨_, hg.2⟩, by omega⟩

variable (nbrs key)

open Classical in
/-- **A shortest legal next hop** (any one). -/
noncomputable def shortestHop (ph : Bool) (u d : V) : V :=
  if h : ∃ v, v ∈ nbrs u ∧ UDGood (nbrs := nbrs) (key := key) ph u d v then h.choose else u

open Classical in
/-- **The first neighbour, in the order of `nbrs u`, starting a shortest legal path**: the
simulator's tie-break (lowest port) when `nbrs u` lists the ports in order. -/
noncomputable def firstHop (ph : Bool) (u d : V) : V :=
  ((nbrs u).find? fun v => decide (UDGood (nbrs := nbrs) (key := key) ph u d v)).getD u

open Classical in
/-- Every first hop of a shortest legal path is an admissible choice. -/
theorem shortestHop_choice : UDChoice nbrs key (shortestHop nbrs key) := by
  intro ph u d hne h
  have hex := exists_good (nbrs := nbrs) (key := key) hne h
  have e : shortestHop nbrs key ph u d = hex.choose := dite_eq_left hex
  rw [e]
  exact ⟨hex.choose_spec.1, good_spec hne h hex.choose_spec.2⟩

open Classical in
/-- The first neighbour starting a shortest legal path is an admissible choice. -/
theorem firstHop_choice : UDChoice nbrs key (firstHop nbrs key) := by
  intro ph u d hne h
  obtain ⟨v, hv, hg⟩ := exists_good (nbrs := nbrs) (key := key) hne h
  unfold firstHop
  cases hf : (nbrs u).find? (fun v => decide (UDGood (nbrs := nbrs) (key := key) ph u d v)) with
  | none =>
    exact absurd (decide_eq_true hg) (List.find?_eq_none.1 hf v hv)
  | some w =>
    have hw' := List.find?_some hf
    have hw := of_decide_eq_true hw'
    exact ⟨List.mem_of_find?_eq_some hf, good_spec hne h hw⟩

end Paths

/-! ### The up*/down* escape on a graph -/

namespace GraphData

variable {V : Type*} [DecidableEq V]

/-- **Up*/down* routing on the graph `G`**: a key on the vertices for which the parent edges of
the spanning tree are up hops, and a choice of escape hops decreasing the up*/down* distance
over all the links of the graph. -/
structure UpDown (G : GraphData V) where
  /-- The key: a hop `u → v` is up if `key v < key u`, down if `key u < key v`. -/
  key : V → ℕ
  /-- The parent edges of the spanning tree are up hops. -/
  key_par : ∀ u, u ≠ G.root → key (G.par u) < key u
  /-- The escape hop in phase `ph` from `u` towards `d`. -/
  nxt : Bool → V → V → V
  /-- It is a legal hop decreasing the up*/down* distance. -/
  nxt_spec : UDChoice G.nbrs key nxt

namespace UpDown

variable {G : GraphData V} (U : G.UpDown)

/-! #### Connectivity -/

omit [DecidableEq V] in
/-- Every vertex is reached from the root by a down-only path (down the spanning tree). -/
theorem reach_root (d : V) : UDReach G.nbrs U.key true G.root d := by
  suffices h : ∀ k d, U.key d = k → UDReach G.nbrs U.key true G.root d from h _ d rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hk
    by_cases hd : d = G.root
    · subst hd; exact ⟨0, .nil _ _⟩
    · have hlt := U.key_par d hd
      obtain ⟨n, hn⟩ := ih _ (hk ▸ hlt) (G.par d) rfl
      exact ⟨n + 1, hn.snoc_down (G.symm _ _ (G.par_adj d hd)) hlt⟩

omit [DecidableEq V] in
/-- **The up*/down* escape is connected**: every vertex reaches every destination by a legal
up*/down* path (up the spanning tree to the root, then down it). -/
theorem reach (u d : V) : UDReach G.nbrs U.key false u d := by
  suffices h : ∀ k u, U.key u = k → UDReach G.nbrs U.key false u d from h _ u rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro u hk
    by_cases hu : u = G.root
    · subst hu
      obtain ⟨n, hn⟩ := U.reach_root d
      exact ⟨n, hn.anyPhase false⟩
    · have hlt := U.key_par u hu
      obtain ⟨n, hn⟩ := ih _ (hk ▸ hlt) (G.par u) rfl
      exact ⟨n + 1, .up (G.par_adj u hu) hlt hn⟩

/-! #### The phase in the channel -/

/-- The phase of a packet in a channel: `true` (down hops only) in a virtual channel 0 channel
entered by a down hop; `false` (a fresh up*/down* path) in a virtual channel 0 channel entered
by an up hop, a virtual channel 1 channel or an injection channel. -/
def phase : GChan V → Bool
  | .link u v false => udPhase U.key u v
  | _ => false

/-- The legal pairs: the destination is reachable from the head of the channel in its phase. -/
def legal (c : GChan V) (d : V) : Prop := UDReach G.nbrs U.key (U.phase c) c.head d

/-- The next vertex of the escape hop. -/
def next (c : GChan V) (d : V) : V := U.nxt (U.phase c) c.head d

/-- The largest key. -/
def maxKey : ℕ := G.verts.foldr (fun v m => max (U.key v) m) 0

omit [DecidableEq V] in
/-- Every key is at most `maxKey`. -/
theorem key_le (v : V) : U.key v ≤ U.maxKey := by
  have : ∀ l : List V, v ∈ l → U.key v ≤ l.foldr (fun v m => max (U.key v) m) 0 := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons a l ih =>
      rcases List.mem_cons.1 hl with rfl | hl
      · exact le_max_left _ _
      · exact (ih hl).trans (le_max_right _ _)
  exact this _ (G.mem_verts v)

/-- The order of the escape channels: down channels first, by decreasing key of their head,
then up channels by increasing key of their head, then the other channels.  An escape
dependency goes from an up channel to an up channel of smaller key or to a down channel, and
from a down channel only to a down channel of larger key. -/
def ord : GChan V → ℕ × ℕ
  | .link u v false => if U.key u < U.key v then (0, U.maxKey - U.key v) else (1, U.key v)
  | _ => (2, 0)

omit [DecidableEq V] in
theorem legal_iff (c : GChan V) (d : V) :
    U.legal c d ↔ UDReach G.nbrs U.key (U.phase c) c.head d := Iff.rfl

omit [DecidableEq V] in
/-- Injection and virtual channel 1 channels are legal (fresh paths, by connectivity). -/
theorem legal_of_not_esc {c : GChan V} (hc : c.isEsc = false) (d : V) : U.legal c d := by
  rcases c with s | ⟨u, v, _ | _⟩
  · exact U.reach s d
  · simp [GChan.isEsc] at hc
  · exact U.reach v d

omit [DecidableEq V] in
/-- The escape hop from a legal pair: a neighbour, an allowed hop in the channel's phase, a
legal pair, closer by the up*/down* distance. -/
theorem next_spec {c : GChan V} {d : V} (hl : U.legal c d) (h : c.head ≠ d) :
    U.next c d ∈ G.nbrs c.head ∧ UDHop U.key (U.phase c) c.head (U.next c d) ∧
      U.legal (.link c.head (U.next c d) false) d ∧
      udDist G.nbrs U.key (U.phase (.link c.head (U.next c d) false)) (U.next c d) d <
        udDist G.nbrs U.key (U.phase c) c.head d :=
  U.nxt_spec (U.phase c) c.head d h hl

omit [DecidableEq V] in
/-- **The escape hop decreases the order of the channels.** -/
theorem ord_lt {c : GChan V} {d : V} (hl : U.legal c d) (h : c.head ≠ d) :
    Prod.Lex (· < ·) (· < ·) (U.ord (.link c.head (U.next c d) false)) (U.ord c) := by
  obtain ⟨-, hhop, -, -⟩ := U.next_spec hl h
  have hle := U.key_le (U.next c d)
  have hnew : ∀ u v : V, U.ord (.link u v false) =
      if U.key u < U.key v then (0, U.maxKey - U.key v) else (1, U.key v) := fun _ _ => rfl
  generalize U.next c d = v at hhop hle ⊢
  rw [hnew]
  rcases c with s | ⟨x, u, _ | _⟩
  · show Prod.Lex _ _ _ (2, 0)
    split_ifs <;> exact Prod.Lex.left _ _ (by omega)
  · have hph : U.phase (.link x u false) = decide (U.key x < U.key u) := rfl
    rw [hph] at hhop
    simp only [GChan.head] at hhop
    rw [show U.ord (.link x u false) =
      if U.key x < U.key u then (0, U.maxKey - U.key u) else (1, U.key u) from rfl]
    split_ifs with hd hxu hxu <;> simp only [GChan.head] at hd
    · rw [Prod.lex_def]; right; exact ⟨rfl, by omega⟩
    · exact Prod.Lex.left _ _ (by omega)
    · exfalso
      rcases hhop with h1 | ⟨h1, -⟩
      · exact hd h1
      · simp [hxu] at h1
    · rcases hhop with h1 | ⟨-, h1⟩
      · exact absurd h1 hd
      · rw [Prod.lex_def]; right; exact ⟨rfl, h1⟩
  · show Prod.Lex _ _ _ (2, 0)
    split_ifs <;> exact Prod.Lex.left _ _ (by omega)

/-- **The escape dependency relation of up*/down* routing**, with the phase in the channel: a
packet in `c` for a destination `d` it can legally reach may request the escape channel
`c.head → next c d`. -/
def EscDep (c c' : GChan V) : Prop :=
  ∃ d, U.legal c d ∧ c.head ≠ d ∧ c' = .link c.head (U.next c d) false

omit [DecidableEq V] in
/-- **The escape dependency relation is well-founded** (acyclic). -/
theorem escDep_wf : WellFounded (flip U.EscDep) :=
  Network.wf_of_lexRank U.ord fun _ _ ⟨_, hl, h, e⟩ => e ▸ U.ord_lt hl h

/-- **The up*/down* escape layer**: escape distance the up*/down* distance from the channel's
head in its phase, below `2 * maxKey + 1`. -/
noncomputable def esc : G.EscapeLayer where
  next := U.next
  legal := U.legal
  legal_inj s d := U.legal_of_not_esc rfl d
  legal_adapt _ _ d := U.legal_of_not_esc rfl d
  next_adj _ _ hl h := (U.next_spec hl h).1
  legal_next _ _ hl h := (U.next_spec hl h).2.2.1
  ord := U.ord
  ord_lt _ _ hl h := U.ord_lt hl h
  edist c d := udDist G.nbrs U.key (U.phase c) c.head d
  edist_lt _ _ _ hl h := (U.next_spec hl h).2.2.2
  bound := 2 * U.maxKey + 1
  edist_lt_bound u v d _ := by
    have := udDist_le_key (nbrs := G.nbrs) U.key_le (U.phase (.link u v false)) v d
    have := U.key_le v
    show udDist _ _ _ v d < _
    omega

omit [DecidableEq V] in
/-- **From every legal pair the escape hops alone reach the destination**, within the up*/down*
distance, through legal pairs. -/
theorem escape_reaches {c : GChan V} {d : V} (hl : U.legal c d) :
    ∃ c', Relation.ReflTransGen (fun a b => U.legal a d ∧ a.head ≠ d ∧
      b = .link a.head (U.next a d) false) c c' ∧ c'.head = d := by
  suffices h : ∀ n c, udDist G.nbrs U.key (U.phase c) c.head d = n → U.legal c d →
      ∃ c', Relation.ReflTransGen (fun a b => U.legal a d ∧ a.head ≠ d ∧
        b = .link a.head (U.next a d) false) c c' ∧ c'.head = d from h _ c rfl hl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hn hl
    by_cases hd : c.head = d
    · exact ⟨c, .refl, hd⟩
    · obtain ⟨-, -, hl', hlt⟩ := U.next_spec hl hd
      obtain ⟨c', hp, hc'⟩ := ih _ (hn ▸ hlt) _ rfl hl'
      exact ⟨c', .head ⟨hl, hd, rfl⟩ hp, hc'⟩

end UpDown

/-! ### Breadth-first levels -/

/-- The depth of a vertex is the length of a walk from the root (along the parent edges). -/
theorem walkLen_dep (G : GraphData V) (u : V) : WalkLen G.nbrs G.root (G.dep u) u := by
  suffices h : ∀ k u, G.dep u = k → WalkLen G.nbrs G.root k u from h _ u rfl
  intro k
  induction k with
  | zero => intro u hu; exact G.eq_root_of_dep hu
  | succ k ih =>
    intro u hu
    have hr : u ≠ G.root := fun h => by rw [h, G.dep_root] at hu; omega
    have := G.dep_par u hr
    exact walkLen_succ.2 ⟨G.par u, ih _ (by omega), G.symm _ _ (G.par_adj u hr)⟩

/-- **The depth is the breadth-first level** when it grows by at most one along every edge:
then it is the length of a shortest walk from the root. -/
theorem dep_isLeast_walk (G : GraphData V) (hnb : ∀ u v, v ∈ G.nbrs u → G.dep v ≤ G.dep u + 1)
    (u : V) : WalkLen G.nbrs G.root (G.dep u) u ∧ ∀ n, WalkLen G.nbrs G.root n u → G.dep u ≤ n := by
  refine ⟨G.walkLen_dep u, fun n h => ?_⟩
  induction n generalizing u with
  | zero => have : u = G.root := h; rw [this, G.dep_root]
  | succ n ih =>
    obtain ⟨v, hv, huv⟩ := walkLen_succ.1 h
    have := ih v hv
    have := hnb v u huv
    omega

/-! ### The key of the simulation -/

/-- The key `(dep v, idx v)`, lexicographically, as a number: `dep v * n + idx v`.  With `dep`
the breadth-first level from the root and `idx` the vertex number, it is the key
`(level[v], v)` of the simulation. -/
def levelKey (G : GraphData V) (idx : V → ℕ) (n : ℕ) (v : V) : ℕ := G.dep v * n + idx v

omit [DecidableEq V] in
/-- With `idx < n`, the key compares `(dep, idx)` lexicographically. -/
theorem levelKey_lt_iff (G : GraphData V) {idx : V → ℕ} {n : ℕ} (hidx : ∀ v, idx v < n)
    (u v : V) : G.levelKey idx n v < G.levelKey idx n u ↔
      G.dep v < G.dep u ∨ G.dep v = G.dep u ∧ idx v < idx u := by
  have hkey : ∀ a b : V, G.dep a < G.dep b → G.levelKey idx n a < G.levelKey idx n b := by
    intro a b h
    have h1 : (G.dep a + 1) * n ≤ G.dep b * n := Nat.mul_le_mul_right _ h
    have h2 := hidx a
    rw [Nat.add_mul, Nat.one_mul] at h1
    unfold levelKey; omega
  constructor
  · intro h
    rcases lt_trichotomy (G.dep v) (G.dep u) with h' | h' | h'
    · exact Or.inl h'
    · right; refine ⟨h', ?_⟩; unfold levelKey at h; rw [h'] at h; omega
    · exact absurd (hkey u v h') (by omega)
  · rintro (h | ⟨h, h'⟩)
    · exact hkey v u h
    · unfold levelKey; rw [h]; omega

omit [DecidableEq V] in
/-- With `idx < n`, the parent edges are up hops for the key `(dep, idx)`. -/
theorem levelKey_par (G : GraphData V) {idx : V → ℕ} {n : ℕ} (hidx : ∀ v, idx v < n) (u : V)
    (hu : u ≠ G.root) : G.levelKey idx n (G.par u) < G.levelKey idx n u :=
  (G.levelKey_lt_iff hidx u (G.par u)).2 (Or.inl (by have := G.dep_par u hu; omega))

/-- **The up*/down* escape of the simulation** on a graph with a rooted spanning tree: key
`(dep, idx)` lexicographically (with `idx < n`), escape hop the first neighbour in the order of
`nbrs` starting a shortest legal up*/down* path. -/
noncomputable def UpDown.ofLevels (G : GraphData V) (idx : V → ℕ) (n : ℕ)
    (hidx : ∀ v, idx v < n) : G.UpDown where
  key := G.levelKey idx n
  key_par := G.levelKey_par hidx
  nxt := firstHop G.nbrs (G.levelKey idx n)
  nxt_spec := firstHop_choice _ _

/-- **Every finite connected undirected graph carries a correct adaptive network with an
up*/down* escape**: with any distance estimate `dist`, any return budget `B`, any choice of
intermediates `W` and any root `r`, the detour network with up*/down* routing as the escape
layer, over a breadth-first spanning tree from `r` with the key (BFS level, position in the
vertex list) and the first shortest legal next hop, is deadlock and livelock free under every
valid selection, starvation free under strongly fair scheduling, and delivers every packet
along every channel-fair run under every valid selection. -/
theorem exists_updown_correct (verts : List V) (mem_verts : ∀ v, v ∈ verts)
    (nbrs : V → List V) (symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v) (dist : V → V → ℕ) (r : V)
    (conn : ∀ u, Relation.ReflTransGen (fun a b => b ∈ nbrs a) r u) (B : ℕ)
    (W : V → V → List (Option V)) :
    ∃ G : GraphData V, ∃ U : G.UpDown, G.nbrs = nbrs ∧ G.dist = dist ∧ G.root = r ∧
      G.dep = bfsDep conn ∧ (∀ v, U.key v = G.dep v * verts.length + verts.idxOf v) ∧
      U.nxt = firstHop nbrs U.key ∧
      (U.esc.net B W).Correct ∧ (U.esc.net B W).StarvationFree ∧
      ∀ sel, (U.esc.net B W).ValidSel sel →
        (U.esc.net B W).StarvationFreeUnderLoad sel (fun _ => False) :=
  let G := GraphData.ofConnected verts mem_verts nbrs symm dist r conn
  let U := UpDown.ofLevels G (fun v => verts.idxOf v) verts.length
    (fun v => List.idxOf_lt_length_of_mem (mem_verts v))
  ⟨G, U, rfl, rfl, rfl, rfl, fun _ => rfl, rfl, (U.esc.correct B W).1, (U.esc.correct B W).2,
    fun _ hsel => EscapeLayer.underLoad hsel⟩

end GraphData

end AsyncLean
