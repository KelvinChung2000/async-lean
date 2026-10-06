/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
import AsyncLean.AxiomAudit

/-!
# Example: deadlock and livelock freedom of dynamically routed networks

Packet-switched networks with one-packet channel buffers (`AsyncLean.Routing.Basic`).  Each
channel is a directed link, or a virtual channel on a link; a packet header is its
destination node (plus a misrouting budget in `misrouteMesh`).  The statements hold for
**every** work-conserving selection function, so for every dynamic routing policy.

* `ring` — a unidirectional ring with one channel per link deadlocks (`ring_deadlocks`):
  four packets, each waiting for the channel held by the next.
* `datelineRing` — the same ring with two virtual channels and a dateline (Dally and Seitz)
  is deadlock and livelock free, checked for 8 nodes (`datelineRing_correct_8`) and proved
  for **every** size (`datelineRing_correct`).
* `xyMesh` — dimension-order (XY) routing on a 4×4 mesh: an acyclic channel dependency graph.
* `adaptiveMesh` — fully adaptive minimal routing on one virtual channel deadlocks
  (`adaptiveMesh_deadlocks`).
* `duatoMesh` — fully adaptive minimal routing on virtual channel 1 with XY routing on
  virtual channel 0 as escape channels.  Its dependency graph has cycles, yet it is deadlock
  free by Duato's theorem (`duatoMesh_correct`).
* `misrouteMesh` — non-minimal adaptive routing, where a packet may take up to `b`
  unproductive hops, is livelock free because the budget bounds the detours
  (`misrouteMesh_correct`).  With unbounded misrouting (`deflectionMesh`) a packet can bounce
  between two nodes forever (`deflectionMesh_livelocks`).
-/

namespace AsyncLean.Examples

open Network

/-- Every source `s < n` injects packets for every other destination into channel `ch s`. -/
def allPairs (n : ℕ) (ch : ℕ → ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun s => ((List.range n).filter (· ≠ s)).map fun d => (ch s, d)

/-! ### Rings -/

/-- A unidirectional ring of `n` nodes: channel `i` is the link from node `i` to node
`i + 1 mod n`; packets carry their destination. -/
def ring (n : ℕ) : Network ℕ ℕ where
  arrived c d := (c + 1) % n == d
  route c d := [((c + 1) % n, d)]
  inject := allPairs n id

/-- Its channel dependency graph is a cycle, and the cycle can be filled. -/
theorem ring_deadlocks : ¬ (ring 4).DeadlockFree :=
  Network.not_deadlockFree_of_refuteB
    (as := [.inject 1 0, .inject 2 0, .inject 3 1, .inject 0 2]) (by decide +kernel)

/-- The ring with two virtual channels per link: channel `i` (virtual channel 0) and channel
`n + i` (virtual channel 1) both lead from node `i` to node `i + 1`.  Packets start on virtual
channel 0 and move to virtual channel 1 when they cross the dateline from node `n - 1` to
node `0`. -/
def datelineRing (n : ℕ) : Network ℕ ℕ where
  arrived c d := (c % n + 1) % n == d
  route c d := let i := (c % n + 1) % n; [(if i = 0 then n else i + n * (c / n), d)]
  inject := allPairs n id

theorem datelineRing_correct_8 : (datelineRing 8).Correct := by async_decide

/-! #### Every dateline ring is correct

The legal pairs, the hops still to go and the position of each channel in the (acyclic)
dependency order, in closed form. -/

/-- The pairs packets can occupy: on virtual channel 1, packets have not passed their
destination. -/
def dlLegal (n c d : ℕ) : Prop := d < n ∧ (c < n ∨ (n ≤ c ∧ c < n + d))

/-- The number of hops still to go. -/
def dlRank (n c d : ℕ) : ℕ :=
  if c < n then (if c < d then d - c - 1 else n - c - 1 + d) else d + n - c - 1

/-- Channels in dependency order: virtual channel 0 from node 0 up, then virtual channel 1. -/
def dlChan (n c : ℕ) : ℕ := 2 * n - c

/-- One hop of the dateline ring from a legal pair: along virtual channel 0, across the
dateline onto virtual channel 1, or along virtual channel 1. -/
theorem dl_step {n c d : ℕ} (hl : dlLegal n c d) (ha : (datelineRing n).arrived c d = false) :
    (datelineRing n).route c d = [(c + 1, d)] ∧ c + 1 < n ∧ c + 1 ≠ d ∨
    (datelineRing n).route c d = [(n, d)] ∧ c + 1 = n ∧ d ≠ 0 ∨
    (datelineRing n).route c d = [(c + 1, d)] ∧ n ≤ c ∧ c + 1 < n + d := by
  have harr : (c % n + 1) % n ≠ d := by simpa [datelineRing] using ha
  have hroute : (datelineRing n).route c d =
      [(if (c % n + 1) % n = 0 then n else (c % n + 1) % n + n * (c / n), d)] := rfl
  obtain ⟨hd, hc | ⟨hc1, hc2⟩⟩ := hl
  · rw [Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc] at hroute
    rw [Nat.mod_eq_of_lt hc] at harr
    rcases Nat.lt_or_ge (c + 1) n with h | h
    · rw [Nat.mod_eq_of_lt h] at hroute harr
      exact Or.inl ⟨by rw [hroute, ite_eq_right (by omega)]; simp, h, harr⟩
    · have h1 : c + 1 = n := by omega
      rw [h1, Nat.mod_self] at hroute harr
      exact Or.inr (Or.inl ⟨by rw [hroute, ite_eq_left rfl], h1, fun h => harr h.symm⟩)
  · have hm : c % n = c - n := by
      rw [Nat.mod_eq_sub_mod hc1, Nat.mod_eq_of_lt (by omega)]
    have hv : c / n = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hm, hv] at hroute
    rw [hm] at harr
    rw [Nat.mod_eq_of_lt (by omega : c - n + 1 < n)] at hroute harr
    refine Or.inr (Or.inr ⟨?_, hc1, by omega⟩)
    rw [hroute, ite_eq_right (by omega)]
    simp only [List.cons.injEq, Prod.mk.injEq, and_true]
    omega

/-- **Every dateline ring is deadlock and livelock free**, under every dynamic routing
policy (Dally and Seitz's theorem with the dependency order `dlChan`, and the ranking
function `dlRank`). -/
theorem datelineRing_correct (n : ℕ) : (datelineRing n).Correct := by
  have hcl : (datelineRing n).Closed (dlLegal n) := by
    constructor
    · intro q hq
      simp only [datelineRing, allPairs, List.mem_flatMap, List.mem_range, List.mem_map,
        List.mem_filter] at hq
      obtain ⟨s, hs, d, ⟨hd, -⟩, rfl⟩ := hq
      exact ⟨hd, Or.inl hs⟩
    · intro c d q hl ha hq
      have hd := hl.1
      rcases dl_step hl ha with ⟨hr, h1, h2⟩ | ⟨hr, h1, h2⟩ | ⟨hr, h1, h2⟩ <;>
        rw [hr, List.mem_singleton] at hq <;> subst hq
      · exact ⟨hd, Or.inl h1⟩
      · exact ⟨hd, Or.inr ⟨le_refl _, by omega⟩⟩
      · exact ⟨hd, Or.inr ⟨by omega, by omega⟩⟩
  refine ⟨(datelineRing n).deadlockFree_of_cdg hcl ?_ (wf_of_rank (dlChan n) ?_),
    (datelineRing n).livelockFree_of_ranking hcl ?_ (dlRank n) ?_⟩
  · intro c d hl ha
    rcases dl_step hl ha with ⟨hr, -⟩ | ⟨hr, -⟩ | ⟨hr, -⟩ <;> simp [hr]
  · rintro c c' ⟨d, d', hl, ha, hq⟩
    have hd := hl.1
    rcases dl_step hl ha with ⟨hr, h1, h2⟩ | ⟨hr, h1, h2⟩ | ⟨hr, h1, h2⟩ <;>
      rw [hr, List.mem_singleton, Prod.mk.injEq] at hq <;> obtain ⟨hc', -⟩ := hq <;>
      subst hc' <;> simp only [dlChan] <;> omega
  · refine (Set.finite_lt_nat (2 * n)).subset ?_
    rintro c ⟨d, hd, hc⟩
    change c < 2 * n
    omega
  · rintro c d q hl ha hq
    have hd := hl.1
    rcases dl_step hl ha with ⟨hr, h1, h2⟩ | ⟨hr, h1, h2⟩ | ⟨hr, h1, h2⟩ <;>
      rw [hr, List.mem_singleton] at hq <;> subst hq <;> simp only [dlRank] <;>
      split_ifs <;> omega

/-! ### Meshes -/

namespace Mesh

/-- Channel `ch u dir vc` leaves node `u` in direction `dir` (`0` east, `1` west, `2` north,
`3` south, `4` the local injection channel) on virtual channel `vc`.  Node `u` of a `k × k`
mesh is at column `u % k`, row `u / k`. -/
def ch (u dir vc : ℕ) : ℕ := (u * 5 + dir) * 2 + vc

/-- The node a channel leaves. -/
def node (c : ℕ) : ℕ := c / 10

/-- The direction of a channel. -/
def dir (c : ℕ) : ℕ := c / 2 % 5

/-- The node a channel leads to. -/
def head (k c : ℕ) : ℕ :=
  match dir c with
  | 0 => node c + 1
  | 1 => node c - 1
  | 2 => node c + k
  | 3 => node c - k
  | _ => node c

/-- Dimension-order routing: correct the column first, then the row. -/
def xy (k u d : ℕ) : ℕ :=
  if u % k < d % k then 0 else if d % k < u % k then 1 else if u / k < d / k then 2 else 3

/-- The productive directions from `u` towards `d` (minimal routing). -/
def productive (k u d : ℕ) : List ℕ :=
  (if u % k < d % k then [0] else []) ++ (if d % k < u % k then [1] else []) ++
    (if u / k < d / k then [2] else []) ++ (if d / k < u / k then [3] else [])

/-- The directions leading to a neighbour of `u` inside the mesh. -/
def neighbours (k u : ℕ) : List ℕ :=
  (if u % k + 1 < k then [0] else []) ++ (if 0 < u % k then [1] else []) ++
    (if u / k + 1 < k then [2] else []) ++ (if 0 < u / k then [3] else [])

end Mesh

open Mesh

/-- XY routing on a `k × k` mesh. -/
def xyMesh (k : ℕ) : Network ℕ ℕ where
  arrived c d := head k c == d
  route c d := [(ch (head k c) (xy k (head k c) d) 0, d)]
  inject := allPairs (k * k) fun s => ch s 4 0

/-- Deterministic routing with an acyclic dependency graph (Dally and Seitz). -/
theorem xyMesh_correct : (xyMesh 4).Correct := by async_decide

/-- Fully adaptive minimal routing on a single virtual channel. -/
def adaptiveMesh (k : ℕ) : Network ℕ ℕ where
  arrived c d := head k c == d
  route c d := (productive k (head k c) d).map fun dr => (ch (head k c) dr 0, d)
  inject := allPairs (k * k) fun s => ch s 4 0

/-- Six packets around a cycle of turns, each with only blocked productive hops. -/
theorem adaptiveMesh_deadlocks : ¬ (adaptiveMesh 3).DeadlockFree :=
  Network.not_deadlockFree_of_refuteB
    (as := [.inject 88 6, .hop 88 82 6, .inject 78 0, .hop 78 72 0, .inject 68 4,
      .hop 68 66 4, .inject 38 5, .hop 38 30 5, .inject 48 8, .hop 48 40 8, .inject 58 6,
      .hop 58 54 6])
    (by decide +kernel)

/-- Duato's design: the escape hop (XY routing on virtual channel 0) is listed first, then
every productive hop on virtual channel 1. -/
def duatoMesh (k : ℕ) : Network ℕ ℕ where
  arrived c d := head k c == d
  route c d :=
    let u := head k c
    (ch u (xy k u d) 0, d) :: (productive k u d).map fun dr => (ch u dr 1, d)
  inject := allPairs (k * k) fun s => ch s 4 0

/-- **Duato's theorem at work**: the dependency graph of the full routing function has cycles,
but the escape channels make the network deadlock free; minimal routing makes it livelock
free.  `async_decide` uses the first-listed hop as the escape subfunction. -/
theorem duatoMesh_correct : (duatoMesh 4).Correct := by async_decide

/-- The same proof with the escape subfunction named explicitly. -/
example : (duatoMesh 3).DeadlockFree := by
  async_routing (escape := fun c d => [(ch (head 3 c) (xy 3 (head 3 c) d) 0, d)])

/-- Bounded misrouting: the header `d + k² · m` carries the destination `d` and a budget `m`
of unproductive hops on virtual channel 1, each of which uses up one unit. -/
def misrouteMesh (k b : ℕ) : Network ℕ ℕ where
  arrived c h := head k c == h % (k * k)
  route c h :=
    let u := head k c
    let d := h % (k * k)
    (ch u (xy k u d) 0, h) :: (productive k u d).map (fun dr => (ch u dr 1, h)) ++
      (if h / (k * k) = 0 then [] else
        ((neighbours k u).filter (· ∉ productive k u d)).map fun dr => (ch u dr 1, h - k * k))
  inject := (allPairs (k * k) fun s => ch s 4 0).map fun q => (q.1, q.2 + k * k * b)

/-- Non-minimal adaptive routing with a misrouting budget is livelock free (and deadlock free
by Duato's theorem). -/
theorem misrouteMesh_correct : (misrouteMesh 3 2).Correct := by async_decide

/-- Unbounded misrouting (deflection): every neighbour is permitted on virtual channel 1. -/
def deflectionMesh (k : ℕ) : Network ℕ ℕ where
  arrived c d := head k c == d
  route c d :=
    let u := head k c
    (ch u (xy k u d) 0, d) :: (neighbours k u).map fun dr => (ch u dr 1, d)
  inject := allPairs (k * k) fun s => ch s 4 0

/-- A packet for node 1 can bounce between nodes 4 and 5 forever. -/
theorem deflectionMesh_livelocks : ¬ (deflectionMesh 3).LivelockFree :=
  Network.not_livelockFree_of_refuteB (pre := [.inject 8 1, .hop 8 5 1, .hop 5 30 1, .hop 30 41 1])
    (cyc := [.hop 41 52 1, .hop 52 41 1]) (by decide +kernel)

/-! ### Consequences -/

/-- Under the congestion-aware policy "take the first free permitted channel", every
reachable configuration of the Duato mesh drains: all packets are delivered once
injection stops. -/
theorem duatoMesh_drains {f : Config ℕ ℕ}
    (hf : ((duatoMesh 4).ltsWith (duatoMesh 4).firstFree).Reachable empty f) :
    Relation.ReflTransGen
      (((duatoMesh 4).ltsWith (duatoMesh 4).firstFree).IStep Act.IsMove) f empty :=
  duatoMesh_correct.drain (firstFree_valid _) hf

/-- The network as a whole never gets stuck, under any valid policy. -/
theorem duatoMesh_never_stuck {sel : Selection ℕ ℕ} (hsel : (duatoMesh 4).ValidSel sel) :
    ((duatoMesh 4).ltsWith sel).DeadlockFree empty :=
  duatoMesh_correct.1.lts (by decide) hsel

#assert_standard_axioms ring_deadlocks datelineRing_correct_8 datelineRing_correct
  xyMesh_correct adaptiveMesh_deadlocks duatoMesh_correct misrouteMesh_correct
  deflectionMesh_livelocks duatoMesh_drains duatoMesh_never_stuck

end AsyncLean.Examples
