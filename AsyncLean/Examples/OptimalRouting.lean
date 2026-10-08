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
  `duatoMesh_lt_westFirstMesh`) and are minimal (`turnDuatoMesh_within`), for every size.
* **The west-first mesh of every size** `k` is deadlock and livelock free
  (`westFirstMesh_correct`), starvation free (`westFirstMesh_starvationFree`) and correct under
  wormhole switching for packets of every length (`westFirstMesh_wormholeCorrect`), and every
  packet travels along a shortest path: it takes exactly as many hops as the distance from its
  source to its destination (`westFirstMesh_hops`).  The proofs give the legal pairs, an order
  of the channels that decreases along every escape dependency (`wfRank`) and the distance to
  the destination in closed form.
* The west-first mesh is **maximally adaptive** on the 3 × 3 mesh (`westFirstMesh_maximal`),
  and so is the north-last mesh (`northLastMesh_maximal`): adding *any* set of productive hops,
  at a pair their packets can occupy, introduces a deadlock, under store-and-forward and under
  wormhole switching (`westFirstMesh_maximal_wormhole`).  No improvement in adaptivity is
  possible without giving up deadlock freedom.  `AsyncLean.Examples.MeshMaximal` proves both
  for **every size**, from finitely many kernel-checked deadlocks in a 3 × 3 window.
* They are incomparable, and **no deadlock-free routing function is at least as adaptive as
  both** (`no_common_improvement`, `no_common_improvement_wormhole`).  So there is no "most
  adaptive" deadlock-free minimal routing to look for: there are several maximal ones, and the
  turn-model escapes reach them.
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
  (productive k u d).map (fun dr => (ch u dr 0, d)) ++
    (productive k u d).map fun dr => (ch u dr 1, d)

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

/-! #### Coordinates

Node `u` of a `k × k` mesh is at column `u % k` and row `u / k`; a productive hop moves the head
of a packet one step towards its destination. -/

/-- The node a channel leaves, its direction and its virtual channel. -/
theorem node_ch {u dr vc : ℕ} (hdr : dr < 5) (hvc : vc < 2) : node (ch u dr vc) = u := by
  simp only [node, ch]; omega

theorem dir_ch {u dr vc : ℕ} (hdr : dr < 5) (hvc : vc < 2) : dir (ch u dr vc) = dr := by
  simp only [dir, ch]; omega

theorem vc_ch {u dr vc : ℕ} (hvc : vc < 2) : ch u dr vc % 2 = vc := by
  simp only [ch]; omega

/-- Coordinates of the node `k * y + x` (column `x`, row `y`). -/
theorem coord {k a x y : ℕ} (hx : x < k) (h : a = k * y + x) : a % k = x ∧ a / k = y := by
  subst h
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem lt_sq_of_coord {k a : ℕ} (h1 : a % k < k) (h2 : a / k < k) : a < k * k := by
  have := Nat.div_add_mod a k
  have : k * (a / k) + k ≤ k * k := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
  omega

theorem coord_lt {k a : ℕ} (h : a < k * k) : a % k < k ∧ a / k < k := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at h
  exact ⟨Nat.mod_lt _ hk, Nat.div_lt_of_lt_mul h⟩

/-- The head of a channel leaving `v` in a productive direction `e`: one step towards `d`. -/
theorem head_ch {k v d e vc : ℕ} (hv : v < k * k) (hd : d < k * k) (hvc : vc < 2)
    (he : e ∈ productive k v d) :
    head k (ch v e vc) < k * k ∧
    (e = 0 ∧ head k (ch v e vc) % k = v % k + 1 ∧ head k (ch v e vc) / k = v / k ∧
        v % k < d % k ∨
     e = 1 ∧ head k (ch v e vc) % k + 1 = v % k ∧ head k (ch v e vc) / k = v / k ∧
        d % k < v % k ∨
     e = 2 ∧ head k (ch v e vc) % k = v % k ∧ head k (ch v e vc) / k = v / k + 1 ∧
        v / k < d / k ∨
     e = 3 ∧ head k (ch v e vc) % k = v % k ∧ head k (ch v e vc) / k + 1 = v / k ∧
        d / k < v / k) := by
  set h := head k (ch v e vc) with hdef
  obtain ⟨hvx, hvy⟩ := coord_lt hv
  obtain ⟨hdx, hdy⟩ := coord_lt hd
  have hv' := Nat.div_add_mod v k
  simp only [productive, List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at he
  rcases he with ((⟨hlt, rfl⟩ | ⟨hlt, rfl⟩) | ⟨hlt, rfl⟩) | ⟨hlt, rfl⟩
  · have hh : h = v + 1 := by
      simp only [hdef, head, dir_ch (by omega : (0 : ℕ) < 5) hvc,
        node_ch (by omega : (0 : ℕ) < 5) hvc]
    obtain ⟨h1, h2⟩ := coord (k := k) (a := h) (x := v % k + 1) (y := v / k) (by omega)
      (by omega)
    exact ⟨lt_sq_of_coord (by omega) (by omega), Or.inl ⟨rfl, h1, h2, hlt⟩⟩
  · have hh : h = v - 1 := by
      simp only [hdef, head, dir_ch (by omega : (1 : ℕ) < 5) hvc,
        node_ch (by omega : (1 : ℕ) < 5) hvc]
    obtain ⟨h1, h2⟩ := coord (k := k) (a := h) (x := v % k - 1) (y := v / k) (by omega)
      (by omega)
    exact ⟨lt_sq_of_coord (by omega) (by omega), Or.inr (Or.inl ⟨rfl, by omega, h2, hlt⟩)⟩
  · have hh : h = v + k := by
      simp only [hdef, head, dir_ch (by omega : (2 : ℕ) < 5) hvc,
        node_ch (by omega : (2 : ℕ) < 5) hvc]
    obtain ⟨h1, h2⟩ := coord (k := k) (a := h) (x := v % k) (y := v / k + 1) (by omega)
      (by rw [Nat.mul_add, Nat.mul_one]; omega)
    exact ⟨lt_sq_of_coord (by omega) (by omega), Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2, hlt⟩))⟩
  · have hh : h = v - k := by
      simp only [hdef, head, dir_ch (by omega : (3 : ℕ) < 5) hvc,
        node_ch (by omega : (3 : ℕ) < 5) hvc]
    have hpos : 0 < v / k := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    obtain ⟨y', hy'⟩ : ∃ y', v / k = y' + 1 := ⟨v / k - 1, by omega⟩
    have hy : k * (v / k) = k * (v / k - 1) + k := by
      rw [hy', Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one]
    obtain ⟨h1, h2⟩ := coord (k := k) (a := h) (x := v % k) (y := v / k - 1) (by omega)
      (by omega)
    exact ⟨lt_sq_of_coord (by omega) (by omega),
      Or.inr (Or.inr (Or.inr ⟨rfl, h1, by omega, hlt⟩))⟩

theorem head_inj {k v : ℕ} : head k (ch v 4 0) = v := by
  simp only [head, dir_ch (by omega : 4 < 5) (by omega : 0 < 2),
    node_ch (by omega : 4 < 5) (by omega : 0 < 2)]

/-- Which direction XY routing takes, and why. -/
theorem xy_cases {k v d : ℕ} (h : v ≠ d) :
    xy k v d = 0 ∧ v % k < d % k ∨ xy k v d = 1 ∧ d % k < v % k ∨
    xy k v d = 2 ∧ v % k = d % k ∧ v / k < d / k ∨
    xy k v d = 3 ∧ v % k = d % k ∧ d / k < v / k := by
  have := xy_mem_productive (k := k) h
  unfold xy at this ⊢
  simp only [productive, List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at this
  split_ifs at this ⊢ <;> omega

theorem productive_lt {k u d dr : ℕ} (h : dr ∈ productive k u d) : dr < 4 := by
  simp only [productive, List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at h
  omega

theorem dir_lt (c : ℕ) : dir c < 5 := Nat.mod_lt _ (by omega)

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

/-! ### The west-first mesh of every size

Deadlock freedom follows from Duato's theorem with the XY hop as the escape hop: on the legal
pairs (`wfLegal`), the escape hops only make the turns of the west-first turn model, and the
order `wfRank` decreases along each of them.  Livelock freedom and the hop count follow from the
distance to the destination (`wfDist`), which every hop decreases by exactly one. -/

/-- The pairs a packet of the west-first mesh can occupy: an injection channel, or a channel
leaving node `u` in a direction that is productive from `u`; on virtual channel 0, a packet
going north or south has no westward hop left. -/
def wfLegal (k c d : ℕ) : Prop :=
  d < k * k ∧ ∃ u dr vc, c = ch u dr vc ∧ u < k * k ∧ vc < 2 ∧
    (dr = 4 ∧ vc = 0 ∨ dr ∈ productive k u d ∧ (vc = 0 → dr = 2 ∨ dr = 3 → u % k ≤ d % k))

/-- The head of a legal channel is a node of the mesh. -/
theorem wfLegal_head {k c d : ℕ} (h : wfLegal k c d) : head k c < k * k := by
  obtain ⟨hd, u, dr, vc, rfl, hu, hvc, ⟨rfl, rfl⟩ | ⟨hp, -⟩⟩ := h
  · rw [head_inj]; exact hu
  · exact (head_ch hu hd hvc hp).1

theorem wf_route_mem {k c d : ℕ} {q : ℕ × ℕ} (hq : q ∈ (westFirstMesh k).route c d) :
    q = (ch (head k c) (xy k (head k c) d) 0, d) ∨
    (∃ dr ∈ westFirst k (head k c) d, q = (ch (head k c) dr 0, d)) ∨
    ∃ dr ∈ productive k (head k c) d, q = (ch (head k c) dr 1, d) := by
  simp only [westFirstMesh, turnDuatoMesh, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_filter] at hq
  rcases hq with (h | ⟨dr, ⟨hdr, -⟩, rfl⟩) | ⟨dr, hdr, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨dr, hdr, rfl⟩)
  · exact Or.inr (Or.inr ⟨dr, hdr, rfl⟩)

theorem wf_closed (k : ℕ) : (westFirstMesh k).Closed (wfLegal k) := by
  constructor
  · intro q hq
    simp only [westFirstMesh, turnDuatoMesh, allPairs, List.mem_flatMap, List.mem_range,
      List.mem_map, List.mem_filter] at hq
    obtain ⟨s, hs, d, ⟨hd, -⟩, rfl⟩ := hq
    exact ⟨hd, s, 4, 0, rfl, hs, by omega, Or.inl ⟨rfl, rfl⟩⟩
  · intro c d q hl ha hq
    have hv := wfLegal_head hl
    have hd := hl.1
    have hne : head k c ≠ d := by simpa [westFirstMesh, turnDuatoMesh] using ha
    rcases wf_route_mem hq with rfl | ⟨dr, hdr, rfl⟩ | ⟨dr, hdr, rfl⟩
    · dsimp only
      refine ⟨hd, _, _, 0, rfl, hv, by omega, Or.inr ⟨xy_mem_productive hne, fun _ h => ?_⟩⟩
      rcases xy_cases (k := k) hne with h' | h' | h' | h' <;> omega
    · dsimp only
      refine ⟨hd, _, dr, 0, rfl, hv, by omega, Or.inr ⟨westFirst_sub hdr, fun _ h => ?_⟩⟩
      unfold westFirst at hdr
      split_ifs at hdr with hw
      · simp at hdr; omega
      · omega
    · exact ⟨hd, _, dr, 1, rfl, hv, by omega, Or.inr ⟨hdr, by omega⟩⟩


/-- The escape hop: XY routing on virtual channel 0. -/
def xyEscape (k c d : ℕ) : List (ℕ × ℕ) := [(ch (head k c) (xy k (head k c) d) 0, d)]

/-- A position of every channel in the dependency order of the escape hops: virtual channel 1
and injection channels first, then westward channels from east to west, then the other
channels of virtual channel 0, column by column from west to east (within a column, the
eastward channel arriving there, then northward channels from south to north and southward
channels from north to south). -/
def wfRank (k c : ℕ) : ℕ × ℕ :=
  if c % 2 = 1 ∨ dir c = 4 then (k + 2, 0)
  else if dir c = 1 then (k + 1, head k c % k)
  else if dir c = 0 then (k - head k c % k, k)
  else if dir c = 2 then (k - head k c % k, k - head k c / k)
  else (k - head k c % k, head k c / k)

theorem wfRank_vc1 {k v e : ℕ} : wfRank k (ch v e 1) = (k + 2, 0) := by
  unfold wfRank; rw [vc_ch (by omega), ite_eq_left_iff.2 fun h => absurd (Or.inl rfl) h]

theorem wfRank_inj {k v : ℕ} : wfRank k (ch v 4 0) = (k + 2, 0) := by
  unfold wfRank; rw [dir_ch (by omega) (by omega), ite_eq_left_iff.2 fun h => absurd (Or.inr rfl) h]

theorem wfRank_W {k v : ℕ} : wfRank k (ch v 1 0) = (k + 1, head k (ch v 1 0) % k) := by
  unfold wfRank; rw [vc_ch (by omega), dir_ch (by omega) (by omega)]; rfl

theorem wfRank_E {k v : ℕ} : wfRank k (ch v 0 0) = (k - head k (ch v 0 0) % k, k) := by
  unfold wfRank; rw [vc_ch (by omega), dir_ch (by omega) (by omega)]; rfl

theorem wfRank_N {k v : ℕ} :
    wfRank k (ch v 2 0) = (k - head k (ch v 2 0) % k, k - head k (ch v 2 0) / k) := by
  unfold wfRank; rw [vc_ch (by omega), dir_ch (by omega) (by omega)]; rfl

theorem wfRank_S {k v : ℕ} :
    wfRank k (ch v 3 0) = (k - head k (ch v 3 0) % k, head k (ch v 3 0) / k) := by
  unfold wfRank; rw [vc_ch (by omega), dir_ch (by omega) (by omega)]; rfl

theorem wf_dep {k c c' : ℕ} (h : (westFirstMesh k).Dep (wfLegal k) (xyEscape k) c c') :
    Prod.Lex (· < ·) (· < ·) (wfRank k c') (wfRank k c) := by
  obtain ⟨d, d', hl, ha, hq⟩ := h
  have hv := wfLegal_head hl
  have hd := hl.1
  have hne : head k c ≠ d := by simpa [westFirstMesh, turnDuatoMesh] using ha
  simp only [xyEscape, List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, -⟩ := hq
  have he := xy_mem_productive (k := k) hne
  obtain ⟨-, hh'⟩ := head_ch (vc := 0) hv hd (by omega) he
  have hxy := xy_cases (k := k) hne
  obtain ⟨hvx, hvy⟩ := coord_lt hv
  obtain ⟨hdx, hdy⟩ := coord_lt hd
  generalize xy k (head k c) d = e at hh' hxy ⊢
  -- `omega` reads `x / k` and `x % k` as integer division: it needs their signs
  have := Nat.zero_le (head k (ch (head k c) e 0) / k)
  have := Nat.zero_le (head k (ch (head k c) e 0) % k)
  have := Nat.zero_le (head k c / k)
  have := Nat.zero_le (head k c % k)
  have := Nat.zero_le (d / k)
  have := Nat.zero_le (d % k)
  obtain ⟨-, u, dr, vc, rfl, hu, hvc, ⟨rfl, rfl⟩ | ⟨hp, hwf⟩⟩ := hl
  · rw [wfRank_inj]
    rcases hh' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
      simp only [wfRank_W, wfRank_E, wfRank_N, wfRank_S, Prod.lex_def] <;> omega
  · obtain ⟨-, hh⟩ := head_ch hu hd hvc hp
    have := Nat.zero_le (u / k)
    have := Nat.zero_le (u % k)
    rcases (show vc = 0 ∨ vc = 1 by omega) with rfl | rfl
    · rcases hh' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
        rcases hh with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;>
        simp only [wfRank_W, wfRank_E, wfRank_N, wfRank_S, Prod.lex_def, true_and,
          lt_self_iff_false, false_or] <;> omega
    · rw [wfRank_vc1]
      rcases hh' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
        simp only [wfRank_W, wfRank_E, wfRank_N, wfRank_S, Prod.lex_def] <;> omega

theorem wf_wf (k : ℕ) : WellFounded (flip ((westFirstMesh k).Dep (wfLegal k) (xyEscape k))) :=
  Network.wf_of_lexRank (wfRank k) fun _ _ h => wf_dep h

/-- The distance from the head of a channel to the destination. -/
def wfDist (k c d : ℕ) : ℕ :=
  (head k c % k - d % k) + (d % k - head k c % k) + (head k c / k - d / k) + (d / k - head k c / k)

/-- Every hop brings the packet exactly one step closer. -/
theorem wf_dist {k c d : ℕ} {q : ℕ × ℕ} (hl : wfLegal k c d)
    (ha : (westFirstMesh k).arrived c d = false) (hq : q ∈ (westFirstMesh k).route c d) :
    wfDist k q.1 q.2 + 1 = wfDist k c d := by
  have hv := wfLegal_head hl
  have hd := hl.1
  have hne : head k c ≠ d := by simpa [westFirstMesh, turnDuatoMesh] using ha
  have key : ∀ e vc, vc < 2 → e ∈ productive k (head k c) d →
      wfDist k (ch (head k c) e vc) d + 1 = wfDist k c d := by
    intro e vc hvc he
    obtain ⟨-, hh⟩ := head_ch hv hd hvc he
    simp only [wfDist]
    rcases hh with h1 | h1 | h1 | h1 <;> omega
  rcases wf_route_mem hq with rfl | ⟨dr, hdr, rfl⟩ | ⟨dr, hdr, rfl⟩
  · exact key _ 0 (by omega) (xy_mem_productive hne)
  · exact key _ 0 (by omega) (westFirst_sub hdr)
  · exact key _ 1 (by omega) hdr

/-! #### Wormhole switching

The escape channels are those of virtual channel 0.  Duato's *extended* dependency graph also
counts the escape channels a packet requests after detours on virtual channel 1.  Such a detour
is productive, so it keeps the head of the packet between the escape channel it left and its
destination (`wfBox`), and the same order `wfRank` decreases. -/

/-- The escape channels under wormhole switching: virtual channel 0. -/
def wfEsc (c : ℕ) : Prop := c % 2 = 0

/-- While a packet that left the escape channel `e` moves on, its head stays between the head of
`e` and its destination, in the directions `e` was heading. -/
def wfBox (k e : ℕ) (q : ℕ × ℕ) : Prop :=
  wfLegal k q.1 q.2 ∧
  (dir e = 1 → head k q.1 % k ≤ head k e % k ∧ q.2 % k ≤ head k q.1 % k) ∧
  (dir e = 0 ∨ dir e = 2 ∨ dir e = 3 → head k e % k ≤ head k q.1 % k ∧ head k q.1 % k ≤ q.2 % k) ∧
  (dir e = 2 → head k e / k ≤ head k q.1 / k ∧ head k q.1 / k ≤ q.2 / k) ∧
  (dir e = 3 → head k q.1 / k ≤ head k e / k ∧ q.2 / k ≤ head k q.1 / k)

theorem wfBox_base {k e d : ℕ} (hl : wfLegal k e d) (he : wfEsc e) : wfBox k e (e, d) := by
  refine ⟨hl, ?_⟩
  dsimp only
  obtain ⟨hd, u, dr, vc, rfl, hu, hvc, ⟨rfl, rfl⟩ | ⟨hp, hwf⟩⟩ := hl
  · rw [dir_ch (by omega) (by omega)]; omega
  · have hvc0 : vc = 0 := by unfold wfEsc at he; rw [vc_ch hvc] at he; exact he
    subst hvc0
    have := Nat.zero_le (u / k)
    have := Nat.zero_le (u % k)
    have := Nat.zero_le (d / k)
    have := Nat.zero_le (d % k)
    obtain ⟨-, hh⟩ := head_ch hu hd hvc hp
    rw [dir_ch (by have := productive_lt hp; omega) hvc]
    rcases hh with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> omega

theorem wfBox_step {k e : ℕ} {q q' : ℕ × ℕ} (hb : wfBox k e q)
    (ha : (westFirstMesh k).arrived q.1 q.2 = false) (hq : q' ∈ (westFirstMesh k).route q.1 q.2) :
    wfBox k e q' := by
  obtain ⟨hl, hW, hX, hN, hS⟩ := hb
  have hl' := (wf_closed k).route _ _ _ hl ha hq
  have hv := wfLegal_head hl
  have hd := hl.1
  have hne : head k q.1 ≠ q.2 := by simpa [westFirstMesh, turnDuatoMesh] using ha
  obtain ⟨dr, vc, hvc, hdr, rfl⟩ : ∃ dr vc, vc < 2 ∧ dr ∈ productive k (head k q.1) q.2 ∧
      q' = (ch (head k q.1) dr vc, q.2) := by
    rcases wf_route_mem hq with h | ⟨dr, hdr, h⟩ | ⟨dr, hdr, h⟩
    · exact ⟨_, 0, by omega, xy_mem_productive hne, h⟩
    · exact ⟨dr, 0, by omega, westFirst_sub hdr, h⟩
    · exact ⟨dr, 1, by omega, hdr, h⟩
  refine ⟨hl', ?_⟩
  obtain ⟨-, hh⟩ := head_ch hv hd hvc hdr
  have := Nat.zero_le (head k q.1 / k)
  have := Nat.zero_le (head k q.1 % k)
  have := Nat.zero_le (head k (ch (head k q.1) dr vc) / k)
  have := Nat.zero_le (head k (ch (head k q.1) dr vc) % k)
  have := Nat.zero_le (q.2 / k)
  have := Nat.zero_le (q.2 % k)
  have := Nat.zero_le (head k e / k)
  have := Nat.zero_le (head k e % k)
  dsimp only
  rcases hh with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> omega

theorem wfBox_of_NE {k e : ℕ} {q : ℕ × ℕ} (h : (westFirstMesh k).NE (wfLegal k) wfEsc e q) :
    wfBox k e q ∧ wfEsc e := by
  induction h with
  | base hl he => exact ⟨wfBox_base hl he, he⟩
  | step _ ha hq _ ih => exact ⟨wfBox_step ih.1 ha hq, ih.2⟩

theorem wfRank_esc {k c : ℕ} (h : wfEsc c) :
    wfRank k c =
      if dir c = 4 then (k + 2, 0)
      else if dir c = 1 then (k + 1, head k c % k)
      else if dir c = 0 then (k - head k c % k, k)
      else if dir c = 2 then (k - head k c % k, k - head k c / k)
      else (k - head k c % k, head k c / k) := by
  unfold wfEsc at h
  simp only [wfRank, h, zero_ne_one, false_or]

theorem wf_extDep {k e e' : ℕ} (h : (westFirstMesh k).ExtDep (wfLegal k) wfEsc e e') :
    Prod.Lex (· < ·) (· < ·) (wfRank k e') (wfRank k e) := by
  obtain ⟨q, hne, ha, p', hq, he'⟩ := h
  obtain ⟨⟨hl, hW, hX, hN, hS⟩, he⟩ := wfBox_of_NE hne
  have hv := wfLegal_head hl
  have hd := hl.1
  have hneq : head k q.1 ≠ q.2 := by simpa [westFirstMesh, turnDuatoMesh] using ha
  have hp' : p' = q.2 := by
    rcases wf_route_mem hq with h | ⟨dr, -, h⟩ | ⟨dr, -, h⟩ <;> simp only [Prod.mk.injEq] at h <;>
      exact h.2
  subst hp'
  -- the requested escape channel leaves the head of `q` on virtual channel 0, in a direction
  -- productive for `q.2`, and westward only when the packet still has to go west
  obtain ⟨dr, hdr, hwest, rfl⟩ : ∃ dr ∈ productive k (head k q.1) q.2,
      (dr = 1 → q.2 % k < head k q.1 % k) ∧ e' = ch (head k q.1) dr 0 := by
    rcases wf_route_mem hq with h | ⟨dr, hdr, h⟩ | ⟨dr, hdr, h⟩ <;>
      simp only [Prod.mk.injEq, and_true] at h <;> subst h
    · refine ⟨_, xy_mem_productive hneq, fun h1 => ?_, rfl⟩
      rcases xy_cases (k := k) hneq with h2 | h2 | h2 | h2 <;> omega
    · refine ⟨dr, westFirst_sub hdr, fun h1 => ?_, rfl⟩
      unfold westFirst at hdr
      split_ifs at hdr with hw
      · exact hw
      · subst h1
        simp only [productive, List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hdr
        omega
    · unfold wfEsc at he'; rw [vc_ch (by omega)] at he'; cases he'
  have hdr4 := productive_lt hdr
  obtain ⟨-, hh⟩ := head_ch (vc := 0) hv hd (by omega) hdr
  have := Nat.zero_le (head k q.1 / k)
  have := Nat.zero_le (head k q.1 % k)
  have := Nat.zero_le (head k (ch (head k q.1) dr 0) / k)
  have := Nat.zero_le (head k (ch (head k q.1) dr 0) % k)
  have := Nat.zero_le (q.2 / k)
  have := Nat.zero_le (q.2 % k)
  have := Nat.zero_le (head k e / k)
  have := Nat.zero_le (head k e % k)
  obtain ⟨hvx, hvy⟩ := coord_lt hv
  obtain ⟨hdx, hdy⟩ := coord_lt hd
  have hde := dir_lt e
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hd
  have := Nat.mod_lt (head k e) hk
  rw [wfRank_esc he]
  rcases hh with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
    simp only [wfRank_W, wfRank_E, wfRank_N, wfRank_S, Prod.lex_def] <;>
    rcases (by omega : dir e = 0 ∨ dir e = 1 ∨ dir e = 2 ∨ dir e = 3 ∨ dir e = 4) with
      h2 | h2 | h2 | h2 | h2 <;>
      simp only [h2, Nat.reduceEqDiff, ite_true, ite_false, or_true, false_or, or_false,
        true_implies, false_implies, true_and, lt_self_iff_false] at hW hX hN hS hwest ⊢ <;> omega

/-! #### Correct for every size, along shortest paths -/

theorem wf_pairs_finite (k : ℕ) : {q : ℕ × ℕ | wfLegal k q.1 q.2}.Finite := by
  refine (Finset.finite_toSet (Finset.range (10 * (k * k)) ×ˢ Finset.range (k * k))).subset ?_
  rintro ⟨c, d⟩ ⟨hd, u, dr, vc, rfl, hu, hvc, hdr⟩
  have : dr < 5 := by
    rcases hdr with ⟨rfl, -⟩ | ⟨hp, -⟩
    · omega
    · have := productive_lt hp; omega
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio, ch]
  omega

theorem wf_chans_finite (k : ℕ) : {c | ∃ d, wfLegal k c d}.Finite :=
  ((wf_pairs_finite k).image Prod.fst).subset fun c ⟨d, hl⟩ => ⟨(c, d), hl, rfl⟩

theorem wf_esc_sub {k : ℕ} : ∀ c d q, wfLegal k c d → (westFirstMesh k).arrived c d = false →
    q ∈ xyEscape k c d → q ∈ (westFirstMesh k).route c d := by
  intro c d q _ _ hq
  simp only [xyEscape, List.mem_singleton] at hq
  subst hq
  simp [westFirstMesh, turnDuatoMesh]

theorem wf_esc_conn {k : ℕ} : ∀ c d, wfLegal k c d → (westFirstMesh k).arrived c d = false →
    xyEscape k c d ≠ [] := by
  intro c d _ _; simp [xyEscape]

/-- **The west-first mesh of every size is deadlock and livelock free**, under every dynamic
routing policy. -/
theorem westFirstMesh_correct (k : ℕ) : (westFirstMesh k).Correct :=
  ⟨(westFirstMesh k).deadlockFree_of_escape (wf_closed k) (xyEscape k) wf_esc_sub wf_esc_conn
      (wf_wf k),
    (westFirstMesh k).livelockFree_of_ranking (wf_closed k) (wf_chans_finite k) (wfDist k)
      fun _ _ _ hl ha hq => by have := wf_dist hl ha hq; omega⟩

/-- **No packet of the west-first mesh of any size starves** along a strongly fair run. -/
theorem westFirstMesh_starvationFree (k : ℕ) : (westFirstMesh k).StarvationFree :=
  (westFirstMesh k).starvationFree_of_escape_ranking (wf_closed k) (wf_pairs_finite k)
    (xyEscape k) wf_esc_sub wf_esc_conn (wf_wf k) (wfDist k)
    fun _ _ _ hl ha hq => by have := wf_dist hl ha hq; omega

/-- **The west-first mesh of every size is correct under wormhole switching**, for packets of
every length: virtual channel 0 is the set of escape channels. -/
theorem westFirstMesh_wormholeCorrect (k : ℕ) : (westFirstMesh k).WormholeCorrect :=
  ⟨(westFirstMesh k).wormholeDeadlockFree_of_escape (E := wfEsc) (wf_closed k)
      (fun c d hl ha => ⟨_, wf_esc_sub c d _ hl ha (List.mem_singleton_self _),
        by simp [wfEsc, vc_ch]⟩)
      (wf_of_lexRank (wfRank k) fun _ _ h => wf_extDep h),
    (westFirstMesh k).wormholeLivelockFree_of_ranking (wf_closed k) (wfDist k)
      fun _ _ _ hl ha hq => by have := wf_dist hl ha hq; omega⟩

/-- **Every packet takes a shortest path**: a packet injected at node `s` for node `d` is
delivered after exactly as many hops as the distance from `s` to `d` in the mesh. -/
theorem westFirstMesh_hops {k s d : ℕ} (hs : s < k * k) (hd : d < k * k) {q : ℕ × ℕ}
    {ls : List Unit} (h : (westFirstMesh k).packetLTS.Path (ch s 4 0, d) ls q)
    (harr : (westFirstMesh k).arrived q.1 q.2 = true) :
    ls.length = (s % k - d % k) + (d % k - s % k) + (s / k - d / k) + (d / k - s / k) := by
  have hl : wfLegal k (ch s 4 0) d := ⟨hd, s, 4, 0, rfl, hs, by omega, Or.inl ⟨rfl, rfl⟩⟩
  have := (westFirstMesh k).packet_hops_eq (wf_closed k) (wfDist k)
    (fun _ _ _ hl ha hq => wf_dist hl ha hq) hl h
  have h0 : wfDist k q.1 q.2 = 0 := by
    have : head k q.1 = q.2 := by simpa [westFirstMesh, turnDuatoMesh] using harr
    simp [wfDist, this]
  rw [h0] at this
  simp only [wfDist, head_inj] at this
  omega

/-! #### Congestion-aware selection

More adaptivity on the escape layer is not always faster: under heavy, adversarial traffic,
packets taking the extra hops of virtual channel 0 crowd the escape channels.  (In a cycle-level
simulation, `scripts/routing_sim.py`, an 8 × 8 west-first mesh with a random choice among the
free hops saturates at about 0.11 packets per node and cycle under bit-complement traffic,
against 0.18 for Duato's mesh.)  Duato's theorem does not need the selection to take every free
hop, only never to refuse a free escape hop (`Network.EscapeSel`).  So a router may use the extra
hops only when the router ahead is lightly loaded (`westFirstGated`) and stay deadlock and
livelock free; in the simulation this matches Duato's mesh under uniform and bit-complement
traffic and has a third of its latency under transpose traffic near saturation. -/

/-- **Any selection that never refuses a free XY escape hop** keeps the west-first mesh of every
size deadlock and livelock free. -/
theorem westFirstMesh_correctWith (k : ℕ) {sel : Selection ℕ ℕ}
    (hsel : (westFirstMesh k).EscapeSel (xyEscape k) sel) :
    (westFirstMesh k).DeadlockFreeWith sel ∧ (westFirstMesh k).LivelockFreeWith sel :=
  ⟨(westFirstMesh k).deadlockFreeWith_of_escape (wf_closed k) (xyEscape k) wf_esc_conn (wf_wf k)
      hsel,
    (westFirstMesh k).livelockFreeWith_of_ranking (wf_closed k) (wf_chans_finite k) (wfDist k)
      (fun _ _ _ hl ha hq => by have := wf_dist hl ha hq; omega) hsel.sub⟩

/-- The number of free channels leaving node `v` (on both virtual channels). -/
def freeOut (f : Config ℕ ℕ) (v : ℕ) : ℕ :=
  ((List.range 4).flatMap fun dr => [ch v dr 0, ch v dr 1]).countP fun c => (f c).isNone

/-- The congestion-aware west-first mesh: virtual channel 1 and the XY escape hop are always
offered; the extra hops of virtual channel 0 only towards a router with at least `g` of its 8
outgoing channels free. -/
def westFirstGated (k g : ℕ) : Selection ℕ ℕ :=
  (westFirstMesh k).gatedSel (xyEscape k) fun f _ _ q =>
    q.1 % 2 == 1 || decide (g ≤ freeOut f (head k q.1))

theorem westFirstGated_correct (k g : ℕ) :
    (westFirstMesh k).DeadlockFreeWith (westFirstGated k g) ∧
      (westFirstMesh k).LivelockFreeWith (westFirstGated k g) :=
  westFirstMesh_correctWith k ((westFirstMesh k).gatedSel_escapeSel
    (fun c d q hq => by
      simp only [xyEscape, List.mem_singleton] at hq
      subst hq
      simp [westFirstMesh, turnDuatoMesh]) _)

/-! ### Other routing functions -/

/-- Fully adaptive minimal routing on both virtual channels deadlocks: eight packets, two in each
channel of the square of nodes 0, 1, 4 and 3, each with a single productive direction. -/
theorem minimalMesh_deadlocks : ¬ (minimalMesh 3).DeadlockFree :=
  Network.not_deadlockFree_of_refuteB
    (as := [.inject 8 4, .hop 8 1 4, .inject 38 1, .hop 38 37 1, .inject 38 1, .hop 38 36 1,
      .inject 48 0, .hop 48 43 0, .inject 48 0, .hop 48 42 0, .inject 18 3, .hop 18 15 3,
      .inject 18 3, .hop 18 14 3, .inject 8 4, .hop 8 0 4])
    (by decide +kernel)

/-- The north-last mesh is correct too (checked here for one size). -/
theorem northLastMesh_correct : (northLastMesh 4).Correct := by async_decide

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
    (turnDuatoMesh_within 3 fun _ _ _ => westFirst_sub) (westFirstMesh_correct 3).1
    (pairReachable_of_mem_inject (by decide)) (by decide) duatoMesh_lt_westFirstMesh.1
    duatoMesh_lt_westFirstMesh.2

/-! ### Maximality -/

/-- **The west-first mesh is maximally adaptive**: any deadlock-free minimal routing function
that permits all its hops permits no other. -/
theorem westFirstMesh_maximal : (westFirstMesh 3).MaximallyAdaptive (minimalHops 3) := by
  async_decide

/-- **Maximal under wormhole switching too**: a minimal routing function that permits every hop
of the west-first mesh and one more deadlocks under wormhole switching as well. -/
theorem westFirstMesh_maximal_wormhole (N : Network ℕ ℕ) (h : (westFirstMesh 3).Extends N)
    (hU : N.Within (minimalHops 3)) (hW : N.WormholeDeadlockFree) :
    ∀ c d, (westFirstMesh 3).PairReachable (c, d) → (westFirstMesh 3).arrived c d = false →
      ∀ q ∈ N.route c d, q ∈ (westFirstMesh 3).route c d :=
  westFirstMesh_maximal.wormhole N h hU hW

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

/-- No common improvement under wormhole switching either. -/
theorem no_common_improvement_wormhole (N : Network ℕ ℕ) (h₁ : (westFirstMesh 3).Extends N)
    (h₂ : (northLastMesh 3).Extends N) (hU : N.Within (minimalHops 3)) :
    ¬ N.WormholeDeadlockFree :=
  fun hW => no_common_improvement N h₁ h₂ hU (N.deadlockFree_of_wormholeDeadlockFree hW)

#assert_standard_axioms minimalMesh_deadlocks westFirstMesh_correct westFirstMesh_starvationFree
  westFirstMesh_wormholeCorrect westFirstMesh_hops westFirstMesh_correctWith
  westFirstGated_correct northLastMesh_correct duatoMesh_extends
  turnDuatoMesh_within duatoMesh_lt_westFirstMesh duatoMesh_not_maximal westFirstMesh_maximal
  westFirstMesh_maximal_wormhole northLastMesh_maximal
  westFirst_northLast_incomparable no_common_improvement no_common_improvement_wormhole

end AsyncLean.Examples
