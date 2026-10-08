/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshNorthLast

/-!
# Optimal mesh routing, metric by metric

"Most adaptive" depends on the yardstick: which hops count, on how many virtual channels.  This
file fixes the yardstick by the cost one wants to optimise and proves, for every mesh size, what
the optimum is and which routing function reaches it.

## Latency: hop count

* `hops_lower_bound` : on a `k × k` mesh, a packet that only moves between neighbouring nodes
  needs at least as many hops as the distance from its source to its destination, **whatever
  the routing function**.
* Every mesh family (`MeshFamily`) — XY, the turn-model meshes on one or two virtual channels —
  meets the bound exactly (`family_hops`), so none can be beaten on hop count.

## Buffers: one virtual channel

* With a single virtual channel per link (the fewest buffers a mesh can have), the west-first
  and north-last turn models (`westFirst1`, `northLast1`) are deadlock and livelock free for
  every size, under store-and-forward and wormhole switching (`westFirst1_correct`,
  `westFirst1_wormholeCorrect`, and the same for north-last), and take shortest paths.
* They are **maximally adaptive** among the minimal routing functions on one virtual channel
  (`minimalHops1`), for every size (`westFirst1_maximal_all`, `northLast1_maximal_all`), and
  XY routing is not (`xyMesh_not_maximal_all`).  On two virtual channels, `westFirstMesh` and
  `northLastMesh` are maximal (`AsyncLean.Examples.MeshMaximal`).

## Routing tables

* `table_lower_bound` : on any mesh of size at least 3, a deadlock-free minimal routing function
  needs at least 4 different routing decisions at an inner router.
* XY routing makes exactly as few (`xy_table`), so it is optimal for routing-table size.  Every
  turn-model mesh decides from the relative position of the destination alone, so it needs at
  most 8 decisions per router, independent of the size (`turnDuato_table`).
-/

namespace AsyncLean.Examples

open Network Mesh

/-! ### One virtual channel -/

/-- A turn-model mesh on a single virtual channel: every hop of the turn model `turn`. -/
def turnMesh1 (turn : ℕ → ℕ → ℕ → List ℕ) (k : ℕ) : Network ℕ ℕ where
  arrived c d := head k c == d
  route c d := (turn k (head k c) d).map fun dr => (ch (head k c) dr 0, d)
  inject := allPairs (k * k) fun s => ch s 4 0

/-- West-first routing on one virtual channel. -/
abbrev westFirst1 (k : ℕ) : Network ℕ ℕ := turnMesh1 westFirst k

/-- North-last routing on one virtual channel. -/
abbrev northLast1 (k : ℕ) : Network ℕ ℕ := turnMesh1 northLast k

/-- Every productive hop on a single virtual channel: the yardstick for one virtual channel. -/
def minimalHops1 (k c d : ℕ) : List (ℕ × ℕ) :=
  (productive k (head k c) d).map fun dr => (ch (head k c) dr 0, d)

namespace Mesh

variable {turn : ℕ → ℕ → ℕ → List ℕ}

theorem turnMesh1_family (ht : TurnLocal turn) : MeshFamily (turnMesh1 turn) where
  arrived _ _ _ := rfl
  inject _ := rfl
  route k c d q _ hq := by
    simp only [turnMesh1, List.mem_map] at hq
    obtain ⟨dr, hdr, rfl⟩ := hq
    exact ⟨dr, 0, ht.1 _ _ _ _ hdr, by omega, rfl⟩
  emb k ox oy L hL c d hc hd := by
    have fh := hL _ (winOK_iff.1 hc).2.2
    have fd := hL _ hd
    simp only [turnMesh1, head_embCh hL hc, ht.2 k ox oy _ _ fh fd, List.map_map]
    refine List.map_congr_left fun dr hdr => ?_
    have := productive_lt (ht.1 _ _ _ _ hdr)
    simp only [Function.comp_apply, embCh_ch (u := head 3 c) (dr := dr) (vc := 0) (by omega)
      (by omega)]

theorem minimalHops1_local : HopsLocal minimalHops1 := fun k ox oy L hL c d hc hd => by
  have fh := hL _ (winOK_iff.1 hc).2.2
  have fd := hL _ hd
  simp only [minimalHops1, head_embCh hL hc, productive_emb fh fd, List.map_map]
  refine List.map_congr_left fun dr hdr => ?_
  have := productive_lt hdr
  simp only [Function.comp_apply, embCh_ch (u := head 3 c) (dr := dr) (vc := 0) (by omega)
    (by omega)]

theorem minimalHops1_mem {k c d : ℕ} {q : ℕ × ℕ} (hq : q ∈ minimalHops1 k c d) :
    ∃ dr, dr ∈ productive k (head k c) d ∧ q = (ch (head k c) dr 0, d) := by
  simp only [minimalHops1, List.mem_map] at hq
  obtain ⟨dr, hdr, rfl⟩ := hq
  exact ⟨dr, hdr, rfl⟩

/-! #### Window certificates on one virtual channel: four packets around a square -/

/-- West of `C = 4`, north-bound `P` in channel `14`. -/
def cert1NW : List (Act ℕ ℕ) :=
  [.inject 8 4, .hop 8 0 4, .inject 48 0, .hop 48 42 0, .inject 38 1, .hop 38 36 1]

/-- West of `C = 1`, south-bound `P` in channel `46`. -/
def cert1SW : List (Act ℕ ℕ) :=
  [.inject 18 3, .hop 18 12 3, .inject 8 4, .hop 8 4 4, .inject 38 1, .hop 38 30 1]

/-- East of `C = 3`, north-bound `P` in channel `4`. -/
def cert1NE : List (Act ℕ ℕ) :=
  [.inject 38 1, .hop 38 30 1, .inject 48 0, .hop 48 46 0, .inject 18 3, .hop 18 12 3]

theorem wf1_certNW :
    winCertB (westFirst1 3) (minimalHops1 3) [0, 1, 3, 4] 14 [(42, 9)] cert1NW = true := by
  decide +kernel

theorem wf1_certSW :
    winCertB (westFirst1 3) (minimalHops1 3) [0, 1, 3, 4] 46 [(12, 9)] cert1SW = true := by
  decide +kernel

theorem nl1_certNW :
    winCertB (northLast1 3) (minimalHops1 3) [0, 1, 3, 4] 14 [(42, 9)] cert1NW = true := by
  decide +kernel

theorem nl1_certNE :
    winCertB (northLast1 3) (minimalHops1 3) [0, 1, 3, 4] 4 [(30, 9)] cert1NE = true := by
  decide +kernel

/-! #### Following the packet on one virtual channel -/

variable {Mk : ℕ → Network ℕ ℕ}

theorem minimal1_of {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N)
    (hU : N.Within (minimalHops1 k)) {c d : ℕ} {q : ℕ × ℕ}
    (ha : (Mk k).arrived c d = false) (hq : q ∈ N.route c d) :
    ∃ dr, dr ∈ productive k (head k c) d ∧ q = (ch (head k c) dr 0, d) :=
  minimalHops1_mem (hU c d q (by rw [hext.arrived]; exact ha) hq)

/-- A packet alone in the channel from `(x, y)` north to `(x, y + 1)`, with its destination west
of column `x` and no northward hop left on virtual channel 0: the square deadlock. -/
theorem square1NW (hF : MeshFamily Mk)
    (hcert : winCertB (Mk 3) (minimalHops1 3) [0, 1, 3, 4] 14 [(42, 9)] cert1NW = true)
    {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N) (hU : N.Within (minimalHops1 k))
    {x y d : ℕ} (hd : d < k * k) (hdx : d % k < x) (hx : x < k) (hdy : y + 1 ≤ d / k)
    (hreach : N.lts.Reachable empty (fill [(ch (k * y + x) 2 0, d)]))
    (hno : (ch (k * (y + 1) + x) 2 0, d) ∉ N.route (ch (k * y + x) 2 0) d) :
    ¬ N.DeadlockFree := by
  obtain ⟨-, hdyk⟩ := coord_lt hd
  have hC := coord (k := k) (a := k * (y + 1) + x) hx rfl
  have hh : head k (ch (k * y + x) 2 0) = k * (y + 1) + x := by
    rw [head_N (by omega), Nat.mul_add_one]; omega
  have hne : head k (ch (k * y + x) 2 0) ≠ d := by
    rw [hh]; intro he; rw [he] at hC; omega
  have ha := arrived_false hF hne
  have e14 : embCh k (x - 1) y 14 = ch (k * y + x) 2 0 :=
    embCh_at (u := 1) (by omega) (by omega) 14 rfl (by omega) (by omega)
  rw [← e14] at hreach ha
  refine not_deadlockFree_of_winCertB hF minimalHops1_local hext hU hcert (ox := x - 1) (oy := y)
    ?_ hreach (by rw [hext.arrived]; exact ha) ?_
  · intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  · intro q hq
    rw [e14] at hq ha
    obtain ⟨dr, hdr, rfl⟩ := minimal1_of hext hU ha hq
    rw [hh, mem_productive, hC.1, hC.2] at hdr
    rw [hh] at hq ⊢
    rcases (by omega : dr = 1 ∨ dr = 2) with rfl | rfl
    · exact ⟨(42, 9), by simp, embCh_at (u := 4) (by omega) (by omega) 42 rfl (by omega)
        (by omega)⟩
    · exact absurd hq hno

theorem climb1NW (hF : MeshFamily Mk)
    (hcert : winCertB (Mk 3) (minimalHops1 3) [0, 1, 3, 4] 14 [(42, 9)] cert1NW = true)
    {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N) (hU : N.Within (minimalHops1 k)) :
    ∀ r x y d, d < k * k → d % k < x → x < k → d / k = y + 1 + r →
      N.lts.Reachable empty (fill [(ch (k * y + x) 2 0, d)]) → ¬ N.DeadlockFree := by
  intro r
  induction r with
  | zero =>
    intro x y d hd hdx hx hdy hreach
    refine square1NW hF hcert hext hU hd hdx hx (by omega) hreach fun hq => ?_
    have hC := coord (k := k) (a := k * (y + 1) + x) hx rfl
    have hh : head k (ch (k * y + x) 2 0) = k * (y + 1) + x := by
      rw [head_N (by omega), Nat.mul_add_one]; omega
    have hne : head k (ch (k * y + x) 2 0) ≠ d := by
      rw [hh]; intro he; rw [he] at hC; omega
    obtain ⟨dr, hdr, he⟩ := minimal1_of hext hU (arrived_false hF hne) hq
    rw [hh] at hdr he
    simp only [Prod.mk.injEq, and_true] at he
    obtain ⟨-, rfl, -⟩ := ch_inj (by omega) (by omega) (by have := productive_lt hdr; omega)
      (by omega) he
    rw [mem_productive, hC.1, hC.2] at hdr
    omega
  | succ r ih =>
    intro x y d hd hdx hx hdy hreach
    by_cases hN0 : (ch (k * (y + 1) + x) 2 0, d) ∈ N.route (ch (k * y + x) 2 0) d
    · have hC := coord (k := k) (a := k * (y + 1) + x) hx rfl
      have hh : head k (ch (k * y + x) 2 0) = k * (y + 1) + x := by
        rw [head_N (by omega), Nat.mul_add_one]; omega
      have hne : head k (ch (k * y + x) 2 0) ≠ d := by
        rw [hh]; intro he; rw [he] at hC; omega
      refine ih x (y + 1) d hd hdx hx (by omega) (reach_hop hreach
        (by rw [hext.arrived]; exact arrived_false hF hne) hN0 fun he => ?_)
      obtain ⟨h1, -, -⟩ := ch_inj (by omega) (by omega) (by omega) (by omega) he
      rw [Nat.mul_add_one] at h1; omega
    · exact square1NW hF hcert hext hU hd hdx hx (by omega) hreach hN0

/-- The mirror image of `square1NW`, south-bound. -/
theorem square1SW (hF : MeshFamily Mk)
    (hcert : winCertB (Mk 3) (minimalHops1 3) [0, 1, 3, 4] 46 [(12, 9)] cert1SW = true)
    {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N) (hU : N.Within (minimalHops1 k))
    {x y d : ℕ} (_hd : d < k * k) (hdx : d % k < x) (hx : x < k) (hy : y + 1 < k)
    (hdy : d / k ≤ y)
    (hreach : N.lts.Reachable empty (fill [(ch (k * (y + 1) + x) 3 0, d)]))
    (hno : y ≠ d / k → (ch (k * y + x) 3 0, d) ∉ N.route (ch (k * (y + 1) + x) 3 0) d) :
    ¬ N.DeadlockFree := by
  have hC := coord (k := k) (a := k * y + x) hx rfl
  have hh : head k (ch (k * (y + 1) + x) 3 0) = k * y + x := by
    rw [head_S (by omega), Nat.mul_add_one]; omega
  obtain ⟨dy, hdq⟩ : ∃ dy, d / k = dy := ⟨_, rfl⟩
  rw [hdq] at hdy hno
  have hne : head k (ch (k * (y + 1) + x) 3 0) ≠ d := by
    rw [hh]; intro he; rw [he] at hC; omega
  have ha := arrived_false hF hne
  have e46 : embCh k (x - 1) y 46 = ch (k * (y + 1) + x) 3 0 :=
    embCh_at (u := 4) (by omega) (by omega) 46 rfl (by omega) (by omega)
  rw [← e46] at hreach ha
  refine not_deadlockFree_of_winCertB hF minimalHops1_local hext hU hcert (ox := x - 1) (oy := y)
    ?_ hreach (by rw [hext.arrived]; exact ha) ?_
  · intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  · intro q hq
    rw [e46] at hq ha
    obtain ⟨dr, hdr, rfl⟩ := minimal1_of hext hU ha hq
    rw [hh, mem_productive, hC.1, hC.2, hdq] at hdr
    rw [hh] at hq ⊢
    rcases (by omega : dr = 1 ∨ dr = 3) with rfl | rfl
    · exact ⟨(12, 9), by simp, embCh_at (u := 1) (by omega) (by omega) 12 rfl (by omega)
        (by omega)⟩
    · exact absurd hq (hno (by omega))

theorem climb1SW (hF : MeshFamily Mk)
    (hcert : winCertB (Mk 3) (minimalHops1 3) [0, 1, 3, 4] 46 [(12, 9)] cert1SW = true)
    {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N) (hU : N.Within (minimalHops1 k)) :
    ∀ r x y d, d < k * k → d % k < x → x < k → y + 1 < k → d / k + r = y →
      N.lts.Reachable empty (fill [(ch (k * (y + 1) + x) 3 0, d)]) → ¬ N.DeadlockFree := by
  intro r
  induction r with
  | zero =>
    intro x y d hd hdx hx hy hdy hreach
    exact square1SW hF hcert hext hU hd hdx hx hy (by omega) hreach fun h => absurd hdy.symm h
  | succ r ih =>
    intro x y d hd hdx hx hy hdy hreach
    obtain ⟨dy, hdq⟩ : ∃ dy, d / k = dy := ⟨_, rfl⟩
    rw [hdq] at hdy
    by_cases hS0 : (ch (k * y + x) 3 0, d) ∈ N.route (ch (k * (y + 1) + x) 3 0) d
    · have hC := coord (k := k) (a := k * y + x) hx rfl
      have hh : head k (ch (k * (y + 1) + x) 3 0) = k * y + x := by
        rw [head_S (by omega), Nat.mul_add_one]; omega
      have hne : head k (ch (k * (y + 1) + x) 3 0) ≠ d := by
        rw [hh]; intro he; rw [he] at hC; omega
      have := ih x (y - 1) d hd hdx hx (by omega) (by rw [hdq]; omega)
      rw [show y - 1 + 1 = y by omega] at this
      refine this (reach_hop hreach (by rw [hext.arrived]; exact arrived_false hF hne) hS0
        fun he => ?_)
      obtain ⟨h1, -, -⟩ := ch_inj (by omega) (by omega) (by omega) (by omega) he
      rw [Nat.mul_add_one] at h1; omega
    · exact square1SW hF hcert hext hU hd hdx hx hy (by omega) hreach fun _ => hS0

/-- The mirror image of `square1NW`, east of the packet. -/
theorem square1NE (hF : MeshFamily Mk)
    (hcert : winCertB (Mk 3) (minimalHops1 3) [0, 1, 3, 4] 4 [(30, 9)] cert1NE = true)
    {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N) (hU : N.Within (minimalHops1 k))
    {x y d : ℕ} (hd : d < k * k) (hdx : x < d % k) (hdy : y + 1 ≤ d / k)
    (hreach : N.lts.Reachable empty (fill [(ch (k * y + x) 2 0, d)]))
    (hno : (ch (k * (y + 1) + x) 2 0, d) ∉ N.route (ch (k * y + x) 2 0) d) :
    ¬ N.DeadlockFree := by
  obtain ⟨hdxk, hdyk⟩ := coord_lt hd
  have hx : x < k := by omega
  have hC := coord (k := k) (a := k * (y + 1) + x) hx rfl
  have hh : head k (ch (k * y + x) 2 0) = k * (y + 1) + x := by
    rw [head_N (by omega), Nat.mul_add_one]; omega
  have hne : head k (ch (k * y + x) 2 0) ≠ d := by
    rw [hh]; intro he; rw [he] at hC; omega
  have ha := arrived_false hF hne
  have e4 : embCh k x y 4 = ch (k * y + x) 2 0 :=
    embCh_at (u := 0) (by omega) (by omega) 4 rfl (by omega) (by omega)
  rw [← e4] at hreach ha
  refine not_deadlockFree_of_winCertB hF minimalHops1_local hext hU hcert (ox := x) (oy := y)
    ?_ hreach (by rw [hext.arrived]; exact ha) ?_
  · intro u hu
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  · intro q hq
    rw [e4] at hq ha
    obtain ⟨dr, hdr, rfl⟩ := minimal1_of hext hU ha hq
    rw [hh, mem_productive, hC.1, hC.2] at hdr
    rw [hh] at hq ⊢
    rcases (by omega : dr = 0 ∨ dr = 2) with rfl | rfl
    · exact ⟨(30, 9), by simp, embCh_at (u := 3) (by omega) (by omega) 30 rfl (by omega)
        (by omega)⟩
    · exact absurd hq hno

theorem climb1NE (hF : MeshFamily Mk)
    (hcert : winCertB (Mk 3) (minimalHops1 3) [0, 1, 3, 4] 4 [(30, 9)] cert1NE = true)
    {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N) (hU : N.Within (minimalHops1 k)) :
    ∀ r x y d, d < k * k → x < d % k → d / k = y + 1 + r →
      N.lts.Reachable empty (fill [(ch (k * y + x) 2 0, d)]) → ¬ N.DeadlockFree := by
  intro r
  induction r with
  | zero =>
    intro x y d hd hdx hdy hreach
    refine square1NE hF hcert hext hU hd hdx (by omega) hreach fun hq => ?_
    obtain ⟨hdxk, -⟩ := coord_lt hd
    have hx : x < k := by omega
    have hC := coord (k := k) (a := k * (y + 1) + x) hx rfl
    have hh : head k (ch (k * y + x) 2 0) = k * (y + 1) + x := by
      rw [head_N (by omega), Nat.mul_add_one]; omega
    have hne : head k (ch (k * y + x) 2 0) ≠ d := by
      rw [hh]; intro he; rw [he] at hC; omega
    obtain ⟨dr, hdr, he⟩ := minimal1_of hext hU (arrived_false hF hne) hq
    rw [hh] at hdr he
    simp only [Prod.mk.injEq, and_true] at he
    obtain ⟨-, rfl, -⟩ := ch_inj (by omega) (by omega) (by have := productive_lt hdr; omega)
      (by omega) he
    rw [mem_productive, hC.1, hC.2] at hdr
    omega
  | succ r ih =>
    intro x y d hd hdx hdy hreach
    by_cases hN0 : (ch (k * (y + 1) + x) 2 0, d) ∈ N.route (ch (k * y + x) 2 0) d
    · obtain ⟨hdxk, -⟩ := coord_lt hd
      have hx : x < k := by omega
      have hC := coord (k := k) (a := k * (y + 1) + x) hx rfl
      have hh : head k (ch (k * y + x) 2 0) = k * (y + 1) + x := by
        rw [head_N (by omega), Nat.mul_add_one]; omega
      have hne : head k (ch (k * y + x) 2 0) ≠ d := by
        rw [hh]; intro he; rw [he] at hC; omega
      refine ih x (y + 1) d hd hdx (by omega) (reach_hop hreach
        (by rw [hext.arrived]; exact arrived_false hF hne) hN0 fun he => ?_)
      obtain ⟨h1, -, -⟩ := ch_inj (by omega) (by omega) (by omega) (by omega) he
      rw [Nat.mul_add_one] at h1; omega
    · exact square1NE hF hcert hext hU hd hdx (by omega) hreach hN0


/-! #### Correct for every size -/

theorem wf1_route_mem {k c d : ℕ} {q : ℕ × ℕ} (hq : q ∈ (westFirst1 k).route c d) :
    ∃ e ∈ westFirst k (head k c) d, q = (ch (head k c) e 0, d) := by
  simp only [turnMesh1, List.mem_map] at hq
  obtain ⟨e, he, rfl⟩ := hq
  exact ⟨e, he, rfl⟩

theorem wf1_closed (k : ℕ) : (westFirst1 k).Closed (wfLegal k) := by
  constructor
  · intro q hq
    obtain ⟨s, hs, hd, -, he⟩ := mem_allPairs.1 (show (q.1, q.2) ∈ allPairs (k * k) _ from hq)
    exact ⟨hd, s, 4, 0, he, hs, by omega, Or.inl ⟨rfl, rfl⟩⟩
  · intro c d q hl ha hq
    have hv := wfLegal_head hl
    obtain ⟨dr, hdr, rfl⟩ := wf1_route_mem hq
    dsimp only
    refine ⟨hl.1, _, dr, 0, rfl, hv, by omega, Or.inr ⟨westFirst_sub hdr, fun _ h => ?_⟩⟩
    unfold westFirst at hdr
    split_ifs at hdr with hw
    · simp at hdr; omega
    · omega

/-- Every hop of the single-channel west-first mesh lowers `wfRank`: its channel dependency
graph is acyclic. -/
theorem wf1_dep {k c c' : ℕ} (h : (westFirst1 k).Dep (wfLegal k) (westFirst1 k).route c c') :
    Prod.Lex (· < ·) (· < ·) (wfRank k c') (wfRank k c) := by
  obtain ⟨d, d', hl, ha, hq⟩ := h
  have hv := wfLegal_head hl
  have hd := hl.1
  obtain ⟨e, he, hq⟩ := wf1_route_mem hq
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, -⟩ := hq
  have hwe : (e = 1 → d % k < head k c % k) ∧ (e ≠ 1 → ¬ d % k < head k c % k) := by
    unfold westFirst at he
    split_ifs at he with hw
    · simp only [List.mem_singleton] at he; exact ⟨fun _ => hw, fun h => absurd he h⟩
    · refine ⟨fun h1 => ?_, fun _ => hw⟩
      subst h1
      rcases mem_productive.1 he with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  obtain ⟨-, hh'⟩ := head_ch (vc := 0) hv hd (by omega) (westFirst_sub he)
  obtain ⟨hvx, hvy⟩ := coord_lt hv
  obtain ⟨hdx, hdy⟩ := coord_lt hd
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
    -- after a northward or southward hop on virtual channel 0, no westward hop
    have hNS : vc = 0 → dr = 2 ∨ dr = 3 → e ≠ 1 := by
      intro hv h23 he1
      have h3 := hwf hv h23
      have h4 := hwe.1 he1
      rcases hh with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;> omega
    have hE : e = 0 → ¬ d % k < head k (ch u dr vc) % k := fun h0 => hwe.2 (by omega)
    rcases (show vc = 0 ∨ vc = 1 by omega) with rfl | rfl
    · rcases hh' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
        rcases hh with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;>
        simp only [wfRank_W, wfRank_E, wfRank_N, wfRank_S, Prod.lex_def, true_and,
          lt_self_iff_false, false_or, true_implies, false_implies, Nat.reduceEqDiff,
          or_true, true_or, ne_eq, not_true_eq_false, imp_false] at hwf hNS hE ⊢ <;> omega
    · rw [wfRank_vc1]
      rcases hh' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
        simp only [wfRank_W, wfRank_E, wfRank_N, wfRank_S, Prod.lex_def] <;> omega

theorem wf1_wf (k : ℕ) :
    WellFounded (flip ((westFirst1 k).Dep (wfLegal k) (westFirst1 k).route)) :=
  Network.wf_of_lexRank (wfRank k) fun _ _ h => wf1_dep h

theorem wf1_conn {k : ℕ} : ∀ c d, wfLegal k c d → (westFirst1 k).arrived c d = false →
    (westFirst1 k).route c d ≠ [] := by
  intro c d _ ha
  have hne : head k c ≠ d := by simpa [turnMesh1] using ha
  simp only [turnMesh1, ne_eq, List.map_eq_nil_iff]
  unfold westFirst
  split_ifs
  · simp
  · exact List.ne_nil_of_mem (xy_mem_productive hne)

theorem wfLegal_td {k c d : ℕ} (h : wfLegal k c d) : tdLegal k c d := by
  obtain ⟨hd, u, dr, vc, rfl, hu, hvc, h | ⟨h, -⟩⟩ := h
  · exact ⟨hd, u, dr, vc, rfl, hu, hvc, Or.inl h⟩
  · exact ⟨hd, u, dr, vc, rfl, hu, hvc, Or.inr h⟩

theorem wf1_dist {k c d : ℕ} {q : ℕ × ℕ} (hl : wfLegal k c d)
    (ha : (westFirst1 k).arrived c d = false) (hq : q ∈ (westFirst1 k).route c d) :
    meshDist k q.1 q.2 < meshDist k c d := by
  have := td_dist (turnMesh1_family westFirst_local) (wfLegal_td hl) ha hq; omega

end Mesh

/-- **West-first routing on a single virtual channel is deadlock and livelock free for every
size**, under every selection function: its channel dependency graph is acyclic. -/
theorem westFirst1_correct (k : ℕ) : (westFirst1 k).Correct :=
  ⟨(westFirst1 k).deadlockFree_of_escape (wf1_closed k) (westFirst1 k).route
      (fun _ _ _ _ _ h => h) wf1_conn (wf1_wf k),
    (westFirst1 k).livelockFree_of_ranking (wf1_closed k) (wf_chans_finite k) (meshDist k)
      fun _ _ _ hl ha hq => wf1_dist hl ha hq⟩

/-- **No packet starves**, for every size. -/
theorem westFirst1_starvationFree (k : ℕ) : (westFirst1 k).StarvationFree :=
  (westFirst1 k).starvationFree_of_escape_ranking (wf1_closed k) (wf_pairs_finite k)
    (westFirst1 k).route (fun _ _ _ _ _ h => h) wf1_conn (wf1_wf k) (meshDist k)
    fun _ _ _ hl ha hq => wf1_dist hl ha hq

/-- **Correct under wormhole switching too**, for packets of every length and every size. -/
theorem westFirst1_wormholeCorrect (k : ℕ) : (westFirst1 k).WormholeCorrect :=
  ⟨(westFirst1 k).wormholeDeadlockFree_of_cdg (wf1_closed k) wf1_conn (wf1_wf k),
    (westFirst1 k).wormholeLivelockFree_of_ranking (wf1_closed k) (meshDist k)
      fun _ _ _ hl ha hq => wf1_dist hl ha hq⟩

/-- **The single-channel west-first mesh takes shortest paths.** -/
theorem westFirst1_hops {k s d : ℕ} (hs : s < k * k) (hd : d < k * k) {q : ℕ × ℕ}
    {ls : List Unit} (h : (westFirst1 k).packetLTS.Path (ch s 4 0, d) ls q)
    (harr : (westFirst1 k).arrived q.1 q.2 = true) :
    ls.length = (s % k - d % k) + (d % k - s % k) + (s / k - d / k) + (d / k - s / k) :=
  family_hops (turnMesh1_family westFirst_local) hs hd h harr

/-! #### Maximal for every size -/

namespace Mesh

theorem t1_mem {turn : ℕ → ℕ → ℕ → List ℕ} {k c d dr : ℕ} (h : dr ∈ turn k (head k c) d) :
    (ch (head k c) dr 0, d) ∈ (turnMesh1 turn k).route c d :=
  List.mem_map.2 ⟨dr, h, rfl⟩

end Mesh

/-- **West-first routing is maximally adaptive on one virtual channel**, for every size: any
deadlock-free minimal routing function on a single virtual channel that permits all its hops
permits no other. -/
theorem westFirst1_maximal_all (k : ℕ) : (westFirst1 k).MaximallyAdaptive (minimalHops1 k) := by
  intro N hext hU hD c d hreach harr q hq
  by_contra hqN
  have hF := turnMesh1_family westFirst_local
  obtain ⟨hl, hr⟩ := reachable_single hF hext hreach
  obtain ⟨dr, hdr, rfl⟩ := minimal1_of hext hU harr hq
  have hnot : dr ∉ westFirst k (head k c) d := fun h => hqN (t1_mem h)
  have hr' := reach_hop hr (by rw [hext.arrived]; exact harr) hq
    (ch_head_ne hl (by have := productive_lt hdr; omega) (by omega))
  have hd := hl.1
  obtain ⟨hux, huy⟩ := coord_lt (tdLegal_head hl)
  unfold westFirst at hnot
  split_ifs at hnot with hwest
  swap; · exact hnot hdr
  rw [mem_productive] at hdr
  simp only [List.mem_singleton] at hnot
  generalize head k c = u at *
  have hu : k * (u / k) + u % k = u := Nat.div_add_mod u k
  obtain ⟨a, ha⟩ : ∃ a, d / k = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, u / k = b := ⟨_, rfl⟩
  rw [ha, hb] at hdr
  rw [hb] at huy hu
  rcases (by omega : dr = 2 ∨ dr = 3) with rfl | rfl
  · rw [← hu] at hr'
    exact climb1NW hF wf1_certNW hext hU (a - (b + 1)) (u % k) b d hd hwest hux (by omega) hr' hD
  · rw [show b = (b - 1) + 1 by omega] at hu
    rw [← hu] at hr'
    exact climb1SW hF wf1_certSW hext hU (b - 1 - a) (u % k) (b - 1) d hd hwest hux (by omega)
      (by omega) hr' hD

/-- **North-last routing is maximally adaptive on one virtual channel** as well. -/
theorem northLast1_maximal_all (k : ℕ) :
    (northLast1 k).MaximallyAdaptive (minimalHops1 k) := by
  intro N hext hU hD c d hreach harr q hq
  by_contra hqN
  have hF := turnMesh1_family northLast_local
  obtain ⟨hl, hr⟩ := reachable_single hF hext hreach
  obtain ⟨dr, hdr, rfl⟩ := minimal1_of hext hU harr hq
  have hnot : dr ∉ northLast k (head k c) d := fun h => hqN (t1_mem h)
  have hr' := reach_hop hr (by rw [hext.arrived]; exact harr) hq
    (ch_head_ne hl (by have := productive_lt hdr; omega) (by omega))
  have hd := hl.1
  obtain ⟨hux, huy⟩ := coord_lt (tdLegal_head hl)
  unfold northLast at hnot
  split_ifs at hnot with hn
  · exact hnot (hn ▸ hdr)
  have hdr2 : dr = 2 := by
    by_contra h2
    exact hnot (List.mem_filter.2 ⟨hdr, by simpa using h2⟩)
  subst hdr2
  have hside : d % k ≠ head k c % k := by
    intro he
    have hn2 : head k c / k < d / k := by
      rcases mem_productive.1 hdr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · omega
      · exact h
      · omega
    exact hn (by simp [productive, he, hn2, not_lt.2 hn2.le])
  rw [mem_productive] at hdr
  generalize head k c = u at *
  have hu : k * (u / k) + u % k = u := Nat.div_add_mod u k
  obtain ⟨a, ha⟩ : ∃ a, d / k = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, u / k = b := ⟨_, rfl⟩
  rw [ha, hb] at hdr
  rw [hb] at huy hu
  rw [← hu] at hr'
  rcases Nat.lt_or_gt_of_ne hside with hw | he
  · exact climb1NW hF nl1_certNW hext hU (a - (b + 1)) (u % k) b d hd hw hux (by omega) hr' hD
  · exact climb1NE hF nl1_certNE hext hU (a - (b + 1)) (u % k) b d hd he (by omega) hr' hD

/-- **XY routing is not maximally adaptive** on one virtual channel, for every size at least 2:
the single-channel west-first mesh permits every XY hop and more, and is deadlock free. -/
theorem xyMesh_not_maximal_all {k : ℕ} (hk : 2 ≤ k) :
    ¬ (xyMesh k).MaximallyAdaptive (minimalHops1 k) := by
  have h1 : (k + 1) % k = 1 := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have h2 : (k + 1) / k = 1 := by
    rw [Nat.add_div_left _ (by omega), Nat.div_eq_of_lt (by omega)]
  have hp : productive k 0 (k + 1) = [0, 2] := by simp [productive, h1, h2]
  have hx : xy k 0 (k + 1) = 0 := by simp [xy, h1]
  have hh : head k (ch 0 4 0) = 0 := head_inj
  refine not_maximallyAdaptive_of_extends (N' := westFirst1 k) ⟨rfl, rfl, fun c d q ha hq => ?_⟩
    (fun c d q ha hq => ?_) (westFirst1_correct k).1 (c := ch 0 4 0) (p := k + 1)
    (q := (ch 0 2 0, k + 1)) (pairReachable_of_mem_inject (mem_allPairs.2 ⟨0, by nlinarith,
      by nlinarith, by omega, rfl⟩)) (by simp [xyMesh, hh]) ?_ ?_
  · have hne : head k c ≠ d := by simpa [xyMesh] using ha
    simp only [xyMesh, List.mem_singleton] at hq
    subst hq
    refine t1_mem ?_
    unfold westFirst
    split_ifs with hw
    · rcases xy_cases (k := k) hne with h | h | h | h <;> simp [h.1] <;> omega
    · exact xy_mem_productive hne
  · obtain ⟨e, he, rfl⟩ := wf1_route_mem hq
    exact List.mem_map.2 ⟨e, westFirst_sub he, rfl⟩
  · have := t1_mem (turn := westFirst) (k := k) (c := ch 0 4 0) (d := k + 1) (dr := 2)
      (by rw [hh]; simp [westFirst, h1, hp])
    rwa [hh] at this
  · simp only [xyMesh, hh, hx, List.mem_singleton, Prod.mk.injEq]
    simp [ch]

#assert_standard_axioms westFirst1_correct westFirst1_starvationFree westFirst1_wormholeCorrect
  westFirst1_hops westFirst1_maximal_all northLast1_maximal_all xyMesh_not_maximal_all


/-! #### North-last on one virtual channel -/

namespace Mesh

theorem nl1_route_mem {k c d : ℕ} {q : ℕ × ℕ} (hq : q ∈ (northLast1 k).route c d) :
    ∃ e ∈ northLast k (head k c) d, q = (ch (head k c) e 0, d) := by
  simp only [turnMesh1, List.mem_map] at hq
  obtain ⟨e, he, rfl⟩ := hq
  exact ⟨e, he, rfl⟩

/-- A northward hop of the north-last turn model is the last direction left. -/
theorem northLast_N {k u d : ℕ} (h : 2 ∈ northLast k u d) : u % k = d % k := by
  unfold northLast at h
  split_ifs at h with hn
  · have h1 : ¬ u % k < d % k := fun h1 => by
      have : 0 ∈ productive k u d := mem_productive.2 (Or.inl ⟨rfl, h1⟩)
      rw [hn] at this; simp at this
    have h2 : ¬ d % k < u % k := fun h2 => by
      have : 1 ∈ productive k u d := mem_productive.2 (Or.inr (Or.inl ⟨rfl, h2⟩))
      rw [hn] at this; simp at this
    omega
  · simp at h

theorem nl1_closed (k : ℕ) : (northLast1 k).Closed (nlLegal k) := by
  constructor
  · intro q hq
    obtain ⟨s, hs, hd, -, he⟩ := mem_allPairs.1 (show (q.1, q.2) ∈ allPairs (k * k) _ from hq)
    exact ⟨hd, s, 4, 0, he, hs, by omega, Or.inl ⟨rfl, rfl⟩⟩
  · intro c d q hl ha hq
    have hv := tdLegal_head (nlLegal_td hl)
    obtain ⟨e, he, rfl⟩ := nl1_route_mem hq
    dsimp only
    exact ⟨hl.1, _, e, 0, rfl, hv, by omega, Or.inr ⟨northLast_sub he, fun _ h =>
      northLast_N (h ▸ he)⟩⟩

theorem nl1_dep {k c c' : ℕ} (h : (northLast1 k).Dep (nlLegal k) (northLast1 k).route c c') :
    Prod.Lex (· < ·) (· < ·) (nlRank k c') (nlRank k c) := by
  obtain ⟨d, d', hl, ha, hq⟩ := h
  have hv := tdLegal_head (nlLegal_td hl)
  have hd := hl.1
  obtain ⟨e, he, hq⟩ := nl1_route_mem hq
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, -⟩ := hq
  have hN : e = 2 → head k c % k = d % k := fun h2 => northLast_N (h2 ▸ he)
  obtain ⟨-, hh'⟩ := head_ch (vc := 0) hv hd (by omega) (northLast_sub he)
  obtain ⟨hvx, hvy⟩ := coord_lt hv
  obtain ⟨hdx, hdy⟩ := coord_lt hd
  have := Nat.zero_le (head k (ch (head k c) e 0) / k)
  have := Nat.zero_le (head k (ch (head k c) e 0) % k)
  have := Nat.zero_le (head k c / k)
  have := Nat.zero_le (head k c % k)
  have := Nat.zero_le (d / k)
  have := Nat.zero_le (d % k)
  obtain ⟨-, u, dr, vc, rfl, hu, hvc, ⟨rfl, rfl⟩ | ⟨hp, hnl⟩⟩ := hl
  · rw [nlRank_inj]
    rcases hh' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
      simp only [nlRank_W, nlRank_E, nlRank_N, nlRank_S, Prod.lex_def] <;> omega
  · obtain ⟨-, hh⟩ := head_ch hu hd hvc hp
    have := Nat.zero_le (u / k)
    have := Nat.zero_le (u % k)
    rcases (show vc = 0 ∨ vc = 1 by omega) with rfl | rfl
    · rcases hh' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
        rcases hh with ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ | ⟨rfl, h2⟩ <;>
        simp only [nlRank_W, nlRank_E, nlRank_N, nlRank_S, Prod.lex_def, true_and,
          lt_self_iff_false, false_or, true_implies, false_implies, Nat.reduceEqDiff]
          at hnl hN ⊢ <;> omega
    · rw [nlRank_vc1]
      rcases hh' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
        simp only [nlRank_W, nlRank_E, nlRank_N, nlRank_S, Prod.lex_def] <;> omega

theorem nl1_wf (k : ℕ) :
    WellFounded (flip ((northLast1 k).Dep (nlLegal k) (northLast1 k).route)) :=
  Network.wf_of_lexRank (nlRank k) fun _ _ h => nl1_dep h

theorem nl1_conn {k : ℕ} : ∀ c d, nlLegal k c d → (northLast1 k).arrived c d = false →
    (northLast1 k).route c d ≠ [] := by
  intro c d _ ha
  have hne : head k c ≠ d := by simpa [turnMesh1] using ha
  have hx := xy_mem_productive (k := k) hne
  simp only [turnMesh1, ne_eq, List.map_eq_nil_iff]
  unfold northLast
  split_ifs with hn
  · simp
  · intro h
    rw [List.filter_eq_nil_iff] at h
    rcases xy_cases (k := k) hne with h' | h' | h' | h' <;> rw [h'.1] at hx
    · exact h 0 hx (by decide)
    · exact h 1 hx (by decide)
    · exact hn (by simp [productive, h'.2.1, h'.2.2, not_lt.2 h'.2.2.le])
    · exact h 3 hx (by decide)

theorem nl1_dist {k c d : ℕ} {q : ℕ × ℕ} (hl : nlLegal k c d)
    (ha : (northLast1 k).arrived c d = false) (hq : q ∈ (northLast1 k).route c d) :
    meshDist k q.1 q.2 < meshDist k c d := by
  have := td_dist (turnMesh1_family northLast_local) (nlLegal_td hl) ha hq; omega

end Mesh

/-- **North-last routing on a single virtual channel is deadlock and livelock free for every
size.** -/
theorem northLast1_correct (k : ℕ) : (northLast1 k).Correct :=
  ⟨(northLast1 k).deadlockFree_of_escape (nl1_closed k) (northLast1 k).route
      (fun _ _ _ _ _ h => h) nl1_conn (nl1_wf k),
    (northLast1 k).livelockFree_of_ranking (nl1_closed k) (nl_chans_finite k) (meshDist k)
      fun _ _ _ hl ha hq => nl1_dist hl ha hq⟩

theorem northLast1_starvationFree (k : ℕ) : (northLast1 k).StarvationFree :=
  (northLast1 k).starvationFree_of_escape_ranking (nl1_closed k) (nl_pairs_finite k)
    (northLast1 k).route (fun _ _ _ _ _ h => h) nl1_conn (nl1_wf k) (meshDist k)
    fun _ _ _ hl ha hq => nl1_dist hl ha hq

/-- **Correct under wormhole switching too.** -/
theorem northLast1_wormholeCorrect (k : ℕ) : (northLast1 k).WormholeCorrect :=
  ⟨(northLast1 k).wormholeDeadlockFree_of_cdg (nl1_closed k) nl1_conn (nl1_wf k),
    (northLast1 k).wormholeLivelockFree_of_ranking (nl1_closed k) (meshDist k)
      fun _ _ _ hl ha hq => nl1_dist hl ha hq⟩

#assert_standard_axioms northLast1_correct northLast1_starvationFree northLast1_wormholeCorrect


/-! ### Latency: no routing function takes fewer hops -/

/-- A routing function on the `k × k` mesh that moves packets between neighbouring nodes only,
keeps their headers, and delivers a packet only at its destination.  Any number of virtual
channels, any adaptivity, detours included. -/
def NeighbourRouting (k : ℕ) (N : Network ℕ ℕ) : Prop :=
  (∀ c d, N.arrived c d = true → head k c = d) ∧
  ∀ c d q, N.arrived c d = false → q ∈ N.route c d →
    q.2 = d ∧ ∃ dr vc, dr ∈ neighbours k (head k c) ∧ vc < 2 ∧ q.1 = ch (head k c) dr vc

namespace Mesh

/-- A hop to a neighbour stays in the mesh and changes the distance to any node by at most one. -/
theorem neighbour_step {k u d dr vc : ℕ} (hu : u < k * k) (hdr : dr ∈ neighbours k u)
    (hvc : vc < 2) :
    head k (ch u dr vc) < k * k ∧
      meshDist k (ch (k * (u / k) + u % k) 4 0) d ≤ meshDist k (ch (head k (ch u dr vc)) 4 0) d + 1 := by
  obtain ⟨hux, huy⟩ := coord_lt hu
  have hu' := Nat.div_add_mod u k
  simp only [neighbours, List.mem_append, List.mem_ite_nil_right, List.mem_singleton] at hdr
  simp only [meshDist, head_inj, Nat.div_add_mod]
  rcases hdr with ((⟨h, rfl⟩ | ⟨h, rfl⟩) | ⟨h, rfl⟩) | ⟨h, rfl⟩
  · rw [head_E hvc]
    obtain ⟨h1, h2⟩ := coord (k := k) (a := u + 1) (x := u % k + 1) (y := u / k) h (by omega)
    exact ⟨lt_sq_of_coord (by omega) (by omega), by rw [h1, h2]; omega⟩
  · rw [head_W hvc]
    obtain ⟨h1, h2⟩ := coord (k := k) (a := u - 1) (x := u % k - 1) (y := u / k) (by omega)
      (by omega)
    exact ⟨lt_sq_of_coord (by omega) (by omega), by rw [h1, h2]; omega⟩
  · rw [head_N hvc]
    obtain ⟨h1, h2⟩ := coord (k := k) (a := u + k) (x := u % k) (y := u / k + 1) hux
      (by rw [Nat.mul_add_one]; omega)
    exact ⟨lt_sq_of_coord (by omega) (by omega), by rw [h1, h2]; omega⟩
  · rw [head_S hvc]
    have hy : k * (u / k) = k * (u / k - 1) + k := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel (by omega)]
    obtain ⟨h1, h2⟩ := coord (k := k) (a := u - k) (x := u % k) (y := u / k - 1) hux (by omega)
    exact ⟨lt_sq_of_coord (by omega) (by omega), by rw [h1, h2]; omega⟩

end Mesh

/-- **The hop-count lower bound.**  Under any neighbour routing of the `k × k` mesh, a packet
delivered from a channel whose head is a node of the mesh has taken at least as many hops as
the distance from that node to its destination. -/
theorem hops_lower_bound {k : ℕ} {N : Network ℕ ℕ} (hN : NeighbourRouting k N) :
    ∀ {q₀ q : ℕ × ℕ} {ls : List Unit}, head k q₀.1 < k * k → N.packetLTS.Path q₀ ls q →
      N.arrived q.1 q.2 = true → meshDist k q₀.1 q₀.2 ≤ ls.length := by
  intro q₀ q ls hq₀ h harr
  induction h with
  | nil s =>
    have : head k s.1 = s.2 := hN.1 _ _ harr
    simp [meshDist, this]
  | @cons s s' s'' l ls hst _ ih =>
    obtain ⟨ha, hq⟩ := hst
    obtain ⟨h2, dr, vc, hdr, hvc, h1⟩ := hN.2 _ _ _ ha hq
    obtain ⟨hlt, hle⟩ := neighbour_step (d := s.2) hq₀ hdr hvc
    have ih := ih (by rw [h1]; exact hlt) harr
    have e1 : meshDist k s.1 s.2 = meshDist k (ch (k * (head k s.1 / k) + head k s.1 % k) 4 0) s.2 := by
      simp only [meshDist, head_inj, Nat.div_add_mod]
    have e2 : meshDist k s'.1 s'.2 = meshDist k (ch (head k (ch (head k s.1) dr vc)) 4 0) s.2 := by
      simp only [meshDist, head_inj, h1, h2]
    simp only [List.length_cons]
    omega

/-- **Shortest paths are optimal for latency**: no neighbour routing of the mesh delivers a
packet in fewer hops than any routing function of a mesh family (XY, the turn-model meshes on
one or two virtual channels, ...). -/
theorem family_latency_optimal {Mk : ℕ → Network ℕ ℕ} (hF : MeshFamily Mk) {k s d : ℕ}
    (hs : s < k * k) (hd : d < k * k) {N : Network ℕ ℕ} (hN : NeighbourRouting k N)
    {ls ls' : List Unit} {q q' : ℕ × ℕ}
    (h : (Mk k).packetLTS.Path (ch s 4 0, d) ls q) (ha : (Mk k).arrived q.1 q.2 = true)
    (h' : N.packetLTS.Path (ch s 4 0, d) ls' q') (ha' : N.arrived q'.1 q'.2 = true) :
    ls.length ≤ ls'.length := by
  have e := family_hops hF hs hd h ha
  have := hops_lower_bound hN (q₀ := (ch s 4 0, d)) (by rw [head_inj]; exact hs) h' ha'
  simp only [meshDist, head_inj] at this
  omega

/-! ### XY routing for every size -/

namespace Mesh

theorem xy_closed (k : ℕ) : (xyMesh k).Closed (wfLegal k) := by
  constructor
  · intro q hq
    obtain ⟨s, hs, hd, -, he⟩ := mem_allPairs.1 (show (q.1, q.2) ∈ allPairs (k * k) _ from hq)
    exact ⟨hd, s, 4, 0, he, hs, by omega, Or.inl ⟨rfl, rfl⟩⟩
  · intro c d q hl ha hq
    have hv := wfLegal_head hl
    have hne : head k c ≠ d := by simpa [xyMesh] using ha
    simp only [xyMesh, List.mem_singleton] at hq
    subst hq
    dsimp only
    refine ⟨hl.1, _, _, 0, rfl, hv, by omega, Or.inr ⟨xy_mem_productive hne, fun _ h => ?_⟩⟩
    rcases xy_cases (k := k) hne with h' | h' | h' | h' <;> omega

theorem xy_dist {k c d : ℕ} {q : ℕ × ℕ} (hl : wfLegal k c d)
    (ha : (xyMesh k).arrived c d = false) (hq : q ∈ (xyMesh k).route c d) :
    meshDist k q.1 q.2 < meshDist k c d := by
  have hv := wfLegal_head hl
  have hd := hl.1
  have hne : head k c ≠ d := by simpa [xyMesh] using ha
  simp only [xyMesh, List.mem_singleton] at hq
  subst hq
  obtain ⟨-, hh⟩ := head_ch (vc := 0) hv hd (by omega) (xy_mem_productive hne)
  simp only [meshDist]
  rcases hh with h1 | h1 | h1 | h1 <;> omega

end Mesh

/-- **XY routing is deadlock and livelock free on every mesh**, on a single virtual channel. -/
theorem xyMesh_correct_all (k : ℕ) : (xyMesh k).Correct :=
  ⟨(xyMesh k).deadlockFree_of_escape (xy_closed k) (xyEscape k) (fun _ _ _ _ _ h => h)
      (fun _ _ _ _ => by simp [xyEscape]) (wf_wf k),
    (xyMesh k).livelockFree_of_ranking (xy_closed k) (wf_chans_finite k) (meshDist k)
      fun _ _ _ hl ha hq => xy_dist hl ha hq⟩

/-! ### Routing tables -/

/-- The routing decision of the router at node `u` for a packet injected there for `d`: the
channels it may take. -/
def decision (N : Network ℕ ℕ) (u d : ℕ) : List ℕ := (N.route (ch u 4 0) d).map Prod.fst

/-- The number of different routing decisions of the router at node `u` of the `k × k` mesh:
the number of entries of its routing table, once entries with the same decision are merged
(for example by destination ranges). -/
def tableSize (N : Network ℕ ℕ) (k u : ℕ) : ℕ :=
  (((Finset.range (k * k)).filter (· ≠ u)).image (decision N u)).card

theorem four_le_card {α : Type*} [DecidableEq α] {s : Finset α} {a b c e : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (he : e ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) : 4 ≤ s.card := by
  have h4 : ({a, b, c, e} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbe]), Finset.card_pair_eq_two_iff.2 hce]
  rw [← h4]
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> assumption

theorem fill_single {a x c p : ℕ} (h : fill [(a, x)] c = some p) : c = a ∧ p = x := by
  simp only [fill, Function.update_apply] at h
  split_ifs at h with hc
  · exact ⟨hc, (Option.some.inj h).symm⟩
  · simp [empty] at h

/-- **The routing-table lower bound.**  A deadlock-free minimal routing function of a mesh (on
any number of virtual channels) needs at least 4 different routing decisions at a router with
four neighbours: a packet for each neighbour must go straight to it. -/
theorem table_lower_bound {k u : ℕ} {N : Network ℕ ℕ}
    (harr : ∀ c d, N.arrived c d = (head k c == d))
    (hinj : ∀ d, d < k * k → d ≠ u → (ch u 4 0, d) ∈ N.inject)
    (hmin : ∀ c d q, N.arrived c d = false → q ∈ N.route c d →
      ∃ dr vc, dr ∈ productive k (head k c) d ∧ vc < 2 ∧ q.1 = ch (head k c) dr vc)
    (hD : N.DeadlockFree) (hx : 0 < u % k) (hx' : u % k + 1 < k) (hy : 0 < u / k)
    (hy' : u / k + 1 < k) : 4 ≤ tableSize N k u := by
  have hk : 0 < k := by omega
  have hu' := Nat.div_add_mod u k
  have hu : u < k * k := lt_sq_of_coord (by omega) (by omega)
  -- every packet injected at `u` has a hop: else it is deadlocked alone
  have hne : ∀ d, d < k * k → d ≠ u → decision N u d ≠ [] := by
    intro d hd hdu h
    have hr : N.lts.Reachable empty (fill [(ch u 4 0, d)]) :=
      Relation.ReflTransGen.single ⟨.inject _ _, StepWith.inject (f := empty) (hinj d hd hdu) rfl⟩
    obtain ⟨a, f', hmv, hst⟩ := hD _ N.adaptive_valid _ hr (fun he => by
      have : fill [(ch u 4 0, d)] (ch u 4 0) = none := by rw [he]; rfl
      simp [fill] at this)
    change N.StepWith N.adaptive _ a f' at hst
    cases hst with
    | inject => simp [Act.IsMove] at hmv
    | hop hp _ hq _ =>
      obtain ⟨rfl, rfl⟩ := fill_single hp
      simp only [decision, List.map_eq_nil_iff] at h
      simp only [adaptive, h, List.not_mem_nil] at hq
    | eject hp ha =>
      obtain ⟨rfl, rfl⟩ := fill_single hp
      rw [harr, head_inj, beq_iff_eq] at ha
      exact hdu ha.symm
  -- the decision for a neighbour only uses channels towards it
  have hdir : ∀ d e, d < k * k → d ≠ u → (∀ dr, dr ∈ productive k u d → dr = e) →
      ∀ c ∈ decision N u d, dir c = e := by
    intro d e hd hdu hp c hc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
    have ha : N.arrived (ch u 4 0) d = false := by
      rw [harr, head_inj]; simpa using hdu.symm
    obtain ⟨dr, vc, hdr, hvc, h⟩ := hmin _ _ _ ha hq
    rw [head_inj] at hdr h
    rw [h, dir_ch (by have := productive_lt hdr; omega) hvc]
    exact hp dr hdr
  have hdiff : ∀ d d' e e', d < k * k → d ≠ u → d' < k * k → d' ≠ u →
      (∀ dr, dr ∈ productive k u d → dr = e) → (∀ dr, dr ∈ productive k u d' → dr = e') →
      e ≠ e' → decision N u d ≠ decision N u d' := by
    intro d d' e e' hd hdu hd' hdu' hp hp' hee h
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (hne d hd hdu)
    have h1 := hdir d e hd hdu hp c hc
    rw [h] at hc
    exact hee (h1.symm.trans (hdir d' e' hd' hdu' hp' c hc))
  have hmem : ∀ d, d < k * k → d ≠ u →
      decision N u d ∈ ((Finset.range (k * k)).filter (· ≠ u)).image (decision N u) :=
    fun d hd hdu => Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hd, hdu⟩)
  -- the four neighbours
  obtain ⟨cE1, cE2⟩ := coord (k := k) (a := u + 1) (x := u % k + 1) (y := u / k) hx' (by omega)
  obtain ⟨cW1, cW2⟩ := coord (k := k) (a := u - 1) (x := u % k - 1) (y := u / k) (by omega)
    (by omega)
  obtain ⟨cN1, cN2⟩ := coord (k := k) (a := u + k) (x := u % k) (y := u / k + 1) (by omega)
    (by rw [Nat.mul_add_one]; omega)
  have hyk : k * (u / k) = k * (u / k - 1) + k := by
    rw [← Nat.mul_add_one, Nat.sub_add_cancel (by omega)]
  obtain ⟨cS1, cS2⟩ := coord (k := k) (a := u - k) (x := u % k) (y := u / k - 1) (by omega)
    (by omega)
  have lE : u + 1 < k * k := lt_sq_of_coord (by omega) (by omega)
  have lW : u - 1 < k * k := by omega
  have lN : u + k < k * k := lt_sq_of_coord (by omega) (by omega)
  have lS : u - k < k * k := by omega
  have pE : ∀ dr, dr ∈ productive k u (u + 1) → dr = 0 := fun dr h => by
    rw [mem_productive, cE1, cE2] at h; omega
  have pW : ∀ dr, dr ∈ productive k u (u - 1) → dr = 1 := fun dr h => by
    rw [mem_productive, cW1, cW2] at h; omega
  have pN : ∀ dr, dr ∈ productive k u (u + k) → dr = 2 := fun dr h => by
    rw [mem_productive, cN1, cN2] at h; omega
  have pS : ∀ dr, dr ∈ productive k u (u - k) → dr = 3 := fun dr h => by
    rw [mem_productive, cS1, cS2] at h; omega
  have nE : u + 1 ≠ u := by omega
  have nW : u - 1 ≠ u := by omega
  have nN : u + k ≠ u := by omega
  have nS : u - k ≠ u := by omega
  exact four_le_card (hmem _ lE nE) (hmem _ lW nW) (hmem _ lN nN) (hmem _ lS nS)
    (hdiff _ _ _ _ lE nE lW nW pE pW (by omega)) (hdiff _ _ _ _ lE nE lN nN pE pN (by omega))
    (hdiff _ _ _ _ lE nE lS nS pE pS (by omega)) (hdiff _ _ _ _ lW nW lN nN pW pN (by omega))
    (hdiff _ _ _ _ lW nW lS nS pW pS (by omega)) (hdiff _ _ _ _ lN nN lS nS pN pS (by omega))

/-- **XY routing needs at most 4 routing decisions per router**, on every mesh. -/
theorem xy_table_le (k u : ℕ) : tableSize (xyMesh k) k u ≤ 4 := by
  refine (Finset.card_le_card (t := (Finset.range 4).image fun e => [ch u e 0]) ?_).trans
    (Finset.card_image_le.trans (by simp))
  intro l hl
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hl
  exact Finset.mem_image.2 ⟨xy k u d, Finset.mem_range.2 (xy_lt k u d), by
    simp [decision, xyMesh, head_inj]⟩

/-- **XY routing is optimal for routing-table size**: exactly 4 decisions at every router with
four neighbours, the least any deadlock-free minimal routing function can make. -/
theorem xy_table {k u : ℕ} (hx : 0 < u % k) (hx' : u % k + 1 < k) (hy : 0 < u / k)
    (hy' : u / k + 1 < k) : tableSize (xyMesh k) k u = 4 := by
  refine le_antisymm (xy_table_le k u) (table_lower_bound (fun _ _ => rfl) (fun d hd hdu =>
    mem_allPairs.2 ⟨u, lt_sq_of_coord (by omega) (by omega), hd, hdu, rfl⟩) ?_
    (xyMesh_correct_all k).1 hx hx' hy hy')
  intro c d q ha hq
  have hne : head k c ≠ d := by simpa [xyMesh] using ha
  simp only [xyMesh, List.mem_singleton] at hq
  subst hq
  exact ⟨_, 0, xy_mem_productive hne, by omega, rfl⟩

/-- The relative position of the destination: which of the four directions are productive. -/
def sgn (k u d : ℕ) : Bool × Bool × Bool × Bool :=
  (decide (u % k < d % k), decide (d % k < u % k), decide (u / k < d / k), decide (d / k < u / k))

/-- **A turn-model mesh needs at most 8 routing decisions per router, on every mesh size**: its
decisions only depend on the relative position of the destination. -/
theorem turnDuato_table_le {turn : ℕ → ℕ → ℕ → List ℕ}
    (T : Bool × Bool × Bool × Bool → List ℕ) (hT : ∀ k u d, turn k u d = T (sgn k u d))
    (k u : ℕ) : tableSize (turnDuatoMesh turn k) k u ≤ 8 := by
  let prod (s : Bool × Bool × Bool × Bool) : List ℕ :=
    (if s.1 then [0] else []) ++ (if s.2.1 then [1] else []) ++ (if s.2.2.1 then [2] else []) ++
      (if s.2.2.2 then [3] else [])
  let xyOf (s : Bool × Bool × Bool × Bool) : ℕ :=
    if s.1 then 0 else if s.2.1 then 1 else if s.2.2.1 then 2 else 3
  let G (s : Bool × Bool × Bool × Bool) : List ℕ :=
    ch u (xyOf s) 0 :: ((T s).filter (· ≠ xyOf s)).map (fun dr => ch u dr 0) ++
      (prod s).map fun dr => ch u dr 1
  let S : Finset (Bool × Bool × Bool × Bool) :=
    {(true, false, true, false), (true, false, false, true), (true, false, false, false),
      (false, true, true, false), (false, true, false, true), (false, true, false, false),
      (false, false, true, false), (false, false, false, true)}
  refine (Finset.card_le_card (t := S.image G) ?_).trans (Finset.card_image_le.trans
    (by decide))
  intro l hl
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hl
  obtain ⟨-, hdu⟩ := Finset.mem_filter.1 hd
  refine Finset.mem_image.2 ⟨sgn k u d, ?_, ?_⟩
  · have hne : ¬ (u % k = d % k ∧ u / k = d / k) := fun ⟨h1, h2⟩ => hdu (by
      rw [← Nat.div_add_mod d k, ← h1, ← h2, Nat.div_add_mod])
    simp only [sgn, S, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
      decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · have hp : productive k u d = prod (sgn k u d) := by
      simp only [productive, prod, sgn, decide_eq_true_eq]
    have hx : xy k u d = xyOf (sgn k u d) := by
      simp only [xy, xyOf, sgn, decide_eq_true_eq]
    simp only [G, decision, turnDuatoMesh, head_inj, hp, hx, hT k u d, List.map_cons,
      List.map_append, List.map_map, Function.comp_def]

/-- The productive directions, from the relative position of the destination. -/
def prodT (s : Bool × Bool × Bool × Bool) : List ℕ :=
  (if s.1 then [0] else []) ++ (if s.2.1 then [1] else []) ++ (if s.2.2.1 then [2] else []) ++
    (if s.2.2.2 then [3] else [])

/-- The west-first turn model, from the relative position of the destination. -/
def westFirstT (s : Bool × Bool × Bool × Bool) : List ℕ := if s.2.1 then [1] else prodT s

/-- The north-last turn model, from the relative position of the destination. -/
def northLastT (s : Bool × Bool × Bool × Bool) : List ℕ :=
  if prodT s = [2] then [2] else (prodT s).filter (· ≠ 2)

theorem productive_sgn (k u d : ℕ) : productive k u d = prodT (sgn k u d) := by
  simp only [productive, prodT, sgn, decide_eq_true_eq]

theorem westFirst_sgn (k u d : ℕ) : westFirst k u d = westFirstT (sgn k u d) := by
  rw [westFirst, westFirstT, productive_sgn]
  simp only [sgn, decide_eq_true_eq]

theorem northLast_sgn (k u d : ℕ) : northLast k u d = northLastT (sgn k u d) := by
  rw [northLast, northLastT, productive_sgn]

theorem westFirstMesh_table_le (k u : ℕ) : tableSize (westFirstMesh k) k u ≤ 8 :=
  turnDuato_table_le _ westFirst_sgn k u

theorem northLastMesh_table_le (k u : ℕ) : tableSize (northLastMesh k) k u ≤ 8 :=
  turnDuato_table_le _ northLast_sgn k u

#assert_standard_axioms xyMesh_correct_all hops_lower_bound family_latency_optimal table_lower_bound xy_table
  westFirstMesh_table_le northLastMesh_table_le

end AsyncLean.Examples
