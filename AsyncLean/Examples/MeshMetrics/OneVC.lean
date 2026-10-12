/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshNorthLast

/-!
# Optimal mesh routing, metric by metric, part 1: one virtual channel, correct for every size

Part 1 of 3 of `AsyncLean.Examples.MeshMetrics`; that module has the overview.
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

end AsyncLean.Examples
