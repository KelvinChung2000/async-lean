/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshMaximal.Certificates

/-!
# Maximally adaptive routing on meshes of every size, part 3: following the packet; maximal for every size

Part 3 of 3 of `AsyncLean.Examples.MeshMaximal`; that module has the overview.
-/

namespace AsyncLean.Examples

open Network Mesh

namespace Mesh

variable {Mk : ℕ → Network ℕ ℕ}

/-! ### Following the packet -/

theorem embCh_val {k ox oy u dr vc : ℕ} (hdr : dr < 5) (hvc : vc < 2) (c : ℕ)
    (hc : c = ch u dr vc) :
    embCh k ox oy c = ch (k * (oy + u / 3) + (ox + u % 3)) dr vc := by
  subst hc; exact embCh_ch hdr hvc

theorem minimal_of {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N)
    (hU : N.Within (minimalHops k)) {c d : ℕ} {q : ℕ × ℕ}
    (ha : (Mk k).arrived c d = false) (hq : q ∈ N.route c d) :
    ∃ dr vc, dr ∈ productive k (head k c) d ∧ vc < 2 ∧ q = (ch (head k c) dr vc, d) :=
  minimalHops_mem (hU c d q (by rw [hext.arrived]; exact ha) hq)

theorem arrived_false (hF : MeshFamily Mk) {k c d : ℕ} (h : head k c ≠ d) :
    (Mk k).arrived c d = false := (not_arrived hF).2 h

/-- **Following a north-bound packet that has to go west.**  A packet for `d` alone on virtual
channel 0 in the channel from node `(x, y)` north to `(x, y + 1)`, with `d` west of column `x`
and `r` rows above row `y + 1`: whatever minimal hops `N` adds to the turn-model mesh, the
packet runs into one of the two window deadlocks. -/
theorem climbNW (hF : MeshFamily Mk)
    (htop : winCertB (Mk 3) (minimalHops 3) [0, 1, 3, 4] 14 [(42, 9), (43, 9)] certNW = true)
    (hB : winCertB (Mk 3) (minimalHops 3) [0, 1, 3, 4, 6, 7] 14 [(42, 9), (43, 9), (45, 9)]
      certNWB = true)
    {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N)
    (hU : N.Within (minimalHops k)) :
    ∀ r x y d, d < k * k → d % k < x → x < k → d / k = y + 1 + r →
      N.lts.Reachable empty (fill [(ch (k * y + x) 2 0, d)]) → ¬ N.DeadlockFree := by
  intro r
  induction r with
  | zero =>
    intro x y d hd hdx hx hdy hreach
    have hk : 0 < k := by omega
    obtain ⟨hdxk, hdyk⟩ := coord_lt hd
    have hC := coord (k := k) (a := k * (y + 1) + x) hx rfl
    have hh : head k (ch (k * y + x) 2 0) = k * (y + 1) + x := by
      rw [head_N (by omega), Nat.mul_add_one]; omega
    have hne : head k (ch (k * y + x) 2 0) ≠ d := by
      rw [hh]; intro he; rw [he] at hC; omega
    have ha := arrived_false hF hne
    have e14 : embCh k (x - 1) y 14 = ch (k * y + x) 2 0 := by
      rw [embCh_val (u := 1) (dr := 2) (vc := 0) (by omega) (by omega) 14 rfl]
      congr 1; norm_num; omega
    rw [← e14] at hreach ha
    refine not_deadlockFree_of_winCertB hF minimalHops_local hext hU htop (ox := x - 1) (oy := y) ?_ hreach
      (by rw [hext.arrived]; exact ha) ?_
    · intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · intro q hq
      rw [e14] at hq ha
      obtain ⟨dr, vc, hdr, hvc, rfl⟩ := minimal_of hext hU ha hq
      rw [hh, mem_productive, hC.1, hC.2] at hdr
      obtain rfl : dr = 1 := by omega
      have e4 : ∀ c, c = ch 4 1 vc →
          embCh k (x - 1) y c = ch (head k (ch (k * y + x) 2 0)) 1 vc := by
        intro c hc
        rw [embCh_val (by omega) hvc c hc, hh]; congr 1; norm_num; omega
      rcases (by omega : vc = 0 ∨ vc = 1) with rfl | rfl
      · exact ⟨(42, 9), by simp, e4 42 rfl⟩
      · exact ⟨(43, 9), by simp, e4 43 rfl⟩
  | succ r ih =>
    intro x y d hd hdx hx hdy hreach
    have hk : 0 < k := by omega
    obtain ⟨hdxk, hdyk⟩ := coord_lt hd
    have hC := coord (k := k) (a := k * (y + 1) + x) hx rfl
    have hh : head k (ch (k * y + x) 2 0) = k * (y + 1) + x := by
      rw [head_N (by omega), Nat.mul_add_one]; omega
    have hne : head k (ch (k * y + x) 2 0) ≠ d := by
      rw [hh]; intro he; rw [he] at hC; omega
    have ha := arrived_false hF hne
    by_cases hN0 : (ch (k * (y + 1) + x) 2 0, d) ∈ N.route (ch (k * y + x) 2 0) d
    · -- the packet goes on north on virtual channel 0
      refine ih x (y + 1) d hd hdx hx (by omega) (reach_hop hreach
        (by rw [hext.arrived]; exact ha) hN0 fun he => ?_)
      obtain ⟨h1, -, -⟩ := ch_inj (by omega) (by omega) (by omega) (by omega) he
      rw [Nat.mul_add_one] at h1; omega
    · have e14 : embCh k (x - 1) y 14 = ch (k * y + x) 2 0 := by
        rw [embCh_val (u := 1) (dr := 2) (vc := 0) (by omega) (by omega) 14 rfl]
        congr 1; norm_num; omega
      rw [← e14] at hreach ha
      refine not_deadlockFree_of_winCertB hF minimalHops_local hext hU hB (ox := x - 1) (oy := y) ?_ hreach
        (by rw [hext.arrived]; exact ha) ?_
      · intro u hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      · intro q hq
        rw [e14] at hq ha
        obtain ⟨dr, vc, hdr, hvc, rfl⟩ := minimal_of hext hU ha hq
        rw [hh, mem_productive, hC.1, hC.2] at hdr
        have e4 : ∀ c dr', dr' < 5 → c = ch 4 dr' vc →
            embCh k (x - 1) y c = ch (head k (ch (k * y + x) 2 0)) dr' vc := by
          intro c dr' hdr' hc
          rw [embCh_val hdr' hvc c hc, hh]; congr 1; norm_num; omega
        rcases (by omega : dr = 1 ∨ dr = 2) with rfl | rfl <;>
          rcases (by omega : vc = 0 ∨ vc = 1) with rfl | rfl
        · exact ⟨(42, 9), by simp, e4 42 1 (by omega) rfl⟩
        · exact ⟨(43, 9), by simp, e4 43 1 (by omega) rfl⟩
        · rw [hh] at hq; exact absurd hq hN0
        · exact ⟨(45, 9), by simp, e4 45 2 (by omega) rfl⟩

theorem embCh_at {k ox oy u dr vc X Y : ℕ} (hdr : dr < 5) (hvc : vc < 2) (c : ℕ)
    (hc : c = ch u dr vc) (hx : ox + u % 3 = X) (hy : oy + u / 3 = Y) :
    embCh k ox oy c = ch (k * Y + X) dr vc := by
  rw [embCh_val hdr hvc c hc, hx, hy]

/-- **Following a south-bound packet that has to go west**: the mirror image of `climbNW`. -/
theorem climbSW (hF : MeshFamily Mk)
    (htop : winCertB (Mk 3) (minimalHops 3) [0, 1, 3, 4] 46 [(12, 9), (13, 9)] certSW = true)
    (hB : winCertB (Mk 3) (minimalHops 3) [0, 1, 3, 4, 6, 7] 76 [(42, 9), (43, 9), (47, 9)]
      certSWB = true)
    {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N)
    (hU : N.Within (minimalHops k)) :
    ∀ r x y d, d < k * k → d % k < x → x < k → y + 1 < k → d / k + r = y →
      N.lts.Reachable empty (fill [(ch (k * (y + 1) + x) 3 0, d)]) → ¬ N.DeadlockFree := by
  intro r
  induction r with
  | zero =>
    intro x y d hd hdx hx hy hdy hreach
    have hk : 0 < k := by omega
    obtain ⟨hdxk, hdyk⟩ := coord_lt hd
    obtain ⟨dy, hdq⟩ : ∃ dy, d / k = dy := ⟨_, rfl⟩
    rw [hdq] at hdy hdyk
    have hC := coord (k := k) (a := k * y + x) hx rfl
    have hh : head k (ch (k * (y + 1) + x) 3 0) = k * y + x := by
      rw [head_S (by omega), Nat.mul_add_one]; omega
    have hne : head k (ch (k * (y + 1) + x) 3 0) ≠ d := by
      rw [hh]; intro he; rw [he] at hC; omega
    have ha := arrived_false hF hne
    have e46 : embCh k (x - 1) y 46 = ch (k * (y + 1) + x) 3 0 :=
      embCh_at (u := 4) (by omega) (by omega) 46 rfl (by omega) (by omega)
    rw [← e46] at hreach ha
    refine not_deadlockFree_of_winCertB hF minimalHops_local hext hU htop (ox := x - 1) (oy := y) ?_ hreach
      (by rw [hext.arrived]; exact ha) ?_
    · intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · intro q hq
      rw [e46] at hq ha
      obtain ⟨dr, vc, hdr, hvc, rfl⟩ := minimal_of hext hU ha hq
      rw [hh, mem_productive, hC.1, hC.2, hdq] at hdr
      obtain rfl : dr = 1 := by omega
      rw [hh]
      rcases (by omega : vc = 0 ∨ vc = 1) with rfl | rfl
      · exact ⟨(12, 9), by simp, embCh_at (u := 1) (by omega) (by omega) 12 rfl (by omega)
          (by omega)⟩
      · exact ⟨(13, 9), by simp, embCh_at (u := 1) (by omega) (by omega) 13 rfl (by omega)
          (by omega)⟩
  | succ r ih =>
    intro x y d hd hdx hx hy hdy hreach
    have hk : 0 < k := by omega
    obtain ⟨hdxk, hdyk⟩ := coord_lt hd
    -- `omega` does not see through `d / k`: name it
    obtain ⟨dy, hdq⟩ : ∃ dy, d / k = dy := ⟨_, rfl⟩
    rw [hdq] at hdy hdyk
    have hy1 : y - 1 + 1 < k := by omega
    have hdy1 : d / k + r = y - 1 := by rw [hdq]; omega
    have hC := coord (k := k) (a := k * y + x) hx rfl
    have hh : head k (ch (k * (y + 1) + x) 3 0) = k * y + x := by
      rw [head_S (by omega), Nat.mul_add_one]; omega
    have hne : head k (ch (k * (y + 1) + x) 3 0) ≠ d := by
      rw [hh]; intro he; rw [he] at hC; omega
    have ha := arrived_false hF hne
    by_cases hS0 : (ch (k * y + x) 3 0, d) ∈ N.route (ch (k * (y + 1) + x) 3 0) d
    · -- the packet goes on south on virtual channel 0
      have := ih x (y - 1) d hd hdx hx hy1 hdy1
      rw [show y - 1 + 1 = y by omega] at this
      refine this (reach_hop hreach (by rw [hext.arrived]; exact ha) hS0 fun he => ?_)
      obtain ⟨h1, -, -⟩ := ch_inj (by omega) (by omega) (by omega) (by omega) he
      rw [Nat.mul_add_one] at h1; omega
    · have e76 : embCh k (x - 1) (y - 1) 76 = ch (k * (y + 1) + x) 3 0 :=
        embCh_at (u := 7) (by omega) (by omega) 76 rfl (by omega) (by omega)
      rw [← e76] at hreach ha
      refine not_deadlockFree_of_winCertB hF minimalHops_local hext hU hB (ox := x - 1) (oy := y - 1) ?_ hreach
        (by rw [hext.arrived]; exact ha) ?_
      · intro u hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      · intro q hq
        rw [e76] at hq ha
        obtain ⟨dr, vc, hdr, hvc, rfl⟩ := minimal_of hext hU ha hq
        rw [hh, mem_productive, hC.1, hC.2, hdq] at hdr
        rw [hh]
        rcases (by omega : dr = 1 ∨ dr = 3) with rfl | rfl <;>
          rcases (by omega : vc = 0 ∨ vc = 1) with rfl | rfl
        · exact ⟨(42, 9), by simp, embCh_at (u := 4) (by omega) (by omega) 42 rfl (by omega)
            (by omega)⟩
        · exact ⟨(43, 9), by simp, embCh_at (u := 4) (by omega) (by omega) 43 rfl (by omega)
            (by omega)⟩
        · rw [hh] at hq; exact absurd hq hS0
        · exact ⟨(47, 9), by simp, embCh_at (u := 4) (by omega) (by omega) 47 rfl (by omega)
            (by omega)⟩

/-- **Following a north-bound packet that has to go east**: the mirror image of `climbNW`. -/
theorem climbNE (hF : MeshFamily Mk)
    (htop : winCertB (Mk 3) (minimalHops 3) [0, 1, 3, 4] 4 [(30, 9), (31, 9)] certNE = true)
    (hB : winCertB (Mk 3) (minimalHops 3) [0, 1, 3, 4, 6, 7] 4 [(30, 9), (31, 9), (35, 9)]
      certNEB = true)
    {k : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N)
    (hU : N.Within (minimalHops k)) :
    ∀ r x y d, d < k * k → x < d % k → d / k = y + 1 + r →
      N.lts.Reachable empty (fill [(ch (k * y + x) 2 0, d)]) → ¬ N.DeadlockFree := by
  intro r
  induction r with
  | zero =>
    intro x y d hd hdx hdy hreach
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
    refine not_deadlockFree_of_winCertB hF minimalHops_local hext hU htop (ox := x) (oy := y) ?_ hreach
      (by rw [hext.arrived]; exact ha) ?_
    · intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · intro q hq
      rw [e4] at hq ha
      obtain ⟨dr, vc, hdr, hvc, rfl⟩ := minimal_of hext hU ha hq
      rw [hh, mem_productive, hC.1, hC.2] at hdr
      obtain rfl : dr = 0 := by omega
      rw [hh]
      rcases (by omega : vc = 0 ∨ vc = 1) with rfl | rfl
      · exact ⟨(30, 9), by simp, embCh_at (u := 3) (by omega) (by omega) 30 rfl (by omega)
          (by omega)⟩
      · exact ⟨(31, 9), by simp, embCh_at (u := 3) (by omega) (by omega) 31 rfl (by omega)
          (by omega)⟩
  | succ r ih =>
    intro x y d hd hdx hdy hreach
    obtain ⟨hdxk, hdyk⟩ := coord_lt hd
    have hx : x < k := by omega
    have hC := coord (k := k) (a := k * (y + 1) + x) hx rfl
    have hh : head k (ch (k * y + x) 2 0) = k * (y + 1) + x := by
      rw [head_N (by omega), Nat.mul_add_one]; omega
    have hne : head k (ch (k * y + x) 2 0) ≠ d := by
      rw [hh]; intro he; rw [he] at hC; omega
    have ha := arrived_false hF hne
    by_cases hN0 : (ch (k * (y + 1) + x) 2 0, d) ∈ N.route (ch (k * y + x) 2 0) d
    · refine ih x (y + 1) d hd hdx (by omega) (reach_hop hreach
        (by rw [hext.arrived]; exact ha) hN0 fun he => ?_)
      obtain ⟨h1, -, -⟩ := ch_inj (by omega) (by omega) (by omega) (by omega) he
      rw [Nat.mul_add_one] at h1; omega
    · have e4 : embCh k x y 4 = ch (k * y + x) 2 0 :=
        embCh_at (u := 0) (by omega) (by omega) 4 rfl (by omega) (by omega)
      rw [← e4] at hreach ha
      refine not_deadlockFree_of_winCertB hF minimalHops_local hext hU hB (ox := x) (oy := y) ?_ hreach
        (by rw [hext.arrived]; exact ha) ?_
      · intro u hu
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
      · intro q hq
        rw [e4] at hq ha
        obtain ⟨dr, vc, hdr, hvc, rfl⟩ := minimal_of hext hU ha hq
        rw [hh, mem_productive, hC.1, hC.2] at hdr
        rw [hh]
        rcases (by omega : dr = 0 ∨ dr = 2) with rfl | rfl <;>
          rcases (by omega : vc = 0 ∨ vc = 1) with rfl | rfl
        · exact ⟨(30, 9), by simp, embCh_at (u := 3) (by omega) (by omega) 30 rfl (by omega)
            (by omega)⟩
        · exact ⟨(31, 9), by simp, embCh_at (u := 3) (by omega) (by omega) 31 rfl (by omega)
            (by omega)⟩
        · rw [hh] at hq; exact absurd hq hN0
        · exact ⟨(35, 9), by simp, embCh_at (u := 3) (by omega) (by omega) 35 rfl (by omega)
            (by omega)⟩

/-- A productive hop leaves the channel the packet is in. -/
theorem ch_head_ne {k c d e vc : ℕ} (hl : tdLegal k c d) (he : e < 4) (hvc : vc < 2) :
    ch (head k c) e vc ≠ c := by
  obtain ⟨hd, u, dr', vc', rfl, hu, hvc', hdr'⟩ := hl
  intro h
  have hdr5 : dr' < 5 := by
    rcases hdr' with ⟨rfl, -⟩ | h
    · omega
    · have := productive_lt h; omega
  obtain ⟨hu', rfl, rfl⟩ := ch_inj (by omega) hvc hdr5 hvc' h
  rcases hdr' with ⟨h4, -⟩ | hp
  · omega
  · obtain ⟨-, hh⟩ := head_ch hu hd hvc' hp
    rw [hu'] at hh
    rcases hh with ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩ <;> omega

theorem td_route_eq {turn : ℕ → ℕ → ℕ → List ℕ} {k c d : ℕ} :
    (turnDuatoMesh turn k).route c d =
      (ch (head k c) (xy k (head k c) d) 0, d) ::
        (((turn k (head k c) d).filter (· ≠ xy k (head k c) d)).map
          (fun dr => (ch (head k c) dr 0, d)) ++
        (productive k (head k c) d).map fun dr => (ch (head k c) dr 1, d)) := rfl

theorem td_mem_vc0 {turn : ℕ → ℕ → ℕ → List ℕ} {k c d dr : ℕ}
    (h : dr = xy k (head k c) d ∨ dr ∈ turn k (head k c) d) :
    (ch (head k c) dr 0, d) ∈ (turnDuatoMesh turn k).route c d := by
  rw [td_route_eq]
  by_cases hx : dr = xy k (head k c) d
  · rw [hx]; exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2
      ⟨dr, List.mem_filter.2 ⟨h.resolve_left hx, by simpa using hx⟩, rfl⟩))

theorem td_mem_vc1 {turn : ℕ → ℕ → ℕ → List ℕ} {k c d dr : ℕ}
    (h : dr ∈ productive k (head k c) d) :
    (ch (head k c) dr 1, d) ∈ (turnDuatoMesh turn k).route c d := by
  rw [td_route_eq]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map.2 ⟨dr, h, rfl⟩))

/-- **The hops a minimal routing function can add to the west-first mesh**: a northward or
southward hop on virtual channel 0, of a packet that still has to go west. -/
theorem wf_extra {k c d dr vc : ℕ} (hdr : dr ∈ productive k (head k c) d) (hvc : vc < 2)
    (h : (ch (head k c) dr vc, d) ∉ (westFirstMesh k).route c d) :
    vc = 0 ∧ d % k < head k c % k ∧ (dr = 2 ∨ dr = 3) := by
  have hvc0 : vc = 0 := by
    rcases (by omega : vc = 0 ∨ vc = 1) with rfl | rfl
    · rfl
    · exact absurd (td_mem_vc1 hdr) h
  subst hvc0
  have hwf : dr ∉ westFirst k (head k c) d := fun h' => h (td_mem_vc0 (Or.inr h'))
  unfold westFirst at hwf
  split_ifs at hwf with hw
  · refine ⟨rfl, hw, ?_⟩
    rw [mem_productive] at hdr
    simp only [List.mem_singleton] at hwf
    omega
  · exact absurd hdr hwf

/-- **The hops a minimal routing function can add to the north-last mesh**: a northward hop on
virtual channel 0, of a packet that still has to go east or west. -/
theorem nl_extra {k c d dr vc : ℕ} (hdr : dr ∈ productive k (head k c) d) (hvc : vc < 2)
    (h : (ch (head k c) dr vc, d) ∉ (northLastMesh k).route c d) :
    vc = 0 ∧ dr = 2 ∧ d % k ≠ head k c % k := by
  have hvc0 : vc = 0 := by
    rcases (by omega : vc = 0 ∨ vc = 1) with rfl | rfl
    · rfl
    · exact absurd (td_mem_vc1 hdr) h
  subst hvc0
  have hnl : dr ∉ northLast k (head k c) d := fun h' => h (td_mem_vc0 (Or.inr h'))
  unfold northLast at hnl
  split_ifs at hnl with hn
  · exact absurd (hn ▸ hdr) hnl
  · have hdr2 : dr = 2 := by
      by_contra h2
      exact hnl (List.mem_filter.2 ⟨hdr, by simpa using h2⟩)
    subst hdr2
    refine ⟨rfl, rfl, fun he => hn ?_⟩
    have hn2 : head k c / k < d / k := by
      rcases mem_productive.1 hdr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · omega
      · exact h
      · omega
    simp [productive, he, hn2, not_lt.2 hn2.le]

end Mesh

/-! ### Maximal for every size -/

/-- **The west-first mesh of every size is maximally adaptive**: any deadlock-free minimal
routing function on two virtual channels that permits all its hops permits no other. -/
theorem westFirstMesh_maximal_all (k : ℕ) :
    (westFirstMesh k).MaximallyAdaptive (minimalHops k) := by
  intro N hext hU hD c d hreach harr q hq
  by_contra hqN
  obtain ⟨hl, hr⟩ := reachable_single (turnDuato_family westFirst_local) hext hreach
  obtain ⟨dr, vc, hdr, hvc, rfl⟩ := minimal_of hext hU harr hq
  obtain ⟨rfl, hwest, hdr23⟩ := wf_extra hdr hvc hqN
  have hr' := reach_hop hr (by rw [hext.arrived]; exact harr) hq
    (ch_head_ne hl (by have := productive_lt hdr; omega) (by omega))
  have hd := hl.1
  obtain ⟨hux, huy⟩ := coord_lt (tdLegal_head hl)
  rw [mem_productive] at hdr
  generalize head k c = u at *
  have hu : k * (u / k) + u % k = u := Nat.div_add_mod u k
  obtain ⟨a, ha⟩ : ∃ a, d / k = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, u / k = b := ⟨_, rfl⟩
  rw [ha, hb] at hdr
  rw [hb] at huy hu
  rcases hdr23 with rfl | rfl
  · rw [← hu] at hr'
    exact climbNW (turnDuato_family westFirst_local) wf_certNW wf_certNWB hext hU (a - (b + 1)) (u % k) b d hd
      hwest hux (by omega) hr' hD
  · rw [show b = (b - 1) + 1 by omega] at hu
    rw [← hu] at hr'
    exact climbSW (turnDuato_family westFirst_local) wf_certSW wf_certSWB hext hU (b - 1 - a) (u % k) (b - 1) d hd
      hwest hux (by omega) (by omega) hr' hD

/-- **The north-last mesh of every size is maximally adaptive** as well. -/
theorem northLastMesh_maximal_all (k : ℕ) :
    (northLastMesh k).MaximallyAdaptive (minimalHops k) := by
  intro N hext hU hD c d hreach harr q hq
  by_contra hqN
  obtain ⟨hl, hr⟩ := reachable_single (turnDuato_family northLast_local) hext hreach
  obtain ⟨dr, vc, hdr, hvc, rfl⟩ := minimal_of hext hU harr hq
  obtain ⟨rfl, rfl, hside⟩ := nl_extra hdr hvc hqN
  have hr' := reach_hop hr (by rw [hext.arrived]; exact harr) hq
    (ch_head_ne hl (by omega) (by omega))
  have hd := hl.1
  obtain ⟨hux, huy⟩ := coord_lt (tdLegal_head hl)
  obtain ⟨hdx, -⟩ := coord_lt hd
  rw [mem_productive] at hdr
  generalize head k c = u at *
  have hu : k * (u / k) + u % k = u := Nat.div_add_mod u k
  obtain ⟨a, ha⟩ : ∃ a, d / k = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, u / k = b := ⟨_, rfl⟩
  rw [ha, hb] at hdr
  rw [hb] at huy hu
  rw [← hu] at hr'
  rcases Nat.lt_or_gt_of_ne hside with hw | he
  · exact climbNW (turnDuato_family northLast_local) nl_certNW nl_certNWB hext hU (a - (b + 1)) (u % k) b d hd
      hw hux (by omega) hr' hD
  · exact climbNE (turnDuato_family northLast_local) nl_certNE nl_certNEB hext hU (a - (b + 1)) (u % k) b d hd
      he (by omega) hr' hD

/-- Maximal under wormhole switching too, for every size. -/
theorem westFirstMesh_maximal_all_wormhole (k : ℕ) (N : Network ℕ ℕ)
    (h : (westFirstMesh k).Extends N) (hU : N.Within (minimalHops k))
    (hW : N.WormholeDeadlockFree) :
    ∀ c d, (westFirstMesh k).PairReachable (c, d) → (westFirstMesh k).arrived c d = false →
      ∀ q ∈ N.route c d, q ∈ (westFirstMesh k).route c d :=
  (westFirstMesh_maximal_all k).wormhole N h hU hW

/-- A packet injected at node `0` for node `k + 1` (one hop east and one north) may go north
first on virtual channel 0 in the west-first mesh, but not in the north-last mesh nor in Duato's
mesh; every mesh of size at least 2. -/
theorem westFirst_hop_extra {k : ℕ} (hk : 2 ≤ k) :
    (ch 0 2 0, k + 1) ∈ (westFirstMesh k).route (ch 0 4 0) (k + 1) ∧
      (ch 0 2 0, k + 1) ∉ (northLastMesh k).route (ch 0 4 0) (k + 1) ∧
      (ch 0 2 0, k + 1) ∉ (duatoMesh k).route (ch 0 4 0) (k + 1) := by
  have h1 : (k + 1) % k = 1 := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have h2 : (k + 1) / k = 1 := by
    rw [Nat.add_div_left _ (by omega), Nat.div_eq_of_lt (by omega)]
  have hp : productive k 0 (k + 1) = [0, 2] := by
    simp [productive, h1, h2]
  have hx : xy k 0 (k + 1) = 0 := by simp [xy, h1]
  have hh : head k (ch 0 4 0) = 0 := head_inj
  refine ⟨?_, ?_, ?_⟩
  · have := td_mem_vc0 (turn := westFirst) (k := k) (c := ch 0 4 0) (d := k + 1) (dr := 2)
      (Or.inr (by rw [hh]; simp [westFirst, h1, hp]))
    rwa [hh] at this
  · simp only [turnDuatoMesh, hh, hp, hx, northLast, List.mem_cons, List.mem_append,
      List.mem_map, List.mem_filter, Prod.mk.injEq]
    simp [ch]
  · simp only [duatoMesh, hh, hp, hx, List.mem_cons, List.mem_map, Prod.mk.injEq]
    simp [ch]

theorem inject_mem {k : ℕ} (hk : 2 ≤ k) :
    (ch 0 4 0, k + 1) ∈ (northLastMesh k).inject := by
  refine mem_allPairs.2 ⟨0, by nlinarith, by nlinarith, by omega, rfl⟩

/-- **No common improvement, for every size**: on every mesh of size at least 2, no
deadlock-free minimal routing function is at least as adaptive as both the west-first and the
north-last mesh. -/
theorem no_common_improvement_all {k : ℕ} (hk : 2 ≤ k) (N : Network ℕ ℕ)
    (h₁ : (westFirstMesh k).Extends N) (h₂ : (northLastMesh k).Extends N)
    (hU : N.Within (minimalHops k)) : ¬ N.DeadlockFree :=
  (northLastMesh_maximal_all k).not_deadlockFree (pairReachable_of_mem_inject (inject_mem hk))
    (by simp [turnDuatoMesh, head_inj]) (westFirst_hop_extra hk).1 (westFirst_hop_extra hk).2.1
    h₂ h₁ hU

/-- **Duato's mesh is not maximally adaptive**, for every size at least 2. -/
theorem duatoMesh_not_maximal_all {k : ℕ} (hk : 2 ≤ k) :
    ¬ (duatoMesh k).MaximallyAdaptive (minimalHops k) :=
  not_maximallyAdaptive_of_extends (duatoMesh_extends westFirst k)
    (turnDuatoMesh_within k fun _ _ _ => westFirst_sub) (westFirstMesh_correct k).1
    (pairReachable_of_mem_inject (inject_mem hk)) (by simp [duatoMesh, head_inj])
    (westFirst_hop_extra hk).1 (westFirst_hop_extra hk).2.2

#assert_standard_axioms Network.not_deadlockFree_of_runGoodB Mesh.not_deadlockFree_of_winCertB
  westFirstMesh_maximal_all northLastMesh_maximal_all westFirstMesh_maximal_all_wormhole
  no_common_improvement_all duatoMesh_not_maximal_all

end AsyncLean.Examples
