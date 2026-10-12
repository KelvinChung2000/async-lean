/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshMetrics.OneVC

/-!
# Optimal mesh routing, metric by metric, part 2: one virtual channel, maximal for every size; north-last

Part 2 of 3 of `AsyncLean.Examples.MeshMetrics`; that module has the overview.
-/

namespace AsyncLean.Examples

open Network Mesh

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

end AsyncLean.Examples
