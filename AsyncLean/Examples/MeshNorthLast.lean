/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshMaximal

/-!
# The north-last mesh of every size

`AsyncLean.Examples.OptimalRouting` proves the west-first mesh correct for every size; here the
same is done for the north-last mesh (`northLastMesh k`): virtual channel 0 offers the XY hop and
every hop of the north-last turn model, virtual channel 1 every productive hop.

* `northLastMesh_correct_all k` : deadlock and livelock free under every selection function.
* `northLastMesh_starvationFree_all k` : no packet starves along a strongly fair run.
* `northLastMesh_correctWith k` : the same for every selection that never refuses a free XY
  escape hop (`Network.EscapeSel`), for example a congestion-aware one.
* `family_hops` : every packet of every mesh family (`MeshFamily`), the north-last mesh
  included, takes exactly as many hops as the distance to its destination.

The escape hops (XY on virtual channel 0) follow the order `nlRank`: rows from north to south
for the channels of virtual channel 0 that are not northward (within a row, eastward channels
from west to east and westward ones from east to west), then the northward channels from south
to north.  On the legal pairs (`nlLegal`), a packet on a northward channel of virtual channel 0
has no eastward or westward hop left, so after it only northward escape hops follow.

Under wormhole switching Duato's condition fails for the north-last mesh with these escape
channels: a packet that took a southward hop on virtual channel 0 while it still had to go east
or west can turn on virtual channel 0 after detours on virtual channel 1, and these indirect
dependencies close cycles.  The west-first mesh does not have this problem
(`westFirstMesh_wormholeCorrect`).
-/

namespace AsyncLean.Examples

open Network Mesh

namespace Mesh

/-! ### Distance -/

/-- The distance from the head of a channel to the destination. -/
def meshDist (k c d : ℕ) : ℕ :=
  (head k c % k - d % k) + (d % k - head k c % k) + (head k c / k - d / k) + (d / k - head k c / k)

theorem tdLegal_finite (k : ℕ) : {q : ℕ × ℕ | tdLegal k q.1 q.2}.Finite := by
  refine (Finset.finite_toSet (Finset.range (10 * (k * k)) ×ˢ Finset.range (k * k))).subset ?_
  rintro ⟨c, d⟩ ⟨hd, u, dr, vc, rfl, hu, hvc, hdr⟩
  have : dr < 5 := by
    rcases hdr with ⟨rfl, -⟩ | hp
    · omega
    · have := productive_lt hp; omega
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio, ch]
  omega

variable {Mk : ℕ → Network ℕ ℕ}

/-- Every hop of a mesh family brings the packet exactly one step closer. -/
theorem td_dist (hF : MeshFamily Mk) {k c d : ℕ} {q : ℕ × ℕ} (hl : tdLegal k c d)
    (ha : (Mk k).arrived c d = false) (hq : q ∈ (Mk k).route c d) :
    meshDist k q.1 q.2 + 1 = meshDist k c d := by
  have hv := tdLegal_head hl
  have hd := hl.1
  have hne : head k c ≠ d := (not_arrived hF).1 ha
  obtain ⟨dr, vc, hdr, hvc, rfl⟩ := hF.route k c d q hne hq
  obtain ⟨-, hh⟩ := head_ch hv hd hvc hdr
  simp only [meshDist]
  rcases hh with h1 | h1 | h1 | h1 <;> omega

/-- **Every packet of a mesh family takes a shortest path**: a packet injected at node `s` for
node `d` is delivered after exactly as many hops as the distance from `s` to `d`. -/
theorem family_hops (hF : MeshFamily Mk) {k s d : ℕ} (hs : s < k * k) (hd : d < k * k)
    {q : ℕ × ℕ} {ls : List Unit} (h : (Mk k).packetLTS.Path (ch s 4 0, d) ls q)
    (harr : (Mk k).arrived q.1 q.2 = true) :
    ls.length = (s % k - d % k) + (d % k - s % k) + (s / k - d / k) + (d / k - s / k) := by
  have hl : tdLegal k (ch s 4 0) d := ⟨hd, s, 4, 0, rfl, hs, by omega, Or.inl ⟨rfl, rfl⟩⟩
  have := (Mk k).packet_hops_eq (td_closed hF k) (meshDist k)
    (fun _ _ _ hl ha hq => td_dist hF hl ha hq) hl h
  have h0 : meshDist k q.1 q.2 = 0 := by
    have : head k q.1 = q.2 := by rw [hF.arrived] at harr; simpa using harr
    simp [meshDist, this]
  rw [h0] at this
  simp only [meshDist, head_inj] at this
  omega

/-! ### Legal pairs and the escape order -/

/-- The pairs a packet of the north-last mesh can occupy: an injection channel, or a channel
leaving node `u` in a direction that is productive from `u`; on virtual channel 0, a packet
going north has no eastward or westward hop left. -/
def nlLegal (k c d : ℕ) : Prop :=
  d < k * k ∧ ∃ u dr vc, c = ch u dr vc ∧ u < k * k ∧ vc < 2 ∧
    (dr = 4 ∧ vc = 0 ∨ dr ∈ productive k u d ∧ (vc = 0 → dr = 2 → u % k = d % k))

theorem nlLegal_td {k c d : ℕ} (h : nlLegal k c d) : tdLegal k c d := by
  obtain ⟨hd, u, dr, vc, rfl, hu, hvc, h | ⟨h, -⟩⟩ := h
  · exact ⟨hd, u, dr, vc, rfl, hu, hvc, Or.inl h⟩
  · exact ⟨hd, u, dr, vc, rfl, hu, hvc, Or.inr h⟩

theorem nl_closed (k : ℕ) : (northLastMesh k).Closed (nlLegal k) := by
  constructor
  · intro q hq
    obtain ⟨s', hs', hd', -, he'⟩ := mem_allPairs.1 (show (q.1, q.2) ∈ allPairs (k * k) _ from hq)
    exact ⟨hd', s', 4, 0, he', hs', by omega, Or.inl ⟨rfl, rfl⟩⟩
  · intro c d q hl ha hq
    have hv := tdLegal_head (nlLegal_td hl)
    have hd := hl.1
    have hne : head k c ≠ d := by simpa [turnDuatoMesh] using ha
    rw [td_route_eq] at hq
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_filter] at hq
    rcases hq with rfl | ⟨dr, ⟨hdr, -⟩, rfl⟩ | ⟨dr, hdr, rfl⟩
    · dsimp only
      refine ⟨hd, _, _, 0, rfl, hv, by omega, Or.inr ⟨xy_mem_productive hne, fun _ h => ?_⟩⟩
      rcases xy_cases (k := k) hne with h' | h' | h' | h' <;> omega
    · dsimp only
      refine ⟨hd, _, dr, 0, rfl, hv, by omega, Or.inr ⟨northLast_sub hdr, fun _ h => ?_⟩⟩
      subst h
      unfold northLast at hdr
      split_ifs at hdr with hn
      · have h1 : ¬ head k c % k < d % k := fun h1 => by
          have : 0 ∈ productive k (head k c) d := mem_productive.2 (Or.inl ⟨rfl, h1⟩)
          rw [hn] at this; simp at this
        have h2 : ¬ d % k < head k c % k := fun h2 => by
          have : 1 ∈ productive k (head k c) d := mem_productive.2 (Or.inr (Or.inl ⟨rfl, h2⟩))
          rw [hn] at this; simp at this
        omega
      · simp at hdr
    · exact ⟨hd, _, dr, 1, rfl, hv, by omega, Or.inr ⟨hdr, by omega⟩⟩

/-- A position of every channel in the dependency order of the escape hops: virtual channel 1
and injection channels first; then the channels of virtual channel 0 that are not northward,
row by row from north to south (in each row, the southward channels arriving there, then the
eastward channels from west to east and the westward channels from east to west); then the
northward channels of virtual channel 0, from south to north. -/
def nlRank (k c : ℕ) : ℕ × ℕ :=
  if c % 2 = 1 ∨ dir c = 4 then (2 * k + 1, 0)
  else if dir c = 2 then (0, k - head k c / k)
  else if dir c = 3 then (2 * (head k c / k) + 2, 0)
  else if dir c = 0 then (2 * (head k c / k) + 1, k - head k c % k)
  else (2 * (head k c / k) + 1, head k c % k)

theorem nlRank_vc1 {k v e : ℕ} : nlRank k (ch v e 1) = (2 * k + 1, 0) := by
  unfold nlRank; rw [vc_ch (by omega), ite_eq_left_iff.2 fun h => absurd (Or.inl rfl) h]

theorem nlRank_inj {k v : ℕ} : nlRank k (ch v 4 0) = (2 * k + 1, 0) := by
  unfold nlRank
  rw [dir_ch (by omega) (by omega), ite_eq_left_iff.2 fun h => absurd (Or.inr rfl) h]

theorem nlRank_N {k v : ℕ} : nlRank k (ch v 2 0) = (0, k - head k (ch v 2 0) / k) := by
  unfold nlRank; rw [vc_ch (by omega), dir_ch (by omega) (by omega)]; rfl

theorem nlRank_S {k v : ℕ} : nlRank k (ch v 3 0) = (2 * (head k (ch v 3 0) / k) + 2, 0) := by
  unfold nlRank; rw [vc_ch (by omega), dir_ch (by omega) (by omega)]; rfl

theorem nlRank_E {k v : ℕ} :
    nlRank k (ch v 0 0) = (2 * (head k (ch v 0 0) / k) + 1, k - head k (ch v 0 0) % k) := by
  unfold nlRank; rw [vc_ch (by omega), dir_ch (by omega) (by omega)]; rfl

theorem nlRank_W {k v : ℕ} :
    nlRank k (ch v 1 0) = (2 * (head k (ch v 1 0) / k) + 1, head k (ch v 1 0) % k) := by
  unfold nlRank; rw [vc_ch (by omega), dir_ch (by omega) (by omega)]; rfl

theorem nl_dep {k c c' : ℕ} (h : (northLastMesh k).Dep (nlLegal k) (xyEscape k) c c') :
    Prod.Lex (· < ·) (· < ·) (nlRank k c') (nlRank k c) := by
  obtain ⟨d, d', hl, ha, hq⟩ := h
  have hv := tdLegal_head (nlLegal_td hl)
  have hd := hl.1
  have hne : head k c ≠ d := by simpa [turnDuatoMesh] using ha
  simp only [xyEscape, List.mem_singleton, Prod.mk.injEq] at hq
  obtain ⟨rfl, -⟩ := hq
  have he := xy_mem_productive (k := k) hne
  obtain ⟨-, hh'⟩ := head_ch (vc := 0) hv hd (by omega) he
  have hxy := xy_cases (k := k) hne
  obtain ⟨hvx, hvy⟩ := coord_lt hv
  obtain ⟨hdx, hdy⟩ := coord_lt hd
  generalize xy k (head k c) d = e at hh' hxy ⊢
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
          lt_self_iff_false, false_or, true_implies, Nat.reduceEqDiff] at hnl ⊢ <;> omega
    · rw [nlRank_vc1]
      rcases hh' with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
        simp only [nlRank_W, nlRank_E, nlRank_N, nlRank_S, Prod.lex_def] <;> omega

theorem nl_wf (k : ℕ) : WellFounded (flip ((northLastMesh k).Dep (nlLegal k) (xyEscape k))) :=
  Network.wf_of_lexRank (nlRank k) fun _ _ h => nl_dep h

theorem nl_pairs_finite (k : ℕ) : {q : ℕ × ℕ | nlLegal k q.1 q.2}.Finite :=
  (tdLegal_finite k).subset fun _ h => nlLegal_td h

theorem nl_chans_finite (k : ℕ) : {c | ∃ d, nlLegal k c d}.Finite :=
  ((nl_pairs_finite k).image Prod.fst).subset fun c ⟨d, hl⟩ => ⟨(c, d), hl, rfl⟩

theorem nl_esc_sub {k : ℕ} : ∀ c d q, nlLegal k c d → (northLastMesh k).arrived c d = false →
    q ∈ xyEscape k c d → q ∈ (northLastMesh k).route c d := by
  intro c d q _ _ hq
  simp only [xyEscape, List.mem_singleton] at hq
  subst hq
  simp [turnDuatoMesh]

theorem nl_esc_conn {k : ℕ} : ∀ c d, nlLegal k c d → (northLastMesh k).arrived c d = false →
    xyEscape k c d ≠ [] := by
  intro c d _ _; simp [xyEscape]

theorem nl_dist {k c d : ℕ} {q : ℕ × ℕ} (hl : nlLegal k c d)
    (ha : (northLastMesh k).arrived c d = false) (hq : q ∈ (northLastMesh k).route c d) :
    meshDist k q.1 q.2 < meshDist k c d := by
  have := td_dist (turnDuato_family northLast_local) (nlLegal_td hl) ha hq; omega

end Mesh

/-! ### Correct for every size -/

/-- **The north-last mesh of every size is deadlock and livelock free**, under every dynamic
routing policy. -/
theorem northLastMesh_correct_all (k : ℕ) : (northLastMesh k).Correct :=
  ⟨(northLastMesh k).deadlockFree_of_escape (nl_closed k) (xyEscape k) nl_esc_sub nl_esc_conn
      (nl_wf k),
    (northLastMesh k).livelockFree_of_ranking (nl_closed k) (nl_chans_finite k) (meshDist k)
      fun _ _ _ hl ha hq => nl_dist hl ha hq⟩

/-- **No packet of the north-last mesh of any size starves** along a strongly fair run. -/
theorem northLastMesh_starvationFree_all (k : ℕ) : (northLastMesh k).StarvationFree :=
  (northLastMesh k).starvationFree_of_escape_ranking (nl_closed k) (nl_pairs_finite k)
    (xyEscape k) nl_esc_sub nl_esc_conn (nl_wf k) (meshDist k) fun _ _ _ hl ha hq => nl_dist hl ha hq

/-- **Any selection that never refuses a free XY escape hop** keeps the north-last mesh of every
size deadlock and livelock free. -/
theorem northLastMesh_correctWith (k : ℕ) {sel : Selection ℕ ℕ}
    (hsel : (northLastMesh k).EscapeSel (xyEscape k) sel) :
    (northLastMesh k).DeadlockFreeWith sel ∧ (northLastMesh k).LivelockFreeWith sel :=
  ⟨(northLastMesh k).deadlockFreeWith_of_escape (nl_closed k) (xyEscape k) nl_esc_conn (nl_wf k)
      hsel,
    (northLastMesh k).livelockFreeWith_of_ranking (nl_closed k) (nl_chans_finite k) (meshDist k)
      (fun _ _ _ hl ha hq => nl_dist hl ha hq) hsel.sub⟩

/-- **Every packet of the north-last mesh takes a shortest path.** -/
theorem northLastMesh_hops {k s d : ℕ} (hs : s < k * k) (hd : d < k * k) {q : ℕ × ℕ}
    {ls : List Unit} (h : (northLastMesh k).packetLTS.Path (ch s 4 0, d) ls q)
    (harr : (northLastMesh k).arrived q.1 q.2 = true) :
    ls.length = (s % k - d % k) + (d % k - s % k) + (s / k - d / k) + (d / k - s / k) :=
  family_hops (turnDuato_family northLast_local) hs hd h harr

#assert_standard_axioms northLastMesh_correct_all northLastMesh_starvationFree_all
  northLastMesh_correctWith northLastMesh_hops family_hops

end AsyncLean.Examples
