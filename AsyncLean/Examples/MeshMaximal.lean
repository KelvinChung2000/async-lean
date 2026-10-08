/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.OptimalRouting
import AsyncLean.Routing.Embed

/-!
# Maximally adaptive routing on meshes of every size

`AsyncLean.Examples.OptimalRouting` checks, mesh by mesh, that the west-first and north-last
meshes are maximally adaptive.  Here the same is proved **for every size `k`**.

## The argument

A hop the west-first mesh does not permit, but a minimal routing function `N` permits, is a
northward or southward hop on virtual channel 0 of a packet `P` that still has to go west
(`wf_extra`).  For the north-last mesh it is a northward hop on virtual channel 0 of a packet
that still has to go east or west (`nl_extra`).  Follow `P` after the hop:

* while `N` lets it go on north (or south) on virtual channel 0, let it;
* it stops on virtual channel 0 in a column next to its destination's side, either in its
  destination's row (`top`) or with one more vertical hop left that `N` does not permit on
  virtual channel 0 (`caseB`).

Either way, a small group of packets around `P` (8 or 13 of them, in a 2 × 2 or 2 × 3 window)
blocks it and blocks itself: `P` closes a cycle of turns that the turn model alone forbids.
This group is found and checked by the kernel once, in a 3 × 3 mesh (`winCertB`), with `P`
frozen in its channel standing for a packet whose destination may lie far outside the window.
`Network.not_deadlockFree_of_runGoodB` carries the deadlock into the `k × k` mesh, at the
position of `P` (`emb`, `not_deadlockFree_of_winCertB`).  The induction on the vertical distance
left (`climbNW`, `climbSW`, `climbNE`) and the single-packet run to the extra hop
(`reachable_single`) complete the proof.

## Results

* `westFirstMesh_maximal_all k`, `northLastMesh_maximal_all k` : the west-first and the
  north-last meshes are maximally adaptive among the minimal routing functions on two virtual
  channels, for every size (under wormhole switching too, `MaximallyAdaptive.wormhole`).
* `no_common_improvement_all k` : no deadlock-free minimal routing function of any mesh of size
  at least 2 is at least as adaptive as both.
-/

namespace AsyncLean.Examples

open Network Mesh

namespace Mesh

/-! ### Windows

The 3 × 3 mesh placed into the `k × k` mesh, at column offset `ox` and row offset `oy`. -/

/-- Node `u` of the 3 × 3 mesh, placed in the `k × k` mesh. -/
def emb (k ox oy u : ℕ) : ℕ := k * (oy + u / 3) + (ox + u % 3)

/-- Channel `c` of the 3 × 3 mesh, placed in the `k × k` mesh. -/
def embCh (k ox oy c : ℕ) : ℕ := ch (emb k ox oy (node c)) (dir c) (c % 2)

/-- Node `u` of the window lands on a node of the `k × k` mesh. -/
def Fits (k ox oy u : ℕ) : Prop := ox + u % 3 < k ∧ oy + u / 3 < k

theorem emb_coord {k ox oy u : ℕ} (h : Fits k ox oy u) :
    emb k ox oy u % k = ox + u % 3 ∧ emb k ox oy u / k = oy + u / 3 :=
  coord h.1 rfl

theorem emb_lt {k ox oy u : ℕ} (h : Fits k ox oy u) : emb k ox oy u < k * k := by
  obtain ⟨h1, h2⟩ := emb_coord h
  exact lt_sq_of_coord (by rw [h1]; exact h.1) (by rw [h2]; exact h.2)

theorem emb_inj {k ox oy u v : ℕ} (hu : Fits k ox oy u) (hv : Fits k ox oy v)
    (h : emb k ox oy u = emb k ox oy v) : u = v := by
  obtain ⟨h1, h2⟩ := emb_coord hu
  obtain ⟨h3, h4⟩ := emb_coord hv
  rw [h] at h1 h2
  omega

theorem ch_inj {u dr vc u' dr' vc' : ℕ} (hdr : dr < 5) (hvc : vc < 2) (hdr' : dr' < 5)
    (hvc' : vc' < 2) (h : ch u dr vc = ch u' dr' vc') : u = u' ∧ dr = dr' ∧ vc = vc' := by
  simp only [ch] at h; omega

theorem ch_node_dir (c : ℕ) : ch (node c) (dir c) (c % 2) = c := by
  simp only [ch, node, dir]; omega

theorem embCh_ch {k ox oy u dr vc : ℕ} (hdr : dr < 5) (hvc : vc < 2) :
    embCh k ox oy (ch u dr vc) = ch (emb k ox oy u) dr vc := by
  simp only [embCh, node_ch hdr hvc, dir_ch hdr hvc, vc_ch hvc]

theorem xy_lt (k u d : ℕ) : xy k u d < 4 := by
  unfold xy; split_ifs <;> omega

/-- A channel of the 3 × 3 mesh that does not wrap around its border: an injection channel, or a
channel to a neighbour. -/
def proper (c : ℕ) : Bool :=
  decide (c < 90) && (dir c == 4 && c % 2 == 0 || dir c == 0 && decide (node c % 3 < 2) ||
    dir c == 1 && decide (0 < node c % 3) || dir c == 2 && decide (node c / 3 < 2) ||
    dir c == 3 && decide (0 < node c / 3))

/-- A proper channel between nodes of the window `L`. -/
def winOK (L : List ℕ) (c : ℕ) : Bool := proper c && L.contains (node c) && L.contains (head 3 c)

/-- A packet in a channel of the window `L`, for a node of `L`. -/
def winGood (L : List ℕ) (c d : ℕ) : Bool := winOK L c && L.contains d

theorem winOK_iff {L : List ℕ} {c : ℕ} :
    winOK L c = true ↔ proper c = true ∧ node c ∈ L ∧ head 3 c ∈ L := by
  simp [winOK, and_assoc]

section Window

variable {k ox oy : ℕ} {L : List ℕ}

theorem head_E {k u vc : ℕ} (hvc : vc < 2) : head k (ch u 0 vc) = u + 1 := by
  simp only [head, dir_ch (by omega : 0 < 5) hvc, node_ch (by omega : 0 < 5) hvc]

theorem head_W {k u vc : ℕ} (hvc : vc < 2) : head k (ch u 1 vc) = u - 1 := by
  simp only [head, dir_ch (by omega : 1 < 5) hvc, node_ch (by omega : 1 < 5) hvc]

theorem head_N {k u vc : ℕ} (hvc : vc < 2) : head k (ch u 2 vc) = u + k := by
  simp only [head, dir_ch (by omega : 2 < 5) hvc, node_ch (by omega : 2 < 5) hvc]

theorem head_S {k u vc : ℕ} (hvc : vc < 2) : head k (ch u 3 vc) = u - k := by
  simp only [head, dir_ch (by omega : 3 < 5) hvc, node_ch (by omega : 3 < 5) hvc]

theorem head_I {k u vc : ℕ} (hvc : vc < 2) : head k (ch u 4 vc) = u := by
  simp only [head, dir_ch (by omega : 4 < 5) hvc, node_ch (by omega : 4 < 5) hvc]

theorem head_embCh (hL : ∀ u ∈ L, Fits k ox oy u) {c : ℕ} (hc : winOK L c = true) :
    head k (embCh k ox oy c) = emb k ox oy (head 3 c) := by
  obtain ⟨hp, hn, -⟩ := winOK_iff.1 hc
  have fn := hL _ hn
  have hvc : c % 2 < 2 := Nat.mod_lt _ (by omega)
  simp only [proper, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  obtain ⟨-, hp⟩ := hp
  have e1 : head k (embCh k ox oy c) = head k (ch (emb k ox oy (node c)) (dir c) (c % 2)) := rfl
  have e2 : head 3 c = head 3 (ch (node c) (dir c) (c % 2)) := by rw [ch_node_dir]
  rw [e1, e2]
  generalize node c = n at fn hp ⊢
  unfold emb
  rcases hp with ((((⟨h0, -⟩ | ⟨h0, h⟩) | ⟨h0, h⟩) | ⟨h0, h⟩) | ⟨h0, h⟩) <;> rw [h0]
  · rw [head_I hvc, head_I hvc]
  · rw [head_E hvc, head_E hvc, show (n + 1) / 3 = n / 3 by omega,
      show (n + 1) % 3 = n % 3 + 1 by omega]; omega
  · rw [head_W hvc, head_W hvc, show (n - 1) / 3 = n / 3 by omega,
      show (n - 1) % 3 = n % 3 - 1 by omega]; omega
  · rw [head_N hvc, head_N hvc, show (n + 3) / 3 = n / 3 + 1 by omega,
      show (n + 3) % 3 = n % 3 by omega, show oy + (n / 3 + 1) = (oy + n / 3) + 1 by omega,
      Nat.mul_add_one]; omega
  · rw [head_S hvc, head_S hvc]
    have h3 : (n - 3) / 3 + 1 = n / 3 := by omega
    have h4 : (n - 3) % 3 = n % 3 := by omega
    have : k * (oy + (n - 3) / 3) + k = k * (oy + n / 3) := by
      rw [← Nat.mul_add_one, Nat.add_assoc, h3]
    rw [h4]; omega

theorem productive_emb {u v : ℕ} (hu : Fits k ox oy u) (hv : Fits k ox oy v) :
    productive k (emb k ox oy u) (emb k ox oy v) = productive 3 u v := by
  obtain ⟨h1, h2⟩ := emb_coord hu
  obtain ⟨h3, h4⟩ := emb_coord hv
  simp only [productive, h1, h2, h3, h4, Nat.add_lt_add_iff_left]

theorem xy_emb {u v : ℕ} (hu : Fits k ox oy u) (hv : Fits k ox oy v) :
    xy k (emb k ox oy u) (emb k ox oy v) = xy 3 u v := by
  obtain ⟨h1, h2⟩ := emb_coord hu
  obtain ⟨h3, h4⟩ := emb_coord hv
  simp only [xy, h1, h2, h3, h4, Nat.add_lt_add_iff_left]

theorem westFirst_emb {u v : ℕ} (hu : Fits k ox oy u) (hv : Fits k ox oy v) :
    westFirst k (emb k ox oy u) (emb k ox oy v) = westFirst 3 u v := by
  obtain ⟨h1, -⟩ := emb_coord hu
  obtain ⟨h3, -⟩ := emb_coord hv
  simp only [westFirst, h1, h3, Nat.add_lt_add_iff_left, productive_emb hu hv]

theorem northLast_emb {u v : ℕ} (hu : Fits k ox oy u) (hv : Fits k ox oy v) :
    northLast k (emb k ox oy u) (emb k ox oy v) = northLast 3 u v := by
  simp only [northLast, productive_emb hu hv]

theorem minimalHops_emb (hL : ∀ u ∈ L, Fits k ox oy u) {c d : ℕ} (hc : winOK L c = true)
    (hd : d ∈ L) :
    minimalHops k (embCh k ox oy c) (emb k ox oy d) =
      (minimalHops 3 c d).map fun q => (embCh k ox oy q.1, emb k ox oy q.2) := by
  have fh := hL _ (winOK_iff.1 hc).2.2
  have fd := hL _ hd
  simp only [minimalHops, head_embCh hL hc, productive_emb fh fd, List.map_append, List.map_map]
  congr 1 <;> refine List.map_congr_left fun dr hdr => ?_ <;> have := productive_lt hdr
  · simp only [Function.comp_apply, embCh_ch (u := head 3 c) (dr := dr) (vc := 0) (by omega)
      (by omega)]
  · simp only [Function.comp_apply, embCh_ch (u := head 3 c) (dr := dr) (vc := 1) (by omega)
      (by omega)]

/-- A turn model that only looks at the relative position of the destination. -/
def TurnLocal (turn : ℕ → ℕ → ℕ → List ℕ) : Prop :=
  (∀ k u d dr, dr ∈ turn k u d → dr ∈ productive k u d) ∧
  ∀ k ox oy u v, Fits k ox oy u → Fits k ox oy v →
    turn k (emb k ox oy u) (emb k ox oy v) = turn 3 u v

theorem westFirst_local : TurnLocal westFirst :=
  ⟨fun _ _ _ _ h => westFirst_sub h, fun _ _ _ _ _ hu hv => westFirst_emb hu hv⟩

theorem northLast_local : TurnLocal northLast :=
  ⟨fun _ _ _ _ h => northLast_sub h, fun _ _ _ _ _ hu hv => northLast_emb hu hv⟩

variable {turn : ℕ → ℕ → ℕ → List ℕ}

theorem route_emb (ht : TurnLocal turn) (hL : ∀ u ∈ L, Fits k ox oy u) {c d : ℕ}
    (hc : winOK L c = true) (hd : d ∈ L) :
    (turnDuatoMesh turn k).route (embCh k ox oy c) (emb k ox oy d) =
      ((turnDuatoMesh turn 3).route c d).map fun q => (embCh k ox oy q.1, emb k ox oy q.2) := by
  have fh := hL _ (winOK_iff.1 hc).2.2
  have fd := hL _ hd
  have hxy := xy_lt 3 (head 3 c) d
  simp only [turnDuatoMesh, head_embCh hL hc, productive_emb fh fd, xy_emb fh fd,
    ht.2 k ox oy _ _ fh fd, List.map_cons, List.map_append, List.map_map,
    embCh_ch (u := head 3 c) (dr := xy 3 (head 3 c) d) (vc := 0) (by omega) (by omega)]
  refine congrArg (List.cons _) (congrArg₂ List.append ?_ ?_)
  · refine List.map_congr_left fun dr hdr => ?_
    have := productive_lt (ht.1 _ _ _ _ (List.mem_filter.1 hdr).1)
    simp only [Function.comp_apply, embCh_ch (u := head 3 c) (dr := dr) (vc := 0) (by omega)
      (by omega)]
  · refine List.map_congr_left fun dr hdr => ?_
    have := productive_lt hdr
    simp only [Function.comp_apply, embCh_ch (u := head 3 c) (dr := dr) (vc := 1) (by omega)
      (by omega)]

theorem td_route_mem (ht : TurnLocal turn) {k c d : ℕ} {q : ℕ × ℕ} (hne : head k c ≠ d)
    (hq : q ∈ (turnDuatoMesh turn k).route c d) :
    ∃ dr vc, dr ∈ productive k (head k c) d ∧ vc < 2 ∧ q = (ch (head k c) dr vc, d) := by
  simp only [turnDuatoMesh, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter] at hq
  rcases hq with (rfl | ⟨dr, ⟨hdr, -⟩, rfl⟩) | ⟨dr, hdr, rfl⟩
  · exact ⟨_, 0, xy_mem_productive hne, by omega, rfl⟩
  · exact ⟨dr, 0, ht.1 _ _ _ _ hdr, by omega, rfl⟩
  · exact ⟨dr, 1, hdr, by omega, rfl⟩

/-- **A family of mesh routing functions**, one per size, that the window argument applies to:
packets are injected at every node for every other node and arrive at their destination, every
hop is productive, and the hops only depend on the position of the destination relative to the
packet (so a window of a large mesh routes like the 3 × 3 mesh). -/
structure MeshFamily (Mk : ℕ → Network ℕ ℕ) : Prop where
  arrived : ∀ k c d, (Mk k).arrived c d = (head k c == d)
  inject : ∀ k, (Mk k).inject = allPairs (k * k) fun s => ch s 4 0
  route : ∀ k c d q, head k c ≠ d → q ∈ (Mk k).route c d →
    ∃ dr vc, dr ∈ productive k (head k c) d ∧ vc < 2 ∧ q = (ch (head k c) dr vc, d)
  emb : ∀ k ox oy (L : List ℕ), (∀ u ∈ L, Fits k ox oy u) → ∀ c d, winOK L c = true → d ∈ L →
    (Mk k).route (embCh k ox oy c) (emb k ox oy d) =
      ((Mk 3).route c d).map fun q => (embCh k ox oy q.1, emb k ox oy q.2)

/-- A yardstick that only depends on the position of the destination relative to the packet. -/
def HopsLocal (Uk : ℕ → ℕ → ℕ → List (ℕ × ℕ)) : Prop :=
  ∀ k ox oy (L : List ℕ), (∀ u ∈ L, Fits k ox oy u) → ∀ c d, winOK L c = true → d ∈ L →
    Uk k (embCh k ox oy c) (emb k ox oy d) =
      (Uk 3 c d).map fun q => (embCh k ox oy q.1, emb k ox oy q.2)

theorem minimalHops_local : HopsLocal minimalHops := fun _ _ _ _ hL _ _ hc hd =>
  minimalHops_emb hL hc hd

theorem turnDuato_family (ht : TurnLocal turn) : MeshFamily (turnDuatoMesh turn) where
  arrived _ _ _ := rfl
  inject _ := rfl
  route _ _ _ _ hne hq := td_route_mem ht hne hq
  emb _ _ _ _ hL _ _ hc hd := route_emb ht hL hc hd

variable {Mk : ℕ → Network ℕ ℕ}

theorem arrived_emb (hF : MeshFamily Mk) (hL : ∀ u ∈ L, Fits k ox oy u) {c d : ℕ}
    (hc : winOK L c = true) (hd : d ∈ L) :
    (Mk k).arrived (embCh k ox oy c) (emb k ox oy d) = (Mk 3).arrived c d := by
  have fh := hL _ (winOK_iff.1 hc).2.2
  have fd := hL _ hd
  rw [hF.arrived, hF.arrived, head_embCh hL hc, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨emb_inj fh fd, congrArg _⟩

theorem mem_allPairs {n : ℕ} {f : ℕ → ℕ} {c d : ℕ} :
    (c, d) ∈ allPairs n f ↔ ∃ s < n, d < n ∧ d ≠ s ∧ c = f s := by
  simp only [allPairs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨s, hs, d', ⟨hd', hne⟩, rfl, rfl⟩; exact ⟨s, hs, hd', hne, rfl⟩
  · rintro ⟨s, hs, hd, hne, rfl⟩; exact ⟨s, hs, d, ⟨hd, hne⟩, rfl, rfl⟩

theorem inject_emb (hF : MeshFamily Mk) (hL : ∀ u ∈ L, Fits k ox oy u) {c d : ℕ}
    (hc : winOK L c = true) (hd : d ∈ L) (h : (c, d) ∈ (Mk 3).inject) :
    (embCh k ox oy c, emb k ox oy d) ∈ (Mk k).inject := by
  rw [hF.inject] at h ⊢
  obtain ⟨s, -, -, hne, rfl⟩ := mem_allPairs.1 h
  have hn : node (ch s 4 0) = s := node_ch (by omega) (by omega)
  have fs := hL _ (hn ▸ (winOK_iff.1 hc).2.1)
  have fd := hL _ hd
  exact mem_allPairs.2 ⟨emb k ox oy s, emb_lt fs, emb_lt fd, fun he => hne (emb_inj fd fs he),
    embCh_ch (u := s) (dr := 4) (vc := 0) (by omega) (by omega)⟩

theorem not_arrived (hF : MeshFamily Mk) {k c d : ℕ} : (Mk k).arrived c d = false ↔ head k c ≠ d := by
  rw [hF.arrived]; simp

theorem route_snd (hF : MeshFamily Mk) {k c d : ℕ} {q : ℕ × ℕ}
    (ha : (Mk k).arrived c d = false) (hq : q ∈ (Mk k).route c d) : q.2 = d := by
  obtain ⟨_, _, _, _, rfl⟩ := hF.route k c d q ((not_arrived hF).1 ha) hq
  rfl

end Window

/-! ### Window certificates -/

/-- The routing function blocking the packets of a window certificate: the frozen packet
(header `9`) is blocked when the hops `spec` are; every other packet when all its productive
hops are. -/
def winHi (U : ℕ → ℕ → List (ℕ × ℕ)) (spec : List (ℕ × ℕ)) (c d : ℕ) : List (ℕ × ℕ) :=
  if d = 9 then spec else U c d

/-- **A window certificate.**  From the configuration with only the frozen packet (header `9`,
standing for a packet whose destination may lie outside the window) in channel `n`, the run
`as` of `M` stays in the window `L` and ends in a configuration where every packet is blocked:
the frozen packet when the hops `spec` are, every other one when all its hops in the yardstick
`U` are. -/
def winCertB (M : Network ℕ ℕ) (U : ℕ → ℕ → List (ℕ × ℕ)) (L : List ℕ) (n : ℕ)
    (spec : List (ℕ × ℕ)) (as : List (Act ℕ ℕ)) : Bool :=
  !L.contains 9 && winOK L n &&
  match M.runGoodB (winOK L) (winGood L) [(n, 9)] as with
  | some qs => !qs.isEmpty && (M.withRoute (winHi U spec)).stuckB qs &&
      qs.all fun q => q.1 == n && q.2 == 9 || winGood L q.1 q.2
  | none => false

/-- **A window certificate refutes deadlock freedom at any position of any mesh.**  If the
frozen packet's channel, placed in the `k × k` mesh, can hold a packet for `d` alone, and the
hops `N` permits it there are among the hops `spec` (placed in the mesh), then every network
`N` permitting the hops of the family and only hops of the yardstick deadlocks. -/
theorem not_deadlockFree_of_winCertB {Mk : ℕ → Network ℕ ℕ} (hF : MeshFamily Mk)
    {Uk : ℕ → ℕ → ℕ → List (ℕ × ℕ)} (hUk : HopsLocal Uk)
    {k ox oy : ℕ} {N : Network ℕ ℕ} (hext : (Mk k).Extends N)
    (hU : N.Within (Uk k)) {L : List ℕ} {n : ℕ} {spec : List (ℕ × ℕ)}
    {as : List (Act ℕ ℕ)} (hcert : winCertB (Mk 3) (Uk 3) L n spec as = true)
    (hL : ∀ u ∈ L, Fits k ox oy u) {d : ℕ}
    (hreach : N.lts.Reachable empty (fill [(embCh k ox oy n, d)]))
    (harr : N.arrived (embCh k ox oy n) d = false)
    (hP : ∀ q ∈ N.route (embCh k ox oy n) d, ∃ q' ∈ spec, embCh k ox oy q'.1 = q.1) :
    ¬ N.DeadlockFree := by
  unfold winCertB at hcert
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcert
  obtain ⟨⟨h9, hn⟩, hcert⟩ := hcert
  split at hcert
  · rename_i qs hrun
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true] at hcert
    obtain ⟨⟨hne, hstuck⟩, hfin⟩ := hcert
    have h9L : 9 ∉ L := fun h => by simp [h] at h9
    let ψ : ℕ → ℕ := fun p => if p = 9 then d else emb k ox oy p
    have hψ : ∀ p ∈ L, ψ p = emb k ox oy p := fun p hp => by
      simp only [ψ]
      split_ifs with h
      · subst h; exact absurd hp h9L
      · rfl
    have hgood : ∀ c p, winGood L c p = true → winOK L c = true ∧ p ∈ L := fun c p h => by
      simpa [winGood, List.contains_iff_mem] using h
    refine not_deadlockFree_of_runGoodB (M := Mk 3) (N := N) (φ := embCh k ox oy)
      (ψ := ψ) (winHi (Uk 3) spec) ?_ ?_ ?_ ?_ ?_ hrun hne hstuck ?_
    · intro c₁ c₂ h₁ h₂ he
      have hc₁ := winOK_iff.1 h₁
      have hc₂ := winOK_iff.1 h₂
      obtain ⟨hn', hd', hv'⟩ := ch_inj (dir_lt _) (Nat.mod_lt _ (by omega)) (dir_lt _)
        (Nat.mod_lt _ (by omega)) he
      rw [← ch_node_dir c₁, ← ch_node_dir c₂, emb_inj (hL _ hc₁.2.1) (hL _ hc₂.2.1) hn', hd', hv']
    · intro c p hg hcp
      obtain ⟨hc, hp⟩ := hgood c p hg
      rw [hψ p hp, hext.inject]
      exact inject_emb hF hL hc hp hcp
    · intro c p c' p' hg hg' harr' hq
      obtain ⟨hc, hp⟩ := hgood c p hg
      obtain ⟨-, hp'⟩ := hgood c' p' hg'
      rw [hψ p hp, hψ p' hp']
      have ha : (Mk k).arrived (embCh k ox oy c) (emb k ox oy p) = false := by
        rw [arrived_emb hF hL hc hp]; exact harr'
      refine ⟨by rw [hext.arrived]; exact ha, hext.route _ _ _ ha ?_⟩
      obtain rfl : p' = p := route_snd hF harr' hq
      have h2 := hF.emb k ox oy L hL c _ hc hp
      have h3 := List.mem_map_of_mem (f := fun q : ℕ × ℕ => (embCh k ox oy q.1, emb k ox oy q.2)) hq
      rw [h2]; exact h3
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact hn
    · have : ψ 9 = d := by simp [ψ]
      simpa only [List.map_cons, List.map_nil, this] using hreach
    · intro c p hcp harr'
      rcases Bool.or_eq_true_iff.1 (hfin (c, p) hcp) with h | h
      · simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [ψ, ite_true, winHi]
        exact ⟨harr, hP⟩
      · obtain ⟨hc, hp⟩ := hgood c p h
        have ha : (Mk k).arrived (embCh k ox oy c) (emb k ox oy p) = false := by
          rw [arrived_emb hF hL hc hp]; exact harr'
        have hp9 : p ≠ 9 := fun h => h9L (h ▸ hp)
        simp only [hψ p hp, winHi, hp9, ite_false]
        refine ⟨by rw [hext.arrived]; exact ha, fun q hq => ?_⟩
        have hq' := hU _ _ _ (by rw [hext.arrived]; exact ha) hq
        rw [hUk k ox oy L hL c p hc hp] at hq'
        obtain ⟨q'', hq'', rfl⟩ := List.mem_map.1 hq'
        exact ⟨q'', hq'', rfl⟩
  · simp at hcert

/-! ### The certificates

Each certificate is a run in the 3 × 3 mesh around the frozen packet `P` (header `9`) in channel
`n`, which arrived at node `C` on virtual channel 0 and still has to go west (or east).

* `top` : `P` has only its horizontal hops left.  Eight packets, two per channel around the
  square of `C`, each turning towards the next corner, block each other and `P`.
* `caseB` : `P` may still go on vertically, but not on virtual channel 0.  Five more packets
  block that hop on virtual channel 1 and lean on the square. -/

/-- West of `C = 4`, north-bound `P` in channel `14` (node 1 to node 4). -/
def certNW : List (Act ℕ ℕ) :=
  [.inject 8 4, .hop 8 0 4, .inject 8 4, .hop 8 1 4, .inject 18 3, .hop 18 15 3,
    .inject 48 0, .hop 48 42 0, .inject 48 0, .hop 48 43 0, .inject 38 1, .hop 38 36 1,
    .inject 38 1, .hop 38 37 1]

/-- The same, with a northward hop on virtual channel 1 left to block. -/
def certNWB : List (Act ℕ ℕ) :=
  certNW ++ [.inject 48 6, .hop 48 45 6, .inject 78 3, .hop 78 72 3, .inject 78 3, .hop 78 73 3,
    .inject 68 0, .hop 68 66 0, .inject 68 0, .hop 68 67 0]

/-- West of `C = 1`, south-bound `P` in channel `46` (node 4 to node 1). -/
def certSW : List (Act ℕ ℕ) :=
  [.inject 18 3, .hop 18 12 3, .inject 18 3, .hop 18 13 3, .inject 8 4, .hop 8 4 4,
    .inject 8 4, .hop 8 5 4, .inject 38 1, .hop 38 30 1, .inject 38 1, .hop 38 31 1,
    .inject 48 0, .hop 48 47 0]

/-- West of `C = 4`, south-bound `P` in channel `76` (node 7 to node 4), with a southward hop on
virtual channel 1 left to block. -/
def certSWB : List (Act ℕ ℕ) :=
  [.inject 48 6, .hop 48 42 6, .inject 48 6, .hop 48 43 6, .inject 38 7, .hop 38 34 7,
    .inject 38 7, .hop 38 35 7, .inject 68 4, .hop 68 60 4, .inject 68 4, .hop 68 61 4,
    .inject 78 3, .hop 78 77 3, .inject 48 0, .hop 48 47 0, .inject 18 3, .hop 18 12 3,
    .inject 18 3, .hop 18 13 3, .inject 8 6, .hop 8 4 6, .inject 8 6, .hop 8 5 6]

/-- East of `C = 3`, north-bound `P` in channel `4` (node 0 to node 3). -/
def certNE : List (Act ℕ ℕ) :=
  [.inject 38 1, .hop 38 30 1, .inject 38 1, .hop 38 31 1, .inject 48 0, .hop 48 46 0,
    .inject 48 0, .hop 48 47 0, .inject 18 3, .hop 18 12 3, .inject 18 3, .hop 18 13 3,
    .inject 8 4, .hop 8 5 4]

/-- The same, with a northward hop on virtual channel 1 left to block. -/
def certNEB : List (Act ℕ ℕ) :=
  certNE ++ [.inject 38 7, .hop 38 35 7, .inject 68 4, .hop 68 60 4, .inject 68 4, .hop 68 61 4,
    .inject 78 1, .hop 78 76 1, .inject 78 1, .hop 78 77 1]

theorem wf_certNW : winCertB (westFirstMesh 3) (minimalHops 3) [0, 1, 3, 4] 14 [(42, 9), (43, 9)] certNW = true := by
  decide +kernel

theorem wf_certNWB : winCertB (westFirstMesh 3) (minimalHops 3) [0, 1, 3, 4, 6, 7] 14 [(42, 9), (43, 9), (45, 9)]
    certNWB = true := by
  decide +kernel

theorem wf_certSW : winCertB (westFirstMesh 3) (minimalHops 3) [0, 1, 3, 4] 46 [(12, 9), (13, 9)] certSW = true := by
  decide +kernel

theorem wf_certSWB : winCertB (westFirstMesh 3) (minimalHops 3) [0, 1, 3, 4, 6, 7] 76 [(42, 9), (43, 9), (47, 9)]
    certSWB = true := by
  decide +kernel

theorem nl_certNW : winCertB (northLastMesh 3) (minimalHops 3) [0, 1, 3, 4] 14 [(42, 9), (43, 9)] certNW = true := by
  decide +kernel

theorem nl_certNWB : winCertB (northLastMesh 3) (minimalHops 3) [0, 1, 3, 4, 6, 7] 14 [(42, 9), (43, 9), (45, 9)]
    certNWB = true := by
  decide +kernel

theorem nl_certNE : winCertB (northLastMesh 3) (minimalHops 3) [0, 1, 3, 4] 4 [(30, 9), (31, 9)] certNE = true := by
  decide +kernel

theorem nl_certNEB : winCertB (northLastMesh 3) (minimalHops 3) [0, 1, 3, 4, 6, 7] 4 [(30, 9), (31, 9), (35, 9)]
    certNEB = true := by
  decide +kernel

/-! ### A single packet -/

/-- The pairs a packet of a turn-model mesh can occupy: an injection channel, or a channel
leaving a node in a direction that is productive from there. -/
def tdLegal (k c d : ℕ) : Prop :=
  d < k * k ∧ ∃ u dr vc, c = ch u dr vc ∧ u < k * k ∧ vc < 2 ∧
    (dr = 4 ∧ vc = 0 ∨ dr ∈ productive k u d)

theorem tdLegal_head {k c d : ℕ} (h : tdLegal k c d) : head k c < k * k := by
  obtain ⟨hd, u, dr, vc, rfl, hu, hvc, ⟨rfl, rfl⟩ | hp⟩ := h
  · rw [head_inj]; exact hu
  · exact (head_ch hu hd hvc hp).1

theorem mem_productive {k u d dr : ℕ} :
    dr ∈ productive k u d ↔ dr = 0 ∧ u % k < d % k ∨ dr = 1 ∧ d % k < u % k ∨
      dr = 2 ∧ u / k < d / k ∨ dr = 3 ∧ d / k < u / k := by
  simp only [productive, List.mem_append, List.mem_ite_nil_right, List.mem_singleton]
  tauto

theorem minimalHops_mem {k c d : ℕ} {q : ℕ × ℕ} (hq : q ∈ minimalHops k c d) :
    ∃ dr vc, dr ∈ productive k (head k c) d ∧ vc < 2 ∧ q = (ch (head k c) dr vc, d) := by
  simp only [minimalHops, List.mem_append, List.mem_map] at hq
  rcases hq with ⟨dr, hdr, rfl⟩ | ⟨dr, hdr, rfl⟩
  · exact ⟨dr, 0, hdr, by omega, rfl⟩
  · exact ⟨dr, 1, hdr, by omega, rfl⟩

variable {Mk : ℕ → Network ℕ ℕ}

theorem td_closed (hF : MeshFamily Mk) (k : ℕ) : (Mk k).Closed (tdLegal k) := by
  constructor
  · intro q hq
    rw [hF.inject] at hq
    obtain ⟨s, hs, hd, -, he⟩ := mem_allPairs.1 (show (q.1, q.2) ∈ allPairs (k * k) _ from hq)
    exact ⟨hd, s, 4, 0, he, hs, by omega, Or.inl ⟨rfl, rfl⟩⟩
  · intro c d q hl ha hq
    have hne : head k c ≠ d := (not_arrived hF).1 ha
    obtain ⟨dr, vc, hdr, hvc, rfl⟩ := hF.route k c d q hne hq
    exact ⟨hl.1, _, dr, vc, rfl, tdLegal_head hl, hvc, Or.inr hdr⟩

/-- A hop leaves the channel the packet is in. -/
theorem td_ne (hF : MeshFamily Mk) {k c d : ℕ} {q : ℕ × ℕ} (hl : tdLegal k c d)
    (ha : (Mk k).arrived c d = false) (hq : q ∈ (Mk k).route c d) : q.1 ≠ c := by
  have hne : head k c ≠ d := (not_arrived hF).1 ha
  obtain ⟨dr, vc, hdr, hvc, rfl⟩ := hF.route k c d q hne hq
  obtain ⟨hd, u, dr', vc', rfl, hu, hvc', hdr'⟩ := hl
  intro he
  have hdr4 := productive_lt hdr
  have hdr5 : dr' < 5 := by
    rcases hdr' with ⟨rfl, -⟩ | h
    · omega
    · have := productive_lt h; omega
  obtain ⟨hu', rfl, rfl⟩ := ch_inj (by omega) hvc hdr5 hvc' he
  rcases hdr' with ⟨h4, -⟩ | hp
  · omega
  · obtain ⟨-, hh⟩ := head_ch hu hd hvc' hp
    rw [hu'] at hh
    rcases hh with ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩ | ⟨-, h1, h2, -⟩ <;> omega

theorem fill_hop {a b x y : ℕ} :
    Function.update (Function.update (fill [(a, x)]) a none) b (some y) = fill [(b, y)] := by
  simp only [fill, Function.update_idem]
  rw [show Function.update (empty : Config ℕ ℕ) a none = empty from
    Function.update_eq_self a empty]

/-- A lone packet hops on. -/
theorem reach_hop {N : Network ℕ ℕ} {c d c' : ℕ}
    (hr : N.lts.Reachable empty (fill [(c, d)])) (ha : N.arrived c d = false)
    (hq : (c', d) ∈ N.route c d) (hne : c' ≠ c) : N.lts.Reachable empty (fill [(c', d)]) := by
  refine hr.tail ?_
  have hst := StepWith.hop (N := N) (sel := N.adaptive) (f := fill [(c, d)]) (c := c) (c' := c')
    (by simp [fill]) ha hq (by simp [fill, hne, empty])
  rw [fill_hop] at hst
  exact ⟨_, hst⟩

/-- **A packet can occupy alone every pair it can occupy**, in every network permitting the
hops of a mesh family. -/
theorem reachable_single (hF : MeshFamily Mk) {k : ℕ} {N : Network ℕ ℕ}
    (hext : (Mk k).Extends N) {c d : ℕ} (h : (Mk k).PairReachable (c, d)) :
    tdLegal k c d ∧ N.lts.Reachable empty (fill [(c, d)]) := by
  obtain ⟨q₀, hq₀, hr⟩ := h
  suffices ∀ q, Relation.ReflTransGen (Mk k).PacketStep q₀ q →
      tdLegal k q.1 q.2 ∧ N.lts.Reachable empty (fill [q]) from this _ hr
  intro q hq
  induction hq with
  | refl =>
    refine ⟨(td_closed hF k).inject _ hq₀, Relation.ReflTransGen.single ⟨.inject q₀.1 q₀.2, ?_⟩⟩
    exact StepWith.inject (f := empty) (by rw [hext.inject]; exact hq₀) rfl
  | @tail b q' _ hst ih =>
    obtain ⟨hl, hr⟩ := ih
    obtain ⟨ha, hq⟩ := hst
    refine ⟨(td_closed hF k).route _ _ _ hl ha hq, ?_⟩
    have hsnd : q'.2 = b.2 := route_snd hF ha hq
    have he : q' = (q'.1, b.2) := Prod.ext rfl hsnd
    have hne := td_ne hF hl ha hq
    rw [he] at hq ⊢
    exact reach_hop (c := b.1) (d := b.2) hr (by rw [hext.arrived]; exact ha)
      (hext.route _ _ _ ha hq) hne

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
