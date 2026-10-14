/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.OptimalRouting
import AsyncLean.Routing.Embed

/-!
# Maximally adaptive routing on meshes of every size, part 1: windows

Part 1 of 3 of `AsyncLean.Examples.MeshMaximal`; that module has the overview.
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

end Mesh

end AsyncLean.Examples
