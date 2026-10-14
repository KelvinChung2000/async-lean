/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshMaximal.Windows

/-!
# Maximally adaptive routing on meshes of every size, part 2: the window certificates and a single packet

Part 2 of 3 of `AsyncLean.Examples.MeshMaximal`; that module has the overview.
-/

namespace AsyncLean.Examples

open Network Mesh

namespace Mesh

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

end Mesh

end AsyncLean.Examples
