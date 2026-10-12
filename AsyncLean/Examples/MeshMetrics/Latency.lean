/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshMetrics.OneVCMaximal

/-!
# Optimal mesh routing, metric by metric, part 3: latency, XY routing and routing tables

Part 3 of 3 of `AsyncLean.Examples.MeshMetrics`; that module has the overview.
-/

namespace AsyncLean.Examples

open Network Mesh

/-! ### Latency: no routing function takes fewer hops -/

/-- A routing function on the `k × k` mesh that moves packets between neighbouring nodes only,
keeps their headers, and delivers a packet only at its destination.  Any number of virtual
channels, any adaptivity, non-minimal routes included. -/
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
