/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.GraphTwoPhase
import Mathlib.Data.Set.Finite.Lattice

/-!
# Planes: routing that scales linearly with the connections

`AsyncLean.Flow.Scaling` shows that in the fluid model the best throughput of `m` connections
per link is exactly `m` times the best throughput of one, and that it is reached by treating
the connections as `m` **planes**: each plane a full copy of the network, every packet choosing a
plane at its source and staying on it.  This file makes that scheme a packet network and proves
that it keeps every guarantee of its planes, for every number of planes, and that the planes do
not interfere: `m` planes carry `m` independent copies of the traffic of one.

In the literature these are **multiple physical networks** (Yoon, Jiang, Becker and Dally,
*Virtual channels vs. multiple physical networks*, 2010), also called network planes.  The word
*lane* is avoided: Dally (*Virtual-channel flow control*, 1992) uses it for a virtual channel.

## The network (`Network.planes`)

Given a list `ls` of planes and a network `N i` for each plane (the same network on every plane,
or different ones: a different spanning tree, a different escape, a different choice of
intermediates), the channels are pairs `(i, c)` of a plane and a channel of that plane; a packet in
plane `i` is routed by `N i` and stays in plane `i`; a source may inject into any plane (the choice
of plane is free: round robin, hashing, the least loaded plane, any rule, as the injection actions
are chosen by the environment and throttled by the selection).  Each plane keeps its own virtual
channels; no virtual channel is added, whatever the number of planes.

## Safety for every number of planes

The library's safety proofs all follow one recipe: a closed set of legal pairs, an escape
subfunction that is connected and has a well-founded dependency graph (Duato), and a ranking
function that decreases on every hop.  `Network.SafeCert` packages it, `SafeCert.correct`,
`SafeCert.underLoad` and `SafeCert.sourceSel` derive the guarantees from it, and
**`SafeCert.planes`** builds the certificate of the plane network from those of its planes: the
dependencies of the plane network never cross planes, so its escape dependency graph is the
disjoint union of the planes' graphs, well founded when each of them is.

* `Network.planes_correct` : if every plane has a certificate, the plane network is deadlock free
  and livelock free under every valid selection (which may look at every plane: pick the least
  congested hop, compare planes) and starvation free under strong fairness, and delivers every
  packet under saturation along every channel-fair run (`Network.planes_underLoad`).
* `GraphData.planes_correct`, `GraphData.planes_twoPhase_correct`,
  `GraphData.planes_twoPhase_sourceSel` : on **every finite connected graph**, any number of planes
  of minimal adaptive routing with a spanning-tree escape (`GraphData.net`), or of the two-phase
  network with bounded returns (`GraphData.twoPhaseNet`, the scheme behind `bandit2m7f5k`), with
  a different spanning tree and choice of intermediates on every plane if wished, under every
  selection that never refuses a free escape hop and may throttle the sources.

## Independence: `m` planes carry `m` times the traffic

* `Network.planes_reachable_iff` : the reachable configurations of the plane network are exactly
  the tuples of reachable configurations of the planes (and empty planes outside `ls`).
* `Network.planes_path` : **planes run in parallel.**  Any runs of the planes, one per plane, are
  together one run of the plane network, whose actions are those of the planes; no plane blocks
  another.
* `Network.planes_path_ejections` : the run delivers the sum of the packets the planes deliver.
  With `m` copies of one network, any schedule of one copy is achieved by all `m` at once and
  delivers `m` times its packets: the packet network keeps the linear scaling of the fluid
  model.
-/

namespace AsyncLean

namespace Network

variable {ι C P : Type*}

/-! ### The plane network -/

/-- A channel and header of a plane network, from a channel and header of plane `i`. -/
def toPlane (i : ι) (q : C × P) : (ι × C) × P := ((i, q.1), q.2)

/-- **The plane network**: the networks `N i` side by side, one per plane of `ls`.  A packet in
plane `i` is routed by `N i` and stays in plane `i`; a source may inject into every plane. -/
def planes (ls : List ι) (N : ι → Network C P) : Network (ι × C) P where
  arrived x p := (N x.1).arrived x.2 p
  route x p := ((N x.1).route x.2 p).map (toPlane x.1)
  inject := ls.flatMap fun i => (N i).inject.map (toPlane i)

section Basic

variable {ls : List ι} {N : ι → Network C P}

@[simp] theorem planes_arrived (i : ι) (c : C) (p : P) :
    (planes ls N).arrived (i, c) p = (N i).arrived c p := rfl

theorem mem_planes_route {x : ι × C} {p : P} {q : (ι × C) × P} :
    q ∈ (planes ls N).route x p ↔ ∃ q' ∈ (N x.1).route x.2 p, toPlane x.1 q' = q := by
  simp [planes]

theorem mem_planes_inject {q : (ι × C) × P} :
    q ∈ (planes ls N).inject ↔ ∃ i ∈ ls, ∃ q' ∈ (N i).inject, toPlane i q' = q := by
  simp [planes]

theorem toPlane_mem_route {i : ι} {c : C} {p : P} {q : C × P} :
    toPlane i q ∈ (planes ls N).route (i, c) p ↔ q ∈ (N i).route c p := by
  constructor
  · intro h
    obtain ⟨q', hq', he⟩ := mem_planes_route.1 h
    obtain ⟨a, b⟩ := q
    obtain ⟨a', b'⟩ := q'
    simp only [toPlane, Prod.mk.injEq] at he
    obtain ⟨⟨-, rfl⟩, rfl⟩ := he
    exact hq'
  · intro h; exact mem_planes_route.2 ⟨q, h, rfl⟩

end Basic

/-! ### Safety certificates -/

/-- **A safety certificate** of a network, the recipe of every safety proof of the library: a
closed set of legal pairs with finitely many elements, an escape subfunction inside the routing
that is connected and has a well-founded dependency graph (Duato's condition), and a ranking
function that decreases on every hop. -/
structure SafeCert (M : Network C P) where
  /-- The legal pairs: every pair a packet can occupy. -/
  legal : C → P → Prop
  closed : M.Closed legal
  finite : {q : C × P | legal q.1 q.2}.Finite
  /-- The escape subfunction. -/
  esc : C → P → List (C × P)
  esc_sub : ∀ c p q, q ∈ esc c p → q ∈ M.route c p
  esc_conn : ∀ c p, legal c p → M.arrived c p = false → esc c p ≠ []
  esc_wf : WellFounded (flip (M.Dep legal esc))
  /-- The ranking function. -/
  rank : C → P → ℕ
  rank_lt : ∀ c p q, legal c p → M.arrived c p = false → q ∈ M.route c p →
    rank q.1 q.2 < rank c p

namespace SafeCert

variable {M : Network C P} (K : SafeCert M)

theorem chans_finite : {c | ∃ p, K.legal c p}.Finite :=
  (K.finite.image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩

section Guarantees

variable [DecidableEq C]

include K

/-- A certified network is deadlock and livelock free under every valid selection and starvation
free under strongly fair scheduling. -/
theorem correct : M.Correct ∧ M.StarvationFree :=
  ⟨⟨M.deadlockFree_of_escape K.closed K.esc (fun c p q _ _ h => K.esc_sub c p q h) K.esc_conn
      K.esc_wf,
    M.livelockFree_of_ranking K.closed K.chans_finite K.rank K.rank_lt⟩,
    M.starvationFree_of_escape_ranking K.closed K.finite K.esc
      (fun c p q _ _ h => K.esc_sub c p q h) K.esc_conn K.esc_wf K.rank K.rank_lt⟩

/-- Under every selection that never refuses a free escape hop, a certified network is deadlock
and livelock free and delivers every packet along every channel-fair run, with injections going
on for ever. -/
theorem underLoad {sel : Selection C P} (hsel : M.EscapeSel K.esc sel) :
    M.DeadlockFreeWith sel ∧ M.LivelockFreeWith sel ∧
      M.StarvationFreeUnderLoad sel (fun _ => False) :=
  ⟨M.deadlockFreeWith_of_escape K.closed K.esc K.esc_conn K.esc_wf hsel,
    M.livelockFreeWith_of_ranking K.closed K.chans_finite K.rank K.rank_lt hsel.sub,
    M.starvationFreeUnderLoad_of_escape K.closed K.esc K.esc_conn K.esc_wf K.rank K.rank_lt hsel⟩

/-- `underLoad` under every valid selection. -/
theorem underLoad_of_valid {sel : Selection C P} (hsel : M.ValidSel sel) :
    M.DeadlockFreeWith sel ∧ M.LivelockFreeWith sel ∧
      M.StarvationFreeUnderLoad sel (fun _ => False) :=
  K.underLoad (ValidSel.escapeSel M hsel K.esc_sub)

/-- **Throttled sources**: if no hop leads into a source channel (`src`), then under every
selection that never refuses a free escape hop outside the sources and releases a source's
packet once the rest of the network is empty, a certified network is deadlock and livelock free
and delivers every packet outside the sources along every channel-fair run. -/
theorem sourceSel {src : C → Prop}
    (hroute : ∀ c p q, K.legal c p → M.arrived c p = false → q ∈ M.route c p → ¬ src q.1)
    {sel : Selection C P} (hsel : M.SourceSel K.esc src sel) :
    M.DeadlockFreeWith sel ∧ M.LivelockFreeWith sel ∧ M.StarvationFreeUnderLoad sel src :=
  have hesc : ∀ c p q, K.legal c p → M.arrived c p = false → q ∈ K.esc c p → ¬ src q.1 :=
    fun c p q hl ha hq => hroute c p q hl ha (K.esc_sub c p q hq)
  ⟨M.deadlockFreeWith_of_source K.closed K.esc K.esc_conn K.esc_wf hesc hsel,
    M.livelockFreeWith_of_ranking K.closed K.chans_finite K.rank K.rank_lt hsel.sub,
    M.starvationFreeUnderLoad_of_source K.closed K.esc K.esc_conn K.esc_wf hesc hroute K.rank
      K.rank_lt hsel⟩

end Guarantees

/-! ### The certificate of the plane network -/

variable {N : ι → Network C P}

/-- The legal pairs of the plane network: a plane of `ls` and a legal pair of that plane. -/
def planesLegal (K : ∀ i, SafeCert (N i)) (ls : List ι) (x : ι × C) (p : P) : Prop :=
  x.1 ∈ ls ∧ (K x.1).legal x.2 p

/-- The escape subfunction of the plane network: the escape of the packet's plane. -/
def planesEsc (K : ∀ i, SafeCert (N i)) (x : ι × C) (p : P) : List ((ι × C) × P) :=
  ((K x.1).esc x.2 p).map (toPlane x.1)

/-- **The escape dependencies never cross planes**: a dependency of the plane network is a
dependency of one plane. -/
theorem planes_dep {K : ∀ i, SafeCert (N i)} {ls : List ι} {x y : ι × C}
    (h : (Network.planes ls N).Dep (planesLegal K ls) (planesEsc K) x y) :
    y.1 = x.1 ∧ (N x.1).Dep (K x.1).legal (K x.1).esc x.2 y.2 := by
  obtain ⟨p, p', hl, ha, hq⟩ := h
  obtain ⟨⟨c', p''⟩, hq', he⟩ := List.mem_map.1 hq
  simp only [toPlane, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨rfl, p, _, hl.2, ha, hq'⟩

theorem planes_esc_wf (K : ∀ i, SafeCert (N i)) (ls : List ι) :
    WellFounded (flip ((Network.planes ls N).Dep (planesLegal K ls) (planesEsc K))) := by
  have key : ∀ i c, Acc (flip ((N i).Dep (K i).legal (K i).esc)) c →
      Acc (flip ((Network.planes ls N).Dep (planesLegal K ls) (planesEsc K))) (i, c) := by
    intro i c h
    induction h with
    | intro c _ ih =>
      refine ⟨_, fun y hy => ?_⟩
      obtain ⟨hy1, hy2⟩ := planes_dep hy
      obtain ⟨j, c'⟩ := y
      simp only at hy1
      subst hy1
      exact ih c' hy2
  exact ⟨fun ⟨i, c⟩ => key i c ((K i).esc_wf.apply c)⟩

/-- **The certificate of the plane network**, from the certificates of its planes: legal pairs,
escape and ranking of the packet's plane. -/
def planes (K : ∀ i, SafeCert (N i)) (ls : List ι) : SafeCert (Network.planes ls N) where
  legal := planesLegal K ls
  closed := ⟨fun q hq => by
      obtain ⟨i, hi, q', hq', rfl⟩ := mem_planes_inject.1 hq
      exact ⟨hi, (K i).closed.inject q' hq'⟩,
    fun x p q hl ha hq => by
      obtain ⟨q', hq', rfl⟩ := mem_planes_route.1 hq
      exact ⟨hl.1, (K x.1).closed.route x.2 p q' hl.2 ha hq'⟩⟩
  finite := by
    refine (Set.Finite.biUnion (List.finite_toSet ls)
      fun i _ => ((K i).finite.image (toPlane i))).subset ?_
    rintro ⟨⟨i, c⟩, p⟩ ⟨hi, hl⟩
    exact Set.mem_biUnion hi ⟨(c, p), hl, rfl⟩
  esc := planesEsc K
  esc_sub x p q hq := by
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact mem_planes_route.2 ⟨q', (K x.1).esc_sub _ _ _ hq', rfl⟩
  esc_conn x p hl ha := by
    simpa [planesEsc] using (K x.1).esc_conn x.2 p hl.2 ha
  esc_wf := planes_esc_wf K ls
  rank x p := (K x.1).rank x.2 p
  rank_lt x p q hl ha hq := by
    obtain ⟨q', hq', rfl⟩ := mem_planes_route.1 hq
    exact (K x.1).rank_lt x.2 p q' hl.2 ha hq'

end SafeCert

/-! ### Safety of the plane network -/

section Safety

variable [DecidableEq ι] [DecidableEq C] {N : ι → Network C P}

/-- **Planes keep the guarantees of their planes, for every number of planes**: if every plane has
a safety certificate, the plane network is deadlock and livelock free under every valid selection
(which may look at every plane) and starvation free under strongly fair scheduling. -/
theorem planes_correct (K : ∀ i, SafeCert (N i)) (ls : List ι) :
    (planes ls N).Correct ∧ (planes ls N).StarvationFree :=
  (SafeCert.planes K ls).correct

/-- **Planes deliver under saturation**: under every valid selection, the plane network is
deadlock and livelock free and delivers every packet along every channel-fair run, with
injections going on for ever. -/
theorem planes_underLoad (K : ∀ i, SafeCert (N i)) (ls : List ι) {sel : Selection (ι × C) P}
    (hsel : (planes ls N).ValidSel sel) :
    (planes ls N).DeadlockFreeWith sel ∧ (planes ls N).LivelockFreeWith sel ∧
      (planes ls N).StarvationFreeUnderLoad sel (fun _ => False) :=
  (SafeCert.planes K ls).underLoad_of_valid hsel

end Safety

/-! ### Independence of the planes -/

section Independence

variable [DecidableEq ι] [DecidableEq C] {ls : List ι} {N : ι → Network C P}

/-- Plane `i` of a configuration of the plane network. -/
def plane (f : Config (ι × C) P) (i : ι) : Config C P := fun c => f (i, c)

/-- The configuration of the plane network made of one configuration per plane. -/
def combine (F : ι → Config C P) : Config (ι × C) P := fun x => F x.1 x.2

omit [DecidableEq ι] [DecidableEq C] in
@[simp] theorem plane_combine (F : ι → Config C P) (i : ι) : plane (combine F) i = F i := rfl

omit [DecidableEq ι] [DecidableEq C] in
@[simp] theorem combine_plane (f : Config (ι × C) P) : combine (plane f) = f := rfl

/-- An action of plane `i`, as an action of the plane network. -/
def Act.toPlane (i : ι) : Act C P → Act (ι × C) P
  | .inject c p => .inject (i, c) p
  | .hop c c' p' => .hop (i, c) (i, c') p'
  | .eject c => .eject (i, c)

/-- The action delivers a packet. -/
def Act.isEject : Act C P → Bool
  | .eject _ => true
  | _ => false

omit [DecidableEq ι] [DecidableEq C] in
@[simp] theorem Act.isEject_toPlane (i : ι) (a : Act C P) : (a.toPlane i).isEject = a.isEject := by
  cases a <;> rfl

theorem combine_update (F : ι → Config C P) (i : ι) (g : Config C P) (c : C) (v : Option P) :
    combine (Function.update F i (Function.update g c v)) =
      Function.update (combine (Function.update F i g)) (i, c) v := by
  funext ⟨j, d⟩
  by_cases hj : j = i
  · subst hj
    by_cases hd : d = c
    · subst hd; simp [combine]
    · simp [combine, hd]
  · simp [combine, hj]

theorem plane_update_same (f : Config (ι × C) P) (i : ι) (c : C) (v : Option P) :
    plane (Function.update f (i, c) v) i = Function.update (plane f i) c v := by
  funext d
  by_cases hd : d = c
  · subst hd; simp [plane]
  · simp [plane, hd]

theorem plane_update_ne (f : Config (ι × C) P) {i j : ι} (h : j ≠ i) (c : C) (v : Option P) :
    plane (Function.update f (i, c) v) j = plane f j := by
  funext d
  simp [plane, h]

/-- A step of plane `i` is a step of the plane network, whatever the other planes hold. -/
theorem planes_step {i : ι} (hi : i ∈ ls) {F : ι → Config C P} {a : Act C P} {g : Config C P}
    (h : (N i).lts.step (F i) a g) :
    (planes ls N).lts.step (combine F) (a.toPlane i) (combine (Function.update F i g)) := by
  change (N i).StepWith (N i).adaptive (F i) a g at h
  change (planes ls N).StepWith (planes ls N).adaptive _ _ _
  cases h with
  | @inject c p hq hfree =>
    rw [combine_update, Function.update_eq_self]
    exact StepWith.inject (mem_planes_inject.2 ⟨i, hi, (c, p), hq, rfl⟩) hfree
  | @hop c c' p p' hp harr hq hfree =>
    rw [combine_update, combine_update, Function.update_eq_self]
    exact StepWith.hop (c := (i, c)) (c' := (i, c')) hp harr (toPlane_mem_route.2 hq) hfree
  | @eject c p hp harr =>
    rw [combine_update, Function.update_eq_self]
    exact StepWith.eject (c := (i, c)) hp harr

/-- A run of plane `i` is a run of the plane network, whatever the other planes hold. -/
theorem planes_path_one {i : ι} (hi : i ∈ ls) {g g' : Config C P} {as : List (Act C P)}
    (h : (N i).lts.Path g as g') : ∀ F : ι → Config C P, F i = g →
    (planes ls N).lts.Path (combine F) (as.map (Act.toPlane i))
      (combine (Function.update F i g')) := by
  induction h with
  | nil s =>
    intro F hF
    subst hF
    rw [Function.update_eq_self]
    exact LTS.Path.nil _
  | @cons s s' s'' l as hst _ ih =>
    intro F hF
    subst hF
    refine LTS.Path.cons (planes_step hi hst) ?_
    have := ih (Function.update F i s') (by simp)
    rwa [Function.update_idem] at this

/-- **Planes run in parallel.**  For distinct planes `L` of `ls`, runs of the planes from `F i` to
`G i` (the other planes stay as they are) are together one run of the plane network, performing
the actions of the planes one plane after the other.  No plane blocks another: any schedule each
plane can follow on its own, all planes follow at once. -/
theorem planes_path {L : List ι} (hL : ∀ i ∈ L, i ∈ ls) (hnd : L.Nodup)
    {F G : ι → Config C P} {as : ι → List (Act C P)}
    (h : ∀ i ∈ L, (N i).lts.Path (F i) (as i) (G i)) (hout : ∀ i ∉ L, F i = G i) :
    (planes ls N).lts.Path (combine F) (L.flatMap fun i => (as i).map (Act.toPlane i))
      (combine G) := by
  induction L generalizing F with
  | nil =>
    have : F = G := funext fun i => hout i (by simp)
    subst this
    exact LTS.Path.nil _
  | cons i L ih =>
    obtain ⟨hiL, hnd'⟩ := List.nodup_cons.1 hnd
    rw [List.flatMap_cons]
    refine (planes_path_one (hL i (by simp)) (h i (by simp)) F rfl).append
      (ih (fun j hj => hL j (by simp [hj])) hnd' (fun j hj => ?_) (fun j hj => ?_))
    · have hji : j ≠ i := fun e => hiL (e ▸ hj)
      rw [Function.update_of_ne hji]
      exact h j (by simp [hj])
    · by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]
        exact hout j (by simp [hji, hj])

omit [DecidableEq ι] [DecidableEq C] in
/-- The packets delivered by the actions of all planes are the sum over the planes. -/
theorem ejections_flatMap (L : List ι) (as : ι → List (Act C P)) :
    (L.flatMap fun i => (as i).map (Act.toPlane i)).countP (fun a => a.isEject) =
      (L.map fun i => (as i).countP (fun a => a.isEject)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.flatMap_cons, List.countP_append, ih, List.countP_map, List.map_cons,
      List.sum_cons]
    simp [Function.comp_def]

/-- **`m` copies deliver `m` times the packets.**  Any run of one network, run in each of `m`
planes of copies of it at once, is a run of the plane network delivering `m` times the packets
the single run delivers. -/
theorem copies_path {M : Network C P} {m : ℕ} {g g' : Config C P} {as : List (Act C P)}
    (h : M.lts.Path g as g') :
    ∃ bs, (planes (List.finRange m) fun _ => M).lts.Path (combine fun _ => g) bs
      (combine fun _ => g') ∧
      bs.countP (fun a => a.isEject) = m * as.countP (fun a => a.isEject) := by
  refine ⟨_, planes_path (L := List.finRange m) (as := fun _ => as) (fun i hi => hi)
    (List.nodup_finRange m) (fun _ _ => h) (fun i hi => absurd (List.mem_finRange i) hi), ?_⟩
  rw [ejections_flatMap]
  simp

/-- **The reachable configurations of the plane network are exactly the tuples of reachable
configurations of its planes** (the planes outside `ls` stay empty). -/
theorem planes_reachable_iff {f : Config (ι × C) P} :
    (planes ls N).lts.Reachable empty f ↔
      (∀ i ∈ ls, (N i).lts.Reachable empty (plane f i)) ∧
        ∀ i ∉ ls, plane f i = empty := by
  constructor
  · intro h
    refine LTS.Reachable.invariant
      (I := fun f => (∀ i ∈ ls, (N i).lts.Reachable empty (plane f i)) ∧
        ∀ i ∉ ls, plane f i = empty) h ⟨fun _ _ => LTS.Reachable.refl _, fun _ _ => rfl⟩ ?_
    rintro f a f' ⟨hr, ho⟩ hst
    change (planes ls N).StepWith (planes ls N).adaptive f a f' at hst
    -- `i` is the plane of the step, `g'` its new configuration
    have hplane : ∀ (i : ι), i ∈ ls → (∀ j ≠ i, plane f' j = plane f j) →
        (N i).lts.Reachable empty (plane f' i) →
        (∀ i ∈ ls, (N i).lts.Reachable empty (plane f' i)) ∧
          ∀ i ∉ ls, plane f' i = empty := by
      intro i hi hne hri
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · by_cases hji : j = i
        · subst hji; exact hri
        · rw [hne j hji]; exact hr j hj
      · have hji : j ≠ i := fun e => hj (e ▸ hi)
        rw [hne j hji]; exact ho j hj
    have hin : ∀ i c p, f (i, c) = some p → i ∈ ls := fun i c p hp => by
      by_contra hi
      have : f (i, c) = none := congrFun (ho i hi) c
      simp [hp] at this
    cases hst with
    | @inject x p hq hfree =>
      obtain ⟨i, hi, ⟨c, p0⟩, hq', he⟩ := mem_planes_inject.1 hq
      simp only [toPlane, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine hplane i hi (fun j hj => plane_update_ne _ hj _ _) ?_
      rw [plane_update_same]
      exact (hr i hi).tail ⟨_, StepWith.inject hq' hfree⟩
    | @hop x x' p p' hp harr hq hfree =>
      obtain ⟨i, c⟩ := x
      obtain ⟨⟨c', p0⟩, hq', he⟩ := mem_planes_route.1 hq
      simp only [toPlane, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hi := hin i c p hp
      refine hplane i hi (fun j hj => by rw [plane_update_ne _ hj, plane_update_ne _ hj]) ?_
      rw [plane_update_same, plane_update_same]
      exact (hr i hi).tail ⟨_, StepWith.hop (f := plane f i) hp harr hq' hfree⟩
    | @eject x p hp harr =>
      obtain ⟨i, c⟩ := x
      have hi := hin i c p hp
      refine hplane i hi (fun j hj => plane_update_ne _ hj _ _) ?_
      rw [plane_update_same]
      exact (hr i hi).tail ⟨_, StepWith.eject (f := plane f i) hp harr⟩
  · rintro ⟨hr, ho⟩
    have : ∀ i, ∃ as : List (Act C P), i ∈ ls → (N i).lts.Path empty as (plane f i) :=
        fun i => by
      by_cases hi : i ∈ ls
      · obtain ⟨as, has⟩ := (hr i hi).exists_path
        exact ⟨as, fun _ => has⟩
      · exact ⟨[], fun h => absurd h hi⟩
    choose as has using this
    have := planes_path (N := N) (L := ls.dedup) (F := fun _ => empty) (G := plane f) (as := as)
      (fun i hi => List.mem_dedup.1 hi) (List.nodup_dedup ls)
      (fun i hi => has i (List.mem_dedup.1 hi))
      (fun i hi => (ho i (fun h => hi (List.mem_dedup.2 h))).symm)
    exact this.reachable

/-- Under every valid selection, every plane of a reachable configuration of the plane network is
a reachable configuration of that plane. -/
theorem planes_reachable_plane {sel : Selection (ι × C) P} (hsel : (planes ls N).ValidSel sel)
    {f : Config (ι × C) P} (h : ((planes ls N).ltsWith sel).Reachable empty f) (i : ι) :
    (N i).lts.Reachable empty (plane f i) := by
  obtain ⟨hr, ho⟩ := planes_reachable_iff.1 ((planes ls N).reachable_to_adaptive hsel h)
  by_cases hi : i ∈ ls
  · exact hr i hi
  · rw [ho i hi]

end Independence

end Network

/-! ### Planes on every graph -/

namespace GraphData

open Network

variable {V : Type*} [DecidableEq V]

/-- The safety certificate of minimal adaptive routing with a spanning-tree escape. -/
def cert (G : GraphData V) : SafeCert G.net where
  legal := G.legal
  closed := G.closed
  finite := G.pairs_finite
  esc := G.escape
  esc_sub c d q hq := by
    simp only [escape, List.mem_singleton] at hq
    subst hq
    exact G.escHop_mem_route c d
  esc_conn := G.esc_conn
  esc_wf := G.esc_wf
  rank := G.rank
  rank_lt := G.rank_lt

/-- The safety certificate of adaptive routing with bounded returns. -/
def budgetCert (G : GraphData V) (B : ℕ) : SafeCert (G.budgetNet B) where
  legal := G.budgetLegal B
  closed := G.budget_closed B
  finite := G.budget_pairs_finite B
  esc := G.budgetEscape
  esc_sub _ _ _ hq := G.budgetEscape_sub hq
  esc_conn := G.budget_esc_conn B
  esc_wf := G.budget_esc_wf B
  rank := G.budgetRank
  rank_lt := G.budget_rank_lt B

/-- The safety certificate of adaptive two-phase routing and bounded returns. -/
def twoPhaseCert (G : GraphData V) (B : ℕ) (W : V → V → List (Option V)) :
    SafeCert (G.twoPhaseNet B W) where
  legal := G.twoPhaseLegal B
  closed := G.twoPhase_closed B W
  finite := G.twoPhase_pairs_finite B
  esc := G.twoPhaseEscape
  esc_sub _ _ _ hq := G.twoPhaseEscape_sub hq
  esc_conn := G.twoPhase_esc_conn B W
  esc_wf := G.twoPhase_esc_wf B W
  rank := G.twoPhaseRank
  rank_lt := G.twoPhase_rank_lt B W

variable {ι : Type*} [DecidableEq ι]

/-- **Planes of minimal adaptive routing on every graph**: for any planes `ls`, each with its own
graph data (the same graph with a different spanning tree, for example, to spread the escape
traffic over different trees), the plane network is deadlock and livelock free under every valid
selection, starvation free under strong fairness, and delivers every packet under
saturation. -/
theorem planes_correct (Gs : ι → GraphData V) (ls : List ι) :
    (planes ls fun i => (Gs i).net).Correct ∧ (planes ls fun i => (Gs i).net).StarvationFree ∧
      ∀ sel, (planes ls fun i => (Gs i).net).ValidSel sel →
        (planes ls fun i => (Gs i).net).StarvationFreeUnderLoad sel (fun _ => False) :=
  let K := fun i => (Gs i).cert
  ⟨(Network.planes_correct K ls).1, (Network.planes_correct K ls).2,
    fun _ hsel => (Network.planes_underLoad K ls hsel).2.2⟩

/-- **Planes of adaptive routing with bounded returns on every graph**: deadlock, livelock and
starvation free, and delivering under saturation, for every number of planes and every return
budget. -/
theorem planes_budget_correct (Gs : ι → GraphData V) (B : ℕ) (ls : List ι) :
    (planes ls fun i => (Gs i).budgetNet B).Correct ∧
      (planes ls fun i => (Gs i).budgetNet B).StarvationFree ∧
      ∀ sel, (planes ls fun i => (Gs i).budgetNet B).ValidSel sel →
        (planes ls fun i => (Gs i).budgetNet B).StarvationFreeUnderLoad sel (fun _ => False) :=
  let K := fun i => (Gs i).budgetCert B
  ⟨(Network.planes_correct K ls).1, (Network.planes_correct K ls).2,
    fun _ hsel => (Network.planes_underLoad K ls hsel).2.2⟩

/-- **Planes of the two-phase network on every graph**: for every number of planes, every return
budget and every choice of intermediates per plane, deadlock, livelock and starvation free, and
delivering under saturation. -/
theorem planes_twoPhase_correct (Gs : ι → GraphData V) (B : ℕ)
    (W : ι → V → V → List (Option V)) (ls : List ι) :
    (planes ls fun i => (Gs i).twoPhaseNet B (W i)).Correct ∧
      (planes ls fun i => (Gs i).twoPhaseNet B (W i)).StarvationFree ∧
      ∀ sel, (planes ls fun i => (Gs i).twoPhaseNet B (W i)).ValidSel sel →
        (planes ls fun i => (Gs i).twoPhaseNet B (W i)).StarvationFreeUnderLoad sel
          (fun _ => False) :=
  let K := fun i => (Gs i).twoPhaseCert B (W i)
  ⟨(Network.planes_correct K ls).1, (Network.planes_correct K ls).2,
    fun _ hsel => (Network.planes_underLoad K ls hsel).2.2⟩

/-- **Planes of the two-phase network with throttled sources** (the selection of the simulated
scheme `bandit2m7f5k`, run in every plane): under every selection that never refuses a free
escape hop outside the injection channels and releases a packet from its injection channel once
the rest of the network is empty — which may compare planes, pick a plane by congestion and
throttle per plane — the plane network is deadlock and livelock free and delivers every packet
outside the injection channels along every channel-fair run. -/
theorem planes_twoPhase_sourceSel (Gs : ι → GraphData V) (B : ℕ)
    (W : ι → V → V → List (Option V)) (ls : List ι)
    {sel : Selection (ι × GChan V) (V × Option V × ℕ)}
    (hsel : (planes ls fun i => (Gs i).twoPhaseNet B (W i)).SourceSel
      (SafeCert.planes (fun i => (Gs i).twoPhaseCert B (W i)) ls).esc
      (fun x => x.2.isInj = true) sel) :
    (planes ls fun i => (Gs i).twoPhaseNet B (W i)).DeadlockFreeWith sel ∧
      (planes ls fun i => (Gs i).twoPhaseNet B (W i)).LivelockFreeWith sel ∧
      (planes ls fun i => (Gs i).twoPhaseNet B (W i)).StarvationFreeUnderLoad sel
        (fun x => x.2.isInj = true) :=
  (SafeCert.planes (fun i => (Gs i).twoPhaseCert B (W i)) ls).sourceSel
    (fun x _ q _ _ hq => by
      obtain ⟨q', hq', rfl⟩ := mem_planes_route.1 hq
      exact (Gs x.1).twoPhase_route_not_inj hq') hsel

end GraphData

end AsyncLean
