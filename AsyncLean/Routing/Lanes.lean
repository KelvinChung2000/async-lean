/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.GraphDetour
import Mathlib.Data.Set.Finite.Lattice

/-!
# Lanes: routing that scales linearly with the connections

`AsyncLean.Flow.Scaling` shows that in the fluid model the best throughput of `m` connections
per link is exactly `m` times the best throughput of one, and that it is reached by treating
the connections as `m` **lanes**: each lane a full copy of the network, every packet choosing a
lane at its source and staying on it.  This file makes that scheme a packet network and proves
that it keeps every guarantee of its lanes, for every number of lanes, and that the lanes do
not interfere: `m` lanes carry `m` independent copies of the traffic of one.

## The network (`Network.lanes`)

Given a list `ls` of lanes and a network `N i` for each lane (the same network on every lane,
or different ones: a different spanning tree, a different escape, a different detour rule), the
channels are pairs `(i, c)` of a lane and a channel of that lane; a packet in lane `i` is routed
by `N i` and stays in lane `i`; a source may inject into any lane (the choice of lane is free:
round robin, hashing, the least loaded lane, any rule, as the injection actions are chosen by
the environment and throttled by the selection).  Each lane keeps its own virtual channels; no
virtual channel is added, whatever the number of lanes.

## Safety for every number of lanes

The library's safety proofs all follow one recipe: a closed set of legal pairs, an escape
subfunction that is connected and has a well-founded dependency graph (Duato), and a ranking
function that decreases on every hop.  `Network.SafeCert` packages it, `SafeCert.correct`,
`SafeCert.underLoad` and `SafeCert.sourceSel` derive the guarantees from it, and
**`SafeCert.lanes`** builds the certificate of the lane network from those of its lanes: the
dependencies of the lane network never cross lanes, so its escape dependency graph is the
disjoint union of the lanes' graphs, well founded when each of them is.

* `Network.lanes_correct` : if every lane has a certificate, the lane network is deadlock free
  and livelock free under every valid selection (which may look at every lane: pick the least
  congested hop, compare lanes) and starvation free under strong fairness, and delivers every
  packet under saturation along every channel-fair run (`Network.lanes_underLoad`).
* `GraphData.lanes_correct`, `GraphData.lanes_detour_correct`,
  `GraphData.lanes_detour_sourceSel` : on **every finite connected graph**, any number of lanes
  of minimal adaptive routing with a spanning-tree escape (`GraphData.net`), or of the detour
  network with bounded returns (`GraphData.detourNet`, the scheme behind `bandit2m7f5k`), with
  a different spanning tree and detour rule on every lane if wished, under every selection that
  never refuses a free escape hop and may throttle the sources.

## Independence: `m` lanes carry `m` times the traffic

* `Network.lanes_reachable_iff` : the reachable configurations of the lane network are exactly
  the tuples of reachable configurations of the lanes (and empty lanes outside `ls`).
* `Network.lanes_path` : **lanes run in parallel.**  Any runs of the lanes, one per lane, are
  together one run of the lane network, whose actions are those of the lanes; no lane blocks
  another.
* `Network.lanes_path_ejections` : the run delivers the sum of the packets the lanes deliver.
  With `m` copies of one network, any schedule of one copy is achieved by all `m` at once and
  delivers `m` times its packets: the packet network keeps the linear scaling of the fluid
  model.
-/

namespace AsyncLean

namespace Network

variable {ι C P : Type*}

/-! ### The lane network -/

/-- A channel and header of a lane network, from a channel and header of lane `i`. -/
def toLane (i : ι) (q : C × P) : (ι × C) × P := ((i, q.1), q.2)

/-- **The lane network**: the networks `N i` side by side, one per lane of `ls`.  A packet in
lane `i` is routed by `N i` and stays in lane `i`; a source may inject into every lane. -/
def lanes (ls : List ι) (N : ι → Network C P) : Network (ι × C) P where
  arrived x p := (N x.1).arrived x.2 p
  route x p := ((N x.1).route x.2 p).map (toLane x.1)
  inject := ls.flatMap fun i => (N i).inject.map (toLane i)

section Basic

variable {ls : List ι} {N : ι → Network C P}

@[simp] theorem lanes_arrived (i : ι) (c : C) (p : P) :
    (lanes ls N).arrived (i, c) p = (N i).arrived c p := rfl

theorem mem_lanes_route {x : ι × C} {p : P} {q : (ι × C) × P} :
    q ∈ (lanes ls N).route x p ↔ ∃ q' ∈ (N x.1).route x.2 p, toLane x.1 q' = q := by
  simp [lanes]

theorem mem_lanes_inject {q : (ι × C) × P} :
    q ∈ (lanes ls N).inject ↔ ∃ i ∈ ls, ∃ q' ∈ (N i).inject, toLane i q' = q := by
  simp [lanes]

theorem toLane_mem_route {i : ι} {c : C} {p : P} {q : C × P} :
    toLane i q ∈ (lanes ls N).route (i, c) p ↔ q ∈ (N i).route c p := by
  constructor
  · intro h
    obtain ⟨q', hq', he⟩ := mem_lanes_route.1 h
    obtain ⟨a, b⟩ := q
    obtain ⟨a', b'⟩ := q'
    simp only [toLane, Prod.mk.injEq] at he
    obtain ⟨⟨-, rfl⟩, rfl⟩ := he
    exact hq'
  · intro h; exact mem_lanes_route.2 ⟨q, h, rfl⟩

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

/-! ### The certificate of the lane network -/

variable {N : ι → Network C P}

/-- The legal pairs of the lane network: a lane of `ls` and a legal pair of that lane. -/
def lanesLegal (K : ∀ i, SafeCert (N i)) (ls : List ι) (x : ι × C) (p : P) : Prop :=
  x.1 ∈ ls ∧ (K x.1).legal x.2 p

/-- The escape subfunction of the lane network: the escape of the packet's lane. -/
def lanesEsc (K : ∀ i, SafeCert (N i)) (x : ι × C) (p : P) : List ((ι × C) × P) :=
  ((K x.1).esc x.2 p).map (toLane x.1)

/-- **The escape dependencies never cross lanes**: a dependency of the lane network is a
dependency of one lane. -/
theorem lanes_dep {K : ∀ i, SafeCert (N i)} {ls : List ι} {x y : ι × C}
    (h : (Network.lanes ls N).Dep (lanesLegal K ls) (lanesEsc K) x y) :
    y.1 = x.1 ∧ (N x.1).Dep (K x.1).legal (K x.1).esc x.2 y.2 := by
  obtain ⟨p, p', hl, ha, hq⟩ := h
  obtain ⟨⟨c', p''⟩, hq', he⟩ := List.mem_map.1 hq
  simp only [toLane, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨rfl, p, _, hl.2, ha, hq'⟩

theorem lanes_esc_wf (K : ∀ i, SafeCert (N i)) (ls : List ι) :
    WellFounded (flip ((Network.lanes ls N).Dep (lanesLegal K ls) (lanesEsc K))) := by
  have key : ∀ i c, Acc (flip ((N i).Dep (K i).legal (K i).esc)) c →
      Acc (flip ((Network.lanes ls N).Dep (lanesLegal K ls) (lanesEsc K))) (i, c) := by
    intro i c h
    induction h with
    | intro c _ ih =>
      refine ⟨_, fun y hy => ?_⟩
      obtain ⟨hy1, hy2⟩ := lanes_dep hy
      obtain ⟨j, c'⟩ := y
      simp only at hy1
      subst hy1
      exact ih c' hy2
  exact ⟨fun ⟨i, c⟩ => key i c ((K i).esc_wf.apply c)⟩

/-- **The certificate of the lane network**, from the certificates of its lanes: legal pairs,
escape and ranking of the packet's lane. -/
def lanes (K : ∀ i, SafeCert (N i)) (ls : List ι) : SafeCert (Network.lanes ls N) where
  legal := lanesLegal K ls
  closed := ⟨fun q hq => by
      obtain ⟨i, hi, q', hq', rfl⟩ := mem_lanes_inject.1 hq
      exact ⟨hi, (K i).closed.inject q' hq'⟩,
    fun x p q hl ha hq => by
      obtain ⟨q', hq', rfl⟩ := mem_lanes_route.1 hq
      exact ⟨hl.1, (K x.1).closed.route x.2 p q' hl.2 ha hq'⟩⟩
  finite := by
    refine (Set.Finite.biUnion (List.finite_toSet ls)
      fun i _ => ((K i).finite.image (toLane i))).subset ?_
    rintro ⟨⟨i, c⟩, p⟩ ⟨hi, hl⟩
    exact Set.mem_biUnion hi ⟨(c, p), hl, rfl⟩
  esc := lanesEsc K
  esc_sub x p q hq := by
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    exact mem_lanes_route.2 ⟨q', (K x.1).esc_sub _ _ _ hq', rfl⟩
  esc_conn x p hl ha := by
    simpa [lanesEsc] using (K x.1).esc_conn x.2 p hl.2 ha
  esc_wf := lanes_esc_wf K ls
  rank x p := (K x.1).rank x.2 p
  rank_lt x p q hl ha hq := by
    obtain ⟨q', hq', rfl⟩ := mem_lanes_route.1 hq
    exact (K x.1).rank_lt x.2 p q' hl.2 ha hq'

end SafeCert

/-! ### Safety of the lane network -/

section Safety

variable [DecidableEq ι] [DecidableEq C] {N : ι → Network C P}

/-- **Lanes keep the guarantees of their lanes, for every number of lanes**: if every lane has
a safety certificate, the lane network is deadlock and livelock free under every valid selection
(which may look at every lane) and starvation free under strongly fair scheduling. -/
theorem lanes_correct (K : ∀ i, SafeCert (N i)) (ls : List ι) :
    (lanes ls N).Correct ∧ (lanes ls N).StarvationFree :=
  (SafeCert.lanes K ls).correct

/-- **Lanes deliver under saturation**: under every valid selection, the lane network is
deadlock and livelock free and delivers every packet along every channel-fair run, with
injections going on for ever. -/
theorem lanes_underLoad (K : ∀ i, SafeCert (N i)) (ls : List ι) {sel : Selection (ι × C) P}
    (hsel : (lanes ls N).ValidSel sel) :
    (lanes ls N).DeadlockFreeWith sel ∧ (lanes ls N).LivelockFreeWith sel ∧
      (lanes ls N).StarvationFreeUnderLoad sel (fun _ => False) :=
  (SafeCert.lanes K ls).underLoad_of_valid hsel

end Safety

/-! ### Independence of the lanes -/

section Independence

variable [DecidableEq ι] [DecidableEq C] {ls : List ι} {N : ι → Network C P}

/-- Lane `i` of a configuration of the lane network. -/
def lane (f : Config (ι × C) P) (i : ι) : Config C P := fun c => f (i, c)

/-- The configuration of the lane network made of one configuration per lane. -/
def combine (F : ι → Config C P) : Config (ι × C) P := fun x => F x.1 x.2

omit [DecidableEq ι] [DecidableEq C] in
@[simp] theorem lane_combine (F : ι → Config C P) (i : ι) : lane (combine F) i = F i := rfl

omit [DecidableEq ι] [DecidableEq C] in
@[simp] theorem combine_lane (f : Config (ι × C) P) : combine (lane f) = f := rfl

/-- An action of lane `i`, as an action of the lane network. -/
def Act.toLane (i : ι) : Act C P → Act (ι × C) P
  | .inject c p => .inject (i, c) p
  | .hop c c' p' => .hop (i, c) (i, c') p'
  | .eject c => .eject (i, c)

/-- The action delivers a packet. -/
def Act.isEject : Act C P → Bool
  | .eject _ => true
  | _ => false

omit [DecidableEq ι] [DecidableEq C] in
@[simp] theorem Act.isEject_toLane (i : ι) (a : Act C P) : (a.toLane i).isEject = a.isEject := by
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

theorem lane_update_same (f : Config (ι × C) P) (i : ι) (c : C) (v : Option P) :
    lane (Function.update f (i, c) v) i = Function.update (lane f i) c v := by
  funext d
  by_cases hd : d = c
  · subst hd; simp [lane]
  · simp [lane, hd]

theorem lane_update_ne (f : Config (ι × C) P) {i j : ι} (h : j ≠ i) (c : C) (v : Option P) :
    lane (Function.update f (i, c) v) j = lane f j := by
  funext d
  simp [lane, h]

/-- A step of lane `i` is a step of the lane network, whatever the other lanes hold. -/
theorem lanes_step {i : ι} (hi : i ∈ ls) {F : ι → Config C P} {a : Act C P} {g : Config C P}
    (h : (N i).lts.step (F i) a g) :
    (lanes ls N).lts.step (combine F) (a.toLane i) (combine (Function.update F i g)) := by
  change (N i).StepWith (N i).adaptive (F i) a g at h
  change (lanes ls N).StepWith (lanes ls N).adaptive _ _ _
  cases h with
  | @inject c p hq hfree =>
    rw [combine_update, Function.update_eq_self]
    exact StepWith.inject (mem_lanes_inject.2 ⟨i, hi, (c, p), hq, rfl⟩) hfree
  | @hop c c' p p' hp harr hq hfree =>
    rw [combine_update, combine_update, Function.update_eq_self]
    exact StepWith.hop (c := (i, c)) (c' := (i, c')) hp harr (toLane_mem_route.2 hq) hfree
  | @eject c p hp harr =>
    rw [combine_update, Function.update_eq_self]
    exact StepWith.eject (c := (i, c)) hp harr

/-- A run of lane `i` is a run of the lane network, whatever the other lanes hold. -/
theorem lanes_path_one {i : ι} (hi : i ∈ ls) {g g' : Config C P} {as : List (Act C P)}
    (h : (N i).lts.Path g as g') : ∀ F : ι → Config C P, F i = g →
    (lanes ls N).lts.Path (combine F) (as.map (Act.toLane i))
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
    refine LTS.Path.cons (lanes_step hi hst) ?_
    have := ih (Function.update F i s') (by simp)
    rwa [Function.update_idem] at this

/-- **Lanes run in parallel.**  For distinct lanes `L` of `ls`, runs of the lanes from `F i` to
`G i` (the other lanes stay as they are) are together one run of the lane network, performing
the actions of the lanes one lane after the other.  No lane blocks another: any schedule each
lane can follow on its own, all lanes follow at once. -/
theorem lanes_path {L : List ι} (hL : ∀ i ∈ L, i ∈ ls) (hnd : L.Nodup)
    {F G : ι → Config C P} {as : ι → List (Act C P)}
    (h : ∀ i ∈ L, (N i).lts.Path (F i) (as i) (G i)) (hout : ∀ i ∉ L, F i = G i) :
    (lanes ls N).lts.Path (combine F) (L.flatMap fun i => (as i).map (Act.toLane i))
      (combine G) := by
  induction L generalizing F with
  | nil =>
    have : F = G := funext fun i => hout i (by simp)
    subst this
    exact LTS.Path.nil _
  | cons i L ih =>
    obtain ⟨hiL, hnd'⟩ := List.nodup_cons.1 hnd
    rw [List.flatMap_cons]
    refine (lanes_path_one (hL i (by simp)) (h i (by simp)) F rfl).append
      (ih (fun j hj => hL j (by simp [hj])) hnd' (fun j hj => ?_) (fun j hj => ?_))
    · have hji : j ≠ i := fun e => hiL (e ▸ hj)
      rw [Function.update_of_ne hji]
      exact h j (by simp [hj])
    · by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]
        exact hout j (by simp [hji, hj])

omit [DecidableEq ι] [DecidableEq C] in
/-- The packets delivered by the actions of all lanes are the sum over the lanes. -/
theorem ejections_flatMap (L : List ι) (as : ι → List (Act C P)) :
    (L.flatMap fun i => (as i).map (Act.toLane i)).countP (fun a => a.isEject) =
      (L.map fun i => (as i).countP (fun a => a.isEject)).sum := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.flatMap_cons, List.countP_append, ih, List.countP_map, List.map_cons,
      List.sum_cons]
    simp [Function.comp_def]

/-- **`m` copies deliver `m` times the packets.**  Any run of one network, run in each of `m`
lanes of copies of it at once, is a run of the lane network delivering `m` times the packets
the single run delivers. -/
theorem copies_path {M : Network C P} {m : ℕ} {g g' : Config C P} {as : List (Act C P)}
    (h : M.lts.Path g as g') :
    ∃ bs, (lanes (List.finRange m) fun _ => M).lts.Path (combine fun _ => g) bs
      (combine fun _ => g') ∧
      bs.countP (fun a => a.isEject) = m * as.countP (fun a => a.isEject) := by
  refine ⟨_, lanes_path (L := List.finRange m) (as := fun _ => as) (fun i hi => hi)
    (List.nodup_finRange m) (fun _ _ => h) (fun i hi => absurd (List.mem_finRange i) hi), ?_⟩
  rw [ejections_flatMap]
  simp

/-- **The reachable configurations of the lane network are exactly the tuples of reachable
configurations of its lanes** (the lanes outside `ls` stay empty). -/
theorem lanes_reachable_iff {f : Config (ι × C) P} :
    (lanes ls N).lts.Reachable empty f ↔
      (∀ i ∈ ls, (N i).lts.Reachable empty (lane f i)) ∧ ∀ i ∉ ls, lane f i = empty := by
  constructor
  · intro h
    refine LTS.Reachable.invariant
      (I := fun f => (∀ i ∈ ls, (N i).lts.Reachable empty (lane f i)) ∧
        ∀ i ∉ ls, lane f i = empty) h ⟨fun _ _ => LTS.Reachable.refl _, fun _ _ => rfl⟩ ?_
    rintro f a f' ⟨hr, ho⟩ hst
    change (lanes ls N).StepWith (lanes ls N).adaptive f a f' at hst
    -- `i` is the lane of the step, `g'` its new configuration
    have hlane : ∀ (i : ι), i ∈ ls → (∀ j ≠ i, lane f' j = lane f j) →
        (N i).lts.Reachable empty (lane f' i) →
        (∀ i ∈ ls, (N i).lts.Reachable empty (lane f' i)) ∧ ∀ i ∉ ls, lane f' i = empty := by
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
      obtain ⟨i, hi, ⟨c, p0⟩, hq', he⟩ := mem_lanes_inject.1 hq
      simp only [toLane, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine hlane i hi (fun j hj => lane_update_ne _ hj _ _) ?_
      rw [lane_update_same]
      exact (hr i hi).tail ⟨_, StepWith.inject hq' hfree⟩
    | @hop x x' p p' hp harr hq hfree =>
      obtain ⟨i, c⟩ := x
      obtain ⟨⟨c', p0⟩, hq', he⟩ := mem_lanes_route.1 hq
      simp only [toLane, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hi := hin i c p hp
      refine hlane i hi (fun j hj => by rw [lane_update_ne _ hj, lane_update_ne _ hj]) ?_
      rw [lane_update_same, lane_update_same]
      exact (hr i hi).tail ⟨_, StepWith.hop (f := lane f i) hp harr hq' hfree⟩
    | @eject x p hp harr =>
      obtain ⟨i, c⟩ := x
      have hi := hin i c p hp
      refine hlane i hi (fun j hj => lane_update_ne _ hj _ _) ?_
      rw [lane_update_same]
      exact (hr i hi).tail ⟨_, StepWith.eject (f := lane f i) hp harr⟩
  · rintro ⟨hr, ho⟩
    have : ∀ i, ∃ as : List (Act C P), i ∈ ls → (N i).lts.Path empty as (lane f i) := fun i => by
      by_cases hi : i ∈ ls
      · obtain ⟨as, has⟩ := (hr i hi).exists_path
        exact ⟨as, fun _ => has⟩
      · exact ⟨[], fun h => absurd h hi⟩
    choose as has using this
    have := lanes_path (N := N) (L := ls.dedup) (F := fun _ => empty) (G := lane f) (as := as)
      (fun i hi => List.mem_dedup.1 hi) (List.nodup_dedup ls)
      (fun i hi => has i (List.mem_dedup.1 hi))
      (fun i hi => (ho i (fun h => hi (List.mem_dedup.2 h))).symm)
    exact this.reachable

/-- Under every valid selection, every lane of a reachable configuration of the lane network is
a reachable configuration of that lane. -/
theorem lanes_reachable_lane {sel : Selection (ι × C) P} (hsel : (lanes ls N).ValidSel sel)
    {f : Config (ι × C) P} (h : ((lanes ls N).ltsWith sel).Reachable empty f) (i : ι) :
    (N i).lts.Reachable empty (lane f i) := by
  obtain ⟨hr, ho⟩ := lanes_reachable_iff.1 ((lanes ls N).reachable_to_adaptive hsel h)
  by_cases hi : i ∈ ls
  · exact hr i hi
  · rw [ho i hi]

end Independence

end Network

/-! ### Lanes on every graph -/

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

/-- The safety certificate of adaptive routing with detours and bounded returns. -/
def detourCert (G : GraphData V) (B : ℕ) (W : V → V → List (Option V)) :
    SafeCert (G.detourNet B W) where
  legal := G.detLegal B
  closed := G.detour_closed B W
  finite := G.detour_pairs_finite B
  esc := G.detEscape
  esc_sub _ _ _ hq := G.detEscape_sub hq
  esc_conn := G.detour_esc_conn B W
  esc_wf := G.detour_esc_wf B W
  rank := G.detRank
  rank_lt := G.detour_rank_lt B W

variable {ι : Type*} [DecidableEq ι]

/-- **Lanes of minimal adaptive routing on every graph**: for any lanes `ls`, each with its own
graph data (the same graph with a different spanning tree, for example, to spread the escape
traffic over different trees), the lane network is deadlock and livelock free under every valid
selection, starvation free under strong fairness, and delivers every packet under
saturation. -/
theorem lanes_correct (Gs : ι → GraphData V) (ls : List ι) :
    (lanes ls fun i => (Gs i).net).Correct ∧ (lanes ls fun i => (Gs i).net).StarvationFree ∧
      ∀ sel, (lanes ls fun i => (Gs i).net).ValidSel sel →
        (lanes ls fun i => (Gs i).net).StarvationFreeUnderLoad sel (fun _ => False) :=
  let K := fun i => (Gs i).cert
  ⟨(Network.lanes_correct K ls).1, (Network.lanes_correct K ls).2,
    fun _ hsel => (Network.lanes_underLoad K ls hsel).2.2⟩

/-- **Lanes of adaptive routing with bounded returns on every graph**: deadlock, livelock and
starvation free, and delivering under saturation, for every number of lanes and every return
budget. -/
theorem lanes_budget_correct (Gs : ι → GraphData V) (B : ℕ) (ls : List ι) :
    (lanes ls fun i => (Gs i).budgetNet B).Correct ∧
      (lanes ls fun i => (Gs i).budgetNet B).StarvationFree ∧
      ∀ sel, (lanes ls fun i => (Gs i).budgetNet B).ValidSel sel →
        (lanes ls fun i => (Gs i).budgetNet B).StarvationFreeUnderLoad sel (fun _ => False) :=
  let K := fun i => (Gs i).budgetCert B
  ⟨(Network.lanes_correct K ls).1, (Network.lanes_correct K ls).2,
    fun _ hsel => (Network.lanes_underLoad K ls hsel).2.2⟩

/-- **Lanes of the detour network on every graph**: for every number of lanes, every return
budget and every choice of intermediates per lane, deadlock, livelock and starvation free, and
delivering under saturation. -/
theorem lanes_detour_correct (Gs : ι → GraphData V) (B : ℕ) (W : ι → V → V → List (Option V))
    (ls : List ι) :
    (lanes ls fun i => (Gs i).detourNet B (W i)).Correct ∧
      (lanes ls fun i => (Gs i).detourNet B (W i)).StarvationFree ∧
      ∀ sel, (lanes ls fun i => (Gs i).detourNet B (W i)).ValidSel sel →
        (lanes ls fun i => (Gs i).detourNet B (W i)).StarvationFreeUnderLoad sel
          (fun _ => False) :=
  let K := fun i => (Gs i).detourCert B (W i)
  ⟨(Network.lanes_correct K ls).1, (Network.lanes_correct K ls).2,
    fun _ hsel => (Network.lanes_underLoad K ls hsel).2.2⟩

/-- **Lanes of the detour network with throttled sources** (the selection of the simulated
scheme `bandit2m7f5k`, run in every lane): under every selection that never refuses a free
escape hop outside the injection channels and releases a packet from its injection channel once
the rest of the network is empty — which may compare lanes, pick a lane by congestion and
throttle per lane — the lane network is deadlock and livelock free and delivers every packet
outside the injection channels along every channel-fair run. -/
theorem lanes_detour_sourceSel (Gs : ι → GraphData V) (B : ℕ)
    (W : ι → V → V → List (Option V)) (ls : List ι)
    {sel : Selection (ι × GChan V) (V × Option V × ℕ)}
    (hsel : (lanes ls fun i => (Gs i).detourNet B (W i)).SourceSel
      (SafeCert.lanes (fun i => (Gs i).detourCert B (W i)) ls).esc
      (fun x => x.2.isInj = true) sel) :
    (lanes ls fun i => (Gs i).detourNet B (W i)).DeadlockFreeWith sel ∧
      (lanes ls fun i => (Gs i).detourNet B (W i)).LivelockFreeWith sel ∧
      (lanes ls fun i => (Gs i).detourNet B (W i)).StarvationFreeUnderLoad sel
        (fun x => x.2.isInj = true) :=
  (SafeCert.lanes (fun i => (Gs i).detourCert B (W i)) ls).sourceSel
    (fun x _ q _ _ hq => by
      obtain ⟨q', hq', rfl⟩ := mem_lanes_route.1 hq
      exact (Gs x.1).detour_route_not_inj hq') hsel

end GraphData

end AsyncLean
