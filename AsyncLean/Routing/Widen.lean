/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.SharedLanes

/-!
# Widening: any number of copies of every channel, shared freely

`AsyncLean.Routing.Lanes` keeps `m` connections apart as `m` lanes and
`AsyncLean.Routing.SharedLanes` shares their adaptive channels.  The most flexible use of more
connections is to let a packet take **any copy** of any channel its routing permits.
`scripts/lane_scaling.py` finds that this is also the best performing use on the 8 × 8 torus
(`shared`: one escape channel and `2m - 1` adaptive channels per link).

This file proves that it is always safe: **widening** a certified network keeps every
guarantee, whatever the number of copies of each channel, for every network of the library.

## Widening (`Network.widen`)

A `Network.Widening C C'` gives every channel `c` a nonempty list of copies `cp c` in `C'`, and
maps every copy back to its channel (`φ`).  `N.widen W` routes a packet in a copy `c'` like `N`
routes it in `φ c'`, onto **every copy** of every permitted channel, and injects into every copy
of every injection channel.  The escape is widened with it: a packet may escape on any copy of
its escape channel.

* `Network.SafeCert.widen` : a safety certificate of `N` gives one of `N.widen W`.  An escape
  dependency between copies is an escape dependency between the channels they copy, so the
  dependency graph of the widening is well founded when that of `N` is
  (`Network.wf_dep_of_reduction`); legal pairs, escape and ranking are those of the channel
  copied.
* `Network.widen_correct`, `Network.widen_underLoad` : deadlock and livelock free under every
  valid selection, starvation free under strong fairness, and delivering under saturation.
* `Network.slots` : copies `(c, k)` for `k < n c` of every channel `c`.
* `GraphData.wide_correct`, `GraphData.wide_detour_correct` : on every finite connected graph,
  the bounded-return and the detour networks with `n c ≥ 1` copies of every channel `c`; for
  example one escape channel, `2m - 1` adaptive channels and `m` injection channels per link
  and node, the `shared` scheme of the simulation (`GraphData.sharedSlots`).
-/

namespace AsyncLean

namespace Network

variable {C C' P : Type*}

/-- **A widening**: every channel `c` has a nonempty list of copies `cp c`, each mapped back to
`c` by `φ`. -/
structure Widening (C C' : Type*) where
  /-- The channel a copy copies. -/
  φ : C' → C
  /-- The copies of a channel. -/
  cp : C → List C'
  φ_cp : ∀ c c', c' ∈ cp c → φ c' = c
  cp_ne_nil : ∀ c, cp c ≠ []

/-- Every copy of the channel of a hop, with the hop's header. -/
def Widening.lift (W : Widening C C') (q : C × P) : List (C' × P) :=
  (W.cp q.1).map fun c' => (c', q.2)

theorem Widening.mem_lift {W : Widening C C'} {q : C × P} {q' : C' × P} :
    q' ∈ W.lift q ↔ q'.1 ∈ W.cp q.1 ∧ q'.2 = q.2 := by
  obtain ⟨c', p'⟩ := q'
  simp only [Widening.lift, List.mem_map]
  constructor
  · rintro ⟨c'', h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨c', h, rfl⟩

/-- **The widened network**: a packet in a copy is routed as in the channel copied, onto every
copy of every permitted channel. -/
def widen (N : Network C P) (W : Widening C C') : Network C' P where
  arrived c' p := N.arrived (W.φ c') p
  route c' p := (N.route (W.φ c') p).flatMap W.lift
  inject := N.inject.flatMap W.lift

variable {N : Network C P} {W : Widening C C'}

theorem mem_widen_route {c' : C'} {p : P} {q' : C' × P} :
    q' ∈ (N.widen W).route c' p ↔ ∃ q ∈ N.route (W.φ c') p, q'.1 ∈ W.cp q.1 ∧ q'.2 = q.2 := by
  simp only [widen, List.mem_flatMap, Widening.mem_lift]

theorem mem_widen_inject {q' : C' × P} :
    q' ∈ (N.widen W).inject ↔ ∃ q ∈ N.inject, q'.1 ∈ W.cp q.1 ∧ q'.2 = q.2 := by
  simp only [widen, List.mem_flatMap, Widening.mem_lift]

namespace SafeCert

/-- The legal pairs of a widening: a legal pair of the channel copied, in one of its copies. -/
def widenLegal (K : SafeCert N) (W : Widening C C') (c' : C') (p : P) : Prop :=
  K.legal (W.φ c') p ∧ c' ∈ W.cp (W.φ c')

/-- The escape of a widening: every copy of the escape hop. -/
def widenEsc (K : SafeCert N) (W : Widening C C') (c' : C') (p : P) : List (C' × P) :=
  (K.esc (W.φ c') p).flatMap W.lift

/-- **An escape dependency between copies is an escape dependency between the channels they
copy.** -/
theorem widen_dep (K : SafeCert N) {c' d' : C'}
    (h : (N.widen W).Dep (widenLegal K W) (widenEsc K W) c' d') :
    N.Dep K.legal K.esc (W.φ c') (W.φ d') := by
  obtain ⟨p, p', hl, ha, hq⟩ := h
  obtain ⟨q, hq, hl'⟩ := List.mem_flatMap.1 hq
  obtain ⟨h1, h2⟩ := Widening.mem_lift.1 hl'
  rw [W.φ_cp _ _ h1]
  exact ⟨p, q.2, hl.1, ha, by simpa using hq⟩

/-- **The certificate of a widening**, from the certificate of the network widened. -/
def widen (K : SafeCert N) (W : Widening C C') : SafeCert (N.widen W) where
  legal := widenLegal K W
  closed := ⟨fun q' hq' => by
      obtain ⟨q, hq, h1, h2⟩ := mem_widen_inject.1 hq'
      have he := W.φ_cp _ _ h1
      refine ⟨?_, ?_⟩
      · rw [he, h2]; exact K.closed.inject q hq
      · rw [he]; exact h1,
    fun c' p q' hl ha hq' => by
      obtain ⟨q, hq, h1, h2⟩ := mem_widen_route.1 hq'
      have he := W.φ_cp _ _ h1
      refine ⟨?_, ?_⟩
      · rw [he, h2]; exact K.closed.route (W.φ c') p q hl.1 ha hq
      · rw [he]; exact h1⟩
  finite := by
    refine (Set.Finite.biUnion K.finite fun q _ =>
      (List.finite_toSet (W.lift q))).subset ?_
    rintro ⟨c', p⟩ ⟨hl, hc⟩
    exact Set.mem_biUnion (x := (W.φ c', p)) hl
      ((Widening.mem_lift (q := (W.φ c', p)) (q' := (c', p))).2 ⟨hc, rfl⟩)
  esc := widenEsc K W
  esc_sub c' p q' hq' := by
    obtain ⟨q, hq, hl'⟩ := List.mem_flatMap.1 hq'
    exact List.mem_flatMap.2 ⟨q, K.esc_sub _ _ _ hq, hl'⟩
  esc_conn c' p hl ha := by
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (K.esc_conn _ p hl.1 ha)
    obtain ⟨c'', hc⟩ := List.exists_mem_of_ne_nil _ (W.cp_ne_nil q.1)
    exact List.ne_nil_of_mem (List.mem_flatMap.2
      ⟨q, hq, (Widening.mem_lift (q := q) (q' := (c'', q.2))).2 ⟨hc, rfl⟩⟩)
  esc_wf := (N.widen W).wf_dep_of_reduction N W.φ
    (fun _ _ h => Relation.TransGen.single (widen_dep K h)) K.esc_wf
  rank c' p := K.rank (W.φ c') p
  rank_lt c' p q' hl ha hq' := by
    obtain ⟨q, hq, h1, h2⟩ := mem_widen_route.1 hq'
    have := K.rank_lt (W.φ c') p q hl.1 ha hq
    rw [W.φ_cp _ _ h1, h2]
    exact this

end SafeCert

section Safety

variable [DecidableEq C']

/-- **Widening keeps every guarantee**: if `N` has a safety certificate, then whatever the
number of copies of each channel, the widened network is deadlock and livelock free under every
valid selection, starvation free under strong fairness, and delivers every packet under
saturation along every channel-fair run. -/
theorem widen_correct (K : SafeCert N) (W : Widening C C') :
    (N.widen W).Correct ∧ (N.widen W).StarvationFree ∧
      ∀ sel, (N.widen W).ValidSel sel →
        (N.widen W).StarvationFreeUnderLoad sel (fun _ => False) :=
  ⟨(K.widen W).correct.1, (K.widen W).correct.2,
    fun _ hsel => ((K.widen W).underLoad_of_valid hsel).2.2⟩

/-- **Widening with throttled sources**: if no hop of `N` leads into a source channel, the same
holds for the copies of the source channels of the widening, under every selection that never
refuses a free escape hop outside them and releases a source once the rest is empty. -/
theorem widen_sourceSel (K : SafeCert N) (W : Widening C C') {src : C → Prop}
    (hroute : ∀ c p q, K.legal c p → N.arrived c p = false → q ∈ N.route c p → ¬ src q.1)
    {sel : Selection C' P}
    (hsel : (N.widen W).SourceSel (K.widen W).esc (fun c' => src (W.φ c')) sel) :
    (N.widen W).DeadlockFreeWith sel ∧ (N.widen W).LivelockFreeWith sel ∧
      (N.widen W).StarvationFreeUnderLoad sel (fun c' => src (W.φ c')) :=
  (K.widen W).sourceSel (fun c' p q' hl ha hq' => by
    obtain ⟨q, hq, h1, -⟩ := mem_widen_route.1 hq'
    rw [W.φ_cp _ _ h1]
    exact hroute _ p q hl.1 ha hq) hsel

end Safety

/-! ### Slots: `n c` copies of every channel -/

/-- **`n c ≥ 1` copies of every channel `c`**: the copies `(c, k)` for `k < n c`. -/
def slots (n : C → ℕ) (hn : ∀ c, 0 < n c) : Widening C (C × ℕ) where
  φ := Prod.fst
  cp c := (List.range (n c)).map fun k => (c, k)
  φ_cp c c' h := by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 h
    rfl
  cp_ne_nil c := by simpa using (hn c).ne'

end Network

/-! ### Widening on every graph -/

namespace GraphData

open Network

variable {V : Type*} [DecidableEq V]

/-- **The bounded-return network with any number of copies of every channel**, on every graph:
deadlock and livelock free under every valid selection, starvation free under strong fairness,
and delivering under saturation. -/
theorem wide_correct (G : GraphData V) (B : ℕ) (n : GChan V → ℕ) (hn : ∀ c, 0 < n c) :
    ((G.budgetNet B).widen (slots n hn)).Correct ∧
      ((G.budgetNet B).widen (slots n hn)).StarvationFree ∧
      ∀ sel, ((G.budgetNet B).widen (slots n hn)).ValidSel sel →
        ((G.budgetNet B).widen (slots n hn)).StarvationFreeUnderLoad sel (fun _ => False) :=
  widen_correct (G.budgetCert B) (slots n hn)

/-- **The detour network with any number of copies of every channel**, on every graph. -/
theorem wide_detour_correct (G : GraphData V) (B : ℕ) (W : V → V → List (Option V))
    (n : GChan V → ℕ) (hn : ∀ c, 0 < n c) :
    ((G.detourNet B W).widen (slots n hn)).Correct ∧
      ((G.detourNet B W).widen (slots n hn)).StarvationFree ∧
      ∀ sel, ((G.detourNet B W).widen (slots n hn)).ValidSel sel →
        ((G.detourNet B W).widen (slots n hn)).StarvationFreeUnderLoad sel (fun _ => False) :=
  widen_correct (G.detourCert B W) (slots n hn)

/-- **The detour network, widened, with throttled sources**: no hop leads into a copy of an
injection channel, so the source-throttling guarantee carries over. -/
theorem wide_detour_sourceSel (G : GraphData V) (B : ℕ) (W : V → V → List (Option V))
    (n : GChan V → ℕ) (hn : ∀ c, 0 < n c)
    {sel : Selection (GChan V × ℕ) (V × Option V × ℕ)}
    (hsel : ((G.detourNet B W).widen (slots n hn)).SourceSel
      ((G.detourCert B W).widen (slots n hn)).esc (fun c' => c'.1.isInj = true) sel) :
    ((G.detourNet B W).widen (slots n hn)).DeadlockFreeWith sel ∧
      ((G.detourNet B W).widen (slots n hn)).LivelockFreeWith sel ∧
      ((G.detourNet B W).widen (slots n hn)).StarvationFreeUnderLoad sel
        (fun c' => c'.1.isInj = true) :=
  widen_sourceSel (G.detourCert B W) (slots n hn) (src := fun c => c.isInj = true)
    (fun _ _ _ _ _ hq => G.detour_route_not_inj hq) hsel

/-- The copies of the `shared` scheme with `m ≥ 1` connections per link: one escape channel,
`2m - 1` adaptive channels on every link, `m` injection channels at every node. -/
def sharedSlots (m : ℕ) : GChan V → ℕ
  | .inj _ => m
  | .link _ _ false => 1
  | .link _ _ true => 2 * m - 1

omit [DecidableEq V] in
theorem sharedSlots_pos {m : ℕ} (hm : 0 < m) (c : GChan V) : 0 < sharedSlots m c := by
  rcases c with _ | ⟨_, _, _ | _⟩ <;> simp [sharedSlots] <;> omega

/-- **The `shared` scheme on every graph**: `m` connections per link used as one escape channel
and `2m - 1` adaptive channels, with `m` injection channels per node, over the detour network
with bounded returns. -/
theorem shared_slots_correct (G : GraphData V) (B : ℕ) (W : V → V → List (Option V)) {m : ℕ}
    (hm : 0 < m) :
    ((G.detourNet B W).widen (slots (sharedSlots m) (sharedSlots_pos hm))).Correct ∧
      ((G.detourNet B W).widen (slots (sharedSlots m) (sharedSlots_pos hm))).StarvationFree :=
  ⟨(G.wide_detour_correct B W _ _).1, (G.wide_detour_correct B W _ _).2.1⟩

end GraphData

end AsyncLean
