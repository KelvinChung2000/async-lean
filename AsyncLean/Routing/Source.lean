/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Fairness

/-!
# Throttled sources and tiered selections

Duato's theorem for selection functions (`Network.deadlockFreeWith_of_escape`) asks the selection
never to refuse a free escape hop.  Under heavy load it pays to hold packets back at their
sources (*source throttling*): a packet waits in its injection channel while the routers ahead
are congested, so that the packets already in the network drain first.  Such a selection refuses
free escape hops at the sources, and Duato's condition fails there.

The escape argument still goes through when the refusing channels are never the target of a hop
(injection channels) and a source lets its packet go once the rest of the network is empty:

* `Network.SourceSel R₁ src sel` — `sel` only offers permitted hops, never refuses a free escape
  hop at a channel outside `src`, and at a channel of `src` offers a free hop when every channel
  outside `src` is empty and an escape hop is free.
* `Network.deadlockFreeWith_of_source` — Duato's theorem for such selections, when no escape hop
  leads into `src`.
* `Network.StarvationFreeWith`, `Network.starvationFreeWith_of_source` — with a ranking function
  and finitely many legal pairs, every packet of every strongly fair run is delivered, the
  packets held in their injection channels included.  Strong fairness is demanding: in a finite
  deadlock- and livelock-free network it makes a run revisit every reachable configuration, the
  empty one included, so this says nothing about a network kept saturated (and nothing about a
  source's queue before its injection channel, which the model does not have).
* `Network.tieredSel` — a selection given by a list of tiers: a packet is offered the free
  permitted hops admitted by the first tier that admits one (for example: the preferred hop, then
  the escape hop, then the adaptive ones).  `tieredSel_conserving`: it offers a free hop whenever
  some tier admits a free permitted hop.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*} [DecidableEq C] (N : Network C P)

/-- **Duato's condition with throttled sources** (`src`): the selection only offers permitted
hops; outside `src` it never refuses a free escape hop; in `src` it may hold its packet back,
except when every channel outside `src` is empty. -/
structure SourceSel (R₁ : C → P → List (C × P)) (src : C → Prop) (sel : Selection C P) :
    Prop where
  sub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p
  conserving : ∀ f c p, ¬ src c → f c = some p → (∃ q ∈ R₁ c p, f q.1 = none) →
    ∃ q ∈ sel f c p, f q.1 = none
  source : ∀ f c p, src c → f c = some p → (∀ c', ¬ src c' → f c' = none) →
    (∃ q ∈ R₁ c p, f q.1 = none) → ∃ q ∈ sel f c p, f q.1 = none

omit [DecidableEq C] in
/-- A selection that never refuses a free escape hop throttles no source. -/
theorem EscapeSel.sourceSel {R₁ : C → P → List (C × P)} {sel : Selection C P}
    (h : N.EscapeSel R₁ sel) (src : C → Prop) : N.SourceSel R₁ src sel :=
  ⟨h.sub, fun f c p _ => h.conserving f c p, fun f c p _ hp _ => h.conserving f c p hp⟩

/-- Following the escape hops from a packet outside the sources (or from any packet, when the
channels outside the sources are empty) leads to a packet that can move. -/
theorem movable_of_source {legal : C → P → Prop} {R₁ : C → P → List (C × P)} {src : C → Prop}
    {sel : Selection C P} (hsel : N.SourceSel R₁ src sel)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    {f : Config C P} (hf : Legal legal f) :
    ∀ c, (¬ src c ∨ ∀ c', ¬ src c' → f c' = none) → ∀ p, f c = some p → N.Movable sel f := by
  intro c
  refine hwf.induction (C := fun c => (¬ src c ∨ ∀ c', ¬ src c' → f c' = none) →
    ∀ p, f c = some p → N.Movable sel f) c ?_
  intro c ih hc p hp
  have hl := hf c p hp
  cases harr : N.arrived c p with
  | true => exact ⟨.eject c, _, rfl, StepWith.eject hp harr⟩
  | false =>
    obtain ⟨⟨c', p'⟩, hq⟩ := List.exists_mem_of_ne_nil _ (hconn c p hl harr)
    cases hc' : f c' with
    | none =>
      have hfree : ∃ q ∈ R₁ c p, f q.1 = none := ⟨(c', p'), hq, hc'⟩
      have hoff : ∃ q ∈ sel f c p, f q.1 = none := by
        by_cases hs : src c
        · exact hsel.source f c p hs hp (hc.resolve_left (not_not.2 hs)) hfree
        · exact hsel.conserving f c p hs hp hfree
      obtain ⟨⟨c'', p''⟩, hq', hfree'⟩ := hoff
      exact ⟨.hop c c'' p'', _, rfl, StepWith.hop hp harr hq' hfree'⟩
    | some p'' => exact ih c' ⟨p, p', hl, harr, hq⟩ (Or.inl (hR₁ c p _ hl harr hq)) p'' hc'

/-- **Duato's theorem with throttled sources**: if the escape subfunction `R₁` is connected, its
dependency graph is well-founded and no escape hop leads into a source, the network is deadlock
free under every selection satisfying `SourceSel`. -/
theorem deadlockFreeWith_of_source {legal : C → P → Prop} (hcl : N.Closed legal)
    (R₁ : C → P → List (C × P)) {src : C → Prop}
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    {sel : Selection C P} (hsel : N.SourceSel R₁ src sel) : N.DeadlockFreeWith sel := by
  intro f hf hne
  have hl := N.legal_of_reachable_sub hcl hsel.sub hf
  by_cases h : ∃ c p, ¬ src c ∧ f c = some p
  · obtain ⟨c, p, hs, hp⟩ := h
    exact N.movable_of_source hsel hconn hwf hR₁ hl c (Or.inl hs) p hp
  · obtain ⟨c, p, hp⟩ := exists_of_ne_empty hne
    refine N.movable_of_source hsel hconn hwf hR₁ hl c (Or.inr fun c' hc' => ?_) p hp
    cases h' : f c' with
    | none => rfl
    | some p' => exact absurd ⟨c', p', hc', h'⟩ h

/-- **Starvation freedom under the selection `sel`**: along every strongly fair run, every packet
in the network is eventually delivered. -/
def StarvationFreeWith (sel : Selection C P) : Prop :=
  ∀ r : (N.ltsWith sel).Run empty, r.StronglyFair → ∀ n c, r.st n c ≠ none → N.Delivered r n c

/-- **No packet starves under a throttling selection**: with finitely many legal pairs, Duato's
condition with throttled sources and a ranking function that decreases on every hop, every
packet of every strongly fair run is delivered — a packet held back in its injection channel
too (see the module docstring for how much strong fairness asks). -/
theorem starvationFreeWith_of_source {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) (R₁ : C → P → List (C × P)) {src : C → Prop}
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {sel : Selection C P} (hsel : N.SourceSel R₁ src sel) : N.StarvationFreeWith sel := by
  intro r hfair n c hc
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hc
  have hchan : {c | ∃ p, legal c p}.Finite :=
    (hfin.image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩
  exact N.delivered_of_ranking hcl rk hrk hsel.sub
    (N.deadlockFreeWith_of_source hcl R₁ hconn hwf hR₁ hsel)
    (N.livelockFreeWith_of_ranking hcl hchan rk hrk hsel.sub)
    (N.reachable_finite hcl hfin hsel.sub) r hfair n c p hp

/-! ### Tiered selections -/

/-- A **tiered selection**: the packet is offered the free permitted hops admitted by the first
tier that admits one of them (and nothing, if no tier does). -/
def tieredSel (tiers : List (Config C P → C → P → C × P → Bool)) : Selection C P :=
  fun f c p => ((tiers.map fun t => (N.route c p).filter fun q => (f q.1).isNone && t f c p q).find?
    (fun l => !l.isEmpty)).getD []

omit [DecidableEq C] in
theorem mem_tieredSel {tiers : List (Config C P → C → P → C × P → Bool)} {f : Config C P}
    {c : C} {p : P} {q : C × P} (h : q ∈ N.tieredSel tiers f c p) :
    q ∈ N.route c p ∧ f q.1 = none := by
  simp only [tieredSel] at h
  cases hl : (tiers.map fun t => (N.route c p).filter fun q => (f q.1).isNone && t f c p q).find?
      (fun l => !l.isEmpty) with
  | none => rw [hl] at h; simp at h
  | some l =>
    rw [hl, Option.getD_some] at h
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hl)
    obtain ⟨hq, hf⟩ := List.mem_filter.1 h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hf
    exact ⟨hq, hf.1⟩

omit [DecidableEq C] in
/-- A tiered selection offers a free hop whenever some tier admits a free permitted hop. -/
theorem tieredSel_conserving {tiers : List (Config C P → C → P → C × P → Bool)}
    {t : Config C P → C → P → C × P → Bool} (ht : t ∈ tiers) {f : Config C P} {c : C} {p : P}
    {q : C × P} (hq : q ∈ N.route c p) (hfree : f q.1 = none) (htq : t f c p q = true) :
    ∃ q ∈ N.tieredSel tiers f c p, f q.1 = none := by
  have hsome : ((tiers.map fun t => (N.route c p).filter fun q => (f q.1).isNone && t f c p q).find?
      (fun l => !l.isEmpty)).isSome := by
    rw [List.find?_isSome]
    refine ⟨_, List.mem_map.2 ⟨t, ht, rfl⟩, ?_⟩
    have : q ∈ (N.route c p).filter fun q => (f q.1).isNone && t f c p q :=
      List.mem_filter.2 ⟨hq, by simp [hfree, htq]⟩
    cases hl : (N.route c p).filter fun q => (f q.1).isNone && t f c p q with
    | nil => rw [hl] at this; simp at this
    | cons _ _ => rfl
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hsome
  have hne := List.find?_some hl
  obtain ⟨q', hq'⟩ : ∃ q', q' ∈ l := by
    cases l with
    | nil => simp at hne
    | cons a _ => exact ⟨a, List.mem_cons_self⟩
  have hmem : q' ∈ N.tieredSel tiers f c p := by
    simp only [tieredSel]; rw [hl, Option.getD_some]; exact hq'
  exact ⟨q', hmem, (N.mem_tieredSel hmem).2⟩

end Network

end AsyncLean
