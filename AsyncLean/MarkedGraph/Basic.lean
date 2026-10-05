/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.Basic
import Mathlib.Data.Fintype.Card

/-!
# Marked graphs and Commoner's liveness theorem

A *marked graph* (decision-free Petri net, "event graph") is a Petri net in which every place
has exactly one producing and one consuming transition, with unit arc weights.  Marked
graphs model choice-free asynchronous control: Muller pipelines, micropipelines, ring
oscillators, handshake controllers, self-timed FIFOs and data-flow pipelines.

The fundamental theorem of their behaviour (Commoner, Holt, Even & Pnueli, 1971) is

> **A marked graph is live iff every directed circuit carries at least one token.**

We prove it in full (`MarkedGraph.live_iff_circuitsMarked`), together with:

* every reachable marking preserves "all circuits marked" (`CircuitsMarked.fire`);
* a token-free circuit is token-free forever, so its transitions are dead
  (`not_enabled_of_unmarked_circuit`);
* liveness ⇒ deadlock freedom (`deadlockFree_of_circuitsMarked`);
* the token count of every circuit is invariant (`tokens_fire`), giving place bounds and
  safeness (`le_tokens_of_mem`, `safe_of_circuit_cover`);
* a decidable certificate for "all circuits marked": a ranking of the transitions that
  strictly increases along every empty place (`circuitsMarked_of_rank`), which exists
  exactly when all circuits are marked (`circuitsMarked_iff_exists_rank`).

"Every circuit carries a token" is expressed graph-theoretically as `CircuitsMarked M`:
the relation `EmptyEdge M t t'` ("some empty place leads from `t` to `t'`") has no cycle.
-/

namespace AsyncLean

/-- A marked graph: every place `p` has a unique producer `src p` and consumer `dst p`. -/
structure MarkedGraph (P T : Type*) where
  /-- The transition producing tokens into `p`. -/
  src : P → T
  /-- The transition consuming tokens from `p`. -/
  dst : P → T

namespace MarkedGraph

variable {P T : Type*} [DecidableEq T] (G : MarkedGraph P T)

/-- The Petri net of a marked graph. -/
def toNet : Net P T where
  pre t p := if G.dst p = t then 1 else 0
  post t p := if G.src p = t then 1 else 0

/-- `EmptyEdge M t t'` : there is an empty place from `t` to `t'`, so `t` must fire before
`t'` can. -/
def EmptyEdge (M : Marking P) (t t' : T) : Prop := ∃ p, M p = 0 ∧ G.src p = t ∧ G.dst p = t'

/-- Every directed circuit of the marked graph carries a token in `M`, i.e. the graph of
empty places is acyclic. -/
def CircuitsMarked (M : Marking P) : Prop := ∀ t, ¬ Relation.TransGen (G.EmptyEdge M) t t

variable {G}

theorem enabled_iff {M : Marking P} {t : T} :
    G.toNet.Enabled M t ↔ ∀ p, G.dst p = t → 0 < M p := by
  unfold Net.Enabled toNet
  constructor
  · intro h p hp
    have := h p
    simp only [hp, ↓reduceIte] at this
    omega
  · intro h p
    dsimp only
    split_ifs with hp
    · exact h p hp
    · exact Nat.zero_le _

theorem fire_apply (M : Marking P) (t : T) (p : P) :
    G.toNet.fire M t p = M p - (if G.dst p = t then 1 else 0) + (if G.src p = t then 1 else 0) :=
  rfl

theorem fire_pos_of_src {M : Marking P} {u : T} {p : P} (h : G.src p = u) :
    0 < G.toNet.fire M u p := by
  simp only [fire_apply, h, ↓reduceIte]; omega

theorem fire_eq_of_ne {M : Marking P} {u : T} {p : P} (h₁ : G.dst p ≠ u) (h₂ : G.src p ≠ u) :
    G.toNet.fire M u p = M p := by
  simp only [fire_apply, h₁, h₂, ↓reduceIte]; omega

theorem not_enabled_of_emptyEdge {M : Marking P} {x y : T} (h : G.EmptyEdge M x y) :
    ¬ G.toNet.Enabled M y := by
  obtain ⟨p, hp, -, hd⟩ := h
  intro hen
  have := enabled_iff.1 hen p hd
  omega

/-! ### Preservation of "all circuits marked" -/

/-- After firing `u`, no empty place leaves `u`. -/
theorem EmptyEdge.src_ne_of_fire {M : Marking P} {u x y : T}
    (h : G.EmptyEdge (G.toNet.fire M u) x y) : x ≠ u := by
  rintro rfl
  obtain ⟨p, hp, hs, -⟩ := h
  have := fire_pos_of_src (M := M) hs
  omega

theorem EmptyEdge.of_fire {M : Marking P} {u x y : T} (h : G.EmptyEdge (G.toNet.fire M u) x y)
    (hy : y ≠ u) : G.EmptyEdge M x y := by
  have hx := h.src_ne_of_fire
  obtain ⟨p, hp, hs, hd⟩ := h
  refine ⟨p, ?_, hs, hd⟩
  rw [fire_eq_of_ne (hd ▸ hy) (hs ▸ hx)] at hp
  exact hp

theorem transGen_of_fire {M : Marking P} {u a b : T}
    (h : Relation.TransGen (G.EmptyEdge (G.toNet.fire M u)) a b) (hb : b ≠ u) :
    Relation.TransGen (G.EmptyEdge M) a b := by
  induction h with
  | single hab => exact Relation.TransGen.single (hab.of_fire hb)
  | tail _ hcb ih => exact Relation.TransGen.tail (ih hcb.src_ne_of_fire) (hcb.of_fire hb)

/-- Firing any transition preserves "all circuits marked". -/
theorem CircuitsMarked.fire {M : Marking P} (h : G.CircuitsMarked M) (u : T) :
    G.CircuitsMarked (G.toNet.fire M u) := by
  intro t ht
  obtain ⟨c, htc, -⟩ := Relation.TransGen.head'_iff.1 ht
  exact h t (transGen_of_fire ht htc.src_ne_of_fire)

theorem CircuitsMarked.reachable {M₀ M : Marking P} (h : G.CircuitsMarked M₀)
    (hr : G.toNet.lts.Reachable M₀ M) : G.CircuitsMarked M :=
  hr.invariant h fun _ _ _ hM ⟨_, he⟩ => he ▸ hM.fire _

omit [DecidableEq T] in
/-- With all circuits marked, the "must fire before" relation is well-founded. -/
theorem CircuitsMarked.wellFounded [Finite T] {M : Marking P} (h : G.CircuitsMarked M) :
    WellFounded (G.EmptyEdge M) := by
  have : Std.Irrefl (Relation.TransGen (G.EmptyEdge M)) := ⟨h⟩
  exact Subrelation.wf (fun hxy => Relation.TransGen.single hxy)
    (Finite.wellFounded_of_trans_of_irrefl _)

/-! ### Liveness -/

theorem reflTransGen_of_fire {M : Marking P} {u x t : T}
    (h : Relation.ReflTransGen (G.EmptyEdge (G.toNet.fire M u)) x t) (ht : t ≠ u) :
    Relation.ReflTransGen (G.EmptyEdge M) x t ∧ x ≠ u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨Relation.ReflTransGen.refl, ht⟩
  | head hxc _ ih =>
    obtain ⟨h1, hc⟩ := ih
    exact ⟨Relation.ReflTransGen.head (hxc.of_fire hc) h1, hxc.src_ne_of_fire⟩

/-- **Key lemma.**  If all circuits are marked, every transition can be enabled by firing
some sequence of transitions.  The proof repeatedly fires a minimal transition among those
that must fire before `t`; the set of such transitions strictly shrinks. -/
theorem exists_enabled_of_circuitsMarked [Fintype T] {M : Marking P}
    (h : G.CircuitsMarked M) (t : T) :
    ∃ M', G.toNet.lts.Reachable M M' ∧ G.toNet.Enabled M' t := by
  classical
  -- the transitions that must fire before `t`
  let B : Marking P → Finset T := fun M =>
    Finset.univ.filter fun x => Relation.ReflTransGen (G.EmptyEdge M) x t
  suffices key : ∀ n, ∀ M, G.CircuitsMarked M → (B M).card = n →
      ∃ M', G.toNet.lts.Reachable M M' ∧ G.toNet.Enabled M' t from key _ M h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hM hn
    by_cases hen : G.toNet.Enabled M t
    · exact ⟨M, LTS.Reachable.refl M, hen⟩
    obtain ⟨u, hu, hmin⟩ := hM.wellFounded.has_min
      {x | Relation.ReflTransGen (G.EmptyEdge M) x t} ⟨t, Relation.ReflTransGen.refl⟩
    have huen : G.toNet.Enabled M u := by
      refine enabled_iff.2 fun p hp => Nat.pos_of_ne_zero fun h0 => ?_
      exact hmin (G.src p) (Relation.ReflTransGen.head ⟨p, h0, rfl, hp⟩ hu) ⟨p, h0, rfl, hp⟩
    have hut : u ≠ t := fun h => hen (h ▸ huen)
    have hsub : B (G.toNet.fire M u) ⊂ B M := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨u, by simpa [B] using hu, ?_⟩
        intro hu'
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
        exact (reflTransGen_of_fire hu' (Ne.symm hut)).2 rfl
      · intro x hx
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact (reflTransGen_of_fire hx (Ne.symm hut)).1
    obtain ⟨M'', h1, h2⟩ :=
      ih _ (hn ▸ Finset.card_lt_card hsub) (G.toNet.fire M u) (hM.fire u) rfl
    exact ⟨M'', LTS.Reachable.head ⟨u, huen, rfl⟩ h1, h2⟩

/-- **Commoner's theorem, sufficiency.**  If every circuit carries a token initially, the
marked graph is live: every transition can fire again from every reachable marking. -/
theorem live_of_circuitsMarked [Fintype T] {M₀ : Marking P} (h : G.CircuitsMarked M₀) :
    G.toNet.lts.Live M₀ := by
  intro t M hr
  obtain ⟨M', h1, h2⟩ := exists_enabled_of_circuitsMarked (h.reachable hr) t
  exact ⟨M', h1, Net.lts_enabled_iff.2 h2⟩

/-- A marked graph whose circuits are all marked is deadlock free. -/
theorem deadlockFree_of_circuitsMarked [Fintype T] [Nonempty T] {M₀ : Marking P}
    (h : G.CircuitsMarked M₀) : G.toNet.lts.DeadlockFree M₀ :=
  (live_of_circuitsMarked h).deadlockFree

/-! ### Token-free circuits stay token-free -/

theorem EmptyEdge.dst_ne_of_enabled {M : Marking P} {u x y : T} (h : G.EmptyEdge M x y)
    (hen : G.toNet.Enabled M u) : y ≠ u :=
  fun hyu => not_enabled_of_emptyEdge h (hyu ▸ hen)

theorem EmptyEdge.fire_of {M : Marking P} {u x y : T} (h : G.EmptyEdge M x y)
    (hen : G.toNet.Enabled M u) (hx : x ≠ u) : G.EmptyEdge (G.toNet.fire M u) x y := by
  have hy : y ≠ u := fun hyu => not_enabled_of_emptyEdge h (hyu ▸ hen)
  obtain ⟨p, hp, hs, hd⟩ := h
  exact ⟨p, by rw [fire_eq_of_ne (hd ▸ hy) (hs ▸ hx)]; exact hp, hs, hd⟩

theorem transGen_fire_of {M : Marking P} {u a b : T} (h : Relation.TransGen (G.EmptyEdge M) a b)
    (hen : G.toNet.Enabled M u) (ha : a ≠ u) :
    Relation.TransGen (G.EmptyEdge (G.toNet.fire M u)) a b := by
  induction h using Relation.TransGen.head_induction_on with
  | single hab => exact Relation.TransGen.single (hab.fire_of hen ha)
  | head hac _ ih =>
    exact Relation.TransGen.head (hac.fire_of hen ha) (ih (hac.dst_ne_of_enabled hen))

/-- A transition lying on a token-free circuit stays on a token-free circuit forever. -/
theorem transGen_self_reachable {M₀ M : Marking P} {t : T}
    (hc : Relation.TransGen (G.EmptyEdge M₀) t t) (hr : G.toNet.lts.Reachable M₀ M) :
    Relation.TransGen (G.EmptyEdge M) t t := by
  refine hr.invariant (I := fun M => Relation.TransGen (G.EmptyEdge M) t t) hc ?_
  rintro M u M' hM ⟨hen, rfl⟩
  obtain ⟨b, -, hbt⟩ := Relation.TransGen.tail'_iff.1 hM
  have htu : t ≠ u := fun h => not_enabled_of_emptyEdge hbt (h ▸ hen)
  exact transGen_fire_of hM hen htu

/-- A transition on a token-free circuit can never fire. -/
theorem not_enabled_of_unmarked_circuit {M₀ M : Marking P} {t : T}
    (hc : Relation.TransGen (G.EmptyEdge M₀) t t) (hr : G.toNet.lts.Reachable M₀ M) :
    ¬ G.toNet.Enabled M t := by
  obtain ⟨b, -, hbt⟩ := Relation.TransGen.tail'_iff.1 (transGen_self_reachable hc hr)
  exact not_enabled_of_emptyEdge hbt

/-- **Commoner's theorem, necessity.**  A transition on a token-free circuit is not live. -/
theorem not_liveLabel_of_unmarked_circuit {M₀ : Marking P} {t : T}
    (hc : Relation.TransGen (G.EmptyEdge M₀) t t) : ¬ G.toNet.lts.LiveLabel M₀ t :=
  LTS.not_liveLabel_of_dead (LTS.Reachable.refl M₀) fun _ hr hen =>
    not_enabled_of_unmarked_circuit hc hr (Net.lts_enabled_iff.1 hen)

/-- **Commoner's theorem.**  A (finite) marked graph is live if and only if every directed
circuit carries a token. -/
theorem live_iff_circuitsMarked [Fintype T] {M₀ : Marking P} :
    G.toNet.lts.Live M₀ ↔ G.CircuitsMarked M₀ :=
  ⟨fun h t ht => not_liveLabel_of_unmarked_circuit ht (h t), live_of_circuitsMarked⟩

/-! ### Rank certificates: deciding "all circuits marked" -/

omit [DecidableEq T] in
/-- A ranking of transitions strictly increasing along every empty place certifies that all
circuits are marked. -/
theorem circuitsMarked_of_rank {M : Marking P} (r : T → ℕ)
    (hr : ∀ p, M p = 0 → r (G.src p) < r (G.dst p)) : G.CircuitsMarked M := by
  have key : ∀ a b, Relation.TransGen (G.EmptyEdge M) a b → r a < r b := by
    intro a b h
    induction h with
    | single hab => obtain ⟨p, hp, rfl, rfl⟩ := hab; exact hr p hp
    | tail _ hcb ih => obtain ⟨p, hp, rfl, rfl⟩ := hcb; exact ih.trans (hr p hp)
  exact fun t ht => lt_irrefl _ (key t t ht)

omit [DecidableEq T] in
/-- Conversely, if all circuits are marked such a ranking exists (count the transitions that
must fire before a given one). -/
theorem exists_rank_of_circuitsMarked [Fintype T] {M : Marking P} (h : G.CircuitsMarked M) :
    ∃ r : T → ℕ, ∀ p, M p = 0 → r (G.src p) < r (G.dst p) := by
  classical
  refine ⟨fun t => (Finset.univ.filter fun x => Relation.TransGen (G.EmptyEdge M) x t).card,
    fun p hp => Finset.card_lt_card ?_⟩
  have he : G.EmptyEdge M (G.src p) (G.dst p) := ⟨p, hp, rfl, rfl⟩
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨G.src p, by simpa using Relation.TransGen.single he, ?_⟩
    simpa using h (G.src p)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.tail he

omit [DecidableEq T] in
theorem circuitsMarked_iff_exists_rank [Fintype T] {M : Marking P} :
    G.CircuitsMarked M ↔ ∃ r : T → ℕ, ∀ p, M p = 0 → r (G.src p) < r (G.dst p) :=
  ⟨exists_rank_of_circuitsMarked, fun ⟨r, hr⟩ => circuitsMarked_of_rank r hr⟩

/-! ### Circuits as lists of places, token conservation and safeness -/

variable (G) in
/-- Consecutive places of the list are linked: the consumer of each is the producer of the
next. -/
def Linked : List P → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => G.dst p = G.src q ∧ Linked (q :: rest)

instance decLinked : ∀ ps : List P, Decidable (G.Linked ps)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | _ :: q :: rest =>
    haveI := decLinked (q :: rest)
    inferInstanceAs (Decidable (_ ∧ _))

variable (G) in
/-- `ps` lists the places of a directed circuit (closed walk) of the marked graph. -/
def IsCircuit : List P → Prop
  | [] => False
  | p :: rest => G.Linked (p :: rest) ∧ G.dst ((p :: rest).getLast (List.cons_ne_nil _ _)) = G.src p

instance : ∀ ps : List P, Decidable (G.IsCircuit ps)
  | [] => isFalse id
  | _ :: _ => inferInstanceAs (Decidable (_ ∧ _))

private theorem le_sum_of_mem' {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- Number of tokens on a list of places (with multiplicity). -/
def tokens (M : Marking P) (ps : List P) : ℕ := (ps.map M).sum

private theorem linked_fire_sum {M : Marking P} {u : T} (hen : G.toNet.Enabled M u) :
    ∀ (p : P) (rest : List P), G.Linked (p :: rest) →
      tokens (G.toNet.fire M u) (p :: rest) +
          (if G.dst ((p :: rest).getLast (List.cons_ne_nil _ _)) = u then 1 else 0) =
        tokens M (p :: rest) + (if G.src p = u then 1 else 0) := by
  have hpt : ∀ p, G.toNet.fire M u p + (if G.dst p = u then 1 else 0) =
      M p + (if G.src p = u then 1 else 0) := by
    intro p
    rw [fire_apply]
    by_cases hd : G.dst p = u
    · have := enabled_iff.1 hen p hd
      simp only [hd, ↓reduceIte]
      omega
    · simp only [hd, ↓reduceIte]
      omega
  intro p rest
  induction rest generalizing p with
  | nil =>
    intro _
    simp only [tokens, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.getLast_singleton]
    exact hpt p
  | cons q rest ih =>
    rintro ⟨hpq, hl⟩
    have ih' := ih q hl
    have hlast : (p :: q :: rest).getLast (List.cons_ne_nil _ _) =
        (q :: rest).getLast (List.cons_ne_nil _ _) := List.getLast_cons _
    simp only [tokens, List.map_cons, List.sum_cons] at ih' ⊢
    rw [hlast]
    have := hpt p
    rw [hpq] at this
    omega

/-- **Token conservation on circuits**: firing an enabled transition does not change the
number of tokens on any circuit. -/
theorem tokens_fire {M : Marking P} {u : T} (hen : G.toNet.Enabled M u) {ps : List P}
    (hc : G.IsCircuit ps) : tokens (G.toNet.fire M u) ps = tokens M ps := by
  match ps, hc with
  | p :: rest, ⟨hl, hlast⟩ =>
    have := linked_fire_sum hen p rest hl
    rw [hlast] at this
    omega

theorem tokens_reachable {M₀ M : Marking P} {ps : List P} (hc : G.IsCircuit ps)
    (hr : G.toNet.lts.Reachable M₀ M) : tokens M ps = tokens M₀ ps :=
  hr.invariant (I := fun M => tokens M ps = tokens M₀ ps) rfl
    fun _ _ _ hM ⟨hen, he⟩ => he ▸ (tokens_fire hen hc).trans hM

/-- **Place bound**: a place on a circuit never holds more tokens than the circuit held
initially. -/
theorem le_tokens_of_mem {M₀ M : Marking P} {ps : List P} (hc : G.IsCircuit ps) {p : P}
    (hp : p ∈ ps) (hr : G.toNet.lts.Reachable M₀ M) : M p ≤ tokens M₀ ps := by
  rw [← tokens_reachable hc hr]
  exact le_sum_of_mem' (List.mem_map_of_mem hp)

/-- **Safeness**: if every place lies on a circuit carrying at most one token, the marked
graph is 1-safe (no place ever holds two tokens) — the classical condition for a marked
graph to be implementable as a speed-independent circuit. -/
theorem safe_of_circuit_cover {M₀ : Marking P}
    (hcov : ∀ p, ∃ ps, G.IsCircuit ps ∧ p ∈ ps ∧ tokens M₀ ps ≤ 1) {M : Marking P}
    (hr : G.toNet.lts.Reachable M₀ M) (p : P) : M p ≤ 1 := by
  obtain ⟨ps, hc, hp, h1⟩ := hcov p
  exact (le_tokens_of_mem hc hp hr).trans h1

omit [DecidableEq T] in
private theorem transGen_of_linked {M : Marking P} :
    ∀ (p : P) (rest : List P), G.Linked (p :: rest) → (∀ q ∈ p :: rest, M q = 0) →
      Relation.TransGen (G.EmptyEdge M) (G.src p)
        (G.dst ((p :: rest).getLast (List.cons_ne_nil _ _))) := by
  intro p rest
  induction rest generalizing p with
  | nil => intro _ h0; exact Relation.TransGen.single ⟨p, h0 p (by simp), rfl, rfl⟩
  | cons q rest ih =>
    rintro ⟨hpq, hl⟩ h0
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    refine Relation.TransGen.head ⟨p, h0 p (by simp), rfl, hpq⟩ (ih q hl ?_)
    intro x hx; exact h0 x (List.mem_cons_of_mem _ hx)

omit [DecidableEq T] in
/-- A token-free circuit (given explicitly as a list of places) violates
`CircuitsMarked`. -/
theorem not_circuitsMarked_of_circuit {M : Marking P} {ps : List P} (hc : G.IsCircuit ps)
    (h0 : tokens M ps = 0) : ¬ G.CircuitsMarked M := by
  match ps, hc with
  | p :: rest, ⟨hl, hlast⟩ =>
    intro h
    have hz : ∀ q ∈ p :: rest, M q = 0 := by
      intro q hq
      have := le_sum_of_mem' (List.mem_map_of_mem (f := M) hq)
      unfold tokens at h0
      omega
    have := transGen_of_linked p rest hl hz
    rw [hlast] at this
    exact h _ this

/-- **Refuting liveness of a marked graph**: exhibit a token-free circuit. -/
theorem not_live_of_circuit [Fintype T] {M₀ : Marking P} {ps : List P} (hc : G.IsCircuit ps)
    (h0 : tokens M₀ ps = 0) : ¬ G.toNet.lts.Live M₀ :=
  fun h => not_circuitsMarked_of_circuit hc h0 (live_iff_circuitsMarked.1 h)

end MarkedGraph

end AsyncLean
