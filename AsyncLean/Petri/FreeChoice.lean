/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.SiphonTrap
import Mathlib.Data.Fintype.Card

/-!
# Free-choice nets: Commoner's liveness theorem

A Petri net is *free choice* when two transitions sharing an input place have the same input
places: conflicts are resolved freely, never influenced by the rest of the marking.  Most
asynchronous control circuits with arbitration-free choice (e.g. choice made by the
environment) are free choice.

**Commoner's theorem** (sufficiency): *in an ordinary free-choice net, if every non-empty
siphon contains an initially marked trap, the net is live*
(`Net.live_of_siphonTrap`).  Together with the decidability of the siphon–trap
property (`Net.SiphonTrapProperty`), this gives a purely structural liveness proof.  The
converse, and hence the full theorem `Net.live_iff_siphonTrap`, is in
`AsyncLean.Petri.FreeChoiceNecessity`.

Proof outline.  If the net were not live, choose a reachable marking `M` whose set of dead
transitions is maximal; every other transition is then live from `M`.  In a free-choice net
the input places of a dead transition never lose tokens.  Hence every dead transition has an
input place that is empty at `M` and fed only by dead transitions; these places form a
non-empty siphon that is empty at `M` — but it contains a trap marked initially, and marked
traps stay marked.
-/

namespace AsyncLean

namespace Net

open Classical

variable {P T : Type*} [Fintype P] [Fintype T] {N : Net P T}

variable (N) in
/-- Ordinary: all arc weights are at most one. -/
def Ordinary : Prop := ∀ t p, N.pre t p ≤ 1 ∧ N.post t p ≤ 1

variable (N) in
/-- (Extended) free choice: transitions sharing an input place have the same input places. -/
def FreeChoice : Prop :=
  ∀ t u p, 0 < N.pre t p → 0 < N.pre u p → ∀ q, (0 < N.pre t q ↔ 0 < N.pre u q)

variable (N) in
/-- `t` is dead at `M`: it is never enabled again. -/
def DeadAt (M : Marking P) (t : T) : Prop := ∀ M', N.lts.Reachable M M' → ¬ N.Enabled M' t

instance : Decidable N.Ordinary := by unfold Ordinary; infer_instance
instance : Decidable N.FreeChoice := by unfold FreeChoice; infer_instance

omit [Fintype P] [Fintype T] in
/-- In an ordinary net, a transition is enabled iff all its input places are marked. -/
theorem enabled_iff_of_ordinary (hord : N.Ordinary) {M : Marking P} {t : T} :
    N.Enabled M t ↔ ∀ q, 0 < N.pre t q → 0 < M q := by
  constructor
  · intro h q hq; exact lt_of_lt_of_le hq (h q)
  · intro h q
    by_cases hq : 0 < N.pre t q
    · have := (hord t q).1; have := h q hq; omega
    · omega

omit [Fintype P] [Fintype T] in
theorem DeadAt.reachable {M M' : Marking P} {t : T} (h : N.DeadAt M t)
    (hr : N.lts.Reachable M M') : N.DeadAt M' t :=
  fun M'' hr' => h M'' (hr.trans hr')

omit [Fintype P] [Fintype T] in
/-- In a free-choice net, an input place of a dead transition never loses a token. -/
theorem le_of_deadAt (hord : N.Ordinary) (hfc : N.FreeChoice) {M M' : Marking P} {t : T}
    (hdead : N.DeadAt M t) {p : P} (hp : 0 < N.pre t p) (hr : N.lts.Reachable M M') :
    M p ≤ M' p := by
  induction hr with
  | refl => exact le_rfl
  | tail hr' hst ih =>
    obtain ⟨v, hen, rfl⟩ := hst
    rw [fire_apply]
    by_cases hv : 0 < N.pre v p
    · exfalso
      apply hdead _ hr'
      rw [enabled_iff_of_ordinary hord]
      intro q hq
      exact (enabled_iff_of_ordinary hord).1 hen q ((hfc t v p hp hv q).1 hq)
    · omega

variable (N) in
/-- The transitions dead at `M`. -/
noncomputable def deadSet (M : Marking P) : Finset T := Finset.univ.filter (N.DeadAt M)

omit [Fintype P] in
theorem deadSet_mono {M M' : Marking P} (hr : N.lts.Reachable M M') :
    N.deadSet M ⊆ N.deadSet M' := by
  intro t ht
  simp only [deadSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  exact ht.reachable hr

omit [Fintype P] in
/-- Some marking reachable from `M` has a maximal set of dead transitions. -/
theorem exists_deadSet_stable (M : Marking P) :
    ∃ M₂, N.lts.Reachable M M₂ ∧ ∀ M', N.lts.Reachable M₂ M' → N.deadSet M' = N.deadSet M₂ := by
  suffices key : ∀ n, ∀ M, Fintype.card T - (N.deadSet M).card = n →
      ∃ M₂, N.lts.Reachable M M₂ ∧ ∀ M', N.lts.Reachable M₂ M' → N.deadSet M' = N.deadSet M₂ from
    key _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hn
    by_cases h : ∀ M', N.lts.Reachable M M' → N.deadSet M' = N.deadSet M
    · exact ⟨M, LTS.Reachable.refl _, h⟩
    · push Not at h
      obtain ⟨M', hr, hne⟩ := h
      have hss : N.deadSet M ⊂ N.deadSet M' :=
        Finset.ssubset_iff_subset_ne.2 ⟨deadSet_mono hr, fun h => hne h.symm⟩
      have hlt := Finset.card_lt_card hss
      have hle := Finset.card_le_univ (N.deadSet M')
      obtain ⟨M₂, hr₂, hst⟩ := ih _ (by omega) M' rfl
      exact ⟨M₂, hr.trans hr₂, hst⟩

/-- At a marking with a maximal set of dead transitions, every dead transition has an empty
input place fed only by dead transitions. -/
theorem exists_empty_input (hord : N.Ordinary) (hfc : N.FreeChoice) {M₂ : Marking P}
    (hstable : ∀ M', N.lts.Reachable M₂ M' → N.deadSet M' = N.deadSet M₂) {t : T}
    (ht : t ∈ N.deadSet M₂) :
    ∃ p, 0 < N.pre t p ∧ M₂ p = 0 ∧ ∀ v, 0 < N.post v p → v ∈ N.deadSet M₂ := by
  by_contra hcon
  push Not at hcon
  have htd : N.DeadAt M₂ t := by
    simpa [deadSet] using ht
  -- every finite set of input places of `t` can be marked simultaneously
  have key : ∀ K : Finset P, (∀ p ∈ K, 0 < N.pre t p) →
      ∃ M, N.lts.Reachable M₂ M ∧ ∀ p ∈ K, 0 < M p := by
    intro K
    induction K using Finset.induction_on with
    | empty => exact fun _ => ⟨M₂, LTS.Reachable.refl _, by simp⟩
    | insert p K hpK ih =>
      intro hK
      obtain ⟨M, hr, hM⟩ := ih fun q hq => hK q (Finset.mem_insert_of_mem hq)
      have hp : 0 < N.pre t p := hK p (Finset.mem_insert_self p K)
      have htM : N.DeadAt M t := htd.reachable hr
      by_cases h0 : M₂ p = 0
      · obtain ⟨v, hv, hvd⟩ := hcon p hp h0
        have hvd' : v ∉ N.deadSet M := by rw [hstable M hr]; exact hvd
        simp only [deadSet, Finset.mem_filter, Finset.mem_univ, true_and, DeadAt,
          not_forall, not_not] at hvd'
        obtain ⟨M', hr', hen⟩ := hvd'
        refine ⟨N.fire M' v, hr.trans (hr'.tail ⟨v, hen, rfl⟩), ?_⟩
        intro q hq
        rcases Finset.mem_insert.1 hq with rfl | hq
        · rw [fire_apply]; omega
        · have h1 := le_of_deadAt hord hfc htM (hK q (Finset.mem_insert_of_mem hq))
            (hr'.tail ⟨v, hen, rfl⟩)
          have := hM q hq
          omega
      · refine ⟨M, hr, fun q hq => ?_⟩
        rcases Finset.mem_insert.1 hq with rfl | hq
        · have := le_of_deadAt hord hfc htd hp hr; omega
        · exact hM q hq
  obtain ⟨M, hr, hM⟩ := key (Finset.univ.filter fun p => 0 < N.pre t p) (by simp)
  exact htd M hr ((enabled_iff_of_ordinary hord).2 fun q hq => hM q (by simp [hq]))

/-- **Commoner's theorem for free-choice nets (sufficiency).**  An ordinary free-choice net
in which every non-empty siphon contains an initially marked trap is live. -/
theorem live_of_siphonTrap (hord : N.Ordinary) (hfc : N.FreeChoice) {M₀ : Marking P}
    (h : N.SiphonTrapProperty M₀) : N.lts.Live M₀ := by
  intro t M₁ hr₁
  by_contra hnot
  push Not at hnot
  have hdead₁ : N.DeadAt M₁ t := fun M' hr' hen => hnot M' hr' (lts_enabled_iff.2 hen)
  obtain ⟨M₂, hr₂, hstable⟩ := exists_deadSet_stable (N := N) M₁
  have ht₂ : t ∈ N.deadSet M₂ := by
    simpa [deadSet] using hdead₁.reachable hr₂
  -- the siphon of empty places fed only by dead transitions
  let S : Finset P := Finset.univ.filter fun p =>
    M₂ p = 0 ∧ ∀ v, 0 < N.post v p → v ∈ N.deadSet M₂
  have hS : N.IsSiphon S := by
    rintro v ⟨p, hp, hpost⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨q, hq, hq0, hqd⟩ := exists_empty_input hord hfc hstable (hp.2 v hpost)
    exact ⟨q, Finset.mem_filter.2 ⟨Finset.mem_univ _, hq0, hqd⟩, hq⟩
  obtain ⟨p, hp, hp0, hpd⟩ := exists_empty_input hord hfc hstable ht₂
  have hne : S.Nonempty := ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp0, hpd⟩⟩
  obtain ⟨Q, hQS, hQ, hm⟩ := h S hne hS
  rw [Finset.mem_powerset] at hQS
  obtain ⟨q, hq, hpos⟩ := hQ.marked_reachable hm (hr₁.trans hr₂)
  have := hQS hq
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at this
  omega

/-- Liveness implies deadlock freedom: the same hypotheses give deadlock freedom. -/
theorem deadlockFree_of_siphonTrap_fc [Nonempty T] (hord : N.Ordinary) (hfc : N.FreeChoice)
    {M₀ : Marking P} (h : N.SiphonTrapProperty M₀) : N.lts.DeadlockFree M₀ :=
  (live_of_siphonTrap hord hfc h).deadlockFree

end Net

end AsyncLean
