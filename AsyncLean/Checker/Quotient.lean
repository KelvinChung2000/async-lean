/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Invariant
import AsyncLean.LTS.Compose
import Mathlib.Tactic.Set

/-!
# Certified minimisation of components

To verify a composition compositionally, a component `E` is replaced by a small quotient `Q`
(an explicit LTS on class numbers), related to `E` by a divergence-preserving weak
bisimulation (`AsyncLean.LTS.Compose`).  The quotient and the bisimulation are computed by
untrusted code (`mkQuot`: branching-bisimulation signature refinement) and checked by the
kernel (`checkQuot`).

The certificate assigns to each reachable state `s` of `E`

* its class `c`,
* a rank `r`, decreasing along internal steps that stay inside the class (so classes contain
  no internal cycles), and
* for each outgoing edge `(l, c')` of class `c` in `Q`, a distance that decreases along
  internal steps inside the class until a state is reached that takes the edge directly.

`divBisim_of_checkQuot` proves that "reachable and in class `c`" is a divergence-preserving
weak bisimulation between `E` and `Q`.
-/

namespace AsyncLean

namespace ExplicitLTS

variable {S L : Type*} (E : ExplicitLTS S L)

/-- The explicit LTS on class numbers defined by a quotient table. -/
def quotLTS (q : BTree (ℕ × List (L × ℕ))) : ExplicitLTS ℕ L :=
  ⟨fun c => (q.lookup compare c).getD []⟩

/-- Data of a quotient certificate: class, rank, distances to the class exits. -/
abbrev QData := ℕ × ℕ × List ℕ

section

variable [DecidableEq S] [DecidableEq L] (cmp : S → S → Ordering)

/-- The quotient checks at one state. -/
def quotNode (internal : L → Bool) (q : BTree (ℕ × List (L × ℕ))) (s : S)
    (es : List (L × S)) (look : S → Option QData) : Bool :=
  match look s with
  | none => false
  | some (c, r, ds) =>
    let qs := (quotLTS q).succ c
    (es.all fun e => match look e.2 with
      | none => false
      | some (c', r', _) =>
        if internal e.1 && decide (c' = c) then decide (r' < r) else decide ((e.1, c') ∈ qs)) &&
    ((qs.zip (List.range qs.length)).all fun qk =>
      !(internal qk.1.1 && decide (qk.1.2 = c)) &&
      es.any fun e => match look e.2 with
        | some (c₂, _, ds₂) =>
          (decide (e.1 = qk.1.1) && decide (c₂ = qk.1.2)) ||
            (internal e.1 && decide (c₂ = c) && decide (ds₂.getD qk.2 0 < ds.getD qk.2 0))
        | none => false)

/-- Check a quotient certificate for `E` from `s₀` (trusted). -/
def checkQuot (internal : L → Bool) (q : BTree (ℕ × List (L × ℕ))) (s₀ : S)
    (c : InvCert S QData) : Bool :=
  E.checkInv cmp (fun s es look => quotNode internal q s es look) s₀ c

/-- The class of a state according to a certificate. -/
def InvCert.cls (c : InvCert S QData) (s : S) : Option ℕ := (c.look cmp s).map Prod.fst

variable {E} {cmp}

/-- **Soundness of quotient certificates.** -/
theorem divBisim_of_checkQuot {internal : L → Bool} {q : BTree (ℕ × List (L × ℕ))} {s₀ : S}
    {c : InvCert S QData} (h : E.checkQuot cmp internal q s₀ c = true) :
    LTS.DivBisim E.toLTS (quotLTS q).toLTS (fun l => internal l = true)
      (fun s k => E.toLTS.Reachable s₀ s ∧ c.cls cmp s = some k) := by
  have hnode := ExplicitLTS.of_checkInv h
  set look := c.look cmp with hlook
  -- unpack the node checks at a reachable state
  have spec : ∀ s, E.toLTS.Reachable s₀ s → ∀ k r ds, look s = some (k, r, ds) →
      (∀ l s', (l, s') ∈ E.succ s → ∃ k' r' ds', look s' = some (k', r', ds') ∧
        (internal l = true ∧ k' = k → r' < r) ∧
        (¬ (internal l = true ∧ k' = k) → (l, k') ∈ (quotLTS q).succ k)) ∧
      (∀ l k' i, ((l, k'), i) ∈ ((quotLTS q).succ k).zip
          (List.range ((quotLTS q).succ k).length) →
        ¬ (internal l = true ∧ k' = k) ∧
        ∃ l₂ s', (l₂, s') ∈ E.succ s ∧ ∃ k₂ r₂ ds₂, look s' = some (k₂, r₂, ds₂) ∧
          ((l₂ = l ∧ k₂ = k') ∨ (internal l₂ = true ∧ k₂ = k ∧ ds₂.getD i 0 < ds.getD i 0))) := by
    intro s hs k r ds hl
    have := hnode s hs
    simp only [quotNode, hl, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at this
    obtain ⟨h1, h2⟩ := this
    refine ⟨fun l s' hmem => ?_, fun l k' i hmem => ?_⟩
    · have := h1 (l, s') hmem
      split at this
      · cases this
      · rename_i k' r' ds' hl'
        refine ⟨k', r', ds', hl', fun hc => ?_, fun hc => ?_⟩
        · split_ifs at this with hcond
          · exact of_decide_eq_true this
          · exact absurd (by simpa using hc) hcond
        · split_ifs at this with hcond
          · exact absurd (by simpa using hcond) hc
          · exact of_decide_eq_true this
    · obtain ⟨hnot, e, he, hok⟩ := h2 _ hmem
      refine ⟨by simpa using hnot, e.1, e.2, he, ?_⟩
      split at hok
      · rename_i k₂ r₂ ds₂ hl₂
        refine ⟨k₂, r₂, ds₂, hl₂, ?_⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
        rcases hok with h | ⟨⟨h₁, h₂⟩, h₃⟩
        · exact Or.inl h
        · exact Or.inr ⟨h₁, h₂, h₃⟩
      · cases hok
  -- every reachable state has data
  have hdata : ∀ s, E.toLTS.Reachable s₀ s → ∃ d, look s = some d := by
    intro s hs
    have := hnode s hs
    simp only [quotNode] at this
    split at this
    · cases this
    · exact ⟨_, ‹_›⟩
  -- the exit-distance argument (backward transfer)
  have bwd_aux : ∀ (i : ℕ) (n : ℕ) s k r ds, E.toLTS.Reachable s₀ s → look s = some (k, r, ds) →
      ds.getD i 0 = n → ∀ l k', ((l, k'), i) ∈ ((quotLTS q).succ k).zip
        (List.range ((quotLTS q).succ k).length) →
      ∃ s', E.toLTS.WMatch (fun l => internal l = true) l s s' ∧ E.toLTS.Reachable s₀ s' ∧
        c.cls cmp s' = some k' := by
    intro i n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s k r ds hs hl hn l k' hmem
      obtain ⟨hnot, l₂, s', hst, k₂, r₂, ds₂, hl₂, hcase⟩ := (spec s hs k r ds hl).2 l k' i hmem
      have hs' : E.toLTS.Reachable s₀ s' := hs.tail ⟨l₂, hst⟩
      rcases hcase with ⟨rfl, rfl⟩ | ⟨hi, rfl, hlt⟩
      · refine ⟨s', ?_, hs', by simp [InvCert.cls, ← hlook, hl₂]⟩
        by_cases hil : internal l₂ = true
        · exact Or.inl ⟨hil, Relation.ReflTransGen.single ⟨l₂, hil, hst⟩⟩
        · exact Or.inr (LTS.WeakStep.of_step hst)
      · obtain ⟨s'', hm, hs'', hcls⟩ :=
          ih _ (hn ▸ hlt) s' k₂ r₂ ds₂ hs' hl₂ rfl l k' hmem
        refine ⟨s'', ?_, hs'', hcls⟩
        have hτ : E.toLTS.TauStar (fun l => internal l = true) s s' :=
          Relation.ReflTransGen.single ⟨l₂, hi, hst⟩
        rcases hm with ⟨hil, hp⟩ | hw
        · exact Or.inl ⟨hil, hτ.trans hp⟩
        · exact Or.inr (hw.tauStar_left hτ)
  have bwd : ∀ s k, E.toLTS.Reachable s₀ s → c.cls cmp s = some k → ∀ l k',
      (quotLTS q).toLTS.step k l k' →
      ∃ s', E.toLTS.WMatch (fun l => internal l = true) l s s' ∧ E.toLTS.Reachable s₀ s' ∧
        c.cls cmp s' = some k' := by
    intro s k hs hk l k' hq
    obtain ⟨⟨k₀, r, ds⟩, hl⟩ := hdata s hs
    have : k₀ = k := by simpa [InvCert.cls, ← hlook, hl] using hk
    subst this
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (show (l, k') ∈ (quotLTS q).succ k₀ from hq)
    have hmem : ((l, k'), i) ∈ ((quotLTS q).succ k₀).zip
        (List.range ((quotLTS q).succ k₀).length) := by
      have hi' : i < (((quotLTS q).succ k₀).zip
          (List.range ((quotLTS q).succ k₀).length)).length := by
        simp [List.length_zip, hi]
      have := List.getElem_mem hi'
      rwa [List.getElem_zip, List.getElem_range, hget] at this
    exact bwd_aux i _ s k₀ r ds hs hl rfl l k' hmem
  refine ⟨?_, ?_, ?_⟩
  · -- forward transfer
    rintro s k ⟨hs, hk⟩ l s' hst
    obtain ⟨⟨k₀, r, ds⟩, hl⟩ := hdata s hs
    have : k₀ = k := by simpa [InvCert.cls, ← hlook, hl] using hk
    subst this
    obtain ⟨k', r', ds', hl', hin, hout⟩ := (spec s hs k₀ r ds hl).1 l s' hst
    have hs' : E.toLTS.Reachable s₀ s' := hs.tail ⟨l, hst⟩
    have hcls : c.cls cmp s' = some k' := by simp [InvCert.cls, ← hlook, hl']
    by_cases hc : internal l = true ∧ k' = k₀
    · obtain ⟨hil, rfl⟩ := hc
      exact ⟨k', Or.inl ⟨hil, Relation.ReflTransGen.refl⟩, hs', hcls⟩
    · exact ⟨k', Or.inr (LTS.WeakStep.of_step (hout hc)), hs', hcls⟩
  · -- backward transfer
    rintro s k ⟨hs, hk⟩ l k' hq
    obtain ⟨s', hm, hs', hcls⟩ := bwd s k hs hk l k' hq
    exact ⟨s', hm, hs', hcls⟩
  · -- divergence
    rintro s k ⟨hs, hk⟩
    constructor
    · intro hacc
      have houter := hacc.transGen
      clear hacc
      induction houter generalizing k with
      | intro s _ ih =>
        refine Acc.intro k fun k' ⟨l, hil, hq⟩ => ?_
        obtain ⟨s', hm, hs', hcls⟩ := bwd s k hs hk l k' hq
        rcases Relation.reflTransGen_iff_eq_or_transGen.1
          (LTS.WMatch.tauStar (internal := fun l => internal l = true) hil hm) with heq | hp
        · -- staying put would make `k' = k`, an internal self-loop of the quotient
          exfalso
          obtain ⟨⟨k₀, r, ds⟩, hl⟩ := hdata s hs
          have hk₀ : k₀ = k := by simpa [InvCert.cls, ← hlook, hl] using hk
          subst hk₀
          rw [heq] at hcls
          have hkk : k' = k₀ := by
            rw [hk] at hcls; exact (Option.some.inj hcls).symm
          obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (show (l, k') ∈ (quotLTS q).succ k₀ from hq)
          have hmem : ((l, k'), i) ∈ ((quotLTS q).succ k₀).zip
              (List.range ((quotLTS q).succ k₀).length) := by
            have hi' : i < (((quotLTS q).succ k₀).zip
                (List.range ((quotLTS q).succ k₀).length)).length := by
              simp [List.length_zip, hi]
            have := List.getElem_mem hi'
            rwa [List.getElem_zip, List.getElem_range, hget] at this
          exact ((spec s hs k₀ r ds hl).2 l k' i hmem).1 ⟨hil, hkk⟩
        · exact ih s' (Relation.transGen_swap.2 hp) k' hs' hcls
    · intro hacc
      induction hacc generalizing s with
      | intro k _ ihO =>
        obtain ⟨⟨k₀, r, ds⟩, hl⟩ := hdata s hs
        have hk₀ : k₀ = k := by simpa [InvCert.cls, ← hlook, hl] using hk
        subst hk₀
        -- inner induction on the rank
        suffices key : ∀ n s, E.toLTS.Reachable s₀ s → ∀ r ds, look s = some (k₀, r, ds) →
            r = n → Acc (E.toLTS.IRel fun l => internal l = true) s from key r s hs r ds hl rfl
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ihI =>
          intro s hs r ds hl hrn
          refine Acc.intro s fun s' ⟨l, hil, hst⟩ => ?_
          obtain ⟨k', r', ds', hl', hin, hout⟩ := (spec s hs k₀ r ds hl).1 l s' hst
          have hs' : E.toLTS.Reachable s₀ s' := hs.tail ⟨l, hst⟩
          by_cases hkk : k' = k₀
          · subst hkk
            exact ihI r' (hrn ▸ hin ⟨hil, rfl⟩) s' hs' r' ds' hl' rfl
          · exact ihO k' ⟨l, hil, hout (fun h => hkk h.2)⟩ s' hs'
              (by simp [InvCert.cls, ← hlook, hl'])

end

/-! ### Explicit parallel composition -/

/-- Parallel composition of explicit LTSs, synchronising on the labels satisfying `sync`. -/
def par [DecidableEq L] {S' : Type*} (E : ExplicitLTS S L) (F : ExplicitLTS S' L)
    (sync : L → Bool) : ExplicitLTS (S × S') L where
  succ p :=
    ((E.succ p.1).flatMap fun e =>
      if sync e.1 then ((F.succ p.2).filter fun f => decide (f.1 = e.1)).map fun f => (e.1, (e.2, f.2))
      else [(e.1, (e.2, p.2))]) ++
    ((F.succ p.2).filterMap fun f => if sync f.1 then none else some (f.1, (p.1, f.2)))

theorem par_toLTS [DecidableEq L] {S' : Type*} (E : ExplicitLTS S L) (F : ExplicitLTS S' L)
    (sync : L → Bool) : (E.par F sync).toLTS = E.toLTS.par F.toLTS (fun l => sync l = true) := by
  cases h : (E.par F sync).toLTS with
  | mk st =>
  have hst : st = (E.par F sync).toLTS.step := by rw [h]
  subst hst
  unfold LTS.par
  congr 1
  funext p l p'
  apply propext
  obtain ⟨s, u⟩ := p
  obtain ⟨s', u'⟩ := p'
  change (l, (s', u')) ∈ (E.par F sync).succ (s, u) ↔ _
  simp only [par, List.mem_append, List.mem_flatMap, List.mem_filterMap, toLTS]
  constructor
  · rintro (⟨e, he, hmem⟩ | ⟨f, hf, hmem⟩)
    · split_ifs at hmem with hs
      · simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq] at hmem
        obtain ⟨f, ⟨hf, hfe⟩, rfl, rfl, rfl⟩ := hmem
        refine Or.inl ⟨hs, he, ?_⟩
        rw [← hfe]; exact hf
      · simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        obtain ⟨rfl, rfl, rfl⟩ := hmem
        exact Or.inr ⟨by simpa using hs, Or.inl ⟨he, rfl⟩⟩
    · split_ifs at hmem with hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl, rfl⟩ := hmem
      exact Or.inr ⟨by simpa using hs, Or.inr ⟨rfl, hf⟩⟩
  · rintro (⟨hs, he, hf⟩ | ⟨hs, ⟨he, hu⟩ | ⟨hs', hf⟩⟩)
    · refine Or.inl ⟨(l, s'), he, ?_⟩
      simp only [hs, ↓reduceIte, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
      exact ⟨(l, u'), ⟨hf, rfl⟩, by simp⟩
    · change u' = u at hu
      subst hu
      refine Or.inl ⟨(l, s'), he, ?_⟩
      have : sync l = false := by simpa using hs
      simp [this]
    · change s' = s at hs'
      subst hs'
      refine Or.inr ⟨(l, u'), hf, ?_⟩
      have : sync l = false := by simpa using hs
      simp [this]

/-! ### Compositional verification with certified quotients -/

section Compositional

variable {S' : Type*} [DecidableEq S] [DecidableEq L] {cmp : S → S → Ordering}

/-- **Replace the left component by its certified quotient.**  Deadlock freedom and livelock
freedom of `E ∥ F` (with every label satisfying `j` internal) are equivalent to those of
`Q ∥ F`.  The component is minimised with the labels that are internal and not synchronised
hidden. -/
theorem dfLf_par_left_iff {E : ExplicitLTS S L} {F : ExplicitLTS S' L} {sync j : L → Bool}
    {q : BTree (ℕ × List (L × ℕ))} {s₀ : S} {c : InvCert S QData} {k₀ : ℕ}
    (hq : E.checkQuot cmp (fun l => j l && !sync l) q s₀ c = true)
    (hk : c.cls cmp s₀ = some k₀) (u₀ : S') :
    ((E.par F sync).toLTS.DeadlockFree (s₀, u₀) ∧
        (E.par F sync).toLTS.LivelockFree (fun l => j l = true) (s₀, u₀)) ↔
      (((quotLTS q).par F sync).toLTS.DeadlockFree (k₀, u₀) ∧
        ((quotLTS q).par F sync).toLTS.LivelockFree (fun l => j l = true) (k₀, u₀)) := by
  rw [par_toLTS, par_toLTS]
  refine LTS.dfLf_par_iff (divBisim_of_checkQuot hq) ?_ ?_ ⟨LTS.Reachable.refl _, hk⟩ u₀
  · intro l hl hs
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hl
    rw [hl.2] at hs
    cases hs
  · intro l hl
    simp only [Bool.and_eq_true] at hl
    exact hl.1

/-- **Replace the right component by its certified quotient.** -/
theorem dfLf_par_right_iff {E : ExplicitLTS S L} {F : ExplicitLTS S' L} {sync j : L → Bool}
    {q : BTree (ℕ × List (L × ℕ))} {s₀ : S} {c : InvCert S QData} {k₀ : ℕ}
    (hq : E.checkQuot cmp (fun l => j l && !sync l) q s₀ c = true)
    (hk : c.cls cmp s₀ = some k₀) (u₀ : S') :
    ((F.par E sync).toLTS.DeadlockFree (u₀, s₀) ∧
        (F.par E sync).toLTS.LivelockFree (fun l => j l = true) (u₀, s₀)) ↔
      ((F.par (quotLTS q) sync).toLTS.DeadlockFree (u₀, k₀) ∧
        (F.par (quotLTS q) sync).toLTS.LivelockFree (fun l => j l = true) (u₀, k₀)) := by
  have h₁ : ((F.par E sync).toLTS.DeadlockFree (u₀, s₀) ∧
        (F.par E sync).toLTS.LivelockFree (fun l => j l = true) (u₀, s₀)) ↔
      ((E.par F sync).toLTS.DeadlockFree (s₀, u₀) ∧
        (E.par F sync).toLTS.LivelockFree (fun l => j l = true) (s₀, u₀)) := by
    rw [par_toLTS, par_toLTS]
    exact (LTS.DivBisim.par_comm _ _ _ _).dfLf_iff rfl
  have h₂ : ((F.par (quotLTS q) sync).toLTS.DeadlockFree (u₀, k₀) ∧
        (F.par (quotLTS q) sync).toLTS.LivelockFree (fun l => j l = true) (u₀, k₀)) ↔
      (((quotLTS q).par F sync).toLTS.DeadlockFree (k₀, u₀) ∧
        ((quotLTS q).par F sync).toLTS.LivelockFree (fun l => j l = true) (k₀, u₀)) := by
    rw [par_toLTS, par_toLTS]
    exact (LTS.DivBisim.par_comm _ _ _ _).dfLf_iff rfl
  rw [h₁, h₂]
  exact dfLf_par_left_iff hq hk u₀

end Compositional

end ExplicitLTS

end AsyncLean
