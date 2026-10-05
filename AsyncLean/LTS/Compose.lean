/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties

/-!
# Compositional verification

Large asynchronous systems are built from components communicating through handshakes.
Exploring the product of all components quickly becomes infeasible.  The standard remedy is
*compositional minimisation*: replace a component by a smaller one that is equivalent for the
properties of interest, then compose.  This file provides the theory.

* `LTS.par A B sync` — parallel composition: labels satisfying `sync` are performed by both
  components together, the others by one component at a time.
* `LTS.DivBisim A B internal R` — `R` is a *divergence-preserving weak bisimulation*: visible
  steps are matched up to internal steps, internal steps by zero or more internal steps, and
  related states agree on the existence of infinite internal runs.

Main results:

* `DivBisim.dfLf_iff` — bisimilar systems agree on *deadlock freedom ∧ livelock freedom*;
* `DivBisim.liveLabel_iff` — and on liveness of every visible label;
* `DivBisim.par` — divergence-preserving weak bisimulation is a congruence for parallel
  composition (when internal labels are not synchronised);
* `DivBisim.hide` — it is preserved by hiding further labels (making them internal);
* `DivBisim.symm`, `DivBisim.refl`.

Together: to verify `A ∥ B` one may verify `A' ∥ B` for any `A'` bisimilar to `A`
(`dfLf_par_iff`).
-/

namespace AsyncLean

namespace LTS

variable {S S' S'' L : Type*}

/-! ### Parallel composition -/

/-- Parallel composition synchronising on the labels satisfying `sync`. -/
def par (A : LTS S L) (B : LTS S' L) (sync : L → Prop) : LTS (S × S') L where
  step p l p' := (sync l ∧ A.step p.1 l p'.1 ∧ B.step p.2 l p'.2) ∨
    (¬ sync l ∧ ((A.step p.1 l p'.1 ∧ p'.2 = p.2) ∨ (p'.1 = p.1 ∧ B.step p.2 l p'.2)))

theorem par_left {A : LTS S L} {B : LTS S' L} {sync : L → Prop} {s s' : S} {u : S'} {l : L}
    (hl : ¬ sync l) (h : A.step s l s') : (A.par B sync).step (s, u) l (s', u) :=
  Or.inr ⟨hl, Or.inl ⟨h, rfl⟩⟩

theorem par_right {A : LTS S L} {B : LTS S' L} {sync : L → Prop} {s : S} {u u' : S'} {l : L}
    (hl : ¬ sync l) (h : B.step u l u') : (A.par B sync).step (s, u) l (s, u') :=
  Or.inr ⟨hl, Or.inr ⟨rfl, h⟩⟩

theorem par_sync {A : LTS S L} {B : LTS S' L} {sync : L → Prop} {s s' : S} {u u' : S'} {l : L}
    (hl : sync l) (h : A.step s l s') (h' : B.step u l u') :
    (A.par B sync).step (s, u) l (s', u') :=
  Or.inl ⟨hl, h, h'⟩

/-! ### Weak steps -/

/-- Zero or more internal steps. -/
def TauStar (A : LTS S L) (internal : L → Prop) : S → S → Prop :=
  Relation.ReflTransGen (A.IStep internal)

/-- A weak `l`-step: internal steps, an `l`-step, internal steps. -/
def WeakStep (A : LTS S L) (internal : L → Prop) (l : L) (s s' : S) : Prop :=
  ∃ s₁ s₂, A.TauStar internal s s₁ ∧ A.step s₁ l s₂ ∧ A.TauStar internal s₂ s'

/-- How a step labelled `l` may be matched: internal labels by internal steps (possibly none),
any label by a weak step. -/
def WMatch (A : LTS S L) (internal : L → Prop) (l : L) (s s' : S) : Prop :=
  (internal l ∧ A.TauStar internal s s') ∨ A.WeakStep internal l s s'

variable {A : LTS S L} {B : LTS S' L} {internal : L → Prop}

theorem TauStar.reachable {s s' : S} (h : A.TauStar internal s s') : A.Reachable s s' :=
  Reachable.of_iStep_rtc h

theorem WeakStep.reachable {l : L} {s s' : S} (h : A.WeakStep internal l s s') :
    A.Reachable s s' := by
  obtain ⟨s₁, s₂, h₁, h₂, h₃⟩ := h
  exact h₁.reachable.trans ((Reachable.of_step h₂).trans h₃.reachable)

theorem WMatch.reachable {l : L} {s s' : S} (h : A.WMatch internal l s s') : A.Reachable s s' := by
  rcases h with ⟨-, h⟩ | h
  · exact h.reachable
  · exact h.reachable

theorem WeakStep.tauStar {l : L} {s s' : S} (hl : internal l) (h : A.WeakStep internal l s s') :
    A.TauStar internal s s' := by
  obtain ⟨s₁, s₂, h₁, h₂, h₃⟩ := h
  exact h₁.trans (Relation.ReflTransGen.head ⟨l, hl, h₂⟩ h₃)

theorem WMatch.tauStar {l : L} {s s' : S} (hl : internal l) (h : A.WMatch internal l s s') :
    A.TauStar internal s s' := by
  rcases h with ⟨-, h⟩ | h
  · exact h
  · exact h.tauStar hl

theorem WMatch.weakStep {l : L} {s s' : S} (hl : ¬ internal l) (h : A.WMatch internal l s s') :
    A.WeakStep internal l s s' := by
  rcases h with ⟨h', -⟩ | h
  · exact absurd h' hl
  · exact h

theorem WeakStep.of_step {l : L} {s s' : S} (h : A.step s l s') : A.WeakStep internal l s s' :=
  ⟨s, s', Relation.ReflTransGen.refl, h, Relation.ReflTransGen.refl⟩

theorem WeakStep.tauStar_left {l : L} {s s₁ s' : S} (h₁ : A.TauStar internal s s₁)
    (h : A.WeakStep internal l s₁ s') : A.WeakStep internal l s s' := by
  obtain ⟨a, b, ha, hb, hc⟩ := h
  exact ⟨a, b, h₁.trans ha, hb, hc⟩

theorem WeakStep.tauStar_right {l : L} {s s₁ s' : S} (h : A.WeakStep internal l s s₁)
    (h₁ : A.TauStar internal s₁ s') : A.WeakStep internal l s s' := by
  obtain ⟨a, b, ha, hb, hc⟩ := h
  exact ⟨a, b, ha, hb, hc.trans h₁⟩

/-- A step from a deadlocked state is impossible, so internal paths from it are trivial. -/
theorem TauStar.eq_of_deadlock {s s' : S} (hd : A.IsDeadlock s) (h : A.TauStar internal s s') :
    s' = s := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, ⟨l, -, hst⟩, -⟩
  · exact h.symm
  · exact absurd hst (hd l c)

theorem WeakStep.not_of_deadlock {l : L} {s s' : S} (hd : A.IsDeadlock s) :
    ¬ A.WeakStep internal l s s' := by
  rintro ⟨s₁, s₂, h₁, h₂, -⟩
  rw [h₁.eq_of_deadlock hd] at h₂
  exact hd l s₂ h₂

/-! ### Divergence-preserving weak bisimulation -/

/-- `R` is a divergence-preserving weak bisimulation between `A` and `B`. -/
structure DivBisim (A : LTS S L) (B : LTS S' L) (internal : L → Prop) (R : S → S' → Prop) :
    Prop where
  /-- Every step of `A` is matched by `B`. -/
  fwd : ∀ s t, R s t → ∀ l s', A.step s l s' → ∃ t', B.WMatch internal l t t' ∧ R s' t'
  /-- Every step of `B` is matched by `A`. -/
  bwd : ∀ s t, R s t → ∀ l t', B.step t l t' → ∃ s', A.WMatch internal l s s' ∧ R s' t'
  /-- Related states agree on the absence of infinite internal runs. -/
  div : ∀ s t, R s t → (Acc (A.IRel internal) s ↔ Acc (B.IRel internal) t)

namespace DivBisim

variable {R : S → S' → Prop}

theorem symm (h : DivBisim A B internal R) : DivBisim B A internal (fun t s => R s t) :=
  ⟨fun t s hr l t' ht => h.bwd s t hr l t' ht, fun t s hr l s' hs => h.fwd s t hr l s' hs,
    fun t s hr => (h.div s t hr).symm⟩

theorem refl (A : LTS S L) (internal : L → Prop) : DivBisim A A internal Eq where
  fwd := by
    rintro s _ rfl l s' h
    exact ⟨s', Or.inr (WeakStep.of_step h), rfl⟩
  bwd := by
    rintro s _ rfl l s' h
    exact ⟨s', Or.inr (WeakStep.of_step h), rfl⟩
  div := by rintro s _ rfl; exact Iff.rfl

theorem tauStar_match (h : DivBisim A B internal R) {s s' : S} {t : S'} (hr : R s t)
    (hp : A.TauStar internal s s') : ∃ t', B.TauStar internal t t' ∧ R s' t' := by
  induction hp with
  | refl => exact ⟨t, Relation.ReflTransGen.refl, hr⟩
  | tail _ hst ih =>
    obtain ⟨t₁, ht₁, hr₁⟩ := ih
    obtain ⟨l, hl, hst⟩ := hst
    obtain ⟨t₂, ht₂, hr₂⟩ := h.fwd _ _ hr₁ l _ hst
    exact ⟨t₂, ht₁.trans (ht₂.tauStar hl), hr₂⟩

theorem reachable_match (h : DivBisim A B internal R) {s s' : S} {t : S'} (hr : R s t)
    (hp : A.Reachable s s') : ∃ t', B.Reachable t t' ∧ R s' t' := by
  induction hp with
  | refl => exact ⟨t, Reachable.refl t, hr⟩
  | tail _ hst ih =>
    obtain ⟨t₁, ht₁, hr₁⟩ := ih
    obtain ⟨l, hst⟩ := hst
    obtain ⟨t₂, ht₂, hr₂⟩ := h.fwd _ _ hr₁ l _ hst
    exact ⟨t₂, ht₁.trans ht₂.reachable, hr₂⟩

/-- Deadlock freedom and livelock freedom transfer from `B` to `A`. -/
theorem dfLf_of (h : DivBisim A B internal R) {s₀ : S} {t₀ : S'} (h₀ : R s₀ t₀)
    (hd : B.DeadlockFree t₀) (hl : B.LivelockFree internal t₀) :
    A.DeadlockFree s₀ ∧ A.LivelockFree internal s₀ := by
  refine ⟨fun s hs hdead => ?_, ?_⟩
  · obtain ⟨t, ht, hr⟩ := h.reachable_match h₀ hs
    have hacc := hl.acc ht
    induction hacc with
    | intro t _ ih =>
      obtain ⟨l, t', hst⟩ := hd.exists_step ht
      obtain ⟨s', hm, hr'⟩ := h.bwd s t hr l t' hst
      rcases hm with ⟨hint, hp⟩ | hw
      · rw [hp.eq_of_deadlock hdead] at hr'
        exact ih t' ⟨l, hint, hst⟩ (ht.tail ⟨l, hst⟩) hr'
      · exact hw.not_of_deadlock hdead
  · rw [livelockFree_iff_acc]
    intro s hs
    obtain ⟨t, ht, hr⟩ := h.reachable_match h₀ hs
    exact (h.div s t hr).2 (hl.acc ht)

/-- **Bisimilar systems agree on deadlock freedom together with livelock freedom.** -/
theorem dfLf_iff (h : DivBisim A B internal R) {s₀ : S} {t₀ : S'} (h₀ : R s₀ t₀) :
    (A.DeadlockFree s₀ ∧ A.LivelockFree internal s₀) ↔
      (B.DeadlockFree t₀ ∧ B.LivelockFree internal t₀) :=
  ⟨fun ⟨hd, hl⟩ => h.symm.dfLf_of h₀ hd hl, fun ⟨hd, hl⟩ => h.dfLf_of h₀ hd hl⟩

/-- Liveness of a visible label transfers from `B` to `A`. -/
theorem liveLabel_of (h : DivBisim A B internal R) {s₀ : S} {t₀ : S'} (h₀ : R s₀ t₀) {l : L}
    (hvis : ¬ internal l) (hlive : B.LiveLabel t₀ l) : A.LiveLabel s₀ l := by
  intro s hs
  obtain ⟨t, ht, hr⟩ := h.reachable_match h₀ hs
  obtain ⟨t', ht', t'', hst⟩ := hlive t ht
  obtain ⟨s', hs', hr'⟩ := h.symm.reachable_match hr ht'
  obtain ⟨s'', hm, -⟩ := h.bwd s' t' hr' l t'' hst
  obtain ⟨s₁, s₂, h₁, h₂, -⟩ := hm.weakStep hvis
  exact ⟨s₁, hs'.trans h₁.reachable, s₂, h₂⟩

theorem liveLabel_iff (h : DivBisim A B internal R) {s₀ : S} {t₀ : S'} (h₀ : R s₀ t₀) {l : L}
    (hvis : ¬ internal l) : A.LiveLabel s₀ l ↔ B.LiveLabel t₀ l :=
  ⟨h.symm.liveLabel_of h₀ hvis, h.liveLabel_of h₀ hvis⟩

theorem wmatch_match (h : DivBisim A B internal R) {s s' : S} {t : S'} {l : L} (hr : R s t)
    (hm : A.WMatch internal l s s') : ∃ t', B.WMatch internal l t t' ∧ R s' t' := by
  rcases hm with ⟨hi, hp⟩ | ⟨s₁, s₂, h₁, h₂, h₃⟩
  · obtain ⟨t', ht', hr'⟩ := h.tauStar_match hr hp
    exact ⟨t', Or.inl ⟨hi, ht'⟩, hr'⟩
  · obtain ⟨t₁, ht₁, hr₁⟩ := h.tauStar_match hr h₁
    obtain ⟨t₂, ht₂, hr₂⟩ := h.fwd _ _ hr₁ l s₂ h₂
    obtain ⟨t₃, ht₃, hr₃⟩ := h.tauStar_match hr₂ h₃
    refine ⟨t₃, ?_, hr₃⟩
    rcases ht₂ with ⟨hi, hp⟩ | hw
    · exact Or.inl ⟨hi, ht₁.trans (hp.trans ht₃)⟩
    · exact Or.inr ((hw.tauStar_left ht₁).tauStar_right ht₃)

/-- Divergence-preserving weak bisimulations compose. -/
theorem trans {C : LTS S'' L} {R' : S' → S'' → Prop} (h : DivBisim A B internal R)
    (h' : DivBisim B C internal R') :
    DivBisim A C internal (fun s u => ∃ t, R s t ∧ R' t u) where
  fwd := by
    rintro s u ⟨t, hr, hr'⟩ l s' hst
    obtain ⟨t', hm, hr₁⟩ := h.fwd s t hr l s' hst
    obtain ⟨u', hm', hr₁'⟩ := h'.wmatch_match hr' hm
    exact ⟨u', hm', t', hr₁, hr₁'⟩
  bwd := by
    rintro s u ⟨t, hr, hr'⟩ l u' hst
    obtain ⟨t', hm, hr₁'⟩ := h'.bwd t u hr' l u' hst
    obtain ⟨s', hm', hr₁⟩ := h.symm.wmatch_match hr hm
    exact ⟨s', hm', t', hr₁, hr₁'⟩
  div := by
    rintro s u ⟨t, hr, hr'⟩
    exact (h.div s t hr).trans (h'.div t u hr')

/-! ### Congruence for parallel composition -/

variable {T : Type*} {C : LTS T L} {sync : L → Prop}

theorem tauStar_par_left {s s' : S} {u : T} (hns : ∀ l, internal l → ¬ sync l)
    (h : A.TauStar internal s s') : (A.par C sync).TauStar internal (s, u) (s', u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
    obtain ⟨l, hl, hst⟩ := hst
    exact ih.tail ⟨l, hl, par_left (hns l hl) hst⟩

theorem transGen_par_left {s s' : S} {u : T} (hns : ∀ l, internal l → ¬ sync l)
    (h : Relation.TransGen (A.IStep internal) s s') :
    Relation.TransGen ((A.par C sync).IStep internal) (s, u) (s', u) := by
  induction h with
  | single hst =>
    obtain ⟨l, hl, hst⟩ := hst
    exact Relation.TransGen.single ⟨l, hl, par_left (hns l hl) hst⟩
  | tail _ hst ih =>
    obtain ⟨l, hl, hst⟩ := hst
    exact ih.tail ⟨l, hl, par_left (hns l hl) hst⟩

/-- One direction of the transfer condition for the composition. -/
theorem par_transfer (hfwd : ∀ s t, R s t → ∀ l s', A.step s l s' →
      ∃ t', B.WMatch internal l t t' ∧ R s' t')
    (hns : ∀ l, internal l → ¬ sync l) :
    ∀ p q, (R p.1 q.1 ∧ p.2 = q.2) → ∀ l p', (A.par C sync).step p l p' →
      ∃ q', (B.par C sync).WMatch internal l q q' ∧ (R p'.1 q'.1 ∧ p'.2 = q'.2) := by
  rintro ⟨s, u⟩ ⟨t, u₀⟩ ⟨hr, he⟩ l ⟨s', u'⟩ hst
  change u = u₀ at he
  subst u₀
  rcases hst with ⟨hsync, hA, hC⟩ | ⟨hns', ⟨hA, rfl⟩ | ⟨rfl, hC⟩⟩
  · -- synchronised step
    have hvis : ¬ internal l := fun hi => hns l hi hsync
    obtain ⟨t', hm, hr'⟩ := hfwd s t hr l s' hA
    obtain ⟨t₁, t₂, h₁, h₂, h₃⟩ := hm.weakStep hvis
    exact ⟨(t', u'), Or.inr ⟨(t₁, u), (t₂, u'), tauStar_par_left hns h₁, par_sync hsync h₂ hC,
      tauStar_par_left hns h₃⟩, hr', rfl⟩
  · -- the left component moves alone
    obtain ⟨t', hm, hr'⟩ := hfwd s t hr l s' hA
    refine ⟨(t', u'), ?_, hr', rfl⟩
    rcases hm with ⟨hi, hp⟩ | ⟨t₁, t₂, h₁, h₂, h₃⟩
    · exact Or.inl ⟨hi, tauStar_par_left hns hp⟩
    · exact Or.inr ⟨(t₁, u'), (t₂, u'), tauStar_par_left hns h₁, par_left hns' h₂,
        tauStar_par_left hns h₃⟩
  · -- the right component moves alone
    refine ⟨(t, u'), ?_, hr, rfl⟩
    by_cases hi : internal l
    · exact Or.inl ⟨hi, Relation.ReflTransGen.single ⟨l, hi, par_right hns' hC⟩⟩
    · exact Or.inr (WeakStep.of_step (par_right hns' hC))

theorem acc_left_of_par {p : S × T} (hns : ∀ l, internal l → ¬ sync l)
    (h : Acc ((A.par C sync).IRel internal) p) : Acc (A.IRel internal) p.1 := by
  induction h with
  | intro p _ ih =>
    refine Acc.intro p.1 fun s' ⟨l, hl, hst⟩ => ?_
    exact ih (s', p.2) ⟨l, hl, par_left (hns l hl) hst⟩

/-- Divergence preservation for the composition, by a double induction: on the internal runs
of the composite of `A` (outer) and on those of `B` (inner). -/
theorem par_acc_aux (h : DivBisim A B internal R) (hns : ∀ l, internal l → ¬ sync l) :
    ∀ p : S × T, Acc (Relation.TransGen ((A.par C sync).IRel internal)) p →
      ∀ t, R p.1 t → Acc (B.IRel internal) t → Acc ((B.par C sync).IRel internal) (t, p.2) := by
  intro p hp
  induction hp with
  | intro p _ ihO =>
    intro t hr ht
    induction ht with
    | intro t hacc ihI =>
      refine Acc.intro _ fun q hq => ?_
      obtain ⟨l, hl, hst⟩ := hq
      obtain ⟨t₁, u₁⟩ := q
      rcases hst with ⟨hsync, -, -⟩ | ⟨hns', ⟨hB, hu⟩ | ⟨ht₁, hC⟩⟩
      · exact absurd hsync (hns l hl)
      · -- `B` moves internally: `A` follows with internal steps
        change u₁ = p.2 at hu
        subst hu
        obtain ⟨s₁, hm, hr₁⟩ := h.bwd p.1 t hr l t₁ hB
        rcases Relation.reflTransGen_iff_eq_or_transGen.1 (hm.tauStar hl) with heq | hp'
        · rw [heq] at hr₁
          exact ihI t₁ ⟨l, hl, hB⟩ hr₁
        · have hlift := transGen_par_left (C := C) (u := p.2) hns hp'
          exact ihO (s₁, p.2) (Relation.transGen_swap.2 hlift) t₁ hr₁ (hacc t₁ ⟨l, hl, hB⟩)
      · -- the third component moves internally
        change t₁ = t at ht₁
        subst ht₁
        exact ihO (p.1, u₁) (Relation.TransGen.single ⟨l, hl, par_right hns' hC⟩) t₁ hr
          (Acc.intro t₁ hacc)

theorem par_acc (h : DivBisim A B internal R) (hns : ∀ l, internal l → ¬ sync l)
    {s : S} {t : S'} {u : T} (hr : R s t) (hacc : Acc ((A.par C sync).IRel internal) (s, u)) :
    Acc ((B.par C sync).IRel internal) (t, u) :=
  par_acc_aux h hns (s, u) hacc.transGen t hr ((h.div s t hr).1 (acc_left_of_par hns hacc))

/-- **Congruence**: divergence-preserving weak bisimulation is preserved by composing both
sides with the same component, provided internal labels are never synchronised. -/
theorem par (h : DivBisim A B internal R) (hns : ∀ l, internal l → ¬ sync l) :
    DivBisim (A.par C sync) (B.par C sync) internal (fun p q => R p.1 q.1 ∧ p.2 = q.2) where
  fwd := par_transfer h.fwd hns
  bwd := by
    rintro p q ⟨hr, he⟩ l q' hst
    obtain ⟨p', hm, hr', he'⟩ :=
      par_transfer (A := B) (B := A) (R := fun t s => R s t) h.symm.fwd hns q p ⟨hr, he.symm⟩
        l q' hst
    exact ⟨p', hm, hr', he'.symm⟩
  div := by
    rintro ⟨s, u⟩ ⟨t, u'⟩ ⟨hr, he⟩
    change u = u' at he
    subst he
    exact ⟨par_acc h hns hr, par_acc h.symm hns hr⟩

/-! ### Hiding -/

theorem tauStar_mono {internal' : L → Prop} (hsub : ∀ l, internal l → internal' l) {s s' : S}
    (h : A.TauStar internal s s') : A.TauStar internal' s s' :=
  Relation.ReflTransGen.mono (fun _ _ ⟨l, hl, hst⟩ => ⟨l, hsub l hl, hst⟩) _ _ h

theorem WMatch.mono {internal' : L → Prop} (hsub : ∀ l, internal l → internal' l) {l : L}
    {s s' : S} (h : A.WMatch internal l s s') : A.WMatch internal' l s s' := by
  rcases h with ⟨hi, hp⟩ | ⟨s₁, s₂, h₁, h₂, h₃⟩
  · exact Or.inl ⟨hsub l hi, tauStar_mono hsub hp⟩
  · exact Or.inr ⟨s₁, s₂, tauStar_mono hsub h₁, h₂, tauStar_mono hsub h₃⟩

theorem acc_antitone {internal' : L → Prop} (hsub : ∀ l, internal l → internal' l) {s : S}
    (h : Acc (A.IRel internal') s) : Acc (A.IRel internal) s :=
  Subrelation.accessible (fun ⟨l, hl, hst⟩ => ⟨l, hsub l hl, hst⟩) h

theorem hide_acc_aux (h : DivBisim A B internal R) {internal' : L → Prop}
    (hsub : ∀ l, internal l → internal' l) :
    ∀ s, Acc (Relation.TransGen (A.IRel internal')) s →
      ∀ t, R s t → Acc (B.IRel internal) t → Acc (B.IRel internal') t := by
  intro s hs
  induction hs with
  | intro s hsacc ihO =>
    intro t hr ht
    induction ht with
    | intro t hacc ihI =>
      refine Acc.intro t fun t₁ ⟨l, hl, hst⟩ => ?_
      obtain ⟨s₁, hm, hr₁⟩ := h.bwd s t hr l t₁ hst
      by_cases hi : internal l
      · rcases Relation.reflTransGen_iff_eq_or_transGen.1 (hm.tauStar hi) with heq | hp
        · rw [heq] at hr₁
          exact ihI t₁ ⟨l, hi, hst⟩ hr₁
        · have hp' : Relation.TransGen (A.IStep internal') s s₁ :=
            Relation.TransGen.mono (fun _ _ ⟨l, hl, hst⟩ => ⟨l, hsub l hl, hst⟩) _ _ hp
          exact ihO s₁ (Relation.transGen_swap.2 hp') t₁ hr₁ (hacc t₁ ⟨l, hi, hst⟩)
      · obtain ⟨a, b, h₁, h₂, h₃⟩ := hm.weakStep hi
        have hp : Relation.TransGen (A.IStep internal') s s₁ :=
          Relation.TransGen.trans_left
            (Relation.TransGen.tail' (tauStar_mono hsub h₁) ⟨l, hl, h₂⟩) (tauStar_mono hsub h₃)
        have hs₁ : Acc (Relation.TransGen (A.IRel internal')) s₁ :=
          hsacc s₁ (Relation.transGen_swap.2 hp)
        have hs₁' : Acc (A.IRel internal) s₁ :=
          acc_antitone hsub (Subrelation.accessible (fun h => Relation.TransGen.single h) hs₁)
        exact ihO s₁ (Relation.transGen_swap.2 hp) t₁ hr₁ ((h.div s₁ t₁ hr₁).1 hs₁')

/-- **Hiding**: making more labels internal preserves divergence-preserving weak
bisimulation. -/
theorem hide (h : DivBisim A B internal R) {internal' : L → Prop}
    (hsub : ∀ l, internal l → internal' l) : DivBisim A B internal' R where
  fwd s t hr l s' hst := by
    obtain ⟨t', hm, hr'⟩ := h.fwd s t hr l s' hst
    exact ⟨t', WMatch.mono hsub hm, hr'⟩
  bwd s t hr l t' hst := by
    obtain ⟨s', hm, hr'⟩ := h.bwd s t hr l t' hst
    exact ⟨s', WMatch.mono hsub hm, hr'⟩
  div s t hr := by
    constructor
    · intro ha
      exact h.hide_acc_aux hsub s ha.transGen t hr ((h.div s t hr).1 (acc_antitone hsub ha))
    · intro hb
      exact h.symm.hide_acc_aux hsub t hb.transGen s hr ((h.div s t hr).2 (acc_antitone hsub hb))

end DivBisim

/-! ### Commutativity of composition -/

theorem par_swap_step {A : LTS S L} {B : LTS S' L} {sync : L → Prop} {p p' : S × S'} {l : L}
    (h : (A.par B sync).step p l p') : (B.par A sync).step p.swap l p'.swap := by
  rcases h with ⟨hs, ha, hb⟩ | ⟨hs, ⟨ha, he⟩ | ⟨he, hb⟩⟩
  · exact Or.inl ⟨hs, hb, ha⟩
  · exact Or.inr ⟨hs, Or.inr ⟨he, ha⟩⟩
  · exact Or.inr ⟨hs, Or.inl ⟨hb, he⟩⟩

theorem acc_par_swap {A : LTS S L} {B : LTS S' L} {sync internal : L → Prop} {p : S × S'}
    (h : Acc ((A.par B sync).IRel internal) p) : Acc ((B.par A sync).IRel internal) p.swap := by
  induction h with
  | intro p _ ih =>
    refine Acc.intro _ fun q ⟨l, hl, hst⟩ => ?_
    have := ih q.swap ⟨l, hl, by simpa using par_swap_step hst⟩
    simpa using this

/-- Parallel composition is commutative up to (strong, hence weak) bisimulation. -/
theorem DivBisim.par_comm (A : LTS S L) (B : LTS S' L) (sync internal : L → Prop) :
    DivBisim (A.par B sync) (B.par A sync) internal (fun p q => q = p.swap) where
  fwd := by
    rintro p q rfl l p' hst
    refine ⟨p'.swap, ?_, rfl⟩
    by_cases hi : internal l
    · exact Or.inl ⟨hi, Relation.ReflTransGen.single ⟨l, hi, par_swap_step hst⟩⟩
    · exact Or.inr (WeakStep.of_step (par_swap_step hst))
  bwd := by
    rintro p q rfl l q' hst
    refine ⟨q'.swap, ?_, by simp⟩
    have hst' : (A.par B sync).step p l q'.swap := by simpa using par_swap_step hst
    by_cases hi : internal l
    · exact Or.inl ⟨hi, Relation.ReflTransGen.single ⟨l, hi, hst'⟩⟩
    · exact Or.inr (WeakStep.of_step hst')
  div := by
    rintro p q rfl
    exact ⟨acc_par_swap, fun h => by simpa using acc_par_swap h⟩

/-- **Compositional verification.**  To prove that `A ∥ C` (with the synchronised labels
hidden, i.e. treated as internal by `internal'`) is deadlock and livelock free, it suffices to
prove it for `B ∥ C`, for any `B` related to `A` by a divergence-preserving weak
bisimulation. -/
theorem dfLf_par_iff {T : Type*} {A : LTS S L} {B : LTS S' L} {C : LTS T L}
    {internal internal' : L → Prop} {sync : L → Prop} {R : S → S' → Prop}
    (h : DivBisim A B internal R) (hns : ∀ l, internal l → ¬ sync l)
    (hsub : ∀ l, internal l → internal' l) {s₀ : S} {t₀ : S'} (h₀ : R s₀ t₀) (u₀ : T) :
    ((A.par C sync).DeadlockFree (s₀, u₀) ∧ (A.par C sync).LivelockFree internal' (s₀, u₀)) ↔
      ((B.par C sync).DeadlockFree (t₀, u₀) ∧ (B.par C sync).LivelockFree internal' (t₀, u₀)) :=
  ((h.par (C := C) hns).hide hsub).dfLf_iff ⟨h₀, rfl⟩

end LTS

end AsyncLean
