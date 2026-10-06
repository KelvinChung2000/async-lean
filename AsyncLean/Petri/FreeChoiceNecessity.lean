/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.FreeChoice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Commoner's theorem: necessity

`Net.live_of_siphonTrap` shows that the siphon–trap property implies liveness of an ordinary
free-choice net.  This file proves the converse, for nets without isolated places
(`Net.siphonTrap_of_live`), and hence **Commoner's theorem**
(`Net.live_iff_siphonTrap`): *an ordinary free-choice net without isolated places is live
iff every non-empty siphon contains an initially marked trap.*

Proof.  Let `S` be a non-empty siphon whose greatest trap `Q` is unmarked.  Shrinking `S` to
`Q` removes its places one round at a time; a place `p` of `S \ Q` is removed because some
transition `α p` consuming from `p` puts nothing into the places still present, so `α p`
puts tokens only into places of `S \ Q` removed earlier, and never into `Q`
(`exists_trap_rank`).

* A transition that takes nothing from `S` does not change the marking of `S`, since `S` is
  a siphon.
* Whenever a transition taking a token from `S` is enabled while `Q` is unmarked, it takes
  that token from some `p ∈ S \ Q`; by free choice `α p` has the same input places, so it is
  enabled too.
* Firing `α p` strictly decreases a weighted count of the tokens in `S \ Q`, and keeps `Q`
  unmarked.

By liveness, from any reachable marking some transition taking from `S` can be enabled,
using only transitions that leave `S` alone before it; replacing it by the matching `α p`
decreases the weighted count.  So a marking with `S` empty is reachable, and then the
transitions consuming from `S` are dead — contradicting liveness.
-/

namespace AsyncLean

namespace Net

open Classical

variable {P T : Type*} [Fintype P] [Fintype T] {N : Net P T}

/-- The greatest trap `Q` in `S`, with ranks of the other places of `S`: each place `p` of
`S \ Q` has a transition taking from `p` whose output places in `S` are outside `Q` and of
lower rank. -/
theorem exists_trap_rank (S : Finset P) :
    ∃ Q ⊆ S, N.IsTrap Q ∧ ∃ ρ : P → ℕ, ∀ p ∈ S, p ∉ Q → ∃ t, 0 < N.pre t p ∧
      ∀ q, 0 < N.post t q → q ∈ S → q ∉ Q ∧ ρ q < ρ p := by
  suffices key : ∀ n, ∀ S : Finset P, S.card = n → ∃ Q ⊆ S, N.IsTrap Q ∧ ∃ ρ : P → ℕ,
      ∀ p ∈ S, p ∉ Q → ∃ t, 0 < N.pre t p ∧
        ∀ q, 0 < N.post t q → q ∈ S → q ∉ Q ∧ ρ q < ρ p from key _ S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn
    let D := S.filter fun p => ∃ t, 0 < N.pre t p ∧ ∀ q ∈ S, N.post t q = 0
    by_cases hD : D = ∅
    · refine ⟨S, subset_rfl, ?_, fun _ => 0, fun p hp hpQ => absurd hp hpQ⟩
      rintro t ⟨p, hp, hpre⟩
      by_contra hno
      push Not at hno
      have : p ∈ D := Finset.mem_filter.2 ⟨hp, t, hpre, fun q hq => by
        have := hno q hq; omega⟩
      rw [hD] at this
      simp at this
    · have hlt : (S \ D).card < n := by
        rw [← hn]
        exact Finset.card_lt_card
          (Finset.sdiff_ssubset (Finset.filter_subset _ _) (Finset.nonempty_iff_ne_empty.2 hD))
      obtain ⟨Q, hQS', hQ, ρ, hρ⟩ := ih _ hlt (S \ D) rfl
      refine ⟨Q, hQS'.trans Finset.sdiff_subset, hQ,
        fun p => if p ∈ S \ D then ρ p + 1 else 0, ?_⟩
      intro p hp hpQ
      by_cases hpD : p ∈ D
      · obtain ⟨-, t, hpre, hno⟩ := Finset.mem_filter.1 hpD
        exact ⟨t, hpre, fun q hq hqS => absurd (hno q hqS) (by omega)⟩
      · have hp' : p ∈ S \ D := Finset.mem_sdiff.2 ⟨hp, hpD⟩
        obtain ⟨t, hpre, hout⟩ := hρ p hp' hpQ
        refine ⟨t, hpre, fun q hq hqS => ?_⟩
        by_cases hq' : q ∈ S \ D
        · obtain ⟨h1, h2⟩ := hout q hq hq'
          simp only [hq', hp', ↓reduceIte]
          exact ⟨h1, by omega⟩
        · refine ⟨fun hqQ => hq' (hQS' hqQ), ?_⟩
          simp only [hq', hp', ↓reduceIte]
          omega

/-- A weighted count of the tokens in `R`, the weight of `p` being `(|P| + 1) ^ ρ p`. -/
noncomputable def pot (R : Finset P) (ρ : P → ℕ) (M : Marking P) : ℕ :=
  ∑ p ∈ R, (Fintype.card P + 1) ^ ρ p * M p

omit [Fintype T] in
/-- Firing a transition that takes from `p ∈ R` and puts tokens into `R` only in places of
lower rank decreases the weighted count. -/
theorem pot_fire_lt (hord : N.Ordinary) {R : Finset P} {ρ : P → ℕ} {M : Marking P} {t : T}
    {p : P} (hp : p ∈ R) (hpre : 0 < N.pre t p) (hen : N.Enabled M t)
    (hout : ∀ q ∈ R, 0 < N.post t q → ρ q < ρ p) : pot R ρ (N.fire M t) < pot R ρ M := by
  set B := Fintype.card P + 1 with hB
  have hterm : ∀ q, B ^ ρ q * N.fire M t q + B ^ ρ q * N.pre t q =
      B ^ ρ q * M q + B ^ ρ q * N.post t q := by
    intro q
    rw [fire_apply, ← Nat.mul_add, ← Nat.mul_add]
    congr 1
    have := hen q
    omega
  have hsum : pot R ρ (N.fire M t) + ∑ q ∈ R, B ^ ρ q * N.pre t q =
      pot R ρ M + ∑ q ∈ R, B ^ ρ q * N.post t q := by
    unfold pot
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => hterm q
  have hA : B ^ ρ p ≤ ∑ q ∈ R, B ^ ρ q * N.pre t q := by
    calc B ^ ρ p ≤ B ^ ρ p * N.pre t p := Nat.le_mul_of_pos_right _ hpre
      _ ≤ ∑ q ∈ R, B ^ ρ q * N.pre t q :=
        Finset.single_le_sum (f := fun q => B ^ ρ q * N.pre t q) (fun _ _ => Nat.zero_le _) hp
  have hpos : 0 < B ^ ρ p := Nat.pow_pos (by omega)
  have hBterm : ∀ q ∈ R, B * (B ^ ρ q * N.post t q) ≤ B ^ ρ p := by
    intro q hq
    by_cases hpost : 0 < N.post t q
    · have hlt := hout q hq hpost
      have h1 := (hord t q).2
      calc B * (B ^ ρ q * N.post t q) ≤ B * (B ^ ρ q * 1) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
        _ = B ^ (ρ q + 1) := by rw [pow_succ, Nat.mul_one, Nat.mul_comm]
        _ ≤ B ^ ρ p := Nat.pow_le_pow_right (by omega) hlt
    · rw [show N.post t q = 0 by omega]; simp
  have hBs : B * ∑ q ∈ R, B ^ ρ q * N.post t q < B * B ^ ρ p := by
    rw [Finset.mul_sum]
    calc ∑ q ∈ R, B * (B ^ ρ q * N.post t q) ≤ ∑ _q ∈ R, B ^ ρ p := Finset.sum_le_sum hBterm
      _ = R.card * B ^ ρ p := by rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      _ ≤ Fintype.card P * B ^ ρ p := Nat.mul_le_mul_right _ (Finset.card_le_univ R)
      _ < B * B ^ ρ p := Nat.mul_lt_mul_of_pos_right (by omega) hpos
  have hBs' := Nat.lt_of_mul_lt_mul_left hBs
  omega

/-- The weighted count only depends on the marking of `R`. -/
theorem pot_congr {R : Finset P} {ρ : P → ℕ} {M M' : Marking P} (h : ∀ q ∈ R, M q = M' q) :
    pot R ρ M = pot R ρ M' :=
  Finset.sum_congr rfl fun q hq => by rw [h q hq]

omit [Fintype P] [Fintype T] in
/-- A transition taking nothing from a siphon does not change its marking. -/
theorem fire_eq_of_not_consume {S : Finset P} (hS : N.IsSiphon S) {M : Marking P} {u : T}
    (hu : ∀ q ∈ S, N.pre u q = 0) : ∀ q ∈ S, N.fire M u q = M q := by
  intro q hq
  rw [fire_apply, hu q hq]
  have : N.post u q = 0 := by
    by_contra h
    obtain ⟨q', hq', hpre⟩ := hS u ⟨q, hq, Nat.pos_of_ne_zero h⟩
    have := hu q' hq'
    omega
  omega

/-- **Commoner's theorem, necessity.**  In a live ordinary free-choice net without isolated
places, every non-empty siphon contains an initially marked trap. -/
theorem siphonTrap_of_live (hord : N.Ordinary) (hfc : N.FreeChoice)
    (hconn : ∀ p, (∃ t, 0 < N.pre t p) ∨ ∃ t, 0 < N.post t p) {M₀ : Marking P}
    (hlive : N.lts.Live M₀) : N.SiphonTrapProperty M₀ := by
  intro S hne hS
  by_contra hno
  push Not at hno
  obtain ⟨Q, hQS, hQ, ρ, hρ⟩ := exists_trap_rank (N := N) S
  have hQ0 : ∀ q ∈ Q, M₀ q = 0 := fun q hq => by
    by_contra h
    exact hno Q (Finset.mem_powerset.2 hQS) hQ ⟨q, hq, Nat.pos_of_ne_zero h⟩
  have : Nonempty T := by
    obtain ⟨p₀, -⟩ := hne
    rcases hconn p₀ with ⟨t, -⟩ | ⟨t, -⟩ <;> exact ⟨t⟩
  choose! α hαpre hαout using hρ
  let R := S \ Q
  -- an enabled transition consuming from `S` (with `Q` empty) has an enabled allocated twin
  have htwin : ∀ (X : Marking P), (∀ q ∈ Q, X q = 0) → ∀ u q, q ∈ S → 0 < N.pre u q →
      N.Enabled X u → q ∈ R ∧ N.Enabled X (α q) := by
    intro X hX u q hq hpre hen
    have hqQ : q ∉ Q := fun h => by have := hen q; have := hX q h; omega
    refine ⟨Finset.mem_sdiff.2 ⟨hq, hqQ⟩, ?_⟩
    rw [enabled_iff_of_ordinary hord] at hen ⊢
    intro r hr
    exact hen r ((hfc (α q) u q (hαpre q hq hqQ) hpre r).1 hr)
  -- firing an allocated transition keeps `Q` empty and decreases the weighted count
  have hfire : ∀ (X : Marking P), (∀ q ∈ Q, X q = 0) → ∀ p ∈ R, N.Enabled X (α p) →
      (∀ q ∈ Q, N.fire X (α p) q = 0) ∧ pot R ρ (N.fire X (α p)) < pot R ρ X := by
    intro X hX p hp hen
    obtain ⟨hpS, hpQ⟩ := Finset.mem_sdiff.1 hp
    refine ⟨fun q hq => ?_, pot_fire_lt hord hp (hαpre p hpS hpQ) hen fun q hq hpost =>
      (hαout p hpS hpQ q hpost (Finset.mem_sdiff.1 hq).1).2⟩
    rw [fire_apply, hX q hq]
    have : N.post (α p) q = 0 := by
      by_contra h
      exact (hαout p hpS hpQ q (Nat.pos_of_ne_zero h) (hQS hq)).1 hq
    omega
  -- from `M` with `Q` empty and some transition consuming from `S` eventually enabled,
  -- the weighted count can be decreased
  have hwalk : ∀ (M M₁ : Marking P), (∀ q ∈ Q, M q = 0) → N.lts.Reachable M M₁ →
      ∀ u q, q ∈ S → 0 < N.pre u q → N.Enabled M₁ u →
      ∃ M'', N.lts.Reachable M M'' ∧ (∀ q ∈ Q, M'' q = 0) ∧ pot R ρ M'' < pot R ρ M := by
    intro M M₁ hM hr u q hq hpre hen
    have key : ∀ X, N.lts.Reachable X M₁ → (∀ r ∈ S, X r = M r) →
        ∃ M'', N.lts.Reachable X M'' ∧ (∀ q ∈ Q, M'' q = 0) ∧ pot R ρ M'' < pot R ρ M := by
      intro X hX
      induction hX using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro hagree
        have hXQ : ∀ q ∈ Q, M₁ q = 0 := fun r hr => by rw [hagree r (hQS hr)]; exact hM r hr
        obtain ⟨hqR, hen'⟩ := htwin M₁ hXQ u q hq hpre hen
        obtain ⟨hQ', hlt⟩ := hfire M₁ hXQ q hqR hen'
        refine ⟨_, LTS.Reachable.of_step ⟨hen', rfl⟩, hQ', ?_⟩
        rw [pot_congr (M' := M) fun r hr => hagree r (Finset.mem_sdiff.1 hr).1] at hlt
        exact hlt
      | head hst hrest ih =>
        rename_i X Y
        intro hagree
        obtain ⟨v, hv, rfl⟩ := hst
        have hXQ : ∀ q ∈ Q, X q = 0 := fun r hr => by rw [hagree r (hQS hr)]; exact hM r hr
        by_cases hcons : ∃ r ∈ S, 0 < N.pre v r
        · obtain ⟨r, hr, hprer⟩ := hcons
          obtain ⟨hrR, hen'⟩ := htwin X hXQ v r hr hprer hv
          obtain ⟨hQ', hlt⟩ := hfire X hXQ r hrR hen'
          refine ⟨_, LTS.Reachable.of_step ⟨hen', rfl⟩, hQ', ?_⟩
          rw [pot_congr (M' := M) fun r hr => hagree r (Finset.mem_sdiff.1 hr).1] at hlt
          exact hlt
        · push Not at hcons
          have hv0 : ∀ r ∈ S, N.pre v r = 0 := fun r hr => by have := hcons r hr; omega
          obtain ⟨M'', hr'', hQ'', hlt⟩ := ih fun r hr => by
            rw [fire_eq_of_not_consume hS hv0 r hr, hagree r hr]
          exact ⟨M'', (LTS.Reachable.of_step (A := N.lts) (l := v) ⟨hv, rfl⟩).trans hr'', hQ'', hlt⟩
    exact key M hr fun _ _ => rfl
  -- hence a marking emptying `S` is reachable
  have hempty : ∀ n, ∀ M, pot R ρ M = n → N.lts.Reachable M₀ M → (∀ q ∈ Q, M q = 0) →
      ∃ M', N.lts.Reachable M M' ∧ ∀ q ∈ S, M' q = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro M hn hr hM
      by_cases hR : ∀ p ∈ R, M p = 0
      · refine ⟨M, LTS.Reachable.refl _, fun q hq => ?_⟩
        by_cases hqQ : q ∈ Q
        · exact hM q hqQ
        · exact hR q (Finset.mem_sdiff.2 ⟨hq, hqQ⟩)
      · push Not at hR
        obtain ⟨p, hp, hMp⟩ := hR
        obtain ⟨hpS, hpQ⟩ := Finset.mem_sdiff.1 hp
        obtain ⟨M₁, hr₁, hen₁⟩ := hlive (α p) M hr
        obtain ⟨M'', hr'', hQ'', hlt⟩ :=
          hwalk M M₁ hM hr₁ (α p) p hpS (hαpre p hpS hpQ) (lts_enabled_iff.1 hen₁)
        obtain ⟨M', hr', hS'⟩ := ih _ (hn ▸ hlt) M'' rfl (hr.trans hr'') hQ''
        exact ⟨M', hr''.trans hr', hS'⟩
  obtain ⟨M', hr', hS'⟩ := hempty _ M₀ rfl (LTS.Reachable.refl _) hQ0
  -- a transition consuming from `S`
  obtain ⟨p, hp⟩ := hne
  obtain ⟨t, q, hq, hpre⟩ : ∃ t q, q ∈ S ∧ 0 < N.pre t q := by
    rcases hconn p with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t, p, hp, ht⟩
    · obtain ⟨q, hq, hpre⟩ := hS t ⟨p, hp, ht⟩
      exact ⟨t, q, hq, hpre⟩
  obtain ⟨M'', hr'', hen''⟩ := hlive t M' hr'
  have h0 := hS.empty_reachable hS' hr'' q hq
  have := (lts_enabled_iff.1 hen'') q
  omega

/-- **Commoner's theorem.**  An ordinary free-choice net without isolated places is live iff
every non-empty siphon contains an initially marked trap. -/
theorem live_iff_siphonTrap (hord : N.Ordinary) (hfc : N.FreeChoice)
    (hconn : ∀ p, (∃ t, 0 < N.pre t p) ∨ ∃ t, 0 < N.post t p) {M₀ : Marking P} :
    N.lts.Live M₀ ↔ N.SiphonTrapProperty M₀ :=
  ⟨siphonTrap_of_live hord hfc hconn, live_of_siphonTrap hord hfc⟩

end Net

end AsyncLean
