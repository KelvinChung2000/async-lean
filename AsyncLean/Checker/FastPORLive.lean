/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.FastPOR
import AsyncLean.Petri.StubbornLive

/-!
# Full correctness by partial-order reduction, checked by the kernel

`PNet.checkPORc` checks a reduced state space for all three properties at once.  Every
marking `m` of the certificate comes with the members of its stubborn set, a rank `r`, a
distance `dd` for the cycle proviso and a distance `ld` for liveness.  The kernel checks:

* the stubborn-set conditions, as for deadlock freedom (`PNet.checkPOR`), and that the
  markings reached by the enabled members are present, without overflow;
* *visibility*: a set with an enabled external member contains every external transition,
  and a marking with an enabled internal transition has an enabled internal member;
* the rank decreases along every enabled internal member (livelock freedom);
* the *cycle proviso*: if `dd = 0` every enabled transition is a member (the marking is
  fully expanded), otherwise some enabled member decreases `dd`;
* liveness: the marking is a hub or some enabled member decreases `ld`; from every hub, a
  trace of transitions (simulated by the kernel) enables each transition.

`PNet.correct_of_checkPORc` combines `Net.deadlockFree_of_stubborn`,
`Net.livelockFree_of_stubborn` and `Net.live_of_stubborn`.
-/

namespace AsyncLean

namespace PNet

open Fast

/-- Data of a marking: members of its stubborn set, rank, proviso distance, liveness
distance. -/
abbrev PData := List ℕ × ℕ × ℕ × ℕ

variable (N : PNet)

/-- Mask of the external transitions. -/
def xmask : ℕ := maskWhere (fun t => !t.internal) N.trans 0

section Checks

variable (fm B : ℕ) (t : BTree (ℕ × PData)) (tt : BTree (ℕ × SEntry))

/-- The marking reached from `m` by the transition of entry `e`. -/
def nextM (m : ℕ) (e : SEntry) : ℕ := m + e.1.2.2.1 - e.1.2.1

/-- The checks for one member `i` of the stubborn set (mask `S`) at `m` of rank `r`. -/
noncomputable def memberOk (imask m S r i : ℕ) : Bool :=
  match kfind i tt with
  | none => false
  | some e =>
    if fEnabled fm m e.1.1 then
      subMask e.2.1 S && fOk fm B m e.1.2.2.2 &&
        match kfind (nextM m e) t with
        | none => false
        | some y => !ktest imask i || Nat.blt y.2.1 r
    else
      kany e.2.2 fun c => Nat.blt (fld fm m c.1) c.2.1 && subMask c.2.2 S

/-- Member `i` is enabled at `m` and satisfies `q` (on its entry and its successor's data). -/
noncomputable def memberWith (m i : ℕ) (q : SEntry → PData → Bool) : Bool :=
  match kfind i tt with
  | none => false
  | some e => fEnabled fm m e.1.1 && match kfind (nextM m e) t with
    | none => false
    | some y => q e y

/-- The checks at one marking `x = (m, members, rank, dd, ld)`; `tl` is the indexed table,
`hubs` the hubs. -/
noncomputable def nodeOkC (ll : Bool) (imask xm : ℕ) (tl : List (ℕ × SEntry)) (hubs : List ℕ)
    (x : ℕ × PData) : Bool :=
  let m := x.1
  let Sl := x.2.1
  let S := kmaskL Sl
  -- the stubborn-set conditions, the successors and the rank
  kall Sl (memberOk fm B t tt imask m S x.2.2.1) &&
  -- some member is enabled
  kany Sl (fun i => memberWith fm t tt m i fun _ _ => true) &&
  -- visibility (for livelock freedom)
  (!ll || (kall Sl fun i => !memberWith fm t tt m i fun _ _ => !ktest imask i) || subMask xm S) &&
  (!ll || (kany Sl fun i => memberWith fm t tt m i fun _ _ => ktest imask i) ||
    kall tl fun ie => !ktest imask ie.1 || !fEnabled fm m ie.2.1.1) &&
  -- the cycle proviso
  (if x.2.2.2.1 = 0 then kall tl fun ie => ktest S ie.1 || !fEnabled fm m ie.2.1.1
   else kany Sl fun i => memberWith fm t tt m i fun _ y => Nat.blt y.2.2.1 x.2.2.2.1) &&
  -- progress towards a hub
  (kany hubs (fun h => Nat.beq h m) ||
    kany Sl fun i => memberWith fm t tt m i fun _ y => Nat.blt y.2.2.2 x.2.2.2.2)

/-- Simulate a trace of transitions from `m`. -/
noncomputable def simTrace : ℕ → List ℕ → Option ℕ
  | m, [] => some m
  | m, j :: js => match kfind j tt with
    | none => none
    | some e => if fEnabled fm m e.1.1 && fOk fm B m e.1.2.2.2 then simTrace (nextM m e) js
      else none

/-- The traces of a hub `h`, the `i`-th enabling transition `i`. -/
noncomputable def hubOk (h : ℕ) : List (List ℕ) → ℕ → Bool
  | [], _ => true
  | tr :: trs, i => (match simTrace fm B tt h tr with
      | none => false
      | some m' => match kfind i tt with
        | none => false
        | some e => fEnabled fm m' e.1.1) && hubOk h trs (i + 1)

end Checks

/-- **The reduced-state-space check** for deadlock freedom, liveness and, with `ll`, livelock
freedom. -/
noncomputable def checkPORc (ll : Bool) (w B fm : ℕ) (tl : List (ℕ × SEntry))
    (tt : BTree (ℕ × SEntry)) (imask xm s₀ : ℕ) (t : BTree (ℕ × PData))
    (hubs : List (ℕ × List (List ℕ))) : Bool :=
  N.wf && Nat.beq B (2 ^ w) && Nat.beq fm (B - 1) &&
    kbeqList ieq tl (indexed (N.stable w) 0) && kbeqList ieq tt.toList tl &&
    Nat.beq imask (cond ll N.imask 0) && Nat.beq xm N.xmask &&
    Nat.beq s₀ (encW w N.init) && N.init.all (fun x => decide (x < B)) &&
    (kfind s₀ t).isSome &&
    ktall t (nodeOkC fm B t tt ll imask xm tl (hubs.map Prod.fst)) &&
    kall hubs (fun h => Nat.beq h.2.length N.trans.length && hubOk fm B tt h.1 h.2 0)

end PNet

end AsyncLean

/-! ### Soundness -/

namespace AsyncLean

namespace PNet

open Fast

variable {N : PNet}

theorem testBit_xmask {t : Fin N.trans.length} :
    N.xmask.testBit t.val = true ↔ (N.tr t).internal = false := by
  rw [xmask, testBit_maskWhere]
  constructor
  · rintro ⟨j, hj, h, hq⟩
    simp only [Nat.zero_add] at h
    subst h
    simpa [tr] using hq
  · intro h
    exact ⟨t.val, t.isLt, by simp, by simpa [tr] using h⟩

theorem mem_indexed_of_lt {α : Type*} (l : List α) (i : ℕ) (j : ℕ) (hj : j < l.length) :
    (i + j, l[j]) ∈ indexed l i := by
  induction l generalizing i j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => simp [indexed]
    | succ j =>
      simp only [indexed, List.mem_cons]
      right
      have := ih (i + 1) j (by simpa using hj)
      rwa [show i + 1 + j = i + (j + 1) by omega] at this

section Specs

variable {fm B : ℕ} {t : BTree (ℕ × PData)} {tt : BTree (ℕ × SEntry)}

theorem memberOk_spec {imask m S r i : ℕ} (h : memberOk fm B t tt imask m S r i = true) :
    ∃ e, kfind i tt = some e ∧
      (fEnabled fm m e.1.1 = true → subMask e.2.1 S = true ∧ fOk fm B m e.1.2.2.2 = true ∧
        ∃ y, kfind (nextM m e) t = some y ∧ (ktest imask i = true → y.2.1 < r)) ∧
      (fEnabled fm m e.1.1 = false → ∃ c ∈ e.2.2,
        Nat.blt (fld fm m c.1) c.2.1 = true ∧ subMask c.2.2 S = true) := by
  unfold memberOk at h
  split at h
  · cases h
  · rename_i e he
    refine ⟨e, he, fun hen => ?_, fun hdis => ?_⟩
    · simp only [hen, ↓reduceIte] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨h1, h2, ?_⟩
      split at h3
      · cases h3
      · rename_i y hy
        refine ⟨y, hy, fun hi => ?_⟩
        simp only [hi, Bool.not_true, Bool.false_or] at h3
        exact blt_true h3
    · rw [hdis] at h
      simp only [Bool.false_eq_true, ↓reduceIte, kany_eq, List.any_eq_true,
        Bool.and_eq_true] at h
      obtain ⟨c, hc, h1, h2⟩ := h
      exact ⟨c, hc, h1, h2⟩

theorem memberWith_spec {m i : ℕ} {q : SEntry → PData → Bool}
    (h : memberWith fm t tt m i q = true) :
    ∃ e y, kfind i tt = some e ∧ fEnabled fm m e.1.1 = true ∧ kfind (nextM m e) t = some y ∧
      q e y = true := by
  unfold memberWith at h
  split at h
  · cases h
  · rename_i e he
    simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · cases h2
    · rename_i y hy
      exact ⟨e, y, he, h1, hy, h2⟩

theorem memberWith_of {m i : ℕ} {q : SEntry → PData → Bool} {e : SEntry} {y : PData}
    (he : kfind i tt = some e) (hen : fEnabled fm m e.1.1 = true)
    (hy : kfind (nextM m e) t = some y) (hq : q e y = true) :
    memberWith fm t tt m i q = true := by
  unfold memberWith
  rw [he]
  simp only [hen, hy, hq, Bool.and_self]

theorem hubOk_spec {h : ℕ} :
    ∀ {trs : List (List ℕ)} {i : ℕ}, hubOk fm B tt h trs i = true →
      ∀ j (hj : j < trs.length), ∃ m' e, simTrace fm B tt h trs[j] = some m' ∧
        kfind (i + j) tt = some e ∧ fEnabled fm m' e.1.1 = true
  | [], _, _, j, hj => by simp at hj
  | tr :: trs, i, hc, j, hj => by
    unfold hubOk at hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨h1, h2⟩ := hc
    cases j with
    | zero =>
      split at h1
      · cases h1
      · rename_i m' hm'
        split at h1
        · cases h1
        · rename_i e he
          exact ⟨m', e, hm', by simpa using he, h1⟩
    | succ j =>
      obtain ⟨m', e, h3, h4, h5⟩ := hubOk_spec h2 j (by simpa using hj)
      exact ⟨m', e, h3, by rwa [show i + (j + 1) = i + 1 + j by omega], h5⟩

end Specs

/-- **Correctness from a reduced state space**: deadlock freedom and liveness, and livelock
freedom when the visibility conditions were checked (`ll`). -/
theorem of_checkPORc {ll : Bool} {w B fm imask xm s₀ : ℕ} {tl : List (ℕ × SEntry)}
    {tt : BTree (ℕ × SEntry)} {t : BTree (ℕ × PData)} {hubs : List (ℕ × List (List ℕ))}
    (h : N.checkPORc ll w B fm tl tt imask xm s₀ t hubs = true) :
    N.toNet.lts.DeadlockFree N.M₀ ∧ (ll = true → N.toNet.lts.LivelockFree N.Internal N.M₀) ∧
      N.toNet.lts.Live N.M₀ := by
  classical
  simp only [checkPORc, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwf, hB⟩, hfm⟩, htl⟩, htt⟩, him⟩, hxm⟩, hs₀⟩, hinit⟩, h₀⟩, hall⟩, hhubs⟩ := h
  rw [Nat.eq_of_beq_eq_true hB] at hfm hinit hall hhubs
  rw [Nat.eq_of_beq_eq_true hfm] at hall hhubs
  rw [Nat.eq_of_beq_eq_true him, Nat.eq_of_beq_eq_true hxm] at hall
  -- with `ll`, the internal transitions are those of the net; otherwise none counts
  let im := cond ll N.imask 0
  rw [ktall_iff] at hall
  have htl' := eq_of_kbeqList (fun _ _ => eq_of_ieq) htl
  have htt' := eq_of_kbeqList (fun _ _ => eq_of_ieq) htt
  have hlen : (N.stable w).length = N.trans.length := by simp [stable]
  have hentry : ∀ i e, kfind i tt = some e → ∃ hi : i < N.trans.length, e = N.sentry w (N.tr ⟨i, hi⟩) := by
    intro i e hf
    have := mem_of_kfind hf
    rw [htt', htl'] at this
    obtain ⟨j, hj, rfl, rfl⟩ := mem_indexed this
    rw [hlen] at hj
    exact ⟨by omega, by simp [stable, tr]⟩
  have hfind : ∀ k (hk : k < N.trans.length), (k, N.sentry w (N.tr ⟨k, hk⟩)) ∈ tl := by
    intro k hk
    rw [htl']
    have := mem_indexed_of_lt (N.stable w) 0 k (by rw [hlen]; exact hk)
    simpa [stable, tr] using this
  -- the encoding of abstract markings
  let e : Marking (Fin N.places) → ℕ := fun M => encW w (N.enc M)
  let Good : Marking (Fin N.places) → Prop := fun M => ∀ p, M p < 2 ^ w
  have hgood : ∀ M, Good M → ∀ x ∈ N.enc M, x < 2 ^ w := by
    intro M hg x hx
    simp only [enc, List.mem_ofFn] at hx
    obtain ⟨p, rfl⟩ := hx
    exact hg p
  have hfield : ∀ M, Good M → ∀ q (hq : q < N.places),
      fld (2 ^ w - 1) (e M) (w * q) = M ⟨q, hq⟩ := by
    intro M hg q hq
    rw [fld, field_eq, encW_field (hgood M hg), getD_enc M q hq]
  have hlenc : ∀ M : Marking (Fin N.places), (N.enc M).length = N.places := by simp [enc]
  have hen : ∀ M (t' : Fin N.trans.length), Good M →
      (fEnabled (2 ^ w - 1) (e M) (N.sentry w (N.tr t')).1.1 = true ↔ N.toNet.Enabled M t') := by
    intro M t' hg
    simp only [sentry]
    rw [fEnabled_spec (hgood M hg), enabledL_enc_iff ((wf_spec hwf).2 t').1]
  have hfire : ∀ M (t' : Fin N.trans.length), Good M → N.toNet.Enabled M t' →
      nextM (e M) (N.sentry w (N.tr t')) = e (N.toNet.fire M t') := by
    intro M t' hg he
    simp only [nextM, e, sentry]
    rw [← fireL_enc]
    exact encW_fire w _ _ ((enabledL_enc_iff ((wf_spec hwf).2 t').1).2 he)
      (fun p hp => (hlenc M).symm ▸ ((wf_spec hwf).2 t').1 p hp)
      (fun p hp => (hlenc M).symm ▸ ((wf_spec hwf).2 t').2 p hp)
  have hgoodFire : ∀ M (t' : Fin N.trans.length), Good M →
      fOk (2 ^ w - 1) (2 ^ w) (e M) (N.sentry w (N.tr t')).1.2.2.2 = true →
      Good (N.toNet.fire M t') := by
    intro M t' hg hok p
    have := fOk_spec (hgood M hg) (N.tr t') hok
    rw [fireL_enc] at this
    exact this _ (by simp only [enc, List.mem_ofFn]; exact ⟨p, rfl⟩)
  have hint : ll = true → ∀ t' : Fin N.trans.length, ktest im t'.val = true ↔ N.Internal t' := by
    intro hll t'; simp only [im, hll, Bool.cond_true]; rw [ktest_eq, testBit_imask]; rfl
  -- the data of a marking
  let D : Marking (Fin N.places) → Option PData := fun M => kfind (e M) t
  let Sl : Marking (Fin N.places) → List ℕ := fun M => ((D M).map (·.1)).getD []
  let r : Marking (Fin N.places) → ℕ := fun M => ((D M).map (·.2.1)).getD 0
  let dd : Marking (Fin N.places) → ℕ := fun M => ((D M).map (·.2.2.1)).getD 0
  let ld : Marking (Fin N.places) → ℕ := fun M => ((D M).map (·.2.2.2)).getD 0
  let Inv : Marking (Fin N.places) → Prop := fun M => Good M ∧ ∃ x, D M = some x
  have hnode : ∀ M, Inv M → nodeOkC (2 ^ w - 1) (2 ^ w) t tt ll im N.xmask tl
      (hubs.map Prod.fst) (e M, (Sl M, r M, dd M, ld M)) = true := by
    rintro M ⟨-, x, hx⟩
    have := hall _ (mem_of_kfind hx)
    simpa [Sl, r, dd, ld, D, hx, im] using this
  -- members of the stubborn sets
  have hmem : ∀ M, Inv M → ∀ k ∈ Sl M, ∃ hk : k < N.trans.length,
      kfind k tt = some (N.sentry w (N.tr ⟨k, hk⟩)) ∧
      (N.toNet.Enabled M ⟨k, hk⟩ → subMask (N.cmask (N.tr ⟨k, hk⟩)) (kmaskL (Sl M)) = true ∧
        Good (N.toNet.fire M ⟨k, hk⟩) ∧
        (∃ y, kfind (nextM (e M) (N.sentry w (N.tr ⟨k, hk⟩))) t = some y) ∧
        (ll = true → N.Internal ⟨k, hk⟩ → r (N.toNet.fire M ⟨k, hk⟩) < r M)) ∧
      (¬ N.toNet.Enabled M ⟨k, hk⟩ → ∃ c ∈ (N.sentry w (N.tr ⟨k, hk⟩)).2.2,
        Nat.blt (fld (2 ^ w - 1) (e M) c.1) c.2.1 = true ∧
          subMask c.2.2 (kmaskL (Sl M)) = true) := by
    intro M hI k hk
    have hn := hnode M hI
    simp only [nodeOkC, Bool.and_eq_true, kall_eq, List.all_eq_true] at hn
    obtain ⟨en, hf, h1, h2⟩ := memberOk_spec (hn.1.1.1.1.1 k hk)
    obtain ⟨hk', rfl⟩ := hentry k en hf
    refine ⟨hk', hf, fun he => ?_, fun hne => h2 ?_⟩
    · obtain ⟨hsub, hok, y, hy, hr⟩ := h1 ((hen M _ hI.1).2 he)
      refine ⟨hsub, hgoodFire M _ hI.1 hok, ⟨y, hy⟩, fun hll hi => ?_⟩
      rw [hfire M _ hI.1 he] at hy
      simp only [r, D, hy, Option.map_some, Option.getD_some]
      exact hr ((hint hll _).2 hi)
    · cases hb : fEnabled (2 ^ w - 1) (e M) (N.sentry w (N.tr ⟨k, hk'⟩)).1.1
      · rfl
      · exact absurd ((hen M _ hI.1).1 hb) hne
  -- an enabled member with property `q`
  have hwith : ∀ M, Inv M → ∀ k (q : SEntry → PData → Bool),
      memberWith (2 ^ w - 1) t tt (e M) k q = true → ∃ hk : k < N.trans.length,
        N.toNet.Enabled M ⟨k, hk⟩ ∧ ∃ y, D (N.toNet.fire M ⟨k, hk⟩) = some y ∧
          q (N.sentry w (N.tr ⟨k, hk⟩)) y = true := by
    intro M hI k q hq
    obtain ⟨en, y, hf, he, hy, hq⟩ := memberWith_spec hq
    obtain ⟨hk, rfl⟩ := hentry k en hf
    have he' := (hen M _ hI.1).1 he
    rw [hfire M _ hI.1 he'] at hy
    exact ⟨hk, he', y, hy, hq⟩
  have hwith' : ∀ M, Inv M → ∀ k ∈ Sl M, ∀ (hk : k < N.trans.length)
      (q : SEntry → PData → Bool), N.toNet.Enabled M ⟨k, hk⟩ →
      (∀ y, D (N.toNet.fire M ⟨k, hk⟩) = some y → q (N.sentry w (N.tr ⟨k, hk⟩)) y = true) →
      memberWith (2 ^ w - 1) t tt (e M) k q = true := by
    intro M hI k hkS hk q he hq
    obtain ⟨hk', hf, h1, -⟩ := hmem M hI k hkS
    obtain ⟨-, -, ⟨y, hy⟩, -⟩ := h1 he
    refine memberWith_of hf ((hen M _ hI.1).2 he) hy (hq y ?_)
    rw [← hy, hfire M _ hI.1 he]
  -- the reduced semantics
  let S : Marking (Fin N.places) → Fin N.trans.length → Prop := fun M t' => t'.val ∈ Sl M
  have hstep : ∀ M t', Inv M → S M t' → N.toNet.Enabled M t' → Inv (N.toNet.fire M t') := by
    intro M t' hI hS he
    obtain ⟨hk, -, h1, -⟩ := hmem M hI t'.val hS
    obtain ⟨-, hg, ⟨y, hy⟩, -⟩ := h1 he
    refine ⟨hg, y, ?_⟩
    rw [← hy, hfire M _ hI.1 he]
  have hprog : ∀ M, Inv M → ∃ t', S M t' ∧ N.toNet.Enabled M t' := by
    intro M hI
    have hn := hnode M hI
    simp only [nodeOkC, Bool.and_eq_true, kany_eq, List.any_eq_true] at hn
    obtain ⟨k, hk, hw⟩ := hn.1.1.1.1.2
    obtain ⟨hk', he, -⟩ := hwith M hI k _ hw
    exact ⟨⟨k, hk'⟩, hk, he⟩
  have hst : ∀ M, Inv M → N.toNet.Stubborn M (S M) := by
    intro M hI
    refine ⟨fun t₁ hS₁ he₁ t₂ hS₂ p hp => ?_, fun t₁ hS₁ hne₁ => ?_, fun _ => hprog M hI⟩
    · obtain ⟨_, _, h1, _⟩ := hmem M hI t₁.val hS₁
      obtain ⟨hsub, -⟩ := h1 he₁
      by_contra hp₂
      apply hS₂
      show t₂.val ∈ Sl M
      rw [← testBit_kmaskL]
      refine testBit_of_subMask hsub (testBit_cmask.2 ⟨p.val, ?_, ?_⟩)
      · exact List.count_pos_iff.1 (Nat.pos_of_ne_zero hp)
      · exact List.count_pos_iff.1 (Nat.pos_of_ne_zero hp₂)
    · obtain ⟨_, _, _, h2⟩ := hmem M hI t₁.val hS₁
      obtain ⟨c, hc, hlt, hsub⟩ := h2 hne₁
      simp only [sentry, List.mem_map] at hc
      obtain ⟨q, hq, rfl⟩ := hc
      have hqp : q < N.places := ((wf_spec hwf).2 t₁).1 q hq
      refine ⟨⟨q, hqp⟩, ?_, fun t₂ hS₂ => ?_⟩
      · rw [← hfield M hI.1 q hqp]
        exact blt_true hlt
      · change (N.tr t₂).post.count q = 0
        refine List.count_eq_zero_of_not_mem fun hm => hS₂ ?_
        show t₂.val ∈ Sl M
        rw [← testBit_kmaskL]
        exact testBit_of_subMask hsub (testBit_prodMask.2 hm)
  have hinv₀ : Inv N.M₀ := by
    refine ⟨fun p => ?_, ?_⟩
    · have := List.all_eq_true.1 hinit (N.init.getD p.val 0) (by
        rw [List.getD_eq_getElem _ _ (by rw [(wf_spec hwf).1]; exact p.isLt)]
        exact List.getElem_mem _)
      simpa [M₀] using this
    · show ∃ x, kfind (e N.M₀) t = some x
      rw [show e N.M₀ = s₀ by simp only [e, enc_M₀ hwf]; exact (Nat.eq_of_beq_eq_true hs₀).symm]
      exact Option.isSome_iff_exists.1 h₀
  refine ⟨Net.deadlockFree_of_stubborn S Inv hinv₀ hstep hst hprog, fun hll => ?_, ?_⟩
  · -- livelock freedom
    refine Net.livelockFree_of_stubborn N.Internal S Inv r hinv₀ hstep hst ?_ ?_ ?_
    · -- visibility: a set with an enabled external member contains every external transition
      intro M hI t₁ hS₁ he₁ hi₁ t₂ hi₂
      have hn := hnode M hI
      simp only [nodeOkC, hll, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
        kall_eq, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hn
      rcases hn.1.1.1.2 with hall' | hsub
      · have := hall' t₁.val hS₁
        rw [hwith' M hI t₁.val hS₁ t₁.isLt _ he₁ fun _ _ => by
          simpa using fun h => hi₁ ((hint hll t₁).1 h)] at this
        cases this
      · show t₂.val ∈ Sl M
        rw [← testBit_kmaskL]
        refine testBit_of_subMask hsub ?_
        rw [testBit_xmask]
        cases h : (N.tr t₂).internal
        · rfl
        · exact absurd h hi₂
    · -- an enabled internal transition gives an enabled internal member
      rintro M hI ⟨t₁, hi₁, he₁⟩
      have hn := hnode M hI
      simp only [nodeOkC, hll, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
        kany_eq, List.any_eq_true, kall_eq, List.all_eq_true] at hn
      rcases hn.1.1.2 with ⟨k, hk, hw⟩ | hscan
      · obtain ⟨hk', he, -, -, hq⟩ := hwith M hI k _ hw
        exact ⟨⟨k, hk'⟩, hk, (hint hll _).1 hq, he⟩
      · have := hscan _ (hfind t₁.val t₁.isLt)
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
        rcases this with h | h
        · exact absurd ((hint hll t₁).2 hi₁) (by simp [h])
        · exact absurd ((hen M t₁ hI.1).2 he₁) (by simp [h])
    · intro M t₁ hI hS₁ he₁ hi₁
      obtain ⟨_, _, h1, _⟩ := hmem M hI t₁.val hS₁
      exact (h1 he₁).2.2.2 hll hi₁
  · -- liveness
    refine Net.live_of_stubborn S dd Inv hinv₀ hstep hst ?_ ?_
    · -- the cycle proviso
      intro M hI
      have hn := hnode M hI
      simp only [nodeOkC, Bool.and_eq_true] at hn
      have hp := hn.1.2
      split_ifs at hp with hd
      · left
        intro t₁ he₁
        simp only [kall_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
          Bool.not_true] at hp
        rcases hp _ (hfind t₁.val t₁.isLt) with h | h
        · show t₁.val ∈ Sl M
          rw [← testBit_kmaskL, ← ktest_eq]
          exact h
        · exact absurd ((hen M t₁ hI.1).2 he₁) (by simp [h])
      · right
        simp only [kany_eq, List.any_eq_true] at hp
        obtain ⟨k, hk, hw⟩ := hp
        obtain ⟨hk', he, y, hy, hq⟩ := hwith M hI k _ hw
        refine ⟨⟨k, hk'⟩, hk, he, ?_⟩
        simp only [dd, hy, Option.map_some, Option.getD_some]
        exact blt_true hq
    · -- every transition can be enabled again: reach a hub, then follow its trace
      have htrace : ∀ (tr : List ℕ) (M : Marking (Fin N.places)) (m' : ℕ), Good M →
          simTrace (2 ^ w - 1) (2 ^ w) tt (e M) tr = some m' →
          ∃ M', N.toNet.lts.Reachable M M' ∧ Good M' ∧ e M' = m' := by
        intro tr
        induction tr with
        | nil =>
          intro M m' hg h
          cases h
          exact ⟨M, LTS.Reachable.refl _, hg, rfl⟩
        | cons j js ih =>
          intro M m' hg h
          unfold simTrace at h
          split at h
          · cases h
          · rename_i en hf
            obtain ⟨hj, rfl⟩ := hentry j en hf
            split_ifs at h with hc
            simp only [Bool.and_eq_true] at hc
            have he := (hen M _ hg).1 hc.1
            rw [hfire M _ hg he] at h
            obtain ⟨M', h₁, h₂, h₃⟩ := ih _ m' (hgoodFire M _ hg hc.2) h
            exact ⟨M', LTS.Reachable.head ⟨_, he, rfl⟩ h₁, h₂, h₃⟩
      intro M hI t₁
      suffices H : ∀ n M, Inv M → ld M = n →
          ∃ M', N.toNet.lts.Reachable M M' ∧ N.toNet.Enabled M' t₁ from H _ M hI rfl
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro M hI hn
        have hnd := hnode M hI
        simp only [nodeOkC, Bool.and_eq_true, Bool.or_eq_true, kany_eq, List.any_eq_true] at hnd
        rcases hnd.2 with ⟨hb, hbm, hbe⟩ | ⟨k, hk, hw⟩
        · -- a hub: follow its trace for `t₁`
          simp only [List.mem_map] at hbm
          obtain ⟨⟨h', trs⟩, hmemh, rfl⟩ := hbm
          have hhb := List.all_eq_true.1 (by rw [← kall_eq]; exact hhubs) _ hmemh
          simp only [Bool.and_eq_true] at hhb
          obtain ⟨hlen', hok⟩ := hhb
          obtain ⟨m', en, hsim, hf, hen'⟩ :=
            hubOk_spec hok t₁.val (by rw [Nat.eq_of_beq_eq_true hlen']; exact t₁.isLt)
          have hhe : h' = e M := Nat.eq_of_beq_eq_true hbe
          rw [hhe] at hsim
          obtain ⟨M', h₁, h₂, rfl⟩ := htrace _ M m' hI.1 hsim
          obtain ⟨hk, rfl⟩ := hentry _ en hf
          have ht₁ : (⟨0 + t₁.val, hk⟩ : Fin N.trans.length) = t₁ := Fin.ext (Nat.zero_add _)
          rw [ht₁] at hen'
          exact ⟨M', h₁, (hen M' _ h₂).1 hen'⟩
        · -- progress towards a hub
          obtain ⟨hk', he, y, hy, hq⟩ := hwith M hI k _ hw
          have hI' := hstep M ⟨k, hk'⟩ hI hk he
          have hlt : ld (N.toNet.fire M ⟨k, hk'⟩) < n := by
            rw [← hn]
            simp only [ld, hy, Option.map_some, Option.getD_some]
            exact blt_true hq
          obtain ⟨M', h₁, h₂⟩ := ih _ hlt _ hI' rfl
          exact ⟨M', LTS.Reachable.head ⟨_, he, rfl⟩ h₁, h₂⟩

end PNet

end AsyncLean

namespace AsyncLean

namespace PNet

variable {N : PNet}

/-- **Full correctness from a reduced state space with the visibility conditions.** -/
theorem correct_of_checkPORc {w B fm imask xm s₀ : ℕ} {tl : List (ℕ × SEntry)}
    {tt : BTree (ℕ × SEntry)} {t : BTree (ℕ × PData)} {hubs : List (ℕ × List (List ℕ))}
    (h : N.checkPORc true w B fm tl tt imask xm s₀ t hubs = true) : N.Correct :=
  let h := of_checkPORc h
  ⟨h.1, h.2.1 rfl, h.2.2⟩

/-- **Full correctness** from a reduced state space for deadlock freedom and liveness, and
livelock freedom proved otherwise. -/
theorem correct_of_checkPORc_lf {w B fm imask xm s₀ : ℕ} {tl : List (ℕ × SEntry)}
    {tt : BTree (ℕ × SEntry)} {t : BTree (ℕ × PData)} {hubs : List (ℕ × List (List ℕ))}
    (h : N.checkPORc false w B fm tl tt imask xm s₀ t hubs = true)
    (hlf : N.toNet.lts.LivelockFree N.Internal N.M₀) : N.Correct :=
  let h := of_checkPORc h
  ⟨h.1, hlf, h.2.2⟩

theorem live_of_checkPORc {ll : Bool} {w B fm imask xm s₀ : ℕ} {tl : List (ℕ × SEntry)}
    {tt : BTree (ℕ × SEntry)} {t : BTree (ℕ × PData)} {hubs : List (ℕ × List (List ℕ))}
    (h : N.checkPORc ll w B fm tl tt imask xm s₀ t hubs = true) : N.toNet.lts.Live N.M₀ :=
  (of_checkPORc h).2.2

theorem livelockFree_of_checkPORc {w B fm imask xm s₀ : ℕ} {tl : List (ℕ × SEntry)}
    {tt : BTree (ℕ × SEntry)} {t : BTree (ℕ × PData)} {hubs : List (ℕ × List (List ℕ))}
    (h : N.checkPORc true w B fm tl tt imask xm s₀ t hubs = true) :
    N.toNet.lts.LivelockFree N.Internal N.M₀ :=
  (of_checkPORc h).2.1 rfl

variable (N) in
/-- The net has no internal transition. -/
def noInternal : Bool := N.trans.all fun t => !t.internal

/-- A net without internal transitions is livelock free. -/
theorem livelockFree_of_noInternal (h : N.noInternal = true) :
    N.toNet.lts.LivelockFree N.Internal N.M₀ :=
  LTS.LivelockFree.of_no_internal fun t ht => by
    have := List.all_eq_true.1 h (N.tr t) (List.getElem_mem _)
    simp only [Internal] at ht
    simp [ht] at this

end PNet

end AsyncLean

/-! ### Untrusted generation -/

namespace AsyncLean

namespace PNet

/-- Close the set `S₀` (a bit mask) under the stubborn-set rules (untrusted). -/
def closeSet (fm m : ℕ) (tb : Array SEntry) (en : Array Bool) (S₀ : ℕ) : ℕ := Id.run do
  let n := tb.size
  let mut S : ℕ := S₀
  let mut work : Array ℕ := ((List.range n).filter S₀.testBit).toArray
  while work.size > 0 do
    let i := work.back!
    work := work.pop
    let e := tb[i]!
    let add : ℕ :=
      if en[i]! then e.2.1
      else
        let cands := e.2.2.filter fun c => (m >>> c.1) &&& fm < c.2.1
        match cands with
        | [] => 0
        | c :: cs => (cs.foldl (fun (best : ℕ × ℕ) c' =>
            let k := popCount n (c'.2.2 ^^^ (c'.2.2 &&& S))
            if k < best.2 then (c'.2.2, k) else best)
            (c.2.2, popCount n (c.2.2 ^^^ (c.2.2 &&& S)))).1
    let new := add ^^^ (add &&& S)
    if new != 0 then
      S := S ||| new
      for j in [0:n] do
        if new.testBit j then work := work.push j
  return S

/-- A stubborn set satisfying the visibility conditions, with few enabled transitions
(untrusted). -/
def visibleStubborn (fm m imask xm : ℕ) (tb : Array SEntry) (en : Array Bool) : ℕ := Id.run do
  let n := tb.size
  let internalEn := (List.range n).filter fun i => en[i]! && imask.testBit i
  let fix (S : ℕ) : ℕ := Id.run do
    let mut S := S
    for _ in [0:3] do
      -- an enabled external member brings in every external transition
      if (List.range n).any (fun i => en[i]! && S.testBit i && !imask.testBit i) &&
          (xm &&& S) != xm then
        S := closeSet fm m tb en (S ||| xm)
      -- an enabled internal transition requires an enabled internal member
      if !internalEn.isEmpty && !internalEn.any S.testBit then
        S := closeSet fm m tb en (S ||| 2 ^ internalEn.head!)
    return S
  let seeds := if internalEn.isEmpty then (List.range n).filter (en[·]!) else internalEn
  let mut best : ℕ := 0
  let mut bestK := n + 1
  for i in seeds do
    let S := fix (closeSet fm m tb en (2 ^ i))
    let k := (List.range n).countP fun j => en[j]! && S.testBit j
    if k < bestK then
      best := S
      bestK := k
      if k ≤ 1 then break
  return best

variable (N : PNet)

/-- Explore the reduced state space for `checkPORc` with fields of `w` bits (untrusted). -/
def porcExplore (ll : Bool) (w fuel : ℕ) :
    Except String (List (ℕ × PData) × List (ℕ × List (List ℕ))) := do
  let B := 2 ^ w
  let fm := B - 1
  let tb := (N.stable w).toArray
  let n := tb.size
  let imask := cond ll N.imask 0
  let xm := N.xmask
  let enabled (m : ℕ) : Array Bool := tb.map fun e => e.1.1.all fun (sh, k) => k ≤ (m >>> sh) &&& fm
  let fire (m i : ℕ) : Except String ℕ := do
    let e := tb[i]!
    unless e.1.2.2.2.all (fun c => ((m >>> c.1) &&& fm) - c.2.1 + c.2.2 < B) do
      throw "overflow"
    return m + e.1.2.2.1 - e.1.2.1
  let s₀ := encW w N.init
  -- states, their sets (bit masks), and reduced edges (transition, target index)
  let mut idx : Std.HashMap ℕ ℕ := ({} : Std.HashMap ℕ ℕ).insert s₀ 0
  let mut states : Array ℕ := #[s₀]
  let mut sets : Array ℕ := #[]
  let mut edges : Array (Array (ℕ × ℕ)) := #[]
  let mut full : Array Bool := #[]
  let mut qi := 0
  let full_ := 2 ^ n - 1
  -- `todo`: states whose set must be (re)computed, `forceFull`: states to expand fully
  let mut forceFull : Std.HashMap ℕ Unit := {}
  let mut rounds := 0
  while true do
    -- breadth-first exploration of the states not explored yet
    while qi < states.size do
      if states.size > fuel then throw "the reduced state space exceeds the fuel"
      let m := states[qi]!
      let en := enabled m
      unless en.any id do throw s!"deadlock at {m}"
      let S := if forceFull.contains qi then full_
        else if ll then visibleStubborn fm m imask xm tb en else bestStubborn fm m tb en
      let isFull := (List.range n).all fun i => !en[i]! || S.testBit i
      let mut out : Array (ℕ × ℕ) := #[]
      for i in [0:n] do
        if en[i]! && S.testBit i then
          let m' ← fire m i
          match idx[m']? with
          | some j => out := out.push (i, j)
          | none =>
            idx := idx.insert m' states.size
            out := out.push (i, states.size)
            states := states.push m'
      sets := sets.push S
      edges := edges.push out
      full := full.push isFull
      qi := qi + 1
    -- the cycle proviso: every state must reach a fully expanded one
    let k := states.size
    let mut preds : Array (Array ℕ) := Array.replicate k #[]
    for v in [0:k] do
      for (_, u) in edges[v]! do
        preds := preds.modify u (·.push v)
    let mut reach : Array Bool := full
    let mut queue : Array ℕ := ((List.range k).filter (full[·]!)).toArray
    let mut q := 0
    while q < queue.size do
      let v := queue[q]!
      q := q + 1
      for u in preds[v]! do
        unless reach[u]! do
          reach := reach.set! u true
          queue := queue.push u
    let bad := (List.range k).filter fun v => !reach[v]!
    if bad.isEmpty then break
    rounds := rounds + 1
    if rounds > 1000 then throw "the cycle proviso does not converge"
    -- fully expand one state of each terminal component of the unreached part
    let comp := Fast.sccs (edges.map fun es => es.filter fun e => !reach[e.2]!)
    let mut chosen : Std.HashMap ℕ Unit := {}
    for v in bad do
      let c := comp[v]!
      if !(chosen.contains c) && (bad.all fun u => comp[u]! != c ||
          edges[u]!.all fun e => reach[e.2]! || comp[e.2]! == c) then
        chosen := chosen.insert c ()
        forceFull := forceFull.insert v ()
    -- re-explore the chosen states
    let redo := (List.range k).filter fun v => forceFull.contains v && !full[v]!
    for v in redo do
      let m := states[v]!
      let en := enabled m
      let mut out : Array (ℕ × ℕ) := #[]
      for i in [0:n] do
        if en[i]! then
          let m' ← fire m i
          match idx[m']? with
          | some j => out := out.push (i, j)
          | none =>
            idx := idx.insert m' states.size
            out := out.push (i, states.size)
            states := states.push m'
      sets := sets.set! v full_
      edges := edges.set! v out
      full := full.set! v true
  let k := states.size
  -- the proviso distance: backward breadth-first search from the fully expanded states
  let inf := k + 1
  let bfsFrom (srcs : List ℕ) (ok : ℕ → ℕ → Bool) : Array ℕ := Id.run do
    let mut preds : Array (Array ℕ) := Array.replicate k #[]
    for v in [0:k] do
      for (i, u) in edges[v]! do
        if ok v i then preds := preds.modify u (·.push v)
    let mut dist := Array.replicate k inf
    let mut queue : Array ℕ := #[]
    for s in srcs do
      dist := dist.set! s 0
      queue := queue.push s
    let mut q := 0
    while q < queue.size do
      let v := queue[q]!
      q := q + 1
      for u in preds[v]! do
        if dist[u]! == inf then
          dist := dist.set! u (dist[v]! + 1)
          queue := queue.push u
    return dist
  let dd := bfsFrom ((List.range k).filter (full[·]!)) fun _ _ => true
  -- ranks along internal reduced edges
  let some rank := Fast.ranks (edges.map fun es => es) (fun l => imask.testBit l)
    | throw "livelock"
  -- hubs: one state per terminal component of the reduced graph
  let comp := Fast.sccs edges
  let ncomp := comp.foldl max 0 + 1
  let mut terminal : Array Bool := Array.replicate ncomp true
  for v in [0:k] do
    for (_, u) in edges[v]! do
      if comp[u]! != comp[v]! then terminal := terminal.set! comp[v]! false
  let mut rep : Array ℕ := Array.replicate ncomp k
  for v in [0:k] do
    if terminal[comp[v]!]! && rep[comp[v]!]! == k then rep := rep.set! comp[v]! v
  let hubIdx := rep.toList.filter (· < k)
  let ld := bfsFrom hubIdx fun _ _ => true
  -- from each hub, a trace of transitions enabling each transition: along reduced edges
  let mut hubs : List (ℕ × List (List ℕ)) := []
  for h in hubIdx do
    let mut parent : Array (ℕ × ℕ) := Array.replicate k (k, n)
    parent := parent.set! h (h, n)
    let mut order : Array ℕ := #[h]
    let mut found : Array (Option ℕ) := Array.replicate n none
    let mut oi := 0
    while oi < order.size && found.any Option.isNone do
      let v := order[oi]!
      oi := oi + 1
      let en := enabled states[v]!
      for i in [0:n] do
        if en[i]! && found[i]!.isNone then found := found.set! i (some v)
      for (i, u) in edges[v]! do
        if parent[u]!.1 == k then
          parent := parent.set! u (v, i)
          order := order.push u
    let mut trs : List (List ℕ) := []
    for i in [0:n] do
      let some v := found[i]! | throw s!"transition {i} is not live"
      let mut path : List ℕ := []
      let mut x := v
      let mut steps := 0
      while x != h && steps ≤ k do
        let (p, j) := parent[x]!
        path := j :: path
        x := p
        steps := steps + 1
      trs := trs ++ [path]
    hubs := hubs ++ [(states[h]!, trs)]
  let es := (List.range k).map fun v =>
    (states[v]!, (((List.range n).filter (sets[v]!).testBit), rank[v]!, dd[v]!, ld[v]!))
  return (es, hubs)

/-- Certificate for `checkPORc` (untrusted): width, reduced state space with data, hubs. -/
def mkPORcCert (ll : Bool) (fuel : ℕ := 1000000) :
    Except String (ℕ × BTree (ℕ × PData) × List (ℕ × List (List ℕ))) := do
  let maxArc := N.trans.foldl (fun a t => max a (max (t.pre.length) (t.post.length))) 1
  let maxInit := N.init.foldl max 1
  let w₀ := Nat.log2 (max maxArc maxInit) + 1
  let mut last := "no width"
  for w in [w₀, w₀ + 1, w₀ + 2, w₀ + 4, w₀ + 8, 32, 64] do
    match N.porcExplore ll w fuel with
    | .ok (es, hubs) =>
      let a := es.toArray.qsort (fun x y => x.1 < y.1)
      return (w, Fast.buildTree a (a.size + 1) 0 a.size, hubs)
    | .error "overflow" => last := "overflow"
    | .error e => throw e
  throw last

end PNet

end AsyncLean
