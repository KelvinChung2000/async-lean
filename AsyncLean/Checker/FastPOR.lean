/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.FastPetri
import AsyncLean.Petri.Stubborn

/-!
# Deadlock freedom by partial-order reduction, checked by the kernel

The certificate is a reduced state space: packed markings (`PNet.encW`), each with a
stubborn set given as a bit mask over the transitions.  At every marking of the certificate
the kernel checks that the set is stubborn (`Net.Stubborn`), with precomputed masks:

* an enabled transition `t` of the set must contain its *conflict mask* — the transitions
  sharing an input place with `t`;
* a disabled transition of the set must have an input place `p` holding too few tokens
  whose *producer mask* — the transitions putting tokens into `p` — is in the set;
* some transition of the set is enabled, and the markings reached by firing the enabled
  transitions of the set are in the certificate (without overflow).

`PNet.deadlockFree_of_checkPOR` then proves deadlock freedom of the whole net, by
`Net.deadlockFree_of_stubborn`.  For concurrent designs the reduced state space can be
exponentially smaller than the full one.
-/

namespace AsyncLean

namespace PNet

open Fast

variable (N : PNet)

/-- Bit mask of the transitions of `ts`, numbered from `i`, satisfying `q`. -/
def maskWhere (q : PTrans → Bool) : List PTrans → ℕ → ℕ
  | [], _ => 0
  | t :: ts, i => (if q t then 2 ^ i else 0) ||| maskWhere q ts (i + 1)

/-- Transitions sharing an input place with `t`. -/
def cmask (t : PTrans) : ℕ :=
  maskWhere (fun t' => t.pre.any fun p => t'.pre.contains p) N.trans 0

/-- Transitions putting tokens into place `p`. -/
def prodMask (p : ℕ) : ℕ := maskWhere (fun t' => t'.post.contains p) N.trans 0

/-- Table entry for the reduced search: the fast entry, the conflict mask, and the
candidate scapegoats (field shift, tokens needed, producer mask). -/
abbrev SEntry := FEntry × ℕ × List (ℕ × ℕ × ℕ)

/-- The table entry of `t`. -/
def sentry (w : ℕ) (t : PTrans) : SEntry :=
  (fentry w t, N.cmask t, t.pre.map fun p => (w * p, t.pre.count p, N.prodMask p))

/-- The table of the net. -/
def stable (w : ℕ) : List SEntry := N.trans.map (N.sentry w)

/-- Boolean equality of triples of numbers. -/
noncomputable def teq (x y : ℕ × ℕ × ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (Nat.beq x.2.2 y.2.2) (Nat.beq x.2.1 y.2.1))
    (Nat.beq x.1 y.1)

theorem eq_of_teq {x y : ℕ × ℕ × ℕ} (h : teq x y = true) : x = y := by
  unfold teq at h
  cases h1 : Nat.beq x.1 y.1 <;> rw [h1] at h
  · cases h
  cases h2 : Nat.beq x.2.1 y.2.1 <;> rw [h2] at h
  · cases h
  exact Prod.ext (Nat.eq_of_beq_eq_true h1)
    (Prod.ext (Nat.eq_of_beq_eq_true h2) (Nat.eq_of_beq_eq_true h))

/-- Boolean equality of table entries. -/
noncomputable def seq (a b : SEntry) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (kbeqList teq a.2.2 b.2.2) (Nat.beq a.2.1 b.2.1))
    (feq a.1 b.1)

theorem eq_of_seq {a b : SEntry} (h : seq a b = true) : a = b := by
  unfold seq at h
  cases h1 : feq a.1 b.1 <;> rw [h1] at h
  · cases h
  cases h2 : Nat.beq a.2.1 b.2.1 <;> rw [h2] at h
  · cases h
  exact Prod.ext (eq_of_feq h1)
    (Prod.ext (Nat.eq_of_beq_eq_true h2) (eq_of_kbeqList (fun _ _ => eq_of_teq) h))

/-- The tokens in the field at shift `sh`. -/
noncomputable def fld (fm m sh : ℕ) : ℕ := Nat.land (Nat.shiftRight m sh) fm

/-- `a ⊆ S` for bit masks. -/
noncomputable def subMask (a S : ℕ) : Bool := Nat.beq (Nat.land a S) a

/-- Bit mask of a list of indices. -/
noncomputable def kmaskL (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun i _ r => Nat.lor r (2 ^ i)) l

/-- A list with its indices, from `i`. -/
def indexed {α : Type*} : List α → ℕ → List (ℕ × α)
  | [], _ => []
  | x :: xs, i => (i, x) :: indexed xs (i + 1)

/-- Boolean equality of indexed table entries. -/
noncomputable def ieq (a b : ℕ × SEntry) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (seq a.2 b.2) (Nat.beq a.1 b.1)

/-- The checks at a marking `m` whose stubborn set has the members `Sl` and the mask `S`
(table entries are looked up in the tree `tt`); `found` records whether an enabled member
has been seen. -/
noncomputable def porNode (fm B : ℕ) (t : BTree (ℕ × List ℕ)) (tt : BTree (ℕ × SEntry))
    (m S : ℕ) (Sl : List ℕ) : Bool → Bool :=
  List.rec (motive := fun _ => Bool → Bool) (fun found => found)
    (fun i _ rec found => Option.rec (motive := fun _ => Bool) false
      (fun e => Bool.rec (motive := fun _ => Bool)
        -- disabled: a scapegoat
        (Bool.rec (motive := fun _ => Bool) false (rec found)
          (kany e.2.2 fun c => Bool.rec (motive := fun _ => Bool) false (subMask c.2.2 S)
            (Nat.blt (fld fm m c.1) c.2.1)))
        -- enabled: its conflicts are in the set, no overflow, and the successor is present
        (Bool.rec (motive := fun _ => Bool) false (rec true)
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (kfind (m + e.1.2.2.1 - e.1.2.1) t).isSome (fOk fm B m e.1.2.2.2))
            (subMask e.2.1 S)))
        (fEnabled fm m e.1.1))
      (kfind i tt)) Sl

/-- **The reduced-state-space check** for deadlock freedom: `tt` is the net's table indexed
by transition, `t` the reduced state space with the members of each stubborn set. -/
noncomputable def checkPOR (w B fm : ℕ) (tt : BTree (ℕ × SEntry)) (s₀ : ℕ)
    (t : BTree (ℕ × List ℕ)) : Bool :=
  N.wf && Nat.beq B (2 ^ w) && Nat.beq fm (B - 1) &&
    kbeqList ieq tt.toList (indexed (N.stable w) 0) &&
    Nat.beq s₀ (encW w N.init) && N.init.all (fun x => decide (x < B)) &&
    (kfind s₀ t).isSome && ktall t (fun x => porNode fm B t tt x.1 (kmaskL x.2) x.2 false)

/-! ### Soundness -/

variable {N}

theorem testBit_kmaskL {l : List ℕ} {j : ℕ} : (kmaskL l).testBit j = true ↔ j ∈ l := by
  induction l with
  | nil => simp [kmaskL]
  | cons i l ih =>
    change (Nat.lor (kmaskL l) (2 ^ i)).testBit j = true ↔ _
    rw [show Nat.lor (kmaskL l) (2 ^ i) = kmaskL l ||| 2 ^ i from rfl, Nat.testBit_lor,
      Nat.testBit_two_pow, Bool.or_eq_true, ih, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (h | rfl) <;> simp [*]
    · rintro (rfl | h) <;> simp [*]

theorem mem_indexed {α : Type*} {l : List α} {i k : ℕ} {e : α} (h : (k, e) ∈ indexed l i) :
    ∃ j, ∃ hj : j < l.length, k = i + j ∧ l[j] = e := by
  induction l generalizing i with
  | nil => simp [indexed] at h
  | cons x xs ih =>
    simp only [indexed, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨0, by simp, by simp, rfl⟩
    · obtain ⟨j, hj, rfl, he⟩ := ih h
      exact ⟨j + 1, by simpa using hj, by omega, by simpa using he⟩

theorem eq_of_ieq {a b : ℕ × SEntry} (h : ieq a b = true) : a = b := by
  unfold ieq at h
  cases h1 : Nat.beq a.1 b.1 <;> rw [h1] at h
  · cases h
  exact Prod.ext (Nat.eq_of_beq_eq_true h1) (eq_of_seq h)

theorem porNode_spec {fm B m S : ℕ} {t : BTree (ℕ × List ℕ)} {tt : BTree (ℕ × SEntry)} :
    ∀ {Sl : List ℕ} {found : Bool}, porNode fm B t tt m S Sl found = true →
      (∀ i ∈ Sl, ∃ e, kfind i tt = some e ∧
        (fEnabled fm m e.1.1 = true → subMask e.2.1 S = true ∧ fOk fm B m e.1.2.2.2 = true ∧
          (kfind (m + e.1.2.2.1 - e.1.2.1) t).isSome = true) ∧
        (fEnabled fm m e.1.1 = false → ∃ c ∈ e.2.2,
          Nat.blt (fld fm m c.1) c.2.1 = true ∧ subMask c.2.2 S = true)) ∧
      (found = true ∨ ∃ i ∈ Sl, ∃ e, kfind i tt = some e ∧ fEnabled fm m e.1.1 = true) := by
  intro Sl
  induction Sl with
  | nil => intro found h; exact ⟨by simp, Or.inl h⟩
  | cons i Sl ih =>
    intro found h
    change Option.rec (motive := fun _ => Bool) false
      (fun e => Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (porNode fm B t tt m S Sl found)
          (kany e.2.2 fun c => Bool.rec (motive := fun _ => Bool) false (subMask c.2.2 S)
            (Nat.blt (fld fm m c.1) c.2.1)))
        (Bool.rec (motive := fun _ => Bool) false (porNode fm B t tt m S Sl true)
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (kfind (m + e.1.2.2.1 - e.1.2.1) t).isSome (fOk fm B m e.1.2.2.2))
            (subMask e.2.1 S)))
        (fEnabled fm m e.1.1))
      (kfind i tt) = true at h
    cases hf : kfind i tt with
    | none => rw [hf] at h; cases h
    | some e =>
      rw [hf] at h
      simp only at h
      cases hen : fEnabled fm m e.1.1
      · rw [hen] at h
        cases hsc : kany e.2.2 fun c => Bool.rec (motive := fun _ => Bool) false
            (subMask c.2.2 S) (Nat.blt (fld fm m c.1) c.2.1)
        · rw [hsc] at h; cases h
        rw [hsc] at h
        obtain ⟨hall, hfound⟩ := ih h
        refine ⟨fun i' hi' => ?_, ?_⟩
        · rcases List.mem_cons.1 hi' with rfl | hi'
          · refine ⟨e, hf, (fun h' => by rw [hen] at h'; cases h'), fun _ => ?_⟩
            simp only [kany_eq, List.any_eq_true] at hsc
            obtain ⟨c, hc, hb⟩ := hsc
            cases hblt : Nat.blt (fld fm m c.1) c.2.1
            · rw [hblt] at hb; cases hb
            · rw [hblt] at hb; exact ⟨c, hc, hblt, hb⟩
          · exact hall i' hi'
        · rcases hfound with h' | ⟨i', hi', e', hf', he'⟩
          · exact Or.inl h'
          · exact Or.inr ⟨i', List.mem_cons_of_mem _ hi', e', hf', he'⟩
      · rw [hen] at h
        cases hsub : subMask e.2.1 S
        · rw [hsub] at h; cases h
        rw [hsub] at h
        cases hok : fOk fm B m e.1.2.2.2
        · rw [hok] at h; cases h
        rw [hok] at h
        cases hfd : (kfind (m + e.1.2.2.1 - e.1.2.1) t).isSome
        · rw [hfd] at h; cases h
        rw [hfd] at h
        obtain ⟨hall, -⟩ := ih h
        refine ⟨fun i' hi' => ?_, Or.inr ⟨i, List.mem_cons_self, e, hf, hen⟩⟩
        rcases List.mem_cons.1 hi' with rfl | hi'
        · exact ⟨e, hf, fun _ => ⟨hsub, hok, hfd⟩, (fun h' => by rw [hen] at h'; cases h')⟩
        · exact hall i' hi'

theorem testBit_maskWhere {q : PTrans → Bool} :
    ∀ {ts : List PTrans} {i k : ℕ}, (maskWhere q ts i).testBit k = true ↔
      ∃ j, ∃ h : j < ts.length, k = i + j ∧ q ts[j] = true
  | [], i, k => by simp [maskWhere]
  | t :: ts, i, k => by
    rw [maskWhere, Nat.testBit_or, Bool.or_eq_true, testBit_maskWhere]
    constructor
    · rintro (h | ⟨j, hj, rfl, hq⟩)
      · split_ifs at h with hq
        · rw [Nat.testBit_two_pow, decide_eq_true_eq] at h
          exact ⟨0, by simp, by omega, by simpa using hq⟩
        · simp at h
      · exact ⟨j + 1, by simpa using hj, by omega, by simpa using hq⟩
    · rintro ⟨j, hj, rfl, hq⟩
      cases j with
      | zero =>
        left
        simp only [List.getElem_cons_zero] at hq
        simp [hq]
      | succ j => exact Or.inr ⟨j, by simpa using hj, by omega, by simpa using hq⟩

theorem testBit_cmask {t t' : Fin N.trans.length} :
    (N.cmask (N.tr t)).testBit t'.val = true ↔ ∃ p ∈ (N.tr t).pre, p ∈ (N.tr t').pre := by
  rw [cmask, testBit_maskWhere]
  simp only [Nat.zero_add, List.any_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨j, hj, rfl, h⟩; exact h
  · intro h; exact ⟨t'.val, t'.isLt, rfl, h⟩

theorem testBit_prodMask {p : ℕ} {t' : Fin N.trans.length} :
    (N.prodMask p).testBit t'.val = true ↔ p ∈ (N.tr t').post := by
  rw [prodMask, testBit_maskWhere]
  simp only [Nat.zero_add, List.contains_iff_mem]
  constructor
  · rintro ⟨j, hj, rfl, h⟩; exact h
  · intro h; exact ⟨t'.val, t'.isLt, rfl, h⟩

theorem testBit_of_subMask {a S i : ℕ} (h : subMask a S = true) (hi : a.testBit i = true) :
    S.testBit i = true := by
  have h' : a &&& S = a := Nat.eq_of_beq_eq_true h
  have : (a &&& S).testBit i = true := by rw [h']; exact hi
  rw [Nat.testBit_land, Bool.and_eq_true] at this
  exact this.2

/-- **Deadlock freedom from a reduced state space.** -/
theorem deadlockFree_of_checkPOR {w B fm s₀ : ℕ} {tt : BTree (ℕ × SEntry)}
    {t : BTree (ℕ × List ℕ)} (h : N.checkPOR w B fm tt s₀ t = true) :
    N.toNet.lts.DeadlockFree N.M₀ := by
  simp only [checkPOR, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwf, hB⟩, hfm⟩, htt⟩, hs₀⟩, hinit⟩, h₀⟩, hall⟩ := h
  rw [Nat.eq_of_beq_eq_true hB] at hfm hinit
  rw [Nat.eq_of_beq_eq_true hfm, Nat.eq_of_beq_eq_true hB] at hall
  rw [ktall_iff] at hall
  have htt' := eq_of_kbeqList (fun _ _ => eq_of_ieq) htt
  have hlen : (N.stable w).length = N.trans.length := by simp [stable]
  -- table lookups give the entries of the net's table
  have hentry : ∀ i e, kfind i tt = some e →
      ∃ hi : i < N.trans.length, e = N.sentry w (N.tr ⟨i, hi⟩) := by
    intro i e hf
    have := mem_of_kfind hf
    rw [htt'] at this
    obtain ⟨j, hj, rfl, rfl⟩ := mem_indexed this
    rw [hlen] at hj
    refine ⟨by omega, ?_⟩
    simp [stable, tr]
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
  have hen : ∀ M (t : Fin N.trans.length), Good M →
      (fEnabled (2 ^ w - 1) (e M) (N.sentry w (N.tr t)).1.1 = true ↔ N.toNet.Enabled M t) := by
    intro M t hg
    simp only [sentry]
    rw [fEnabled_spec (hgood M hg), enabledL_enc_iff ((wf_spec hwf).2 t).1]
  let Sl : Marking (Fin N.places) → List ℕ := fun M => (kfind (e M) t).getD []
  let Inv : Marking (Fin N.places) → Prop := fun M => Good M ∧ ∃ S, kfind (e M) t = some S
  have hnode : ∀ M, Inv M → ∀ k (hk : k < N.trans.length), k ∈ Sl M →
      (N.toNet.Enabled M ⟨k, hk⟩ → subMask (N.cmask (N.tr ⟨k, hk⟩)) (kmaskL (Sl M)) = true ∧
        fOk (2 ^ w - 1) (2 ^ w) (e M) (N.sentry w (N.tr ⟨k, hk⟩)).1.2.2.2 = true ∧
        (kfind (e M + (N.sentry w (N.tr ⟨k, hk⟩)).1.2.2.1 - (N.sentry w (N.tr ⟨k, hk⟩)).1.2.1) t).isSome =
          true) ∧
      (¬ N.toNet.Enabled M ⟨k, hk⟩ → ∃ c ∈ (N.sentry w (N.tr ⟨k, hk⟩)).2.2,
        Nat.blt (fld (2 ^ w - 1) (e M) c.1) c.2.1 = true ∧
          subMask c.2.2 (kmaskL (Sl M)) = true) := by
    rintro M ⟨hg, S, hS⟩ k hk hk'
    have hmem := mem_of_kfind hS
    simp only [Sl, hS, Option.getD_some] at hk' ⊢
    obtain ⟨en, hf, h1, h2⟩ := (porNode_spec (hall _ hmem)).1 k hk'
    obtain ⟨_, rfl⟩ := hentry k en hf
    refine ⟨fun he => h1 ((hen M _ hg).2 he), fun hne => h2 ?_⟩
    cases hb : fEnabled (2 ^ w - 1) (e M) (N.sentry w (N.tr ⟨k, hk⟩)).1.1
    · rfl
    · exact absurd ((hen M _ hg).1 hb) hne
  have hfound : ∀ M, Inv M → ∃ t' : Fin N.trans.length, t'.val ∈ Sl M ∧ N.toNet.Enabled M t' := by
    rintro M ⟨hg, Sv, hSv⟩
    obtain ⟨-, hfd⟩ := porNode_spec (hall _ (mem_of_kfind hSv))
    rcases hfd with hf | ⟨k, hk, en, hf, he⟩
    · cases hf
    · obtain ⟨hk', rfl⟩ := hentry k en hf
      refine ⟨⟨k, hk'⟩, ?_, (hen M _ hg).1 he⟩
      simpa [Sl, hSv] using hk
  -- the reduced semantics: the enabled members of the stubborn set
  let S : Marking (Fin N.places) → Fin N.trans.length → Prop := fun M t' => t'.val ∈ Sl M
  have hfire : ∀ M (t' : Fin N.trans.length), Good M → N.toNet.Enabled M t' →
      e M + (N.sentry w (N.tr t')).1.2.2.1 - (N.sentry w (N.tr t')).1.2.1 =
        e (N.toNet.fire M t') := by
    intro M t' hg he
    simp only [e, sentry]
    rw [← fireL_enc]
    exact encW_fire w _ _ ((enabledL_enc_iff ((wf_spec hwf).2 t').1).2 he)
      (fun p hp => (hlenc M).symm ▸ ((wf_spec hwf).2 t').1 p hp)
      (fun p hp => (hlenc M).symm ▸ ((wf_spec hwf).2 t').2 p hp)
  refine Net.deadlockFree_of_stubborn S Inv ?_ ?_ ?_ ?_
  · -- the initial marking
    refine ⟨fun p => ?_, ?_⟩
    · have := List.all_eq_true.1 hinit (N.init.getD p.val 0) (by
        rw [List.getD_eq_getElem _ _ (by rw [(wf_spec hwf).1]; exact p.isLt)]
        exact List.getElem_mem _)
      simpa [M₀] using this
    · rw [show e N.M₀ = s₀ by simp only [e, enc_M₀ hwf]; exact (Nat.eq_of_beq_eq_true hs₀).symm]
      exact Option.isSome_iff_exists.1 h₀
  · -- firing an enabled member keeps the invariant
    rintro M t' hI hS' he
    obtain ⟨-, hok, hfd⟩ := (hnode M hI t'.val t'.isLt hS').1 he
    refine ⟨fun p => ?_, ?_⟩
    · have := fOk_spec (hgood M hI.1) (N.tr t') hok
      rw [fireL_enc] at this
      exact this _ (by simp only [enc, List.mem_ofFn]; exact ⟨p, rfl⟩)
    · rw [← hfire M t' hI.1 he]
      exact Option.isSome_iff_exists.1 hfd
  · -- the sets are stubborn
    intro M hI
    refine ⟨fun t₁ hS₁ he₁ t₂ hS₂ p hp => ?_, fun t₁ hS₁ hne₁ => ?_, fun _ => ?_⟩
    · -- an enabled member: its conflicts are members
      obtain ⟨hsub, -, -⟩ := (hnode M hI t₁.val t₁.isLt hS₁).1 he₁
      by_contra hp₂
      apply hS₂
      show t₂.val ∈ Sl M
      rw [← testBit_kmaskL]
      refine testBit_of_subMask hsub (testBit_cmask.2 ⟨p.val, ?_, ?_⟩)
      · exact List.count_pos_iff.1 (Nat.pos_of_ne_zero hp)
      · exact List.count_pos_iff.1 (Nat.pos_of_ne_zero hp₂)
    · -- a disabled member: a scapegoat
      obtain ⟨c, hc, hlt, hsub⟩ := (hnode M hI t₁.val t₁.isLt hS₁).2 hne₁
      simp only [sentry, List.mem_map] at hc
      obtain ⟨q, hq, rfl⟩ := hc
      have hqp : q < N.places := ((wf_spec hwf).2 t₁).1 q hq
      refine ⟨⟨q, hqp⟩, ?_, fun t₂ hS₂ => ?_⟩
      · rw [← hfield M hI.1 q hqp]
        exact blt_true hlt
      · change (N.tr t₂).post.count q = 0
        refine List.count_eq_zero_of_not_mem fun hmem => hS₂ ?_
        show t₂.val ∈ Sl M
        rw [← testBit_kmaskL]
        exact testBit_of_subMask hsub (testBit_prodMask.2 hmem)
    · obtain ⟨t', hS', he⟩ := hfound M hI
      exact ⟨t', hS', he⟩
  · intro M hI
    obtain ⟨t', hS', he⟩ := hfound M hI
    exact ⟨t', hS', he⟩

end PNet

end AsyncLean

/-! ### Untrusted generation of the reduced state space -/

namespace AsyncLean

namespace PNet

/-- Number of set bits among the first `n`. -/
def popCount (n x : ℕ) : ℕ := (List.range n).countP fun j => x.testBit j

/-- The stubborn set obtained by closing `{seed}` (untrusted): enabled transitions bring in
their conflicts, disabled ones the producers of a scapegoat place (the one adding the fewest
new transitions). -/
def stubbornFrom (fm m : ℕ) (tb : Array SEntry) (en : Array Bool) (seed : ℕ) : ℕ := Id.run do
  let n := tb.size
  let mut S : ℕ := 2 ^ seed
  let mut work : Array ℕ := #[seed]
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

/-- A stubborn set with few enabled transitions (untrusted). -/
def bestStubborn (fm m : ℕ) (tb : Array SEntry) (en : Array Bool) : ℕ := Id.run do
  let n := tb.size
  let mut best : ℕ := 0
  let mut bestK := n + 1
  for i in [0:n] do
    if en[i]! then
      let S := stubbornFrom fm m tb en i
      let k := (List.range n).countP fun j => en[j]! && S.testBit j
      if k < bestK then
        best := S
        bestK := k
        if k ≤ 1 then break
  return best

variable (N : PNet)

/-- Explore the reduced state space with fields of `w` bits (untrusted). -/
def porExplore (w fuel : ℕ) : Except String (List (ℕ × List ℕ)) := Id.run do
  let B := 2 ^ w
  let fm := B - 1
  let tb := (N.stable w).toArray
  let n := tb.size
  let s₀ := encW w N.init
  let mut seen : Std.HashMap ℕ Unit := ({} : Std.HashMap ℕ Unit).insert s₀ ()
  let mut queue : Array ℕ := #[s₀]
  let mut out : Array (ℕ × List ℕ) := #[]
  let mut qi := 0
  while qi < queue.size do
    if queue.size > fuel then return .error "the reduced state space exceeds the fuel"
    let m := queue[qi]!
    qi := qi + 1
    let en := tb.map fun e => e.1.1.all fun (sh, k) => k ≤ (m >>> sh) &&& fm
    unless en.any id do return .error s!"deadlock at {m}"
    let S := bestStubborn fm m tb en
    out := out.push (m, (List.range n).filter S.testBit)
    for i in [0:n] do
      if en[i]! && S.testBit i then
        let e := tb[i]!
        unless e.1.2.2.2.all (fun c => ((m >>> c.1) &&& fm) - c.2.1 + c.2.2 < B) do
          return .error "overflow"
        let m' := m + e.1.2.2.1 - e.1.2.1
        unless seen.contains m' do
          seen := seen.insert m' ()
          queue := queue.push m'
  return .ok out.toList

/-- Choose a field width and compute a reduced state space (untrusted). Returns the width
and the tree of markings with their stubborn sets. -/
def mkPORCert (fuel : ℕ := 1000000) : Except String (ℕ × BTree (ℕ × List ℕ)) := do
  let maxArc := N.trans.foldl (fun a t => max a (max (t.pre.length) (t.post.length))) 1
  let maxInit := N.init.foldl max 1
  let w₀ := Nat.log2 (max maxArc maxInit) + 1
  let mut last := "no width"
  for w in [w₀, w₀ + 1, w₀ + 2, w₀ + 4, w₀ + 8, 32, 64] do
    match N.porExplore w fuel with
    | .ok es =>
      let a := es.toArray.qsort (fun x y => x.1 < y.1)
      return (w, Fast.buildTree a (a.size + 1) 0 a.size)
    | .error "overflow" => last := "overflow"
    | .error e => throw e
  throw last

end PNet

end AsyncLean
