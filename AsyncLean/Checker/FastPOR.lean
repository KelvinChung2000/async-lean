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

/-- Transitions sharing an input place with `t`. -/
def cmask (t : Fin N.trans.length) : ℕ :=
  mask (((List.finRange N.trans.length).filter fun t' =>
    (N.tr t).pre.any fun p => (N.tr t').pre.contains p).map Fin.val)

/-- Transitions putting tokens into place `p`. -/
def prodMask (p : ℕ) : ℕ :=
  mask (((List.finRange N.trans.length).filter fun t' => (N.tr t').post.contains p).map Fin.val)

/-- Table entry for the reduced search: the fast entry, the conflict mask, and the
candidate scapegoats (field shift, tokens needed, producer mask). -/
abbrev SEntry := FEntry × ℕ × List (ℕ × ℕ × ℕ)

/-- The table entry of `t`. -/
def sentry (w : ℕ) (t : Fin N.trans.length) : SEntry :=
  (fentry w N.places (N.tr t), N.cmask t,
    (N.tr t).pre.dedup.map fun p => (w * p, (N.tr t).pre.count p, N.prodMask p))

/-- The table of the net. -/
def stable (w : ℕ) : List SEntry := (List.finRange N.trans.length).map (N.sentry w)

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

/-- The checks at a marking `m` with stubborn set `S`, along the table from index `i`;
`found` records whether an enabled transition of `S` has been seen. -/
noncomputable def porNode (fm B : ℕ) (t : BTree (ℕ × ℕ)) (m S : ℕ) (tb : List SEntry) :
    ℕ → Bool → Bool :=
  List.rec (motive := fun _ => ℕ → Bool → Bool) (fun _ found => found)
    (fun e _ rec i found => Bool.rec (motive := fun _ => Bool) (rec (i + 1) found)
      (Bool.rec (motive := fun _ => Bool)
        -- disabled: a scapegoat
        (Bool.rec (motive := fun _ => Bool) false (rec (i + 1) found)
          (kany e.2.2 fun c => Bool.rec (motive := fun _ => Bool) false (subMask c.2.2 S)
            (Nat.blt (fld fm m c.1) c.2.1)))
        -- enabled: its conflicts are in `S`, no overflow, and the successor is present
        (Bool.rec (motive := fun _ => Bool) false (rec (i + 1) true)
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (kfind (m + e.1.2.2.1 - e.1.2.1) t).isSome (fOk fm B m e.1.2.2.2))
            (subMask e.2.1 S)))
        (fEnabled fm m e.1.1))
      (ktest S i)) tb

/-- **The reduced-state-space check** for deadlock freedom. -/
noncomputable def checkPOR (w B fm : ℕ) (tb : List SEntry) (s₀ : ℕ) (t : BTree (ℕ × ℕ)) :
    Bool :=
  N.wf && Nat.beq B (2 ^ w) && Nat.beq fm (B - 1) && kbeqList seq tb (N.stable w) &&
    Nat.beq s₀ (encW w N.init) && N.init.all (fun x => decide (x < B)) &&
    (kfind s₀ t).isSome && ktall t (fun x => porNode fm B t x.1 x.2 tb 0 false)

/-! ### Soundness -/

variable {N}

theorem porNode_spec {fm B m S : ℕ} {t : BTree (ℕ × ℕ)} {tb : List SEntry} :
    ∀ {i : ℕ} {found : Bool}, porNode fm B t m S tb i found = true →
      (∀ k (hk : k < tb.length), ktest S (i + k) = true →
        (fEnabled fm m tb[k].1.1 = true → subMask tb[k].2.1 S = true ∧
          fOk fm B m tb[k].1.2.2.2 = true ∧
          (kfind (m + tb[k].1.2.2.1 - tb[k].1.2.1) t).isSome = true) ∧
        (fEnabled fm m tb[k].1.1 = false → ∃ c ∈ tb[k].2.2,
          Nat.blt (fld fm m c.1) c.2.1 = true ∧ subMask c.2.2 S = true)) ∧
      (found = true ∨ ∃ k, ∃ hk : k < tb.length, ktest S (i + k) = true ∧
        fEnabled fm m tb[k].1.1 = true) := by
  induction tb with
  | nil => intro i found h; exact ⟨fun k hk => by simp at hk, Or.inl h⟩
  | cons e tb ih =>
    intro i found h
    change Bool.rec (motive := fun _ => Bool) (porNode fm B t m S tb (i + 1) found)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (porNode fm B t m S tb (i + 1) found)
          (kany e.2.2 fun c => Bool.rec (motive := fun _ => Bool) false (subMask c.2.2 S)
            (Nat.blt (fld fm m c.1) c.2.1)))
        (Bool.rec (motive := fun _ => Bool) false (porNode fm B t m S tb (i + 1) true)
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool) false
              (kfind (m + e.1.2.2.1 - e.1.2.1) t).isSome (fOk fm B m e.1.2.2.2))
            (subMask e.2.1 S)))
        (fEnabled fm m e.1.1))
      (ktest S i) = true at h
    -- the tail
    have tail : ∀ {found'}, porNode fm B t m S tb (i + 1) found' = true →
        (found' = true → found = true ∨ ∃ k, ∃ hk : k < (e :: tb).length,
          ktest S (i + k) = true ∧ fEnabled fm m (e :: tb)[k].1.1 = true) →
        (∀ k (hk : 0 < k) (hk' : k < (e :: tb).length), ktest S (i + k) = true →
          (fEnabled fm m (e :: tb)[k].1.1 = true → subMask (e :: tb)[k].2.1 S = true ∧
            fOk fm B m (e :: tb)[k].1.2.2.2 = true ∧
            (kfind (m + (e :: tb)[k].1.2.2.1 - (e :: tb)[k].1.2.1) t).isSome = true) ∧
          (fEnabled fm m (e :: tb)[k].1.1 = false → ∃ c ∈ (e :: tb)[k].2.2,
            Nat.blt (fld fm m c.1) c.2.1 = true ∧ subMask c.2.2 S = true)) ∧
        (found = true ∨ ∃ k, ∃ hk : k < (e :: tb).length, ktest S (i + k) = true ∧
          fEnabled fm m (e :: tb)[k].1.1 = true) := by
      intro found' h' hf
      obtain ⟨hall, hfound⟩ := ih h'
      refine ⟨fun k hk hk' hS => ?_, ?_⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hk
        have := hall k (by simpa using hk') (by rw [← hS]; congr 1; omega)
        simpa using this
      · rcases hfound with hf' | ⟨k, hk, hS, hen⟩
        · exact hf hf'
        · exact Or.inr ⟨k + 1, by simpa using hk, by rw [← hS]; congr 1; omega, by simpa using hen⟩
    -- the head
    cases hS : ktest S i
    · rw [hS] at h
      obtain ⟨hall, hfound⟩ := tail h fun hf => Or.inl hf
      refine ⟨fun k hk hS' => ?_, hfound⟩
      cases k with
      | zero => rw [Nat.add_zero, hS] at hS'; cases hS'
      | succ k => exact hall (k + 1) (by omega) hk hS'
    rw [hS] at h
    cases hen : fEnabled fm m e.1.1
    · rw [hen] at h
      cases hsc : kany e.2.2 fun c => Bool.rec (motive := fun _ => Bool) false (subMask c.2.2 S)
          (Nat.blt (fld fm m c.1) c.2.1)
      · rw [hsc] at h; cases h
      rw [hsc] at h
      obtain ⟨hall, hfound⟩ := tail h fun hf => Or.inl hf
      refine ⟨fun k hk hS' => ?_, hfound⟩
      cases k with
      | zero =>
        refine ⟨fun h' => by simp [hen] at h', fun _ => ?_⟩
        simp only [kany_eq, List.any_eq_true] at hsc
        obtain ⟨c, hc, hb⟩ := hsc
        cases hblt : Nat.blt (fld fm m c.1) c.2.1
        · rw [hblt] at hb; cases hb
        · rw [hblt] at hb; exact ⟨c, hc, hblt, hb⟩
      | succ k => exact hall (k + 1) (by omega) hk hS'
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
      obtain ⟨hall, hfound⟩ := tail h fun _ => Or.inr ⟨0, by simp, by simpa using hS, hen⟩
      refine ⟨fun k hk hS' => ?_, hfound⟩
      cases k with
      | zero => exact ⟨fun _ => ⟨hsub, hok, hfd⟩, fun h' => by simp [hen] at h'⟩
      | succ k => exact hall (k + 1) (by omega) hk hS'

theorem testBit_cmask {t t' : Fin N.trans.length} :
    (N.cmask t).testBit t'.val = true ↔ ∃ p ∈ (N.tr t).pre, p ∈ (N.tr t').pre := by
  rw [cmask, testBit_mask]
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, Fin.val_inj,
    exists_eq_right, List.any_eq_true, List.contains_iff_mem, decide_eq_true_eq]

theorem testBit_prodMask {p : ℕ} {t' : Fin N.trans.length} :
    (N.prodMask p).testBit t'.val = true ↔ p ∈ (N.tr t').post := by
  rw [prodMask, testBit_mask]
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, Fin.val_inj,
    exists_eq_right, List.contains_iff_mem, decide_eq_true_eq]

theorem testBit_of_subMask {a S i : ℕ} (h : subMask a S = true) (hi : a.testBit i = true) :
    S.testBit i = true := by
  have h' : a &&& S = a := Nat.eq_of_beq_eq_true h
  have : (a &&& S).testBit i = true := by rw [h']; exact hi
  rw [Nat.testBit_land, Bool.and_eq_true] at this
  exact this.2

/-- **Deadlock freedom from a reduced state space.** -/
theorem deadlockFree_of_checkPOR {w B fm s₀ : ℕ} {tb : List SEntry} {t : BTree (ℕ × ℕ)}
    (h : N.checkPOR w B fm tb s₀ t = true) : N.toNet.lts.DeadlockFree N.M₀ := by
  simp only [checkPOR, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwf, hB⟩, hfm⟩, htb⟩, hs₀⟩, hinit⟩, h₀⟩, hall⟩ := h
  rw [Nat.eq_of_beq_eq_true hB] at hfm hinit
  rw [Nat.eq_of_beq_eq_true hfm] at hall
  rw [eq_of_kbeqList (fun _ _ => eq_of_seq) htb] at hall
  rw [Nat.eq_of_beq_eq_true hB] at hall
  rw [ktall_iff] at hall
  have hlen : (N.stable w).length = N.trans.length := by simp [stable]
  have hget : ∀ k (hk : k < (N.stable w).length),
      (N.stable w)[k] = N.sentry w ⟨k, by rwa [hlen] at hk⟩ := by
    intro k hk; simp [stable]
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
      (fEnabled (2 ^ w - 1) (e M) (N.sentry w t).1.1 = true ↔ N.toNet.Enabled M t) := by
    intro M t hg
    simp only [sentry]
    rw [fEnabled_spec (hgood M hg), enabledL_enc_iff ((wf_spec hwf).2 t).1]
  let Sof : Marking (Fin N.places) → ℕ := fun M => (kfind (e M) t).getD 0
  let Inv : Marking (Fin N.places) → Prop := fun M => Good M ∧ ∃ S, kfind (e M) t = some S
  have hnode : ∀ M, Inv M → ∀ k (hk : k < N.trans.length), ktest (Sof M) k = true →
      (N.toNet.Enabled M ⟨k, hk⟩ → subMask (N.cmask ⟨k, hk⟩) (Sof M) = true ∧
        fOk (2 ^ w - 1) (2 ^ w) (e M) (N.sentry w ⟨k, hk⟩).1.2.2.2 = true ∧
        (kfind (e M + (N.sentry w ⟨k, hk⟩).1.2.2.1 - (N.sentry w ⟨k, hk⟩).1.2.1) t).isSome =
          true) ∧
      (¬ N.toNet.Enabled M ⟨k, hk⟩ → ∃ c ∈ (N.sentry w ⟨k, hk⟩).2.2,
        Nat.blt (fld (2 ^ w - 1) (e M) c.1) c.2.1 = true ∧ subMask c.2.2 (Sof M) = true) := by
    rintro M ⟨hg, S, hS⟩ k hk hk'
    have hmem := mem_of_kfind hS
    have := (porNode_spec (hall _ hmem)).1 k (by rw [hlen]; exact hk)
    simp only [Sof, hS, Option.getD_some, Nat.zero_add] at hk' this ⊢
    rw [hget] at this
    obtain ⟨h1, h2⟩ := this hk'
    refine ⟨fun he => h1 ((hen M _ hg).2 he), fun hne => h2 ?_⟩
    cases hb : fEnabled (2 ^ w - 1) (e M) (N.sentry w ⟨k, hk⟩).1.1
    · rfl
    · exact absurd ((hen M _ hg).1 hb) hne
  -- the reduced semantics: the enabled transitions of the stubborn set
  let S : Marking (Fin N.places) → Fin N.trans.length → Prop := fun M t' =>
    ktest (Sof M) t'.val = true
  have hfire : ∀ M (t' : Fin N.trans.length), Good M → N.toNet.Enabled M t' →
      e M + (N.sentry w t').1.2.2.1 - (N.sentry w t').1.2.1 = e (N.toNet.fire M t') := by
    intro M t' hg he
    simp only [e, sentry]
    rw [← fireL_enc, ← hlenc M]
    exact encW_fire w _ _ ((enabledL_enc_iff ((wf_spec hwf).2 t').1).2 he)
  refine Net.deadlockFree_of_stubborn S Inv ?_ ?_ ?_ ?_
  · -- the initial marking
    refine ⟨fun p => ?_, ?_⟩
    · have := List.all_eq_true.1 hinit (N.init.getD p.val 0) (by
        rw [List.getD_eq_getElem _ _ (by rw [(wf_spec hwf).1]; exact p.isLt)]
        exact List.getElem_mem _)
      simpa [M₀] using this
    · rw [show e N.M₀ = s₀ by simp only [e, enc_M₀ hwf]; exact (Nat.eq_of_beq_eq_true hs₀).symm]
      exact Option.isSome_iff_exists.1 h₀
  · -- firing an enabled transition of the set keeps the invariant
    rintro M t' hI hS' he
    obtain ⟨-, hok, hfd⟩ := (hnode M hI t'.val t'.isLt hS').1 he
    refine ⟨fun p => ?_, ?_⟩
    · have := fOk_spec (hgood M hI.1) N.places (N.tr t') hok
      rw [fireL_enc] at this
      exact this _ (by simp only [enc, List.mem_ofFn]; exact ⟨p, rfl⟩)
    · rw [← hfire M t' hI.1 he]
      exact Option.isSome_iff_exists.1 hfd
  · -- the sets are stubborn
    intro M hI
    refine ⟨fun t₁ hS₁ he₁ t₂ hS₂ p hp => ?_, fun t₁ hS₁ hne₁ => ?_, fun _ => ?_⟩
    · -- an enabled transition of the set: its conflicts are in the set
      obtain ⟨hsub, -, -⟩ := (hnode M hI t₁.val t₁.isLt hS₁).1 he₁
      by_contra hp₂
      apply hS₂
      show ktest (Sof M) t₂.val = true
      rw [ktest_eq]
      refine testBit_of_subMask hsub (testBit_cmask.2 ⟨p.val, ?_, ?_⟩)
      · exact List.count_pos_iff.1 (Nat.pos_of_ne_zero hp)
      · exact List.count_pos_iff.1 (Nat.pos_of_ne_zero hp₂)
    · -- a disabled transition of the set: a scapegoat
      obtain ⟨c, hc, hlt, hsub⟩ := (hnode M hI t₁.val t₁.isLt hS₁).2 hne₁
      simp only [sentry, List.mem_map, List.mem_dedup] at hc
      obtain ⟨q, hq, rfl⟩ := hc
      have hqp : q < N.places := ((wf_spec hwf).2 t₁).1 q hq
      refine ⟨⟨q, hqp⟩, ?_, fun t₂ hS₂ => ?_⟩
      · rw [← hfield M hI.1 q hqp]
        exact blt_true hlt
      · change (N.tr t₂).post.count q = 0
        refine List.count_eq_zero_of_not_mem fun hmem => hS₂ ?_
        show ktest (Sof M) t₂.val = true
        rw [ktest_eq]
        exact testBit_of_subMask hsub (testBit_prodMask.2 hmem)
    · -- some transition of the set is enabled
      obtain ⟨hg, Sv, hSv⟩ := hI
      obtain ⟨-, hfound⟩ := porNode_spec (hall _ (mem_of_kfind hSv))
      rcases hfound with hf | ⟨k, hk, hS', he⟩
      · cases hf
      · rw [hget] at he
        have hk' : k < N.trans.length := by rwa [hlen] at hk
        refine ⟨⟨k, hk'⟩, ?_, (hen M _ hg).1 he⟩
        simp only [S, Sof, hSv, Option.getD_some]
        simpa using hS'
  · -- progress: the same
    intro M hI
    obtain ⟨hg, Sv, hSv⟩ := hI
    obtain ⟨-, hfound⟩ := porNode_spec (hall _ (mem_of_kfind hSv))
    rcases hfound with hf | ⟨k, hk, hS', he⟩
    · cases hf
    · rw [hget] at he
      have hk' : k < N.trans.length := by rwa [hlen] at hk
      refine ⟨⟨k, hk'⟩, ?_, (hen M _ hg).1 he⟩
      simp only [S, Sof, hSv, Option.getD_some]
      simpa using hS'

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
def porExplore (w fuel : ℕ) : Except String (List (ℕ × ℕ)) := Id.run do
  let B := 2 ^ w
  let fm := B - 1
  let tb := (N.stable w).toArray
  let n := tb.size
  let s₀ := encW w N.init
  let mut seen : Std.HashMap ℕ Unit := ({} : Std.HashMap ℕ Unit).insert s₀ ()
  let mut queue : Array ℕ := #[s₀]
  let mut out : Array (ℕ × ℕ) := #[]
  let mut qi := 0
  while qi < queue.size do
    if queue.size > fuel then return .error "the reduced state space exceeds the fuel"
    let m := queue[qi]!
    qi := qi + 1
    let en := tb.map fun e => e.1.1.all fun (sh, k) => k ≤ (m >>> sh) &&& fm
    unless en.any id do return .error s!"deadlock at {m}"
    let S := bestStubborn fm m tb en
    out := out.push (m, S)
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
def mkPORCert (fuel : ℕ := 1000000) : Except String (ℕ × BTree (ℕ × ℕ)) := do
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
