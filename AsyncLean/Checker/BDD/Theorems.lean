/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.BDD.Firing

/-!
# Symbolic certificates: decision diagrams checked by the kernel, part 4: soundness of the check

Part 4 of 4 of `AsyncLean.Checker.BDD`; that module has the overview.
-/

namespace AsyncLean

namespace PNet

open Fast

variable {c : BCert}

variable (N : PNet)

theorem packed_step_iff {m m' : ℕ} {t : Fin N.trans.length} :
    N.packed.toLTS.step m t m' ↔
      sub (N.preMask t) m = true ∧ m' = (m ^^^ N.preMask t) ||| N.postMask t := by
  change (t, m') ∈ N.packedSucc m ↔ _
  simp only [packedSucc, List.mem_filterMap, List.mem_finRange, true_and, sub_eq, Nat.land_comm]
  constructor
  · rintro ⟨t', h⟩
    split_ifs at h with hen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hen, rfl⟩
  · rintro ⟨hen, rfl⟩
    exact ⟨t, by simp [hen]⟩

variable {N}

theorem lt_two_pow_mask {ps : List ℕ} {n : ℕ} (h : ∀ q ∈ ps, q < n) : mask ps < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro q hq
  rw [testBit_mask]
  simp only [decide_eq_false_iff_not]
  exact fun hm => absurd (h q hm) (by omega)

/-- A walk from the roots `ra`, `rb` keeps the promise of its first triple. -/
theorem walkOk_spec {c : BCert} (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    (hv : varsOk c.lvls c.vars 0 = true)
    {md i : ℕ} {e : BTrans} {ps : BTree (ℕ × ℕ × ℕ × ℕ)} {ra rb : ℕ}
    (hu : ∀ u ∈ e.us, uOk e.pre e.post u = true) (hus : ∀ u ∈ e.us, usOk c e u = true)
    (hcov : sub (e.pre ||| e.post) (umask e.us) = true) (h : walkOk c md i e ps ra rb = true) :
    TClaim c md i e ps ra rb 0 := by
  simp only [walkOk, Bool.and_eq_true, ktall_iff] at h
  exact tclaim hN hv hu hus hcov h.2 _ _ _ h.1

/-- The chain of cuts, level by level. -/
theorem cutsOk_spec {c : BCert} : ∀ {rest : List (List ℕ)} {L : ℕ} {cur : List ℕ},
    cutsOk c L cur rest = true → ∀ k cl nx, knth (cur :: rest) k = some cl →
      knth (cur :: rest) (k + 1) = some nx → ∀ x ∈ cl, cutStep c (L + k) nx x = true
  | [], _, _, _, k, cl, nx, _, h2 => by rw [knth_eq] at h2; simp at h2
  | nx' :: rest, L, cur, h, k, cl, nx, h1, h2 => by
    simp only [cutsOk, Bool.and_eq_true, kall_eq, List.all_eq_true] at h
    rw [knth_eq] at h1 h2
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at h1 h2
      subst h1 h2
      intro x hx; simpa using h.1 x hx
    | succ k =>
      have := cutsOk_spec h.2 k cl nx (by rw [knth_eq]; simpa using h1)
        (by rw [knth_eq]; simpa using h2)
      intro x hx
      have := this x hx
      rwa [show L + 1 + k = L + (k + 1) by omega] at this

/-- Every marking of the invariant passes the cut of each level, at a reference from which
the rest of its path does not depend on the levels above. -/
theorem cut_reach {c : BCert} (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    {cuts : List (List ℕ)}
    (hcs : ∀ k cl nx, knth cuts k = some cl → knth cuts (k + 1) = some nx →
      ∀ x ∈ cl, cutStep c k nx x = true)
    {c0 : List ℕ} (h0 : knth cuts 0 = some c0) (hr0 : c.rI ∈ c0) :
    ∀ L cl, knth cuts L = some cl → ∀ m ℓ, Reach c c.rI m ℓ → ∃ x ∈ cl, Reach c x m ℓ ∧
      ∀ m', (∀ L' p, L' < L → knth c.vars L' = some p → m'.testBit p = m.testBit p) →
        ∀ ℓ', Reach c x m' ℓ' → Reach c c.rI m' ℓ' := by
  intro L
  induction L with
  | zero =>
    intro cl hcl m ℓ hr
    rw [h0] at hcl; cases hcl
    exact ⟨c.rI, hr0, hr, fun _ _ _ h => h⟩
  | succ L ih =>
    intro nx hnx m ℓ hr
    obtain ⟨cl, hcl⟩ := knth_prev hnx
    obtain ⟨x, hx, hrx, hpath⟩ := ih cl hcl m ℓ hr
    have hst := hcs L cl nx hcl hnx x hx
    unfold cutStep at hst
    split at hst
    · rename_i n hn
      cases hb : Nat.beq n.lvl L
      · rw [hb] at hst
        simp only [Bool.cond_false] at hst
        exact ⟨x, memL_iff.1 hst, hrx, fun m' hag => hpath m' fun L' p hL hp => hag L' p (by omega) hp⟩
      · rw [hb] at hst
        simp only [Bool.cond_true, Bool.and_eq_true] at hst
        have hl := Nat.eq_of_beq_eq_true hb
        refine ⟨cond (m.testBit n.var) n.hi n.lo, ?_, hrx.step_left hn _ fun _ => rfl, ?_⟩
        · cases m.testBit n.var
          · exact memL_iff.1 hst.1
          · exact memL_iff.1 hst.2
        · intro m' hag ℓ' hr'
          refine hpath m' (fun L' p hL hp => hag L' p (by omega) hp) ℓ' ?_
          refine Reach.step_right hn _ (fun hxo => ?_) hr'
          have hvar := varAt_iff.1 (nodeOk_var hN hxo hn)
          rw [hl] at hvar
          exact (hag L _ (by omega) hvar).symm
    · cases hst

/-- The walk on the invariant, from the cut of the lowest level touched. -/
theorem walkCut_spec {c : BCert} (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    (hv : varsOk c.lvls c.vars 0 = true)
    (hcut : ∀ L cl, knth c.cuts L = some cl → ∀ m ℓ, Reach c c.rI m ℓ → ∃ x ∈ cl,
      Reach c x m ℓ ∧ ∀ m', (∀ L' p, L' < L → knth c.vars L' = some p →
        m'.testBit p = m.testBit p) → ∀ ℓ', Reach c x m' ℓ' → Reach c c.rI m' ℓ')
    {i : ℕ} {e : BTrans} (hu : ∀ u ∈ e.us, uOk e.pre e.post u = true)
    (hus : ∀ u ∈ e.us, usOk c e u = true) (hcov : sub (e.pre ||| e.post) (umask e.us) = true)
    (h : walkCut c i e = true) : TClaim c 0 i e e.psI c.rI c.rI 0 := by
  simp only [walkCut, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [ktall_iff] at h2
  split at h1
  · rename_i cl hcl
    rw [kall_eq, List.all_eq_true] at h1
    intro m hpm ℓ₁ hr hne
    obtain ⟨x, hx, hrx, hpath⟩ := hcut _ cl hcl m ℓ₁ hr
    obtain ⟨hs, ℓ₂, hr2, hlc⟩ :=
      tclaim hN hv hu hus hcov h2 x x 0 (h1 x hx) m hpm ℓ₁ hrx hne
    exact ⟨hs, ℓ₂, hpath _ (fun L' p hL hp => fire_agree hv hus hcov hp (Or.inl hL) m) ℓ₂ hr2,
      hlc⟩
  · cases h1

/-- A walk with the empty transition: the second diagram covers the first. -/
theorem cover_of_walk {c : BCert} (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    (hv : varsOk c.lvls c.vars 0 = true) {md : ℕ} {ps : BTree (ℕ × ℕ × ℕ × ℕ)} {ra rb : ℕ} (h : walkOk c md 0 emptyT ps ra rb = true)
    {m ℓ : ℕ} (hr : Reach c ra m ℓ) (hne : ℓ ≠ 0) :
    ∃ ℓ₂, Reach c rb m ℓ₂ ∧ leafCond c md 0 ℓ ℓ₂ = true := by
  have := walkOk_spec hN hv (by simp [emptyT]) (by simp [emptyT]) rfl h m
    (sub_iff.2 fun q hq => by simp [emptyT] at hq) ℓ hr hne
  obtain ⟨-, ℓ₂, hr2, hlc⟩ := this
  simp only [emptyT, Nat.xor_zero, Nat.or_zero] at hr2
  exact ⟨ℓ₂, hr2, hlc⟩

/-- **Soundness of the symbolic check.** -/
theorem of_checkBDD {dl ll lv : Bool} {c : BCert} (h : N.checkBDD dl ll lv c = true) :
    (dl = true → N.toNet.lts.DeadlockFree N.M₀) ∧
      (ll = true → N.toNet.lts.LivelockFree N.Internal N.M₀) ∧
      (lv = true → N.toNet.lts.Live N.M₀) ∧ N.Safe := by
  simp only [checkBDD, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hwf, hv⟩, hcuts⟩, hroot⟩, hN⟩, hL⟩, htr⟩, hcR⟩, hcD⟩, h₀⟩ := h
  rw [ktall_iff] at hL
  replace hN : ∀ k n, nget c k = some n → nodeOk c n = true := fun _ _ hk => nodesOk_spec hN hk
  have hcut : ∀ L cl, knth c.cuts L = some cl → ∀ m ℓ, Reach c c.rI m ℓ → ∃ x ∈ cl,
      Reach c x m ℓ ∧ ∀ m', (∀ L' p, L' < L → knth c.vars L' = some p →
        m'.testBit p = m.testBit p) → ∀ ℓ', Reach c x m' ℓ' → Reach c c.rI m' ℓ' := by
    split at hcuts
    · rename_i c0 rest hc
      simp only [Bool.and_eq_true] at hcuts
      rw [hc]
      exact cut_reach hN (fun k cl nx h1 h2 x hx => by
          simpa using cutsOk_spec hcuts.2 k cl nx h1 h2 x hx)
        (by rw [knth_eq]; rfl) (memL_iff.1 hcuts.1)
    · cases hcuts
  obtain ⟨hwf', hM₀, hnd⟩ := packedWf_spec hwf
  have hroot' : kOf c c.rD = some (0, 0) := by
    split at hroot
    · rename_i k hk
      obtain ⟨k1, k2⟩ := k
      simp only [Bool.and_eq_true] at hroot
      rw [hk, Nat.eq_of_beq_eq_true hroot.1, Nat.eq_of_beq_eq_true hroot.2]
    · cases hroot
  have hcovR : ll = true → c.linR = false → walkOk c 0 0 emptyT c.covR c.rI c.rR = true :=
    fun h h' => by simpa [h, h'] using hcR
  have hcovD : (dl = true ∨ lv = true) → walkOk c 3 0 emptyT c.covD c.rI c.rD = true :=
    fun h => by rcases h with h | h <;> simpa [h] using hcD
  obtain ⟨hlen, htr⟩ := chkTrans_spec htr
  -- the certificate of each transition
  have hT : ∀ t : Fin N.trans.length, ∃ e, knth c.trans t = some e ∧ e.pre = N.preMask t ∧
      e.post = N.postMask t ∧ sub ((e.post &&& e.pre) ^^^ e.post) (kmask2 e.us) = true ∧
      TClaim c 0 t e e.psI c.rI c.rI 0 ∧
      (ll = true → (N.tr t).internal = true → decB c.wR e.pre e.post = true ∨
        (c.linR = false ∧ nincB c.wR e.pre e.post = true ∧
          TClaim c 1 t e e.psR c.rR c.rR 0)) ∧
      (lv = true → c.linD = false → e.wit = true → decB c.wD e.pre e.post = true ∨
        (nincB c.wD e.pre e.post = true ∧ TClaim c 2 t e e.psD c.rD c.rD 0)) ∧
      (lv = true → c.linD = true → e.wit = true → decB c.wD e.pre e.post = true) := by
    intro t
    obtain ⟨e, he, h1, h2, h3⟩ := htr t t.isLt
    simp only [Nat.zero_add, transOk, Bool.and_eq_true] at h3
    obtain ⟨⟨⟨⟨⟨⟨⟨hu, hsub⟩, hus⟩, hcov⟩, hI⟩, hR⟩, hDL⟩, hD⟩ := h3
    rw [kall_eq, List.all_eq_true] at hu hus
    refine ⟨e, by rw [knth_eq]; exact he, h1.symm, h2.symm, hsub,
      walkCut_spec hN hv hcut hu hus hcov hI, fun hll hint => ?_, fun hlv hl hw' => ?_,
      fun hlv hl hw' => by simpa [hlv, hl, hw'] using hDL⟩
    · have : (N.trans[t.val]).internal = true := hint
      simp only [hll, this, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
        Bool.and_eq_true, Bool.not_eq_true'] at hR
      rcases hR with hR | ⟨⟨hl, hn⟩, hw⟩
      · exact Or.inl hR
      · exact Or.inr ⟨hl, hn, walkOk_spec hN hv hu hus hcov hw⟩
    · simp only [hlv, hl, hw', Bool.not_true, Bool.false_or, Bool.or_eq_true,
        Bool.and_eq_true] at hD
      rcases hD with hD | ⟨hn, hw⟩
      · exact Or.inl hD
      · exact Or.inr ⟨hn, walkOk_spec hN hv hu hus hcov hw⟩
  have hT' : ∀ (j : ℕ) (e : BTrans), knth c.trans j = some e → ∃ t : Fin N.trans.length,
      t.val = j ∧ e.pre = N.preMask t ∧ e.post = N.postMask t := by
    intro j e he
    have hj : j < N.trans.length := by
      rw [knth_eq] at he
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 he).1
    obtain ⟨e', he', h⟩ := hT ⟨j, hj⟩
    rw [he] at he'; cases he'
    exact ⟨⟨j, hj⟩, rfl, h.1, h.2.1⟩
  -- the invariant
  let C : ℕ → Prop := fun m => m < 2 ^ N.places ∧ ∃ ℓ, Reach c c.rI m ℓ ∧ ℓ ≠ 0
  have hC₀ : C (N.pack N.M₀) := by
    refine ⟨Nat.lt_pow_two_of_testBit _ fun q hq => ?_, ?_⟩
    · cases hb : Nat.testBit (N.pack N.M₀) q
      · rfl
      · obtain ⟨h', -⟩ := (testBit_pack N.M₀ q).1 hb; omega
    · split at h₀
      · rename_i l hl
        exact ⟨l, evalB_spec hl, fun h0 => by simp [h0] at h₀⟩
      · cases h₀
  -- firing from the invariant
  have hfire : ∀ m (t : Fin N.trans.length), C m → sub (N.preMask t) m = true →
      (∀ q, (N.postMask t).testBit q = true → (N.preMask t).testBit q = false →
        m.testBit q = false) ∧ C ((m ^^^ N.preMask t) ||| N.postMask t) := by
    rintro m t ⟨hm, ℓ₁, hr, hne⟩ hen
    obtain ⟨e, -, hpre, hpost, hsub, hcl, -⟩ := hT t
    rw [← hpre] at hen
    obtain ⟨hsafe, ℓ₂, hr2, hlc⟩ := hcl m hen ℓ₁ hr hne
    refine ⟨fun q hq hq' => ?_, ?_, ℓ₂, by rw [← hpre, ← hpost]; exact hr2,
      (leafCond_spec hlc hne).1⟩
    · rw [← hpost] at hq; rw [← hpre] at hq'
      have : ((e.post &&& e.pre) ^^^ e.post).testBit q = true := by
        simp [Nat.testBit_xor, hq, hq']
      obtain ⟨u, hu, hu2, rfl⟩ := testBit_kmask2 (sub_iff.1 hsub q this)
      exact hsafe u (by simpa using hu) hu2
    · have hpl := ((wf_spec hwf').2 t).1
      have hpo := ((wf_spec hwf').2 t).2
      apply Nat.lt_pow_two_of_testBit
      intro q hq
      have h1 : m.testBit q = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right Nat.two_pos hq))
      have h2 : (N.preMask t).testBit q = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt_two_pow_mask hpl)
          (Nat.pow_le_pow_right Nat.two_pos hq))
      have h3 : (N.postMask t).testBit q = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt_two_pow_mask hpo)
          (Nat.pow_le_pow_right Nat.two_pos hq))
      simp [Nat.testBit_xor, h1, h2, h3]
  have hclosed : ∀ m l m', C m → N.packed.toLTS.step m l m' → C m' := by
    intro m t m' hm hst
    obtain ⟨hen, rfl⟩ := (packed_step_iff N).1 hst
    exact (hfire m t hm hen).2
  have hsafe : ∀ m, C m → N.safeNode m = true := by
    intro m hm
    simp only [safeNode, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
      Bool.not_eq_true']
    intro t
    cases hen : Nat.beq (m &&& N.preMask t) (N.preMask t)
    · exact Or.inl rfl
    · right
      have hen' : sub (N.preMask t) m = true := by
        rw [sub_eq, Nat.land_comm]; exact hen
      have hs := (hfire m t hm hen').1
      rw [Nat.beq_eq]
      apply Nat.eq_of_testBit_eq
      intro q
      simp only [Nat.testBit_land, Nat.testBit_xor, Nat.zero_testBit]
      cases hq : (N.postMask t).testBit q
      · simp
      · cases hp : (N.preMask t).testBit q
        · simp [hs q hq hp]
        · simp [sub_iff.1 hen' q hp]
  -- the data leaf reached by a marking
  have hleaf : ∀ m ℓ, Reach c c.rD m ℓ → ℓ ≠ 0 → ∃ L, kfind (ℓ / 2) c.leaves = some L ∧
      leafOk c dl lv N.trans.length (2 ^ N.places - 1) (ℓ / 2, L) = true ∧
      (∀ q, L.k1.testBit q = true → m.testBit q = true) ∧
      (∀ q, L.k0.testBit q = true → m.testBit q = false) := by
    intro m ℓ hr hne
    obtain ⟨K, hK, h1, h0⟩ := hr.known hN hroot' (by simp) (by simp)
    rw [kOf_leaf hr.even hne] at hK
    cases hk : kfind (ℓ / 2) c.leaves with
    | none => rw [hk] at hK; cases hK
    | some L =>
      rw [hk] at hK
      simp only [Option.map_some, Option.some.injEq] at hK
      subst hK
      exact ⟨L, rfl, hL _ (mem_of_kfind hk), h1, h0⟩
  -- every marking of the invariant reaches a data leaf
  have hdata : (dl = true ∨ lv = true) → ∀ m, C m → ∃ ℓ L, Reach c c.rD m ℓ ∧ ℓ ≠ 0 ∧
      kfind (ℓ / 2) c.leaves = some L ∧ L.dat = true := by
    rintro hc m ⟨-, ℓ₁, hr, hne⟩
    obtain ⟨ℓ₂, hr2, hlc⟩ := cover_of_walk hN hv (hcovD hc) hr hne
    obtain ⟨hne2, -, lb, -, hlb, -, hdat, -⟩ := leafCond_spec hlc hne
    exact ⟨ℓ₂, lb, hr2, hne2, hlb, hdat (by omega)⟩
  -- the witness of a data leaf is enabled
  have hwit : ∀ m ℓ L, kfind (ℓ / 2) c.leaves = some L → L.dat = true →
      leafOk c dl lv N.trans.length (2 ^ N.places - 1) (ℓ / 2, L) = true →
      (∀ q, L.k1.testBit q = true → m.testBit q = true) →
      (dl = true ∨ (lv = true ∧ L.d ≠ 0)) →
      ∃ t : Fin N.trans.length, t.val = L.wit ∧ sub (N.preMask t) m = true ∧
        (lv = true → c.linD = true → L.d ≠ 0 →
          decB c.wD (N.preMask t) (N.postMask t) = true) ∧
        (lv = true → L.d ≠ 0 → ∀ e, knth c.trans t = some e → e.wit = true) := by
    intro m ℓ L _ hdat hok h1 hc
    simp only [leafOk, hdat, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hok
    obtain ⟨hw, -⟩ := hok
    rcases hw with ⟨hdl, hlv⟩ | ⟨hlt, hw⟩
    · exfalso
      rcases hc with hc | ⟨hc, hd⟩
      · simp [hc] at hdl
      · rcases hlv with hlv | hlv
        · simp [hc] at hlv
        · simp [nbeq_false hd] at hlv
    · split at hw
      · rename_i e he
        obtain ⟨t, ht, hpre, hpost⟩ := hT' _ _ he
        simp only [Bool.and_eq_true] at hw
        obtain ⟨hw, hwt⟩ := hw
        have hwit' : lv = true → L.d ≠ 0 → e.wit = true := fun hlv hd => by
          simpa [hlv, nbeq_false hd] using hwt
        refine ⟨t, ht, sub_iff.2 fun q hq => h1 q ?_, fun hlv hl hd => ?_,
          fun hlv hd e' he' => ?_⟩
        · rw [← hpre] at hq
          exact sub_iff.1 hw q hq
        · obtain ⟨e', he', -, -, -, -, -, -, hDL⟩ := hT t
          rw [ht, he] at he'
          cases he'
          rw [← hpre, ← hpost]
          exact hDL hlv hl (hwit' hlv hd)
        · rw [ht, he] at he'
          cases he'
          exact hwit' hlv hd
      · cases hw
  have hbisim := N.funBisimOn_packed hwf C hclosed hsafe
  have hJ₀ : SafeM N.M₀ ∧ C (N.pack N.M₀) := ⟨hM₀, hC₀⟩
  refine ⟨fun hdl => ?_, fun hll => ?_, fun hlv => ?_,
    fun M hr p => (hbisim.inv_reachable hJ₀ hr).1 p⟩
  · -- deadlock freedom
    refine (hbisim.deadlockFree_iff hJ₀).1 (LTS.DeadlockFree.of_invariant C hC₀ hclosed ?_)
    intro m hm
    obtain ⟨ℓ, L, hr, hne, hk, hdat⟩ := hdata (Or.inl hdl) m hm
    obtain ⟨L', hk', hok, h1, -⟩ := hleaf m ℓ hr hne
    rw [hk] at hk'; cases hk'
    obtain ⟨t, -, hen, -⟩ := hwit m ℓ L hk hdat hok h1 (Or.inl hdl)
    exact ⟨t, _, (packed_step_iff N).2 ⟨hen, rfl⟩⟩
  · -- livelock freedom
    classical
    cases hlr : c.linR
    swap
    · -- from the linear rank
      refine (hbisim.livelockFree_iff hJ₀).1
        (LTS.LivelockFree.of_ranking C hC₀ hclosed (fun m => phiL c.wR m 0) ?_)
      rintro m t m' - hint hst
      obtain ⟨hen, rfl⟩ := (packed_step_iff N).1 hst
      obtain ⟨e, -, hpre, hpost, -, -, hR, -⟩ := hT t
      rcases hR hll hint with hd | ⟨h, -⟩
      · rw [hpre, hpost] at hd
        exact phiL_lt hen hd
      · rw [hlr] at h; cases h
    let V : ℕ → ℕ := fun m =>
      if h : ∃ ℓ, Reach c c.rR m ℓ then
        ((kfind (Classical.choose h / 2) c.leaves).map BLeaf.r).getD 0 else 0
    have hV : ∀ m ℓ L, Reach c c.rR m ℓ → kfind (ℓ / 2) c.leaves = some L → V m = L.r := by
      intro m ℓ L hr hk
      have hex : ∃ ℓ, Reach c c.rR m ℓ := ⟨ℓ, hr⟩
      simp only [V, dite_eq_left hex]
      rw [(Classical.choose_spec hex).det hr, hk]; rfl
    -- the ranks are bounded by their sum `S`
    let S := (c.leaves.toList.map fun x => x.2.r).sum
    have hVS : ∀ m, V m ≤ S := by
      intro m
      simp only [V]
      split
      · cases hk : kfind (Classical.choose ‹∃ ℓ, Reach c c.rR m ℓ› / 2) c.leaves with
        | none => simp
        | some L =>
          simp only [Option.map_some, Option.getD_some]
          exact le_sum_of_mem_nat (List.mem_map.2 ⟨_, mem_of_kfind hk, rfl⟩)
      · exact Nat.zero_le _
    -- the linear rank first, then the rank diagram
    refine (hbisim.livelockFree_iff hJ₀).1 (LTS.LivelockFree.of_ranking C hC₀ hclosed
      (fun m => phiL c.wR m 0 * (S + 1) + V m) ?_)
    rintro m t m' ⟨hm, ℓ₀, hr0, hne0⟩ hint hst
    obtain ⟨hen, rfl⟩ := (packed_step_iff N).1 hst
    obtain ⟨e, -, hpre, hpost, -, -, hR, -⟩ := hT t
    rcases hR hll hint with hd | ⟨-, hn, hR⟩
    · rw [hpre, hpost] at hd
      have h1 := Nat.mul_le_mul_right (S + 1) (phiL_lt hen hd)
      have h2 := hVS ((m ^^^ N.preMask t) ||| N.postMask t)
      rw [Nat.succ_mul] at h1
      omega
    obtain ⟨ℓ₁, hr, hlc0⟩ := cover_of_walk hN hv (hcovR hll hlr) hr0 hne0
    have hne := (leafCond_spec hlc0 hne0).1
    rw [← hpre] at hen
    obtain ⟨-, ℓ₂, hr2, hlc⟩ := hR m hen ℓ₁ hr hne
    rw [hpre, hpost] at hr2 hn
    rw [hpre] at hen
    obtain ⟨-, la, lb, hla, hlb, hrk, -⟩ := leafCond_spec hlc hne
    have h1 := Nat.mul_le_mul_right (S + 1) (phiL_le hen hn)
    have h2 := hrk rfl
    rw [← hV _ _ _ hr hla, ← hV _ _ _ hr2 hlb] at h2
    omega
  · -- liveness
    refine (hbisim.live_iff hJ₀).1 fun t m hreach => ?_
    -- simulating a trace
    have hsimR : ∀ (tr : List ℕ) (m m' : ℕ), simB c.trans m tr = some m' →
        N.packed.toLTS.Reachable m m' := by
      intro tr
      induction tr with
      | nil => intro m m' h; simp only [simB, Option.some.injEq] at h; subst h; rfl
      | cons j js ih =>
        intro m m' h
        obtain ⟨e, he, hen, h'⟩ := simB_cons h
        obtain ⟨t', -, hpre, hpost⟩ := hT' _ _ he
        rw [hpre, hpost] at h'
        rw [hpre] at hen
        exact LTS.Reachable.head ⟨t', (packed_step_iff N).2 ⟨hen, rfl⟩⟩ (ih _ _ h')
    -- a hub is a single marking, with a trace enabling `t`
    have hhub : ∀ m ℓ L, C m → Reach c c.rD m ℓ → ℓ ≠ 0 →
        kfind (ℓ / 2) c.leaves = some L → L.dat = true → L.d = 0 →
        ∃ m', N.packed.toLTS.Reachable m m' ∧ N.packed.toLTS.Enabled m' t := by
      intro m ℓ L hm hr hne hk hdat hd0
      obtain ⟨L', hk', hok, h1, h0⟩ := hleaf m ℓ hr hne
      rw [hk] at hk'; cases hk'
      simp only [leafOk, hdat, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hok
      obtain ⟨-, hhub⟩ := hok
      rcases hhub with hhub | hhub
      · simp [hlv, hd0] at hhub
      obtain ⟨⟨⟨hfull, hk1⟩, hlen'⟩, htrs⟩ := hhub
      have hmk : m = L.k1 := by
        apply Nat.eq_of_testBit_eq
        intro q
        by_cases hq : q < N.places
        · have hb : (2 ^ N.places - 1).testBit q = true := by
            rw [Nat.testBit_two_pow_sub_one]; simpa using hq
          have := sub_iff.1 hfull q hb
          rw [Nat.testBit_lor] at this
          cases h1q : L.k1.testBit q
          · rw [h1q, Bool.false_or] at this; exact h0 q this
          · exact h1 q h1q
        · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm.1
            (Nat.pow_le_pow_right Nat.two_pos (by omega)))]
          have : L.k1 < 2 ^ N.places := by
            have := blt_true hk1
            have hp : 0 < 2 ^ N.places := Nat.two_pow_pos _
            omega
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le this
            (Nat.pow_le_pow_right Nat.two_pos (by omega)))]
      subst hmk
      obtain ⟨m', e, hsim, he, hen⟩ := tracesOk_spec htrs t
        (by rw [Nat.eq_of_beq_eq_true hlen']; exact t.isLt)
      obtain ⟨t', ht', hpre, -⟩ := hT' _ _ (by simpa using he)
      have : t' = t := Fin.ext ht'
      subst this
      rw [hpre] at hen
      exact ⟨m', hsimR _ _ _ hsim, _, (packed_step_iff N).2 ⟨hen, rfl⟩⟩
    have hm := hreach.invariant hC₀ hclosed
    cases hld : c.linD
    · -- by the linear potential and the distances, lexicographically: the witness decreases
      -- the potential, or keeps it and leads closer to a hub
      have key : ∀ p d, ∀ m ℓ L, C m → Reach c c.rD m ℓ → ℓ ≠ 0 →
          kfind (ℓ / 2) c.leaves = some L → L.dat = true → phiL c.wD m 0 = p → L.d = d →
          ∃ m', N.packed.toLTS.Reachable m m' ∧ N.packed.toLTS.Enabled m' t := by
        intro p
        induction p using Nat.strong_induction_on with
        | _ p IHp =>
        intro d
        induction d using Nat.strong_induction_on with
        | _ d IH =>
        intro m ℓ L hm hr hne hk hdat hp hd
        by_cases hd0 : L.d = 0
        · exact hhub m ℓ L hm hr hne hk hdat hd0
        obtain ⟨L', hk', hok, h1, -⟩ := hleaf m ℓ hr hne
        rw [hk] at hk'; cases hk'
        obtain ⟨w, hw, hen, -, hwt⟩ := hwit m ℓ L hk hdat hok h1 (Or.inr ⟨hlv, hd0⟩)
        have hC' := (hfire m w hm hen).2
        -- from the next marking on
        have next : phiL c.wD ((m ^^^ N.preMask w) ||| N.postMask w) 0 < p →
            ∃ m', N.packed.toLTS.Reachable m m' ∧ N.packed.toLTS.Enabled m' t := by
          intro hlt
          obtain ⟨ℓ', L', hr', hne', hk'', hdat'⟩ := hdata (Or.inr hlv) _ hC'
          obtain ⟨m', hr'', hen'⟩ := IHp _ hlt L'.d _ ℓ' L' hC' hr' hne' hk'' hdat' rfl rfl
          exact ⟨m', LTS.Reachable.head ⟨w, (packed_step_iff N).2 ⟨hen, rfl⟩⟩ hr'', hen'⟩
        obtain ⟨e, he, hpre, hpost, -, -, -, hD, -⟩ := hT w
        rcases hD hlv hld (hwt hlv hd0 e he) with hdec | ⟨hn, hD⟩
        · rw [hpre, hpost] at hdec
          exact next (hp ▸ phiL_lt hen hdec)
        rw [hpre, hpost] at hn
        rcases Nat.lt_or_eq_of_le (hp ▸ phiL_le hen hn) with hlt | heq
        · exact next hlt
        rw [← hpre] at hen
        obtain ⟨-, ℓ₂, hr2, hlc⟩ := hD m hen ℓ hr hne
        rw [hpre, hpost] at hr2
        rw [hpre] at hen
        obtain ⟨hne2, la, lb, hla, hlb, -, hdat2, hdd⟩ := leafCond_spec hlc hne
        rw [hk] at hla; cases hla
        obtain ⟨m', hr', hen'⟩ := IH lb.d (hd ▸ hdd rfl hw.symm hd0) _ ℓ₂ lb hC' hr2 hne2 hlb
          (hdat2 (by omega)) heq rfl
        exact ⟨m', LTS.Reachable.head ⟨w, (packed_step_iff N).2 ⟨hen, rfl⟩⟩ hr', hen'⟩
      obtain ⟨ℓ, L, hr, hne, hk, hdat⟩ := hdata (Or.inr hlv) m hm
      exact key _ _ m ℓ L hm hr hne hk hdat rfl rfl
    · -- by the linear potential, which the witness decreases
      have key : ∀ n, ∀ m, C m → phiL c.wD m 0 = n →
          ∃ m', N.packed.toLTS.Reachable m m' ∧ N.packed.toLTS.Enabled m' t := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n IH =>
        intro m hm hn
        obtain ⟨ℓ, L, hr, hne, hk, hdat⟩ := hdata (Or.inr hlv) m hm
        by_cases hd0 : L.d = 0
        · exact hhub m ℓ L hm hr hne hk hdat hd0
        obtain ⟨L', hk', hok, h1, -⟩ := hleaf m ℓ hr hne
        rw [hk] at hk'; cases hk'
        obtain ⟨w, -, hen, hdec, -⟩ := hwit m ℓ L hk hdat hok h1 (Or.inr ⟨hlv, hd0⟩)
        have hC' := (hfire m w hm hen).2
        have hlt := phiL_lt hen (hdec hlv hld hd0)
        obtain ⟨m', hr', hen'⟩ := IH _ (hn ▸ hlt) _ hC' rfl
        exact ⟨m', LTS.Reachable.head ⟨w, (packed_step_iff N).2 ⟨hen, rfl⟩⟩ hr', hen'⟩
      exact key _ m hm rfl

theorem correct_of_checkBDD {c : BCert} (h : N.checkBDD true true true c = true) :
    N.Correct ∧ N.Safe :=
  let h := of_checkBDD h
  ⟨⟨h.1 rfl, h.2.1 rfl, h.2.2.1 rfl⟩, h.2.2.2⟩

theorem correct_of_checkBDD_lf {c : BCert} (h : N.checkBDD true false true c = true)
    (hlf : N.toNet.lts.LivelockFree N.Internal N.M₀) : N.Correct ∧ N.Safe :=
  let h := of_checkBDD h
  ⟨⟨h.1 rfl, hlf, h.2.2.1 rfl⟩, h.2.2.2⟩

theorem deadlockFree_of_checkBDD {c : BCert} (h : N.checkBDD true false false c = true) :
    N.toNet.lts.DeadlockFree N.M₀ :=
  (of_checkBDD h).1 rfl

theorem livelockFree_of_checkBDD {c : BCert} (h : N.checkBDD false true false c = true) :
    N.toNet.lts.LivelockFree N.Internal N.M₀ :=
  (of_checkBDD h).2.1 rfl

theorem live_of_checkBDD {c : BCert} (h : N.checkBDD false false true c = true) :
    N.toNet.lts.Live N.M₀ :=
  (of_checkBDD h).2.2.1 rfl

theorem safe_of_checkBDD {c : BCert} (h : N.checkBDD false false false c = true) : N.Safe :=
  (of_checkBDD h).2.2.2

end PNet

end AsyncLean
