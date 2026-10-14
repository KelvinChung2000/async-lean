/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.BDD.Nodes

/-!
# Symbolic certificates: decision diagrams checked by the kernel, part 3: firing, walks and leaf conditions

Part 3 of 4 of `AsyncLean.Checker.BDD`; that module has the overview.
-/

namespace AsyncLean

namespace PNet

open Fast

variable {c : BCert}

/-- Firing does not change the places read at levels outside those it touches. -/
theorem fire_agree (hv : varsOk c.lvls c.vars 0 = true) {e : BTrans}
    (hus : ∀ u ∈ e.us, usOk c e u = true) (hcov : sub (e.pre ||| e.post) (umask e.us) = true)
    {L p : ℕ} (hp : knth c.vars L = some p) (hL : L < e.lo ∨ e.hi < L) (m : ℕ) :
    ((m ^^^ e.pre) ||| e.post).testBit p = m.testBit p := by
  have hno : (e.pre ||| e.post).testBit p = false := by
    cases hb : (e.pre ||| e.post).testBit p
    · rfl
    · obtain ⟨u, hu, rfl⟩ := testBit_umask (sub_iff.1 hcov _ hb)
      have := hus u hu
      simp only [usOk, Bool.and_eq_true, varAt_iff] at this
      obtain ⟨⟨h1, h2⟩, h3⟩ := this
      have := vars_inj hv h3 hp
      have h1 := Nat.le_of_ble_eq_true h1
      have h2 := Nat.le_of_ble_eq_true h2
      omega
  simp only [Nat.testBit_lor, Bool.or_eq_false_iff] at hno
  rw [Nat.testBit_lor, Nat.testBit_xor, hno.1, hno.2]
  simp

theorem side_left {a m ℓ : ℕ} {na : BNode} (ha : rinfo c a = some na) (h : Reach c a m ℓ)
    (s bit : Bool) (hs : s = true → a % 2 = 1 → bit = m.testBit na.var) :
    Reach c (cond bit (cond s na.hi a) (cond s na.lo a)) m ℓ := by
  cases s
  · cases bit <;> exact h
  · have := h.step_left ha bit (hs rfl)
    cases bit <;> exact this

theorem side_right {b m ℓ : ℕ} {nb : BNode} (hb : rinfo c b = some nb) (s bit : Bool)
    (hs : s = true → b % 2 = 1 → bit = m.testBit nb.var)
    (h : Reach c (cond bit (cond s nb.hi b) (cond s nb.lo b)) m ℓ) : Reach c b m ℓ := by
  cases s
  · cases bit <;> exact h
  · exact Reach.step_right hb bit (hs rfl) (by cases bit <;> exact h)

theorem memT_spec {ps : BTree (ℕ × ℕ × ℕ × ℕ)} {a b j : ℕ} (h : memT ps a b j = true) :
    (tkey a b j, a, b, j) ∈ ps.toList := by
  simp only [memT] at h
  split at h
  · cases h
  · rename_i x hx
    obtain ⟨x1, x2, x3⟩ := x
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have := mem_of_kfind hx
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3] at this
    exact this

/-- What the triple `(a, b, j)` of transition `i` guarantees: from a marking `m` enabling the
transition and reaching a non-zero leaf `ℓ₁` from `a`, the output-only places from the `j`-th
touched place on are unmarked, and the marking after firing reaches from `b` a leaf `ℓ₂`
satisfying the leaf condition. -/
def TClaim (c : BCert) (md i : ℕ) (e : BTrans) (_ps : BTree (ℕ × ℕ × ℕ × ℕ)) (a b j : ℕ) : Prop :=
  ∀ m, sub e.pre m = true → ∀ ℓ₁, Reach c a m ℓ₁ → ℓ₁ ≠ 0 →
    (∀ u ∈ e.us.drop j, 2 ≤ u.2.2 → m.testBit u.1 = false) ∧
    ∃ ℓ₂, Reach c b ((m ^^^ e.pre) ||| e.post) ℓ₂ ∧ leafCond c md i ℓ₁ ℓ₂ = true

theorem testBit_fire {m pre post v : ℕ} :
    ((m ^^^ pre) ||| post).testBit v = ((m.testBit v ^^ pre.testBit v) || post.testBit v) := by
  simp [Nat.testBit_xor]

/-- **Every triple keeps its promise.** -/
theorem tclaim (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    (hv : varsOk c.lvls c.vars 0 = true) {md i : ℕ}
    {e : BTrans} {ps : BTree (ℕ × ℕ × ℕ × ℕ)} (hUok : ∀ u ∈ e.us, uOk e.pre e.post u = true)
    (hus : ∀ u ∈ e.us, usOk c e u = true) (hcov : sub (e.pre ||| e.post) (umask e.us) = true)
    (hT : ∀ x ∈ ps.toList, tripleOk c md i e ps x = true) :
    ∀ a b j, memT ps a b j = true → TClaim c md i e ps a b j := by
  -- the measure: levels still to go on both sides, and touched places still to pass
  suffices H : ∀ n, ∀ a b j na nb, rinfo c a = some na → rinfo c b = some nb →
      (c.H - na.lvl) + (c.H - nb.lvl) + (e.us.length - j) = n → memT ps a b j = true →
      TClaim c md i e ps a b j by
    intro a b j hm
    have hx := hT _ (memT_spec hm)
    simp only [tripleOk] at hx
    split at hx
    · rename_i na nb ha hb
      exact H _ a b j na nb ha hb rfl hm
    · cases hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro a b j na nb ha hb hn hm
  have hx := hT _ (memT_spec hm)
  simp only [tripleOk, ha, hb] at hx
  -- an untouched place
  have hU : untouched c e ps a b j na nb = true → TClaim c md i e ps a b j := by
    intro hu
    simp only [untouched, cond_ble_min, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
      ktest_eq] at hu
    obtain ⟨⟨⟨⟨⟨⟨hL, hva⟩, hvb⟩, hpre⟩, hpost⟩, hm0⟩, hm1⟩ := hu
    have hL' := blt_true hL
    intro m hpm ℓ₁ hr hne
    set L := min na.lvl nb.lvl with hLdef
    set v := cond (Nat.ble na.lvl nb.lvl) na.var nb.var
    set bit := m.testBit v
    have hm' : memT ps (cond bit (cond (Nat.beq na.lvl L) na.hi a) (cond (Nat.beq na.lvl L) na.lo a))
        (cond bit (cond (Nat.beq nb.lvl L) nb.hi b) (cond (Nat.beq nb.lvl L) nb.lo b)) j = true := by
      cases bit
      · exact hm0
      · exact hm1
    obtain ⟨na', ha', hla, hla'⟩ := side_lvl hN ha (Nat.beq na.lvl L) bit
    obtain ⟨nb', hb', hlb, hlb'⟩ := side_lvl hN hb (Nat.beq nb.lvl L) bit
    have hmeas : (c.H - na'.lvl) + (c.H - nb'.lvl) + (e.us.length - j) < n := by
      rcases le_total na.lvl nb.lvl with hle | hle
      · have h1 : Nat.beq na.lvl L = true := by
          rw [Nat.beq_eq, hLdef, min_eq_left hle]
        have := hla' h1 (by omega)
        omega
      · have h1 : Nat.beq nb.lvl L = true := by
          rw [Nat.beq_eq, hLdef, min_eq_right hle]
        have := hlb' h1 (by omega)
        omega
    have hva' : Nat.beq na.lvl L = true → a % 2 = 1 → bit = m.testBit na.var := by
      intro h _
      rcases hva with hva | hva
      · rw [hva] at h; cases h
      · rw [Nat.eq_of_beq_eq_true hva]
    obtain ⟨hsafe, ℓ₂, hr2, hlc⟩ := IH _ hmeas _ _ _ na' nb' ha' hb' rfl hm' m hpm ℓ₁
      (side_left ha hr _ bit hva') hne
    refine ⟨hsafe, ℓ₂, side_right hb (Nat.beq nb.lvl L) bit (fun h _ => ?_) hr2, hlc⟩
    rcases hvb with hvb | hvb
    · rw [hvb] at h; cases h
    · rw [Nat.eq_of_beq_eq_true hvb, testBit_fire, hpre, hpost]; simp [bit]
  split at hx
  · -- a touched place
    rename_i u hu
    rw [knth_eq] at hu
    obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.1 hu
    have hdrop : e.us.drop j = u :: e.us.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj, hget]
    have huok := hUok u (List.mem_of_getElem? hu)
    cases hc : (Nat.ble u.2.1 na.lvl && Nat.ble u.2.1 nb.lvl)
    · rw [hc] at hx; exact hU hx
    rw [hc] at hx
    simp only [Bool.cond_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc hx
    obtain ⟨hca, hcb⟩ := hc
    have hla := Nat.le_of_ble_eq_true hca
    have hlb := Nat.le_of_ble_eq_true hcb
    obtain ⟨⟨hva, hvb⟩, hk⟩ := hx
    have hva' : Nat.beq na.lvl u.2.1 = true → na.var = u.1 := fun h => by
      rcases hva with hva | hva
      · rw [hva] at h; cases h
      · exact Nat.eq_of_beq_eq_true hva
    have hvb' : Nat.beq nb.lvl u.2.1 = true → nb.var = u.1 := fun h => by
      rcases hvb with hvb | hvb
      · rw [hvb] at h; cases h
      · exact Nat.eq_of_beq_eq_true hvb
    intro m hpm ℓ₁ hr hne
    have hpre_m := sub_iff.1 hpm
    have succ : ∀ bitA bitB : Bool,
        memT ps (cond bitA (cond (Nat.beq na.lvl u.2.1) na.hi a) (cond (Nat.beq na.lvl u.2.1) na.lo a))
          (cond bitB (cond (Nat.beq nb.lvl u.2.1) nb.hi b) (cond (Nat.beq nb.lvl u.2.1) nb.lo b))
          (j + 1) = true →
        bitA = m.testBit u.1 → bitB = ((m ^^^ e.pre) ||| e.post).testBit u.1 →
        (∀ u' ∈ e.us.drop (j + 1), 2 ≤ u'.2.2 → m.testBit u'.1 = false) ∧
          ∃ ℓ₂, Reach c b ((m ^^^ e.pre) ||| e.post) ℓ₂ ∧
            leafCond c md i ℓ₁ ℓ₂ = true := by
      intro bitA bitB hmem hA hB
      obtain ⟨na', ha', hla1, -⟩ := side_lvl hN ha (Nat.beq na.lvl u.2.1) bitA
      obtain ⟨nb', hb', hlb1, -⟩ := side_lvl hN hb (Nat.beq nb.lvl u.2.1) bitB
      obtain ⟨hs, ℓ₂, hr2, hlc⟩ := IH _ (by omega) _ _ _ na' nb' ha' hb' rfl hmem m hpm ℓ₁
        (side_left ha hr _ bitA fun h _ => by rw [hva' h]; exact hA) hne
      exact ⟨hs, ℓ₂, side_right hb _ bitB (fun h _ => by rw [hvb' h]; exact hB) hr2, hlc⟩
    simp only [uOk, ktest_eq] at huok
    rw [hdrop]
    cases hk0 : Nat.beq u.2.2 0
    · cases hk1 : Nat.beq u.2.2 1
      · -- output only
        rw [hk0, hk1] at huok hk
        simp only [Bool.cond_false, Bool.and_eq_true, Bool.not_eq_true'] at huok hk
        obtain ⟨hpv, hqv⟩ := huok
        cases hmv : m.testBit u.1
        · obtain ⟨hs, h2⟩ := succ false true hk.2 hmv.symm (by simp [hmv, hpv, hqv])
          refine ⟨fun u' hu' h2u => ?_, h2⟩
          rcases List.mem_cons.1 hu' with rfl | hu'
          · exact hmv
          · exact hs u' hu' h2u
        · -- marking an output place that is already marked: impossible in the invariant
          exfalso
          obtain ⟨na', ha', hla1, -⟩ := side_lvl hN ha (Nat.beq na.lvl u.2.1) true
          obtain ⟨-, ℓ₂, hr2, hlc⟩ := IH _ (by dsimp only; omega)
            _ 0 _ na' ⟨c.H, 0, 0, 0, 0, 0⟩ ha' (rinfo_even rfl) rfl hk.1 m hpm ℓ₁
            (side_left ha hr _ true fun h _ => by rw [hva' h]; exact hmv.symm) hne
          rw [hr2.of_even rfl] at hlc
          simp [leafCond, nbeq_false hne] at hlc
      · -- input and output
        rw [hk0, hk1] at huok hk
        simp only [Bool.cond_false, Bool.cond_true, Bool.and_eq_true] at huok hk
        obtain ⟨hpv, hqv⟩ := huok
        obtain ⟨hs, h2⟩ := succ true true hk (hpre_m _ hpv).symm (by simp [hqv])
        refine ⟨fun u' hu' h2u => ?_, h2⟩
        rcases List.mem_cons.1 hu' with rfl | hu'
        · rw [Nat.eq_of_beq_eq_true hk1] at h2u; omega
        · exact hs u' hu' h2u
    · -- input only
      rw [hk0] at huok hk
      simp only [Bool.cond_true, Bool.and_eq_true, Bool.not_eq_true'] at huok hk
      obtain ⟨hpv, hqv⟩ := huok
      obtain ⟨hs, h2⟩ := succ true false hk (hpre_m _ hpv).symm
        (by simp [hpv, hqv, hpre_m _ hpv])
      refine ⟨fun u' hu' h2u => ?_, h2⟩
      rcases List.mem_cons.1 hu' with rfl | hu'
      · rw [Nat.eq_of_beq_eq_true hk0] at h2u; omega
      · exact hs u' hu' h2u
  · -- past the touched places
    rename_i hu
    rw [knth_eq, List.getElem?_eq_none_iff] at hu
    cases hc : (Nat.blt na.lvl c.H || Nat.blt nb.lvl c.H)
    · rw [hc] at hx
      simp only [Bool.or_eq_false_iff] at hc
      have hae : a % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one a with h | h
        · exact h
        · have h1 : Nat.blt na.lvl c.H = true := by rw [Nat.blt_eq]; exact lvl_lt_of_odd hN h ha
          simp [h1] at hc
      have hbe : b % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one b with h | h
        · exact h
        · have h1 : Nat.blt nb.lvl c.H = true := by rw [Nat.blt_eq]; exact lvl_lt_of_odd hN h hb
          simp [h1] at hc
      intro m _ ℓ₁ hr _
      rw [hr.of_even hae]
      refine ⟨fun u' hu' => by simp [List.drop_eq_nil_of_le hu] at hu', b, Reach.leaf hbe, hx⟩
    · rw [hc] at hx
      simp only [Bool.cond_true, Bool.or_eq_true, Bool.and_eq_true] at hx
      simp only [Bool.or_eq_true] at hc
      rcases hx with (⟨⟨hmd, hab⟩, hhi⟩ | ⟨⟨hmd, hlv⟩, hdl⟩) | hx
      · -- the same node before and after firing, below the touched places
        have hmd := Nat.eq_of_beq_eq_true hmd
        have hab := Nat.eq_of_beq_eq_true hab
        subst hmd hab
        rw [ha] at hb; cases hb
        have hhi := blt_true hhi
        have hlt : na.lvl < c.H := by
          rcases hc with h | h <;> exact blt_true h
        have hao := odd_of_lvl_lt ha hlt
        intro m _ ℓ₁ hr hne
        refine ⟨fun u' hu' => by simp [List.drop_eq_nil_of_le hu] at hu', ℓ₁, ?_, ?_⟩
        · exact hr.congr hN (L := na.lvl)
            (fun L' p hL hp => fire_agree hv hus hcov hp (Or.inr (by omega)) m)
            (fun n hn => by rw [ha] at hn; cases hn; exact le_refl _)
        · obtain ⟨L, hL⟩ := hr.leaf_mem hN hao hne
          simp +decide [leafCond, nbeq_false hne, hL]
      · -- a coverage walk that reached a data leaf
        have hmd := Nat.eq_of_beq_eq_true hmd
        subst hmd
        have hao := odd_of_lvl_lt ha (blt_true hlv)
        simp only [dataLeaf, Bool.and_eq_true, Bool.not_eq_true'] at hdl
        obtain ⟨⟨hbe, hb0⟩, hdat⟩ := hdl
        have hbe : b % 2 = 0 := by rw [← land_one]; exact Nat.eq_of_beq_eq_true hbe
        have hb0 : b ≠ 0 := Nat.ne_of_beq_eq_false hb0
        rw [shiftRight_one'] at hdat
        split at hdat
        · rename_i lb hlb
          intro m _ ℓ₁ hr hne
          obtain ⟨L, hL⟩ := hr.leaf_mem hN hao hne
          refine ⟨fun u' hu' => by simp [List.drop_eq_nil_of_le hu] at hu', b, Reach.leaf hbe, ?_⟩
          simp +decide [leafCond, nbeq_false hne, nbeq_false hb0, hL, hlb, hdat]
        · cases hdat
      · exact hU hx

theorem chkTrans_spec {ll lv : Bool} : ∀ {ts : List PTrans} {es : List BTrans} {i : ℕ},
    chkTrans c ll lv ts es i = true → es.length = ts.length ∧ ∀ k (hk : k < ts.length),
      ∃ e, es[k]? = some e ∧ mask ts[k].pre = e.pre ∧ mask ts[k].post = e.post ∧
        transOk c ll lv ts[k].internal (i + k) e = true
  | [], [], _, _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | [], _ :: _, _, h => by simp [chkTrans] at h
  | _ :: _, [], _, h => by simp [chkTrans] at h
  | t :: ts, e :: es, i, h => by
    simp only [chkTrans, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨hl, ih⟩ := chkTrans_spec h4
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero => exact ⟨e, rfl, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, by simpa using h3⟩
    | succ k =>
      obtain ⟨e', he', h'⟩ := ih k (by simpa using hk)
      exact ⟨e', by simpa using he', by simpa [Nat.add_assoc, Nat.add_comm 1 k] using h'⟩

theorem leafCond_spec {md i a b : ℕ} (h : leafCond c md i a b = true)
    (ha : a ≠ 0) : b ≠ 0 ∧ ∃ la lb, kfind (a / 2) c.leaves = some la ∧
      kfind (b / 2) c.leaves = some lb ∧ (md = 1 → lb.r < la.r) ∧ (2 ≤ md → lb.dat = true) ∧
      (md = 2 → la.wit = i → la.d ≠ 0 → lb.d < la.d) := by
  simp only [leafCond, nbeq_false ha, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hb, h⟩ := h
  refine ⟨fun h0 => by simp [h0] at hb, ?_⟩
  split at h
  · rename_i la lb hla hlb
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
      at h
    obtain ⟨⟨h1, h3⟩, h2⟩ := h
    refine ⟨la, lb, hla, hlb, fun hm => ?_, fun hm => ?_, fun hm hw hd => ?_⟩
    · rcases h1 with h1 | h1
      · simp [hm] at h1
      · exact blt_true h1
    · rcases h3 with h3 | h3
      · rw [show Nat.ble 2 md = true by rw [Nat.ble_eq]; exact hm] at h3; cases h3
      · exact h3
    · rcases h2 with h2 | h2
      · simp [hm, hw, nbeq_false hd] at h2
      · exact blt_true h2
  · cases h

theorem simB_cons {tl : List BTrans} {m j : ℕ} {js : List ℕ} {m' : ℕ}
    (h : simB tl m (j :: js) = some m') : ∃ e, knth tl j = some e ∧ sub e.pre m = true ∧
      simB tl ((m ^^^ e.pre) ||| e.post) js = some m' := by
  simp only [simB] at h
  split at h
  · cases h
  · rename_i e he
    cases hs : sub e.pre m
    · rw [hs] at h; cases h
    · rw [hs] at h; exact ⟨e, he, hs, h⟩

theorem tracesOk_spec {tl : List BTrans} {h : ℕ} : ∀ {trs : List (List ℕ)} {i : ℕ},
    tracesOk tl h trs i = true → ∀ k (hk : k < trs.length), ∃ m' e,
      simB tl h trs[k] = some m' ∧ knth tl (i + k) = some e ∧ sub e.pre m' = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | tr :: trs, i, hc, k, hk => by
    simp only [tracesOk, Bool.and_eq_true] at hc
    obtain ⟨h1, h2⟩ := hc
    cases k with
    | zero =>
      split at h1
      · rename_i m' e hm he
        exact ⟨m', e, hm, he, h1⟩
      · cases h1
    | succ k =>
      obtain ⟨m', e, hm, he, hs⟩ := tracesOk_spec h2 k (by simpa using hk)
      exact ⟨m', e, hm, by simpa [Nat.add_assoc, Nat.add_comm 1 k] using he, hs⟩

theorem phiL_cons (w : ℕ) (ws : List ℕ) (x q : ℕ) :
    phiL (w :: ws) x q = cond (ktest x q) w 0 + phiL ws x (q + 1) := rfl

/-- Firing never increases the linear potential by more than the outputs minus the inputs. -/
theorem phiL_fire (ws : List ℕ) {m pre post : ℕ} (hen : sub pre m = true) :
    ∀ q, phiL ws ((m ^^^ pre) ||| post) q + phiL ws pre q ≤ phiL ws m q + phiL ws post q := by
  induction ws with
  | nil => intro q; simp [phiL]
  | cons w ws ih =>
    intro q
    simp only [phiL_cons, ktest_eq, Nat.testBit_lor, Nat.testBit_xor]
    have h := ih (q + 1)
    have hb := sub_iff.1 hen q
    cases hm : m.testBit q <;> cases hp : pre.testBit q <;> cases ho : post.testBit q <;>
      simp only [Bool.true_xor, Bool.false_xor, Bool.not_true, Bool.not_false, Bool.or_true,
        Bool.or_false, Bool.cond_true, Bool.cond_false] <;>
      first | omega | (exfalso; have := hb hp; rw [hm] at this; cases this)

theorem phiL_lt {ws : List ℕ} {m pre post : ℕ} (hen : sub pre m = true)
    (hd : decB ws pre post = true) : phiL ws ((m ^^^ pre) ||| post) 0 < phiL ws m 0 := by
  have h1 := phiL_fire ws (post := post) hen 0
  have h2 := blt_true hd
  omega

theorem le_sum_of_mem_nat {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h
      simp only [List.sum_cons]
      omega

theorem phiL_le {ws : List ℕ} {m pre post : ℕ} (hen : sub pre m = true)
    (hd : nincB ws pre post = true) : phiL ws ((m ^^^ pre) ||| post) 0 ≤ phiL ws m 0 := by
  have h1 := phiL_fire ws (post := post) hen 0
  have h2 := Nat.le_of_ble_eq_true hd
  omega

end PNet

end AsyncLean
