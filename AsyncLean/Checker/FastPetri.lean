/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Fast
import AsyncLean.Checker.Packed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Fast verification of bounded Petri nets

A marking is packed into one natural number, `w` bits per place (`PNet.encW`): place `p`
holds its count in bits `w*p … w*p + w - 1`.  In this encoding

* a transition is enabled when each input field holds enough tokens (a shift and a mask per
  input place),
* firing it adds the encoded output vector and subtracts the encoded input vector — exact
  arithmetic, with no carries between fields as long as no field overflows,
* and the checker verifies, at every reachable marking and for every enabled transition,
  that no output field overflows.

All of this is natural-number arithmetic that the kernel performs natively, and
`PNet.encodes` proves that it faithfully encodes the net on markings below `2^w`.  With the
fast checker of `AsyncLean.Checker.Fast`, `PNet.of_checkFast` proves deadlock freedom,
livelock freedom and liveness, and `PNet.bounded_of_checkFast` the bound `2^w - 1`.
-/

namespace AsyncLean

namespace PNet

open Fast

/-! ### Packing counts into fields -/

/-- Counts packed into fields of `w` bits. -/
def encW (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + 2 ^ w * encW w xs

theorem encW_field {w : ℕ} {xs : List ℕ} (h : ∀ x ∈ xs, x < 2 ^ w) (p : ℕ) :
    encW w xs / 2 ^ (w * p) % 2 ^ w = xs.getD p 0 := by
  induction xs generalizing p with
  | nil => simp [encW]
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    cases p with
    | zero => simp [encW, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    | succ p =>
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * p)) (2 ^ w), ← Nat.div_div_eq_div_mul]
      simp only [encW]
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add]
      simpa using ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) p

theorem field_eq (m w p : ℕ) :
    Nat.land (Nat.shiftRight m (w * p)) (2 ^ w - 1) = m / 2 ^ (w * p) % 2 ^ w := by
  change (m >>> (w * p)) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-! ### The fast successor function -/

/-- Fast-table entry of a transition: its input fields with their weights, the encoded input
and output vectors, and its output fields (with input and output weights) for the overflow
check. -/
abbrev FEntry := List (ℕ × ℕ) × ℕ × ℕ × List (ℕ × ℕ × ℕ)

-- (instance search does not find this one by itself)
instance : DecidableEq FEntry :=
  @instDecidableEqProd _ _ inferInstance
    (@instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance inferInstance))

/-- The sum of `2^(w*p)` over a list of places (with multiplicity): the packed vector of arc
weights. -/
def encList (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | p :: ps => 2 ^ (w * p) + encList w ps

/-- The fast-table entry of `t` for fields of `w` bits (a place listed twice gives two equal
conditions, which is harmless). -/
def fentry (w : ℕ) (t : PTrans) : FEntry :=
  (t.pre.map fun p => (w * p, t.pre.count p), encList w t.pre, encList w t.post,
   t.post.map fun p => (w * p, t.pre.count p, t.post.count p))

/-- Boolean equality of table entries, by the recursors. -/
noncomputable def feq (a b : FEntry) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (kbeqList (fun x y => Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool) false (Nat.beq x.2.2 y.2.2) (Nat.beq x.2.1 y.2.1))
          (Nat.beq x.1 y.1)) a.2.2.2 b.2.2.2)
        (Nat.beq a.2.2.1 b.2.2.1))
      (Nat.beq a.2.1 b.2.1))
    (kbeqList (fun x y => Bool.rec (motive := fun _ => Bool) false (Nat.beq x.2 y.2)
      (Nat.beq x.1 y.1)) a.1 b.1)

theorem eq_of_feq {a b : FEntry} (h : feq a b = true) : a = b := by
  have hb : ∀ {x y : Bool} {p : Prop}, (Bool.rec (motive := fun _ => Bool) false x y = true) →
      (y = true → x = true → p) → p := by
    intro x y p h k; cases y <;> cases x <;> simp_all
  refine hb h fun h1 h => hb h fun h2 h => hb h fun h3 h4 => ?_
  have e1 := eq_of_kbeqList (f := fun x y : ℕ × ℕ => Bool.rec (motive := fun _ => Bool) false
    (Nat.beq x.2 y.2) (Nat.beq x.1 y.1)) (fun x y hxy => by
      exact hb hxy fun e1 e2 => Prod.ext (Nat.eq_of_beq_eq_true e1) (Nat.eq_of_beq_eq_true e2)) h1
  have e4 := eq_of_kbeqList (f := fun x y : ℕ × ℕ × ℕ => Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (Nat.beq x.2.2 y.2.2) (Nat.beq x.2.1 y.2.1))
    (Nat.beq x.1 y.1)) (fun x y hxy => by
      exact hb hxy fun e1 h' => hb h' fun e2 e3 => Prod.ext (Nat.eq_of_beq_eq_true e1)
        (Prod.ext (Nat.eq_of_beq_eq_true e2) (Nat.eq_of_beq_eq_true e3))) h4
  exact Prod.ext e1 (Prod.ext (Nat.eq_of_beq_eq_true h2) (Prod.ext (Nat.eq_of_beq_eq_true h3) e4))

variable (N : PNet)

/-- The fast table of the net. -/
def ftable (w : ℕ) : List FEntry := N.trans.map (fentry w)

/-- Mask of the internal transitions. -/
def imask : ℕ := mask (((List.finRange N.trans.length).filter fun t => (N.tr t).internal).map Fin.val)

/-- Every input field holds enough tokens (`fm` is the field mask). -/
noncomputable def fEnabled (fm m : ℕ) (pres : List (ℕ × ℕ)) : Bool :=
  kall pres fun pk => Nat.ble pk.2 (Nat.land (Nat.shiftRight m pk.1) fm)

/-- No output field overflows (`B` is the field capacity). -/
noncomputable def fOk (fm B m : ℕ) (posts : List (ℕ × ℕ × ℕ)) : Bool :=
  kall posts fun c => Nat.blt (Nat.land (Nat.shiftRight m c.1) fm - c.2.1 + c.2.2) B

/-- Successors along the table, numbering transitions from `i`. -/
noncomputable def fsuccAux (fm B m : ℕ) (tb : List FEntry) : ℕ → List (ℕ × ℕ × Bool) :=
  List.rec (motive := fun _ => ℕ → List (ℕ × ℕ × Bool)) (fun _ => [])
    (fun e _ rec i => Bool.rec (motive := fun _ => List (ℕ × ℕ × Bool)) (rec (i + 1))
      ((i, m + e.2.2.1 - e.2.1, fOk fm B m e.2.2.2) :: rec (i + 1)) (fEnabled fm m e.1)) tb

/-- The fast successor function: label, target and overflow flag. -/
noncomputable def fsucc (fm B : ℕ) (tb : List FEntry) (m : ℕ) : List (ℕ × ℕ × Bool) :=
  fsuccAux fm B m tb 0

variable {N}

theorem mem_fsuccAux {fm B m : ℕ} {tb : List FEntry} {i₀ j m' : ℕ} {b : Bool} :
    (j, m', b) ∈ fsuccAux fm B m tb i₀ ↔ ∃ k, ∃ hk : k < tb.length, j = i₀ + k ∧
      fEnabled fm m tb[k].1 = true ∧ m' = m + tb[k].2.2.1 - tb[k].2.1 ∧
      b = fOk fm B m tb[k].2.2.2 := by
  induction tb generalizing i₀ with
  | nil => simp [fsuccAux]
  | cons e tb ih =>
    change (j, m', b) ∈ Bool.rec (motive := fun _ => List (ℕ × ℕ × Bool))
      (fsuccAux fm B m tb (i₀ + 1))
      ((i₀, m + e.2.2.1 - e.2.1, fOk fm B m e.2.2.2) :: fsuccAux fm B m tb (i₀ + 1))
      (fEnabled fm m e.1) ↔ _
    constructor
    · intro h
      have hrest : (j, m', b) ∈ fsuccAux fm B m tb (i₀ + 1) → ∃ k, ∃ hk : k < (e :: tb).length,
          j = i₀ + k ∧ fEnabled fm m (e :: tb)[k].1 = true ∧
          m' = m + (e :: tb)[k].2.2.1 - (e :: tb)[k].2.1 ∧ b = fOk fm B m (e :: tb)[k].2.2.2 := by
        intro h'
        obtain ⟨k, hk, rfl, h1, h2, h3⟩ := ih.1 h'
        exact ⟨k + 1, by simpa using hk, by omega, h1, h2, h3⟩
      cases hen : fEnabled fm m e.1
      · rw [hen] at h; exact hrest h
      · rw [hen] at h
        rcases List.mem_cons.1 h with h | h
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨0, by simp, rfl, hen, rfl, rfl⟩
        · exact hrest h
    · rintro ⟨k, hk, rfl, h1, h2, h3⟩
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero] at h1 h2 h3
        rw [h1]; subst h2 h3
        exact List.mem_cons_self
      | succ k =>
        have := (ih (i₀ := i₀ + 1)).2 ⟨k, by simpa using hk, by omega, h1, h2, h3⟩
        cases fEnabled fm m e.1
        · exact this
        · exact List.mem_cons_of_mem _ this

/-! ### Correctness of the encoding -/

/-- Markings that the encoding represents faithfully. -/
def GoodW (w places : ℕ) (xs : List ℕ) : Prop := xs.length = places ∧ ∀ x ∈ xs, x < 2 ^ w

theorem fEnabled_spec {w : ℕ} {xs : List ℕ} (hg : ∀ x ∈ xs, x < 2 ^ w) (t : PTrans) :
    fEnabled (2 ^ w - 1) (encW w xs) (fentry w t).1 = enabledL xs t.pre := by
  simp only [fEnabled, fentry, kall_eq, enabledL, List.all_map, Function.comp_def]
  simp only [field_eq, encW_field hg]
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, Nat.ble_eq, decide_eq_true_eq]

theorem encW_eq_sum (w : ℕ) (l : List ℕ) :
    encW w l = ∑ k ∈ Finset.range l.length, l.getD k 0 * 2 ^ (w * k) := by
  induction l with
  | nil => simp [encW]
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ', encW, ih, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    rw [Nat.add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.mul_succ, Nat.pow_add]; ring

theorem encList_eq_sum (w n : ℕ) (ps : List ℕ) (h : ∀ p ∈ ps, p < n) :
    encList w ps = ∑ k ∈ Finset.range n, ps.count k * 2 ^ (w * k) := by
  induction ps with
  | nil => simp [encList]
  | cons q qs ih =>
    rw [encList, ih fun p hp => h p (List.mem_cons_of_mem _ hp)]
    simp only [List.count_cons, Nat.add_mul, Finset.sum_add_distrib, beq_iff_eq]
    rw [Nat.add_comm]
    congr 1
    simp [Finset.sum_ite_eq, h q List.mem_cons_self]

/-- The packed vector of arc weights is the packed count vector. -/
theorem encW_range_count (w n : ℕ) (ps : List ℕ) (h : ∀ p ∈ ps, p < n) :
    encW w ((List.range n).map ps.count) = encList w ps := by
  rw [encW_eq_sum, encList_eq_sum w n ps h, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  simp [List.getD_eq_getElem?_getD, hk]

theorem encW_fireL {w : ℕ} (pre post : List ℕ) :
    ∀ (xs : List ℕ) (i : ℕ), (∀ k (hk : k < xs.length), pre.count (i + k) ≤ xs[k]) →
      encW w (fireL pre post i xs) + encW w ((List.range' i xs.length).map pre.count) =
        encW w xs + encW w ((List.range' i xs.length).map post.count) := by
  intro xs
  induction xs with
  | nil => intro i _; simp [fireL, encW]
  | cons x xs ih =>
    intro i h
    have h0 := h 0 (by simp)
    have := ih (i + 1) fun k hk => by
      have := h (k + 1) (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this
    simp only [fireL, List.length_cons, List.range'_succ, List.map_cons, encW] at this ⊢
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have e1 : x - pre.count i + post.count i + 2 ^ w * encW w (fireL pre post (i + 1) xs) +
        (pre.count i + 2 ^ w * encW w ((List.range' (i + 1) xs.length).map pre.count)) =
        (x - pre.count i + pre.count i + post.count i) + 2 ^ w *
          (encW w (fireL pre post (i + 1) xs) +
            encW w ((List.range' (i + 1) xs.length).map pre.count)) := by ring
    rw [e1, this, Nat.sub_add_cancel h0]
    ring

/-- Firing in the packed encoding: add the output vector, subtract the input vector. -/
theorem encW_fire (w : ℕ) (tr : PTrans) (xs : List ℕ) (hen : enabledL xs tr.pre = true)
    (hpre : ∀ p ∈ tr.pre, p < xs.length) (hpost : ∀ p ∈ tr.post, p < xs.length) :
    encW w xs + (fentry w tr).2.2.1 - (fentry w tr).2.1 =
      encW w (fireL tr.pre tr.post 0 xs) := by
  have := encW_fireL (w := w) tr.pre tr.post xs 0 fun k hk => by
    simp only [enabledL, List.all_eq_true, decide_eq_true_eq] at hen
    by_cases hp : k ∈ tr.pre
    · have := hen k hp
      rwa [Nat.zero_add, List.getD_eq_getElem _ _ hk] at *
    · rw [Nat.zero_add, List.count_eq_zero_of_not_mem hp]; exact Nat.zero_le _
  simp only [fentry, ← List.range_eq_range', encW_range_count w _ _ hpre,
    encW_range_count w _ _ hpost] at this ⊢
  omega

theorem fOk_spec {w : ℕ} {xs : List ℕ} (hg : ∀ x ∈ xs, x < 2 ^ w) (t : PTrans)
    (h : fOk (2 ^ w - 1) (2 ^ w) (encW w xs) (fentry w t).2.2.2 = true) :
    ∀ x ∈ fireL t.pre t.post 0 xs, x < 2 ^ w := by
  simp only [fOk, fentry, kall_eq, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, field_eq, encW_field hg,
    Nat.blt_eq] at h
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [getElem_fireL, Nat.zero_add]
  have hk' : k < xs.length := by rwa [length_fireL] at hk
  have hx' : xs[k] < 2 ^ w := hg _ (List.getElem_mem hk')
  by_cases hp : k ∈ t.post
  · have := h k hp
    rwa [List.getD_eq_getElem _ _ hk'] at this
  · rw [List.count_eq_zero_of_not_mem hp]; omega

theorem mem_succ_iff {xs : List ℕ} {t : Fin N.trans.length} {m : List ℕ} :
    (t, m) ∈ N.succ xs ↔ enabledL xs (N.tr t).pre = true ∧
      m = fireL (N.tr t).pre (N.tr t).post 0 xs := by
  simp only [succ, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨t', h⟩
    split_ifs at h with hen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hen, rfl⟩
  · rintro ⟨hen, rfl⟩
    exact ⟨t, by simp [hen]⟩

/-- **The fast successor function encodes the net** on markings below `2^w`. -/
theorem encodes (hwf : N.wf = true) (w : ℕ) :
    Encodes N.explicit.toLTS (GoodW w N.places) (encW w) Fin.val
      (fsucc (2 ^ w - 1) (2 ^ w) (N.ftable w)) := by
  have hlen : (N.ftable w).length = N.trans.length := by simp [ftable]
  have hget : ∀ k (hk : k < (N.ftable w).length),
      (N.ftable w)[k] = fentry w (N.tr ⟨k, by rwa [hlen] at hk⟩) := by
    intro k hk; simp [ftable, tr]
  have hfire : ∀ xs (t : Fin N.trans.length), GoodW w N.places xs →
      enabledL xs (N.tr t).pre = true →
      encW w xs + (fentry w (N.tr t)).2.2.1 - (fentry w (N.tr t)).2.1 =
        encW w (fireL (N.tr t).pre (N.tr t).post 0 xs) := by
    intro xs t hg hen
    exact encW_fire w _ xs hen (fun p hp => hg.1 ▸ ((wf_spec hwf).2 t).1 p hp)
      (fun p hp => hg.1 ▸ ((wf_spec hwf).2 t).2 p hp)
  refine ⟨fun xs hg i m' hm => ?_, fun xs t xs' hg hst => ?_⟩
  · obtain ⟨k, hk, rfl, hen, rfl, hok⟩ := mem_fsuccAux.1 hm
    have hkn : k < N.trans.length := by rwa [hlen] at hk
    let t : Fin N.trans.length := ⟨k, hkn⟩
    rw [hget k hk] at hen hok
    simp only [Nat.zero_add] at *
    rw [fEnabled_spec hg.2] at hen
    refine ⟨t, fireL (N.tr t).pre (N.tr t).post 0 xs, rfl, ?_, ?_, ?_⟩
    · change (t, _) ∈ N.succ xs
      exact mem_succ_iff.2 ⟨hen, rfl⟩
    · rw [hget k hk]; exact (hfire xs t hg hen).symm
    · exact ⟨by rw [length_fireL, hg.1], fOk_spec hg.2 _ hok.symm⟩
  · change (t, xs') ∈ N.succ xs at hst
    obtain ⟨hen, rfl⟩ := mem_succ_iff.1 hst
    have hk : t.val < (N.ftable w).length := by rw [hlen]; exact t.isLt
    refine ⟨fOk (2 ^ w - 1) (2 ^ w) (encW w xs) (fentry w (N.tr t)).2.2.2, ?_,
      fun hok => ⟨by rw [length_fireL, hg.1], fOk_spec hg.2 _ hok⟩⟩
    refine mem_fsuccAux.2 ⟨t.val, hk, by simp, ?_, ?_, ?_⟩
    · rw [hget _ hk, fEnabled_spec hg.2]; exact hen
    · rw [hget _ hk]; exact (hfire xs t hg hen).symm
    · rw [hget _ hk]

theorem testBit_imask (t : Fin N.trans.length) : N.imask.testBit t.val = (N.tr t).internal := by
  rw [imask, testBit_mask]
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, Fin.val_inj,
    exists_eq_right]
  cases (N.tr t).internal <;> simp

/-! ### The fast check for nets -/

variable (N) in
/-- **The fast check** for a net packed with `w` bits per place.  The literals `B`, `fm`,
`tb`, `k` and `s₀` are compared once with the values they stand for. -/
noncomputable def checkFast (w B fm : ℕ) (tb : List FEntry) (k : ℕ) (dl ll lv : Bool) (s₀ : ℕ)
    (c : Fast.Cert) : Bool :=
  N.wf && Nat.beq B (2 ^ w) && Nat.beq fm (B - 1) && kbeqList feq tb (N.ftable w) &&
    Nat.beq k (cond ll N.imask 0) && Nat.beq s₀ (encW w N.init) &&
    N.init.all (fun x => decide (x < B)) &&
    Fast.check (fsucc fm B tb) k N.trans.length dl lv s₀ c

variable (N) in
/-- The checks of `checkFast` on the literals, before the state space. -/
noncomputable def checkFastPre (w B fm : ℕ) (tb : List FEntry) (k : ℕ) (ll : Bool) (s₀ : ℕ) :
    Bool :=
  N.wf && Nat.beq B (2 ^ w) && Nat.beq fm (B - 1) && kbeqList feq tb (N.ftable w) &&
    Nat.beq k (cond ll N.imask 0) && Nat.beq s₀ (encW w N.init) &&
    N.init.all (fun x => decide (x < B))

/-- `checkFast` from its parts (`Fast.check_of_parts`). -/
theorem checkFast_of_parts {w B fm k s₀ : ℕ} {tb : List FEntry} {dl ll lv : Bool} {c : Fast.Cert}
    (h₁ : N.checkFastPre w B fm tb k ll s₀ = true)
    (h₂ : Fast.checkHead (fsucc fm B tb) N.trans.length lv s₀ c = true)
    (h₃ : Fast.checkPart (fsucc fm B tb) k dl lv c 0 0 = true) :
    N.checkFast w B fm tb k dl ll lv s₀ c = true := by
  change (N.checkFastPre w B fm tb k ll s₀ && Fast.check (fsucc fm B tb) k N.trans.length dl lv s₀ c) = true
  rw [h₁, Fast.check_of_parts h₂ h₃]; rfl

theorem of_checkFast {w B fm k s₀ : ℕ} {tb : List FEntry} {dl ll lv : Bool} {c : Fast.Cert}
    (h : N.checkFast w B fm tb k dl ll lv s₀ c = true) :
    (dl = true → N.toNet.lts.DeadlockFree N.M₀) ∧
      (ll = true → N.toNet.lts.LivelockFree N.Internal N.M₀) ∧
      (lv = true → N.toNet.lts.Live N.M₀) := by
  simp only [checkFast, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwf, hB⟩, hfm⟩, htb⟩, hk⟩, hs₀⟩, hinit⟩, hc⟩ := h
  rw [eq_of_kbeqList (fun _ _ => eq_of_feq) htb] at hc
  rw [Nat.eq_of_beq_eq_true hB] at hfm hc hinit
  rw [Nat.eq_of_beq_eq_true hfm, Nat.eq_of_beq_eq_true hs₀] at hc
  have hg₀ : GoodW w N.places N.init :=
    ⟨(wf_spec hwf).1, by simpa using hinit⟩
  obtain ⟨hd, hl, hv⟩ := Fast.of_check (encodes hwf w) Fin.val_injective hg₀ hc
  rw [← enc_M₀ hwf] at hd hl hv
  refine ⟨fun hdl => (bisim hwf).deadlockFree_iff.1 (hd hdl), fun hll => ?_,
    fun hlv => (bisim hwf).live_iff.1 fun t => hv hlv t t.isLt⟩
  rw [Nat.eq_of_beq_eq_true hk, hll] at hl
  have : (fun t : Fin N.trans.length => (cond true N.imask 0).testBit t.val = true) =
      fun t => (N.tr t).internal = true := by
    funext t; rw [Bool.cond_true, testBit_imask]
  rw [this] at hl
  exact (bisim hwf).livelockFree_iff.1 hl

/-- **A successful fast check proves the design correct.** -/
theorem correct_of_checkFast {w B fm k s₀ : ℕ} {tb : List FEntry} {c : Fast.Cert}
    (h : N.checkFast w B fm tb k true true true s₀ c = true) : N.Correct :=
  let h := of_checkFast h
  ⟨h.1 rfl, h.2.1 rfl, h.2.2 rfl⟩

theorem deadlockFree_of_checkFast {w B fm k s₀ : ℕ} {tb : List FEntry} {ll lv : Bool}
    {c : Fast.Cert} (h : N.checkFast w B fm tb k true ll lv s₀ c = true) :
    N.toNet.lts.DeadlockFree N.M₀ :=
  (of_checkFast h).1 rfl

theorem livelockFree_of_checkFast {w B fm k s₀ : ℕ} {tb : List FEntry} {dl lv : Bool}
    {c : Fast.Cert} (h : N.checkFast w B fm tb k dl true lv s₀ c = true) :
    N.toNet.lts.LivelockFree N.Internal N.M₀ :=
  (of_checkFast h).2.1 rfl

theorem live_of_checkFast {w B fm k s₀ : ℕ} {tb : List FEntry} {dl ll : Bool}
    {c : Fast.Cert} (h : N.checkFast w B fm tb k dl ll true s₀ c = true) :
    N.toNet.lts.Live N.M₀ :=
  (of_checkFast h).2.2 rfl

end PNet

end AsyncLean

/-! ### Untrusted certificate generation -/

namespace AsyncLean

namespace PNet

/-- Compiled counterpart of `fsucc` (untrusted). -/
def fsuccC (fm B : ℕ) (tb : List FEntry) (m : ℕ) : List (ℕ × ℕ × Bool) :=
  go tb 0
where
  go : List FEntry → ℕ → List (ℕ × ℕ × Bool)
    | [], _ => []
    | e :: es, i =>
      if e.1.all (fun pk => pk.2 ≤ (m >>> pk.1) &&& fm) then
        (i, m + e.2.2.1 - e.2.1,
          e.2.2.2.all fun c => ((m >>> c.1) &&& fm) - c.2.1 + c.2.2 < B) :: go es (i + 1)
      else go es (i + 1)

variable (N : PNet)

/-- Choose a field width and compute a fast certificate (untrusted).  Returns the width. -/
def mkFastCert (dl ll lv : Bool) (fuel : ℕ := 1000000) : Except String (ℕ × Fast.Cert) := do
  let maxArc := N.trans.foldl (fun a t => max a (max (t.pre.length) (t.post.length))) 1
  let maxInit := N.init.foldl max 1
  let w₀ := Nat.log2 (max maxArc maxInit) + 1
  let mut last := "no width"
  for w in [w₀, w₀ + 1, w₀ + 2, w₀ + 4, w₀ + 8, 32, 64] do
    let B := 2 ^ w
    match Fast.mkCert (fsuccC (B - 1) B (N.ftable w)) (cond ll N.imask 0) N.trans.length dl lv
        fuel (encW w N.init) with
    | .ok c => return (w, c)
    | .error "overflow" => last := "overflow"
    | .error e => throw e
  throw last

end PNet

end AsyncLean
