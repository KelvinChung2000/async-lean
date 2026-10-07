/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Fast
import AsyncLean.Checker.Petri
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity.Basic

/-!
# Markings packed by a layout of fields

`AsyncLean.Checker.FastPetri` packs a marking into one number with a field of `w` bits per
place.  Most places of an asynchronous controller belong to a *component*: a set of places
of which exactly one is marked in every reachable marking (a signal is high or low, a stage
is full or empty, a philosopher thinks, waits or eats).  Such a component needs only the
bits of the index of its marked place, so a FIFO stage takes one bit instead of two.

A *layout* (`List LField`) lists fields of bits.  The field of a component holds the index
in `ps` of its marked place; the field of a single place holds its count.  The packed value
of a marking is a **linear** function of the marking (`PNet.encV`): place `ps[i]` of a field
at bit `sh` weighs `2^sh * i` (a component) or `2^sh` (a counter).  Firing a transition
therefore adds a constant and subtracts a constant, and its enabledness is a conjunction of
tests on fields (`Aff.Test`).

The generic successor function `Aff.asucc` reads a table of such transitions (`Aff.Tr`), and
`PNet.encodesL` proves that the table of a net (`PNet.atable`) faithfully encodes the net on
the markings that respect the layout (`PNet.GoodL`), provided the layout passes the
structural check `PNet.layoutOk`: every component is balanced by every transition (it
consumes from it exactly as many tokens as it produces, at most one), and every place a
transition consumes from lies in some field.  Places that are only ever produced into
(sinks, possibly unbounded) need no field.
-/

namespace AsyncLean

namespace Aff

open Fast

/-- A test on the field of `w` bits at bit `sh`: `kind = 0` asks for the value `c`, `kind = 1`
for at least `c`, and any other `kind` for at most `c`. -/
structure Test where
  sh : ℕ
  w : ℕ
  c : ℕ
  kind : ℕ
deriving DecidableEq, Repr, Inhabited

/-- A transition on packed states: when every `guard` test holds, it adds `add` and subtracts
`sub`; the `ok` tests say that the target is still faithfully encoded. -/
structure Tr where
  guard : List Test
  ok : List Test
  add : ℕ
  sub : ℕ
deriving DecidableEq, Repr, Inhabited

/-- The field of `w` bits at bit `sh`. -/
noncomputable def fld (x sh w : ℕ) : ℕ := Nat.land (Nat.shiftRight x sh) (Nat.sub (Nat.pow 2 w) 1)

/-- Comparison of a field value `v` with `c` according to `kind`. -/
noncomputable def cmp (kind v c : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) (Nat.beq v c)
    (fun k _ => Nat.rec (motive := fun _ => Bool) (Nat.ble c v) (fun _ _ => Nat.ble v c) k) kind

/-- A test, on the state `x`. -/
noncomputable def ttest (x : ℕ) (a : Test) : Bool := cmp a.kind (fld x a.sh a.w) a.c

/-- All tests hold. -/
noncomputable def tall (x : ℕ) (ts : List Test) : Bool := kall ts (ttest x)

/-- Successors along the table, numbering transitions from `i`. -/
noncomputable def asuccAux (x : ℕ) (tb : List Tr) : ℕ → List (ℕ × ℕ × Bool) :=
  List.rec (motive := fun _ => ℕ → List (ℕ × ℕ × Bool)) (fun _ => [])
    (fun e _ rec i => Bool.rec (motive := fun _ => List (ℕ × ℕ × Bool)) (rec (i + 1))
      ((i, x + e.add - e.sub, tall x e.ok) :: rec (i + 1)) (tall x e.guard)) tb

/-- **The successor function of a table**: label, target and `ok` flag. -/
noncomputable def asucc (tb : List Tr) (x : ℕ) : List (ℕ × ℕ × Bool) := asuccAux x tb 0

theorem fld_eq (x sh w : ℕ) : fld x sh w = x / 2 ^ sh % 2 ^ w := by
  change (x >>> sh) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem cmp_eq (kind v c : ℕ) :
    cmp kind v c = if kind = 0 then decide (v = c) else if kind = 1 then decide (c ≤ v)
      else decide (v ≤ c) := by
  rcases kind with _ | _ | k
  · change Nat.beq v c = _
    simp only [↓reduceIte]
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl v⟩
  · change Nat.ble c v = _
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.ble_eq]
  · change Nat.ble v c = _
    simp only [Nat.add_one_ne_zero, ↓reduceIte, show k + 1 + 1 ≠ 1 by omega]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.ble_eq]

@[simp] theorem ttest_mk (x sh w c kind : ℕ) :
    ttest x ⟨sh, w, c, kind⟩ = cmp kind (fld x sh w) c := rfl

@[simp] theorem cmp_zero (v c : ℕ) : cmp 0 v c = decide (v = c) := by rw [cmp_eq]; rfl
@[simp] theorem cmp_one (v c : ℕ) : cmp 1 v c = decide (c ≤ v) := by rw [cmp_eq]; rfl
@[simp] theorem cmp_two (v c : ℕ) : cmp 2 v c = decide (v ≤ c) := by rw [cmp_eq]; rfl

theorem tall_iff {x : ℕ} {ts : List Test} : tall x ts = true ↔ ∀ a ∈ ts, ttest x a = true := by
  simp [tall, kall_eq]

theorem mem_asuccAux {x : ℕ} {tb : List Tr} {i₀ j m' : ℕ} {b : Bool} :
    (j, m', b) ∈ asuccAux x tb i₀ ↔ ∃ k, ∃ hk : k < tb.length, j = i₀ + k ∧
      tall x tb[k].guard = true ∧ m' = x + tb[k].add - tb[k].sub ∧ b = tall x tb[k].ok := by
  induction tb generalizing i₀ with
  | nil => simp [asuccAux]
  | cons e tb ih =>
    change (j, m', b) ∈ Bool.rec (motive := fun _ => List (ℕ × ℕ × Bool))
      (asuccAux x tb (i₀ + 1))
      ((i₀, x + e.add - e.sub, tall x e.ok) :: asuccAux x tb (i₀ + 1)) (tall x e.guard) ↔ _
    constructor
    · intro h
      have hrest : (j, m', b) ∈ asuccAux x tb (i₀ + 1) → ∃ k, ∃ hk : k < (e :: tb).length,
          j = i₀ + k ∧ tall x (e :: tb)[k].guard = true ∧
          m' = x + (e :: tb)[k].add - (e :: tb)[k].sub ∧ b = tall x (e :: tb)[k].ok := by
        intro h'
        obtain ⟨k, hk, rfl, h1, h2, h3⟩ := ih.1 h'
        exact ⟨k + 1, by simpa using hk, by omega, h1, h2, h3⟩
      cases hen : tall x e.guard
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
        cases tall x e.guard
        · exact this
        · exact List.mem_cons_of_mem _ this

theorem mem_asucc {tb : List Tr} {x j m' : ℕ} {b : Bool} :
    (j, m', b) ∈ asucc tb x ↔ ∃ hj : j < tb.length, tall x tb[j].guard = true ∧
      m' = x + tb[j].add - tb[j].sub ∧ b = tall x tb[j].ok := by
  rw [asucc, mem_asuccAux]
  constructor
  · rintro ⟨k, hk, rfl, h⟩; simpa using ⟨hk, h⟩
  · rintro ⟨hj, h⟩; exact ⟨j, hj, by simp, h⟩

end Aff

/-! ### Layouts -/

/-- A field of a layout: bits `sh … sh + w - 1`.  The field of a component (`comp`) holds the
index in `ps` of its marked place; otherwise `ps` is a single place and the field holds its
count. -/
structure LField where
  sh : ℕ
  w : ℕ
  ps : List ℕ
  comp : Bool
deriving DecidableEq, Repr, Inhabited

namespace LField

/-- `Σ i, coef i * g (ps[i])` with `coef i = i + i₀` for a component and `1` otherwise. -/
def wsum (comp : Bool) (g : ℕ → ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | i, p :: ps => (if comp then i else 1) * g p + wsum comp g (i + 1) ps

/-- The value of a field for the place vector `g`. -/
def val (f : LField) (g : ℕ → ℕ) : ℕ := wsum f.comp g 0 f.ps

theorem wsum_add {comp : Bool} {a b c d : ℕ → ℕ} :
    ∀ {ps : List ℕ} (i : ℕ), (∀ p ∈ ps, a p + b p = c p + d p) →
      wsum comp a i ps + wsum comp b i ps = wsum comp c i ps + wsum comp d i ps
  | [], _, _ => rfl
  | p :: ps, i, h => by
    have h1 := h p List.mem_cons_self
    have h2 := wsum_add (comp := comp) (a := a) (b := b) (c := c) (d := d) (ps := ps) (i + 1)
      fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [wsum]
    have e : (if comp = true then i else 1) * a p + (if comp = true then i else 1) * b p =
        (if comp = true then i else 1) * c p + (if comp = true then i else 1) * d p := by
      rw [← Nat.mul_add, ← Nat.mul_add, h1]
    omega

/-- The value of a component field in which exactly the place at index `j` is marked. -/
theorem wsum_comp_of {g : ℕ → ℕ} :
    ∀ {ps : List ℕ} (i : ℕ), (ps.map g).sum = 1 →
      ∃ j, ∃ hj : j < ps.length, g ps[j] = 1 ∧ wsum true g i ps = i + j ∧
        ∀ k (hk : k < ps.length), k ≠ j → g ps[k] = 0
  | [], _, h => by simp at h
  | p :: ps, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    rcases Nat.eq_zero_or_pos (g p) with hp | hp
    · rw [hp, Nat.zero_add] at h
      obtain ⟨j, hj, h1, h2, h3⟩ := wsum_comp_of (ps := ps) (i + 1) h
      refine ⟨j + 1, by simpa using hj, by simpa using h1, ?_, ?_⟩
      · simp only [wsum, ↓reduceIte, hp, Nat.mul_zero, Nat.zero_add, h2]; omega
      · intro k hk hkj
        cases k with
        | zero => simpa using hp
        | succ k => simpa using h3 k (by simpa using hk) (by omega)
    · have hp1 : g p = 1 := by omega
      have hs : (ps.map g).sum = 0 := by omega
      have hz : ∀ q ∈ ps, g q = 0 := fun q hq =>
        List.sum_eq_zero_iff_forall_eq_nat.1 hs _ (List.mem_map_of_mem hq)
      have hw : ∀ (i : ℕ) (qs : List ℕ), (∀ q ∈ qs, g q = 0) → wsum true g i qs = 0 := by
        intro i qs hq
        induction qs generalizing i with
        | nil => rfl
        | cons q qs ih =>
          simp only [wsum, ↓reduceIte, hq q List.mem_cons_self, Nat.mul_zero, Nat.zero_add]
          exact ih _ fun r hr => hq r (List.mem_cons_of_mem _ hr)
      refine ⟨0, by simp, by simpa using hp1, ?_, ?_⟩
      · simp only [wsum, ↓reduceIte, hp1, Nat.mul_one, hw _ ps hz]
      · intro k hk hk0
        cases k with
        | zero => exact absurd rfl hk0
        | succ k => exact hz _ (List.getElem_mem (by simpa using hk))

theorem wsum_count (g : ℕ → ℕ) (i p : ℕ) : wsum false g i [p] = g p := by simp [wsum]

theorem le_sum_nat {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.sum
  | [], h => by simp at h
  | b :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_nat h; simp only [List.sum_cons]; omega

end LField

namespace PNet

open Aff Fast

/-- The packed value `Σ 2^sh * val` of the place vector `g` under a layout. -/
def encV : List LField → (ℕ → ℕ) → ℕ
  | [], _ => 0
  | f :: L, g => 2 ^ f.sh * f.val g + encV L g

theorem encV_add {a b c d : ℕ → ℕ} :
    ∀ {L : List LField}, (∀ f ∈ L, ∀ p ∈ f.ps, a p + b p = c p + d p) →
      encV L a + encV L b = encV L c + encV L d
  | [], _ => rfl
  | f :: L, h => by
    have h1 := LField.wsum_add (comp := f.comp) (ps := f.ps) 0 (h f List.mem_cons_self)
    have h2 := encV_add (L := L) fun g hg => h g (List.mem_cons_of_mem _ hg)
    simp only [encV, LField.val]
    have e : 2 ^ f.sh * LField.wsum f.comp a 0 f.ps + 2 ^ f.sh * LField.wsum f.comp b 0 f.ps =
        2 ^ f.sh * LField.wsum f.comp c 0 f.ps + 2 ^ f.sh * LField.wsum f.comp d 0 f.ps := by
      rw [← Nat.mul_add, ← Nat.mul_add, h1]
    omega

theorem dvd_encV {c : ℕ} (g : ℕ → ℕ) : ∀ {L : List LField}, (∀ f ∈ L, c ≤ f.sh) →
    2 ^ c ∣ encV L g
  | [], _ => dvd_zero _
  | f :: L, h => by
    refine Nat.dvd_add (Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (h f List.mem_cons_self)) _) ?_
    exact dvd_encV g fun f' hf' => h f' (List.mem_cons_of_mem _ hf')

/-- **Reading a field back.** In a layout whose fields are ordered and disjoint, and whose
values fit their widths, each field reads back its value. -/
theorem encV_fld {g : ℕ → ℕ} : ∀ {L : List LField},
    L.Pairwise (fun f f' => f.sh + f.w ≤ f'.sh) → (∀ f ∈ L, f.val g < 2 ^ f.w) →
      ∀ f ∈ L, fld (encV L g) f.sh f.w = f.val g
  | [], _, _ => by simp
  | f :: L, hp, hv => by
    rw [List.pairwise_cons] at hp
    have hfv := hv f List.mem_cons_self
    obtain ⟨E, hE⟩ := dvd_encV g (c := f.sh + f.w) (L := L) fun f' hf' => hp.1 f' hf'
    have hlt : 2 ^ f.sh * f.val g < 2 ^ (f.sh + f.w) := by
      rw [Nat.pow_add]; exact Nat.mul_lt_mul_of_pos_left hfv (by positivity)
    intro f' hf'
    simp only [encV, fld_eq, hE]
    rcases List.mem_cons.1 hf' with rfl | hf'
    · rw [Nat.pow_add, Nat.mul_assoc, Nat.add_mul_div_left _ _ (by positivity),
        Nat.mul_div_cancel_left _ (by positivity), Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hfv]
    · have ih := encV_fld hp.2 (fun f'' h'' => hv f'' (List.mem_cons_of_mem _ h'')) f' hf'
      rw [fld_eq, hE] at ih
      obtain ⟨d, hd⟩ : ∃ d, f'.sh = f.sh + f.w + d :=
        ⟨_, (Nat.add_sub_cancel' (hp.1 f' hf')).symm⟩
      rw [hd, Nat.pow_add 2 (f.sh + f.w) d, ← Nat.div_div_eq_div_mul] at ih ⊢
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add]
      rw [Nat.mul_div_cancel_left _ (by positivity)] at ih
      exact ih

variable (N : PNet)

/-! ### The table of a net under a layout -/

/-- The place vector of a marking (zero beyond the places). -/
def vec (M : Marking (Fin N.places)) (p : ℕ) : ℕ := if h : p < N.places then M ⟨p, h⟩ else 0

/-- The guard tests of a field for a transition. -/
def fguard (t : PTrans) (f : LField) : List Test :=
  if f.comp then
    ((List.range f.ps.length).filter fun i => 0 < t.pre.count (f.ps.getD i 0)).map
      fun i => ⟨f.sh, f.w, i, 0⟩
  else
    (f.ps.filter fun p => 0 < t.pre.count p).map fun p => ⟨f.sh, f.w, t.pre.count p, 1⟩

/-- The tests of a field that keep the target faithfully encoded (no counter overflows). -/
def fok (t : PTrans) (f : LField) : List Test :=
  if f.comp then []
  else (f.ps.filter fun p => t.pre.count p < t.post.count p).map
    fun p => ⟨f.sh, f.w, 2 ^ f.w - 1 + t.pre.count p - t.post.count p, 2⟩

/-- The packed transition of `t` under the layout `L`. -/
def atr (L : List LField) (t : PTrans) : Tr where
  guard := L.flatMap (fguard t)
  ok := L.flatMap (fok t)
  add := encV L t.post.count
  sub := encV L t.pre.count

/-- **The table of the net** under the layout `L`. -/
def atable (L : List LField) : List Tr := N.trans.map (atr L)

/-- Markings faithfully represented by the layout: one token in each component, and each
counter within its width. -/
def GoodL (L : List LField) (M : Marking (Fin N.places)) : Prop :=
  ∀ f ∈ L, (f.comp = true → (f.ps.map (N.vec M)).sum = 1) ∧
    (f.comp = false → ∀ p ∈ f.ps, N.vec M p < 2 ^ f.w)

/-- Fields are ordered and disjoint. -/
def sortedL : List LField → Bool
  | [] => true
  | f :: L => L.all (fun f' => f.sh + f.w ≤ f'.sh) && sortedL L

/-- **The structural check of a layout.** -/
def layoutOk (L : List LField) : Bool :=
  N.wf && sortedL L &&
    L.all (fun f => f.ps.all (· < N.places) &&
      (if f.comp then decide (f.ps.length ≤ 2 ^ f.w) &&
        N.trans.all (fun t => (f.ps.map t.pre.count).sum == (f.ps.map t.post.count).sum &&
          decide ((f.ps.map t.pre.count).sum ≤ 1)) &&
        (f.ps.map fun p => N.init.getD p 0).sum == 1
      else f.ps.length == 1 &&
        N.trans.all (fun t => f.ps.all fun p => decide (t.post.count p ≤ t.pre.count p + (2 ^ f.w - 1))) &&
        f.ps.all fun p => decide (N.init.getD p 0 < 2 ^ f.w))) &&
    N.trans.all (fun t => t.pre.all fun p => L.any fun f => f.ps.contains p)

/-- The packed value of a marking. -/
def encL (L : List LField) (M : Marking (Fin N.places)) : ℕ := encV L (N.vec M)

variable {N}

theorem sortedL_spec : ∀ {L : List LField}, sortedL L = true →
    L.Pairwise (fun f f' => f.sh + f.w ≤ f'.sh)
  | [], _ => List.Pairwise.nil
  | f :: L, h => by
    simp only [sortedL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact List.Pairwise.cons h.1 (sortedL_spec h.2)

structure LayoutSpec (N : PNet) (L : List LField) : Prop where
  wf : N.wf = true
  sorted : L.Pairwise (fun f f' => f.sh + f.w ≤ f'.sh)
  places : ∀ f ∈ L, ∀ p ∈ f.ps, p < N.places
  compLen : ∀ f ∈ L, f.comp = true → f.ps.length ≤ 2 ^ f.w
  compBal : ∀ f ∈ L, f.comp = true → ∀ t ∈ N.trans,
    (f.ps.map t.pre.count).sum = (f.ps.map t.post.count).sum ∧ (f.ps.map t.pre.count).sum ≤ 1
  compInit : ∀ f ∈ L, f.comp = true → (f.ps.map fun p => N.init.getD p 0).sum = 1
  cntLen : ∀ f ∈ L, f.comp = false → f.ps.length = 1
  cntOk : ∀ f ∈ L, f.comp = false → ∀ t ∈ N.trans, ∀ p ∈ f.ps,
    t.post.count p ≤ t.pre.count p + (2 ^ f.w - 1)
  cntInit : ∀ f ∈ L, f.comp = false → ∀ p ∈ f.ps, N.init.getD p 0 < 2 ^ f.w
  cover : ∀ t ∈ N.trans, ∀ p ∈ t.pre, ∃ f ∈ L, p ∈ f.ps

theorem layoutOk_spec {L : List LField} (h : N.layoutOk L = true) : LayoutSpec N L := by
  simp only [layoutOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨hwf, hs⟩, hf⟩, hc⟩ := h
  refine ⟨hwf, sortedL_spec hs, fun f hf' p hp => by simpa using (hf f hf').1 p hp,
    fun f hf' hc' => ?_, fun f hf' hc' => ?_, fun f hf' hc' => ?_, fun f hf' hc' => ?_,
    fun f hf' hc' => ?_, fun f hf' hc' => ?_, fun t ht p hp => hc t ht p hp⟩
  all_goals have h := (hf f hf').2
  all_goals first
    | (rw [hc'] at h; simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, beq_iff_eq] at h)
    | (rw [hc'] at h; simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h)
  · exact h.1.1
  · exact fun t ht => h.1.2 t ht
  · exact h.2
  · exact h.1.1
  · exact fun t ht p hp => h.1.2 t ht p hp
  · exact fun p hp => h.2 p hp

theorem vec_lt {M : Marking (Fin N.places)} {p : ℕ} (hp : p < N.places) :
    N.vec M p = M ⟨p, hp⟩ := by simp [vec, hp]

/-- Every field of a good marking fits its width. -/
theorem val_lt {L : List LField} (hL : LayoutSpec N L) {M : Marking (Fin N.places)}
    (hg : N.GoodL L M) : ∀ f ∈ L, f.val (N.vec M) < 2 ^ f.w := by
  intro f hf
  cases hc : f.comp
  · have h1 := hL.cntLen f hf hc
    obtain ⟨p, hp⟩ := List.length_eq_one_iff.1 h1
    have := (hg f hf).2 hc p (by rw [hp]; exact List.mem_singleton_self _)
    simpa [LField.val, hc, hp, LField.wsum] using this
  · obtain ⟨j, hj, -, hv, -⟩ := LField.wsum_comp_of (g := N.vec M) (ps := f.ps) 0 ((hg f hf).1 hc)
    simp only [LField.val, hc, hv, Nat.zero_add]
    exact Nat.lt_of_lt_of_le hj (hL.compLen f hf hc)

theorem fld_encL {L : List LField} (hL : LayoutSpec N L) {M : Marking (Fin N.places)}
    (hg : N.GoodL L M) {f : LField} (hf : f ∈ L) :
    fld (N.encL L M) f.sh f.w = f.val (N.vec M) :=
  encV_fld hL.sorted (val_lt hL hg) f hf

theorem count_pre_eq (hwf : N.wf = true) (t : Fin N.trans.length) (p : ℕ) :
    (N.tr t).pre.count p = if h : p < N.places then N.toNet.pre t ⟨p, h⟩ else 0 := by
  split_ifs with h
  · rfl
  · exact List.count_eq_zero_of_not_mem fun hp => h (((wf_spec hwf).2 t).1 p hp)

theorem count_post_eq (hwf : N.wf = true) (t : Fin N.trans.length) (p : ℕ) :
    (N.tr t).post.count p = if h : p < N.places then N.toNet.post t ⟨p, h⟩ else 0 := by
  split_ifs with h
  · rfl
  · exact List.count_eq_zero_of_not_mem fun hp => h (((wf_spec hwf).2 t).2 p hp)

/-- Firing in the packed encoding: add the packed output vector, subtract the input vector. -/
theorem encL_fire {L : List LField} (hL : LayoutSpec N L) {M : Marking (Fin N.places)}
    {t : Fin N.trans.length} (hen : N.toNet.Enabled M t) :
    N.encL L (N.toNet.fire M t) = N.encL L M + (atr L (N.tr t)).add - (atr L (N.tr t)).sub := by
  have h := encV_add (L := L) (a := N.vec (N.toNet.fire M t)) (b := (N.tr t).pre.count)
    (c := N.vec M) (d := (N.tr t).post.count) fun f _ p _ => by
      rw [count_pre_eq hL.wf, count_post_eq hL.wf]
      by_cases hp : p < N.places
      · simp only [vec, hp, ↓reduceDIte, Net.fire]
        have := hen ⟨p, hp⟩
        omega
      · simp [vec, hp]
  simp only [encL, atr]
  omega

/-- The guard of a field holds exactly when the transition has enough tokens in it. -/
theorem fguard_iff {L : List LField} (hL : LayoutSpec N L) {M : Marking (Fin N.places)}
    (hg : N.GoodL L M) {t : Fin N.trans.length} {f : LField} (hf : f ∈ L) :
    (∀ a ∈ fguard (N.tr t) f, ttest (N.encL L M) a = true) ↔
      ∀ p ∈ f.ps, (N.tr t).pre.count p ≤ N.vec M p := by
  have hfl := fld_encL hL hg hf
  have htr : N.tr t ∈ N.trans := List.getElem_mem _
  unfold fguard
  cases hc : f.comp
  · obtain ⟨q, hq⟩ := List.length_eq_one_iff.1 (hL.cntLen f hf hc)
    have hv : f.val (N.vec M) = N.vec M q := by simp [LField.val, hc, hq, LField.wsum]
    rw [hq]
    simp only [Bool.false_eq_true, ↓reduceIte, List.filter_cons, List.filter_nil,
      List.mem_singleton, forall_eq]
    by_cases h0 : 0 < (N.tr t).pre.count q
    · simp only [h0, decide_true, ↓reduceIte, List.map_cons, List.map_nil, List.mem_singleton,
        forall_eq, ttest_mk, cmp_one, decide_eq_true_eq, hfl, hv]
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, List.map_nil,
        List.not_mem_nil, false_imp_iff, implies_true, true_iff]
      omega
  · simp only [↓reduceIte, List.mem_map, List.mem_filter, List.mem_range, forall_exists_index,
      and_imp, decide_eq_true_eq]
    obtain ⟨j, hj, h1, hv, h0⟩ :=
      LField.wsum_comp_of (g := N.vec M) (ps := f.ps) 0 ((hg f hf).1 hc)
    have hval : f.val (N.vec M) = j := by simp [LField.val, hc, hv]
    obtain ⟨hbal, hle⟩ := hL.compBal f hf hc _ htr
    have hsum : ∀ i (hi : i < f.ps.length), (N.tr t).pre.count f.ps[i] ≤ 1 := by
      intro i hi
      exact le_trans (LField.le_sum_nat (List.mem_map_of_mem (f := fun a => (N.tr t).pre.count a)
        (List.getElem_mem hi))) hle
    constructor
    · intro h p hp
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
      rcases Nat.eq_zero_or_pos ((N.tr t).pre.count f.ps[i]) with hz | hz
      · rw [hz]; exact Nat.zero_le _
      · have := h _ i hi (by rwa [List.getD_eq_getElem _ _ hi]) rfl
        rw [ttest_mk, cmp_zero, hfl, hval, decide_eq_true_eq] at this
        subst this
        rw [h1]; exact hsum _ hi
    · rintro h a i hi hpos rfl
      rw [List.getD_eq_getElem _ _ hi] at hpos
      have := h _ (List.getElem_mem hi)
      rw [ttest_mk, cmp_zero, hfl, hval, decide_eq_true_eq]
      by_contra hne
      have := h0 i hi (Ne.symm hne)
      omega

theorem guard_iff {L : List LField} (hL : LayoutSpec N L) {M : Marking (Fin N.places)}
    (hg : N.GoodL L M) (t : Fin N.trans.length) :
    tall (N.encL L M) (atr L (N.tr t)).guard = true ↔ N.toNet.Enabled M t := by
  rw [tall_iff]
  simp only [atr, List.mem_flatMap, forall_exists_index, and_imp]
  constructor
  · intro h p
    change (N.tr t).pre.count p.val ≤ M p
    rcases Nat.eq_zero_or_pos ((N.tr t).pre.count p.val) with hz | hz
    · rw [hz]; exact Nat.zero_le _
    · obtain ⟨f, hf, hpf⟩ := hL.cover _ (List.getElem_mem _) p.val (List.count_pos_iff.1 hz)
      have := (fguard_iff hL hg hf).1 (fun a ha => h a f hf ha) p.val hpf
      rwa [vec_lt p.isLt] at this
  · intro hen a f hf ha
    refine (fguard_iff hL hg hf).2 (fun p hp => ?_) a ha
    have hp' := hL.places f hf p hp
    rw [vec_lt hp', count_pre_eq hL.wf]
    simp only [hp', ↓reduceDIte]
    exact hen _

theorem ok_good {L : List LField} (hL : LayoutSpec N L) {M : Marking (Fin N.places)}
    (hg : N.GoodL L M) {t : Fin N.trans.length} (hen : N.toNet.Enabled M t) :
    tall (N.encL L M) (atr L (N.tr t)).ok = true ↔ N.GoodL L (N.toNet.fire M t) := by
  have htr : N.tr t ∈ N.trans := List.getElem_mem _
  have hvec : ∀ p, N.vec (N.toNet.fire M t) p + (N.tr t).pre.count p =
      N.vec M p + (N.tr t).post.count p := by
    intro p
    rw [count_pre_eq hL.wf, count_post_eq hL.wf]
    by_cases hp : p < N.places
    · simp only [vec, hp, ↓reduceDIte, Net.fire]
      have := hen ⟨p, hp⟩
      omega
    · simp [vec, hp]
  have hpre : ∀ p, (N.tr t).pre.count p ≤ N.vec M p := by
    intro p
    rw [count_pre_eq hL.wf]
    by_cases hp : p < N.places
    · simp only [hp, ↓reduceDIte, vec_lt hp]; exact hen _
    · simp only [hp, ↓reduceDIte]; exact Nat.zero_le _
  -- components stay good whatever the ok tests say
  have hcomp : ∀ f ∈ L, f.comp = true → (f.ps.map (N.vec (N.toNet.fire M t))).sum = 1 := by
    intro f hf hc
    have h1 := (hg f hf).1 hc
    obtain ⟨hbal, -⟩ := hL.compBal f hf hc _ htr
    have : ∀ ps : List ℕ, (ps.map (N.vec (N.toNet.fire M t))).sum + (ps.map (N.tr t).pre.count).sum
        = (ps.map (N.vec M)).sum + (ps.map (N.tr t).post.count).sum := by
      intro ps
      induction ps with
      | nil => rfl
      | cons p ps ih => simp only [List.map_cons, List.sum_cons]; have := hvec p; omega
    have := this f.ps
    omega
  rw [tall_iff]
  simp only [atr, List.mem_flatMap, forall_exists_index, and_imp]
  constructor
  · intro h f hf
    refine ⟨hcomp f hf, fun hc p hp => ?_⟩
    have hv := hvec p
    have hb := (hg f hf).2 hc p hp
    by_cases hlt : (N.tr t).pre.count p < (N.tr t).post.count p
    · have := h _ f hf (by simp only [fok, hc, Bool.false_eq_true, ↓reduceIte, List.mem_map,
          List.mem_filter]; exact ⟨p, ⟨hp, by simpa using hlt⟩, rfl⟩)
      simp only [ttest_mk, cmp_two, fld_encL hL hg hf, decide_eq_true_eq] at this
      obtain ⟨q, hq⟩ := List.length_eq_one_iff.1 (hL.cntLen f hf hc)
      rw [hq, List.mem_singleton] at hp
      subst hp
      simp only [LField.val, hc, hq, LField.wsum, Bool.false_eq_true, ↓reduceIte, Nat.one_mul,
        Nat.add_zero] at this
      have := Nat.one_le_two_pow (n := f.w)
      have := hpre p
      have := hL.cntOk f hf hc _ htr p (by rw [hq]; exact List.mem_singleton_self _)
      omega
    · omega
  · intro hg' a f hf ha
    cases hc : f.comp
    · simp only [fok, hc, Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_filter] at ha
      obtain ⟨p, ⟨hp, -⟩, rfl⟩ := ha
      simp only [ttest_mk, cmp_two, fld_encL hL hg hf, decide_eq_true_eq]
      obtain ⟨q, hq⟩ := List.length_eq_one_iff.1 (hL.cntLen f hf hc)
      rw [hq, List.mem_singleton] at hp
      subst hp
      simp only [LField.val, hc, hq, LField.wsum, Bool.false_eq_true, ↓reduceIte, Nat.one_mul,
        Nat.add_zero]
      have := (hg' f hf).2 hc p (by rw [hq]; exact List.mem_singleton_self _)
      have := hvec p
      have := hpre p
      omega
    · simp [fok, hc] at ha

/-- **The table of a net encodes the net** on the markings that respect the layout. -/
theorem encodesL {L : List LField} (hL : LayoutSpec N L) :
    Encodes N.toNet.lts (N.GoodL L) (N.encL L) Fin.val (asucc (N.atable L)) := by
  have hlen : (N.atable L).length = N.trans.length := by simp [atable]
  have hget : ∀ k (hk : k < (N.atable L).length),
      (N.atable L)[k] = atr L (N.tr ⟨k, by rwa [hlen] at hk⟩) := by
    intro k hk; simp [atable, tr]
  refine ⟨fun M hg i m' hm => ?_, fun M t M' hg hst => ?_⟩
  · obtain ⟨hk, hen, rfl, hok⟩ := mem_asucc.1 hm
    rw [hget i hk] at hen hok
    rw [guard_iff hL hg] at hen
    refine ⟨⟨i, by rwa [hlen] at hk⟩, N.toNet.fire M _, rfl, ⟨hen, rfl⟩, ?_, ?_⟩
    · rw [encL_fire hL hen, hget i hk]
    · exact (ok_good hL hg hen).1 hok.symm
  · obtain ⟨hen, rfl⟩ := hst
    have hk : t.val < (N.atable L).length := by rw [hlen]; exact t.isLt
    refine ⟨tall (N.encL L M) (atr L (N.tr t)).ok, mem_asucc.2 ⟨hk, ?_, ?_, ?_⟩,
      fun hok => (ok_good hL hg hen).1 hok⟩
    · rw [hget _ hk]; exact (guard_iff hL hg t).2 hen
    · rw [hget _ hk]; exact encL_fire hL hen
    · rw [hget _ hk]

theorem goodL_M₀ {L : List LField} (hL : LayoutSpec N L) : N.GoodL L N.M₀ := by
  have hv : ∀ p ∈ (L.flatMap LField.ps), N.vec N.M₀ p = N.init.getD p 0 := by
    intro p hp
    obtain ⟨f, hf, hpf⟩ := List.mem_flatMap.1 hp
    rw [vec_lt (hL.places f hf p hpf)]; rfl
  intro f hf
  have hv' : f.ps.map (N.vec N.M₀) = f.ps.map fun p => N.init.getD p 0 :=
    List.map_congr_left fun p hp => hv p (List.mem_flatMap.2 ⟨f, hf, hp⟩)
  refine ⟨fun hc => by rw [hv']; exact hL.compInit f hf hc, fun hc p hp => ?_⟩
  rw [hv p (List.mem_flatMap.2 ⟨f, hf, hp⟩)]
  exact hL.cntInit f hf hc p hp

/-- Good markings bound every place in a field: a component place holds at most one token, a
counter place at most `2^w - 1`. -/
theorem goodL_bound {L : List LField} {M : Marking (Fin N.places)}
    (hg : N.GoodL L M) {f : LField} (hf : f ∈ L) {p : Fin N.places} (hp : p.val ∈ f.ps) :
    M p ≤ (if f.comp then 1 else 2 ^ f.w - 1) := by
  have := (hg f hf)
  cases hc : f.comp
  · have := this.2 hc p.val hp
    rw [vec_lt p.isLt, Fin.eta] at this
    simp only [Bool.false_eq_true, ↓reduceIte]; omega
  · have h1 := this.1 hc
    have := LField.le_sum_nat (List.mem_map_of_mem (f := N.vec M) hp)
    rw [h1, vec_lt p.isLt, Fin.eta] at this
    simpa using this

end PNet

end AsyncLean
