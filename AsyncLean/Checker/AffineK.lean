/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Bitmap

/-!
# Kernel-friendly evaluation of layouts

The structural check of a layout (`PNet.layoutOk`) and the table of a net (`PNet.atable`)
are written with the list library (`List.count`, `List.filter`, `List.flatMap`, …), whose
type-class instances and well-founded definitions the kernel unfolds slowly.  This file
gives the same functions written with recursors over natural numbers and `Nat.beq`, and
proves them equal to (or as strong as) the originals: `PNet.layoutSpec_of_layoutOkK` and
`PNet.katable_eq`.
-/

namespace AsyncLean

namespace PNet

open Aff Fast

/-- `List.count`, by the recursor. -/
noncomputable def kcount (p : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun x _ r => Bool.rec (motive := fun _ => ℕ) r (Nat.succ r) (Nat.beq x p)) l

/-- `(l.map f).sum`, by the recursor. -/
noncomputable def ksum (f : ℕ → ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ r => Nat.add (f x) r) l

/-- `LField.wsum`, by the recursor. -/
noncomputable def kwsum (comp : Bool) (g : ℕ → ℕ) (ps : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun p _ rec i => Nat.add (Nat.mul (Bool.rec (motive := fun _ => ℕ) 1 i comp) (g p))
      (rec (Nat.succ i))) ps

/-- `encV`, by the recursor. -/
noncomputable def kencV (g : ℕ → ℕ) (L : List LField) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun f _ r => Nat.add (Nat.mul (Nat.pow 2 f.sh) (kwsum f.comp g f.ps 0)) r) L

/-- The component guard tests, numbering the places from `i`. -/
noncomputable def kfgComp (sh w : ℕ) (pre : List ℕ) (ps : List ℕ) : ℕ → List Test :=
  List.rec (motive := fun _ => ℕ → List Test) (fun _ => [])
    (fun p _ rec i => Bool.rec (motive := fun _ => List Test) (rec (Nat.succ i))
      (⟨sh, w, i, 0⟩ :: rec (Nat.succ i)) (Nat.blt 0 (kcount p pre))) ps

/-- The counter guard tests. -/
noncomputable def kfgCount (sh w : ℕ) (pre : List ℕ) (ps : List ℕ) : List Test :=
  List.rec (motive := fun _ => List Test) []
    (fun p _ rec => Bool.rec (motive := fun _ => List Test) rec
      (⟨sh, w, kcount p pre, 1⟩ :: rec) (Nat.blt 0 (kcount p pre))) ps

/-- `fguard`, by the recursors. -/
noncomputable def kfguard (pre : List ℕ) (f : LField) : List Test :=
  Bool.rec (motive := fun _ => List Test) (kfgCount f.sh f.w pre f.ps)
    (kfgComp f.sh f.w pre f.ps 0) f.comp

/-- `fok`, by the recursors. -/
noncomputable def kfok (pre post : List ℕ) (f : LField) : List Test :=
  Bool.rec (motive := fun _ => List Test)
    (List.rec (motive := fun _ => List Test) []
      (fun p _ rec => Bool.rec (motive := fun _ => List Test) rec
        (⟨f.sh, f.w, Nat.sub (Nat.add (Nat.sub (Nat.pow 2 f.w) 1) (kcount p pre)) (kcount p post),
          2⟩ :: rec) (Nat.blt (kcount p pre) (kcount p post))) f.ps)
    [] f.comp

/-- `List.flatMap`, by the recursor. -/
noncomputable def kflat {α β : Type} (f : α → List β) (L : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun x _ r => List.append (f x) r) L

/-- `atr`, by the recursors. -/
noncomputable def katr (L : List LField) (t : PTrans) : Tr :=
  ⟨kflat (kfguard t.pre) L, kflat (kfok t.pre t.post) L, kencV (fun p => kcount p t.post) L,
    kencV (fun p => kcount p t.pre) L, .const true⟩

/-- **The table of a net**, by the recursors. -/
noncomputable def katable (N : PNet) (L : List LField) : List Tr :=
  List.rec (motive := fun _ => List Tr) [] (fun t _ r => katr L t :: r) N.trans

/-- `p ∈ l`, by the recursor. -/
noncomputable def kmem (p : ℕ) (l : List ℕ) : Bool := kany l fun q => Nat.beq q p

/-- The structural check of one field, by the recursors. -/
noncomputable def kfieldOk (N : PNet) (f : LField) : Bool :=
  Bitmap.band (kall f.ps fun p => Nat.blt p N.places)
    (Bool.rec (motive := fun _ => Bool)
      (Bitmap.band (Nat.beq f.ps.length 1)
        (Bitmap.band (kall N.trans fun t => kall f.ps fun p =>
            Nat.ble (kcount p t.post) (Nat.add (kcount p t.pre) (Nat.sub (Nat.pow 2 f.w) 1)))
          (kall f.ps fun p => Nat.blt (N.init.getD p 0) (Nat.pow 2 f.w))))
      (Bitmap.band (Nat.ble f.ps.length (Nat.pow 2 f.w))
        (Bitmap.band (kall N.trans fun t =>
            Bitmap.band (Nat.beq (ksum (fun p => kcount p t.pre) f.ps)
              (ksum (fun p => kcount p t.post) f.ps))
              (Nat.ble (ksum (fun p => kcount p t.pre) f.ps) 1))
          (Nat.beq (ksum (fun p => N.init.getD p 0) f.ps) 1)))
      f.comp)

/-- **The structural check of a layout**, by the recursors. -/
noncomputable def layoutOkK (N : PNet) (L : List LField) : Bool :=
  Bitmap.band N.wf (Bitmap.band (sortedL L) (Bitmap.band (kall L (kfieldOk N))
    (kall N.trans fun t => kall t.pre fun p => kany L fun f => kmem p f.ps)))

/-! ### Equalities -/

theorem kcount_eq (p : ℕ) (l : List ℕ) : kcount p l = l.count p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Bool.rec (motive := fun _ => ℕ) (kcount p l) (Nat.succ (kcount p l)) (Nat.beq x p) = _
    rw [ih, List.count_cons]
    cases h : Nat.beq x p
    · have : x ≠ p := Nat.ne_of_beq_eq_false h
      simp [this]
    · have : x = p := Nat.eq_of_beq_eq_true h
      simp [this]

theorem ksum_eq (f : ℕ → ℕ) (l : List ℕ) : ksum f l = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.add (f x) (ksum f l) = _
    rw [ih]; simp

theorem kwsum_eq (comp : Bool) (g : ℕ → ℕ) : ∀ (ps : List ℕ) (i : ℕ),
    kwsum comp g ps i = LField.wsum comp g i ps
  | [], _ => rfl
  | p :: ps, i => by
    change Nat.add (Nat.mul (Bool.rec (motive := fun _ => ℕ) 1 i comp) (g p))
      (kwsum comp g ps (Nat.succ i)) = _
    rw [kwsum_eq comp g ps]
    cases comp <;> rfl

theorem kencV_eq (g : ℕ → ℕ) : ∀ L : List LField, kencV g L = encV L g
  | [] => rfl
  | f :: L => by
    change Nat.add (Nat.mul (Nat.pow 2 f.sh) (kwsum f.comp g f.ps 0)) (kencV g L) = _
    rw [kencV_eq g L, kwsum_eq]; rfl

theorem kfgComp_eq (sh w : ℕ) (pre : List ℕ) : ∀ (ps : List ℕ) (i : ℕ),
    kfgComp sh w pre ps i = ((List.range ps.length).filter fun j =>
      0 < pre.count (ps.getD j 0)).map fun j => (⟨sh, w, j + i, 0⟩ : Test)
  | [], _ => rfl
  | p :: ps, i => by
    change Bool.rec (motive := fun _ => List Test) (kfgComp sh w pre ps (Nat.succ i))
      (⟨sh, w, i, 0⟩ :: kfgComp sh w pre ps (Nat.succ i)) (Nat.blt 0 (kcount p pre)) = _
    rw [kfgComp_eq sh w pre ps, kcount_eq, List.length_cons, List.range_succ_eq_map,
      List.filter_cons, List.filter_map]
    have e : ((List.range ps.length).filter ((fun j => decide (0 < pre.count ((p :: ps).getD j 0)))
        ∘ Nat.succ)) = (List.range ps.length).filter fun j => decide (0 < pre.count (ps.getD j 0)) := by
      congr 1
    rw [e]
    generalize (List.range ps.length).filter (fun j => decide (0 < pre.count (ps.getD j 0))) = X
    have e3 : List.map (fun j => (⟨sh, w, j + i, 0⟩ : Test)) (List.map Nat.succ X) =
        List.map (fun j => (⟨sh, w, j + Nat.succ i, 0⟩ : Test)) X := by
      rw [List.map_map]; congr 1; funext j
      simp only [Function.comp, Test.mk.injEq, true_and, and_true]; omega
    cases h : Nat.blt 0 (pre.count p)
    · have : ¬ 0 < pre.count p := Nat.not_lt.2 (Bitmap.blt_f h)
      change List.map _ X = _
      simp only [List.getD_cons_zero, this, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [e3]
    · have : 0 < pre.count p := Bitmap.blt_t h
      change _ :: List.map _ X = _
      simp only [List.getD_cons_zero, this, decide_true, ↓reduceIte, List.map_cons]
      rw [e3]
      simp

theorem kfgCount_eq (sh w : ℕ) (pre : List ℕ) : ∀ ps : List ℕ,
    kfgCount sh w pre ps = (ps.filter fun p => 0 < pre.count p).map
      fun p => (⟨sh, w, pre.count p, 1⟩ : Test)
  | [] => rfl
  | p :: ps => by
    change Bool.rec (motive := fun _ => List Test) (kfgCount sh w pre ps)
      (⟨sh, w, kcount p pre, 1⟩ :: kfgCount sh w pre ps) (Nat.blt 0 (kcount p pre)) = _
    rw [kfgCount_eq sh w pre ps, kcount_eq, List.filter_cons]
    cases h : Nat.blt 0 (pre.count p)
    · have : ¬ 0 < pre.count p := Nat.not_lt.2 (Bitmap.blt_f h)
      simp [this]
    · have : 0 < pre.count p := Bitmap.blt_t h
      simp [this]

theorem kfguard_eq (t : PTrans) (f : LField) : kfguard t.pre f = fguard t f := by
  unfold kfguard fguard
  cases f.comp
  · exact kfgCount_eq _ _ _ _
  · change kfgComp f.sh f.w t.pre f.ps 0 = _
    rw [kfgComp_eq]; rfl

theorem kfok_eq (t : PTrans) (f : LField) : kfok t.pre t.post f = fok t f := by
  unfold kfok fok
  cases f.comp
  · change List.rec (motive := fun _ => List Test) [] _ f.ps = _
    simp only [Bool.false_eq_true, ↓reduceIte]
    induction f.ps with
    | nil => rfl
    | cons p ps ih =>
      change Bool.rec (motive := fun _ => List Test) _ (_ :: _)
        (Nat.blt (kcount p t.pre) (kcount p t.post)) = _
      rw [List.filter_cons, kcount_eq, kcount_eq]
      cases h : Nat.blt (t.pre.count p) (t.post.count p)
      · have : ¬ t.pre.count p < t.post.count p := Nat.not_lt.2 (Bitmap.blt_f h)
        simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]; exact ih
      · have : t.pre.count p < t.post.count p := Bitmap.blt_t h
        simp only [this, decide_true, ↓reduceIte, List.map_cons]
        rw [← ih]; rfl
  · rfl

theorem kflat_eq {α β : Type} (f : α → List β) : ∀ L : List α, kflat f L = L.flatMap f
  | [] => rfl
  | x :: L => by
    change List.append (f x) (kflat f L) = _
    rw [kflat_eq f L, List.flatMap_cons]; rfl

theorem katr_eq (L : List LField) (t : PTrans) : katr L t = atr L t := by
  unfold katr atr
  have h1 : (fun p => kcount p t.post) = t.post.count := funext fun p => kcount_eq p _
  have h2 : (fun p => kcount p t.pre) = t.pre.count := funext fun p => kcount_eq p _
  rw [kflat_eq, kflat_eq, kencV_eq, kencV_eq, h1, h2]
  congr 1
  · congr 1; funext f; exact kfguard_eq t f
  · congr 1; funext f; exact kfok_eq t f

theorem katable_eq (N : PNet) (L : List LField) : N.katable L = N.atable L := by
  unfold katable atable
  induction N.trans with
  | nil => rfl
  | cons t ts ih =>
    change katr L t :: List.rec (motive := fun _ => List Tr) [] _ ts = _
    rw [ih, katr_eq]; rfl

theorem band_iff {a b : Bool} : Bitmap.band a b = true ↔ a = true ∧ b = true := Bitmap.band_eq

theorem kmem_iff {p : ℕ} {l : List ℕ} : kmem p l = true ↔ p ∈ l := by
  simp only [kmem, kany_eq, List.any_eq_true]
  constructor
  · rintro ⟨q, hq, h⟩; rwa [← Nat.eq_of_beq_eq_true h]
  · intro h; exact ⟨p, h, Nat.beq_refl p⟩

/-- **The kernel-friendly structural check is as strong as `layoutOk`.** -/
theorem layoutSpec_of_layoutOkK {N : PNet} {L : List LField} (h : N.layoutOkK L = true) :
    LayoutSpec N L := by
  unfold layoutOkK at h
  obtain ⟨hwf, h⟩ := band_iff.1 h
  obtain ⟨hs, h⟩ := band_iff.1 h
  obtain ⟨hf, hc⟩ := band_iff.1 h
  simp only [kall_eq, List.all_eq_true] at hf hc
  have hfs : ∀ f ∈ L, (∀ p ∈ f.ps, p < N.places) ∧
      (f.comp = true → f.ps.length ≤ 2 ^ f.w ∧
        (∀ t ∈ N.trans, (f.ps.map t.pre.count).sum = (f.ps.map t.post.count).sum ∧
          (f.ps.map t.pre.count).sum ≤ 1) ∧
        (f.ps.map fun p => N.init.getD p 0).sum = 1) ∧
      (f.comp = false → f.ps.length = 1 ∧
        (∀ t ∈ N.trans, ∀ p ∈ f.ps, t.post.count p ≤ t.pre.count p + (2 ^ f.w - 1)) ∧
        ∀ p ∈ f.ps, N.init.getD p 0 < 2 ^ f.w) := by
    intro f hfL
    have h := hf f hfL
    unfold kfieldOk at h
    obtain ⟨hp, h⟩ := band_iff.1 h
    simp only [kall_eq, List.all_eq_true] at hp
    have hcnt : ∀ t : PTrans, (fun p => kcount p t.pre) = t.pre.count :=
      fun t => funext fun p => kcount_eq p _
    have hcnt' : ∀ t : PTrans, (fun p => kcount p t.post) = t.post.count :=
      fun t => funext fun p => kcount_eq p _
    refine ⟨fun p hp' => Bitmap.blt_t (hp p hp'), fun hc => ?_, fun hc => ?_⟩
    · rw [hc] at h
      change Bitmap.band _ _ = true at h
      obtain ⟨h1, h⟩ := band_iff.1 h
      obtain ⟨h2, h3⟩ := band_iff.1 h
      simp only [kall_eq, List.all_eq_true] at h2
      refine ⟨Nat.le_of_ble_eq_true h1, fun t ht => ?_, ?_⟩
      · obtain ⟨e1, e2⟩ := band_iff.1 (h2 t ht)
        rw [ksum_eq, ksum_eq, hcnt, hcnt'] at e1
        rw [ksum_eq, hcnt] at e2
        exact ⟨Nat.eq_of_beq_eq_true e1, Nat.le_of_ble_eq_true e2⟩
      · rw [ksum_eq] at h3; exact Nat.eq_of_beq_eq_true h3
    · rw [hc] at h
      change Bitmap.band _ _ = true at h
      obtain ⟨h1, h⟩ := band_iff.1 h
      obtain ⟨h2, h3⟩ := band_iff.1 h
      simp only [kall_eq, List.all_eq_true] at h2 h3
      refine ⟨Nat.eq_of_beq_eq_true h1, fun t ht p hp' => ?_, fun p hp' =>
        Bitmap.blt_t (h3 p hp')⟩
      have := Nat.le_of_ble_eq_true (h2 t ht p hp')
      rwa [kcount_eq, kcount_eq] at this
  refine ⟨hwf, sortedL_spec hs, fun f hfL => (hfs f hfL).1, fun f hfL hc => ((hfs f hfL).2.1 hc).1,
    fun f hfL hc => ((hfs f hfL).2.1 hc).2.1, fun f hfL hc => ((hfs f hfL).2.1 hc).2.2,
    fun f hfL hc => ((hfs f hfL).2.2 hc).1, fun f hfL hc => ((hfs f hfL).2.2 hc).2.1,
    fun f hfL hc => ((hfs f hfL).2.2 hc).2.2, fun t ht p hp => ?_⟩
  have := hc t ht
  simp only [kany_eq, List.any_eq_true] at this
  obtain ⟨f, hfL, hm⟩ := this p hp
  exact ⟨f, hfL, kmem_iff.1 hm⟩

end PNet

end AsyncLean
