/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.BitmapPetri
import AsyncLean.Checker.Packed

/-!
# Bit-parallel verification of gate-level circuits

A state of a circuit is a valuation of its signals, packed into a number with bit `i` for
signal `i` (`Circuit.bpack`).  Gate `g` *rises* when its function is true and its output false,
and *falls* in the opposite case; each is a transition of an `Aff.Tr` table whose guard is a
Boolean expression of the bits (`Circuit.btable`: the rise of gate `g` is entry `2 g`, its fall
entry `2 g + 1`) and whose effect adds or subtracts `2 ^ out`.  The bitmap checker
(`AsyncLean.Checker.Bitmap`) evaluates such a guard on a whole chunk by bitwise operations.

The table encodes the circuit with the rise and the fall of each gate as separate labels
(`Circuit.rfLts`); `Circuit.of_checkBitmap` transfers deadlock freedom, livelock freedom and
liveness to the circuit itself: a gate fires infinitely often exactly when it rises and falls
infinitely often.
-/

namespace AsyncLean

namespace Circuit

open Aff Fast Bitmap

variable (C : Circuit)

/-- A gate that does nothing (outside the gate list). -/
def noGate : Gate := ⟨"", 0, .const false, false⟩

/-- The `i`-th gate, or `noGate`. -/
def gateD (i : ℕ) : Gate := C.gates.getD i noGate

/-- The rise (`fall = false`) or the fall of a gate, on packed states. -/
def bentry (g : Gate) (fall : Bool) : Tr :=
  if fall then ⟨[], [], 0, 2 ^ g.out, .and (.not g.fn) (.var g.out)⟩
  else ⟨[], [], 2 ^ g.out, 0, .and g.fn (.not (.var g.out))⟩

/-- **The table of a circuit**: entry `2 g` is the rise of gate `g`, entry `2 g + 1` its fall. -/
def btable : List Tr :=
  (List.range (2 * C.gates.length)).map fun i => bentry (C.gateD (i / 2)) (i % 2 == 1)

/-- The internal entries: the rises and falls of the internal gates. -/
def imaskB : ℕ :=
  PNet.mask ((List.range (2 * C.gates.length)).filter fun i => (C.gateD (i / 2)).internal)

/-- Bits from a list of Booleans: the head is bit `0`. -/
def packL : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * packL bs

/-- **A state packed into a number**: bit `i` is signal `i`. -/
def bpack (s : Fin C.signals → Bool) : ℕ := packL (C.enc s)

/-- The circuit with the rise (`2 g`) and the fall (`2 g + 1`) of each gate as labels. -/
def rfLts : LTS (Fin C.signals → Bool) ℕ where
  step s i s' := ∃ g : Fin C.gates.length, C.Excited s g ∧ s' = C.fire s g ∧
    i = 2 * g.val + (if C.val s (C.gate g).out then 1 else 0)

variable {C}

theorem testBit_packL : ∀ (bs : List Bool) (i : ℕ), (packL bs).testBit i = bs.getD i false
  | [], i => by simp [packL]
  | b :: bs, 0 => by
    simp only [packL, List.getD_cons_zero]
    cases b <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
  | b :: bs, i + 1 => by
    simp only [packL, List.getD_cons_succ]
    rw [← testBit_packL bs i, Nat.testBit_succ]
    congr 1
    cases b <;> simp; omega

theorem testBit_bpack (s : Fin C.signals → Bool) : (C.bpack s).testBit = C.val s := by
  funext i
  rw [bpack, testBit_packL, ← valL_enc]; rfl

theorem packL_set_true : ∀ (bs : List Bool) (j : ℕ), j < bs.length → bs.getD j false = false →
    packL (bs.set j true) = packL bs + 2 ^ j
  | [], _, h, _ => by simp at h
  | b :: bs, 0, _, hb => by
    simp only [List.getD_cons_zero] at hb
    subst hb
    simp [packL]; omega
  | b :: bs, j + 1, h, hb => by
    simp only [List.getD_cons_succ] at hb
    simp only [List.set_cons_succ, packL]
    rw [packL_set_true bs j (by simpa using h) hb, Nat.pow_succ]; ring

theorem packL_set_false : ∀ (bs : List Bool) (j : ℕ), j < bs.length → bs.getD j false = true →
    packL (bs.set j false) + 2 ^ j = packL bs
  | [], _, h, _ => by simp at h
  | b :: bs, 0, _, hb => by
    simp only [List.getD_cons_zero] at hb
    subst hb
    simp [packL]; omega
  | b :: bs, j + 1, h, hb => by
    simp only [List.getD_cons_succ] at hb
    simp only [List.set_cons_succ, packL]
    have := packL_set_false bs j (by simpa using h) hb
    rw [Nat.pow_succ]; omega

theorem length_btable : C.btable.length = 2 * C.gates.length := by simp [btable]

theorem getElem_btable {i : ℕ} (hi : i < C.btable.length) :
    C.btable[i] = bentry (C.gateD (i / 2)) (i % 2 == 1) := by
  simp [btable]

theorem gateD_eq (g : Fin C.gates.length) : C.gateD g.val = C.gate g := by
  simp [gateD, gate, List.getD_eq_getElem?_getD]

theorem gOk_bentry (s : Fin C.signals → Bool) (g : Gate) (fall : Bool) :
    gOk (C.bpack s) (bentry g fall) =
      (if fall then !(g.fn.eval (C.val s)) && C.val s g.out
       else g.fn.eval (C.val s) && !(C.val s g.out)) := by
  rw [gOk_eq]
  cases fall <;> simp [bentry, tall, kall, bgOk, BExpr.eval, testBit_bpack]

/-- Firing a gate in the packed encoding. -/
theorem bpack_fire (hwf : C.wf = true) {s : Fin C.signals → Bool} {g : Fin C.gates.length}
    (hex : C.Excited s g) :
    C.bpack (C.fire s g) = C.bpack s + (bentry (C.gate g) (C.val s (C.gate g).out)).add -
      (bentry (C.gate g) (C.val s (C.gate g).out)).sub := by
  have hout := (wf_spec hwf).2 g
  have hlen : (C.enc s).length = C.signals := by simp [enc]
  have hv : (C.enc s).getD (C.gate g).out false = C.val s (C.gate g).out := by
    rw [← valL_enc]; rfl
  unfold bpack
  rw [← fireL_enc hwf]
  unfold fireL
  rw [valL_enc]
  unfold Excited at hex
  cases hval : C.val s (C.gate g).out
  · have hfn : (C.gate g).fn.eval (C.val s) = true := by rw [hval] at hex; simpa using hex
    rw [hfn, packL_set_true _ _ (by rw [hlen]; exact hout) (by rw [hv, hval])]
    simp [bentry]
  · have hfn : (C.gate g).fn.eval (C.val s) = false := by rw [hval] at hex; simpa using hex
    rw [hfn]
    have := packL_set_false _ _ (by rw [hlen]; exact hout) (by rw [hv, hval])
    simp only [bentry, ↓reduceIte, Nat.add_zero]
    omega

/-- **The table of a circuit encodes its rises and falls.** -/
theorem encodes (hwf : C.wf = true) :
    Encodes C.rfLts (fun _ => True) C.bpack id (asucc C.btable) := by
  refine ⟨fun s _ i y hm => ?_, fun s i s' _ hst => ?_⟩
  · obtain ⟨hi, hg, rfl, hok⟩ := mem_asucc.1 hm
    rw [length_btable] at hi
    have hg2 : i / 2 < C.gates.length := by omega
    let g : Fin C.gates.length := ⟨i / 2, hg2⟩
    rw [getElem_btable, show i / 2 = g.val from rfl, gateD_eq] at hg
    rw [gOk_bentry] at hg
    have hex : C.Excited s g := by
      unfold Excited
      split_ifs at hg <;> cases h1 : (C.gate g).fn.eval (C.val s) <;>
        cases h2 : C.val s (C.gate g).out <;> simp_all
    have hdir : (i % 2 == 1) = C.val s (C.gate g).out := by
      split_ifs at hg with h <;> cases h2 : C.val s (C.gate g).out <;> simp_all
    refine ⟨i, C.fire s g, rfl, ⟨g, hex, rfl, ?_⟩, ?_, trivial⟩
    · have hdm : i = 2 * (i / 2) + i % 2 := (Nat.div_add_mod i 2).symm
      cases h2 : C.val s (C.gate g).out
      · rw [h2] at hdir
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        change i = 2 * (i / 2)
        simp at hdir; omega
      · rw [h2] at hdir
        simp only [↓reduceIte]
        change i = 2 * (i / 2) + 1
        simp at hdir; omega
    · rw [bpack_fire hwf hex, getElem_btable, show i / 2 = g.val from rfl, gateD_eq, ← hdir]
  · obtain ⟨g, hex, rfl, rfl⟩ := hst
    have hi : 2 * g.val + (if C.val s (C.gate g).out then 1 else 0) < C.btable.length := by
      rw [length_btable]; have := g.isLt; split_ifs <;> omega
    have hdiv : (2 * g.val + (if C.val s (C.gate g).out then 1 else 0)) / 2 = g.val := by
      split_ifs <;> omega
    have hmod : ((2 * g.val + (if C.val s (C.gate g).out then 1 else 0)) % 2 == 1) =
        C.val s (C.gate g).out := by
      split_ifs with h <;> simp [h, Nat.add_mod]
    refine ⟨true, mem_asucc.2 ⟨hi, ?_, ?_, ?_⟩, fun _ => trivial⟩
    · simp only [id_eq]
      rw [getElem_btable, hdiv, gateD_eq, hmod, gOk_bentry]
      unfold Excited at hex
      cases h1 : (C.gate g).fn.eval (C.val s) <;> cases h2 : C.val s (C.gate g).out <;> simp_all
    · simp only [id_eq]
      rw [getElem_btable, hdiv, gateD_eq, hmod, bpack_fire hwf hex]
    · simp only [id_eq]
      rw [getElem_btable, hdiv, gateD_eq, hmod]
      cases C.val s (C.gate g).out <;> rfl

theorem step_of_rf {s s' : Fin C.signals → Bool} {i : ℕ} (h : C.rfLts.step s i s') :
    ∃ g : Fin C.gates.length, C.lts.step s g s' ∧
      i = 2 * g.val + (if C.val s (C.gate g).out then 1 else 0) := by
  obtain ⟨g, hex, rfl, hi⟩ := h
  exact ⟨g, ⟨hex, rfl⟩, hi⟩

theorem rf_of_step {s s' : Fin C.signals → Bool} {g : Fin C.gates.length}
    (h : C.lts.step s g s') :
    C.rfLts.step s (2 * g.val + (if C.val s (C.gate g).out then 1 else 0)) s' := by
  obtain ⟨hex, rfl⟩ := h
  exact ⟨g, hex, rfl, rfl⟩

theorem reachable_rf {s₀ s : Fin C.signals → Bool} (h : C.lts.Reachable s₀ s) :
    C.rfLts.Reachable s₀ s := by
  induction h with
  | refl => exact LTS.Reachable.refl _
  | tail _ hst ih =>
    obtain ⟨g, hst⟩ := hst
    exact ih.tail ⟨_, rf_of_step hst⟩

theorem testBit_imaskB {i : ℕ} (hi : i < 2 * C.gates.length) :
    C.imaskB.testBit i = (C.gateD (i / 2)).internal := by
  rw [imaskB, PNet.testBit_mask]
  simp only [List.mem_filter, List.mem_range, hi, true_and]
  cases (C.gateD (i / 2)).internal <;> simp

/-- **The bitmap check of a circuit** (split in three parts for the kernel). -/
noncomputable def checkBitmapA (k imask : ℕ) (dl ll : Bool) (s₀ : ℕ) (c : Bitmap.Cert) : Bool :=
  band C.wf (band (Nat.beq imask (cond ll C.imaskB 0)) (band (Nat.beq s₀ (C.bpack C.s₀))
    (Bitmap.checkA C.btable k dl s₀ c)))

noncomputable def checkBitmapR (k imask : ℕ) (c : Bitmap.Cert) : Bool :=
  Bitmap.checkR C.btable k imask 0 c

noncomputable def checkBitmapD (k : ℕ) (lv : Bool) (c : Bitmap.Cert) : Bool :=
  Bitmap.checkD C.btable k 0 (Nat.sub (Nat.pow 2 (2 * C.gates.length)) 1)
    (2 * C.gates.length) lv c

/-- **Deadlock freedom, livelock freedom and liveness of a circuit from a bitmap
certificate.** -/
theorem of_checkBitmap {k imask s₀ : ℕ} {dl ll lv : Bool} {c : Bitmap.Cert}
    (hA : C.checkBitmapA k imask dl ll s₀ c = true) (hR : C.checkBitmapR k imask c = true)
    (hD : C.checkBitmapD k lv c = true) :
    (dl = true → C.lts.DeadlockFree C.s₀) ∧ (ll = true → C.lts.LivelockFree C.Internal C.s₀) ∧
      (lv = true → C.lts.Live C.s₀) := by
  unfold checkBitmapA at hA
  obtain ⟨hwf, hA⟩ := band_eq.1 hA
  obtain ⟨hk, hA⟩ := band_eq.1 hA
  obtain ⟨hs₀, hA⟩ := band_eq.1 hA
  rw [Nat.eq_of_beq_eq_true hs₀] at hA
  have hc := Bitmap.check_of_parts (L := 2 * C.gates.length) (dR := 0) (dD := 0)
    (kD := Nat.sub (Nat.pow 2 (2 * C.gates.length)) 1) (lv := lv) hA hR
    hD
  obtain ⟨hd, hl, hv, -⟩ := Bitmap.of_check (encodes hwf) (fun _ _ h => h) (fun _ => 0)
    (fun _ => 0) (fun _ _ _ _ _ => ⟨le_rfl, fun h => by simp at h⟩)
    (fun _ _ _ _ => ⟨fun h => by simp at h, fun _ => le_rfl⟩) trivial hc
  refine ⟨fun hdl s hs hdead => ?_, fun hll => ?_, fun hlv g => ?_⟩
  · -- a step of the rises and falls is a step of the circuit
    obtain ⟨i, s', hst⟩ := LTS.DeadlockFree.exists_step (hd hdl) (reachable_rf hs)
    obtain ⟨g, hst', -⟩ := step_of_rf hst
    exact hdead g s' hst'
  · -- an internal step of the circuit is an internal rise or fall
    rw [Nat.eq_of_beq_eq_true hk, hll] at hl
    refine LTS.livelockFree_iff_acc.2 fun s hs => ?_
    have hacc := LTS.livelockFree_iff_acc.1 hl s (reachable_rf hs)
    refine Subrelation.accessible (fun {s' s} hrel => ?_) hacc
    obtain ⟨g, hg, hst⟩ := hrel
    refine ⟨_, ?_, rf_of_step hst⟩
    have hi : 2 * g.val + (if C.val s (C.gate g).out then 1 else 0) < 2 * C.gates.length := by
      have := g.isLt; split_ifs <;> omega
    have hdiv : (2 * g.val + (if C.val s (C.gate g).out then 1 else 0)) / 2 = g.val := by
      split_ifs <;> omega
    change (cond true C.imaskB 0).testBit _ = true
    simp only [id_eq, Bool.cond_true]
    rw [testBit_imaskB hi, hdiv, gateD_eq]
    exact hg
  · -- the rise of a live gate is live, and a rise is a firing
    intro s hs
    have hlive := hv hlv (2 * g.val) (by have := g.isLt; simp only [id]; omega) s (reachable_rf hs)
    obtain ⟨s', hr, s'', hst⟩ := hlive
    obtain ⟨g', hst', hi⟩ := step_of_rf hst
    have : g' = g := by
      apply Fin.ext
      split_ifs at hi <;> omega
    subst this
    refine ⟨s', ?_, s'', hst'⟩
    clear hst hst' hi
    induction hr with
    | refl => exact LTS.Reachable.refl _
    | tail _ hst ih =>
      obtain ⟨_, hst⟩ := hst
      obtain ⟨g'', hst'', -⟩ := step_of_rf hst
      exact ih.tail ⟨g'', hst''⟩

theorem correct_of_checkBitmap {k imask s₀ : ℕ} {c : Bitmap.Cert}
    (hA : C.checkBitmapA k imask true true s₀ c = true) (hR : C.checkBitmapR k imask c = true)
    (hD : C.checkBitmapD k true c = true) : C.Correct :=
  let h := of_checkBitmap hA hR hD
  ⟨h.1 rfl, h.2.1 rfl, h.2.2 rfl⟩

theorem deadlockFree_of_checkBitmap {k imask s₀ : ℕ} {ll lv : Bool} {c : Bitmap.Cert}
    (hA : C.checkBitmapA k imask true ll s₀ c = true) (hR : C.checkBitmapR k imask c = true)
    (hD : C.checkBitmapD k lv c = true) : C.lts.DeadlockFree C.s₀ :=
  (of_checkBitmap hA hR hD).1 rfl

theorem livelockFree_of_checkBitmap {k imask s₀ : ℕ} {dl lv : Bool} {c : Bitmap.Cert}
    (hA : C.checkBitmapA k imask dl true s₀ c = true) (hR : C.checkBitmapR k imask c = true)
    (hD : C.checkBitmapD k lv c = true) : C.lts.LivelockFree C.Internal C.s₀ :=
  (of_checkBitmap hA hR hD).2.1 rfl

theorem live_of_checkBitmap {k imask s₀ : ℕ} {dl ll : Bool} {c : Bitmap.Cert}
    (hA : C.checkBitmapA k imask dl ll s₀ c = true) (hR : C.checkBitmapR k imask c = true)
    (hD : C.checkBitmapD k true c = true) : C.lts.Live C.s₀ :=
  (of_checkBitmap hA hR hD).2.2 rfl

end Circuit

end AsyncLean
