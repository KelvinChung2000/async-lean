/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Circuit.Basic
import AsyncLean.Checker.Diagnose
import Mathlib.Data.Nat.Bitwise

/-!
# Fast verification of circuits: bit-packed states

A state of a circuit is a vector of Booleans, which the default executable semantics stores
as a `List Bool`: reading a signal walks the list, and comparing two states compares lists.
Here a state is a single natural number whose bit `i` is signal `i`.  Reading a signal is
`Nat.testBit`, switching a gate is one `xor`, and comparing states is a number comparison —
all evaluated natively by the Lean kernel.

`Circuit.bisimP` proves the packed semantics bisimilar to the abstract one, so the generic
certificate checkers apply unchanged (`Circuit.correct_of_checkCertHomeP`,
`Circuit.speedIndependent_of_checkCertP`, …).
-/

namespace AsyncLean

namespace BExpr

/-- Evaluate on a packed state (compiled version). -/
def evalNImpl (x : ℕ) : BExpr → Bool
  | var i => x.testBit i
  | const b => b
  | not e => !e.evalNImpl x
  | and a b => a.evalNImpl x && b.evalNImpl x
  | or a b => a.evalNImpl x || b.evalNImpl x
  | xor a b => Bool.xor (a.evalNImpl x) (b.evalNImpl x)

/-- Evaluate on a packed state.  Defined with the recursor, which the kernel evaluates faster
than structural recursion; compiled code uses `evalNImpl`. -/
@[implemented_by evalNImpl]
def evalN (x : ℕ) (e : BExpr) : Bool :=
  BExpr.rec (motive := fun _ => Bool) (fun i => x.testBit i) (fun b => b) (fun _ r => !r)
    (fun _ _ ra rb => ra && rb) (fun _ _ ra rb => ra || rb) (fun _ _ ra rb => Bool.xor ra rb) e

theorem evalN_eq {x : ℕ} {v : ℕ → Bool} (h : ∀ i, x.testBit i = v i) (e : BExpr) :
    e.evalN x = e.eval v := by
  induction e <;> simp_all [evalN, eval]

end BExpr

namespace Circuit

variable (C : Circuit)

/-- Packed encoding of a state. -/
def pack (s : Fin C.signals → Bool) : ℕ :=
  (List.finRange C.signals).foldl (fun acc i => if s i then acc ||| 2 ^ i.val else acc) 0

/-- Packed initial state. -/
def initN : ℕ :=
  (List.range C.signals).foldl (fun acc i => if C.init.getD i false then acc ||| 2 ^ i else acc) 0

/-- Excitation on packed states. -/
def excitedN (x : ℕ) (g : Gate) : Bool := g.fn.evalN x != x.testBit g.out

/-- Packed successors: an excited gate flips its output bit. -/
def succN (x : ℕ) : List (Fin C.gates.length × ℕ) :=
  (List.finRange C.gates.length).filterMap fun g =>
    if excitedN x (C.gate g) then some (g, x ^^^ 2 ^ (C.gate g).out) else none

/-- The packed executable semantics. -/
def packed : ExplicitLTS ℕ (Fin C.gates.length) := ⟨C.succN⟩

variable {C}

theorem testBit_foldl_pack {α : Type*} (f : α → Bool) (idx : α → ℕ) (l : List α) (a q : ℕ) :
    Nat.testBit (l.foldl (fun acc i => if f i then acc ||| 2 ^ idx i else acc) a) q =
      (Nat.testBit a q || l.any fun i => f i && idx i == q) := by
  induction l generalizing a with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons, List.any_cons]
    split_ifs with hf
    · rw [ih, Nat.testBit_lor, Nat.testBit_two_pow]
      by_cases h : idx i = q
      · simp [hf, h]
      · have h' : (idx i == q) = false := by simpa using h
        simp [h', h]
    · rw [ih]; simp [hf]

theorem testBit_pack (s : Fin C.signals → Bool) (q : ℕ) : (C.pack s).testBit q = C.val s q := by
  rw [pack, testBit_foldl_pack]
  simp only [Nat.zero_testBit, Bool.false_or, val]
  split_ifs with hq
  · cases hs : s ⟨q, hq⟩
    · simp only [List.any_eq_false, List.mem_finRange, Bool.and_eq_true, beq_iff_eq, not_and]
      rintro i - hsi rfl; simp_all
    · simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨q, hq⟩, hs, rfl⟩
  · simp only [List.any_eq_false, List.mem_finRange, Bool.and_eq_true, beq_iff_eq, not_and]
    rintro i - - rfl; exact hq i.isLt

theorem initN_eq (hwf : C.wf = true) : C.initN = C.pack C.s₀ := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_pack, initN, testBit_foldl_pack]
  simp only [Nat.zero_testBit, Bool.false_or, val, s₀]
  have hlen := (wf_spec hwf).1
  split_ifs with hq
  · cases hs : C.init.getD q false
    · simp only [List.any_eq_false, List.mem_range, Bool.and_eq_true, beq_iff_eq, not_and]
      rintro i - h rfl; simp_all
    · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
      exact ⟨q, hq, hs, rfl⟩
  · simp only [List.any_eq_false, List.mem_range, Bool.and_eq_true, beq_iff_eq, not_and]
    rintro i hi - rfl; exact hq hi

theorem excitedN_pack {s : Fin C.signals → Bool} {g : Fin C.gates.length} :
    excitedN (C.pack s) (C.gate g) = true ↔ C.Excited s g := by
  simp only [excitedN, bne_iff_ne, ne_eq, Excited, testBit_pack,
    BExpr.evalN_eq (testBit_pack s)]

theorem pack_fire (hwf : C.wf = true) {s : Fin C.signals → Bool} {g : Fin C.gates.length}
    (hex : C.Excited s g) : C.pack (C.fire s g) = C.pack s ^^^ 2 ^ (C.gate g).out := by
  have hout := (wf_spec hwf).2 g
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_xor, Nat.testBit_two_pow, testBit_pack, testBit_pack]
  simp only [val, fire]
  by_cases hq : q < C.signals
  · simp only [hq, ↓reduceDIte]
    by_cases h : q = (C.gate g).out
    · subst h
      simp only [↓reduceIte, decide_true]
      unfold Excited at hex
      simp only [val, hout, ↓reduceDIte] at hex
      cases h1 : (C.gate g).fn.eval (C.val s) <;> cases h2 : s ⟨(C.gate g).out, hout⟩ <;>
        simp_all
    · have h' : (C.gate g).out ≠ q := Ne.symm h
      simp [h, h']
  · have h' : (C.gate g).out ≠ q := by omega
    simp [hq, h']

theorem mem_succN (hwf : C.wf = true) {s : Fin C.signals → Bool} {g : Fin C.gates.length}
    {x : ℕ} : (g, x) ∈ C.succN (C.pack s) ↔ C.Excited s g ∧ x = C.pack (C.fire s g) := by
  simp only [succN, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨g', h⟩
    split_ifs at h with hex
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hex' := excitedN_pack.1 hex
    exact ⟨hex', (pack_fire hwf hex').symm⟩
  · rintro ⟨hex, rfl⟩
    refine ⟨g, ?_⟩
    simp only [excitedN_pack.2 hex, ↓reduceIte, pack_fire hwf hex]

/-- The packed semantics is bisimilar to the abstract one. -/
theorem bisimP (hwf : C.wf = true) : LTS.FunBisim C.lts C.packed.toLTS C.pack := by
  refine ⟨fun s g x => ?_⟩
  change (g, x) ∈ C.succN (C.pack s) ↔ _
  rw [mem_succN hwf]
  constructor
  · rintro ⟨hex, rfl⟩; exact ⟨_, ⟨hex, rfl⟩, rfl⟩
  · rintro ⟨s', ⟨hex, rfl⟩, rfl⟩; exact ⟨hex, rfl⟩

/-! ### Packed certificates -/

variable (C)

/-- Compute a packed certificate (untrusted). -/
def mkCertP (fuel : ℕ := 100000) : ExplicitLTS.Cert ℕ :=
  C.packed.mkCert natCmp (fun g => (C.gate g).internal) (List.finRange C.gates.length)
    fuel C.initN

/-- Compute a packed home-state certificate (untrusted). -/
def mkCertHomeP (fuel : ℕ := 100000) : ExplicitLTS.HomeCert ℕ :=
  C.packed.mkCertHome natCmp (fun g => (C.gate g).internal) (List.finRange C.gates.length)
    fuel C.initN

/-- Check a packed certificate for `Correct` (trusted). -/
def checkCertP (c : ExplicitLTS.Cert ℕ) : Bool :=
  C.wf && C.packed.checkCert natCmp (fun g => (C.gate g).internal)
    (List.finRange C.gates.length) C.initN c

/-- Check a packed home-state certificate for `Correct` (trusted). -/
def checkCertHomeP (c : ExplicitLTS.HomeCert ℕ) : Bool :=
  C.wf && C.packed.checkCertHome natCmp (fun g => (C.gate g).internal)
    (List.finRange C.gates.length) C.initN c

/-- Check a packed certificate for speed independence (trusted). -/
def checkCertSpeedIndependentP (c : ExplicitLTS.Cert ℕ) : Bool :=
  C.wf && C.packed.checkCertPersistent natCmp C.initN c

/-- Compute a labelled-successor certificate for speed independence (untrusted). -/
def mkPCertP (fuel : ℕ := 100000) : ExplicitLTS.PCert ℕ :=
  C.packed.mkPCert natCmp Fin.val fuel C.initN

/-- Check a labelled-successor certificate for speed independence (trusted). -/
def checkPCertP (c : ExplicitLTS.PCert ℕ) : Bool :=
  C.wf && C.packed.checkPCert natCmp Fin.val C.initN c

variable {C}

theorem correct_of_checkCertP {c : ExplicitLTS.Cert ℕ} (h : C.checkCertP c = true) :
    C.Correct := by
  simp only [checkCertP, Bool.and_eq_true] at h
  obtain ⟨hd, hl, hv⟩ := ExplicitLTS.of_checkCert (List.mem_finRange) h.2
  rw [initN_eq h.1] at hd hl hv
  exact ⟨(bisimP h.1).deadlockFree_iff.1 hd, (bisimP h.1).livelockFree_iff.1 hl,
    (bisimP h.1).live_iff.1 hv⟩

theorem correct_of_checkCertHomeP {c : ExplicitLTS.HomeCert ℕ}
    (h : C.checkCertHomeP c = true) : C.Correct := by
  simp only [checkCertHomeP, Bool.and_eq_true] at h
  obtain ⟨hd, hl, hv⟩ := ExplicitLTS.of_checkCertHome (List.mem_finRange) h.2
  rw [initN_eq h.1] at hd hl hv
  exact ⟨(bisimP h.1).deadlockFree_iff.1 hd, (bisimP h.1).livelockFree_iff.1 hl,
    (bisimP h.1).live_iff.1 hv⟩

theorem speedIndependent_of_checkCertP {c : ExplicitLTS.Cert ℕ}
    (h : C.checkCertSpeedIndependentP c = true) : C.SpeedIndependent := by
  simp only [checkCertSpeedIndependentP, Bool.and_eq_true] at h
  have := ExplicitLTS.persistent_of_checkCert h.2
  rw [initN_eq h.1] at this
  exact (bisimP h.1).persistent_iff.1 this

theorem speedIndependent_of_checkPCertP {c : ExplicitLTS.PCert ℕ}
    (h : C.checkPCertP c = true) : C.SpeedIndependent := by
  simp only [checkPCertP, Bool.and_eq_true] at h
  have := ExplicitLTS.persistent_of_checkPCert Fin.val_injective h.2
  rw [initN_eq h.1] at this
  exact (bisimP h.1).persistent_iff.1 this

end Circuit

end AsyncLean
