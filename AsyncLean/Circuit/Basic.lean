/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Explicit
import Mathlib.Data.List.FinRange

/-!
# Gate-level asynchronous circuits (netlists)

A *speed-independent* circuit is a netlist of gates with unbounded, unknown gate delays.
Each gate drives one signal; a gate is **excited** when its Boolean function disagrees with
the current value of its output, and an excited gate may **fire** (switch its output) at any
time.  This is Muller's classical interleaving semantics.  The environment is modelled by
gates too, so a `Circuit` is closed.

* a **deadlock** is a stable state (no gate excited) — the closed system stops;
* a **livelock** is an infinite run in which only *internal* gates switch — the circuit
  oscillates internally without ever producing an observable output transition;
* **liveness** means every gate can always switch again;
* **speed independence / hazard freedom** (`SpeedIndependent`, Muller's semi-modularity):
  an excited gate is never disabled before it fires.  A violation is a hazard: a glitch
  whose effect depends on gate delays.

Everything is decided by the verified model checker through a bisimulation between the
abstract semantics on `Fin signals → Bool` and an executable semantics on `List Bool`.
-/

namespace AsyncLean

/-- Boolean functions of gates, over signal indices. -/
inductive BExpr where
  | var (i : ℕ)
  | const (b : Bool)
  | not (e : BExpr)
  | and (a b : BExpr)
  | or (a b : BExpr)
  | xor (a b : BExpr)
  deriving Repr, DecidableEq

namespace BExpr

/-- Evaluate under a valuation of the signals. -/
def eval (v : ℕ → Bool) : BExpr → Bool
  | var i => v i
  | const b => b
  | not e => !e.eval v
  | and a b => a.eval v && b.eval v
  | or a b => a.eval v || b.eval v
  | xor a b => Bool.xor (a.eval v) (b.eval v)

/-- Inverter. -/
def inv (i : ℕ) : BExpr := not (var i)
/-- Two-input NAND. -/
def nand (i j : ℕ) : BExpr := not (and (var i) (var j))
/-- Two-input NOR. -/
def nor (i j : ℕ) : BExpr := not (or (var i) (var j))
/-- Muller C-element with inputs `a`, `b` and output `o`: the output follows the inputs when
they agree and holds its value otherwise. -/
def celem (a b o : ℕ) : BExpr := or (and (var a) (var b)) (and (var o) (or (var a) (var b)))
/-- C-element with the second input inverted (the standard Muller pipeline stage). -/
def celemInv (a b o : ℕ) : BExpr :=
  or (and (var a) (not (var b))) (and (var o) (or (var a) (not (var b))))

end BExpr

/-- A gate drives signal `out` with function `fn`. -/
structure Gate where
  /-- Human-readable name. -/
  name : String := ""
  /-- The driven signal. -/
  out : ℕ
  /-- The gate's Boolean function. -/
  fn : BExpr
  /-- Internal gate (its switching is not observable), relevant for livelock. -/
  internal : Bool := false

/-- A closed gate-level circuit with signals `0 … signals-1`. -/
structure Circuit where
  /-- Number of signals. -/
  signals : ℕ
  /-- The gates (including the gates modelling the environment). -/
  gates : List Gate
  /-- Initial values of the signals. -/
  init : List Bool

namespace Circuit

variable (C : Circuit)

/-- The `g`-th gate. -/
def gate (g : Fin C.gates.length) : Gate := C.gates[g]

/-- Signal valuation of a state. -/
def val (s : Fin C.signals → Bool) (i : ℕ) : Bool := if h : i < C.signals then s ⟨i, h⟩ else false

/-- Gate `g` is excited in state `s`. -/
def Excited (s : Fin C.signals → Bool) (g : Fin C.gates.length) : Prop :=
  (C.gate g).fn.eval (C.val s) ≠ C.val s (C.gate g).out

/-- Gate `g` fires: its output takes the value of its function. -/
def fire (s : Fin C.signals → Bool) (g : Fin C.gates.length) : Fin C.signals → Bool :=
  fun j => if j.val = (C.gate g).out then (C.gate g).fn.eval (C.val s) else s j

/-- Muller's interleaving semantics. -/
def lts : LTS (Fin C.signals → Bool) (Fin C.gates.length) where
  step s g s' := C.Excited s g ∧ s' = C.fire s g

/-- The initial state. -/
def s₀ : Fin C.signals → Bool := fun i => C.init.getD i false

/-- Internal gates. -/
def Internal (g : Fin C.gates.length) : Prop := (C.gate g).internal = true

instance : DecidablePred C.Internal := fun g => inferInstanceAs (Decidable ((C.gate g).internal = true))

/-- **Correctness**: no deadlock (the closed circuit never stabilises), no livelock (no
endless internal oscillation), every gate live. -/
def Correct : Prop :=
  C.lts.DeadlockFree C.s₀ ∧ C.lts.LivelockFree C.Internal C.s₀ ∧ C.lts.Live C.s₀

/-- **Speed independence** (semi-modularity, hazard freedom). -/
def SpeedIndependent : Prop := C.lts.Persistent C.s₀

/-- Well-formedness: the initial state has the right length and every gate drives an
existing signal. -/
def wf : Bool := C.init.length == C.signals && C.gates.all fun g => decide (g.out < C.signals)

/-! ### Executable semantics -/

/-- Valuation of a list-encoded state. -/
def valL (l : List Bool) (i : ℕ) : Bool := l.getD i false

/-- Excitation on list-encoded states. -/
def excitedL (l : List Bool) (g : Gate) : Bool := g.fn.eval (valL l) != valL l g.out

/-- Firing on list-encoded states. -/
def fireL (l : List Bool) (g : Gate) : List Bool := l.set g.out (g.fn.eval (valL l))

/-- Executable successor function. -/
def succ (l : List Bool) : List (Fin C.gates.length × List Bool) :=
  (List.finRange C.gates.length).filterMap fun g =>
    if excitedL l (C.gate g) then some (g, fireL l (C.gate g)) else none

/-- The executable LTS. -/
def explicit : ExplicitLTS (List Bool) (Fin C.gates.length) := ⟨C.succ⟩

/-- Encoding of states as lists. -/
def enc (s : Fin C.signals → Bool) : List Bool := List.ofFn s

variable {C}

theorem wf_spec (h : C.wf = true) :
    C.init.length = C.signals ∧ ∀ g : Fin C.gates.length, (C.gate g).out < C.signals := by
  simp only [wf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun g => h.2 _ (List.getElem_mem _)⟩

theorem valL_enc (s : Fin C.signals → Bool) : valL (C.enc s) = C.val s := by
  funext i
  unfold valL enc val
  split_ifs with h <;> simp [List.getD_eq_getElem?_getD, h]

theorem excitedL_enc {s : Fin C.signals → Bool} {g : Fin C.gates.length} :
    excitedL (C.enc s) (C.gate g) = true ↔ C.Excited s g := by
  simp [excitedL, Excited, valL_enc]

theorem fireL_enc (hwf : C.wf = true) (s : Fin C.signals → Bool) (g : Fin C.gates.length) :
    fireL (C.enc s) (C.gate g) = C.enc (C.fire s g) := by
  have hout := (wf_spec hwf).2 g
  apply List.ext_getElem
  · simp [fireL, enc]
  · intro k h1 h2
    simp only [fireL, valL_enc, List.getElem_set]
    simp only [enc, List.getElem_ofFn, fire]
    by_cases hk : k = (C.gate g).out
    · simp [hk]
    · simp [hk, Ne.symm hk]

theorem mem_succ_enc (hwf : C.wf = true) {s : Fin C.signals → Bool} {g : Fin C.gates.length}
    {l : List Bool} : (g, l) ∈ C.succ (C.enc s) ↔ C.Excited s g ∧ l = C.enc (C.fire s g) := by
  simp only [succ, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨g', h⟩
    split_ifs at h with hex
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨excitedL_enc.1 hex, fireL_enc hwf s _⟩
  · rintro ⟨hex, rfl⟩
    refine ⟨g, ?_⟩
    simp only [excitedL_enc.2 hex, ↓reduceIte, fireL_enc hwf]

/-- The executable semantics is bisimilar to the abstract one. -/
theorem bisim (hwf : C.wf = true) : LTS.FunBisim C.lts C.explicit.toLTS C.enc := by
  refine ⟨fun s g l => ?_⟩
  change (g, l) ∈ C.succ (C.enc s) ↔ _
  rw [mem_succ_enc hwf]
  constructor
  · rintro ⟨hex, rfl⟩; exact ⟨_, ⟨hex, rfl⟩, rfl⟩
  · rintro ⟨s', ⟨hex, rfl⟩, rfl⟩; exact ⟨hex, rfl⟩

theorem enc_s₀ (hwf : C.wf = true) : C.enc C.s₀ = C.init := by
  have hlen := (wf_spec hwf).1
  apply List.ext_getElem
  · simp [enc, hlen]
  · intro k h1 h2
    simp [enc, s₀, List.getD_eq_getElem?_getD, h2]

/-! ### Verified analysis of concrete circuits -/

/-- Lexicographic comparison of Boolean lists. -/
def boolLexCmp : List Bool → List Bool → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match a, b with
    | false, true => .lt
    | true, false => .gt
    | _, _ => boolLexCmp as bs

variable (C)

/-- Run the verified checker for deadlock freedom, livelock freedom and liveness. -/
def checkAll (fuel : ℕ := 100000) : Bool :=
  C.wf && C.explicit.checkAll boolLexCmp (fun g => (C.gate g).internal)
    (List.finRange C.gates.length) fuel C.init

/-- Run the verified checker for speed independence (hazard freedom). -/
def checkSpeedIndependent (fuel : ℕ := 100000) : Bool :=
  C.wf && C.explicit.checkPersistent boolLexCmp fuel C.init

/-- Compute a certificate (untrusted). -/
def mkCert (fuel : ℕ := 100000) : ExplicitLTS.Cert (List Bool) :=
  C.explicit.mkCert boolLexCmp (fun g => (C.gate g).internal) (List.finRange C.gates.length)
    fuel C.init

/-- Check a certificate for `Correct` (trusted). -/
def checkCert (c : ExplicitLTS.Cert (List Bool)) : Bool :=
  C.wf && C.explicit.checkCert boolLexCmp (fun g => (C.gate g).internal)
    (List.finRange C.gates.length) C.init c

/-- Check a certificate for speed independence (trusted). -/
def checkCertSpeedIndependent (c : ExplicitLTS.Cert (List Bool)) : Bool :=
  C.wf && C.explicit.checkCertPersistent boolLexCmp C.init c

/-- Gate indices as elements of `Fin` (out-of-range indices are dropped). -/
def toFins (gs : List ℕ) : List (Fin C.gates.length) :=
  gs.filterMap fun i => if h : i < C.gates.length then some ⟨i, h⟩ else none

/-- Firing the gates `gs` reaches a stable state. -/
def refuteDeadlockFree (gs : List ℕ) : Bool :=
  C.wf && C.explicit.refuteDeadlockFreeB C.init (C.toFins gs)

/-- Firing `gs` reaches a state from which the internal gates `cyc` oscillate forever. -/
def refuteLivelockFree (gs cyc : List ℕ) : Bool :=
  C.wf && C.explicit.refuteLivelockFreeB (fun g => (C.gate g).internal) C.init (C.toFins gs)
    (C.toFins cyc)

/-- Firing `gs` reaches a state in which firing gate `g'` disables the excited gate `g`
(a hazard). -/
def refuteSpeedIndependent (gs : List ℕ) (g g' : Fin C.gates.length) : Bool :=
  C.wf && C.explicit.refutePersistentB C.init (C.toFins gs) g g'

variable {C}

/-- **A successful run of the verified checker proves the circuit correct.** -/
theorem correct_of_checkAll {fuel : ℕ} (h : C.checkAll fuel = true) : C.Correct := by
  simp only [checkAll, Bool.and_eq_true] at h
  obtain ⟨hd, hl, hv⟩ := ExplicitLTS.of_checkAll (List.mem_finRange) h.2
  rw [← enc_s₀ h.1] at hd hl hv
  exact ⟨(bisim h.1).deadlockFree_iff.1 hd, (bisim h.1).livelockFree_iff.1 hl,
    (bisim h.1).live_iff.1 hv⟩

theorem correct_of_checkCert {c : ExplicitLTS.Cert (List Bool)} (h : C.checkCert c = true) :
    C.Correct := by
  simp only [checkCert, Bool.and_eq_true] at h
  obtain ⟨hd, hl, hv⟩ := ExplicitLTS.of_checkCert (List.mem_finRange) h.2
  rw [← enc_s₀ h.1] at hd hl hv
  exact ⟨(bisim h.1).deadlockFree_iff.1 hd, (bisim h.1).livelockFree_iff.1 hl,
    (bisim h.1).live_iff.1 hv⟩

theorem speedIndependent_of_checkCert {c : ExplicitLTS.Cert (List Bool)}
    (h : C.checkCertSpeedIndependent c = true) : C.SpeedIndependent := by
  simp only [checkCertSpeedIndependent, Bool.and_eq_true] at h
  have := ExplicitLTS.persistent_of_checkCert h.2
  rw [← enc_s₀ h.1] at this
  exact (bisim h.1).persistent_iff.1 this

theorem speedIndependent_of_check {fuel : ℕ} (h : C.checkSpeedIndependent fuel = true) :
    C.SpeedIndependent := by
  simp only [checkSpeedIndependent, Bool.and_eq_true] at h
  have := ExplicitLTS.persistent_of_checkPersistent h.2
  rw [← enc_s₀ h.1] at this
  exact (bisim h.1).persistent_iff.1 this

theorem not_deadlockFree_of_refute {gs : List ℕ} (h : C.refuteDeadlockFree gs = true) :
    ¬ C.lts.DeadlockFree C.s₀ := by
  simp only [refuteDeadlockFree, Bool.and_eq_true] at h
  rw [← (bisim h.1).deadlockFree_iff, enc_s₀ h.1]
  exact ExplicitLTS.not_deadlockFree_of_refuteB h.2

theorem not_livelockFree_of_refute {gs cyc : List ℕ} (h : C.refuteLivelockFree gs cyc = true) :
    ¬ C.lts.LivelockFree C.Internal C.s₀ := by
  simp only [refuteLivelockFree, Bool.and_eq_true] at h
  rw [← (bisim h.1).livelockFree_iff, enc_s₀ h.1]
  exact ExplicitLTS.not_livelockFree_of_refuteB h.2

theorem not_speedIndependent_of_refute {gs : List ℕ} {g g' : Fin C.gates.length}
    (h : C.refuteSpeedIndependent gs g g' = true) : ¬ C.SpeedIndependent := by
  simp only [refuteSpeedIndependent, Bool.and_eq_true] at h
  unfold SpeedIndependent
  rw [← (bisim h.1).persistent_iff, enc_s₀ h.1]
  exact ExplicitLTS.not_persistent_of_refuteB h.2

end Circuit

end AsyncLean
