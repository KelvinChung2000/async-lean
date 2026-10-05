/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic
import AsyncLean.AxiomAudit

/-!
# Example: from an STG specification to a verified gate-level implementation

The specification is the behaviour of a Muller C-element: the environment raises the inputs
`a` and `b` in any order, the circuit answers with `c+`, then the inputs fall in any order and
the circuit answers with `c-`.

1. The specification is proved consistent, CSC, output-persistent and correct (deadlock free,
   livelock free, live).
2. A single C-element `c := C(a, b)` is proved to conform to it; hence the closed loop of the
   circuit and its environment is deadlock free, livelock free and live, never produces an
   unexpected output, and is hazard free (`StgModel.gate_persistent`).
3. An AND gate `c := a ∧ b` does *not* conform: it would lower `c` as soon as one input falls.
4. An STG in which the output pulses twice per input cycle has a CSC conflict: no circuit
   reading only the signal values can implement it (`StgModel.csc_iff_exists_conformant`).
-/

namespace AsyncLean.Examples

open BExpr

/-- The C-element specification.  Signals: `0 = a`, `1 = b` (inputs), `2 = c` (output). -/
def cElementSpec : Stg where
  net := {
    places := 8
    trans := [
      { name := "a+", pre := [0],    post := [2],    edge := some (0, true) },
      { name := "b+", pre := [1],    post := [3],    edge := some (1, true) },
      { name := "c+", pre := [2, 3], post := [4, 5], edge := some (2, true) },
      { name := "a-", pre := [4],    post := [6],    edge := some (0, false) },
      { name := "b-", pre := [5],    post := [7],    edge := some (1, false) },
      { name := "c-", pre := [6, 7], post := [0, 1], edge := some (2, false) }]
    init := [1, 1, 0, 0, 0, 0, 0, 0] }
  signals := [("a", .input), ("b", .input), ("c", .output)]
  initVal := [false, false, false]

/-- The implementation: one C-element. -/
def cElementImpl : List Gate := [{ name := "C", out := 2, fn := celem 0 1 2 }]

theorem spec_correct : cElementSpec.model.Correct := by async_decide
theorem spec_consistent : cElementSpec.model.Consistent := by async_decide
theorem spec_csc : cElementSpec.model.CSC := by async_decide
theorem spec_outputPersistent : cElementSpec.model.OutputPersistent := by async_decide

/-- The C-element conforms to the specification. -/
theorem impl_conformant :
    cElementSpec.model.Conformant (cElementSpec.gateFn cElementImpl) := by
  async_decide

/-- The closed loop of the C-element and its environment never deadlocks. -/
theorem impl_deadlockFree :
    (cElementSpec.model.impl (cElementSpec.gateFn cElementImpl)).DeadlockFree
      cElementSpec.model.s₀ := by
  async_decide

/-- ... never livelocks and never starves an edge. -/
theorem impl_livelockFree_live :
    (cElementSpec.model.impl (cElementSpec.gateFn cElementImpl)).LivelockFree
        cElementSpec.model.Internal cElementSpec.model.s₀ ∧
      (cElementSpec.model.impl (cElementSpec.gateFn cElementImpl)).Live
        cElementSpec.model.s₀ :=
  ⟨by async_decide, by async_decide⟩

/-- ... and is hazard free: an excited gate stays excited until it switches. -/
theorem impl_hazardFree {s s' : Marking (Fin 8) × Val}
    (hs : (cElementSpec.model.impl (cElementSpec.gateFn cElementImpl)).Reachable
      cElementSpec.model.s₀ s)
    (hex : StgModel.Excited (cElementSpec.gateFn cElementImpl) s.2 2)
    {u : Fin 6} (hst : (cElementSpec.model.impl (cElementSpec.gateFn cElementImpl)).step s u s')
    (hu : ∀ b, cElementSpec.model.lab u ≠ some (2, b)) :
    StgModel.Excited (cElementSpec.gateFn cElementImpl) s'.2 2 :=
  StgModel.gate_persistent impl_conformant spec_outputPersistent hs (by decide)
    (Stg.nonInput_iff.2 (by decide)) hex hst hu

/-! ### A wrong implementation -/

/-- An AND gate instead of a C-element. -/
def andImpl : List Gate := [{ name := "AND", out := 2, fn := and (var 0) (var 1) }]

/--
info: "NOT CONFORMANT: after firing [a+(#0), b+(#1), c+(#2), a-(#3)], the gate of c is excited (it would produce c-) but the specification does not allow that edge.\nProve it with: Stg.not_conformant_of_refute (ts := [0, 1, 2, 3]) (by decide +kernel)"
-/
#guard_msgs in
#eval cElementSpec.diagnoseConformant andImpl

/-- The AND gate does not implement the C-element specification. -/
theorem and_not_conformant :
    ¬ cElementSpec.model.Conformant (cElementSpec.gateFn andImpl) :=
  Stg.not_conformant_of_refute (ts := [0, 1, 2, 3]) (by decide +kernel)

/-! ### A specification without complete state coding -/

/-- The output `c` pulses twice per cycle of the input `a`: `a+ c+ c- a- c+ c-`. -/
def doublePulse : Stg where
  net := {
    places := 6
    trans := [
      { name := "a+",   pre := [0], post := [1], edge := some (0, true) },
      { name := "c+.1", pre := [1], post := [2], edge := some (1, true) },
      { name := "c-.1", pre := [2], post := [3], edge := some (1, false) },
      { name := "a-",   pre := [3], post := [4], edge := some (0, false) },
      { name := "c+.2", pre := [4], post := [5], edge := some (1, true) },
      { name := "c-.2", pre := [5], post := [0], edge := some (1, false) }]
    init := [1, 0, 0, 0, 0, 0] }
  signals := [("a", .input), ("c", .output)]
  initVal := [false, false]

theorem doublePulse_consistent : doublePulse.model.Consistent := by async_decide
theorem doublePulse_correct : doublePulse.model.Correct := by async_decide

-- No circuit can implement it:
/--
info: "CSC CONFLICT: firing [a+(#0)] and firing [a+(#0), c+.1(#1), c-.1(#2)] reach states with the same signal values, but the first enables the non-input edges [c+] and the second [].\nProve it with: Stg.not_csc_of_refute (ts₁ := [0]) (ts₂ := [0, 1, 2]) (z := 1) (b := true) (by decide +kernel)"
-/
#guard_msgs in
#eval doublePulse.diagnoseCSC

theorem doublePulse_not_csc : ¬ doublePulse.model.CSC :=
  Stg.not_csc_of_refute (ts₁ := [0]) (ts₂ := [0, 1, 2]) (z := 1) (b := true) (by decide +kernel)

/-- Hence no gate-level circuit implements it. -/
theorem doublePulse_unimplementable (F : ℕ → Val → Bool) :
    ¬ doublePulse.model.Conformant F := fun hc =>
  doublePulse_not_csc (StgModel.csc_of_conformant (Stg.wf_spec (by decide)).2.2 hc)

#assert_standard_axioms spec_correct spec_consistent spec_csc spec_outputPersistent
  impl_conformant impl_deadlockFree impl_livelockFree_live impl_hazardFree
  doublePulse_consistent doublePulse_correct and_not_conformant doublePulse_not_csc
  doublePulse_unimplementable

end AsyncLean.Examples
