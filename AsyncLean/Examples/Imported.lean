/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Import.G
import AsyncLean.Import.Pnml
import AsyncLean.Import.Verilog
import AsyncLean.Checker.Tactic
import AsyncLean.AxiomAudit

/-!
# Example: verifying designs imported from standard formats

The files in `AsyncLean/Examples/designs/` are read at elaboration time; each command defines
an ordinary constant (inspect it with `#print`), about which the theorems are stated.
-/

namespace AsyncLean.Examples.Imported

/-! ### An STG (`.g`) and its Verilog implementation -/

stg_from_g celement "designs/celement.g"
gates_from_verilog celementGates "designs/celement.v" for celement
gates_from_verilog andGates "designs/celement_and.v" for celement

theorem celement_spec :
    celement.model.Correct ∧ celement.model.Consistent ∧ celement.model.CSC ∧
      celement.model.OutputPersistent :=
  ⟨by async_decide, by async_decide, by async_decide, by async_decide⟩

theorem celement_impl :
    celement.model.Conformant (celement.gateFn celementGates) ∧
      (celement.model.impl (celement.gateFn celementGates)).DeadlockFree celement.model.s₀ :=
  ⟨by async_decide, by async_decide⟩

theorem and_wrong : ¬ celement.model.Conformant (celement.gateFn andGates) :=
  Stg.not_conformant_of_refute (ts := [0, 2, 1, 3]) (by decide +kernel)

/-! ### A Petri net (PNML) -/

pnet_from_pnml arbiter "designs/arbiter.pnml" (internal := ["g1", "g2"])

theorem arbiter_correct : arbiter.Correct := by async_decide

/-! ### A closed netlist (Verilog) -/

circuit_from_verilog ring "designs/ring.v"

theorem ring_ok : ring.Correct ∧ ring.SpeedIndependent := ⟨by async_decide, by async_decide⟩

#assert_standard_axioms celement_spec celement_impl and_wrong arbiter_correct ring_ok

end AsyncLean.Examples.Imported
