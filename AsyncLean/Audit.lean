/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties
import AsyncLean.LTS.Fairness
import AsyncLean.Petri.FreeChoice
import AsyncLean.Petri.SiphonCheck
import AsyncLean.Circuit.QDI
import AsyncLean.Circuit.Packed
import AsyncLean.Petri.Invariant
import AsyncLean.Petri.SiphonTrap
import AsyncLean.MarkedGraph.Basic
import AsyncLean.Checker.Petri
import AsyncLean.Circuit.Basic
import AsyncLean.Stg.Concrete
import AsyncLean.Checker.Quotient
import AsyncLean.Checker.Packed
import AsyncLean.Auto.Structural
import AsyncLean.AxiomAudit

/-!
# Axiom audit of the whole library

Building this file fails if any of the main results depends on `sorry`, on a user-declared
axiom, or on `native_decide` (`Lean.ofReduceBool`).  Only `propext`, `Classical.choice` and
`Quot.sound` — the standard foundations of Lean and Mathlib — are permitted.
-/

namespace AsyncLean

open LTS

-- Generic proof rules
#assert_standard_axioms
  DeadlockFree.of_invariant LivelockFree.of_ranking LivelockFree.of_ranking_wf
  livelockFree_iff_acc LiveLabel.of_ranking Live.deadlockFree inevitablyExternal
  InevitablyExternal.exists_external not_deadlockFree_of_path not_livelockFree_of_cycle
  not_liveLabel_of_dead not_persistent_of
  FunBisim.deadlockFree_iff FunBisim.livelockFree_iff FunBisim.live_iff FunBisim.persistent_iff
  StepEqOn.reachable_iff StepEqOn.deadlockFree_iff StepEqOn.livelockFree_iff StepEqOn.live_iff
  StepEqOn.persistent_iff

-- Fairness
#assert_standard_axioms
  Run.infOften_label_of_live Run.infOften_external_of_progress
  Run.infOften_external_of_livelockFree progress_of_dfLf PNet.reachable_finite_of_bounded

-- Bit-packed circuit checking
#assert_standard_axioms
  Circuit.bisimP Circuit.correct_of_checkCertP Circuit.correct_of_checkCertHomeP
  Circuit.speedIndependent_of_checkCertP Circuit.speedIndependent_of_checkPCertP
  ExplicitLTS.persistent_of_checkPCert

-- Wire delays: QDI implies speed independence
#assert_standard_axioms
  Circuit.speedIndependent_of_qdi Circuit.correct_of_qdi Circuit.deadlockFree_of_withWires
  Circuit.livelockFree_of_withWires Circuit.reachable_settle Circuit.reachable_proj

-- Free-choice nets (Commoner's theorem)
#assert_standard_axioms
  Net.live_of_siphonTrap Net.deadlockFree_of_siphonTrap_fc Net.le_of_deadAt
  SiphonCheck.siphonTrap_of_check SiphonCheck.freeChoice_of_checkFC

-- Compositional verification
#assert_standard_axioms
  DivBisim.dfLf_iff DivBisim.liveLabel_iff DivBisim.par DivBisim.hide DivBisim.trans
  DivBisim.symm DivBisim.refl DivBisim.par_comm dfLf_par_iff
  ExplicitLTS.divBisim_of_checkQuot ExplicitLTS.par_toLTS ExplicitLTS.dfLf_par_left_iff
  ExplicitLTS.dfLf_par_right_iff ExplicitLTS.dfLf_of_checkCert

-- Signal transition graphs and their implementations
#assert_standard_axioms
  StgModel.impl_stepEqOn StgModel.impl_correct_iff StgModel.impl_persistent_iff
  StgModel.gate_switch_allowed StgModel.gate_persistent StgModel.csc_of_conformant
  StgModel.nextState_conformant StgModel.csc_iff_exists_conformant
  ExplicitLTS.of_checkInv Stg.bisim Stg.correct_of_checkCert Stg.consistent_of_check
  Stg.csc_of_check Stg.outputPersistent_of_check Stg.conformant_of_check
  Stg.implementation_correct Stg.implementation_correct_of_check
  Stg.not_consistent_of_refute Stg.not_csc_of_refute Stg.not_outputPersistent_of_refute
  Stg.not_conformant_of_refute Stg.not_deadlockFree_of_refute Stg.not_livelockFree_of_refute
  Stg.not_liveLabel_of_refute

-- Petri nets
#assert_standard_axioms
  Net.not_deadlockFree_of_fireSeq Net.not_livelockFree_of_fireSeq Net.not_liveLabel_of_fireSeq
  Net.IsPInvariant.weight_reachable Net.IsPInvariant.bound Net.IsPInvariant.safe
  Net.livelockFree_of_linearRanking Net.deadlockFree_of_siphonTrap
  Net.IsTrap.marked_reachable Net.IsSiphon.empty_reachable

-- Marked graphs (Commoner's theorem)
#assert_standard_axioms
  MarkedGraph.live_iff_circuitsMarked MarkedGraph.live_of_circuitsMarked
  MarkedGraph.deadlockFree_of_circuitsMarked MarkedGraph.not_liveLabel_of_unmarked_circuit
  MarkedGraph.circuitsMarked_iff_exists_rank MarkedGraph.tokens_reachable
  MarkedGraph.safe_of_circuit_cover MarkedGraph.not_live_of_circuit
  MarkedGraph.circuitsMarked_of_rankTable PNet.bounded_of_pinvTable
  PNet.livelockFree_of_rankingTable

-- Verified checker
#assert_standard_axioms
  ExplicitLTS.deadlockFree_of_check ExplicitLTS.livelockFree_of_check
  ExplicitLTS.liveLabel_of_check ExplicitLTS.persistent_of_check ExplicitLTS.of_checkAll
  ExplicitLTS.of_checkCert ExplicitLTS.persistent_of_checkCert ExplicitLTS.of_checkCertHome
  PNet.correct_of_checkPacked PNet.correct_of_checkPackedHome PNet.correct_of_packed
  PNet.correct_of_checkCertHome PNet.bounded_of_check Circuit.correct_of_checkCertHome
  Stg.correct_of_checkCertHome FunBisimOn.deadlockFree_iff FunBisimOn.livelockFree_iff
  FunBisimOn.live_iff
  ExplicitLTS.not_deadlockFree_of_refuteB ExplicitLTS.not_livelockFree_of_refuteB
  ExplicitLTS.not_liveLabel_of_refuteB ExplicitLTS.not_persistent_of_refuteB
  PNet.bisim PNet.correct_of_checkAll PNet.persistent_of_check
  PNet.correct_of_checkCert PNet.persistent_of_checkCert
  PNet.not_deadlockFree_of_refute PNet.not_livelockFree_of_refute
  PNet.not_liveLabel_of_refute PNet.not_persistent_of_refute
  Circuit.bisim Circuit.correct_of_checkAll Circuit.speedIndependent_of_check
  Circuit.correct_of_checkCert Circuit.speedIndependent_of_checkCert
  Circuit.not_deadlockFree_of_refute Circuit.not_livelockFree_of_refute
  Circuit.not_speedIndependent_of_refute

end AsyncLean
