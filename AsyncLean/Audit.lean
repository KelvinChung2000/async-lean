/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties
import AsyncLean.LTS.Fairness
import AsyncLean.Petri.FreeChoice
import AsyncLean.Petri.SiphonCheck
import AsyncLean.Petri.FreeChoiceNecessity
import AsyncLean.Circuit.QDI
import AsyncLean.Circuit.Packed
import AsyncLean.Petri.Step
import AsyncLean.Circuit.Step
import AsyncLean.Petri.Invariant
import AsyncLean.Petri.SiphonTrap
import AsyncLean.MarkedGraph.Basic
import AsyncLean.Checker.Petri
import AsyncLean.Circuit.Basic
import AsyncLean.Stg.Concrete
import AsyncLean.Checker.Quotient
import AsyncLean.Checker.Packed
import AsyncLean.Checker.Abstract
import AsyncLean.Checker.FastPetri
import AsyncLean.Checker.FastPOR
import AsyncLean.Checker.FastPORLive
import AsyncLean.Checker.BDD
import AsyncLean.Auto.StateEq
import AsyncLean.Auto.Structural
import AsyncLean.Routing.WormholeCheck
import AsyncLean.Routing.Optimal
import AsyncLean.Routing.Embed
import AsyncLean.Routing.Source
import AsyncLean.Routing.Reduce
import AsyncLean.Routing.Graph
import AsyncLean.Routing.Saturation
import AsyncLean.Routing.GraphBudget
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
  StepEqOn.persistent_iff LivelockFree.mono LivelockFree.of_sub Path.iStep_rtc
  Path.iStep_transGen

-- Fairness
#assert_standard_axioms
  Run.infOften_label_of_live Run.infOften_external_of_progress
  Run.infOften_external_of_livelockFree progress_of_dfLf PNet.reachable_finite_of_bounded

-- Bit-packed circuit checking
#assert_standard_axioms
  Circuit.bisimP Circuit.correct_of_checkCertP Circuit.correct_of_checkCertHomeP
  Circuit.speedIndependent_of_checkCertP Circuit.speedIndependent_of_checkPCertP
  ExplicitLTS.persistent_of_checkPCert

-- Interconnection networks with dynamic routing
#assert_standard_axioms
  Network.deadlockFree_of_escape Network.deadlockFree_of_cdg Network.movable_of_escape
  Network.wf_of_acyclic Network.wf_of_rank Network.livelockFree_of_ranking
  Network.livelockFree_of_ranking' Network.packetLivelockFree_of_ranking
  Network.packet_hops_le Network.packet_hops_eq Network.wf_of_lexRank Network.inevitablyEmpty
  Network.InevitablyEmpty.drain
  Network.Correct.inevitablyEmpty Network.Correct.drain Network.DeadlockFree.lts
  Network.deadlockFree_iff_adaptive Network.livelockFree_iff_adaptive
  Network.adaptive_valid Network.freeOnly_valid Network.firstFree_valid
  Network.StepWith.packetStep Network.legal_of_reachable Network.legal_of_reachable_sub
  Network.deadlockFreeWith_of_escape Network.livelockFreeWith_of_ranking
  Network.ValidSel.escapeSel Network.gatedSel_escapeSel
  Network.not_deadlockFree_of_refuteB Network.not_livelockFree_of_refuteB
  Network.correct_of_checkCert Network.spec_of_checkCert Network.starvationFree_of_checkCert
  Network.exists_escape_of_static Network.staticDeadlockFree_iff_exists_escape
  Network.deadlockFree_iff_exists_escape Network.reachable_of_injectable
  Network.delivered_of_ranking Network.starvationFree_of_escape_ranking
  Network.reachable_finite Network.exists_leave
  Network.EscapeSel.sourceSel Network.movable_of_source Network.deadlockFreeWith_of_source
  Network.starvationFreeWith_of_source Network.mem_tieredSel Network.tieredSel_conserving
  Network.wf_dep_of_reduction
  GraphData.correct GraphData.correct_of_escapeSel GraphData.correct_of_sourceSel
  GraphData.route_adj GraphData.adaptive_ne_nil GraphData.exists_correct GraphData.escRank_lt
  GraphData.rank_lt GraphData.closed
  Run.stronglyFairFor_of_stronglyFair Network.channelFair_of_stronglyFair Network.leaves_free
  Network.exists_leave_of_channelFair Network.delivered_of_leave_rank
  Network.starvationFreeUnderLoad_of_source Network.starvationFreeUnderLoad_of_escape
  Network.starvationFreeWith_of_underLoad Network.Saturated.run_channelFair
  Network.Saturated.run_infOften_inject Network.Saturated.run_ne_empty
  Network.Saturated.not_stronglyFair Network.Saturated.run_delivered
  GraphData.budget_correct GraphData.budget_correct_of_escapeSel
  GraphData.budget_correct_of_sourceSel GraphData.budget_underLoad_of_escapeSel
  GraphData.budget_underLoad GraphData.budget_underLoad_of_sourceSel GraphData.budget_hops_le
  GraphData.budget_route_adj GraphData.return_mem_route GraphData.budgetNet_route_zero
  GraphData.exists_budget_correct GraphData.budget_esc_wf GraphData.budget_rank_lt
  GraphData.budget_closed GraphData.rank_lt_rankBound
  Network.wormholeDeadlockFree_of_escape Network.wormholeDeadlockFree_of_cdg
  Network.wormholeLivelockFree_of_ranking Network.wdrain Network.WormholeCorrect.drain
  Network.not_wormholeDeadlockFree_of_refuteB Network.not_wormholeLivelockFree_of_refuteB
  Network.wormholeCorrect_of_wcheckCert

-- Maximally adaptive routing
#assert_standard_axioms
  Network.not_deadlockFree_of_refuteBetweenB Network.not_deadlockFree_of_checkTree
  Network.maximallyAdaptive_of_maxCheck Network.MaximallyAdaptive.not_deadlockFree
  Network.path_of_runGoodB Network.not_deadlockFree_of_runGoodB
  Network.not_maximallyAdaptive_of_extends Network.Path.of_extends Network.Extends.trans
  Network.MaximallyAdaptive.wormhole Network.deadlockFree_of_wormholeDeadlockFree

-- Wire delays: QDI implies speed independence
#assert_standard_axioms
  Circuit.speedIndependent_of_qdi Circuit.correct_of_qdi Circuit.deadlockFree_of_withWires
  Circuit.livelockFree_of_withWires Circuit.reachable_settle Circuit.reachable_proj

-- Concurrent firing: step semantics
#assert_standard_axioms
  Net.stepLts_reachable_iff Net.stepLts_deadlockFree_iff Net.stepLts_livelockFree_iff
  Net.stepLive_iff Circuit.stepLts_reachable_iff Circuit.stepLts_deadlockFree_iff
  Circuit.stepLts_livelockFree_iff Circuit.stepLive_iff Circuit.correct_iff_stepCorrect

-- Unbounded nets: counter abstraction
#assert_standard_axioms
  ExplicitLTS.of_checkACert PNet.abstracts PNet.of_checkAbs PNet.correct_of_checkAbs
  PNet.deadlockFree_of_checkAbs PNet.livelockFree_of_checkAbs PNet.live_of_checkAbs

-- Fast kernel checking: numeric states, recursor-based inner loops
#assert_standard_axioms
  Fast.of_check PNet.encodes PNet.of_checkFast PNet.correct_of_checkFast
  PNet.deadlockFree_of_checkFast PNet.livelockFree_of_checkFast PNet.live_of_checkFast

-- Partial-order reduction: stubborn sets preserve deadlocks
#assert_standard_axioms
  Net.reachable_red_of_dead Net.deadlockFree_of_stubborn PNet.deadlockFree_of_checkPOR

-- Partial-order reduction for liveness (cycle proviso) and livelock freedom (visibility)
#assert_standard_axioms
  Net.stubborn_front Net.stubborn_commute Net.catchUp Net.live_of_stubborn
  Net.livelockFree_of_stubborn PNet.of_checkPORc PNet.correct_of_checkPORc
  PNet.correct_of_checkPORc_lf PNet.live_of_checkPORc PNet.livelockFree_of_checkPORc
  PNet.livelockFree_of_noInternal

-- Symbolic certificates: decision diagrams of invariants, witnesses, distances and ranks;
-- linear potentials; cuts and diagonal shortcuts of the joint walks
#assert_standard_axioms
  PNet.funBisimOn_packed PNet.Reach.known PNet.Reach.congr PNet.Reach.leaf_mem PNet.phiL_fire
  PNet.phiL_lt PNet.phiL_le PNet.nodesOk_spec PNet.vars_inj PNet.fire_agree PNet.cutsOk_spec
  PNet.cut_reach PNet.walkCut_spec
  PNet.tclaim PNet.of_checkBDD PNet.correct_of_checkBDD
  PNet.correct_of_checkBDD_lf PNet.deadlockFree_of_checkBDD PNet.livelockFree_of_checkBDD
  PNet.live_of_checkBDD PNet.safe_of_checkBDD

-- The state equation: deadlock freedom and bounds without exploration
#assert_standard_axioms
  Net.stateEq_of_reachable Net.deadlockFree_of_stateEq PNet.deadlockFree_of_checkSE
  PNet.le_of_checkBounds PNet.bounded_of_checkBounds PNet.deadlockFree_of_checks
  PNet.le_of_checkPInv PNet.bounded_of_checkPInv PNet.deadlockFree_of_pinv

-- Free-choice nets (Commoner's theorem)
#assert_standard_axioms
  Net.live_of_siphonTrap Net.deadlockFree_of_siphonTrap_fc Net.le_of_deadAt
  SiphonCheck.siphonTrap_of_check SiphonCheck.freeChoice_of_checkFC
  Net.siphonTrap_of_live Net.live_iff_siphonTrap

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
