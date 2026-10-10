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
import AsyncLean.Routing.GraphDetour
import AsyncLean.Routing.Lanes
import AsyncLean.Routing.SharedLanes
import AsyncLean.Routing.Throughput
import AsyncLean.Routing.Widen
import AsyncLean.Flow.Fluid
import AsyncLean.Flow.MeshWire
import AsyncLean.Flow.MeshOdd
import AsyncLean.Flow.MeshWorst
import AsyncLean.Flow.Certificate
import AsyncLean.Flow.MeshPatterns
import AsyncLean.Flow.Valiant
import AsyncLean.Flow.Tree
import AsyncLean.Flow.Symmetric
import AsyncLean.Flow.GraphCert
import AsyncLean.Flow.GraphPatterns
import AsyncLean.Flow.Scaling
import AsyncLean.Flow.Backpressure
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
  GraphData.detour_correct GraphData.detour_correct_of_escapeSel GraphData.detour_correct_of_sourceSel
  GraphData.detour_underLoad_of_escapeSel GraphData.detour_underLoad GraphData.detour_underLoad_of_sourceSel
  GraphData.detour_hops_le GraphData.detour_hops_le_some GraphData.detour_phase_hops_le
  GraphData.detour_route_adj GraphData.detourNet_route_none GraphData.exists_detour_correct
  Network.SafeCert.correct Network.SafeCert.underLoad Network.SafeCert.underLoad_of_valid
  Network.SafeCert.sourceSel Network.SafeCert.lanes_dep Network.SafeCert.lanes_esc_wf
  Network.lanes_correct Network.lanes_underLoad Network.lanes_step Network.lanes_path_one
  Network.lanes_path Network.ejections_flatMap Network.copies_path Network.lanes_reachable_iff
  Network.lanes_reachable_lane GraphData.lanes_correct GraphData.lanes_budget_correct
  GraphData.lanes_detour_correct GraphData.lanes_detour_sourceSel
  GraphData.shared_closed GraphData.shared_dep GraphData.shared_esc_wf GraphData.shared_correct
  GraphData.shared_sourceSel GraphData.lanes_route_sub
  Network.SafeCert.widen_dep Network.widen_correct Network.widen_sourceSel GraphData.wide_correct
  GraphData.wide_detour_correct GraphData.wide_detour_sourceSel GraphData.shared_slots_correct
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

-- Fluid model: the mesh per unit of wire
#assert_standard_axioms
  Fluid.potential_bound Fluid.Flow.potential_bound_on Fluid.wire_bound Fluid.cut_bound
  Fluid.sum_manhattan Fluid.uniform_dist Fluid.uniform_wire_bound Fluid.throughput_le_wire
  Fluid.mesh_routable Fluid.mesh_upper Fluid.mesh_opt Fluid.mesh_wire Fluid.mesh_len
  Fluid.mesh_cap_le Fluid.wire_ceiling Fluid.wire_ceiling_opt Fluid.mesh_per_wire
  Fluid.ceiling_factor_lt Fluid.mesh_opt_eight Fluid.wire_ceiling_eight

-- Fluid model: the mesh's optimum for every size; no detours needed under uniform traffic
#assert_standard_axioms
  Fluid.mesh_routable_odd Fluid.mesh_cut Fluid.mesh_upper_odd Fluid.mesh_opt_odd
  Fluid.mesh_opt_all Fluid.xyFlow_minimal Fluid.xyRouting_minimal Fluid.xyRoutingOdd_minimal
  Fluid.uniform_minimal_opt

-- Fluid model: the worst case over admissible traffic; O1TURN reaches the best one
#assert_standard_axioms
  Fluid.o1turn_admissible Fluid.o1Routing_minimal Fluid.o1_load Fluid.xy_load
  Fluid.bitcomp_admissible Fluid.bitcomp_upper Fluid.worst_opt Fluid.bitcomp_opt
  Fluid.bitcomp_minimal Fluid.xy_admissible Fluid.xyWorst_admissible Fluid.xy_worst
  Fluid.xy_worst_opt Fluid.o1turn_xy_ratio Fluid.worst_opt_eight Fluid.xy_worst_opt_eight

-- Fluid model: exact optima of the standard patterns on the 8 x 8 mesh (kernel-checked certificates)
#assert_standard_axioms
  Fluid.transpose8_opt Fluid.transpose8_minimal Fluid.shuffle8_opt Fluid.shuffle8_minimal
  Fluid.bitrev8_opt Fluid.bitrev8_minimal Fluid.hotspot8_opt Fluid.hotspot8_minimal_opt
  Fluid.hotspot8_detour_gain

-- Fluid model: Valiant's bound on every symmetric network; worst cases of the torus and hypercube
#assert_standard_axioms
  Fluid.valiant Fluid.valiant_grid Fluid.valiant_mesh Fluid.valiant_mesh_opt
  Fluid.torus_bitcomp_upper Fluid.torus_worst_upper Fluid.cube_comp_upper Fluid.cube_worst_upper
  Fluid.valiant_torus Fluid.torus_worst_opt Fluid.valiant_cube Fluid.cube_worst_opt

-- Fluid model: throughput scales exactly linearly with the connections; lanes reach it
#assert_standard_axioms
  Fluid.Routable.zero Fluid.Routable.smul Fluid.Routable.mono Fluid.Routable.add
  Fluid.routable_sum Fluid.layered_routable Fluid.Routable.copies Fluid.copies_routable_iff
  Fluid.opt_copies Fluid.worstOpt_copies Fluid.opt_superadditive Fluid.mesh_copies_worst
  Fluid.torus_copies_worst Fluid.cube_copies_worst Fluid.mesh_copies_uniform
  Fluid.torus_copies_uniform Fluid.cube_copies_uniform Fluid.torus_eight_copies_worst

-- Packet networks in time: the throughput ceiling of the fluid model, lanes add their throughput
#assert_standard_axioms
  Network.Placement.Fits.respects Network.Placement.restrict_respects Network.sum_update_cval
  Network.step_injW Network.path_injW Network.sum_hopLen Network.round_hopLen
  Network.TimedRun.injW_eq Network.TimedRun.sum_injW Network.TimedRun.injected_le
  Network.TimedRun.sum_lenOf Network.TimedRun.ceiling Network.TimedRun.cut_ceiling
  Network.TimedRun.hop_ceiling Network.TimedRun.occ_update Network.TimedRun.step_occ
  Network.TimedRun.path_occ Network.TimedRun.ejected_ge Network.lanesPlacement_fits
  Network.lanesPlacement_cap Network.lanesTimed Network.lanesTimed_injected
  GraphData.placement_fits GraphData.placement_cap GraphData.netPlacement_fits
  GraphData.budgetPlacement_fits GraphData.detourPlacement_fits

-- Fluid model: backpressure is stable below the fluid optimum, no scheduler above it
#assert_standard_axioms
  Fluid.weight_eq Fluid.Flow.weight_eq Fluid.energy_le_backlog_sq Fluid.backlog_le_energy
  Fluid.queue_sq Fluid.exists_nat_gt_rat Fluid.Run.bounded_of_drift Fluid.Flow.mix
  Fluid.Run.Q_nonneg Fluid.Run.backlog_succ Fluid.Run.delivered_sum Fluid.Run.drift
  Fluid.Run.energy_bounded Fluid.Run.backpressure_stable Fluid.Run.backpressure_optimal
  Fluid.Run.totalFlow Fluid.Run.potential_ceiling Fluid.Run.cut_ceiling Fluid.Run.hop_ceiling
  Fluid.IsHopDistance.copies Fluid.Run.copies_hop_ceiling Fluid.bpRates_maxWeight
  Fluid.bpRates_feasible Fluid.sendAll_sum Fluid.Run.ofArrivals
  Fluid.Run.ofArrivals_backpressure Fluid.mesh_backpressure Fluid.torus_backpressure
  Fluid.cube_backpressure Fluid.mesh_backpressure_exists Fluid.mesh_upper_of_cut
  Fluid.torus_uniform_hop Fluid.cube_uniform_hop Fluid.Run.queue_le_of_energy
  Fluid.Run.backpressure_fitsIn Fluid.Flow.normalize Fluid.meshAdj_symm Fluid.mesh_out_cap
  Fluid.mesh_in_cap Fluid.mesh_buffer
  Fluid.Run.drift_gen Fluid.Run.step_change Fluid.Run.frame_change Fluid.Run.frame_drift
  Fluid.Run.backpressure_stable_bursty Fluid.clamp_eq Fluid.seqPre_total Fluid.sendSeq_sum
  Fluid.Run.ofArrivalsSeq Fluid.Run.ofArrivalsSeq_backpressure Fluid.Run.ofArrivalsSeq_int
  Fluid.mesh_backpressure_packets

-- Fluid model: minimal routing is optimal for every traffic matrix iff the network is a tree
#assert_standard_axioms
  Fluid.UGraph.AllBridges.minimal_of_routable Fluid.UGraph.IsTree.minimal_of_routable
  Fluid.UGraph.IsHopDist.detour_helps Fluid.UGraph.IsHopDist.not_minimal_optimal
  Fluid.UGraph.IsHopDist.minimal_optimal_iff Fluid.UGraph.minimal_optimal_iff_isTree
  Fluid.pathGraph_isTree Fluid.path_minimal_optimal Fluid.cycle4_not_isTree Fluid.cycle4_detour

-- Fluid model: uniform traffic on arc-transitive networks; the torus and the hypercube
#assert_standard_axioms
  Fluid.hop_bound Fluid.minimal_load_total Fluid.balanced_opt Fluid.symmetric_balanced
  Fluid.symmetric_opt Fluid.torus_symmetric_opt Fluid.cube_symmetric_opt
  Fluid.torus_uniform_opt Fluid.torus_uniform_opt_eight Fluid.torus_self_opt
  Fluid.torus_self_routable Fluid.cube_uniform_opt Fluid.cube_uniform_opt_six Fluid.cube_self_opt
  Fluid.cube_self_routable Fluid.torus_worst_opt' Fluid.cube_worst_opt'

-- Fluid model: exact optima on the 8 x 8 torus and the 6-cube (kernel-checked certificates)
#assert_standard_axioms
  Fluid.torusTornado_opt Fluid.torusTornado_minimal_opt Fluid.torusTornado_detour_gain
  Fluid.torusShuffle_opt Fluid.torusShuffle_minimal_opt Fluid.torusShuffle_detour_gain
  Fluid.torusTranspose_opt Fluid.torusTranspose_minimal_opt Fluid.torusTranspose_detour_gain
  Fluid.torusNeighbor_opt Fluid.torusNeighbor_minimal_opt Fluid.torusNeighbor_detour_gain
  Fluid.torusBitrev_opt Fluid.torusBitrev_minimal_opt Fluid.torusBitrev_detour_gain
  Fluid.cubeShuffle_opt Fluid.cubeShuffle_minimal_opt Fluid.cubeShuffle_detour_gain
  Fluid.torusBitcomp_opt Fluid.torusBitcomp_minimal Fluid.torusBitcomp_minimal_opt
  Fluid.cubeTranspose_opt Fluid.cubeTranspose_minimal Fluid.cubeTranspose_minimal_opt
  Fluid.cubeBitrev_opt Fluid.cubeBitrev_minimal Fluid.cubeBitrev_minimal_opt Fluid.cubeBitcomp_opt
  Fluid.cubeBitcomp_minimal Fluid.cubeBitcomp_minimal_opt Fluid.cubeTornado_opt
  Fluid.cubeTornado_minimal Fluid.cubeTornado_minimal_opt

end AsyncLean
