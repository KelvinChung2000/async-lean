/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties
import AsyncLean.Petri.Invariant
import AsyncLean.Petri.SiphonTrap
import AsyncLean.MarkedGraph.Basic
import AsyncLean.Checker.Petri
import AsyncLean.Circuit.Basic
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

-- Verified checker
#assert_standard_axioms
  ExplicitLTS.deadlockFree_of_check ExplicitLTS.livelockFree_of_check
  ExplicitLTS.liveLabel_of_check ExplicitLTS.persistent_of_check ExplicitLTS.of_checkAll
  ExplicitLTS.of_checkCert ExplicitLTS.persistent_of_checkCert
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
