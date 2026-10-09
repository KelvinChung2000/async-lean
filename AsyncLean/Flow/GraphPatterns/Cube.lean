/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.GraphPatterns.Data
import AsyncLean.Flow.MeshPatterns

/-!
# Kernel checks of the certificates on the 6-dimensional hypercube

The certificates of `AsyncLean.Flow.GraphPatterns.Data` on the 6-dimensional hypercube: the flow and
potential over all routings and the minimal pair for the perfect shuffle, and the minimal flow with
a dual over all routings for transpose, bit reversal, bit complement and tornado.  Each is checked
by the kernel (`decide +kernel`) with the checkers of `AsyncLean.Flow.GraphCert`; the optima are in
`AsyncLean.Flow.GraphPatterns`.
-/

namespace AsyncLean

namespace Fluid

open MeshCert GraphCert GraphPatternData

/-- Kernel check: the `cubeShuffleAny` flow conserves every commodity at `108 / 31`. -/
theorem cubeShuffleAny_cons :
    (cubeGraph 6).consCheck cubeShuffleAnyG cubeShuffleAnyD (permN shuffleIdx) 1 108 31 = true := by
  decide +kernel

/-- Kernel check: the `cubeShuffleAny` flow respects the capacities. -/
theorem cubeShuffleAny_cap :
    (cubeGraph 6).capCheck 2 cubeShuffleAnyG cubeShuffleAnyD = true := by
  decide +kernel

/-- Kernel check: the `cubeShuffleAny` potential is valid. -/
theorem cubeShuffleAny_dual :
    (cubeGraph 6).dualCheck cubeShuffleAnyP cubeShuffleAnyL false = true := by
  decide +kernel

/-- Kernel check: the `cubeShuffleAny` dual certificate bounds the throughput by `108 / 31`. -/
theorem cubeShuffleAny_bound :
    (cubeGraph 6).boundCheck 2 (permN shuffleIdx) cubeShuffleAnyP cubeShuffleAnyL 1 108 31 =
      true := by
  decide +kernel

/-- Kernel check: the `cubeShuffleMin` flow conserves every commodity at `12 / 5`. -/
theorem cubeShuffleMin_cons :
    (cubeGraph 6).consCheck cubeShuffleMinG cubeShuffleMinD (permN shuffleIdx) 1 12 5 = true := by
  decide +kernel

/-- Kernel check: the `cubeShuffleMin` flow respects the capacities. -/
theorem cubeShuffleMin_cap :
    (cubeGraph 6).capCheck 2 cubeShuffleMinG cubeShuffleMinD = true := by
  decide +kernel

/-- Kernel check: the `cubeShuffleMin` flow is minimal. -/
theorem cubeShuffleMin_min :
    (cubeGraph 6).minCheck cubeShuffleMinG = true := by
  decide +kernel

/-- Kernel check: the `cubeShuffleMin` potential is valid on the minimal links. -/
theorem cubeShuffleMin_dual :
    (cubeGraph 6).dualCheck cubeShuffleMinP cubeShuffleMinL true = true := by
  decide +kernel

/-- Kernel check: the `cubeShuffleMin` dual certificate bounds the throughput by `12 / 5`. -/
theorem cubeShuffleMin_bound :
    (cubeGraph 6).boundCheck 2 (permN shuffleIdx) cubeShuffleMinP cubeShuffleMinL 1 12 5 =
      true := by
  decide +kernel

/-- Kernel check: the `cubeTranspose` flow conserves every commodity at `4`. -/
theorem cubeTranspose_cons :
    (cubeGraph 6).consCheck cubeTransposeG cubeTransposeD (permN transposeIdx) 1 4 1 = true := by
  decide +kernel

/-- Kernel check: the `cubeTranspose` flow respects the capacities. -/
theorem cubeTranspose_cap :
    (cubeGraph 6).capCheck 2 cubeTransposeG cubeTransposeD = true := by
  decide +kernel

/-- Kernel check: the `cubeTranspose` flow is minimal. -/
theorem cubeTranspose_min :
    (cubeGraph 6).minCheck cubeTransposeG = true := by
  decide +kernel

/-- Kernel check: the `cubeTranspose` potential is valid. -/
theorem cubeTranspose_dual :
    (cubeGraph 6).dualCheck cubeTransposeP cubeTransposeL false = true := by
  decide +kernel

/-- Kernel check: the `cubeTranspose` dual certificate bounds the throughput by `4`. -/
theorem cubeTranspose_bound :
    (cubeGraph 6).boundCheck 2 (permN transposeIdx) cubeTransposeP cubeTransposeL 1 4 1 = true := by
  decide +kernel

/-- Kernel check: the `cubeBitrev` flow conserves every commodity at `4`. -/
theorem cubeBitrev_cons :
    (cubeGraph 6).consCheck cubeBitrevG cubeBitrevD (permN bitrevIdx) 1 4 1 = true := by
  decide +kernel

/-- Kernel check: the `cubeBitrev` flow respects the capacities. -/
theorem cubeBitrev_cap :
    (cubeGraph 6).capCheck 2 cubeBitrevG cubeBitrevD = true := by
  decide +kernel

/-- Kernel check: the `cubeBitrev` flow is minimal. -/
theorem cubeBitrev_min :
    (cubeGraph 6).minCheck cubeBitrevG = true := by
  decide +kernel

/-- Kernel check: the `cubeBitrev` potential is valid. -/
theorem cubeBitrev_dual :
    (cubeGraph 6).dualCheck cubeBitrevP cubeBitrevL false = true := by
  decide +kernel

/-- Kernel check: the `cubeBitrev` dual certificate bounds the throughput by `4`. -/
theorem cubeBitrev_bound :
    (cubeGraph 6).boundCheck 2 (permN bitrevIdx) cubeBitrevP cubeBitrevL 1 4 1 = true := by
  decide +kernel

/-- Kernel check: the `cubeBitcomp` flow conserves every commodity at `2`. -/
theorem cubeBitcomp_cons :
    (cubeGraph 6).consCheck cubeBitcompG cubeBitcompD (permN bitcompIdx) 1 2 1 = true := by
  decide +kernel

/-- Kernel check: the `cubeBitcomp` flow respects the capacities. -/
theorem cubeBitcomp_cap :
    (cubeGraph 6).capCheck 2 cubeBitcompG cubeBitcompD = true := by
  decide +kernel

/-- Kernel check: the `cubeBitcomp` flow is minimal. -/
theorem cubeBitcomp_min :
    (cubeGraph 6).minCheck cubeBitcompG = true := by
  decide +kernel

/-- Kernel check: the `cubeBitcomp` potential is valid. -/
theorem cubeBitcomp_dual :
    (cubeGraph 6).dualCheck cubeBitcompP cubeBitcompL false = true := by
  decide +kernel

/-- Kernel check: the `cubeBitcomp` dual certificate bounds the throughput by `2`. -/
theorem cubeBitcomp_bound :
    (cubeGraph 6).boundCheck 2 (permN bitcompIdx) cubeBitcompP cubeBitcompL 1 2 1 = true := by
  decide +kernel

/-- Kernel check: the `cubeTornado` flow conserves every commodity at `2`. -/
theorem cubeTornado_cons :
    (cubeGraph 6).consCheck cubeTornadoG cubeTornadoD (permN tornadoIdx) 1 2 1 = true := by
  decide +kernel

/-- Kernel check: the `cubeTornado` flow respects the capacities. -/
theorem cubeTornado_cap :
    (cubeGraph 6).capCheck 2 cubeTornadoG cubeTornadoD = true := by
  decide +kernel

/-- Kernel check: the `cubeTornado` flow is minimal. -/
theorem cubeTornado_min :
    (cubeGraph 6).minCheck cubeTornadoG = true := by
  decide +kernel

/-- Kernel check: the `cubeTornado` potential is valid. -/
theorem cubeTornado_dual :
    (cubeGraph 6).dualCheck cubeTornadoP cubeTornadoL false = true := by
  decide +kernel

/-- Kernel check: the `cubeTornado` dual certificate bounds the throughput by `2`. -/
theorem cubeTornado_bound :
    (cubeGraph 6).boundCheck 2 (permN tornadoIdx) cubeTornadoP cubeTornadoL 1 2 1 = true := by
  decide +kernel

end Fluid

end AsyncLean
