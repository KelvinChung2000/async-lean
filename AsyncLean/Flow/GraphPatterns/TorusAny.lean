/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.GraphPatterns.Data
import AsyncLean.Flow.MeshPatterns

/-!
# Kernel checks of the certificates on the `8 × 8` torus, over all routings

The certificates of `AsyncLean.Flow.GraphPatterns.Data` on the `8 × 8` torus, over all routings: the
flows and potentials over all routings for tornado, shuffle, transpose, neighbour and bit reversal,
and the minimal flow with a dual over all routings for bit complement.  Each is checked by the
kernel (`decide +kernel`) with the checkers of `AsyncLean.Flow.GraphCert`; the optima are in
`AsyncLean.Flow.GraphPatterns`.
-/

namespace AsyncLean

namespace Fluid

open MeshCert GraphCert GraphPatternData

/-- Kernel check: the `torusTornadoAny` flow conserves every commodity at `16 / 15`. -/
theorem torusTornadoAny_cons :
    (torusGraph 8).consCheck torusTornadoAnyG torusTornadoAnyD (permN tornadoIdx) 1 16 15 =
      true := by
  decide +kernel

/-- Kernel check: the `torusTornadoAny` flow respects the capacities. -/
theorem torusTornadoAny_cap :
    (torusGraph 8).capCheck 2 torusTornadoAnyG torusTornadoAnyD = true := by
  decide +kernel

/-- Kernel check: the `torusTornadoAny` potential is valid. -/
theorem torusTornadoAny_dual :
    (torusGraph 8).dualCheck torusTornadoAnyP torusTornadoAnyL false = true := by
  decide +kernel

/-- Kernel check: the `torusTornadoAny` dual certificate bounds the throughput by `16 / 15`. -/
theorem torusTornadoAny_bound :
    (torusGraph 8).boundCheck 2 (permN tornadoIdx) torusTornadoAnyP torusTornadoAnyL 1 16 15 =
      true := by
  decide +kernel

/-- Kernel check: the `torusShuffleAny` flow conserves every commodity at `8 / 5`. -/
theorem torusShuffleAny_cons :
    (torusGraph 8).consCheck torusShuffleAnyG torusShuffleAnyD (permN shuffleIdx) 1 8 5 = true := by
  decide +kernel

/-- Kernel check: the `torusShuffleAny` flow respects the capacities. -/
theorem torusShuffleAny_cap :
    (torusGraph 8).capCheck 2 torusShuffleAnyG torusShuffleAnyD = true := by
  decide +kernel

/-- Kernel check: the `torusShuffleAny` potential is valid. -/
theorem torusShuffleAny_dual :
    (torusGraph 8).dualCheck torusShuffleAnyP torusShuffleAnyL false = true := by
  decide +kernel

/-- Kernel check: the `torusShuffleAny` dual certificate bounds the throughput by `8 / 5`. -/
theorem torusShuffleAny_bound :
    (torusGraph 8).boundCheck 2 (permN shuffleIdx) torusShuffleAnyP torusShuffleAnyL 1 8 5 =
      true := by
  decide +kernel

/-- Kernel check: the `torusTransposeAny` flow conserves every commodity at `20 / 11`. -/
theorem torusTransposeAny_cons :
    (torusGraph 8).consCheck torusTransposeAnyG torusTransposeAnyD (permN transposeIdx) 1 20 11 =
      true := by
  decide +kernel

/-- Kernel check: the `torusTransposeAny` flow respects the capacities. -/
theorem torusTransposeAny_cap :
    (torusGraph 8).capCheck 2 torusTransposeAnyG torusTransposeAnyD = true := by
  decide +kernel

/-- Kernel check: the `torusTransposeAny` potential is valid. -/
theorem torusTransposeAny_dual :
    (torusGraph 8).dualCheck torusTransposeAnyP torusTransposeAnyL false = true := by
  decide +kernel

/-- Kernel check: the `torusTransposeAny` dual certificate bounds the throughput by `20 / 11`. -/
theorem torusTransposeAny_bound :
    (torusGraph 8).boundCheck 2 (permN transposeIdx) torusTransposeAnyP torusTransposeAnyL 1 20 11 =
      true := by
  decide +kernel

/-- Kernel check: the `torusNeighborAny` flow conserves every commodity at `16 / 7`. -/
theorem torusNeighborAny_cons :
    (torusGraph 8).consCheck torusNeighborAnyG torusNeighborAnyD (permN neighborIdx) 1 16 7 =
      true := by
  decide +kernel

/-- Kernel check: the `torusNeighborAny` flow respects the capacities. -/
theorem torusNeighborAny_cap :
    (torusGraph 8).capCheck 2 torusNeighborAnyG torusNeighborAnyD = true := by
  decide +kernel

/-- Kernel check: the `torusNeighborAny` potential is valid. -/
theorem torusNeighborAny_dual :
    (torusGraph 8).dualCheck torusNeighborAnyP torusNeighborAnyL false = true := by
  decide +kernel

/-- Kernel check: the `torusNeighborAny` dual certificate bounds the throughput by `16 / 7`. -/
theorem torusNeighborAny_bound :
    (torusGraph 8).boundCheck 2 (permN neighborIdx) torusNeighborAnyP torusNeighborAnyL 1 16 7 =
      true := by
  decide +kernel

/-- Kernel check: the `torusBitrevAny` flow conserves every commodity at `40 / 21`. -/
theorem torusBitrevAny_cons :
    (torusGraph 8).consCheck torusBitrevAnyG torusBitrevAnyD (permN bitrevIdx) 1 40 21 = true := by
  decide +kernel

/-- Kernel check: the `torusBitrevAny` flow respects the capacities. -/
theorem torusBitrevAny_cap :
    (torusGraph 8).capCheck 2 torusBitrevAnyG torusBitrevAnyD = true := by
  decide +kernel

/-- Kernel check: the `torusBitrevAny` potential is valid. -/
theorem torusBitrevAny_dual :
    (torusGraph 8).dualCheck torusBitrevAnyP torusBitrevAnyL false = true := by
  decide +kernel

/-- Kernel check: the `torusBitrevAny` dual certificate bounds the throughput by `40 / 21`. -/
theorem torusBitrevAny_bound :
    (torusGraph 8).boundCheck 2 (permN bitrevIdx) torusBitrevAnyP torusBitrevAnyL 1 40 21 =
      true := by
  decide +kernel

/-- Kernel check: the `torusBitcomp` flow conserves every commodity at `1`. -/
theorem torusBitcomp_cons :
    (torusGraph 8).consCheck torusBitcompG torusBitcompD (permN bitcompIdx) 1 1 1 = true := by
  decide +kernel

/-- Kernel check: the `torusBitcomp` flow respects the capacities. -/
theorem torusBitcomp_cap :
    (torusGraph 8).capCheck 2 torusBitcompG torusBitcompD = true := by
  decide +kernel

/-- Kernel check: the `torusBitcomp` flow is minimal. -/
theorem torusBitcomp_min :
    (torusGraph 8).minCheck torusBitcompG = true := by
  decide +kernel

/-- Kernel check: the `torusBitcomp` potential is valid. -/
theorem torusBitcomp_dual :
    (torusGraph 8).dualCheck torusBitcompP torusBitcompL false = true := by
  decide +kernel

/-- Kernel check: the `torusBitcomp` dual certificate bounds the throughput by `1`. -/
theorem torusBitcomp_bound :
    (torusGraph 8).boundCheck 2 (permN bitcompIdx) torusBitcompP torusBitcompL 1 1 1 = true := by
  decide +kernel

end Fluid

end AsyncLean
