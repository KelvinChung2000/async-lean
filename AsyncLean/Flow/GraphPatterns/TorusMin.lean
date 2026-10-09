/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.GraphPatterns.Data
import AsyncLean.Flow.MeshPatterns

/-!
# Kernel checks of the certificates on the `8 × 8` torus, over minimal routings

The certificates of `AsyncLean.Flow.GraphPatterns.Data` on the `8 × 8` torus, over minimal routings:
the minimal flows and the potentials on the minimal links for tornado, shuffle, transpose, neighbour
and bit reversal.  Each is checked by the kernel (`decide +kernel`) with the checkers of
`AsyncLean.Flow.GraphCert`; the optima are in `AsyncLean.Flow.GraphPatterns`.
-/

namespace AsyncLean

namespace Fluid

open MeshCert GraphCert GraphPatternData

/-- Kernel check: the `torusTornadoMin` flow conserves every commodity at `2 / 3`. -/
theorem torusTornadoMin_cons :
    (torusGraph 8).consCheck torusTornadoMinG torusTornadoMinD (permN tornadoIdx) 1 2 3 = true := by
  decide +kernel

/-- Kernel check: the `torusTornadoMin` flow respects the capacities. -/
theorem torusTornadoMin_cap :
    (torusGraph 8).capCheck 2 torusTornadoMinG torusTornadoMinD = true := by
  decide +kernel

/-- Kernel check: the `torusTornadoMin` flow is minimal. -/
theorem torusTornadoMin_min :
    (torusGraph 8).minCheck torusTornadoMinG = true := by
  decide +kernel

/-- Kernel check: the `torusTornadoMin` potential is valid on the minimal links. -/
theorem torusTornadoMin_dual :
    (torusGraph 8).dualCheck torusTornadoMinP torusTornadoMinL true = true := by
  decide +kernel

/-- Kernel check: the `torusTornadoMin` dual certificate bounds the throughput by `2 / 3`. -/
theorem torusTornadoMin_bound :
    (torusGraph 8).boundCheck 2 (permN tornadoIdx) torusTornadoMinP torusTornadoMinL 1 2 3 =
      true := by
  decide +kernel

/-- Kernel check: the `torusShuffleMin` flow conserves every commodity at `1`. -/
theorem torusShuffleMin_cons :
    (torusGraph 8).consCheck torusShuffleMinG torusShuffleMinD (permN shuffleIdx) 1 1 1 = true := by
  decide +kernel

/-- Kernel check: the `torusShuffleMin` flow respects the capacities. -/
theorem torusShuffleMin_cap :
    (torusGraph 8).capCheck 2 torusShuffleMinG torusShuffleMinD = true := by
  decide +kernel

/-- Kernel check: the `torusShuffleMin` flow is minimal. -/
theorem torusShuffleMin_min :
    (torusGraph 8).minCheck torusShuffleMinG = true := by
  decide +kernel

/-- Kernel check: the `torusShuffleMin` potential is valid on the minimal links. -/
theorem torusShuffleMin_dual :
    (torusGraph 8).dualCheck torusShuffleMinP torusShuffleMinL true = true := by
  decide +kernel

/-- Kernel check: the `torusShuffleMin` dual certificate bounds the throughput by `1`. -/
theorem torusShuffleMin_bound :
    (torusGraph 8).boundCheck 2 (permN shuffleIdx) torusShuffleMinP torusShuffleMinL 1 1 1 =
      true := by
  decide +kernel

/-- Kernel check: the `torusTransposeMin` flow conserves every commodity at `4 / 3`. -/
theorem torusTransposeMin_cons :
    (torusGraph 8).consCheck torusTransposeMinG torusTransposeMinD (permN transposeIdx) 1 4 3 =
      true := by
  decide +kernel

/-- Kernel check: the `torusTransposeMin` flow respects the capacities. -/
theorem torusTransposeMin_cap :
    (torusGraph 8).capCheck 2 torusTransposeMinG torusTransposeMinD = true := by
  decide +kernel

/-- Kernel check: the `torusTransposeMin` flow is minimal. -/
theorem torusTransposeMin_min :
    (torusGraph 8).minCheck torusTransposeMinG = true := by
  decide +kernel

/-- Kernel check: the `torusTransposeMin` potential is valid on the minimal links. -/
theorem torusTransposeMin_dual :
    (torusGraph 8).dualCheck torusTransposeMinP torusTransposeMinL true = true := by
  decide +kernel

/-- Kernel check: the `torusTransposeMin` dual certificate bounds the throughput by `4 / 3`. -/
theorem torusTransposeMin_bound :
    (torusGraph 8).boundCheck 2 (permN transposeIdx) torusTransposeMinP torusTransposeMinL 1 4 3 =
      true := by
  decide +kernel

/-- Kernel check: the `torusNeighborMin` flow conserves every commodity at `2`. -/
theorem torusNeighborMin_cons :
    (torusGraph 8).consCheck torusNeighborMinG torusNeighborMinD (permN neighborIdx) 1 2 1 =
      true := by
  decide +kernel

/-- Kernel check: the `torusNeighborMin` flow respects the capacities. -/
theorem torusNeighborMin_cap :
    (torusGraph 8).capCheck 2 torusNeighborMinG torusNeighborMinD = true := by
  decide +kernel

/-- Kernel check: the `torusNeighborMin` flow is minimal. -/
theorem torusNeighborMin_min :
    (torusGraph 8).minCheck torusNeighborMinG = true := by
  decide +kernel

/-- Kernel check: the `torusNeighborMin` potential is valid on the minimal links. -/
theorem torusNeighborMin_dual :
    (torusGraph 8).dualCheck torusNeighborMinP torusNeighborMinL true = true := by
  decide +kernel

/-- Kernel check: the `torusNeighborMin` dual certificate bounds the throughput by `2`. -/
theorem torusNeighborMin_bound :
    (torusGraph 8).boundCheck 2 (permN neighborIdx) torusNeighborMinP torusNeighborMinL 1 2 1 =
      true := by
  decide +kernel

/-- Kernel check: the `torusBitrevMin` flow conserves every commodity at `16 / 9`. -/
theorem torusBitrevMin_cons :
    (torusGraph 8).consCheck torusBitrevMinG torusBitrevMinD (permN bitrevIdx) 1 16 9 = true := by
  decide +kernel

/-- Kernel check: the `torusBitrevMin` flow respects the capacities. -/
theorem torusBitrevMin_cap :
    (torusGraph 8).capCheck 2 torusBitrevMinG torusBitrevMinD = true := by
  decide +kernel

/-- Kernel check: the `torusBitrevMin` flow is minimal. -/
theorem torusBitrevMin_min :
    (torusGraph 8).minCheck torusBitrevMinG = true := by
  decide +kernel

/-- Kernel check: the `torusBitrevMin` potential is valid on the minimal links. -/
theorem torusBitrevMin_dual :
    (torusGraph 8).dualCheck torusBitrevMinP torusBitrevMinL true = true := by
  decide +kernel

/-- Kernel check: the `torusBitrevMin` dual certificate bounds the throughput by `16 / 9`. -/
theorem torusBitrevMin_bound :
    (torusGraph 8).boundCheck 2 (permN bitrevIdx) torusBitrevMinP torusBitrevMinL 1 16 9 =
      true := by
  decide +kernel

end Fluid

end AsyncLean
