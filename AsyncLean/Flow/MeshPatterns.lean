/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.MeshPatterns.Data

/-!
# Exact fluid optima of the standard traffic patterns on the `8 × 8` mesh

The `8 × 8` mesh (`meshNet 8`, capacity `2` on every directed link) under the standard
patterns of the simulator (`scripts/routing_sim.py`), in the fluid model: the largest throughput
`θ` (per active source) at which the pattern is routable, over **all** routings (adaptive, split
over many paths, with detours) and over **minimal** routings only (`Flow.Minimal` for the
Manhattan distance `MeshCert.mdist`).

* `transpose8_opt`, `transpose8_minimal` : transpose `(x, y) ↦ (y, x)`: `θ = 10/11`.
* `shuffle8_opt`, `shuffle8_minimal` : perfect shuffle (rotate the 6 index bits left): `θ = 1`.
* `bitrev8_opt`, `bitrev8_minimal` : bit reversal of the 6 index bits: `θ = 20/21`.
* For these three permutations **detours add nothing**: the optimum over all routings is reached
  by a minimal flow.
* `hotspot8_opt`, `hotspot8_minimal_opt`, `hotspot8_detour_gain` : hotspot traffic (every vertex
  sends `4/5` uniformly and the others send `1/5` more to the centre `(4, 4)`): `θ = 40/67` over
  all routings but only `840/1471` over minimal routings: detours gain `4.5 %`.  The four links
  into the centre are the bottleneck; with detours they can be loaded evenly, but a vertex in the
  centre's row or column has only one minimal way in.

Every optimum is certified by data computed in exact rational arithmetic by
`scripts/fluid_certificates.py` (`AsyncLean.Flow.MeshPatterns.Data`): a flow at `θ` (the lower
bound) and link lengths with potentials (the upper bound, `Fluid.potential_bound`), checked by
the kernel (`decide +kernel`) with the sound checkers of `AsyncLean.Flow.Certificate`.

Vertex `(x, y)` has the simulator's index `x + 8 y` (`MeshCert.idx`); the permutations are
defined on indices (`transposeIdx`, `shuffleIdx`, `bitrevIdx`) and transported to the grid.
-/

namespace AsyncLean

namespace Fluid

open MeshCert MeshPatternData

/-! ### Patterns -/

/-- The vertex of index `j` of the `8 × 8` grid (`x = j % 8`, `y = j / 8`, reduced mod `8`). -/
def ofIdx8 (j : ℕ) : Fin 8 × Fin 8 :=
  (⟨j % 8, Nat.mod_lt _ (by norm_num)⟩, ⟨j / 8 % 8, Nat.mod_lt _ (by norm_num)⟩)

/-- `ofIdx8` inverts the index below `64`. -/
theorem idx_ofIdx8 {j : ℕ} (h : j < 64) : idx (ofIdx8 j) = j := by
  simp only [idx, ofIdx8]
  omega

/-- The **permutation pattern** of `p`: every vertex `s` sends rate `1` to `p s` (nothing if
`p s = s`). -/
def permDem {V : Type*} [DecidableEq V] (p : V → V) (s d : V) : ℚ :=
  if d = p s ∧ d ≠ s then 1 else 0

/-- The permutation pattern of `σ` on indices. -/
def permN (σ : ℕ → ℕ) (s d : ℕ) : ℕ := if d = σ s ∧ d ≠ s then 1 else 0

/-- The permutation pattern of `p` on the grid is the one of `σ` on indices. -/
theorem permDem_eq {k : ℕ} {p : Fin k × Fin k → Fin k × Fin k} {σ : ℕ → ℕ}
    (hσ : ∀ v, idx (p v) = σ (idx v)) (s d : Fin k × Fin k) :
    permDem p s d = (permN σ (idx s) (idx d) : ℚ) / (1 : ℕ) := by
  have e1 : d = p s ↔ idx d = σ (idx s) := by
    rw [← hσ]; exact ⟨fun h => h ▸ rfl, idx_inj⟩
  have e2 : d = s ↔ idx d = idx s := ⟨fun h => h ▸ rfl, idx_inj⟩
  unfold permDem permN
  simp only [ne_eq, e1, e2]
  split_ifs <;> norm_num

/-- Transpose on indices: `x + 8 y ↦ y + 8 x`. -/
def transposeIdx (j : ℕ) : ℕ := j / 8 + 8 * (j % 8)

/-- Perfect shuffle on indices: rotate the 6 bits left. -/
def shuffleIdx (s : ℕ) : ℕ := ((s <<< 1) ||| (s >>> 5)) &&& 63

/-- Bit reversal on indices: reverse the 6 bits. -/
def bitrevIdx (s : ℕ) : ℕ :=
  s % 2 * 32 + s / 2 % 2 * 16 + s / 4 % 2 * 8 + s / 8 % 2 * 4 + s / 16 % 2 * 2 + s / 32 % 2

/-- The transpose permutation `(x, y) ↦ (y, x)`. -/
def transposeMap (v : Fin 8 × Fin 8) : Fin 8 × Fin 8 := (v.2, v.1)

/-- The perfect shuffle permutation. -/
def shuffleMap (v : Fin 8 × Fin 8) : Fin 8 × Fin 8 := ofIdx8 (shuffleIdx (idx v))

/-- The bit reversal permutation. -/
def bitrevMap (v : Fin 8 × Fin 8) : Fin 8 × Fin 8 := ofIdx8 (bitrevIdx (idx v))

/-- **Transpose traffic** on the `8 × 8` grid. -/
def transpose8 : Fin 8 × Fin 8 → Fin 8 × Fin 8 → ℚ := permDem transposeMap

/-- **Perfect shuffle traffic** on the `8 × 8` grid. -/
def shuffle8 : Fin 8 × Fin 8 → Fin 8 × Fin 8 → ℚ := permDem shuffleMap

/-- **Bit reversal traffic** on the `8 × 8` grid. -/
def bitrev8 : Fin 8 × Fin 8 → Fin 8 × Fin 8 → ℚ := permDem bitrevMap

/-- The hotspot, the vertex `(4, 4)`. -/
def hot8 : Fin 8 × Fin 8 := (4, 4)

/-- **Hotspot traffic** on the `8 × 8` grid: every vertex sends `4/5` spread evenly over the
`63` others (`4/315` each), and every vertex but the hotspot sends `1/5` more to the hotspot. -/
def hotspot8 (s d : Fin 8 × Fin 8) : ℚ :=
  (if s ≠ d then 4 / 315 else 0) + (if d = hot8 ∧ s ≠ hot8 then 1 / 5 else 0)

/-- Hotspot traffic on indices, times `315`. -/
def hotspotN (s d : ℕ) : ℕ := (if s ≠ d then 4 else 0) + (if d = 36 ∧ s ≠ 36 then 63 else 0)

/-- Transpose on the grid is `transposeIdx` on indices. -/
theorem transposeMap_idx (v : Fin 8 × Fin 8) : idx (transposeMap v) = transposeIdx (idx v) := by
  simp only [transposeMap, transposeIdx, idx_div, idx_mod]
  simp only [idx]

/-- The shuffle on the grid is `shuffleIdx` on indices. -/
theorem shuffleMap_idx (v : Fin 8 × Fin 8) : idx (shuffleMap v) = shuffleIdx (idx v) :=
  idx_ofIdx8 (Nat.lt_succ_of_le Nat.and_le_right)

/-- Bit reversal on the grid is `bitrevIdx` on indices. -/
theorem bitrevMap_idx (v : Fin 8 × Fin 8) : idx (bitrevMap v) = bitrevIdx (idx v) :=
  idx_ofIdx8 (by unfold bitrevIdx; omega)

/-- Hotspot traffic is `hotspotN / 315` on indices. -/
theorem hotspot8_eq (s d : Fin 8 × Fin 8) :
    hotspot8 s d = (hotspotN (idx s) (idx d) : ℚ) / (315 : ℕ) := by
  have hh : idx hot8 = 36 := rfl
  have e1 : s = d ↔ idx s = idx d := ⟨fun h => h ▸ rfl, idx_inj⟩
  have e2 : d = hot8 ↔ idx d = 36 := hh ▸ ⟨fun h => h ▸ rfl, idx_inj⟩
  have e3 : s = hot8 ↔ idx s = 36 := hh ▸ ⟨fun h => h ▸ rfl, idx_inj⟩
  unfold hotspot8 hotspotN
  simp only [ne_eq, e1, e2, e3]
  split_ifs <;> norm_num

/-! ### The certificates, checked by the kernel -/

/-- Kernel check: the transpose flow conserves every commodity at `10/11`. -/
theorem transpose_cons :
    consCheck 8 transposeG transposeD (permN transposeIdx) 1 10 11 = true := by decide +kernel

/-- Kernel check: the transpose flow respects the capacities. -/
theorem transpose_cap : capCheck 8 transposeG transposeD = true := by decide +kernel

/-- Kernel check: the transpose flow is minimal. -/
theorem transpose_min : minCheck 8 transposeG = true := by decide +kernel

/-- Kernel check: the transpose dual certificate is a valid potential. -/
theorem transpose_dual : dualCheck 8 transposeP transposeL false = true := by decide +kernel

/-- Kernel check: the transpose dual certificate bounds the throughput by `10/11`. -/
theorem transpose_bound :
    boundCheck 8 (permN transposeIdx) transposeP transposeL 1 10 11 = true := by decide +kernel

/-- Kernel check: the shuffle flow conserves every commodity at `1`. -/
theorem shuffle_cons :
    consCheck 8 shuffleG shuffleD (permN shuffleIdx) 1 1 1 = true := by decide +kernel

/-- Kernel check: the shuffle flow respects the capacities. -/
theorem shuffle_cap : capCheck 8 shuffleG shuffleD = true := by decide +kernel

/-- Kernel check: the shuffle flow is minimal. -/
theorem shuffle_min : minCheck 8 shuffleG = true := by decide +kernel

/-- Kernel check: the shuffle dual certificate is a valid potential. -/
theorem shuffle_dual : dualCheck 8 shuffleP shuffleL false = true := by decide +kernel

/-- Kernel check: the shuffle dual certificate bounds the throughput by `1`. -/
theorem shuffle_bound :
    boundCheck 8 (permN shuffleIdx) shuffleP shuffleL 1 1 1 = true := by decide +kernel

/-- Kernel check: the bit reversal flow conserves every commodity at `20/21`. -/
theorem bitrev_cons :
    consCheck 8 bitrevG bitrevD (permN bitrevIdx) 1 20 21 = true := by decide +kernel

/-- Kernel check: the bit reversal flow respects the capacities. -/
theorem bitrev_cap : capCheck 8 bitrevG bitrevD = true := by decide +kernel

/-- Kernel check: the bit reversal flow is minimal. -/
theorem bitrev_min : minCheck 8 bitrevG = true := by decide +kernel

/-- Kernel check: the bit reversal dual certificate is a valid potential. -/
theorem bitrev_dual : dualCheck 8 bitrevP bitrevL false = true := by decide +kernel

/-- Kernel check: the bit reversal dual certificate bounds the throughput by `20/21`. -/
theorem bitrev_bound :
    boundCheck 8 (permN bitrevIdx) bitrevP bitrevL 1 20 21 = true := by decide +kernel

/-- Kernel check: the hotspot (any routing) flow conserves every commodity at `40/67`. -/
theorem hotspotAny_cons :
    consCheck 8 hotspotAnyG hotspotAnyD hotspotN 315 40 67 = true := by decide +kernel

/-- Kernel check: the hotspot (any routing) flow respects the capacities. -/
theorem hotspotAny_cap : capCheck 8 hotspotAnyG hotspotAnyD = true := by decide +kernel

/-- Kernel check: the hotspot (any routing) dual certificate is a valid potential. -/
theorem hotspotAny_dual : dualCheck 8 hotspotAnyP hotspotAnyL false = true := by decide +kernel

/-- Kernel check: the hotspot (any routing) dual certificate bounds the throughput by `40/67`. -/
theorem hotspotAny_bound :
    boundCheck 8 hotspotN hotspotAnyP hotspotAnyL 315 40 67 = true := by decide +kernel

/-- Kernel check: the hotspot (minimal routing) flow conserves every commodity at `840/1471`. -/
theorem hotspotMin_cons :
    consCheck 8 hotspotMinG hotspotMinD hotspotN 315 840 1471 = true := by decide +kernel

/-- Kernel check: the hotspot (minimal routing) flow respects the capacities. -/
theorem hotspotMin_cap : capCheck 8 hotspotMinG hotspotMinD = true := by decide +kernel

/-- Kernel check: the hotspot (minimal routing) flow is minimal. -/
theorem hotspotMin_min : minCheck 8 hotspotMinG = true := by decide +kernel

/-- Kernel check: the hotspot (minimal routing) dual certificate is a valid potential on the
minimal links. -/
theorem hotspotMin_dual : dualCheck 8 hotspotMinP hotspotMinL true = true := by decide +kernel

/-- Kernel check: the hotspot (minimal routing) dual certificate bounds the throughput by
`840/1471`. -/
theorem hotspotMin_bound :
    boundCheck 8 hotspotN hotspotMinP hotspotMinL 315 840 1471 = true := by decide +kernel

/-! ### The optima -/

/-- **Transpose: the exact fluid optimum over all routings is `10/11`.** -/
theorem transpose8_opt :
    IsGreatest {θ : ℚ | Routable (meshNet 8) transpose8 θ} (10 / 11) :=
  isGreatest_routable _ _ 1 (permDem_eq transposeMap_idx) transposeG transposeD transposeP
    transposeL 10 11 (by norm_num) one_pos (by decide) (by norm_num) transpose_cons transpose_cap
    transpose_dual transpose_bound

/-- **Transpose: the optimum `10/11` is reached by a minimal flow** (detours add nothing). -/
theorem transpose8_minimal : ∃ F : Flow (meshNet 8) transpose8 (10 / 11), F.Minimal mdist :=
  exists_minimal _ _ 1 (permDem_eq transposeMap_idx) transposeG transposeD 10 11 (by norm_num)
    one_pos (by decide) (by norm_num) transpose_cons transpose_cap transpose_min

/-- **Perfect shuffle: the exact fluid optimum over all routings is `1`.** -/
theorem shuffle8_opt : IsGreatest {θ : ℚ | Routable (meshNet 8) shuffle8 θ} 1 :=
  isGreatest_routable _ _ 1 (permDem_eq shuffleMap_idx) shuffleG shuffleD shuffleP shuffleL 1 1
    (by norm_num) one_pos (by decide) one_pos shuffle_cons shuffle_cap shuffle_dual shuffle_bound

/-- **Perfect shuffle: the optimum `1` is reached by a minimal flow.** -/
theorem shuffle8_minimal : ∃ F : Flow (meshNet 8) shuffle8 1, F.Minimal mdist :=
  exists_minimal _ _ 1 (permDem_eq shuffleMap_idx) shuffleG shuffleD 1 1 (by norm_num) one_pos
    (by decide) one_pos shuffle_cons shuffle_cap shuffle_min

/-- **Bit reversal: the exact fluid optimum over all routings is `20/21`.** -/
theorem bitrev8_opt : IsGreatest {θ : ℚ | Routable (meshNet 8) bitrev8 θ} (20 / 21) :=
  isGreatest_routable _ _ 1 (permDem_eq bitrevMap_idx) bitrevG bitrevD bitrevP bitrevL 20 21
    (by norm_num) one_pos (by decide) (by norm_num) bitrev_cons bitrev_cap bitrev_dual
    bitrev_bound

/-- **Bit reversal: the optimum `20/21` is reached by a minimal flow.** -/
theorem bitrev8_minimal : ∃ F : Flow (meshNet 8) bitrev8 (20 / 21), F.Minimal mdist :=
  exists_minimal _ _ 1 (permDem_eq bitrevMap_idx) bitrevG bitrevD 20 21 (by norm_num) one_pos
    (by decide) (by norm_num) bitrev_cons bitrev_cap bitrev_min

/-- **Hotspot: the exact fluid optimum over all routings is `40/67`** (the four links into the
hotspot carry `8 = (40/67) * (63/5 + 4/5)`). -/
theorem hotspot8_opt : IsGreatest {θ : ℚ | Routable (meshNet 8) hotspot8 θ} (40 / 67) :=
  isGreatest_routable _ _ 315 hotspot8_eq hotspotAnyG hotspotAnyD hotspotAnyP hotspotAnyL 40 67
    (by norm_num) (by norm_num) (by decide) (by norm_num) hotspotAny_cons hotspotAny_cap
    hotspotAny_dual hotspotAny_bound

/-- **Hotspot: the exact fluid optimum over minimal routings is `840/1471`.** -/
theorem hotspot8_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (meshNet 8) hotspot8 θ, F.Minimal mdist} (840 / 1471) :=
  isGreatest_minimal _ _ 315 hotspot8_eq hotspotMinG hotspotMinD hotspotMinP hotspotMinL 840 1471
    (by norm_num) (by norm_num) (by decide) (by norm_num) hotspotMin_cons hotspotMin_cap
    hotspotMin_min hotspotMin_dual hotspotMin_bound

/-- **Detours help the hotspot**: the minimal optimum is strictly below the optimum over all
routings (by `4.5 %`). -/
theorem hotspot8_detour_gain : (840 / 1471 : ℚ) < 40 / 67 := by norm_num

end Fluid

end AsyncLean
