/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.GraphPatterns.TorusAny
import AsyncLean.Flow.GraphPatterns.TorusMin
import AsyncLean.Flow.GraphPatterns.Cube
import AsyncLean.Flow.MeshWorst

/-!
# Exact fluid optima of the standard traffic patterns on the torus and the hypercube

The `8 × 8` torus (`torusNet 8`) and the 6-dimensional hypercube (`cubeNet 6`), capacity `2` on
every directed link, under the standard permutation patterns, in the fluid model: the largest
throughput `θ` (per active source) at which the pattern is routable, over **all** routings
(adaptive, split over many paths, with detours) and over **minimal** routings only
(`Flow.Minimal` for the hop distance `torusDist`, `cubeDist`).

The patterns are defined on the vertex index `s < 64`: on the torus `s = x + 8 y`; on the
hypercube **coordinate `i` of the vertex is bit `i` of `s`** (`GraphCert.cubeEquiv`).  On the
hypercube the index permutations become: transpose `u ↦ (i ↦ u (i + 3))` (swap the low and the
high three bits), shuffle `u ↦ (i ↦ u (i - 1))` (rotate the bits), bit reversal
`u ↦ (i ↦ u (5 - i))`, bit complement `u ↦ (i ↦ !u i)`.

**Torus** (minimal-only optimum / optimum over all routings):

* tornado `(x, y) ↦ (x + 3, y)`: `2/3` / `16/15` (detours gain `60 %`);
* perfect shuffle: `1` / `8/5` (`+60 %`);
* transpose: `4/3` / `20/11` (`+36 %`);
* neighbour `(x, y) ↦ (x + 1, y)`: `2` / `16/7` (`+14 %`);
* bit reversal: `16/9` / `40/21` (`+7 %`);
* bit complement: `1` / `1`.

**Hypercube**:

* perfect shuffle: `12/5` / `108/31` (`+45 %`);
* transpose `4`, bit reversal `4`, bit complement `2`, tornado `2`: minimal routing is optimal.

The demands are `tornado8`, `shuffle8`, `transpose8`, `neighbor8`, `bitrev8` and `bitcomp 8` on
the torus (on `Fin 8 × Fin 8`, shared with the mesh), and `cubeShuffle`, `cubeTranspose`,
`cubeBitrev`, `cubeBitcomp` and `cubeTornado` on the hypercube, all permutation patterns
(`permDem`).  For each pattern `X` (`torusTornado`, …, `cubeTornado`): `X_opt` (`IsGreatest` over
all routings), `X_minimal_opt` (`IsGreatest` over minimal routings), and `X_detour_gain` (the
strict gap) or `X_minimal` (a minimal flow reaches the optimum over all routings).  Uniform and
hotspot traffic are not covered here.  Every optimum is certified by data computed in exact rational
arithmetic by `scripts/graph_certificates.py` (`AsyncLean.Flow.GraphPatterns.Data`): a flow at `θ`
(the lower bound) and port lengths with potentials (the upper bound, `Fluid.potential_bound`),
checked by the kernel (`decide +kernel`, in `GraphPatterns.TorusAny`, `GraphPatterns.TorusMin`
and `GraphPatterns.Cube`) with the sound checkers of `AsyncLean.Flow.GraphCert` and transported
to `torusNet 8` and `cubeNet 6` by `GraphCert.torusModel` and `GraphCert.cubeModel`.
-/

namespace AsyncLean

namespace Fluid

open MeshCert GraphCert GraphPatternData

/-! ### Permutation patterns on indices -/

/-- The permutation pattern of `p` is the one of `σ` on the indices given by `e`. -/
theorem permDem_index {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n) {p : V → V}
    {σ : ℕ → ℕ} (hσ : ∀ v, (e (p v) : ℕ) = σ (e v)) (s d : V) :
    permDem p s d = (permN σ (e s) (e d) : ℚ) / (1 : ℕ) := by
  have e1 : d = p s ↔ (e d : ℕ) = σ (e s) := by
    rw [← hσ]; exact ⟨fun h => h ▸ rfl, fun h => e.injective (Fin.ext h)⟩
  have e2 : d = s ↔ (e d : ℕ) = e s :=
    ⟨fun h => h ▸ rfl, fun h => e.injective (Fin.ext h)⟩
  unfold permDem permN
  simp only [ne_eq, e1, e2]
  split_ifs <;> norm_num

/-! ### The torus patterns -/

/-- The tornado permutation `(x, y) ↦ (x + 3, y)` (half-way round the ring, less one). -/
def tornadoMap (v : Fin 8 × Fin 8) : Fin 8 × Fin 8 := (v.1 + 3, v.2)

/-- The neighbour permutation `(x, y) ↦ (x + 1, y)`. -/
def neighborMap (v : Fin 8 × Fin 8) : Fin 8 × Fin 8 := (v.1 + 1, v.2)

/-- **Tornado traffic** on the `8 × 8` grid. -/
def tornado8 : Fin 8 × Fin 8 → Fin 8 × Fin 8 → ℚ := permDem tornadoMap

/-- **Neighbour traffic** on the `8 × 8` grid. -/
def neighbor8 : Fin 8 × Fin 8 → Fin 8 × Fin 8 → ℚ := permDem neighborMap

/-- Tornado on the grid is `tornadoIdx` on indices. -/
theorem tornadoMap_idx (v : Fin 8 × Fin 8) : idx (tornadoMap v) = tornadoIdx (idx v) := by
  rw [tornadoIdx, idx_mod, idx_div]
  simp [idx, tornadoMap, Fin.val_add]

/-- Neighbour traffic on the grid is `neighborIdx` on indices. -/
theorem neighborMap_idx (v : Fin 8 × Fin 8) : idx (neighborMap v) = neighborIdx (idx v) := by
  rw [neighborIdx, idx_mod, idx_div]
  simp [idx, neighborMap, Fin.val_add]

/-- The bit complement permutation `(x, y) ↦ (7 - x, 7 - y)`. -/
def bitcompMap (v : Fin 8 × Fin 8) : Fin 8 × Fin 8 := (v.1.rev, v.2.rev)

/-- Bit complement traffic (`bitcomp 8`) is the permutation pattern of `bitcompMap`. -/
theorem bitcomp8_eq (s d : Fin 8 × Fin 8) : bitcomp 8 s d = permDem bitcompMap s d := by
  have hs : (s.1.rev, s.2.rev) ≠ s := by revert s; decide
  unfold bitcomp permDem bitcompMap
  by_cases h : d = (s.1.rev, s.2.rev)
  · subst h; simp [hs]
  · simp [h]

/-- Bit complement on the grid is `bitcompIdx` on indices. -/
theorem bitcompMap_idx (v : Fin 8 × Fin 8) : idx (bitcompMap v) = bitcompIdx (idx v) := by
  simp only [idx, bitcompMap, bitcompIdx, Fin.val_rev]
  omega

/-- A permutation of the torus given on indices, through `torusModel`. -/
theorem torus_perm {p : Fin 8 × Fin 8 → Fin 8 × Fin 8} {σ : ℕ → ℕ}
    (h : ∀ v, idx (p v) = σ (idx v)) (v : Fin 8 × Fin 8) :
    (torusModel.e (p v) : ℕ) = σ (torusModel.e v) :=
  (torusEquiv_val (p v)).trans ((h v).trans (congrArg σ (torusEquiv_val v).symm))

/-! ### The hypercube patterns -/

/-- A vertex of the hypercube is determined by the bits of its index. -/
theorem cubeEquiv_eq_of_bits {n : ℕ} (u : Fin n → Bool) {m : ℕ} (hm : m < 2 ^ n)
    (h : ∀ i : Fin n, m / 2 ^ (i : ℕ) % 2 = if u i then 1 else 0) :
    (cubeEquiv n u : ℕ) = m := by
  have hw : u = (cubeEquiv n).symm ⟨m, hm⟩ := by
    funext i
    have h1 := cubeEquiv_bit ((cubeEquiv n).symm ⟨m, hm⟩) i
    rw [Equiv.apply_symm_apply] at h1
    have h2 := h i
    rw [h1] at h2
    revert h2
    cases u i <;> cases ((cubeEquiv n).symm ⟨m, hm⟩ i) <;> simp
  rw [hw, Equiv.apply_symm_apply]

/-- A permutation `π` of the coordinates of the hypercube is the permutation `σ` of the indices if
bit `i` of `σ j` is bit `π i` of `j`. -/
theorem cubeEquiv_coord (π : Fin 6 → Fin 6) (σ : ℕ → ℕ)
    (hσ : ∀ j < 64, σ j < 64 ∧
      ∀ i : Fin 6, σ j / 2 ^ (i : ℕ) % 2 = j / 2 ^ (π i : ℕ) % 2)
    (u : Fin 6 → Bool) : (cubeEquiv 6 (fun i => u (π i)) : ℕ) = σ (cubeEquiv 6 u) := by
  obtain ⟨h1, h2⟩ := hσ _ (cubeEquiv 6 u).isLt
  exact cubeEquiv_eq_of_bits _ h1 fun i => by rw [h2, cubeEquiv_bit]

/-- The vertex of the hypercube of index `j` (mod `64`). -/
def cubeOfIdx (j : ℕ) : Fin 6 → Bool :=
  (cubeEquiv 6).symm ⟨j % 64, Nat.mod_lt _ (by norm_num)⟩

/-- `cubeOfIdx` inverts the index below `64`. -/
theorem cubeEquiv_ofIdx {j : ℕ} (h : j < 64) : (cubeEquiv 6 (cubeOfIdx j) : ℕ) = j := by
  simp [cubeOfIdx, Nat.mod_eq_of_lt h]

/-- Transpose on the hypercube: swap the low and the high three coordinates. -/
def cubeTransposeMap (u : Fin 6 → Bool) : Fin 6 → Bool := fun i => u (i + 3)

/-- The perfect shuffle on the hypercube: rotate the coordinates. -/
def cubeShuffleMap (u : Fin 6 → Bool) : Fin 6 → Bool := fun i => u (i - 1)

/-- Bit reversal on the hypercube: reverse the coordinates. -/
def cubeBitrevMap (u : Fin 6 → Bool) : Fin 6 → Bool := fun i => u i.rev

/-- Bit complement on the hypercube: complement every coordinate. -/
def cubeBitcompMap (u : Fin 6 → Bool) : Fin 6 → Bool := fun i => !u i

/-- Tornado on the hypercube: add `3` mod `8` to the number formed by the low three
coordinates. -/
def cubeTornadoMap (u : Fin 6 → Bool) : Fin 6 → Bool := cubeOfIdx (tornadoIdx (cubeEquiv 6 u))

/-- **Transpose traffic** on the hypercube. -/
def cubeTranspose : (Fin 6 → Bool) → (Fin 6 → Bool) → ℚ := permDem cubeTransposeMap

/-- **Perfect shuffle traffic** on the hypercube. -/
def cubeShuffle : (Fin 6 → Bool) → (Fin 6 → Bool) → ℚ := permDem cubeShuffleMap

/-- **Bit reversal traffic** on the hypercube. -/
def cubeBitrev : (Fin 6 → Bool) → (Fin 6 → Bool) → ℚ := permDem cubeBitrevMap

/-- **Bit complement traffic** on the hypercube. -/
def cubeBitcomp : (Fin 6 → Bool) → (Fin 6 → Bool) → ℚ := permDem cubeBitcompMap

/-- **Tornado traffic** on the hypercube. -/
def cubeTornado : (Fin 6 → Bool) → (Fin 6 → Bool) → ℚ := permDem cubeTornadoMap

/-- Transpose on the hypercube is `transposeIdx` on indices. -/
theorem cubeTransposeMap_idx (u : Fin 6 → Bool) :
    (cubeModel.e (cubeTransposeMap u) : ℕ) = transposeIdx (cubeModel.e u) :=
  cubeEquiv_coord (fun i => i + 3) transposeIdx (by decide +kernel) u

/-- The shuffle on the hypercube is `shuffleIdx` on indices. -/
theorem cubeShuffleMap_idx (u : Fin 6 → Bool) :
    (cubeModel.e (cubeShuffleMap u) : ℕ) = shuffleIdx (cubeModel.e u) :=
  cubeEquiv_coord (fun i => i - 1) shuffleIdx (by decide +kernel) u

/-- Bit reversal on the hypercube is `bitrevIdx` on indices. -/
theorem cubeBitrevMap_idx (u : Fin 6 → Bool) :
    (cubeModel.e (cubeBitrevMap u) : ℕ) = bitrevIdx (cubeModel.e u) :=
  cubeEquiv_coord Fin.rev bitrevIdx (by decide +kernel) u

/-- Bit complement on the hypercube is `bitcompIdx` on indices. -/
theorem cubeBitcompMap_idx (u : Fin 6 → Bool) :
    (cubeModel.e (cubeBitcompMap u) : ℕ) = bitcompIdx (cubeModel.e u) := by
  have hσ : ∀ j < 64, ∀ i : Fin 6,
      (63 - j) / 2 ^ (i : ℕ) % 2 = 1 - j / 2 ^ (i : ℕ) % 2 := by
    decide +kernel
  have hu := (cubeEquiv 6 u).isLt
  show (cubeEquiv 6 (cubeBitcompMap u) : ℕ) = 63 - (cubeEquiv 6 u : ℕ)
  refine cubeEquiv_eq_of_bits _ (Nat.lt_of_le_of_lt (Nat.sub_le 63 _) (by norm_num)) fun i => ?_
  rw [hσ _ hu, cubeEquiv_bit]
  by_cases h : u i = true <;> simp [cubeBitcompMap, h]

/-- Tornado on the hypercube is `tornadoIdx` on indices. -/
theorem cubeTornadoMap_idx (u : Fin 6 → Bool) :
    (cubeModel.e (cubeTornadoMap u) : ℕ) = tornadoIdx (cubeModel.e u) :=
  cubeEquiv_ofIdx (by unfold tornadoIdx; have := (cubeEquiv 6 u).isLt; omega)

/-! ### The optima -/

/-- Tornado on the indices. -/
theorem torusTornado_dem (s d : Fin 8 × Fin 8) :
    tornado8 s d = (permN tornadoIdx (torusModel.e s) (torusModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index torusModel.e (torus_perm tornadoMap_idx) s d

/-- **Tornado on the torus: the exact fluid optimum over all routings is `16/15`.** -/
theorem torusTornado_opt :
    IsGreatest {θ : ℚ | Routable (torusNet 8) tornado8 θ} (16 / 15) :=
  torusModel.isGreatest_routable _ _ 1 torusTornado_dem torusTornadoAnyG torusTornadoAnyD
    torusTornadoAnyP torusTornadoAnyL 16 15 (by norm_num) one_pos (by decide) (by norm_num)
    torusTornadoAny_cons torusTornadoAny_cap torusTornadoAny_dual torusTornadoAny_bound

/-- **Tornado on the torus: the exact fluid optimum over minimal routings is
`2/3`.** -/
theorem torusTornado_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (torusNet 8) tornado8 θ, F.Minimal torusDist} (2 / 3) :=
  torusModel.isGreatest_minimal _ _ 1 torusTornado_dem torusTornadoMinG torusTornadoMinD
    torusTornadoMinP torusTornadoMinL 2 3 (by norm_num) one_pos (by decide) (by norm_num)
    torusTornadoMin_cons torusTornadoMin_cap torusTornadoMin_min torusTornadoMin_dual
    torusTornadoMin_bound

/-- **Tornado on the torus: detours help**: the minimal optimum is below the optimum
over all routings (by `60 %`). -/
theorem torusTornado_detour_gain : (2 / 3 : ℚ) < 16 / 15 := by norm_num

/-- Perfect shuffle on the indices. -/
theorem torusShuffle_dem (s d : Fin 8 × Fin 8) :
    shuffle8 s d = (permN shuffleIdx (torusModel.e s) (torusModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index torusModel.e (torus_perm shuffleMap_idx) s d

/-- **Perfect shuffle on the torus: the exact fluid optimum over all routings is `8/5`.** -/
theorem torusShuffle_opt :
    IsGreatest {θ : ℚ | Routable (torusNet 8) shuffle8 θ} (8 / 5) :=
  torusModel.isGreatest_routable _ _ 1 torusShuffle_dem torusShuffleAnyG torusShuffleAnyD
    torusShuffleAnyP torusShuffleAnyL 8 5 (by norm_num) one_pos (by decide) (by norm_num)
    torusShuffleAny_cons torusShuffleAny_cap torusShuffleAny_dual torusShuffleAny_bound

/-- **Perfect shuffle on the torus: the exact fluid optimum over minimal routings is
`1`.** -/
theorem torusShuffle_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (torusNet 8) shuffle8 θ, F.Minimal torusDist} 1 :=
  torusModel.isGreatest_minimal _ _ 1 torusShuffle_dem torusShuffleMinG torusShuffleMinD
    torusShuffleMinP torusShuffleMinL 1 1 (by norm_num) one_pos (by decide) one_pos
    torusShuffleMin_cons torusShuffleMin_cap torusShuffleMin_min torusShuffleMin_dual
    torusShuffleMin_bound

/-- **Perfect shuffle on the torus: detours help**: the minimal optimum is below the optimum
over all routings (by `60 %`). -/
theorem torusShuffle_detour_gain : (1 : ℚ) < 8 / 5 := by norm_num

/-- Transpose on the indices. -/
theorem torusTranspose_dem (s d : Fin 8 × Fin 8) :
    transpose8 s d = (permN transposeIdx (torusModel.e s) (torusModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index torusModel.e (torus_perm transposeMap_idx) s d

/-- **Transpose on the torus: the exact fluid optimum over all routings is `20/11`.** -/
theorem torusTranspose_opt :
    IsGreatest {θ : ℚ | Routable (torusNet 8) transpose8 θ} (20 / 11) :=
  torusModel.isGreatest_routable _ _ 1 torusTranspose_dem torusTransposeAnyG torusTransposeAnyD
    torusTransposeAnyP torusTransposeAnyL 20 11 (by norm_num) one_pos (by decide) (by norm_num)
    torusTransposeAny_cons torusTransposeAny_cap torusTransposeAny_dual torusTransposeAny_bound

/-- **Transpose on the torus: the exact fluid optimum over minimal routings is
`4/3`.** -/
theorem torusTranspose_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (torusNet 8) transpose8 θ, F.Minimal torusDist} (4 / 3) :=
  torusModel.isGreatest_minimal _ _ 1 torusTranspose_dem torusTransposeMinG torusTransposeMinD
    torusTransposeMinP torusTransposeMinL 4 3 (by norm_num) one_pos (by decide) (by norm_num)
    torusTransposeMin_cons torusTransposeMin_cap torusTransposeMin_min torusTransposeMin_dual
    torusTransposeMin_bound

/-- **Transpose on the torus: detours help**: the minimal optimum is below the optimum
over all routings (by `36 %`). -/
theorem torusTranspose_detour_gain : (4 / 3 : ℚ) < 20 / 11 := by norm_num

/-- Neighbour traffic on the indices. -/
theorem torusNeighbor_dem (s d : Fin 8 × Fin 8) :
    neighbor8 s d = (permN neighborIdx (torusModel.e s) (torusModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index torusModel.e (torus_perm neighborMap_idx) s d

/-- **Neighbour traffic on the torus: the exact fluid optimum over all routings is `16/7`.** -/
theorem torusNeighbor_opt :
    IsGreatest {θ : ℚ | Routable (torusNet 8) neighbor8 θ} (16 / 7) :=
  torusModel.isGreatest_routable _ _ 1 torusNeighbor_dem torusNeighborAnyG torusNeighborAnyD
    torusNeighborAnyP torusNeighborAnyL 16 7 (by norm_num) one_pos (by decide) (by norm_num)
    torusNeighborAny_cons torusNeighborAny_cap torusNeighborAny_dual torusNeighborAny_bound

/-- **Neighbour traffic on the torus: the exact fluid optimum over minimal routings is
`2`.** -/
theorem torusNeighbor_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (torusNet 8) neighbor8 θ, F.Minimal torusDist} 2 :=
  torusModel.isGreatest_minimal _ _ 1 torusNeighbor_dem torusNeighborMinG torusNeighborMinD
    torusNeighborMinP torusNeighborMinL 2 1 (by norm_num) one_pos (by decide) one_pos
    torusNeighborMin_cons torusNeighborMin_cap torusNeighborMin_min torusNeighborMin_dual
    torusNeighborMin_bound

/-- **Neighbour traffic on the torus: detours help**: the minimal optimum is below the optimum
over all routings (by `14 %`). -/
theorem torusNeighbor_detour_gain : (2 : ℚ) < 16 / 7 := by norm_num

/-- Bit reversal on the indices. -/
theorem torusBitrev_dem (s d : Fin 8 × Fin 8) :
    bitrev8 s d = (permN bitrevIdx (torusModel.e s) (torusModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index torusModel.e (torus_perm bitrevMap_idx) s d

/-- **Bit reversal on the torus: the exact fluid optimum over all routings is `40/21`.** -/
theorem torusBitrev_opt :
    IsGreatest {θ : ℚ | Routable (torusNet 8) bitrev8 θ} (40 / 21) :=
  torusModel.isGreatest_routable _ _ 1 torusBitrev_dem torusBitrevAnyG torusBitrevAnyD
    torusBitrevAnyP torusBitrevAnyL 40 21 (by norm_num) one_pos (by decide) (by norm_num)
    torusBitrevAny_cons torusBitrevAny_cap torusBitrevAny_dual torusBitrevAny_bound

/-- **Bit reversal on the torus: the exact fluid optimum over minimal routings is
`16/9`.** -/
theorem torusBitrev_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (torusNet 8) bitrev8 θ, F.Minimal torusDist} (16 / 9) :=
  torusModel.isGreatest_minimal _ _ 1 torusBitrev_dem torusBitrevMinG torusBitrevMinD
    torusBitrevMinP torusBitrevMinL 16 9 (by norm_num) one_pos (by decide) (by norm_num)
    torusBitrevMin_cons torusBitrevMin_cap torusBitrevMin_min torusBitrevMin_dual
    torusBitrevMin_bound

/-- **Bit reversal on the torus: detours help**: the minimal optimum is below the optimum
over all routings (by `7 %`). -/
theorem torusBitrev_detour_gain : (16 / 9 : ℚ) < 40 / 21 := by norm_num

/-- Bit complement on the indices. -/
theorem torusBitcomp_dem (s d : Fin 8 × Fin 8) :
    (bitcomp 8) s d = (permN bitcompIdx (torusModel.e s) (torusModel.e d) : ℚ) / (1 : ℕ) :=
  (bitcomp8_eq s d).trans (permDem_index torusModel.e (torus_perm bitcompMap_idx) s d)

/-- **Bit complement on the torus: the exact fluid optimum over all routings is `1`.** -/
theorem torusBitcomp_opt :
    IsGreatest {θ : ℚ | Routable (torusNet 8) (bitcomp 8) θ} 1 :=
  torusModel.isGreatest_routable _ _ 1 torusBitcomp_dem torusBitcompG torusBitcompD torusBitcompP
    torusBitcompL 1 1 (by norm_num) one_pos (by decide) one_pos torusBitcomp_cons torusBitcomp_cap
    torusBitcomp_dual torusBitcomp_bound

/-- **Bit complement on the torus: the optimum `1` is reached by a minimal flow** (detours add
nothing). -/
theorem torusBitcomp_minimal : ∃ F : Flow (torusNet 8) (bitcomp 8) 1, F.Minimal torusDist :=
  torusModel.exists_minimal _ _ 1 torusBitcomp_dem torusBitcompG torusBitcompD 1 1 (by norm_num)
    one_pos (by decide) one_pos torusBitcomp_cons torusBitcomp_cap torusBitcomp_min

/-- **Bit complement on the torus: the exact fluid optimum over minimal routings is also
`1`.** -/
theorem torusBitcomp_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (torusNet 8) (bitcomp 8) θ, F.Minimal torusDist} 1 :=
  isGreatest_minimal_of_routable torusBitcomp_opt torusBitcomp_minimal

/-- Perfect shuffle on the indices. -/
theorem cubeShuffle_dem (s d : Fin 6 → Bool) :
    cubeShuffle s d = (permN shuffleIdx (cubeModel.e s) (cubeModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index cubeModel.e cubeShuffleMap_idx s d

/-- **Perfect shuffle on the hypercube: the exact fluid optimum over all routings is `108/31`.** -/
theorem cubeShuffle_opt :
    IsGreatest {θ : ℚ | Routable (cubeNet 6) cubeShuffle θ} (108 / 31) :=
  cubeModel.isGreatest_routable _ _ 1 cubeShuffle_dem cubeShuffleAnyG cubeShuffleAnyD
    cubeShuffleAnyP cubeShuffleAnyL 108 31 (by norm_num) one_pos (by decide) (by norm_num)
    cubeShuffleAny_cons cubeShuffleAny_cap cubeShuffleAny_dual cubeShuffleAny_bound

/-- **Perfect shuffle on the hypercube: the exact fluid optimum over minimal routings is
`12/5`.** -/
theorem cubeShuffle_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (cubeNet 6) cubeShuffle θ, F.Minimal cubeDist} (12 / 5) :=
  cubeModel.isGreatest_minimal _ _ 1 cubeShuffle_dem cubeShuffleMinG cubeShuffleMinD cubeShuffleMinP
    cubeShuffleMinL 12 5 (by norm_num) one_pos (by decide) (by norm_num) cubeShuffleMin_cons
    cubeShuffleMin_cap cubeShuffleMin_min cubeShuffleMin_dual cubeShuffleMin_bound

/-- **Perfect shuffle on the hypercube: detours help**: the minimal optimum is below the optimum
over all routings (by `45 %`). -/
theorem cubeShuffle_detour_gain : (12 / 5 : ℚ) < 108 / 31 := by norm_num

/-- Transpose on the indices. -/
theorem cubeTranspose_dem (s d : Fin 6 → Bool) :
    cubeTranspose s d = (permN transposeIdx (cubeModel.e s) (cubeModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index cubeModel.e cubeTransposeMap_idx s d

/-- **Transpose on the hypercube: the exact fluid optimum over all routings is `4`.** -/
theorem cubeTranspose_opt :
    IsGreatest {θ : ℚ | Routable (cubeNet 6) cubeTranspose θ} 4 :=
  cubeModel.isGreatest_routable _ _ 1 cubeTranspose_dem cubeTransposeG cubeTransposeD cubeTransposeP
    cubeTransposeL 4 1 (by norm_num) one_pos (by decide) one_pos cubeTranspose_cons
    cubeTranspose_cap cubeTranspose_dual cubeTranspose_bound

/-- **Transpose on the hypercube: the optimum `4` is reached by a minimal flow** (detours add
nothing). -/
theorem cubeTranspose_minimal : ∃ F : Flow (cubeNet 6) cubeTranspose 4, F.Minimal cubeDist :=
  cubeModel.exists_minimal _ _ 1 cubeTranspose_dem cubeTransposeG cubeTransposeD 4 1 (by norm_num)
    one_pos (by decide) one_pos cubeTranspose_cons cubeTranspose_cap cubeTranspose_min

/-- **Transpose on the hypercube: the exact fluid optimum over minimal routings is also
`4`.** -/
theorem cubeTranspose_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (cubeNet 6) cubeTranspose θ, F.Minimal cubeDist} 4 :=
  isGreatest_minimal_of_routable cubeTranspose_opt cubeTranspose_minimal

/-- Bit reversal on the indices. -/
theorem cubeBitrev_dem (s d : Fin 6 → Bool) :
    cubeBitrev s d = (permN bitrevIdx (cubeModel.e s) (cubeModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index cubeModel.e cubeBitrevMap_idx s d

/-- **Bit reversal on the hypercube: the exact fluid optimum over all routings is `4`.** -/
theorem cubeBitrev_opt :
    IsGreatest {θ : ℚ | Routable (cubeNet 6) cubeBitrev θ} 4 :=
  cubeModel.isGreatest_routable _ _ 1 cubeBitrev_dem cubeBitrevG cubeBitrevD cubeBitrevP cubeBitrevL
    4 1 (by norm_num) one_pos (by decide) one_pos cubeBitrev_cons cubeBitrev_cap cubeBitrev_dual
    cubeBitrev_bound

/-- **Bit reversal on the hypercube: the optimum `4` is reached by a minimal flow** (detours add
nothing). -/
theorem cubeBitrev_minimal : ∃ F : Flow (cubeNet 6) cubeBitrev 4, F.Minimal cubeDist :=
  cubeModel.exists_minimal _ _ 1 cubeBitrev_dem cubeBitrevG cubeBitrevD 4 1 (by norm_num) one_pos
    (by decide) one_pos cubeBitrev_cons cubeBitrev_cap cubeBitrev_min

/-- **Bit reversal on the hypercube: the exact fluid optimum over minimal routings is also
`4`.** -/
theorem cubeBitrev_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (cubeNet 6) cubeBitrev θ, F.Minimal cubeDist} 4 :=
  isGreatest_minimal_of_routable cubeBitrev_opt cubeBitrev_minimal

/-- Bit complement on the indices. -/
theorem cubeBitcomp_dem (s d : Fin 6 → Bool) :
    cubeBitcomp s d = (permN bitcompIdx (cubeModel.e s) (cubeModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index cubeModel.e cubeBitcompMap_idx s d

/-- **Bit complement on the hypercube: the exact fluid optimum over all routings is `2`.** -/
theorem cubeBitcomp_opt :
    IsGreatest {θ : ℚ | Routable (cubeNet 6) cubeBitcomp θ} 2 :=
  cubeModel.isGreatest_routable _ _ 1 cubeBitcomp_dem cubeBitcompG cubeBitcompD cubeBitcompP
    cubeBitcompL 2 1 (by norm_num) one_pos (by decide) one_pos cubeBitcomp_cons cubeBitcomp_cap
    cubeBitcomp_dual cubeBitcomp_bound

/-- **Bit complement on the hypercube: the optimum `2` is reached by a minimal flow** (detours add
nothing). -/
theorem cubeBitcomp_minimal : ∃ F : Flow (cubeNet 6) cubeBitcomp 2, F.Minimal cubeDist :=
  cubeModel.exists_minimal _ _ 1 cubeBitcomp_dem cubeBitcompG cubeBitcompD 2 1 (by norm_num) one_pos
    (by decide) one_pos cubeBitcomp_cons cubeBitcomp_cap cubeBitcomp_min

/-- **Bit complement on the hypercube: the exact fluid optimum over minimal routings is also
`2`.** -/
theorem cubeBitcomp_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (cubeNet 6) cubeBitcomp θ, F.Minimal cubeDist} 2 :=
  isGreatest_minimal_of_routable cubeBitcomp_opt cubeBitcomp_minimal

/-- Tornado on the indices. -/
theorem cubeTornado_dem (s d : Fin 6 → Bool) :
    cubeTornado s d = (permN tornadoIdx (cubeModel.e s) (cubeModel.e d) : ℚ) / (1 : ℕ) :=
  permDem_index cubeModel.e cubeTornadoMap_idx s d

/-- **Tornado on the hypercube: the exact fluid optimum over all routings is `2`.** -/
theorem cubeTornado_opt :
    IsGreatest {θ : ℚ | Routable (cubeNet 6) cubeTornado θ} 2 :=
  cubeModel.isGreatest_routable _ _ 1 cubeTornado_dem cubeTornadoG cubeTornadoD cubeTornadoP
    cubeTornadoL 2 1 (by norm_num) one_pos (by decide) one_pos cubeTornado_cons cubeTornado_cap
    cubeTornado_dual cubeTornado_bound

/-- **Tornado on the hypercube: the optimum `2` is reached by a minimal flow** (detours add
nothing). -/
theorem cubeTornado_minimal : ∃ F : Flow (cubeNet 6) cubeTornado 2, F.Minimal cubeDist :=
  cubeModel.exists_minimal _ _ 1 cubeTornado_dem cubeTornadoG cubeTornadoD 2 1 (by norm_num) one_pos
    (by decide) one_pos cubeTornado_cons cubeTornado_cap cubeTornado_min

/-- **Tornado on the hypercube: the exact fluid optimum over minimal routings is also
`2`.** -/
theorem cubeTornado_minimal_opt :
    IsGreatest {θ : ℚ | ∃ F : Flow (cubeNet 6) cubeTornado θ, F.Minimal cubeDist} 2 :=
  isGreatest_minimal_of_routable cubeTornado_opt cubeTornado_minimal

end Fluid

end AsyncLean
