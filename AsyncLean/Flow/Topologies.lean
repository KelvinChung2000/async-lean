/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.MeshWire

/-!
# The torus and the hypercube in the fluid model

The two networks the mesh is most often compared with, with the same link capacity as `meshNet`
(`2` in each direction: two lanes of capacity `1`), and their hop distances.

* `torusNet k` : the `k × k` torus, the mesh with wrap-around links in every row and column;
  `torusDist` its hop distance (the ring distance in each coordinate).
* `cubeNet n` : the `n`-dimensional hypercube on `Fin n → Bool`, neighbours differing in exactly
  one coordinate; `cubeDist` its hop distance (the Hamming distance).
-/

namespace AsyncLean

namespace Fluid

open Finset

/-- Two positions on a ring of length `k` are neighbours. -/
def RingAdj {k : ℕ} (a b : Fin k) : Prop := ((a : ℕ) + 1) % k = b ∨ ((b : ℕ) + 1) % k = a

instance {k : ℕ} : DecidableRel (@RingAdj k) := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Two vertices of the `k × k` torus are neighbours: same row and neighbouring columns on the
ring, or same column and neighbouring rows on the ring. -/
def TorusAdj {k : ℕ} (u v : Fin k × Fin k) : Prop :=
  (u.2 = v.2 ∧ RingAdj u.1 v.1) ∨ (u.1 = v.1 ∧ RingAdj u.2 v.2)

instance {k : ℕ} : DecidableRel (@TorusAdj k) := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- **The `k × k` torus**: capacity `2` in both directions between torus neighbours. -/
def torusNet (k : ℕ) : Net (Fin k × Fin k) where
  cap u v := if TorusAdj u v then 2 else 0
  cap_nonneg u v := by by_cases h : TorusAdj u v <;> simp [h]

/-- The distance of two positions on a ring of length `k`. -/
def ringDist {k : ℕ} (a b : Fin k) : ℕ := min (((a : ℕ) + k - b) % k) (((b : ℕ) + k - a) % k)

/-- The hop distance of the torus. -/
def torusDist {k : ℕ} (u v : Fin k × Fin k) : ℚ := (ringDist u.1 v.1 + ringDist u.2 v.2 : ℕ)

/-- The coordinates in which two vertices of the hypercube differ. -/
def cubeDiff {n : ℕ} (u v : Fin n → Bool) : Finset (Fin n) := univ.filter fun i => u i ≠ v i

/-- Two vertices of the hypercube are neighbours: they differ in exactly one coordinate. -/
def CubeAdj {n : ℕ} (u v : Fin n → Bool) : Prop := (cubeDiff u v).card = 1

instance {n : ℕ} : DecidableRel (@CubeAdj n) := fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- **The `n`-dimensional hypercube**: capacity `2` in both directions between neighbours. -/
def cubeNet (n : ℕ) : Net (Fin n → Bool) where
  cap u v := if CubeAdj u v then 2 else 0
  cap_nonneg u v := by by_cases h : CubeAdj u v <;> simp [h]

/-- The hop distance of the hypercube: the number of coordinates in which the vertices differ. -/
def cubeDist {n : ℕ} (u v : Fin n → Bool) : ℚ := ((cubeDiff u v).card : ℕ)

end Fluid

end AsyncLean
