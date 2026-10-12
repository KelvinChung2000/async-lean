/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Symmetric.Cube

/-!
# Symmetric networks: minimal routing is optimal for uniform traffic

This module gathers 3 parts:

1. `Symmetric.General` — minimal routing on arc-transitive networks;
2. `Symmetric.Torus` — the torus;
3. `Symmetric.Cube` — the hypercube and worst-case traffic.

On a network whose automorphisms act transitively on the links (the torus, the hypercube),
traffic invariant under the automorphisms is routed optimally by a **minimal** flow (no
detours), and the optimum is the total capacity divided by the traffic times the hop distance.

**General theory** (any network `N`, traffic `dem`, distance `dist`):

* `IsHopDistance N dist` : `dist d d = 0` and `dist u d - dist v d ≤ 1` on every link of positive
  capacity; `hopDemand dem dist = ∑ s d, dem s d * dist s d`.
* `hop_bound` : any routing has `θ * ∑ dem * dist ≤ ∑ cap` (the potential bound, length `1`).
* `minimal_load_total` : a flow in which every used link brings its commodity one hop closer
  (`Flow.Minimal.drop_one`: true of every minimal flow for a distance with natural values) has
  total load exactly `θ * ∑ dem * dist` (telescoping).
* `balanced_opt` : **a geodesic flow loading every link of positive capacity to exactly its
  capacity is optimal** (`IsGreatest`), with value `∑ cap / ∑ dem * dist`.
* `FreeFlow`, `exists_geodesic_freeFlow` : if every `v ≠ d` has a neighbour one hop closer to `d`,
  greedy walks give a geodesic flow ignoring capacities.
* `IsAut`, `ArcTransitive` : automorphisms of `(N, dem, dist)` and transitivity on the links.
  `symmetric_balanced` : averaging a geodesic free flow over all automorphisms loads every link
  equally, so scaled to `∑ cap / ∑ dem * dist` it saturates every link.
* `symmetric_opt` : **on an arc-transitive network, minimal routing is optimal**: the optimum is
  `∑ cap / ∑ dem * dist`, reached by a minimal flow.

**The torus** `torusNet k` (`torus_symmetric_opt`, for every permutation-invariant traffic): its
automorphisms (rotations `torusShift`, the reflection `torusNeg`, the exchange `torusSwap`) are
transitive on the links (`torus_arcTransitive`); `torus_sum_cap`, `torus_sum_dist` (via
`ringTotal`: `m²` for `k = 2m`, `m (m + 1)` for `k = 2m + 1`).

* `torus_uniform_opt` : uniform traffic (`uniform k`, `k ≥ 3`): the optimum is `16 (k² - 1) / k³`
  for even `k` and `16 / k` for odd `k`, reached by a minimal flow; `63/32` for `k = 8`
  (`torus_uniform_opt_eight`); `3` for `k = 2` (`torus_uniform_opt_two`: the two links between
  the positions of a ring of length `2` coincide).
* `torus_self_opt` : uniform traffic including self (`1 / k²` for every pair): `16 / k` for even
  `k ≥ 4`, `16 k / (k² - 1)` for odd `k`; `torus_self_routable` : routable at `16 / k` for every
  `k ≥ 3`; `4` for `k = 2` (`torus_self_opt_two`).

**The hypercube** `cubeNet n` (`cube_symmetric_opt`): translations `cubeXor` and permutations of
the coordinates `cubePerm` (`cube_arcTransitive`); `cube_sum_cap = 2 n 2ⁿ`,
`cube_sum_dist = n 2ⁿ 2ⁿ / 2`.

* `cube_uniform_opt` : uniform traffic (`cubeUniform n`, `n ≥ 1`): the optimum is
  `4 (2ⁿ - 1) / 2ⁿ`, reached by a minimal flow; `63/16` for `n = 6` (`cube_uniform_opt_six`).
* `cube_self_opt`, `cube_self_routable` : uniform traffic including self (`1 / 2ⁿ`): the optimum
  is `4`.

**Worst case** (with `AsyncLean.Flow.Valiant`): `torus_worst_opt'` (even `k ≥ 4`: `8 / k`) and
`cube_worst_opt'` (`n ≥ 1`: `2`), unconditionally.

All results are over `ℚ`.
-/
