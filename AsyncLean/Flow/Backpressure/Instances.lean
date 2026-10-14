/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure.Buffers
import AsyncLean.Flow.Backpressure.Bursty
import AsyncLean.Flow.Backpressure.Converse
import AsyncLean.Flow.Backpressure.Scheduler

/-!
# Backpressure, part 7: the mesh, the torus and the hypercube

With `m` connections per link and uniform traffic, backpressure is stable at every load below `m`
times the fluid optimum and no scheduler is stable above it (`mesh_backpressure`,
`torus_backpressure`, `cube_backpressure`); such runs exist (`mesh_backpressure_exists`); finite
buffers suffice (`mesh_buffer`); whole packets with bursty arrivals are stable
(`mesh_backpressure_packets`).
-/

namespace AsyncLean

namespace Fluid

open Finset

/-! ### Instances: the mesh, the torus and the hypercube with `m` connections per link -/

section Instances

/-- Every pair of a grid shares in uniform traffic. -/
theorem uniform_props {k : ℕ} (hk : 2 ≤ k) :
    (∀ v d, 0 ≤ uniform k v d) ∧ ∀ v d, v ≠ d → 1 / ((k : ℚ) ^ 2 - 1) ≤ uniform k v d := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  refine ⟨fun v d => ?_, fun v d hvd => ?_⟩
  · unfold uniform; split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one hK.le
  · unfold uniform; rw [ite_eq_right hvd]

/-- **Backpressure on the mesh with `m` connections per link** (even `k ≥ 2`, uniform
traffic).  Let `θ = m · 8 (k² - 1) / k³`, the fluid optimum (`mesh_copies_uniform`).  A
backpressure run is stable under every load `ρ < θ`; no run of any scheduler keeps its backlog
bounded under a load `ρ > θ`. -/
theorem mesh_backpressure (k : ℕ) (hk : 2 ≤ k) (he : Even k) {m : ℕ} (hm : 0 < m)
    (r : Run ((meshNet k).copies m)) {ρ : ℚ} :
    (r.Backpressure → 0 ≤ ρ → ρ < m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) →
        (∀ t v d, v ≠ d → r.a t v d ≤ ρ * uniform k v d) → r.Stable) ∧
      ((∀ t v d, v ≠ d → r.a t v d = ρ * uniform k v d) → r.BoundedBacklog →
        ρ ≤ m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3)) := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  obtain ⟨hunn, hunc⟩ := uniform_props hk
  have hR := (mesh_routable k hk).copies m
  refine ⟨fun hr hρ hρθ harr => r.backpressure_optimal hr hR hR hunn hunn
    (div_pos one_pos hK) hunc (mul_pos hm' (div_pos (by linarith) (by positivity))) hρ hρθ harr,
    fun harr hb => ?_⟩
  have h := r.cut_bound harr hb (fun u : Fin k × Fin k => 2 * (u.1 : ℕ) < k)
  beta_reduce at h
  have e : ∀ u v : Fin k × Fin k,
      (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then ((meshNet k).copies m).cap u v else 0) =
        m * (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then (meshNet k).cap u v else 0) :=
    fun u v => by split_ifs <;> simp
  simp only [e, ← mul_sum] at h
  set D := ∑ s : Fin k × Fin k, ∑ d : Fin k × Fin k,
    (if 2 * (s.1 : ℕ) < k ∧ ¬ 2 * (d.1 : ℕ) < k then uniform k s d else 0)
  set Cc := ∑ u : Fin k × Fin k, ∑ v : Fin k × Fin k,
    (if 2 * (u.1 : ℕ) < k ∧ ¬ 2 * (v.1 : ℕ) < k then (meshNet k).cap u v else 0)
  have key : ρ / m * D ≤ Cc := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hm']; linarith
  have := mesh_upper_of_cut k hk he key
  rw [div_le_iff₀ hm'] at this
  linarith

/-- The hop distance of the torus. -/
theorem torus_isHopPotential (k : ℕ) : IsHopPotential (torusNet k) torusDist :=
  ⟨fun d => by rw [torusDist_eq]; simp only [Nat.cast_eq_zero]; exact (torusHops_eq_zero d d).2 rfl,
    fun u v d hc => by
      have h := torusHops_le_of_cap hc d
      have : ((torusHops u d : ℕ) : ℚ) ≤ (torusHops v d : ℕ) + 1 := by exact_mod_cast h
      rw [torusDist_eq]; linarith⟩

/-- **Backpressure on the torus with `m` connections per link** (`k ≥ 3`, uniform traffic).
Let `θ` be `m` times `torus_uniform_opt`.  A backpressure run is stable under every load
`ρ < θ`; no run of any scheduler keeps its backlog bounded under a load `ρ > θ`. -/
theorem torus_backpressure (k : ℕ) (hk : 3 ≤ k) {m : ℕ} (hm : 0 < m)
    (r : Run ((torusNet k).copies m)) {ρ : ℚ} :
    (r.Backpressure → 0 ≤ ρ →
        ρ < m * (if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / (k : ℚ)) →
        (∀ t v d, v ≠ d → r.a t v d ≤ ρ * uniform k v d) → r.Stable) ∧
      ((∀ t v d, v ≠ d → r.a t v d = ρ * uniform k v d) → r.BoundedBacklog →
        ρ ≤ m * (if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / (k : ℚ))) := by
  have hk' : (3 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  obtain ⟨hunn, hunc⟩ := uniform_props (k := k) (by omega)
  have hopt := (torus_uniform_opt k hk).1.1
  have hR := hopt.copies m
  have hθ : 0 < (if Even k then 16 * ((k : ℚ) ^ 2 - 1) / k ^ 3 else 16 / (k : ℚ)) := by
    split_ifs
    · exact div_pos (by linarith) (by positivity)
    · exact div_pos (by norm_num) (by linarith)
  refine ⟨fun hr hρ hρθ harr => r.backpressure_optimal hr hR hR hunn hunn
    (div_pos one_pos hK) hunc (mul_pos hm' hθ) hρ hρθ harr, fun harr hb => ?_⟩
  have hD : 0 < hopDemand (uniform k) torusDist := by
    rw [torus_hop_uniform]
    exact div_pos (mul_pos (by positivity) (ringTotal_pos (by omega))) hK
  exact r.copies_hop_bound harr hb (torus_isHopPotential k)
    (fun u v => by rw [torusDist_eq]; positivity) hD
    (by rw [torus_sum_cap (by omega)]; exact torus_uniform_hop k hk)

/-- The hop distance of the hypercube. -/
theorem cube_isHopPotential (n : ℕ) : IsHopPotential (cubeNet n) cubeDist :=
  ⟨fun d => by rw [cubeDist_eq]; simp only [Nat.cast_eq_zero]; exact (cubeHops_eq_zero d d).2 rfl,
    fun u v d hc => by
      have h := cubeHops_le_of_cap hc d
      have : ((cubeHops u d : ℕ) : ℚ) ≤ (cubeHops v d : ℕ) + 1 := by exact_mod_cast h
      rw [cubeDist_eq]; linarith⟩

/-- **Backpressure on the `n`-cube with `m` connections per link** (`n ≥ 1`, uniform traffic).
Let `θ = m · 4 (2ⁿ - 1) / 2ⁿ` (`cube_uniform_opt`).  A backpressure run is stable under every
load `ρ < θ`; no run of any scheduler keeps its backlog bounded under a load `ρ > θ`. -/
theorem cube_backpressure (n : ℕ) (hn : 1 ≤ n) {m : ℕ} (hm : 0 < m)
    (r : Run ((cubeNet n).copies m)) {ρ : ℚ} :
    (r.Backpressure → 0 ≤ ρ → ρ < m * (4 * (2 ^ n - 1) / 2 ^ n) →
        (∀ t v d, v ≠ d → r.a t v d ≤ ρ * cubeUniform n v d) → r.Stable) ∧
      ((∀ t v d, v ≠ d → r.a t v d = ρ * cubeUniform n v d) → r.BoundedBacklog →
        ρ ≤ m * (4 * (2 ^ n - 1) / 2 ^ n)) := by
  have hP : (2 : ℚ) ≤ 2 ^ n := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hP1 : (0 : ℚ) < 2 ^ n - 1 := by linarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hunn : ∀ v d, 0 ≤ cubeUniform n v d := fun v d => by
    unfold cubeUniform; split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one hP1.le
  have hunc : ∀ v d, v ≠ d → 1 / ((2 : ℚ) ^ n - 1) ≤ cubeUniform n v d := fun v d hvd => by
    unfold cubeUniform; rw [ite_eq_right hvd]
  have hR := (cube_uniform_opt n hn).1.1.copies m
  refine ⟨fun hr hρ hρθ harr => r.backpressure_optimal hr hR hR hunn hunn
    (div_pos one_pos hP1) hunc (mul_pos hm' (div_pos (by linarith) (by positivity))) hρ hρθ harr,
    fun harr hb => ?_⟩
  have hD : 0 < hopDemand (cubeUniform n) cubeDist := by
    rw [cube_hop_uniform]
    have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
    exact div_pos (by positivity) (by positivity)
  exact r.copies_hop_bound harr hb (cube_isHopPotential n)
    (fun u v => by rw [cubeDist_eq]; positivity) hD
    (by rw [cube_sum_cap]; exact cube_uniform_hop n hn)

theorem meshAdj_symm {k : ℕ} (u v : Fin k × Fin k) : MeshAdj u v ↔ MeshAdj v u := by
  simp only [MeshAdj, LineAdj, Fin.ext_iff]; omega

/-- A vertex of the mesh has at most four neighbours: its capacity out is at most `8`. -/
theorem mesh_out_cap (k : ℕ) (v : Fin k × Fin k) : ∑ w, (meshNet k).cap v w ≤ 8 := by
  have one : ∀ (P : Fin k × Fin k → Prop) [DecidablePred P], (∀ a b, P a → P b → a = b) →
      ∑ w, (if P w then (1 : ℚ) else 0) ≤ 1 := by
    intro P _ hP
    rw [sum_boole]
    exact_mod_cast card_le_one.2 fun a ha b hb =>
      hP a b (by simpa using ha) (by simpa using hb)
  have hcap : ∀ w : Fin k × Fin k, (meshNet k).cap v w ≤ 2 *
      ((if (w.2 : ℕ) = v.2 ∧ (v.1 : ℕ) + 1 = w.1 then (1 : ℚ) else 0) +
        (if (w.2 : ℕ) = v.2 ∧ (w.1 : ℕ) + 1 = v.1 then (1 : ℚ) else 0) +
        (if (w.1 : ℕ) = v.1 ∧ (v.2 : ℕ) + 1 = w.2 then (1 : ℚ) else 0) +
        (if (w.1 : ℕ) = v.1 ∧ (w.2 : ℕ) + 1 = v.2 then (1 : ℚ) else 0)) := by
    intro w
    show (if MeshAdj v w then (2 : ℚ) else 0) ≤ _
    by_cases h : MeshAdj v w
    · rw [ite_eq_left h]
      simp only [MeshAdj, LineAdj, Fin.ext_iff] at h
      split_ifs <;> first | (exfalso; omega) | norm_num
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  calc ∑ w, (meshNet k).cap v w ≤ ∑ w : Fin k × Fin k, 2 *
        ((if (w.2 : ℕ) = v.2 ∧ (v.1 : ℕ) + 1 = w.1 then (1 : ℚ) else 0) +
          (if (w.2 : ℕ) = v.2 ∧ (w.1 : ℕ) + 1 = v.1 then (1 : ℚ) else 0) +
          (if (w.1 : ℕ) = v.1 ∧ (v.2 : ℕ) + 1 = w.2 then (1 : ℚ) else 0) +
          (if (w.1 : ℕ) = v.1 ∧ (w.2 : ℕ) + 1 = v.2 then (1 : ℚ) else 0)) :=
        sum_le_sum fun w _ => hcap w
    _ ≤ 2 * (1 + 1 + 1 + 1) := by
        rw [← mul_sum]
        simp only [sum_add_distrib]
        have h1 := one (fun w => (w.2 : ℕ) = v.2 ∧ (v.1 : ℕ) + 1 = w.1)
          fun a b ⟨h1, h2⟩ ⟨h3, h4⟩ => Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
        have h2 := one (fun w => (w.2 : ℕ) = v.2 ∧ (w.1 : ℕ) + 1 = v.1)
          fun a b ⟨h1, h2⟩ ⟨h3, h4⟩ => Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
        have h3 := one (fun w => (w.1 : ℕ) = v.1 ∧ (v.2 : ℕ) + 1 = w.2)
          fun a b ⟨h1, h2⟩ ⟨h3, h4⟩ => Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
        have h4 := one (fun w => (w.1 : ℕ) = v.1 ∧ (w.2 : ℕ) + 1 = v.2)
          fun a b ⟨h1, h2⟩ ⟨h3, h4⟩ => Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
        linarith
    _ = 8 := by norm_num

/-- The capacity into a vertex of the mesh is at most `8`. -/
theorem mesh_in_cap (k : ℕ) (v : Fin k × Fin k) : ∑ u, (meshNet k).cap u v ≤ 8 := by
  have e : ∀ u, (meshNet k).cap u v = (meshNet k).cap v u := fun u => by
    show (if MeshAdj u v then (2 : ℚ) else 0) = if MeshAdj v u then 2 else 0
    rw [if_congr (meshAdj_symm u v) rfl rfl]
  simp only [e]
  exact mesh_out_cap k v

/-- **Buffers for backpressure on the mesh** with `m` connections per link (`k ≥ 2`, uniform
traffic).  Let `θ = m · 8 (k² - 1) / k³` (the fluid optimum for even `k`).  Started empty, under
any load at most `(1 - δ) θ` (`0 < δ ≤ 1`) a backpressure run never holds more than
`b = 145 m k⁷ / (16 δ) + m` packets in any per-destination queue, and it delivers everything that
arrives except at most `k⁴ b`.  The buffer is linear in the number of connections and in
`1 / δ`; the constant is that of the drift argument, far above what simulation needs. -/
theorem mesh_buffer (k : ℕ) (hk : 2 ≤ k) {m : ℕ} (hm : 0 < m) {δ : ℚ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (r : Run ((meshNet k).copies m)) (hr : r.Backpressure)
    (h0 : ∀ v d, r.Q 0 v d = 0)
    (harr : ∀ t v d, v ≠ d →
      r.a t v d ≤ (1 - δ) * (m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3)) * uniform k v d) :
    r.FitsIn (145 * m * k ^ 7 / (16 * δ) + m) ∧
      ∀ t, ∑ s ∈ range t, r.arrived s - (k : ℚ) ^ 4 * (145 * m * k ^ 7 / (16 * δ) + m) ≤
        ∑ s ∈ range t, r.delivered s := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hk3 : (8 : ℚ) ≤ (k : ℚ) ^ 3 := by nlinarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hk3' : (0 : ℚ) < (k : ℚ) ^ 3 := by linarith
  set θ := (m : ℚ) * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]; exact mul_nonneg hm'.le (div_nonneg (by linarith) hk3'.le)
  obtain ⟨F⟩ := (mesh_routable k hk).copies m
  have F' := F.normalize
  set dem := fun v d => θ * uniform k v d with hdemdef
  -- the demand of a pair
  have hθu : ∀ v d : Fin k × Fin k, v ≠ d → θ * uniform k v d = 8 * m / k ^ 3 := fun v d hvd => by
    unfold uniform; rw [ite_eq_right hvd, hθdef]
    rw [show (m : ℚ) * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) * (1 / ((k : ℚ) ^ 2 - 1)) =
        8 * m / k ^ 3 * (((k : ℚ) ^ 2 - 1) * (1 / ((k : ℚ) ^ 2 - 1))) by ring,
      mul_one_div_cancel hK.ne', mul_one]
  have hdem0 : ∀ v d, 0 ≤ dem v d := fun v d => by
    simp only [hdemdef]
    exact mul_nonneg hθ0 ((uniform_props hk).1 v d)
  have hdemm : ∀ v d, dem v d ≤ m := fun v d => by
    simp only [hdemdef]
    by_cases hvd : v = d
    · subst hvd; simp [uniform]
    · rw [hθu v d hvd, div_le_iff₀ hk3']; nlinarith
  -- the slack
  set ε := 8 * m * δ / (k : ℚ) ^ 3 with hεdef
  have hε : 0 < ε := div_pos (by positivity) hk3'
  have harr' : ∀ t v d, v ≠ d → r.a t v d + ε ≤ dem v d := fun t v d hvd => by
    have h := harr t v d hvd
    simp only [hdemdef]
    rw [hθu v d hvd]
    rw [show (1 - δ) * θ * uniform k v d = (1 - δ) * (θ * uniform k v d) by ring,
      hθu v d hvd] at h
    rw [hεdef]
    have : (1 - δ) * (8 * m / k ^ 3) + 8 * m * δ / k ^ 3 = 8 * m / (k : ℚ) ^ 3 := by
      ring
    linarith
  obtain ⟨hfit, hdel⟩ := r.backpressure_fitsIn hr F' hdem0 hε harr' h0
  -- the drift constant
  have hout : ∀ v, ∑ w, ((meshNet k).copies m).cap v w ≤ 8 * m := fun v => by
    simp only [Net.copies_cap, ← mul_sum]
    nlinarith [mesh_out_cap k v]
  have hin : ∀ v, ∑ u, ((meshNet k).copies m).cap u v ≤ 8 * m := fun v => by
    simp only [Net.copies_cap, ← mul_sum]
    nlinarith [mesh_in_cap k v]
  have hB : Run.driftConst ((meshNet k).copies m) dem ≤ 145 * (m : ℚ) ^ 2 * (k : ℚ) ^ 4 := by
    calc Run.driftConst ((meshNet k).copies m) dem ≤
          ∑ _d : Fin k × Fin k, ∑ _v : Fin k × Fin k, (145 * (m : ℚ) ^ 2) := by
          refine sum_le_sum fun d _ => sum_le_sum fun v _ => ?_
          have h1 : 0 ≤ ∑ w, ((meshNet k).copies m).cap v w :=
            sum_nonneg fun w _ => ((meshNet k).copies m).cap_nonneg v w
          have h2 : 0 ≤ ∑ u, ((meshNet k).copies m).cap u v :=
            sum_nonneg fun u _ => ((meshNet k).copies m).cap_nonneg u v
          have h3 := hout v
          have h4 := hin v
          have h5 := hdemm v d
          have h6 := hdem0 v d
          nlinarith
      _ = 145 * (m : ℚ) ^ 2 * (k : ℚ) ^ 4 := by
          simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- the buffer
  have hb : Run.driftConst ((meshNet k).copies m) dem / (2 * ε) + ε ≤
      145 * m * k ^ 7 / (16 * δ) + m := by
    have e1 : 145 * (m : ℚ) ^ 2 * k ^ 4 / (2 * ε) = 145 * m * k ^ 7 / (16 * δ) := by
      rw [hεdef, show (2 : ℚ) * (8 * m * δ / k ^ 3) = 16 * m * δ / k ^ 3 by ring,
        div_div_eq_mul_div, div_eq_div_iff (mul_pos (mul_pos (by norm_num) hm') hδ).ne'
          (mul_pos (by norm_num) hδ).ne']
      ring
    have e2 : ε ≤ m := by
      rw [hεdef, div_le_iff₀ hk3']; nlinarith
    have e3 := div_le_div_of_nonneg_right hB (show (0 : ℚ) ≤ 2 * ε by linarith)
    linarith
  refine ⟨fun t v d => (hfit t v d).trans hb, fun t => ?_⟩
  have h := hdel t
  have hc : ((Fintype.card (Fin k × Fin k) : ℕ) : ℚ) ^ 2 = (k : ℚ) ^ 4 := by
    simp only [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
  rw [hc] at h
  have := mul_le_mul_of_nonneg_left hb (show (0 : ℚ) ≤ (k : ℚ) ^ 4 by positivity)
  linarith

/-- **Whole packets on the mesh with `m` connections per link** (`k ≥ 2`, uniform traffic).
Let `θ = m · 8 (k² - 1) / k³`.  For every arrival sequence of whole packets at most `A` per
queue and slot, within a leaky bucket of rate `ρ < θ` times the uniform traffic and burst `σ`
(over every window of `W` slots at most `W ρ / (k² - 1) + σ` packets from `v` for `d`), the
backpressure run with sequential sends moves whole packets only, keeps its backlog bounded and
delivers everything that arrives, up to a constant. -/
theorem mesh_backpressure_packets (k : ℕ) (hk : 2 ≤ k) {m : ℕ} (hm : 0 < m)
    (a : ℕ → Fin k × Fin k → Fin k × Fin k → ℚ) (ha : ∀ t v d, 0 ≤ a t v d)
    (had : ∀ t d, a t d d = 0) (haI : ∀ t v d, IsInt (a t v d)) {A : ℚ}
    (hA : ∀ t v d, a t v d ≤ A) {ρ σ : ℚ} (hρθ : ρ < m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3))
    (hσ : 0 ≤ σ)
    (hburst : ∀ t W v d, v ≠ d → ∑ s ∈ range W, a (t + s) v d ≤ W * ρ * uniform k v d + σ) :
    ∃ r : Run ((meshNet k).copies m), r.Backpressure ∧ (∀ t v d, r.a t v d = a t v d) ∧
      (∀ t, (∀ v d, IsInt (r.Q t v d)) ∧ ∀ d u v, IsInt (r.x t d u v)) ∧ r.Stable := by
  have : Nonempty (Fin k × Fin k) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  set θ := (m : ℚ) * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3) with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]; exact mul_nonneg hm'.le (div_nonneg (by linarith) (by positivity))
  obtain ⟨hunn, -⟩ := uniform_props hk
  have hA0 : 0 ≤ A := (ha 0 (⟨0, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨0, by omega⟩)).trans
    (hA _ _ _)
  let r := Run.ofArrivalsSeq ((meshNet k).copies m) (a := a) (Q₀ := fun _ _ => 0) ha had
    (fun _ _ => le_rfl) (fun _ => rfl)
  have hr := Run.ofArrivalsSeq_backpressure ((meshNet k).copies m) (a := a) (Q₀ := fun _ _ => 0)
    ha had (fun _ _ => le_rfl) (fun _ => rfl)
  have hint := Run.ofArrivalsSeq_int ((meshNet k).copies m) (a := a) (Q₀ := fun _ _ => 0) ha had
    (fun _ _ => le_rfl) (fun _ => rfl) (fun u v => by
      show IsInt ((m : ℚ) * (if MeshAdj u v then 2 else 0))
      split_ifs
      · exact ⟨2 * m, by push_cast; ring⟩
      · exact ⟨0, by simp⟩) haI (fun _ _ => IsInt.zero)
  refine ⟨r, hr, fun _ _ _ => rfl, hint, ?_⟩
  obtain ⟨F⟩ := (mesh_routable k hk).copies m
  have hu : ∀ v d : Fin k × Fin k, v ≠ d → uniform k v d = 1 / ((k : ℚ) ^ 2 - 1) :=
    fun v d hvd => by unfold uniform; rw [ite_eq_right hvd]
  refine r.backpressure_stable_bursty hr (dem := fun v d => θ * uniform k v d) ⟨F.normalize⟩
    (fun v d => mul_nonneg hθ0 (hunn v d)) (D := θ / ((k : ℚ) ^ 2 - 1))
    (div_nonneg hθ0 hK.le) (fun v d => ?_) hA0 hA (ε := (θ - ρ) / ((k : ℚ) ^ 2 - 1))
    (div_pos (by linarith) hK) hσ (fun t W v d hvd => ?_)
  · by_cases hvd : v = d
    · subst hvd; simp only [uniform, ite_true, mul_zero]; exact div_nonneg hθ0 hK.le
    · rw [hu v d hvd, mul_one_div]
  · have h := hburst t W v d hvd
    rw [hu v d hvd] at h
    show ∑ s ∈ range W, a (t + s) v d ≤ W * (θ * uniform k v d - (θ - ρ) / ((k : ℚ) ^ 2 - 1)) + σ
    rw [hu v d hvd]
    have e : (W : ℚ) * (θ * (1 / ((k : ℚ) ^ 2 - 1)) - (θ - ρ) / ((k : ℚ) ^ 2 - 1)) =
        W * ρ * (1 / ((k : ℚ) ^ 2 - 1)) := by ring
    linarith

/-- **Not vacuous**: on the mesh with `m` connections per link, for every load
`0 ≤ ρ < m · 8 (k² - 1) / k³` there is a backpressure run, from the empty network, with
arrivals exactly `ρ` times the uniform traffic in every slot, and it is stable. -/
theorem mesh_backpressure_exists (k : ℕ) (hk : 2 ≤ k) (he : Even k) {m : ℕ} (hm : 0 < m)
    {ρ : ℚ} (hρ : 0 ≤ ρ) (hρθ : ρ < m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3)) :
    ∃ r : Run ((meshNet k).copies m), r.Backpressure ∧
      (∀ t v d, r.a t v d = ρ * uniform k v d) ∧ r.Stable := by
  have : Nonempty (Fin k × Fin k) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨hunn, -⟩ := uniform_props hk
  let r := Run.ofArrivals ((meshNet k).copies m) (a := fun _ v d => ρ * uniform k v d)
    (Q₀ := fun _ _ => 0) (fun _ v d => mul_nonneg hρ (hunn v d))
    (fun _ d => by simp [uniform]) (fun _ _ => le_rfl) (fun _ => rfl)
  have hr := Run.ofArrivals_backpressure ((meshNet k).copies m)
    (a := fun _ v d => ρ * uniform k v d) (Q₀ := fun _ _ => 0)
    (fun _ v d => mul_nonneg hρ (hunn v d)) (fun _ d => by simp [uniform]) (fun _ _ => le_rfl)
    (fun _ => rfl)
  exact ⟨r, hr, fun _ _ _ => rfl,
    (mesh_backpressure k hk he hm r).1 hr hρ hρθ fun _ _ _ _ => le_rfl⟩

end Instances

end Fluid

end AsyncLean
