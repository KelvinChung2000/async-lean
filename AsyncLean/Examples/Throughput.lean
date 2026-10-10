/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.Lanes
import AsyncLean.Routing.Throughput
import AsyncLean.AxiomAudit

/-!
# Example: the throughput of the torus with `m` lanes, with packets

`torusLanes k m B` (`AsyncLean.Examples.Lanes`) is the `(k + 1) × (k + 1)` torus with `m`
connections per link, used as `m` lanes of the detour network.  With time
(`Network.TimedRun`: rounds in which every channel receives at most one packet):

* `torusLanes_ceiling` : **no timed run of the lane network, under any selection, sustains
  uniform traffic above `m` times the fluid optimum of one connection** (`torus_uniform_opt`);
* `torusLanes_timed` : **any timed run of one lane, run in all `m` lanes, is a timed run of the
  lane network injecting `m` times the packets**: whatever load one connection sustains, `m`
  connections sustain `m` times it;
* `torusLanes_delivered` : every timed run delivers all it injects but for the packets the
  network holds.

So the packet throughput of the lanes is exactly linear in `m`, up to the fluid optimum, which
it can never exceed.
-/

namespace AsyncLean.Examples

open Network Finset Fluid

/-- One step forward on the ring is adding one modulo the length. -/
theorem cycSucc_eq_iff {k : ℕ} (a b : Fin (k + 1)) :
    cycSucc a = b ↔ ((a : ℕ) + 1) % (k + 1) = b := by
  unfold cycSucc
  split_ifs with h
  · rw [Fin.ext_iff, h, Nat.mod_self]; simp
  · rw [Fin.ext_iff, Nat.mod_eq_of_lt (by omega)]

/-- One step back on the ring. -/
theorem cycPred_eq_iff {k : ℕ} (a b : Fin (k + 1)) :
    cycPred a = b ↔ ((b : ℕ) + 1) % (k + 1) = a := by
  have hb := b.isLt
  have ha := a.isLt
  unfold cycPred
  rcases Nat.lt_or_ge ((b : ℕ) + 1) (k + 1) with h | h
  · rw [Nat.mod_eq_of_lt h]
    split_ifs with h0
    · rw [Fin.ext_iff]; simp; omega
    · rw [Fin.ext_iff]; simp; omega
  · have : (b : ℕ) + 1 = k + 1 := by omega
    rw [this, Nat.mod_self]
    split_ifs with h0
    · rw [Fin.ext_iff]; simp; omega
    · rw [Fin.ext_iff]; simp; omega

/-- **The neighbours of the torus `GraphData` are those of the fluid torus.** -/
theorem torus_nbrs_iff (k : ℕ) (u v : TV k) : v ∈ (torus k).nbrs u ↔ TorusAdj u v := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  have e1 : (v1 = cycSucc u1) ↔ ((u1 : ℕ) + 1) % (k + 1) = v1 := by
    rw [eq_comm]; exact cycSucc_eq_iff _ _
  have e2 : (v1 = cycPred u1) ↔ ((v1 : ℕ) + 1) % (k + 1) = u1 := by
    rw [eq_comm]; exact cycPred_eq_iff _ _
  have e3 : (v2 = cycSucc u2) ↔ ((u2 : ℕ) + 1) % (k + 1) = v2 := by
    rw [eq_comm]; exact cycSucc_eq_iff _ _
  have e4 : (v2 = cycPred u2) ↔ ((v2 : ℕ) + 1) % (k + 1) = u2 := by
    rw [eq_comm]; exact cycPred_eq_iff _ _
  simp only [torus, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, TorusAdj, RingAdj,
    e1, e2, e3, e4]
  constructor
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h', h⟩ | ⟨h', h⟩)
    exacts [Or.inl ⟨h'.symm, Or.inl h⟩, Or.inl ⟨h'.symm, Or.inr h⟩, Or.inr ⟨h'.symm, Or.inl h⟩,
      Or.inr ⟨h'.symm, Or.inr h⟩]
  · rintro (⟨h', h | h⟩ | ⟨h', h | h⟩)
    exacts [Or.inl ⟨h, h'.symm⟩, Or.inr (Or.inl ⟨h, h'.symm⟩),
      Or.inr (Or.inr (Or.inl ⟨h'.symm, h⟩)), Or.inr (Or.inr (Or.inr ⟨h'.symm, h⟩))]


/-- The torus with `m` lanes, placed on the torus. -/
abbrev torusLanesPlacement (k m B : ℕ) : (torusLanes k m B).Placement (TV k) :=
  lanesPlacement (List.finRange m) ((torus k).detourPlacement B (torus k).anyDetour)

theorem torusLanesPlacement_fits (k m B : ℕ) : (torusLanesPlacement k m B).Fits :=
  lanesPlacement_fits _ ((torus k).detourPlacement_fits B _)

/-- **The fluid network of the torus with `m` lanes is `m` copies of the fluid torus.** -/
theorem torusLanesPlacement_cap (k m B : ℕ) (u v : TV k) :
    (torusLanesPlacement k m B).net.cap u v = m * (torusNet (k + 1)).cap u v := by
  rw [lanesPlacement_cap, Fintype.card_fin]
  unfold GraphData.detourPlacement
  rw [GraphData.placement_cap]
  by_cases h : TorusAdj u v
  · simp [torusNet, h, (torus_nbrs_iff k u v).2 h]
  · simp [torusNet, h, torus_nbrs_iff]

/-- **The packet ceiling of the torus with `m` lanes** (`k + 1 ≥ 3`): no timed run, under any
selection offering only permitted hops, sustains uniform traffic at more than `m` times the
fluid optimum of one connection (`torus_uniform_opt`). -/
theorem torusLanes_ceiling (k m B : ℕ) (hk : 2 ≤ k)
    {sel : Selection (Fin m × GChan (TV k)) (THdr k)}
    (hsub : ∀ f c p q, q ∈ sel f c p → q ∈ (torusLanes k m B).route c p)
    (R : (torusLanes k m B).TimedRun sel) {ρ K : ℚ}
    (hload : ∀ T s d, T * ρ * uniform (k + 1) s d - K ≤
      R.injected (torusLanesPlacement k m B) T s d) :
    ρ ≤ m * (if Even (k + 1) then 16 * (((k + 1 : ℕ) : ℚ) ^ 2 - 1) / ((k + 1 : ℕ) : ℚ) ^ 3
      else 16 / ((k + 1 : ℕ) : ℚ)) := by
  have hk3 : 3 ≤ k + 1 := by omega
  have hk' : (3 : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := by exact_mod_cast hk3
  have hK : (0 : ℚ) < ((k + 1 : ℕ) : ℚ) ^ 2 - 1 := by nlinarith
  have hD : 0 < hopDemand (uniform (k + 1)) torusDist := by
    rw [torus_hop_uniform]
    exact div_pos (mul_pos (by positivity) (ringTotal_pos (by omega))) hK
  have hhop : IsHopDistance (torusLanesPlacement k m B).net torusDist :=
    ⟨(torus_isHopDistance (k + 1)).1, fun u v d hc => (torus_isHopDistance (k + 1)).2 u v d (by
      rw [torusLanesPlacement_cap] at hc
      exact pos_of_mul_pos_right hc (Nat.cast_nonneg m))⟩
  have h := R.hop_ceiling (torusLanesPlacement k m B)
    ((torusLanesPlacement_fits k m B).respects hsub) hload hhop
    (fun u v => by rw [torusDist_eq]; positivity)
  simp only [torusLanesPlacement_cap, ← mul_sum] at h
  rw [torus_sum_cap (by omega), ← torus_uniform_hop (k + 1) hk3] at h
  have : ρ * hopDemand (uniform (k + 1)) torusDist ≤
      (m * (if Even (k + 1) then 16 * (((k + 1 : ℕ) : ℚ) ^ 2 - 1) / ((k + 1 : ℕ) : ℚ) ^ 3
        else 16 / ((k + 1 : ℕ) : ℚ))) * hopDemand (uniform (k + 1)) torusDist := by
    linarith
  exact le_of_mul_le_mul_right this hD

/-- **`m` lanes sustain `m` times the load of one**: any timed run of one lane (the detour
network on the torus) is run in all `m` lanes at once, round by round, as a timed run of the lane
network that injects, from every source for every destination, `m` times the packets. -/
theorem torusLanes_timed (k m B : ℕ)
    (R : ((torus k).detourNet B (torus k).anyDetour).TimedRun
      ((torus k).detourNet B (torus k).anyDetour).adaptive) :
    ∃ R' : (torusLanes k m B).TimedRun (torusLanes k m B).adaptive,
      ∀ T s d, R'.injected (torusLanesPlacement k m B) T s d =
        m * R.injected ((torus k).detourPlacement B (torus k).anyDetour) T s d := by
  refine ⟨lanesTimed (L := List.finRange m) (fun i _ => List.mem_finRange i)
    (List.nodup_finRange m) (fun _ => R), fun T s d => ?_⟩
  rw [lanesTimed_injected]
  simp

/-- **Linear scaling with packets**: if one lane sustains the load `ρ * dem`, the torus with
`m` lanes sustains `m ρ * dem`. -/
theorem torusLanes_sustains (k m B : ℕ)
    (R : ((torus k).detourNet B (torus k).anyDetour).TimedRun
      ((torus k).detourNet B (torus k).anyDetour).adaptive)
    {dem : TV k → TV k → ℚ} {ρ K : ℚ}
    (hload : ∀ T s d, T * ρ * dem s d - K ≤
      R.injected ((torus k).detourPlacement B (torus k).anyDetour) T s d) :
    ∃ R' : (torusLanes k m B).TimedRun (torusLanes k m B).adaptive,
      ∀ T s d, T * (m * ρ) * dem s d - m * K ≤ R'.injected (torusLanesPlacement k m B) T s d := by
  obtain ⟨R', hR'⟩ := torusLanes_timed k m B R
  refine ⟨R', fun T s d => ?_⟩
  rw [hR']
  push_cast
  have := mul_le_mul_of_nonneg_left (hload T s d) (Nat.cast_nonneg (α := ℚ) m)
  linarith

/-- Every timed run of the torus with `m` lanes delivers all it injects but for the packets the
network holds (at most its number of channels). -/
theorem torusLanes_delivered (k m B : ℕ) {sel : Selection (Fin m × GChan (TV k)) (THdr k)}
    (R : (torusLanes k m B).TimedRun sel) (T : ℕ) :
    (R.injectedAll T : ℤ) - Fintype.card (Fin m × GChan (TV k)) ≤ R.ejected T :=
  R.ejected_ge T

/-- **Backpressure-style hop choices are safe**: choosing, among the free permitted hops of the
torus with `m` lanes, those of largest score (any score: backlog differences, congestion
estimates) keeps the network deadlock and livelock free. -/
theorem torusLanes_scoreSel (k m B : ℕ)
    (score : Config (Fin m × GChan (TV k)) (THdr k) → Fin m × GChan (TV k) → THdr k →
      (Fin m × GChan (TV k)) × THdr k → ℚ) :
    (torusLanes k m B).DeadlockFreeWith ((torusLanes k m B).scoreSel score) ∧
      (torusLanes k m B).LivelockFreeWith ((torusLanes k m B).scoreSel score) :=
  (torusLanes_correct k m B).1.scoreSel score

/-- The same for the widened torus (one escape and `2m - 1` adaptive channels per link). -/
theorem torusWide_scoreSel (k m B : ℕ) (hm : 0 < m) (score : _) :
    (torusWide k m B hm).DeadlockFreeWith ((torusWide k m B hm).scoreSel score) ∧
      (torusWide k m B hm).LivelockFreeWith ((torusWide k m B hm).scoreSel score) :=
  (torusWide_correct k m B hm).1.scoreSel score

#assert_standard_axioms torusLanes_scoreSel torusWide_scoreSel
#assert_standard_axioms torus_nbrs_iff torusLanesPlacement_cap torusLanes_ceiling
#assert_standard_axioms torusLanes_timed torusLanes_sustains torusLanes_delivered

end AsyncLean.Examples
