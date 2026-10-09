/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Throughput bounds in the fluid model

The fluid model of a network ignores packets, buffers and timing: every directed link `u → v`
carries a rate of traffic up to its capacity `cap u v`, and a traffic matrix `dem s d` (the rate
from `s` to `d` per unit of throughput) is **routable at throughput `θ`** if a multicommodity
flow (one commodity per destination) carries `θ * dem` within the capacities (`Fluid.Flow`).
The throughput a network reaches with packets is at most what it reaches in the fluid model,
under any routing, adaptive or not, with or without detours.

The upper bounds here are all instances of one argument (`Fluid.potential_bound`, the weak
duality of the maximum concurrent flow problem): give every vertex a potential `φ d v` towards
each destination, with `φ d d = 0`, that drops by at most `len u v` along every link.  Every
unit of commodity `d` starting at `s` must lose the potential `φ d s` on its way, and a link
can lose at most `len u v` per unit, so

  `θ * ∑ s d, dem s d * φ d s ≤ ∑ u v, cap u v * len u v`.

* `Fluid.potential_bound` : the bound for any potential.
* `Fluid.Flow.potential_bound_on` : the same for a flow restricted to some links (for example a
  minimal flow, `Fluid.Flow.Minimal`): the potential need only respect the allowed links.
* `Fluid.wire_bound` : **the wire bound.**  Place the vertices on the integer grid and let
  `len u v` be the wire length of the link, at least the Manhattan distance of its ends.  Then
  `θ * ∑ s d, dem s d * dist s d ≤ ∑ u v, cap u v * len u v`: the traffic times the distance it
  must travel is at most the capacity times the wire.  This holds for every topology and every
  routing; only the wire is counted (any radix, any number of links).
* `Fluid.cut_bound` : **the cut bound.**  For a set `S` of vertices, the traffic from `S` to its
  complement is at most the capacity of the links leaving `S`.
-/

namespace AsyncLean

namespace Fluid

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A network in the fluid model: the capacity of every directed link (`0`: no link). -/
structure Net (V : Type*) where
  /-- The capacity of the directed link `u → v`; `0` if there is no link. -/
  cap : V → V → ℚ
  cap_nonneg : ∀ u v, 0 ≤ cap u v

/-- A multicommodity flow routing the traffic matrix `θ * dem` in `N`: `f d u v` is the rate of
traffic for destination `d` on the link `u → v`. -/
structure Flow (N : Net V) (dem : V → V → ℚ) (θ : ℚ) where
  /-- The rate of commodity `d` on the link `u → v`. -/
  f : V → V → V → ℚ
  nonneg : ∀ d u v, 0 ≤ f d u v
  /-- Away from its destination, a commodity leaves a vertex at the rate it enters it plus the
  rate the vertex sends. -/
  conserve : ∀ d v, v ≠ d → ∑ w, f d v w - ∑ u, f d u v = θ * dem v d
  capacity : ∀ u v, ∑ d, f d u v ≤ N.cap u v

/-- The traffic matrix `dem` is routable at throughput `θ` in `N`. -/
def Routable (N : Net V) (dem : V → V → ℚ) (θ : ℚ) : Prop := Nonempty (Flow N dem θ)

namespace Flow

variable {N : Net V} {dem : V → V → ℚ} {θ : ℚ}

omit [DecidableEq V] in
/-- There is no flow on a link of capacity zero. -/
theorem eq_zero_of_cap (F : Flow N dem θ) {u v : V} (h : N.cap u v ≤ 0) (d : V) :
    F.f d u v = 0 := by
  have hsum := F.capacity u v
  have hle : F.f d u v ≤ ∑ d', F.f d' u v :=
    Finset.single_le_sum (fun d' _ => F.nonneg d' u v) (Finset.mem_univ d)
  linarith [F.nonneg d u v]

/-- The potential drop along the links, weighted by the flow, telescopes to the potential of
the sources: for a potential `φ` with `φ d = 0`,
`∑ u v, f d u v * (φ u - φ v) = θ * ∑ s, dem s d * φ s`. -/
theorem telescope (F : Flow N dem θ) (d : V) (φ : V → ℚ) (hφ : φ d = 0) :
    ∑ u, ∑ v, F.f d u v * (φ u - φ v) = θ * ∑ s, dem s d * φ s := by
  have h1 : ∑ u, ∑ v, F.f d u v * (φ u - φ v) =
      ∑ u, φ u * (∑ w, F.f d u w - ∑ x, F.f d x u) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => mul_comm _ _
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => mul_comm _ _
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s = d
  · subst hs; simp [hφ]
  · rw [F.conserve d s hs]; ring

end Flow

namespace Flow

variable {N : Net V} {dem : V → V → ℚ} {θ : ℚ}

/-- The flow uses only the links allowed by `S`: commodity `d` is on the link `u → v` only if
`S d u v`. -/
def SupportedOn (F : Flow N dem θ) (S : V → V → V → Prop) : Prop :=
  ∀ d u v, 0 < F.f d u v → S d u v

/-- The flow is **minimal** for the distance `dist`: every link a commodity uses brings it
strictly closer to its destination (no detours). -/
def Minimal (F : Flow N dem θ) (dist : V → V → ℚ) : Prop :=
  F.SupportedOn fun d u v => dist v d < dist u d

/-- **The potential bound for a restricted flow.**  If `F` uses only the links allowed by `S`,
the potential needs to drop by at most `len u v` only along the allowed links. -/
theorem potential_bound_on (F : Flow N dem θ) {S : V → V → V → Prop} (hF : F.SupportedOn S)
    (len : V → V → ℚ) (hlen : ∀ u v, 0 ≤ len u v) (φ : V → V → ℚ) (hφd : ∀ d, φ d d = 0)
    (hφ : ∀ d u v, S d u v → 0 < N.cap u v → φ d u - φ d v ≤ len u v) :
    θ * ∑ s, ∑ d, dem s d * φ d s ≤ ∑ u, ∑ v, N.cap u v * len u v := by
  calc θ * ∑ s, ∑ d, dem s d * φ d s
      = ∑ d, θ * ∑ s, dem s d * φ d s := by rw [Finset.sum_comm, Finset.mul_sum]
    _ = ∑ d, ∑ u, ∑ v, F.f d u v * (φ d u - φ d v) :=
        Finset.sum_congr rfl fun d _ => (F.telescope d (φ d) (hφd d)).symm
    _ ≤ ∑ d, ∑ u, ∑ v, F.f d u v * len u v := by
        refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun u _ =>
          Finset.sum_le_sum fun v _ => ?_
        rcases (F.nonneg d u v).lt_or_eq with hp | hz
        · have hc : 0 < N.cap u v := by
            by_contra hc
            rw [F.eq_zero_of_cap (not_lt.1 hc) d] at hp
            exact lt_irrefl _ hp
          exact mul_le_mul_of_nonneg_left (hφ d u v (hF d u v hp) hc) (F.nonneg d u v)
        · rw [← hz]; simp
    _ = ∑ u, ∑ v, (∑ d, F.f d u v) * len u v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun v _ => (Finset.sum_mul ..).symm
    _ ≤ ∑ u, ∑ v, N.cap u v * len u v :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_right (F.capacity u v) (hlen u v)

end Flow

/-- **The potential bound** (weak duality).  Let `φ d v` be a potential towards every
destination `d` with `φ d d = 0`, dropping by at most `len u v ≥ 0` along every link of positive
capacity.  If `θ * dem` is routable, then
`θ * ∑ s d, dem s d * φ d s ≤ ∑ u v, cap u v * len u v`. -/
theorem potential_bound {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (h : Routable N dem θ)
    (len : V → V → ℚ) (hlen : ∀ u v, 0 ≤ len u v) (φ : V → V → ℚ) (hφd : ∀ d, φ d d = 0)
    (hφ : ∀ d u v, 0 < N.cap u v → φ d u - φ d v ≤ len u v) :
    θ * ∑ s, ∑ d, dem s d * φ d s ≤ ∑ u, ∑ v, N.cap u v * len u v := by
  obtain ⟨F⟩ := h
  exact F.potential_bound_on (S := fun _ _ _ => True) (fun _ _ _ _ => trivial) len hlen φ hφd
    (fun d u v _ hc => hφ d u v hc)

/-- The Manhattan distance of two grid points. -/
def manhattan (p q : ℤ × ℤ) : ℚ := |(p.1 - q.1 : ℚ)| + |(p.2 - q.2 : ℚ)|

theorem manhattan_self (p : ℤ × ℤ) : manhattan p p = 0 := by simp [manhattan]

theorem manhattan_nonneg (p q : ℤ × ℤ) : 0 ≤ manhattan p q := by
  unfold manhattan; positivity

/-- The triangle inequality, in the form the wire bound uses. -/
theorem manhattan_sub_le (p q r : ℤ × ℤ) :
    manhattan p r - manhattan q r ≤ manhattan p q := by
  unfold manhattan
  have h1 := abs_sub_le (p.1 : ℚ) q.1 r.1
  have h2 := abs_sub_le (p.2 : ℚ) q.2 r.2
  have h3 : |(q.1 - r.1 : ℚ)| = |(r.1 - q.1 : ℚ)| := abs_sub_comm _ _
  have h4 : |(q.2 - r.2 : ℚ)| = |(r.2 - q.2 : ℚ)| := abs_sub_comm _ _
  have h5 : |(p.1 - r.1 : ℚ)| ≤ |(p.1 - q.1 : ℚ)| + |(q.1 - r.1 : ℚ)| := abs_sub_le _ _ _
  have h6 : |(p.2 - r.2 : ℚ)| ≤ |(p.2 - q.2 : ℚ)| + |(q.2 - r.2 : ℚ)| := abs_sub_le _ _ _
  linarith

/-- **The wire bound.**  Place the vertices on the grid (`pos`); let `len u v ≥ 0` be the wire
length of every link of positive capacity, at least the Manhattan distance of its ends.  If
`θ * dem` is routable, the traffic times the distance it must travel is at most the capacity
times the wire: `θ * ∑ s d, dem s d * dist s d ≤ ∑ u v, cap u v * len u v`.  Every topology and
every routing (adaptive, with detours, split over many paths) is covered. -/
theorem wire_bound {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (h : Routable N dem θ)
    (pos : V → ℤ × ℤ) (len : V → V → ℚ) (hlen : ∀ u v, 0 ≤ len u v)
    (hwire : ∀ u v, 0 < N.cap u v → manhattan (pos u) (pos v) ≤ len u v) :
    θ * ∑ s, ∑ d, dem s d * manhattan (pos s) (pos d) ≤ ∑ u, ∑ v, N.cap u v * len u v :=
  potential_bound h len hlen (fun d v => manhattan (pos v) (pos d))
    (fun _ => manhattan_self _)
    (fun _ u v hc => (manhattan_sub_le _ _ _).trans (hwire u v hc))

/-- **The cut bound.**  For a set `S` of vertices, the traffic from `S` to its complement is at
most the capacity of the links leaving `S`. -/
theorem cut_bound {N : Net V} {dem : V → V → ℚ} {θ : ℚ} (h : Routable N dem θ)
    (S : V → Prop) [DecidablePred S] :
    θ * ∑ s, ∑ d, (if S s ∧ ¬ S d then dem s d else 0) ≤
      ∑ u, ∑ v, if S u ∧ ¬ S v then N.cap u v else 0 := by
  have key := potential_bound h (fun u v => if S u ∧ ¬ S v then 1 else 0)
    (fun u v => by split_ifs <;> norm_num)
    (fun d v => if S v ∧ ¬ S d then 1 else 0) (fun d => by simp)
    (fun _ u v _ => by
      by_cases hu : S u <;> by_cases hv : S v <;> split_ifs <;> simp_all)
  have e1 : ∑ s, ∑ d, dem s d * (if S s ∧ ¬ S d then (1 : ℚ) else 0) =
      ∑ s, ∑ d, (if S s ∧ ¬ S d then dem s d else 0) :=
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
  have e2 : ∑ u, ∑ v, N.cap u v * (if S u ∧ ¬ S v then (1 : ℚ) else 0) =
      ∑ u, ∑ v, (if S u ∧ ¬ S v then N.cap u v else 0) :=
    Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by split_ifs <;> simp
  rw [e1, e2] at key
  exact key

end Fluid

end AsyncLean
