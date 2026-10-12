/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Throughput.Timed

/-!
# Packet networks in time, part 2: lanes add their throughput

Timed runs of the lanes, side by side round by round, are a timed run of the lane network
(`Network.lanesTimed`) that injects the sum of what the lanes inject
(`Network.lanesTimed_injected`); a placement of a network places its lanes with `m` times the
capacity (`Network.lanesPlacement_cap`).
-/

namespace AsyncLean

namespace Network

open Finset

variable {C P V : Type*}

variable {N : Network C P}

/-! ### Lanes run in parallel, in time -/

section LanesTimed

variable {ι : Type*} [DecidableEq ι] [DecidableEq C]

/-- A placement of a network places its lanes: every lane on the same graph. -/
def lanesPlacement (ls : List ι) {M : Network C P} (L : M.Placement V) :
    (lanes ls fun _ => M).Placement V where
  pos x := L.pos x.2
  dest := L.dest
  link x := L.link x.2
  arrived x p h := L.arrived x.2 p h

omit [DecidableEq ι] [DecidableEq C] in
theorem lanesPlacement_fits (ls : List ι) {M : Network C P} {L : M.Placement V} (h : L.Fits) :
    (lanesPlacement ls L).Fits := by
  intro x p q ha hq
  obtain ⟨i, c⟩ := x
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
  exact h c p q' ha hq'

omit [DecidableEq ι] [DecidableEq C] in
/-- `m` lanes have `m` times the capacity of one. -/
theorem lanesPlacement_cap [Fintype ι] [Fintype C] [DecidableEq V] (ls : List ι)
    {M : Network C P} (L : M.Placement V) (u v : V) :
    (lanesPlacement ls L).net.cap u v = Fintype.card ι * L.net.cap u v := by
  show ((univ.filter fun x : ι × C => L.link x.2 = some (u, v)).card : ℚ) =
    Fintype.card ι * ((univ.filter fun c => L.link c = some (u, v)).card : ℚ)
  have e : (univ.filter fun x : ι × C => L.link x.2 = some (u, v)) =
      (univ : Finset ι) ×ˢ (univ.filter fun c => L.link c = some (u, v)) := by
    ext x; simp
  rw [e, card_product, card_univ]
  push_cast; ring

omit [DecidableEq ι] [DecidableEq C] in
theorem countP_flatMap_toLane {L : List ι} (as : ι → List (Act C P)) (p : Act (ι × C) P → Bool) :
    (L.flatMap fun i => (as i).map (Act.toLane i)).countP p =
      (L.map fun i => (as i).countP (p ∘ Act.toLane i)).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [List.flatMap_cons, List.countP_append, ih, List.countP_map]

omit [DecidableEq ι] [DecidableEq C] in
theorem hopTarget_toLane (i : ι) (a : Act C P) (j : ι) (c : C) :
    ((Act.toLane i a).hopTarget = some (j, c)) ↔ i = j ∧ a.hopTarget = some c := by
  cases a <;> simp [Act.toLane, Act.hopTarget, eq_comm]

omit [DecidableEq C] in
theorem sum_ite_nodup {L : List ι} (hnd : L.Nodup) (j : ι) (n : ι → ℕ) :
    (L.map fun i => if i = j then n i else 0).sum ≤ n j := by
  induction L with
  | nil => simp
  | cons i L ih =>
    obtain ⟨hi, hnd'⟩ := List.nodup_cons.1 hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases h : i = j
    · subst h
      have : (L.map fun i' => if i' = i then n i' else 0).sum = 0 := by
        rw [List.sum_eq_zero]
        intro x hx
        obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hx
        exact ite_eq_right (fun e => hi (by rw [← e]; exact hi'))
      simp [this]
    · simp [h, ih hnd']

omit [DecidableEq ι] [DecidableEq C] in
/-- A sum over the rounds of sums over the lanes is the sum over the lanes of the sums over the
rounds. -/
theorem sum_range_list_sum (L : List ι) (T : ℕ) (g : ℕ → ι → ℕ) :
    ∑ t ∈ range T, (L.map fun i => g t i).sum = (L.map fun i => ∑ t ∈ range T, g t i).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [sum_add_distrib, ih]

/-- **Timed runs of the lanes are together a timed run of the lane network**: round by round,
the lanes act side by side.  The lane network injects, in every round, the packets of all the
lanes. -/
noncomputable def lanesTimed {ls : List ι} {M : Network C P} {L : List ι}
    (hL : ∀ i ∈ L, i ∈ ls) (hnd : L.Nodup) (R : ι → M.TimedRun M.adaptive) :
    (lanes ls fun _ => M).TimedRun (lanes ls fun _ => M).adaptive where
  conf t := combine fun i => if i ∈ L then (R i).conf t else empty
  acts t := L.flatMap fun i => ((R i).acts t).map (Act.toLane i)
  start := by
    funext x
    simp [combine, (R _).start, empty]
  path t := by
    refine lanes_path (N := fun _ => M) hL hnd (fun i hi => ?_) (fun i hi => ?_)
    · simp only [hi, ite_true]; exact (R i).path t
    · simp [hi]
  once t x := by
    obtain ⟨j, c⟩ := x
    rw [countP_flatMap_toLane]
    have e : ∀ i, ((R i).acts t).countP
        ((fun a : Act (ι × C) P => decide (a.hopTarget = some (j, c))) ∘ Act.toLane i) =
        if i = j then ((R i).acts t).countP (fun a => decide (a.hopTarget = some c)) else 0 :=
      fun i => by
        by_cases h : i = j
        · subst h
          rw [ite_eq_left rfl]
          congr 1; funext a; simp [hopTarget_toLane]
        · rw [ite_eq_right h]
          rw [List.countP_eq_zero]
          intro a _; simp [hopTarget_toLane, h]
    simp only [e]
    exact (sum_ite_nodup hnd j _).trans ((R j).once t c)

/-- **Lanes add their throughput**: the lane network injects from `s` for `d` exactly the sum of
what its lanes inject. -/
theorem lanesTimed_injected [DecidableEq V] {ls : List ι} {M : Network C P} {L : List ι}
    (hL : ∀ i ∈ L, i ∈ ls) (hnd : L.Nodup) (R : ι → M.TimedRun M.adaptive)
    (Lp : M.Placement V) (T : ℕ) (s d : V) :
    (lanesTimed hL hnd R).injected (lanesPlacement ls Lp) T s d =
      (L.map fun i => (R i).injected Lp T s d).sum := by
  simp only [TimedRun.injected, lanesTimed, countP_flatMap_toLane]
  have e : ∀ i a, ((TimedRun.isInj (lanesPlacement ls Lp) s d) ∘ Act.toLane i) a =
      TimedRun.isInj Lp s d a := fun i a => by
    cases a <;> rfl
  simp only [funext (e _)]
  exact sum_range_list_sum L T _

end LanesTimed

end Network

end AsyncLean
