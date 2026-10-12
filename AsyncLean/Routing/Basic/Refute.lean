/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Basic.Livelock

/-!
# Interconnection networks with dynamic routing, part 5: refutation

Part 5 of 5 of `AsyncLean.Routing.Basic`; that module has the overview.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*}

variable (N : Network C P)

/-! ### Refutation -/

section Refute

variable [DecidableEq C] [DecidableEq P]

/-- The configuration holding the packets of a list (the first entry for a channel wins). -/
def fill : List (C × P) → Config C P
  | [] => empty
  | q :: qs => Function.update (fill qs) q.1 (some q.2)

omit [DecidableEq P] in
theorem fill_eq_none {qs : List (C × P)} {c : C} : fill qs c = none ↔ c ∉ qs.map Prod.fst := by
  induction qs with
  | nil => simp [fill, empty]
  | cons q qs ih =>
    by_cases h : c = q.1
    · subst h; simp [fill]
    · simp [fill, ih, h]

omit [DecidableEq P] in
theorem mem_of_fill {qs : List (C × P)} {c : C} {p : P} (h : fill qs c = some p) :
    (c, p) ∈ qs := by
  induction qs with
  | nil => simp [fill, empty] at h
  | cons q qs ih =>
    by_cases hc : c = q.1
    · subst hc
      simp only [fill, Function.update_self, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · rw [fill, Function.update_of_ne hc] at h
      exact List.mem_cons_of_mem _ (ih h)

omit [DecidableEq P] in
theorem fill_filter (qs : List (C × P)) (c : C) :
    fill (qs.filter fun q => decide (q.1 ≠ c)) = Function.update (fill qs) c none := by
  induction qs with
  | nil => funext x; by_cases hx : x = c <;> simp [fill, empty, Function.update_apply, hx]
  | cons q qs ih =>
    by_cases hq : q.1 = c
    · rw [List.filter_cons_of_neg (by simpa using hq), ih, fill, hq, Function.update_idem]
    · rw [List.filter_cons_of_pos (by simpa using hq), fill, ih, fill,
        Function.update_comm hq]

/-- Execute actions on the list of occupied channels (under adaptive routing). -/
def runB : List (C × P) → List (Act C P) → Option (List (C × P))
  | qs, [] => some qs
  | qs, .inject c p :: as =>
    if (c, p) ∈ N.inject ∧ fill qs c = none then runB ((c, p) :: qs) as else none
  | qs, .hop c c' p' :: as =>
    match fill qs c with
    | some p =>
      if N.arrived c p = false ∧ (c', p') ∈ N.route c p ∧ fill qs c' = none then
        runB ((c', p') :: qs.filter fun q => decide (q.1 ≠ c)) as
      else none
    | none => none
  | qs, .eject c :: as =>
    match fill qs c with
    | some p => if N.arrived c p = true then runB (qs.filter fun q => decide (q.1 ≠ c)) as
      else none
    | none => none

theorem path_of_runB {qs qs' : List (C × P)} {as : List (Act C P)}
    (h : N.runB qs as = some qs') : N.lts.Path (fill qs) as (fill qs') := by
  induction as generalizing qs with
  | nil =>
    simp only [runB, Option.some.injEq] at h
    subst h; exact LTS.Path.nil _
  | cons a as ih =>
    cases a with
    | inject c p =>
      simp only [runB] at h
      split_ifs at h with hc
      exact LTS.Path.cons (StepWith.inject hc.1 hc.2) (ih h)
    | hop c c' p' =>
      simp only [runB] at h
      split at h
      · rename_i p hp
        split_ifs at h with hc
        have hst := StepWith.hop (N := N) (sel := N.adaptive) hp hc.1 hc.2.1 hc.2.2
        rw [← fill_filter] at hst
        exact LTS.Path.cons hst (ih h)
      · simp at h
    | eject c =>
      simp only [runB] at h
      split at h
      · rename_i p hp
        split_ifs at h with hc
        have hst := StepWith.eject (N := N) (sel := N.adaptive) hp hc
        rw [← fill_filter] at hst
        exact LTS.Path.cons hst (ih h)
      · simp at h

/-- Every packet of `qs` is blocked: it has not arrived and every permitted hop leads to an
occupied channel. -/
def stuckB (qs : List (C × P)) : Bool :=
  qs.all fun q => match fill qs q.1 with
    | some p => !N.arrived q.1 p && (N.route q.1 p).all fun q' => (fill qs q'.1).isSome
    | none => false

/-- A run from the empty network to a non-empty configuration in which every packet is
blocked. -/
def refuteDeadlockB (as : List (Act C P)) : Bool :=
  match N.runB [] as with
  | some qs => !qs.isEmpty && N.stuckB qs
  | none => false

variable {N} in
/-- **Refuting deadlock freedom**: exhibit a run to a configuration in which every packet is
blocked. -/
theorem not_deadlockFree_of_refuteB {as : List (Act C P)} (h : N.refuteDeadlockB as = true) :
    ¬ N.DeadlockFree := by
  unfold refuteDeadlockB at h
  split at h
  · rename_i qs hrun
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    obtain ⟨hne, hstuck⟩ := h
    intro hD
    have hr : N.lts.Reachable empty (fill qs) := (N.path_of_runB hrun).reachable
    have hfne : fill qs ≠ empty := by
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
      intro he
      have : fill qs q.1 = none := by rw [he]; rfl
      exact fill_eq_none.1 this (List.mem_map_of_mem hq)
    obtain ⟨a, f', ha, hst⟩ := hD _ N.adaptive_valid _ hr hfne
    have key : ∀ c p, fill qs c = some p →
        N.arrived c p = false ∧ ∀ q' ∈ N.route c p, fill qs q'.1 ≠ none := by
      intro c p hp
      have := (List.all_eq_true.1 hstuck) (c, p) (mem_of_fill hp)
      simp only [hp, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
        Option.isSome_iff_ne_none] at this
      exact this
    change N.StepWith N.adaptive _ a f' at hst
    cases hst with
    | inject => simp [Act.IsMove] at ha
    | hop hp _ hq hfree => exact (key _ _ hp).2 _ hq hfree
    | eject hp harr => simp [(key _ _ hp).1] at harr
  · simp at h

/-- The two lists describe the same configuration. -/
def sameB (qs qs' : List (C × P)) : Bool :=
  (qs ++ qs').all fun q => decide (fill qs q.1 = fill qs' q.1)

theorem fill_eq_of_sameB {qs qs' : List (C × P)} (h : sameB qs qs' = true) :
    fill qs = fill qs' := by
  funext c
  by_cases hc : c ∈ (qs ++ qs').map Prod.fst
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
    exact of_decide_eq_true ((List.all_eq_true.1 h) q hq)
  · simp only [List.map_append, List.mem_append, not_or] at hc
    rw [fill_eq_none.2 hc.1, fill_eq_none.2 hc.2]

/-- A run `pre` from the empty network, followed by a non-empty cycle `cyc` of moves that
returns to the same configuration. -/
def refuteLivelockB (pre cyc : List (Act C P)) : Bool :=
  !cyc.isEmpty && cyc.all Act.isMove &&
    match N.runB [] pre with
    | some qs => match N.runB qs cyc with
      | some qs' => sameB qs qs'
      | none => false
    | none => false

variable {N} in
/-- **Refuting livelock freedom**: exhibit a reachable configuration and a non-empty cycle of
moves (without injections) back to it. -/
theorem not_livelockFree_of_refuteB {pre cyc : List (Act C P)}
    (h : N.refuteLivelockB pre cyc = true) : ¬ N.LivelockFree := by
  unfold refuteLivelockB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨hne, hmv⟩, h⟩ := h
  split at h
  · rename_i qs hpre
    split at h
    · rename_i qs' hcyc
      intro hL
      have hp := N.path_of_runB hcyc
      rw [← fill_eq_of_sameB h] at hp
      refine LTS.not_livelockFree_of_cycle (N.path_of_runB hpre).reachable
        (hp.iStep_transGen (fun a ha => (List.all_eq_true.1 hmv) a ha) hne)
        ((N.livelockFree_iff_adaptive).1 hL)
    · simp at h
  · simp at h

end Refute

end Network

end AsyncLean
