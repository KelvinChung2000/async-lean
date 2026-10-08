/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Optimal

/-!
# Refuting deadlock freedom through an embedding

A deadlock found in a small network carries over to every network that contains a copy of it.
This is how a finite, kernel-checked counterexample proves a statement about networks of every
size: the small network is a window of the large one.

* `runGoodB` : a run of the small network `M` that only uses channels satisfying `chanOK` (the
  window) and only moves or injects packets satisfying `good` (the pairs the large network is
  known to simulate).  Other packets may sit in the initial configuration: they never move.
* `path_of_runGoodB` : such a run, mapped along `φ` (channels) and `ψ` (headers), is a run of
  the large network `N`, provided `φ` is injective on the window and every injection and hop of a
  good pair has its image in `N`.
* `not_deadlockFree_of_runGoodB` : if the run ends in a configuration where every packet is
  blocked under a routing function `hi` of the small network, and every hop `N` permits from
  the image of a packet is the image of a hop of `hi`, then `N` deadlocks.

The packets that never move are what make this useful: one of them may stand for a packet of
the large network whose destination lies far outside the window, about which `N` is only known
through hypotheses (its permitted hops at the one pair it occupies).
-/

namespace AsyncLean

namespace Network

variable {C P C' P' : Type*}

/-- An action of one network as an action of another, along maps of the channels and headers. -/
def Act.map (φ : C → C') (ψ : P → P') : Act C P → Act C' P'
  | .inject c p => .inject (φ c) (ψ p)
  | .hop c c' p => .hop (φ c) (φ c') (ψ p)
  | .eject c => .eject (φ c)

variable [DecidableEq C] [DecidableEq P] [DecidableEq C']

/-- Run `as` from `qs` under `M`, without ejections, checking that every channel the run uses
satisfies `chanOK` and every pair that is injected, moves, or is moved to satisfies `good`. -/
def runGoodB (M : Network C P) (chanOK : C → Bool) (good : C → P → Bool) :
    List (C × P) → List (Act C P) → Option (List (C × P))
  | qs, [] => some qs
  | qs, .inject c p :: as =>
    if (c, p) ∈ M.inject ∧ chanOK c = true ∧ good c p = true ∧ fill qs c = none then
      runGoodB M chanOK good ((c, p) :: qs) as
    else none
  | qs, .hop c c' p' :: as =>
    match fill qs c with
    | some p =>
      if chanOK c = true ∧ chanOK c' = true ∧ good c p = true ∧ good c' p' = true ∧
          M.arrived c p = false ∧ (c', p') ∈ M.route c p ∧ fill qs c' = none then
        runGoodB M chanOK good ((c', p') :: qs.filter fun q => decide (q.1 ≠ c)) as
      else none
    | none => none
  | _, .eject _ :: _ => none

section Map

variable {chanOK : C → Bool} {φ : C → C'} {ψ : P → P'}

omit [DecidableEq P] in
theorem fill_map (hφ : ∀ c₁ c₂, chanOK c₁ = true → chanOK c₂ = true → φ c₁ = φ c₂ → c₁ = c₂)
    {qs : List (C × P)} (hqs : ∀ q ∈ qs, chanOK q.1 = true) {c : C} (hc : chanOK c = true) :
    fill (qs.map fun q => (φ q.1, ψ q.2)) (φ c) = (fill qs c).map ψ := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have ih := ih fun q' hq' => hqs q' (List.mem_cons_of_mem _ hq')
    simp only [List.map_cons, fill]
    by_cases h : c = q.1
    · subst h; simp
    · have h' : φ c ≠ φ q.1 := fun he => h (hφ _ _ hc (hqs q List.mem_cons_self) he)
      rw [Function.update_of_ne h', Function.update_of_ne h, ih]

omit [DecidableEq P] in
theorem map_filter_ne (hφ : ∀ c₁ c₂, chanOK c₁ = true → chanOK c₂ = true → φ c₁ = φ c₂ → c₁ = c₂)
    {qs : List (C × P)} (hqs : ∀ q ∈ qs, chanOK q.1 = true) {c : C} (hc : chanOK c = true) :
    (qs.filter fun q => decide (q.1 ≠ c)).map (fun q => (φ q.1, ψ q.2)) =
      (qs.map fun q => (φ q.1, ψ q.2)).filter fun q => decide (q.1 ≠ φ c) := by
  rw [List.filter_map]
  congr 1
  refine List.filter_congr fun q hq => ?_
  simp only [Function.comp_apply, decide_eq_decide]
  exact ⟨fun h he => h (hφ _ _ (hqs q hq) hc he), fun h he => h (by rw [he])⟩

/-- **A run in a window is a run of the large network.** -/
theorem path_of_runGoodB {M : Network C P} {N : Network C' P'} {good : C → P → Bool}
    (hφ : ∀ c₁ c₂, chanOK c₁ = true → chanOK c₂ = true → φ c₁ = φ c₂ → c₁ = c₂)
    (hinj : ∀ c p, good c p = true → (c, p) ∈ M.inject → (φ c, ψ p) ∈ N.inject)
    (hhop : ∀ c p c' p', good c p = true → good c' p' = true → M.arrived c p = false →
      (c', p') ∈ M.route c p → N.arrived (φ c) (ψ p) = false ∧ (φ c', ψ p') ∈ N.route (φ c) (ψ p))
    {qs qs' : List (C × P)} {as : List (Act C P)} (hqs : ∀ q ∈ qs, chanOK q.1 = true)
    (h : M.runGoodB chanOK good qs as = some qs') :
    N.lts.Path (fill (qs.map fun q => (φ q.1, ψ q.2))) (as.map (Act.map φ ψ))
        (fill (qs'.map fun q => (φ q.1, ψ q.2))) ∧ ∀ q ∈ qs', chanOK q.1 = true := by
  induction as generalizing qs with
  | nil =>
    simp only [runGoodB, Option.some.injEq] at h
    subst h; exact ⟨LTS.Path.nil _, hqs⟩
  | cons a as ih =>
    cases a with
    | inject c p =>
      simp only [runGoodB] at h
      split_ifs at h with hc
      obtain ⟨hcM, hcok, hgood, hfree⟩ := hc
      have hqs' : ∀ q ∈ (c, p) :: qs, chanOK q.1 = true := by
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hcok
        · exact hqs q hq
      obtain ⟨hp, hok⟩ := ih hqs' h
      refine ⟨LTS.Path.cons (StepWith.inject (hinj c p hgood hcM) ?_) hp, hok⟩
      rw [fill_map hφ hqs hcok, hfree]; rfl
    | hop c c' p' =>
      simp only [runGoodB] at h
      split at h
      · rename_i p hp
        split_ifs at h with hc
        obtain ⟨hcok, hcok', hg, hg', harr, hroute, hfree⟩ := hc
        have hqs' : ∀ q ∈ (c', p') :: qs.filter (fun q => decide (q.1 ≠ c)),
            chanOK q.1 = true := by
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hcok'
          · exact hqs q (List.mem_filter.1 hq).1
        obtain ⟨hpath, hok⟩ := ih hqs' h
        obtain ⟨harr', hroute'⟩ := hhop c p c' p' hg hg' harr hroute
        have hst := StepWith.hop (N := N) (sel := N.adaptive)
          (f := fill (qs.map fun q => (φ q.1, ψ q.2)))
          (by rw [fill_map hφ hqs hcok, hp]; rfl) harr' hroute'
          (by rw [fill_map hφ hqs hcok', hfree]; rfl)
        rw [← fill_filter, ← map_filter_ne hφ hqs hcok] at hst
        exact ⟨LTS.Path.cons hst hpath, hok⟩
      · simp at h
    | eject c => simp [runGoodB] at h

/-- **A deadlock in a window is a deadlock of the large network.**  A run of `M` from `qs` (whose
image is reachable in `N`) to a configuration where every packet is blocked under `hi`, such that
every hop `N` permits from the image of a packet is the image of a hop of `hi`. -/
theorem not_deadlockFree_of_runGoodB {M : Network C P} {N : Network C' P'} {good : C → P → Bool}
    (hi : C → P → List (C × P))
    (hφ : ∀ c₁ c₂, chanOK c₁ = true → chanOK c₂ = true → φ c₁ = φ c₂ → c₁ = c₂)
    (hinj : ∀ c p, good c p = true → (c, p) ∈ M.inject → (φ c, ψ p) ∈ N.inject)
    (hhop : ∀ c p c' p', good c p = true → good c' p' = true → M.arrived c p = false →
      (c', p') ∈ M.route c p → N.arrived (φ c) (ψ p) = false ∧ (φ c', ψ p') ∈ N.route (φ c) (ψ p))
    {qs qs' : List (C × P)} {as : List (Act C P)} (hqs : ∀ q ∈ qs, chanOK q.1 = true)
    (hpre : N.lts.Reachable empty (fill (qs.map fun q => (φ q.1, ψ q.2))))
    (h : M.runGoodB chanOK good qs as = some qs') (hne : qs' ≠ [])
    (hstuck : (M.withRoute hi).stuckB qs' = true)
    (hcover : ∀ c p, (c, p) ∈ qs' → M.arrived c p = false →
      N.arrived (φ c) (ψ p) = false ∧ ∀ q ∈ N.route (φ c) (ψ p), ∃ q' ∈ hi c p, φ q'.1 = q.1) :
    ¬ N.DeadlockFree := by
  obtain ⟨hpath, hok⟩ := path_of_runGoodB hφ hinj hhop hqs h
  intro hD
  have hr := hpre.trans hpath.reachable
  have key : ∀ c p, fill qs' c = some p →
      M.arrived c p = false ∧ ∀ q' ∈ hi c p, fill qs' q'.1 ≠ none := by
    intro c p hp
    have := (List.all_eq_true.1 hstuck) (c, p) (mem_of_fill hp)
    simp only [hp, withRoute_arrived, withRoute_route, Bool.and_eq_true, Bool.not_eq_true',
      List.all_eq_true, Option.isSome_iff_ne_none] at this
    exact this
  -- every occupied channel of the image is the image of an occupied channel
  have hocc : ∀ c₀ p₀, fill (qs'.map fun q => (φ q.1, ψ q.2)) c₀ = some p₀ →
      ∃ c p, chanOK c = true ∧ fill qs' c = some p ∧ φ c = c₀ ∧ ψ p = p₀ := by
    intro c₀ p₀ hp₀
    obtain ⟨q, hq, he⟩ := List.mem_map.1 (mem_of_fill hp₀)
    have hc := hok q hq
    have h1 := fill_map (ψ := ψ) hφ hok hc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    rw [hp₀] at h1
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 h1.symm
    exact ⟨q.1, p, hc, hp, rfl, rfl⟩
  have hfne : fill (qs'.map fun q => (φ q.1, ψ q.2)) ≠ empty := by
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
    intro he
    have h1 := fill_map (ψ := ψ) hφ hok (hok q hq)
    rw [he] at h1
    have h2 : fill qs' q.1 ≠ none := fun h0 => (fill_eq_none.1 h0) (List.mem_map_of_mem hq)
    revert h2
    cases hf : fill qs' q.1 with
    | none => simp
    | some p => simp [hf, empty] at h1
  obtain ⟨a, f', ha, hst⟩ := hD _ N.adaptive_valid _ hr hfne
  change N.StepWith N.adaptive _ a f' at hst
  cases hst with
  | inject => simp [Act.IsMove] at ha
  | hop hp _ hq hfree =>
    obtain ⟨c, p, hc, hcp, rfl, rfl⟩ := hocc _ _ hp
    obtain ⟨harr, hall⟩ := key c p hcp
    obtain ⟨-, hcov⟩ := hcover c p (mem_of_fill hcp) harr
    obtain ⟨q', hq', hφq⟩ := hcov _ hq
    have hocc' := hall q' hq'
    obtain ⟨p', hp'⟩ := Option.ne_none_iff_exists'.1 hocc'
    have hc' : chanOK q'.1 = true := hok (q'.1, p') (mem_of_fill hp')
    have := fill_map (ψ := ψ) hφ hok hc'
    rw [hp', hφq, hfree] at this
    simp at this
  | eject hp harr =>
    obtain ⟨c, p, hc, hcp, rfl, rfl⟩ := hocc _ _ hp
    obtain ⟨harr', -⟩ := key c p hcp
    rw [(hcover c p (mem_of_fill hcp) harr').1] at harr
    cases harr

end Map

end Network

end AsyncLean
