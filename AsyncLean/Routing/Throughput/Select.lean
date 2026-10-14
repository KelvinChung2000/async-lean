/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Throughput.Timed

/-!
# Packet networks in time, part 3: selections that follow a score are safe

Choosing, among the free permitted hops, those of largest score (backlog differences, as
backpressure does) is a valid selection (`Network.scoreSel_valid`), so every correct network stays
deadlock and livelock free under it (`Network.Correct.scoreSel`).
-/

namespace AsyncLean

namespace Network

open Finset

variable {C P V : Type*}

variable {N : Network C P}

/-! ### Selections that follow a score are safe -/

section ScoreSel

variable [DecidableEq C] (N)

/-- **Selection by score**: among the free permitted hops, offer those of largest score (for
example the backlog difference across the link, as backpressure does); if none is free, offer
every permitted hop. -/
def scoreSel (score : Config C P → C → P → C × P → ℚ) : Selection C P := fun f c p =>
  let free := (N.route c p).filter fun q => (f q.1).isNone
  if free = [] then N.route c p
  else free.filter fun q => decide (∀ q' ∈ free, score f c p q' ≤ score f c p q)

omit [DecidableEq C] in
/-- A nonempty list has an element of largest score. -/
theorem exists_max_score {α : Type*} (g : α → ℚ) :
    ∀ l : List α, l ≠ [] → ∃ x ∈ l, ∀ y ∈ l, g y ≤ g x
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, fun y hy => by simp at hy; rw [hy]⟩
  | a :: b :: l, _ => by
    obtain ⟨x, hx, hmax⟩ := exists_max_score g (b :: l) (by simp)
    by_cases hax : g x ≤ g a
    · refine ⟨a, by simp, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_rfl
      · exact (hmax y hy).trans hax
    · refine ⟨x, List.mem_cons_of_mem _ hx, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact (lt_of_not_ge hax).le
      · exact hmax y hy

omit [DecidableEq C] in
/-- **Selection by score is valid**: it offers only permitted hops and is work conserving.  So
every network proved correct under all valid selections (`Network.Correct`) — the planes, the
shared planes, the replicated networks — stays deadlock and livelock free when its hops are chosen
by any score, backlog differences included. -/
theorem scoreSel_valid (score : Config C P → C → P → C × P → ℚ) :
    N.ValidSel (N.scoreSel score) := by
  refine ⟨fun f c p q hq => ?_, fun f c p _ hfree => ?_⟩
  · unfold scoreSel at hq
    simp only at hq
    split_ifs at hq
    · exact hq
    · exact (List.mem_filter.1 (List.mem_filter.1 hq).1).1
  · obtain ⟨q, hq, hqf⟩ := hfree
    have hne : (N.route c p).filter (fun q => (f q.1).isNone) ≠ [] := by
      intro h
      have : q ∈ (N.route c p).filter (fun q => (f q.1).isNone) :=
        List.mem_filter.2 ⟨hq, by simp [hqf]⟩
      rw [h] at this; simp at this
    obtain ⟨x, hx, hmax⟩ := exists_max_score (score f c p) _ hne
    refine ⟨x, ?_, ?_⟩
    · unfold scoreSel
      simp only [hne, ↓reduceIte]
      exact List.mem_filter.2 ⟨hx, by simpa using hmax⟩
    · simpa using (List.mem_filter.1 hx).2

/-- A correct network stays deadlock and livelock free when its hops are chosen by a score. -/
theorem Correct.scoreSel {N : Network C P} (h : N.Correct)
    (score : Config C P → C → P → C × P → ℚ) :
    N.DeadlockFreeWith (N.scoreSel score) ∧ N.LivelockFreeWith (N.scoreSel score) :=
  ⟨h.1 _ (N.scoreSel_valid score), h.2 _ (N.scoreSel_valid score)⟩

end ScoreSel

end Network

end AsyncLean
