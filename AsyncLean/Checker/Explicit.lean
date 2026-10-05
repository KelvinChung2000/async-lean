/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties
import AsyncLean.Checker.BTree

/-!
# A verified, certificate-checking model checker for finite-state systems

For a concrete design whose reachable state space is finite (a bounded Petri net, a
signal transition graph, a gate-level circuit, …) the properties of
`AsyncLean.LTS.Properties` can be established *by computation inside the Lean kernel*.

The design follows the "untrusted search, trusted check" principle:

1. An **untrusted** exploration (`explore`) enumerates candidate states, and untrusted
   heuristics compute ranking functions (`autoRank`) and distance functions (`autoDist`).
   None of these functions is verified — they need not be.
2. A small **trusted checker** (`closedB`, `noDeadlockB`, `rankDecreasesB`, `progressB`)
   validates the resulting *certificate*: a finite set of states (stored in a binary tree,
   `AsyncLean.BTree`) that contains the initial state and is closed under successors,
   together with ranking / distance functions.  Its soundness theorems
   (`deadlockFree_of_check`, `livelockFree_of_check`, `live_of_check`) are proved once and
   for all, so a successful check *is* a proof.

Checks are run with `decide +kernel` (or `decide`), which uses only the Lean kernel's
definitional evaluation — no `native_decide`, hence no `Lean.ofReduceBool` axiom.

If a check returns `false` nothing is proved: either the property fails, or the fuel was
too small.  Use the refutation rules of `AsyncLean.LTS.Properties` (counterexample traces)
to prove the negation.
-/

namespace AsyncLean

/-- An LTS given by an explicit, computable successor function. -/
structure ExplicitLTS (S L : Type*) where
  /-- All labelled successors of a state. -/
  succ : S → List (L × S)

namespace ExplicitLTS

variable {S L : Type*} (E : ExplicitLTS S L)

/-- The semantics of an explicit LTS. -/
def toLTS : LTS S L where
  step s l s' := (l, s') ∈ E.succ s

section Checker

variable [DecidableEq S] (cmp : S → S → Ordering)

/-! ### The trusted checker

A certificate is a tree `t` of states.  The invariant it certifies is membership in
`t.toList`; `cmp` only guides the search (any function is sound). -/

/-- `t` is closed under successors. -/
def closedB (t : BTree S) : Bool :=
  t.all fun s => (E.succ s).all fun e => t.find cmp e.2

/-- No state of `t` is a deadlock. -/
def noDeadlockB (t : BTree S) : Bool :=
  t.all fun s => !(E.succ s).isEmpty

/-- `rank` strictly decreases along every internal step out of `t`. -/
def rankDecreasesB (internal : L → Bool) (rank : S → ℕ) (t : BTree S) : Bool :=
  t.all fun s => (E.succ s).all fun e => !internal e.1 || decide (rank e.2 < rank s)

/-- `l` is enabled in `s`. -/
def enabledB [DecidableEq L] (s : S) (l : L) : Bool :=
  (E.succ s).any fun e => decide (e.1 = l)

/-- From every state of `t`, either `l` is enabled or some step decreases `d`. -/
def progressB [DecidableEq L] (l : L) (d : S → ℕ) (t : BTree S) : Bool :=
  t.all fun s => E.enabledB s l || (E.succ s).any fun e => decide (d e.2 < d s)

/-! ### Soundness of the checker -/

variable {E} {cmp}

theorem mem_of_reachable {t : BTree S} {s₀ s : S} (h₀ : s₀ ∈ t.toList)
    (hc : E.closedB cmp t = true) (hr : E.toLTS.Reachable s₀ s) : s ∈ t.toList := by
  refine hr.invariant h₀ fun s l s' hs hst => ?_
  simp only [closedB, BTree.all_eq_true, List.all_eq_true] at hc
  exact BTree.mem_toList_of_find (hc s hs (l, s') hst)

theorem step_mem {t : BTree S} (hc : E.closedB cmp t = true) {s s' : S} {l : L}
    (hs : s ∈ t.toList) (hst : E.toLTS.step s l s') : s' ∈ t.toList :=
  mem_of_reachable hs hc (LTS.Reachable.of_step hst)

theorem deadlockFree_of_check {t : BTree S} {s₀ : S} (h₀ : t.find cmp s₀ = true)
    (hc : E.closedB cmp t = true) (hd : E.noDeadlockB t = true) :
    E.toLTS.DeadlockFree s₀ := by
  refine LTS.DeadlockFree.of_invariant (· ∈ t.toList) (BTree.mem_toList_of_find h₀)
    (fun s l s' hs hst => step_mem hc hs hst) fun s hs => ?_
  simp only [noDeadlockB, BTree.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_eq_false_iff] at hd
  obtain ⟨⟨l, s'⟩, hmem⟩ := List.exists_mem_of_ne_nil _ (hd s hs)
  exact ⟨l, s', hmem⟩

theorem livelockFree_of_check {t : BTree S} {s₀ : S} {internal : L → Bool} {rank : S → ℕ}
    (h₀ : t.find cmp s₀ = true) (hc : E.closedB cmp t = true)
    (hr : E.rankDecreasesB internal rank t = true) :
    E.toLTS.LivelockFree (fun l => internal l = true) s₀ := by
  refine LTS.LivelockFree.of_ranking (· ∈ t.toList) (BTree.mem_toList_of_find h₀)
    (fun s l s' hs hst => step_mem hc hs hst) rank fun s l s' hs hl hst => ?_
  simp only [rankDecreasesB, BTree.all_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hr
  rcases hr s hs (l, s') hst with h | h
  · simp [h] at hl
  · exact h

omit [DecidableEq S] in
theorem enabledB_iff [DecidableEq L] {s : S} {l : L} :
    E.enabledB s l = true ↔ E.toLTS.Enabled s l := by
  simp only [enabledB, List.any_eq_true, decide_eq_true_eq, LTS.Enabled, toLTS]
  constructor
  · rintro ⟨⟨l', s'⟩, hmem, rfl⟩; exact ⟨s', hmem⟩
  · rintro ⟨s', hmem⟩; exact ⟨(l, s'), hmem, rfl⟩

theorem liveLabel_of_check [DecidableEq L] {t : BTree S} {s₀ : S} {l : L} {d : S → ℕ}
    (h₀ : t.find cmp s₀ = true) (hc : E.closedB cmp t = true)
    (hp : E.progressB l d t = true) : E.toLTS.LiveLabel s₀ l := by
  refine LTS.LiveLabel.of_ranking (· ∈ t.toList) (BTree.mem_toList_of_find h₀)
    (fun s l s' hs hst => step_mem hc hs hst) l d fun s hs => ?_
  simp only [progressB, BTree.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq] at hp
  rcases hp s hs with h | ⟨⟨l', s'⟩, hmem, hlt⟩
  · exact Or.inl (enabledB_iff.1 h)
  · exact Or.inr ⟨l', s', hmem, hlt⟩

end Checker

/-! ### Untrusted certificate generation

Nothing below needs to be correct for the results to be sound; a wrong answer merely makes
the check fail. -/

section Search

variable [DecidableEq S] (cmp : S → S → Ordering)

/-- Depth-first exploration; `fuel` bounds the number of expanded states. -/
def exploreAux : ℕ → List S → BStore S → BStore S
  | 0, _, visited => visited
  | _ + 1, [], visited => visited
  | fuel + 1, s :: stack, visited =>
    let r := (E.succ s).foldl
      (fun (acc : List S × BStore S) e =>
        if acc.2.tree.find cmp e.2 then acc else (e.2 :: acc.1, acc.2.push cmp e.2))
      (stack, visited)
    exploreAux fuel r.1 r.2

/-- Candidate reachable state space from `s₀`, as a balanced search tree. -/
def explore (fuel : ℕ) (s₀ : S) : BTree S :=
  (E.exploreAux cmp fuel [s₀] (({} : BStore S).push cmp s₀)).tree.rebalance

/-- Longest internal path from `s` (memoised depth-first search, bounded by `fuel`). -/
def heightAux (internal : L → Bool) : ℕ → BStore (S × ℕ) → S → ℕ × BStore (S × ℕ)
  | 0, memo, _ => (0, memo)
  | fuel + 1, memo, s =>
    match memo.tree.lookup cmp s with
    | some h => (h, memo)
    | none =>
      let r := (E.succ s).foldl
        (fun (acc : ℕ × BStore (S × ℕ)) e =>
          if internal e.1 then
            let r' := heightAux internal fuel acc.2 e.2
            (max acc.1 (r'.1 + 1), r'.2)
          else acc)
        (0, memo)
      (r.1, r.2.pushKV cmp s r.1)

/-- Candidate ranking function for livelock freedom: the length of the longest internal
path from each state, as a lookup tree. -/
def autoRank (internal : L → Bool) (t : BTree S) : BTree (S × ℕ) :=
  let states := t.toListAcc []
  (states.foldl (fun memo s => (E.heightAux cmp internal (states.length + 1) memo s).2)
    ({} : BStore (S × ℕ))).tree.rebalance

/-- Backward breadth-first layering of `states` by distance to a state enabling `l`. -/
def distAux (states : List S) : ℕ → ℕ → BStore (S × ℕ) → BTree S → BStore (S × ℕ)
  | 0, _, tbl, _ => tbl
  | fuel + 1, k, tbl, layer =>
    let next := states.filter fun s =>
      (tbl.tree.lookup cmp s).isNone && (E.succ s).any fun e => layer.find cmp e.2
    if next.isEmpty then tbl
    else distAux states fuel (k + 1)
      (next.foldl (fun tb s => tb.pushKV cmp s (k + 1)) tbl) (BTree.ofList next)

/-- Candidate distance function for liveness of `l`, as a lookup tree. -/
def autoDist [DecidableEq L] (l : L) (t : BTree S) : BTree (S × ℕ) :=
  let states := t.toListAcc []
  let layer0 := states.filter fun s => E.enabledB s l
  (E.distAux cmp states states.length 0
    (layer0.foldl (fun tb s => tb.pushKV cmp s 0) {}) (BTree.ofList layer0)).tree.rebalance

end Search

/-- Read a lookup tree as a function (missing entries map to `0`). -/
def tblFn (cmp : S → S → Ordering) (tbl : BTree (S × ℕ)) (s : S) : ℕ :=
  (tbl.lookup cmp s).getD 0

/-! ### One-shot checks

These combine the untrusted search with the trusted checker; a `true` result is turned into
a proof by the corresponding `of_check*` theorem. -/

section OneShot

variable [DecidableEq S] (cmp : S → S → Ordering)

/-- Explore from `s₀` and check deadlock freedom. -/
def checkDeadlockFree (fuel : ℕ) (s₀ : S) : Bool :=
  let t := E.explore cmp fuel s₀
  t.find cmp s₀ && E.closedB cmp t && E.noDeadlockB t

/-- Explore from `s₀` and check livelock freedom with an automatically computed ranking. -/
def checkLivelockFree (internal : L → Bool) (fuel : ℕ) (s₀ : S) : Bool :=
  let t := E.explore cmp fuel s₀
  t.find cmp s₀ && E.closedB cmp t &&
    E.rankDecreasesB internal (tblFn cmp (E.autoRank cmp internal t)) t

/-- Explore from `s₀` and check liveness of all the given labels. -/
def checkLive [DecidableEq L] (labels : List L) (fuel : ℕ) (s₀ : S) : Bool :=
  let t := E.explore cmp fuel s₀
  t.find cmp s₀ && E.closedB cmp t &&
    labels.all fun l => E.progressB l (tblFn cmp (E.autoDist cmp l t)) t

/-- Explore once and check deadlock freedom, livelock freedom and liveness together. -/
def checkAll [DecidableEq L] (internal : L → Bool) (labels : List L) (fuel : ℕ) (s₀ : S) :
    Bool :=
  let t := E.explore cmp fuel s₀
  t.find cmp s₀ && E.closedB cmp t && E.noDeadlockB t &&
    E.rankDecreasesB internal (tblFn cmp (E.autoRank cmp internal t)) t &&
    labels.all fun l => E.progressB l (tblFn cmp (E.autoDist cmp l t)) t

variable {E} {cmp}

theorem deadlockFree_of_checkDeadlockFree {fuel : ℕ} {s₀ : S}
    (h : E.checkDeadlockFree cmp fuel s₀ = true) : E.toLTS.DeadlockFree s₀ := by
  simp only [checkDeadlockFree, Bool.and_eq_true] at h
  exact deadlockFree_of_check h.1.1 h.1.2 h.2

theorem livelockFree_of_checkLivelockFree {internal : L → Bool} {fuel : ℕ} {s₀ : S}
    (h : E.checkLivelockFree cmp internal fuel s₀ = true) :
    E.toLTS.LivelockFree (fun l => internal l = true) s₀ := by
  simp only [checkLivelockFree, Bool.and_eq_true] at h
  exact livelockFree_of_check h.1.1 h.1.2 h.2

theorem live_of_checkLive [DecidableEq L] {labels : List L} (hl : ∀ l, l ∈ labels)
    {fuel : ℕ} {s₀ : S} (h : E.checkLive cmp labels fuel s₀ = true) : E.toLTS.Live s₀ := by
  simp only [checkLive, Bool.and_eq_true, List.all_eq_true] at h
  exact fun l => liveLabel_of_check h.1.1 h.1.2 (h.2 l (hl l))

/-- The combined check proves all three properties at once. -/
theorem of_checkAll [DecidableEq L] {internal : L → Bool} {labels : List L}
    (hl : ∀ l, l ∈ labels) {fuel : ℕ} {s₀ : S}
    (h : E.checkAll cmp internal labels fuel s₀ = true) :
    E.toLTS.DeadlockFree s₀ ∧ E.toLTS.LivelockFree (fun l => internal l = true) s₀ ∧
      E.toLTS.Live s₀ := by
  simp only [checkAll, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h₀, hc⟩, hd⟩, hr⟩, hp⟩ := h
  exact ⟨deadlockFree_of_check h₀ hc hd, livelockFree_of_check h₀ hc hr,
    fun l => liveLabel_of_check h₀ hc (hp l (hl l))⟩

end OneShot

/-! ### Verified refutation: counterexample traces -/

section Refute

variable [DecidableEq S] [DecidableEq L]

/-- Follow an explicit trace of `(label, state)` pairs, checking each step. -/
def followB : S → List (L × S) → Option S
  | s, [] => some s
  | s, (l, s') :: rest => if (E.succ s).contains (l, s') then followB s' rest else none

variable {E}

theorem path_of_followB {s s' : S} {tr : List (L × S)} (h : E.followB s tr = some s') :
    E.toLTS.Path s (tr.map Prod.fst) s' := by
  induction tr generalizing s with
  | nil => cases h; exact LTS.Path.nil _
  | cons e rest ih =>
    obtain ⟨l, s''⟩ := e
    simp only [followB] at h
    split_ifs at h with hmem
    rw [List.contains_iff_mem] at hmem
    exact LTS.Path.cons hmem (ih h)

theorem transGen_of_followB {internal : L → Bool} {s s' : S} {e : L × S} {tr : List (L × S)}
    (h : E.followB s (e :: tr) = some s') (hint : ((e :: tr).all fun e => internal e.1) = true) :
    Relation.TransGen (E.toLTS.IStep fun l => internal l = true) s s' := by
  induction tr generalizing s e with
  | nil =>
    obtain ⟨l, s''⟩ := e
    simp only [followB] at h
    split_ifs at h with hmem
    cases h
    rw [List.contains_iff_mem] at hmem
    simp only [List.all_cons, List.all_nil, Bool.and_true] at hint
    exact Relation.TransGen.single ⟨l, hint, hmem⟩
  | cons e' rest ih =>
    obtain ⟨l, s''⟩ := e
    rw [followB] at h
    split_ifs at h with hmem
    rw [List.contains_iff_mem] at hmem
    simp only [List.all_cons, Bool.and_eq_true] at hint ih
    exact Relation.TransGen.head ⟨l, hint.1, hmem⟩ (ih h hint.2)

/-- **Deadlock counterexample**: a checked trace to a state without successors. -/
theorem not_deadlockFree_of_trace {s₀ s : S} {tr : List (L × S)}
    (h : E.followB s₀ tr = some s) (hd : (E.succ s).isEmpty = true) :
    ¬ E.toLTS.DeadlockFree s₀ := by
  refine LTS.not_deadlockFree_of_path (path_of_followB h) fun l s' hst => ?_
  rw [List.isEmpty_iff] at hd
  change (l, s') ∈ E.succ s at hst
  simp [hd] at hst

/-- **Livelock counterexample**: a checked trace to a state lying on a non-empty cycle of
internal steps. -/
theorem not_livelockFree_of_trace {internal : L → Bool} {s₀ s : S} {tr : List (L × S)}
    {e : L × S} {cyc : List (L × S)} (h : E.followB s₀ tr = some s)
    (hc : E.followB s (e :: cyc) = some s) (hint : ((e :: cyc).all fun e => internal e.1) = true) :
    ¬ E.toLTS.LivelockFree (fun l => internal l = true) s₀ :=
  LTS.not_livelockFree_of_cycle (path_of_followB h).reachable (transGen_of_followB hc hint)

variable (E) (cmp : S → S → Ordering)

/-- Explore from `s` and check that `l` is never enabled. -/
def checkNeverEnabled (l : L) (fuel : ℕ) (s : S) : Bool :=
  let t := E.explore cmp fuel s
  t.find cmp s && E.closedB cmp t && t.all fun x => !E.enabledB x l

variable {E} {cmp}

/-- **Liveness counterexample**: a checked trace to a state from which `l` can never be
enabled again. -/
theorem not_liveLabel_of_trace {l : L} {fuel : ℕ} {s₀ s : S} {tr : List (L × S)}
    (h : E.followB s₀ tr = some s) (hn : E.checkNeverEnabled cmp l fuel s = true) :
    ¬ E.toLTS.LiveLabel s₀ l := by
  simp only [checkNeverEnabled, Bool.and_eq_true, BTree.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hn
  obtain ⟨⟨h₀, hc⟩, hne⟩ := hn
  refine LTS.not_liveLabel_of_dead (path_of_followB h).reachable fun s' hr hen => ?_
  have := hne s' (mem_of_reachable (BTree.mem_toList_of_find h₀) hc hr)
  rw [← Bool.not_eq_true, enabledB_iff] at this
  exact this hen

end Refute

end ExplicitLTS

end AsyncLean
