/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Explicit

/-!
# Counterexample search (untrusted)

When a design fails a check, these functions search for a counterexample — a trace to a
deadlock, a reachable internal cycle, a label that becomes permanently disabled, or a
persistence violation.  They are *not* verified: their output is meant to be fed to the
refutation theorems (`not_deadlockFree_of_refuteB`, …), which re-check it in the kernel.
They are executed by the tactics of `AsyncLean.Checker.Tactic` (in compiled code).
-/

namespace AsyncLean

namespace ExplicitLTS

variable {S L : Type*} (E : ExplicitLTS S L) [DecidableEq S] (cmp : S → S → Ordering)

/-- Breadth-first search recording, for each reached state, a shortest path from `s₀`
(as a reversed list of labels).  Returns the states in BFS order. -/
def bfsPathsAux : ℕ → List S → List S → BStore (S × List L) → List (S × List L)
  | 0, _, _, _ => []
  | _ + 1, [], [], _ => []
  | fuel + 1, [], next, seen => bfsPathsAux fuel next.reverse [] seen
  | fuel + 1, s :: queue, next, seen =>
    let p := (seen.tree.lookup cmp s).getD []
    let r := (E.succ s).foldl
      (fun (acc : List S × BStore (S × List L)) e =>
        if (acc.2.tree.lookup cmp e.2).isSome then acc
        else (e.2 :: acc.1, acc.2.pushKV cmp e.2 (e.1 :: p)))
      (next, seen)
    (s, p) :: bfsPathsAux fuel queue r.1 r.2

/-- All reachable states with a shortest path (labels in order) from `s₀`. -/
def bfsPaths (fuel : ℕ) (s₀ : S) : List (S × List L) :=
  (E.bfsPathsAux cmp fuel [s₀] [] (({} : BStore (S × List L)).pushKV cmp s₀ [])).map
    fun p => (p.1, p.2.reverse)

/-- A shortest trace to a deadlock, if any is found. -/
def findDeadlock (fuel : ℕ) (s₀ : S) : Option (List L) :=
  ((E.bfsPaths cmp fuel s₀).find? fun p => (E.succ p.1).isEmpty).map Prod.snd

/-- A non-empty internal path from `s` back to `s` (breadth-first, bounded by `fuel`). -/
def findInternalCycleFrom (internal : L → Bool) (fuel : ℕ) (s : S) : Option (List L) :=
  let E' : ExplicitLTS S L := ⟨fun x => (E.succ x).filter fun e => internal e.1⟩
  -- paths from the internal successors of `s`
  (E'.succ s).findSome? fun e =>
    if e.2 = s then some [e.1]
    else ((E'.bfsPaths cmp fuel e.2).find? fun p => (E'.succ p.1).any fun e' => e'.2 = s).map
      fun p => e.1 :: p.2 ++ (((E'.succ p.1).find? fun e' => e'.2 = s).map Prod.fst).toList

/-- A trace to a state on an internal cycle, together with the cycle. -/
def findLivelock (internal : L → Bool) (fuel : ℕ) (s₀ : S) : Option (List L × List L) :=
  (E.bfsPaths cmp fuel s₀).findSome? fun p =>
    (E.findInternalCycleFrom cmp internal fuel p.1).map fun c => (p.2, c)

/-- A trace to a state from which `l` can never be enabled again. -/
def findDeadLabel [DecidableEq L] (fuel : ℕ) (s₀ : S) (l : L) : Option (List L) :=
  ((E.bfsPaths cmp fuel s₀).find? fun p =>
    (E.bfsPaths cmp fuel p.1).all fun q => !E.enabledB q.1 l).map Prod.snd

/-- A trace to a state where performing `l'` disables `l`, with `l` and `l'`. -/
def findNonPersistent [DecidableEq L] (fuel : ℕ) (s₀ : S) : Option (List L × L × L) :=
  (E.bfsPaths cmp fuel s₀).findSome? fun p =>
    (E.succ p.1).findSome? fun e => (E.succ p.1).findSome? fun e' =>
      if e.1 ≠ e'.1 ∧ !E.enabledB e'.2 e.1 then some (p.2, e.1, e'.1) else none

/-- Compute a home-state certificate (untrusted): ranks, distances back to `s₀`, and for each
label a shortest trace of states to a state enabling it. -/
def mkCertHome [DecidableEq L] (internal : L → Bool) (labels : List L) (fuel : ℕ) (s₀ : S) :
    HomeCert S :=
  let t := E.explore cmp fuel s₀
  let rk := E.autoRank cmp internal t
  let states := t.toListAcc []
  let home := (E.distAux cmp states states.length 0
    (({} : BStore (S × ℕ)).pushKV cmp s₀ 0) (BTree.ofList [s₀])).tree.rebalance
  let tree := BTree.ofList (states.map fun s =>
    (s, (tblFn cmp rk s, tblFn cmp home s, (E.succ s).map Prod.snd)))
  let paths := E.bfsPaths cmp fuel s₀
  let traces := labels.map fun l =>
    match paths.find? (fun p => E.enabledB p.1 l) with
    | some p => (E.labelTrace s₀ p.2).map Prod.snd
    | none => []
  (tree, traces)

end ExplicitLTS

end AsyncLean
