/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.WellFounded

/-!
# Binary search trees for the kernel-evaluated checker

A minimal binary tree used as a set / map of explored states.  Everything here is written
with structural recursion only, so that it evaluates efficiently in the Lean kernel (used by
`decide +kernel`).

Crucially, the soundness of the model checker only needs *one* fact about these trees:
if `find` reports a state, then the state is stored in the tree (`mem_toList_of_find`).
That holds for **any** tree and **any** comparison function, because `find` confirms with a
decidable equality test.  The search-tree ordering and balance invariants are therefore
purely a matter of performance and need no proof.
-/

namespace AsyncLean

/-- A binary tree with values at the nodes. -/
inductive BTree (α : Type*) where
  | leaf : BTree α
  | node (l : BTree α) (x : α) (r : BTree α) : BTree α
  deriving Inhabited

namespace BTree

variable {α β : Type*}

/-- In-order list of the elements. -/
def toList : BTree α → List α
  | leaf => []
  | node l x r => l.toList ++ x :: r.toList

/-- `p` holds at every node. -/
def all (p : α → Bool) : BTree α → Bool
  | leaf => true
  | node l x r => p x && l.all p && r.all p

@[simp] theorem all_eq_true {p : α → Bool} {t : BTree α} :
    t.all p = true ↔ ∀ x ∈ t.toList, p x = true := by
  induction t with
  | leaf => simp [all, toList]
  | node l x r ihl ihr =>
    simp only [all, Bool.and_eq_true, ihl, ihr, toList, List.mem_append, List.mem_cons]
    constructor
    · rintro ⟨⟨hx, hl⟩, hr⟩ y (hy | rfl | hy)
      · exact hl y hy
      · exact hx
      · exact hr y hy
    · intro h
      exact ⟨⟨h x (Or.inr (Or.inl rfl)), fun y hy => h y (Or.inl hy)⟩,
        fun y hy => h y (Or.inr (Or.inr hy))⟩

/-- Search guided by `cmp`, confirmed by decidable equality. -/
def find [DecidableEq α] (cmp : α → α → Ordering) (a : α) : BTree α → Bool
  | leaf => false
  | node l x r =>
    match cmp a x with
    | .lt => find cmp a l
    | .gt => find cmp a r
    | .eq => decide (a = x)

/-- **Soundness of search**: whatever the comparison function, a found element is stored
in the tree. -/
theorem mem_toList_of_find [DecidableEq α] {cmp : α → α → Ordering} {a : α} {t : BTree α}
    (h : t.find cmp a = true) : a ∈ t.toList := by
  induction t with
  | leaf => simp [find] at h
  | node l x r ihl ihr =>
    simp only [toList, List.mem_append, List.mem_cons]
    simp only [find] at h
    split at h
    · exact Or.inl (ihl h)
    · exact Or.inr (Or.inr (ihr h))
    · exact Or.inr (Or.inl (of_decide_eq_true h))

/-- Map lookup: the tree stores key–value pairs, compared on keys. -/
def lookup (cmp : α → α → Ordering) (a : α) : BTree (α × β) → Option β
  | leaf => none
  | node l x r =>
    match cmp a x.1 with
    | .lt => lookup cmp a l
    | .gt => lookup cmp a r
    | .eq => some x.2

/-- Insertion (no-op if an element comparing equal is present). -/
def insert (cmp : α → α → Ordering) (a : α) : BTree α → BTree α
  | leaf => node leaf a leaf
  | node l x r =>
    match cmp a x with
    | .lt => node (insert cmp a l) x r
    | .gt => node l x (insert cmp a r)
    | .eq => node l x r

/-- Map insertion, comparing on keys (overwrites). -/
def insertKV (cmp : α → α → Ordering) (a : α) (b : β) : BTree (α × β) → BTree (α × β)
  | leaf => node leaf (a, b) leaf
  | node l x r =>
    match cmp a x.1 with
    | .lt => node (insertKV cmp a b l) x r
    | .gt => node l x (insertKV cmp a b r)
    | .eq => node l (a, b) r

/-- In-order traversal with an accumulator (linear time). -/
def toListAcc : BTree α → List α → List α
  | leaf, acc => acc
  | node l x r, acc => toListAcc l (x :: toListAcc r acc)

/-- Balanced tree from a list (in order), by repeated halving; `fuel` bounds the depth. -/
def ofListAux : ℕ → List α → BTree α
  | 0, _ => leaf
  | _ + 1, [] => leaf
  | fuel + 1, l@(_ :: _) =>
    let m := l.length / 2
    match l.drop m with
    | [] => leaf
    | x :: rest => node (ofListAux fuel (l.take m)) x (ofListAux fuel rest)

/-- Balanced tree with the elements of `l` in order. -/
def ofList (l : List α) : BTree α := ofListAux (l.length + 1) l

/-- Rebalance a tree. -/
def rebalance (t : BTree α) : BTree α := ofList (t.toListAcc [])

end BTree

/-- A tree together with its size and a rebalancing threshold: inserting keeps the tree
balanced up to a constant factor in amortised `O(log n)` time. -/
structure BStore (α : Type*) where
  tree : BTree α := .leaf
  size : ℕ := 0
  cap : ℕ := 8

namespace BStore

variable {α β : Type*}

/-- Insert a new element (the caller ensures it is new); rebalance when the size doubles. -/
def push (cmp : α → α → Ordering) (s : BStore α) (a : α) : BStore α :=
  let t := s.tree.insert cmp a
  if s.size + 1 < s.cap then { tree := t, size := s.size + 1, cap := s.cap }
  else { tree := t.rebalance, size := s.size + 1, cap := 2 * s.cap }

/-- Insert or overwrite a key–value pair. -/
def pushKV (cmp : α → α → Ordering) (s : BStore (α × β)) (a : α) (b : β) : BStore (α × β) :=
  let t := s.tree.insertKV cmp a b
  if s.size + 1 < s.cap then { tree := t, size := s.size + 1, cap := s.cap }
  else { tree := t.rebalance, size := s.size + 1, cap := 2 * s.cap }

end BStore

/-- Lexicographic comparison of lists of naturals (the default state order). -/
def lexCmp : List ℕ → List ℕ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if a = b then lexCmp as bs else .gt

end AsyncLean
