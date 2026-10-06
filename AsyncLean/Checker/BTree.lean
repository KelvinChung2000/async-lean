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

/-- Map lookup confirmed by decidable equality on the key. -/
def findData [DecidableEq α] (cmp : α → α → Ordering) (a : α) : BTree (α × β) → Option β
  | leaf => none
  | node l x r =>
    match cmp a x.1 with
    | .lt => findData cmp a l
    | .gt => findData cmp a r
    | .eq => if a = x.1 then some x.2 else none

/-- **Soundness of map lookup**: whatever the comparison function, a found entry is stored in
the tree. -/
theorem mem_toList_of_findData [DecidableEq α] {cmp : α → α → Ordering} {a : α} {b : β}
    {t : BTree (α × β)} (h : t.findData cmp a = some b) : (a, b) ∈ t.toList := by
  induction t with
  | leaf => simp [findData] at h
  | node l x r ihl ihr =>
    simp only [toList, List.mem_append, List.mem_cons]
    simp only [findData] at h
    split at h
    · exact Or.inl (ihl h)
    · exact Or.inr (Or.inr (ihr h))
    · split_ifs at h with hax
      cases h
      exact Or.inr (Or.inl (by rw [hax]))

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

/-- An AVL tree: the balanced search tree used by the untrusted searches (insertion in any
order, e.g. sorted, stays logarithmic). -/
inductive AVL (α : Type*) where
  | leaf : AVL α
  | node (h : ℕ) (l : AVL α) (x : α) (r : AVL α) : AVL α
  deriving Inhabited

namespace AVL

variable {α β : Type*}

/-- Height. -/
def height : AVL α → ℕ
  | leaf => 0
  | node h _ _ _ => h

/-- Node with its height. -/
def mk (l : AVL α) (x : α) (r : AVL α) : AVL α := node (max l.height r.height + 1) l x r

/-- Restore the balance at a node whose subtrees differ in height by at most two. -/
def balance (l : AVL α) (x : α) (r : AVL α) : AVL α :=
  if l.height > r.height + 1 then
    match l with
    | node _ ll lx lr =>
      if ll.height ≥ lr.height then mk ll lx (mk lr x r)
      else match lr with
        | node _ lrl lrx lrr => mk (mk ll lx lrl) lrx (mk lrr x r)
        | leaf => mk l x r
    | leaf => mk l x r
  else if r.height > l.height + 1 then
    match r with
    | node _ rl rx rr =>
      if rr.height ≥ rl.height then mk (mk l x rl) rx rr
      else match rl with
        | node _ rll rlx rlr => mk (mk l x rll) rlx (mk rlr rx rr)
        | leaf => mk l x r
    | leaf => mk l x r
  else mk l x r

/-- Insertion (no-op if an element comparing equal is present). -/
def insert (cmp : α → α → Ordering) (a : α) : AVL α → AVL α
  | leaf => node 1 leaf a leaf
  | node h l x r =>
    match cmp a x with
    | .lt => balance (insert cmp a l) x r
    | .gt => balance l x (insert cmp a r)
    | .eq => node h l x r

/-- Map insertion, comparing on keys (overwrites). -/
def insertKV (cmp : α → α → Ordering) (a : α) (b : β) : AVL (α × β) → AVL (α × β)
  | leaf => node 1 leaf (a, b) leaf
  | node h l x r =>
    match cmp a x.1 with
    | .lt => balance (insertKV cmp a b l) x r
    | .gt => balance l x (insertKV cmp a b r)
    | .eq => node h l (a, b) r

/-- Membership, by the comparison. -/
def mem (cmp : α → α → Ordering) (a : α) : AVL α → Bool
  | leaf => false
  | node _ l x r =>
    match cmp a x with
    | .lt => mem cmp a l
    | .gt => mem cmp a r
    | .eq => true

/-- Map lookup, by the comparison on keys. -/
def lookup (cmp : α → α → Ordering) (a : α) : AVL (α × β) → Option β
  | leaf => none
  | node _ l x r =>
    match cmp a x.1 with
    | .lt => lookup cmp a l
    | .gt => lookup cmp a r
    | .eq => some x.2

/-- The same (balanced) tree as a `BTree`. -/
def toBTree : AVL α → BTree α
  | leaf => .leaf
  | node _ l x r => .node l.toBTree x r.toBTree

end AVL

/-- A growing set or map used by the untrusted searches. -/
structure BStore (α : Type*) where
  /-- The elements. -/
  avl : AVL α := .leaf

namespace BStore

variable {α β : Type*}

/-- Insert an element. -/
def push (cmp : α → α → Ordering) (s : BStore α) (a : α) : BStore α := ⟨s.avl.insert cmp a⟩

/-- Insert or overwrite a key–value pair. -/
def pushKV (cmp : α → α → Ordering) (s : BStore (α × β)) (a : α) (b : β) : BStore (α × β) :=
  ⟨s.avl.insertKV cmp a b⟩

/-- Membership. -/
def find (cmp : α → α → Ordering) (s : BStore α) (a : α) : Bool := s.avl.mem cmp a

/-- Lookup. -/
def lookup (cmp : α → α → Ordering) (s : BStore (α × β)) (a : α) : Option β :=
  s.avl.lookup cmp a

/-- The contents as a balanced `BTree`. -/
def tree (s : BStore α) : BTree α := s.avl.toBTree

end BStore

/-- Lexicographic comparison of lists of naturals (the default state order).  Written with
`Nat.blt` / `Nat.beq`, which the kernel evaluates natively. -/
def lexCmp : List ℕ → List ℕ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match Nat.blt a b with
    | true => .lt
    | false =>
      match Nat.beq a b with
      | true => lexCmp as bs
      | false => .gt

/-- Comparison of explicit states used to organise search trees.  Any function is sound (see
`BTree.mem_toList_of_find`); a total order makes the search efficient. -/
class StateOrd (S : Type*) where
  /-- The comparison function. -/
  cmp : S → S → Ordering

/-- Comparison of naturals with the kernel-native `Nat.blt` / `Nat.beq`. -/
def natCmp (a b : ℕ) : Ordering :=
  match Nat.blt a b with
  | true => .lt
  | false => match Nat.beq a b with
    | true => .eq
    | false => .gt

instance : StateOrd ℕ := ⟨natCmp⟩
instance : StateOrd (List ℕ) := ⟨lexCmp⟩

instance {S S' : Type*} [StateOrd S] [StateOrd S'] : StateOrd (S × S') :=
  ⟨fun a b => match StateOrd.cmp a.1 b.1 with
    | .eq => StateOrd.cmp a.2 b.2
    | o => o⟩

end AsyncLean
