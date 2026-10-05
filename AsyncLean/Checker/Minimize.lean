/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Quotient

/-!
# Computing quotient certificates (untrusted)

`ExplicitLTS.mkQuot` minimises a component modulo branching bisimulation by signature
refinement, and produces the quotient table together with a certificate for
`ExplicitLTS.checkQuot`.  Nothing here is verified: the kernel re-checks the certificate.
-/

namespace AsyncLean

namespace ExplicitLTS

variable {S L : Type*} (E : ExplicitLTS S L) [DecidableEq S] [DecidableEq L]
  (cmp : S → S → Ordering)

/-- The result of minimisation. -/
structure QuotResult (S L : Type*) where
  /-- The quotient table. -/
  q : BTree (ℕ × List (L × ℕ))
  /-- The certificate. -/
  cert : InvCert S QData
  /-- Class of the initial state. -/
  init : ℕ
  /-- Number of states of the component. -/
  states : ℕ
  /-- Number of classes. -/
  classes : ℕ

private def setEq {α : Type*} [DecidableEq α] (a b : List α) : Bool :=
  a.all (· ∈ b) && b.all (· ∈ a)

private def union {α : Type*} [DecidableEq α] (a b : List α) : List α :=
  a ++ b.filter (· ∉ a)

/-- Iterate a function `n` times. -/
private def iter {α : Type*} : ℕ → (α → α) → α → α
  | 0, _, a => a
  | n + 1, f, a => iter n f (f a)

/-- Minimise `E` from `s₀` (untrusted). -/
def mkQuot (internal : L → Bool) (fuel : ℕ) (s₀ : S) : QuotResult S L :=
  let states : Array S := ((E.explore cmp fuel s₀).toListAcc []).toArray
  let n := states.size
  let idxTree : BTree (S × ℕ) := BTree.ofList (states.toList.zip (List.range n))
  let idx (s : S) : ℕ := (idxTree.lookup cmp s).getD 0
  let succs : Array (List (L × ℕ)) := states.map fun s => (E.succ s).map fun e => (e.1, idx e.2)
  -- inert steps: internal steps inside the class
  let inert (cls : Array ℕ) (i : ℕ) (e : L × ℕ) : Bool :=
    internal e.1 && cls.getD i 0 == cls.getD e.2 0
  -- signatures: visible / class-changing moves reachable by inert steps
  let sigs (cls : Array ℕ) : Array (List (L × ℕ)) :=
    let direct : Array (List (L × ℕ)) := (Array.range n).map fun i =>
      ((succs.getD i []).filter fun e => !inert cls i e).map fun e => (e.1, cls.getD e.2 0)
    iter n (fun (sg : Array (List (L × ℕ))) => (Array.range n).map fun i =>
      ((succs.getD i []).filter (inert cls i)).foldl (fun acc e => union acc (sg.getD e.2 []))
        (direct.getD i [])) direct
  -- one refinement round: new class = (old class, signature)
  let refine (cls : Array ℕ) : Array ℕ :=
    let sg := sigs cls
    let r := (Array.range n).foldl (fun (acc : Array (ℕ × List (L × ℕ)) × Array ℕ) i =>
      let key := (cls.getD i 0, sg.getD i [])
      match acc.1.findIdx? fun k => k.1 == key.1 && setEq k.2 key.2 with
      | some j => (acc.1, acc.2.push j)
      | none => (acc.1.push key, acc.2.push acc.1.size)) (#[], #[])
    r.2
  let count (cls : Array ℕ) : ℕ := (cls.foldl (fun m c => max m (c + 1)) 0)
  let rec loop : ℕ → Array ℕ → Array ℕ
    | 0, cls => cls
    | k + 1, cls =>
      let cls' := refine cls
      if count cls' == count cls then cls' else loop k cls'
  let cls := loop (n + 1) (Array.replicate n 0)
  let nc := count cls
  let sg := sigs cls
  -- quotient edges of each class: the signature of its first member
  let edges : Array (List (L × ℕ)) := (Array.range nc).map fun c =>
    match (Array.range n).find? (fun i => cls.getD i 0 == c) with
    | some i => sg.getD i []
    | none => []
  -- ranks: longest inert path
  let rank : Array ℕ := iter n (fun (rk : Array ℕ) => (Array.range n).map fun i =>
    ((succs.getD i []).filter (inert cls i)).foldl (fun m e => max m (rk.getD e.2 0 + 1)) 0)
    (Array.replicate n 0)
  -- distances to each exit of the class
  let dists : Array (List ℕ) :=
    let direct (i : ℕ) (ex : L × ℕ) : Bool :=
      (succs.getD i []).any fun e => !inert cls i e && e.1 == ex.1 && cls.getD e.2 0 == ex.2
    let init : Array (List ℕ) := (Array.range n).map fun i =>
      (edges.getD (cls.getD i 0) []).map fun ex => if direct i ex then 0 else n + 1
    iter n (fun (d : Array (List ℕ)) => (Array.range n).map fun i =>
      ((edges.getD (cls.getD i 0) []).zip (List.range (edges.getD (cls.getD i 0) []).length)).map
        fun exk =>
          let own := (d.getD i []).getD exk.2 (n + 1)
          ((succs.getD i []).filter (inert cls i)).foldl
            (fun m e => min m ((d.getD e.2 []).getD exk.2 (n + 1) + 1)) own) init
  let entries := (List.range n).map fun i =>
    (states.getD i s₀, ((E.succ (states.getD i s₀)).map Prod.snd,
      (cls.getD i 0, rank.getD i 0, dists.getD i [])))
  { q := BTree.ofList ((List.range nc).map fun c => (c, edges.getD c []))
    cert := BTree.ofList entries
    init := cls.getD (idx s₀) 0
    states := n
    classes := nc }

end ExplicitLTS

end AsyncLean
