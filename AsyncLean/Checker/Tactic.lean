/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Petri
import AsyncLean.Checker.Diagnose
import AsyncLean.Circuit.Basic
import AsyncLean.Circuit.Wires
import AsyncLean.Circuit.Packed
import AsyncLean.Stg.Concrete
import AsyncLean.Checker.Minimize
import AsyncLean.Checker.Packed
import AsyncLean.Checker.Abstract
import AsyncLean.Checker.FastPetri
import AsyncLean.Checker.FastPOR
import AsyncLean.Checker.FastPORLive
import AsyncLean.Checker.BDDGen
import AsyncLean.Checker.BitmapGen
import AsyncLean.Checker.AbstractPot
import AsyncLean.Auto.StateEq
import AsyncLean.Import.Basic
import AsyncLean.Routing.WormholeHold

/-!
# The `async_decide` tactic

`async_decide` proves, for a concrete design, goals of the form

* `N.Correct`, `N.toNet.lts.DeadlockFree N.M₀`, `N.toNet.lts.LivelockFree N.Internal N.M₀`,
  `N.toNet.lts.Live N.M₀`, `N.toNet.lts.Persistent N.M₀` for a Petri net `N : PNet`;
* `C.Correct`, `C.lts.DeadlockFree C.s₀`, `C.lts.LivelockFree C.Internal C.s₀`,
  `C.lts.Live C.s₀`, `C.SpeedIndependent` for a gate-level circuit `C : Circuit`;
* `N.Correct`, `N.DeadlockFree`, `N.LivelockFree`, `N.StarvationFree` and
  `N.WormholeCorrect`, `N.WormholeDeadlockFree`, `N.WormholeLivelockFree` for an
  interconnection network `N : Network ℕ ℕ` with dynamic routing.  No configuration of the network is explored: the
  routing function is checked locally (Dally–Seitz with the full routing function, then
  Duato with the first-listed hop of every packet as its escape channel).  `async_routing
  (escape := R₁)` names the escape subfunction explicitly.

It works in three steps:

1. **search (untrusted)** — the reachable state space, a ranking function and distance
   functions are computed by *compiled code* at elaboration time (`PNet.mkCert`);
2. **certificate** — the result is embedded in the proof as a literal term;
3. **check (trusted)** — the kernel evaluates the verified checker on the literal certificate
   (`decide +kernel`), and `PNet.correct_of_checkCert` turns the result into a proof.

Running code at elaboration time adds nothing to the trusted base: the final proof term only
contains data and a kernel-checked decision, so it depends on no axiom beyond `propext`,
`Classical.choice` and `Quot.sound` (no `Lean.ofReduceBool`, unlike `native_decide`).

If the design is incorrect, the tactic fails with a counterexample and the exact
refutation theorem that proves the negation.  `async_decide (fuel := n)` raises the bound on
the number of explored states (default `100000`).

If the state space of a Petri net does not close (it may be unbounded), the tactic checks the
net's counter abstraction instead (`AsyncLean.Checker.Abstract`), with caps just above the arc
weights; `async_decide (cap := k)` chooses the cap.
-/

namespace AsyncLean

open Lean Meta Elab Tactic

/-! ### Literal certificates -/

/-- Literal syntax tree for a `BTree`. -/
def BTree.toExprAux {α : Type} [ToExpr α] : BTree α → Expr
  | .leaf => mkApp (mkConst ``BTree.leaf [Level.zero]) (toTypeExpr α)
  | .node l x r =>
    mkApp4 (mkConst ``BTree.node [Level.zero]) (toTypeExpr α) (BTree.toExprAux l) (toExpr x)
      (BTree.toExprAux r)

instance {α : Type} [ToExpr α] : ToExpr (BTree α) where
  toTypeExpr := mkApp (mkConst ``BTree [Level.zero]) (toTypeExpr α)
  toExpr := BTree.toExprAux

/-! ### Human-readable diagnosis (untrusted) -/

namespace PNet

variable (N : PNet)

private def tname (t : Fin N.trans.length) : String :=
  let n := (N.tr t).name
  if n.isEmpty then s!"t{t.val}" else s!"{n}(#{t.val})"

/-- Search for a counterexample to `Correct` and explain how to prove its negation. -/
def diagnose (fuel : ℕ := 100000) : String :=
  let E := N.explicit
  let names (ts : List (Fin N.trans.length)) := ts.map N.tname
  let idx (ts : List (Fin N.trans.length)) := ts.map Fin.val
  if !N.wf then "the net is ill-formed: `init` must have one entry per place and every arc \
    must refer to an existing place" else
  match E.findDeadlock lexCmp fuel N.init with
  | some tr => s!"DEADLOCK reachable by firing {names tr}.\n\
      Prove it with: PNet.not_deadlockFree_of_refute (ts := {idx tr}) (by decide +kernel)"
  | none =>
  match E.findLivelock lexCmp (fun t => (N.tr t).internal) fuel N.init with
  | some (tr, cyc) => s!"LIVELOCK: after firing {names tr}, the internal transitions \
      {names cyc} can repeat forever.\n\
      Prove it with: PNet.not_livelockFree_of_refute (ts := {idx tr}) (cyc := {idx cyc}) \
      (by decide +kernel)"
  | none =>
  match (List.finRange N.trans.length).findSome? fun t =>
      (E.findDeadLabel lexCmp fuel N.init t).map fun tr => (t, tr) with
  | some (t, tr) => s!"NOT LIVE: after firing {names tr}, transition {N.tname t} can never \
      fire again.\nProve it with: PNet.not_liveLabel_of_refute (ts := {idx tr}) \
      (t := ⟨{t.val}, by decide⟩) (fuel := {fuel}) (by decide +kernel)"
  | none => s!"no counterexample found within {fuel} states; increase the fuel"

/-- Search for a counterexample to persistence. -/
def diagnosePersistent (fuel : ℕ := 100000) : String :=
  if !N.wf then "the net is ill-formed" else
  match N.explicit.findNonPersistent lexCmp fuel N.init with
  | some (tr, t, t') => s!"NOT PERSISTENT: after firing {tr.map N.tname}, firing \
      {N.tname t'} disables {N.tname t}.\nProve it with: PNet.not_persistent_of_refute \
      (ts := {tr.map Fin.val}) (t := ⟨{t.val}, by decide⟩) (t' := ⟨{t'.val}, by decide⟩) \
      (by decide +kernel)"
  | none => s!"no counterexample found within {fuel} states; increase the fuel"

end PNet

namespace Circuit

variable (C : Circuit)

private def gname (g : Fin C.gates.length) : String :=
  let n := (C.gate g).name
  if n.isEmpty then s!"g{g.val}" else s!"{n}(#{g.val})"

/-- Search for a counterexample to `Correct` and explain how to prove its negation. -/
def diagnose (fuel : ℕ := 100000) : String :=
  let E := C.explicit
  let names (gs : List (Fin C.gates.length)) := gs.map C.gname
  let idx (gs : List (Fin C.gates.length)) := gs.map Fin.val
  if !C.wf then "the circuit is ill-formed: `init` must have one entry per signal and every \
    gate must drive an existing signal" else
  match E.findDeadlock boolLexCmp fuel C.init with
  | some tr => s!"DEADLOCK (stable state) reached by firing {names tr}.\n\
      Prove it with: Circuit.not_deadlockFree_of_refute (gs := {idx tr}) (by decide +kernel)"
  | none =>
  match E.findLivelock boolLexCmp (fun g => (C.gate g).internal) fuel C.init with
  | some (tr, cyc) => s!"LIVELOCK: after firing {names tr}, the internal gates {names cyc} \
      can oscillate forever.\nProve it with: Circuit.not_livelockFree_of_refute \
      (gs := {idx tr}) (cyc := {idx cyc}) (by decide +kernel)"
  | none =>
  match (List.finRange C.gates.length).findSome? fun g =>
      (E.findDeadLabel boolLexCmp fuel C.init g).map fun tr => (g, tr) with
  | some (g, tr) => s!"NOT LIVE: after firing {names tr}, gate {C.gname g} can never switch \
      again."
  | none => s!"no counterexample found within {fuel} states; increase the fuel"

/-- Search for a hazard (violation of speed independence). -/
def diagnoseSpeedIndependent (fuel : ℕ := 100000) : String :=
  if !C.wf then "the circuit is ill-formed" else
  match C.explicit.findNonPersistent boolLexCmp fuel C.init with
  | some (tr, g, g') => s!"HAZARD: after firing {tr.map C.gname}, firing {C.gname g'} \
      disables the excited gate {C.gname g}.\nProve it with: \
      Circuit.not_speedIndependent_of_refute (gs := {tr.map Fin.val}) \
      (g := ⟨{g.val}, by decide⟩) (g' := ⟨{g'.val}, by decide⟩) (by decide +kernel)"
  | none => s!"no counterexample found within {fuel} states; increase the fuel"

end Circuit

namespace Stg

variable (N : Stg)

private def sname (z : ℕ) : String := (N.signals.getD z (s!"s{z}", .input)).1

private def ename (z : ℕ) (b : Bool) : String := N.sname z ++ (if b then "+" else "-")

private def tname (t : Fin N.net.trans.length) : String :=
  let n := (N.net.tr t).name
  let n := if n.isEmpty then
    match N.edge t with
    | some (z, b) => N.ename z b
    | none => s!"t{t.val}"
    else n
  s!"{n}(#{t.val})"

private def names (ts : List (Fin N.net.trans.length)) : List String := ts.map N.tname

/-- Search for a counterexample to `Correct`. -/
def diagnose (fuel : ℕ := 100000) : String :=
  let E := N.explicit
  if !N.wf then "the STG is ill-formed: check `init`, `initVal` (one value per signal) and that \
    every arc and edge refers to an existing place or signal" else
  let idx (ts : List (Fin N.net.trans.length)) := ts.map Fin.val
  match E.findDeadlock stateCmp fuel N.init with
  | some tr => s!"DEADLOCK reachable by firing {N.names tr}.\n\
      Prove it with: Stg.not_deadlockFree_of_refute (ts := {idx tr}) (by decide +kernel)"
  | none =>
  match E.findLivelock stateCmp N.isInternal fuel N.init with
  | some (tr, cyc) => s!"LIVELOCK: after firing {N.names tr}, the internal transitions \
      {N.names cyc} can repeat forever.\nProve it with: Stg.not_livelockFree_of_refute \
      (ts := {idx tr}) (cyc := {idx cyc}) (by decide +kernel)"
  | none =>
  match (List.finRange N.net.trans.length).findSome? fun t =>
      (E.findDeadLabel stateCmp fuel N.init t).map fun tr => (t, tr) with
  | some (t, tr) => s!"NOT LIVE: after firing {N.names tr}, transition {N.tname t} can never \
      fire again.\nProve it with: Stg.not_liveLabel_of_refute (ts := {idx tr}) \
      (t := ⟨{t.val}, by decide⟩) (fuel := {fuel}) (by decide +kernel)"
  | none => s!"no counterexample found within {fuel} states; increase the fuel"

private def paths (fuel : ℕ) : List (StgState × List (Fin N.net.trans.length)) :=
  N.explicit.bfsPaths stateCmp fuel N.init

/-- Search for a violation of consistency. -/
def diagnoseConsistent (fuel : ℕ := 100000) : String :=
  if !N.wf then "the STG is ill-formed" else
  match (N.paths fuel).findSome? fun p => (N.succ p.1).findSome? fun e =>
      match N.edge e.1 with
      | some (z, b) => if p.1.2.getD z false = b then some (p.2, e.1, z, b) else none
      | none => none with
  | some (tr, t, z, b) => s!"INCONSISTENT: after firing {N.names tr}, transition {N.tname t} \
      is enabled although {N.sname z} is already {b}.\nProve it with: \
      Stg.not_consistent_of_refute (ts := {tr.map Fin.val}) (by decide +kernel)"
  | none => s!"no counterexample found within {fuel} states; increase the fuel"

/-- Search for a violation of complete state coding. -/
def diagnoseCSC (fuel : ℕ := 100000) : String :=
  if !N.wf then "the STG is ill-formed" else
  let ps := N.paths fuel
  let tbl := (ps.foldl (fun (st : BStore (List Bool × (List (Fin N.net.trans.length) ×
      List (ℕ × Bool)))) p =>
    if (st.lookup Circuit.boolLexCmp p.1.2).isSome then st
    else st.pushKV Circuit.boolLexCmp p.1.2 (p.2, N.edgesOf (N.succ p.1))) {}).tree
  match ps.findSome? fun p =>
      match tbl.lookup Circuit.boolLexCmp p.1.2 with
      | some (tr, es) => if es = N.edgesOf (N.succ p.1) then none else some (tr, es, p.2,
          N.edgesOf (N.succ p.1))
      | none => none with
  | some (tr₁, es₁, tr₂, es₂) =>
    let show_ (es : List (ℕ × Bool)) := es.map fun zb => N.ename zb.1 zb.2
    let hint := match es₁.find? (· ∉ es₂), es₂.find? (· ∉ es₁) with
      | some (z, b), _ => s!"Stg.not_csc_of_refute (ts₁ := {tr₁.map Fin.val}) \
          (ts₂ := {tr₂.map Fin.val}) (z := {z}) (b := {b}) (by decide +kernel)"
      | none, some (z, b) => s!"Stg.not_csc_of_refute (ts₁ := {tr₂.map Fin.val}) \
          (ts₂ := {tr₁.map Fin.val}) (z := {z}) (b := {b}) (by decide +kernel)"
      | none, none => "(no witness edge)"
    s!"CSC CONFLICT: firing {N.names tr₁} and firing {N.names tr₂} reach states with the same \
      signal values, but the first enables the non-input edges {show_ es₁} and the second \
      {show_ es₂}.\nProve it with: {hint}"
  | none => s!"no counterexample found within {fuel} states; increase the fuel"

/-- Search for a violation of output persistence. -/
def diagnoseOutputPersistent (fuel : ℕ := 100000) : String :=
  if !N.wf then "the STG is ill-formed" else
  match (N.paths fuel).findSome? fun p =>
      (N.edgesOf (N.succ p.1)).findSome? fun zb => (N.succ p.1).findSome? fun e =>
        let onZ := match N.edge e.1 with | some (z', _) => z' = zb.1 | none => false
        if !onZ && zb ∉ N.edgesOf (N.succ e.2) then some (p.2, zb, e.1) else none with
  | some (tr, zb, u) => s!"NOT OUTPUT-PERSISTENT: after firing {N.names tr}, the edge \
      {N.ename zb.1 zb.2} is enabled but firing {N.tname u} disables it.\nProve it with: \
      Stg.not_outputPersistent_of_refute (ts := {tr.map Fin.val}) (z := {zb.1}) (b := {zb.2}) \
      (u := {u.val}) (by decide +kernel)"
  | none => s!"no counterexample found within {fuel} states; increase the fuel"

/-- Search for a violation of conformance of `gates`. -/
def diagnoseConformant (gates : List Gate) (fuel : ℕ := 100000) : String :=
  if !N.wf then "the STG is ill-formed" else
  let bad (p : StgState × List (Fin N.net.trans.length)) : Option String :=
    let v := p.1.2
    let es := N.succ p.1
    match (List.range N.nsig).find? fun z => N.isNonInput z &&
        gateFnL gates z v != v.getD z false &&
        !es.any fun e => N.edge e.1 == some (z, gateFnL gates z v) with
    | some z => some s!"after firing {N.names p.2}, the gate of {N.sname z} is excited \
        (it would produce {N.ename z (gateFnL gates z v)}) but the specification does not \
        allow that edge.\nProve it with: Stg.not_conformant_of_refute \
        (ts := {p.2.map Fin.val}) (by decide +kernel)"
    | none =>
      (es.find? fun e => match N.edge e.1 with
        | some (z, b) => N.isNonInput z && (gateFnL gates z v != b || v.getD z false == b)
        | none => false).map fun e =>
          let zb := (N.edge e.1).getD (0, false)
          s!"after firing {N.names p.2}, the specification expects {N.ename zb.1 zb.2} \
            (transition {N.tname e.1}) but the gate of {N.sname zb.1} is not excited that way.\n\
            Prove it with: Stg.not_conformant_of_refute (ts := {p.2.map Fin.val}) \
            (by decide +kernel)"
  match (N.paths fuel).findSome? bad with
  | some msg => s!"NOT CONFORMANT: {msg}"
  | none => s!"no counterexample found within {fuel} states; increase the fuel"

end Stg

/-! ### Raw literals for the fast checker

Numbers are embedded as raw literals (`Expr.lit`), which the kernel reads directly; the
`OfNat` form produced by `ToExpr` costs a few unfoldings at every use. -/

namespace FastExpr

def natT : Expr := mkConst ``Nat
def prodT (α β : Expr) : Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) α β
def pairE (α β a b : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) α β a b
def listT (α : Expr) : Expr := mkApp (mkConst ``List [Level.zero]) α
def listE (α : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) α x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) α)
def treeE {β : Type} (α : Expr) (f : β → Expr) : BTree β → Expr
  | .leaf => mkApp (mkConst ``BTree.leaf [Level.zero]) α
  | .node l x r => mkApp4 (mkConst ``BTree.node [Level.zero]) α (treeE α f l) (f x) (treeE α f r)
def boolE (b : Bool) : Expr := if b then mkConst ``Bool.true else mkConst ``Bool.false

/-- A net as a literal, with raw numerals. -/
def pnetE (Nv : PNet) : Expr :=
  let nats (xs : List ℕ) := listE natT (xs.map mkRawNatLit)
  let tr (t : PTrans) := mkAppN (mkConst ``PTrans.mk)
    #[toExpr t.name, nats t.pre, nats t.post, boolE t.internal, toExpr t.edge]
  mkAppN (mkConst ``PNet.mk)
    #[mkRawNatLit Nv.places, listE (mkConst ``PTrans) (Nv.trans.map tr), nats Nv.init]

/-- A fast certificate as a literal. -/
def certE (c : Fast.Cert) : Expr :=
  let n2 := prodT natT natT
  let n3 := prodT natT n2
  let t := treeE n3 (fun (a, b, d) => pairE natT n2 (mkRawNatLit a)
    (pairE natT natT (mkRawNatLit b) (mkRawNatLit d))) c.1
  let lln := listT (listT natT)
  let hubT := prodT natT lln
  let hubs := listE hubT (c.2.map fun (h, trs) => pairE natT lln (mkRawNatLit h)
    (listE (listT natT) (trs.map fun tr => listE natT (tr.map mkRawNatLit))))
  pairE (mkApp (mkConst ``BTree [Level.zero]) n3) (listT hubT) t hubs

/-- A fast-table entry as a literal. -/
def fentryE (e : PNet.FEntry) : Expr :=
  let p2 := prodT natT natT
  let p3 := prodT natT p2
  let pres := listE p2 (e.1.map fun (a, b) => pairE natT natT (mkRawNatLit a) (mkRawNatLit b))
  let posts := listE p3 (e.2.2.2.map fun (a, b, c) =>
    pairE natT p2 (mkRawNatLit a) (pairE natT natT (mkRawNatLit b) (mkRawNatLit c)))
  pairE (listT p2) (prodT natT (prodT natT (listT p3))) pres
    (pairE natT (prodT natT (listT p3)) (mkRawNatLit e.2.1)
      (pairE natT (listT p3) (mkRawNatLit e.2.2.1) posts))

/-- The fast check `PNet.checkFast` for the net `N` (with value `Nv`), width `w` and
certificate `c`. -/
def checkFastE (N : Expr) (Nv : PNet) (w : ℕ) (c : Fast.Cert) (dl ll lv : Bool) : Expr :=
  let B := 2 ^ w
  let tb := listE (mkConst ``PNet.FEntry) ((Nv.ftable w).map fentryE)
  mkAppN (mkConst ``PNet.checkFast) #[N, mkRawNatLit w, mkRawNatLit B, mkRawNatLit (B - 1), tb,
    mkRawNatLit (cond ll Nv.imask 0), boolE dl, boolE ll, boolE lv,
    mkRawNatLit (PNet.encW w Nv.init), certE c]

/-- A table entry of the reduced search as a literal. -/
def sentryE (e : PNet.SEntry) : Expr :=
  let p2 := prodT natT natT
  let p3 := prodT natT p2
  let scs := listE p3 (e.2.2.map fun (a, b, c) =>
    pairE natT p2 (mkRawNatLit a) (pairE natT natT (mkRawNatLit b) (mkRawNatLit c)))
  pairE (mkConst ``PNet.FEntry) (prodT natT (listT p3)) (fentryE e.1)
    (pairE natT (listT p3) (mkRawNatLit e.2.1) scs)

/-- The reduced-state-space check `PNet.checkPOR` for the net `N` (with value `Nv`). -/
def checkPORE (N : Expr) (Nv : PNet) (w : ℕ) (t : BTree (ℕ × List ℕ)) : Expr :=
  let B := 2 ^ w
  let tbl := (Nv.stable w).toArray
  let it := prodT natT (mkConst ``PNet.SEntry)
  let ttE := treeE it (fun (i, e) => pairE natT (mkConst ``PNet.SEntry) (mkRawNatLit i)
    (sentryE e)) (Fast.buildTree (tbl.mapIdx fun i e => (i, e)) (tbl.size + 1) 0 tbl.size)
  let tE := treeE (prodT natT (listT natT)) (fun (a, l) => pairE natT (listT natT)
    (mkRawNatLit a) (listE natT (l.map mkRawNatLit))) t
  mkAppN (mkConst ``PNet.checkPOR) #[N, mkRawNatLit w, mkRawNatLit B, mkRawNatLit (B - 1), ttE,
    mkRawNatLit (PNet.encW w Nv.init), tE]

/-- The full-correctness reduced-state-space check `PNet.checkPORc`. -/
def checkPORcE (N : Expr) (Nv : PNet) (ll : Bool) (w : ℕ) (t : BTree (ℕ × PNet.PData))
    (hubs : List (ℕ × List (List ℕ))) : Expr :=
  let B := 2 ^ w
  let tbl := (Nv.stable w).toArray
  let se := mkConst ``PNet.SEntry
  let it := prodT natT se
  let entry := fun (ie : ℕ × PNet.SEntry) => pairE natT se (mkRawNatLit ie.1) (sentryE ie.2)
  let tlE := listE it ((tbl.mapIdx fun i e => (i, e)).toList.map entry)
  let ttE := treeE it entry (Fast.buildTree (tbl.mapIdx fun i e => (i, e)) (tbl.size + 1) 0 tbl.size)
  let ln := listT natT
  let d3 := prodT natT (prodT natT natT)
  let pd := prodT ln d3
  let tE := treeE (prodT natT pd) (fun (m, (sl, r, d, l)) => pairE natT pd (mkRawNatLit m)
    (pairE ln d3 (listE natT (sl.map mkRawNatLit)) (pairE natT (prodT natT natT) (mkRawNatLit r)
      (pairE natT natT (mkRawNatLit d) (mkRawNatLit l))))) t
  let lln := listT ln
  let hubT := prodT natT lln
  let hubsE := listE hubT (hubs.map fun (h, trs) => pairE natT lln (mkRawNatLit h)
    (listE ln (trs.map fun tr => listE natT (tr.map mkRawNatLit))))
  mkAppN (mkConst ``PNet.checkPORc) #[N, boolE ll, mkRawNatLit w, mkRawNatLit B,
    mkRawNatLit (B - 1), tlE, ttE, mkRawNatLit (cond ll Nv.imask 0), mkRawNatLit Nv.xmask,
    mkRawNatLit (PNet.encW w Nv.init), tE, hubsE]

/-- A list of numbers as a literal. -/
def natsE (xs : List ℕ) : Expr := listE natT (xs.map mkRawNatLit)

/-- The packed bounds check `PNet.checkPInv`. -/
def checkPInvE (N : Expr) (f g J : ℕ) (cols : BTree (ℕ × ℕ × ℕ)) (bs : List ℕ) : Expr :=
  let n2 := prodT natT natT
  let colsE := treeE (prodT natT n2) (fun (p, c, j) => pairE natT n2 (mkRawNatLit p)
    (pairE natT natT (mkRawNatLit c) (mkRawNatLit j))) cols
  mkAppN (mkConst ``PNet.checkPInv)
    #[N, mkRawNatLit f, mkRawNatLit g, mkRawNatLit J, colsE, natsE bs]

/-- A symbolic certificate as a literal. -/
def bcertE (c : PNet.BCert) : Expr :=
  let n := mkRawNatLit
  let n2 := prodT natT natT
  let n3 := prodT natT n2
  let n4 := prodT natT n3
  let lnat := listT natT
  let leafE := fun (k, (l : PNet.BLeaf)) => pairE natT (mkConst ``PNet.BLeaf) (n k)
    (mkAppN (mkConst ``PNet.BLeaf.mk) #[n l.wit, n l.d, n l.r, n l.k1, n l.k0,
      listE lnat (l.traces.map fun tr => listE natT (tr.map n)), boolE l.dat])
  let tripE := fun ((k, a, b, j) : ℕ × ℕ × ℕ × ℕ) =>
    pairE natT n3 (n k) (pairE natT n2 (n a) (pairE natT natT (n b) (n j)))
  let transE := fun (t : PNet.BTrans) => mkAppN (mkConst ``PNet.BTrans.mk) #[n t.pre, n t.post,
    listE n3 (t.us.map fun (v, l, k) => pairE natT n2 (n v) (pairE natT natT (n l) (n k))),
    treeE n4 tripE t.psI, treeE n4 tripE t.psR, treeE n4 tripE t.psD, n t.lo, n t.hi, boolE t.wit]
  mkAppN (mkConst ``PNet.BCert.mk) #[n c.H, n c.rI, n c.rR, n c.rD,
    n c.ncnt, n c.nw, n c.kw, n c.nlvl, n c.nvar, n c.nlo, n c.nhi, n c.nk1, n c.nk0,
    treeE (prodT natT (mkConst ``PNet.BLeaf)) leafE c.leaves,
    listE (mkConst ``PNet.BTrans) (c.trans.map transE), treeE n4 tripE c.covR,
    treeE n4 tripE c.covD, boolE c.linR, natsE c.wR, boolE c.linD, natsE c.wD,
    natsE c.vars, natsE c.lvls, listE lnat (c.cuts.map natsE)]

/-- The symbolic check `PNet.checkBDD`. -/
def checkBDDE (N : Expr) (dl ll lv : Bool) (c : PNet.BCert) : Expr :=
  mkAppN (mkConst ``PNet.checkBDD) #[N, boolE dl, boolE ll, boolE lv, bcertE c]

/-- A layout as a literal. -/
def layoutE (L : List LField) : Expr :=
  listE (mkConst ``LField) (L.map fun f => mkAppN (mkConst ``LField.mk)
    #[mkRawNatLit f.sh, mkRawNatLit f.w, natsE f.ps, boolE f.comp])

/-- A bitmap certificate as a literal; equal bitmaps share one literal. -/
def bitmapCertE (c : Bitmap.Cert) : Expr := Id.run do
  let mut memo : Std.HashMap ℕ Expr := {}
  for (_, a) in c.1.toList do
    unless memo.contains a do memo := memo.insert a (mkRawNatLit a)
  let lit (v : ℕ) : Expr := memo.getD v (mkRawNatLit v)
  let p2 := prodT natT natT
  let tE := treeE p2 (fun (h, a) => pairE natT natT (mkRawNatLit h) (lit a)) c.1
  let lln := listT (listT natT)
  let hubT := prodT natT lln
  let hubs := listE hubT (c.2.1.map fun (h, trs) => pairE natT lln (mkRawNatLit h)
    (listE (listT natT) (trs.map fun tr => listE natT (tr.map mkRawNatLit))))
  let restT := prodT (listT hubT) p2
  return pairE (mkApp (mkConst ``BTree [Level.zero]) p2) restT tE
    (pairE (listT hubT) p2 hubs (pairE natT natT (mkRawNatLit c.2.2.1) (mkRawNatLit c.2.2.2)))

/-- The three parts of the bitmap check `PNet.checkBitmap` for the net `N` (with value `Nv`),
checked separately by the kernel. -/
def checkBitmapEs (N : Expr) (Nv : PNet) (L : List LField) (k : ℕ) (dl ll lv : Bool)
    (c : Bitmap.Cert) (pR : List ℕ × ℕ) (pD : List ℕ × ℕ × ℕ) : List Expr :=
  let LE := layoutE L
  let cE := bitmapCertE c
  let imask := mkRawNatLit (cond ll Nv.imask 0)
  [mkAppN (mkConst ``PNet.checkBitmapA) #[N, LE, mkRawNatLit k, imask, mkRawNatLit pR.2,
    mkRawNatLit pD.2.1, mkRawNatLit pD.2.2, natsE pR.1, natsE pD.1, boolE dl, boolE ll,
    mkRawNatLit (PNet.encV L Nv.initVec), cE],
   mkAppN (mkConst ``PNet.checkBitmapR) #[N, LE, mkRawNatLit k, imask, mkRawNatLit pR.2, cE],
   mkAppN (mkConst ``PNet.checkBitmapD) #[N, LE, mkRawNatLit k, mkRawNatLit pD.2.1,
    mkRawNatLit pD.2.2, boolE lv, cE]]

end FastExpr

/-! ### Evaluation at elaboration time -/

namespace Tactic

unsafe def evalAsImpl (α : Type) [Inhabited α] [ToExpr α] (e : Expr) : MetaM α :=
  evalExpr α (toTypeExpr α) e

/-- Evaluate a closed term of a type with a `ToExpr` instance (untrusted, compiled code). -/
@[implemented_by evalAsImpl]
opaque evalAs (α : Type) [Inhabited α] [ToExpr α] (e : Expr) : MetaM α

unsafe def evalExprValImpl (e : Expr) : MetaM Expr := evalExpr Expr (mkConst ``Lean.Expr) e

/-- Evaluate a closed term of type `Expr`. -/
@[implemented_by evalExprValImpl]
opaque evalExprVal (e : Expr) : MetaM Expr

/-- Evaluate a closed term `e` (of any type with a `ToExpr` instance) to a literal. -/
def evalToLiteral (e : Expr) : MetaM Expr := do
  evalExprVal (← mkAppM ``Lean.ToExpr.toExpr #[e])

/-- Evaluate a Boolean. -/
def evalBool (e : Expr) : MetaM Bool := evalAs Bool e

/-- Evaluate a string. -/
def evalString (e : Expr) : MetaM String := evalAs String e

/-- Which component of a correctness statement a goal asks for. -/
inductive Goal where
  | correct | deadlock | livelock | live | persistent

/-- Recognise a goal about a concrete Petri net. -/
def matchPNet (tgt : Expr) : Option (Expr × Goal) :=
  match tgt.getAppFnArgs with
  | (``PNet.Correct, #[N]) => some (N, .correct)
  | (``LTS.DeadlockFree, #[_, _, A, _]) => (netOf A).map (·, .deadlock)
  | (``LTS.LivelockFree, #[_, _, A, _, _]) => (netOf A).map (·, .livelock)
  | (``LTS.Live, #[_, _, A, _]) => (netOf A).map (·, .live)
  | (``LTS.Persistent, #[_, _, A, _]) => (netOf A).map (·, .persistent)
  | _ => none
where
  netOf (A : Expr) : Option Expr :=
    match A.getAppFnArgs with
    | (``Net.lts, #[_, _, net]) =>
      match net.getAppFnArgs with
      | (``PNet.toNet, #[N]) => some N
      | _ => none
    | _ => none

/-- Recognise a boundedness goal `N.Bounded k` or `N.Safe`. -/
def matchBounded (tgt : Expr) : Option (Expr × Expr) :=
  match tgt.getAppFnArgs with
  | (``PNet.Bounded, #[N, k]) => some (N, k)
  | (``PNet.Safe, #[N]) => some (N, mkNatLit 1)
  | _ => none

/-- Recognise a goal about a concrete circuit. -/
def matchCircuit (tgt : Expr) : Option (Expr × Goal) :=
  match tgt.getAppFnArgs with
  | (``Circuit.Correct, #[C]) => some (C, .correct)
  | (``Circuit.SpeedIndependent, #[C]) => some (C, .persistent)
  | (``Circuit.QDI, #[C, iso]) => some (mkApp2 (mkConst ``Circuit.withWires) C iso, .persistent)
  | (``Circuit.QDICorrect, #[C, iso]) => some (mkApp2 (mkConst ``Circuit.withWires) C iso, .correct)
  | (``LTS.DeadlockFree, #[_, _, A, _]) => (circOf A).map (·, .deadlock)
  | (``LTS.LivelockFree, #[_, _, A, _, _]) => (circOf A).map (·, .livelock)
  | (``LTS.Live, #[_, _, A, _]) => (circOf A).map (·, .live)
  | (``LTS.Persistent, #[_, _, A, _]) => (circOf A).map (·, .persistent)
  | _ => none
where
  circOf (A : Expr) : Option Expr :=
    match A.getAppFnArgs with
    | (``Circuit.lts, #[C]) => some C
    | _ => none

/-- What a goal about a concrete STG asks for. -/
inductive StgGoal where
  | spec (p : Goal)
  | consistent
  | csc
  | outputPersistent
  | conformant (gates : Expr)
  | impl (gates : Expr) (p : Goal)

/-- Recognise a goal about a concrete STG or its implementation. -/
def matchStg (tgt : Expr) : Option (Expr × StgGoal) :=
  match tgt.getAppFnArgs with
  | (``StgModel.Correct, #[_, _, M]) => (stgOf M).map (·, .spec .correct)
  | (``StgModel.Consistent, #[_, _, M]) => (stgOf M).map (·, .consistent)
  | (``StgModel.CSC, #[_, _, M]) => (stgOf M).map (·, .csc)
  | (``StgModel.OutputPersistent, #[_, _, M]) => (stgOf M).map (·, .outputPersistent)
  | (``StgModel.Conformant, #[_, _, M, F]) => do
    let N ← stgOf M
    let gates ← gatesOf F
    pure (N, .conformant gates)
  | (``LTS.DeadlockFree, #[_, _, A, _]) => ofLts A .deadlock
  | (``LTS.LivelockFree, #[_, _, A, _, _]) => ofLts A .livelock
  | (``LTS.Live, #[_, _, A, _]) => ofLts A .live
  | _ => none
where
  stgOf (M : Expr) : Option Expr :=
    match M.getAppFnArgs with
    | (``Stg.model, #[N]) => some N
    | _ => none
  gatesOf (F : Expr) : Option Expr :=
    match F.getAppFnArgs with
    | (``Stg.gateFn, #[_, gates]) => some gates
    | _ => none
  ofLts (A : Expr) (p : Goal) : Option (Expr × StgGoal) :=
    match A.getAppFnArgs with
    | (``StgModel.sg, #[_, _, M]) => (stgOf M).map (·, .spec p)
    | (``StgModel.impl, #[_, _, M, F]) => do
      let N ← stgOf M
      let gates ← gatesOf F
      pure (N, .impl gates p)
    | _ => none

/-- Project the requested component out of a proof of a three-part correctness statement. -/
def project (pf : Expr) : Goal → MetaM Expr
  | .correct | .persistent => pure pf
  | .deadlock => mkAppM ``And.left #[pf]
  | .livelock => do mkAppM ``And.left #[← mkAppM ``And.right #[pf]]
  | .live => do mkAppM ``And.right #[← mkAppM ``And.right #[pf]]

/-- Close `goal` with `mkPf h`, where `h : checkE = true` is proved by the kernel. -/
def closeWithCheck (goal : MVarId) (checkE : Expr) (mkPf : Expr → Expr) (p : Goal) :
    TacticM Unit := do
  let hTy ← mkEq checkE (mkConst ``Bool.true)
  let h ← mkFreshExprSyntheticOpaqueMVar hTy
  let pf ← project (mkPf h) p
  let pfTy ← inferType pf
  unless ← isDefEq pfTy (← goal.getType) do
    let msg := "async_decide: the goal must be stated for the design's own initial state " ++
      "and internal predicate; can prove"
    throwError "{msg}{indentExpr pfTy}\nbut the goal is{indentExpr (← goal.getType)}"
  goal.assign pf
  replaceMainGoal [h.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- Variant of `closeWithCheck` for a design `orig` that was replaced by its evaluated literal
`lit`: the goal is matched against the proof's type with `lit` read back as `orig`, and the
kernel checks that `orig` and `lit` agree (by evaluation, once). -/
def closeWithCheckLit (goal : MVarId) (checkE : Expr) (mkPf : Expr → Expr) (p : Goal)
    (orig lit : Expr) : TacticM Unit := do
  let hTy ← mkEq checkE (mkConst ``Bool.true)
  let h ← mkFreshExprSyntheticOpaqueMVar hTy
  let pf ← project (mkPf h) p
  let pfTy ← inferType pf
  let pfTy' := pfTy.replace fun e => if e == lit then some orig else none
  let gTy ← goal.getType
  unless ← isDefEq pfTy' gTy do
    let msg := "async_decide: the goal must be stated for the design's own initial state " ++
      "and internal predicate; can prove"
    throwError "{msg}{indentExpr pfTy'}\nbut the goal is{indentExpr gTy}"
  goal.assign (← mkExpectedTypeHint pf gTy)
  replaceMainGoal [h.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- Variant of `closeWithCheckLit` whose proof builder runs in `MetaM`. -/
def closeWithCheckLitM (goal : MVarId) (checkE : Expr) (mkPf : Expr → MetaM Expr)
    (orig lit : Expr) : TacticM Unit := do
  let hTy ← mkEq checkE (mkConst ``Bool.true)
  let h ← mkFreshExprSyntheticOpaqueMVar hTy
  let pf ← mkPf h
  let pfTy ← inferType pf
  let pfTy' := pfTy.replace fun e => if e == lit then some orig else none
  let gTy ← goal.getType
  unless ← isDefEq pfTy' gTy do
    let msg := "async_decide: the goal must be stated for the design's own initial state " ++
      "and internal predicate; can prove"
    throwError "{msg}{indentExpr pfTy'}\nbut the goal is{indentExpr gTy}"
  goal.assign (← mkExpectedTypeHint pf gTy)
  replaceMainGoal [h.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- Variant of `closeWithCheck` whose proof builder runs in `MetaM`. -/
def closeWithCheckM (goal : MVarId) (checkE : Expr) (mkPf : Expr → MetaM Expr) (p : Goal) :
    TacticM Unit := do
  let hTy ← mkEq checkE (mkConst ``Bool.true)
  let h ← mkFreshExprSyntheticOpaqueMVar hTy
  let pf ← project (← mkPf h) p
  unless ← isDefEq (← inferType pf) (← goal.getType) do
    throwError "async_decide: the goal does not match{indentExpr (← inferType pf)}"
  goal.assign pf
  replaceMainGoal [h.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- Close `goal` with `mkPf hs`, where each `h ∈ hs : check = true` (for the checks built on
the net as a literal `lit`) is proved by the kernel; the goal is matched with `lit` read back
as the original net `N`. -/
def closeWithChecksLit (goal : MVarId) (N : Expr) (net : PNet) (checks : Expr → List Expr)
    (mkPf : List Expr → MetaM Expr) : TacticM Bool := do
  let lit := FastExpr.pnetE net
  let hs ← (checks lit).mapM fun c => do
    mkFreshExprSyntheticOpaqueMVar (← mkEq c (mkConst ``Bool.true))
  let pf ← mkPf hs
  let pfTy := (← inferType pf).replace fun e => if e == lit then some N else none
  let gTy ← goal.getType
  unless ← isDefEq pfTy gTy do return false
  goal.assign (← mkExpectedTypeHint pf gTy)
  replaceMainGoal (hs.map (·.mvarId!))
  evalTactic (← `(tactic| all_goals decide +kernel))
  return true

/-- Close `goal` by the fast check `PNet.checkFast` split into `K` parts
(`PNet.checkFast_of_parts`): the certificate becomes an auxiliary definition, the states are cut
into `K` key ranges of equal size, and each range is its own kernel goal. -/
def closeFastParts (goal : MVarId) (N : Expr) (Nv : PNet) (w : ℕ) (c : Fast.Cert)
    (dl ll lv : Bool) (thm : Name) (K : ℕ) : TacticM Bool := do
  let nm ← mkAuxDeclName `_fastCert
  addDecl (.defnDecl { name := nm, levelParams := [], type := mkConst ``Fast.Cert,
    value := FastExpr.certE c, hints := .opaque, safety := .safe })
  let cE := mkConst nm
  let B := 2 ^ w
  let tb := FastExpr.listE (mkConst ``PNet.FEntry) ((Nv.ftable w).map FastExpr.fentryE)
  let (wE, BE, fmE) := (mkRawNatLit w, mkRawNatLit B, mkRawNatLit (B - 1))
  let kE := mkRawNatLit (cond ll Nv.imask 0)
  let s₀E := mkRawNatLit (PNet.encW w Nv.init)
  let F := mkAppN (mkConst ``PNet.fsucc) #[fmE, BE, tb]
  -- range boundaries: keys at equal steps through the sorted states (`0` is no bound above)
  let keys := (c.1.toList.map (·.1)).toArray.qsort (· < ·)
  let bs := ((List.range K).filterMap fun i =>
    if i == 0 then none else keys[i * keys.size / K]?).filter (· != 0) |>.eraseDups
  let ranges := (0 :: bs).zip (bs ++ [0])
  let part (lo hi : ℕ) := mkAppN (mkConst ``Fast.checkPart)
    #[F, kE, FastExpr.boolE dl, FastExpr.boolE lv, cE, mkRawNatLit lo, mkRawNatLit hi]
  let hfalse := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false)
  closeWithChecksLit goal N Nv
    (fun lit => mkAppN (mkConst ``PNet.checkFastPre) #[lit, wE, BE, fmE, tb, kE,
        FastExpr.boolE ll, s₀E] ::
      mkAppN (mkConst ``Fast.checkHead) #[F, mkRawNatLit Nv.trans.length, FastExpr.boolE lv,
        s₀E, cE] ::
      ranges.map fun (lo, hi) => part lo hi)
    fun hs => do
      let hp := hs.drop 2 |>.toArray
      -- glue the parts `[i, j)` by halves
      let rec glue (i j : ℕ) (fuel : ℕ) : MetaM Expr := do
        match fuel with
        | 0 => throwError "closeFastParts: out of fuel"
        | fuel + 1 =>
          if j ≤ i + 1 then return hp[i]!
          let m := (i + j) / 2
          mkAppM ``Fast.checkPart_split
            #[mkRawNatLit (ranges[m]!).1, hfalse, ← glue i m fuel, ← glue m j fuel]
      let h ← mkAppM ``PNet.checkFast_of_parts #[hs[0]!, hs[1]!, ← glue 0 hp.size (hp.size + 1)]
      mkAppM thm #[h]

/-- Prove deadlock freedom of the `PNet` `N` from the state equation, without exploring its
state space (`PNet.deadlockFree_of_checks`), with bounds from place invariants.  Returns
`false` (leaving the goal untouched) when no certificate is found. -/
def decideSE (goal : MVarId) (N : Expr) : TacticM Bool := do
  let net ← evalAs PNet N
  let some (invs, ks) := net.findBounds (Auto.pinvFor net) | return false
  let bs := ks.map Prod.snd
  let some (yp, yn, z) := net.findSE bs | return false
  let (f, g, J, cols) := net.packInvs invs ks
  closeWithChecksLit goal N net
    (fun lit => [FastExpr.checkPInvE lit f g J cols bs,
      mkAppN (mkConst ``PNet.checkSE)
        #[lit, FastExpr.natsE bs, FastExpr.natsE yp, FastExpr.natsE yn, FastExpr.natsE z]])
    (fun hs => mkAppM ``PNet.deadlockFree_of_pinv hs.toArray)

/-- Prove a property of a safe `PNet` from a symbolic certificate (`PNet.of_checkBDD`):
`p = none` asks for safety.  Returns `false` (leaving the goal untouched) when no certificate
is found. -/
def decideBDD (goal : MVarId) (N : Expr) (p : Option Goal) (fuel : ℕ) : TacticM Bool := do
  let net ← evalAs PNet N
  unless net.packedWf do return false
  let noInt := net.noInternal
  let (dl, ll, lv) := match p with
    | none => (false, false, false)
    | some .deadlock => (true, false, false)
    | some .livelock => (false, !noInt, false)
    | some .live => (false, false, true)
    | _ => (true, !noInt, true)
  let needNoInt := noInt && (p matches some .livelock || p matches some .correct)
  match PNet.BDDGen.mkBDDCert net dl ll lv fuel with
  | .error _ => return false
  | .ok (c, _) =>
    closeWithChecksLit goal N net
      (fun lit => FastExpr.checkBDDE lit dl ll lv c ::
        (if needNoInt then [mkApp (mkConst ``PNet.noInternal) lit] else []))
      (fun hs => match p with
        | none => mkAppM ``PNet.safe_of_checkBDD #[hs[0]!]
        | some .deadlock => mkAppM ``PNet.deadlockFree_of_checkBDD #[hs[0]!]
        | some .live => mkAppM ``PNet.live_of_checkBDD #[hs[0]!]
        | some .livelock =>
          if needNoInt then mkAppM ``PNet.livelockFree_of_noInternal #[hs[1]!]
          else mkAppM ``PNet.livelockFree_of_checkBDD #[hs[0]!]
        | _ => do
          if needNoInt then
            mkAppM ``And.left #[← mkAppM ``PNet.correct_of_checkBDD_lf
              #[hs[0]!, ← mkAppM ``PNet.livelockFree_of_noInternal #[hs[1]!]]]
          else mkAppM ``And.left #[← mkAppM ``PNet.correct_of_checkBDD #[hs[0]!]])

/-- `async_bdd`: prove a property of a concrete safe `PNet` from a symbolic certificate. -/
def asyncBDD (fuel : ℕ) : TacticM Unit := do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let (N, p) ← match matchPNet tgt, matchBounded tgt with
    | some (N, p), _ => pure (N, some p)
    | none, some (N, k) =>
      unless (← evalAs ℕ k) == 1 do throwError "async_bdd: only safety (`Bounded 1`)"
      pure (N, none)
    | none, none => throwError "async_bdd: unsupported goal{indentExpr tgt}"
  if p matches some .persistent then throwError "async_bdd: persistence is not supported"
  unless ← decideBDD goal N p fuel do
    throwError "async_bdd: no symbolic certificate found (the net must be safe, without \
      repeated arcs, and satisfy the property)"

/-- Estimated kernel time, in seconds, of a bitmap certificate: every round (closure, ranks,
distances) costs, per transition and chunk, a fixed overhead and a time per byte of bitmap. -/
def bitmapCost (T k : ℕ) (c : Bitmap.Cert) : Float :=
  let chunks := c.1.toList.length
  let rounds := 1 + c.2.2.1 + c.2.2.2
  rounds.toFloat * T.toFloat * chunks.toFloat * (0.0004 + (2 ^ k / 8 : ℕ).toFloat * 3.0e-8)

/-- The most chunks of `2 ^ k` markings whose single round over `T` transitions fits in
`limit` seconds (`bitmapCost`): a cheaper certificate has no more chunks. -/
def bitmapChunkBound (T k : ℕ) (limit : Float) : ℕ :=
  (limit / (T.toFloat * (0.0004 + (2 ^ k / 8 : ℕ).toFloat * 3.0e-8))).ceil.toUInt64.toNat + 1

/-- Estimated kernel memory, in bytes, of one round of a bitmap check: the kernel keeps about
three bitmaps per transition and chunk. -/
def bitmapRoundBytes (T k : ℕ) (c : Bitmap.Cert) : Float :=
  T.toFloat * 3.0 * c.1.toList.length.toFloat * (2 ^ k / 8 : ℕ).toFloat

/-- Rounds per checkpoint segment, for about `budget` bytes of kernel memory per part. -/
def segRounds (T k : ℕ) (c : Bitmap.Cert) (budget : Float := 1.5e9) : ℕ :=
  max 1 (budget / bitmapRoundBytes T k c).floor.toUInt64.toNat

/-- Estimated kernel memory, in bytes, of the largest part of a bitmap check cut into
segments of `segRounds` rounds. -/
def bitmapBytes (T k : ℕ) (c : Bitmap.Cert) : Float :=
  let rounds := 1 + min (segRounds T k c) (max c.2.2.1 c.2.2.2)
  rounds.toFloat * bitmapRoundBytes T k c

/-- The arguments of `e` once its head is unfolded to the definition `expect`. -/
def unfoldArgs (e : Expr) (expect : Name) : MetaM (Array Expr) := do
  let some e' ← unfoldDefinition? e | throwError "bitmap: cannot unfold {e.getAppFn}"
  let e' := e'.headBeta
  unless e'.isAppOf expect do throwError "bitmap: {e.getAppFn} does not unfold to {expect}"
  return e'.getAppArgs

/-- **Rank and distance checks through checkpoints.**  From `rE` and `dE`, Boolean checks that
unfold to `Bitmap.checkR` and `Bitmap.checkD`, and the checkpoints `cR`, `cD` every `m` rounds
(`BitmapGen.checkpoints`) of the `nR` rank and `nD` distance rounds: the checks to hand to the
kernel, one declaration each, and the proofs of `rE = true` and `dE = true` from theirs. -/
def bitmapChain (rE dE : Expr) (m nR nD : ℕ) (cR cD : List (BTree (ℕ × ℕ))) :
    MetaM (List Expr × (Array Expr → Expr × Expr)) := do
  let ra ← unfoldArgs rE ``Bitmap.checkR
  let da ← unfoldArgs dE ``Bitmap.checkD
  let (tb, k, imask, dR, c) := (ra[0]!, ra[1]!, ra[2]!, ra[3]!, ra[4]!)
  let (tbD, kDk, dD, kD, L, lv, cDc) := (da[0]!, da[1]!, da[2]!, da[3]!, da[4]!, da[5]!, da[6]!)
  let p2 := FastExpr.prodT FastExpr.natT FastExpr.natT
  let lit (t : BTree (ℕ × ℕ)) := FastExpr.treeE p2
    (fun (h, a) => FastExpr.pairE FastExpr.natT FastExpr.natT (mkRawNatLit h) (mkRawNatLit a)) t
  let mE := mkRawNatLit m
  let mut checks : Array Expr := #[]
  -- ranks
  let mut A := mkApp (mkConst ``Bitmap.rankZero) c
  let mut nE := mkRawNatLit 0
  let mut rSteps : Array (Expr × Expr × Expr) := #[]
  for C in cR do
    let B := lit C
    checks := checks.push (mkAppN (mkConst ``Bitmap.segR) #[tb, k, imask, dR, c, mE, A, B])
    rSteps := rSteps.push (nE, A, B)
    nE := mkApp2 (mkConst ``Nat.add) nE mE
    A := B
  let rR := mkRawNatLit (nR - cR.length * m)
  checks := checks.push (mkAppN (mkConst ``Bitmap.finR) #[tb, k, imask, dR, c, A, nE, rR])
  let (rA, rN) := (A, nE)
  -- distances
  A := mkAppN (mkConst ``Bitmap.distZero) #[tbD, kDk, dD, cDc]
  nE := mkRawNatLit 0
  let mut dSteps : Array (Expr × Expr × Expr) := #[]
  for C in cD do
    let B := lit C
    checks := checks.push (mkAppN (mkConst ``Bitmap.segD) #[tbD, kDk, kD, cDc, mE, A, B])
    dSteps := dSteps.push (nE, A, B)
    nE := mkApp2 (mkConst ``Nat.add) nE mE
    A := B
  let rD := mkRawNatLit (nD - cD.length * m)
  checks := checks.push
    (mkAppN (mkConst ``Bitmap.finD) #[tbD, kDk, kD, L, lv, cDc, A, nE, rD])
  let (dA, dN) := (A, nE)
  let assemble (hs : Array Expr) : Expr × Expr := Id.run do
    let mut p := mkAppN (mkConst ``Bitmap.rankAt_zero) #[tb, k, imask, dR, c]
    for i in [0:rSteps.size] do
      let (n, A, B) := rSteps[i]!
      p := mkAppN (mkConst ``Bitmap.rankAt_seg) #[tb, k, imask, dR, c, n, mE, A, B, p, hs[i]!]
    let hR := mkAppN (mkConst ``Bitmap.checkR_of_fin)
      #[tb, k, imask, dR, c, rN, rR, rA, p, hs[rSteps.size]!]
    let o := rSteps.size + 1
    let mut q := mkAppN (mkConst ``Bitmap.distAt_zero) #[tbD, kDk, dD, kD, cDc]
    for i in [0:dSteps.size] do
      let (n, A, B) := dSteps[i]!
      q := mkAppN (mkConst ``Bitmap.distAt_seg) #[tbD, kDk, dD, kD, cDc, n, mE, A, B, q, hs[o + i]!]
    let hD := mkAppN (mkConst ``Bitmap.checkD_of_fin)
      #[tbD, kDk, dD, kD, L, lv, cDc, dN, rD, dA, q, hs[o + dSteps.size]!]
    return (hR, hD)
  return (checks.toList, assemble)

/-- Prove a property of a bounded `PNet` from a bitmap certificate (`PNet.of_checkBitmap`):
`p = none` asks for the bound `K`.  Returns `false` (leaving the goal untouched) when no
certificate is found, or when its estimated cost exceeds `limit` (seconds). -/
def decideBitmap (goal : MVarId) (N : Expr) (p : Option Goal) (K : ℕ := 1)
    (maxChunks : ℕ := 100000) (low : ℕ := 20) (limit : Option Float := none) (seg : ℕ := 0) :
    TacticM Bool := do
  let net ← evalAs PNet N
  unless net.wf do return false
  -- do not search for more chunks than the cost limit could accept
  let maxChunks := match limit with
    | some lim => min maxChunks (bitmapChunkBound net.trans.length low lim)
    | none => maxChunks
  let (dl, ll, lv) := match p with
    | none => (false, false, false)
    | some .deadlock => (true, false, false)
    | some .livelock => (false, true, false)
    | some .live => (false, false, true)
    | _ => (true, true, true)
  -- a speculative search (with a cost limit) also stops early on sparse sets: 16384 chunks
  -- of 2 ^ 12 markings (2 ^ 26 markings) take about as long as the time limit allows
  match net.mkBitmapCert dl ll lv p.isNone maxChunks low (if limit.isSome then 16384 else 0) with
  | .error _ => return false
  | .ok (L, k, c, pR, pD) =>
    if p.isNone && !net.layoutBound L K then return false
    if let some lim := limit then
      if bitmapCost net.trans.length k c > lim then return false
      -- leave room in memory: `async_bitmap` itself can be asked for more
      if bitmapBytes net.trans.length k c > 4.0e9 then return false
    -- the rank and distance rounds, cut at checkpoints to bound the kernel's memory
    let T := net.trans.length
    let m := if seg == 0 then segRounds T k c else seg
    let (cR, cD) := BitmapGen.checkpoints (net.atable L).toArray
      (fun i => (net.trans[i]?.map (·.internal)).getD false) k ll lv c pR.2 pD.2.1 pD.2.2 m
    let lit := FastExpr.pnetE net
    let es := FastExpr.checkBitmapEs lit net L k dl ll lv c pR pD
    let (chain, assemble) ← bitmapChain es[1]! es[2]! m c.2.2.1 c.2.2.2 cR cD
    let nc := chain.length
    closeWithChecksLit goal N net
      (fun lit => es[0]! :: chain ++
        (if p.isNone then [mkApp3 (mkConst ``PNet.layoutBound) lit (FastExpr.layoutE L)
          (mkRawNatLit K)] else []))
      (fun hs => do
        let (hR, hD) := assemble (hs.toArray.extract 1 (1 + nc))
        let h ← mkAppM ``PNet.checkBitmap_of_parts #[hs[0]!, hR, hD]
        match p with
        | none => mkAppM ``PNet.bounded_of_checkBitmap #[h, hs[1 + nc]!]
        | some .deadlock => mkAppM ``PNet.deadlockFree_of_checkBitmap #[h]
        | some .live => mkAppM ``PNet.live_of_checkBitmap #[h]
        | some .livelock => mkAppM ``PNet.livelockFree_of_checkBitmap #[h]
        | _ => mkAppM ``PNet.correct_of_checkBitmap #[h])

/-- Prove a property of a concrete circuit `C₀` from a bitmap certificate
(`Circuit.of_checkBitmap`).  Returns `false` (leaving the goal untouched) when no certificate is
found or when its estimated cost exceeds `limit` (seconds). -/
def decideBitmapC (goal : MVarId) (C₀ : Expr) (p : Goal) (maxChunks : ℕ := 100000)
    (low : ℕ := 20) (limit : Option Float := none) (seg : ℕ := 0) : TacticM Bool := do
  let Cv ← evalAs Circuit C₀
  unless Cv.wf do return false
  let (dl, ll, lv, thm) := match p with
    | .deadlock => (true, false, false, ``Circuit.deadlockFree_of_checkBitmap)
    | .livelock => (false, true, false, ``Circuit.livelockFree_of_checkBitmap)
    | .live => (false, false, true, ``Circuit.live_of_checkBitmap)
    | _ => (true, true, true, ``Circuit.correct_of_checkBitmap)
  if p matches .persistent then return false
  let maxChunks := match limit with
    | some lim => min maxChunks (bitmapChunkBound (2 * Cv.gates.length) low lim)
    | none => maxChunks
  match Cv.mkBitmapCert dl ll lv maxChunks low (if limit.isSome then 16384 else 0) with
  | .error _ => return false
  | .ok (k, c) =>
    if let some lim := limit then
      if bitmapCost (2 * Cv.gates.length) k c > lim then return false
      if bitmapBytes (2 * Cv.gates.length) k c > 4.0e9 then return false
    let lit := toExpr Cv
    let n := mkRawNatLit
    let imask := n (cond ll Cv.imaskB 0)
    let cE := FastExpr.bitmapCertE c
    let rE := mkAppN (mkConst ``Circuit.checkBitmapR) #[lit, n k, imask, cE]
    let dE := mkAppN (mkConst ``Circuit.checkBitmapD) #[lit, n k, FastExpr.boolE lv, cE]
    -- the rank and distance rounds, cut at checkpoints to bound the kernel's memory
    let T := 2 * Cv.gates.length
    let m := if seg == 0 then segRounds T k c else seg
    let (cR, cD) := BitmapGen.checkpoints Cv.btable.toArray (fun i => (Cv.gateD (i / 2)).internal)
      k ll lv c 0 0 (2 ^ T - 1) m
    let (chain, assemble) ← bitmapChain rE dE m c.2.2.1 c.2.2.2 cR cD
    let checks := mkAppN (mkConst ``Circuit.checkBitmapA) #[lit, n k, imask, FastExpr.boolE dl,
        FastExpr.boolE ll, n (Cv.bpack Cv.s₀), cE] :: chain
    let hs ← checks.mapM fun ch => do mkFreshExprSyntheticOpaqueMVar (← mkEq ch (mkConst ``Bool.true))
    let (hR, hD) := assemble (hs.toArray.extract 1 hs.length)
    let pf ← mkAppM thm #[hs[0]!, hR, hD]
    let pfTy := (← inferType pf).replace fun e => if e == lit then some C₀ else none
    let gTy ← goal.getType
    unless ← isDefEq pfTy gTy do return false
    goal.assign (← mkExpectedTypeHint pf gTy)
    replaceMainGoal (hs.map (·.mvarId!))
    evalTactic (← `(tactic| all_goals decide +kernel))
    return true

/-- `async_bitmap`: prove a property of a concrete bounded `PNet` from a bitmap certificate. -/
def asyncBitmap (maxChunks low : ℕ) (seg : ℕ := 0) : TacticM Unit := do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let ok ← match matchPNet tgt, matchBounded tgt, matchCircuit tgt with
    | some (N, p), _, _ =>
      if p matches .persistent then throwError "async_bitmap: persistence is not supported"
      decideBitmap goal N (some p) 1 maxChunks low none seg
    | none, some (N, k), _ => decideBitmap goal N none (← evalAs ℕ k) maxChunks low none seg
    | none, none, some (C, p) =>
      if p matches .persistent then throwError "async_bitmap: persistence is not supported"
      decideBitmapC goal C p maxChunks low none seg
    | none, none, none => throwError "async_bitmap: unsupported goal{indentExpr tgt}"
  unless ok do
    throwError "async_bitmap: no bitmap certificate found (the net must be bounded, satisfy \
      the property, and its packed reachable markings fit in the chunk budget)"

/-- Prove `N.Bounded k` from packed place invariants (`PNet.bounded_of_checkPInv`). -/
def decideBounded (goal : MVarId) (N k : Expr) : TacticM Bool := do
  let net ← evalAs PNet N
  let kv ← evalAs ℕ k
  let some (invs, ks) := net.findBounds (Auto.pinvFor net) | return false
  let bs := ks.map Prod.snd
  unless bs.all (· ≤ kv) do return false
  let (f, g, J, cols) := net.packInvs invs ks
  closeWithChecksLit goal N net
    (fun lit => [FastExpr.checkPInvE lit f g J cols bs,
      mkApp2 (mkConst ``PNet.allLe) (FastExpr.natsE bs) k])
    (fun hs => mkAppOptM ``PNet.bounded_of_checkPInv
      #[none, none, none, none, none, none, k, hs[0]!, hs[1]!])

/-- Fail with the diagnosis `diag` unless `checkE` evaluates to `true`. -/
def ensure (checkE diag : Expr) : MetaM Unit := do
  unless ← evalBool checkE do
    throwError "async_decide: {← evalString diag}"

/-- Recognise `fun l => b l = true` and return `fun l => b l`. -/
def boolPred? (i : Expr) : Option Expr :=
  match i with
  | .lam n ty body bi =>
    match body.getAppFnArgs with
    | (``Eq, #[_, b, t]) => if t.isConstOf ``Bool.true then some (.lam n ty b bi) else none
    | _ => none
  | _ => none

/-- The explicit LTS underlying `E.toLTS`. -/
def explicitOf? (A : Expr) : Option Expr :=
  match A.getAppFnArgs with
  | (``ExplicitLTS.toLTS, #[_, _, E]) => some E
  | _ => none

/-- Recognise deadlock / livelock goals about an explicit LTS: returns the explicit LTS, the
initial state, the Boolean internal predicate (if any) and which component is asked for. -/
def matchExplicit (tgt : Expr) : Option (Expr × Expr × Option Expr × Goal) :=
  match tgt.getAppFnArgs with
  | (``And, #[a, b]) =>
    match a.getAppFnArgs, b.getAppFnArgs with
    | (``LTS.DeadlockFree, #[_, _, A, s₀]), (``LTS.LivelockFree, #[_, _, _, i, _]) => do
      let E ← explicitOf? A
      let j ← boolPred? i
      pure (E, s₀, some j, .correct)
    | _, _ => none
  | (``LTS.DeadlockFree, #[_, _, A, s₀]) => (explicitOf? A).map fun E => (E, s₀, none, .deadlock)
  | (``LTS.LivelockFree, #[_, _, A, i, s₀]) => do
    let E ← explicitOf? A
    let j ← boolPred? i
    pure (E, s₀, some j, .livelock)
  | _ => none

/-- Recognise a goal about a concrete interconnection network. -/
def matchNetwork (tgt : Expr) : Option (Expr × Option Goal) :=
  match tgt.getAppFnArgs with
  | (``Network.Correct, #[_, _, N, _]) => some (N, some .correct)
  | (``Network.DeadlockFree, #[_, _, N, _]) => some (N, some .deadlock)
  | (``Network.LivelockFree, #[_, _, N, _]) => some (N, some .livelock)
  | (``Network.StarvationFree, #[_, _, _, N]) => some (N, none)
  | _ => none

/-- Prove a routing goal by `Network.correct_of_checkCert` (or
`Network.starvationFree_of_checkCert` when `p` is `none`), trying the escape subfunctions
`escs` in turn; on failure, diagnose with `diagEsc`. -/
def decideRouting (goal : MVarId) (N : Expr) (escs : List Expr) (diagEsc : Expr) (p : Option Goal)
    (fuel : ℕ) (tac : String) : TacticM Unit := do
  let (``Network, #[C, P]) := (← whnfR (← inferType N)).getAppFnArgs
    | throwError "{tac}: expected a network"
  let cmpC ← mkAppOptM ``StateOrd.cmp #[C, none]
  let cmpQ ← mkAppOptM ``StateOrd.cmp #[← mkAppM ``Prod #[C, P], none]
  let pairs ← evalToLiteral (← mkAppM ``Network.mkPairs #[N, cmpQ, mkNatLit fuel])
  for esc in escs do
    let ranks ← evalToLiteral (← mkAppM ``Network.mkRanks #[N, cmpC, esc, pairs])
    let chk ← mkAppM ``Network.checkCert #[N, cmpC, cmpQ, esc, pairs, ranks]
    if ← evalBool chk then
      let h ← mkFreshExprSyntheticOpaqueMVar (← mkEq chk (mkConst ``Bool.true))
      let pf ← match p with
        | none => mkAppM ``Network.starvationFree_of_checkCert #[h]
        | some .deadlock => mkAppM ``And.left #[← mkAppM ``Network.correct_of_checkCert #[h]]
        | some .livelock => mkAppM ``And.right #[← mkAppM ``Network.correct_of_checkCert #[h]]
        | some _ => mkAppM ``Network.correct_of_checkCert #[h]
      unless ← isDefEq (← inferType pf) (← goal.getType) do
        throwError "{tac}: could not match the goal with{indentExpr (← inferType pf)}"
      goal.assign pf
      replaceMainGoal [h.mvarId!]
      evalTactic (← `(tactic| decide +kernel))
      return
  let diag ← mkAppM ``Network.diagnose #[N, cmpC, cmpQ, diagEsc, mkNatLit fuel]
  throwError "{tac}: {← evalString diag}"

/-- Recognise a goal about a concrete network under wormhole switching. -/
def matchWormhole (tgt : Expr) : Option (Expr × Goal) :=
  match tgt.getAppFnArgs with
  | (``Network.WormholeCorrect, #[_, _, N]) => some (N, .correct)
  | (``Network.WormholeDeadlockFree, #[_, _, N]) => some (N, .deadlock)
  | (``Network.WormholeLivelockFree, #[_, _, N]) => some (N, .livelock)
  -- starvation freedom is the liveness of packets: every packet is eventually delivered
  | (``Network.WormholeStarvationFree, #[_, _, N]) => some (N, .live)
  | _ => none

/-- Prove a wormhole goal by `Network.wormholeCorrect_of_wcheckCert`, with the escape
channels `esc?` or, by default, all channels and then the channels of the first-listed hops. -/
def decideWormhole (goal : MVarId) (N : Expr) (esc? : Option Expr) (p : Goal) (fuel : ℕ)
    (tac : String) : TacticM Unit := do
  let (``Network, #[C, P]) := (← whnfR (← inferType N)).getAppFnArgs
    | throwError "{tac}: expected a network"
  let cmpC ← mkAppOptM ``StateOrd.cmp #[C, none]
  let cmpQ ← mkAppOptM ``StateOrd.cmp #[← mkAppM ``Prod #[C, P], none]
  let pairs ← evalToLiteral (← mkAppM ``Network.mkPairs #[N, cmpQ, mkNatLit fuel])
  let all := Expr.lam `c C (mkConst ``Bool.true) .default
  let escs ← match esc? with
    | some e => pure [e]
    | none => do
      let fh ← evalToLiteral (← mkAppM ``Network.firstHopEscapes #[N, cmpC, pairs])
      pure [all, ← mkAppM ``Network.inTree #[cmpC, fh]]
  for E in escs do
    let cert ← mkAppM ``Network.mkWCert #[N, cmpC, cmpQ, E, pairs, mkNatLit fuel]
    let ranks ← evalToLiteral (← mkAppM ``Prod.fst #[cert])
    let lo ← evalToLiteral (← mkAppM ``Prod.snd #[cert])
    let chk ← mkAppM ``Network.wcheckCert #[N, cmpC, cmpQ, E, pairs, ranks, lo]
    if ← evalBool chk then
      let h ← mkFreshExprSyntheticOpaqueMVar (← mkEq chk (mkConst ``Bool.true))
      let pf ← match p with
        | .deadlock => mkAppM ``And.left #[← mkAppM ``Network.wormholeCorrect_of_wcheckCert #[h]]
        | .livelock => mkAppM ``And.right #[← mkAppM ``Network.wormholeCorrect_of_wcheckCert #[h]]
        | .live => mkAppM ``Network.wormholeStarvationFree_of_wcheckCert #[h]
        | _ => mkAppM ``Network.wormholeCorrect_of_wcheckCert #[h]
      unless ← isDefEq (← inferType pf) (← goal.getType) do
        throwError "{tac}: could not match the goal with{indentExpr (← inferType pf)}"
      goal.assign pf
      replaceMainGoal [h.mvarId!]
      evalTactic (← `(tactic| decide +kernel))
      return
  -- Duato's condition is only sufficient under wormhole switching: on small networks, try the
  -- blocking sets of `Network.wormholeDeadlockFree_of_wholdCert` (exponential in the pairs)
  if p matches .deadlock then
    let n ← evalAs ℕ (← mkAppM ``List.length #[← mkAppM ``BTree.toList #[pairs]])
    if n ≤ 12 then
      let chk ← mkAppM ``Network.wholdCert #[N, cmpQ, pairs]
      if ← evalBool chk then
        let h ← mkFreshExprSyntheticOpaqueMVar (← mkEq chk (mkConst ``Bool.true))
        let pf ← mkAppM ``Network.wormholeDeadlockFree_of_wholdCert #[N, h]
        if ← isDefEq (← inferType pf) (← goal.getType) then
          goal.assign pf
          replaceMainGoal [h.mvarId!]
          evalTactic (← `(tactic| decide +kernel))
          return
  let diag ← mkAppM ``Network.wdiagnose #[N, cmpC, cmpQ, esc?.getD all, mkNatLit fuel]
  throwError "{tac}: {← evalString diag}"

/-- Deadlock and livelock freedom of an explicit LTS. -/
def decideExplicit (goal : MVarId) (E s₀ : Expr) (j : Option Expr) (p : Goal) (fuel : ℕ) :
    TacticM Unit := do
  let ty ← inferType s₀
  let cmp ← mkAppOptM ``StateOrd.cmp #[ty, none]
  let lty ← match (← whnfR (← inferType E)).getAppFnArgs with
    | (``ExplicitLTS, #[_, l]) => pure l
    | _ => throwError "async_decide: expected an explicit LTS"
  let j ← match j with
    | some j => pure j
    | none => pure (.lam `l lty (mkConst ``Bool.false) .default)
  let nil ← mkAppOptM ``List.nil #[lty]
  let cert ← mkAppM ``ExplicitLTS.mkCert #[E, cmp, j, nil, mkNatLit fuel, s₀]
  let lit ← evalToLiteral cert
  let chk ← mkAppM ``ExplicitLTS.checkCert #[E, cmp, j, nil, s₀, lit]
  unless ← evalBool chk do
    throwError "async_decide: the explicit system has a reachable deadlock or an infinite run \
      of internal steps (or its state space exceeds the fuel {fuel})"
  let hTy ← mkEq chk (mkConst ``Bool.true)
  let h ← mkFreshExprSyntheticOpaqueMVar hTy
  let pf ← mkAppM ``ExplicitLTS.dfLf_of_checkCert #[h]
  let pf ← match p with
    | .deadlock => mkAppM ``And.left #[pf]
    | .livelock => mkAppM ``And.right #[pf]
    | _ => pure pf
  unless ← isDefEq (← inferType pf) (← goal.getType) do
    throwError "async_decide: could not match the goal with{indentExpr (← inferType pf)}"
  goal.assign pf
  replaceMainGoal [h.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- Replace one component of a composition by its certified quotient (see
`ExplicitLTS.dfLf_par_left_iff`). -/
def minimize (right : Bool) (fuel : ℕ) : TacticM Unit := do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let err {α : Type} : TacticM α := throwError "async_minimize: expected a goal of the form\
    {indentD "(E.par F sync).toLTS.DeadlockFree (s₀, u₀) ∧\n  (E.par F sync).toLTS.LivelockFree (fun l => j l = true) (s₀, u₀)"}"
  let some (P, p₀, some j, .correct) := matchExplicit tgt | err
  let (``ExplicitLTS.par, args) := P.getAppFnArgs | err
  let some E := args[args.size - 3]? | err
  let some F := args[args.size - 2]? | err
  let some sync := args[args.size - 1]? | err
  let (``Prod.mk, #[_, _, s₀, u₀]) := p₀.getAppFnArgs | err
  let (comp, init, other) := if right then (F, u₀, s₀) else (E, s₀, u₀)
  let ty ← inferType init
  let lty ← match (← whnfR (← inferType comp)).getAppFnArgs with
    | (``ExplicitLTS, #[_, l]) => pure l
    | _ => err
  let cmp ← mkAppOptM ``StateOrd.cmp #[ty, none]
  let internalB := Expr.lam `l lty (mkApp2 (mkConst ``and) (mkApp j (.bvar 0))
    (mkApp (mkConst ``not) (mkApp sync (.bvar 0)))) .default
  let r ← mkAppM ``ExplicitLTS.mkQuot #[comp, cmp, internalB, mkNatLit fuel, init]
  let qLit ← evalToLiteral (← mkAppM ``ExplicitLTS.QuotResult.q #[r])
  let cLit ← evalToLiteral (← mkAppM ``ExplicitLTS.QuotResult.cert #[r])
  let k ← evalAs ℕ (← mkAppM ``ExplicitLTS.QuotResult.init #[r])
  let chk ← mkAppM ``ExplicitLTS.checkQuot #[comp, cmp, internalB, qLit, init, cLit]
  unless ← evalBool chk do
    throwError "async_minimize: the minimised component could not be certified (it may have a \
      cycle of internal steps — a livelock — or exceed the fuel {fuel})"
  let hq ← mkFreshExprSyntheticOpaqueMVar (← mkEq chk (mkConst ``Bool.true))
  let clsE ← mkAppM ``ExplicitLTS.InvCert.cls #[cmp, cLit, init]
  let hk ← mkFreshExprSyntheticOpaqueMVar (← mkEq clsE (← mkAppM ``Option.some #[mkNatLit k]))
  let thm := if right then ``ExplicitLTS.dfLf_par_right_iff else ``ExplicitLTS.dfLf_par_left_iff
  let otherComp := if right then E else F
  let iff ← mkAppOptM thm #[ty, lty, ← inferType other, none, none, cmp, comp, otherComp, sync, j,
    qLit, init, cLit, mkNatLit k, hq, hk, other]
  let some (lhs, rhs) := (← inferType iff).iff? | err
  unless ← isDefEq lhs tgt do err
  let g' ← mkFreshExprSyntheticOpaqueMVar rhs
  goal.assign (← mkAppM ``Iff.mpr #[iff, g'])
  replaceMainGoal [hq.mvarId!, hk.mvarId!, g'.mvarId!]
  evalTactic (← `(tactic| decide +kernel))
  evalTactic (← `(tactic| decide +kernel))

/-- Try to prove a property of a Petri net from its counter abstraction with cap `K`; returns
whether it succeeded. -/
def decideAbstract (goal : MVarId) (N : Expr) (p : Goal) (K fuelE : Expr) : TacticM Bool := do
  let app (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) args
  let (dl, ll, lv, thm) := match p with
    | .deadlock => (true, false, false, ``PNet.deadlockFree_of_checkAbs)
    | .livelock => (false, true, false, ``PNet.livelockFree_of_checkAbs)
    | .live => (false, false, true, ``PNet.live_of_checkAbs)
    | _ => (true, true, true, ``PNet.correct_of_checkAbs)
  let litA := toExpr (← evalAs (ExplicitLTS.ACert (List ℕ))
    (app ``PNet.mkAbsCert #[N, K, toExpr ll, toExpr lv, fuelE]))
  let chkA := app ``PNet.checkAbs #[N, K, toExpr dl, toExpr ll, toExpr lv, litA]
  if ← evalBool chkA then
    closeWithCheck goal chkA (fun h => app thm #[N, K, litA, h]) .correct
    return true
  -- linear potentials see what the cap hides: lexicographic ranks and must-distances
  let net ← evalAs PNet N
  let Kv ← evalAs ℕ K
  let fuel ← evalAs ℕ fuelE
  unless net.wf && net.capOk Kv do return false
  let thmP := match p with
    | .deadlock => ``PNet.deadlockFree_of_checkAbsP
    | .livelock => ``PNet.livelockFree_of_checkAbsP
    | .live => ``PNet.live_of_checkAbsP
    | _ => ``PNet.correct_of_checkAbsP
  let internal : ℕ → Bool := if ll then net.internalKey else fun _ => false
  let labels := if lv then List.range net.trans.length else []
  let a₀ := net.init.map (min · Kv)
  let allMask := 2 ^ net.trans.length - 1
  let dCands : List (List ℕ × ℕ × ℕ) := ([], 0, allMask) ::
    (if lv then
      let w := PNet.BDDGen.linLex net (List.range net.trans.length)
      let (d, k) := net.potMasks w
      if d != 0 then [(w, d, k)] else []
    else [])
  for (wR, dR) in net.rankCands ll do
    for (wD, dD, kD) in dCands do
      let c := (net.abstr Kv).mkACertP lexCmp Fin.val internal dR.testBit dD.testBit kD.testBit
        labels fuel a₀
      if (net.abstr Kv).checkACertP lexCmp Fin.val dl internal dR.testBit dD.testBit kD.testBit
          labels a₀ c then
        let litP := toExpr c
        let chk := app ``PNet.checkAbsP #[N, K, toExpr dl, toExpr ll, toExpr lv,
          FastExpr.natsE wR, mkNatLit dR, FastExpr.natsE wD, mkNatLit dD, mkNatLit kD, litP]
        closeWithCheck goal chk (fun h => mkAppN (mkConst thmP)
          #[N, K, FastExpr.natsE wR, FastExpr.natsE wD, mkNatLit dR, mkNatLit dD, mkNatLit kD,
            litP, h]) .correct
        return true
  return false

/-- The error reported when the counter abstraction with cap `K` is too coarse. -/
def abstractionTooCoarse {α : Type} (K : Expr) : MetaM α := do
  throwError "async_decide: the net's state space exceeds the fuel (it may be unbounded) and \
    no counterexample was found, but the counter abstraction with cap {← evalAs ℕ K} is too \
    coarse to prove the goal; try a larger cap with `async_decide (cap := k)`, or \
    `async_structural`"

/-- The `async_decide` tactic (see the module documentation). -/
def asyncDecide (fuel : ℕ) (cap : Option ℕ := none) : TacticM Unit := do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let fuelE := mkNatLit fuel
  let app (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) args
  if let some (N, k) := matchBounded tgt then
    -- safety of a large safe net: a symbolic invariant
    if (← evalAs ℕ k) == 1 then
      unless ← evalBool (app ``PNet.closes #[N, mkNatLit (min fuel 10000)]) do
        if ← decideBDD goal N none 200000 then return
    let lit := toExpr (← evalAs (ExplicitLTS.InvCert (List ℕ) Unit) (app ``PNet.mkBoundCert #[N, fuelE]))
    let chk := app ``PNet.checkBounded #[N, k, lit]
    unless ← evalBool chk do
      throwError "async_decide: the net is not {← evalAs ℕ k}-bounded (some reachable marking \
        exceeds it), or its state space exceeds the fuel"
    closeWithCheck goal chk (fun h => app ``PNet.bounded_of_check #[N, k, lit, h]) .correct
  else if let some (N, p) := matchPNet tgt then
    let cert : MetaM Expr := do
      return toExpr (← evalAs (ExplicitLTS.Cert (List ℕ)) (app ``PNet.mkCert #[N, fuelE]))
    match p, cap with
    | .persistent, _ =>
      let lit ← cert
      let chk := app ``PNet.checkCertPersistent #[N, lit]
      ensure chk (app ``PNet.diagnosePersistent #[N, fuelE])
      closeWithCheck goal chk (fun h => app ``PNet.persistent_of_checkCert #[N, lit, h]) p
    | _, some K =>
      unless ← decideAbstract goal N p (mkNatLit K) fuelE do abstractionTooCoarse (mkNatLit K)
    | _, none =>
      -- deadlock freedom: partial-order reduction (stubborn sets) first
      if p matches .deadlock then
        let Nv ← evalAs PNet N
        match Nv.mkPORCert fuel with
        | .ok (w, t) =>
          -- a large reduced state space: bitmaps may be cheaper (about a millisecond of
          -- kernel time per reduced marking; finding a bitmap certificate takes seconds, so
          -- not below a few thousand)
          let n := t.toList.length
          if n > 2000 then
            if ← decideBitmap goal N (some p) 1 8192 20 (some (n.toFloat * 0.003)) then return
          let lit := FastExpr.pnetE Nv
          closeWithCheckLitM goal (FastExpr.checkPORE lit Nv w t)
            (fun h => mkAppM ``PNet.deadlockFree_of_checkPOR #[h]) N lit
          return
        | .error e =>
          -- no deadlock found, but the reduced state space is too large (or the net may be
          -- unbounded): the state equation needs no exploration at all
          unless e.startsWith "deadlock" do
            if ← decideSE goal N then return
            if ← decideBitmap goal N (some p) 1 8192 20 (some 120.0) then return
      -- partial-order reduction for livelock freedom and liveness too
      unless p matches .deadlock do
        let Nv ← evalAs PNet N
        let noInt := Nv.noInternal
        -- without internal transitions, livelock freedom is immediate and the visibility
        -- conditions (which would force full expansion) are not needed
        let ll := !noInt && !(p matches .live)
        -- a quick probe: a reduced state space beyond a few thousand markings of a dense net
        -- goes to bitmaps before the full reduction is computed
        let probe := Nv.mkPORcCert ll (min fuel 3000)
        let early := probe matches .error _
        if early && Nv.bitmapDense then
          if ← decideBitmap goal N (some p) 1 8192 20 (some 120.0) then return
        let porc := if probe matches .ok _ then probe else Nv.mkPORcCert ll fuel
        -- bitmaps, when the reduced state space is large or the reduction does not reduce
        let porcSize : Option ℕ := match porc with
          | .ok (_, t, _) =>
            let l := t.toList
            if 2 * (l.filter fun x => x.2.2.2.1 == 0).length < l.length then some l.length
            else none
          | .error _ => none
        -- a reduced marking costs about 10 ms of kernel time with the cycle proviso and the
        -- traces of liveness
        -- (finding a bitmap certificate takes seconds, so not below a few thousand)
        if !early && porcSize.all (fun n => n > 2000) && Nv.bitmapDense then
          let lim := (porcSize.map fun n => n.toFloat * 0.01).getD 120.0
          if ← decideBitmap goal N (some p) 1 8192 20 (some lim) then return
        if let .ok (w, t, hubs) := porc then
          let l := t.toList
          -- worth it only if the reduction actually reduces
          if 2 * (l.filter fun x => x.2.2.2.1 == 0).length < l.length then
            let needNoInt := noInt && !(p matches .live)
            let ok ← closeWithChecksLit goal N Nv
              (fun lit => FastExpr.checkPORcE lit Nv ll w t hubs ::
                (if needNoInt then [mkApp (mkConst ``PNet.noInternal) lit] else []))
              (fun hs => match p with
                | .live => mkAppM ``PNet.live_of_checkPORc #[hs[0]!]
                | .livelock =>
                  if needNoInt then mkAppM ``PNet.livelockFree_of_noInternal #[hs[1]!]
                  else mkAppM ``PNet.livelockFree_of_checkPORc #[hs[0]!]
                | _ =>
                  if needNoInt then do
                    mkAppM ``PNet.correct_of_checkPORc_lf
                      #[hs[0]!, ← mkAppM ``PNet.livelockFree_of_noInternal #[hs[1]!]]
                  else mkAppM ``PNet.correct_of_checkPORc #[hs[0]!])
            if ok then return
      -- a quick probe: if the state space does not close (e.g. an unbounded net), try the
      -- counter abstraction first
      unless ← evalBool (app ``PNet.closes #[N, mkNatLit (min fuel 10000)]) do
        -- a large safe net: a symbolic certificate (decision diagrams)
        if ← decideBDD goal N (some p) 200000 then return
        -- caps above the arc weights keep the places holding few tokens exact
        let k ← evalAs ℕ (app ``PNet.minCap #[N])
        let mut proved := false
        for K in [k + 1, k + 3] do
          unless proved do
            proved ← decideAbstract goal N p (mkNatLit K) fuelE
        if proved then return
        unless ← evalBool (app ``PNet.closes #[N, fuelE]) do
          -- look for a counterexample among the first few thousand states
          let d ← evalString (app ``PNet.diagnose #[N, mkNatLit (min fuel 500)])
          unless d.startsWith "no counterexample" do throwError "async_decide: {d}"
          abstractionTooCoarse (mkNatLit (k + 3))
      -- fastest path: markings packed into bit fields, checked by `PNet.checkFast`
      let (dl, ll, lv, thm) := match p with
        | .deadlock => (true, false, false, ``PNet.deadlockFree_of_checkFast)
        | .livelock => (false, true, false, ``PNet.livelockFree_of_checkFast)
        | .live => (false, false, true, ``PNet.live_of_checkFast)
        | _ => (true, true, true, ``PNet.correct_of_checkFast)
      let Nv ← evalAs PNet N
      if let .ok (w, c) := Nv.mkFastCert dl ll lv fuel then
        let lit := FastExpr.pnetE Nv
        closeWithCheckLitM goal (FastExpr.checkFastE lit Nv w c dl ll lv)
          (fun h => mkAppM thm #[h]) N lit
        return
      -- safe nets that can always return to their initial marking
      let litH := toExpr (← evalAs (ExplicitLTS.HomeCert ℕ) (app ``PNet.mkPackedHomeCert #[N, fuelE]))
      let chkH := app ``PNet.checkPackedHome #[N, litH]
      if ← evalBool chkH then
        closeWithCheckM goal chkH (fun h => mkAppM ``And.left
          #[app ``PNet.correct_of_checkPackedHome #[N, litH, h]]) p
      else
      -- fast path: safe nets, with markings packed into bit masks
      let litP := toExpr (← evalAs (ExplicitLTS.Cert ℕ) (app ``PNet.mkPackedCert #[N, fuelE]))
      let chkP := app ``PNet.checkPacked #[N, litP]
      if ← evalBool chkP then
        closeWithCheckM goal chkP (fun h => mkAppM ``And.left
          #[app ``PNet.correct_of_checkPacked #[N, litP, h]]) p
      else
      let litH := toExpr (← evalAs (ExplicitLTS.HomeCert (List ℕ)) (app ``PNet.mkCertHome #[N, fuelE]))
      let chkH := app ``PNet.checkCertHome #[N, litH]
      if ← evalBool chkH then
        closeWithCheck goal chkH (fun h => app ``PNet.correct_of_checkCertHome #[N, litH, h]) p
      else
      let lit ← cert
      let chk := app ``PNet.checkCert #[N, lit]
      ensure chk (app ``PNet.diagnose #[N, fuelE])
      closeWithCheck goal chk (fun h => app ``PNet.correct_of_checkCert #[N, lit, h]) p
  else if let some (C₀, p) := matchCircuit tgt then
    -- evaluate the circuit to a literal once (e.g. `withWires`), then check bit-packed states
    -- (`Circuit.bisimP`) natively in the kernel
    let C := toExpr (← evalAs Circuit C₀)
    match p with
    | .persistent =>
      let lit := toExpr (← evalAs (ExplicitLTS.PCert ℕ) (app ``Circuit.mkPCertP #[C, fuelE]))
      let chk := app ``Circuit.checkPCertP #[C, lit]
      ensure chk (app ``Circuit.diagnoseSpeedIndependent #[C₀, fuelE])
      closeWithCheckLit goal chk
        (fun h => app ``Circuit.speedIndependent_of_checkPCertP #[C, lit, h]) p C₀ C
    | _ =>
      -- many signals: bitmaps, if they are estimated cheap
      if (← evalAs Circuit C₀).signals ≥ 14 then
        if ← decideBitmapC goal C₀ p 8192 20 (some 120.0) then return
      let litH := toExpr (← evalAs (ExplicitLTS.HomeCert ℕ) (app ``Circuit.mkCertHomeP #[C, fuelE]))
      let chkH := app ``Circuit.checkCertHomeP #[C, litH]
      if ← evalBool chkH then
        closeWithCheckLit goal chkH
          (fun h => app ``Circuit.correct_of_checkCertHomeP #[C, litH, h]) p C₀ C
      else
      let lit := toExpr (← evalAs (ExplicitLTS.Cert ℕ) (app ``Circuit.mkCertP #[C, fuelE]))
      let chk := app ``Circuit.checkCertP #[C, lit]
      ensure chk (app ``Circuit.diagnose #[C₀, fuelE])
      closeWithCheckLit goal chk (fun h => app ``Circuit.correct_of_checkCertP #[C, lit, h]) p C₀ C
  else if let some (N, g) := matchStg tgt then
    let cert : MetaM Expr := do
      return toExpr (← evalAs (ExplicitLTS.Cert StgState) (app ``Stg.mkCert #[N, fuelE]))
    let invCert : MetaM Expr := do
      return toExpr (← evalAs Stg.InvCert (app ``Stg.mkInvCert #[N, fuelE]))
    match g with
    | .spec p =>
      let litH := toExpr (← evalAs (ExplicitLTS.HomeCert StgState) (app ``Stg.mkCertHome #[N, fuelE]))
      let chkH := app ``Stg.checkCertHome #[N, litH]
      if ← evalBool chkH then
        closeWithCheck goal chkH (fun h => app ``Stg.correct_of_checkCertHome #[N, litH, h]) p
      else
      let lit ← cert
      let chk := app ``Stg.checkCert #[N, lit]
      ensure chk (app ``Stg.diagnose #[N, fuelE])
      closeWithCheck goal chk (fun h => app ``Stg.correct_of_checkCert #[N, lit, h]) p
    | .consistent =>
      let lit ← invCert
      let chk := app ``Stg.checkConsistent #[N, lit]
      ensure chk (app ``Stg.diagnoseConsistent #[N, fuelE])
      closeWithCheck goal chk (fun h => app ``Stg.consistent_of_check #[N, lit, h]) .correct
    | .csc =>
      let lit ← invCert
      let chk := app ``Stg.checkCSC #[N, lit]
      ensure chk (app ``Stg.diagnoseCSC #[N, fuelE])
      closeWithCheck goal chk (fun h => app ``Stg.csc_of_check #[N, lit, h]) .correct
    | .outputPersistent =>
      let lit ← invCert
      let chk := app ``Stg.checkOutputPersistent #[N, lit]
      ensure chk (app ``Stg.diagnoseOutputPersistent #[N, fuelE])
      closeWithCheck goal chk (fun h => app ``Stg.outputPersistent_of_check #[N, lit, h]) .correct
    | .conformant gates =>
      let lit ← invCert
      let chk := app ``Stg.checkConformant #[N, gates, lit]
      ensure chk (app ``Stg.diagnoseConformant #[N, gates, fuelE])
      closeWithCheck goal chk (fun h => app ``Stg.conformant_of_check #[N, gates, lit, h]) .correct
    | .impl gates p =>
      let lit ← invCert
      let lit' ← cert
      ensure (app ``Stg.checkConformant #[N, gates, lit])
        (app ``Stg.diagnoseConformant #[N, gates, fuelE])
      ensure (app ``Stg.checkCert #[N, lit']) (app ``Stg.diagnose #[N, fuelE])
      let chk := app ``Stg.checkImpl #[N, gates, lit, lit']
      closeWithCheck goal chk
        (fun h => app ``Stg.implementation_correct_of_check #[N, gates, lit, lit', h]) p
  else if let some (E, s₀, j, p) := matchExplicit tgt then
    decideExplicit goal E s₀ j p fuel
  else if let some (N, p) := matchNetwork tgt then
    let route ← mkAppM ``Network.route #[N]
    decideRouting goal N [route, ← mkAppM ``Network.firstHop #[N]] route p fuel "async_decide"
  else if let some (N, p) := matchWormhole tgt then
    decideWormhole goal N none p fuel "async_decide"
  else
    throwError "async_decide: unsupported goal{indentExpr tgt}\nExpected a property of a \
      concrete `PNet`, `Circuit`, `Stg` (or of an STG implementation) or `Network`, or \
      deadlock / livelock freedom of an explicit LTS."

end Tactic

/-- An option of `async_decide`: `(fuel := n)` or `(cap := k)`. -/
syntax asyncDecideOpt := " (" (&"fuel" <|> &"cap") " := " num ")"

/-- `async_decide` proves deadlock freedom, livelock freedom, liveness or persistence of a
concrete `PNet` / `Circuit` by a kernel-checked certificate (see `AsyncLean.Checker.Tactic`).
`(fuel := n)` bounds the number of explored states; `(cap := k)` checks a Petri net through
its counter abstraction with cap `k` (see `AsyncLean.Checker.Abstract`). -/
syntax (name := asyncDecideStx) "async_decide" asyncDecideOpt* : tactic

elab_rules : tactic
  | `(tactic| async_decide $opts*) => do
    let mut fuel := 100000
    let mut cap : Option ℕ := none
    for o in opts do
      match o with
      | `(asyncDecideOpt| (fuel := $n)) => fuel := n.getNat
      | `(asyncDecideOpt| (cap := $n)) => cap := some n.getNat
      | _ => Lean.Elab.throwUnsupportedSyntax
    -- large certificates are big terms: lift the recursion limit while handling them
    withTheReader Core.Context (fun ctx => { ctx with
        maxRecDepth := max ctx.maxRecDepth 1000000
        options := maxRecDepth.set ctx.options (max ctx.maxRecDepth 1000000) })
      (Tactic.asyncDecide fuel cap)

/-- `async_bdd` proves deadlock freedom, livelock freedom, liveness, correctness or safety of
a concrete safe `PNet` from a symbolic certificate: a decision diagram of an inductive
invariant with ranks, distances and witnesses, checked by the kernel without enumerating the
markings (`PNet.of_checkBDD`).  `(fuel := n)` bounds the number of diagram nodes. -/
syntax (name := asyncBddStx) "async_bdd" (" (" &"fuel" " := " num ")")? : tactic

elab_rules : tactic
  | `(tactic| async_bdd $[ (fuel := $n)]?) =>
    withTheReader Core.Context (fun ctx => { ctx with
        maxRecDepth := max ctx.maxRecDepth 1000000
        options := maxRecDepth.set ctx.options (max ctx.maxRecDepth 1000000) })
      (Tactic.asyncBDD (n.map (·.getNat) |>.getD 300000))

/-- `async_bitmap` proves `N.Correct`, deadlock freedom, livelock freedom, liveness or
`N.Bounded k` of a concrete bounded `PNet` from a *bitmap* certificate: the reachable
markings, packed by a layout of fields, grouped into chunks of bitmaps, each transition fired
on a whole chunk by one shift, checked by the kernel (`PNet.of_checkBitmap`).
`(chunks := n)` bounds the number of chunks. -/
syntax asyncBitmapOpt := " (" (&"chunks" <|> &"low" <|> &"seg") " := " num ")"

syntax (name := asyncBitmapStx) "async_bitmap" asyncBitmapOpt* : tactic

elab_rules : tactic
  | `(tactic| async_bitmap $opts*) => do
    let mut chunks := 100000
    let mut low := 20
    let mut seg := 0
    for o in opts do
      match o with
      | `(asyncBitmapOpt| (chunks := $n)) => chunks := n.getNat
      | `(asyncBitmapOpt| (low := $n)) => low := n.getNat
      | `(asyncBitmapOpt| (seg := $n)) => seg := n.getNat
      | _ => throwUnsupportedSyntax
    withTheReader Core.Context (fun ctx => { ctx with
        maxRecDepth := max ctx.maxRecDepth 1000000
        options := maxRecDepth.set ctx.options (max ctx.maxRecDepth 1000000) })
      (Tactic.asyncBitmap chunks low seg)

/-- `async_routing` proves `N.Correct`, `N.DeadlockFree` or `N.LivelockFree` for a concrete
interconnection network `N` with dynamic routing, like `async_decide`.
`async_routing (escape := R₁)` uses the routing subfunction `R₁` as the escape channels of
Duato's theorem. -/
syntax (name := asyncRoutingStx) "async_routing" (" (" &"escape" " := " term ")")?
  (" (" &"fuel" " := " num ")")? : tactic

elab_rules : tactic
  | `(tactic| async_routing $[ (escape := $e)]? $[ (fuel := $n)]?) =>
    withTheReader Core.Context (fun ctx => { ctx with
        maxRecDepth := max ctx.maxRecDepth 1000000
        options := maxRecDepth.set ctx.options (max ctx.maxRecDepth 1000000) }) do
      let goal ← getMainGoal
      let tgt ← instantiateMVars (← goal.getType)
      let fuel := n.map (·.getNat) |>.getD 100000
      if let some (N, p) := Tactic.matchWormhole tgt then
        let esc? ← e.mapM fun e => do
          let (``Network, #[C, _]) := (← whnfR (← inferType N)).getAppFnArgs
            | throwError "async_routing: expected a network"
          instantiateMVars (← Tactic.elabTermEnsuringType e (← mkArrow C (mkConst ``Bool)))
        return ← Tactic.decideWormhole goal N esc? p fuel "async_routing"
      let some (N, p) := Tactic.matchNetwork tgt
        | throwError "async_routing: expected `N.Correct`, `N.DeadlockFree`, \
            `N.LivelockFree`, `N.StarvationFree` or a `Wormhole` goal for a concrete network `N`"
      match e with
      | some e =>
        let (``Network, #[C, P]) := (← whnfR (← inferType N)).getAppFnArgs
          | throwError "async_routing: expected a network"
        let ty ← mkArrow C (← mkArrow P (← mkAppM ``List #[← mkAppM ``Prod #[C, P]]))
        let esc ← instantiateMVars (← Tactic.elabTermEnsuringType e ty)
        Tactic.decideRouting goal N [esc] esc p fuel "async_routing"
      | none =>
        let route ← mkAppM ``Network.route #[N]
        Tactic.decideRouting goal N [route, ← mkAppM ``Network.firstHop #[N]] route p fuel
          "async_routing"

/-- `async_minimize` (or `async_minimize right`) replaces the left (right) component of a
parallel composition of explicit LTSs by its minimal quotient modulo branching bisimulation,
certified by the kernel; the goal must state deadlock and livelock freedom of the composition. -/
syntax (name := asyncMinimizeStx) "async_minimize" (&" right")? (" (" &"fuel" " := " num ")")? :
  tactic

elab_rules : tactic
  | `(tactic| async_minimize $[right%$r]? $[ (fuel := $n)]?) =>
    withTheReader Core.Context (fun ctx => { ctx with
        maxRecDepth := max ctx.maxRecDepth 1000000
        options := maxRecDepth.set ctx.options (max ctx.maxRecDepth 1000000) })
      (Tactic.minimize r.isSome (n.map (·.getNat) |>.getD 100000))

end AsyncLean

namespace AsyncLean.Tactic

open Lean Elab Tactic Meta

/-- `async_fast (parts := k)` proves a property of a concrete `PNet` by the fast explicit check
only (`PNet.checkFast`), as one kernel goal, or with `parts := k` (`k ≥ 1`) split into `k`
kernel goals (`PNet.checkFast_of_parts`). -/
syntax (name := asyncFastStx) "async_fast" (" (" &"parts" " := " num ")")? : tactic

elab_rules : tactic
  | `(tactic| async_fast $[(parts := $k)]?) => do
    let goal ← getMainGoal
    let tgt ← instantiateMVars (← goal.getType)
    let some (N, p) := matchPNet tgt | throwError "async_fast: unsupported goal{indentExpr tgt}"
    let (dl, ll, lv, thm) := match p with
      | .deadlock => (true, false, false, ``PNet.deadlockFree_of_checkFast)
      | .livelock => (false, true, false, ``PNet.livelockFree_of_checkFast)
      | .live => (false, false, true, ``PNet.live_of_checkFast)
      | _ => (true, true, true, ``PNet.correct_of_checkFast)
    let Nv ← evalAs PNet N
    let .ok (w, c) := Nv.mkFastCert dl ll lv 10000000 | throwError "async_fast: no certificate"
    withTheReader Core.Context (fun ctx => { ctx with
        maxRecDepth := max ctx.maxRecDepth 1000000
        options := maxRecDepth.set ctx.options (max ctx.maxRecDepth 1000000) }) do
      match k with
      | none =>
        let lit := FastExpr.pnetE Nv
        closeWithCheckLitM goal (FastExpr.checkFastE lit Nv w c dl ll lv)
          (fun h => mkAppM thm #[h]) N lit
      | some k =>
        unless ← closeFastParts goal N Nv w c dl ll lv thm k.getNat do
          throwError "async_fast: the goal does not match"

end AsyncLean.Tactic
