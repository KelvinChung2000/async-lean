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
import AsyncLean.Routing.Optimal

/-!
# The `async_decide` tactic, part 1: literal certificates and the diagnosis of failures

Part 1 of 5 of `AsyncLean.Checker.Tactic`; that module has the overview.
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

/-- Literal syntax tree for a network action. -/
def Network.Act.toExprAux {C P : Type} [ToExpr C] [ToExpr P] : Network.Act C P → Expr
  | .inject c p => mkApp4 (mkConst ``Network.Act.inject [Level.zero, Level.zero])
      (toTypeExpr C) (toTypeExpr P) (toExpr c) (toExpr p)
  | .hop c c' p' => mkApp5 (mkConst ``Network.Act.hop [Level.zero, Level.zero])
      (toTypeExpr C) (toTypeExpr P) (toExpr c) (toExpr c') (toExpr p')
  | .eject c => mkApp3 (mkConst ``Network.Act.eject [Level.zero, Level.zero])
      (toTypeExpr C) (toTypeExpr P) (toExpr c)

instance {C P : Type} [ToExpr C] [ToExpr P] : ToExpr (Network.Act C P) where
  toTypeExpr := mkApp2 (mkConst ``Network.Act [Level.zero, Level.zero]) (toTypeExpr C)
    (toTypeExpr P)
  toExpr := Network.Act.toExprAux

/-- Literal syntax tree for a refutation tree. -/
def Network.RefTree.toExprAux {C P : Type} [ToExpr C] [ToExpr P] : Network.RefTree C P → Expr
  | .leaf as => mkApp3 (mkConst ``Network.RefTree.leaf [Level.zero, Level.zero])
      (toTypeExpr C) (toTypeExpr P) (toExpr as)
  | .split c p q t₁ t₂ => mkAppN (mkConst ``Network.RefTree.split [Level.zero, Level.zero])
      #[toTypeExpr C, toTypeExpr P, toExpr c, toExpr p, toExpr q, t₁.toExprAux, t₂.toExprAux]

instance {C P : Type} [ToExpr C] [ToExpr P] : ToExpr (Network.RefTree C P) where
  toTypeExpr := mkApp2 (mkConst ``Network.RefTree [Level.zero, Level.zero]) (toTypeExpr C)
    (toTypeExpr P)
  toExpr := Network.RefTree.toExprAux

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

end AsyncLean
