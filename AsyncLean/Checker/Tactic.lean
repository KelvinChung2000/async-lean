/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Petri
import AsyncLean.Checker.Diagnose
import AsyncLean.Circuit.Basic
import AsyncLean.Stg.Concrete

/-!
# The `async_decide` tactic

`async_decide` proves, for a concrete design, goals of the form

* `N.Correct`, `N.toNet.lts.DeadlockFree N.M₀`, `N.toNet.lts.LivelockFree N.Internal N.M₀`,
  `N.toNet.lts.Live N.M₀`, `N.toNet.lts.Persistent N.M₀` for a Petri net `N : PNet`;
* `C.Correct`, `C.lts.DeadlockFree C.s₀`, `C.lts.LivelockFree C.Internal C.s₀`,
  `C.lts.Live C.s₀`, `C.SpeedIndependent` for a gate-level circuit `C : Circuit`.

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
    if (st.tree.lookup Circuit.boolLexCmp p.1.2).isSome then st
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

/-! ### Evaluation at elaboration time -/

namespace Tactic

unsafe def evalAsImpl (α : Type) [Inhabited α] [ToExpr α] (e : Expr) : MetaM α :=
  evalExpr α (toTypeExpr α) e

/-- Evaluate a closed term of a type with a `ToExpr` instance (untrusted, compiled code). -/
@[implemented_by evalAsImpl]
opaque evalAs (α : Type) [Inhabited α] [ToExpr α] (e : Expr) : MetaM α

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

/-- Recognise a goal about a concrete circuit. -/
def matchCircuit (tgt : Expr) : Option (Expr × Goal) :=
  match tgt.getAppFnArgs with
  | (``Circuit.Correct, #[C]) => some (C, .correct)
  | (``Circuit.SpeedIndependent, #[C]) => some (C, .persistent)
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

/-- Fail with the diagnosis `diag` unless `checkE` evaluates to `true`. -/
def ensure (checkE diag : Expr) : MetaM Unit := do
  unless ← evalBool checkE do
    throwError "async_decide: {← evalString diag}"

/-- The `async_decide` tactic (see the module documentation). -/
def asyncDecide (fuel : ℕ) : TacticM Unit := do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let fuelE := mkNatLit fuel
  let app (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) args
  if let some (N, p) := matchPNet tgt then
    let lit := toExpr (← evalAs (ExplicitLTS.Cert (List ℕ)) (app ``PNet.mkCert #[N, fuelE]))
    match p with
    | .persistent =>
      let chk := app ``PNet.checkCertPersistent #[N, lit]
      ensure chk (app ``PNet.diagnosePersistent #[N, fuelE])
      closeWithCheck goal chk (fun h => app ``PNet.persistent_of_checkCert #[N, lit, h]) p
    | _ =>
      let chk := app ``PNet.checkCert #[N, lit]
      ensure chk (app ``PNet.diagnose #[N, fuelE])
      closeWithCheck goal chk (fun h => app ``PNet.correct_of_checkCert #[N, lit, h]) p
  else if let some (C, p) := matchCircuit tgt then
    let lit := toExpr (← evalAs (ExplicitLTS.Cert (List Bool)) (app ``Circuit.mkCert #[C, fuelE]))
    match p with
    | .persistent =>
      let chk := app ``Circuit.checkCertSpeedIndependent #[C, lit]
      ensure chk (app ``Circuit.diagnoseSpeedIndependent #[C, fuelE])
      closeWithCheck goal chk (fun h => app ``Circuit.speedIndependent_of_checkCert #[C, lit, h]) p
    | _ =>
      let chk := app ``Circuit.checkCert #[C, lit]
      ensure chk (app ``Circuit.diagnose #[C, fuelE])
      closeWithCheck goal chk (fun h => app ``Circuit.correct_of_checkCert #[C, lit, h]) p
  else if let some (N, g) := matchStg tgt then
    let cert : MetaM Expr := do
      return toExpr (← evalAs (ExplicitLTS.Cert StgState) (app ``Stg.mkCert #[N, fuelE]))
    let invCert : MetaM Expr := do
      return toExpr (← evalAs Stg.InvCert (app ``Stg.mkInvCert #[N, fuelE]))
    match g with
    | .spec p =>
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
  else
    throwError "async_decide: unsupported goal{indentExpr tgt}\nExpected a property of a \
      concrete `PNet`, `Circuit` or `Stg` (or of an STG implementation)."

end Tactic

/-- `async_decide` proves deadlock freedom, livelock freedom, liveness or persistence of a
concrete `PNet` / `Circuit` by a kernel-checked certificate (see `AsyncLean.Checker.Tactic`).
-/
syntax (name := asyncDecideStx) "async_decide" (" (" &"fuel" " := " num ")")? : tactic

elab_rules : tactic
  | `(tactic| async_decide $[ (fuel := $n)]?) =>
    -- large certificates are big terms: lift the recursion limit while handling them
    withTheReader Core.Context (fun ctx => { ctx with
        maxRecDepth := max ctx.maxRecDepth 1000000
        options := maxRecDepth.set ctx.options (max ctx.maxRecDepth 1000000) })
      (Tactic.asyncDecide (n.map (·.getNat) |>.getD 100000))

end AsyncLean
