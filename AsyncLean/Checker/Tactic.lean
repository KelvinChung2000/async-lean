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
import AsyncLean.Routing.WormholeCheck
import AsyncLean.Checker.Abstract
import AsyncLean.Import.Basic

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
      let pf ← mkAppM ``Network.wormholeCorrect_of_wcheckCert #[h]
      let pf ← match p with
        | .deadlock => mkAppM ``And.left #[pf]
        | .livelock => mkAppM ``And.right #[pf]
        | _ => pure pf
      unless ← isDefEq (← inferType pf) (← goal.getType) do
        throwError "{tac}: could not match the goal with{indentExpr (← inferType pf)}"
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
      -- a quick probe: if the state space does not close (e.g. an unbounded net), try the
      -- counter abstraction first
      unless ← evalBool (app ``PNet.closes #[N, mkNatLit (min fuel 10000)]) do
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
      -- fastest path: safe nets that can always return to their initial marking
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
