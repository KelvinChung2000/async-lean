/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Petri
import AsyncLean.Checker.Diagnose
import AsyncLean.Circuit.Basic

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

/-! ### Evaluation at elaboration time -/

namespace Tactic

unsafe def evalNatCertImpl (e : Expr) : MetaM (ExplicitLTS.Cert (List ℕ)) :=
  evalExpr (ExplicitLTS.Cert (List ℕ)) (toTypeExpr (ExplicitLTS.Cert (List ℕ))) e

unsafe def evalBoolCertImpl (e : Expr) : MetaM (ExplicitLTS.Cert (List Bool)) :=
  evalExpr (ExplicitLTS.Cert (List Bool)) (toTypeExpr (ExplicitLTS.Cert (List Bool))) e

unsafe def evalBoolImpl (e : Expr) : MetaM Bool := evalExpr Bool (mkConst ``Bool) e

unsafe def evalStringImpl (e : Expr) : MetaM String := evalExpr String (mkConst ``String) e

/-- Evaluate a certificate over markings. -/
@[implemented_by evalNatCertImpl]
opaque evalNatCert (e : Expr) : MetaM (ExplicitLTS.Cert (List ℕ))

/-- Evaluate a certificate over signal valuations. -/
@[implemented_by evalBoolCertImpl]
opaque evalBoolCert (e : Expr) : MetaM (ExplicitLTS.Cert (List Bool))

/-- Evaluate a Boolean. -/
@[implemented_by evalBoolImpl]
opaque evalBool (e : Expr) : MetaM Bool

/-- Evaluate a string. -/
@[implemented_by evalStringImpl]
opaque evalString (e : Expr) : MetaM String

/-- Which property a goal asks for. -/
inductive Prop' where
  | correct | deadlock | livelock | live | persistent

/-- Recognise a goal about a concrete Petri net. -/
def matchPNet (tgt : Expr) : Option (Expr × Prop') :=
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
def matchCircuit (tgt : Expr) : Option (Expr × Prop') :=
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

/-- Project the requested component out of a proof of `Correct`. -/
def project (pf : Expr) : Prop' → MetaM Expr
  | .correct | .persistent => pure pf
  | .deadlock => mkAppM ``And.left #[pf]
  | .livelock => do mkAppM ``And.left #[← mkAppM ``And.right #[pf]]
  | .live => do mkAppM ``And.right #[← mkAppM ``And.right #[pf]]

/-- Close `goal` with `thm M lit h`, where `h : check M lit = true` is proved by the kernel. -/
def closeWith (goal : MVarId) (thm check : Name) (M lit : Expr) (p : Prop') :
    TacticM Unit := do
  let hTy ← mkEq (mkApp2 (mkConst check) M lit) (mkConst ``Bool.true)
  let h ← mkFreshExprSyntheticOpaqueMVar hTy
  let pf ← project (mkApp3 (mkConst thm) M lit h) p
  goal.assign pf
  replaceMainGoal [h.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- The `async_decide` tactic (see the module documentation). -/
def asyncDecide (fuel : ℕ) : TacticM Unit := do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let fuelE := mkNatLit fuel
  if let some (N, p) := matchPNet tgt then
    let lit := toExpr (← evalNatCert (mkApp2 (mkConst ``PNet.mkCert) N fuelE))
    match p with
    | .persistent =>
      unless ← evalBool (mkApp2 (mkConst ``PNet.checkCertPersistent) N lit) do
        throwError "async_decide: {← evalString (mkApp2 (mkConst ``PNet.diagnosePersistent) N fuelE)}"
      closeWith goal ``PNet.persistent_of_checkCert ``PNet.checkCertPersistent N lit p
    | _ =>
      unless ← evalBool (mkApp2 (mkConst ``PNet.checkCert) N lit) do
        throwError "async_decide: {← evalString (mkApp2 (mkConst ``PNet.diagnose) N fuelE)}"
      closeWith goal ``PNet.correct_of_checkCert ``PNet.checkCert N lit p
  else if let some (C, p) := matchCircuit tgt then
    let lit := toExpr (← evalBoolCert (mkApp2 (mkConst ``Circuit.mkCert) C fuelE))
    match p with
    | .persistent =>
      unless ← evalBool (mkApp2 (mkConst ``Circuit.checkCertSpeedIndependent) C lit) do
        throwError "async_decide: {← evalString
          (mkApp2 (mkConst ``Circuit.diagnoseSpeedIndependent) C fuelE)}"
      closeWith goal ``Circuit.speedIndependent_of_checkCert ``Circuit.checkCertSpeedIndependent
        C lit p
    | _ =>
      unless ← evalBool (mkApp2 (mkConst ``Circuit.checkCert) C lit) do
        throwError "async_decide: {← evalString (mkApp2 (mkConst ``Circuit.diagnose) C fuelE)}"
      closeWith goal ``Circuit.correct_of_checkCert ``Circuit.checkCert C lit p
  else
    throwError "async_decide: unsupported goal{indentExpr tgt}\nExpected a correctness, \
      deadlock, livelock, liveness or persistence property of a concrete `PNet` or `Circuit`."

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
