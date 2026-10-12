/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic.Bitmap

/-!
# The `async_decide` tactic, part 4: routing, explicit and abstract checks

Part 4 of 5 of `AsyncLean.Checker.Tactic`; that module has the overview.
-/

namespace AsyncLean

open Lean Meta Elab Tactic

namespace Tactic

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

/-- Recognise `N.MaximallyAdaptive U`; returns `N` and `U`. -/
def matchMaximal (tgt : Expr) : Option (Expr × Expr) :=
  match tgt.getAppFnArgs with
  | (``Network.MaximallyAdaptive, #[_, _, _, U, N]) => some (N, U)
  | _ => none

/-- Prove `N.MaximallyAdaptive U` by `Network.maximallyAdaptive_of_maxCheck`: the pairs a packet
can occupy, and a refutation tree for every hop of `U` that `N` does not permit. -/
def decideMaximal (goal : MVarId) (N U : Expr) (fuel : ℕ) (tac : String) : TacticM Unit := do
  let (``Network, #[C, P]) := (← whnfR (← inferType N)).getAppFnArgs
    | throwError "{tac}: expected a network"
  let cmpC ← mkAppOptM ``StateOrd.cmp #[C, none]
  let cmpQ ← mkAppOptM ``StateOrd.cmp #[← mkAppM ``Prod #[C, P], none]
  let pairs ← evalToLiteral (← mkAppM ``Network.explorePairs #[N, cmpQ, mkNatLit fuel])
  let certs ← evalToLiteral
    (← mkAppM ``Network.maxCerts #[cmpC, cmpQ, N, U, mkNatLit fuel, mkNatLit 2])
  let chk ← mkAppM ``Network.maxCheck #[cmpQ, N, U, pairs, certs]
  unless ← evalBool chk do
    let diag ← mkAppM ``Network.explainMaximal #[cmpC, cmpQ, N, U, mkNatLit fuel, mkNatLit 2]
    throwError "{tac}: {← evalString diag}"
  let h ← mkFreshExprSyntheticOpaqueMVar (← mkEq chk (mkConst ``Bool.true))
  let pf ← mkAppM ``Network.maximallyAdaptive_of_maxCheck #[h]
  unless ← isDefEq (← inferType pf) (← goal.getType) do
    throwError "{tac}: could not match the goal with{indentExpr (← inferType pf)}"
  goal.assign pf
  replaceMainGoal [h.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

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

end Tactic

end AsyncLean
