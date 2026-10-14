/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic.Decide

/-!
# The `async_decide` tactic, part 5: `async_decide` and the tactic syntax

Part 5 of 5 of `AsyncLean.Checker.Tactic`; that module has the overview.
-/

namespace AsyncLean

open Lean Meta Elab Tactic

namespace Tactic

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
  else if let some (N, U) := matchMaximal tgt then
    decideMaximal goal N U fuel "async_decide"
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
