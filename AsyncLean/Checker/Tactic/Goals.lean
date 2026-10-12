/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic.Diagnosis

/-!
# The `async_decide` tactic, part 2: raw literals, goal recognition and the checks behind `async_bdd`

Part 2 of 5 of `AsyncLean.Checker.Tactic`; that module has the overview.
-/

namespace AsyncLean

open Lean Meta Elab Tactic

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
  let certT := mkConst ``Fast.Cert
  let dv : DefinitionVal :=
    { name := nm, levelParams := [], type := certT, value := FastExpr.certE c,
      hints := .opaque, safety := .safe }
  addDecl (.defnDecl dv)
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

end Tactic

end AsyncLean
