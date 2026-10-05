/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Auto.Simplex
import AsyncLean.Import.Basic
import AsyncLean.Petri.Invariant
import AsyncLean.MarkedGraph.Basic
import AsyncLean.Petri.FreeChoice
import Mathlib.Tactic.Linarith

/-!
# Automatic structural proofs

Structural arguments prove properties *without exploring the state space* — for every
marking reachable from the initial one, or even for every initial marking.  The tactic
`async_structural` finds the certificates automatically (by linear programming or graph
search, in untrusted code) and has the kernel check them:

* `N.Bounded k` / `N.Safe` for a `PNet` — a non-negative place invariant for every place
  (`PNet.bounded_of_pinvTable`);
* `N.toNet.lts.LivelockFree N.Internal M₀` (for any `M₀`) — a linear ranking function
  (`PNet.livelockFree_of_rankingTable`);
* `N.lts.Live M`, `N.lts.DeadlockFree M` for an ordinary free-choice net `N` — Commoner's
  siphon–trap property (`Net.live_of_siphonTrap`), decided by enumerating siphons, so only
  for nets with few places;
* `G.CircuitsMarked M`, `G.toNet.lts.Live M`, `G.toNet.lts.DeadlockFree M` for a marked graph
  over `Fin` types — a rank certificate for Commoner's theorem
  (`MarkedGraph.circuitsMarked_of_rankTable`).
-/

namespace AsyncLean

/-! ### Checkable forms of the structural theorems -/

namespace PNet

variable {N : PNet}

/-- Row `p` of an integer table, as a function. -/
def row (tbl : List (List ℤ)) (p q : ℕ) : ℤ := (tbl.getD p []).getD q 0

/-- **Boundedness from place invariants**: for every place `p`, a non-negative place invariant
`y` with `y · M₀ < (k + 1) · y p` shows that `p` never holds more than `k` tokens. -/
theorem bounded_of_pinvTable {k : ℕ} (tbl : List (List ℤ))
    (h : ∀ p : Fin N.places,
      N.toNet.IsPInvariant (fun q : Fin N.places => row tbl p q) ∧
      (∀ q : Fin N.places, 0 ≤ row tbl p q) ∧
      Net.weight (fun q : Fin N.places => row tbl p q) N.M₀ < ((k : ℤ) + 1) * row tbl p p) :
    N.Bounded k := by
  intro M hr p
  obtain ⟨hinv, hnn, hlt⟩ := h p
  have hb := hinv.bound hnn hr p
  have hw : 0 ≤ Net.weight (fun q : Fin N.places => row tbl p q) N.M₀ :=
    Finset.sum_nonneg fun q _ => mul_nonneg (hnn q) (Nat.cast_nonneg _)
  have hpos : 0 < row tbl p p := by nlinarith
  have : ((M p : ℕ) : ℤ) < (k : ℤ) + 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  omega

/-- **Livelock freedom from a linear ranking function**, for every initial marking. -/
theorem livelockFree_of_rankingTable (wl : List ℕ)
    (h : ∀ t, N.Internal t →
      ∑ p : Fin N.places, wl.getD p.val 0 * N.toNet.post t p <
        ∑ p : Fin N.places, wl.getD p.val 0 * N.toNet.pre t p)
    (M₀ : Marking (Fin N.places)) : N.toNet.lts.LivelockFree N.Internal M₀ :=
  Net.livelockFree_of_linearRanking _ h M₀

end PNet

namespace MarkedGraph

/-- **All circuits marked from a rank table.** -/
theorem circuitsMarked_of_rankTable {m n : ℕ} {G : MarkedGraph (Fin m) (Fin n)}
    {M : Marking (Fin m)} (rl : List ℕ)
    (h : ∀ p, M p = 0 → rl.getD (G.src p).val 0 < rl.getD (G.dst p).val 0) :
    G.CircuitsMarked M :=
  circuitsMarked_of_rank (fun t => rl.getD t.val 0) h

end MarkedGraph

/-! ### Certificate search (untrusted) -/

namespace Auto

/-- The incidence matrix `C[t][p] = post - pre`. -/
def incidence (N : PNet) : List (List ℤ) :=
  N.trans.map fun t => (List.range N.places).map fun p =>
    (t.post.count p : ℤ) - (t.pre.count p : ℤ)

/-- A non-negative place invariant `y` with `y p = 1` minimising `y · M₀`, scaled to integers. -/
def pinvFor (N : PNet) (p : ℕ) : Option (List ℤ) := do
  let C := incidence N
  let m := N.places
  let eqs : Array (Array Rat) := (C.map fun row => (row.map fun c => (c : Rat)).toArray).toArray
  let unit : Array Rat := (Array.range m).map fun q => if q == p then 1 else 0
  let A := eqs.push unit
  let b : Array Rat := ((List.replicate C.length (0 : Rat)) ++ [1]).toArray
  let c : Array Rat := (Array.range m).map fun q => ((N.init.getD q 0 : ℕ) : Rat)
  let y ← Simplex.solve A b c
  return Simplex.toInt y

/-- A linear ranking function for the internal transitions. -/
def rankingFor (N : PNet) : Option (List ℕ) := do
  let internal := N.trans.filter (·.internal)
  let m := N.places
  let k := internal.length
  -- variables: w (m), slacks (k);  Σ_p (pre - post) w_p - s_t = 1
  let A : Array (Array Rat) := (List.range k).toArray.map fun i =>
    let t := internal.getD i default
    ((Array.range m).map fun p => ((t.pre.count p : ℤ) - (t.post.count p : ℤ) : Rat)) ++
      (Array.range k).map fun j => if j == i then (-1 : Rat) else 0
  let b : Array Rat := (Array.range k).map fun _ => 1
  let c : Array Rat := (Array.range m).map (fun _ => (1 : Rat)) ++ (Array.range k).map fun _ => 0
  let x ← Simplex.solve A b c
  return Simplex.toNat (x.extract 0 m)

/-- Longest-path ranks of the transitions along empty places (`none` if the empty places
contain a cycle, i.e. a token-free circuit). -/
def mgRank (n : ℕ) (src dst M : List ℕ) : Option (List ℕ) :=
  let edges := ((List.range src.length).filter fun p => M.getD p 0 == 0).map fun p =>
    (src.getD p 0, dst.getD p 0)
  let step (r : Array ℕ) : Array ℕ := edges.foldl (fun r e =>
    r.set! e.2 (max (r[e.2]!) (r[e.1]! + 1))) r
  let r := (List.range (n + 1)).foldl (fun r _ => step r) (Array.replicate n 0)
  if edges.all fun e => r[e.1]! < r[e.2]! then some r.toList else none

end Auto

/-! ### The tactic -/

namespace Tactic

open Lean Meta Elab Tactic

unsafe def evalStructImpl {α : Type} [Inhabited α] (ty : Expr) (e : Expr) : MetaM α :=
  evalExpr α ty e

/-- Evaluate a closed term. -/
@[implemented_by evalStructImpl]
opaque evalStruct {α : Type} [Inhabited α] (ty : Expr) (e : Expr) : MetaM α

/-- Evaluate `(List.finRange k).map fun i => (f i).val` (or `f i` if `nat`). -/
def evalFinFun (k : ℕ) (f : Expr) (val : Bool) : MetaM (List ℕ) := do
  let finTy := mkApp (mkConst ``Fin) (mkNatLit k)
  let body ← withLocalDeclD `i finTy fun i => do
    let v := mkApp f i
    let v ← if val then mkAppM ``Fin.val #[v] else pure v
    mkLambdaFVars #[i] v
  let e ← mkAppM ``List.map #[body, ← mkAppOptM ``List.finRange #[mkNatLit k]]
  evalStruct (mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)) e

/-- The type of the first explicit hypothesis left after applying `thm` to `args`. -/
def hypType (thm : Name) (args : Array Expr) : MetaM Expr := do
  let ty ← instantiateForall (← inferType (mkConst thm)) args
  match ty with
  | .forallE _ d _ _ => pure d
  | _ => throwError "async_structural: internal error"

/-- Close `goal` with `pf`, proving its hypothesis `h : prop` by `decide +kernel`. -/
def closeDecide (goal : MVarId) (pf : Expr → MetaM Expr) (prop : Expr) : TacticM Unit := do
  let h ← mkFreshExprSyntheticOpaqueMVar prop
  let p ← pf h
  unless ← isDefEq (← inferType p) (← goal.getType) do
    throwError "async_structural: could not match the goal with{indentExpr (← inferType p)}"
  goal.assign p
  replaceMainGoal [h.mvarId!]
  evalTactic (← `(tactic| decide +kernel))

/-- The `async_structural` tactic. -/
def structural : TacticM Unit := do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let fail {α : Type} (msg : String) : TacticM α := throwError "async_structural: {msg}"
  match tgt.getAppFnArgs with
  | (``PNet.Bounded, #[N, _]) | (``PNet.Safe, #[N]) =>
    let k ← match tgt.getAppFnArgs with
      | (``PNet.Bounded, #[_, k]) => pure k
      | _ => pure (mkNatLit 1)
    let net : PNet ← evalStruct (mkConst ``PNet) N
    let kv : ℕ ← evalStruct (mkConst ``Nat) k
    let tbl ← (List.range net.places).mapM fun p => do
      match Auto.pinvFor net p with
      | some y => pure y
      | none => fail s!"place {p} is not covered by a non-negative place invariant"
    let tblE := toExpr tbl
    let pf (h : Expr) : MetaM Expr :=
      mkAppOptM ``PNet.bounded_of_pinvTable #[N, k, tblE, h]
    let prop ← hypType ``PNet.bounded_of_pinvTable #[N, k, tblE]
    let _ := kv
    closeDecide goal pf prop
  | (``LTS.LivelockFree, #[_, _, A, _, M₀]) =>
    let (``Net.lts, #[_, _, net]) := A.getAppFnArgs | fail "unsupported goal"
    let (``PNet.toNet, #[N]) := net.getAppFnArgs | fail "unsupported goal"
    let n : PNet ← evalStruct (mkConst ``PNet) N
    let some wl := Auto.rankingFor n
      | fail "no linear ranking function exists for the internal transitions (there may be \
          an internal cycle; try `async_decide`)"
    let wlE := toExpr wl
    let prop ← hypType ``PNet.livelockFree_of_rankingTable #[N, wlE]
    closeDecide goal (fun h => mkAppOptM ``PNet.livelockFree_of_rankingTable #[N, wlE, h, M₀])
      prop
  | (``MarkedGraph.CircuitsMarked, #[_, _, _, _, M]) | (``LTS.Live, #[_, _, _, M])
  | (``LTS.DeadlockFree, #[_, _, _, M]) =>
    -- find the marked graph
    let mg? : Option (Expr × Expr × Expr) := match tgt.getAppFnArgs with
      | (``MarkedGraph.CircuitsMarked, #[P, T, _, G, _]) => some (G, P, T)
      | (_, #[_, _, A, _]) =>
        match A.getAppFnArgs with
        | (``Net.lts, #[P, T, net]) =>
          match net.getAppFnArgs with
          | (``MarkedGraph.toNet, #[_, _, _, G]) => some (G, P, T)
          | _ => none
        | _ => none
      | _ => none
    let some (G, P, T) := mg?
      | -- not a marked graph: Commoner's theorem for free-choice nets
        match tgt.getAppFnArgs with
        | (``LTS.Live, #[_, _, A, _]) | (``LTS.DeadlockFree, #[_, _, A, _]) =>
          unless A.isAppOf ``Net.lts do fail "unsupported goal"
          if tgt.isAppOf ``LTS.Live then
            evalTactic (← `(tactic| refine Net.live_of_siphonTrap ?_ ?_ ?_))
          else
            evalTactic (← `(tactic| refine Net.deadlockFree_of_siphonTrap_fc ?_ ?_ ?_))
          evalTactic (← `(tactic| all_goals decide +kernel))
        | _ => fail "unsupported goal"
    let some m := (← whnf P).getAppFnArgs |> fun | (``Fin, #[m]) => some m | _ => none
      | fail "the places must be `Fin m`"
    let some n := (← whnf T).getAppFnArgs |> fun | (``Fin, #[n]) => some n | _ => none
      | fail "the transitions must be `Fin n`"
    let mv : ℕ ← evalStruct (mkConst ``Nat) m
    let nv : ℕ ← evalStruct (mkConst ``Nat) n
    let src ← evalFinFun mv (← mkAppM ``MarkedGraph.src #[G]) true
    let dst ← evalFinFun mv (← mkAppM ``MarkedGraph.dst #[G]) true
    let mk ← evalFinFun mv M false
    let some rl := Auto.mgRank nv src dst mk
      | fail "some directed circuit carries no token: the marked graph is not live \
          (Commoner's theorem)"
    let rlE := toExpr rl
    let prop ← hypType ``MarkedGraph.circuitsMarked_of_rankTable #[m, n, G, M, rlE]
    let pf (h : Expr) : MetaM Expr := do
      let c ← mkAppOptM ``MarkedGraph.circuitsMarked_of_rankTable #[m, n, G, M, rlE, h]
      match tgt.getAppFnArgs with
      | (``MarkedGraph.CircuitsMarked, _) => pure c
      | (``LTS.Live, _) => mkAppM ``MarkedGraph.live_of_circuitsMarked #[c]
      | _ => mkAppM ``MarkedGraph.deadlockFree_of_circuitsMarked #[c]
    closeDecide goal pf prop
  | _ => throwError "async_structural: unsupported goal{indentExpr tgt}"

end Tactic

/-- `async_structural` proves boundedness / safeness of a `PNet` (place invariants), livelock
freedom of a `PNet` for any initial marking (linear ranking function), or liveness / deadlock
freedom of a marked graph or a small free-choice net (Commoner's theorems), by kernel-checked certificates found by
linear programming or graph search. -/
elab "async_structural" : tactic =>
  withTheReader Lean.Core.Context (fun ctx => { ctx with
      maxRecDepth := max ctx.maxRecDepth 1000000
      options := Lean.maxRecDepth.set ctx.options (max ctx.maxRecDepth 1000000) })
    Tactic.structural

end AsyncLean
