/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Tactic.Goals

/-!
# The `async_decide` tactic, part 3: bitmap certificates and `async_bitmap`

Part 3 of 5 of `AsyncLean.Checker.Tactic`; that module has the overview.
-/

namespace AsyncLean

open Lean Meta Elab Tactic

namespace Tactic

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

end Tactic

end AsyncLean
