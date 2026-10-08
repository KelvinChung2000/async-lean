/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.BitmapPetri
import AsyncLean.Checker.BDDGen
import AsyncLean.Checker.BitmapCircuit

/-!
# Untrusted generation of bitmap certificates

Compiled code, not verified: a wrong certificate only makes the kernel check fail.

* `PNet.findLayout` explores a few thousand markings and groups the places into
  *components* — places of which exactly one is marked in every explored marking, and that
  every transition keeps balanced — packed as the index of the marked place, and counters
  for the other places.  Places that no transition consumes from are left out (unless all
  places are asked for), so an unbounded sink place costs nothing.
* `BitmapGen.forward` computes the reachable set chunk by chunk, firing each transition on a
  whole bitmap with one shift, exactly as the kernel will check it.
* Livelock freedom: rank layers by peeling (states whose internal successors are all ranked).
* Liveness: hubs, one per terminal strongly connected component (found by forward and
  backward reachability on bitmaps), distance layers by backward breadth-first search, and
  for each hub an explicit trace to a state enabling each transition.
-/

namespace AsyncLean

namespace BitmapGen

open Aff

/-! ### Compiled counterparts of the kernel functions -/

def fldC (x sh w : ℕ) : ℕ := (x >>> sh) &&& (2 ^ w - 1)

def cmpC (kind v c : ℕ) : Bool :=
  if kind = 0 then v == c else if kind = 1 then decide (c ≤ v) else decide (v ≤ c)

def ttestC (x : ℕ) (a : Test) : Bool := cmpC a.kind (fldC x a.sh a.w) a.c

def tallC (x : ℕ) (ts : List Test) : Bool := ts.all (ttestC x)

/-- The whole guard of a transition (compiled `Aff.gOk`). -/
def gOkC (x : ℕ) (e : Tr) : Bool := tallC x e.guard && e.bg.eval x.testBit

/-- Successors of a packed state (compiled `Aff.asucc`). -/
def asuccC (tb : Array Tr) (x : ℕ) : Array (ℕ × ℕ × Bool) := Id.run do
  let mut out := #[]
  for i in [0:tb.size] do
    let e := tb[i]!
    if gOkC x e then out := out.push (i, x + e.add - e.sub, tallC x e.ok)
  return out

def fullC (k : ℕ) : ℕ := (1 <<< (1 <<< k)) - 1

/-- The masks `bm k i` for `i < k`. -/
def bmsC (k : ℕ) : Array ℕ := Id.run do
  let mut out : Array ℕ := #[]
  for i in [0:k] do
    let mut r := 0
    for j in [0:k] do
      r := if i == j then fullC j <<< (1 <<< j) else r ||| (r <<< (1 <<< j))
    out := out.push r
  return out

/-- Context of the masks for chunks of `k` low bits. -/
structure Ctx where
  k : ℕ
  full : ℕ
  bms : Array ℕ

def Ctx.mk' (k : ℕ) : Ctx := ⟨k, fullC k, bmsC k⟩

def eqMaskC (cx : Ctx) (sh w c : ℕ) : ℕ := Id.run do
  if c ≥ 2 ^ w then return 0
  let mut r := cx.full
  for j in [0:w] do
    let b := cx.bms[sh + j]!
    r := r &&& (if c.testBit j then b else cx.full ^^^ b)
  return r

def tmaskC (cx : Ctx) (a : Test) : ℕ := Id.run do
  if a.kind = 0 then return eqMaskC cx a.sh a.w a.c
  let (lo, n) := if a.kind = 1 then (a.c, 2 ^ a.w - a.c) else (0, min (a.c + 1) (2 ^ a.w))
  let mut r := 0
  for i in [0:n] do
    r := r ||| eqMaskC cx a.sh a.w (lo + i)
  return r

def gLC (cx : Ctx) (ts : List Test) : ℕ :=
  ts.foldl (fun r a => if a.sh + a.w ≤ cx.k then r &&& tmaskC cx a else r) cx.full

def gHC (k h : ℕ) (ts : List Test) : Bool :=
  ts.all fun a => if k ≤ a.sh then cmpC a.kind (fldC h (a.sh - k) a.w) a.c else true

def shiftByC (S addL subL : ℕ) : ℕ := if subL ≤ addL then S <<< (addL - subL) else S >>> (subL - addL)

def unshiftByC (X addL subL : ℕ) : ℕ :=
  if subL ≤ addL then X >>> (addL - subL) else X <<< (subL - addL)

/-- The mask of a Boolean guard in the chunk `h` (compiled `Bitmap.bmaskE`). -/
def bmaskEC (cx : Ctx) (h : ℕ) : BExpr → ℕ
  | .var i => if i < cx.k then cx.bms[i]! else if h.testBit (i - cx.k) then cx.full else 0
  | .const b => if b then cx.full else 0
  | .not e => cx.full ^^^ bmaskEC cx h e
  | .and a b => bmaskEC cx h a &&& bmaskEC cx h b
  | .or a b => bmaskEC cx h a ||| bmaskEC cx h b
  | .xor a b => bmaskEC cx h a ^^^ bmaskEC cx h b

/-- A transition, prepared for chunks of `k` low bits. -/
structure TInfo where
  gL₀ : ℕ
  oL : ℕ
  guard : List Test
  ok : List Test
  addH : ℕ
  addL : ℕ
  subH : ℕ
  subL : ℕ
  internal : Bool
  bg : BExpr
  bgTrue : Bool
  k : ℕ
  cx : Ctx

/-- The guard mask of a transition in the chunk `h` (compiled `Bitmap.gLB`). -/
def TInfo.gLAt (t : TInfo) (h : ℕ) : ℕ := if t.bgTrue then t.gL₀ else t.gL₀ &&& bmaskEC t.cx h t.bg

def tinfo (cx : Ctx) (e : Tr) (internal : Bool) : TInfo :=
  let m := 2 ^ cx.k - 1
  ⟨gLC cx e.guard, gLC cx e.ok, e.guard, e.ok, e.add >>> cx.k, e.add &&& m, e.sub >>> cx.k,
    e.sub &&& m, internal, e.bg, e.bg matches .const true, cx.k, cx⟩

abbrev BSet := Std.HashMap ℕ ℕ

def BSet.get (s : BSet) (h : ℕ) : ℕ := s.getD h 0

/-- The lowest set bit of a nonzero number. -/
def lsb (b : ℕ) : ℕ := Id.run do
  let mut i := 0
  let mut x := b
  -- skip whole 64-bit words first
  while x &&& (2 ^ 64 - 1) == 0 do
    x := x >>> 64
    i := i + 64
  while !x.testBit 0 do
    x := x >>> 1
    i := i + 1
  return i

/-- A state of `s` (as a packed number), if any. -/
def BSet.any (s : BSet) (k : ℕ) : Option ℕ := Id.run do
  let mut best : Option ℕ := none
  for (h, b) in s do
    if b != 0 then
      let x := h * 2 ^ k + lsb b
      match best with
      | none => best := some x
      | some y => if x < y then best := some x
  return best

def BSet.diff (a b : BSet) : BSet := Id.run do
  let mut out : BSet := {}
  for (h, x) in a do
    let d := x ^^^ (x &&& b.get h)
    if d != 0 then out := out.insert h d
  return out

def BSet.subset (a b : BSet) : Bool := a.toList.all fun (h, x) => x &&& b.get h == x

def BSet.single (k x : ℕ) : BSet := ({} : BSet).insert (x >>> k) (1 <<< (x &&& (2 ^ k - 1)))

def BSet.count (s : BSet) : ℕ := s.fold (fun n _ b => n + (Nat.toDigits 2 b).count '1') 0

/-- **Forward reachability**: the states reachable from `init`, staying inside `within` if
given.  Fails on an overflow (an `ok` test failing) or a borrow/carry across the chunk
boundary, or beyond `maxChunks` chunks of `2 ^ (k + shift)` states. -/
def forward (cx : Ctx) (ti : Array TInfo) (init : BSet) (within : Option BSet)
    (maxChunks : ℕ) (shift : ℕ := 0) : Except String BSet := Id.run do
  let k := cx.k
  let mut all := init
  let mut frontier := init
  let mut big : Std.HashSet ℕ := init.fold (fun s h _ => s.insert (h >>> shift)) {}
  while !frontier.isEmpty do
    let mut next : BSet := {}
    for (h, F) in frontier do
      for t in ti do
        if F == 0 then continue
        if !gHC k h t.guard then continue
        let S := F &&& t.gLAt h
        if S == 0 then continue
        if !(gHC k h t.ok && (S &&& t.oL == S)) then return .error "overflow"
        if h + t.addH < t.subH then return .error "range"
        let lo := t.subL - t.addL
        let hi := 2 ^ k + t.subL - t.addL
        unless ((S >>> lo) <<< lo == S) && (S >>> hi == 0) do return .error "range"
        let h' := h + t.addH - t.subH
        let mut J := shiftByC S t.addL t.subL
        if let some w := within then J := J &&& w.get h'
        let old := all.get h'
        let new := J ^^^ (J &&& old)
        if new != 0 then
          if old == 0 then big := big.insert (h' >>> shift)
          all := all.insert h' (old ||| new)
          next := next.insert h' (next.get h' ||| new)
      if big.size > maxChunks then return .error "too many chunks"
    frontier := next
  return .ok all

/-- **Backward reachability** inside `A` from `B₀`; with `layers`, the cumulative layers of
each chunk, by breadth-first distance. -/
def backward (cx : Ctx) (ti : Array TInfo) (A B₀ : BSet) :
    BSet × ℕ := Id.run do
  let k := cx.k
  let mut B := B₀
  let mut frontier := B₀
  let mut d := 0
  let mut rounds := 0
  while !frontier.isEmpty do
    d := d + 1
    let mut next : BSet := {}
    for (h', F) in frontier do
      for t in ti do
        if h' + t.subH < t.addH then continue
        let h := h' + t.subH - t.addH
        let a := A.get h
        if a == 0 then continue
        if !gHC k h t.guard then continue
        if h + t.addH - t.subH != h' then continue
        let P := t.gLAt h &&& unshiftByC F t.addL t.subL &&& a
        let old := B.get h
        let new := P ^^^ (P &&& old)
        if new != 0 then
          B := B.insert h (old ||| new)
          next := next.insert h (next.get h ||| new)
    if !next.isEmpty then rounds := d
    frontier := next
  return (B, rounds)

/-- Rounds of ranking by peeling, as the kernel computes them (`Bitmap.rankIter`): a round
adds the states whose internal successors all have been added.  `none` if internal steps form
a cycle. -/
def rankRounds (cx : Ctx) (ti : Array TInfo) (A : BSet) : Option ℕ := Id.run do
  let k := cx.k
  let tis := ti.filter (·.internal)
  let mut done : BSet := {}
  let mut r := 0
  let mut rest := A
  while !rest.isEmpty do
    let mut added : BSet := {}
    for (h, a) in rest do
      let mut bad := 0
      for t in tis do
        if !gHC k h t.guard then continue
        if h + t.addH < t.subH then continue
        let h' := h + t.addH - t.subH
        let open' := (A.get h') ^^^ ((A.get h') &&& done.get h')
        if open' == 0 then continue
        bad := bad ||| (t.gLAt h &&& unshiftByC open' t.addL t.subL)
      let N := a ^^^ (a &&& bad)
      if N != 0 then added := added.insert h N
    if added.isEmpty then return none
    for (h, N) in added do
      done := done.insert h (done.get h ||| N)
    rest := A.diff done
    r := r + 1
  return some (max r 1)

/-- A state of a terminal strongly connected component reachable from `y`. -/
partial def terminalFrom (cx : Ctx) (ti : Array TInfo) (A : BSet) (y : ℕ) (maxChunks : ℕ) :
    Except String ℕ := do
  let F ← forward cx ti (BSet.single cx.k y) (some A) maxChunks
  let (B, _) := backward cx ti F (BSet.single cx.k y)
  if F.subset B then return y
  match (F.diff B).any cx.k with
  | some z => terminalFrom cx ti A z maxChunks
  | none => return y

/-- An explicit trace from the hub `s` to a state enabling each label `0 … L-1`. -/
def traces (tb : Array Tr) (L s fuel : ℕ) : Except String (List (List ℕ)) := Id.run do
  let mut parent : Std.HashMap ℕ ℕ := ({} : Std.HashMap ℕ ℕ).insert s s
  let mut order : Array ℕ := #[s]
  let mut found : Array (Option ℕ) := Array.replicate L none
  let mut nfound := 0
  let mut oi := 0
  while oi < order.size && nfound < L do
    if order.size > fuel then return .error "trace search exceeds the fuel"
    let v := order[oi]!
    oi := oi + 1
    for (i, w, ok) in asuccC tb v do
      if ok && i < L && found[i]!.isNone then
        found := found.set! i (some v)
        nfound := nfound + 1
      if ok && !parent.contains w then
        parent := parent.insert w v
        order := order.push w
  let mut trs : List (List ℕ) := []
  for i in [0:L] do
    let some v := found[i]! | return .error s!"transition {i} is not live"
    let mut path : List ℕ := []
    let mut x := v
    let mut steps := 0
    while x != s && steps ≤ order.size do
      path := x :: path
      x := parent.getD x s
      steps := steps + 1
    trs := trs ++ [path]
  return .ok trs

/-- Build a balanced search tree of chunks. -/
def chunkTree (cs : Array (ℕ × ℕ)) : BTree (ℕ × ℕ) :=
  let sorted := cs.qsort (fun a b => a.1 < b.1)
  Fast.buildTree sorted (sorted.size + 1) 0 sorted.size

/-- The same set with chunks of `k₁ ≥ k₀` low bits. -/
def BSet.regroup (A : BSet) (k₀ k₁ : ℕ) : BSet :=
  A.fold (fun s h b =>
    let h' := h >>> (k₁ - k₀)
    let off := (h &&& (2 ^ (k₁ - k₀) - 1)) * 2 ^ k₀
    s.insert h' (s.get h' ||| (b <<< off))) {}

/-- The states of `A` enabling a transition of `ts`. -/
def enabledIn (cx : Ctx) (ts : Array TInfo) (A : BSet) : BSet := Id.run do
  let mut out : BSet := {}
  for (h, a) in A do
    let mut en := 0
    for t in ts do
      if gHC cx.k h t.guard then en := en ||| t.gLAt h
    let x := a &&& en
    if x != 0 then out := out.insert h x
  return out

def BSet.union (a b : BSet) : BSet := b.fold (fun s h x => s.insert h (s.get h ||| x)) a

/-- A mask of transition numbers. -/
def maskOf (is : List ℕ) : ℕ := is.foldl (fun m i => m ||| (1 <<< i)) 0

/-- **Compute a bitmap certificate** for the table `tb` from `s₀`, with `k` low bits.
`rankCands` are candidate rank potentials `(weights, decreasing internal transitions)` and
`distCands`, given the hubs, candidate distance potentials `(weights, decreasing, not
increasing)`; the candidate needing the fewest rounds is kept. -/
def mkCert (tb : Array Tr) (internal : ℕ → Bool) (k₀ k L : ℕ) (dl ll lv : Bool) (s₀ : ℕ)
    (rankCands : List (List ℕ × ℕ)) (distCands : List ℕ → List (List ℕ × ℕ × ℕ))
    (maxChunks : ℕ := 200000) :
    Except String (Bitmap.Cert × BSet × (List ℕ × ℕ) × (List ℕ × ℕ × ℕ)) := do
  -- explore with small chunks: a sparse set exceeds the budget quickly
  let cx₀ := Ctx.mk' k₀
  let A₀ ← forward cx₀ (tb.map fun e => tinfo cx₀ e false) (BSet.single k₀ s₀) none maxChunks
    (k - k₀)
  let cx := Ctx.mk' k
  let ti := (tb.mapIdx fun i e => tinfo cx e (ll && internal i))
  let A := A₀.regroup k₀ k
  -- deadlock freedom
  if dl then
    for (h, a) in A do
      let mut en := 0
      for t in ti do
        if gHC k h t.guard then en := en ||| t.gLAt h
      let dead := a ^^^ (a &&& en)
      if dead != 0 then
        throw s!"deadlock at the packed state {h * 2 ^ k + lsb dead}"
  -- rounds of ranking, for the best rank potential
  let mut bestR : Option (ℕ × List ℕ × ℕ) := none
  for (w, dR) in rankCands do
    -- a single round cannot be improved on
    if let some (r', _, _) := bestR then if r' ≤ 1 then break
    let ti' := ti.mapIdx fun i t => { t with internal := t.internal && !dR.testBit i }
    if let some r := rankRounds cx ti' A then
      match bestR with
      | some (r', _, _) => if r < r' then bestR := some (r, w, dR)
      | none => bestR := some (r, w, dR)
  let some (rR, wR, dR) := bestR | throw "livelock: internal transitions form a cycle"
  -- hubs, and rounds of distances for the best distance potential
  let mut hubs : List (ℕ × List (List ℕ)) := []
  let mut rD := 0
  let mut potD : List ℕ × ℕ × ℕ := ([], 0, 2 ^ tb.size - 1)
  if lv then
    let mut hubStates : Array ℕ := #[]
    let mut rest := A
    -- first, the initial state: everything is reachable from it
    let (B₀, _) := backward cx ti A (BSet.single k s₀)
    if (A.diff B₀).isEmpty then
      hubStates := #[s₀]
      rest := {}
    while !rest.isEmpty do
      let some z := rest.any k | break
      let y ← terminalFrom cx ti A z maxChunks
      hubStates := hubStates.push y
      let H : BSet := hubStates.foldl (fun s x =>
        s.insert (x >>> k) (s.get (x >>> k) ||| (1 <<< (x &&& (2 ^ k - 1))))) {}
      let (B, _) := backward cx ti A H
      rest := A.diff B
    let H : BSet := hubStates.foldl (fun s x =>
      s.insert (x >>> k) (s.get (x >>> k) ||| (1 <<< (x &&& (2 ^ k - 1))))) {}
    let mut bestD : Option (ℕ × List ℕ × ℕ × ℕ) := none
    for (w, dD, kD) in distCands hubStates.toList ++ [([], 0, 2 ^ tb.size - 1)] do
      if let some (d', _, _, _) := bestD then if d' == 0 then break
      let decs := (ti.mapIdx fun i t => (i, t)).filter (fun (i, _) => dD.testBit i) |>.map (·.2)
      let keeps := (ti.mapIdx fun i t => (i, t)).filter (fun (i, _) => kD.testBit i) |>.map (·.2)
      let D₀ := H.union (enabledIn cx decs A)
      let (B, d) := backward cx keeps A D₀
      if (A.diff B).isEmpty then
        match bestD with
        | some (d', _, _, _) => if d < d' then bestD := some (d, w, dD, kD)
        | none => bestD := some (d, w, dD, kD)
    let some (d, w, dD, kD) := bestD | throw "some reachable marking reaches no hub"
    rD := d
    potD := (w, dD, kD)
    for y in hubStates do
      let trs ← traces tb L y 1000000
      hubs := hubs ++ [(y, trs)]
  return ((chunkTree A.toArray, hubs, rR, rD), A, (wR, dR), potD)

end BitmapGen

namespace PNet

open Aff BitmapGen

variable (N : PNet)

/-- Breadth-first exploration of up to `fuel` markings (untrusted). -/
def sample (fuel : ℕ) : Array (List ℕ) := Id.run do
  let mut seen : Std.HashSet (List ℕ) := ({} : Std.HashSet (List ℕ)).insert N.init
  let mut order : Array (List ℕ) := #[N.init]
  let mut i := 0
  while i < order.size && order.size < fuel do
    let m := order[i]!
    i := i + 1
    for (_, m') in N.succ m do
      if !seen.contains m' then
        seen := seen.insert m'
        order := order.push m'
  return order

/-- Bits needed for the values `0 … n`. -/
def bitsFor (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

/-- Is the group of places `ps` a component: balanced by every transition, one initial token? -/
def isComp (ps : List ℕ) : Bool :=
  N.trans.all (fun t => (ps.map t.pre.count).sum == (ps.map t.post.count).sum &&
    decide ((ps.map t.pre.count).sum ≤ 1)) &&
  (ps.map fun p => N.init.getD p 0).sum == 1

/-- **Find a layout** (untrusted): components found on a sample of the reachable markings,
counters for the other places.  `extra` adds bits to every counter; `allPlaces` keeps the
places that no transition consumes from. -/
def findLayout (extra : ℕ) (allPlaces : Bool) (fuel : ℕ := 3000) : List LField := Id.run do
  let smp := N.sample fuel
  let n := smp.size
  let allMask := 2 ^ n - 1
  let mut marked : Array ℕ := Array.replicate N.places 0
  let mut maxc : Array ℕ := Array.replicate N.places 0
  for j in [0:n] do
    let m := smp[j]!
    for p in [0:N.places] do
      let c := m.getD p 0
      if c > 0 then marked := marked.modify p (· ||| (1 <<< j))
      if c > maxc[p]! then maxc := maxc.set! p c
  let consumed : Array Bool := Id.run do
    let mut a := Array.replicate N.places false
    for t in N.trans do
      for p in t.pre do a := a.set! p true
    return a
  -- token flow between places: `t` consumes from `p` and produces into `q`
  let mut flow : Array (List ℕ) := Array.replicate N.places []
  for t in N.trans do
    for p in t.pre do
      for q in t.post do
        if p != q then
          flow := flow.modify p (q :: ·)
          flow := flow.modify q (p :: ·)
  let mut covered : Array Bool := Array.replicate N.places false
  let mut groups : Array (List ℕ) := #[]
  for p in [0:N.places] do
    if covered[p]! || maxc[p]! > 1 then continue
    -- grow a group of pairwise exclusive places, along the token flow first
    let mut g : List ℕ := [p]
    let mut U := marked[p]!
    let mut queue : List ℕ := flow[p]!
    let mut tried : Std.HashSet ℕ := ({} : Std.HashSet ℕ).insert p
    let mut steps := 0
    while U != allMask && steps < 4 * N.places do
      steps := steps + 1
      match queue with
      | q :: rest =>
        queue := rest
        if tried.contains q then continue
        tried := tried.insert q
        if covered[q]! || maxc[q]! > 1 then continue
        if marked[q]! &&& U == 0 then
          g := g ++ [q]
          U := U ||| marked[q]!
          queue := queue ++ flow[q]!
      | [] => break
    if U == allMask && N.isComp g then
      for q in g do covered := covered.set! q true
      groups := groups.push g
  -- fields: components, then counters
  let mut fields : Array LField := #[]
  let mut sh := 0
  for g in groups do
    let w := bitsFor (g.length - 1)
    fields := fields.push ⟨sh, w, g, true⟩
    sh := sh + w
  for p in [0:N.places] do
    if covered[p]! then continue
    if !allPlaces && !consumed[p]! then continue
    let w := max 1 (bitsFor maxc[p]!) + extra
    fields := fields.push ⟨sh, w, [p], false⟩
    sh := sh + w
  return fields.toList

/-- The fields of a layout reordered (`rev`) and repacked from bit `0`. -/
def repack (L : List LField) (rev : Bool) : List LField := Id.run do
  let L' := if rev then L.reverse else L
  let mut sh := 0
  let mut out : Array LField := #[]
  for f in L' do
    out := out.push { f with sh := sh }
    sh := sh + f.w
  return out.toList

/-- Total bits of a layout. -/
def layoutBits (L : List LField) : ℕ := L.foldl (fun a f => max a (f.sh + f.w)) 0

/-- Low bits for a layout: a field boundary near `target`. -/
def chooseK (L : List LField) (target : ℕ) : ℕ :=
  let B := layoutBits L
  if B ≤ target then B
  else L.foldl (fun k f => if f.sh + f.w ≤ target then max k (f.sh + f.w) else k) 0

/-- The weighted sum of an arc list, with multiplicity (as the kernel computes it). -/
def weightOf (w : List ℕ) (ps : List ℕ) : ℕ := (ps.map fun p => w.getD p 0).sum

/-- The transitions that the weights `w` strictly decrease, and those they do not increase. -/
def potMasks (w : List ℕ) : ℕ × ℕ := Id.run do
  let mut d := 0
  let mut k := 0
  let mut i := 0
  for t in N.trans do
    if weightOf w t.post < weightOf w t.pre then d := d ||| (1 <<< i)
    if weightOf w t.post ≤ weightOf w t.pre then k := k ||| (1 <<< i)
    i := i + 1
  return (d, k)

/-- Candidate rank potentials: a linear rank decreasing every internal transition, or a
lexicographic one. -/
def rankCands (ll : Bool) : List (List ℕ × ℕ) := Id.run do
  let ints := (List.range N.trans.length).filter fun i => (N.trans[i]?.map (·.internal)).getD false
  if !ll || ints.isEmpty then return [([], 0)]
  let imask := BitmapGen.maskOf ints
  let mut out : List (List ℕ × ℕ) := []
  for w? in [PNet.BDDGen.linRank N ints, some (PNet.BDDGen.linLex N ints)] do
    if let some w := w? then
      let (d, k) := N.potMasks w
      -- every internal transition must not increase the potential
      if k &&& imask == imask && d &&& imask != 0 then out := out ++ [(w, d &&& imask)]
  return out ++ [([], 0)]

/-- Candidate distance potentials, given the hubs (packed under `L`): weights decreasing the
transitions disabled at every hub. -/
def distCands (tb : Array Aff.Tr) (hubs : List ℕ) : List (List ℕ × ℕ × ℕ) := Id.run do
  let atHub := fun (i : ℕ) => hubs.any fun h => BitmapGen.gOkC h tb[i]!
  let gs := (List.range N.trans.length).filter fun i => !atHub i
  if gs.isEmpty then return []
  let mut out : List (List ℕ × ℕ × ℕ) := []
  for w? in [PNet.BDDGen.linRank N gs, some (PNet.BDDGen.linLex N gs)] do
    if let some w := w? then
      let (d, k) := N.potMasks w
      if d != 0 then out := out ++ [(w, d, k)]
  return out

/-- A cheap probe (untrusted): the state space is large (a sample of `fuel` markings does not
exhaust it) and dense once packed — the sampled markings share their high bits with at least
`8` others on average. -/
def bitmapDense (fuel : ℕ := 3000) : Bool := Id.run do
  let smp := N.sample fuel
  if smp.size < fuel then return false
  let L := repack (N.findLayout 0 false) false
  if !N.layoutOk L then return false
  let k₀ := min (layoutBits L) (chooseK L 12)
  let mut highs : Std.HashSet ℕ := {}
  for m in smp do
    highs := highs.insert (encV L (fun p => m.getD p 0) >>> k₀)
  return smp.size ≥ 8 * highs.size

/-- **A bitmap certificate for a net** (untrusted): the layout, the number of low bits, the
certificate, and the potentials of ranks and distances. -/
def mkBitmapCert (dl ll lv allPlaces : Bool) (maxChunks : ℕ := 100000) (target : ℕ := 20) :
    Except String (List LField × ℕ × Bitmap.Cert × (List ℕ × ℕ) × (List ℕ × ℕ × ℕ)) := do
  let mut last := "no layout"
  let rc := N.rankCands ll
  for extra in [0, 1, 3] do
    let L₀ := N.findLayout extra allPlaces
    if !N.layoutOk L₀ then
      last := "the layout fails its structural check"
      continue
    let mut best : Option (List LField × ℕ × Bitmap.Cert × (List ℕ × ℕ) × (List ℕ × ℕ × ℕ) × ℕ) :=
      none
    for rev in [false, true] do
      let L := repack L₀ rev
      let k := chooseK L target
      let k₀ := min k (chooseK L 12)
      let tb := (N.atable L).toArray
      match BitmapGen.mkCert tb (fun i => (N.trans[i]?.map (·.internal)).getD false) k₀ k
          N.trans.length dl ll lv (encV L N.initVec) rc (N.distCands tb) maxChunks with
      | .ok (c, A, pR, pD) =>
        match best with
        | some (_, _, _, _, _, n) => if A.size < n then best := some (L, k, c, pR, pD, A.size)
        | none => best := some (L, k, c, pR, pD, A.size)
      | .error e =>
        if e == "overflow" || e == "range" || e == "too many chunks" then last := e
        else throw e
      -- one order is enough when everything fits in one chunk
      if layoutBits L ≤ k then break
    if let some (L, k, c, pR, pD, _) := best then return (L, k, c, pR, pD)
  throw last

end PNet

namespace Circuit

variable (C : Circuit)

/-- **A bitmap certificate for a circuit** (untrusted): the number of low bits and the
certificate.  Signals are single bits, so any number of low bits fits. -/
def mkBitmapCert (dl ll lv : Bool) (maxChunks : ℕ := 100000) (target : ℕ := 20) :
    Except String (ℕ × Bitmap.Cert) := do
  let k := min C.signals target
  let k₀ := min k 12
  let (c, _, _, _) ← BitmapGen.mkCert C.btable.toArray (fun i => (C.gateD (i / 2)).internal) k₀ k
    (2 * C.gates.length) dl ll lv (C.bpack C.s₀) [([], 0)] (fun _ => []) maxChunks
  return (k, c)

end Circuit

end AsyncLean
