/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.BDD
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Computing symbolic certificates (untrusted)

A small decision-diagram package and the computation of a certificate for `PNet.checkBDD`:

* a variable order, placing the places of each transition close together;
* the reachable markings, by symbolic breadth-first search (images transition by
  transition, valid for safe nets);
* ranks (layers of markings all of whose internal successors lie in lower layers), hubs (one
  marking in each terminal strongly connected component, found by alternating forward and
  backward closures), distances to the hubs with a witness transition per marking, and one
  trace from each hub to each transition;
* the diagrams of the invariant, of the ranks and of the witnesses and distances, their known
  places, and the triples of the joint walks.

Nothing here is trusted: `PNet.of_checkBDD` checks the result.
-/

namespace AsyncLean

namespace PNet

namespace BDDGen

open Std

/-- The node store: references as in `BCert` (`2 i` leaf `i`, `2 k + 1` node `k`). Plain
decision diagrams use leaf `0` for false and leaf `1` (reference `2`) for true. -/
structure Man where
  H : ℕ
  nodes : Array (ℕ × ℕ × ℕ) := #[]
  uniq : HashMap (ℕ × ℕ × ℕ) ℕ := {}

abbrev M := StateM Man

/-- Level, low child, high child (a leaf is its own child at level `H`). -/
@[inline] def nd (r : ℕ) : M (ℕ × ℕ × ℕ) := do
  if r % 2 == 0 then return ((← get).H, r, r) else return (← get).nodes[r / 2]!

def mk (l lo hi : ℕ) : M ℕ := do
  if lo == hi then return lo
  if let some r := (← get).uniq[(l, lo, hi)]? then return r
  modifyGet fun s =>
    let r := 2 * s.nodes.size + 1
    (r, { s with nodes := s.nodes.push (l, lo, hi), uniq := s.uniq.insert (l, lo, hi) r })

/-- Boolean operations: `0` and, `1` or, `2` and-not. -/
partial def bop (op : ℕ) (a b : ℕ) : StateT (HashMap (ℕ × ℕ) ℕ) M ℕ := do
  match op with
  | 0 => if a == 0 || b == 0 then return 0
         if a == 2 then return b
         if b == 2 || a == b then return a
  | 1 => if a == 2 || b == 2 then return 2
         if a == 0 then return b
         if b == 0 || a == b then return a
  | _ => if a == 0 || b == 2 || a == b then return 0
         if b == 0 then return a
  let key := if op != 2 && b < a then (b, a) else (a, b)
  if let some r := (← get)[key]? then return r
  let (la, al, ah) ← nd a
  let (lb, bl, bh) ← nd b
  let l := min la lb
  let (a0, a1) := if la == l then (al, ah) else (a, a)
  let (b0, b1) := if lb == l then (bl, bh) else (b, b)
  let r0 ← bop op a0 b0
  let r1 ← bop op a1 b1
  let r ← (mk l r0 r1 : M ℕ)
  modify (·.insert key r)
  return r

def band (a b : ℕ) : M ℕ := (bop 0 a b).run' {}
def bor (a b : ℕ) : M ℕ := (bop 1 a b).run' {}
def bdiff (a b : ℕ) : M ℕ := (bop 2 a b).run' {}

/-- Cofactor by a partial assignment of levels. -/
partial def restr (σ : Array (Option Bool)) (maxL : ℕ) (a : ℕ) :
    StateT (HashMap ℕ ℕ) M ℕ := do
  if a % 2 == 0 then return a
  if let some r := (← get)[a]? then return r
  let (l, lo, hi) ← nd a
  if l > maxL then return a
  let r ← match σ[l]! with
    | some true => restr σ maxL hi
    | some false => restr σ maxL lo
    | none => do
      let r0 ← restr σ maxL lo
      let r1 ← restr σ maxL hi
      (mk l r0 r1 : M ℕ)
  modify (·.insert a r)
  return r

/-- The cube of a partial assignment. -/
def cube (σ : Array (Option Bool)) : M ℕ := do
  let mut r := 2
  for i in [0:σ.size] do
    let l := σ.size - 1 - i
    match σ[l]! with
    | some true => r ← mk l 0 r
    | some false => r ← mk l r 0
    | none => pure ()
  return r

/-- Multi-terminal if-then-else with a Boolean condition. -/
partial def iteM (s x y : ℕ) : StateT (HashMap (ℕ × ℕ × ℕ) ℕ) M ℕ := do
  if s == 0 then return y
  if s == 2 || x == y then return x
  if let some r := (← get)[(s, x, y)]? then return r
  let (ls, s0, s1) ← nd s
  let (lx, x0, x1) ← nd x
  let (ly, y0, y1) ← nd y
  let l := min ls (min lx ly)
  let c := fun (lv a0 a1 a : ℕ) => if lv == l then (a0, a1) else (a, a)
  let (s0, s1) := c ls s0 s1 s
  let (x0, x1) := c lx x0 x1 x
  let (y0, y1) := c ly y0 y1 y
  let r0 ← iteM s0 x0 y0
  let r1 ← iteM s1 x1 y1
  let r ← (mk l r0 r1 : M ℕ)
  modify (·.insert (s, x, y) r)
  return r

/-- Combine two multi-terminal diagrams leaf by leaf. -/
partial def comb (f : ℕ → ℕ → ℕ) (a b : ℕ) : StateT (HashMap (ℕ × ℕ) ℕ) M ℕ := do
  if a % 2 == 0 && b % 2 == 0 then return 2 * f (a / 2) (b / 2)
  if let some r := (← get)[(a, b)]? then return r
  let (la, al, ah) ← nd a
  let (lb, bl, bh) ← nd b
  let l := min la lb
  let (a0, a1) := if la == l then (al, ah) else (a, a)
  let (b0, b1) := if lb == l then (bl, bh) else (b, b)
  let r0 ← comb f a0 b0
  let r1 ← comb f a1 b1
  let r ← (mk l r0 r1 : M ℕ)
  modify (·.insert (a, b) r)
  return r

/-- One marking (as a mask over places) of a non-empty set. -/
partial def pick (π : Array ℕ) (s : ℕ) (acc : ℕ := 0) : M ℕ := do
  if s % 2 == 0 then return acc
  let (l, lo, hi) ← nd s
  if lo != 0 then pick π lo acc else pick π hi (acc ||| 2 ^ π[l]!)

/-- The number of nodes reachable from `r`. -/
partial def size (r : ℕ) : M ℕ := do
  let mut seen : HashSet ℕ := {}
  let mut stack := [r]
  while true do
    match stack with
    | [] => break
    | x :: rest =>
      stack := rest
      if x % 2 == 0 || seen.contains x then continue
      seen := seen.insert x
      let (_, lo, hi) ← nd x
      stack := lo :: hi :: stack
  return seen.size

/-- The data of the net, in the variable order. -/
structure Ctx where
  n : ℕ
  /-- level → place, place → level -/
  π : Array ℕ
  lam : Array ℕ
  /-- per transition: input / output places, internal -/
  pre : Array (List ℕ)
  post : Array (List ℕ)
  internal : Array Bool
  /-- assignments before and after firing, and enabledness -/
  σpre : Array (Array (Option Bool))
  σpost : Array (Array (Option Bool))
  σen : Array (Array (Option Bool))

def Ctx.ofNet (N : PNet) : Ctx := Id.run do
  let n := N.places
  -- order: the places of each transition in turn
  let mut π : Array ℕ := #[]
  let mut seen : Array Bool := Array.replicate n false
  for t in N.trans do
    for p in t.pre ++ t.post do
      if p < n && !seen[p]! then
        π := π.push p
        seen := seen.set! p true
  for p in [0:n] do
    if !seen[p]! then π := π.push p
  let mut lam : Array ℕ := Array.replicate n 0
  for i in [0:n] do lam := lam.set! π[i]! i
  let asg := fun (ones zeros : List ℕ) => Id.run do
    let mut a : Array (Option Bool) := Array.replicate n none
    for p in zeros do a := a.set! lam[p]! (some false)
    for p in ones do a := a.set! lam[p]! (some true)
    return a
  let pre := N.trans.toArray.map (·.pre)
  let post := N.trans.toArray.map (·.post)
  let σpre := N.trans.toArray.map fun t => asg t.pre (t.post.filter (· ∉ t.pre))
  let σpost := N.trans.toArray.map fun t => asg t.post (t.pre.filter (· ∉ t.post))
  let σen := N.trans.toArray.map fun t => asg t.pre []
  return { n, π, lam, pre, post, internal := N.trans.toArray.map (·.internal), σpre, σpost, σen }

def maxLvl (σ : Array (Option Bool)) : ℕ := Id.run do
  let mut m := 0
  for i in [0:σ.size] do if σ[i]!.isSome then m := i
  return m

/-- Fire symbolically: the markings of `s` matching `src` on the touched levels `us` (sorted),
with these levels set to `dst`. -/
partial def fireOp (src dst : Array (Option Bool)) (us : Array ℕ) (s k : ℕ) :
    StateT (HashMap (ℕ × ℕ) ℕ) M ℕ := do
  if s == 0 then return 0
  if h : k < us.size then
    if let some r := (← get)[(s, k)]? then return r
    let u := us[k]
    let (l, lo, hi) ← nd s
    let set := fun (r : ℕ) => (if dst[u]! == some true then mk u 0 r else mk u r 0 : M ℕ)
    let r ← if u < l then do
        set (← fireOp src dst us s (k + 1))
      else if u == l then do
        set (← fireOp src dst us (if src[u]! == some true then hi else lo) (k + 1))
      else do
        let r0 ← fireOp src dst us lo k
        let r1 ← fireOp src dst us hi k
        (mk l r0 r1 : M ℕ)
    modify (·.insert (s, k) r)
    return r
  else return s

/-- The touched levels of an assignment, in order. -/
def touched (σ : Array (Option Bool)) : Array ℕ :=
  (Array.range σ.size).filter fun l => σ[l]!.isSome

/-- Image and preimage of a set under transition `t`. -/
def img (C : Ctx) (t s : ℕ) : M ℕ :=
  (fireOp C.σpre[t]! C.σpost[t]! (touched C.σpre[t]!) s 0).run' {}

def preimg (C : Ctx) (t s : ℕ) : M ℕ :=
  (fireOp C.σpost[t]! C.σpre[t]! (touched C.σpost[t]!) s 0).run' {}

def imgAll (C : Ctx) (s : ℕ) : M ℕ := do
  let mut r := 0
  for t in [0:C.pre.size] do r ← bor r (← img C t s)
  return r

def preAll (C : Ctx) (s : ℕ) : M ℕ := do
  let mut r := 0
  for t in [0:C.pre.size] do r ← bor r (← preimg C t s)
  return r

/-- Forward closure of `s`, by chaining the transitions. -/
def fwd (C : Ctx) (s : ℕ) (fuel : ℕ) : ExceptT String M ℕ := do
  let mut r := s
  repeat
    if (← get).nodes.size > fuel then throw "the decision diagrams exceed the fuel"
    let old := r
    for t in [0:C.pre.size] do r ← bor r (← img C t r)
    if r == old then break
  return r

/-- Backward closure of `s` inside `R`, by chaining. -/
def bwd (C : Ctx) (R s : ℕ) (fuel : ℕ) : ExceptT String M ℕ := do
  let mut r := s
  repeat
    if (← get).nodes.size > fuel then throw "the decision diagrams exceed the fuel"
    let old := r
    for t in [0:C.pre.size] do r ← bor r (← band (← preimg C t r) R)
    if r == old then break
  return r

/-- The marking `m` (a mask over places) as a diagram. -/
def minterm (C : Ctx) (m : ℕ) : M ℕ :=
  cube ((Array.range C.n).map fun l => some (m.testBit C.π[l]!))

/-- One trace from the marking `h` to a marking enabling `t`, by forward layers. -/
def trace (C : Ctx) (h t : ℕ) (fuel : ℕ) : ExceptT String M (List ℕ) := do
  let en ← cube C.σen[t]!
  let mut layers : Array ℕ := #[← minterm C h]
  let mut seen := layers[0]!
  let mut hit ← band layers[0]! en
  while hit == 0 do
    if (← get).nodes.size > fuel then throw "the decision diagrams exceed the fuel"
    let nx ← bdiff (← imgAll C layers.back!) seen
    if nx == 0 then throw s!"transition {t} is dead from a hub: the net is not live"
    layers := layers.push nx
    seen ← bor seen nx
    hit ← band nx en
  -- walk back through the layers
  let mut x ← pick C.π hit
  let mut tr : List ℕ := []
  let mut k := layers.size - 1
  while k > 0 do
    let xs ← minterm C x
    let mut found := false
    for t' in [0:C.pre.size] do
      unless found do
        let p ← band (← preimg C t' xs) layers[k - 1]!
        if p != 0 then
          x ← pick C.π p
          tr := t' :: tr
          found := true
    unless found do throw "trace reconstruction failed"
    k := k - 1
  return tr

/-- The successors of a triple in the joint walk (mirrors `PNet.tripleOk`); `none` at the
leaves. -/
def tsucc (H : ℕ) (info : ℕ → ℕ × ℕ × ℕ × ℕ) (U : Array (ℕ × ℕ × ℕ)) (a b j : ℕ) :
    Option (List (ℕ × ℕ × ℕ)) :=
  let (la, _, alo, ahi) := info a
  let (lb, _, blo, bhi) := info b
  let untouched := fun _ : Unit =>
    let L := min la lb
    let sa := la == L
    let sb := lb == L
    some [(if sa then alo else a, if sb then blo else b, j),
      (if sa then ahi else a, if sb then bhi else b, j)]
  if h : j < U.size then
    let (_, ul, uk) := U[j]
    if ul ≤ la && ul ≤ lb then
      let sa := la == ul
      let sb := lb == ul
      let a1 := if sa then ahi else a
      let a0 := if sa then alo else a
      let b1 := if sb then bhi else b
      let b0 := if sb then blo else b
      if uk == 0 then some [(a1, b0, j + 1)]
      else if uk == 1 then some [(a1, b1, j + 1)]
      else some [(a1, 0, j + 1), (a0, b1, j + 1)]
    else untouched ()
  else if la < H || lb < H then untouched () else none

/-- Compute a certificate for `checkBDD dl ll lv` (untrusted); also returns the number of
nodes of the diagram of reachable markings. -/
def mkBDDCert (N : PNet) (dl ll lv : Bool) (fuel : ℕ := 300000) :
    Except String (BCert × List ℕ) := do
  unless N.packedWf do throw "not a safe net without repeated arcs"
  let C := Ctx.ofNet N
  let n := C.n
  let nT := N.trans.length
  let m₀ := N.pack N.M₀
  let chk : ExceptT String M Unit := do
    if (← get).nodes.size > fuel then throw "the decision diagrams exceed the fuel"
  let act : ExceptT String M (BCert × List ℕ) := do
    let s0 ← minterm C m₀
    let R ← fwd C s0 fuel
    -- firing never marks a marked place
    for t in [0:nT] do
      for p in C.post[t]! do
        unless C.pre[t]!.contains p do
          let a := C.σen[t]!.set! C.lam[p]! (some true)
          if (← band R (← cube a)) != 0 then throw "the net is not safe"
    let mut en := 0
    for t in [0:nT] do en ← bor en (← cube C.σen[t]!)
    if dl && (← bdiff R en) != 0 then throw "deadlock"
    -- ranks: all internal successors of a layer lie in lower layers
    let mut rankSets : Array ℕ := #[R]
    if ll then
      let mut ienab := 0
      for t in [0:nT] do
        if C.internal[t]! then ienab ← bor ienab (← cube C.σen[t]!)
      let mut Z ← bdiff R ienab
      rankSets := #[Z]
      while Z != R do
        chk
        let rest ← bdiff R Z
        let mut bad := 0
        for t in [0:nT] do
          if C.internal[t]! then bad ← bor bad (← preimg C t rest)
        let Z' ← bor Z (← bdiff R bad)
        if Z' == Z then throw "livelock"
        rankSets := rankSets.push (← bdiff Z' Z)
        Z := Z'
    -- witnesses are preferred in the order in which the diagram decides them
    let worder := (Array.range nT).qsort fun a b =>
      let k := fun t => C.pre[t]!.foldl (fun m p => max m C.lam[p]!) 0
      k a < k b || (k a == k b && a < b)
    -- witnesses and distances: (set, witness, distance, hub)
    let mut parts : Array (ℕ × ℕ × ℕ × Option ℕ) := #[]
    let mut hubs : Array ℕ := #[]
    let mut traces : Array (List (List ℕ)) := #[]
    if lv then
      let mut covered := 0
      let mut s := m₀
      repeat
        -- descend to a terminal strongly connected component
        let mut x := s
        repeat
          let xs ← minterm C x
          let out ← bdiff (← fwd C xs fuel) (← bwd C R xs fuel)
          if out == 0 then break
          x ← pick C.π out
        hubs := hubs.push x
        covered ← bor covered (← bwd C R (← minterm C x) fuel)
        let rest ← bdiff R covered
        if rest == 0 then break
        s ← pick C.π rest
      let mut D := 0
      for h in hubs do D ← bor D (← minterm C h)
      let mut k := 0
      while D != R do
        chk
        let mut assigned := D
        for t in worder do
          let w ← bdiff (← band (← preimg C t D) R) assigned
          if w != 0 then
            parts := parts.push (w, t, k + 1, none)
            assigned ← bor assigned w
        if assigned == D then throw "some marking reaches no hub"
        D := assigned
        k := k + 1
      for i in [0:hubs.size] do
        let h := hubs[i]!
        let w := ((List.range nT).find? fun t => C.pre[t]!.all fun p => h.testBit p).getD 0
        parts := parts.push (← minterm C h, w, 0, some i)
        let mut trs : List (List ℕ) := []
        for t in [0:nT] do trs := trs ++ [← trace C h t fuel]
        traces := traces.push trs
    else if dl then
      let mut assigned := 0
      for t in worder do
        let w ← bdiff (← band R (← cube C.σen[t]!)) assigned
        if w != 0 then
          parts := parts.push (w, t, 0, none)
          assigned ← bor assigned w
    else parts := #[(R, 0, 0, none)]
    -- the diagrams: the invariant (leaf 1), the ranks (leaves `2 + k`) and the data (leaves
    -- `dbase + i`)
    let nR := rankSets.size
    let dbase := 2 + nR
    let rI := R
    let mut rR := 0
    if ll then
      for i in [0:nR] do
        let j := nR - 1 - i
        rR ← (iteM rankSets[j]! (2 * (2 + j)) rR).run' {}
    let mut rD := 0
    if dl || lv then
      for i in [0:parts.size] do
        let j := parts.size - 1 - i
        rD ← (iteM parts[j]!.1 (2 * (dbase + j)) rD).run' {}
    chk
    -- export the nodes reachable from the roots, numbered afresh
    let mut ids : HashMap ℕ ℕ := {}
    let mut order : Array ℕ := #[]
    let mut stack := [rI, rR, rD]
    let mut leafRefs : HashSet ℕ := {}
    while true do
      match stack with
      | [] => break
      | x :: rest =>
        stack := rest
        if x % 2 == 0 then
          if x != 0 then leafRefs := leafRefs.insert x
          continue
        if ids.contains x then continue
        ids := ids.insert x order.size
        order := order.push x
        let (_, lo, hi) ← nd x
        stack := lo :: hi :: stack
    let rename := fun (r : ℕ) => if r % 2 == 0 then r else 2 * ids.getD r 0 + 1
    let mut raw : Array (ℕ × ℕ × ℕ) := #[]
    for x in order do raw := raw.push (← nd x)
    -- known places, top-down by level, from every root
    let byLvl := (Array.range order.size).qsort fun i j => raw[i]!.1 < raw[j]!.1
    let mut K : HashMap ℕ (ℕ × ℕ) := {}
    for r in [rI, rR, rD] do K := K.insert r (0, 0)
    let meet := fun (K : HashMap ℕ (ℕ × ℕ)) (r : ℕ) (k : ℕ × ℕ) =>
      match K[r]? with
      | some k' => K.insert r (k.1 &&& k'.1, k.2 &&& k'.2)
      | none => K.insert r k
    for i in byLvl do
      let (l, lo, hi) := raw[i]!
      let v := C.π[l]!
      let k := K.getD order[i]! (0, 0)
      if lo != 0 then K := meet K lo (k.1, k.2 ||| 2 ^ v)
      if hi != 0 then K := meet K hi (k.1 ||| 2 ^ v, k.2)
    let nodesL : List (ℕ × BNode) := (List.range order.size).map fun i =>
      let (l, lo, hi) := raw[i]!
      let k := K.getD order[i]! (0, 0)
      (i, ⟨l, C.π[l]!, rename lo, rename hi, k.1, k.2⟩)
    let leavesL : List (ℕ × BLeaf) := leafRefs.toList.map fun ℓ =>
      let idx := ℓ / 2
      let k := K.getD ℓ (0, 0)
      if idx < 2 then (idx, ⟨0, 0, 0, k.1, k.2, [], false⟩)
      else if idx < dbase then (idx, ⟨0, 0, idx - 2, k.1, k.2, [], false⟩)
      else
        let (_, w, d, hub) := parts[idx - dbase]!
        (idx, ⟨w, d, 0, k.1, k.2, match hub with | some h => traces[h]! | none => [], true⟩)
    let nodeArr : Array (ℕ × ℕ × ℕ × ℕ) :=
      (nodesL.map fun (_, b) => (b.lvl, b.var, b.lo, b.hi)).toArray
    let info := fun (r : ℕ) => if r % 2 == 0 then (n, 0, r, r) else nodeArr[r / 2]!
    -- a joint walk
    let walk := fun (us : Array (ℕ × ℕ × ℕ)) (ra rb : ℕ) => Id.run do
      let mut seen : HashSet (ℕ × ℕ × ℕ) := {}
      let mut st := [(ra, rb, 0)]
      while true do
        match st with
        | [] => break
        | x :: rest =>
          st := rest
          if seen.contains x then continue
          seen := seen.insert x
          match tsucc n info us x.1 x.2.1 x.2.2 with
          | some l => st := l ++ st
          | none => pure ()
      let arr := (seen.toArray.map fun (a, b, j) => (tkey a b j, a, b, j)).qsort
        fun x y => x.1 < y.1
      return (Fast.buildTree arr (arr.size + 1) 0 arr.size, arr.size,
        seen.toList.all fun (_, b, j) => b < 4294967296 && j < 256)
    let (rI', rR', rD') := (rename rI, rename rR, rename rD)
    let mut trans : List BTrans := []
    let mut nTriples := 0
    for tp in N.trans do
      let us := ((tp.pre ++ tp.post).eraseDups.map fun p =>
        (p, C.lam[p]!, if tp.pre.contains p then (if tp.post.contains p then 1 else 0) else 2)).toArray.qsort
          fun x y => x.2.1 < y.2.1
      let (psI, k1, ok1) := walk us rI' rI'
      let (psR, k2, ok2) := if ll && tp.internal then walk us rR' rR' else (.leaf, 0, true)
      let (psD, k3, ok3) := if lv then walk us rD' rD' else (.leaf, 0, true)
      unless ok1 && ok2 && ok3 do throw "the diagram is too large for the triple keys"
      nTriples := nTriples + k1 + k2 + k3
      trans := trans ++ [⟨mask tp.pre, mask tp.post, us.toList, psI, psR, psD⟩]
    let (covR, k4, _) := if ll then walk #[] rI' rR' else (.leaf, 0, true)
    let (covD, k5, _) := if dl || lv then walk #[] rI' rD' else (.leaf, 0, true)
    let nodeT := nodesL.toArray
    let leafT := leavesL.toArray.qsort fun x y => x.1 < y.1
    return (⟨n, rI', rR', rD', Fast.buildTree nodeT (nodeT.size + 1) 0 nodeT.size,
      Fast.buildTree leafT (leafT.size + 1) 0 leafT.size, trans, covR, covD⟩,
      [← size rI, ← size rR, ← size rD, order.size, nTriples + k4 + k5])
  match (act.run.run' { H := n } : Except String (BCert × List ℕ)) with
  | .ok r => return r
  | .error e => throw e
end BDDGen

end PNet

end AsyncLean
