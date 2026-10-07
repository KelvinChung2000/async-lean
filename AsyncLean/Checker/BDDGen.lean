/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.BDD
import AsyncLean.Auto.Simplex
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Computing symbolic certificates (untrusted)

A small decision-diagram package and the computation of a certificate for `PNet.checkBDD`:

* a variable order, placing the places of each transition close together;
* the reachable markings, by *saturation*: each node is closed, bottom-up, under the
  transitions whose touched places all lie at or below its level, so that a firing is never
  repeated below its own levels (images transition by transition, valid for safe nets);
  backward closures likewise, constrained by the reachable markings;
* for livelock freedom, a linear rank found by linear programming; or else a linear rank that
  no internal transition increases, decreasing as many as possible, and ranks (layers of
  markings all of whose successors by the remaining internal transitions lie in lower layers);
* for liveness, hubs (one marking in each terminal strongly connected component, found by
  alternating forward and backward closures) and one trace from each hub to each transition,
  from chained rounds of images, walking back marking by marking; then a linear potential
  decreased by the witnesses, found by linear programming; or else distances to the hubs with
  a witness transition per marking, counting, when that is smaller, only the steps of the
  witnesses that keep a linear potential unchanged (a lexicographic measure);
* witnesses over the whole space, by enabledness, when no distances are needed;
* the diagrams, their known places, the cuts of the invariant, and the triples of the joint
  walks, which stop where the checker needs no more.

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

/-- The transitions as events of saturation: at each level, the source and target assignments
and touched levels of the transitions whose first touched level (nearest the root) it is
(forward), or the reverse (backward). -/
def Ctx.events (C : Ctx) (back : Bool) :
    Array (List (Array (Option Bool) × Array (Option Bool) × Array ℕ)) := Id.run do
  let mut evs := Array.replicate C.n []
  for t in [0:C.pre.size] do
    let us := touched C.σpre[t]!
    if h : 0 < us.size then
      let e := if back then (C.σpost[t]!, C.σpre[t]!, us) else (C.σpre[t]!, C.σpost[t]!, us)
      evs := evs.modify us[0] (e :: ·)
  return evs

/-- Saturation constrained by `c`: the least set containing `a ∩ c` and closed under the events
whose touched levels are all at least `L`, inside `c` (the diagrams `a` and `c` are read as
functions of the levels from `L` on).  Every node built is saturated in turn, bottom-up, so
that a firing never has to be repeated at the levels below its own.  Beyond `fuel` nodes it
gives up, returning a partial result. -/
partial def sat (evs : Array (List (Array (Option Bool) × Array (Option Bool) × Array ℕ)))
    (fuel n L a c : ℕ) : StateT (HashMap (ℕ × ℕ × ℕ) ℕ) M ℕ := do
  if a == 0 || c == 0 then return 0
  if L ≥ n || (← getThe Man).nodes.size > fuel then return a
  if let some r := (← get)[(L, a, c)]? then return r
  let split := fun (x : ℕ) => do
    let (lx, x0, x1) ← (nd x : M _)
    return if lx == L then (x0, x1) else (x, x)
  let (a0, a1) ← split a
  let (c0, c1) ← split c
  let r0 ← sat evs fuel n (L + 1) a0 c0
  let r1 ← sat evs fuel n (L + 1) a1 c1
  let mut r ← (mk L r0 r1 : M ℕ)
  let es := evs[L]!
  unless es.isEmpty do
    repeat
      let old := r
      for (src, dst, us) in es do
        let x ← (fireOp src dst us r 0).run' {}
        if x != 0 then
          let (x0, x1) ← split x
          let z0 ← sat evs fuel n (L + 1) x0 c0
          let z1 ← sat evs fuel n (L + 1) x1 c1
          r ← (bor r (← mk L z0 z1) : M ℕ)
      if r == old || (← getThe Man).nodes.size > fuel then break
  modify (·.insert (L, a, c) r)
  return r

/-- Forward closure of `s`, by saturation. -/
def fwd (C : Ctx) (s : ℕ) (fuel : ℕ) : ExceptT String M ℕ := do
  let r ← (sat (C.events false) fuel C.n 0 s 2).run' {}
  if (← get).nodes.size > fuel then throw "the decision diagrams exceed the fuel"
  return r

/-- Backward closure of `s` inside `R` (the markings of `R` from which `s` is reachable), by
saturation constrained by `R`. -/
def bwd (C : Ctx) (R s : ℕ) (fuel : ℕ) : ExceptT String M ℕ := do
  let r ← (sat (C.events true) fuel C.n 0 s R).run' {}
  if (← get).nodes.size > fuel then throw "the decision diagrams exceed the fuel"
  return r

/-- The marking `m` (a mask over places) as a diagram. -/
def minterm (C : Ctx) (m : ℕ) : M ℕ :=
  cube ((Array.range C.n).map fun l => some (m.testBit C.π[l]!))

/-- The marking `m` (a mask over places) belongs to the set `s`. -/
def mem (C : Ctx) (s m : ℕ) : M Bool := do
  let mut r := s
  let mut fuel := C.n + 1
  while r % 2 == 1 && fuel > 0 do
    let (l, lo, hi) ← nd r
    r := if m.testBit C.π[l]! then hi else lo
    fuel := fuel - 1
  return r != 0

/-- The marking before firing `t` into `x`, if `t` can fire into `x` (safe nets). -/
def predOf (C : Ctx) (t x : ℕ) : Option ℕ :=
  let pre := C.pre[t]!.foldl (fun m p => m ||| 2 ^ p) 0
  let post := C.post[t]!.foldl (fun m p => m ||| 2 ^ p) 0
  let y := (x ^^^ (x &&& post)) ||| pre
  if (y &&& pre) == pre && (y ^^^ pre) &&& post == 0 && ((y ^^^ pre) ||| post) == x then some y
  else none

/-- One trace from the marking `h` to a marking enabling each transition.  The transitions are
chained, in rounds, and every set reached is kept: a marking first reached by firing `t` has
its predecessor under `t` in the set before, so walking back marking by marking ends at `h`. -/
def traces (C : Ctx) (h : ℕ) (fuel : ℕ) : ExceptT String M (List (List ℕ)) := do
  let nT := C.pre.size
  let mut ens : Array ℕ := #[]
  for t in [0:nT] do ens := ens.push (← cube C.σen[t]!)
  -- the sets reached, each with the transition that extended the one before
  let mut snaps : Array (ℕ × ℕ) := #[(← minterm C h, nT)]
  let mut S := snaps[0]!.1
  let mut hit : Array (Option ℕ) := Array.replicate nT none
  repeat
    for t in [0:nT] do
      if hit[t]!.isNone && (← band S ens[t]!) != 0 then hit := hit.set! t (some (snaps.size - 1))
    if hit.all (·.isSome) then break
    if (← get).nodes.size > fuel then throw "the decision diagrams exceed the fuel"
    let old := S
    for t in [0:nT] do
      let S' ← bor S (← img C t S)
      if S' != S then
        S := S'
        snaps := snaps.push (S, t)
    if S == old then throw "a transition is dead from a hub: the net is not live"
  let mut out : List (List ℕ) := []
  for t in [0:nT] do
    let i0 := hit[t]!.getD 0
    let mut x ← pick C.π (← band snaps[i0]!.1 ens[t]!)
    let mut tr : List ℕ := []
    let mut i := i0
    -- invariant: `x` is in `snaps[i]`
    while i > 0 do
      -- the sets grow: the first one holding `x`, by galloping back, then bisection
      let mut step := 1
      let mut lo := i
      while lo > 0 && (← mem C snaps[lo - 1]!.1 x) do
        i := lo - 1
        lo := if step < lo then lo - step else 0
        step := 2 * step
      if i == 0 then break
      -- now `x` is in `snaps[i]`, and not in `snaps[lo - 1]` unless `lo = 0`
      lo := if lo == 0 then 0 else lo - 1
      if lo == 0 && (← mem C snaps[0]!.1 x) then break
      while lo + 1 < i do
        let mid := (lo + i) / 2
        if ← mem C snaps[mid]!.1 x then i := mid else lo := mid
      let t' := snaps[i]!.2
      match predOf C t' x with
      | some y =>
        x := y
        tr := t' :: tr
        i := i - 1
      | none => throw "trace reconstruction failed"
    out := out ++ [tr]
  return out

/-- Weights on the places, as small as possible, such that firing any of the transitions `ts`
strictly decreases the weighted sum of the marked places (`none` if there are none). -/
def linRank (N : PNet) (ts : List ℕ) : Option (List ℕ) := do
  let m := N.places
  let k := ts.length
  -- variables: w (m), slacks (k);  Σ_p (pre - post) w_p - s_t = 1
  let A : Array (Array Rat) := (List.range k).toArray.map fun i =>
    let (pre, post) := ((N.trans[ts.getD i 0]?).map fun t => (t.pre, t.post)).getD ([], [])
    ((Array.range m).map fun p => ((pre.count p : ℤ) - (post.count p : ℤ) : Rat)) ++
      (Array.range k).map fun j => if j == i then (-1 : Rat) else 0
  let b : Array Rat := (Array.range k).map fun _ => 1
  let c : Array Rat := (Array.range m).map (fun _ => (1 : Rat)) ++ (Array.range k).map fun _ => 0
  let x ← Simplex.solve A b c
  return Simplex.toNat (x.extract 0 m)

/-- Weights on the places that no transition of `ts` increases, and that decrease as many of
them as a linear relaxation finds (all zero if it fails): the first component of a
lexicographic measure. -/
def linLex (N : PNet) (ts : List ℕ) : List ℕ :=
  let m := N.places
  let k := ts.length
  let z := fun (n : ℕ) => (Array.range n).map fun _ => (0 : Rat)
  let unit := fun (n i : ℕ) (v : Rat) => (Array.range n).map fun j => if j == i then v else 0
  -- variables: w (m), δ (k), s (k), e (k);  (pre - post) · w - δ_t - s_t = 0,  δ_t + e_t = 1
  let A1 : Array (Array Rat) := (List.range k).toArray.map fun i =>
    let (pre, post) := ((N.trans[ts.getD i 0]?).map fun t => (t.pre, t.post)).getD ([], [])
    ((Array.range m).map fun p => ((pre.count p : ℤ) - (post.count p : ℤ) : Rat)) ++
      unit k i (-1) ++ unit k i (-1) ++ z k
  let A2 : Array (Array Rat) := (List.range k).toArray.map fun i =>
    z m ++ unit k i 1 ++ z k ++ unit k i 1
  let b : Array Rat := z k ++ (Array.range k).map fun _ => 1
  let c : Array Rat := z m ++ (Array.range k).map (fun _ => (-1 : Rat)) ++ z k ++ z k
  match Simplex.solve (A1 ++ A2) b c with
  | some x => Simplex.toNat (x.extract 0 m)
  | none => List.replicate m 0

/-- The linear potential `w` decreases strictly when `t` fires. -/
def decT (N : PNet) (w : List ℕ) (t : ℕ) : Bool :=
  let f := fun (l : List ℕ) => (l.eraseDups.map fun p => w.getD p 0).sum
  match N.trans[t]? with
  | some tp => f tp.post < f tp.pre
  | none => false

/-- The linear potential `w` does not increase when `t` fires. -/
def nincT (N : PNet) (w : List ℕ) (t : ℕ) : Bool :=
  let f := fun (l : List ℕ) => (l.eraseDups.map fun p => w.getD p 0).sum
  match N.trans[t]? with
  | some tp => f tp.post ≤ f tp.pre
  | none => false

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
    let internals := (List.range nT).filter fun t => C.internal[t]!
    -- a linear rank found together with the potential of the witnesses
    let mut wRU : Option (List ℕ) := none
    -- witnesses are preferred in the order in which the diagram decides them
    let worder := (Array.range nT).qsort fun a b =>
      let k := fun t => C.pre[t]!.foldl (fun m p => max m C.lam[p]!) 0
      k a < k b || (k a == k b && a < b)
    -- witnesses and distances: (set, witness, distance, hub)
    let mut parts : Array (ℕ × ℕ × ℕ × Option ℕ) := #[]
    let mut hubs : Array ℕ := #[]
    let mut traces : Array (List (List ℕ)) := #[]
    let mut wD : Option (List ℕ) := none
    -- the potential of a lexicographic measure, with the distances
    let mut wX : List ℕ := []
    let dsize := fun (ps : Array (ℕ × ℕ × ℕ × Option ℕ)) => do
      let mut r := 0
      for i in [0:ps.size] do
        r ← (iteM ps[ps.size - 1 - i]!.1 (2 * (ps.size - i)) r).run' {}
      size r
    if lv then
      let mut covered := 0
      let mut s := m₀
      repeat
        -- descend to a terminal strongly connected component
        let mut x := s
        let mut back := 0
        repeat
          let xs ← minterm C x
          back ← bwd C R xs fuel
          -- the markings reachable from the initial one are `R` itself
          let out ← bdiff (← if x == m₀ then pure R else fwd C xs fuel) back
          if out == 0 then break
          x ← pick C.π out
        hubs := hubs.push x
        covered ← bor covered back
        let rest ← bdiff R covered
        if rest == 0 then break
        s ← pick C.π rest
      let mut hubParts : Array (ℕ × ℕ × ℕ × Option ℕ) := #[]
      for i in [0:hubs.size] do
        let h := hubs[i]!
        let w := ((List.range nT).find? fun t => C.pre[t]!.all fun p => h.testBit p).getD 0
        hubParts := hubParts.push (← minterm C h, w, 0, some i)
        traces := traces.push (← BDDGen.traces C h fuel)
      -- a linear potential decreased by the witnesses replaces the distances when one exists:
      -- the witnesses are then the transitions it decreases, over the whole space
      let linParts := fun (w : List ℕ) => do
        let mut lparts := hubParts
        let mut assigned := 0
        for p in hubParts do assigned ← bor assigned p.1
        for t in worder do
          if decT N w t then
            let x ← bdiff (← cube C.σen[t]!) assigned
            if x != 0 then
              lparts := lparts.push (x, t, 1, none)
              assigned ← bor assigned x
        return if (← bdiff R assigned) == 0 then some lparts else none
      -- first guess: decrease every transition disabled at all hubs
      let atHub := fun (t : ℕ) => hubs.any fun h => C.pre[t]!.all fun p => h.testBit p
      let gs := (List.range nT).filter fun t => !atHub t
      -- with livelock freedom too, one linear program for both potentials if possible
      let wU := if ll then linRank N (gs ++ internals.filter (· ∉ gs)) else none
      if wU.isSome then wRU := wU
      let mut guess := none
      if let some w := wU then guess := (← linParts w).map (w, ·)
      if guess.isNone then
        if let some w := linRank N gs then guess := (← linParts w).map (w, ·)
      match guess with
      | some (w, lparts) =>
        parts := lparts
        wD := some w
      | none =>
        -- distances to the hubs, by backward layers
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
        -- second guess: decrease the witnesses of the distances
        let wits := (parts.toList.map (·.2.1)).eraseDups
        let lin ← match linRank N wits with
          | some w => pure ((← linParts w).map (w, ·))
          | none => pure none
        match lin with
        | some (w, lparts) =>
          parts := lparts
          wD := some w
        | none =>
          -- lexicographically: a potential that no witness increases; the witnesses that
          -- decrease it have distance `1`, and the distances count the steps of the others
          let w := linLex N wits
          let mut mparts := hubParts
          let mut assigned := 0
          for p in hubParts do assigned ← bor assigned p.1
          for t in worder do
            if decT N w t then
              let x ← bdiff (← band R (← cube C.σen[t]!)) assigned
              if x != 0 then
                mparts := mparts.push (x, t, 1, none)
                assigned ← bor assigned x
          let mut E := assigned
          let mut kx := 1
          let mut ok := true
          while ok && E != R do
            chk
            let mut a := E
            for t in worder do
              if !decT N w t && nincT N w t then
                let x ← bdiff (← band (← preimg C t E) R) a
                if x != 0 then
                  mparts := mparts.push (x, t, kx + 1, none)
                  a ← bor a x
            if a == E then ok := false
            E := a
            kx := kx + 1
          parts := parts ++ hubParts
          if ok && (← dsize mparts) < (← dsize parts) then
            parts := mparts
            wX := w
    else if dl then
      -- witnesses by enabledness: over the whole space, or only on the reachable markings,
      -- whichever diagram is smaller
      let mut full : Array (ℕ × ℕ × ℕ × Option ℕ) := #[]
      let mut onR : Array (ℕ × ℕ × ℕ × Option ℕ) := #[]
      let mut aF := 0
      let mut aR := 0
      for t in worder do
        let ent ← cube C.σen[t]!
        let x ← bdiff ent aF
        if x != 0 then
          full := full.push (x, t, 0, none)
          aF ← bor aF x
        let y ← bdiff (← band R ent) aR
        if y != 0 then
          onR := onR.push (y, t, 0, none)
          aR ← bor aR y
      parts := if (← dsize full) ≤ (← dsize onR) then full else onR
    else parts := #[(R, 0, 0, none)]
    -- ranks: a linear rank if one exists; otherwise a linear rank that the internal transitions
    -- never increase, then layers all of whose successors by the others (which keep it) lie in
    -- lower layers
    let wR := if ll then wRU <|> linRank N internals else none
    let linR := wR.isSome
    let wRx : List ℕ := wR.getD (if ll then linLex N internals else [])
    let flat := fun (t : ℕ) => C.internal[t]! && !decT N wRx t
    let mut rankSets : Array ℕ := #[R]
    if ll && !linR then
      let mut ienab := 0
      for t in [0:nT] do
        if flat t then ienab ← bor ienab (← cube C.σen[t]!)
      let mut Z ← bdiff R ienab
      rankSets := #[Z]
      while Z != R do
        chk
        let rest ← bdiff R Z
        let mut bad := 0
        for t in [0:nT] do
          if flat t then bad ← bor bad (← preimg C t rest)
        let Z' ← bor Z (← bdiff R bad)
        if Z' == Z then throw "livelock"
        rankSets := rankSets.push (← bdiff Z' Z)
        Z := Z'
    -- the diagrams: the invariant (leaf 1), the ranks (leaves `2 + k`) and the data (leaves
    -- `dbase + i`)
    let nR := rankSets.size
    let dbase := 2 + nR
    let rI := R
    let mut rR := 0
    if ll && !linR then
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
    let dataRef := fun (r : ℕ) => r % 2 == 0 && r != 0 && r / 2 ≥ dbase && leafRefs.contains r
    -- a joint walk in mode `md`, from the pairs `starts`; it stops where `PNet.tripleOk` needs
    -- no successors (below the touched places `us`, at most at level `hi`)
    let walk := fun (md : ℕ) (us : Array (ℕ × ℕ × ℕ)) (hi : ℕ) (starts : List (ℕ × ℕ)) => Id.run do
      let mut seen : HashSet (ℕ × ℕ × ℕ) := {}
      let mut st := starts.map fun (a, b) => (a, b, 0)
      while true do
        match st with
        | [] => break
        | x :: rest =>
          st := rest
          if seen.contains x then continue
          seen := seen.insert x
          let (a, b, j) := x
          let la := (info a).1
          if j ≥ us.size && (la < n || (info b).1 < n) &&
              ((md == 0 && a == b && hi < la) || (md == 3 && la < n && dataRef b)) then
            continue
          match tsucc n info us a b j with
          | some l => st := l ++ st
          | none => pure ()
      let arr := (seen.toArray.map fun (a, b, j) => (tkey a b j, a, b, j)).qsort
        fun x y => x.1 < y.1
      return (Fast.buildTree arr (arr.size + 1) 0 arr.size, arr.size,
        seen.toList.all fun (_, b, j) => b < 4294967296 && j < 256)
    let (rI', rR', rD') := (rename rI, rename rR, rename rD)
    -- the cuts of the invariant, level by level
    let mut cuts : Array (List ℕ) := #[[rI']]
    for L in [0:n] do
      let mut nx : Array ℕ := #[]
      for x in cuts[L]! do
        let (lx, _, lo, hi) := info x
        if lx == L then nx := nx.push lo |>.push hi else nx := nx.push x
      cuts := cuts.push (nx.qsort (· < ·)).toList.eraseDups
    let mut trans : List BTrans := []
    let mut nTriples := 0
    -- the transitions that are witnesses away from the hubs
    let wits := parts.foldl (fun (a : Array Bool) p =>
      if p.2.2.2.isNone then a.set! p.2.1 true else a) (Array.replicate nT false)
    for (tp, t) in N.trans.zip (List.range nT) do
      let wit := !lv || wits[t]!
      let us := ((tp.pre ++ tp.post).eraseDups.map fun p =>
        (p, C.lam[p]!, if tp.pre.contains p then (if tp.post.contains p then 1 else 0) else 2)).toArray.qsort
          fun x y => x.2.1 < y.2.1
      let lo := if h : 0 < us.size then us[0].2.1 else 0
      let hi := us.foldl (fun m u => max m u.2.1) 0
      let (psI, k1, ok1) := walk 0 us hi (cuts[lo]!.map fun x => (x, x))
      let (psR, k2, ok2) :=
        if ll && !linR && flat t then walk 1 us hi [(rR', rR')] else (.leaf, 0, true)
      let (psD, k3, ok3) :=
        if lv && wD.isNone && wit && !decT N wX t then walk 2 us hi [(rD', rD')]
        else (.leaf, 0, true)
      unless ok1 && ok2 && ok3 do throw "the diagram is too large for the triple keys"
      nTriples := nTriples + k1 + k2 + k3
      trans := trans ++ [⟨mask tp.pre, mask tp.post, us.toList, psI, psR, psD, lo, hi, wit⟩]
    let (covR, k4, _) := if ll && !linR then walk 0 #[] 0 [(rI', rR')] else (.leaf, 0, true)
    let (covD, k5, _) := if dl || lv then walk 3 #[] 0 [(rI', rD')] else (.leaf, 0, true)
    -- the packed node table: record `k` holds level, place, children and known places
    let maxv := nodesL.foldl (fun m (_, b) => max m (max b.lvl (max b.var (max b.lo b.hi)))) n
    let nw := Nat.log2 maxv + 1
    let kw := N.places
    let pack := fun (w : ℕ) (f : BNode → ℕ) =>
      nodesL.toArray.foldr (fun (_, b) acc => (acc <<< w) ||| f b) 0
    let leafT := leavesL.toArray.qsort fun x y => x.1 < y.1
    return (⟨n, rI', rR', rD', nodesL.length, nw, kw, pack nw (·.lvl), pack nw (·.var),
      pack nw (·.lo), pack nw (·.hi), pack kw (·.k1), pack kw (·.k0),
      Fast.buildTree leafT (leafT.size + 1) 0 leafT.size, trans, covR, covD,
      linR, wRx, wD.isSome, wD.getD wX, C.π.toList, C.lam.toList, cuts.toList⟩,
      [← size rI, ← size rR, ← size rD, order.size, nTriples + k4 + k5])
  match (act.run.run' { H := n } : Except String (BCert × List ℕ)) with
  | .ok r => return r
  | .error e => throw e
end BDDGen

end PNet

end AsyncLean
