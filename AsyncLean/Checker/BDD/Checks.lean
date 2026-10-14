/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Packed
import AsyncLean.Checker.Fast

/-!
# Symbolic certificates: decision diagrams checked by the kernel, part 1: the certificate format and the trusted checker

Part 1 of 4 of `AsyncLean.Checker.BDD`; that module has the overview.
-/

namespace AsyncLean

namespace PNet

open Fast

/-- A decision node: its level (the order of variables), the place it reads, its children
(references), and the places known to be marked / unmarked on every path to it. -/
structure BNode where
  lvl : ℕ
  var : ℕ
  lo : ℕ
  hi : ℕ
  k1 : ℕ
  k0 : ℕ
  deriving Inhabited, Repr

/-- A leaf: witness transition, distance, rank, known places, and (at a hub) one trace per
transition. -/
structure BLeaf where
  wit : ℕ
  d : ℕ
  r : ℕ
  k1 : ℕ
  k0 : ℕ
  traces : List (List ℕ)
  /-- a leaf of the data diagram, whose checks apply -/
  dat : Bool
  deriving Inhabited, Repr

/-- The certificate for one transition: its input and output masks, the places it touches
`(place, level, kind)` (kind `0`: input only, `1`: input and output, `2`: output only), and
the triples of the joint walk, keyed by `tkey`. -/
structure BTrans where
  pre : ℕ
  post : ℕ
  us : List (ℕ × ℕ × ℕ)
  /-- the walks on the invariant, rank and data diagrams -/
  psI : BTree (ℕ × ℕ × ℕ × ℕ)
  psR : BTree (ℕ × ℕ × ℕ × ℕ)
  psD : BTree (ℕ × ℕ × ℕ × ℕ)
  /-- the lowest and highest levels touched; the walk on the invariant starts at the cut of
  level `lo` -/
  lo : ℕ := 0
  hi : ℕ := 0
  /-- the transition may be the witness of a leaf away from a hub; only then must it decrease
  the potential, or keep it and decrease the distance -/
  wit : Bool := true
  deriving Inhabited

/-- A symbolic certificate.  References: `2 i` is leaf `i` (leaf `0`: outside the invariant),
`2 k + 1` is node `k`; nodes have levels below `H`.  The nodes are packed, one number per
field (`PNet.nget`): the level, place and children of node `k` are its `k`-th field of `nw`
bits in `nlvl`, `nvar`, `nlo` and `nhi`, and its known places its `k`-th field of `kw` bits
in `nk1` and `nk0`, so that the kernel reads a node with a few shifts instead of a search. -/
structure BCert where
  H : ℕ
  /-- roots of the invariant, rank and data diagrams -/
  rI : ℕ
  rR : ℕ
  rD : ℕ
  ncnt : ℕ
  nw : ℕ
  kw : ℕ
  nlvl : ℕ
  nvar : ℕ
  nlo : ℕ
  nhi : ℕ
  nk1 : ℕ
  nk0 : ℕ
  leaves : BTree (ℕ × BLeaf)
  trans : List BTrans
  /-- the walks showing that the rank and data diagrams cover the invariant -/
  covR : BTree (ℕ × ℕ × ℕ × ℕ)
  covD : BTree (ℕ × ℕ × ℕ × ℕ)
  /-- with `linR`, livelock freedom from the linear rank with weights `wR` (one per place)
  instead of the rank diagram; otherwise from `wR` and the rank diagram, lexicographically -/
  linR : Bool := false
  wR : List ℕ := []
  /-- with `linD`, liveness from the linear potential with weights `wD`, decreased by the
  witness of every leaf away from a hub, instead of distances; otherwise from `wD` and the
  distances, lexicographically -/
  linD : Bool := false
  wD : List ℕ := []
  /-- the place read at each level, and the level of each place -/
  vars : List ℕ := []
  lvls : List ℕ := []
  /-- the cuts of the invariant: for each level, the references first reached at or below it -/
  cuts : List (List ℕ) := []
  deriving Inhabited

/-! ### The trusted checker -/

section Checks

variable {α : Type*}

/-- `l[i]?`, by the recursors. -/
noncomputable def knth (l : List α) : ℕ → Option α :=
  List.rec (motive := fun _ => ℕ → Option α) (fun _ => none)
    (fun x _ rec i => Nat.rec (motive := fun _ => Option α) (some x) (fun k _ => rec k) i) l

/-- `x ⊆ y` on bit masks. -/
noncomputable def sub (x y : ℕ) : Bool := Nat.beq (Nat.land x y) x

/-- The key of a triple. -/
def tkey (a b j : ℕ) : ℕ := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft a 32) b) 8) j

/-- The weighted sum `∑ ws[k] · bit (q + k) x` of the bits of `x`, by the recursor. -/
noncomputable def phiL (ws : List ℕ) (x : ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun w _ r q => Nat.add (cond (ktest x q) w 0) (r (Nat.succ q))) ws

/-- Firing a transition with these masks strictly decreases the linear potential `ws`. -/
noncomputable def decB (ws : List ℕ) (pre post : ℕ) : Bool :=
  Nat.blt (phiL ws post 0) (phiL ws pre 0)

/-- Firing a transition with these masks never increases the linear potential `ws`. -/
noncomputable def nincB (ws : List ℕ) (pre post : ℕ) : Bool :=
  Nat.ble (phiL ws post 0) (phiL ws pre 0)

/-- Bits `o` to `o + w - 1` of `x`. -/
noncomputable def bits (x o w : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight x o) (Nat.sub (Nat.pow 2 w) 1)

variable (c : BCert)

/-- Node `k`, from the packed tables. -/
noncomputable def nget (k : ℕ) : Option BNode :=
  bif Nat.blt k c.ncnt then
    some ⟨bits c.nlvl (Nat.mul k c.nw) c.nw, bits c.nvar (Nat.mul k c.nw) c.nw,
      bits c.nlo (Nat.mul k c.nw) c.nw, bits c.nhi (Nat.mul k c.nw) c.nw,
      bits c.nk1 (Nat.mul k c.kw) c.kw, bits c.nk0 (Nat.mul k c.kw) c.kw⟩
  else none

/-- The mask of the places listed. -/
noncomputable def umask (us : List (ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun u _ r => r ||| 2 ^ u.1) us

/-- `x ∈ l`. -/
noncomputable def memL (x : ℕ) (l : List ℕ) : Bool := kany l (Nat.beq x)

/-- `lvls` inverts `vars` (from level `L` on), so that each place is read at one level. -/
noncomputable def varsOk (lvls : List ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | p :: ps, L => (match knth lvls p with
      | some L' => Nat.beq L' L
      | none => false) && varsOk lvls ps (L + 1)

/-- The place read at level `L` is `p`. -/
noncomputable def varAt (vars : List ℕ) (L p : ℕ) : Bool :=
  match knth vars L with
  | some q => Nat.beq q p
  | none => false

/-- The node at a reference; a leaf is a pseudo-node at level `H` whose children are itself. -/
noncomputable def rinfo (r : ℕ) : Option BNode :=
  bif Nat.beq (Nat.land r 1) 0 then some ⟨c.H, 0, r, r, 0, 0⟩ else nget c (Nat.shiftRight r 1)

/-- The known places of a reference (leaf `0` knows nothing). -/
noncomputable def kOf (r : ℕ) : Option (ℕ × ℕ) :=
  bif Nat.beq (Nat.land r 1) 0 then
    (bif Nat.beq r 0 then some (0, 0)
     else (kfind (Nat.shiftRight r 1) c.leaves).map fun l => (l.k1, l.k0))
  else (nget c (Nat.shiftRight r 1)).map fun n => (n.k1, n.k0)

/-- Level and known places of a reference, with a single lookup. -/
noncomputable def cinfo (r : ℕ) : Option (ℕ × ℕ × ℕ) :=
  bif Nat.beq (Nat.land r 1) 0 then
    (bif Nat.beq r 0 then some (c.H, 0, 0)
     else (kfind (Nat.shiftRight r 1) c.leaves).map fun l => (c.H, l.k1, l.k0))
  else (nget c (Nat.shiftRight r 1)).map fun n => (n.lvl, n.k1, n.k0)

/-- The local checks of a node: levels increase towards the leaves, and the known places of
its children are justified by its own and by the place it reads. -/
noncomputable def nodeOk (n : BNode) : Bool :=
  Nat.blt n.lvl c.H && varAt c.vars n.lvl n.var &&
  (match cinfo c n.lo, cinfo c n.hi with
   | some a, some b => Nat.blt n.lvl a.1 && Nat.blt n.lvl b.1 &&
     sub a.2.1 n.k1 && sub a.2.2 (n.k0 ||| 2 ^ n.var) &&
       sub b.2.1 (n.k1 ||| 2 ^ n.var) && sub b.2.2 n.k0
   | _, _ => false)

/-- Simulate a trace from the packed marking `m`. -/
noncomputable def simB (tl : List BTrans) : ℕ → List ℕ → Option ℕ
  | m, [] => some m
  | m, j :: js => match knth tl j with
    | none => none
    | some e => bif sub e.pre m then simB tl ((m ^^^ e.pre) ||| e.post) js else none

/-- The `i`-th trace from `h` enables transition `i`. -/
noncomputable def tracesOk (tl : List BTrans) (h : ℕ) : List (List ℕ) → ℕ → Bool
  | [], _ => true
  | tr :: trs, i => (match simB tl h tr, knth tl i with
      | some m', some e => sub e.pre m'
      | _, _ => false) && tracesOk tl h trs (i + 1)

/-- The checks of a leaf: with `dl`, or with `lv` away from a hub, its witness is enabled;
with `lv`, a hub (distance `0`) is a single marking, with a trace enabling each of the `nT`
transitions; `full` is the mask of all places. -/
noncomputable def leafOk (dl lv : Bool) (nT full : ℕ) (x : ℕ × BLeaf) : Bool :=
  let l := x.2
  !l.dat || ((!(dl || (lv && !Nat.beq l.d 0)) ||
    (Nat.blt l.wit nT && match knth c.trans l.wit with
      | some e => sub e.pre l.k1 && (!(lv && !Nat.beq l.d 0) || e.wit)
      | none => false)) &&
  (!(lv && Nat.beq l.d 0) ||
    (sub full (l.k1 ||| l.k0) && Nat.blt l.k1 (full + 1) &&
      Nat.beq l.traces.length nT && tracesOk c.trans l.k1 l.traces 0)))

/-- The triple `(a, b, j)` is present. -/
noncomputable def memT (ps : BTree (ℕ × ℕ × ℕ × ℕ)) (a b j : ℕ) : Bool :=
  match kfind (tkey a b j) ps with
  | none => false
  | some x => Nat.beq x.1 a && Nat.beq x.2.1 b && Nat.beq x.2.2 j

/-- The condition on the leaves `a` (before) and `b` (after firing transition `i`): staying in
the diagram; in mode `1` decreasing the rank; in mode `2` decreasing the distance along the
witness; in modes `2` and `3` reaching a data leaf. -/
noncomputable def leafCond (md i a b : ℕ) : Bool :=
  Nat.beq a 0 || (!Nat.beq b 0 &&
    match kfind (a / 2) c.leaves, kfind (b / 2) c.leaves with
    | some la, some lb => (!Nat.beq md 1 || Nat.blt lb.r la.r) && (!Nat.ble 2 md || lb.dat) &&
        (!(Nat.beq md 2 && Nat.beq la.wit i && !Nat.beq la.d 0) || Nat.blt lb.d la.d)
    | _, _ => false)

/-- `b` is a leaf of the data diagram. -/
noncomputable def dataLeaf (b : ℕ) : Bool :=
  Nat.beq (Nat.land b 1) 0 && !Nat.beq b 0 &&
    (match kfind (Nat.shiftRight b 1) c.leaves with
     | some l => l.dat
     | none => false)

/-- A step of the joint walk on a place not touched by the transition. -/
noncomputable def untouched (e : BTrans) (ps : BTree (ℕ × ℕ × ℕ × ℕ)) (a b j : ℕ)
    (na nb : BNode) : Bool :=
  let L := cond (Nat.ble na.lvl nb.lvl) na.lvl nb.lvl
  let v := cond (Nat.ble na.lvl nb.lvl) na.var nb.var
  let sa := Nat.beq na.lvl L
  let sb := Nat.beq nb.lvl L
  Nat.blt L c.H && (!sa || Nat.beq na.var v) && (!sb || Nat.beq nb.var v) &&
    !ktest e.pre v && !ktest e.post v &&
    memT ps (cond sa na.lo a) (cond sb nb.lo b) j &&
    memT ps (cond sa na.hi a) (cond sb nb.hi b) j

/-- The local check of a triple `x = (key, a, b, j)` of the walk `ps` (in mode `md`) for
transition `i`. -/
noncomputable def tripleOk (md i : ℕ) (e : BTrans) (ps : BTree (ℕ × ℕ × ℕ × ℕ))
    (x : ℕ × ℕ × ℕ × ℕ) : Bool :=
  let a := x.2.1
  let b := x.2.2.1
  let j := x.2.2.2
  match rinfo c a, rinfo c b with
  | some na, some nb =>
    match knth e.us j with
    | some u =>
      bif Nat.ble u.2.1 na.lvl && Nat.ble u.2.1 nb.lvl then
        let sa := Nat.beq na.lvl u.2.1
        let sb := Nat.beq nb.lvl u.2.1
        (!sa || Nat.beq na.var u.1) && (!sb || Nat.beq nb.var u.1) &&
        (bif Nat.beq u.2.2 0 then memT ps (cond sa na.hi a) (cond sb nb.lo b) (j + 1)
         else bif Nat.beq u.2.2 1 then memT ps (cond sa na.hi a) (cond sb nb.hi b) (j + 1)
         else memT ps (cond sa na.hi a) 0 (j + 1) &&
           memT ps (cond sa na.lo a) (cond sb nb.hi b) (j + 1))
      else untouched c e ps a b j na nb
    | none =>
      bif Nat.blt na.lvl c.H || Nat.blt nb.lvl c.H then
        -- past the touched places, the same node before and after firing reads the same
        -- places; and a coverage walk that has reached a data leaf is done
        (Nat.beq md 0 && Nat.beq a b && Nat.blt e.hi na.lvl) ||
        (Nat.beq md 3 && Nat.blt na.lvl c.H && dataLeaf c b) ||
        untouched c e ps a b j na nb
      else leafCond c md i a b
  | _, _ => false

/-- The kind of a touched place agrees with the masks. -/
noncomputable def uOk (pre post : ℕ) (u : ℕ × ℕ × ℕ) : Bool :=
  bif Nat.beq u.2.2 0 then ktest pre u.1 && !ktest post u.1
  else bif Nat.beq u.2.2 1 then ktest pre u.1 && ktest post u.1
  else !ktest pre u.1 && ktest post u.1

/-- Mask of the output-only places listed. -/
noncomputable def kmask2 (us : List (ℕ × ℕ × ℕ)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun u _ r => bif Nat.ble 2 u.2.2 then r ||| 2 ^ u.1 else r) us

/-- A walk from the roots `ra`, `rb`. -/
noncomputable def walkOk (md i : ℕ) (e : BTrans) (ps : BTree (ℕ × ℕ × ℕ × ℕ)) (ra rb : ℕ) :
    Bool :=
  memT ps ra rb 0 && ktall ps (tripleOk c md i e ps)

/-- The walk on the invariant: from every reference of the cut at level `e.lo`. -/
noncomputable def walkCut (i : ℕ) (e : BTrans) : Bool :=
  (match knth c.cuts e.lo with
   | some cl => kall cl fun x => memT e.psI x x 0
   | none => false) &&
  ktall e.psI (tripleOk c 0 i e e.psI)

/-- The touched places lie between levels `lo` and `hi`, at the levels listed. -/
noncomputable def usOk (e : BTrans) (u : ℕ × ℕ × ℕ) : Bool :=
  Nat.ble e.lo u.2.1 && Nat.ble u.2.1 e.hi && varAt c.vars u.2.1 u.1

/-- The checks of transition `i`: on the invariant; with `ll`, if internal, it decreases the
linear rank, or keeps it and decreases the rank diagram; with `lv`, it decreases the linear
potential, or keeps it and decreases the distance wherever it is the witness (if it may be one,
`e.wit`). -/
noncomputable def transOk (ll lv int : Bool) (i : ℕ) (e : BTrans) : Bool :=
  kall e.us (uOk e.pre e.post) &&
  sub ((e.post &&& e.pre) ^^^ e.post) (kmask2 e.us) &&
  kall e.us (usOk c e) && sub (e.pre ||| e.post) (umask e.us) &&
  walkCut c i e &&
  (!(ll && int) || decB c.wR e.pre e.post ||
    (!c.linR && nincB c.wR e.pre e.post && walkOk c 1 i e e.psR c.rR c.rR)) &&
  (!(lv && c.linD && e.wit) || decB c.wD e.pre e.post) &&
  (!lv || c.linD || !e.wit || decB c.wD e.pre e.post ||
    (nincB c.wD e.pre e.post && walkOk c 2 i e e.psD c.rD c.rD))

/-- The certificates of the transitions, in order. -/
noncomputable def chkTrans (ll lv : Bool) : List PTrans → List BTrans → ℕ → Bool
  | [], [], _ => true
  | t :: ts, e :: es, i => Nat.beq (mask t.pre) e.pre && Nat.beq (mask t.post) e.post &&
      transOk c ll lv t.internal i e && chkTrans ll lv ts es (i + 1)
  | _, _, _ => false

/-- One step of the chain of cuts, at level `L`: a reference `x` of the cut is replaced in the
next cut by its children if it reads level `L`, and stays otherwise. -/
noncomputable def cutStep (L : ℕ) (nx : List ℕ) (x : ℕ) : Bool :=
  match rinfo c x with
  | some n => bif Nat.beq n.lvl L then memL n.lo nx && memL n.hi nx else memL x nx
  | none => false

/-- The chain of cuts from level `L`. -/
noncomputable def cutsOk : ℕ → List ℕ → List (List ℕ) → Bool
  | _, _, [] => true
  | L, cur, nx :: rest => kall cur (cutStep c L nx) && cutsOk (L + 1) nx rest

/-- The checks of node `k`. -/
noncomputable def nodeAt (k : ℕ) : Bool :=
  match nget c k with
  | some n => nodeOk c n
  | none => false

/-- The checks of every node of the table. -/
noncomputable def nodesOk : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k r => Bool.rec (motive := fun _ => Bool) false r (nodeAt c k)) c.ncnt

/-- Evaluate the diagram on a packed marking. -/
noncomputable def evalB (m : ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | f + 1, r => bif Nat.beq (r % 2) 0 then some r else
    match nget c (r / 2) with
    | none => none
    | some n => evalB m f (cond (m.testBit n.var) n.hi n.lo)

end Checks

/-- The empty transition, for the walks comparing two diagrams. -/
def emptyT : BTrans := ⟨0, 0, [], .leaf, .leaf, .leaf, 0, 0, true⟩

variable (N : PNet)

/-- **The symbolic check.** -/
noncomputable def checkBDD (dl ll lv : Bool) (c : BCert) : Bool :=
  N.packedWf && varsOk c.lvls c.vars 0 &&
  (match c.cuts with
   | c0 :: rest => memL c.rI c0 && cutsOk c 0 c0 rest
   | [] => false) &&
  (match kOf c c.rD with
   | some k => Nat.beq k.1 0 && Nat.beq k.2 0
   | none => false) &&
  nodesOk c &&
  ktall c.leaves (leafOk c dl lv N.trans.length (2 ^ N.places - 1)) &&
  chkTrans c ll lv N.trans c.trans 0 &&
  (!ll || c.linR || walkOk c 0 0 emptyT c.covR c.rI c.rR) &&
  (!(dl || lv) || walkOk c 3 0 emptyT c.covD c.rI c.rD) &&
  (match evalB c (N.pack N.M₀) (c.H + 1) c.rI with
   | some l => !Nat.beq l 0
   | none => false)

end PNet

end AsyncLean
