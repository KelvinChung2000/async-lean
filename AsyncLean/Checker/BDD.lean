/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Packed
import AsyncLean.Checker.Fast

/-!
# Symbolic certificates: decision diagrams checked by the kernel

A safe net's reachable markings are sets of places, and a *binary decision diagram* often
describes such a set in a size that grows with the structure of the net rather than with the
number of markings.  `PNet.checkBDD` checks properties of a safe net from decision diagrams
over the places, without enumerating any marking:

* the markings of the *invariant* diagram form an inductive invariant: it contains the
  initial marking and is closed under firing, and firing never marks a marked place;
* the leaves of a *data* diagram, which covers the invariant, carry a *witness* transition
  enabled at every marking reaching the leaf (deadlock freedom); for liveness, either a
  *linear potential* (weights on the places) that every witness decreases, or, lexicographically,
  a linear potential that each witness decreases or keeps while decreasing a *distance*, down to
  *hubs* from which a trace enables each transition;
* for livelock freedom, either a linear rank that every internal transition decreases, or,
  lexicographically, a linear rank that each internal transition decreases or keeps while
  decreasing a *rank* diagram.

Closure is checked transition by transition, by a joint walk of a diagram before and after
firing: a set of *triples* `(a, b, j)` — a node `a` read before firing, a node `b` read after,
and the number `j` of places touched by the transition already passed — each checked locally
against its successors (`PNet.tripleOk`).  Which markings reach which leaf is the semantics
`PNet.Reach`; `PNet.TClaim` is what a triple guarantees.  Every node also carries the places
known to be marked (`k1`) and unmarked (`k0`) on every path to it, so the kernel can see that
a witness is enabled, or that a hub is a single marking, from the leaf alone.

Most of a walk is *diagonal*: the same node before and after firing, above or below the
places the transition touches.  Each level reads one place (`vars`, inverted by `lvls`), so
below the touched places a diagonal triple holds by itself (`PNet.Reach.congr`), and a walk on
the invariant starts at the *cut* of the lowest level touched — the references first reached
at or below it, checked level by level once for all transitions (`PNet.cut_reach`).  A walk
showing that the data diagram covers the invariant stops at the first data leaf.

`PNet.of_checkBDD` turns a successful check into deadlock freedom, livelock freedom, liveness
and safety of the net, through the packed semantics of `AsyncLean.Checker.Packed`.  The
diagrams are computed by untrusted code (`PNet.BDDGen.mkBDDCert`), symbolically: reachability,
witnesses, ranks and distances are all computed on decision diagrams, and the weights by
linear programming.
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

/-! ### Soundness -/

namespace AsyncLean

namespace PNet

open Fast

section Basic

variable {α : Type*}

theorem nbeq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases h' : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true h') h

theorem knth_eq (l : List α) (i : ℕ) : knth l i = l[i]? := by
  induction l generalizing i with
  | nil => rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ k => exact ih k

theorem sub_eq (x y : ℕ) : sub x y = Nat.beq (x &&& y) x := rfl

theorem cond_ble_min (a b : ℕ) : cond (Nat.ble a b) a b = min a b := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun h' => by simp [Nat.ble_eq.mpr h'] at h
    simp [min_eq_right (by omega : b ≤ a)]
  · have : a ≤ b := by simpa [Nat.ble_eq] using h
    simp [min_eq_left this]

theorem land_one (r : ℕ) : Nat.land r 1 = r % 2 := Nat.and_one_is_mod r

theorem shiftRight_one' (r : ℕ) : Nat.shiftRight r 1 = r / 2 := by
  rw [show Nat.shiftRight r 1 = r >>> 1 from rfl, Nat.shiftRight_eq_div_pow, pow_one]

theorem shr_one (r : ℕ) : r >>> 1 = r / 2 := by
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem sub_iff {x y : ℕ} : sub x y = true ↔ ∀ q, x.testBit q = true → y.testBit q = true := by
  rw [sub_eq, Nat.beq_eq]
  constructor
  · intro h q hq
    have := congrArg (fun z => Nat.testBit z q) h
    simp only [Nat.testBit_land, hq, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_land]
    cases hq : x.testBit q
    · rfl
    · simp [h q hq]

theorem testBit_kmask2 {us : List (ℕ × ℕ × ℕ)} {q : ℕ} (h : (kmask2 us).testBit q = true) :
    ∃ u ∈ us, 2 ≤ u.2.2 ∧ u.1 = q := by
  induction us with
  | nil => simp [kmask2] at h
  | cons u us ih =>
    change (bif Nat.ble 2 u.2.2 then kmask2 us ||| 2 ^ u.1 else kmask2 us).testBit q = true at h
    cases hb : Nat.ble 2 u.2.2
    · rw [hb] at h
      obtain ⟨v, hv, h'⟩ := ih h
      exact ⟨v, List.mem_cons_of_mem _ hv, h'⟩
    · rw [hb] at h
      simp only [Bool.cond_true, Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow,
        decide_eq_true_eq] at h
      rcases h with h | rfl
      · obtain ⟨v, hv, h'⟩ := ih h
        exact ⟨v, List.mem_cons_of_mem _ hv, h'⟩
      · exact ⟨u, List.mem_cons_self .., Nat.le_of_ble_eq_true hb, rfl⟩

end Basic

variable {c : BCert}

theorem memL_iff {x : ℕ} {l : List ℕ} : memL x l = true ↔ x ∈ l := by
  rw [memL, kany_eq, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, h⟩
    rw [Nat.eq_of_beq_eq_true h]; exact hy
  · intro h; exact ⟨x, h, Nat.beq_refl x⟩

theorem varAt_iff {vars : List ℕ} {L p : ℕ} : varAt vars L p = true ↔ knth vars L = some p := by
  unfold varAt
  cases knth vars L with
  | none => simp
  | some q => simp [Nat.beq_eq]

theorem varsOk_spec {lvls : List ℕ} : ∀ {vars : List ℕ} {L₀ : ℕ}, varsOk lvls vars L₀ = true →
    ∀ L p, knth vars L = some p → knth lvls p = some (L₀ + L)
  | [], _, _, L, p, h => by rw [knth_eq] at h; simp at h
  | q :: qs, L₀, hv, L, p, h => by
    simp only [varsOk, Bool.and_eq_true] at hv
    obtain ⟨h1, h2⟩ := hv
    cases L with
    | zero =>
      rw [knth_eq] at h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      split at h1
      · rename_i L' hL
        rw [hL, Nat.eq_of_beq_eq_true h1]; rfl
      · cases h1
    | succ k =>
      have h' : knth qs k = some p := by
        rw [knth_eq] at h ⊢; simpa using h
      rw [varsOk_spec h2 k p h']
      congr 1; omega

theorem vars_inj {c : BCert} (h : varsOk c.lvls c.vars 0 = true) {L L' p : ℕ}
    (h1 : knth c.vars L = some p) (h2 : knth c.vars L' = some p) : L = L' := by
  have a := varsOk_spec h L p h1
  have b := varsOk_spec h L' p h2
  rw [a] at b
  simpa using b

theorem testBit_umask {us : List (ℕ × ℕ × ℕ)} {q : ℕ} (h : (umask us).testBit q = true) :
    ∃ u ∈ us, u.1 = q := by
  induction us with
  | nil => simp [umask] at h
  | cons u us ih =>
    change (umask us ||| 2 ^ u.1).testBit q = true at h
    simp only [Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨v, hv, h'⟩ := ih h
      exact ⟨v, List.mem_cons_of_mem _ hv, h'⟩
    · exact ⟨u, List.mem_cons_self, h⟩

theorem knth_prev {β : Type*} {l : List β} {k : ℕ} {y : β} (h : knth l (k + 1) = some y) :
    ∃ z, knth l k = some z := by
  rw [knth_eq] at h ⊢
  obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.1 h
  exact ⟨l[k], List.getElem?_eq_getElem (by omega)⟩

theorem nodesOk_spec {c : BCert} (h : nodesOk c = true) {k : ℕ} {n : BNode}
    (hk : nget c k = some n) : nodeOk c n = true := by
  have hlt : k < c.ncnt := by
    simp only [nget] at hk
    cases hb : Nat.blt k c.ncnt
    · rw [hb] at hk; cases hk
    · simpa [Nat.blt_eq] using hb
  have key : ∀ N, Nat.rec (motive := fun _ => Bool) true
      (fun k r => Bool.rec (motive := fun _ => Bool) false r (nodeAt c k)) N = true →
      ∀ k < N, nodeAt c k = true := by
    intro N
    induction N with
    | zero => intro _ k hk; omega
    | succ N ih =>
      intro h k hk
      change Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
        (fun k r => Bool.rec (motive := fun _ => Bool) false r (nodeAt c k)) N)
        (nodeAt c N) = true at h
      cases hb : nodeAt c N
      · rw [hb] at h; cases h
      · rw [hb] at h
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hl | rfl
        · exact ih h k hl
        · exact hb
  have hat := key c.ncnt h k hlt
  unfold nodeAt at hat
  rw [hk] at hat
  exact hat

/-- `Reach c r m ℓ`: from reference `r`, the packed marking `m` leads to the leaf `ℓ`. -/
inductive Reach (c : BCert) : ℕ → ℕ → ℕ → Prop
  | leaf {r m : ℕ} : r % 2 = 0 → Reach c r m r
  | node {r m ℓ : ℕ} {n : BNode} : r % 2 = 1 → nget c (r / 2) = some n →
      Reach c (cond (m.testBit n.var) n.hi n.lo) m ℓ → Reach c r m ℓ

theorem Reach.even {r m ℓ : ℕ} (h : Reach c r m ℓ) : ℓ % 2 = 0 := by
  induction h with
  | leaf h => exact h
  | node _ _ _ ih => exact ih

theorem Reach.det {r m ℓ ℓ' : ℕ} (h : Reach c r m ℓ) (h' : Reach c r m ℓ') : ℓ = ℓ' := by
  induction h generalizing ℓ' with
  | leaf hr =>
    cases h' with
    | leaf _ => rfl
    | node hr' _ _ => omega
  | node hr hk _ ih =>
    cases h' with
    | leaf hr' => omega
    | node _ hk' h'' =>
      rw [hk] at hk'
      cases hk'
      exact ih h''

theorem Reach.of_even {r m ℓ : ℕ} (h : Reach c r m ℓ) (hr : r % 2 = 0) : ℓ = r := by
  cases h with
  | leaf _ => rfl
  | node hr' _ _ => omega

theorem evalB_spec {m : ℕ} : ∀ {f r ℓ : ℕ}, evalB c m f r = some ℓ → Reach c r m ℓ
  | 0, _, _, h => by simp [evalB] at h
  | f + 1, r, ℓ, h => by
    simp only [evalB] at h
    cases hb : Nat.beq (r % 2) 0
    · rw [hb] at h
      have hr : r % 2 = 1 := by
        have := Nat.ne_of_beq_eq_false hb; omega
      simp only [Bool.cond_false] at h
      split at h
      · cases h
      · exact Reach.node hr (by assumption) (evalB_spec h)
    · rw [hb] at h
      simp only [Bool.cond_true, Option.some.injEq] at h
      subst h
      exact Reach.leaf (Nat.eq_of_beq_eq_true hb)

theorem rinfo_even {r : ℕ} (hr : r % 2 = 0) : rinfo c r = some ⟨c.H, 0, r, r, 0, 0⟩ := by
  simp [rinfo, shr_one, hr]

theorem rinfo_odd {r : ℕ} (hr : r % 2 = 1) : rinfo c r = nget c (r / 2) := by
  simp [rinfo, shr_one, hr]

theorem kOf_odd {r : ℕ} (hr : r % 2 = 1) :
    kOf c r = (nget c (r / 2)).map fun n => (n.k1, n.k0) := by
  simp only [kOf, land_one, shiftRight_one', hr]; rfl

theorem kOf_leaf {r : ℕ} (hr : r % 2 = 0) (h0 : r ≠ 0) :
    kOf c r = (kfind (r / 2) c.leaves).map fun l => (l.k1, l.k0) := by
  simp only [kOf, land_one, shiftRight_one', hr]
  rw [nbeq_false h0]; rfl

theorem cinfo_spec {r : ℕ} {x : ℕ × ℕ × ℕ} (h : cinfo c r = some x) :
    (∃ n, rinfo c r = some n ∧ n.lvl = x.1) ∧ kOf c r = some (x.2.1, x.2.2) := by
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · by_cases h0 : r = 0
    · subst h0
      simp only [cinfo, kOf, rinfo, land_one, shiftRight_one'] at h ⊢
      cases h
      exact ⟨⟨_, rfl, rfl⟩, rfl⟩
    · have h' := h
      simp only [cinfo, land_one, shiftRight_one', hr, nbeq_false h0] at h'
      change (kfind (r / 2) c.leaves).map (fun l => (c.H, l.k1, l.k0)) = some x at h'
      refine ⟨⟨_, rinfo_even hr, ?_⟩, ?_⟩
      · cases hk : kfind (r / 2) c.leaves with
        | none => rw [hk] at h'; cases h'
        | some l => rw [hk] at h'; cases h'; rfl
      · rw [kOf_leaf hr h0]
        cases hk : kfind (r / 2) c.leaves with
        | none => rw [hk] at h'; cases h'
        | some l => rw [hk] at h'; cases h'; rfl
  · have h' := h
    simp only [cinfo, land_one, shiftRight_one', hr] at h'
    change (nget c (r / 2)).map (fun n => (n.lvl, n.k1, n.k0)) = some x at h'
    cases hk : nget c (r / 2) with
    | none => rw [hk] at h'; cases h'
    | some n =>
      rw [hk] at h'; cases h'
      exact ⟨⟨n, by rw [rinfo_odd hr, hk], rfl⟩, by rw [kOf_odd hr, hk]; rfl⟩

/-- Stepping the walk before firing: a node reads its place, a leaf stays put. -/
theorem Reach.step_left {a m ℓ : ℕ} {na : BNode} (ha : rinfo c a = some na)
    (h : Reach c a m ℓ) (bit : Bool) (hbit : a % 2 = 1 → bit = m.testBit na.var) :
    Reach c (cond bit na.hi na.lo) m ℓ := by
  rcases Nat.mod_two_eq_zero_or_one a with hr | hr
  · rw [rinfo_even hr] at ha
    cases ha
    cases bit <;> exact h
  · rw [rinfo_odd hr] at ha
    rw [hbit hr]
    cases h with
    | leaf hr' => omega
    | node _ hk h' => rw [ha] at hk; cases hk; exact h'

/-- Stepping the walk after firing. -/
theorem Reach.step_right {b m ℓ : ℕ} {nb : BNode} (hb : rinfo c b = some nb) (bit : Bool)
    (hbit : b % 2 = 1 → bit = m.testBit nb.var) (h : Reach c (cond bit nb.hi nb.lo) m ℓ) :
    Reach c b m ℓ := by
  rcases Nat.mod_two_eq_zero_or_one b with hr | hr
  · rw [rinfo_even hr] at hb
    cases hb
    cases bit <;> exact h
  · rw [rinfo_odd hr] at hb
    rw [hbit hr] at h
    exact Reach.node hr hb h

section Nodes

variable (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
include hN

theorem nodeOk_of_rinfo {r : ℕ} {n : BNode} (hr : r % 2 = 1) (h : rinfo c r = some n) :
    nodeOk c n = true := by
  rw [rinfo_odd hr] at h
  exact hN _ _ h

theorem lvl_lt_of_odd {r : ℕ} {n : BNode} (hr : r % 2 = 1) (h : rinfo c r = some n) :
    n.lvl < c.H := by
  have := nodeOk_of_rinfo hN hr h
  simp only [nodeOk, Bool.and_eq_true] at this
  exact blt_true this.1.1

theorem nodeOk_var {r : ℕ} {n : BNode} (hr : r % 2 = 1) (h : rinfo c r = some n) :
    varAt c.vars n.lvl n.var = true := by
  have := nodeOk_of_rinfo hN hr h
  simp only [nodeOk, Bool.and_eq_true] at this
  exact this.1.2

omit hN in
theorem odd_of_lvl_lt {r : ℕ} {n : BNode} (h : rinfo c r = some n) (hl : n.lvl < c.H) :
    r % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one r with hr | hr
  · rw [rinfo_even hr] at h; cases h; exact absurd hl (lt_irrefl _)
  · exact hr

/-- The children of a node lie at greater levels. -/
theorem children_lvl {r : ℕ} {n : BNode} (hr : r % 2 = 1) (h : rinfo c r = some n) :
    (∃ a, rinfo c n.lo = some a ∧ n.lvl < a.lvl) ∧ (∃ b, rinfo c n.hi = some b ∧ n.lvl < b.lvl) := by
  have := nodeOk_of_rinfo hN hr h
  simp only [nodeOk, Bool.and_eq_true] at this
  obtain ⟨-, h2⟩ := this
  split at h2
  · rename_i a b ha hb
    simp only [Bool.and_eq_true] at h2
    obtain ⟨⟨a', ha', hla⟩, -⟩ := cinfo_spec ha
    obtain ⟨⟨b', hb', hlb⟩, -⟩ := cinfo_spec hb
    exact ⟨⟨a', ha', hla ▸ blt_true h2.1.1.1.1.1⟩, ⟨b', hb', hlb ▸ blt_true h2.1.1.1.1.2⟩⟩
  · cases h2

/-- The places known to be marked and unmarked at a reference hold all the way to the leaf. -/
theorem Reach.known {r m ℓ : ℕ} (h : Reach c r m ℓ) {K : ℕ × ℕ} (hK : kOf c r = some K)
    (h1 : ∀ q, K.1.testBit q = true → m.testBit q = true)
    (h0 : ∀ q, K.2.testBit q = true → m.testBit q = false) :
    ∃ K', kOf c ℓ = some K' ∧ (∀ q, K'.1.testBit q = true → m.testBit q = true) ∧
      (∀ q, K'.2.testBit q = true → m.testBit q = false) := by
  induction h generalizing K with
  | leaf _ => exact ⟨K, hK, h1, h0⟩
  | @node r m ℓ n hr hk _ ih =>
    have hKn : K = (n.k1, n.k0) := by
      rw [kOf_odd hr, hk] at hK
      simp only [Option.map_some, Option.some.injEq] at hK
      exact hK.symm
    subst hKn
    have hok := hN _ _ hk
    simp only [nodeOk, Bool.and_eq_true] at hok
    obtain ⟨-, hk2⟩ := hok
    split at hk2
    · rename_i a b ha hb
      have hl := (cinfo_spec ha).2
      have hh := (cinfo_spec hb).2
      simp only [Bool.and_eq_true, sub_iff] at hk2
      obtain ⟨⟨⟨⟨-, s1⟩, s2⟩, s3⟩, s4⟩ := hk2
      cases hb : m.testBit n.var
      · rw [hb] at ih
        refine ih hl (fun q hq => h1 q (s1 q hq)) (fun q hq => ?_)
        have := s2 q hq
        simp only [Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow,
          decide_eq_true_eq] at this
        rcases this with h | rfl
        · exact h0 q h
        · exact hb
      · rw [hb] at ih
        refine ih hh (fun q hq => ?_) (fun q hq => h0 q (s4 q hq))
        have := s3 q hq
        simp only [Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow,
          decide_eq_true_eq] at this
        rcases this with h | rfl
        · exact h1 q h
        · exact hb
    · cases hk2

/-- A step of one side of the walk, by the level of the node (`s`) and the bit read. -/
theorem side_lvl {r : ℕ} {n : BNode} (hr : rinfo c r = some n) (s bit : Bool) :
    ∃ n', rinfo c (cond bit (cond s n.hi r) (cond s n.lo r)) = some n' ∧ n.lvl ≤ n'.lvl ∧
      (s = true → n.lvl < c.H → n.lvl < n'.lvl) := by
  cases s
  · exact ⟨n, by cases bit <;> exact hr, le_refl _, fun h => by cases h⟩
  · by_cases hl : n.lvl < c.H
    · obtain ⟨⟨a, ha, hla⟩, ⟨b, hb, hlb⟩⟩ := children_lvl hN (odd_of_lvl_lt hr hl) hr
      cases bit
      · exact ⟨a, ha, hla.le, fun _ _ => hla⟩
      · exact ⟨b, hb, hlb.le, fun _ _ => hlb⟩
    · have hr2 : r % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one r with h | h
        · exact h
        · exact absurd (lvl_lt_of_odd hN h hr) hl
      have hn := hr
      rw [rinfo_even hr2] at hn
      cases hn
      exact ⟨_, by cases bit <;> exact rinfo_even hr2, le_refl _, fun _ h => absurd h hl⟩

/-- Reachability of a leaf only depends on the places read at the levels of the nodes. -/
theorem Reach.congr {r m ℓ : ℕ} (h : Reach c r m ℓ) {m' L : ℕ} :
    (∀ L' p, L ≤ L' → knth c.vars L' = some p → m'.testBit p = m.testBit p) →
    (∀ n, rinfo c r = some n → L ≤ n.lvl) → Reach c r m' ℓ := by
  induction h with
  | leaf hr => intro _ _; exact Reach.leaf hr
  | @node r m ℓ n hr hk h' ih =>
    intro hag hL
    have hrn : rinfo c r = some n := by rw [rinfo_odd hr]; exact hk
    have hl := hL n hrn
    have hb := hag _ _ hl (varAt_iff.1 (nodeOk_var hN hr hrn))
    refine Reach.node hr hk ?_
    rw [hb]
    refine ih hag fun n' hn' => ?_
    obtain ⟨⟨a, ha, hla⟩, ⟨b, hb', hlb⟩⟩ := children_lvl hN hr hrn
    cases hbit : m.testBit n.var
    · rw [hbit] at hn'
      change rinfo c n.lo = some n' at hn'
      rw [ha] at hn'; cases hn'; omega
    · rw [hbit] at hn'
      change rinfo c n.hi = some n' at hn'
      rw [hb'] at hn'; cases hn'; omega

/-- The leaves reached from a node are in the table. -/
theorem Reach.leaf_mem {r m ℓ : ℕ} (h : Reach c r m ℓ) :
    r % 2 = 1 → ℓ ≠ 0 → ∃ L, kfind (ℓ / 2) c.leaves = some L := by
  induction h with
  | leaf h => intro h'; omega
  | @node r m ℓ n hr' hk h' ih =>
    intro _ hne
    rcases Nat.mod_two_eq_zero_or_one (cond (m.testBit n.var) n.hi n.lo) with he | ho
    · have hℓ := h'.of_even he
      have hok := hN _ _ hk
      simp only [nodeOk, Bool.and_eq_true] at hok
      obtain ⟨-, h2⟩ := hok
      split at h2
      · rename_i a b ha hb
        have hK : ∃ K, kOf c (cond (m.testBit n.var) n.hi n.lo) = some K := by
          cases m.testBit n.var
          · exact ⟨_, (cinfo_spec ha).2⟩
          · exact ⟨_, (cinfo_spec hb).2⟩
        obtain ⟨K, hK⟩ := hK
        rw [← hℓ] at hK he
        rw [kOf_leaf he hne] at hK
        cases hl : kfind (ℓ / 2) c.leaves with
        | none => rw [hl] at hK; cases hK
        | some L => exact ⟨L, rfl⟩
      · cases h2
    · exact ih ho hne

end Nodes

/-- Firing does not change the places read at levels outside those it touches. -/
theorem fire_agree (hv : varsOk c.lvls c.vars 0 = true) {e : BTrans}
    (hus : ∀ u ∈ e.us, usOk c e u = true) (hcov : sub (e.pre ||| e.post) (umask e.us) = true)
    {L p : ℕ} (hp : knth c.vars L = some p) (hL : L < e.lo ∨ e.hi < L) (m : ℕ) :
    ((m ^^^ e.pre) ||| e.post).testBit p = m.testBit p := by
  have hno : (e.pre ||| e.post).testBit p = false := by
    cases hb : (e.pre ||| e.post).testBit p
    · rfl
    · obtain ⟨u, hu, rfl⟩ := testBit_umask (sub_iff.1 hcov _ hb)
      have := hus u hu
      simp only [usOk, Bool.and_eq_true, varAt_iff] at this
      obtain ⟨⟨h1, h2⟩, h3⟩ := this
      have := vars_inj hv h3 hp
      have h1 := Nat.le_of_ble_eq_true h1
      have h2 := Nat.le_of_ble_eq_true h2
      omega
  simp only [Nat.testBit_lor, Bool.or_eq_false_iff] at hno
  rw [Nat.testBit_lor, Nat.testBit_xor, hno.1, hno.2]
  simp

theorem side_left {a m ℓ : ℕ} {na : BNode} (ha : rinfo c a = some na) (h : Reach c a m ℓ)
    (s bit : Bool) (hs : s = true → a % 2 = 1 → bit = m.testBit na.var) :
    Reach c (cond bit (cond s na.hi a) (cond s na.lo a)) m ℓ := by
  cases s
  · cases bit <;> exact h
  · have := h.step_left ha bit (hs rfl)
    cases bit <;> exact this

theorem side_right {b m ℓ : ℕ} {nb : BNode} (hb : rinfo c b = some nb) (s bit : Bool)
    (hs : s = true → b % 2 = 1 → bit = m.testBit nb.var)
    (h : Reach c (cond bit (cond s nb.hi b) (cond s nb.lo b)) m ℓ) : Reach c b m ℓ := by
  cases s
  · cases bit <;> exact h
  · exact Reach.step_right hb bit (hs rfl) (by cases bit <;> exact h)

theorem memT_spec {ps : BTree (ℕ × ℕ × ℕ × ℕ)} {a b j : ℕ} (h : memT ps a b j = true) :
    (tkey a b j, a, b, j) ∈ ps.toList := by
  simp only [memT] at h
  split at h
  · cases h
  · rename_i x hx
    obtain ⟨x1, x2, x3⟩ := x
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have := mem_of_kfind hx
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3] at this
    exact this

/-- What the triple `(a, b, j)` of transition `i` guarantees: from a marking `m` enabling the
transition and reaching a non-zero leaf `ℓ₁` from `a`, the output-only places from the `j`-th
touched place on are unmarked, and the marking after firing reaches from `b` a leaf `ℓ₂`
satisfying the leaf condition. -/
def TClaim (c : BCert) (md i : ℕ) (e : BTrans) (_ps : BTree (ℕ × ℕ × ℕ × ℕ)) (a b j : ℕ) : Prop :=
  ∀ m, sub e.pre m = true → ∀ ℓ₁, Reach c a m ℓ₁ → ℓ₁ ≠ 0 →
    (∀ u ∈ e.us.drop j, 2 ≤ u.2.2 → m.testBit u.1 = false) ∧
    ∃ ℓ₂, Reach c b ((m ^^^ e.pre) ||| e.post) ℓ₂ ∧ leafCond c md i ℓ₁ ℓ₂ = true

theorem testBit_fire {m pre post v : ℕ} :
    ((m ^^^ pre) ||| post).testBit v = ((m.testBit v ^^ pre.testBit v) || post.testBit v) := by
  simp [Nat.testBit_xor]

/-- **Every triple keeps its promise.** -/
theorem tclaim (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    (hv : varsOk c.lvls c.vars 0 = true) {md i : ℕ}
    {e : BTrans} {ps : BTree (ℕ × ℕ × ℕ × ℕ)} (hUok : ∀ u ∈ e.us, uOk e.pre e.post u = true)
    (hus : ∀ u ∈ e.us, usOk c e u = true) (hcov : sub (e.pre ||| e.post) (umask e.us) = true)
    (hT : ∀ x ∈ ps.toList, tripleOk c md i e ps x = true) :
    ∀ a b j, memT ps a b j = true → TClaim c md i e ps a b j := by
  -- the measure: levels still to go on both sides, and touched places still to pass
  suffices H : ∀ n, ∀ a b j na nb, rinfo c a = some na → rinfo c b = some nb →
      (c.H - na.lvl) + (c.H - nb.lvl) + (e.us.length - j) = n → memT ps a b j = true →
      TClaim c md i e ps a b j by
    intro a b j hm
    have hx := hT _ (memT_spec hm)
    simp only [tripleOk] at hx
    split at hx
    · rename_i na nb ha hb
      exact H _ a b j na nb ha hb rfl hm
    · cases hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro a b j na nb ha hb hn hm
  have hx := hT _ (memT_spec hm)
  simp only [tripleOk, ha, hb] at hx
  -- an untouched place
  have hU : untouched c e ps a b j na nb = true → TClaim c md i e ps a b j := by
    intro hu
    simp only [untouched, cond_ble_min, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
      ktest_eq] at hu
    obtain ⟨⟨⟨⟨⟨⟨hL, hva⟩, hvb⟩, hpre⟩, hpost⟩, hm0⟩, hm1⟩ := hu
    have hL' := blt_true hL
    intro m hpm ℓ₁ hr hne
    set L := min na.lvl nb.lvl with hLdef
    set v := cond (Nat.ble na.lvl nb.lvl) na.var nb.var
    set bit := m.testBit v
    have hm' : memT ps (cond bit (cond (Nat.beq na.lvl L) na.hi a) (cond (Nat.beq na.lvl L) na.lo a))
        (cond bit (cond (Nat.beq nb.lvl L) nb.hi b) (cond (Nat.beq nb.lvl L) nb.lo b)) j = true := by
      cases bit
      · exact hm0
      · exact hm1
    obtain ⟨na', ha', hla, hla'⟩ := side_lvl hN ha (Nat.beq na.lvl L) bit
    obtain ⟨nb', hb', hlb, hlb'⟩ := side_lvl hN hb (Nat.beq nb.lvl L) bit
    have hmeas : (c.H - na'.lvl) + (c.H - nb'.lvl) + (e.us.length - j) < n := by
      rcases le_total na.lvl nb.lvl with hle | hle
      · have h1 : Nat.beq na.lvl L = true := by
          rw [Nat.beq_eq, hLdef, min_eq_left hle]
        have := hla' h1 (by omega)
        omega
      · have h1 : Nat.beq nb.lvl L = true := by
          rw [Nat.beq_eq, hLdef, min_eq_right hle]
        have := hlb' h1 (by omega)
        omega
    have hva' : Nat.beq na.lvl L = true → a % 2 = 1 → bit = m.testBit na.var := by
      intro h _
      rcases hva with hva | hva
      · rw [hva] at h; cases h
      · rw [Nat.eq_of_beq_eq_true hva]
    obtain ⟨hsafe, ℓ₂, hr2, hlc⟩ := IH _ hmeas _ _ _ na' nb' ha' hb' rfl hm' m hpm ℓ₁
      (side_left ha hr _ bit hva') hne
    refine ⟨hsafe, ℓ₂, side_right hb (Nat.beq nb.lvl L) bit (fun h _ => ?_) hr2, hlc⟩
    rcases hvb with hvb | hvb
    · rw [hvb] at h; cases h
    · rw [Nat.eq_of_beq_eq_true hvb, testBit_fire, hpre, hpost]; simp [bit]
  split at hx
  · -- a touched place
    rename_i u hu
    rw [knth_eq] at hu
    obtain ⟨hj, hget⟩ := List.getElem?_eq_some_iff.1 hu
    have hdrop : e.us.drop j = u :: e.us.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj, hget]
    have huok := hUok u (List.mem_of_getElem? hu)
    cases hc : (Nat.ble u.2.1 na.lvl && Nat.ble u.2.1 nb.lvl)
    · rw [hc] at hx; exact hU hx
    rw [hc] at hx
    simp only [Bool.cond_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc hx
    obtain ⟨hca, hcb⟩ := hc
    have hla := Nat.le_of_ble_eq_true hca
    have hlb := Nat.le_of_ble_eq_true hcb
    obtain ⟨⟨hva, hvb⟩, hk⟩ := hx
    have hva' : Nat.beq na.lvl u.2.1 = true → na.var = u.1 := fun h => by
      rcases hva with hva | hva
      · rw [hva] at h; cases h
      · exact Nat.eq_of_beq_eq_true hva
    have hvb' : Nat.beq nb.lvl u.2.1 = true → nb.var = u.1 := fun h => by
      rcases hvb with hvb | hvb
      · rw [hvb] at h; cases h
      · exact Nat.eq_of_beq_eq_true hvb
    intro m hpm ℓ₁ hr hne
    have hpre_m := sub_iff.1 hpm
    have succ : ∀ bitA bitB : Bool,
        memT ps (cond bitA (cond (Nat.beq na.lvl u.2.1) na.hi a) (cond (Nat.beq na.lvl u.2.1) na.lo a))
          (cond bitB (cond (Nat.beq nb.lvl u.2.1) nb.hi b) (cond (Nat.beq nb.lvl u.2.1) nb.lo b))
          (j + 1) = true →
        bitA = m.testBit u.1 → bitB = ((m ^^^ e.pre) ||| e.post).testBit u.1 →
        (∀ u' ∈ e.us.drop (j + 1), 2 ≤ u'.2.2 → m.testBit u'.1 = false) ∧
          ∃ ℓ₂, Reach c b ((m ^^^ e.pre) ||| e.post) ℓ₂ ∧
            leafCond c md i ℓ₁ ℓ₂ = true := by
      intro bitA bitB hmem hA hB
      obtain ⟨na', ha', hla1, -⟩ := side_lvl hN ha (Nat.beq na.lvl u.2.1) bitA
      obtain ⟨nb', hb', hlb1, -⟩ := side_lvl hN hb (Nat.beq nb.lvl u.2.1) bitB
      obtain ⟨hs, ℓ₂, hr2, hlc⟩ := IH _ (by omega) _ _ _ na' nb' ha' hb' rfl hmem m hpm ℓ₁
        (side_left ha hr _ bitA fun h _ => by rw [hva' h]; exact hA) hne
      exact ⟨hs, ℓ₂, side_right hb _ bitB (fun h _ => by rw [hvb' h]; exact hB) hr2, hlc⟩
    simp only [uOk, ktest_eq] at huok
    rw [hdrop]
    cases hk0 : Nat.beq u.2.2 0
    · cases hk1 : Nat.beq u.2.2 1
      · -- output only
        rw [hk0, hk1] at huok hk
        simp only [Bool.cond_false, Bool.and_eq_true, Bool.not_eq_true'] at huok hk
        obtain ⟨hpv, hqv⟩ := huok
        cases hmv : m.testBit u.1
        · obtain ⟨hs, h2⟩ := succ false true hk.2 hmv.symm (by simp [hmv, hpv, hqv])
          refine ⟨fun u' hu' h2u => ?_, h2⟩
          rcases List.mem_cons.1 hu' with rfl | hu'
          · exact hmv
          · exact hs u' hu' h2u
        · -- marking an output place that is already marked: impossible in the invariant
          exfalso
          obtain ⟨na', ha', hla1, -⟩ := side_lvl hN ha (Nat.beq na.lvl u.2.1) true
          obtain ⟨-, ℓ₂, hr2, hlc⟩ := IH _ (by dsimp only; omega)
            _ 0 _ na' ⟨c.H, 0, 0, 0, 0, 0⟩ ha' (rinfo_even rfl) rfl hk.1 m hpm ℓ₁
            (side_left ha hr _ true fun h _ => by rw [hva' h]; exact hmv.symm) hne
          rw [hr2.of_even rfl] at hlc
          simp [leafCond, nbeq_false hne] at hlc
      · -- input and output
        rw [hk0, hk1] at huok hk
        simp only [Bool.cond_false, Bool.cond_true, Bool.and_eq_true] at huok hk
        obtain ⟨hpv, hqv⟩ := huok
        obtain ⟨hs, h2⟩ := succ true true hk (hpre_m _ hpv).symm (by simp [hqv])
        refine ⟨fun u' hu' h2u => ?_, h2⟩
        rcases List.mem_cons.1 hu' with rfl | hu'
        · rw [Nat.eq_of_beq_eq_true hk1] at h2u; omega
        · exact hs u' hu' h2u
    · -- input only
      rw [hk0] at huok hk
      simp only [Bool.cond_true, Bool.and_eq_true, Bool.not_eq_true'] at huok hk
      obtain ⟨hpv, hqv⟩ := huok
      obtain ⟨hs, h2⟩ := succ true false hk (hpre_m _ hpv).symm
        (by simp [hpv, hqv, hpre_m _ hpv])
      refine ⟨fun u' hu' h2u => ?_, h2⟩
      rcases List.mem_cons.1 hu' with rfl | hu'
      · rw [Nat.eq_of_beq_eq_true hk0] at h2u; omega
      · exact hs u' hu' h2u
  · -- past the touched places
    rename_i hu
    rw [knth_eq, List.getElem?_eq_none_iff] at hu
    cases hc : (Nat.blt na.lvl c.H || Nat.blt nb.lvl c.H)
    · rw [hc] at hx
      simp only [Bool.or_eq_false_iff] at hc
      have hae : a % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one a with h | h
        · exact h
        · have h1 : Nat.blt na.lvl c.H = true := by rw [Nat.blt_eq]; exact lvl_lt_of_odd hN h ha
          simp [h1] at hc
      have hbe : b % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one b with h | h
        · exact h
        · have h1 : Nat.blt nb.lvl c.H = true := by rw [Nat.blt_eq]; exact lvl_lt_of_odd hN h hb
          simp [h1] at hc
      intro m _ ℓ₁ hr _
      rw [hr.of_even hae]
      refine ⟨fun u' hu' => by simp [List.drop_eq_nil_of_le hu] at hu', b, Reach.leaf hbe, hx⟩
    · rw [hc] at hx
      simp only [Bool.cond_true, Bool.or_eq_true, Bool.and_eq_true] at hx
      simp only [Bool.or_eq_true] at hc
      rcases hx with (⟨⟨hmd, hab⟩, hhi⟩ | ⟨⟨hmd, hlv⟩, hdl⟩) | hx
      · -- the same node before and after firing, below the touched places
        have hmd := Nat.eq_of_beq_eq_true hmd
        have hab := Nat.eq_of_beq_eq_true hab
        subst hmd hab
        rw [ha] at hb; cases hb
        have hhi := blt_true hhi
        have hlt : na.lvl < c.H := by
          rcases hc with h | h <;> exact blt_true h
        have hao := odd_of_lvl_lt ha hlt
        intro m _ ℓ₁ hr hne
        refine ⟨fun u' hu' => by simp [List.drop_eq_nil_of_le hu] at hu', ℓ₁, ?_, ?_⟩
        · exact hr.congr hN (L := na.lvl)
            (fun L' p hL hp => fire_agree hv hus hcov hp (Or.inr (by omega)) m)
            (fun n hn => by rw [ha] at hn; cases hn; exact le_refl _)
        · obtain ⟨L, hL⟩ := hr.leaf_mem hN hao hne
          simp +decide [leafCond, nbeq_false hne, hL]
      · -- a coverage walk that reached a data leaf
        have hmd := Nat.eq_of_beq_eq_true hmd
        subst hmd
        have hao := odd_of_lvl_lt ha (blt_true hlv)
        simp only [dataLeaf, Bool.and_eq_true, Bool.not_eq_true'] at hdl
        obtain ⟨⟨hbe, hb0⟩, hdat⟩ := hdl
        have hbe : b % 2 = 0 := by rw [← land_one]; exact Nat.eq_of_beq_eq_true hbe
        have hb0 : b ≠ 0 := Nat.ne_of_beq_eq_false hb0
        rw [shiftRight_one'] at hdat
        split at hdat
        · rename_i lb hlb
          intro m _ ℓ₁ hr hne
          obtain ⟨L, hL⟩ := hr.leaf_mem hN hao hne
          refine ⟨fun u' hu' => by simp [List.drop_eq_nil_of_le hu] at hu', b, Reach.leaf hbe, ?_⟩
          simp +decide [leafCond, nbeq_false hne, nbeq_false hb0, hL, hlb, hdat]
        · cases hdat
      · exact hU hx

theorem chkTrans_spec {ll lv : Bool} : ∀ {ts : List PTrans} {es : List BTrans} {i : ℕ},
    chkTrans c ll lv ts es i = true → es.length = ts.length ∧ ∀ k (hk : k < ts.length),
      ∃ e, es[k]? = some e ∧ mask ts[k].pre = e.pre ∧ mask ts[k].post = e.post ∧
        transOk c ll lv ts[k].internal (i + k) e = true
  | [], [], _, _ => ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | [], _ :: _, _, h => by simp [chkTrans] at h
  | _ :: _, [], _, h => by simp [chkTrans] at h
  | t :: ts, e :: es, i, h => by
    simp only [chkTrans, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨hl, ih⟩ := chkTrans_spec h4
    refine ⟨by simp [hl], fun k hk => ?_⟩
    cases k with
    | zero => exact ⟨e, rfl, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, by simpa using h3⟩
    | succ k =>
      obtain ⟨e', he', h'⟩ := ih k (by simpa using hk)
      exact ⟨e', by simpa using he', by simpa [Nat.add_assoc, Nat.add_comm 1 k] using h'⟩

theorem leafCond_spec {md i a b : ℕ} (h : leafCond c md i a b = true)
    (ha : a ≠ 0) : b ≠ 0 ∧ ∃ la lb, kfind (a / 2) c.leaves = some la ∧
      kfind (b / 2) c.leaves = some lb ∧ (md = 1 → lb.r < la.r) ∧ (2 ≤ md → lb.dat = true) ∧
      (md = 2 → la.wit = i → la.d ≠ 0 → lb.d < la.d) := by
  simp only [leafCond, nbeq_false ha, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hb, h⟩ := h
  refine ⟨fun h0 => by simp [h0] at hb, ?_⟩
  split at h
  · rename_i la lb hla hlb
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
      at h
    obtain ⟨⟨h1, h3⟩, h2⟩ := h
    refine ⟨la, lb, hla, hlb, fun hm => ?_, fun hm => ?_, fun hm hw hd => ?_⟩
    · rcases h1 with h1 | h1
      · simp [hm] at h1
      · exact blt_true h1
    · rcases h3 with h3 | h3
      · rw [show Nat.ble 2 md = true by rw [Nat.ble_eq]; exact hm] at h3; cases h3
      · exact h3
    · rcases h2 with h2 | h2
      · simp [hm, hw, nbeq_false hd] at h2
      · exact blt_true h2
  · cases h

theorem simB_cons {tl : List BTrans} {m j : ℕ} {js : List ℕ} {m' : ℕ}
    (h : simB tl m (j :: js) = some m') : ∃ e, knth tl j = some e ∧ sub e.pre m = true ∧
      simB tl ((m ^^^ e.pre) ||| e.post) js = some m' := by
  simp only [simB] at h
  split at h
  · cases h
  · rename_i e he
    cases hs : sub e.pre m
    · rw [hs] at h; cases h
    · rw [hs] at h; exact ⟨e, he, hs, h⟩

theorem tracesOk_spec {tl : List BTrans} {h : ℕ} : ∀ {trs : List (List ℕ)} {i : ℕ},
    tracesOk tl h trs i = true → ∀ k (hk : k < trs.length), ∃ m' e,
      simB tl h trs[k] = some m' ∧ knth tl (i + k) = some e ∧ sub e.pre m' = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | tr :: trs, i, hc, k, hk => by
    simp only [tracesOk, Bool.and_eq_true] at hc
    obtain ⟨h1, h2⟩ := hc
    cases k with
    | zero =>
      split at h1
      · rename_i m' e hm he
        exact ⟨m', e, hm, he, h1⟩
      · cases h1
    | succ k =>
      obtain ⟨m', e, hm, he, hs⟩ := tracesOk_spec h2 k (by simpa using hk)
      exact ⟨m', e, hm, by simpa [Nat.add_assoc, Nat.add_comm 1 k] using he, hs⟩

theorem phiL_cons (w : ℕ) (ws : List ℕ) (x q : ℕ) :
    phiL (w :: ws) x q = cond (ktest x q) w 0 + phiL ws x (q + 1) := rfl

/-- Firing never increases the linear potential by more than the outputs minus the inputs. -/
theorem phiL_fire (ws : List ℕ) {m pre post : ℕ} (hen : sub pre m = true) :
    ∀ q, phiL ws ((m ^^^ pre) ||| post) q + phiL ws pre q ≤ phiL ws m q + phiL ws post q := by
  induction ws with
  | nil => intro q; simp [phiL]
  | cons w ws ih =>
    intro q
    simp only [phiL_cons, ktest_eq, Nat.testBit_lor, Nat.testBit_xor]
    have h := ih (q + 1)
    have hb := sub_iff.1 hen q
    cases hm : m.testBit q <;> cases hp : pre.testBit q <;> cases ho : post.testBit q <;>
      simp only [Bool.true_xor, Bool.false_xor, Bool.not_true, Bool.not_false, Bool.or_true,
        Bool.or_false, Bool.cond_true, Bool.cond_false] <;>
      first | omega | (exfalso; have := hb hp; rw [hm] at this; cases this)

theorem phiL_lt {ws : List ℕ} {m pre post : ℕ} (hen : sub pre m = true)
    (hd : decB ws pre post = true) : phiL ws ((m ^^^ pre) ||| post) 0 < phiL ws m 0 := by
  have h1 := phiL_fire ws (post := post) hen 0
  have h2 := blt_true hd
  omega

theorem le_sum_of_mem_nat {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h
      simp only [List.sum_cons]
      omega

theorem phiL_le {ws : List ℕ} {m pre post : ℕ} (hen : sub pre m = true)
    (hd : nincB ws pre post = true) : phiL ws ((m ^^^ pre) ||| post) 0 ≤ phiL ws m 0 := by
  have h1 := phiL_fire ws (post := post) hen 0
  have h2 := Nat.le_of_ble_eq_true hd
  omega

variable (N : PNet)

theorem packed_step_iff {m m' : ℕ} {t : Fin N.trans.length} :
    N.packed.toLTS.step m t m' ↔
      sub (N.preMask t) m = true ∧ m' = (m ^^^ N.preMask t) ||| N.postMask t := by
  change (t, m') ∈ N.packedSucc m ↔ _
  simp only [packedSucc, List.mem_filterMap, List.mem_finRange, true_and, sub_eq, Nat.land_comm]
  constructor
  · rintro ⟨t', h⟩
    split_ifs at h with hen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hen, rfl⟩
  · rintro ⟨hen, rfl⟩
    exact ⟨t, by simp [hen]⟩

variable {N}

theorem lt_two_pow_mask {ps : List ℕ} {n : ℕ} (h : ∀ q ∈ ps, q < n) : mask ps < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro q hq
  rw [testBit_mask]
  simp only [decide_eq_false_iff_not]
  exact fun hm => absurd (h q hm) (by omega)

/-- A walk from the roots `ra`, `rb` keeps the promise of its first triple. -/
theorem walkOk_spec {c : BCert} (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    (hv : varsOk c.lvls c.vars 0 = true)
    {md i : ℕ} {e : BTrans} {ps : BTree (ℕ × ℕ × ℕ × ℕ)} {ra rb : ℕ}
    (hu : ∀ u ∈ e.us, uOk e.pre e.post u = true) (hus : ∀ u ∈ e.us, usOk c e u = true)
    (hcov : sub (e.pre ||| e.post) (umask e.us) = true) (h : walkOk c md i e ps ra rb = true) :
    TClaim c md i e ps ra rb 0 := by
  simp only [walkOk, Bool.and_eq_true, ktall_iff] at h
  exact tclaim hN hv hu hus hcov h.2 _ _ _ h.1

/-- The chain of cuts, level by level. -/
theorem cutsOk_spec {c : BCert} : ∀ {rest : List (List ℕ)} {L : ℕ} {cur : List ℕ},
    cutsOk c L cur rest = true → ∀ k cl nx, knth (cur :: rest) k = some cl →
      knth (cur :: rest) (k + 1) = some nx → ∀ x ∈ cl, cutStep c (L + k) nx x = true
  | [], _, _, _, k, cl, nx, _, h2 => by rw [knth_eq] at h2; simp at h2
  | nx' :: rest, L, cur, h, k, cl, nx, h1, h2 => by
    simp only [cutsOk, Bool.and_eq_true, kall_eq, List.all_eq_true] at h
    rw [knth_eq] at h1 h2
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at h1 h2
      subst h1 h2
      intro x hx; simpa using h.1 x hx
    | succ k =>
      have := cutsOk_spec h.2 k cl nx (by rw [knth_eq]; simpa using h1)
        (by rw [knth_eq]; simpa using h2)
      intro x hx
      have := this x hx
      rwa [show L + 1 + k = L + (k + 1) by omega] at this

/-- Every marking of the invariant passes the cut of each level, at a reference from which
the rest of its path does not depend on the levels above. -/
theorem cut_reach {c : BCert} (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    {cuts : List (List ℕ)}
    (hcs : ∀ k cl nx, knth cuts k = some cl → knth cuts (k + 1) = some nx →
      ∀ x ∈ cl, cutStep c k nx x = true)
    {c0 : List ℕ} (h0 : knth cuts 0 = some c0) (hr0 : c.rI ∈ c0) :
    ∀ L cl, knth cuts L = some cl → ∀ m ℓ, Reach c c.rI m ℓ → ∃ x ∈ cl, Reach c x m ℓ ∧
      ∀ m', (∀ L' p, L' < L → knth c.vars L' = some p → m'.testBit p = m.testBit p) →
        ∀ ℓ', Reach c x m' ℓ' → Reach c c.rI m' ℓ' := by
  intro L
  induction L with
  | zero =>
    intro cl hcl m ℓ hr
    rw [h0] at hcl; cases hcl
    exact ⟨c.rI, hr0, hr, fun _ _ _ h => h⟩
  | succ L ih =>
    intro nx hnx m ℓ hr
    obtain ⟨cl, hcl⟩ := knth_prev hnx
    obtain ⟨x, hx, hrx, hpath⟩ := ih cl hcl m ℓ hr
    have hst := hcs L cl nx hcl hnx x hx
    unfold cutStep at hst
    split at hst
    · rename_i n hn
      cases hb : Nat.beq n.lvl L
      · rw [hb] at hst
        simp only [Bool.cond_false] at hst
        exact ⟨x, memL_iff.1 hst, hrx, fun m' hag => hpath m' fun L' p hL hp => hag L' p (by omega) hp⟩
      · rw [hb] at hst
        simp only [Bool.cond_true, Bool.and_eq_true] at hst
        have hl := Nat.eq_of_beq_eq_true hb
        refine ⟨cond (m.testBit n.var) n.hi n.lo, ?_, hrx.step_left hn _ fun _ => rfl, ?_⟩
        · cases m.testBit n.var
          · exact memL_iff.1 hst.1
          · exact memL_iff.1 hst.2
        · intro m' hag ℓ' hr'
          refine hpath m' (fun L' p hL hp => hag L' p (by omega) hp) ℓ' ?_
          refine Reach.step_right hn _ (fun hxo => ?_) hr'
          have hvar := varAt_iff.1 (nodeOk_var hN hxo hn)
          rw [hl] at hvar
          exact (hag L _ (by omega) hvar).symm
    · cases hst

/-- The walk on the invariant, from the cut of the lowest level touched. -/
theorem walkCut_spec {c : BCert} (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    (hv : varsOk c.lvls c.vars 0 = true)
    (hcut : ∀ L cl, knth c.cuts L = some cl → ∀ m ℓ, Reach c c.rI m ℓ → ∃ x ∈ cl,
      Reach c x m ℓ ∧ ∀ m', (∀ L' p, L' < L → knth c.vars L' = some p →
        m'.testBit p = m.testBit p) → ∀ ℓ', Reach c x m' ℓ' → Reach c c.rI m' ℓ')
    {i : ℕ} {e : BTrans} (hu : ∀ u ∈ e.us, uOk e.pre e.post u = true)
    (hus : ∀ u ∈ e.us, usOk c e u = true) (hcov : sub (e.pre ||| e.post) (umask e.us) = true)
    (h : walkCut c i e = true) : TClaim c 0 i e e.psI c.rI c.rI 0 := by
  simp only [walkCut, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [ktall_iff] at h2
  split at h1
  · rename_i cl hcl
    rw [kall_eq, List.all_eq_true] at h1
    intro m hpm ℓ₁ hr hne
    obtain ⟨x, hx, hrx, hpath⟩ := hcut _ cl hcl m ℓ₁ hr
    obtain ⟨hs, ℓ₂, hr2, hlc⟩ :=
      tclaim hN hv hu hus hcov h2 x x 0 (h1 x hx) m hpm ℓ₁ hrx hne
    exact ⟨hs, ℓ₂, hpath _ (fun L' p hL hp => fire_agree hv hus hcov hp (Or.inl hL) m) ℓ₂ hr2,
      hlc⟩
  · cases h1

/-- A walk with the empty transition: the second diagram covers the first. -/
theorem cover_of_walk {c : BCert} (hN : ∀ k n, nget c k = some n → nodeOk c n = true)
    (hv : varsOk c.lvls c.vars 0 = true) {md : ℕ} {ps : BTree (ℕ × ℕ × ℕ × ℕ)} {ra rb : ℕ} (h : walkOk c md 0 emptyT ps ra rb = true)
    {m ℓ : ℕ} (hr : Reach c ra m ℓ) (hne : ℓ ≠ 0) :
    ∃ ℓ₂, Reach c rb m ℓ₂ ∧ leafCond c md 0 ℓ ℓ₂ = true := by
  have := walkOk_spec hN hv (by simp [emptyT]) (by simp [emptyT]) rfl h m
    (sub_iff.2 fun q hq => by simp [emptyT] at hq) ℓ hr hne
  obtain ⟨-, ℓ₂, hr2, hlc⟩ := this
  simp only [emptyT, Nat.xor_zero, Nat.or_zero] at hr2
  exact ⟨ℓ₂, hr2, hlc⟩

/-- **Soundness of the symbolic check.** -/
theorem of_checkBDD {dl ll lv : Bool} {c : BCert} (h : N.checkBDD dl ll lv c = true) :
    (dl = true → N.toNet.lts.DeadlockFree N.M₀) ∧
      (ll = true → N.toNet.lts.LivelockFree N.Internal N.M₀) ∧
      (lv = true → N.toNet.lts.Live N.M₀) ∧ N.Safe := by
  simp only [checkBDD, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hwf, hv⟩, hcuts⟩, hroot⟩, hN⟩, hL⟩, htr⟩, hcR⟩, hcD⟩, h₀⟩ := h
  rw [ktall_iff] at hL
  replace hN : ∀ k n, nget c k = some n → nodeOk c n = true := fun _ _ hk => nodesOk_spec hN hk
  have hcut : ∀ L cl, knth c.cuts L = some cl → ∀ m ℓ, Reach c c.rI m ℓ → ∃ x ∈ cl,
      Reach c x m ℓ ∧ ∀ m', (∀ L' p, L' < L → knth c.vars L' = some p →
        m'.testBit p = m.testBit p) → ∀ ℓ', Reach c x m' ℓ' → Reach c c.rI m' ℓ' := by
    split at hcuts
    · rename_i c0 rest hc
      simp only [Bool.and_eq_true] at hcuts
      rw [hc]
      exact cut_reach hN (fun k cl nx h1 h2 x hx => by
          simpa using cutsOk_spec hcuts.2 k cl nx h1 h2 x hx)
        (by rw [knth_eq]; rfl) (memL_iff.1 hcuts.1)
    · cases hcuts
  obtain ⟨hwf', hM₀, hnd⟩ := packedWf_spec hwf
  have hroot' : kOf c c.rD = some (0, 0) := by
    split at hroot
    · rename_i k hk
      obtain ⟨k1, k2⟩ := k
      simp only [Bool.and_eq_true] at hroot
      rw [hk, Nat.eq_of_beq_eq_true hroot.1, Nat.eq_of_beq_eq_true hroot.2]
    · cases hroot
  have hcovR : ll = true → c.linR = false → walkOk c 0 0 emptyT c.covR c.rI c.rR = true :=
    fun h h' => by simpa [h, h'] using hcR
  have hcovD : (dl = true ∨ lv = true) → walkOk c 3 0 emptyT c.covD c.rI c.rD = true :=
    fun h => by rcases h with h | h <;> simpa [h] using hcD
  obtain ⟨hlen, htr⟩ := chkTrans_spec htr
  -- the certificate of each transition
  have hT : ∀ t : Fin N.trans.length, ∃ e, knth c.trans t = some e ∧ e.pre = N.preMask t ∧
      e.post = N.postMask t ∧ sub ((e.post &&& e.pre) ^^^ e.post) (kmask2 e.us) = true ∧
      TClaim c 0 t e e.psI c.rI c.rI 0 ∧
      (ll = true → (N.tr t).internal = true → decB c.wR e.pre e.post = true ∨
        (c.linR = false ∧ nincB c.wR e.pre e.post = true ∧
          TClaim c 1 t e e.psR c.rR c.rR 0)) ∧
      (lv = true → c.linD = false → e.wit = true → decB c.wD e.pre e.post = true ∨
        (nincB c.wD e.pre e.post = true ∧ TClaim c 2 t e e.psD c.rD c.rD 0)) ∧
      (lv = true → c.linD = true → e.wit = true → decB c.wD e.pre e.post = true) := by
    intro t
    obtain ⟨e, he, h1, h2, h3⟩ := htr t t.isLt
    simp only [Nat.zero_add, transOk, Bool.and_eq_true] at h3
    obtain ⟨⟨⟨⟨⟨⟨⟨hu, hsub⟩, hus⟩, hcov⟩, hI⟩, hR⟩, hDL⟩, hD⟩ := h3
    rw [kall_eq, List.all_eq_true] at hu hus
    refine ⟨e, by rw [knth_eq]; exact he, h1.symm, h2.symm, hsub,
      walkCut_spec hN hv hcut hu hus hcov hI, fun hll hint => ?_, fun hlv hl hw' => ?_,
      fun hlv hl hw' => by simpa [hlv, hl, hw'] using hDL⟩
    · have : (N.trans[t.val]).internal = true := hint
      simp only [hll, this, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true,
        Bool.and_eq_true, Bool.not_eq_true'] at hR
      rcases hR with hR | ⟨⟨hl, hn⟩, hw⟩
      · exact Or.inl hR
      · exact Or.inr ⟨hl, hn, walkOk_spec hN hv hu hus hcov hw⟩
    · simp only [hlv, hl, hw', Bool.not_true, Bool.false_or, Bool.or_eq_true,
        Bool.and_eq_true] at hD
      rcases hD with hD | ⟨hn, hw⟩
      · exact Or.inl hD
      · exact Or.inr ⟨hn, walkOk_spec hN hv hu hus hcov hw⟩
  have hT' : ∀ (j : ℕ) (e : BTrans), knth c.trans j = some e → ∃ t : Fin N.trans.length,
      t.val = j ∧ e.pre = N.preMask t ∧ e.post = N.postMask t := by
    intro j e he
    have hj : j < N.trans.length := by
      rw [knth_eq] at he
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 he).1
    obtain ⟨e', he', h⟩ := hT ⟨j, hj⟩
    rw [he] at he'; cases he'
    exact ⟨⟨j, hj⟩, rfl, h.1, h.2.1⟩
  -- the invariant
  let C : ℕ → Prop := fun m => m < 2 ^ N.places ∧ ∃ ℓ, Reach c c.rI m ℓ ∧ ℓ ≠ 0
  have hC₀ : C (N.pack N.M₀) := by
    refine ⟨Nat.lt_pow_two_of_testBit _ fun q hq => ?_, ?_⟩
    · cases hb : Nat.testBit (N.pack N.M₀) q
      · rfl
      · obtain ⟨h', -⟩ := (testBit_pack N.M₀ q).1 hb; omega
    · split at h₀
      · rename_i l hl
        exact ⟨l, evalB_spec hl, fun h0 => by simp [h0] at h₀⟩
      · cases h₀
  -- firing from the invariant
  have hfire : ∀ m (t : Fin N.trans.length), C m → sub (N.preMask t) m = true →
      (∀ q, (N.postMask t).testBit q = true → (N.preMask t).testBit q = false →
        m.testBit q = false) ∧ C ((m ^^^ N.preMask t) ||| N.postMask t) := by
    rintro m t ⟨hm, ℓ₁, hr, hne⟩ hen
    obtain ⟨e, -, hpre, hpost, hsub, hcl, -⟩ := hT t
    rw [← hpre] at hen
    obtain ⟨hsafe, ℓ₂, hr2, hlc⟩ := hcl m hen ℓ₁ hr hne
    refine ⟨fun q hq hq' => ?_, ?_, ℓ₂, by rw [← hpre, ← hpost]; exact hr2,
      (leafCond_spec hlc hne).1⟩
    · rw [← hpost] at hq; rw [← hpre] at hq'
      have : ((e.post &&& e.pre) ^^^ e.post).testBit q = true := by
        simp [Nat.testBit_xor, hq, hq']
      obtain ⟨u, hu, hu2, rfl⟩ := testBit_kmask2 (sub_iff.1 hsub q this)
      exact hsafe u (by simpa using hu) hu2
    · have hpl := ((wf_spec hwf').2 t).1
      have hpo := ((wf_spec hwf').2 t).2
      apply Nat.lt_pow_two_of_testBit
      intro q hq
      have h1 : m.testBit q = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right Nat.two_pos hq))
      have h2 : (N.preMask t).testBit q = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt_two_pow_mask hpl)
          (Nat.pow_le_pow_right Nat.two_pos hq))
      have h3 : (N.postMask t).testBit q = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt_two_pow_mask hpo)
          (Nat.pow_le_pow_right Nat.two_pos hq))
      simp [Nat.testBit_xor, h1, h2, h3]
  have hclosed : ∀ m l m', C m → N.packed.toLTS.step m l m' → C m' := by
    intro m t m' hm hst
    obtain ⟨hen, rfl⟩ := (packed_step_iff N).1 hst
    exact (hfire m t hm hen).2
  have hsafe : ∀ m, C m → N.safeNode m = true := by
    intro m hm
    simp only [safeNode, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
      Bool.not_eq_true']
    intro t
    cases hen : Nat.beq (m &&& N.preMask t) (N.preMask t)
    · exact Or.inl rfl
    · right
      have hen' : sub (N.preMask t) m = true := by
        rw [sub_eq, Nat.land_comm]; exact hen
      have hs := (hfire m t hm hen').1
      rw [Nat.beq_eq]
      apply Nat.eq_of_testBit_eq
      intro q
      simp only [Nat.testBit_land, Nat.testBit_xor, Nat.zero_testBit]
      cases hq : (N.postMask t).testBit q
      · simp
      · cases hp : (N.preMask t).testBit q
        · simp [hs q hq hp]
        · simp [sub_iff.1 hen' q hp]
  -- the data leaf reached by a marking
  have hleaf : ∀ m ℓ, Reach c c.rD m ℓ → ℓ ≠ 0 → ∃ L, kfind (ℓ / 2) c.leaves = some L ∧
      leafOk c dl lv N.trans.length (2 ^ N.places - 1) (ℓ / 2, L) = true ∧
      (∀ q, L.k1.testBit q = true → m.testBit q = true) ∧
      (∀ q, L.k0.testBit q = true → m.testBit q = false) := by
    intro m ℓ hr hne
    obtain ⟨K, hK, h1, h0⟩ := hr.known hN hroot' (by simp) (by simp)
    rw [kOf_leaf hr.even hne] at hK
    cases hk : kfind (ℓ / 2) c.leaves with
    | none => rw [hk] at hK; cases hK
    | some L =>
      rw [hk] at hK
      simp only [Option.map_some, Option.some.injEq] at hK
      subst hK
      exact ⟨L, rfl, hL _ (mem_of_kfind hk), h1, h0⟩
  -- every marking of the invariant reaches a data leaf
  have hdata : (dl = true ∨ lv = true) → ∀ m, C m → ∃ ℓ L, Reach c c.rD m ℓ ∧ ℓ ≠ 0 ∧
      kfind (ℓ / 2) c.leaves = some L ∧ L.dat = true := by
    rintro hc m ⟨-, ℓ₁, hr, hne⟩
    obtain ⟨ℓ₂, hr2, hlc⟩ := cover_of_walk hN hv (hcovD hc) hr hne
    obtain ⟨hne2, -, lb, -, hlb, -, hdat, -⟩ := leafCond_spec hlc hne
    exact ⟨ℓ₂, lb, hr2, hne2, hlb, hdat (by omega)⟩
  -- the witness of a data leaf is enabled
  have hwit : ∀ m ℓ L, kfind (ℓ / 2) c.leaves = some L → L.dat = true →
      leafOk c dl lv N.trans.length (2 ^ N.places - 1) (ℓ / 2, L) = true →
      (∀ q, L.k1.testBit q = true → m.testBit q = true) →
      (dl = true ∨ (lv = true ∧ L.d ≠ 0)) →
      ∃ t : Fin N.trans.length, t.val = L.wit ∧ sub (N.preMask t) m = true ∧
        (lv = true → c.linD = true → L.d ≠ 0 →
          decB c.wD (N.preMask t) (N.postMask t) = true) ∧
        (lv = true → L.d ≠ 0 → ∀ e, knth c.trans t = some e → e.wit = true) := by
    intro m ℓ L _ hdat hok h1 hc
    simp only [leafOk, hdat, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff] at hok
    obtain ⟨hw, -⟩ := hok
    rcases hw with ⟨hdl, hlv⟩ | ⟨hlt, hw⟩
    · exfalso
      rcases hc with hc | ⟨hc, hd⟩
      · simp [hc] at hdl
      · rcases hlv with hlv | hlv
        · simp [hc] at hlv
        · simp [nbeq_false hd] at hlv
    · split at hw
      · rename_i e he
        obtain ⟨t, ht, hpre, hpost⟩ := hT' _ _ he
        simp only [Bool.and_eq_true] at hw
        obtain ⟨hw, hwt⟩ := hw
        have hwit' : lv = true → L.d ≠ 0 → e.wit = true := fun hlv hd => by
          simpa [hlv, nbeq_false hd] using hwt
        refine ⟨t, ht, sub_iff.2 fun q hq => h1 q ?_, fun hlv hl hd => ?_,
          fun hlv hd e' he' => ?_⟩
        · rw [← hpre] at hq
          exact sub_iff.1 hw q hq
        · obtain ⟨e', he', -, -, -, -, -, -, hDL⟩ := hT t
          rw [ht, he] at he'
          cases he'
          rw [← hpre, ← hpost]
          exact hDL hlv hl (hwit' hlv hd)
        · rw [ht, he] at he'
          cases he'
          exact hwit' hlv hd
      · cases hw
  have hbisim := N.funBisimOn_packed hwf C hclosed hsafe
  have hJ₀ : SafeM N.M₀ ∧ C (N.pack N.M₀) := ⟨hM₀, hC₀⟩
  refine ⟨fun hdl => ?_, fun hll => ?_, fun hlv => ?_,
    fun M hr p => (hbisim.inv_reachable hJ₀ hr).1 p⟩
  · -- deadlock freedom
    refine (hbisim.deadlockFree_iff hJ₀).1 (LTS.DeadlockFree.of_invariant C hC₀ hclosed ?_)
    intro m hm
    obtain ⟨ℓ, L, hr, hne, hk, hdat⟩ := hdata (Or.inl hdl) m hm
    obtain ⟨L', hk', hok, h1, -⟩ := hleaf m ℓ hr hne
    rw [hk] at hk'; cases hk'
    obtain ⟨t, -, hen, -⟩ := hwit m ℓ L hk hdat hok h1 (Or.inl hdl)
    exact ⟨t, _, (packed_step_iff N).2 ⟨hen, rfl⟩⟩
  · -- livelock freedom
    classical
    cases hlr : c.linR
    swap
    · -- from the linear rank
      refine (hbisim.livelockFree_iff hJ₀).1
        (LTS.LivelockFree.of_ranking C hC₀ hclosed (fun m => phiL c.wR m 0) ?_)
      rintro m t m' - hint hst
      obtain ⟨hen, rfl⟩ := (packed_step_iff N).1 hst
      obtain ⟨e, -, hpre, hpost, -, -, hR, -⟩ := hT t
      rcases hR hll hint with hd | ⟨h, -⟩
      · rw [hpre, hpost] at hd
        exact phiL_lt hen hd
      · rw [hlr] at h; cases h
    let V : ℕ → ℕ := fun m =>
      if h : ∃ ℓ, Reach c c.rR m ℓ then
        ((kfind (Classical.choose h / 2) c.leaves).map BLeaf.r).getD 0 else 0
    have hV : ∀ m ℓ L, Reach c c.rR m ℓ → kfind (ℓ / 2) c.leaves = some L → V m = L.r := by
      intro m ℓ L hr hk
      have hex : ∃ ℓ, Reach c c.rR m ℓ := ⟨ℓ, hr⟩
      simp only [V, dite_eq_left hex]
      rw [(Classical.choose_spec hex).det hr, hk]; rfl
    -- the ranks are bounded by their sum `S`
    let S := (c.leaves.toList.map fun x => x.2.r).sum
    have hVS : ∀ m, V m ≤ S := by
      intro m
      simp only [V]
      split
      · cases hk : kfind (Classical.choose ‹∃ ℓ, Reach c c.rR m ℓ› / 2) c.leaves with
        | none => simp
        | some L =>
          simp only [Option.map_some, Option.getD_some]
          exact le_sum_of_mem_nat (List.mem_map.2 ⟨_, mem_of_kfind hk, rfl⟩)
      · exact Nat.zero_le _
    -- the linear rank first, then the rank diagram
    refine (hbisim.livelockFree_iff hJ₀).1 (LTS.LivelockFree.of_ranking C hC₀ hclosed
      (fun m => phiL c.wR m 0 * (S + 1) + V m) ?_)
    rintro m t m' ⟨hm, ℓ₀, hr0, hne0⟩ hint hst
    obtain ⟨hen, rfl⟩ := (packed_step_iff N).1 hst
    obtain ⟨e, -, hpre, hpost, -, -, hR, -⟩ := hT t
    rcases hR hll hint with hd | ⟨-, hn, hR⟩
    · rw [hpre, hpost] at hd
      have h1 := Nat.mul_le_mul_right (S + 1) (phiL_lt hen hd)
      have h2 := hVS ((m ^^^ N.preMask t) ||| N.postMask t)
      rw [Nat.succ_mul] at h1
      omega
    obtain ⟨ℓ₁, hr, hlc0⟩ := cover_of_walk hN hv (hcovR hll hlr) hr0 hne0
    have hne := (leafCond_spec hlc0 hne0).1
    rw [← hpre] at hen
    obtain ⟨-, ℓ₂, hr2, hlc⟩ := hR m hen ℓ₁ hr hne
    rw [hpre, hpost] at hr2 hn
    rw [hpre] at hen
    obtain ⟨-, la, lb, hla, hlb, hrk, -⟩ := leafCond_spec hlc hne
    have h1 := Nat.mul_le_mul_right (S + 1) (phiL_le hen hn)
    have h2 := hrk rfl
    rw [← hV _ _ _ hr hla, ← hV _ _ _ hr2 hlb] at h2
    omega
  · -- liveness
    refine (hbisim.live_iff hJ₀).1 fun t m hreach => ?_
    -- simulating a trace
    have hsimR : ∀ (tr : List ℕ) (m m' : ℕ), simB c.trans m tr = some m' →
        N.packed.toLTS.Reachable m m' := by
      intro tr
      induction tr with
      | nil => intro m m' h; simp only [simB, Option.some.injEq] at h; subst h; rfl
      | cons j js ih =>
        intro m m' h
        obtain ⟨e, he, hen, h'⟩ := simB_cons h
        obtain ⟨t', -, hpre, hpost⟩ := hT' _ _ he
        rw [hpre, hpost] at h'
        rw [hpre] at hen
        exact LTS.Reachable.head ⟨t', (packed_step_iff N).2 ⟨hen, rfl⟩⟩ (ih _ _ h')
    -- a hub is a single marking, with a trace enabling `t`
    have hhub : ∀ m ℓ L, C m → Reach c c.rD m ℓ → ℓ ≠ 0 →
        kfind (ℓ / 2) c.leaves = some L → L.dat = true → L.d = 0 →
        ∃ m', N.packed.toLTS.Reachable m m' ∧ N.packed.toLTS.Enabled m' t := by
      intro m ℓ L hm hr hne hk hdat hd0
      obtain ⟨L', hk', hok, h1, h0⟩ := hleaf m ℓ hr hne
      rw [hk] at hk'; cases hk'
      simp only [leafOk, hdat, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at hok
      obtain ⟨-, hhub⟩ := hok
      rcases hhub with hhub | hhub
      · simp [hlv, hd0] at hhub
      obtain ⟨⟨⟨hfull, hk1⟩, hlen'⟩, htrs⟩ := hhub
      have hmk : m = L.k1 := by
        apply Nat.eq_of_testBit_eq
        intro q
        by_cases hq : q < N.places
        · have hb : (2 ^ N.places - 1).testBit q = true := by
            rw [Nat.testBit_two_pow_sub_one]; simpa using hq
          have := sub_iff.1 hfull q hb
          rw [Nat.testBit_lor] at this
          cases h1q : L.k1.testBit q
          · rw [h1q, Bool.false_or] at this; exact h0 q this
          · exact h1 q h1q
        · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm.1
            (Nat.pow_le_pow_right Nat.two_pos (by omega)))]
          have : L.k1 < 2 ^ N.places := by
            have := blt_true hk1
            have hp : 0 < 2 ^ N.places := Nat.two_pow_pos _
            omega
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le this
            (Nat.pow_le_pow_right Nat.two_pos (by omega)))]
      subst hmk
      obtain ⟨m', e, hsim, he, hen⟩ := tracesOk_spec htrs t
        (by rw [Nat.eq_of_beq_eq_true hlen']; exact t.isLt)
      obtain ⟨t', ht', hpre, -⟩ := hT' _ _ (by simpa using he)
      have : t' = t := Fin.ext ht'
      subst this
      rw [hpre] at hen
      exact ⟨m', hsimR _ _ _ hsim, _, (packed_step_iff N).2 ⟨hen, rfl⟩⟩
    have hm := hreach.invariant hC₀ hclosed
    cases hld : c.linD
    · -- by the linear potential and the distances, lexicographically: the witness decreases
      -- the potential, or keeps it and leads closer to a hub
      have key : ∀ p d, ∀ m ℓ L, C m → Reach c c.rD m ℓ → ℓ ≠ 0 →
          kfind (ℓ / 2) c.leaves = some L → L.dat = true → phiL c.wD m 0 = p → L.d = d →
          ∃ m', N.packed.toLTS.Reachable m m' ∧ N.packed.toLTS.Enabled m' t := by
        intro p
        induction p using Nat.strong_induction_on with
        | _ p IHp =>
        intro d
        induction d using Nat.strong_induction_on with
        | _ d IH =>
        intro m ℓ L hm hr hne hk hdat hp hd
        by_cases hd0 : L.d = 0
        · exact hhub m ℓ L hm hr hne hk hdat hd0
        obtain ⟨L', hk', hok, h1, -⟩ := hleaf m ℓ hr hne
        rw [hk] at hk'; cases hk'
        obtain ⟨w, hw, hen, -, hwt⟩ := hwit m ℓ L hk hdat hok h1 (Or.inr ⟨hlv, hd0⟩)
        have hC' := (hfire m w hm hen).2
        -- from the next marking on
        have next : phiL c.wD ((m ^^^ N.preMask w) ||| N.postMask w) 0 < p →
            ∃ m', N.packed.toLTS.Reachable m m' ∧ N.packed.toLTS.Enabled m' t := by
          intro hlt
          obtain ⟨ℓ', L', hr', hne', hk'', hdat'⟩ := hdata (Or.inr hlv) _ hC'
          obtain ⟨m', hr'', hen'⟩ := IHp _ hlt L'.d _ ℓ' L' hC' hr' hne' hk'' hdat' rfl rfl
          exact ⟨m', LTS.Reachable.head ⟨w, (packed_step_iff N).2 ⟨hen, rfl⟩⟩ hr'', hen'⟩
        obtain ⟨e, he, hpre, hpost, -, -, -, hD, -⟩ := hT w
        rcases hD hlv hld (hwt hlv hd0 e he) with hdec | ⟨hn, hD⟩
        · rw [hpre, hpost] at hdec
          exact next (hp ▸ phiL_lt hen hdec)
        rw [hpre, hpost] at hn
        rcases Nat.lt_or_eq_of_le (hp ▸ phiL_le hen hn) with hlt | heq
        · exact next hlt
        rw [← hpre] at hen
        obtain ⟨-, ℓ₂, hr2, hlc⟩ := hD m hen ℓ hr hne
        rw [hpre, hpost] at hr2
        rw [hpre] at hen
        obtain ⟨hne2, la, lb, hla, hlb, -, hdat2, hdd⟩ := leafCond_spec hlc hne
        rw [hk] at hla; cases hla
        obtain ⟨m', hr', hen'⟩ := IH lb.d (hd ▸ hdd rfl hw.symm hd0) _ ℓ₂ lb hC' hr2 hne2 hlb
          (hdat2 (by omega)) heq rfl
        exact ⟨m', LTS.Reachable.head ⟨w, (packed_step_iff N).2 ⟨hen, rfl⟩⟩ hr', hen'⟩
      obtain ⟨ℓ, L, hr, hne, hk, hdat⟩ := hdata (Or.inr hlv) m hm
      exact key _ _ m ℓ L hm hr hne hk hdat rfl rfl
    · -- by the linear potential, which the witness decreases
      have key : ∀ n, ∀ m, C m → phiL c.wD m 0 = n →
          ∃ m', N.packed.toLTS.Reachable m m' ∧ N.packed.toLTS.Enabled m' t := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n IH =>
        intro m hm hn
        obtain ⟨ℓ, L, hr, hne, hk, hdat⟩ := hdata (Or.inr hlv) m hm
        by_cases hd0 : L.d = 0
        · exact hhub m ℓ L hm hr hne hk hdat hd0
        obtain ⟨L', hk', hok, h1, -⟩ := hleaf m ℓ hr hne
        rw [hk] at hk'; cases hk'
        obtain ⟨w, -, hen, hdec, -⟩ := hwit m ℓ L hk hdat hok h1 (Or.inr ⟨hlv, hd0⟩)
        have hC' := (hfire m w hm hen).2
        have hlt := phiL_lt hen (hdec hlv hld hd0)
        obtain ⟨m', hr', hen'⟩ := IH _ (hn ▸ hlt) _ hC' rfl
        exact ⟨m', LTS.Reachable.head ⟨w, (packed_step_iff N).2 ⟨hen, rfl⟩⟩ hr', hen'⟩
      exact key _ m hm rfl

theorem correct_of_checkBDD {c : BCert} (h : N.checkBDD true true true c = true) :
    N.Correct ∧ N.Safe :=
  let h := of_checkBDD h
  ⟨⟨h.1 rfl, h.2.1 rfl, h.2.2.1 rfl⟩, h.2.2.2⟩

theorem correct_of_checkBDD_lf {c : BCert} (h : N.checkBDD true false true c = true)
    (hlf : N.toNet.lts.LivelockFree N.Internal N.M₀) : N.Correct ∧ N.Safe :=
  let h := of_checkBDD h
  ⟨⟨h.1 rfl, hlf, h.2.2.1 rfl⟩, h.2.2.2⟩

theorem deadlockFree_of_checkBDD {c : BCert} (h : N.checkBDD true false false c = true) :
    N.toNet.lts.DeadlockFree N.M₀ :=
  (of_checkBDD h).1 rfl

theorem livelockFree_of_checkBDD {c : BCert} (h : N.checkBDD false true false c = true) :
    N.toNet.lts.LivelockFree N.Internal N.M₀ :=
  (of_checkBDD h).2.1 rfl

theorem live_of_checkBDD {c : BCert} (h : N.checkBDD false false true c = true) :
    N.toNet.lts.Live N.M₀ :=
  (of_checkBDD h).2.2.1 rfl

theorem safe_of_checkBDD {c : BCert} (h : N.checkBDD false false false c = true) : N.Safe :=
  (of_checkBDD h).2.2.2

end PNet

end AsyncLean
