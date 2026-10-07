/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Affine

/-!
# Bit-parallel certificates: sets of states as bitmaps

The fast checker (`AsyncLean.Checker.Fast`) visits the states one by one, and each visit
costs the kernel a few unfoldings of the successor function and of the search tree.  This
file checks **many states at once**.  A set of packed states that agree on their high bits
`h = x / 2^k` is stored as one number, a *bitmap* `B` with bit `l` set when the state
`h * 2^k + l` is in the set.  The kernel's arithmetic on natural numbers is native (GMP),
so an operation on a bitmap of `2^k` positions costs a few machine instructions per 64
states.

For a transition of an `Aff.Tr` table (markings packed by a layout, `PNet.atable`):

* its guard is a conjunction of tests on fields.  Tests on the low `k` bits become a *mask*
  of the positions that pass them (`tmask`, built from the masks `bm k i` of the positions
  whose bit `i` is set); tests on the high bits are evaluated once, on `h`;
* firing it adds a constant and subtracts a constant.  On the states of `B` that enable it,
  this moves the chunk to `h + addH - subH` and shifts the bitmap by `addL - subL`: **one
  shift fires the transition in every state of the chunk** (`shiftBy`), once the kernel has
  checked with two more shifts that no state of the chunk borrows from or carries into the
  high bits (`rangeOk`).

A certificate (`Cert`) is a search tree of *chunks* — the high bits, the bitmap of the states
(`all`), and two gradings of them into cumulative layers: ranks (for livelock freedom) and
distances to *hubs* (for liveness) — together with the hubs and their traces, as for the
fast checker.  The kernel checks (`check`) that

* the initial state is in the set, and every transition maps the set into itself, without
  breaking the encoding (the `ok` tests);
* every state enables a transition (deadlock freedom);
* an internal transition maps each rank layer below its rank (livelock freedom);
* each distance layer above `0` lies in the *preimage* of the lower layers (computed by the
  inverse shift), and the layer `0` consists of hubs, from which traces enable every label
  (liveness).

`Bitmap.of_check` gives the same conclusions as `Fast.of_check`, for any system that the
table encodes (`Fast.Encodes`).  Duplicate bitmaps of a certificate are shared in the proof
term, so the kernel's evaluation cache also computes each image only once.
-/

namespace AsyncLean

namespace Bitmap

open Fast Aff

/-! ### Kernel-friendly helpers and masks -/

/-- `a && b`, by the recursor. -/
noncomputable def band (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

/-- `a ⊆ b` for bitmaps. -/
noncomputable def sub (a b : ℕ) : Bool := Nat.beq (Nat.land a b) a

/-- The low `k` bits of `x`. -/
noncomputable def lo (k x : ℕ) : ℕ := Nat.land x (Nat.sub (Nat.shiftLeft 1 k) 1)

/-- The bits of `x` above `k`. -/
noncomputable def hi (k x : ℕ) : ℕ := Nat.shiftRight x k

/-- Every position below `2^k`. -/
noncomputable def full (k : ℕ) : ℕ := Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 k)) 1

/-- The positions below `2^k` whose bit `i` is set, by doubling. -/
noncomputable def bm (k i : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun j r => Bool.rec (motive := fun _ => ℕ)
      (Nat.lor r (Nat.shiftLeft r (Nat.shiftLeft 1 j)))
      (Nat.shiftLeft (full j) (Nat.shiftLeft 1 j)) (Nat.beq i j)) k

/-- The positions whose bits `sh … sh + w - 1` agree with those of `c`. -/
noncomputable def eqMaskAux (k sh c : ℕ) (w : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (full k)
    (fun j r => Nat.land r (Bool.rec (motive := fun _ => ℕ) (Nat.xor (full k) (bm k (Nat.add sh j)))
      (bm k (Nat.add sh j)) (ktest c j))) w

/-- The positions whose field of `w` bits at `sh` holds `c`. -/
noncomputable def eqMask (k sh w c : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0 (eqMaskAux k sh c w) (Nat.blt c (Nat.pow 2 w))

/-- The positions whose field holds one of `a, …, a + n - 1`. -/
noncomputable def orRange (k sh w a n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i r => Nat.lor r (eqMask k sh w (Nat.add a i))) n

/-- The smaller of two numbers. -/
noncomputable def kmin (a b : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) b a (Nat.ble a b)

/-- **The mask of a test**: the positions below `2^k` that pass it. -/
noncomputable def tmask (k : ℕ) (a : Test) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (eqMask k a.sh a.w a.c)
    (fun j _ => Nat.rec (motive := fun _ => ℕ)
      (orRange k a.sh a.w a.c (Nat.sub (Nat.pow 2 a.w) a.c))
      (fun _ _ => orRange k a.sh a.w 0 (kmin (Nat.succ a.c) (Nat.pow 2 a.w))) j) a.kind

/-- The test reads only the low `k` bits. -/
noncomputable def isLow (k : ℕ) (a : Test) : Bool := Nat.ble (Nat.add a.sh a.w) k

/-- The test reads only the bits above `k`. -/
noncomputable def isHigh (k : ℕ) (a : Test) : Bool := Nat.ble k a.sh

/-- Every test is low or high. -/
noncomputable def splitOk (k : ℕ) (ts : List Test) : Bool :=
  kall ts fun a => Bool.rec (motive := fun _ => Bool) (isHigh k a) true (isLow k a)

/-- The high tests, on the high bits `h`. -/
noncomputable def gH (k h : ℕ) (ts : List Test) : Bool :=
  kall ts fun a => Bool.rec (motive := fun _ => Bool) true
    (cmp a.kind (fld h (Nat.sub a.sh k) a.w) a.c) (isHigh k a)

/-- The mask of the low tests. -/
noncomputable def gL (k : ℕ) (ts : List Test) : ℕ :=
  List.rec (motive := fun _ => ℕ) (full k)
    (fun a _ r => Bool.rec (motive := fun _ => ℕ) r (Nat.land r (tmask k a)) (isLow k a)) ts

/-- The mask of a Boolean guard in the chunk `h`: the variables of the high bits are
constants there. -/
noncomputable def bmaskE (k h : ℕ) (e : BExpr) : ℕ :=
  BExpr.rec (motive := fun _ => ℕ)
    (fun i => Bool.rec (motive := fun _ => ℕ) (bm k i)
      (Bool.rec (motive := fun _ => ℕ) 0 (full k) (ktest h (Nat.sub i k))) (Nat.ble k i))
    (fun b => Bool.rec (motive := fun _ => ℕ) 0 (full k) b)
    (fun _ r => Nat.xor (full k) r)
    (fun _ _ ra rb => Nat.land ra rb)
    (fun _ _ ra rb => Nat.lor ra rb)
    (fun _ _ ra rb => Nat.xor ra rb) e

/-- The expression is the constant `true`. -/
noncomputable def isTrueE (e : BExpr) : Bool :=
  BExpr.rec (motive := fun _ => Bool) (fun _ => false) (fun b => b) (fun _ _ => false)
    (fun _ _ _ _ => false) (fun _ _ _ _ => false) (fun _ _ _ _ => false) e

/-- The mask of the low tests and of the Boolean guard of `e`, in the chunk `h`. -/
noncomputable def gLB (k h : ℕ) (e : Tr) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.land (gL k e.guard) (bmaskE k h e.bg)) (gL k e.guard)
    (isTrueE e.bg)

/-- Fire, in every state of `S` at once: shift by `addL - subL`. -/
noncomputable def shiftBy (S addL subL : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight S (Nat.sub subL addL))
    (Nat.shiftLeft S (Nat.sub addL subL)) (Nat.ble subL addL)

/-- The inverse shift: the positions whose image is in `X`. -/
noncomputable def unshiftBy (X addL subL : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftLeft X (Nat.sub subL addL))
    (Nat.shiftRight X (Nat.sub addL subL)) (Nat.ble subL addL)

/-- No position of `S` borrows from or carries into the high bits. -/
noncomputable def rangeOk (k S addL subL : ℕ) : Bool :=
  band (Nat.beq (Nat.shiftLeft (Nat.shiftRight S (Nat.sub subL addL)) (Nat.sub subL addL)) S)
    (Nat.beq (Nat.shiftRight S (Nat.sub (Nat.add (Nat.shiftLeft 1 k) subL) addL)) 0)

/-! ### Certificates -/

/-- A certificate: the bitmaps of the chunks keyed by their high bits, the hubs with one trace
per label, and the numbers of rounds of the rank and distance computations. -/
abbrev Cert := BTree (ℕ × ℕ) × List (ℕ × List (List ℕ)) × ℕ × ℕ

/-- The bitmap of the chunk `h` (`0` if none). -/
noncomputable def look (h : ℕ) (D : BTree (ℕ × ℕ)) : ℕ :=
  Option.rec (motive := fun _ => ℕ) 0 (fun v => v) (kfind h D)

/-- Map the bitmaps of a tree, keeping the keys. -/
noncomputable def tmap (f : ℕ → ℕ → ℕ) (t : BTree (ℕ × ℕ)) : BTree (ℕ × ℕ) :=
  BTree.rec (motive := fun _ => BTree (ℕ × ℕ)) BTree.leaf
    (fun _ x _ l r => BTree.node l (x.1, f x.1 x.2) r) t

/-- The chunk that transition `e` leads to from the chunk `h`. -/
noncomputable def tgt (k h : ℕ) (e : Tr) : ℕ := Nat.sub (Nat.add h (hi k e.add)) (hi k e.sub)

/-- The checks of transition `e` at the chunk `h`, once the states `S ≠ 0` of the chunk
enabling it are known: the `ok` tests, no borrow or carry, and the image in the set. -/
noncomputable def chkS (k : ℕ) (t : BTree (ℕ × ℕ)) (h : ℕ) (e : Tr) (S : ℕ) : Bool :=
  band (gH k h e.ok) (band (sub S (gL k e.ok))
    (band (Nat.ble (hi k e.sub) (Nat.add h (hi k e.add)))
    (band (rangeOk k S (lo k e.add) (lo k e.sub))
      (sub (shiftBy S (lo k e.add) (lo k e.sub)) (look (tgt k h e) t)))))

/-- The checks of transition `e` at the chunk `h` with bitmap `a`. -/
noncomputable def chkOne (k : ℕ) (t : BTree (ℕ × ℕ)) (h a : ℕ) (e : Tr) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool) (chkS k t h e (Nat.land a (gLB k h e)))
      true (Nat.beq (Nat.land a (gLB k h e)) 0))
    (gH k h e.guard)

/-- The positions of the chunk `h` enabling some transition. -/
noncomputable def enAny (k : ℕ) (tb : List Tr) (h : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun e _ acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.lor acc (gLB k h e))
      (gH k h e.guard)) tb

/-- The checks at one chunk: closure under every transition, and deadlock freedom. -/
noncomputable def chkChunk (tb : List Tr) (k : ℕ) (t : BTree (ℕ × ℕ)) (dl : Bool)
    (x : ℕ × ℕ) : Bool :=
  band (Bool.rec (motive := fun _ => Bool) true (sub x.2 (enAny k tb x.1)) dl)
    (kall tb (chkOne k t x.1 x.2))

/-- The positions of the chunk `h` from which transition `e` leads into `D`. -/
noncomputable def preOf (k : ℕ) (D : BTree (ℕ × ℕ)) (h : ℕ) (e : Tr) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0
    (Bool.rec (motive := fun _ => ℕ) 0
      (Nat.land (gLB k h e) (unshiftBy (look (tgt k h e) D) (lo k e.add) (lo k e.sub)))
      (Nat.ble (hi k e.sub) (Nat.add h (hi k e.add))))
    (gH k h e.guard)

/-- The positions of the chunk `h` with a step into `D` by a transition of `kD` (numbered
from `i`). -/
noncomputable def prog (k kD : ℕ) (D : BTree (ℕ × ℕ)) (tb : List Tr) (h : ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun e _ rec i => Bool.rec (motive := fun _ => ℕ) (rec (Nat.succ i))
      (Nat.lor (rec (Nat.succ i)) (preOf k D h e)) (ktest kD i)) tb

/-- The positions of the chunk `h` enabling a transition of `dD` (numbered from `i`). -/
noncomputable def decEn (k dD : ℕ) (tb : List Tr) (h : ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun e _ rec i => Bool.rec (motive := fun _ => ℕ) (rec (Nat.succ i))
      (Bool.rec (motive := fun _ => ℕ) (rec (Nat.succ i)) (Nat.lor (rec (Nat.succ i)) (gLB k h e))
        (gH k h e.guard)) (ktest dD i)) tb

/-- The positions of the hubs in the chunk `h`. -/
noncomputable def hubBits (k h : ℕ) (hubs : List (ℕ × List (List ℕ))) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0
    (fun x _ acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.lor acc (Nat.shiftLeft 1 (lo k x.1)))
      (Nat.beq (hi k x.1) h)) hubs

/-- One round of backward reachability towards the hubs, by the transitions of `kD`. -/
noncomputable def dstep (k kD : ℕ) (t : BTree (ℕ × ℕ)) (tb : List Tr) (D : BTree (ℕ × ℕ)) :
    BTree (ℕ × ℕ) :=
  tmap (fun h a => Nat.lor (look h D) (Nat.land a (prog k kD D tb h 0))) t

/-- The states reaching, within `n` steps of `kD`, a hub or a state enabling a transition of
`dD`. -/
noncomputable def distIter (k dD kD : ℕ) (t : BTree (ℕ × ℕ)) (tb : List Tr)
    (hubs : List (ℕ × List (List ℕ))) (n : ℕ) : BTree (ℕ × ℕ) :=
  Nat.rec (motive := fun _ => BTree (ℕ × ℕ))
    (tmap (fun h a => Nat.land a (Nat.lor (hubBits k h hubs) (decEn k dD tb h 0))) t)
    (fun _ D => dstep k kD t tb D) n

/-- The positions of the chunk `h` with a step by `e` to a state of the set outside `R`. -/
noncomputable def badOf (k : ℕ) (t R : BTree (ℕ × ℕ)) (h : ℕ) (e : Tr) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) 0
    (Bool.rec (motive := fun _ => ℕ) 0
      (Nat.land (gLB k h e) (unshiftBy (Nat.xor (look (tgt k h e) t)
        (Nat.land (look (tgt k h e) t) (look (tgt k h e) R))) (lo k e.add) (lo k e.sub)))
      (Nat.ble (hi k e.sub) (Nat.add h (hi k e.add))))
    (gH k h e.guard)

/-- The positions of the chunk `h` with an internal step (a transition of `imask` outside
`dR`, numbered from `i`) to a state of the set outside `R`. -/
noncomputable def bad (k imask dR : ℕ) (t R : BTree (ℕ × ℕ)) (tb : List Tr) (h : ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun e _ rec i => Bool.rec (motive := fun _ => ℕ) (rec (Nat.succ i))
      (Bool.rec (motive := fun _ => ℕ) (Nat.lor (rec (Nat.succ i)) (badOf k t R h e))
        (rec (Nat.succ i)) (ktest dR i)) (ktest imask i)) tb

/-- One round of ranking: the states whose internal steps outside `dR` all lead into `R` join
it. -/
noncomputable def rstep (k imask dR : ℕ) (t : BTree (ℕ × ℕ)) (tb : List Tr)
    (R : BTree (ℕ × ℕ)) : BTree (ℕ × ℕ) :=
  tmap (fun h a => Nat.lor (look h R) (Nat.xor a (Nat.land a (bad k imask dR t R tb h 0)))) t

/-- The states from which every run of internal steps outside `dR` is shorter than `n`. -/
noncomputable def rankIter (k imask dR : ℕ) (t : BTree (ℕ × ℕ)) (tb : List Tr) (n : ℕ) :
    BTree (ℕ × ℕ) :=
  Nat.rec (motive := fun _ => BTree (ℕ × ℕ)) (tmap (fun _ _ => 0) t)
    (fun _ R => rstep k imask dR t tb R) n

/-- **The bitmap checker.**  The potentials of the ranks and distances are given by the
masks `dR` (internal transitions decreasing the rank potential), `dD` (transitions decreasing
the distance potential) and `kD` (transitions not increasing it). -/
noncomputable def check (tb : List Tr) (k imask dR dD kD L : ℕ) (dl lv : Bool) (s₀ : ℕ)
    (c : Cert) : Bool :=
  band (kall tb fun e => band (splitOk k e.guard) (splitOk k e.ok))
    (band (ktest (look (hi k s₀) c.1) (lo k s₀))
    (band (ktall c.1 (chkChunk tb k c.1 dl))
    (band (ktall c.1 fun x => sub x.2 (look x.1 (rankIter k imask dR c.1 tb c.2.2.1)))
      (Bool.rec (motive := fun _ => Bool) true
        (band (ktall c.1 fun x => sub x.2 (look x.1 (distIter k dD kD c.1 tb c.2.1 c.2.2.2)))
          (kall c.2.1 fun h => band (Nat.beq h.2.length L) (chkTraces (asucc tb) h.1 h.2 0)))
        lv))))

/-- The first part of `check`: the tests split, the initial state is in the set, and every
chunk is closed (and deadlock free). -/
noncomputable def checkA (tb : List Tr) (k : ℕ) (dl : Bool) (s₀ : ℕ) (c : Cert) : Bool :=
  band (kall tb fun e => band (splitOk k e.guard) (splitOk k e.ok))
    (band (ktest (look (hi k s₀) c.1) (lo k s₀)) (ktall c.1 (chkChunk tb k c.1 dl)))

/-- The second part of `check`: the rank rounds cover the set. -/
noncomputable def checkR (tb : List Tr) (k imask dR : ℕ) (c : Cert) : Bool :=
  ktall c.1 fun x => sub x.2 (look x.1 (rankIter k imask dR c.1 tb c.2.2.1))

/-- The third part of `check`: the distance rounds cover the set, and the hubs' traces. -/
noncomputable def checkD (tb : List Tr) (k dD kD L : ℕ) (lv : Bool) (c : Cert) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (band (ktall c.1 fun x => sub x.2 (look x.1 (distIter k dD kD c.1 tb c.2.1 c.2.2.2)))
      (kall c.2.1 fun h => band (Nat.beq h.2.length L) (chkTraces (asucc tb) h.1 h.2 0)))
    lv

/-! ### Bit-level facts -/

section Bits

theorem ble_t {a b : ℕ} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem ble_f {a b : ℕ} (h : Nat.ble a b = false) : b < a := by
  by_contra h'
  rw [Nat.ble_eq_true_of_le (by omega)] at h; cases h

theorem blt_t {a b : ℕ} (h : Nat.blt a b = true) : a < b := ble_t h

theorem blt_f {a b : ℕ} (h : Nat.blt a b = false) : b ≤ a := by
  have := ble_f (a := a + 1) (b := b) h; omega

theorem band_eq {a b : Bool} : band a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [band]

theorem sub_spec {a b : ℕ} (h : sub a b = true) {i : ℕ} (hi : a.testBit i = true) :
    b.testBit i = true := by
  have := Nat.eq_of_beq_eq_true h
  have h2 := congrArg (fun x => Nat.testBit x i) this
  change (a &&& b).testBit i = a.testBit i at h2
  rw [Nat.testBit_and, hi] at h2
  simpa using h2

theorem shiftLeft_one (k : ℕ) : Nat.shiftLeft 1 k = 2 ^ k := by
  change 1 <<< k = _; rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem lo_eq (k x : ℕ) : lo k x = x % 2 ^ k := by
  change x &&& (Nat.shiftLeft 1 k - 1) = _
  rw [shiftLeft_one, Nat.and_two_pow_sub_one_eq_mod]

theorem hi_eq (k x : ℕ) : hi k x = x / 2 ^ k := by
  change x >>> k = _; rw [Nat.shiftRight_eq_div_pow]

theorem full_eq (k : ℕ) : full k = 2 ^ 2 ^ k - 1 := by
  change Nat.shiftLeft 1 (Nat.shiftLeft 1 k) - 1 = _
  rw [shiftLeft_one, shiftLeft_one]

theorem testBit_full (k l : ℕ) : (full k).testBit l = decide (l < 2 ^ k) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_lt_two_pow_iff {l k : ℕ} (hl : l < 2 ^ (k + 1)) :
    l.testBit k = decide (2 ^ k ≤ l) := by
  by_cases h : 2 ^ k ≤ l
  · obtain ⟨m, rfl⟩ : ∃ m, l = 2 ^ k + m := ⟨l - 2 ^ k, by omega⟩
    have hm : m < 2 ^ k := by rw [Nat.pow_succ] at hl; omega
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]; simp
  · rw [Nat.testBit_lt_two_pow (by omega)]; simp [h]

theorem testBit_bm (k i l : ℕ) : (bm k i).testBit l = (decide (l < 2 ^ k) && l.testBit i) := by
  induction k generalizing l with
  | zero =>
    change (0 : ℕ).testBit l = _
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    · have : decide (l < 2 ^ 0) = false := by simp; omega
      rw [this]; simp
  | succ k ih =>
    have hpk : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    change (Bool.rec (motive := fun _ => ℕ) (Nat.lor (bm k i) (Nat.shiftLeft (bm k i)
      (Nat.shiftLeft 1 k))) (Nat.shiftLeft (full k) (Nat.shiftLeft 1 k)) (Nat.beq i k)).testBit l
      = _
    rw [shiftLeft_one]
    cases hik : Nat.beq i k
    · have hne : i ≠ k := fun h => by rw [h, Nat.beq_refl] at hik; cases hik
      change (bm k i ||| (bm k i <<< 2 ^ k)).testBit l = _
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, ih, ih]
      by_cases hl : l < 2 ^ k
      · have h1 : ¬ (l ≥ 2 ^ k) := by omega
        have h2 : l < 2 ^ (k + 1) := by omega
        simp [hl, h1, h2]
      · obtain ⟨m, rfl⟩ : ∃ m, l = 2 ^ k + m := ⟨l - 2 ^ k, by omega⟩
        have e1 : (2 ^ k + m) - 2 ^ k = m := by omega
        simp only [hl, decide_false, Bool.false_and, Bool.false_or, ge_iff_le, Nat.le_add_right,
          decide_true, Bool.true_and, e1]
        by_cases hm : m < 2 ^ k
        · have h2 : 2 ^ k + m < 2 ^ (k + 1) := by omega
          simp only [hm, decide_true, Bool.true_and, h2]
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · rw [Nat.testBit_two_pow_add_gt h]
          · have h3 : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
            rw [Nat.testBit_lt_two_pow (by omega : m < 2 ^ i),
              Nat.testBit_lt_two_pow (by omega : 2 ^ k + m < 2 ^ i)]
        · have h2 : ¬ 2 ^ k + m < 2 ^ (k + 1) := by omega
          simp [hm, h2]
    · have hik' : i = k := Nat.eq_of_beq_eq_true hik
      subst hik'
      change ((full i) <<< 2 ^ i).testBit l = _
      rw [Nat.testBit_shiftLeft, testBit_full]
      by_cases hl : 2 ^ i ≤ l
      · by_cases hl2 : l < 2 ^ (i + 1)
        · have h3 : l - 2 ^ i < 2 ^ i := by omega
          have := testBit_lt_two_pow_iff hl2
          simp [hl, hl2, h3, this]
        · have h3 : ¬ l - 2 ^ i < 2 ^ i := by omega
          simp [hl, hl2, h3]
      · have hl2 : l < 2 ^ (i + 1) := by omega
        have := testBit_lt_two_pow_iff hl2
        simp [hl, hl2, this]

theorem testBit_fld (x sh w j : ℕ) :
    (fld x sh w).testBit j = (decide (j < w) && x.testBit (j + sh)) := by
  rw [fld_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

theorem testBit_eqMaskAux {k sh c l : ℕ} (hl : l < 2 ^ k) (w : ℕ) :
    (eqMaskAux k sh c w).testBit l = decide (∀ j < w, l.testBit (sh + j) = c.testBit j) := by
  induction w with
  | zero => change (full k).testBit l = _; rw [testBit_full]; simp [hl]
  | succ w ih =>
    change (Nat.land (eqMaskAux k sh c w) (Bool.rec (motive := fun _ => ℕ)
      (Nat.xor (full k) (bm k (Nat.add sh w))) (bm k (Nat.add sh w)) (ktest c w))).testBit l = _
    change (eqMaskAux k sh c w &&& _).testBit l = _
    rw [Nat.testBit_and, ih, ktest_eq]
    have hlt : ∀ j, j < w + 1 ↔ j < w ∨ j = w := fun j => by omega
    cases hc : c.testBit w
    · change (decide _ && (full k ^^^ bm k (sh + w)).testBit l) = _
      rw [Nat.testBit_xor, testBit_full, testBit_bm]
      simp only [hl, decide_true, Bool.true_and, Bool.true_xor]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', hlt]
      constructor
      · rintro ⟨h1, h2⟩ j (hj | rfl)
        · exact h1 j hj
        · rw [hc, h2]
      · intro h
        exact ⟨fun j hj => h j (Or.inl hj), by rw [h w (Or.inr rfl), hc]⟩
    · change (decide _ && (bm k (sh + w)).testBit l) = _
      rw [testBit_bm]
      simp only [hl, decide_true, Bool.true_and]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, hlt]
      constructor
      · rintro ⟨h1, h2⟩ j (hj | rfl)
        · exact h1 j hj
        · rw [hc, h2]
      · intro h
        exact ⟨fun j hj => h j (Or.inl hj), by rw [h w (Or.inr rfl), hc]⟩

theorem testBit_eqMask {k sh w c l : ℕ} (hl : l < 2 ^ k) :
    (eqMask k sh w c).testBit l = decide (fld l sh w = c) := by
  unfold eqMask
  cases hc : Nat.blt c (Nat.pow 2 w)
  · change (0 : ℕ).testBit l = _
    have : ¬ c < 2 ^ w := Nat.not_lt.2 (blt_f hc)
    have hf : fld l sh w < 2 ^ w := by rw [fld_eq]; exact Nat.mod_lt _ (by positivity)
    simp only [Nat.zero_testBit, false_eq_decide_iff]
    omega
  · change (eqMaskAux k sh c w).testBit l = _
    have hcw : c < 2 ^ w := blt_t hc
    rw [testBit_eqMaskAux hl, Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · intro h
      apply Nat.eq_of_testBit_eq
      intro j
      rw [testBit_fld]
      by_cases hj : j < w
      · simp only [hj, decide_true, Bool.true_and]; rw [Nat.add_comm]; exact h j hj
      · simp only [hj, decide_false, Bool.false_and]
        exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hcw
          (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
    · rintro rfl j hj
      rw [testBit_fld]; simp [hj, Nat.add_comm]

theorem testBit_orRange {k sh w a l : ℕ} (hl : l < 2 ^ k) (n : ℕ) :
    (orRange k sh w a n).testBit l = decide (∃ j < n, fld l sh w = a + j) := by
  induction n with
  | zero => change (0 : ℕ).testBit l = _; simp
  | succ n ih =>
    change (orRange k sh w a n ||| eqMask k sh w (a + n)).testBit l = _
    rw [Nat.testBit_or, ih, testBit_eqMask hl, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact Or.inl ⟨j, hj, h⟩
      · exact Or.inr h

theorem kmin_eq (a b : ℕ) : kmin a b = min a b := by
  unfold kmin
  cases h : Nat.ble a b
  · change b = _; have := ble_f h; omega
  · change a = _; have := ble_t h; omega

/-- **The mask of a test** contains exactly the positions that pass it. -/
theorem testBit_tmask {k l : ℕ} (hl : l < 2 ^ k) (a : Test) :
    (tmask k a).testBit l = ttest l a := by
  have hf : fld l a.sh a.w < 2 ^ a.w := by rw [fld_eq]; exact Nat.mod_lt _ (by positivity)
  unfold ttest tmask
  rw [cmp_eq]
  rcases ha : a.kind with _ | _ | j
  · change (eqMask k a.sh a.w a.c).testBit l = _
    rw [testBit_eqMask hl]; rfl
  · change (orRange k a.sh a.w a.c (Nat.pow 2 a.w - a.c)).testBit l = _
    rw [testBit_orRange hl]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.pow_eq, decide_eq_decide]
    constructor
    · rintro ⟨j, -, h⟩; omega
    · intro h; exact ⟨fld l a.sh a.w - a.c, by omega, by omega⟩
  · change (orRange k a.sh a.w 0 (kmin (a.c + 1) (Nat.pow 2 a.w))).testBit l = _
    rw [testBit_orRange hl, kmin_eq]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, show j + 1 + 1 ≠ 1 by omega, Nat.zero_add,
      Nat.pow_eq, decide_eq_decide]
    constructor
    · rintro ⟨j, hj, h⟩; omega
    · intro h; exact ⟨_, by omega, rfl⟩

theorem fld_low {k sh w : ℕ} (h : sh + w ≤ k) (x : ℕ) : fld (x % 2 ^ k) sh w = fld x sh w := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_fld, testBit_fld, Nat.testBit_mod_two_pow]
  by_cases hj : j < w
  · have : j + sh < k := by omega
    simp [hj, this]
  · simp [hj]

theorem fld_high {k sh w : ℕ} (h : k ≤ sh) (x : ℕ) : fld (x / 2 ^ k) (sh - k) w = fld x sh w := by
  rw [fld_eq, fld_eq, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' h]

/-- A test reads either the low or the high bits. -/
theorem ttest_split {k : ℕ} {a : Test} (hs : Bool.rec (motive := fun _ => Bool) (isHigh k a) true
    (isLow k a) = true) (x : ℕ) :
    ttest x a = (Bool.rec (motive := fun _ => Bool) true
      (cmp a.kind (fld (x / 2 ^ k) (Nat.sub a.sh k) a.w) a.c) (isHigh k a) &&
      (Bool.rec (motive := fun _ => Bool) true (ttest (x % 2 ^ k) a) (isLow k a))) := by
  cases hlo : isLow k a
  · rw [hlo] at hs
    change isHigh k a = true at hs
    rw [hs]
    have : k ≤ a.sh := ble_t hs
    change ttest x a = (cmp a.kind (fld (x / 2 ^ k) (a.sh - k) a.w) a.c && true)
    rw [Bool.and_true, fld_high this]; rfl
  · have : a.sh + a.w ≤ k := ble_t hlo
    have hhi : isHigh k a = true → a.w = 0 := by
      intro hh; have : k ≤ a.sh := ble_t hh
      omega
    change ttest x a = (Bool.rec (motive := fun _ => Bool) true
      (cmp a.kind (fld (x / 2 ^ k) (a.sh - k) a.w) a.c) (isHigh k a) && ttest (x % 2 ^ k) a)
    have hl : ttest (x % 2 ^ k) a = ttest x a := by
      unfold ttest; rw [fld_low this]
    rw [hl]
    cases hh : isHigh k a
    · rfl
    · change ttest x a = (cmp a.kind (fld (x / 2 ^ k) (a.sh - k) a.w) a.c && ttest x a)
      have hw := hhi hh
      have e : fld (x / 2 ^ k) (a.sh - k) a.w = fld x a.sh a.w := by
        rw [fld_eq, fld_eq, hw]; simp [Nat.mod_one]
      rw [e]
      unfold ttest
      cases cmp a.kind (fld x a.sh a.w) a.c <;> rfl

theorem splitOk_spec {k : ℕ} {ts : List Test} (h : splitOk k ts = true) :
    ∀ a ∈ ts, Bool.rec (motive := fun _ => Bool) (isHigh k a) true (isLow k a) = true := by
  simpa [splitOk, kall_eq] using h

/-- The guard of a transition is the high tests and the mask of the low tests. -/
theorem tall_split {k : ℕ} {ts : List Test} (h : splitOk k ts = true) (x : ℕ) :
    tall x ts = (gH k (x / 2 ^ k) ts && (gL k ts).testBit (x % 2 ^ k)) := by
  have hl : x % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  have hs := splitOk_spec h
  induction ts with
  | nil =>
    change true = (true && (full k).testBit (x % 2 ^ k))
    rw [testBit_full]; simp [hl]
  | cons a ts ih =>
    have ih := ih (by simpa [splitOk, kall_eq] using fun b hb => hs b (List.mem_cons_of_mem _ hb))
      fun b hb => hs b (List.mem_cons_of_mem _ hb)
    have e1 : tall x (a :: ts) = (ttest x a && tall x ts) := by simp [tall, kall_eq]
    have e2 : gH k (x / 2 ^ k) (a :: ts) = (Bool.rec (motive := fun _ => Bool) true
        (cmp a.kind (fld (x / 2 ^ k) (Nat.sub a.sh k) a.w) a.c) (isHigh k a) &&
        gH k (x / 2 ^ k) ts) := by
      simp only [gH, kall_eq, List.all_cons]
    have e3 : gL k (a :: ts) = Bool.rec (motive := fun _ => ℕ) (gL k ts)
        (Nat.land (gL k ts) (tmask k a)) (isLow k a) := rfl
    have hmask : (Bool.rec (motive := fun _ => ℕ) (gL k ts) (Nat.land (gL k ts) (tmask k a))
        (isLow k a)).testBit (x % 2 ^ k) = ((gL k ts).testBit (x % 2 ^ k) &&
          Bool.rec (motive := fun _ => Bool) true (ttest (x % 2 ^ k) a) (isLow k a)) := by
      cases isLow k a
      · exact (Bool.and_true _).symm
      · change (gL k ts &&& tmask k a).testBit _ = _
        rw [Nat.testBit_and, testBit_tmask hl]
    rw [e1, e2, e3, ih, ttest_split (hs a List.mem_cons_self), hmask]
    generalize Bool.rec (motive := fun _ => Bool) true
      (cmp a.kind (fld (x / 2 ^ k) (Nat.sub a.sh k) a.w) a.c) (isHigh k a) = b1
    generalize Bool.rec (motive := fun _ => Bool) true (ttest (x % 2 ^ k) a) (isLow k a) = b2
    generalize gH k (x / 2 ^ k) ts = b3
    generalize (gL k ts).testBit (x % 2 ^ k) = b4
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

theorem testBit_bmaskE {k h l : ℕ} (hl : l < 2 ^ k) :
    ∀ e : BExpr, (bmaskE k h e).testBit l = e.eval (h * 2 ^ k + l).testBit
  | .var i => by
    change (Bool.rec (motive := fun _ => ℕ) (bm k i)
      (Bool.rec (motive := fun _ => ℕ) 0 (full k) (ktest h (Nat.sub i k))) (Nat.ble k i)).testBit l
      = (h * 2 ^ k + l).testBit i
    rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add h hl]
    cases hb : Nat.ble k i
    · have hik : i < k := ble_f hb
      change (bm k i).testBit l = _
      rw [testBit_bm]; simp [hl, hik]
    · have hik : k ≤ i := ble_t hb
      have : ¬ i < k := by omega
      simp only [this, ↓reduceIte]
      rw [ktest_eq]
      change (Bool.rec (motive := fun _ => ℕ) 0 (full k) (h.testBit (i - k))).testBit l = _
      cases h.testBit (i - k)
      · simp
      · change (full k).testBit l = true; rw [testBit_full]; simp [hl]
  | .const b => by
    cases b
    · change (0 : ℕ).testBit l = false; simp
    · change (full k).testBit l = true; rw [testBit_full]; simp [hl]
  | .not e => by
    change (full k ^^^ bmaskE k h e).testBit l = !(e.eval _)
    rw [Nat.testBit_xor, testBit_full, testBit_bmaskE hl e]; simp [hl]
  | .and a b => by
    change (bmaskE k h a &&& bmaskE k h b).testBit l = (a.eval _ && b.eval _)
    rw [Nat.testBit_and, testBit_bmaskE hl a, testBit_bmaskE hl b]
  | .or a b => by
    change (bmaskE k h a ||| bmaskE k h b).testBit l = (a.eval _ || b.eval _)
    rw [Nat.testBit_or, testBit_bmaskE hl a, testBit_bmaskE hl b]
  | .xor a b => by
    change (bmaskE k h a ^^^ bmaskE k h b).testBit l = Bool.xor (a.eval _) (b.eval _)
    rw [Nat.testBit_xor, testBit_bmaskE hl a, testBit_bmaskE hl b]

theorem isTrueE_spec {e : BExpr} (h : isTrueE e = true) : e = .const true := by
  cases e with
  | const b => cases b <;> first | rfl | cases h
  | _ => cases h

/-- The whole guard of a transition is its high tests and its mask. -/
theorem gOk_split {k : ℕ} {e : Tr} (h : splitOk k e.guard = true) (x : ℕ) :
    gOk x e = (gH k (x / 2 ^ k) e.guard && (gLB k (x / 2 ^ k) e).testBit (x % 2 ^ k)) := by
  have hl : x % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  have hx : x = x / 2 ^ k * 2 ^ k + x % 2 ^ k := (Nat.div_add_mod' x _).symm
  rw [gOk_eq, tall_split h x]
  unfold gLB
  cases ht : isTrueE e.bg
  · change _ = (_ && (gL k e.guard &&& bmaskE k (x / 2 ^ k) e.bg).testBit (x % 2 ^ k))
    rw [Nat.testBit_and, testBit_bmaskE hl, ← hx]
    unfold bgOk
    cases gH k (x / 2 ^ k) e.guard <;> cases (gL k e.guard).testBit (x % 2 ^ k) <;> rfl
  · change _ = (_ && (gL k e.guard).testBit (x % 2 ^ k))
    rw [isTrueE_spec ht]
    simp [bgOk, BExpr.eval]

/-- **Firing in a chunk.**  If no position of `S` borrows or carries, the state `x` of the chunk
`h` at a position `l` of `S` fires to the chunk `h + addH - subH`, at the position of `l` in
the shifted bitmap. -/
theorem fire_chunk {k S h l add sub : ℕ} (hb : Nat.ble (hi k sub) (h + hi k add) = true)
    (hr : rangeOk k S (lo k add) (lo k sub) = true) (hl : S.testBit l = true) :
    (h * 2 ^ k + l) + add - sub = (h + hi k add - hi k sub) * 2 ^ k + (l + lo k add - lo k sub) ∧
      l + lo k add - lo k sub < 2 ^ k ∧ lo k sub ≤ l + lo k add ∧
      (shiftBy S (lo k add) (lo k sub)).testBit (l + lo k add - lo k sub) = true ∧
      ∀ X, (unshiftBy X (lo k add) (lo k sub)).testBit l =
        X.testBit (l + lo k add - lo k sub) := by
  rw [lo_eq, lo_eq, hi_eq, hi_eq] at *
  have hb' : sub / 2 ^ k ≤ h + add / 2 ^ k := ble_t hb
  obtain ⟨hr1, hr2⟩ := band_eq.1 hr
  have hr1 := Nat.eq_of_beq_eq_true hr1
  have hr2 := Nat.eq_of_beq_eq_true hr2
  rw [shiftLeft_one] at hr2
  set aL := add % 2 ^ k
  set sL := sub % 2 ^ k
  have hpos : 0 < 2 ^ k := by positivity
  -- the range: `sL - aL ≤ l < 2^k + sL - aL`
  have hlo : sL - aL ≤ l := by
    have h2 := congrArg (fun x => Nat.testBit x l) hr1
    change ((S >>> (sL - aL)) <<< (sL - aL)).testBit l = S.testBit l at h2
    rw [Nat.testBit_shiftLeft, hl] at h2
    by_contra hc
    simp [show ¬ l ≥ sL - aL by omega] at h2
  have hhi : l < 2 ^ k + sL - aL := by
    by_contra hc
    have h2 := congrArg (fun x => Nat.testBit x (l - (2 ^ k + sL - aL))) hr2
    change (S >>> (2 ^ k + sL - aL)).testBit (l - (2 ^ k + sL - aL)) = (0 : ℕ).testBit _ at h2
    rw [Nat.testBit_shiftRight, Nat.add_sub_cancel' (by omega), hl] at h2
    simp at h2
  have haL : aL < 2 ^ k := Nat.mod_lt _ hpos
  have hsL : sL < 2 ^ k := Nat.mod_lt _ hpos
  have hadd : add = add / 2 ^ k * 2 ^ k + aL := by rw [Nat.div_add_mod']
  have hsub : sub = sub / 2 ^ k * 2 ^ k + sL := by rw [Nat.div_add_mod']
  refine ⟨?_, by omega, by omega, ?_, ?_⟩
  · have e1 : (h + add / 2 ^ k - sub / 2 ^ k) * 2 ^ k + sub / 2 ^ k * 2 ^ k =
        (h + add / 2 ^ k) * 2 ^ k := by rw [← Nat.add_mul, Nat.sub_add_cancel hb']
    have e2 : (h + add / 2 ^ k) * 2 ^ k = h * 2 ^ k + add / 2 ^ k * 2 ^ k := Nat.add_mul _ _ _
    conv_lhs => rw [hadd, hsub]
    omega
  · unfold shiftBy
    cases hle : Nat.ble sL aL
    · have : ¬ sL ≤ aL := Nat.not_le.2 (ble_f hle)
      change (S >>> (sL - aL)).testBit _ = true
      rw [Nat.testBit_shiftRight]
      have : sL - aL + (l + aL - sL) = l := by omega
      rw [this, hl]
    · have : sL ≤ aL := ble_t hle
      change (S <<< (aL - sL)).testBit _ = true
      rw [Nat.testBit_shiftLeft]
      have : l + aL - sL - (aL - sL) = l := by omega
      simp [this, hl]; omega
  · intro X
    unfold unshiftBy
    cases hle : Nat.ble sL aL
    · have : ¬ sL ≤ aL := Nat.not_le.2 (ble_f hle)
      change (X <<< (sL - aL)).testBit l = _
      rw [Nat.testBit_shiftLeft]
      have : l - (sL - aL) = l + aL - sL := by omega
      simp [this, hlo]
    · have : sL ≤ aL := ble_t hle
      change (X >>> (aL - sL)).testBit l = _
      rw [Nat.testBit_shiftRight]
      congr 1; omega

end Bits

/-! ### Soundness -/

section Sound

variable {tb : List Tr} {k imask L : ℕ} {dl lv : Bool} {t : BTree (ℕ × ℕ)}

/-- The three parts make the whole check: the kernel can check them separately, each with its
own cache, which bounds the memory by the largest part. -/
theorem check_of_parts {tb : List Tr} {k imask dR dD kD L : ℕ} {dl lv : Bool} {s₀ : ℕ}
    {c : Cert} (hA : checkA tb k dl s₀ c = true) (hR : checkR tb k imask dR c = true)
    (hD : checkD tb k dD kD L lv c = true) : check tb k imask dR dD kD L dl lv s₀ c = true := by
  unfold checkA at hA
  unfold checkR at hR
  unfold checkD at hD
  unfold check
  obtain ⟨h1, hA⟩ := band_eq.1 hA
  obtain ⟨h2, h3⟩ := band_eq.1 hA
  rw [h1, h2, h3, hR, hD]; rfl


theorem kfind_tmap (f : ℕ → ℕ → ℕ) (h : ℕ) :
    ∀ t : BTree (ℕ × ℕ), kfind h (tmap f t) = (kfind h t).map (f h)
  | .leaf => rfl
  | .node l x r => by
    change Bool.rec (motive := fun _ => Option ℕ) (kfind h (tmap f l))
      (Bool.rec (motive := fun _ => Option ℕ) (kfind h (tmap f r)) (some (f x.1 x.2))
        (Nat.beq h x.1)) (Nat.ble x.1 h) =
      (Bool.rec (motive := fun _ => Option ℕ) (kfind h l)
      (Bool.rec (motive := fun _ => Option ℕ) (kfind h r) (some x.2) (Nat.beq h x.1))
        (Nat.ble x.1 h)).map (f h)
    rw [kfind_tmap f h l, kfind_tmap f h r]
    cases Nat.ble x.1 h
    · rfl
    · cases he : Nat.beq h x.1
      · rfl
      · rw [Nat.eq_of_beq_eq_true he]; rfl

theorem look_tmap (f : ℕ → ℕ → ℕ) (h : ℕ) (t : BTree (ℕ × ℕ)) :
    look h (tmap f t) = Option.rec (motive := fun _ => ℕ) 0 (f h) (kfind h t) := by
  unfold look; rw [kfind_tmap]; cases kfind h t <;> rfl

theorem look_of_kfind {h a : ℕ} {D : BTree (ℕ × ℕ)} (hf : kfind h D = some a) : look h D = a := by
  unfold look; rw [hf]

theorem look_bit {h l : ℕ} {D : BTree (ℕ × ℕ)} (hb : (look h D).testBit l = true) :
    ∃ a, kfind h D = some a ∧ a.testBit l = true := by
  unfold look at hb
  cases hf : kfind h D with
  | none => rw [hf] at hb; change (0 : ℕ).testBit l = true at hb; simp at hb
  | some a => rw [hf] at hb; exact ⟨a, rfl, hb⟩

theorem chunk_ok (hall : ∀ y ∈ t.toList, chkChunk tb k t dl y = true) {h a : ℕ}
    (hf : kfind h t = some a) : chkChunk tb k t dl (h, a) = true :=
  hall _ (mem_of_kfind hf)

theorem enAny_spec {h l : ℕ} : ∀ {tb : List Tr}, (enAny k tb h).testBit l = true →
    ∃ j, ∃ hj : j < tb.length, gH k h tb[j].guard = true ∧ (gLB k h tb[j]).testBit l = true
  | [], hb => by change (0 : ℕ).testBit l = true at hb; simp at hb
  | e :: tb, hb => by
    change (Bool.rec (motive := fun _ => ℕ) (enAny k tb h) (Nat.lor (enAny k tb h)
      (gLB k h e)) (gH k h e.guard)).testBit l = true at hb
    have hrest : (enAny k tb h).testBit l = true → ∃ j, ∃ hj : j < (e :: tb).length,
        gH k h (e :: tb)[j].guard = true ∧ (gLB k h (e :: tb)[j]).testBit l = true := by
      intro h'
      obtain ⟨j, hj, h1, h2⟩ := enAny_spec h'
      exact ⟨j + 1, by simpa using hj, h1, h2⟩
    cases hg : gH k h e.guard
    · rw [hg] at hb; exact hrest hb
    · rw [hg] at hb
      change (enAny k tb h ||| gLB k h e).testBit l = true at hb
      rw [Nat.testBit_or, Bool.or_eq_true] at hb
      rcases hb with hb | hb
      · exact hrest hb
      · exact ⟨0, by simp, hg, hb⟩

theorem prog_spec {D : BTree (ℕ × ℕ)} {kD h l : ℕ} : ∀ {tb : List Tr} {i₀ : ℕ},
    (prog k kD D tb h i₀).testBit l = true →
    ∃ j, ∃ hj : j < tb.length, ktest kD (i₀ + j) = true ∧ gH k h tb[j].guard = true ∧
      (gLB k h tb[j]).testBit l = true ∧
      (unshiftBy (look (tgt k h tb[j]) D) (lo k tb[j].add) (lo k tb[j].sub)).testBit l = true
  | [], _, hb => by change (0 : ℕ).testBit l = true at hb; simp at hb
  | e :: tb, i₀, hb => by
    change (Bool.rec (motive := fun _ => ℕ) (prog k kD D tb h (Nat.succ i₀))
      (Nat.lor (prog k kD D tb h (Nat.succ i₀)) (preOf k D h e)) (ktest kD i₀)).testBit l
      = true at hb
    have hrest : (prog k kD D tb h (Nat.succ i₀)).testBit l = true → ∃ j,
        ∃ hj : j < (e :: tb).length, ktest kD (i₀ + j) = true ∧ gH k h (e :: tb)[j].guard = true ∧
        (gLB k h (e :: tb)[j]).testBit l = true ∧
        (unshiftBy (look (tgt k h (e :: tb)[j]) D) (lo k (e :: tb)[j].add)
          (lo k (e :: tb)[j].sub)).testBit l = true := by
      intro h'
      obtain ⟨j, hj, h0, h1, h2, h3⟩ := prog_spec h'
      exact ⟨j + 1, by simpa using hj, by rw [show i₀ + (j + 1) = Nat.succ i₀ + j by omega]; exact h0, h1, h2, h3⟩
    cases hk : ktest kD i₀
    · rw [hk] at hb; exact hrest hb
    rw [hk] at hb
    change (prog k kD D tb h (Nat.succ i₀) ||| preOf k D h e).testBit l = true at hb
    rw [Nat.testBit_or, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact hrest hb
    · unfold preOf at hb
      cases hg : gH k h e.guard
      · rw [hg] at hb; change (0 : ℕ).testBit l = true at hb; simp at hb
      rw [hg] at hb
      cases hb' : Nat.ble (hi k e.sub) (Nat.add h (hi k e.add))
      · rw [hb'] at hb; change (0 : ℕ).testBit l = true at hb; simp at hb
      rw [hb'] at hb
      change (gLB k h e &&& _).testBit l = true at hb
      rw [Nat.testBit_and, Bool.and_eq_true] at hb
      exact ⟨0, by simp, by simpa using hk, hg, hb.1, hb.2⟩

theorem decEn_spec {dD h l : ℕ} : ∀ {tb : List Tr} {i₀ : ℕ},
    (decEn k dD tb h i₀).testBit l = true →
    ∃ j, ∃ hj : j < tb.length, ktest dD (i₀ + j) = true ∧ gH k h tb[j].guard = true ∧
      (gLB k h tb[j]).testBit l = true
  | [], _, hb => by change (0 : ℕ).testBit l = true at hb; simp at hb
  | e :: tb, i₀, hb => by
    change (Bool.rec (motive := fun _ => ℕ) (decEn k dD tb h (Nat.succ i₀))
      (Bool.rec (motive := fun _ => ℕ) (decEn k dD tb h (Nat.succ i₀))
        (Nat.lor (decEn k dD tb h (Nat.succ i₀)) (gLB k h e)) (gH k h e.guard))
      (ktest dD i₀)).testBit l = true at hb
    have hrest : (decEn k dD tb h (Nat.succ i₀)).testBit l = true → ∃ j,
        ∃ hj : j < (e :: tb).length, ktest dD (i₀ + j) = true ∧ gH k h (e :: tb)[j].guard = true ∧
        (gLB k h (e :: tb)[j]).testBit l = true := by
      intro h'
      obtain ⟨j, hj, h0, h1, h2⟩ := decEn_spec h'
      exact ⟨j + 1, by simpa using hj, by rw [show i₀ + (j + 1) = Nat.succ i₀ + j by omega]; exact h0, h1, h2⟩
    cases hk : ktest dD i₀
    · rw [hk] at hb; exact hrest hb
    rw [hk] at hb
    cases hg : gH k h e.guard
    · rw [hg] at hb; exact hrest hb
    rw [hg] at hb
    change (decEn k dD tb h (Nat.succ i₀) ||| gLB k h e).testBit l = true at hb
    rw [Nat.testBit_or, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact hrest hb
    · exact ⟨0, by simp, by simpa using hk, hg, hb⟩

theorem bad_of {dR : ℕ} {R : BTree (ℕ × ℕ)} {h l : ℕ} : ∀ {tb : List Tr} {i₀ j : ℕ}
    (hj : j < tb.length), ktest imask (i₀ + j) = true → ktest dR (i₀ + j) = false →
      (badOf k t R h tb[j]).testBit l = true → (bad k imask dR t R tb h i₀).testBit l = true
  | [], _, _, hj, _, _, _ => by simp at hj
  | e :: tb, i₀, j, hj, hi, hd, hb => by
    change (Bool.rec (motive := fun _ => ℕ) (bad k imask dR t R tb h (Nat.succ i₀))
      (Bool.rec (motive := fun _ => ℕ) (Nat.lor (bad k imask dR t R tb h (Nat.succ i₀))
        (badOf k t R h e)) (bad k imask dR t R tb h (Nat.succ i₀)) (ktest dR i₀))
      (ktest imask i₀)).testBit l = true
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hi hd
      rw [hi, hd]
      change (bad k imask dR t R tb h (Nat.succ i₀) ||| badOf k t R h e).testBit l = true
      rw [Nat.testBit_or, Bool.or_eq_true]
      exact Or.inr hb
    | succ j =>
      have := bad_of (tb := tb) (i₀ := Nat.succ i₀) (j := j) (by simpa using hj)
        (by rw [Nat.succ_add, ← Nat.add_succ]; exact hi)
        (by rw [Nat.succ_add, ← Nat.add_succ]; exact hd) hb
      cases ktest imask i₀
      · exact this
      · cases ktest dR i₀
        · change (bad k imask dR t R tb h (Nat.succ i₀) ||| badOf k t R h e).testBit l = true
          rw [Nat.testBit_or, this]; rfl
        · exact this

theorem hubBits_spec {h l : ℕ} : ∀ {hubs : List (ℕ × List (List ℕ))},
    (hubBits k h hubs).testBit l = true → ∃ hb ∈ hubs, hb.1 / 2 ^ k = h ∧ hb.1 % 2 ^ k = l
  | [], hb => by change (0 : ℕ).testBit l = true at hb; simp at hb
  | x :: hubs, hb => by
    change (Bool.rec (motive := fun _ => ℕ) (hubBits k h hubs)
      (Nat.lor (hubBits k h hubs) (Nat.shiftLeft 1 (lo k x.1))) (Nat.beq (hi k x.1) h)).testBit l
      = true at hb
    have hrest : (hubBits k h hubs).testBit l = true →
        ∃ hb ∈ x :: hubs, hb.1 / 2 ^ k = h ∧ hb.1 % 2 ^ k = l := by
      intro h'
      obtain ⟨hb, hm, h1, h2⟩ := hubBits_spec h'
      exact ⟨hb, List.mem_cons_of_mem _ hm, h1, h2⟩
    cases he : Nat.beq (hi k x.1) h
    · rw [he] at hb; exact hrest hb
    · rw [he] at hb
      change (hubBits k h hubs ||| Nat.shiftLeft 1 (lo k x.1)).testBit l = true at hb
      rw [Nat.testBit_or, Bool.or_eq_true, shiftLeft_one, Nat.testBit_two_pow] at hb
      rcases hb with hb | hb
      · exact hrest hb
      · refine ⟨x, List.mem_cons_self, ?_, ?_⟩
        · rw [← hi_eq]; exact Nat.eq_of_beq_eq_true he
        · rw [← lo_eq]; simpa using hb

/-- **One step from a state of the set.** -/
theorem step_spec (hs : ∀ e ∈ tb, splitOk k e.guard = true ∧ splitOk k e.ok = true)
    (hall : ∀ y ∈ t.toList, chkChunk tb k t dl y = true) {x a : ℕ}
    (hf : kfind (x / 2 ^ k) t = some a) (hx : a.testBit (x % 2 ^ k) = true)
    {i y : ℕ} {b : Bool} (hm : (i, y, b) ∈ asucc tb x) :
    ∃ hil : i < tb.length, b = true ∧ (look (y / 2 ^ k) t).testBit (y % 2 ^ k) = true ∧
      y / 2 ^ k = tgt k (x / 2 ^ k) tb[i] ∧
      gH k (x / 2 ^ k) tb[i].guard = true ∧ (gLB k (x / 2 ^ k) tb[i]).testBit (x % 2 ^ k) = true ∧
      Nat.ble (hi k tb[i].sub) (Nat.add (x / 2 ^ k) (hi k tb[i].add)) = true ∧
      ∀ X, (unshiftBy X (lo k tb[i].add) (lo k tb[i].sub)).testBit (x % 2 ^ k) =
        X.testBit (y % 2 ^ k) := by
  obtain ⟨hil, hg, rfl, rfl⟩ := mem_asucc.1 hm
  refine ⟨hil, ?_⟩
  set e := tb[i]
  have hse := hs e (List.getElem_mem hil)
  set h := x / 2 ^ k
  set l := x % 2 ^ k
  have hc := chunk_ok hall hf
  unfold chkChunk at hc
  obtain ⟨-, hc⟩ := band_eq.1 hc
  simp only [kall_eq, List.all_eq_true] at hc
  have h1 := hc e (List.getElem_mem hil)
  rw [gOk_split hse.1] at hg
  obtain ⟨hgH, hgL⟩ := Bool.and_eq_true_iff.1 hg
  unfold chkOne at h1
  rw [hgH] at h1
  have hS : (Nat.land a (gLB k h e)).testBit l = true := by
    change (a &&& gLB k h e).testBit l = true
    rw [Nat.testBit_and, hx, hgL]; rfl
  have hS0 : Nat.beq (Nat.land a (gLB k h e)) 0 = false := by
    cases h0 : Nat.beq (Nat.land a (gLB k h e)) 0
    · rfl
    · rw [Nat.eq_of_beq_eq_true h0] at hS; simp at hS
  rw [hS0] at h1
  change chkS k t h e (Nat.land a (gLB k h e)) = true at h1
  unfold chkS at h1
  obtain ⟨hok1, h1⟩ := band_eq.1 h1
  obtain ⟨hok2, h1⟩ := band_eq.1 h1
  obtain ⟨hble, h1⟩ := band_eq.1 h1
  obtain ⟨hrange, hin⟩ := band_eq.1 h1
  obtain ⟨hy, hylt, -, hJ, hun⟩ := fire_chunk hble hrange hS
  have hxe : x = h * 2 ^ k + l := (Nat.div_add_mod' x (2 ^ k)).symm
  have hpos : 0 < 2 ^ k := by positivity
  set y := x + e.add - e.sub with hydef
  have hy' : y = (h + hi k e.add - hi k e.sub) * 2 ^ k + (l + lo k e.add - lo k e.sub) := by
    rw [hydef, hxe]; exact hy
  have hyd : y / 2 ^ k = h + hi k e.add - hi k e.sub := by
    rw [hy', Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hylt, Nat.zero_add]
  have hym : y % 2 ^ k = l + lo k e.add - lo k e.sub := by
    rw [hy', Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hylt]
  refine ⟨?_, ?_, hyd, hgH, hgL, hble, fun X => by rw [hun X, hym]⟩
  · rw [tall_split hse.2, hok1, Bool.true_and]
    exact sub_spec hok2 hS
  · rw [hyd, hym]; exact sub_spec hin hJ

/-- The set, as a predicate on packed states. -/
def InSet (k : ℕ) (t : BTree (ℕ × ℕ)) (x : ℕ) : Prop :=
  ∃ a, kfind (x / 2 ^ k) t = some a ∧ a.testBit (x % 2 ^ k) = true

theorem inSet_of_look {x : ℕ} (h : (look (x / 2 ^ k) t).testBit (x % 2 ^ k) = true) :
    InSet k t x := look_bit h

/-- **Soundness of the bitmap checker.**  `potR` is non-increasing along internal steps and
decreasing along those of `dR`; `potD` is decreasing along the steps of `dD` and
non-increasing along those of `kD`. -/
theorem of_check {σ ι : Type*} {A : LTS σ ι} {Good : σ → Prop} {enc : σ → ℕ} {lab : ι → ℕ}
    (hE : Encodes A Good enc lab (asucc tb)) (hinj : Function.Injective lab) {M₀ : σ}
    {dR dD kD : ℕ} (potR potD : σ → ℕ)
    (hR : ∀ M l M', A.step M l M' → imask.testBit (lab l) = true →
      potR M' ≤ potR M ∧ (dR.testBit (lab l) = true → potR M' < potR M))
    (hD : ∀ M l M', A.step M l M' → (dD.testBit (lab l) = true → potD M' < potD M) ∧
      (kD.testBit (lab l) = true → potD M' ≤ potD M))
    {c : Cert} (hg₀ : Good M₀) (h : check tb k imask dR dD kD L dl lv (enc M₀) c = true) :
    (dl = true → A.DeadlockFree M₀) ∧
      A.LivelockFree (fun l => imask.testBit (lab l) = true) M₀ ∧
      (lv = true → ∀ l, lab l < L → A.LiveLabel M₀ l) ∧
      ∀ M, A.Reachable M₀ M → Good M := by
  unfold check at h
  obtain ⟨hsplit, h⟩ := band_eq.1 h
  obtain ⟨h₀, h⟩ := band_eq.1 h
  obtain ⟨hall, h⟩ := band_eq.1 h
  obtain ⟨hrk, hlv⟩ := band_eq.1 h
  have hs : ∀ e ∈ tb, splitOk k e.guard = true ∧ splitOk k e.ok = true := by
    simp only [kall_eq, List.all_eq_true] at hsplit
    exact fun e he => band_eq.1 (hsplit e he)
  rw [ktall_iff] at hall hrk
  set t := c.1
  let Inv : σ → Prop := fun M => Good M ∧ InSet k t (enc M)
  have hinv₀ : Inv M₀ := ⟨hg₀, inSet_of_look (by rw [← hi_eq, ← lo_eq, ← ktest_eq]; exact h₀)⟩
  have hstep : ∀ M l M', Inv M → A.step M l M' → Inv M' := by
    rintro M l M' ⟨hg, a, hf, hx⟩ hst
    obtain ⟨b, hm, hb⟩ := hE.complete M l M' hg hst
    obtain ⟨_, hb', hy, -⟩ := step_spec hs hall hf hx hm
    exact ⟨hb hb', inSet_of_look hy⟩
  have hreach : ∀ M, A.Reachable M₀ M → Inv M := fun M hM => hM.invariant hinv₀ hstep
  -- every state of the set is in the last round
  have hcov : ∀ {D : BTree (ℕ × ℕ)}, (∀ x ∈ t.toList, sub x.2 (look x.1 D) = true) →
      ∀ M, Inv M → (look (enc M / 2 ^ k) D).testBit (enc M % 2 ^ k) = true := by
    rintro D hD M ⟨-, a, hf, hx⟩
    exact sub_spec (hD _ (mem_of_kfind hf)) hx
  refine ⟨fun hdl => ?_, ?_, fun hlv' => ?_, fun M hM => (hreach M hM).1⟩
  · -- deadlock freedom
    refine LTS.DeadlockFree.of_invariant Inv hinv₀ hstep fun M ⟨hg, a, hf, hx⟩ => ?_
    have hc := chunk_ok hall hf
    unfold chkChunk at hc
    obtain ⟨hd, -⟩ := band_eq.1 hc
    rw [hdl] at hd
    obtain ⟨j, hj, h1, h2⟩ := enAny_spec (sub_spec hd hx)
    have hgd : gOk (enc M) tb[j] = true := by
      rw [gOk_split (hs _ (List.getElem_mem hj)).1, h1, h2]; rfl
    have hm : (j, enc M + tb[j].add - tb[j].sub, tall (enc M) tb[j].ok) ∈ asucc tb (enc M) :=
      mem_asucc.2 ⟨hj, hgd, rfl, rfl⟩
    obtain ⟨_, hok, -⟩ := step_spec hs hall hf hx hm
    obtain ⟨l, M', -, hst, -⟩ := hE.sound M hg _ _ (hok ▸ hm)
    exact ⟨l, M', hst⟩
  · -- livelock freedom: lexicographically, the rank potential and the rank rounds
    set rI := rankIter k imask dR t tb
    have key : ∀ p n M, potR M = p → Inv M →
        (look (enc M / 2 ^ k) (rI n)).testBit (enc M % 2 ^ k) = true →
        Acc (A.IRel fun l => imask.testBit (lab l) = true) M := by
      intro p
      induction p using Nat.strong_induction_on with
      | _ p ihp =>
      intro n
      induction n with
      | zero =>
        intro M _ _ hb
        change (look _ (tmap (fun _ _ => 0) t)).testBit _ = true at hb
        rw [look_tmap] at hb
        generalize kfind (enc M / 2 ^ k) t = o at hb
        cases o <;> (change (0 : ℕ).testBit _ = true at hb; simp at hb)
      | succ n ih =>
        intro M hp ⟨hg, a, hf, hx⟩ hb
        change (look _ (tmap (fun h a => Nat.lor (look h (rI n))
          (Nat.xor a (Nat.land a (bad k imask dR t (rI n) tb h 0)))) t)).testBit _ = true at hb
        rw [look_tmap, hf] at hb
        change (look _ (rI n) ||| (a ^^^ (a &&& _))).testBit _ = true at hb
        rw [Nat.testBit_or, Bool.or_eq_true] at hb
        rcases hb with hb | hb
        · exact ih M hp ⟨hg, a, hf, hx⟩ hb
        · rw [Nat.testBit_xor, Nat.testBit_and, hx] at hb
          have hnb : (bad k imask dR t (rI n) tb (enc M / 2 ^ k) 0).testBit
              (enc M % 2 ^ k) = false := by
            cases hh : (bad k imask dR t (rI n) tb (enc M / 2 ^ k) 0).testBit (enc M % 2 ^ k)
            · rfl
            · rw [hh] at hb; cases hb
          refine Acc.intro M fun M' ⟨l, hl, hst⟩ => ?_
          obtain ⟨b, hm, hbg⟩ := hE.complete M l M' hg hst
          obtain ⟨hil, hok, hy, hyd, hgH, hgL, hble, hun⟩ := step_spec hs hall hf hx hm
          have hg' := hbg hok
          have hinv' : Inv M' := ⟨hg', inSet_of_look hy⟩
          obtain ⟨hle, hlt⟩ := hR M l M' hst hl
          -- a strict decrease of the potential
          have hdec : potR M' < potR M → Acc (A.IRel fun l => imask.testBit (lab l) = true) M' :=
            fun h' => ihp _ (hp ▸ h') c.2.2.1 M' rfl hinv' (hcov hrk M' hinv')
          cases hd : dR.testBit (lab l)
          · rcases Nat.lt_or_eq_of_le hle with h' | h'
            · exact hdec h'
            by_contra hacc
            have hin : (look (enc M' / 2 ^ k) (rI n)).testBit (enc M' % 2 ^ k) = false := by
              cases hh : (look (enc M' / 2 ^ k) (rI n)).testBit (enc M' % 2 ^ k)
              · rfl
              · exact absurd (ih M' (h'.trans hp) hinv' hh) hacc
            have hbad := bad_of (t := t) (R := rI n) (tb := tb) (dR := dR) (i₀ := 0)
              (j := lab l) hil (by rw [Nat.zero_add, ktest_eq]; exact hl)
              (by rw [Nat.zero_add, ktest_eq]; exact hd) (h := enc M / 2 ^ k)
              (l := enc M % 2 ^ k) (by
                unfold badOf
                rw [hgH, hble]
                change (gLB k _ tb[lab l] &&& _).testBit _ = true
                rw [Nat.testBit_and, hgL, Bool.true_and, hun, ← hyd]
                change ((look _ t) ^^^ ((look _ t) &&& (look _ (rI n)))).testBit _ = true
                rw [Nat.testBit_xor, Nat.testBit_and, hy, hin]
                rfl)
            rw [hnb] at hbad; cases hbad
          · exact hdec (hlt hd)
    exact LTS.livelockFree_iff_acc.2 fun M hM =>
      key _ c.2.2.1 M rfl (hreach M hM) (hcov hrk M (hreach M hM))
  · -- liveness: reach a hub, then follow its trace
    rw [hlv'] at hlv
    obtain ⟨hdist, hhubs⟩ := band_eq.1 hlv
    rw [ktall_iff] at hdist
    have hhubs : ∀ x ∈ c.2.1, Nat.beq x.2.length L = true ∧
        chkTraces (asucc tb) x.1 x.2 0 = true := by
      simp only [kall_eq, List.all_eq_true] at hhubs
      exact fun x hx => band_eq.1 (hhubs x hx)
    set dI := distIter k dD kD t tb c.2.1
    -- one step by a transition of the table
    have onestep : ∀ M a j (hj : j < tb.length), Good M → kfind (enc M / 2 ^ k) t = some a →
        a.testBit (enc M % 2 ^ k) = true → gH k (enc M / 2 ^ k) tb[j].guard = true →
        (gLB k (enc M / 2 ^ k) tb[j]).testBit (enc M % 2 ^ k) = true →
        ∃ l M', lab l = j ∧ A.step M l M' ∧ Inv M' ∧
          enc M' / 2 ^ k = tgt k (enc M / 2 ^ k) tb[j] ∧
          ∀ X, (unshiftBy X (lo k tb[j].add) (lo k tb[j].sub)).testBit (enc M % 2 ^ k) =
            X.testBit (enc M' % 2 ^ k) := by
      intro M a j hj hg hf hx h1 h2
      have hgd : gOk (enc M) tb[j] = true := by
        rw [gOk_split (hs _ (List.getElem_mem hj)).1, h1, h2]; rfl
      have hm : (j, enc M + tb[j].add - tb[j].sub, tall (enc M) tb[j].ok) ∈ asucc tb (enc M) :=
        mem_asucc.2 ⟨hj, hgd, rfl, rfl⟩
      obtain ⟨_, hok, hy, hyd, -, -, -, hun⟩ := step_spec hs hall hf hx hm
      obtain ⟨l', M', hl', hst, henc, hg'⟩ := hE.sound M hg _ _ (hok ▸ hm)
      exact ⟨l', M', hl', hst, ⟨hg', inSet_of_look (by rw [henc]; exact hy)⟩,
        by rw [henc]; exact hyd, fun X => by rw [hun, henc]⟩
    have key : ∀ p n M, potD M = p → Inv M →
        (look (enc M / 2 ^ k) (dI n)).testBit (enc M % 2 ^ k) = true →
        ∃ hb ∈ c.2.1, ∃ M', A.Reachable M M' ∧ Good M' ∧ enc M' = hb.1 := by
      intro p
      induction p using Nat.strong_induction_on with
      | _ p ihp =>
      intro n
      induction n with
      | zero =>
        intro M hp ⟨hg, a, hf, hx⟩ hb
        change (look _ (tmap (fun h a => Nat.land a (Nat.lor (hubBits k h c.2.1)
          (decEn k dD tb h 0))) t)).testBit _ = true at hb
        rw [look_tmap, hf] at hb
        change (a &&& (hubBits k _ c.2.1 ||| decEn k dD tb _ 0)).testBit _ = true at hb
        rw [Nat.testBit_and, Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true] at hb
        rcases hb.2 with hb | hb
        · obtain ⟨hb', hmem, h1, h2⟩ := hubBits_spec hb
          refine ⟨hb', hmem, M, LTS.Reachable.refl _, hg, ?_⟩
          rw [← Nat.div_add_mod' hb'.1 (2 ^ k), ← Nat.div_add_mod' (enc M) (2 ^ k), h1, h2]
        · -- a transition decreasing the potential
          obtain ⟨j, hj, hk, h1, h2⟩ := decEn_spec hb
          obtain ⟨l, M', hl, hst, hinv', -, -⟩ := onestep M a j hj hg hf hx h1 h2
          have hlt := (hD M l M' hst).1 (by rw [hl, ← ktest_eq]; simpa using hk)
          obtain ⟨hb', hmem, M'', hr, hg'', he⟩ :=
            ihp _ (hp ▸ hlt) c.2.2.2 M' rfl hinv' (hcov hdist M' hinv')
          exact ⟨hb', hmem, M'', LTS.Reachable.head ⟨l, hst⟩ hr, hg'', he⟩
      | succ n ih =>
        intro M hp ⟨hg, a, hf, hx⟩ hb
        change (look _ (tmap (fun h a => Nat.lor (look h (dI n))
          (Nat.land a (prog k kD (dI n) tb h 0))) t)).testBit _ = true at hb
        rw [look_tmap, hf] at hb
        change (look _ (dI n) ||| (a &&& _)).testBit _ = true at hb
        rw [Nat.testBit_or, Bool.or_eq_true] at hb
        rcases hb with hb | hb
        · exact ih M hp ⟨hg, a, hf, hx⟩ hb
        · rw [Nat.testBit_and, Bool.and_eq_true] at hb
          obtain ⟨j, hj, hk, h1, h2, h3⟩ := prog_spec hb.2
          obtain ⟨l, M', hl, hst, hinv', h5, hX⟩ := onestep M a j hj hg hf hx h1 h2
          have hle := (hD M l M' hst).2 (by rw [hl, ← ktest_eq]; simpa using hk)
          rw [hX] at h3
          rcases Nat.lt_or_eq_of_le hle with h' | h'
          · obtain ⟨hb', hmem, M'', hr, hg'', he⟩ :=
              ihp _ (hp ▸ h') c.2.2.2 M' rfl hinv' (hcov hdist M' hinv')
            exact ⟨hb', hmem, M'', LTS.Reachable.head ⟨l, hst⟩ hr, hg'', he⟩
          · obtain ⟨hb', hmem, M'', hr, hg'', he⟩ :=
              ih M' (h'.trans hp) hinv' (by rw [h5]; exact h3)
            exact ⟨hb', hmem, M'', LTS.Reachable.head ⟨l, hst⟩ hr, hg'', he⟩
    intro l hl M hM
    obtain ⟨hb, hmem, M', hr, hg', he⟩ :=
      key _ c.2.2.2 M rfl (hreach M hM) (hcov hdist M (hreach M hM))
    obtain ⟨hlen, htr⟩ := hhubs hb hmem
    have := chkTraces_spec htr (lab l) (by rw [Nat.eq_of_beq_eq_true hlen]; exact hl)
    rw [Nat.zero_add, ← he] at this
    obtain ⟨M'', hr', hen⟩ := follow_spec hE hinj hg' this
    exact ⟨M'', hr.trans hr', hen⟩

end Sound
end Bitmap

end AsyncLean
