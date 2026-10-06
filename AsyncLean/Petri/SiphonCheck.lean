/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.FreeChoice
import Mathlib.Data.Nat.Bitwise

/-!
# Checking the siphon–trap property without enumerating subsets

Commoner's siphon–trap property ("every non-empty siphon contains an initially marked trap")
quantifies over all sets of places.  Deciding it by enumerating subsets is hopeless beyond a
dozen places.  Here it is decided by a *branching certificate* instead, checked by the
kernel on bit masks (`SiphonCheck.siphonTrap_of_check`).

A node of the certificate is a *region*: the siphons `S` with `I ⊆ S ⊆ X`.  A node is

* `empty` — the region contains no non-empty siphon.  Every siphon inside `X` is inside the
  greatest siphon inside `X`, computed by repeatedly removing the places with an input
  transition that takes nothing from `X`; the check is that `I` is not inside it, or that it
  is empty;
* `trap Q` — `Q ⊆ I` is a trap marked initially, so every siphon of the region contains it;
* `split p l r` — the siphons containing `p` (region `l`) and those avoiding `p` (region `r`).

The root is `I = ∅`, `X = all places`.  The certificate is found by an untrusted search
(`SiphonCheck.search`), which also produces a counterexample siphon when the property fails.
The size of the certificate depends on the structure of the net and is usually far smaller
than the number of subsets.

The same file checks free choice on bit masks (`SiphonCheck.freeChoice_of_checkFC`).
-/

namespace AsyncLean

namespace SiphonCheck

/-! ### Bit masks -/

/-- The bit mask of the numbers `p < m` satisfying `P`. -/
def ofPred (m : ℕ) (P : ℕ → Bool) : ℕ :=
  (List.range m).foldl (fun acc p => if P p then acc ||| 2 ^ p else acc) 0

theorem testBit_foldl (P : ℕ → Bool) (l : List ℕ) (a q : ℕ) :
    Nat.testBit (l.foldl (fun acc p => if P p then acc ||| 2 ^ p else acc) a) q =
      (Nat.testBit a q || l.any fun p => P p && p == q) := by
  induction l generalizing a with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldl_cons, List.any_cons]
    split_ifs with hP
    · rw [ih, Nat.testBit_lor, Nat.testBit_two_pow]
      by_cases h : p = q
      · subst h; simp [hP]
      · have h' : (p == q) = false := by simpa using h
        simp [h', h]
    · rw [ih]; simp [hP]

@[simp] theorem testBit_ofPred (m : ℕ) (P : ℕ → Bool) (q : ℕ) :
    (ofPred m P).testBit q = (decide (q < m) && P q) := by
  rw [ofPred, testBit_foldl]
  simp only [Nat.zero_testBit, Bool.false_or]
  by_cases hq : q < m
  · simp only [hq, decide_true, Bool.true_and]
    cases hP : P q
    · simp only [List.any_eq_false, List.mem_range, Bool.and_eq_true, beq_iff_eq, not_and]
      rintro x - hx rfl; simp_all
    · simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
      exact ⟨q, hq, hP, rfl⟩
  · simp only [hq, decide_false, Bool.false_and, List.any_eq_false, List.mem_range,
      Bool.and_eq_true, beq_iff_eq, not_and]
    rintro x hx - rfl; exact hq hx

theorem land_ne_zero_iff {a b : ℕ} : a &&& b ≠ 0 ↔ ∃ i, a.testBit i ∧ b.testBit i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_land, Bool.and_eq_true] at hi
    exact ⟨i, hi⟩
  · rintro ⟨i, ha, hb⟩ h
    have := Nat.testBit_land a b i
    rw [h, Nat.zero_testBit, ha, hb] at this
    exact Bool.false_ne_true this

/-- `X` without the elements of `Y`. -/
def diff (X Y : ℕ) : ℕ := X ^^^ (X &&& Y)

@[simp] theorem testBit_diff (X Y q : ℕ) :
    (diff X Y).testBit q = (X.testBit q && !Y.testBit q) := by
  simp only [diff, Nat.testBit_xor, Nat.testBit_land]
  cases X.testBit q <;> cases Y.testBit q <;> rfl

/-- The union of `f e` over the entries `e` satisfying `c`. -/
def unionIf (ts : List (ℕ × ℕ)) (c : ℕ × ℕ → Bool) (f : ℕ × ℕ → ℕ) : ℕ :=
  ts.foldl (fun acc e => if c e then acc ||| f e else acc) 0

theorem testBit_foldl_unionIf (c : ℕ × ℕ → Bool) (f : ℕ × ℕ → ℕ) (ts : List (ℕ × ℕ))
    (a q : ℕ) :
    (ts.foldl (fun acc e => if c e then acc ||| f e else acc) a).testBit q =
      (a.testBit q || ts.any fun e => c e && (f e).testBit q) := by
  induction ts generalizing a with
  | nil => simp
  | cons e ts ih =>
    simp only [List.foldl_cons, List.any_cons]
    split_ifs with hc
    · rw [ih, Nat.testBit_lor]; simp [hc, Bool.or_assoc]
    · rw [ih]; simp [hc]

@[simp] theorem testBit_unionIf (ts : List (ℕ × ℕ)) (c : ℕ × ℕ → Bool) (f : ℕ × ℕ → ℕ)
    (q : ℕ) : (unionIf ts c f).testBit q = ts.any fun e => c e && (f e).testBit q := by
  simp [unionIf, testBit_foldl_unionIf]

/-! ### The checker -/

/-- One shrinking step towards the greatest siphon inside `X`: remove the output places of the
transitions that take nothing from `X`.  `ts` lists, per transition, the masks of its input
and output places. -/
def shrinkS (ts : List (ℕ × ℕ)) (X : ℕ) : ℕ :=
  diff X (unionIf ts (fun e => e.1 &&& X == 0) Prod.snd)

/-- The greatest siphon inside `X` (after at most `k` shrinking steps). -/
def maxSiphon (ts : List (ℕ × ℕ)) : ℕ → ℕ → ℕ
  | 0, X => X
  | k + 1, X => let Y := shrinkS ts X; if Y == X then X else maxSiphon ts k Y

/-- No non-empty siphon `S` with `I ⊆ S ⊆ X`: shrinking `X` towards its greatest siphon
eventually drops a place of `I`, or empties it. -/
def emptyRegionAux (ts : List (ℕ × ℕ)) (I : ℕ) : ℕ → ℕ → Bool
  | k, X =>
    if I &&& X != I || X == 0 then true
    else match k with
      | 0 => false
      | k + 1 => let Y := shrinkS ts X; if Y == X then false else emptyRegionAux ts I k Y

/-- No non-empty siphon `S` with `I ⊆ S ⊆ X`. -/
def emptyRegion (m : ℕ) (ts : List (ℕ × ℕ)) (I X : ℕ) : Bool := emptyRegionAux ts I m X

/-- `q` is (the mask of) a trap. -/
def isTrapMask (ts : List (ℕ × ℕ)) (q : ℕ) : Bool :=
  ts.all fun e => e.1 &&& q == 0 || e.2 &&& q != 0

/-- Every siphon `S` with `I ⊆ S ⊆ X` is a trap and is initially marked: no such siphon
avoids the marked places, and for every transition `t` and input place `p ∈ X` of `t`, no such
siphon contains `p` but avoids the output places of `t`. -/
def trapsRegion (m : ℕ) (ts : List (ℕ × ℕ)) (m0 I X : ℕ) : Bool :=
  emptyRegion m ts I (diff X m0) &&
    ts.all fun e => (List.range m).all fun p =>
      !(e.1.testBit p && X.testBit p) || emptyRegion m ts (I ||| 2 ^ p) (diff X e.2)

/-- A certificate for the siphon–trap property. -/
inductive Tree where
  /-- No non-empty siphon in the region. -/
  | empty
  /-- An initially marked trap inside the included places. -/
  | trap (q : ℕ)
  /-- Every siphon in the region is an initially marked trap. -/
  | traps
  /-- Split on whether place `p` is in the siphon. -/
  | split (p : ℕ) (inc exc : Tree)
  deriving Repr, Inhabited, Lean.ToExpr

/-- Check a certificate for the region `I ⊆ S ⊆ X`. -/
def check (m : ℕ) (ts : List (ℕ × ℕ)) (m0 : ℕ) : Tree → ℕ → ℕ → Bool
  | .empty, I, X => emptyRegion m ts I X
  | .trap q, I, _ => q &&& I == q && isTrapMask ts q && q &&& m0 != 0
  | .traps, I, X => trapsRegion m ts m0 I X
  | .split p l r, I, X =>
    check m ts m0 l (I ||| 2 ^ p) X && check m ts m0 r I (diff X (2 ^ p))

/-- Free choice on masks: two transitions whose input masks meet have the same input mask. -/
def checkFC (ts : List (ℕ × ℕ)) : Bool :=
  ts.all fun a => ts.all fun b => a.1 &&& b.1 == 0 || a.1 == b.1

/-! ### Soundness -/

variable {m n : ℕ} (N : Net (Fin m) (Fin n))

/-- The mask of the places `p` with `f p`. -/
def finMask (f : Fin m → Bool) : ℕ := ofPred m fun p => if h : p < m then f ⟨p, h⟩ else false

theorem testBit_finMask (f : Fin m → Bool) (q : ℕ) :
    (finMask f).testBit q = true ↔ ∃ h : q < m, f ⟨q, h⟩ = true := by
  simp only [finMask, testBit_ofPred, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hf⟩; simp only [h, ↓reduceDIte] at hf; exact ⟨h, hf⟩
  · rintro ⟨h, hf⟩; exact ⟨h, by simp only [h, ↓reduceDIte]; exact hf⟩

theorem testBit_finMask_fin (f : Fin m → Bool) (p : Fin m) :
    (finMask f).testBit p = f p := by
  simp [finMask, p.isLt]

/-- Input and output masks of every transition. -/
def table : List (ℕ × ℕ) :=
  (List.finRange n).map fun t =>
    (finMask fun p => decide (0 < N.pre t p), finMask fun p => decide (0 < N.post t p))

/-- The mask of the initially marked places. -/
def markMask (M : Marking (Fin m)) : ℕ := finMask fun p => decide (0 < M p)

variable {N}

theorem mem_table (t : Fin n) :
    (finMask (fun p => decide (0 < N.pre t p)), finMask fun p => decide (0 < N.post t p)) ∈
      table N :=
  List.mem_map.2 ⟨t, List.mem_finRange t, rfl⟩

variable (N) in
/-- `S` is a non-empty siphon with `I ⊆ S ⊆ X`. -/
def InRegion (S : Finset (Fin m)) (I X : ℕ) : Prop :=
  S.Nonempty ∧ N.IsSiphon S ∧ (∀ p ∈ S, X.testBit p = true) ∧
    ∀ q, I.testBit q = true → ∃ hq : q < m, (⟨q, hq⟩ : Fin m) ∈ S

theorem shrinkS_sound {S : Finset (Fin m)} (hS : N.IsSiphon S) {X : ℕ}
    (hSX : ∀ p ∈ S, X.testBit p = true) : ∀ p ∈ S, (shrinkS (table N) X).testBit p = true := by
  intro p hp
  simp only [shrinkS, testBit_diff, hSX p hp, Bool.true_and, Bool.not_eq_true',
    testBit_unionIf, List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
  intro e he hX hpost
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 he
  rw [testBit_finMask_fin, decide_eq_true_eq] at hpost
  obtain ⟨q, hq, hpre⟩ := hS t ⟨p, hp, hpost⟩
  exact (land_ne_zero_iff (a := finMask fun p => decide (0 < N.pre t p)) (b := X)).2
    ⟨q, by rw [testBit_finMask_fin]; exact decide_eq_true hpre, hSX q hq⟩ hX

theorem emptyRegion_base {S : Finset (Fin m)} {I X : ℕ} (hne : S.Nonempty)
    (hSX : ∀ p ∈ S, X.testBit p = true)
    (hIS : ∀ q, I.testBit q = true → ∃ hq : q < m, (⟨q, hq⟩ : Fin m) ∈ S)
    (hc : ¬ I &&& X = I ∨ X = 0) : False := by
  rcases hc with h | h
  · apply h
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_land]
    cases hI : I.testBit q
    · rfl
    · obtain ⟨hq, hqS⟩ := hIS q hI
      simpa using hSX _ hqS
  · obtain ⟨p, hp⟩ := hne
    have := hSX p hp
    rw [h, Nat.zero_testBit] at this
    exact Bool.false_ne_true this

theorem emptyRegionAux_sound {S : Finset (Fin m)} {I : ℕ} (hne : S.Nonempty)
    (hS : N.IsSiphon S)
    (hIS : ∀ q, I.testBit q = true → ∃ hq : q < m, (⟨q, hq⟩ : Fin m) ∈ S) (k : ℕ) :
    ∀ X : ℕ, (∀ p ∈ S, X.testBit p = true) → emptyRegionAux (table N) I k X = true → False := by
  induction k with
  | zero =>
    intro X hSX h
    rw [emptyRegionAux] at h
    split at h
    · rename_i hc
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
      exact emptyRegion_base hne hSX hIS hc
    · exact Bool.false_ne_true h
  | succ k ih =>
    intro X hSX h
    rw [emptyRegionAux] at h
    split at h
    · rename_i hc
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
      exact emptyRegion_base hne hSX hIS hc
    · simp only at h
      split at h
      · exact Bool.false_ne_true h
      · exact ih _ (shrinkS_sound hS hSX) h

theorem emptyRegion_sound {S : Finset (Fin m)} {I X : ℕ}
    (h : emptyRegion m (table N) I X = true) (hR : InRegion N S I X) : False :=
  emptyRegionAux_sound hR.1 hR.2.1 hR.2.2.2 m X hR.2.2.1 h

theorem inRegion_or {S : Finset (Fin m)} {I X : ℕ} (hR : InRegion N S I X) (p : ℕ)
    (hp : ∃ hp : p < m, (⟨p, hp⟩ : Fin m) ∈ S) : InRegion N S (I ||| 2 ^ p) X := by
  refine ⟨hR.1, hR.2.1, hR.2.2.1, fun q hq => ?_⟩
  rw [Nat.testBit_lor, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hq
  rcases hq with hq | rfl
  · exact hR.2.2.2 q hq
  · exact hp

theorem inRegion_diff {S : Finset (Fin m)} {I X : ℕ} (hR : InRegion N S I X) (Y : ℕ)
    (hY : ∀ p ∈ S, Y.testBit p = false) : InRegion N S I (diff X Y) := by
  refine ⟨hR.1, hR.2.1, fun p hp => ?_, hR.2.2.2⟩
  simp [hR.2.2.1 p hp, hY p hp]

theorem check_sound {M₀ : Marking (Fin m)} (tree : Tree) (I X : ℕ)
    (h : check m (table N) (markMask M₀) tree I X = true) (S : Finset (Fin m))
    (hR : InRegion N S I X) : ∃ Q ∈ S.powerset, N.IsTrap Q ∧ Net.Marked M₀ Q := by
  induction tree generalizing I X with
  | empty => exact (emptyRegion_sound h hR).elim
  | trap q =>
    simp only [check, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hqI, htrap⟩, hmark⟩ := h
    classical
    refine ⟨Finset.univ.filter fun p : Fin m => q.testBit p, ?_, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have : I.testBit p = true := by
        have := congrArg (·.testBit p) hqI
        simp only [Nat.testBit_land, hp, Bool.true_and] at this
        exact this
      obtain ⟨_, hpS⟩ := hR.2.2.2 p this
      exact hpS
    · rintro t ⟨p, hp, hpre⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have ht := List.all_eq_true.1 htrap _ (mem_table t)
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at ht
      rcases ht with ht | ht
      · exfalso
        exact (land_ne_zero_iff (a := finMask fun p => decide (0 < N.pre t p)) (b := q)).2
          ⟨p, by rw [testBit_finMask_fin]; exact decide_eq_true hpre, hp⟩ ht
      · obtain ⟨j, hj1, hj2⟩ := land_ne_zero_iff.1 ht
        obtain ⟨hj, hpost⟩ := (testBit_finMask _ j).1 hj1
        exact ⟨⟨j, hj⟩, by simpa using hj2, by simpa using hpost⟩
    · obtain ⟨j, hj1, hj2⟩ := land_ne_zero_iff.1 hmark
      obtain ⟨hj, hM⟩ := (testBit_finMask _ j).1 hj2
      exact ⟨⟨j, hj⟩, by simpa using hj1, by simpa using hM⟩
  | traps =>
    simp only [check, trapsRegion, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hm, ht⟩ := h
    refine ⟨S, Finset.mem_powerset.2 subset_rfl, ?_, ?_⟩
    · rintro t ⟨p, hp, hpre⟩
      by_contra hno
      push Not at hno
      have he := ht _ (mem_table t) p p.isLt
      have hb : ((finMask fun p => decide (0 < N.pre t p)).testBit p &&
          X.testBit p) = true := by
        rw [testBit_finMask_fin, hR.2.2.1 p hp]; simpa using hpre
      rcases he with he | he
      · rw [hb] at he; exact Bool.false_ne_true he.symm
      · exact emptyRegion_sound he (inRegion_diff (inRegion_or hR p ⟨p.isLt, hp⟩) _
          fun q hq => by rw [testBit_finMask_fin]; simpa using hno q hq)
    · by_contra hno
      have hz : ∀ q ∈ S, (markMask M₀).testBit q = false := by
        intro q hq
        simp only [markMask, testBit_finMask_fin, decide_eq_false_iff_not, not_lt, Nat.le_zero]
        by_contra hq0
        exact hno ⟨q, hq, Nat.pos_of_ne_zero hq0⟩
      exact emptyRegion_sound hm (inRegion_diff hR _ hz)
  | split p l r ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hp : ∃ hp : p < m, (⟨p, hp⟩ : Fin m) ∈ S
    · exact ihl _ _ h.1 (inRegion_or hR p hp)
    · apply ihr _ _ h.2 (inRegion_diff hR _ fun x hx => ?_)
      rw [Nat.testBit_two_pow, decide_eq_false_iff_not]
      rintro rfl
      exact hp ⟨x.isLt, hx⟩

/-- **The siphon–trap property from a certificate.**  The transition masks `ts` and the
initial mask `m0` are literals, checked once against the net. -/
theorem siphonTrap_of_check {M₀ : Marking (Fin m)} {ts : List (ℕ × ℕ)} {m0 : ℕ} {tree : Tree}
    (hts : table N = ts) (hm0 : markMask M₀ = m0)
    (h : check m ts m0 tree 0 (ofPred m fun _ => true) = true) :
    N.SiphonTrapProperty M₀ := by
  subst hts hm0
  intro S hne hS
  exact check_sound tree 0 _ h S ⟨hne, hS, fun p _ => by simp [p.isLt], fun q hq => by simp at hq⟩

/-- **Free choice from masks.** -/
theorem freeChoice_of_checkFC {ts : List (ℕ × ℕ)} (hts : table N = ts)
    (h : checkFC ts = true) : N.FreeChoice := by
  subst hts
  intro t u p ht hu q
  have h' := List.all_eq_true.1 (List.all_eq_true.1 h _ (mem_table t)) _ (mem_table u)
  simp only [Bool.or_eq_true, beq_iff_eq] at h'
  rcases h' with h' | h'
  · exfalso
    exact (land_ne_zero_iff (a := finMask fun p => decide (0 < N.pre t p))
      (b := finMask fun p => decide (0 < N.pre u p))).2
      ⟨p, by rw [testBit_finMask_fin]; exact decide_eq_true ht,
        by rw [testBit_finMask_fin]; exact decide_eq_true hu⟩ h'
  · have := congrArg (·.testBit q) h'
    simp only [testBit_finMask_fin, decide_eq_decide] at this
    exact this

/-! ### Untrusted search -/

/-- One shrinking step towards the greatest trap inside `Y`: remove the input places of the
transitions that put nothing into `Y`. -/
def shrinkT (ts : List (ℕ × ℕ)) (Y : ℕ) : ℕ :=
  diff Y (unionIf ts (fun e => e.2 &&& Y == 0) Prod.fst)

/-- The greatest trap inside `Y`. -/
def maxTrap (ts : List (ℕ × ℕ)) : ℕ → ℕ → ℕ
  | 0, Y => Y
  | k + 1, Y => let Z := shrinkT ts Y; if Z == Y then Y else maxTrap ts k Z

/-- Search for a certificate; `Except.error S` returns a non-empty siphon `S` (as a mask)
containing no initially marked trap.  Splits follow the siphon condition: a transition putting
tokens into the included places must take tokens from the siphon. -/
def search (m : ℕ) (ts : List (ℕ × ℕ)) (m0 : ℕ) : ℕ → ℕ → ℕ → Except ℕ Tree
  | 0, I, _ => .error I
  | fuel + 1, I, X =>
    if emptyRegion m ts I X then .ok .empty
    else if maxTrap ts m I &&& m0 != 0 then .ok (.trap (maxTrap ts m I))
    else if trapsRegion m ts m0 I X then .ok .traps
    else
      let R := maxSiphon ts m X
      -- prefer a candidate that closes a marked trap, then a marked one, then the lowest
      let pick (c : ℕ) : Option ℕ :=
        let cs := (List.range m).filter c.testBit
        (cs.find? fun p => maxTrap ts m (I ||| 2 ^ p) &&& m0 != 0) <|>
          (cs.find? m0.testBit) <|> cs.head?
      let p? := match ts.find? (fun e => e.2 &&& I != 0 && e.1 &&& I == 0) with
        | some e => pick (e.1 &&& R)
        | none => if I == 0 then pick R else none
      match p? with
      | none => .error (if I == 0 then R else I)
      | some p => do
        let l ← search m ts m0 fuel (I ||| 2 ^ p) X
        let r ← search m ts m0 fuel I (diff X (2 ^ p))
        return .split p l r

variable (N) in
/-- A certificate for `N.SiphonTrapProperty M₀`, or a bad siphon (as a list of places). -/
def mkCert (M₀ : Marking (Fin m)) : Except (List ℕ) Tree :=
  match search m (table N) (markMask M₀) (2 * m + 2) 0 (ofPred m fun _ => true) with
  | .ok t => .ok t
  | .error R => .error ((List.range m).filter R.testBit)

end SiphonCheck

end AsyncLean
