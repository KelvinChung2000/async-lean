/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties
import AsyncLean.Checker.BTree
import Mathlib.Data.Nat.Bitwise

/-!
# A fast kernel checker for systems with numerically encoded states

The kernel evaluates definitions by unfolding them.  Functions defined by pattern matching
are compiled to `brecOn`/matcher terms whose unfolding costs several times more than a
direct recursor application, and type-class-generic code (`BEq`, `DecidableEq`, `Fin`
lists, …) adds further layers.  For model checking, where the same few operations run at
every state, this overhead dominates.

This file provides a checker whose inner loops are written directly with recursors and
operate only on natural numbers, whose arithmetic the kernel performs natively (GMP):

* states and labels are natural numbers (`enc : σ → ℕ`, `lab : λ → ℕ`);
* successors are produced by a function `F : ℕ → List (ℕ × ℕ × Bool)` giving the label,
  the target and an `ok` flag (used by encodings that are faithful only on part of the
  state space, such as markings packed into bit fields of a fixed width);
* the certificate (`Cert`) is a search tree of states with a rank (for livelock freedom)
  and a distance (for liveness), plus a list of *hubs*: from every state some hub is
  reachable (the distance decreases), and from every hub a trace leads, for each label, to
  a state enabling it.  Hubs are one state per terminal strongly connected component, so
  every live system has such a certificate.

`Fast.of_check` transfers a successful check to any LTS that `F` *encodes* (`Encodes`).

The trusted functions are kernel-only (`noncomputable`): the untrusted search runs compiled
code, and the result is checked once, by the kernel.
-/

namespace AsyncLean

namespace Fast

/-! ### Kernel-friendly primitives -/

section Prim

variable {α : Type*}

/-- `List.all`, by the recursor. -/
noncomputable def kall (l : List α) (p : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ r => Bool.rec (motive := fun _ => Bool)
    false r (p x)) l

/-- `List.any`, by the recursor. -/
noncomputable def kany (l : List α) (p : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ r => Bool.rec (motive := fun _ => Bool)
    r true (p x)) l

/-- Lookup in a search tree keyed by natural numbers. -/
noncomputable def kfind {β : Type*} (k : ℕ) (t : BTree (ℕ × β)) : Option β :=
  BTree.rec (motive := fun _ => Option β) none
    (fun _ x _ rl rr => Bool.rec (motive := fun _ => Option β) rl
      (Bool.rec (motive := fun _ => Option β) rr (some x.2) (Nat.beq k x.1)) (Nat.ble x.1 k))
    t

/-- `BTree.all`, by the recursor. -/
noncomputable def ktall (t : BTree α) (p : α → Bool) : Bool :=
  BTree.rec (motive := fun _ => Bool) true
    (fun _ x _ rl rr => Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false rr rl) (p x)) t

/-- `Nat.testBit`, with the kernel's native operations. -/
noncomputable def ktest (m i : ℕ) : Bool := !Nat.beq (Nat.land (Nat.shiftRight m i) 1) 0

/-- List equality by a Boolean element test, by the recursor. -/
noncomputable def kbeqList (f : α → α → Bool) (l : List α) : List α → Bool :=
  List.rec (motive := fun _ => List α → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ r m => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => Bool.rec (motive := fun _ => Bool) false (r ys) (f x y)) m) l

theorem eq_of_kbeqList {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l m : List α}, kbeqList f l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    change Bool.rec (motive := fun _ => Bool) false (kbeqList f xs ys) (f x y) = true at h
    cases hxy : f x y
    · rw [hxy] at h; cases h
    · rw [hxy] at h
      rw [hf x y hxy, eq_of_kbeqList hf h]

theorem blt_true {a b : ℕ} (h : Nat.blt a b = true) : a < b := by
  simpa [Nat.blt_eq] using h

theorem kall_eq (l : List α) (p : α → Bool) : kall l p = l.all p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [kall, List.all_cons] at *
    rw [← ih]; cases p x <;> rfl

theorem kany_eq (l : List α) (p : α → Bool) : kany l p = l.any p := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [kany, List.any_cons] at *
    rw [← ih]; cases p x <;> rfl

theorem mem_of_kfind {β : Type*} {k : ℕ} {t : BTree (ℕ × β)} {b : β} (h : kfind k t = some b) :
    (k, b) ∈ t.toList := by
  induction t with
  | leaf => cases h
  | node l x r ihl ihr =>
    simp only [BTree.toList, List.mem_append, List.mem_cons]
    change Bool.rec (motive := fun _ => Option β) (kfind k l)
      (Bool.rec (motive := fun _ => Option β) (kfind k r) (some x.2) (Nat.beq k x.1))
      (Nat.ble x.1 k) = some b at h
    cases hl : Nat.ble x.1 k
    · rw [hl] at h; exact Or.inl (ihl h)
    · rw [hl] at h
      cases hb : Nat.beq k x.1
      · rw [hb] at h; exact Or.inr (Or.inr (ihr h))
      · rw [hb] at h
        cases h
        exact Or.inr (Or.inl (by rw [Nat.eq_of_beq_eq_true hb]))

theorem ktall_iff {t : BTree α} {p : α → Bool} : ktall t p = true ↔ ∀ x ∈ t.toList, p x = true := by
  rw [← BTree.all_eq_true]
  suffices ktall t p = t.all p by rw [this]
  induction t with
  | leaf => rfl
  | node l x r ihl ihr =>
    change Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (ktall r p) (ktall l p)) (p x) = _
    rw [ihl, ihr]
    simp only [BTree.all]
    cases p x <;> cases l.all p <;> rfl

theorem ktest_eq (m i : ℕ) : ktest m i = m.testBit i := by
  rw [Bool.eq_iff_iff]; simp [ktest, Nat.testBit, Nat.land_comm]
  rcases Nat.mod_two_eq_zero_or_one (m >>> i) with h | h <;> simp [h]; rfl

end Prim

/-! ### Encodings -/

variable {σ ι : Type*}

/-- `F` faithfully encodes the LTS `A` on the states satisfying `Good`: every successor with
the `ok` flag is a step of `A` to a good state, and every step of `A` from a good state
appears among the successors, with the `ok` flag set only if the target is good. -/
structure Encodes (A : LTS σ ι) (Good : σ → Prop) (enc : σ → ℕ) (lab : ι → ℕ)
    (F : ℕ → List (ℕ × ℕ × Bool)) : Prop where
  sound : ∀ M, Good M → ∀ i m', (i, m', true) ∈ F (enc M) →
    ∃ l M', lab l = i ∧ A.step M l M' ∧ enc M' = m' ∧ Good M'
  complete : ∀ M l M', Good M → A.step M l M' →
    ∃ b, (lab l, enc M', b) ∈ F (enc M) ∧ (b = true → Good M')

/-! ### The trusted checker -/

/-- A certificate: states with rank and distance, and hubs with one trace per label. -/
abbrev Cert := BTree (ℕ × ℕ × ℕ) × List (ℕ × List (List ℕ))

/-- Checks along the successors `es` of a state of rank `r` and distance `d`; `prog` records
whether progress towards a hub has been seen. -/
noncomputable def chkSuccs (t : BTree (ℕ × ℕ × ℕ)) (imask r d : ℕ) (es : List (ℕ × ℕ × Bool)) :
    Bool → Bool :=
  List.rec (motive := fun _ => Bool → Bool) (fun prog => prog)
    (fun e _ rec prog => Bool.rec (motive := fun _ => Bool) false
      (Option.rec (motive := fun _ => Bool) false
        (fun rd => Bool.rec (motive := fun _ => Bool) false
          (rec (Bool.rec (motive := fun _ => Bool) (Nat.blt rd.2 d) true prog))
          (Bool.rec (motive := fun _ => Bool) true (Nat.blt rd.1 r) (ktest imask e.1)))
        (kfind e.2.1 t))
      e.2.2) es

/-- The checks at one state `x = (state, rank, distance)`. -/
noncomputable def chkNode (F : ℕ → List (ℕ × ℕ × Bool)) (t : BTree (ℕ × ℕ × ℕ))
    (hubs : List (ℕ × List (List ℕ))) (imask : ℕ) (dl lv : Bool) (x : ℕ × ℕ × ℕ) : Bool :=
  let init := Bool.rec (motive := fun _ => Bool) true (kany hubs fun h => Nat.beq h.1 x.1) lv
  List.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) init false dl)
    (fun e es _ => chkSuccs t imask x.2.1 x.2.2 (e :: es) init) (F x.1)

/-- Follow a trace of states from `s`; at its end, the label `i` must be enabled. -/
noncomputable def follow (F : ℕ → List (ℕ × ℕ × Bool)) (i : ℕ) (tr : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool)
    (fun s => kany (F s) fun e => Bool.rec (motive := fun _ => Bool) false e.2.2 (Nat.beq e.1 i))
    (fun s' _ rec s => Bool.rec (motive := fun _ => Bool) false (rec s')
      (kany (F s) fun e => Bool.rec (motive := fun _ => Bool) false e.2.2 (Nat.beq e.2.1 s')))
    tr

/-- The traces of a hub `h`, the `i`-th leading to label `i`. -/
noncomputable def chkTraces (F : ℕ → List (ℕ × ℕ × Bool)) (h : ℕ) (trs : List (List ℕ)) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun tr _ rec i => Bool.rec (motive := fun _ => Bool) false (rec (i + 1)) (follow F i tr h))
    trs

/-- **The fast checker.** With `dl`, every state has a successor; every internal step (a
label in `imask`) decreases the rank; with `lv`, every state makes progress towards a hub
and every hub has traces enabling each of the `L` labels. -/
noncomputable def check (F : ℕ → List (ℕ × ℕ × Bool)) (imask L : ℕ) (dl lv : Bool) (s₀ : ℕ)
    (c : Cert) : Bool :=
  (kfind s₀ c.1).isSome && ktall c.1 (chkNode F c.1 c.2 imask dl lv) &&
    (!lv || kall c.2 fun h => Nat.beq h.2.length L && chkTraces F h.1 h.2 0)

/-! ### Soundness -/

section Sound

variable {F : ℕ → List (ℕ × ℕ × Bool)} {t : BTree (ℕ × ℕ × ℕ)}

theorem chkSuccs_spec {imask r d : ℕ} {es : List (ℕ × ℕ × Bool)} {prog : Bool}
    (h : chkSuccs t imask r d es prog = true) :
    (∀ e ∈ es, e.2.2 = true ∧ ∃ r' d', kfind e.2.1 t = some (r', d') ∧
      (ktest imask e.1 = true → r' < r)) ∧
    (prog = true ∨ ∃ e ∈ es, ∃ r' d', kfind e.2.1 t = some (r', d') ∧ d' < d) := by
  induction es generalizing prog with
  | nil => exact ⟨by simp, Or.inl h⟩
  | cons e es ih =>
    change Bool.rec (motive := fun _ => Bool) false
      (Option.rec (motive := fun _ => Bool) false (fun rd => Bool.rec (motive := fun _ => Bool)
        false (chkSuccs t imask r d es (Bool.rec (motive := fun _ => Bool) (Nat.blt rd.2 d) true prog))
        (Bool.rec (motive := fun _ => Bool) true (Nat.blt rd.1 r) (ktest imask e.1)))
        (kfind e.2.1 t)) e.2.2 = true at h
    cases hok : e.2.2
    · rw [hok] at h; cases h
    rw [hok] at h
    cases hf : kfind e.2.1 t with
    | none => rw [hf] at h; cases h
    | some rd =>
      rw [hf] at h
      obtain ⟨r', d'⟩ := rd
      cases hr : (Bool.rec (motive := fun _ => Bool) true (Nat.blt r' r) (ktest imask e.1) : Bool)
      · simp only at h; rw [hr] at h; cases h
      simp only at h; rw [hr] at h
      obtain ⟨hall, hprog⟩ := ih h
      refine ⟨?_, ?_⟩
      · intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · refine ⟨hok, r', d', hf, fun hi => ?_⟩
          rw [hi] at hr
          exact blt_true hr
        · exact hall e' he'
      · rcases hprog with hp | ⟨e', he', r'', d'', hf', hlt⟩
        · cases prog
          · simp only at hp
            exact Or.inr ⟨e, List.mem_cons_self, r', d', hf, blt_true hp⟩
          · exact Or.inl rfl
        · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', r'', d'', hf', hlt⟩

theorem chkNode_spec {hubs : List (ℕ × List (List ℕ))} {imask : ℕ} {dl lv : Bool}
    {x : ℕ × ℕ × ℕ} (h : chkNode F t hubs imask dl lv x = true) :
    (dl = true → F x.1 ≠ []) ∧
    (∀ e ∈ F x.1, e.2.2 = true ∧ ∃ r' d', kfind e.2.1 t = some (r', d') ∧
      (ktest imask e.1 = true → r' < x.2.1)) ∧
    (lv = true → (∃ hb ∈ hubs, hb.1 = x.1) ∨
      ∃ e ∈ F x.1, ∃ r' d', kfind e.2.1 t = some (r', d') ∧ d' < x.2.2) := by
  have hinit : ∀ (b : Bool), b = Bool.rec (motive := fun _ => Bool) true
      (kany hubs fun h => Nat.beq h.1 x.1) lv →
      b = true → lv = true → ∃ hb ∈ hubs, hb.1 = x.1 := by
    rintro b rfl hb rfl
    simp only [kany_eq, List.any_eq_true] at hb
    obtain ⟨hb', hm, he⟩ := hb
    exact ⟨hb', hm, Nat.eq_of_beq_eq_true he⟩
  unfold chkNode at h
  simp only at h
  generalize hI : (Bool.rec (motive := fun _ => Bool) true (kany hubs fun h => Nat.beq h.1 x.1) lv
    : Bool) = I at h
  revert h
  cases hF : F x.1 with
  | nil =>
    intro h
    cases dl
    · refine ⟨by simp, by simp, fun hlv => Or.inl (hinit I hI.symm h hlv)⟩
    · cases h
  | cons e es =>
    intro h
    obtain ⟨hall, hprog⟩ := chkSuccs_spec h
    refine ⟨fun _ => by simp, hall, fun hlv => ?_⟩
    rcases hprog with hp | hp
    · exact Or.inl (hinit I hI.symm hp hlv)
    · exact Or.inr hp

theorem follow_spec {A : LTS σ ι} {Good : σ → Prop} {enc : σ → ℕ} {lab : ι → ℕ}
    (hE : Encodes A Good enc lab F) (hinj : Function.Injective lab) {l : ι} {tr : List ℕ}
    {M : σ} (hg : Good M) (h : follow F (lab l) tr (enc M) = true) :
    ∃ M', A.Reachable M M' ∧ A.Enabled M' l := by
  induction tr generalizing M with
  | nil =>
    change kany (F (enc M)) (fun e => Bool.rec (motive := fun _ => Bool) false e.2.2
      (Nat.beq e.1 (lab l))) = true at h
    simp only [kany_eq, List.any_eq_true] at h
    obtain ⟨⟨i, m', b⟩, hm, hb⟩ := h
    cases hi : Nat.beq i (lab l)
    · simp only [hi] at hb; cases hb
    simp only [hi] at hb
    subst hb
    rw [Nat.eq_of_beq_eq_true hi] at hm
    obtain ⟨l', M', hl', hst, -, -⟩ := hE.sound M hg _ _ hm
    rw [hinj hl'] at hst
    exact ⟨M, LTS.Reachable.refl _, M', hst⟩
  | cons s' rest ih =>
    change Bool.rec (motive := fun _ => Bool) false (follow F (lab l) rest s')
      (kany (F (enc M)) fun e => Bool.rec (motive := fun _ => Bool) false e.2.2
        (Nat.beq e.2.1 s')) = true at h
    cases hany : kany (F (enc M)) fun e => Bool.rec (motive := fun _ => Bool) false e.2.2
      (Nat.beq e.2.1 s')
    · rw [hany] at h; cases h
    rw [hany] at h
    simp only [kany_eq, List.any_eq_true] at hany
    obtain ⟨⟨i, m', b⟩, hm, hb⟩ := hany
    cases hi : Nat.beq m' s'
    · simp only [hi] at hb; cases hb
    simp only [hi] at hb
    subst hb
    rw [Nat.eq_of_beq_eq_true hi] at hm
    obtain ⟨l', M', -, hst, henc, hg'⟩ := hE.sound M hg _ _ hm
    rw [← henc] at h
    obtain ⟨M'', hr, hen⟩ := ih hg' h
    exact ⟨M'', LTS.Reachable.head ⟨l', hst⟩ hr, hen⟩

theorem chkTraces_spec {trs : List (List ℕ)} {h i : ℕ} (hc : chkTraces F h trs i = true) :
    ∀ j (hj : j < trs.length), follow F (i + j) trs[j] h = true := by
  induction trs generalizing i with
  | nil => intro j hj; simp at hj
  | cons tr rest ih =>
    change Bool.rec (motive := fun _ => Bool) false (chkTraces F h rest (i + 1))
      (follow F i tr h) = true at hc
    cases hf : follow F i tr h
    · rw [hf] at hc; cases hc
    rw [hf] at hc
    intro j hj
    cases j with
    | zero => simpa using hf
    | succ j =>
      have := ih hc j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- **Soundness of the fast checker.** -/
theorem of_check {A : LTS σ ι} {Good : σ → Prop} {enc : σ → ℕ} {lab : ι → ℕ}
    (hE : Encodes A Good enc lab F) (hinj : Function.Injective lab) {imask L : ℕ}
    {dl lv : Bool} {M₀ : σ} {c : Cert} (hg₀ : Good M₀)
    (h : check F imask L dl lv (enc M₀) c = true) :
    (dl = true → A.DeadlockFree M₀) ∧
      A.LivelockFree (fun l => imask.testBit (lab l) = true) M₀ ∧
      (lv = true → ∀ l, lab l < L → A.LiveLabel M₀ l) := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  obtain ⟨⟨h₀, hall⟩, hhubs⟩ := h
  rw [ktall_iff] at hall
  -- the invariant: good, and present in the tree
  let Inv : σ → Prop := fun M => Good M ∧ ∃ rd, kfind (enc M) c.1 = some rd
  have hnode : ∀ M rd, kfind (enc M) c.1 = some rd →
      chkNode F c.1 c.2 imask dl lv (enc M, rd) = true :=
    fun M rd hf => hall _ (mem_of_kfind hf)
  have hinv₀ : Inv M₀ := ⟨hg₀, Option.isSome_iff_exists.1 h₀⟩
  have hstep : ∀ M l M', Inv M → A.step M l M' → Inv M' := by
    rintro M l M' ⟨hg, rd, hf⟩ hst
    obtain ⟨b, hm, hb⟩ := hE.complete M l M' hg hst
    obtain ⟨-, hs, -⟩ := chkNode_spec (hnode M rd hf)
    obtain ⟨hok, r', d', hf', -⟩ := hs _ hm
    exact ⟨hb hok, _, hf'⟩
  have hreach : ∀ M, A.Reachable M₀ M → Inv M := fun M hM => hM.invariant hinv₀ hstep
  refine ⟨fun hdl => ?_, ?_, fun hlv => ?_⟩
  · -- deadlock freedom
    refine LTS.DeadlockFree.of_invariant Inv hinv₀ hstep fun M ⟨hg, rd, hf⟩ => ?_
    obtain ⟨hne, hs, -⟩ := chkNode_spec (hnode M rd hf)
    obtain ⟨⟨i, m', b⟩, hm⟩ := List.exists_mem_of_ne_nil _ (hne hdl)
    obtain ⟨hok, -⟩ := hs _ hm
    simp only at hok
    subst hok
    obtain ⟨l, M', -, hst, -⟩ := hE.sound M hg _ _ hm
    exact ⟨l, M', hst⟩
  · -- livelock freedom: the rank decreases along internal steps
    refine LTS.LivelockFree.of_ranking Inv hinv₀ hstep
      (fun M => ((kfind (enc M) c.1).map Prod.fst).getD 0) fun M l M' ⟨hg, rd, hf⟩ hl hst => ?_
    obtain ⟨b, hm, -⟩ := hE.complete M l M' hg hst
    obtain ⟨-, hs, -⟩ := chkNode_spec (hnode M rd hf)
    obtain ⟨-, r', d', hf', hlt⟩ := hs _ hm
    simp only [hf, hf', Option.map_some, Option.getD_some]
    exact hlt (by rw [ktest_eq]; exact hl)
  · -- liveness: reach a hub, then follow its trace
    have hhubs : ∀ x ∈ c.2, Nat.beq x.2.length L = true ∧ chkTraces F x.1 x.2 0 = true := by
      simpa [hlv, kall_eq] using hhubs
    intro l hl M hM
    have key : ∀ n M, A.Reachable M₀ M → ((kfind (enc M) c.1).map fun rd => rd.2).getD 0 = n →
        ∃ M', A.Reachable M M' ∧ A.Enabled M' l := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro M hM hn
        obtain ⟨hg, rd, hf⟩ := hreach M hM
        obtain ⟨-, -, hp⟩ := chkNode_spec (hnode M rd hf)
        rcases hp hlv with ⟨hb, hmem, heq⟩ | ⟨⟨i, m', b⟩, hm, r', d', hf', hlt⟩
        · obtain ⟨hlen, htr⟩ := hhubs hb hmem
          have := chkTraces_spec htr (lab l) (by rw [Nat.eq_of_beq_eq_true hlen]; exact hl)
          rw [Nat.zero_add, heq] at this
          exact follow_spec hE hinj hg this
        · obtain ⟨hs, -⟩ := (chkNode_spec (hnode M rd hf)).2
          obtain ⟨hok, -⟩ := hs _ hm
          simp only at hok
          subst hok
          obtain ⟨l', M', -, hst, henc, -⟩ := hE.sound M hg _ _ hm
          have hM' : A.Reachable M₀ M' := hM.tail ⟨l', hst⟩
          obtain ⟨M'', hr, hen⟩ := ih d' (by rw [← hn, hf]; exact hlt) M' hM'
            (by rw [henc, hf']; rfl)
          exact ⟨M'', LTS.Reachable.head ⟨l', hst⟩ hr, hen⟩
    exact key _ M hM rfl

end Sound

/-! ### Checking in parts

`check` is one kernel evaluation over the whole tree.  It splits into the checks of the
initial state and the hubs (`checkHead`) and the checks at the states in key ranges
(`checkPart`), each its own kernel goal: the kernel's memory then grows with a part, not with
the whole state space. -/

/-- `n ∈ [lo, hi)`, where `hi = 0` stands for no upper bound. -/
noncomputable def inR (lo hi n : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) (Nat.blt n hi) true (Nat.beq hi 0)) (Nat.ble lo n)

/-- The checks of `check` other than those at the states. -/
noncomputable def checkHead (F : ℕ → List (ℕ × ℕ × Bool)) (L : ℕ) (lv : Bool) (s₀ : ℕ)
    (c : Cert) : Bool :=
  (kfind s₀ c.1).isSome && (!lv || kall c.2 fun h => Nat.beq h.2.length L && chkTraces F h.1 h.2 0)

/-- The checks of `check` at the states in `[lo, hi)`. -/
noncomputable def checkPart (F : ℕ → List (ℕ × ℕ × Bool)) (imask : ℕ) (dl lv : Bool) (c : Cert)
    (lo hi : ℕ) : Bool :=
  ktall c.1 fun x => Bool.rec (motive := fun _ => Bool) true (chkNode F c.1 c.2 imask dl lv x)
    (inR lo hi x.1)

theorem inR_spec {lo hi n : ℕ} : inR lo hi n = true ↔ lo ≤ n ∧ (hi = 0 ∨ n < hi) := by
  have hl : Nat.ble lo n = true ↔ lo ≤ n := ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩
  have hb : Nat.beq hi 0 = true ↔ hi = 0 := ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl 0⟩
  have ht : Nat.blt n hi = true ↔ n < hi := ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩
  unfold inR
  cases h₁ : Nat.ble lo n <;> cases h₂ : Nat.beq hi 0 <;> cases h₃ : Nat.blt n hi <;>
    simp only [h₁, h₂, h₃, Bool.false_eq_true, false_iff, true_iff] at hl hb ht ⊢ <;> omega

theorem checkPart_split {F : ℕ → List (ℕ × ℕ × Bool)} {imask : ℕ} {dl lv : Bool} {c : Cert}
    {lo hi : ℕ} (m : ℕ) (hm : Nat.beq m 0 = false) (h₁ : checkPart F imask dl lv c lo m = true)
    (h₂ : checkPart F imask dl lv c m hi = true) : checkPart F imask dl lv c lo hi = true := by
  have hm : m ≠ 0 := Nat.ne_of_beq_eq_false hm
  unfold checkPart at *
  rw [ktall_iff] at *
  intro x hx
  have e₁ := h₁ x hx
  have e₂ := h₂ x hx
  cases hr : inR lo hi x.1
  · rfl
  · rw [inR_spec] at hr
    by_cases hlt : x.1 < m
    · have : inR lo m x.1 = true := inR_spec.2 ⟨hr.1, Or.inr hlt⟩
      rwa [this] at e₁
    · have : inR m hi x.1 = true := inR_spec.2 ⟨by omega, hr.2⟩
      rwa [this] at e₂

theorem check_of_parts {F : ℕ → List (ℕ × ℕ × Bool)} {imask L : ℕ} {dl lv : Bool} {s₀ : ℕ}
    {c : Cert} (hh : checkHead F L lv s₀ c = true) (hp : checkPart F imask dl lv c 0 0 = true) :
    check F imask L dl lv s₀ c = true := by
  unfold checkHead at hh
  unfold checkPart at hp
  unfold check
  rw [ktall_iff] at hp
  simp only [Bool.and_eq_true] at hh ⊢
  refine ⟨⟨hh.1, ktall_iff.2 fun x hx => ?_⟩, hh.2⟩
  have := hp x hx
  rwa [inR_spec.2 ⟨Nat.zero_le _, Or.inl rfl⟩] at this

end Fast

end AsyncLean

/-! ### Untrusted certificate generation

Compiled code, not verified: a wrong certificate only makes the kernel check fail. -/

namespace AsyncLean

namespace Fast

/-- Explore from `s₀`: the states (index 0 is `s₀`) and, for each, its labelled successors
as state indices.  Fails on a successor without the `ok` flag or beyond `fuel` states. -/
def explore (succ : ℕ → List (ℕ × ℕ × Bool)) (fuel s₀ : ℕ) :
    Except String (Array ℕ × Array (Array (ℕ × ℕ))) := Id.run do
  let mut idx : Std.HashMap ℕ ℕ := ({} : Std.HashMap ℕ ℕ).insert s₀ 0
  let mut states : Array ℕ := #[s₀]
  let mut succs : Array (Array (ℕ × ℕ)) := #[]
  let mut i := 0
  while i < states.size do
    if states.size > fuel then return .error "the state space exceeds the fuel"
    let s := states[i]!
    let mut out : Array (ℕ × ℕ) := #[]
    for (l, t, ok) in succ s do
      unless ok do return .error "overflow"
      match idx[t]? with
      | some j => out := out.push (l, j)
      | none =>
        idx := idx.insert t states.size
        out := out.push (l, states.size)
        states := states.push t
    succs := succs.push out
    i := i + 1
  return .ok (states, succs)

/-- Longest internal path from each state, or `none` if internal steps form a cycle. -/
def ranks (succs : Array (Array (ℕ × ℕ))) (internal : ℕ → Bool) : Option (Array ℕ) := Id.run do
  let n := succs.size
  let mut indeg : Array ℕ := Array.replicate n 0
  for v in [0:n] do
    for (l, w) in succs[v]! do
      if internal l then indeg := indeg.modify w (· + 1)
  let mut queue : Array ℕ := #[]
  for v in [0:n] do
    if indeg[v]! == 0 then queue := queue.push v
  let mut qi := 0
  while qi < queue.size do
    let v := queue[qi]!
    qi := qi + 1
    for (l, w) in succs[v]! do
      if internal l then
        indeg := indeg.modify w (· - 1)
        if indeg[w]! == 0 then queue := queue.push w
  if queue.size < n then return none
  let mut rank : Array ℕ := Array.replicate n 0
  for v in queue.reverse do
    let mut r := 0
    for (l, w) in succs[v]! do
      if internal l then r := max r (rank[w]! + 1)
    rank := rank.set! v r
  return some rank

/-- Strongly connected components (iterative Tarjan): the component of each state. -/
def sccs (succs : Array (Array (ℕ × ℕ))) : Array ℕ := Id.run do
  let n := succs.size
  let none' := n + 1
  let mut index : Array ℕ := Array.replicate n none'
  let mut low : Array ℕ := Array.replicate n 0
  let mut onStack : Array Bool := Array.replicate n false
  let mut stack : Array ℕ := #[]
  let mut comp : Array ℕ := Array.replicate n 0
  let mut ncomp := 0
  let mut counter := 0
  for root in [0:n] do
    if index[root]! != none' then continue
    let mut call : Array (ℕ × ℕ) := #[(root, 0)]
    index := index.set! root counter
    low := low.set! root counter
    counter := counter + 1
    stack := stack.push root
    onStack := onStack.set! root true
    while call.size > 0 do
      let (v, i) := call.back!
      let es := succs[v]!
      if i < es.size then
        call := call.set! (call.size - 1) (v, i + 1)
        let w := es[i]!.2
        if index[w]! == none' then
          index := index.set! w counter
          low := low.set! w counter
          counter := counter + 1
          stack := stack.push w
          onStack := onStack.set! w true
          call := call.push (w, 0)
        else if onStack[w]! then
          low := low.set! v (min low[v]! index[w]!)
      else
        call := call.pop
        if low[v]! == index[v]! then
          let mut go := true
          while go do
            let x := stack.back!
            stack := stack.pop
            onStack := onStack.set! x false
            comp := comp.set! x ncomp
            if x == v then go := false
          ncomp := ncomp + 1
        if call.size > 0 then
          let u := call.back!.1
          low := low.set! u (min low[u]! low[v]!)
  return comp

/-- A balanced search tree from an array sorted by key. -/
def buildTree {α : Type} [Inhabited α] (a : Array α) : ℕ → ℕ → ℕ → BTree α
  | 0, _, _ => .leaf
  | fuel + 1, lo, hi =>
    if lo ≥ hi then .leaf
    else
      let mid := (lo + hi) / 2
      .node (buildTree a fuel lo mid) a[mid]! (buildTree a fuel (mid + 1) hi)

/-- Compute a certificate for `check succ imask L dl lv s₀` (untrusted). -/
def mkCert (succ : ℕ → List (ℕ × ℕ × Bool)) (imask L : ℕ) (dl lv : Bool) (fuel s₀ : ℕ) :
    Except String Cert := do
  let (states, succs) ← explore succ fuel s₀
  let n := states.size
  if dl then
    if let some v := (List.range n).find? (fun v => succs[v]!.isEmpty) then
      throw s!"deadlock at state {states[v]!}"
  let some rank := ranks succs (fun l => imask.testBit l) | throw "livelock"
  let mut dist : Array ℕ := Array.replicate n 0
  let mut hubs : List (ℕ × List (List ℕ)) := []
  if lv then
    let comp := sccs succs
    -- terminal components: no edge leaves them
    let ncomp := comp.foldl max 0 + 1
    let mut terminal : Array Bool := Array.replicate ncomp true
    for v in [0:n] do
      for (_, w) in succs[v]! do
        if comp[w]! != comp[v]! then terminal := terminal.set! comp[v]! false
    let mut rep : Array ℕ := Array.replicate ncomp n
    for v in [0:n] do
      if terminal[comp[v]!]! && rep[comp[v]!]! == n then rep := rep.set! comp[v]! v
    let hubIdx := rep.toList.filter (· < n)
    -- distances to the hubs, by backward breadth-first search
    let mut preds : Array (Array ℕ) := Array.replicate n #[]
    for v in [0:n] do
      for (_, w) in succs[v]! do
        preds := preds.modify w (·.push v)
    let inf := n + 1
    dist := Array.replicate n inf
    let mut queue : Array ℕ := #[]
    for h in hubIdx do
      dist := dist.set! h 0
      queue := queue.push h
    let mut qi := 0
    while qi < queue.size do
      let v := queue[qi]!
      qi := qi + 1
      for u in preds[v]! do
        if dist[u]! == inf then
          dist := dist.set! u (dist[v]! + 1)
          queue := queue.push u
    -- for each hub, a trace to a state enabling each label
    for h in hubIdx do
      let mut parent : Array ℕ := Array.replicate n inf
      parent := parent.set! h h
      let mut order : Array ℕ := #[h]
      let mut oi := 0
      while oi < order.size do
        let v := order[oi]!
        oi := oi + 1
        for (_, w) in succs[v]! do
          if parent[w]! == inf then
            parent := parent.set! w v
            order := order.push w
      let mut trs : List (List ℕ) := []
      for i in [0:L] do
        let some v := order.find? (fun v => succs[v]!.any (·.1 == i))
          | throw s!"label {i} is not live"
        let mut path : List ℕ := []
        let mut x := v
        let mut steps := 0
        while x != h && steps ≤ n do
          path := states[x]! :: path
          x := parent[x]!
          steps := steps + 1
        trs := trs ++ [path]
      hubs := hubs ++ [(states[h]!, trs)]
  let entries := ((List.range n).map fun v => (states[v]!, rank[v]!, dist[v]!)).toArray.qsort
    (fun a b => a.1 < b.1)
  return (buildTree entries (n + 1) 0 n, hubs)

end Fast

end AsyncLean
