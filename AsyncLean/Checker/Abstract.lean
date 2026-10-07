/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Petri

/-!
# Checking infinite-state systems through a finite abstraction

The explicit model checker enumerates the reachable states, so it needs finitely many of
them.  An unbounded Petri net has infinitely many reachable markings.  This file checks such
systems through a finite **over-approximation**.

## Abstractions

`ExplicitLTS.Abstracts E B α` says that the finite explicit system `E` over-approximates the
system `B` through `α`: every step of `B` is matched by a step of `E` with the same label,
and a label enabled in `E` at `α s` is enabled in `B` at `s`.  Then (`of_checkACert`):

* if no reachable state of `E` is a deadlock, `B` is deadlock free;
* if a ranking decreases along the internal steps of `E`, `B` is livelock free;
* if, for each label `l`, every reachable state of `E` has a finite *must-distance* to `l` —
  either `l` is enabled, or for some enabled label `u` **every** `u`-successor is closer —
  then `l` is live in `B`.  Requiring all `u`-successors to be closer is what makes this
  sound for an over-approximation: whichever concrete successor `B` takes, its abstraction
  is one of them.

## Counter abstraction of Petri nets

`PNet.abstr K` caps every place at `K` tokens, where `K` is at least every arc weight from a
place, so enabledness is exact.  A place with fewer than `K` tokens is tracked exactly; a
place at the cap stands for "`K` or more", and when tokens are removed from it every value
the concrete marking could have, capped at `K`, is a possible successor.  `PNet.of_checkAbs`
turns a checked certificate for the abstraction into deadlock freedom, livelock freedom and
liveness of the net itself.

The method is sound for any net, bounded or not, but not complete: a property can hold while
the abstraction is too coarse to show it.  Raising `K` refines it.
-/

namespace AsyncLean

namespace ExplicitLTS

section AbstractSection

variable {S A L : Type*} [DecidableEq A] (E : ExplicitLTS A L) (cmp : A → A → Ordering)
  (key : L → ℕ)

/-- `E` over-approximates `B` through `α`. -/
structure Abstracts (B : LTS S L) (α : S → A) : Prop where
  /-- Every step of `B` is matched by a step of `E`. -/
  sim : ∀ s l s', B.step s l s' → (l, α s') ∈ E.succ (α s)
  /-- A label enabled in the abstraction is enabled in `B`. -/
  en : ∀ s l a', (l, a') ∈ E.succ (α s) → B.Enabled s l

/-- An abstraction certificate: each abstract state with its rank (for livelock freedom),
its must-distances to the labels (indexed by key) and its successors (labels as keys). -/
abbrev ACert (A : Type*) := BTree (A × (ℕ × List ℕ × List (ℕ × A)))

/-- The checks at one abstract state.  `dl` asks for deadlock freedom, `internal` gives the
internal labels (by key) and `labels` the labels (by key) whose liveness is checked. -/
def checkNodeA (dl : Bool) (internal : ℕ → Bool) (labels : List ℕ) (c : ACert A) (a : A) :
    Bool :=
  match c.findData cmp a with
  | none => false
  | some (r, dv, es) =>
    decide (E.keyedSucc key a = es) && (!dl || !es.isEmpty) &&
    (es.all fun e => match c.findData cmp e.2 with
      | none => false
      | some (r', _, _) => !internal e.1 || decide (r' < r)) &&
    labels.all fun k => es.any (fun e => e.1 == k) ||
      es.any fun e => es.all fun e' => e'.1 != e.1 || match c.findData cmp e'.2 with
        | none => false
        | some (_, dv', _) => decide (dv'.getD k 0 < dv.getD k 0)

/-- Check an abstraction certificate from the abstract initial state `a₀` (trusted). -/
def checkACert (dl : Bool) (internal : ℕ → Bool) (labels : List ℕ) (a₀ : A) (c : ACert A) :
    Bool :=
  (c.findData cmp a₀).isSome && c.all fun x => E.checkNodeA cmp key dl internal labels c x.1

variable {E cmp key}

theorem checkNodeA_spec {dl : Bool} {internal : ℕ → Bool} {labels : List ℕ} {c : ACert A}
    {a : A} {r : ℕ} {dv : List ℕ} {es : List (ℕ × A)} (hf : c.findData cmp a = some (r, dv, es))
    (h : E.checkNodeA cmp key dl internal labels c a = true) :
    E.keyedSucc key a = es ∧ (dl = true → es ≠ []) ∧
      (∀ e ∈ es, ∃ r' dv' es', c.findData cmp e.2 = some (r', dv', es') ∧
        (internal e.1 = true → r' < r)) ∧
      (∀ k ∈ labels, (∃ e ∈ es, e.1 = k) ∨ ∃ e ∈ es, ∀ e' ∈ es, e'.1 = e.1 →
        ∃ r' dv' es', c.findData cmp e'.2 = some (r', dv', es') ∧ dv'.getD k 0 < dv.getD k 0) := by
  unfold checkNodeA at h
  rw [hf] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hks, hdl⟩, hr⟩, hl⟩ := h
  refine ⟨hks, fun hd => ?_, fun e he => ?_, fun k hk => ?_⟩
  · simp only [hd, Bool.not_true, Bool.false_or, Bool.not_eq_eq_eq_not,
      List.isEmpty_eq_false_iff] at hdl
    exact hdl
  · have := hr e he
    split at this
    · cases this
    · rename_i r' dv' es' hf'
      refine ⟨r', dv', es', hf', fun hi => ?_⟩
      simp only [hi, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
      exact this
  · have := hl k hk
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq, List.all_eq_true] at this
    rcases this with h1 | ⟨e, he, hall⟩
    · exact Or.inl h1
    · refine Or.inr ⟨e, he, fun e' he' heq => ?_⟩
      rcases hall e' he' with h1 | h1
      · simp [heq] at h1
      · split at h1
        · cases h1
        · rename_i r' dv' es' hf'
          exact ⟨r', dv', es', hf', of_decide_eq_true h1⟩

/-- **Soundness of abstraction certificates.** -/
theorem of_checkACert (hkey : Function.Injective key) {B : LTS S L} {α : S → A}
    (hab : E.Abstracts B α) {s₀ : S} {dl : Bool} {internal : ℕ → Bool} {labels : List ℕ}
    {c : ACert A} (h : E.checkACert cmp key dl internal labels (α s₀) c = true) :
    (dl = true → B.DeadlockFree s₀) ∧
      B.LivelockFree (fun l => internal (key l) = true) s₀ ∧
      ∀ l, key l ∈ labels → B.LiveLabel s₀ l := by
  simp only [checkACert, Bool.and_eq_true] at h
  obtain ⟨h₀, hc⟩ := h
  rw [BTree.all_eq_true] at hc
  have hnode : ∀ a d, c.findData cmp a = some d → E.checkNodeA cmp key dl internal labels c a =
      true := fun a d hf => hc _ (BTree.mem_toList_of_findData hf)
  have hmem : ∀ {s l s'} {es : List (ℕ × A)}, E.keyedSucc key (α s) = es → B.step s l s' →
      (key l, α s') ∈ es := fun hks hst =>
    hks ▸ List.mem_map_of_mem (f := fun e => (key e.1, e.2)) (hab.sim _ _ _ hst)
  -- the invariant: the abstraction of a reachable state is in the certificate
  let I : S → Prop := fun s => ∃ d, c.findData cmp (α s) = some d
  have hI₀ : I s₀ := Option.isSome_iff_exists.1 h₀
  have hstep : ∀ s l s', I s → B.step s l s' → I s' := by
    rintro s l s' ⟨⟨r, dv, es⟩, hf⟩ hst
    obtain ⟨hks, -, hsucc, -⟩ := checkNodeA_spec hf (hnode _ _ hf)
    obtain ⟨r', dv', es', hf', -⟩ := hsucc _ (hmem hks hst)
    exact ⟨_, hf'⟩
  -- a keyed abstract successor is a labelled abstract successor
  have hkeyed : ∀ {s k a'} {es : List (ℕ × A)}, E.keyedSucc key (α s) = es → (k, a') ∈ es →
      ∃ l, key l = k ∧ (l, a') ∈ E.succ (α s) := by
    intro s k a' es hks he
    rw [← hks, keyedSucc, List.mem_map] at he
    obtain ⟨⟨l, a''⟩, hm, he⟩ := he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨l, rfl, hm⟩
  refine ⟨fun hd => ?_, ?_, fun l hl => ?_⟩
  · refine LTS.DeadlockFree.of_invariant I hI₀ hstep fun s ⟨⟨r, dv, es⟩, hf⟩ => ?_
    obtain ⟨hks, hne, -, -⟩ := checkNodeA_spec hf (hnode _ _ hf)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hne hd)
    obtain ⟨l, -, hm⟩ := hkeyed hks he
    obtain ⟨s', hs'⟩ := hab.en _ _ _ hm
    exact ⟨l, s', hs'⟩
  · refine LTS.LivelockFree.of_ranking I hI₀ hstep
      (fun s => ((c.findData cmp (α s)).map Prod.fst).getD 0) fun s l s' hs hl hst => ?_
    obtain ⟨⟨r, dv, es⟩, hf⟩ := hs
    obtain ⟨hks, -, hsucc, -⟩ := checkNodeA_spec hf (hnode _ _ hf)
    obtain ⟨r', dv', es', hf', hlt⟩ := hsucc _ (hmem hks hst)
    simp only [hf, hf', Option.map_some, Option.getD_some]
    exact hlt hl
  · refine LTS.LiveLabel.of_ranking I hI₀ hstep l
      (fun s => ((c.findData cmp (α s)).map fun d => d.2.1.getD (key l) 0).getD 0)
      fun s ⟨⟨r, dv, es⟩, hf⟩ => ?_
    obtain ⟨hks, -, -, hlive⟩ := checkNodeA_spec hf (hnode _ _ hf)
    rcases hlive _ hl with ⟨e, he, hk⟩ | ⟨e, he, hall⟩
    · obtain ⟨l', hl', hm⟩ := hkeyed hks he
      rw [hk] at hl'
      exact Or.inl (hkey hl' ▸ hab.en _ _ _ hm)
    · obtain ⟨u, hu, hm⟩ := hkeyed hks he
      obtain ⟨s', hs'⟩ := hab.en _ _ _ hm
      obtain ⟨r', dv', es', hf', hlt⟩ := hall _ (hmem hks hs') hu
      refine Or.inr ⟨u, s', hs', ?_⟩
      simp only [hf, hf', Option.map_some, Option.getD_some]
      exact hlt

end AbstractSection

/-! ### Untrusted certificate generation -/

section AbstractSearch

variable {A L : Type*} [DecidableEq A] (E : ExplicitLTS A L) (cmp : A → A → Ordering)
  (key : L → ℕ)

/-- Rounds of backward must-distance layering: a state gets distance `j + 1` once some
label's successors all have a distance. -/
def andDistAux (states : List (A × List (ℕ × A))) : ℕ → ℕ → BStore (A × ℕ) → BStore (A × ℕ)
  | 0, _, tbl => tbl
  | fuel + 1, j, tbl =>
    let has (a : A) : Bool := (tbl.lookup cmp a).isSome
    let next := states.filter fun x => !has x.1 && x.2.any fun e =>
      x.2.all fun e' => e'.1 != e.1 || has e'.2
    if next.isEmpty then tbl
    else andDistAux states fuel (j + 1) (next.foldl (fun tb x => tb.pushKV cmp x.1 (j + 1)) tbl)

/-- Candidate must-distances to the label with key `k`. -/
def andDist (states : List (A × List (ℕ × A))) (k : ℕ) : BTree (A × ℕ) :=
  let layer0 := states.filter fun x => x.2.any (·.1 == k)
  (andDistAux cmp states states.length 0
    (layer0.foldl (fun tb x => tb.pushKV cmp x.1 0) {})).tree.rebalance

/-- Compute an abstraction certificate (untrusted). -/
def mkACert (internal : ℕ → Bool) (labels : List ℕ) (fuel : ℕ) (a₀ : A) : ACert A :=
  let t := E.explore cmp fuel a₀
  let states := (t.toListAcc []).map fun a => (a, E.keyedSucc key a)
  let rk := E.autoRank cmp (fun l => internal (key l)) t
  let m := labels.foldl max 0 + 1
  let ds := labels.map fun k => (k, andDist cmp states k)
  BTree.ofList (states.map fun x => (x.1, (tblFn cmp rk x.1,
    (List.range m).map (fun k => match ds.lookup k with
      | some d => (d.lookup cmp x.1).getD (states.length + 1)
      | none => 0), x.2)))

end AbstractSearch

end ExplicitLTS

/-! ### Counter abstraction of Petri nets -/

namespace PNet

variable (N : PNet)

/-- The capped values a place can take after firing, from the capped value `v`, when `a`
tokens are consumed and `b` produced.  Below the cap the value is exact; at the cap the
place held `K` or more tokens. -/
def capVals (K v a b : ℕ) : List ℕ :=
  if v < K then [min (v - a + b) K]
  else List.range' (min (K - a + b) K) (K + 1 - min (K - a + b) K)

/-- All the capped markings that firing can produce from the capped marking given as a list
(`i` is the index of its head). -/
def absFire (K : ℕ) (pre post : List ℕ) : ℕ → List ℕ → List (List ℕ)
  | _, [] => [[]]
  | i, v :: vs =>
    let rest := absFire K pre post (i + 1) vs
    (capVals K v (pre.count i) (post.count i)).flatMap fun x => rest.map (x :: ·)

/-- Successors in the counter abstraction. -/
def absSucc (K : ℕ) (a : List ℕ) : List (Fin N.trans.length × List ℕ) :=
  (List.finRange N.trans.length).flatMap fun t =>
    if enabledL a (N.tr t).pre then (absFire K (N.tr t).pre (N.tr t).post 0 a).map (t, ·)
    else []

/-- The counter abstraction with cap `K`. -/
def abstr (K : ℕ) : ExplicitLTS (List ℕ) (Fin N.trans.length) := ⟨N.absSucc K⟩

/-- The abstraction of a marking: every place capped at `K`. -/
def cap (K : ℕ) (M : Marking (Fin N.places)) : List ℕ := (N.enc M).map (min · K)

/-- The cap is at least every arc weight from a place, so enabledness is exact. -/
def capOk (K : ℕ) : Bool := N.trans.all fun t => t.pre.all fun i => decide (t.pre.count i ≤ K)

/-- The smallest valid cap (the largest arc weight from a place, at least one).  With this
cap a place holding one token stands for "one or more"; `async_decide` starts one above it,
so that places holding few tokens are tracked exactly. -/
def minCap : ℕ := N.trans.foldl (fun k t => t.pre.foldl (fun k i => max k (t.pre.count i)) k) 1

/-- Internal transitions, by index. -/
def internalKey (i : ℕ) : Bool := (N.trans[i]?.map (·.internal)).getD false

/-- Check an abstraction certificate for the properties selected by `dl` (deadlock freedom),
`ll` (livelock freedom) and `lv` (liveness) (trusted). -/
def checkAbs (K : ℕ) (dl ll lv : Bool) (c : ExplicitLTS.ACert (List ℕ)) : Bool :=
  N.wf && N.capOk K && (N.abstr K).checkACert lexCmp Fin.val dl
    (if ll then N.internalKey else fun _ => false)
    (if lv then List.range N.trans.length else []) (N.init.map (min · K)) c

/-- Compute an abstraction certificate (untrusted). -/
def mkAbsCert (K : ℕ) (ll lv : Bool) (fuel : ℕ := 100000) : ExplicitLTS.ACert (List ℕ) :=
  (N.abstr K).mkACert lexCmp Fin.val (if ll then N.internalKey else fun _ => false)
    (if lv then List.range N.trans.length else []) fuel (N.init.map (min · K))

/-- Whether the explicit exploration of the net closes within `fuel` states (untrusted; used to
decide whether to fall back to the abstraction). -/
def closes (fuel : ℕ := 100000) : Bool :=
  N.wf && N.explicit.closedB lexCmp (N.explicit.explore lexCmp fuel N.init)

variable {N}

theorem getD_map_min (xs : List ℕ) (K i : ℕ) :
    (xs.map (min · K)).getD i 0 = min (xs.getD i 0) K := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> simp

theorem enabledL_map_min {K : ℕ} {pre : List ℕ} (hK : ∀ i, pre.count i ≤ K) (xs : List ℕ) :
    enabledL (xs.map (min · K)) pre = enabledL xs pre := by
  simp only [enabledL, getD_map_min]
  congr 1
  funext i
  simp only [le_min_iff, hK i, and_true]

theorem mem_capVals {K x a b : ℕ} (hx : a ≤ x) (hK : a ≤ K) :
    min (x - a + b) K ∈ capVals K (min x K) a b := by
  unfold capVals
  by_cases h : x < K
  · simp [Nat.min_eq_left h.le, h]
  · have hxK : min x K = K := Nat.min_eq_right (by omega)
    simp only [hxK, Nat.lt_irrefl, ↓reduceIte, List.mem_range'_1]
    omega

theorem mem_absFire {K : ℕ} {pre post : List ℕ} (hK : ∀ j, pre.count j ≤ K) :
    ∀ (i : ℕ) (xs : List ℕ), (∀ k (hk : k < xs.length), pre.count (i + k) ≤ xs[k]) →
      (fireL pre post i xs).map (min · K) ∈ absFire K pre post i (xs.map (min · K)) := by
  intro i xs
  induction xs generalizing i with
  | nil => intro _; simp [fireL, absFire]
  | cons x xs ih =>
    intro hen
    simp only [fireL, List.map_cons, absFire, List.mem_flatMap, List.mem_map, List.cons.injEq]
    refine ⟨_, mem_capVals (hen 0 (by simp)) (hK i), _, ih (i + 1) fun k hk => ?_, rfl, rfl⟩
    have := hen (k + 1) (by simpa using hk)
    simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem capOk_spec {K : ℕ} (h : N.capOk K = true) (t : Fin N.trans.length) (j : ℕ) :
    (N.tr t).pre.count j ≤ K := by
  simp only [capOk, List.all_eq_true, decide_eq_true_eq] at h
  by_cases hj : j ∈ (N.tr t).pre
  · exact h _ (List.getElem_mem _) j hj
  · rw [List.count_eq_zero_of_not_mem hj]; exact Nat.zero_le _

/-- **The counter abstraction over-approximates the net.** -/
theorem abstracts (hwf : N.wf = true) {K : ℕ} (hK : N.capOk K = true) :
    (N.abstr K).Abstracts N.toNet.lts (N.cap K) := by
  have hpre := fun t => ((wf_spec hwf).2 t).1
  refine ⟨fun M t M' ⟨hen, he⟩ => ?_, fun M t a' hm => ?_⟩
  · subst he
    simp only [abstr, absSucc, cap, List.mem_flatMap, List.mem_finRange, true_and]
    refine ⟨t, ?_⟩
    rw [enabledL_map_min (capOk_spec hK t), (enabledL_enc_iff (hpre t)).2 hen]
    simp only [↓reduceIte, List.mem_map, Prod.mk.injEq, true_and, exists_eq_right]
    rw [← fireL_enc]
    refine mem_absFire (capOk_spec hK t) 0 _ fun k hk => ?_
    have hk' : k < N.places := by simpa [enc] using hk
    simpa [enc, toNet] using hen ⟨k, hk'⟩
  · simp only [abstr, absSucc, cap, List.mem_flatMap, List.mem_finRange, true_and] at hm
    obtain ⟨t', hm⟩ := hm
    split_ifs at hm with hen
    · simp only [List.mem_map, Prod.mk.injEq] at hm
      obtain ⟨_, _, rfl, -⟩ := hm
      rw [enabledL_map_min (capOk_spec hK t'), enabledL_enc_iff (hpre t')] at hen
      exact Net.lts_enabled_iff.2 hen
    · cases hm

theorem internalKey_iff (t : Fin N.trans.length) : N.internalKey t.val = true ↔ N.Internal t := by
  simp [internalKey, Internal, tr]

/-- **Deadlock freedom, livelock freedom and liveness of a net from its counter
abstraction.** -/
theorem of_checkAbs {K : ℕ} {dl ll lv : Bool} {c : ExplicitLTS.ACert (List ℕ)}
    (h : N.checkAbs K dl ll lv c = true) :
    (dl = true → N.toNet.lts.DeadlockFree N.M₀) ∧
      (ll = true → N.toNet.lts.LivelockFree N.Internal N.M₀) ∧
      (lv = true → N.toNet.lts.Live N.M₀) := by
  simp only [checkAbs, Bool.and_eq_true] at h
  obtain ⟨⟨hwf, hK⟩, h⟩ := h
  have hinit : N.cap K N.M₀ = N.init.map (min · K) := by rw [cap, enc_M₀ hwf]
  rw [← hinit] at h
  obtain ⟨hd, hl, hv⟩ := ExplicitLTS.of_checkACert Fin.val_injective (abstracts hwf hK) h
  refine ⟨hd, fun hll => ?_, fun hlv t => hv t ?_⟩
  · subst hll
    simp only [↓reduceIte, internalKey_iff] at hl
    exact hl
  · subst hlv
    simp

theorem correct_of_checkAbs {K : ℕ} {c : ExplicitLTS.ACert (List ℕ)}
    (h : N.checkAbs K true true true c = true) : N.Correct :=
  let h := of_checkAbs h
  ⟨h.1 rfl, h.2.1 rfl, h.2.2 rfl⟩

theorem deadlockFree_of_checkAbs {K : ℕ} {c : ExplicitLTS.ACert (List ℕ)}
    (h : N.checkAbs K true false false c = true) : N.toNet.lts.DeadlockFree N.M₀ :=
  (of_checkAbs h).1 rfl

theorem livelockFree_of_checkAbs {K : ℕ} {c : ExplicitLTS.ACert (List ℕ)}
    (h : N.checkAbs K false true false c = true) : N.toNet.lts.LivelockFree N.Internal N.M₀ :=
  (of_checkAbs h).2.1 rfl

theorem live_of_checkAbs {K : ℕ} {c : ExplicitLTS.ACert (List ℕ)}
    (h : N.checkAbs K false false true c = true) : N.toNet.lts.Live N.M₀ :=
  (of_checkAbs h).2.2 rfl

end PNet

end AsyncLean
