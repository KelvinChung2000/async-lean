/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Abstract
import AsyncLean.Checker.BitmapPetri

/-!
# Counter abstractions with linear potentials

The counter abstraction (`AsyncLean.Checker.Abstract`) tracks each place exactly up to a cap
`K` and as "`K` or more" above it.  At the cap, a transition that removes tokens may leave the
abstract marking unchanged, so a rank on abstract markings cannot decrease along it: a buffer
drained by an internal transition is livelock free, yet its abstraction has an internal
self-loop.  Likewise a must-distance cannot decrease along such a step.

A *linear potential* — weights on the places — sees what the cap hides.  Here the ranks and
the must-distances are lexicographic, as in `AsyncLean.Checker.Bitmap`:

* livelock freedom: every internal transition does not increase the rank potential (`wR`),
  and an internal step either strictly decreases it (a transition of `dR`) or decreases the
  abstract rank;
* liveness: a state enables the label, or enables a transition of `dD` (strictly decreasing
  the distance potential `wD`), or enables a transition of `kD` (not increasing it) all of
  whose abstract successors are closer.

The potentials are checked transition by transition (`PNet.checkPot`); the abstraction itself
needs no change.  `PNet.of_checkAbsP` gives the same conclusions as `PNet.of_checkAbs`, on
strictly more nets.
-/

namespace AsyncLean

namespace ExplicitLTS

section AbstractPot

variable {S A L : Type*} [DecidableEq A] (E : ExplicitLTS A L) (cmp : A → A → Ordering)
  (key : L → ℕ)

/-- The checks at one abstract state, with the potentials given by the label sets `dR`
(internal labels decreasing the rank potential), `dD` (labels decreasing the distance
potential) and `kD` (labels not increasing it). -/
def checkNodeAP (dl : Bool) (internal dR dD kD : ℕ → Bool) (labels : List ℕ) (c : ACert A)
    (a : A) : Bool :=
  match c.findData cmp a with
  | none => false
  | some (r, dv, es) =>
    decide (E.keyedSucc key a = es) && (!dl || !es.isEmpty) &&
    (es.all fun e => match c.findData cmp e.2 with
      | none => false
      | some (r', _, _) => !internal e.1 || dR e.1 || decide (r' < r)) &&
    labels.all fun k => es.any (fun e => e.1 == k) || es.any (fun e => dD e.1) ||
      es.any fun e => kD e.1 && es.all fun e' => e'.1 != e.1 || match c.findData cmp e'.2 with
        | none => false
        | some (_, dv', _) => decide (dv'.getD k 0 < dv.getD k 0)

/-- Check an abstraction certificate with potentials (trusted). -/
def checkACertP (dl : Bool) (internal dR dD kD : ℕ → Bool) (labels : List ℕ) (a₀ : A)
    (c : ACert A) : Bool :=
  (c.findData cmp a₀).isSome && c.all fun x => E.checkNodeAP cmp key dl internal dR dD kD labels c x.1

variable {E cmp key}

theorem checkNodeAP_spec {dl : Bool} {internal dR dD kD : ℕ → Bool} {labels : List ℕ}
    {c : ACert A} {a : A} {r : ℕ} {dv : List ℕ} {es : List (ℕ × A)}
    (hf : c.findData cmp a = some (r, dv, es))
    (h : E.checkNodeAP cmp key dl internal dR dD kD labels c a = true) :
    E.keyedSucc key a = es ∧ (dl = true → es ≠ []) ∧
      (∀ e ∈ es, ∃ r' dv' es', c.findData cmp e.2 = some (r', dv', es') ∧
        (internal e.1 = true → dR e.1 = false → r' < r)) ∧
      (∀ k ∈ labels, (∃ e ∈ es, e.1 = k) ∨ (∃ e ∈ es, dD e.1 = true) ∨
        ∃ e ∈ es, kD e.1 = true ∧ ∀ e' ∈ es, e'.1 = e.1 →
        ∃ r' dv' es', c.findData cmp e'.2 = some (r', dv', es') ∧ dv'.getD k 0 < dv.getD k 0) := by
  unfold checkNodeAP at h
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
      refine ⟨r', dv', es', hf', fun hi hd => ?_⟩
      simp only [hi, hd, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
      exact this
  · have := hl k hk
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq, List.all_eq_true,
      Bool.and_eq_true] at this
    rcases this with (h1 | h2) | ⟨e, he, hkd, hall⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · refine Or.inr (Or.inr ⟨e, he, hkd, fun e' he' heq => ?_⟩)
      rcases hall e' he' with h1 | h1
      · simp [heq] at h1
      · split at h1
        · cases h1
        · rename_i r' dv' es' hf'
          exact ⟨r', dv', es', hf', of_decide_eq_true h1⟩

/-- **Soundness of abstraction certificates with potentials.** -/
theorem of_checkACertP (hkey : Function.Injective key) {B : LTS S L} {α : S → A}
    (hab : E.Abstracts B α) {s₀ : S} {dl : Bool} {internal dR dD kD : ℕ → Bool}
    {labels : List ℕ} {c : ACert A} (potR potD : S → ℕ)
    (hR : ∀ s l s', B.step s l s' → internal (key l) = true →
      potR s' ≤ potR s ∧ (dR (key l) = true → potR s' < potR s))
    (hD : ∀ s l s', B.step s l s' → (dD (key l) = true → potD s' < potD s) ∧
      (kD (key l) = true → potD s' ≤ potD s))
    (h : E.checkACertP cmp key dl internal dR dD kD labels (α s₀) c = true) :
    (dl = true → B.DeadlockFree s₀) ∧
      B.LivelockFree (fun l => internal (key l) = true) s₀ ∧
      ∀ l, key l ∈ labels → B.LiveLabel s₀ l := by
  simp only [checkACertP, Bool.and_eq_true] at h
  obtain ⟨h₀, hc⟩ := h
  rw [BTree.all_eq_true] at hc
  have hnode : ∀ a d, c.findData cmp a = some d →
      E.checkNodeAP cmp key dl internal dR dD kD labels c a = true :=
    fun a d hf => hc _ (BTree.mem_toList_of_findData hf)
  have hmem : ∀ {s l s'} {es : List (ℕ × A)}, E.keyedSucc key (α s) = es → B.step s l s' →
      (key l, α s') ∈ es := fun hks hst =>
    hks ▸ List.mem_map_of_mem (f := fun e => (key e.1, e.2)) (hab.sim _ _ _ hst)
  let I : S → Prop := fun s => ∃ d, c.findData cmp (α s) = some d
  have hI₀ : I s₀ := Option.isSome_iff_exists.1 h₀
  have hstep : ∀ s l s', I s → B.step s l s' → I s' := by
    rintro s l s' ⟨⟨r, dv, es⟩, hf⟩ hst
    obtain ⟨hks, -, hsucc, -⟩ := checkNodeAP_spec hf (hnode _ _ hf)
    obtain ⟨r', dv', es', hf', -⟩ := hsucc _ (hmem hks hst)
    exact ⟨_, hf'⟩
  have hkeyed : ∀ {s k a'} {es : List (ℕ × A)}, E.keyedSucc key (α s) = es → (k, a') ∈ es →
      ∃ l, key l = k ∧ (l, a') ∈ E.succ (α s) := by
    intro s k a' es hks he
    rw [← hks, keyedSucc, List.mem_map] at he
    obtain ⟨⟨l, a''⟩, hm, he⟩ := he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨l, rfl, hm⟩
  have hreach : ∀ s, B.Reachable s₀ s → I s := fun s hs => hs.invariant hI₀ hstep
  refine ⟨fun hd => ?_, ?_, fun l hl => ?_⟩
  · refine LTS.DeadlockFree.of_invariant I hI₀ hstep fun s ⟨⟨r, dv, es⟩, hf⟩ => ?_
    obtain ⟨hks, hne, -, -⟩ := checkNodeAP_spec hf (hnode _ _ hf)
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hne hd)
    obtain ⟨l, -, hm⟩ := hkeyed hks he
    obtain ⟨s', hs'⟩ := hab.en _ _ _ hm
    exact ⟨l, s', hs'⟩
  · -- lexicographically: the rank potential, then the abstract rank
    let rk : S → ℕ := fun s => ((c.findData cmp (α s)).map Prod.fst).getD 0
    have key' : ∀ p n s, potR s = p → rk s = n → I s →
        Acc (B.IRel fun l => internal (key l) = true) s := by
      intro p
      induction p using Nat.strong_induction_on with
      | _ p ihp =>
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ihn =>
      intro s hp hn hs
      refine Acc.intro s fun s' ⟨l, hl, hst⟩ => ?_
      have hs' := hstep s l s' hs hst
      obtain ⟨hle, hlt⟩ := hR s l s' hst hl
      cases hd : dR (key l)
      · rcases Nat.lt_or_eq_of_le hle with h' | h'
        · exact ihp _ (hp ▸ h') _ s' rfl rfl hs'
        · obtain ⟨⟨r, dv, es⟩, hf⟩ := hs
          obtain ⟨hks, -, hsucc, -⟩ := checkNodeAP_spec hf (hnode _ _ hf)
          obtain ⟨r', dv', es', hf', hr⟩ := hsucc _ (hmem hks hst)
          have : rk s' < n := by
            rw [← hn]; simp only [rk, hf, hf', Option.map_some, Option.getD_some]
            exact hr hl hd
          exact ihn _ this s' (h'.trans hp) rfl hs'
      · exact ihp _ (hp ▸ hlt hd) _ s' rfl rfl hs'
    exact LTS.livelockFree_iff_acc.2 fun s hs => key' _ _ s rfl rfl (hreach s hs)
  · -- lexicographically: the distance potential, then the must-distance
    let dd : S → ℕ := fun s => ((c.findData cmp (α s)).map fun d => d.2.1.getD (key l) 0).getD 0
    have key' : ∀ p n s, potD s = p → dd s = n → I s → ∃ s', B.Reachable s s' ∧ B.Enabled s' l := by
      intro p
      induction p using Nat.strong_induction_on with
      | _ p ihp =>
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ihn =>
      intro s hp hn hs
      obtain ⟨⟨r, dv, es⟩, hf⟩ := hs
      obtain ⟨hks, -, -, hlive⟩ := checkNodeAP_spec hf (hnode _ _ hf)
      rcases hlive _ hl with ⟨e, he, hk⟩ | ⟨e, he, hdd⟩ | ⟨e, he, hkd, hall⟩
      · obtain ⟨l', hl', hm⟩ := hkeyed hks he
        rw [hk] at hl'
        exact ⟨s, LTS.Reachable.refl s, hkey hl' ▸ hab.en _ _ _ hm⟩
      · obtain ⟨u, hu, hm⟩ := hkeyed hks he
        obtain ⟨s', hs'⟩ := hab.en _ _ _ hm
        have hlt := (hD s u s' hs').1 (by rw [hu]; exact hdd)
        obtain ⟨s'', h1, h2⟩ := ihp _ (hp ▸ hlt) _ s' rfl rfl (hstep s u s' ⟨_, hf⟩ hs')
        exact ⟨s'', LTS.Reachable.head ⟨u, hs'⟩ h1, h2⟩
      · obtain ⟨u, hu, hm⟩ := hkeyed hks he
        obtain ⟨s', hs'⟩ := hab.en _ _ _ hm
        obtain ⟨r', dv', es', hf', hlt⟩ := hall _ (hmem hks hs') hu
        have hle := (hD s u s' hs').2 (by rw [hu]; exact hkd)
        have hsI := hstep s u s' ⟨_, hf⟩ hs'
        rcases Nat.lt_or_eq_of_le hle with h' | h'
        · obtain ⟨s'', h1, h2⟩ := ihp _ (hp ▸ h') _ s' rfl rfl hsI
          exact ⟨s'', LTS.Reachable.head ⟨u, hs'⟩ h1, h2⟩
        · have : dd s' < n := by
            rw [← hn]; simp only [dd, hf, hf', Option.map_some, Option.getD_some]
            exact hlt
          obtain ⟨s'', h1, h2⟩ := ihn _ this s' (h'.trans hp) rfl hsI
          exact ⟨s'', LTS.Reachable.head ⟨u, hs'⟩ h1, h2⟩
    exact fun s hs => key' _ _ s rfl rfl (hreach s hs)

end AbstractPot

/-! ### Untrusted certificate generation -/

section AbstractPotSearch

variable {A L : Type*} [DecidableEq A] (E : ExplicitLTS A L) (cmp : A → A → Ordering)
  (key : L → ℕ)

/-- Must-distances to the label with key `k`, where enabling a transition of `dD` counts as
distance `0` and only transitions of `kD` lead closer. -/
def andDistP (dD kD : ℕ → Bool) (states : List (A × List (ℕ × A))) (k : ℕ) : BTree (A × ℕ) :=
  let layer0 := states.filter fun x => x.2.any fun e => e.1 == k || dD e.1
  let rec go : ℕ → ℕ → BStore (A × ℕ) → BStore (A × ℕ)
    | 0, _, tbl => tbl
    | fuel + 1, j, tbl =>
      let has (a : A) : Bool := (tbl.lookup cmp a).isSome
      let next := states.filter fun x => !has x.1 && x.2.any fun e =>
        kD e.1 && x.2.all fun e' => e'.1 != e.1 || has e'.2
      if next.isEmpty then tbl
      else go fuel (j + 1) (next.foldl (fun tb x => tb.pushKV cmp x.1 (j + 1)) tbl)
  (go states.length 0 (layer0.foldl (fun tb x => tb.pushKV cmp x.1 0) {})).tree.rebalance

/-- Compute an abstraction certificate with potentials (untrusted). -/
def mkACertP (internal dR dD kD : ℕ → Bool) (labels : List ℕ) (fuel : ℕ) (a₀ : A) : ACert A :=
  let t := E.explore cmp fuel a₀
  let states := (t.toListAcc []).map fun a => (a, E.keyedSucc key a)
  let rk := E.autoRank cmp (fun l => internal (key l) && !dR (key l)) t
  let m := labels.foldl max 0 + 1
  let ds := labels.map fun k => (k, andDistP cmp dD kD states k)
  BTree.ofList (states.map fun x => (x.1, (tblFn cmp rk x.1,
    (List.range m).map (fun k => match ds.lookup k with
      | some d => (d.lookup cmp x.1).getD (states.length + 1)
      | none => 0), x.2)))

end AbstractPotSearch

end ExplicitLTS

namespace PNet

variable (N : PNet)

/-- Check an abstraction certificate with the potentials `wR` (ranks: the internal
transitions of `dR` decrease it, the others do not increase it) and `wD` (distances: the
transitions of `dD` decrease it, those of `kD` do not increase it) (trusted). -/
noncomputable def checkAbsP (K : ℕ) (dl ll lv : Bool) (wR : List ℕ) (dR : ℕ) (wD : List ℕ)
    (dD kD : ℕ) (c : ExplicitLTS.ACert (List ℕ)) : Bool :=
  N.wf && N.capOk K && N.checkPot wR dR (cond ll N.imask 0) && N.checkPot wD dD kD &&
    (N.abstr K).checkACertP lexCmp Fin.val dl
      (if ll then N.internalKey else fun _ => false) dR.testBit dD.testBit kD.testBit
      (if lv then List.range N.trans.length else []) (N.init.map (min · K)) c

variable {N}

theorem internalKey_eq_imask (t : Fin N.trans.length) :
    N.internalKey t.val = N.imask.testBit t.val := by
  rw [testBit_imask]; simp [internalKey, tr]

/-- **Deadlock freedom, livelock freedom and liveness of a net from its counter abstraction
with potentials.** -/
theorem of_checkAbsP {K : ℕ} {dl ll lv : Bool} {wR wD : List ℕ} {dR dD kD : ℕ}
    {c : ExplicitLTS.ACert (List ℕ)} (h : N.checkAbsP K dl ll lv wR dR wD dD kD c = true) :
    (dl = true → N.toNet.lts.DeadlockFree N.M₀) ∧
      (ll = true → N.toNet.lts.LivelockFree N.Internal N.M₀) ∧
      (lv = true → N.toNet.lts.Live N.M₀) := by
  simp only [checkAbsP, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hwf, hK⟩, hpR⟩, hpD⟩, h⟩ := h
  have hinit : N.cap K N.M₀ = N.init.map (min · K) := by rw [cap, enc_M₀ hwf]
  rw [← hinit] at h
  obtain ⟨hd, hl, hv⟩ := ExplicitLTS.of_checkACertP Fin.val_injective (abstracts hwf hK)
    (N.pot wR) (N.pot wD)
    (fun M t M' hst hi => by
      have hi' : (cond ll N.imask 0).testBit t.val = true := by
        cases ll
        · simp at hi
        · rw [Bool.cond_true, ← internalKey_eq_imask]; simpa using hi
      have h := pot_step hwf hpR hst
      exact ⟨h.2 hi', h.1⟩)
    (fun M t M' hst => pot_step hwf hpD hst) h
  refine ⟨hd, fun hll => ?_, fun hlv t => hv t ?_⟩
  · subst hll
    simp only [↓reduceIte, internalKey_iff] at hl
    exact hl
  · subst hlv
    simp

theorem correct_of_checkAbsP {K : ℕ} {wR wD : List ℕ} {dR dD kD : ℕ}
    {c : ExplicitLTS.ACert (List ℕ)} (h : N.checkAbsP K true true true wR dR wD dD kD c = true) :
    N.Correct :=
  let h := of_checkAbsP h
  ⟨h.1 rfl, h.2.1 rfl, h.2.2 rfl⟩

theorem deadlockFree_of_checkAbsP {K : ℕ} {wR wD : List ℕ} {dR dD kD : ℕ}
    {c : ExplicitLTS.ACert (List ℕ)} (h : N.checkAbsP K true false false wR dR wD dD kD c = true) :
    N.toNet.lts.DeadlockFree N.M₀ :=
  (of_checkAbsP h).1 rfl

theorem livelockFree_of_checkAbsP {K : ℕ} {wR wD : List ℕ} {dR dD kD : ℕ}
    {c : ExplicitLTS.ACert (List ℕ)} (h : N.checkAbsP K false true false wR dR wD dD kD c = true) :
    N.toNet.lts.LivelockFree N.Internal N.M₀ :=
  (of_checkAbsP h).2.1 rfl

theorem live_of_checkAbsP {K : ℕ} {wR wD : List ℕ} {dR dD kD : ℕ}
    {c : ExplicitLTS.ACert (List ℕ)} (h : N.checkAbsP K false false true wR dR wD dD kD c = true) :
    N.toNet.lts.Live N.M₀ :=
  (of_checkAbsP h).2.2 rfl

end PNet

end AsyncLean
