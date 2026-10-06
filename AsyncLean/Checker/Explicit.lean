/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties
import AsyncLean.Checker.BTree

/-!
# A verified, certificate-checking model checker for finite-state systems

For a concrete design whose reachable state space is finite (a bounded Petri net, a
signal transition graph, a gate-level circuit, …) the properties of
`AsyncLean.LTS.Properties` can be established *by computation inside the Lean kernel*.

The design follows the "untrusted search, trusted check" principle:

1. An **untrusted** exploration (`explore`) enumerates candidate states, and untrusted
   heuristics compute ranking functions (`autoRank`) and distance functions (`autoDist`).
   None of these functions is verified — they need not be.
2. A small **trusted checker** (`closedB`, `noDeadlockB`, `rankDecreasesB`, `progressB`)
   validates the resulting *certificate*: a finite set of states (stored in a binary tree,
   `AsyncLean.BTree`) that contains the initial state and is closed under successors,
   together with ranking / distance functions.  Its soundness theorems
   (`deadlockFree_of_check`, `livelockFree_of_check`, `live_of_check`) are proved once and
   for all, so a successful check *is* a proof.

Checks are run with `decide +kernel` (or `decide`), which uses only the Lean kernel's
definitional evaluation — no `native_decide`, hence no `Lean.ofReduceBool` axiom.

If a check returns `false` nothing is proved: either the property fails, or the fuel was
too small.  Use the refutation rules of `AsyncLean.LTS.Properties` (counterexample traces)
to prove the negation.
-/

namespace AsyncLean

/-- An LTS given by an explicit, computable successor function. -/
structure ExplicitLTS (S L : Type*) where
  /-- All labelled successors of a state. -/
  succ : S → List (L × S)

namespace ExplicitLTS

variable {S L : Type*} (E : ExplicitLTS S L)

/-- The semantics of an explicit LTS. -/
def toLTS : LTS S L where
  step s l s' := (l, s') ∈ E.succ s

section Checker

variable [DecidableEq S] (cmp : S → S → Ordering)

/-! ### The trusted checker

A certificate is a tree `t` of states.  The invariant it certifies is membership in
`t.toList`; `cmp` only guides the search (any function is sound). -/

/-- `t` is closed under successors. -/
def closedB (t : BTree S) : Bool :=
  t.all fun s => (E.succ s).all fun e => t.find cmp e.2

/-- No state of `t` is a deadlock. -/
def noDeadlockB (t : BTree S) : Bool :=
  t.all fun s => !(E.succ s).isEmpty

/-- `rank` strictly decreases along every internal step out of `t`. -/
def rankDecreasesB (internal : L → Bool) (rank : S → ℕ) (t : BTree S) : Bool :=
  t.all fun s => (E.succ s).all fun e => !internal e.1 || decide (rank e.2 < rank s)

/-- `l` is enabled in `s`. -/
def enabledB [DecidableEq L] (s : S) (l : L) : Bool :=
  (E.succ s).any fun e => decide (e.1 = l)

/-- From every state of `t`, either `l` is enabled or some step decreases `d`. -/
def progressB [DecidableEq L] (l : L) (d : S → ℕ) (t : BTree S) : Bool :=
  t.all fun s => E.enabledB s l || (E.succ s).any fun e => decide (d e.2 < d s)

/-- No step out of `t` disables a different enabled label. -/
def persistentB [DecidableEq L] (t : BTree S) : Bool :=
  t.all fun s => (E.succ s).all fun e => (E.succ s).all fun e' =>
    decide (e.1 = e'.1) || E.enabledB e'.2 e.1

/-! ### Soundness of the checker -/

variable {E} {cmp}

theorem mem_of_reachable {t : BTree S} {s₀ s : S} (h₀ : s₀ ∈ t.toList)
    (hc : E.closedB cmp t = true) (hr : E.toLTS.Reachable s₀ s) : s ∈ t.toList := by
  refine hr.invariant h₀ fun s l s' hs hst => ?_
  simp only [closedB, BTree.all_eq_true, List.all_eq_true] at hc
  exact BTree.mem_toList_of_find (hc s hs (l, s') hst)

theorem step_mem {t : BTree S} (hc : E.closedB cmp t = true) {s s' : S} {l : L}
    (hs : s ∈ t.toList) (hst : E.toLTS.step s l s') : s' ∈ t.toList :=
  mem_of_reachable hs hc (LTS.Reachable.of_step hst)

theorem deadlockFree_of_check {t : BTree S} {s₀ : S} (h₀ : t.find cmp s₀ = true)
    (hc : E.closedB cmp t = true) (hd : E.noDeadlockB t = true) :
    E.toLTS.DeadlockFree s₀ := by
  refine LTS.DeadlockFree.of_invariant (· ∈ t.toList) (BTree.mem_toList_of_find h₀)
    (fun s l s' hs hst => step_mem hc hs hst) fun s hs => ?_
  simp only [noDeadlockB, BTree.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_eq_false_iff] at hd
  obtain ⟨⟨l, s'⟩, hmem⟩ := List.exists_mem_of_ne_nil _ (hd s hs)
  exact ⟨l, s', hmem⟩

theorem livelockFree_of_check {t : BTree S} {s₀ : S} {internal : L → Bool} {rank : S → ℕ}
    (h₀ : t.find cmp s₀ = true) (hc : E.closedB cmp t = true)
    (hr : E.rankDecreasesB internal rank t = true) :
    E.toLTS.LivelockFree (fun l => internal l = true) s₀ := by
  refine LTS.LivelockFree.of_ranking (· ∈ t.toList) (BTree.mem_toList_of_find h₀)
    (fun s l s' hs hst => step_mem hc hs hst) rank fun s l s' hs hl hst => ?_
  simp only [rankDecreasesB, BTree.all_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hr
  rcases hr s hs (l, s') hst with h | h
  · simp [h] at hl
  · exact h

omit [DecidableEq S] in
theorem enabledB_iff [DecidableEq L] {s : S} {l : L} :
    E.enabledB s l = true ↔ E.toLTS.Enabled s l := by
  simp only [enabledB, List.any_eq_true, decide_eq_true_eq, LTS.Enabled, toLTS]
  constructor
  · rintro ⟨⟨l', s'⟩, hmem, rfl⟩; exact ⟨s', hmem⟩
  · rintro ⟨s', hmem⟩; exact ⟨(l, s'), hmem, rfl⟩

theorem liveLabel_of_check [DecidableEq L] {t : BTree S} {s₀ : S} {l : L} {d : S → ℕ}
    (h₀ : t.find cmp s₀ = true) (hc : E.closedB cmp t = true)
    (hp : E.progressB l d t = true) : E.toLTS.LiveLabel s₀ l := by
  refine LTS.LiveLabel.of_ranking (· ∈ t.toList) (BTree.mem_toList_of_find h₀)
    (fun s l s' hs hst => step_mem hc hs hst) l d fun s hs => ?_
  simp only [progressB, BTree.all_eq_true, Bool.or_eq_true, List.any_eq_true,
    decide_eq_true_eq] at hp
  rcases hp s hs with h | ⟨⟨l', s'⟩, hmem, hlt⟩
  · exact Or.inl (enabledB_iff.1 h)
  · exact Or.inr ⟨l', s', hmem, hlt⟩

theorem persistent_of_check [DecidableEq L] {t : BTree S} {s₀ : S}
    (h₀ : t.find cmp s₀ = true) (hc : E.closedB cmp t = true)
    (hp : E.persistentB t = true) : E.toLTS.Persistent s₀ := by
  intro s hs l l' s' hne hen hst
  have hmem := mem_of_reachable (BTree.mem_toList_of_find h₀) hc hs
  obtain ⟨s₁, h₁⟩ := hen
  simp only [persistentB, BTree.all_eq_true, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hp
  rcases hp s hmem (l, s₁) h₁ (l', s') hst with h | h
  · exact absurd h hne
  · exact enabledB_iff.1 h

end Checker

/-! ### Untrusted certificate generation

Nothing below needs to be correct for the results to be sound; a wrong answer merely makes
the check fail. -/

section Search

variable [DecidableEq S] (cmp : S → S → Ordering)

/-- Depth-first exploration; `fuel` bounds the number of expanded states. -/
def exploreAux : ℕ → List S → BStore S → BStore S
  | 0, _, visited => visited
  | _ + 1, [], visited => visited
  | fuel + 1, s :: stack, visited =>
    let r := (E.succ s).foldl
      (fun (acc : List S × BStore S) e =>
        if acc.2.find cmp e.2 then acc else (e.2 :: acc.1, acc.2.push cmp e.2))
      (stack, visited)
    exploreAux fuel r.1 r.2

/-- Candidate reachable state space from `s₀`, as a balanced search tree. -/
def explore (fuel : ℕ) (s₀ : S) : BTree S :=
  (E.exploreAux cmp fuel [s₀] (({} : BStore S).push cmp s₀)).tree.rebalance

/-- Longest internal path from `s` (memoised depth-first search, bounded by `fuel`). -/
def heightAux (internal : L → Bool) : ℕ → BStore (S × ℕ) → S → ℕ × BStore (S × ℕ)
  | 0, memo, _ => (0, memo)
  | fuel + 1, memo, s =>
    match memo.lookup cmp s with
    | some h => (h, memo)
    | none =>
      let r := (E.succ s).foldl
        (fun (acc : ℕ × BStore (S × ℕ)) e =>
          if internal e.1 then
            let r' := heightAux internal fuel acc.2 e.2
            (max acc.1 (r'.1 + 1), r'.2)
          else acc)
        (0, memo)
      (r.1, r.2.pushKV cmp s r.1)

/-- Candidate ranking function for livelock freedom: the length of the longest internal
path from each state, as a lookup tree. -/
def autoRank (internal : L → Bool) (t : BTree S) : BTree (S × ℕ) :=
  let states := t.toListAcc []
  (states.foldl (fun memo s => (E.heightAux cmp internal (states.length + 1) memo s).2)
    ({} : BStore (S × ℕ))).tree.rebalance

/-- Backward breadth-first layering of `states` by distance to a state enabling `l`. -/
def distAux (states : List S) : ℕ → ℕ → BStore (S × ℕ) → BTree S → BStore (S × ℕ)
  | 0, _, tbl, _ => tbl
  | fuel + 1, k, tbl, layer =>
    let next := states.filter fun s =>
      (tbl.lookup cmp s).isNone && (E.succ s).any fun e => layer.find cmp e.2
    if next.isEmpty then tbl
    else distAux states fuel (k + 1)
      (next.foldl (fun tb s => tb.pushKV cmp s (k + 1)) tbl) (BTree.ofList next)

/-- Candidate distance function for liveness of `l`, as a lookup tree. -/
def autoDist [DecidableEq L] (l : L) (t : BTree S) : BTree (S × ℕ) :=
  let states := t.toListAcc []
  let layer0 := states.filter fun s => E.enabledB s l
  (E.distAux cmp states states.length 0
    (layer0.foldl (fun tb s => tb.pushKV cmp s 0) {}) (BTree.ofList layer0)).tree.rebalance

end Search

/-- Read a lookup tree as a function (missing entries map to `0`). -/
def tblFn (cmp : S → S → Ordering) (tbl : BTree (S × ℕ)) (s : S) : ℕ :=
  (tbl.lookup cmp s).getD 0

/-! ### One-shot checks

These combine the untrusted search with the trusted checker; a `true` result is turned into
a proof by the corresponding `of_check*` theorem. -/

section OneShot

variable [DecidableEq S] (cmp : S → S → Ordering)

/-- Explore from `s₀` and check deadlock freedom. -/
def checkDeadlockFree (fuel : ℕ) (s₀ : S) : Bool :=
  let t := E.explore cmp fuel s₀
  t.find cmp s₀ && E.closedB cmp t && E.noDeadlockB t

/-- Explore from `s₀` and check livelock freedom with an automatically computed ranking. -/
def checkLivelockFree (internal : L → Bool) (fuel : ℕ) (s₀ : S) : Bool :=
  let t := E.explore cmp fuel s₀
  t.find cmp s₀ && E.closedB cmp t &&
    E.rankDecreasesB internal (tblFn cmp (E.autoRank cmp internal t)) t

/-- Explore from `s₀` and check liveness of all the given labels. -/
def checkLive [DecidableEq L] (labels : List L) (fuel : ℕ) (s₀ : S) : Bool :=
  let t := E.explore cmp fuel s₀
  t.find cmp s₀ && E.closedB cmp t &&
    labels.all fun l => E.progressB l (tblFn cmp (E.autoDist cmp l t)) t

/-- Explore once and check deadlock freedom, livelock freedom and liveness together. -/
def checkAll [DecidableEq L] (internal : L → Bool) (labels : List L) (fuel : ℕ) (s₀ : S) :
    Bool :=
  let t := E.explore cmp fuel s₀
  t.find cmp s₀ && E.closedB cmp t && E.noDeadlockB t &&
    E.rankDecreasesB internal (tblFn cmp (E.autoRank cmp internal t)) t &&
    labels.all fun l => E.progressB l (tblFn cmp (E.autoDist cmp l t)) t

/-- Explore from `s₀` and check persistence (speed independence / hazard freedom). -/
def checkPersistent [DecidableEq L] (fuel : ℕ) (s₀ : S) : Bool :=
  let t := E.explore cmp fuel s₀
  t.find cmp s₀ && E.closedB cmp t && E.persistentB t

variable {E} {cmp}

theorem persistent_of_checkPersistent [DecidableEq L] {fuel : ℕ} {s₀ : S}
    (h : E.checkPersistent cmp fuel s₀ = true) : E.toLTS.Persistent s₀ := by
  simp only [checkPersistent, Bool.and_eq_true] at h
  exact persistent_of_check h.1.1 h.1.2 h.2

theorem deadlockFree_of_checkDeadlockFree {fuel : ℕ} {s₀ : S}
    (h : E.checkDeadlockFree cmp fuel s₀ = true) : E.toLTS.DeadlockFree s₀ := by
  simp only [checkDeadlockFree, Bool.and_eq_true] at h
  exact deadlockFree_of_check h.1.1 h.1.2 h.2

theorem livelockFree_of_checkLivelockFree {internal : L → Bool} {fuel : ℕ} {s₀ : S}
    (h : E.checkLivelockFree cmp internal fuel s₀ = true) :
    E.toLTS.LivelockFree (fun l => internal l = true) s₀ := by
  simp only [checkLivelockFree, Bool.and_eq_true] at h
  exact livelockFree_of_check h.1.1 h.1.2 h.2

theorem live_of_checkLive [DecidableEq L] {labels : List L} (hl : ∀ l, l ∈ labels)
    {fuel : ℕ} {s₀ : S} (h : E.checkLive cmp labels fuel s₀ = true) : E.toLTS.Live s₀ := by
  simp only [checkLive, Bool.and_eq_true, List.all_eq_true] at h
  exact fun l => liveLabel_of_check h.1.1 h.1.2 (h.2 l (hl l))

/-- The combined check proves all three properties at once. -/
theorem of_checkAll [DecidableEq L] {internal : L → Bool} {labels : List L}
    (hl : ∀ l, l ∈ labels) {fuel : ℕ} {s₀ : S}
    (h : E.checkAll cmp internal labels fuel s₀ = true) :
    E.toLTS.DeadlockFree s₀ ∧ E.toLTS.LivelockFree (fun l => internal l = true) s₀ ∧
      E.toLTS.Live s₀ := by
  simp only [checkAll, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h₀, hc⟩, hd⟩, hr⟩, hp⟩ := h
  exact ⟨deadlockFree_of_check h₀ hc hd, livelockFree_of_check h₀ hc hr,
    fun l => liveLabel_of_check h₀ hc (hp l (hl l))⟩

end OneShot

/-! ### Certificates as data

For larger systems it is much faster to compute the certificate *outside* the kernel (in
compiled code, at elaboration time) and to hand it to the kernel as a literal term: the kernel
then only runs the trusted checker.  A `Cert` is a search tree mapping every candidate state
to its rank (for livelock freedom) and its distance to each label (for liveness); `mkCert`
computes it (untrusted) and `checkCert` validates it in a single pass with one lookup per
transition (trusted, `of_checkCert`).  The `async_decide` tactic automates this. -/

/-- A certificate: each state with its rank, its distances to the labels, and (as literal
data, so that the kernel does not recompute them during lookups) its successor states in the
order produced by `succ`. -/
abbrev Cert (S : Type*) := BTree (S × (ℕ × List ℕ × List S))

section CertSection

variable [DecidableEq S] [DecidableEq L] (cmp : S → S → Ordering)

/-- Compute a certificate (untrusted). -/
def mkCert (internal : L → Bool) (labels : List L) (fuel : ℕ) (s₀ : S) : Cert S :=
  let t := E.explore cmp fuel s₀
  let rk := E.autoRank cmp internal t
  let ds := labels.map fun l => E.autoDist cmp l t
  BTree.ofList ((t.toListAcc []).map fun s =>
    (s, (tblFn cmp rk s, ds.map (fun d => tblFn cmp d s), (E.succ s).map Prod.snd)))

/-- The checks performed at one state of the certificate. -/
def checkNode (internal : L → Bool) (labels : List L) (c : Cert S) (s : S) : Bool :=
  match c.findData cmp s with
  | none => false
  | some (r, dv, ss) =>
    let es := E.succ s
    let ds := ((es.map Prod.fst).zip ss).map fun e => (e.1, c.findData cmp e.2)
    decide (es.map Prod.snd = ss) && !ss.isEmpty &&
    (ds.all fun p => match p.2 with
      | none => false
      | some (r', _, _) => !internal p.1 || decide (r' < r)) &&
    ((labels.zip (List.range labels.length)).all fun li => E.enabledB s li.1 ||
      ds.any fun p => match p.2 with
        | none => false
        | some (_, dv', _) => decide (dv'.getD li.2 0 < dv.getD li.2 0))

/-- Check a certificate (trusted). -/
def checkCert (internal : L → Bool) (labels : List L) (s₀ : S) (c : Cert S) : Bool :=
  (c.findData cmp s₀).isSome && c.all fun x => E.checkNode cmp internal labels c x.1

/-- The persistence checks at one state of the certificate. -/
def checkNodePersistent (c : Cert S) (s : S) : Bool :=
  match c.findData cmp s with
  | none => false
  | some (_, _, ss) =>
    let es := E.succ s
    let es' := (es.map Prod.fst).zip ss
    decide (es.map Prod.snd = ss) && (ss.all fun s' => (c.findData cmp s').isSome) &&
      es.all fun e => es'.all fun e' => decide (e.1 = e'.1) || E.enabledB e'.2 e.1

/-- Check a certificate for persistence (trusted). -/
def checkCertPersistent (s₀ : S) (c : Cert S) : Bool :=
  (c.findData cmp s₀).isSome && c.all fun x => E.checkNodePersistent cmp c x.1

variable {E} {cmp}

/-- The states of a certificate. -/
def Cert.Mem (c : Cert S) (s : S) : Prop := ∃ b, (s, b) ∈ c.toList

omit [DecidableEq S] [DecidableEq L] in
theorem zip_map_fst_snd {α β : Type*} (l : List (α × β)) :
    (l.map Prod.fst).zip (l.map Prod.snd) = l := by
  induction l with
  | nil => rfl
  | cons y l ih => simp [ih]

theorem Cert.mem_of_findData {c : Cert S} {s : S} {b : ℕ × List ℕ × List S}
    (h : c.findData cmp s = some b) : c.Mem s :=
  ⟨b, BTree.mem_toList_of_findData h⟩

theorem Cert.mem_of_isSome {c : Cert S} {s : S} (h : (c.findData cmp s).isSome = true) :
    c.Mem s := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
  exact Cert.mem_of_findData hb

/-- Unpack the checks at a state of the certificate. -/
theorem checkNode_spec {internal : L → Bool} {labels : List L} {c : Cert S} {s : S}
    (h : E.checkNode cmp internal labels c s = true) :
    ∃ r dv, (∃ ss, c.findData cmp s = some (r, dv, ss)) ∧ (E.succ s ≠ []) ∧
      (∀ l s', (l, s') ∈ E.succ s → ∃ r' dv' ss', c.findData cmp s' = some (r', dv', ss') ∧
        (internal l = true → r' < r)) ∧
      (∀ l i, (l, i) ∈ labels.zip (List.range labels.length) → E.enabledB s l = true ∨
        ∃ l' s' r' dv' ss', (l', s') ∈ E.succ s ∧ c.findData cmp s' = some (r', dv', ss') ∧
          dv'.getD i 0 < dv.getD i 0) := by
  unfold checkNode at h
  split at h
  · cases h
  · rename_i r dv ss hfind
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.isEmpty_eq_false_iff, List.all_eq_true, List.any_eq_true, List.mem_map,
      Bool.or_eq_true] at h
    obtain ⟨⟨⟨hss, hne⟩, hr⟩, hp⟩ := h
    subst hss
    refine ⟨r, dv, ⟨_, hfind⟩, fun h => hne (by simp [h]), ?_, ?_⟩
    · intro l s' hmem
      have := hr _ ⟨(l, s'), by rw [zip_map_fst_snd]; exact hmem, rfl⟩
      split at this
      · cases this
      · rename_i r' dv' ss' hf
        refine ⟨r', dv', ss', hf, fun hl => ?_⟩
        simp only [hl, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
        exact this
    · intro l i hli
      rcases hp _ hli with h | ⟨p, ⟨e, he, rfl⟩, hlt⟩
      · exact Or.inl h
      · right
        split at hlt
        · cases hlt
        · rename_i r' dv' ss' hf
          have he' : e ∈ E.succ s := by
            rw [zip_map_fst_snd] at he
            exact he
          exact ⟨e.1, e.2, r', dv', ss', he', hf, of_decide_eq_true hlt⟩

theorem mem_of_reachable_cert {internal : L → Bool} {labels : List L} {c : Cert S} {s₀ s : S}
    (h₀ : c.Mem s₀) (hc : c.all (fun x => E.checkNode cmp internal labels c x.1) = true)
    (hr : E.toLTS.Reachable s₀ s) : c.Mem s := by
  refine hr.invariant h₀ fun s l s' ⟨b, hs⟩ hst => ?_
  rw [BTree.all_eq_true] at hc
  obtain ⟨_, _, _, _, hsucc, _⟩ := checkNode_spec (hc _ hs)
  obtain ⟨r', dv', ss', hf, -⟩ := hsucc l s' hst
  exact Cert.mem_of_findData hf

theorem of_checkCert {internal : L → Bool} {labels : List L} (hl : ∀ l, l ∈ labels) {s₀ : S}
    {c : Cert S} (h : E.checkCert cmp internal labels s₀ c = true) :
    E.toLTS.DeadlockFree s₀ ∧ E.toLTS.LivelockFree (fun l => internal l = true) s₀ ∧
      E.toLTS.Live s₀ := by
  simp only [checkCert, Bool.and_eq_true] at h
  obtain ⟨h₀, hc⟩ := h
  have hmem₀ := Cert.mem_of_isSome h₀
  have hnode : ∀ s, c.Mem s → E.checkNode cmp internal labels c s = true :=
    fun s ⟨b, hs⟩ => (BTree.all_eq_true.1 hc) _ hs
  have hstep : ∀ s l s', c.Mem s → E.toLTS.step s l s' → c.Mem s' := fun s l s' hs hst =>
    mem_of_reachable_cert hs hc (LTS.Reachable.of_step hst)
  refine ⟨?_, ?_, ?_⟩
  · refine LTS.DeadlockFree.of_invariant c.Mem hmem₀ hstep fun s hs => ?_
    obtain ⟨_, _, _, hne, _⟩ := checkNode_spec (hnode s hs)
    obtain ⟨⟨l, s'⟩, hmem⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨l, s', hmem⟩
  · refine LTS.LivelockFree.of_ranking c.Mem hmem₀ hstep
      (fun s => ((c.findData cmp s).map Prod.fst).getD 0) fun s l s' hs hl hst => ?_
    obtain ⟨r, dv, ⟨ss, hf⟩, -, hsucc, -⟩ := checkNode_spec (hnode s hs)
    obtain ⟨r', dv', ss', hf', hlt⟩ := hsucc l s' hst
    simp only [hf, hf', Option.map_some, Option.getD_some]
    exact hlt hl
  · intro l
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hl l)
    have hli : (labels[i], i) ∈ labels.zip (List.range labels.length) := by
      have hi' : i < (labels.zip (List.range labels.length)).length := by
        simp [List.length_zip, hi]
      have := List.getElem_mem hi'
      rwa [List.getElem_zip, List.getElem_range] at this
    refine LTS.LiveLabel.of_ranking c.Mem hmem₀ hstep labels[i]
      (fun s => ((c.findData cmp s).map fun b => b.2.1.getD i 0).getD 0) fun s hs => ?_
    obtain ⟨r, dv, ⟨ss, hf⟩, -, -, hprog⟩ := checkNode_spec (hnode s hs)
    rcases hprog _ _ hli with h | ⟨l', s', r', dv', ss', hmem, hf', hlt⟩
    · exact Or.inl (enabledB_iff.1 h)
    · refine Or.inr ⟨l', s', hmem, ?_⟩
      simp only [hf, hf', Option.map_some, Option.getD_some]
      exact hlt

/-- Deadlock and livelock freedom from a certificate, without liveness (no label enumeration
is needed: pass `[]` as the label list). -/
theorem dfLf_of_checkCert {internal : L → Bool} {labels : List L} {s₀ : S} {c : Cert S}
    (h : E.checkCert cmp internal labels s₀ c = true) :
    E.toLTS.DeadlockFree s₀ ∧ E.toLTS.LivelockFree (fun l => internal l = true) s₀ := by
  simp only [checkCert, Bool.and_eq_true] at h
  obtain ⟨h₀, hc⟩ := h
  have hmem₀ := Cert.mem_of_isSome h₀
  have hnode : ∀ s, c.Mem s → E.checkNode cmp internal labels c s = true :=
    fun s ⟨b, hs⟩ => (BTree.all_eq_true.1 hc) _ hs
  have hstep : ∀ s l s', c.Mem s → E.toLTS.step s l s' → c.Mem s' := fun s l s' hs hst =>
    mem_of_reachable_cert hs hc (LTS.Reachable.of_step hst)
  refine ⟨?_, ?_⟩
  · refine LTS.DeadlockFree.of_invariant c.Mem hmem₀ hstep fun s hs => ?_
    obtain ⟨_, _, _, hne, _⟩ := checkNode_spec (hnode s hs)
    obtain ⟨⟨l, s'⟩, hmem⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨l, s', hmem⟩
  · refine LTS.LivelockFree.of_ranking c.Mem hmem₀ hstep
      (fun s => ((c.findData cmp s).map Prod.fst).getD 0) fun s l s' hs hl hst => ?_
    obtain ⟨r, dv, ⟨ss, hf⟩, -, hsucc, -⟩ := checkNode_spec (hnode s hs)
    obtain ⟨r', dv', ss', hf', hlt⟩ := hsucc l s' hst
    simp only [hf, hf', Option.map_some, Option.getD_some]
    exact hlt hl

theorem persistent_of_checkCert {s₀ : S} {c : Cert S}
    (h : E.checkCertPersistent cmp s₀ c = true) : E.toLTS.Persistent s₀ := by
  simp only [checkCertPersistent, Bool.and_eq_true] at h
  obtain ⟨h₀, hc⟩ := h
  rw [BTree.all_eq_true] at hc
  have hnode : ∀ s, c.Mem s → E.checkNodePersistent cmp c s = true :=
    fun s ⟨b, hs⟩ => hc _ hs
  have hspec : ∀ s, c.Mem s → (∀ l s', (l, s') ∈ E.succ s → c.Mem s') ∧
      ∀ e ∈ E.succ s, ∀ e' ∈ E.succ s, e.1 = e'.1 ∨ E.enabledB e'.2 e.1 = true := by
    intro s hs
    have := hnode s hs
    unfold checkNodePersistent at this
    split at this
    · cases this
    · rename_i ss _
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at this
      obtain ⟨⟨hss, hmem⟩, hp⟩ := this
      subst hss
      rw [zip_map_fst_snd] at hp
      refine ⟨fun l s' hst => Cert.mem_of_isSome (hmem s' (List.mem_map_of_mem hst)), hp⟩
  have hstep : ∀ s l s', c.Mem s → E.toLTS.step s l s' → c.Mem s' :=
    fun s l s' hs hst => (hspec s hs).1 l s' hst
  intro s hs l l' s' hne hen hst
  have hmem := hs.invariant (Cert.mem_of_isSome h₀) hstep
  obtain ⟨s₁, h₁⟩ := hen
  rcases (hspec s hmem).2 (l, s₁) h₁ (l', s') hst with h | h
  · exact absurd h hne
  · exact enabledB_iff.1 h

end CertSection

/-! ### Home-state certificates

For systems that can always return to their initial state (a *home state*), liveness has a
much smaller certificate: one distance per state, towards the initial state, and for each
label one trace from the initial state to a state enabling it. -/

/-- A home-state certificate: each state with its rank, its distance to the initial state and
its successors (literal); and, for each label, a trace of states from the initial state. -/
abbrev HomeCert (S : Type*) := BTree (S × (ℕ × ℕ × List S)) × List (List S)

section HomeSection

variable [DecidableEq S] [DecidableEq L] (cmp : S → S → Ordering)

/-- Follow a trace of states, each a successor of the previous one. -/
def followStates : S → List S → Option S
  | s, [] => some s
  | s, s' :: rest => if (E.succ s).any (fun e => decide (e.2 = s')) then followStates s' rest
    else none

/-- The checks at one state of a home-state certificate. -/
def checkNodeHome (internal : L → Bool) (c : BTree (S × (ℕ × ℕ × List S))) (s₀ s : S) : Bool :=
  match c.findData cmp s with
  | none => false
  | some (r, d, ss) =>
    let es := E.succ s
    let ds := ((es.map Prod.fst).zip ss).map fun e => (e.1, c.findData cmp e.2)
    decide (es.map Prod.snd = ss) && !ss.isEmpty &&
    (ds.all fun p => match p.2 with
      | none => false
      | some (r', _, _) => !internal p.1 || decide (r' < r)) &&
    (decide (s = s₀) || ds.any fun p => match p.2 with
      | some (_, d', _) => decide (d' < d)
      | none => false)

/-- Check a home-state certificate (trusted). -/
def checkCertHome (internal : L → Bool) (labels : List L) (s₀ : S) (c : HomeCert S) : Bool :=
  (c.1.findData cmp s₀).isSome && c.1.all (fun x => E.checkNodeHome cmp internal c.1 s₀ x.1) &&
    (labels.length == c.2.length) &&
    (labels.zip c.2).all fun lt => match E.followStates s₀ lt.2 with
      | some s => E.enabledB s lt.1
      | none => false

variable {E} {cmp}

omit [DecidableEq L] in
theorem reachable_of_followStates {s s' : S} {tr : List S} (h : E.followStates s tr = some s') :
    E.toLTS.Reachable s s' := by
  induction tr generalizing s with
  | nil => cases h; exact LTS.Reachable.refl _
  | cons x rest ih =>
    simp only [followStates] at h
    split_ifs at h with hany
    simp only [List.any_eq_true, decide_eq_true_eq] at hany
    obtain ⟨⟨l, y⟩, hmem, rfl⟩ := hany
    exact LTS.Reachable.head ⟨l, hmem⟩ (ih h)

omit [DecidableEq L] in
theorem checkNodeHome_spec {internal : L → Bool} {c : BTree (S × (ℕ × ℕ × List S))} {s₀ s : S}
    (h : E.checkNodeHome cmp internal c s₀ s = true) :
    ∃ r d, (∃ ss, c.findData cmp s = some (r, d, ss)) ∧ E.succ s ≠ [] ∧
      (∀ l s', (l, s') ∈ E.succ s → ∃ r' d' ss', c.findData cmp s' = some (r', d', ss') ∧
        (internal l = true → r' < r)) ∧
      (s = s₀ ∨ ∃ l s' r' d' ss', (l, s') ∈ E.succ s ∧ c.findData cmp s' = some (r', d', ss') ∧
        d' < d) := by
  unfold checkNodeHome at h
  split at h
  · cases h
  · rename_i r d ss hfind
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.isEmpty_eq_false_iff, List.all_eq_true, List.any_eq_true, List.mem_map,
      Bool.or_eq_true] at h
    obtain ⟨⟨⟨hss, hne⟩, hr⟩, hd⟩ := h
    subst hss
    refine ⟨r, d, ⟨_, hfind⟩, fun h => hne (by simp [h]), ?_, ?_⟩
    · intro l s' hmem
      have := hr _ ⟨(l, s'), by rw [zip_map_fst_snd]; exact hmem, rfl⟩
      split at this
      · cases this
      · rename_i r' d' ss' hf
        refine ⟨r', d', ss', hf, fun hl => ?_⟩
        simp only [hl, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
        exact this
    · rcases hd with h | ⟨p, ⟨e, he, rfl⟩, hlt⟩
      · exact Or.inl h
      · right
        split at hlt
        · rename_i r' d' ss' hf
          rw [zip_map_fst_snd] at he
          exact ⟨e.1, e.2, r', d', ss', he, hf, of_decide_eq_true hlt⟩
        · cases hlt

/-- **Soundness of home-state certificates.** -/
theorem of_checkCertHome {internal : L → Bool} {labels : List L} (hl : ∀ l, l ∈ labels)
    {s₀ : S} {c : HomeCert S} (h : E.checkCertHome cmp internal labels s₀ c = true) :
    E.toLTS.DeadlockFree s₀ ∧ E.toLTS.LivelockFree (fun l => internal l = true) s₀ ∧
      E.toLTS.Live s₀ := by
  simp only [checkCertHome, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    BTree.all_eq_true] at h
  obtain ⟨⟨⟨h₀, hc⟩, hlen⟩, htr⟩ := h
  let Mem : S → Prop := fun s => ∃ b, (s, b) ∈ c.1.toList
  have hnode : ∀ s, Mem s → E.checkNodeHome cmp internal c.1 s₀ s = true :=
    fun s ⟨b, hs⟩ => hc _ hs
  have hmem₀ : Mem s₀ := by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h₀
    exact ⟨b, BTree.mem_toList_of_findData hb⟩
  have hstep : ∀ s l s', Mem s → E.toLTS.step s l s' → Mem s' := by
    intro s l s' hs hst
    obtain ⟨_, _, _, _, hsucc, _⟩ := checkNodeHome_spec (hnode s hs)
    obtain ⟨r', d', ss', hf, -⟩ := hsucc l s' hst
    exact ⟨_, BTree.mem_toList_of_findData hf⟩
  -- every certificate state can return to `s₀`
  have home : ∀ n s, Mem s → ∀ r ss, c.1.findData cmp s = some (r, n, ss) →
      E.toLTS.Reachable s s₀ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs r ss hf
      obtain ⟨r₀, d₀, ⟨ss₀, hf₀⟩, -, -, hback⟩ := checkNodeHome_spec (hnode s hs)
      rw [hf] at hf₀
      simp only [Option.some.injEq, Prod.mk.injEq] at hf₀
      obtain ⟨-, rfl, -⟩ := hf₀
      rcases hback with rfl | ⟨l, s', r', d', ss', hmem, hf', hlt⟩
      · exact LTS.Reachable.refl _
      · exact LTS.Reachable.head ⟨l, hmem⟩
          (ih d' hlt s' (hstep s l s' hs hmem) r' ss' hf')
  refine ⟨?_, ?_, fun l s hs => ?_⟩
  · refine LTS.DeadlockFree.of_invariant Mem hmem₀ hstep fun s hs => ?_
    obtain ⟨_, _, _, hne, _⟩ := checkNodeHome_spec (hnode s hs)
    obtain ⟨⟨l, s'⟩, hmem⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨l, s', hmem⟩
  · refine LTS.LivelockFree.of_ranking Mem hmem₀ hstep
      (fun s => ((c.1.findData cmp s).map Prod.fst).getD 0) fun s l s' hs hl hst => ?_
    obtain ⟨r, d, ⟨ss, hf⟩, -, hsucc, -⟩ := checkNodeHome_spec (hnode s hs)
    obtain ⟨r', d', ss', hf', hlt⟩ := hsucc l s' hst
    simp only [hf, hf', Option.map_some, Option.getD_some]
    exact hlt hl
  · -- go home, then follow the trace for `l`
    have hsM : Mem s := hs.invariant hmem₀ hstep
    obtain ⟨r, d, ⟨ss, hf⟩, -⟩ := checkNodeHome_spec (hnode s hsM)
    have hback := home d s hsM r ss hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hl l)
    have hi' : i < (labels.zip c.2).length := by simp [List.length_zip, hi, ← hlen]
    have hmem := List.getElem_mem hi'
    have := htr _ hmem
    rw [List.getElem_zip] at this
    split at this
    · rename_i s' hs'
      exact ⟨s', hback.trans (reachable_of_followStates hs'), enabledB_iff.1 this⟩
    · cases this

end HomeSection

/-! ### Verified refutation: counterexample traces -/

section Refute

variable [DecidableEq S] [DecidableEq L]

/-- Follow an explicit trace of `(label, state)` pairs, checking each step. -/
def followB : S → List (L × S) → Option S
  | s, [] => some s
  | s, (l, s') :: rest => if (E.succ s).contains (l, s') then followB s' rest else none

variable {E}

theorem path_of_followB {s s' : S} {tr : List (L × S)} (h : E.followB s tr = some s') :
    E.toLTS.Path s (tr.map Prod.fst) s' := by
  induction tr generalizing s with
  | nil => cases h; exact LTS.Path.nil _
  | cons e rest ih =>
    obtain ⟨l, s''⟩ := e
    simp only [followB] at h
    split_ifs at h with hmem
    rw [List.contains_iff_mem] at hmem
    exact LTS.Path.cons hmem (ih h)

theorem transGen_of_followB {internal : L → Bool} {s s' : S} {e : L × S} {tr : List (L × S)}
    (h : E.followB s (e :: tr) = some s') (hint : ((e :: tr).all fun e => internal e.1) = true) :
    Relation.TransGen (E.toLTS.IStep fun l => internal l = true) s s' := by
  induction tr generalizing s e with
  | nil =>
    obtain ⟨l, s''⟩ := e
    simp only [followB] at h
    split_ifs at h with hmem
    cases h
    rw [List.contains_iff_mem] at hmem
    simp only [List.all_cons, List.all_nil, Bool.and_true] at hint
    exact Relation.TransGen.single ⟨l, hint, hmem⟩
  | cons e' rest ih =>
    obtain ⟨l, s''⟩ := e
    rw [followB] at h
    split_ifs at h with hmem
    rw [List.contains_iff_mem] at hmem
    simp only [List.all_cons, Bool.and_eq_true] at hint ih
    exact Relation.TransGen.head ⟨l, hint.1, hmem⟩ (ih h hint.2)

/-- **Deadlock counterexample**: a checked trace to a state without successors. -/
theorem not_deadlockFree_of_trace {s₀ s : S} {tr : List (L × S)}
    (h : E.followB s₀ tr = some s) (hd : (E.succ s).isEmpty = true) :
    ¬ E.toLTS.DeadlockFree s₀ := by
  refine LTS.not_deadlockFree_of_path (path_of_followB h) fun l s' hst => ?_
  rw [List.isEmpty_iff] at hd
  change (l, s') ∈ E.succ s at hst
  simp [hd] at hst

/-- **Livelock counterexample**: a checked trace to a state lying on a non-empty cycle of
internal steps. -/
theorem not_livelockFree_of_trace {internal : L → Bool} {s₀ s : S} {tr : List (L × S)}
    {e : L × S} {cyc : List (L × S)} (h : E.followB s₀ tr = some s)
    (hc : E.followB s (e :: cyc) = some s) (hint : ((e :: cyc).all fun e => internal e.1) = true) :
    ¬ E.toLTS.LivelockFree (fun l => internal l = true) s₀ :=
  LTS.not_livelockFree_of_cycle (path_of_followB h).reachable (transGen_of_followB hc hint)

variable (E) (cmp : S → S → Ordering)

/-- Explore from `s` and check that `l` is never enabled. -/
def checkNeverEnabled (l : L) (fuel : ℕ) (s : S) : Bool :=
  let t := E.explore cmp fuel s
  t.find cmp s && E.closedB cmp t && t.all fun x => !E.enabledB x l

variable {E} {cmp}

/-- **Liveness counterexample**: a checked trace to a state from which `l` can never be
enabled again. -/
theorem not_liveLabel_of_trace {l : L} {fuel : ℕ} {s₀ s : S} {tr : List (L × S)}
    (h : E.followB s₀ tr = some s) (hn : E.checkNeverEnabled cmp l fuel s = true) :
    ¬ E.toLTS.LiveLabel s₀ l := by
  simp only [checkNeverEnabled, Bool.and_eq_true, BTree.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hn
  obtain ⟨⟨h₀, hc⟩, hne⟩ := hn
  refine LTS.not_liveLabel_of_dead (path_of_followB h).reachable fun s' hr hen => ?_
  have := hne s' (mem_of_reachable (BTree.mem_toList_of_find h₀) hc hr)
  rw [← Bool.not_eq_true, enabledB_iff] at this
  exact this hen

end Refute

/-! ### Refutation by label traces

Counterexamples given just as a list of labels; the intermediate states are computed by an
(untrusted) search and re-checked by `followB`. -/

section RefuteLabels

variable [DecidableEq S] [DecidableEq L]

/-- The `(label, state)` trace obtained by repeatedly taking the first successor carrying
the next label (untrusted). -/
def labelTrace : S → List L → List (L × S)
  | _, [] => []
  | s, l :: ls =>
    match (E.succ s).find? (fun e => decide (e.1 = l)) with
    | some e => (l, e.2) :: labelTrace e.2 ls
    | none => []

/-- The state reached by following the labels `ls` from `s`. -/
def runLabels (s : S) (ls : List L) : Option S := E.followB s (E.labelTrace s ls)

/-- Following `ls` from `s₀` reaches a deadlock. -/
def refuteDeadlockFreeB (s₀ : S) (ls : List L) : Bool :=
  match E.runLabels s₀ ls with
  | some s => (E.succ s).isEmpty
  | none => false

/-- Following `ls` from `s₀` reaches a state `s` from which the non-empty internal cycle
`cyc` returns to `s`. -/
def refuteLivelockFreeB (internal : L → Bool) (s₀ : S) (ls cyc : List L) : Bool :=
  match E.runLabels s₀ ls with
  | some s =>
    match E.labelTrace s cyc with
    | [] => false
    | e :: tr =>
      decide (E.followB s (e :: tr) = some s) && ((e :: tr).all fun e => internal e.1)
  | none => false

/-- Following `ls` from `s₀` reaches a state from which `l` is never enabled again. -/
def refuteLiveB (cmp : S → S → Ordering) (fuel : ℕ) (s₀ : S) (ls : List L) (l : L) : Bool :=
  match E.runLabels s₀ ls with
  | some s => E.checkNeverEnabled cmp l fuel s
  | none => false

/-- Following `ls` from `s₀` reaches a state where performing `l'` disables `l`. -/
def refutePersistentB (s₀ : S) (ls : List L) (l l' : L) : Bool :=
  match E.runLabels s₀ ls with
  | some s =>
    !decide (l = l') && E.enabledB s l &&
      (E.succ s).any fun e => decide (e.1 = l') && !E.enabledB e.2 l
  | none => false

variable {E}

theorem not_deadlockFree_of_refuteB {s₀ : S} {ls : List L}
    (h : E.refuteDeadlockFreeB s₀ ls = true) : ¬ E.toLTS.DeadlockFree s₀ := by
  unfold refuteDeadlockFreeB at h
  split at h
  · rename_i s hs
    exact not_deadlockFree_of_trace hs h
  · cases h

theorem not_livelockFree_of_refuteB {internal : L → Bool} {s₀ : S} {ls cyc : List L}
    (h : E.refuteLivelockFreeB internal s₀ ls cyc = true) :
    ¬ E.toLTS.LivelockFree (fun l => internal l = true) s₀ := by
  unfold refuteLivelockFreeB at h
  rcases hs : E.runLabels s₀ ls with _ | s
  · simp [hs] at h
  rcases ht : E.labelTrace s cyc with _ | ⟨e, tr⟩
  · simp [hs, ht] at h
  simp only [hs, ht, Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_livelockFree_of_trace hs h.1 h.2

theorem not_liveLabel_of_refuteB {cmp : S → S → Ordering} {fuel : ℕ} {s₀ : S} {ls : List L}
    {l : L} (h : E.refuteLiveB cmp fuel s₀ ls l = true) : ¬ E.toLTS.LiveLabel s₀ l := by
  unfold refuteLiveB at h
  split at h
  · rename_i s hs
    exact not_liveLabel_of_trace hs h
  · cases h

theorem not_persistent_of_refuteB {s₀ : S} {ls : List L} {l l' : L}
    (h : E.refutePersistentB s₀ ls l l' = true) : ¬ E.toLTS.Persistent s₀ := by
  unfold refutePersistentB at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      List.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hne, hen⟩, ⟨l'', s'⟩, hmem, rfl, hdis⟩ := h
    refine LTS.not_persistent_of (path_of_followB hs).reachable hne (enabledB_iff.1 hen) hmem ?_
    rw [← enabledB_iff, hdis]
    simp
  · cases h

end RefuteLabels

/-! ### Persistence certificates with labelled successors

The persistence check of `checkCertPersistent` recomputes the successors of every successor.
A `PCert` stores, for each reachable state, its successors with their labels (as keys), so
each state's successors are computed once, and the labels enabled after a step are read from
the certificate. -/

section PersistSection

variable {S L : Type*} (E : ExplicitLTS S L) [DecidableEq S] (cmp : S → S → Ordering)
  (key : L → ℕ)

/-- Each state with its successors, labels replaced by their keys. -/
abbrev PCert (S : Type*) := BTree (S × List (ℕ × S))

/-- The successors of `s`, labels replaced by their keys. -/
def keyedSucc (s : S) : List (ℕ × S) := (E.succ s).map fun e => (key e.1, e.2)

/-- Check one state of a persistence certificate. -/
def checkNodeP (c : PCert S) (s : S) : Bool :=
  match c.findData cmp s with
  | none => false
  | some es =>
    decide (E.keyedSucc key s = es) &&
      es.all fun e' => match c.findData cmp e'.2 with
        | none => false
        | some es' => es.all fun e => e.1 == e'.1 || es'.any fun e'' => e''.1 == e.1

/-- Check a persistence certificate (trusted). -/
def checkPCert (s₀ : S) (c : PCert S) : Bool :=
  (c.findData cmp s₀).isSome && c.all fun x => E.checkNodeP cmp key c x.1

variable {E cmp key}

theorem checkNodeP_spec {c : PCert S} {s : S} {es : List (ℕ × S)}
    (hf : c.findData cmp s = some es) (h : E.checkNodeP cmp key c s = true) :
    E.keyedSucc key s = es ∧ ∀ e' ∈ es, ∃ es', c.findData cmp e'.2 = some es' ∧
      ∀ e ∈ es, e.1 = e'.1 ∨ ∃ e'' ∈ es', e''.1 = e.1 := by
  unfold checkNodeP at h
  rw [hf] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine ⟨h.1, fun e' he' => ?_⟩
  have := h.2 e' he'
  split at this
  · cases this
  · rename_i es' hf'
    refine ⟨es', hf', fun e he => ?_⟩
    have := List.all_eq_true.1 this e he
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at this
    exact this

/-- **Persistence from a labelled-successor certificate.** -/
theorem persistent_of_checkPCert (hkey : Function.Injective key) {s₀ : S} {c : PCert S}
    (h : E.checkPCert cmp key s₀ c = true) : E.toLTS.Persistent s₀ := by
  simp only [checkPCert, Bool.and_eq_true] at h
  obtain ⟨h₀, hc⟩ := h
  rw [BTree.all_eq_true] at hc
  have hnode : ∀ s es, c.findData cmp s = some es → E.checkNodeP cmp key c s = true :=
    fun s es hf => hc _ (BTree.mem_toList_of_findData hf)
  have hstep : ∀ s l s', (∃ es, c.findData cmp s = some es) → E.toLTS.step s l s' →
      ∃ es, c.findData cmp s' = some es := by
    rintro s l s' ⟨es, hf⟩ hst
    obtain ⟨hks, hall⟩ := checkNodeP_spec hf (hnode s es hf)
    have hmem : (key l, s') ∈ es := hks ▸ List.mem_map_of_mem (f := fun e => (key e.1, e.2)) hst
    obtain ⟨es', hf', -⟩ := hall _ hmem
    exact ⟨es', hf'⟩
  intro s hs l l' s' hne hen hst
  have hgood := hs.invariant (Option.isSome_iff_exists.1 h₀) hstep
  obtain ⟨es, hf⟩ := hgood
  obtain ⟨hks, hall⟩ := checkNodeP_spec hf (hnode s es hf)
  obtain ⟨s₁, h₁⟩ := hen
  have hm₁ : (key l, s₁) ∈ es := hks ▸ List.mem_map_of_mem (f := fun e => (key e.1, e.2)) h₁
  have hm' : (key l', s') ∈ es := hks ▸ List.mem_map_of_mem (f := fun e => (key e.1, e.2)) hst
  obtain ⟨es', hf', hcond⟩ := hall _ hm'
  rcases hcond _ hm₁ with heq | ⟨e'', he'', hk⟩
  · exact absurd (hkey heq) hne
  · obtain ⟨hks', -⟩ := checkNodeP_spec hf' (hnode s' es' hf')
    rw [← hks', keyedSucc, List.mem_map] at he''
    obtain ⟨e, he, rfl⟩ := he''
    have : e.1 = l := hkey hk
    exact ⟨e.2, by rw [← this]; exact he⟩

end PersistSection

end ExplicitLTS

end AsyncLean
