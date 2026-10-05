/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Explicit
import AsyncLean.Petri.Basic
import Mathlib.Data.List.FinRange

/-!
# Concrete Petri nets and their verified analysis

`PNet` is a plain-data description of a Petri net, convenient for writing down a concrete
design: places are numbered `0 … places-1`, each transition lists its input and output
places (a place listed `k` times means an arc of weight `k`), and may be marked internal
(silent / dummy).

* `PNet.toNet` is its abstract semantics as a `Net (Fin places) (Fin trans.length)`, so all
  the theory (invariants, siphons/traps, …) applies.
* `PNet.explicit` is an *executable* semantics on markings encoded as `List ℕ`.
* `PNet.bisim` proves that the two semantics are bisimilar (via `List.ofFn`).
* `PNet.checkAll` runs the verified model checker; `PNet.correct_of_checkAll` turns a
  successful run into a proof of `PNet.Correct`: deadlock freedom, livelock freedom and
  liveness of the abstract net.
-/

namespace AsyncLean

/-- A transition of a concrete Petri net. -/
structure PTrans where
  /-- A human-readable name, e.g. a signal edge `"req+"` (not used by the semantics). -/
  name : String := ""
  /-- Input places (with multiplicity). -/
  pre : List ℕ
  /-- Output places (with multiplicity). -/
  post : List ℕ
  /-- Internal (silent / dummy) transition, relevant for livelock. -/
  internal : Bool := false

/-- A concrete Petri net with places `0 … places - 1`. -/
structure PNet where
  /-- Number of places. -/
  places : ℕ
  /-- The transitions. -/
  trans : List PTrans
  /-- Initial marking, one entry per place. -/
  init : List ℕ

namespace PNet

variable (N : PNet)

/-- The `t`-th transition. -/
def tr (t : Fin N.trans.length) : PTrans := N.trans[t]

/-- Abstract semantics. -/
def toNet : Net (Fin N.places) (Fin N.trans.length) where
  pre t p := (N.tr t).pre.count p.val
  post t p := (N.tr t).post.count p.val

/-- Abstract initial marking. -/
def M₀ : Marking (Fin N.places) := fun p => N.init.getD p.val 0

/-- Internal transitions. -/
def Internal (t : Fin N.trans.length) : Prop := (N.tr t).internal = true

instance : DecidablePred N.Internal := fun t => inferInstanceAs (Decidable ((N.tr t).internal = true))

/-- **The correctness specification**: no deadlock, no livelock (no infinite run of internal
transitions), and every transition live (can always fire again). -/
def Correct : Prop :=
  N.toNet.lts.DeadlockFree N.M₀ ∧ N.toNet.lts.LivelockFree N.Internal N.M₀ ∧
    N.toNet.lts.Live N.M₀

/-- Well-formedness: the initial marking has the right length and all arcs refer to
existing places. -/
def wf : Bool :=
  N.init.length == N.places &&
    N.trans.all fun t => t.pre.all (· < N.places) && t.post.all (· < N.places)

/-! ### Executable semantics -/

/-- `pre` is enabled in the list-encoded marking `m`. -/
def enabledL (m : List ℕ) (pre : List ℕ) : Bool :=
  pre.all fun i => decide (pre.count i ≤ m.getD i 0)

/-- Firing on list-encoded markings; `i` is the index of the head of the list. -/
def fireL (pre post : List ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | i, x :: xs => (x - pre.count i + post.count i) :: fireL pre post (i + 1) xs

/-- Executable successor function. -/
def succ (m : List ℕ) : List (Fin N.trans.length × List ℕ) :=
  (List.finRange N.trans.length).filterMap fun t =>
    if enabledL m (N.tr t).pre then some (t, fireL (N.tr t).pre (N.tr t).post 0 m) else none

/-- The executable LTS. -/
def explicit : ExplicitLTS (List ℕ) (Fin N.trans.length) := ⟨N.succ⟩

/-- Encoding of abstract markings as lists. -/
def enc (M : Marking (Fin N.places)) : List ℕ := List.ofFn M

/-! ### Correctness of the executable semantics -/

variable {N}

theorem wf_spec (h : N.wf = true) :
    N.init.length = N.places ∧ ∀ t : Fin N.trans.length, (∀ i ∈ (N.tr t).pre, i < N.places) ∧
      ∀ i ∈ (N.tr t).post, i < N.places := by
  simp only [wf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun t => ?_⟩
  exact h.2 _ (List.getElem_mem _)

theorem getD_enc (M : Marking (Fin N.places)) (i : ℕ) (hi : i < N.places) :
    (N.enc M).getD i 0 = M ⟨i, hi⟩ := by
  simp [enc, List.getD_eq_getElem?_getD, hi]

theorem enabledL_enc_iff {M : Marking (Fin N.places)} {t : Fin N.trans.length}
    (hwf : ∀ i ∈ (N.tr t).pre, i < N.places) :
    enabledL (N.enc M) (N.tr t).pre = true ↔ N.toNet.Enabled M t := by
  simp only [enabledL, List.all_eq_true, decide_eq_true_eq, Net.Enabled, toNet]
  constructor
  · intro h p
    by_cases hp : p.val ∈ (N.tr t).pre
    · have := h _ hp
      rwa [getD_enc M p.val p.isLt] at this
    · rw [List.count_eq_zero_of_not_mem hp]; exact Nat.zero_le _
  · intro h i hi
    rw [getD_enc M i (hwf i hi)]
    exact h ⟨i, hwf i hi⟩

theorem length_fireL (pre post : List ℕ) (i : ℕ) (xs : List ℕ) :
    (fireL pre post i xs).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [fireL, ih]

theorem getElem_fireL (pre post : List ℕ) (i : ℕ) (xs : List ℕ) (k : ℕ)
    (hk : k < (fireL pre post i xs).length) :
    (fireL pre post i xs)[k] =
      xs[k]'(by rwa [length_fireL] at hk) - pre.count (i + k) + post.count (i + k) := by
  induction xs generalizing i k with
  | nil => simp [fireL] at hk
  | cons x xs ih =>
    cases k with
    | zero => simp [fireL]
    | succ k =>
      simp only [fireL, List.getElem_cons_succ]
      rw [ih]
      simp only [Nat.add_assoc, Nat.add_comm 1 k]

theorem fireL_enc (M : Marking (Fin N.places)) (t : Fin N.trans.length) :
    fireL (N.tr t).pre (N.tr t).post 0 (N.enc M) = N.enc (N.toNet.fire M t) := by
  apply List.ext_getElem
  · simp [length_fireL, enc]
  · intro k h1 h2
    rw [getElem_fireL]
    simp [enc, Net.fire, toNet]

theorem mem_succ_enc {M : Marking (Fin N.places)} {t : Fin N.trans.length} {m : List ℕ}
    (hwf : ∀ i ∈ (N.tr t).pre, i < N.places) :
    (t, m) ∈ N.succ (N.enc M) ↔ N.toNet.Enabled M t ∧ m = N.enc (N.toNet.fire M t) := by
  simp only [succ, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨t', h⟩
    split_ifs at h with hen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(enabledL_enc_iff hwf).1 hen, fireL_enc M _⟩
  · rintro ⟨hen, rfl⟩
    refine ⟨t, ?_⟩
    simp only [(enabledL_enc_iff hwf).2 hen, ↓reduceIte, fireL_enc]

/-- The executable semantics is bisimilar to the abstract one. -/
theorem bisim (hwf : N.wf = true) : LTS.FunBisim N.toNet.lts N.explicit.toLTS N.enc := by
  refine ⟨fun M t m => ?_⟩
  change (t, m) ∈ N.succ (N.enc M) ↔ _
  rw [mem_succ_enc ((wf_spec hwf).2 t).1]
  constructor
  · rintro ⟨hen, rfl⟩; exact ⟨_, ⟨hen, rfl⟩, rfl⟩
  · rintro ⟨M', ⟨hen, rfl⟩, rfl⟩; exact ⟨hen, rfl⟩

theorem enc_M₀ (hwf : N.wf = true) : N.enc N.M₀ = N.init := by
  have hlen := (wf_spec hwf).1
  apply List.ext_getElem
  · simp [enc, hlen]
  · intro k h1 h2
    simp [enc, M₀, List.getD_eq_getElem?_getD, h2]

/-! ### Verified analysis of concrete nets -/

variable (N)

/-- Run the verified checker for deadlock freedom. -/
def checkDeadlockFree (fuel : ℕ := 100000) : Bool :=
  N.wf && N.explicit.checkDeadlockFree lexCmp fuel N.init

/-- Run the verified checker for livelock freedom. -/
def checkLivelockFree (fuel : ℕ := 100000) : Bool :=
  N.wf && N.explicit.checkLivelockFree lexCmp (fun t => (N.tr t).internal) fuel N.init

/-- Run the verified checker for liveness of every transition. -/
def checkLive (fuel : ℕ := 100000) : Bool :=
  N.wf && N.explicit.checkLive lexCmp (List.finRange N.trans.length) fuel N.init

/-- Run the verified checker for all three properties at once. -/
def checkAll (fuel : ℕ := 100000) : Bool :=
  N.wf && N.explicit.checkAll lexCmp (fun t => (N.tr t).internal)
    (List.finRange N.trans.length) fuel N.init

variable {N}

theorem deadlockFree_of_check {fuel : ℕ} (h : N.checkDeadlockFree fuel = true) :
    N.toNet.lts.DeadlockFree N.M₀ := by
  simp only [checkDeadlockFree, Bool.and_eq_true] at h
  have := ExplicitLTS.deadlockFree_of_checkDeadlockFree h.2
  rw [← enc_M₀ h.1] at this
  exact (bisim h.1).deadlockFree_iff.1 this

theorem livelockFree_of_check {fuel : ℕ} (h : N.checkLivelockFree fuel = true) :
    N.toNet.lts.LivelockFree N.Internal N.M₀ := by
  simp only [checkLivelockFree, Bool.and_eq_true] at h
  have := ExplicitLTS.livelockFree_of_checkLivelockFree h.2
  rw [← enc_M₀ h.1] at this
  exact (bisim h.1).livelockFree_iff.1 this

theorem live_of_check {fuel : ℕ} (h : N.checkLive fuel = true) : N.toNet.lts.Live N.M₀ := by
  simp only [checkLive, Bool.and_eq_true] at h
  have := ExplicitLTS.live_of_checkLive (List.mem_finRange) h.2
  rw [← enc_M₀ h.1] at this
  exact (bisim h.1).live_iff.1 this

/-- **A successful run of the verified checker proves the design correct.** -/
theorem correct_of_checkAll {fuel : ℕ} (h : N.checkAll fuel = true) : N.Correct := by
  simp only [checkAll, Bool.and_eq_true] at h
  obtain ⟨hd, hl, hv⟩ := ExplicitLTS.of_checkAll (List.mem_finRange) h.2
  rw [← enc_M₀ h.1] at hd hl hv
  exact ⟨(bisim h.1).deadlockFree_iff.1 hd, (bisim h.1).livelockFree_iff.1 hl,
    (bisim h.1).live_iff.1 hv⟩

/-! ### Certificates computed outside the kernel (used by the `pnet_decide` tactic) -/

variable (N) in
/-- Compute a certificate (untrusted). -/
def mkCert (fuel : ℕ := 100000) : ExplicitLTS.Cert (List ℕ) :=
  N.explicit.mkCert lexCmp (fun t => (N.tr t).internal) (List.finRange N.trans.length) fuel N.init

variable (N) in
/-- Check a certificate for `Correct` (trusted). -/
def checkCert (c : ExplicitLTS.Cert (List ℕ)) : Bool :=
  N.wf && N.explicit.checkCert lexCmp (fun t => (N.tr t).internal)
    (List.finRange N.trans.length) N.init c

variable (N) in
/-- Check a certificate for persistence (trusted). -/
def checkCertPersistent (c : ExplicitLTS.Cert (List ℕ)) : Bool :=
  N.wf && N.explicit.checkCertPersistent lexCmp N.init c

theorem correct_of_checkCert {c : ExplicitLTS.Cert (List ℕ)} (h : N.checkCert c = true) :
    N.Correct := by
  simp only [checkCert, Bool.and_eq_true] at h
  obtain ⟨hd, hl, hv⟩ := ExplicitLTS.of_checkCert (List.mem_finRange) h.2
  rw [← enc_M₀ h.1] at hd hl hv
  exact ⟨(bisim h.1).deadlockFree_iff.1 hd, (bisim h.1).livelockFree_iff.1 hl,
    (bisim h.1).live_iff.1 hv⟩

theorem persistent_of_checkCert {c : ExplicitLTS.Cert (List ℕ)}
    (h : N.checkCertPersistent c = true) : N.toNet.lts.Persistent N.M₀ := by
  simp only [checkCertPersistent, Bool.and_eq_true] at h
  have := ExplicitLTS.persistent_of_checkCert h.2
  rw [← enc_M₀ h.1] at this
  exact (bisim h.1).persistent_iff.1 this

variable (N) in
/-- Run the verified checker for persistence (no transition is ever disabled by another). -/
def checkPersistent (fuel : ℕ := 100000) : Bool :=
  N.wf && N.explicit.checkPersistent lexCmp fuel N.init

theorem persistent_of_check {fuel : ℕ} (h : N.checkPersistent fuel = true) :
    N.toNet.lts.Persistent N.M₀ := by
  simp only [checkPersistent, Bool.and_eq_true] at h
  have := ExplicitLTS.persistent_of_checkPersistent h.2
  rw [← enc_M₀ h.1] at this
  exact (bisim h.1).persistent_iff.1 this

/-! ### Verified refutation of concrete nets

Counterexamples are given as lists of transition *indices*. -/

variable (N)

/-- Transition indices as elements of `Fin` (out-of-range indices are dropped). -/
def toFins (ts : List ℕ) : List (Fin N.trans.length) :=
  ts.filterMap fun i => if h : i < N.trans.length then some ⟨i, h⟩ else none

/-- Firing `ts` from the initial marking reaches a dead marking. -/
def refuteDeadlockFree (ts : List ℕ) : Bool :=
  N.wf && N.explicit.refuteDeadlockFreeB N.init (N.toFins ts)

/-- Firing `ts` reaches a marking `m` from which the non-empty sequence of internal
transitions `cyc` leads back to `m`. -/
def refuteLivelockFree (ts cyc : List ℕ) : Bool :=
  N.wf && N.explicit.refuteLivelockFreeB (fun t => (N.tr t).internal) N.init (N.toFins ts)
    (N.toFins cyc)

/-- Firing `ts` reaches a marking from which `t` can never fire again. -/
def refuteLive (ts : List ℕ) (t : Fin N.trans.length) (fuel : ℕ := 100000) : Bool :=
  N.wf && N.explicit.refuteLiveB lexCmp fuel N.init (N.toFins ts) t

/-- Firing `ts` reaches a marking where firing `t'` disables `t`. -/
def refutePersistent (ts : List ℕ) (t t' : Fin N.trans.length) : Bool :=
  N.wf && N.explicit.refutePersistentB N.init (N.toFins ts) t t'

variable {N}

theorem not_deadlockFree_of_refute {ts : List ℕ} (h : N.refuteDeadlockFree ts = true) :
    ¬ N.toNet.lts.DeadlockFree N.M₀ := by
  simp only [refuteDeadlockFree, Bool.and_eq_true] at h
  rw [← (bisim h.1).deadlockFree_iff, enc_M₀ h.1]
  exact ExplicitLTS.not_deadlockFree_of_refuteB h.2

theorem not_livelockFree_of_refute {ts cyc : List ℕ} (h : N.refuteLivelockFree ts cyc = true) :
    ¬ N.toNet.lts.LivelockFree N.Internal N.M₀ := by
  simp only [refuteLivelockFree, Bool.and_eq_true] at h
  rw [← (bisim h.1).livelockFree_iff, enc_M₀ h.1]
  exact ExplicitLTS.not_livelockFree_of_refuteB h.2

theorem not_liveLabel_of_refute {ts : List ℕ} {t : Fin N.trans.length} {fuel : ℕ}
    (h : N.refuteLive ts t fuel = true) : ¬ N.toNet.lts.LiveLabel N.M₀ t := by
  simp only [refuteLive, Bool.and_eq_true] at h
  rw [← (bisim h.1).liveLabel_iff, enc_M₀ h.1]
  exact ExplicitLTS.not_liveLabel_of_refuteB h.2

theorem not_persistent_of_refute {ts : List ℕ} {t t' : Fin N.trans.length}
    (h : N.refutePersistent ts t t' = true) : ¬ N.toNet.lts.Persistent N.M₀ := by
  simp only [refutePersistent, Bool.and_eq_true] at h
  rw [← (bisim h.1).persistent_iff, enc_M₀ h.1]
  exact ExplicitLTS.not_persistent_of_refuteB h.2

end PNet

end AsyncLean
