/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.Petri
import AsyncLean.Checker.Diagnose
import Mathlib.Data.Nat.Bitwise

/-!
# Fast verification of safe Petri nets

Asynchronous controllers are usually *1-safe*: no place ever holds two tokens.  A marking of
a safe net is then a set of places, which we store as a bit mask (a single natural number).
Testing whether a transition is enabled and firing it become a couple of bitwise operations,
and comparing states a single number comparison — all evaluated natively by the Lean kernel
(GMP-accelerated `Nat.land`, `Nat.lor`, `Nat.xor`).

The packed semantics is only faithful for safe nets, so the checker also verifies, at every
reachable state, that firing never puts a token on an already marked place (`safeNode`).
`PNet.correct_of_checkPacked` then proves `N.Correct ∧ N.Safe` for the original net, through
a functional bisimulation on the invariant "safe, and present in the certificate"
(`LTS.FunBisimOn`).
-/

namespace AsyncLean

namespace PNet

variable (N : PNet)

/-- Bit mask with the bits of `ps` set. -/
def mask (ps : List ℕ) : ℕ := ps.foldl (fun acc p => acc ||| 2 ^ p) 0

/-- Mask of the input places of `t`. -/
def preMask (t : Fin N.trans.length) : ℕ := mask (N.tr t).pre

/-- Mask of the output places of `t`. -/
def postMask (t : Fin N.trans.length) : ℕ := mask (N.tr t).post

/-- Packed encoding of a marking: the set of marked places. -/
def pack (M : Marking (Fin N.places)) : ℕ :=
  (List.finRange N.places).foldl (fun acc p => if M p = 0 then acc else acc ||| 2 ^ p.val) 0

/-- Successors in the packed semantics. -/
def packedSucc (m : ℕ) : List (Fin N.trans.length × ℕ) :=
  (List.finRange N.trans.length).filterMap fun t =>
    if Nat.beq (m &&& N.preMask t) (N.preMask t) then
      some (t, (m ^^^ N.preMask t) ||| N.postMask t)
    else none

/-- The packed semantics as an explicit LTS. -/
def packed : ExplicitLTS ℕ (Fin N.trans.length) := ⟨N.packedSucc⟩

/-- Safety at a packed state: firing an enabled transition never marks a marked place. -/
def safeNode (m : ℕ) : Bool :=
  (List.finRange N.trans.length).all fun t =>
    !Nat.beq (m &&& N.preMask t) (N.preMask t) ||
      Nat.beq ((m ^^^ N.preMask t) &&& N.postMask t) 0

/-- Well-formedness for the packed checker: a well-formed net with a safe initial marking and
no repeated places in any arc list. -/
def packedWf : Bool :=
  N.wf && N.init.all (· ≤ 1) &&
    N.trans.all fun t => decide t.pre.Nodup && decide t.post.Nodup

/-- Compute a certificate for the packed semantics (untrusted). -/
def mkPackedCert (fuel : ℕ := 100000) : ExplicitLTS.Cert ℕ :=
  N.packed.mkCert natCmp (fun t => (N.tr t).internal) (List.finRange N.trans.length) fuel
    (N.pack N.M₀)

/-- Compute a home-state certificate for the packed semantics (untrusted). -/
def mkPackedHomeCert (fuel : ℕ := 100000) : ExplicitLTS.HomeCert ℕ :=
  N.packed.mkCertHome natCmp (fun t => (N.tr t).internal) (List.finRange N.trans.length) fuel
    (N.pack N.M₀)

/-- Check a home-state certificate for the packed semantics, together with safety. -/
def checkPackedHome (c : ExplicitLTS.HomeCert ℕ) : Bool :=
  N.packedWf &&
    N.packed.checkCertHome natCmp (fun t => (N.tr t).internal) (List.finRange N.trans.length)
      (N.pack N.M₀) c &&
    c.1.all fun x => N.safeNode x.1

/-- Check a certificate for the packed semantics, together with safety. -/
def checkPacked (c : ExplicitLTS.Cert ℕ) : Bool :=
  N.packedWf &&
    N.packed.checkCert natCmp (fun t => (N.tr t).internal) (List.finRange N.trans.length)
      (N.pack N.M₀) c &&
    c.all fun x => N.safeNode x.1

/-! ### Bit-level lemmas -/

theorem testBit_foldl_mask (ps : List ℕ) (a q : ℕ) :
    Nat.testBit (ps.foldl (fun acc p => acc ||| 2 ^ p) a) q =
      (Nat.testBit a q || decide (q ∈ ps)) := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_lor, Nat.testBit_two_pow, List.mem_cons]
    by_cases h : q = p
    · subst h; simp
    · simp [h, Ne.symm h]

theorem testBit_mask (ps : List ℕ) (q : ℕ) : Nat.testBit (mask ps) q = decide (q ∈ ps) := by
  simp [mask, testBit_foldl_mask]

theorem testBit_foldl_pack (M : Marking (Fin N.places)) (l : List (Fin N.places)) (a q : ℕ) :
    Nat.testBit (l.foldl (fun acc p => if M p = 0 then acc else acc ||| 2 ^ p.val) a) q =
      (Nat.testBit a q || l.any fun p => decide (M p ≠ 0) && decide (p.val = q)) := by
  induction l generalizing a with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldl_cons, List.any_cons]
    split_ifs with hM
    · rw [ih]; simp [hM]
    · rw [ih, Nat.testBit_lor, Nat.testBit_two_pow]
      simp [hM, Bool.or_assoc]

variable {N}

theorem testBit_pack (M : Marking (Fin N.places)) (q : ℕ) :
    Nat.testBit (N.pack M) q = true ↔ ∃ h : q < N.places, M ⟨q, h⟩ ≠ 0 := by
  rw [pack, testBit_foldl_pack]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.isLt, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨⟨q, h⟩, hp, rfl⟩

/-- A marking is safe: at most one token per place. -/
def SafeM (M : Marking (Fin N.places)) : Prop := ∀ p, M p ≤ 1

theorem packedWf_spec (h : N.packedWf = true) :
    N.wf = true ∧ (∀ p, N.M₀ p ≤ 1) ∧ ∀ t : Fin N.trans.length,
      (N.tr t).pre.Nodup ∧ (N.tr t).post.Nodup := by
  simp only [packedWf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hwf, hinit⟩, hnd⟩ := h
  refine ⟨hwf, fun p => ?_, fun t => hnd _ (List.getElem_mem _)⟩
  show N.init.getD p.val 0 ≤ 1
  rw [List.getD_eq_getElem?_getD]
  cases h : N.init[p.val]? with
  | none => simp
  | some v => simpa using hinit v (List.mem_of_getElem? h)

theorem count_le_one_of_nodup {l : List ℕ} (h : l.Nodup) (a : ℕ) : l.count a ≤ 1 :=
  List.nodup_iff_count_le_one.1 h a

/-- Enabledness in the packed semantics. -/
theorem enabled_iff_packed (hwf : N.packedWf = true) {M : Marking (Fin N.places)}
    (hM : SafeM M) (t : Fin N.trans.length) :
    Nat.beq (N.pack M &&& N.preMask t) (N.preMask t) = true ↔ N.toNet.Enabled M t := by
  obtain ⟨hwf', -, hnd⟩ := packedWf_spec hwf
  have hpre := ((wf_spec hwf').2 t).1
  rw [Nat.beq_eq]
  constructor
  · intro heq p
    change (N.tr t).pre.count p.val ≤ M p
    by_cases hp : p.val ∈ (N.tr t).pre
    · have := congrArg (fun x => Nat.testBit x p.val) heq
      simp only [Nat.testBit_land, preMask, testBit_mask, hp, decide_true, Bool.and_true] at this
      obtain ⟨_, hne⟩ := (testBit_pack M p.val).1 this
      have h1 := count_le_one_of_nodup (hnd t).1 p.val
      have := hM p
      simp only [Fin.eta] at hne
      omega
    · rw [List.count_eq_zero_of_not_mem hp]; exact Nat.zero_le _
  · intro hen
    apply Nat.eq_of_testBit_eq
    intro q
    simp only [Nat.testBit_land, preMask, testBit_mask]
    by_cases hq : q ∈ (N.tr t).pre
    · have hlt := hpre q hq
      have hc := hen ⟨q, hlt⟩
      change (N.tr t).pre.count q ≤ M ⟨q, hlt⟩ at hc
      have hpos := List.count_pos_iff.2 hq
      have hbit : Nat.testBit (N.pack M) q = true := (testBit_pack M q).2 ⟨hlt, by omega⟩
      simp [hq, hbit]
    · simp [hq]

/-- Firing in the packed semantics. -/
theorem fire_packed (hwf : N.packedWf = true) {M : Marking (Fin N.places)} (hM : SafeM M)
    {t : Fin N.trans.length} (hen : N.toNet.Enabled M t)
    (hsafe : Nat.beq ((N.pack M ^^^ N.preMask t) &&& N.postMask t) 0 = true) :
    SafeM (N.toNet.fire M t) ∧
      N.pack (N.toNet.fire M t) = (N.pack M ^^^ N.preMask t) ||| N.postMask t := by
  obtain ⟨hwf', -, hnd⟩ := packedWf_spec hwf
  have hpre := ((wf_spec hwf').2 t).1
  have hpost := ((wf_spec hwf').2 t).2
  rw [Nat.beq_eq] at hsafe
  -- the per-place facts
  have key : ∀ p : Fin N.places,
      N.toNet.fire M t p ≤ 1 ∧
        ((N.toNet.fire M t p ≠ 0) ↔
          ((Nat.testBit (N.pack M) p.val ^^ decide (p.val ∈ (N.tr t).pre)) ||
            decide (p.val ∈ (N.tr t).post)) = true) := by
    intro p
    have hs := congrArg (fun x => Nat.testBit x p.val) hsafe
    simp only [Nat.testBit_land, Nat.testBit_xor, preMask, postMask, testBit_mask,
      Nat.zero_testBit] at hs
    have hbit : Nat.testBit (N.pack M) p.val = decide (M p ≠ 0) := by
      by_cases h0 : M p = 0
      · have : ¬ Nat.testBit (N.pack M) p.val = true := fun h => by
          obtain ⟨_, hne⟩ := (testBit_pack M p.val).1 h; exact hne h0
        simp [h0, this]
      · have : Nat.testBit (N.pack M) p.val = true := (testBit_pack M p.val).2 ⟨p.isLt, h0⟩
        simp [h0, this]
    have hmx : decide (p.val ∈ (N.tr t).pre) = decide (0 < (N.tr t).pre.count p.val) := by
      simp [List.count_pos_iff]
    have hmy : decide (p.val ∈ (N.tr t).post) = decide (0 < (N.tr t).post.count p.val) := by
      simp [List.count_pos_iff]
    rw [hbit, hmx, hmy] at hs ⊢
    have hx := count_le_one_of_nodup (hnd t).1 p.val
    have hy := count_le_one_of_nodup (hnd t).2 p.val
    have he := hen p
    change (N.tr t).pre.count p.val ≤ M p at he
    change M p - (N.tr t).pre.count p.val + (N.tr t).post.count p.val ≤ 1 ∧
      (M p - (N.tr t).pre.count p.val + (N.tr t).post.count p.val ≠ 0 ↔ _)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hM p) with ha | ha <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hx with hx' | hx' <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hy with hy' | hy' <;>
    simp_all
  refine ⟨fun p => (key p).1, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [Nat.testBit_lor, Nat.testBit_xor, preMask, postMask, testBit_mask]
  by_cases hq : q < N.places
  · have := (key ⟨q, hq⟩).2
    rw [Bool.eq_iff_iff, testBit_pack]
    constructor
    · rintro ⟨_, h⟩; exact this.1 h
    · intro h; exact ⟨hq, this.2 h⟩
  · have h1 : Nat.testBit (N.pack (N.toNet.fire M t)) q = false := by
      by_contra h
      obtain ⟨h', -⟩ := (testBit_pack _ q).1 (by simpa using h)
      exact hq h'
    have h2 : Nat.testBit (N.pack M) q = false := by
      by_contra h
      obtain ⟨h', -⟩ := (testBit_pack _ q).1 (by simpa using h)
      exact hq h'
    have h3 : q ∉ (N.tr t).pre := fun h => hq (hpre q h)
    have h4 : q ∉ (N.tr t).post := fun h => hq (hpost q h)
    simp [h1, h2, h3, h4]

/-- Transfer from the packed semantics: a set of packed states containing the initial one,
closed under packed steps and on which firing is always safe, makes the packed semantics a
faithful image of the net. -/
theorem correct_of_packed (hwf : N.packedWf = true) (C : ℕ → Prop) (h₀ : C (N.pack N.M₀))
    (hclosed : ∀ m l m', C m → N.packed.toLTS.step m l m' → C m')
    (hsafe : ∀ m, C m → N.safeNode m = true)
    (hcorr : N.packed.toLTS.DeadlockFree (N.pack N.M₀) ∧
      N.packed.toLTS.LivelockFree (fun t => (N.tr t).internal = true) (N.pack N.M₀) ∧
      N.packed.toLTS.Live (N.pack N.M₀)) :
    N.Correct ∧ N.Safe := by
  obtain ⟨-, hM₀, -⟩ := packedWf_spec hwf
  let J : Marking (Fin N.places) → Prop := fun M => SafeM M ∧ C (N.pack M)
  have hsafeAt : ∀ M, J M → ∀ t, N.toNet.Enabled M t →
      Nat.beq ((N.pack M ^^^ N.preMask t) &&& N.postMask t) 0 = true := by
    rintro M ⟨hM, hC⟩ t hen
    have := hsafe _ hC
    simp only [safeNode, List.all_eq_true, List.mem_finRange, forall_const, Bool.or_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true] at this
    rcases this t with h | h
    · rw [(enabled_iff_packed hwf hM t).2 hen] at h; cases h
    · exact h
  have hstep : ∀ M, J M → ∀ t m, (t, m) ∈ N.packedSucc (N.pack M) ↔
      N.toNet.Enabled M t ∧ m = N.pack (N.toNet.fire M t) := by
    intro M hJ t m
    simp only [packedSucc, List.mem_filterMap, List.mem_finRange, true_and]
    constructor
    · rintro ⟨t', h⟩
      split_ifs at h with hen
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hen' := (enabled_iff_packed hwf hJ.1 t').1 hen
      exact ⟨hen', (fire_packed hwf hJ.1 hen' (hsafeAt M hJ t' hen')).2.symm⟩
    · rintro ⟨hen, rfl⟩
      refine ⟨t, ?_⟩
      simp only [(enabled_iff_packed hwf hJ.1 t).2 hen, ↓reduceIte,
        (fire_packed hwf hJ.1 hen (hsafeAt M hJ t hen)).2]
  have hbisim : LTS.FunBisimOn N.toNet.lts N.packed.toLTS N.pack J := by
    refine ⟨fun M hJ t m => ?_, fun M hJ t M' hst => ?_⟩
    · change (t, m) ∈ N.packedSucc (N.pack M) ↔ _
      rw [hstep M hJ]
      constructor
      · rintro ⟨hen, rfl⟩; exact ⟨_, ⟨hen, rfl⟩, rfl⟩
      · rintro ⟨M', ⟨hen, rfl⟩, rfl⟩; exact ⟨hen, rfl⟩
    · obtain ⟨hen, rfl⟩ := hst
      exact ⟨(fire_packed hwf hJ.1 hen (hsafeAt M hJ t hen)).1,
        hclosed _ t _ hJ.2 ((hstep M hJ t _).2 ⟨hen, rfl⟩)⟩
  have hJ₀ : J N.M₀ := ⟨hM₀, h₀⟩
  obtain ⟨hd, hl, hv⟩ := hcorr
  exact ⟨⟨(hbisim.deadlockFree_iff hJ₀).1 hd, (hbisim.livelockFree_iff hJ₀).1 hl,
    (hbisim.live_iff hJ₀).1 hv⟩, fun M hr p => (hbisim.inv_reachable hJ₀ hr).1 p⟩

/-- **Soundness of the packed checker.** -/
theorem correct_of_checkPacked {c : ExplicitLTS.Cert ℕ} (h : N.checkPacked c = true) :
    N.Correct ∧ N.Safe := by
  simp only [checkPacked, Bool.and_eq_true, BTree.all_eq_true] at h
  obtain ⟨⟨hwf, hcert⟩, hsafe⟩ := h
  have hc := hcert
  simp only [ExplicitLTS.checkCert, Bool.and_eq_true] at hc
  obtain ⟨h₀, hall⟩ := hc
  refine correct_of_packed hwf c.Mem (ExplicitLTS.Cert.mem_of_isSome h₀)
    (fun m l m' hm hst => ExplicitLTS.mem_of_reachable_cert hm hall (LTS.Reachable.of_step hst))
    (fun m ⟨b, hb⟩ => hsafe _ hb) (ExplicitLTS.of_checkCert (List.mem_finRange) hcert)

/-- **Soundness of the packed checker with a home-state certificate.** -/
theorem correct_of_checkPackedHome {c : ExplicitLTS.HomeCert ℕ}
    (h : N.checkPackedHome c = true) : N.Correct ∧ N.Safe := by
  simp only [checkPackedHome, Bool.and_eq_true, BTree.all_eq_true] at h
  obtain ⟨⟨hwf, hcert⟩, hsafe⟩ := h
  have hc := hcert
  simp only [ExplicitLTS.checkCertHome, Bool.and_eq_true, BTree.all_eq_true] at hc
  obtain ⟨⟨⟨h₀, hall⟩, -⟩, -⟩ := hc
  let C : ℕ → Prop := fun m => ∃ b, (m, b) ∈ c.1.toList
  refine correct_of_packed hwf C ?_ ?_ (fun m ⟨b, hb⟩ => hsafe _ hb)
    (ExplicitLTS.of_checkCertHome (List.mem_finRange) hcert)
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h₀
    exact ⟨b, BTree.mem_toList_of_findData hb⟩
  · rintro m l m' ⟨b, hb⟩ hst
    obtain ⟨_, _, _, _, hsucc, _⟩ := ExplicitLTS.checkNodeHome_spec (hall _ hb)
    obtain ⟨r', d', ss', hf, -⟩ := hsucc l m' hst
    exact ⟨_, BTree.mem_toList_of_findData hf⟩

end PNet

end AsyncLean
