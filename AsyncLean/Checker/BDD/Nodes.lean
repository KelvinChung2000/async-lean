/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.BDD.Checks

/-!
# Symbolic certificates: decision diagrams checked by the kernel, part 2: basic lemmas and node invariants

Part 2 of 4 of `AsyncLean.Checker.BDD`; that module has the overview.
-/

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

end PNet

end AsyncLean
