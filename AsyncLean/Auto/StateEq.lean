/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.StateEquation
import AsyncLean.Petri.Invariant
import AsyncLean.Checker.Petri
import AsyncLean.Auto.Simplex
import AsyncLean.Checker.FastPetri
import Mathlib.Algebra.BigOperators.Fin

/-!
# Deadlock freedom of concrete nets from the state equation

`PNet.checkSE` checks a Farkas certificate for `Net.deadlockFree_of_stateEq` on the lists of a
`PNet`: place weights `y = yp - yn` (two lists of natural numbers) and transition weights
`z`, for a bound `K` on every reachable marking.  All sums are over arcs, so the check is
linear in the size of the net (plus one pass over the places per transition for the second
condition).  `PNet.deadlockFree_of_checkSE` turns a successful check into deadlock freedom.

`PNet.findSE` finds a certificate by linear programming (untrusted).
-/

namespace AsyncLean

namespace PNet

variable (N : PNet)

/-- The tokens a disabled transition `t` can leave on its input places when place `p` holds
at most `ks[p]` tokens: one input place lacks tokens. -/
def deadBound (ks : List ℕ) (t : PTrans) : ℕ := (t.pre.dedup.map (ks.getD · 0)).sum - 1

/-- Sum of `f` over the places of an arc list (with multiplicity). -/
def arcSum (f : ℕ → ℕ) (ps : List ℕ) : ℕ := (ps.map f).sum

/-- **The state-equation check** for deadlock freedom with bounds `ks` (place by place). -/
def checkSE (ks : List ℕ) (yp yn z : List ℕ) : Bool :=
  N.wf && yp.length == N.places && yn.length == N.places && z.length == N.trans.length &&
    N.trans.all (fun t => t.pre.all fun p => decide (t.pre.count p ≤ ks.getD p 0)) &&
    N.trans.all (fun t => decide (arcSum (yp.getD · 0) t.pre + arcSum (yn.getD · 0) t.post ≤
      arcSum (yp.getD · 0) t.post + arcSum (yn.getD · 0) t.pre)) &&
    (List.range N.places).all (fun p => decide (yp.getD p 0 ≤ yn.getD p 0 +
      ((N.trans.zip z).map fun tz => if tz.1.pre.contains p then tz.2 else 0).sum)) &&
    decide (((N.trans.zip z).map fun tz => tz.2 * deadBound ks tz.1).sum +
        ((List.range N.places).map fun p => yn.getD p 0 * N.init.getD p 0).sum <
      ((List.range N.places).map fun p => yp.getD p 0 * N.init.getD p 0).sum)

variable {N}

/-- A sum over an arc list is a sum over the places, weighted by multiplicities. -/
theorem sum_map_eq_sum_count {M : Type*} [AddCommMonoid M] {n : ℕ} (l : List ℕ)
    (hl : ∀ p ∈ l, p < n) (f : ℕ → M) :
    (l.map f).sum = ∑ p : Fin n, l.count p.val • f p.val := by
  rw [Finset.sum_list_map_count, Fin.sum_univ_eq_sum_range (fun p => l.count p • f p)]
  refine Finset.sum_subset (fun p hp => ?_) fun p _ hp => ?_
  · exact Finset.mem_range.2 (hl p (List.mem_toFinset.1 hp))
  · rw [List.count_eq_zero_of_not_mem (fun h => hp (List.mem_toFinset.2 h)), zero_nsmul]

theorem sum_range_eq_sum_fin {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ p : Fin n, f p.val := by
  rw [Fin.sum_univ_eq_sum_range, ← List.toFinset_range, List.sum_toFinset _ List.nodup_range]

theorem sum_zip_eq_sum_fin {M : Type*} [AddCommMonoid M] {z : List ℕ}
    (hz : z.length = N.trans.length) (g : PTrans → ℕ → M) :
    ((N.trans.zip z).map fun tz => g tz.1 tz.2).sum =
      ∑ t : Fin N.trans.length, g (N.tr t) (z.getD t.val 0) := by
  rw [← Fin.sum_univ_fun_getElem]
  have hlen : (N.trans.zip z).length = N.trans.length := by simp [hz]
  rw [← Fin.sum_congr' _ hlen.symm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [List.getElem_zip, tr, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  rfl

/-- A sum over the input places of a transition is a sum over its deduplicated input list. -/
theorem sum_inputs (hwf : N.wf = true) (t : Fin N.trans.length) (f : ℕ → ℕ) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin N.places => N.toNet.pre t p ≠ 0), f p.val =
      ((N.tr t).pre.dedup.map f).sum := by
  have hlt := ((wf_spec hwf).2 t).1
  rw [← List.sum_toFinset _ (List.nodup_dedup _), List.toFinset_dedup]
  refine Finset.sum_bij (fun p _ => p.val) (fun p hp => ?_) (fun _ _ _ _ h => Fin.ext h)
    (fun q hq => ?_) (fun _ _ => rfl)
  · have hp' : N.toNet.pre t p ≠ 0 := (Finset.mem_filter.1 hp).2
    exact List.mem_toFinset.2 (List.count_pos_iff.1 (Nat.pos_of_ne_zero hp'))
  · refine ⟨⟨q, hlt q (List.mem_toFinset.1 hq)⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact (List.count_pos_iff.2 (List.mem_toFinset.1 hq)).ne'

/-- **Deadlock freedom from a state-equation certificate.** -/
theorem deadlockFree_of_checkSE {ks : List ℕ}
    (hK : ∀ M, N.toNet.lts.Reachable N.M₀ M → ∀ p : Fin N.places, M p ≤ ks.getD p.val 0)
    {yp yn z : List ℕ} (h : N.checkSE ks yp yn z = true) : N.toNet.lts.DeadlockFree N.M₀ := by
  simp only [checkSE, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hwf, hyp⟩, hyn⟩, hz⟩, hw⟩, h₁⟩, h₂⟩, h₃⟩ := h
  have hpre := fun t => ((wf_spec hwf).2 t).1
  have hpost := fun t => ((wf_spec hwf).2 t).2
  let y : Fin N.places → ℤ := fun p => (yp.getD p.val 0 : ℤ) - yn.getD p.val 0
  refine Net.deadlockFree_of_stateEq (fun p => ks.getD p.val 0) hK
    (fun t => deadBound ks (N.tr t)) ?_ y (fun t => z.getD t.val 0) ?_ ?_ ?_
  · -- a disabled transition leaves few tokens on its input places
    intro t M hM hdis
    simp only [Net.Enabled, not_forall, not_le] at hdis
    obtain ⟨p₀, hp₀⟩ := hdis
    have hne : N.toNet.pre t p₀ ≠ 0 := by omega
    have hwK : N.toNet.pre t p₀ ≤ ks.getD p₀.val 0 :=
      hw (N.tr t) (List.getElem_mem _) p₀.val (List.count_pos_iff.1 (Nat.pos_of_ne_zero hne))
    rw [← Finset.sum_filter, deadBound, ← sum_inputs hwf t]
    set S := (Finset.univ.filter fun p : Fin N.places => N.toNet.pre t p ≠ 0) with hS
    have hmem : p₀ ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
    have hrest : ∑ p ∈ S.erase p₀, M p ≤ ∑ p ∈ S.erase p₀, ks.getD p.val 0 :=
      Finset.sum_le_sum fun p _ => hM p
    omega
  · -- `y · C t ≥ 0`
    intro t
    have h := h₁ (N.tr t) (List.getElem_mem _)
    simp only [arcSum] at h
    rw [sum_map_eq_sum_count _ (hpre t), sum_map_eq_sum_count _ (hpost t),
      sum_map_eq_sum_count _ (hpost t), sum_map_eq_sum_count _ (hpre t)] at h
    simp only [smul_eq_mul] at h
    have h' : ((∑ p : Fin N.places, (N.tr t).pre.count p.val * yp.getD p.val 0 +
        ∑ p : Fin N.places, (N.tr t).post.count p.val * yn.getD p.val 0 : ℕ) : ℤ) ≤
        ((∑ p : Fin N.places, (N.tr t).post.count p.val * yp.getD p.val 0 +
          ∑ p : Fin N.places, (N.tr t).pre.count p.val * yn.getD p.val 0 : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast at h'
    have : ∑ p, y p * N.toNet.effect t p =
        (∑ p : Fin N.places, ((N.tr t).post.count p.val : ℤ) * yp.getD p.val 0 +
          ∑ p : Fin N.places, ((N.tr t).pre.count p.val : ℤ) * yn.getD p.val 0) -
        (∑ p : Fin N.places, ((N.tr t).pre.count p.val : ℤ) * yp.getD p.val 0 +
          ∑ p : Fin N.places, ((N.tr t).post.count p.val : ℤ) * yn.getD p.val 0) := by
      simp only [y, Net.effect, toNet, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [this]
    linarith
  · -- `y p ≤ Σ_t z t · [p ∈ •t]`
    intro p
    have h := h₂ p.val p.isLt
    rw [sum_zip_eq_sum_fin hz (fun t zt => if t.pre.contains p.val then zt else 0)] at h
    have : ∑ t : Fin N.trans.length, (if N.toNet.pre t p ≠ 0 then (z.getD t.val 0 : ℤ) else 0) =
        ((∑ t : Fin N.trans.length, (if (N.tr t).pre.contains p.val then z.getD t.val 0 else 0)
          : ℕ) : ℤ) := by
      push_cast
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [toNet, ne_eq, List.count_eq_zero, not_not, List.contains_iff_mem]
    rw [this]
    simp only [y]
    omega
  · -- `Σ_t z t · D t < y · M₀`
    rw [sum_zip_eq_sum_fin hz (fun t zt => zt * deadBound ks t),
      sum_range_eq_sum_fin N.places (fun p => yn.getD p 0 * N.init.getD p 0),
      sum_range_eq_sum_fin N.places (fun p => yp.getD p 0 * N.init.getD p 0)] at h₃
    have h₃' : ((∑ t : Fin N.trans.length, z.getD t.val 0 * deadBound ks (N.tr t) +
        ∑ p : Fin N.places, yn.getD p.val 0 * N.init.getD p.val 0 : ℕ) : ℤ) <
        ((∑ p : Fin N.places, yp.getD p.val 0 * N.init.getD p.val 0 : ℕ) : ℤ) := by
      exact_mod_cast h₃
    push_cast at h₃'
    have : ∑ p, y p * (N.M₀ p : ℤ) =
        ∑ p : Fin N.places, (yp.getD p.val 0 : ℤ) * N.init.getD p.val 0 -
          ∑ p : Fin N.places, (yn.getD p.val 0 : ℤ) * N.init.getD p.val 0 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by simp only [y, M₀]; ring
    rw [this]
    linarith

/-! ### Bounds from sparse place invariants -/

variable (N) in
/-- The weight of place `q` in a sparse vector of (place, weight) entries. -/
def sw (s : List (ℕ × ℕ)) (q : ℕ) : ℕ := ((s.filter fun e => e.1 == q).map (·.2)).sum

variable (N) in
/-- **The bounds check**: `invs` are sparse non-negative place invariants, and place `p` is
bounded by `(ks p).2` thanks to the invariant number `(ks p).1`. -/
def checkBounds (invs : List (List (ℕ × ℕ))) (ks : List (ℕ × ℕ)) : Bool :=
  N.wf && ks.length == N.places &&
    invs.all (fun s => s.all (fun e => decide (e.1 < N.places)) &&
      N.trans.all fun t => arcSum (sw s) t.post == arcSum (sw s) t.pre) &&
    (List.range N.places).all fun p =>
      let s := invs.getD (ks.getD p (0, 0)).1 []
      decide ((s.map fun e => e.2 * N.init.getD e.1 0).sum <
        ((ks.getD p (0, 0)).2 + 1) * sw s p)

theorem getD_mem_or {α : Type*} (l : List α) (i : ℕ) (d : α) : l.getD i d ∈ l ∨ l.getD i d = d := by
  by_cases h : i < l.length
  · left; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem _
  · right; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem sum_sw {n : ℕ} (s : List (ℕ × ℕ)) (hs : ∀ e ∈ s, e.1 < n) (f : ℕ → ℤ) :
    ∑ q : Fin n, (sw s q.val : ℤ) * f q.val = (s.map fun e => (e.2 : ℤ) * f e.1).sum := by
  induction s with
  | nil => simp [sw]
  | cons e s ih =>
    have he := hs e List.mem_cons_self
    have : ∀ q : ℕ, sw (e :: s) q = (if e.1 == q then e.2 else 0) + sw s q := by
      intro q; simp only [sw, List.filter_cons]; split_ifs <;> simp
    simp only [this, Nat.cast_add, add_mul, Finset.sum_add_distrib, List.map_cons,
      List.sum_cons, ih fun e' he' => hs e' (List.mem_cons_of_mem _ he')]
    congr 1
    rw [Finset.sum_eq_single ⟨e.1, he⟩]
    · simp
    · intro q _ hq
      have : ¬ (e.1 == q.val) = true := by
        simp only [beq_iff_eq]; intro h; exact hq (Fin.ext h.symm)
      simp [this]
    · simp

/-- **Bounds from sparse place invariants.** -/
theorem le_of_checkBounds {invs : List (List (ℕ × ℕ))} {ks : List (ℕ × ℕ)}
    (h : N.checkBounds invs ks = true) :
    ∀ M, N.toNet.lts.Reachable N.M₀ M → ∀ p : Fin N.places, M p ≤ (ks.getD p.val (0, 0)).2 := by
  simp only [checkBounds, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨hwf, -⟩, hinv⟩, hbnd⟩ := h
  intro M hM p
  set s := invs.getD (ks.getD p.val (0, 0)).1 []
  have hs : (∀ e ∈ s, e.1 < N.places) ∧ ∀ t ∈ N.trans, arcSum (sw s) t.post = arcSum (sw s) t.pre := by
    rcases getD_mem_or invs (ks.getD p.val (0, 0)).1 [] with hm | hm
    · simpa using hinv s hm
    · have hs' : s = [] := hm
      have h0 : sw [] = fun _ => 0 := funext fun q => by simp [sw]
      rw [hs', h0]
      exact ⟨by simp, fun t _ => by simp [arcSum]⟩
  let y : Fin N.places → ℤ := fun q => sw s q.val
  have hy : N.toNet.IsPInvariant y := by
    intro t
    have h := hs.2 (N.tr t) (List.getElem_mem _)
    simp only [arcSum] at h
    rw [sum_map_eq_sum_count _ ((wf_spec hwf).2 t).2,
      sum_map_eq_sum_count _ ((wf_spec hwf).2 t).1] at h
    simp only [Net.weightEffect, y, toNet, mul_sub]
    rw [Finset.sum_sub_distrib]
    have h' : ((∑ p : Fin N.places, (N.tr t).post.count p.val • sw s p.val : ℕ) : ℤ) =
        ((∑ p : Fin N.places, (N.tr t).pre.count p.val • sw s p.val : ℕ) : ℤ) := by
      exact_mod_cast h
    simp only [smul_eq_mul] at h'
    push_cast at h'
    have e1 : ∑ p : Fin N.places, (sw s p.val : ℤ) * ((N.tr t).post.count p.val : ℤ) =
        ∑ p : Fin N.places, ((N.tr t).post.count p.val : ℤ) * (sw s p.val : ℤ) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have e2 : ∑ p : Fin N.places, (sw s p.val : ℤ) * ((N.tr t).pre.count p.val : ℤ) =
        ∑ p : Fin N.places, ((N.tr t).pre.count p.val : ℤ) * (sw s p.val : ℤ) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    linarith
  have hb := hy.bound (fun q => Nat.cast_nonneg _) hM p
  have hw : Net.weight y N.M₀ = ((s.map fun e => e.2 * N.init.getD e.1 0).sum : ℕ) := by
    simp only [Net.weight, y, M₀]
    rw [sum_sw s hs.1 (fun q => (N.init.getD q 0 : ℤ))]
    simp [Nat.cast_list_sum, List.map_map, Function.comp_def]
  have hlt := hbnd p.val p.isLt
  rw [hw] at hb
  have hlt' := Nat.cast_lt (α := ℤ) |>.2 hlt
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hlt'
  simp only [y] at hb
  by_contra hc
  push Not at hc
  have hc' : ((ks.getD p.val (0, 0)).2 + 1 : ℤ) ≤ M p := by exact_mod_cast hc
  have := mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg (α := ℤ) (sw s p.val))
  change ((List.map (fun e => e.2 * N.init.getD e.1 0) s).sum : ℤ) < _ at hlt'
  nlinarith

/-- All the bounds of `ks` are at most `k`. -/
def boundsLe (ks : List (ℕ × ℕ)) (k : ℕ) : Bool := ks.all fun e => decide (e.2 ≤ k)

/-- **Boundedness from sparse place invariants.** -/
theorem bounded_of_checkBounds {invs : List (List (ℕ × ℕ))} {ks : List (ℕ × ℕ)} {k : ℕ}
    (h : N.checkBounds invs ks = true) (hk : boundsLe ks k = true) : N.Bounded k := by
  intro M hM p
  refine (le_of_checkBounds h M hM p).trans ?_
  rw [List.getD_eq_getElem?_getD]
  cases hp : ks[p.val]? with
  | none => exact Nat.zero_le _
  | some e =>
    simp only [Option.getD_some]
    exact of_decide_eq_true (List.all_eq_true.1 hk e (List.mem_of_getElem? hp))

/-- **Deadlock freedom from the state equation**, with bounds from sparse place invariants:
two checks linear in the size of the net, and no exploration of the state space. -/
theorem deadlockFree_of_checks {invs : List (List (ℕ × ℕ))} {ks : List (ℕ × ℕ)}
    {yp yn z : List ℕ} (hb : N.checkBounds invs ks = true)
    (hc : N.checkSE (ks.map Prod.snd) yp yn z = true) : N.toNet.lts.DeadlockFree N.M₀ := by
  refine deadlockFree_of_checkSE (fun M hM p => ?_) hc
  have := le_of_checkBounds hb M hM p
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getD_eq_getElem?_getD] at this
  cases h : ks[p.val]? <;> simp_all

/-! ### Bounds from packed place invariants

All the invariants are checked at once: place `p` gets one number, its *column*, holding
the weight of `p` in every invariant, one field of `f` bits per invariant.  Summing the
columns of a transition's output places and of its input places gives, field by field, the
weight it produces and consumes in every invariant; one comparison per transition checks all
the invariants, provided no field overflows (`g`-bit weights, fewer than `2^(f-g)` arcs). -/

/-- The first `J` digits of `n` in base `2^f`. -/
def digitsW (f J n : ℕ) : List ℕ := (List.range J).map fun j => n / 2 ^ (f * j) % 2 ^ f

/-- Digit `j` of `n` in base `2^f`. -/
def dig (f n j : ℕ) : ℕ := n / 2 ^ (f * j) % 2 ^ f

theorem encW_digitsW (f : ℕ) : ∀ (J n : ℕ), n < 2 ^ (f * J) → encW f (digitsW f J n) = n := by
  intro J
  induction J with
  | zero => intro n h; simp [digitsW, encW] at *; omega
  | succ J ih =>
    intro n h
    have hd : digitsW f (J + 1) n = n % 2 ^ f :: digitsW f J (n / 2 ^ f) := by
      simp only [digitsW, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.mul_zero,
        Nat.pow_zero, Nat.div_one]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply, Nat.mul_succ, Nat.pow_add, Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm (2 ^ f)]
    rw [hd, encW, ih]
    · exact Nat.mod_add_div n (2 ^ f)
    · rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
      rwa [Nat.mul_succ] at h

theorem field_encW_range {f J : ℕ} (a : ℕ → ℕ) (ha : ∀ j < J, a j < 2 ^ f) (i : ℕ)
    (hi : i < J) : encW f ((List.range J).map a) / 2 ^ (f * i) % 2 ^ f = a i := by
  rw [encW_field (by simpa using ha)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem encW_range_eq_sum (f J : ℕ) (a : ℕ → ℕ) :
    encW f ((List.range J).map a) = ∑ j ∈ Finset.range J, a j * 2 ^ (f * j) := by
  rw [encW_eq_sum, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  simp [List.getD_eq_getElem?_getD, hj]

/-- A number below `2^(f*J)` is the sum of its digits. -/
theorem eq_sum_dig {f J n : ℕ} (h : n < 2 ^ (f * J)) :
    n = ∑ j ∈ Finset.range J, dig f n j * 2 ^ (f * j) := by
  conv_lhs => rw [← encW_digitsW f J n h]
  rw [digitsW, encW_range_eq_sum]; rfl

/-- Linear combinations of columns, digit by digit. -/
theorem sum_cols {f J : ℕ} (l : List ℕ) (c col : ℕ → ℕ)
    (hcol : ∀ q ∈ l, col q < 2 ^ (f * J)) :
    (l.map fun q => c q * col q).sum =
      encW f ((List.range J).map fun j => (l.map fun q => c q * dig f (col q) j).sum) := by
  rw [encW_range_eq_sum]
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons, Nat.add_mul, Finset.sum_add_distrib]
    rw [ih fun q' hq' => hcol q' (List.mem_cons_of_mem _ hq'),
      eq_sum_dig (hcol q List.mem_cons_self), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← eq_sum_dig (hcol q List.mem_cons_self)]
    ring

theorem dig_sum_cols {f g J : ℕ} (hg : g ≤ f) (l : List ℕ) (c col : ℕ → ℕ)
    (hcol : ∀ q ∈ l, col q < 2 ^ (f * J)) (hdig : ∀ q ∈ l, ∀ j < J, dig f (col q) j < 2 ^ g)
    (hsmall : (l.map c).sum < 2 ^ (f - g)) (i : ℕ) (hi : i < J) :
    dig f (l.map fun q => c q * col q).sum i = (l.map fun q => c q * dig f (col q) i).sum := by
  rw [sum_cols l c col hcol, dig]
  refine field_encW_range _ (fun j hj => ?_) i hi
  calc (l.map fun q => c q * dig f (col q) j).sum
      ≤ (l.map fun q => c q * (2 ^ g - 1)).sum := by
        refine List.sum_le_sum fun q hq => Nat.mul_le_mul_left _ ?_
        have := hdig q hq j hj
        omega
    _ = (l.map c).sum * (2 ^ g - 1) := by rw [← List.sum_map_mul_right]
    _ < 2 ^ f := by
        have h1 : (l.map c).sum * (2 ^ g - 1) ≤ (2 ^ (f - g) - 1) * (2 ^ g - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h2 : 2 ^ (f - g) * 2 ^ g = 2 ^ f := by rw [← Nat.pow_add, Nat.sub_add_cancel hg]
        have h3 : 0 < 2 ^ g := by positivity
        have h4 : 0 < 2 ^ (f - g) := by positivity
        calc (l.map c).sum * (2 ^ g - 1) ≤ (2 ^ (f - g) - 1) * (2 ^ g - 1) := h1
          _ ≤ (2 ^ (f - g) - 1) * 2 ^ g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ < 2 ^ (f - g) * 2 ^ g := Nat.mul_lt_mul_of_pos_right (Nat.sub_lt h4 Nat.one_pos) h3
          _ = 2 ^ f := h2

/-- The column of place `q` (`0` if absent). -/
noncomputable def colOf (cols : BTree (ℕ × ℕ × ℕ)) (q : ℕ) : ℕ :=
  ((Fast.kfind q cols).map (·.1)).getD 0

/-- Sum of the columns of a list of places. -/
noncomputable def colSum (cols : BTree (ℕ × ℕ × ℕ)) (ps : List ℕ) : ℕ :=
  (ps.map fun q => 1 * colOf cols q).sum

/-- `f` at every index of a list. -/
def allIdx (l : List ℕ) (f : ℕ → ℕ → Bool) : ℕ → Bool
  | _ => (List.range l.length).all fun i => f i (l.getD i 0)

variable (N) in
/-- **The packed bounds check**: `cols` maps each place to its column and the number `j` of the
invariant bounding it; place `p` is bounded by `ks[p]`. -/
noncomputable def checkPInv (f g J : ℕ) (cols : BTree (ℕ × ℕ × ℕ)) (ks : List ℕ) : Bool :=
  N.wf && decide (g ≤ f) && ks.length == N.places &&
    (List.range N.places).all (fun p => (Fast.kfind p cols).isSome &&
      decide (colOf cols p < 2 ^ (f * J)) &&
      (List.range J).all fun j => decide (dig f (colOf cols p) j < 2 ^ g)) &&
    N.trans.all (fun t => decide ((t.post.map fun _ => 1).sum < 2 ^ (f - g)) &&
      decide ((t.pre.map fun _ => 1).sum < 2 ^ (f - g)) && colSum cols t.post == colSum cols t.pre) &&
    decide (((List.range N.places).map fun p => N.init.getD p 0).sum < 2 ^ (f - g)) &&
    (let W := ((List.range N.places).map fun p => N.init.getD p 0 * colOf cols p).sum
     (List.range N.places).all fun p =>
      let j := ((Fast.kfind p cols).map (·.2)).getD 0
      decide (j < J) && decide (dig f W j < (ks.getD p 0 + 1) * dig f (colOf cols p) j))

/-- **Bounds from packed place invariants.** -/
theorem le_of_checkPInv {f g J : ℕ} {cols : BTree (ℕ × ℕ × ℕ)} {ks : List ℕ}
    (h : N.checkPInv f g J cols ks = true) :
    ∀ M, N.toNet.lts.Reachable N.M₀ M → ∀ p : Fin N.places, M p ≤ ks.getD p.val 0 := by
  simp only [checkPInv, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hwf, hgf⟩, -⟩, hcol⟩, htr⟩, hinit⟩, hbnd⟩ := h
  have hpre := fun t => ((wf_spec hwf).2 t).1
  have hpost := fun t => ((wf_spec hwf).2 t).2
  have hcolP : ∀ q < N.places, colOf cols q < 2 ^ (f * J) := fun q hq => (hcol q hq).1.2
  have hdigP : ∀ q < N.places, ∀ j < J, dig f (colOf cols q) j < 2 ^ g :=
    fun q hq => (hcol q hq).2
  intro M hM p
  obtain ⟨hjJ, hb⟩ := hbnd p.val p.isLt
  set j := ((Fast.kfind p.val cols).map (·.2)).getD 0
  -- the `j`-th invariant
  let y : Fin N.places → ℤ := fun q => dig f (colOf cols q.val) j
  have hy : N.toNet.IsPInvariant y := by
    intro t
    obtain ⟨⟨hpo, hpr⟩, heq⟩ := htr (N.tr t) (List.getElem_mem _)
    have e := congrArg (fun n => dig f n j) heq
    simp only [colSum] at e
    rw [dig_sum_cols hgf _ (fun _ => 1) _ (fun q hq => hcolP q (hpost t q hq))
        (fun q hq => hdigP q (hpost t q hq)) hpo j hjJ,
      dig_sum_cols hgf _ (fun _ => 1) _ (fun q hq => hcolP q (hpre t q hq))
        (fun q hq => hdigP q (hpre t q hq)) hpr j hjJ] at e
    simp only [Nat.one_mul] at e
    rw [sum_map_eq_sum_count _ (hpost t), sum_map_eq_sum_count _ (hpre t)] at e
    simp only [Net.weightEffect, y, toNet, mul_sub, Finset.sum_sub_distrib]
    have e' : ((∑ q : Fin N.places, (N.tr t).post.count q.val • dig f (colOf cols q.val) j : ℕ) : ℤ) =
        ((∑ q : Fin N.places, (N.tr t).pre.count q.val • dig f (colOf cols q.val) j : ℕ) : ℤ) := by
      exact_mod_cast e
    simp only [smul_eq_mul] at e'
    push_cast at e'
    have c1 : ∑ q : Fin N.places, (dig f (colOf cols q.val) j : ℤ) * ((N.tr t).post.count q.val : ℤ) =
        ∑ q : Fin N.places, ((N.tr t).post.count q.val : ℤ) * (dig f (colOf cols q.val) j : ℤ) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have c2 : ∑ q : Fin N.places, (dig f (colOf cols q.val) j : ℤ) * ((N.tr t).pre.count q.val : ℤ) =
        ∑ q : Fin N.places, ((N.tr t).pre.count q.val : ℤ) * (dig f (colOf cols q.val) j : ℤ) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    linarith
  have hbound := hy.bound (fun q => Nat.cast_nonneg _) hM p
  -- the weight of the initial marking is digit `j` of the packed weight
  have hW : Net.weight y N.M₀ =
      (dig f ((List.range N.places).map fun q => N.init.getD q 0 * colOf cols q).sum j : ℕ) := by
    rw [dig_sum_cols hgf _ (fun q => N.init.getD q 0) _ (fun q hq => hcolP q (List.mem_range.1 hq))
      (fun q hq => hdigP q (List.mem_range.1 hq)) hinit j hjJ]
    rw [sum_range_eq_sum_fin]
    simp only [Net.weight, y, M₀]
    push_cast
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [hW] at hbound
  simp only [y] at hbound
  have hb' := Nat.cast_lt (α := ℤ) |>.2 hb
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hb'
  by_contra hc
  push Not at hc
  have hc' : ((ks.getD p.val 0) + 1 : ℤ) ≤ M p := by exact_mod_cast hc
  have := mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg (α := ℤ) (dig f (colOf cols p.val) j))
  nlinarith

/-- All the numbers of `ks` are at most `k`. -/
def allLe (ks : List ℕ) (k : ℕ) : Bool := ks.all fun b => decide (b ≤ k)

/-- **Boundedness from packed place invariants.** -/
theorem bounded_of_checkPInv {f g J : ℕ} {cols : BTree (ℕ × ℕ × ℕ)} {ks : List ℕ} {k : ℕ}
    (h : N.checkPInv f g J cols ks = true) (hk : allLe ks k = true) : N.Bounded k := by
  intro M hM p
  refine (le_of_checkPInv h M hM p).trans ?_
  rw [List.getD_eq_getElem?_getD]
  cases hp : ks[p.val]? with
  | none => exact Nat.zero_le _
  | some b =>
    simp only [Option.getD_some]
    exact of_decide_eq_true (List.all_eq_true.1 hk b (List.mem_of_getElem? hp))

/-- **Deadlock freedom from the state equation**, with bounds from packed place invariants:
no exploration of the state space. -/
theorem deadlockFree_of_pinv {f g J : ℕ} {cols : BTree (ℕ × ℕ × ℕ)} {ks yp yn z : List ℕ}
    (hb : N.checkPInv f g J cols ks = true) (hc : N.checkSE ks yp yn z = true) :
    N.toNet.lts.DeadlockFree N.M₀ :=
  deadlockFree_of_checkSE (le_of_checkPInv hb) hc

/-! ### Certificate search (untrusted) -/

variable (N)

/-- The linear program for a state-equation certificate with bounds `ks`; with `pos`, the
place weights are non-negative (`yn = 0`, a smaller program). -/
def seLP (ks : List ℕ) (pos : Bool) : Array (Array Rat) × Array Rat × ℕ :=
  let P := N.places
  let T := N.trans.length
  let ts := N.trans.toArray
  let C : Array (Array Rat) := ts.map fun t => (Array.range P).map fun p =>
    ((t.post.count p : ℤ) - (t.pre.count p : ℤ) : Rat)
  let inP (t : PTrans) (p : ℕ) : Rat := if t.pre.contains p then 1 else 0
  -- variables: yp (P), yn (Q = P or 0), z (T), slacks s₁ (T), s₂ (P), s₃ (1)
  let Q := if pos then 0 else P
  let nv := 2 * P + Q + 2 * T + 1
  let zero : Array Rat := Array.replicate nv 0
  let rows₁ := (List.range T).map fun t =>
    let ct := C[t]!
    (zero.mapIdx fun j _ =>
      if j < P then ct[j]! else if j < P + Q then -(ct[j - P]!) else 0).set! (P + Q + T + t) (-1)
  let rows₂ := (List.range P).map fun p =>
    (zero.mapIdx fun j _ =>
      if j == p then 1 else if Q > 0 ∧ j == P + p then -1
      else if P + Q ≤ j ∧ j < P + Q + T then -((ts[j - P - Q]?.map (inP · p)).getD 0)
      else 0).set! (P + Q + 2 * T + p) 1
  let row₃ := (zero.mapIdx fun j _ =>
      if j < P then ((N.init.getD j 0 : ℕ) : Rat)
      else if j < P + Q then -((N.init.getD (j - P) 0 : ℕ) : Rat)
      else if j < P + Q + T then
        -(((ts[j - P - Q]?.map (deadBound ks)).getD 0 : ℕ) : Rat) else 0).set! (nv - 1) (-1)
  ((rows₁ ++ rows₂ ++ [row₃]).toArray, ((List.replicate (T + P) (0 : Rat)) ++ [1]).toArray, nv)

/-- Find a state-equation certificate `(yp, yn, z)` for the bounds `ks` by linear
programming, trying non-negative place weights first. -/
def findSE (ks : List ℕ) : Option (List ℕ × List ℕ × List ℕ) :=
  let P := N.places
  let T := N.trans.length
  let attempt (pos : Bool) : Option (List ℕ × List ℕ × List ℕ) := do
    let (A, b, nv) := N.seLP ks pos
    let x ← Simplex.solve A b (Array.replicate nv 0) 100000
    let Q := if pos then 0 else P
    let v := Simplex.toNat (x.extract 0 (P + Q + T))
    let c := (v.take P, if pos then List.replicate P 0 else (v.drop P).take P, v.drop (P + Q))
    if N.checkSE ks c.1 c.2.1 c.2.2 then some c else none
  (attempt true).orElse fun _ => attempt false

/-- Sparse invariants and per-place bounds (untrusted), from one place invariant per place
found by `pinv` (a non-negative invariant `y` with `y p > 0`, as a dense integer vector). -/
def findBounds (pinv : ℕ → Option (List ℤ)) : Option (List (List (ℕ × ℕ)) × List (ℕ × ℕ)) := do
  let mut invs : Array (List (ℕ × ℕ)) := #[]
  let mut ks : Array (ℕ × ℕ) := #[]
  for p in [0:N.places] do
    -- reuse an invariant already covering `p`, if any
    let j ← match invs.findIdx? (fun s => sw s p != 0) with
      | some j => pure j
      | none => do
        let y ← pinv p
        let s := ((List.range N.places).filter fun q => y.getD q 0 ≠ 0).map fun q =>
          (q, (y.getD q 0).toNat)
        invs := invs.push s
        pure (invs.size - 1)
    let s := invs[j]!
    let w := (s.map fun e => e.2 * N.init.getD e.1 0).sum
    let yp := sw s p
    if yp == 0 then none
    ks := ks.push (j, w / yp)
  let r := (invs.toList, ks.toList)
  if N.checkBounds r.1 r.2 then some r else none

/-- Pack sparse invariants into columns (untrusted): field width `f`, weight width `g`, the
number of invariants, and the tree of (place, column, invariant number). -/
def packInvs (invs : List (List (ℕ × ℕ))) (ks : List (ℕ × ℕ)) :
    ℕ × ℕ × ℕ × BTree (ℕ × ℕ × ℕ) :=
  let J := invs.length
  let wmax := invs.foldl (fun a s => s.foldl (fun a e => max a e.2) a) 1
  let g := Nat.log2 wmax + 1
  let arity := N.trans.foldl (fun a t => max a (max t.pre.length t.post.length)) 1
  let tokens := N.init.sum
  let a := Nat.log2 (max arity tokens) + 1
  let f := g + a
  let col (p : ℕ) : ℕ := ((List.range J).map fun j => sw (invs.getD j []) p * 2 ^ (f * j)).sum
  let es := ((List.range N.places).map fun p => (p, col p, (ks.getD p (0, 0)).1)).toArray
  (f, g, J, Fast.buildTree es (es.size + 1) 0 es.size)

end PNet

namespace Auto

/-- The incidence matrix `C[t][p] = post - pre`. -/
def incidence (N : PNet) : List (List ℤ) :=
  N.trans.map fun t => (List.range N.places).map fun p =>
    (t.post.count p : ℤ) - (t.pre.count p : ℤ)

/-- A non-negative place invariant `y` with `y p = 1` minimising `y · M₀`, scaled to integers. -/
def pinvFor (N : PNet) (p : ℕ) : Option (List ℤ) := do
  let C := incidence N
  let m := N.places
  let eqs : Array (Array Rat) := (C.map fun row => (row.map fun c => (c : Rat)).toArray).toArray
  let unit : Array Rat := (Array.range m).map fun q => if q == p then 1 else 0
  let A := eqs.push unit
  let b : Array Rat := ((List.replicate C.length (0 : Rat)) ++ [1]).toArray
  let c : Array Rat := (Array.range m).map fun q => ((N.init.getD q 0 : ℕ) : Rat)
  let y ← Simplex.solve A b c
  return Simplex.toInt y

end Auto

end AsyncLean
