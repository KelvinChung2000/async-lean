/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The exclusion limit of one-packet lanes

The simulators (`scripts/routing_sim.py` and its relatives) move packets between lanes (virtual
channels) that are FIFO buffers of depth `N` (`N = 1` in all of them but
`scripts/flow_control_experiments.py`).  In every cycle each lane that is non-empty at the start
of the cycle takes **one turn**, the lanes taking their turns in a uniformly random order; at its
turn a lane moves its head packet one hop if the next lane has room *at that moment* (a lane
emptied earlier in the cycle can be refilled).  On a ring or a chain of lanes this is the totally
asymmetric exclusion process with site capacity `N` under the random-shuffle update.

This file models one cycle on a **ring of `L = n + 2` lanes** (lane `i` feeds lane `nx i`) for an
arbitrary order of turns, given by a permutation `σ` (lane `i` takes its turn at time `σ i`), and
proves:

* `Ring.cnt_add_moved` : conservation: after the cycle, lane `k + 1` holds
  `n₀ (k + 1) + [k moved] - [k + 1 moved]`; every lane passes at most one packet per cycle (the
  flag `moved` is a `Bool`).
* `Ring.moved_of_room` : a non-empty lane whose successor has room at the start of the cycle
  moves, whatever the order.
* `Ring.all_move` : **depth `N ≥ 2` reaches the per-lane bound `1` deterministically**: if every
  lane holds between `1` and `N - 1` packets, then for every order every lane moves and the
  configuration is unchanged, so every lane carries exactly one packet per cycle forever.
* `Ring.moved_order` : for depth `1`, a lane whose successor was full at the start moves only if
  the successor took its turn before it.
* `Ring.card_lt` : exactly half of the orders put lane `a` before lane `b`.
* `Ring.half_bound` : **the exclusion limit of one-packet lanes.**  For every configuration of a
  ring of depth-1 lanes, summed over all `L!` orders, the number of moves is at most
  `L * L! / 2`: the expected number of packets a lane passes per cycle, under the random-shuffle
  update, is at most `1/2`, from **every** configuration (`Ring.half_bound_rat`).  Hence for every
  distribution of configurations, at every cycle, and so for every time average, the current of
  the ring is at most `1/2` per lane and cycle, at every density.  The bound is attained by the
  alternating configuration (`Ring.alternating_moves`).

The proof: lane `i` moves only if it is non-empty, and then either its successor is empty
(at most one such lane per empty lane) or its successor is full and went first (half of the
orders).  So `2 E[moves] ≤ #empty + #full = L`.

What this does **not** say: a lane that is not in such a ring (a lane feeding the ejection port,
a lane with several possible successors, a lane whose successor is fed by several lanes) can carry
up to one packet per cycle, and in the simulations busy lanes do carry up to 0.6 to 0.7.  The
network-level consequence is an estimate, not a theorem; see `Packet/Ceiling.lean`.
-/

namespace AsyncLean

namespace Packet

namespace Ring

open Finset

variable {n : ℕ}

/-- The next lane on the ring. -/
def nx (i : Fin (n + 2)) : Fin (n + 2) :=
  if h : i.val + 1 < n + 2 then ⟨i.val + 1, h⟩ else ⟨0, by omega⟩

/-- The previous lane on the ring. -/
def pv (i : Fin (n + 2)) : Fin (n + 2) :=
  if h : i.val = 0 then ⟨n + 1, by omega⟩ else ⟨i.val - 1, by omega⟩

/-- The state during the move phase: the number of packets in every lane, and which lanes have
moved their head this cycle. -/
structure St (n : ℕ) where
  /-- Packets in lane `k`. -/
  cnt : Fin (n + 2) → ℕ
  /-- Lane `k` has moved its head this cycle. -/
  moved : Fin (n + 2) → Bool

/-- The turn of lane `i`: it moves its head into lane `nx i` if it was non-empty at the start of
the cycle (`n₀ i > 0`) and lane `nx i` has room now. -/
def turn (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (s : St n) (i : Fin (n + 2)) : St n :=
  if 0 < n₀ i ∧ s.cnt (nx i) < N then
    ⟨fun k => if k = nx i then s.cnt k + 1 else if k = i then s.cnt k - 1 else s.cnt k,
     fun k => if k = i then true else s.moved k⟩
  else s

/-- The first `t` turns of the cycle with order `σ` (lane `i` takes its turn at time `σ i`). -/
def run (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2))) : ℕ → St n
  | 0 => ⟨n₀, fun _ => false⟩
  | t + 1 => if h : t < n + 2 then turn N n₀ (run N n₀ σ t) (σ.symm ⟨t, h⟩) else run N n₀ σ t

/-- The state at the end of the move phase. -/
def cycle (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2))) : St n :=
  run N n₀ σ (n + 2)

/-- The number of lanes that moved (= the packets that moved one hop) in the cycle. -/
def moves (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2))) : ℕ :=
  (univ.filter fun i => (cycle N n₀ σ).moved i = true).card

theorem nx_val (i : Fin (n + 2)) : (nx i).val = if i.val + 1 < n + 2 then i.val + 1 else 0 := by
  unfold nx; split_ifs <;> rfl

theorem nx_ne (i : Fin (n + 2)) : nx i ≠ i := by
  intro h
  have := congrArg Fin.val h
  rw [nx_val] at this
  split_ifs at this <;> omega

theorem nx_inj {i j : Fin (n + 2)} (h : nx i = nx j) : i = j := by
  have hv := congrArg Fin.val h
  rw [nx_val, nx_val] at hv
  apply Fin.ext
  have := i.isLt; have := j.isLt
  split_ifs at hv <;> omega

theorem nx_pv (i : Fin (n + 2)) : nx (pv i) = i := by
  apply Fin.ext
  rw [nx_val]
  have := i.isLt
  by_cases h : i.val = 0
  · have hp : (pv i).val = n + 1 := by unfold pv; simp [h]
    rw [hp]; split_ifs <;> omega
  · have hp : (pv i).val = i.val - 1 := by unfold pv; simp [h]
    rw [hp]; split_ifs <;> omega

theorem pv_nx (i : Fin (n + 2)) : pv (nx i) = i := by
  apply nx_inj; rw [nx_pv]

/-- The rotation of the ring. -/
def rot : Fin (n + 2) ≃ Fin (n + 2) := ⟨nx, pv, pv_nx, nx_pv⟩

/-- A lane is marked as moved only at its own turn, and only if it could move then. -/
theorem moved_spec (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    ∀ t i, (run N n₀ σ t).moved i = true →
      (σ i : ℕ) < t ∧ 0 < n₀ i ∧ (run N n₀ σ (σ i)).cnt (nx i) < N := by
  intro t
  induction t with
  | zero => intro i h; simp [run] at h
  | succ t ih =>
    intro i h
    by_cases ht : t < n + 2
    · simp only [run, ht, dite_true] at h
      set p := σ.symm ⟨t, ht⟩ with hp
      have hσp : σ p = ⟨t, ht⟩ := by simp [hp]
      unfold turn at h
      split_ifs at h with hc
      · by_cases hip : i = p
        · subst hip
          refine ⟨by rw [hσp]; exact Nat.lt_succ_self t, hc.1, ?_⟩
          rw [hσp]; exact hc.2
        · simp only [hip, ite_false] at h
          obtain ⟨h1, h2, h3⟩ := ih i h
          exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩
      · obtain ⟨h1, h2, h3⟩ := ih i h
        exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩
    · simp only [run, ht, dite_false] at h
      obtain ⟨h1, h2, h3⟩ := ih i h
      exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩

/-- Indicator of a flag. -/
def ind (b : Bool) : ℕ := if b then 1 else 0

/-- **Conservation** during the move phase: lane `k + 1` has received a packet iff lane `k` moved,
and lost one iff it moved itself. -/
theorem cnt_add_moved (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    ∀ t k, (run N n₀ σ t).cnt (nx k) + ind ((run N n₀ σ t).moved (nx k)) =
      n₀ (nx k) + ind ((run N n₀ σ t).moved k) := by
  intro t
  induction t with
  | zero => intro k; simp [run, ind]
  | succ t ih =>
    intro k
    by_cases ht : t < n + 2
    · simp only [run, ht, dite_true]
      set p := σ.symm ⟨t, ht⟩ with hp
      have hσp : σ p = ⟨t, ht⟩ := by simp [hp]
      -- p has not moved yet
      have hpm : (run N n₀ σ t).moved p = false := by
        by_contra hc
        have := (moved_spec N n₀ σ t p (by simpa using hc)).1
        rw [hσp] at this; exact lt_irrefl _ this
      unfold turn
      split_ifs with hc
      · -- p moved into p + 1
        have hcp : 1 ≤ (run N n₀ σ t).cnt p := by
          have := ih (pv p)
          rw [nx_pv, hpm] at this
          simp [ind] at this; omega
        simp only
        by_cases hk1 : nx k = nx p
        · have hk : k = p := nx_inj hk1
          rw [hk]
          have h0 := ih p
          rw [hpm] at h0
          simp only [nx_ne p, ite_true, ite_false, ind] at h0 ⊢
          simp at h0 ⊢; omega
        · by_cases hk2 : nx k = p
          · have h0 := ih k
            have hkp : k ≠ p := fun h => nx_ne k (hk2.trans h.symm)
            rw [hk2, hpm] at h0
            simp only [hk2, hkp, ite_true, ite_false, ind] at h0 ⊢
            simp only [(nx_ne p).symm, ite_false]
            simp at h0 ⊢; omega
          · have hkp : k ≠ p := fun h => hk1 (congrArg nx h)
            have h0 := ih k
            simp only [hk1, hk2, hkp, ite_false]
            exact h0
      · exact ih k
    · simp only [run, ht, dite_false]
      exact ih k

/-- **A lane with room ahead moves**, whatever the order: if lane `i` is non-empty and lane
`nx i` holds fewer than `N` packets at the start of the cycle, lane `i` moves. -/
theorem moved_of_room (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2)))
    (i : Fin (n + 2)) (hi : 0 < n₀ i) (hroom : n₀ (nx i) < N) :
    (cycle N n₀ σ).moved i = true := by
  -- at time σ nx i it has moved
  have key : (run N n₀ σ ((σ i : ℕ) + 1)).moved i = true := by
    have ht : (σ i : ℕ) < n + 2 := (σ i).isLt
    simp only [run, ht, dite_true]
    have hs : σ.symm ⟨(σ i : ℕ), ht⟩ = i := by simp
    rw [hs]
    have hpm : (run N n₀ σ (σ i)).moved i = false := by
      by_contra hc
      have := (moved_spec N n₀ σ _ i (by simpa using hc)).1
      exact lt_irrefl _ this
    have h0 := cnt_add_moved N n₀ σ (σ i) i
    rw [hpm] at h0
    have hc : 0 < n₀ i ∧ (run N n₀ σ (σ i)).cnt (nx i) < N := by
      refine ⟨hi, ?_⟩
      simp [ind] at h0; omega
    simp [turn, hc]
  -- flags are never cleared
  have mono : ∀ t u, t ≤ u → (run N n₀ σ t).moved i = true → (run N n₀ σ u).moved i = true := by
    intro t u htu h
    induction u, htu using Nat.le_induction with
    | base => exact h
    | succ u _ ih =>
      by_cases hu : u < n + 2
      · simp only [run, hu, dite_true]
        unfold turn
        split_ifs
        · simp only; split_ifs <;> simp_all
        · exact ih
      · simp only [run, hu, dite_false]; exact ih
  exact mono _ _ (σ i).isLt key


/-- **Depth `N ≥ 2` reaches the per-lane bound deterministically.**  If every lane holds between
`1` and `N - 1` packets, every lane moves in the cycle, whatever the order of the turns. -/
theorem all_move (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2)))
    (h : ∀ k, 0 < n₀ k ∧ n₀ k < N) (i : Fin (n + 2)) : (cycle N n₀ σ).moved i = true :=
  moved_of_room N n₀ σ i (h i).1 (h (nx i)).2

/-- ... and the configuration is the same after the cycle, so every lane carries exactly one
packet in every cycle from then on: the current is `1`, the largest possible. -/
theorem all_move_cnt (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2)))
    (h : ∀ k, 0 < n₀ k ∧ n₀ k < N) (k : Fin (n + 2)) : (cycle N n₀ σ).cnt k = n₀ k := by
  have h0 := cnt_add_moved N n₀ σ (n + 2) (pv k)
  rw [nx_pv] at h0
  have a := all_move N n₀ σ h k
  have b := all_move N n₀ σ h (pv k)
  unfold cycle at a b ⊢
  rw [a, b] at h0
  simpa [ind] using h0

/-- **Depth 1: a lane behind a full lane moves only if that lane went first.** -/
theorem moved_order (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 2))
    (hfull : 1 ≤ n₀ (nx i)) (h : (cycle 1 n₀ σ).moved i = true) :
    (σ (nx i) : ℕ) < σ i := by
  obtain ⟨_, _, h3⟩ := moved_spec 1 n₀ σ _ i h
  have hpm : (run 1 n₀ σ (σ i)).moved i = false := by
    by_contra hc
    have := (moved_spec 1 n₀ σ _ i (by simpa using hc)).1
    exact lt_irrefl _ this
  have h0 := cnt_add_moved 1 n₀ σ (σ i) i
  rw [hpm] at h0
  have hm : (run 1 n₀ σ (σ i)).moved (nx i) = true := by
    cases hb : (run 1 n₀ σ (σ i)).moved (nx i)
    · rw [hb] at h0; simp [ind] at h0; omega
    · rfl
  exact (moved_spec 1 n₀ σ _ (nx i) hm).1

/-- The permutations of the lanes form a finite type (a local instance: `Mathlib.Data.Fintype.Perm`
is not among the built modules). -/
noncomputable instance permFintype : Fintype (Equiv.Perm (Fin (n + 2))) :=
  Fintype.ofEquiv {f : Fin (n + 2) → Fin (n + 2) // Function.Injective f}
    { toFun := fun f => Equiv.ofBijective f.1 (Finite.injective_iff_bijective.1 f.2)
      invFun := fun σ => ⟨σ, σ.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => Equiv.ext fun _ => rfl }

/-- **Half of the orders put lane `a` before lane `b`** (swapping their turns is a bijection). -/
theorem card_lt (a b : Fin (n + 2)) (hab : a ≠ b) :
    2 * (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) => (σ a : ℕ) < σ b).card =
      Fintype.card (Equiv.Perm (Fin (n + 2))) := by
  have e : (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) => (σ a : ℕ) < σ b).card =
      (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) => (σ b : ℕ) < σ a).card := by
    apply Finset.card_nbij' (fun σ => (Equiv.swap a b).trans σ) (fun σ => (Equiv.swap a b).trans σ)
    · intro σ hσ
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hσ ⊢
      simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using hσ
    · intro σ hσ
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hσ ⊢
      simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using hσ
    · intro σ _; ext x; simp [Equiv.swap_apply_self]
    · intro σ _; ext x; simp [Equiv.swap_apply_self]
  have hu := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Equiv.Perm (Fin (n + 2))))) (p := fun σ => (σ a : ℕ) < σ b)
  have hneg : (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) => ¬ (σ a : ℕ) < σ b) =
      (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) => (σ b : ℕ) < σ a) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, not_lt]
    constructor
    · intro h
      rcases Nat.lt_or_eq_of_le h with h' | h'
      · exact h'
      · exact absurd (σ.injective (Fin.ext h').symm) hab
    · exact fun h => h.le
  rw [hneg, ← e, card_univ] at hu
  omega

/-- The number of moves as a sum of indicators. -/
theorem moves_eq (N : ℕ) (n₀ : Fin (n + 2) → ℕ) (σ : Equiv.Perm (Fin (n + 2))) :
    moves N n₀ σ = ∑ i, ind ((cycle N n₀ σ).moved i) := by
  unfold moves; rw [Finset.card_filter]; rfl

/-- **The exclusion limit of one-packet lanes.**  On a ring of `L = n + 2` lanes of depth `1`,
from any configuration, the number of moves summed over all `L!` orders of the turns is at most
`L * L! / 2`: under the random-shuffle update the expected number of moves per lane and cycle is at
most `1/2`. -/
theorem half_bound (n₀ : Fin (n + 2) → ℕ) (h1 : ∀ k, n₀ k ≤ 1) :
    2 * ∑ σ : Equiv.Perm (Fin (n + 2)), moves 1 n₀ σ ≤
      (n + 2) * Fintype.card (Equiv.Perm (Fin (n + 2))) := by
  simp_rw [moves_eq]
  rw [Finset.sum_comm]
  set C := Fintype.card (Equiv.Perm (Fin (n + 2))) with hC
  have per : ∀ i, 2 * ∑ σ : Equiv.Perm (Fin (n + 2)), ind ((cycle 1 n₀ σ).moved i) ≤
      C * ((if n₀ i = 1 then 1 else 0) + (if n₀ (nx i) = 0 then 1 else 0)) := by
    intro i
    by_cases hi : n₀ i = 0
    · have : ∀ σ, (cycle 1 n₀ σ).moved i = false := by
        intro σ; by_contra hc
        have := (moved_spec 1 n₀ σ _ i (by simpa [cycle] using hc)).2.1; omega
      simp [this, ind]
    · have hi1 : n₀ i = 1 := by have := h1 i; omega
      have hle : ∑ σ : Equiv.Perm (Fin (n + 2)), ind ((cycle 1 n₀ σ).moved i) ≤ C := by
        calc ∑ σ : Equiv.Perm (Fin (n + 2)), ind ((cycle 1 n₀ σ).moved i)
            ≤ ∑ _σ : Equiv.Perm (Fin (n + 2)), 1 :=
              sum_le_sum fun σ _ => by unfold ind; split_ifs <;> simp
          _ = C := by simp [hC]
      by_cases hn : n₀ (nx i) = 0
      · simp only [hi1, hn, ite_true]; omega
      · have hn1 : 1 ≤ n₀ (nx i) := by omega
        have hhalf : ∑ σ : Equiv.Perm (Fin (n + 2)), ind ((cycle 1 n₀ σ).moved i) ≤
            (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) => (σ (nx i) : ℕ) < σ i).card := by
          rw [Finset.card_filter]
          apply sum_le_sum; intro σ _
          unfold ind
          split_ifs with hm hlt <;> try simp
          exact hlt (moved_order n₀ σ i hn1 hm)
        have hc := card_lt (nx i) i (nx_ne i)
        simp only [hi1, hn, ite_true, ite_false]; omega
  calc 2 * ∑ i, ∑ σ : Equiv.Perm (Fin (n + 2)), ind ((cycle 1 n₀ σ).moved i)
      = ∑ i, 2 * ∑ σ : Equiv.Perm (Fin (n + 2)), ind ((cycle 1 n₀ σ).moved i) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i, C * ((if n₀ i = 1 then 1 else 0) + (if n₀ (nx i) = 0 then 1 else 0)) :=
        sum_le_sum fun i _ => per i
    _ = C * (∑ i, ((if n₀ i = 1 then 1 else 0) + (if n₀ i = 0 then 1 else 0))) := by
        rw [← Finset.mul_sum, sum_add_distrib, sum_add_distrib]
        congr 2
        exact Fintype.sum_equiv rot _ _ (fun _ => rfl)
    _ = (n + 2) * C := by
        have : ∀ i, ((if n₀ i = 1 then 1 else 0) + (if n₀ i = 0 then 1 else 0) : ℕ) = 1 := by
          intro i; have := h1 i; split_ifs <;> omega
        simp [this, mul_comm]

/-- `half_bound` as an expectation: the mean number of moves per lane over a uniformly random
order of the turns is at most `1/2`, from every configuration of one-packet lanes. -/
theorem half_bound_rat (n₀ : Fin (n + 2) → ℕ) (h1 : ∀ k, n₀ k ≤ 1) :
    (∑ σ : Equiv.Perm (Fin (n + 2)), (moves 1 n₀ σ : ℚ)) /
      ((n + 2) * Fintype.card (Equiv.Perm (Fin (n + 2)))) ≤ 1 / 2 := by
  have h := half_bound n₀ h1
  have hpos : (0 : ℚ) < (n + 2) * Fintype.card (Equiv.Perm (Fin (n + 2))) := by
    have : 0 < Fintype.card (Equiv.Perm (Fin (n + 2))) :=
      Fintype.card_pos_iff.2 ⟨Equiv.refl _⟩
    positivity
  rw [div_le_iff₀ hpos]
  have h' : (2 : ℚ) * ∑ σ : Equiv.Perm (Fin (n + 2)), (moves 1 n₀ σ : ℚ) ≤
      (n + 2) * Fintype.card (Equiv.Perm (Fin (n + 2))) := by exact_mod_cast h
  linarith

/-- **The bound is attained.**  In an alternating configuration (every other lane full) every
full lane moves, whatever the order: `L/2` moves in every cycle, and the configuration is the
same one rotated by one lane. -/
theorem alternating_moves (n₀ : Fin (n + 2) → ℕ) (halt : ∀ i, n₀ i + n₀ (nx i) = 1)
    (σ : Equiv.Perm (Fin (n + 2))) : 2 * moves 1 n₀ σ = n + 2 := by
  have hm : ∀ i, ind ((cycle 1 n₀ σ).moved i) = n₀ i := by
    intro i
    have := halt i
    by_cases hi : n₀ i = 1
    · rw [moved_of_room 1 n₀ σ i (by omega) (by omega)]; simp [ind, hi]
    · have h0 : n₀ i = 0 := by omega
      have : (cycle 1 n₀ σ).moved i = false := by
        by_contra hc
        have := (moved_spec 1 n₀ σ _ i (by simpa [cycle] using hc)).2.1; omega
      simp [this, ind, h0]
  rw [moves_eq]
  simp_rw [hm]
  have hs : ∑ i, n₀ (nx i) = ∑ i, n₀ i := Fintype.sum_equiv rot _ _ (fun _ => rfl)
  have : ∑ i, (n₀ i + n₀ (nx i)) = n + 2 := by simp [halt]
  rw [sum_add_distrib, hs] at this
  omega

end Ring

end Packet

end AsyncLean
