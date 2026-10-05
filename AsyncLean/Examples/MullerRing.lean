/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.MarkedGraph.Basic
import AsyncLean.AxiomAudit

/-!
# Example: Muller pipeline rings of every size

A ring of `n = m + 2` Muller C-element stages `t₀ … t_{n-1}` connected by four-phase
handshakes is modelled by the marked graph with, for every stage `i`,

* a *forward* place `(true, i)` from `tᵢ` to `tᵢ₊₁` (a data token / request), and
* a *backward* place `(false, i)` from `tᵢ₊₁` to `tᵢ` (a bubble / acknowledge),

indices modulo `n`.  Initially the first `k` stages hold tokens and the others hold bubbles.

We prove, **for all ring sizes and token counts at once** (no state-space exploration):

* `live_iff` : the ring is live (no stage ever starves) iff `1 ≤ k ≤ n - 1`, i.e. it needs
  at least one token and at least one bubble;
* `deadlockFree` : hence it never deadlocks in that range;
* `deadlock_of_full` / `deadlock_of_empty` : and it is dead otherwise;
* `safe` : it is always 1-safe (every handshake place holds at most one token), as
  required for a speed-independent implementation;

using Commoner's theorem from `AsyncLean.MarkedGraph.Basic`.  All circuits of this graph
are characterised by the rank certificate below — no enumeration of circuits needed.
-/

namespace AsyncLean.Examples.MullerRing

open MarkedGraph

/-- The Muller ring with `m + 2` stages. -/
def ring (m : ℕ) : MarkedGraph (Bool × Fin (m + 2)) (Fin (m + 2)) where
  src p := if p.1 then p.2 else p.2 + 1
  dst p := if p.1 then p.2 + 1 else p.2

/-- Tokens in the forward places of stages `0 … k-1`, bubbles in all other stages. -/
def init (m k : ℕ) : Marking (Bool × Fin (m + 2)) :=
  fun p => if p.1 = decide (p.2.val < k) then 1 else 0

theorem val_succ {m : ℕ} (i : Fin (m + 2)) :
    ((i + 1 : Fin (m + 2)) : ℕ) = if i.val = m + 1 then 0 else i.val + 1 := by
  rw [Fin.val_add_one]
  simp only [Fin.ext_iff, Fin.val_last]

theorem exists_add_one {m : ℕ} (t : Fin (m + 2)) : ∃ i : Fin (m + 2), i + 1 = t := by
  by_cases h : t.val = 0
  · refine ⟨Fin.last (m + 1), Fin.ext ?_⟩
    rw [val_succ]; simp [h]
  · refine ⟨⟨t.val - 1, by omega⟩, Fin.ext ?_⟩
    have := t.isLt
    rw [val_succ]
    show (if t.val - 1 = m + 1 then 0 else t.val - 1 + 1) = t.val
    split_ifs <;> omega

/-- **Liveness (sufficiency)**: with at least one token and one bubble the ring is live.
The rank certificate orders the stages along the empty places. -/
theorem circuitsMarked {m k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ m + 1) :
    (ring m).CircuitsMarked (init m k) := by
  refine circuitsMarked_of_rank
    (fun i => if i.val = 0 then m + 2 else if k ≤ i.val then i.val - k else k - i.val) ?_
  rintro ⟨b, i⟩ h0
  have hi := i.isLt
  have hs := val_succ i
  unfold init at h0
  split_ifs at h0 with hc
  cases b
  · -- backward place `tᵢ₊₁ → tᵢ`, empty iff `i < k`
    have hik : i.val < k := by simpa using hc
    simp only [ring, Bool.false_eq_true, ↓reduceIte]
    split_ifs at hs ⊢ <;> omega
  · -- forward place `tᵢ → tᵢ₊₁`, empty iff `k ≤ i`
    have hik : k ≤ i.val := by simpa using hc
    simp only [ring, ↓reduceIte]
    split_ifs at hs ⊢ <;> omega

theorem live {m k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ m + 1) :
    (ring m).toNet.lts.Live (init m k) :=
  live_of_circuitsMarked (circuitsMarked hk hk')

theorem deadlockFree {m k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ m + 1) :
    (ring m).toNet.lts.DeadlockFree (init m k) :=
  deadlockFree_of_circuitsMarked (circuitsMarked hk hk')

/-- **Without tokens** the ring is dead immediately: every stage waits for a token. -/
theorem dead_of_empty (m : ℕ) : (ring m).toNet.IsDead (init m 0) := by
  intro t ht
  obtain ⟨i, hi⟩ := exists_add_one t
  have := enabled_iff.1 ht (true, i) (by simp [ring, hi])
  simp [init] at this

/-- **Without bubbles** (`k ≥ n`) the ring is dead immediately: every stage waits for an
acknowledge. -/
theorem dead_of_full {m k : ℕ} (hk : m + 2 ≤ k) : (ring m).toNet.IsDead (init m k) := by
  intro t ht
  have := enabled_iff.1 ht (false, t) (by simp [ring])
  have : t.val < k := by omega
  simp_all [init]

/-- **Commoner's theorem for Muller rings**: the ring is live exactly when it holds at least
one token and at least one bubble. -/
theorem live_iff {m k : ℕ} : (ring m).toNet.lts.Live (init m k) ↔ 1 ≤ k ∧ k ≤ m + 1 := by
  refine ⟨fun h => ?_, fun h => live h.1 h.2⟩
  have hd := h.deadlockFree
  by_contra hk
  rcases Nat.lt_or_ge k 1 with hk0 | hk1
  · obtain rfl : k = 0 := by omega
    exact hd _ (LTS.Reachable.refl _) (Net.lts_isDeadlock_iff.2 (dead_of_empty m))
  · exact hd _ (LTS.Reachable.refl _) (Net.lts_isDeadlock_iff.2 (dead_of_full (by omega)))

/-- The handshake of stage `i` (forward and backward place) is a circuit with exactly one
token. -/
theorem handshake_circuit {m : ℕ} (k : ℕ) (i : Fin (m + 2)) :
    (ring m).IsCircuit [(true, i), (false, i)] ∧
      tokens (init m k) [(true, i), (false, i)] = 1 := by
  refine ⟨⟨⟨rfl, trivial⟩, rfl⟩, ?_⟩
  by_cases h : i.val < k <;> simp [tokens, init, h]

/-- **Safeness**: for every size and every initial number of tokens, no place of the ring
ever holds more than one token. -/
theorem safe {m k : ℕ} {M : Marking (Bool × Fin (m + 2))}
    (hr : (ring m).toNet.lts.Reachable (init m k) M) (p : Bool × Fin (m + 2)) : M p ≤ 1 := by
  refine safe_of_circuit_cover (fun p => ?_) hr p
  obtain ⟨hc, ht⟩ := handshake_circuit k p.2
  refine ⟨_, hc, ?_, ht.le⟩
  obtain ⟨b, i⟩ := p
  cases b <;> simp

#assert_standard_axioms circuitsMarked live deadlockFree live_iff safe

end AsyncLean.Examples.MullerRing
