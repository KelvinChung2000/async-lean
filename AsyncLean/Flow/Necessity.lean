/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Flow.Backpressure
import AsyncLean.Flow.GraphPatterns

/-!
# Adaptivity is necessary: shortest paths alone lose throughput

Backpressure reaches the fluid optimum (`Fluid.Run.backpressure_optimal`) because it may move
traffic along any link, detours included.  This file proves that this freedom is needed: a
scheduler that moves every packet only along shortest paths — whatever else it does, however it
uses the backlogs — is bounded by the fluid optimum *over minimal routings*, which can be far
below the optimum.

* `GraphCert.Model.run_minimal_ceiling` : on a network certified by a port graph
  (`GraphCert.Model`), a stable queueing run whose transmissions all bring their traffic
  strictly closer to its destination is bounded by every dual certificate on the minimal links
  (the ones the library checks in the kernel).  The bridge is `Fluid.PotentialFeasibleOn`: a
  stable run respects every potential bound on the links it uses
  (`Fluid.Run.potentialFeasibleOn`), as a flow does.
* `torusTornado_adaptivity` : **tornado traffic on the `8 × 8` torus.**  Backpressure is stable
  at every load below `16/15`; no scheduler moving traffic only along shortest paths keeps a
  bounded backlog above `2/3`.  Between `2/3` and `16/15` only adaptive, non-minimal scheduling
  is stable.
* `Run.backpressure_progress` : **backpressure never deadlocks**: on a network where every
  destination is reachable, whenever traffic is queued some traffic moves.
  `mesh_finite_buffer_network` : on the mesh with `m` connections, under a load `(1 - δ)` times
  the optimum, backpressure from empty fits in buffers of `145 m k⁷ / (16 δ) + m` packets per
  destination, never deadlocks, and is stable: a finite-buffer network near the optimum without
  deadlock.
* `Run.singleHead_ceiling`, `mesh_headOfLine` : **head-of-line blocking**: a vertex with one
  first-in first-out queue sends at most one packet per slot, so no such run is stable above one
  packet per vertex and slot, whatever the capacities; on the mesh with `m` connections,
  backpressure with a queue per destination is stable up to `m` times the optimum.  Per
  destination queues are necessary for linear scaling.
-/

namespace AsyncLean

namespace Fluid

open Finset GraphCert GraphPatternData

namespace GraphCert

namespace Model

variable {V : Type*} [Fintype V] [DecidableEq V] {G : PortGraph} {C : ℕ} {N : Net V}
  {dist : V → V → ℚ}

omit [DecidableEq V] in
/-- **Potential bounds transfer along a model**: respecting the potential bounds of `N` on the
links `S` is respecting those of the port graph's network on the image of `S`. -/
theorem potentialFeasibleOn_transfer (M : Model G C N dist) {dem : V → V → ℚ}
    {demN : ℕ → ℕ → ℕ} {R : ℕ} (hdem : ∀ s d, dem s d = (demN (M.e s) (M.e d) : ℚ) / R)
    {S : Fin G.n → Fin G.n → Fin G.n → Prop} {θ : ℚ}
    (h : PotentialFeasibleOn N (fun d u v => S (M.e d) (M.e u) (M.e v)) dem θ) :
    PotentialFeasibleOn (G.net C) S (fun a b => (demN a b : ℚ) / R) θ := by
  intro len φ hlen hφd hφ hφ0
  have key := h (fun u v => len (M.e u) (M.e v)) (fun d v => φ (M.e d) (M.e v))
    (fun u v => hlen _ _) (fun d => hφd _)
    (fun d u v hS hc => hφ _ _ _ hS (by rw [← M.cap_eq]; exact hc)) (fun d v => hφ0 _ _)
  simp only [hdem, M.cap_eq] at key
  have e1 : ∑ s, ∑ d, (demN (M.e s) (M.e d) : ℚ) / R * φ (M.e d) (M.e s) =
      ∑ a : Fin G.n, ∑ b : Fin G.n, (demN a b : ℚ) / R * φ b a := by
    rw [M.e.sum_comp (fun a : Fin G.n => ∑ d, (demN a (M.e d) : ℚ) / R * φ (M.e d) a)]
    exact sum_congr rfl fun a _ =>
      M.e.sum_comp (fun b : Fin G.n => (demN a b : ℚ) / R * φ b a)
  have e2 : ∑ u, ∑ v, (G.net C).cap (M.e u) (M.e v) * len (M.e u) (M.e v) =
      ∑ a : Fin G.n, ∑ b : Fin G.n, (G.net C).cap a b * len a b := by
    rw [M.e.sum_comp (fun a : Fin G.n => ∑ v, (G.net C).cap a (M.e v) * len a (M.e v))]
    exact sum_congr rfl fun a _ =>
      M.e.sum_comp (fun b : Fin G.n => (G.net C).cap a b * len a b)
  rw [e1, e2] at key
  exact key

/-- **Shortest paths only: the minimal ceiling for runs.**  On a network certified by a port
graph, a queueing run with arrivals `ρ * dem` and a bounded backlog, whose transmissions all
bring their traffic strictly closer to its destination, has `ρ ≤ p / q` for every dual
certificate on the minimal links. -/
theorem run_minimal_ceiling (M : Model G C N dist) (dem : V → V → ℚ) (demN : ℕ → ℕ → ℕ)
    (R : ℕ) (hdem : ∀ s d, dem s d = (demN (M.e s) (M.e d) : ℚ) / R) (phi lenT : ℕ → ℕ → ℕ)
    (p q : ℕ) (hR : 0 < R) (hq : 0 < q) (hd : G.dualCheck phi lenT true = true)
    (hb : G.boundCheck C demN phi lenT R p q = true) (r : Run N) {ρ : ℚ}
    (harr : ∀ t v d, v ≠ d → r.a t v d = ρ * dem v d) (hbd : r.BoundedBacklog)
    (hmin : ∀ t d u v, 0 < r.x t d u v → dist v d < dist u d) :
    ρ ≤ (p : ℚ) / q := by
  refine PortGraph.upper_of_check' C M.wf M.near (fun a b => (demN a b : ℚ) / R) demN R
    (fun _ _ => rfl) phi lenT true p q hR hq hd hb (M.potentialFeasibleOn_transfer hdem ?_)
  refine r.potentialFeasibleOn harr hbd fun t d u v h => Or.inr ?_
  have := hmin t d u v h
  rwa [M.dist_eq, M.dist_eq] at this

end Model

end GraphCert

/-- Tornado traffic is nonnegative. -/
theorem tornado8_nonneg (s d : Fin 8 × Fin 8) : 0 ≤ tornado8 s d := by
  rw [torusTornado_dem]; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Adaptivity is necessary: tornado traffic on the `8 × 8` torus.**  Backpressure keeps a
bounded backlog and delivers everything at every load `0 ≤ ρ < 16/15` (the fluid optimum,
`torusTornado_opt`); no scheduler whose transmissions all follow shortest paths keeps a bounded
backlog at a load above `2/3` (the optimum over minimal routings, `torusTornado_minimal_opt`). -/
theorem torusTornado_adaptivity (r : Run (torusNet 8)) {ρ : ℚ} :
    (r.Backpressure → 0 ≤ ρ → ρ < 16 / 15 →
        (∀ t v d, v ≠ d → r.a t v d ≤ ρ * tornado8 v d) → r.Stable) ∧
      ((∀ t v d, v ≠ d → r.a t v d = ρ * tornado8 v d) → r.BoundedBacklog →
        (∀ t d u v, 0 < r.x t d u v → torusDist v d < torusDist u d) → ρ ≤ 2 / 3) := by
  refine ⟨fun hr hρ hρθ harr => ?_, fun harr hbd hmin => ?_⟩
  · obtain ⟨hunn, hunc⟩ := uniform_props (k := 8) (by norm_num)
    exact r.backpressure_optimal hr torusTornado_opt.1 torus_uniform_opt_eight.1.1
      tornado8_nonneg hunn (c := 1 / (((8 : ℕ) : ℚ) ^ 2 - 1)) (by norm_num) hunc (by norm_num)
      hρ hρθ harr
  · have h := torusModel.run_minimal_ceiling tornado8 _ 1 torusTornado_dem torusTornadoMinP
      torusTornadoMinL 2 3 one_pos (by norm_num) torusTornadoMin_dual torusTornadoMin_bound r
      harr hbd hmin
    norm_num at h ⊢
    exact h

/-- Between `2/3` and `16/15` only non-minimal scheduling is stable. -/
theorem torusTornado_gap : (2 / 3 : ℚ) < 16 / 15 := by norm_num


/-! ### Finite buffers, no deadlock, near the optimum -/

section Progress

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `d` is reachable from `v` along links of positive capacity. -/
inductive Net.Reach (N : Net V) (d : V) : V → Prop
  | here : Net.Reach N d d
  | step {v w : V} : 0 < N.cap v w → Net.Reach N d w → Net.Reach N d v

namespace Run

variable {N : Net V} (r : Run N)

/-- **No deadlock**: whenever the network holds traffic, some traffic moves. -/
def Progress : Prop := ∀ t, 0 < backlog (r.Q t) → ∃ d u v, 0 < r.x t d u v

omit [DecidableEq V] in
/-- Along a path to `d`, a positive backlog for `d` drops across some link. -/
theorem descent (t : ℕ) {d v : V} (hreach : N.Reach d v) (hpos : 0 < r.Q t v d) :
    ∃ u w, 0 < N.cap u w ∧ r.Q t w d < r.Q t u d := by
  induction hreach with
  | here => rw [r.Q_dest] at hpos; exact absurd hpos (lt_irrefl 0)
  | @step v w hcap _ ih =>
    by_cases h : r.Q t w d < r.Q t v d
    · exact ⟨v, w, hcap, h⟩
    · exact ih (lt_of_lt_of_le hpos (not_lt.1 h))

/-- **Backpressure never deadlocks** on a network in which every destination is reachable from
every vertex: whenever traffic is queued, some traffic moves.  (Across some link of a path to
its destination the backlog drops; that link has positive weight, so the max-weight rates are
positive somewhere with a positive backlog difference, and work conservation sends.) -/
theorem backpressure_progress (hr : r.Backpressure) (hconn : ∀ v d, N.Reach d v) :
    r.Progress := by
  intro t hb
  -- a positive backlog
  obtain ⟨d₀, v₀, hpos⟩ : ∃ d v, 0 < r.Q t v d := by
    by_contra hn
    simp only [not_exists, not_lt] at hn
    have : backlog (r.Q t) ≤ 0 := sum_nonpos fun d _ => sum_nonpos fun v _ => hn d v
    linarith
  have : Nonempty V := ⟨v₀⟩
  obtain ⟨u₀, w₀, hcap, hdrop⟩ := r.descent t (hconn v₀ d₀) hpos
  -- the backpressure rates have positive weight
  have hbp : 0 < weight (r.Q t) (bpRates N (r.Q t)) := by
    rw [weight_comm]
    simp only [bpRates_link]
    have hterm : ∀ u w, 0 ≤ N.cap u w *
        max (r.Q t u (best (r.Q t) u w) - r.Q t w (best (r.Q t) u w)) 0 :=
      fun u w => mul_nonneg (N.cap_nonneg u w) (le_max_right _ _)
    have h0 : 0 < N.cap u₀ w₀ *
        max (r.Q t u₀ (best (r.Q t) u₀ w₀) - r.Q t w₀ (best (r.Q t) u₀ w₀)) 0 := by
      refine mul_pos hcap (lt_of_lt_of_le ?_ (le_max_left _ _))
      have := best_spec (r.Q t) u₀ w₀ d₀
      linarith
    calc (0 : ℚ) < N.cap u₀ w₀ *
          max (r.Q t u₀ (best (r.Q t) u₀ w₀) - r.Q t w₀ (best (r.Q t) u₀ w₀)) 0 := h0
      _ ≤ ∑ w, N.cap u₀ w * max (r.Q t u₀ (best (r.Q t) u₀ w) - r.Q t w (best (r.Q t) u₀ w)) 0 :=
          single_le_sum (f := fun w => N.cap u₀ w *
            max (r.Q t u₀ (best (r.Q t) u₀ w) - r.Q t w (best (r.Q t) u₀ w)) 0)
            (fun w _ => hterm u₀ w) (mem_univ w₀)
      _ ≤ ∑ u, ∑ w, N.cap u w * max (r.Q t u (best (r.Q t) u w) - r.Q t w (best (r.Q t) u w)) 0 :=
          single_le_sum (f := fun u => ∑ w, N.cap u w *
            max (r.Q t u (best (r.Q t) u w) - r.Q t w (best (r.Q t) u w)) 0)
            (fun u _ => sum_nonneg fun w _ => hterm u w) (mem_univ u₀)
  -- so do the run's rates: some rate is positive on a positive backlog difference
  have hw := lt_of_lt_of_le hbp (hr.1 t _ (bpRates_feasible N (r.Q t)))
  obtain ⟨d, u, v, hduv⟩ : ∃ d u v, 0 < r.μ t d u v * (r.Q t u d - r.Q t v d) := by
    by_contra hn
    simp only [not_exists, not_lt] at hn
    have : weight (r.Q t) (r.μ t) ≤ 0 :=
      sum_nonpos fun d _ => sum_nonpos fun u _ => sum_nonpos fun v _ => hn d u v
    linarith
  have hμ0 := (r.μ_feasible t).1 d u v
  have hμ : 0 < r.μ t d u v := by
    rcases hμ0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hduv; exact absurd hduv (lt_irrefl 0)
  have hdiff : 0 < r.Q t u d - r.Q t v d := pos_of_mul_pos_right hduv hμ0
  have hQ : 0 < r.Q t u d := by linarith [r.Q_nonneg t v d]
  -- work conservation sends
  have hsum : 0 < ∑ v, r.μ t d u v :=
    lt_of_lt_of_le hμ (single_le_sum (f := fun v => r.μ t d u v)
      (fun v _ => (r.μ_feasible t).1 d u v) (mem_univ v))
  have hx := lt_of_lt_of_le (lt_min hQ hsum) (hr.2 t d u)
  obtain ⟨v', hv'⟩ : ∃ v', 0 < r.x t d u v' := by
    by_contra hn
    simp only [not_exists, not_lt] at hn
    have : ∑ v, r.x t d u v ≤ 0 := sum_nonpos fun v _ => hn v
    linarith
  exact ⟨d, u, v', hv'⟩

end Run

end Progress

/-- Every vertex of the mesh with `m ≥ 1` connections per link reaches every other. -/
theorem mesh_reach (k : ℕ) {m : ℕ} (hm : 0 < m) (d v : Fin k × Fin k) :
    ((meshNet k).copies m).Reach d v := by
  have hcap : ∀ u w : Fin k × Fin k, MeshAdj u w → 0 < ((meshNet k).copies m).cap u w :=
    fun u w h => by
      show (0 : ℚ) < m * (if MeshAdj u w then 2 else 0)
      rw [ite_eq_left h]; positivity
  suffices H : ∀ n (v : Fin k × Fin k),
      (Int.natAbs ((v.1 : ℤ) - d.1) + Int.natAbs ((v.2 : ℤ) - d.2)) = n →
        ((meshNet k).copies m).Reach d v from H _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn
    by_cases hvd : v = d
    · subst hvd; exact Net.Reach.here
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := v
    obtain ⟨⟨c, hc⟩, ⟨e, he⟩⟩ := d
    simp only at hn
    rcases lt_trichotomy a c with h | h | h
    · refine Net.Reach.step (w := (⟨a + 1, by omega⟩, ⟨b, hb⟩)) (hcap _ _ ?_) (ih _ ?_ _ rfl)
      · left; exact ⟨rfl, Or.inl rfl⟩
      · simp only; omega
    · subst h
      rcases lt_trichotomy b e with h' | h' | h'
      · refine Net.Reach.step (w := (⟨a, ha⟩, ⟨b + 1, by omega⟩)) (hcap _ _ ?_) (ih _ ?_ _ rfl)
        · right; exact ⟨rfl, Or.inl rfl⟩
        · simp only; omega
      · subst h'; exact absurd rfl hvd
      · refine Net.Reach.step (w := (⟨a, ha⟩, ⟨b - 1, by omega⟩)) (hcap _ _ ?_) (ih _ ?_ _ rfl)
        · right; refine ⟨rfl, Or.inr ?_⟩; show b - 1 + 1 = b; omega
        · simp only; omega
    · refine Net.Reach.step (w := (⟨a - 1, by omega⟩, ⟨b, hb⟩)) (hcap _ _ ?_) (ih _ ?_ _ rfl)
      · left; refine ⟨rfl, Or.inr ?_⟩; show a - 1 + 1 = a; omega
      · simp only; omega

/-- **A finite-buffer network near the optimum, without deadlock** (the mesh with `m`
connections per link, `k ≥ 2`, uniform traffic, `θ = m · 8 (k² - 1) / k³`).  Started empty, under
any load at most `(1 - δ) θ`, a backpressure run
* never holds more than `145 m k⁷ / (16 δ) + m` packets in any per-destination queue: buffers of
  that size never overflow, so the run is the finite-buffer one;
* never deadlocks: whenever traffic is queued, some traffic moves;
* is stable: its backlog stays bounded and it delivers everything that arrives, up to a
  constant. -/
theorem mesh_finite_buffer_network (k : ℕ) (hk : 2 ≤ k) {m : ℕ} (hm : 0 < m) {δ : ℚ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (r : Run ((meshNet k).copies m)) (hr : r.Backpressure)
    (h0 : ∀ v d, r.Q 0 v d = 0)
    (harr : ∀ t v d, v ≠ d →
      r.a t v d ≤ (1 - δ) * (m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3)) * uniform k v d) :
    r.FitsIn (145 * m * k ^ 7 / (16 * δ) + m) ∧ r.Progress ∧ r.Stable := by
  obtain ⟨hfit, hdel⟩ := mesh_buffer k hk hm hδ hδ1 r hr h0 harr
  refine ⟨hfit, r.backpressure_progress hr (fun v d => mesh_reach k hm d v), ?_⟩
  have hbnn : (0 : ℚ) ≤ 145 * m * k ^ 7 / (16 * δ) + m :=
    add_nonneg (div_nonneg (by positivity) (by linarith)) (Nat.cast_nonneg m)
  refine ⟨(Fintype.card (Fin k × Fin k) : ℚ) ^ 2 * (145 * m * k ^ 7 / (16 * δ) + m) +
    (k : ℚ) ^ 4 * (145 * m * k ^ 7 / (16 * δ) + m), fun t => ⟨?_, ?_⟩⟩
  · have hb : backlog (r.Q t) ≤ ∑ _d : Fin k × Fin k, ∑ _v : Fin k × Fin k,
        (145 * (m : ℚ) * k ^ 7 / (16 * δ) + m) :=
      sum_le_sum fun d _ => sum_le_sum fun v _ => hfit t v d
    have e : ∑ _d : Fin k × Fin k, ∑ _v : Fin k × Fin k, (145 * (m : ℚ) * k ^ 7 / (16 * δ) + m) =
        (Fintype.card (Fin k × Fin k) : ℚ) ^ 2 * (145 * m * k ^ 7 / (16 * δ) + m) := by
      simp only [sum_const, card_univ, nsmul_eq_mul]; ring
    have : (0 : ℚ) ≤ (k : ℚ) ^ 4 * (145 * m * k ^ 7 / (16 * δ) + m) :=
      mul_nonneg (by positivity) hbnn
    linarith
  · have := hdel t
    have : (0 : ℚ) ≤ (Fintype.card (Fin k × Fin k) : ℚ) ^ 2 * (145 * m * k ^ 7 / (16 * δ) + m) :=
      mul_nonneg (by positivity) hbnn
    linarith

/-! ### Head-of-line blocking: one head per vertex does not scale -/

namespace Run

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Net V} (r : Run N)

/-- **A single head per vertex**: every vertex sends at most one packet per slot in all, as a
vertex with one first-in first-out queue for all destinations does (only the packet at its head
can leave). -/
def SingleHead : Prop := ∀ t u, ∑ d, ∑ v, r.x t d u v ≤ 1

omit [DecidableEq V] in
/-- With a single head per vertex, at most `|V|` packets are delivered per slot. -/
theorem delivered_le_card (h : r.SingleHead) (t : ℕ) : r.delivered t ≤ Fintype.card V := by
  unfold delivered
  calc ∑ d, ∑ u, r.x t d u d ≤ ∑ d, ∑ u, ∑ v, r.x t d u v :=
        sum_le_sum fun d _ => sum_le_sum fun u _ =>
          single_le_sum (f := fun v => r.x t d u v) (fun v _ => r.x_nonneg t d u v) (mem_univ d)
    _ = ∑ u, ∑ d, ∑ v, r.x t d u v := sum_comm
    _ ≤ ∑ _u : V, (1 : ℚ) := sum_le_sum fun u _ => h t u
    _ = Fintype.card V := by simp

/-- **Head-of-line ceiling**: a single-head run whose arrivals total `A` per slot and whose
backlog stays bounded has `A ≤ |V|`, whatever the capacities. -/
theorem singleHead_ceiling (h : r.SingleHead) {A : ℚ} (harr : ∀ t, r.arrived t = A)
    (hb : r.BoundedBacklog) : A ≤ Fintype.card V := by
  obtain ⟨C, hC⟩ := hb
  have hT : ∀ T : ℕ, (T : ℚ) * A ≤ T * Fintype.card V + C := by
    intro T
    have h1 := r.delivered_sum T
    have h2 : ∑ t ∈ range T, r.delivered t ≤ T * Fintype.card V := by
      calc ∑ t ∈ range T, r.delivered t ≤ ∑ _t ∈ range T, (Fintype.card V : ℚ) :=
            sum_le_sum fun t _ => r.delivered_le_card h t
        _ = T * Fintype.card V := by simp
    have h3 : ∑ t ∈ range T, r.arrived t = T * A := by simp [harr]
    have := hC T
    have := r.backlog_nonneg 0
    linarith
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hT'⟩ := exists_nat_gt_rat (C / (A - Fintype.card V))
  have hpos : 0 < A - Fintype.card V := by linarith
  rw [div_lt_iff₀ hpos] at hT'
  have := hT T
  have := mul_sub (T : ℚ) A (Fintype.card V)
  linarith

end Run

/-- Uniform traffic totals one packet per vertex and slot at load one. -/
theorem uniform_total (k : ℕ) (hk : 2 ≤ k) :
    ∑ d : Fin k × Fin k, ∑ v : Fin k × Fin k, uniform k v d = (k : ℚ) ^ 2 := by
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
  have e : ∀ d : Fin k × Fin k, ∑ v, uniform k v d = 1 := fun d => by
    have : ∀ v, uniform k v d = 1 / ((k : ℚ) ^ 2 - 1) - if v = d then 1 / ((k : ℚ) ^ 2 - 1) else 0 :=
      fun v => by unfold uniform; split_ifs <;> simp
    simp only [this, sum_sub_distrib, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
      sum_ite_eq', mem_univ, ite_true, nsmul_eq_mul]
    push_cast
    rw [show (k : ℚ) * k * (1 / ((k : ℚ) ^ 2 - 1)) - 1 / ((k : ℚ) ^ 2 - 1) =
        ((k : ℚ) ^ 2 - 1) * (1 / ((k : ℚ) ^ 2 - 1)) by ring, mul_one_div_cancel hK.ne']
  simp only [e, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

/-- **Per-destination queues are necessary for linear scaling** (the mesh with `m` connections
per link, `k ≥ 2`, uniform traffic).  At every load `ρ` with `1 < ρ < m · 8 (k² - 1) / k³`
(nonempty once `m` is large enough, `m ≥ 2` for `k = 8`), backpressure, with a queue per
destination, keeps a bounded backlog and delivers everything; no run in which every vertex
sends at most one packet per slot (a single first-in first-out queue per vertex) keeps a bounded
backlog, whatever its capacities. -/
theorem mesh_headOfLine (k : ℕ) (hk : 2 ≤ k) {m : ℕ} {ρ : ℚ} (hρ1 : 1 < ρ)
    (hρθ : ρ < m * (8 * ((k : ℚ) ^ 2 - 1) / k ^ 3)) :
    (∀ r : Run ((meshNet k).copies m), r.Backpressure →
        (∀ t v d, v ≠ d → r.a t v d ≤ ρ * uniform k v d) → r.Stable) ∧
      (∀ r : Run ((meshNet k).copies m), r.SingleHead →
        (∀ t v d, v ≠ d → r.a t v d = ρ * uniform k v d) → ¬ r.BoundedBacklog) := by
  refine ⟨fun r hr harr => ?_, fun r hh harr hb => ?_⟩
  · have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have hK : (0 : ℚ) < (k : ℚ) ^ 2 - 1 := by nlinarith
    obtain ⟨hunn, hunc⟩ := uniform_props hk
    have hR := (mesh_routable k hk).copies m
    exact r.backpressure_optimal hr hR hR hunn hunn (div_pos one_pos hK) hunc
      (by linarith) (by linarith) hρθ harr
  · have hA : ∀ t, r.arrived t = ρ * (k : ℚ) ^ 2 := fun t => by
      unfold Run.arrived
      have e : ∀ d v, r.a t v d = ρ * uniform k v d := fun d v => by
        by_cases h : v = d
        · subst h; rw [r.a_dest]; simp [uniform]
        · exact harr t v d h
      simp only [e, ← mul_sum, uniform_total k hk]
    have := r.singleHead_ceiling hh hA hb
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    push_cast at this
    have hk2 : (0 : ℚ) < (k : ℚ) ^ 2 := by
      have : (2 : ℚ) ≤ k := by exact_mod_cast hk
      positivity
    nlinarith


/-! ### Backpressure restricted to permitted links reaches the optimum over them -/

namespace Run

variable {V : Type*} [Fintype V] [DecidableEq V] {N : Net V} (r : Run N)

/-- **Backpressure restricted to the links `S`** (`S d u v`: commodity `d` may use `u → v`, for
instance the hops a certified packet network permits): rates offered only on `S`, max-weight
among such rates, work conserving. -/
def BackpressureOn (S : V → V → V → Prop) : Prop :=
  (∀ t μ', Feasible N μ' → (∀ d u v, ¬ S d u v → μ' d u v = 0) →
      weight (r.Q t) μ' ≤ weight (r.Q t) (r.μ t)) ∧
    r.WorkConserving ∧ ∀ t d u v, ¬ S d u v → r.μ t d u v = 0

omit [DecidableEq V] in
/-- A restricted backpressure run moves traffic only on `S`. -/
theorem BackpressureOn.supported {S : V → V → V → Prop} (hr : r.BackpressureOn S) :
    ∀ t d u v, 0 < r.x t d u v → S d u v := by
  intro t d u v hx
  by_contra hS
  have := r.x_le t d u v
  rw [hr.2.2 t d u v hS] at this
  linarith

/-- **Restricted backpressure reaches the optimum over its links.**  If `dem ≥ 0` is routable at
`θ` by a flow supported on `S`, and some traffic `J` reaching every pair is routable at `η > 0` on
`S`, then under every load `ρ * dem` with `0 ≤ ρ < θ` a backpressure run restricted to `S` keeps
a bounded backlog and delivers everything.  (Conversely, `Run.potentialFeasibleOn` bounds every
run on `S` by every certificate on `S`.) -/
theorem backpressureOn_optimal {S : V → V → V → Prop} (hr : r.BackpressureOn S)
    {dem J : V → V → ℚ} {θ η c ρ : ℚ} (F₁ : Flow N dem θ) (hF₁ : F₁.SupportedOn S)
    (F₂ : Flow N J η) (hF₂ : F₂.SupportedOn S) (hdem : ∀ v d, 0 ≤ dem v d)
    (hJnn : ∀ v d, 0 ≤ J v d) (hc : 0 < c) (hJc : ∀ v d, v ≠ d → c ≤ J v d) (hη : 0 < η)
    (hρ : 0 ≤ ρ) (hρθ : ρ < θ) (harr : ∀ t v d, v ≠ d → r.a t v d ≤ ρ * dem v d) :
    r.Stable := by
  have hθ : 0 < θ := hρ.trans_lt hρθ
  have hα : 0 ≤ ρ / θ := div_nonneg hρ hθ.le
  have hα1 : ρ / θ < 1 := (div_lt_iff₀ hθ).2 (by linarith)
  have hβ : 0 < 1 - ρ / θ := by linarith
  let F := F₁.mix F₂ hα hβ.le (by linarith)
  -- the mixture is supported on `S`
  have hzero : ∀ d u v, ¬ S d u v → F.f d u v = 0 := fun d u v hS => by
    have h1 : F₁.f d u v = 0 := le_antisymm (not_lt.1 fun h => hS (hF₁ d u v h)) (F₁.nonneg d u v)
    have h2 : F₂.f d u v = 0 := le_antisymm (not_lt.1 fun h => hS (hF₂ d u v h)) (F₂.nonneg d u v)
    show ρ / θ * F₁.f d u v + (1 - ρ / θ) * F₂.f d u v = 0
    rw [h1, h2]; ring
  have he : ∀ v d, ρ / θ * θ * dem v d = ρ * dem v d := fun v d => by
    rw [div_mul_cancel₀ ρ hθ.ne']
  refine r.stable_of F (fun t => hr.1 t F.f F.feasible hzero) hr.2.1
    (fun v d => by have := hdem v d; have := hJnn v d; positivity)
    (ε := (1 - ρ / θ) * η * c) (by positivity) fun t v d hvd => ?_
  show r.a t v d + (1 - ρ / θ) * η * c ≤ ρ / θ * θ * dem v d + (1 - ρ / θ) * η * J v d
  rw [he]
  have h1 := harr t v d hvd
  have h2 : (1 - ρ / θ) * η * c ≤ (1 - ρ / θ) * η * J v d :=
    mul_le_mul_of_nonneg_left (hJc v d hvd) (by positivity)
  linarith

end Run

/-- **Backpressure restricted to shortest paths reaches the optimum over shortest paths,
exactly** (tornado on the `8 × 8` torus): it is stable at every load below `2/3`
(`torusTornado_minimal_opt`), and no run moving traffic only along shortest paths — this one
included — keeps a bounded backlog above `2/3`. -/
theorem torusTornado_minimal_backpressure (r : Run (torusNet 8)) {ρ : ℚ}
    (hr : r.BackpressureOn fun d u v => torusDist v d < torusDist u d) :
    (0 ≤ ρ → ρ < 2 / 3 → (∀ t v d, v ≠ d → r.a t v d ≤ ρ * tornado8 v d) → r.Stable) ∧
      ((∀ t v d, v ≠ d → r.a t v d = ρ * tornado8 v d) → r.BoundedBacklog → ρ ≤ 2 / 3) := by
  refine ⟨fun hρ hρθ harr => ?_, fun harr hbd => ?_⟩
  · obtain ⟨F₁, hF₁⟩ := torusTornado_minimal_opt.1
    obtain ⟨F₂, hF₂⟩ := torus_uniform_opt_eight.2
    obtain ⟨hunn, hunc⟩ := uniform_props (k := 8) (by norm_num)
    exact r.backpressureOn_optimal hr F₁ hF₁ F₂ hF₂ tornado8_nonneg hunn
      (c := 1 / (((8 : ℕ) : ℚ) ^ 2 - 1)) (by norm_num) hunc (by norm_num) hρ hρθ harr
  · exact (torusTornado_adaptivity r).2 harr hbd (Run.BackpressureOn.supported r hr)

end Fluid

end AsyncLean
