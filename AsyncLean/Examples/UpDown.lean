/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.Strategy
import AsyncLean.Routing.UpDown
import AsyncLean.AxiomAudit

/-!
# Example: the torus with the up*/down* escape of the simulations

The torus results of `AsyncLean.Examples.GraphDetour` and `AsyncLean.Examples.Strategy` use
tree routing along a comb spanning tree rooted at the corner `(0, 0)` as the escape layer.  The
simulations (`scripts/torus_experiments.py`, `scripts/xp_combo.py`, `scripts/xp_torus16.py`,
all through `scripts/routing_graph_sim.py`, `Net(..., escape='updown', root=...)`) use instead
**up*/down* routing over all the links of the torus**, with breadth-first levels from the
**centre** root `(k/2 - 1)(k + 1)` of the `k × k` torus (`27` at `8 × 8`, `119` at `16 × 16`).
This file restates the torus results for that escape (`AsyncLean.Routing.UpDown`).

## The torus rooted anywhere

* `torusAt k ρ` : the `(k + 1) × (k + 1)` torus of `torus k` (same vertices, neighbours in the
  same order — east, west, north, south, the port order of the simulator — and the same
  wraparound distance) with a breadth-first spanning tree rooted at **any vertex `ρ`**: the
  depth is the wraparound distance to `ρ` (`torusAt_dep_bfs`: it is the breadth-first level,
  the length of a shortest walk from `ρ`), the parent one step closer to `ρ` (first along the
  second coordinate, then along the first).
* `centre k` : the root of the simulations, `((k + 1) / 2 - 1, (k + 1) / 2 - 1)`, the vertex
  numbered `27` on the `8 × 8` torus and `119` on the `16 × 16` torus (`centre_idx_8`,
  `centre_idx_16`, with the simulator's numbering `torusIdx k (x, y) = y * (k + 1) + x`).
* `torusUD k ρ` : the up*/down* escape of the simulator: key `(level, number)`
  lexicographically (`torusUD_up_iff`: a hop `u → v` is up iff `(level v, v) < (level u, u)`),
  escape hop the first neighbour in port order starting a shortest legal up*/down* path
  (`GraphData.firstHop`), phase in the channel; with at least two positions per ring a link is
  down iff it is not up (`torusUD_down_iff_not_up`), as in the simulator.
  `simUD k = torusUD k (centre k)` is the escape of every torus simulation.

## Main results

Every theorem holds for **every size `k`, every root `ρ` and every up*/down* escape
`U : (torusAt k ρ).UpDown`** — any key making the tree's parent edges up hops and **any choice
of legal next hops decreasing the up*/down* distance** (shortest-path hops with any
tie-breaking among them included) — and every budget `B` and choice of intermediates `W`:

* `torus_ud_reach`, `torus_ud_escDep_wf` : the escape is connected (every vertex reaches every
  destination by a legal up*/down* path) and its dependency relation, with the phase in the
  channel, is well-founded;
* `torus_ud_detour_correct`, `torus_ud_detour_correct_of_sourceSel`,
  `torus_ud_detour_underLoad`, `torus_ud_detour_hops_le`, `torus_ud_valiant_correct` : the
  analogues of `torus_detour_correct`, `torus_detour_correct_of_sourceSel`,
  `torus_detour_underLoad`, `torus_detour_hops_le`, `torus_valiant_correct`;
* `torus_ud_choice_safe`, `torus_ud_lx_correct`, `torus_ud_throttle_safe`,
  `udComboStrategy` / `torus_ud_combo_safe` : the analogues of `torus_choice_safe`,
  `torus_lx_correct`, `torus_throttle_safe`, `comboStrategy` / `torus_combo_safe`: any
  history-dependent choice among the free minimal hops and of the intermediate; the `lx`
  throttle; every history-dependent throttle (thresholds up to 8, any blocking rule, read from a
  snapshot or any history); the simulated combined scheme.
* `simUD_detour_correct`, `simUD_throttle_safe`, `simUD_combo_safe` : the same for the exact
  escape of the simulations (`simUD k`, centre root).

## What is not covered

As for every torus result: nothing about throughput; fairness is assumed; the no-chaining move
model of the simulator is a different scheduling of the same moves.  On the `1 × 1` torus
(`k = 0`) the links are self-loops, which are neither up nor down hops here (the simulator calls
them down hops); no packet ever needs one.
-/

namespace AsyncLean.Examples

open Network GraphData

/-! ### The wraparound distance, one step at a time -/

theorem cycDist_self {k : ℕ} (a : Fin (k + 1)) : cycDist a a = 0 := by
  rw [cycDist_val]; split_ifs <;> omega

/-- One step forward changes the wraparound distance by at most one. -/
theorem cycDist_succ_le {k : ℕ} (a b : Fin (k + 1)) :
    cycDist (cycSucc a) b ≤ cycDist a b + 1 ∧ cycDist a b ≤ cycDist (cycSucc a) b + 1 := by
  have := a.isLt; have := b.isLt
  rw [cycDist_val, cycDist_val, cycSucc_val]
  split_ifs <;> omega

/-- One step back changes the wraparound distance by at most one. -/
theorem cycDist_pred_le {k : ℕ} (a b : Fin (k + 1)) :
    cycDist (cycPred a) b ≤ cycDist a b + 1 ∧ cycDist a b ≤ cycDist (cycPred a) b + 1 := by
  have := a.isLt; have := b.isLt
  rw [cycDist_val, cycDist_val, cycPred_val]
  split_ifs <;> omega

/-- One step towards `b` (forward if that is closer, else back). -/
def stepTo {k : ℕ} (a b : Fin (k + 1)) : Fin (k + 1) :=
  if cycDist (cycSucc a) b < cycDist a b then cycSucc a else cycPred a

/-- A step towards `b` brings `a ≠ b` exactly one closer. -/
theorem cycDist_stepTo {k : ℕ} {a b : Fin (k + 1)} (h : a ≠ b) :
    cycDist (stepTo a b) b + 1 = cycDist a b := by
  have h1 := cycDist_succ_le a b
  have h2 := cycDist_pred_le a b
  have h3 := cycDist_step h
  unfold stepTo
  split_ifs <;> omega

theorem stepTo_eq {k : ℕ} (a b : Fin (k + 1)) : stepTo a b = cycSucc a ∨ stepTo a b = cycPred a := by
  unfold stepTo; split_ifs <;> simp

/-! ### The torus with a breadth-first tree rooted anywhere -/

/-- **The `(k + 1) × (k + 1)` torus rooted at `ρ`**: the vertices, neighbours (east, west,
north, south) and wraparound distance of `torus k`, with the breadth-first spanning tree from
`ρ`: depth the wraparound distance to `ρ`, parent one step closer to `ρ` along the second
coordinate, then along the first. -/
def torusAt (k : ℕ) (ρ : TorusV k) : GraphData (TorusV k) where
  verts := (torus k).verts
  mem_verts := (torus k).mem_verts
  nbrs := (torus k).nbrs
  symm := (torus k).symm
  dist := (torus k).dist
  root := ρ
  par u := if u.2 ≠ ρ.2 then (u.1, stepTo u.2 ρ.2) else if u.1 ≠ ρ.1 then (stepTo u.1 ρ.1, u.2)
    else ρ
  dep u := cycDist u.1 ρ.1 + cycDist u.2 ρ.2
  dep_root := by simp [cycDist_self]
  par_root := by simp
  dep_par u hu := by
    obtain ⟨x, y⟩ := u
    by_cases hy : y = ρ.2
    · have hx : x ≠ ρ.1 := fun hx => hu (Prod.ext hx hy)
      subst hy
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, hx, not_false_eq_true, cycDist_self]
      have := cycDist_stepTo hx; omega
    · simp only [ne_eq, hy, not_false_eq_true, ↓reduceIte]
      have := cycDist_stepTo hy; omega
  par_adj u hu := by
    obtain ⟨x, y⟩ := u
    by_cases hy : y = ρ.2
    · have hx : x ≠ ρ.1 := fun hx => hu (Prod.ext hx hy)
      subst hy
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, hx, not_false_eq_true]
      rcases stepTo_eq x ρ.1 with h | h <;> simp [torus, h]
    · simp only [ne_eq, hy, not_false_eq_true, ↓reduceIte]
      rcases stepTo_eq y ρ.2 with h | h <;> simp [torus, h]

/-- The depth changes by at most one along every link. -/
theorem torusAt_dep_nbr (k : ℕ) (ρ : TorusV k) {u v : TorusV k} (h : v ∈ (torusAt k ρ).nbrs u) :
    (torusAt k ρ).dep v ≤ (torusAt k ρ).dep u + 1 := by
  obtain ⟨x, y⟩ := u
  have hd : ∀ a : TorusV k, (torusAt k ρ).dep a = cycDist a.1 ρ.1 + cycDist a.2 ρ.2 := fun _ => rfl
  simp only [torusAt, torus, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> rw [hd, hd] <;> dsimp only
  · have := (cycDist_succ_le x ρ.1).1; omega
  · have := (cycDist_pred_le x ρ.1).1; omega
  · have := (cycDist_succ_le y ρ.2).1; omega
  · have := (cycDist_pred_le y ρ.2).1; omega

/-- **The depth of `torusAt k ρ` is the breadth-first level from `ρ`**: the length of a
shortest walk from `ρ` (the `level` of the simulator). -/
theorem torusAt_dep_bfs (k : ℕ) (ρ : TorusV k) (u : TorusV k) :
    WalkLen (torusAt k ρ).nbrs ρ ((torusAt k ρ).dep u) u ∧
      ∀ n, WalkLen (torusAt k ρ).nbrs ρ n u → (torusAt k ρ).dep u ≤ n :=
  (torusAt k ρ).dep_isLeast_walk (fun _ _ h => torusAt_dep_nbr k ρ h) u

/-- On the torus every vertex other than `t` has a neighbour strictly closer to `t`. -/
theorem torusAt_dist_step (k : ℕ) (ρ : TorusV k) :
    ∀ u t : TorusV k, u ≠ t → ∃ v ∈ (torusAt k ρ).nbrs u,
      (torusAt k ρ).dist v t < (torusAt k ρ).dist u t :=
  torus_dist_step k

theorem torusAt_nbrs_length (k : ℕ) (ρ v : TorusV k) : ((torusAt k ρ).nbrs v).length = 4 := rfl

/-! ### The escape of the simulations -/

/-- The simulator's vertex number: `y * (k + 1) + x`. -/
def torusIdx (k : ℕ) (u : TorusV k) : ℕ := u.2.val * (k + 1) + u.1.val

theorem torusIdx_lt (k : ℕ) (u : TorusV k) : torusIdx k u < (k + 1) * (k + 1) := by
  have h1 := Nat.mul_le_mul_right (k + 1) (Nat.le_of_lt_succ u.2.isLt)
  have h2 := u.1.isLt
  have h3 : (k + 1) * (k + 1) = k * (k + 1) + (k + 1) := Nat.succ_mul k (k + 1)
  unfold torusIdx; omega

/-- **The root of the simulations**: `((k + 1) / 2 - 1, (k + 1) / 2 - 1)`. -/
def centre (k : ℕ) : TorusV k := (⟨(k + 1) / 2 - 1, by omega⟩, ⟨(k + 1) / 2 - 1, by omega⟩)

/-- On the `8 × 8` torus the centre root is vertex `27` (`torus_experiments.py`). -/
theorem centre_idx_8 : torusIdx 7 (centre 7) = 27 := rfl

/-- On the `16 × 16` torus the centre root is vertex `119` (`xp_torus16.py`). -/
theorem centre_idx_16 : torusIdx 15 (centre 15) = 119 := rfl

/-- **The up*/down* escape of the simulator** on the torus rooted at `ρ`: key `(level, number)`
lexicographically, escape hop the first neighbour in port order (east, west, north, south)
starting a shortest legal up*/down* path. -/
noncomputable def torusUD (k : ℕ) (ρ : TorusV k) : (torusAt k ρ).UpDown :=
  UpDown.ofLevels (torusAt k ρ) (torusIdx k) ((k + 1) * (k + 1)) (torusIdx_lt k)

/-- **The escape of every torus simulation**: `torusUD` with the centre root. -/
noncomputable abbrev simUD (k : ℕ) : (torusAt k (centre k)).UpDown := torusUD k (centre k)

/-- The hop `u → v` is up for `torusUD` iff `(level v, v) < (level u, u)` lexicographically, as
in the simulator. -/
theorem torusUD_up_iff (k : ℕ) (ρ u v : TorusV k) :
    (torusUD k ρ).key v < (torusUD k ρ).key u ↔
      (torusAt k ρ).dep v < (torusAt k ρ).dep u ∨
        (torusAt k ρ).dep v = (torusAt k ρ).dep u ∧ torusIdx k v < torusIdx k u :=
  (torusAt k ρ).levelKey_lt_iff (torusIdx_lt k) u v

/-- The escape hop of `torusUD` is the first neighbour, in port order, starting a shortest legal
up*/down* path. -/
theorem torusUD_nxt (k : ℕ) (ρ : TorusV k) :
    (torusUD k ρ).nxt = firstHop (torus k).nbrs (torusUD k ρ).key := rfl

/-- The simulator's vertex numbering is injective. -/
theorem torusIdx_inj (k : ℕ) {u v : TorusV k} (h : torusIdx k u = torusIdx k v) : u = v := by
  have hm : ∀ w : TorusV k, torusIdx k w % (k + 1) = w.1.val := fun w => by
    unfold torusIdx; rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt w.1.isLt
  have hd : ∀ w : TorusV k, torusIdx k w / (k + 1) = w.2.val := fun w => by
    unfold torusIdx; rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt w.1.isLt, Nat.add_zero]
  have h1 := hm u; have h2 := hm v; have h3 := hd u; have h4 := hd v
  rw [h] at h1 h3
  exact Prod.ext (Fin.ext (h1.symm.trans h2)) (Fin.ext (h3.symm.trans h4))

/-- The key of `torusUD` is injective. -/
theorem torusUD_key_inj (k : ℕ) (ρ : TorusV k) {u v : TorusV k}
    (h : (torusUD k ρ).key u = (torusUD k ρ).key v) : u = v := by
  have h1 := (torusUD_up_iff k ρ u v).not.1 (by omega)
  have h2 := (torusUD_up_iff k ρ v u).not.1 (by omega)
  exact torusIdx_inj k (by omega)

/-- From two positions on, the torus has no self-loops. -/
theorem torus_nbr_ne {k : ℕ} (hk : 1 ≤ k) {u v : TorusV k} (h : v ∈ (torus k).nbrs u) : v ≠ u := by
  have hs : ∀ a : Fin (k + 1), cycSucc a ≠ a := fun a e => by
    have := congrArg Fin.val e; rw [cycSucc_val] at this; split_ifs at this <;> omega
  have hp : ∀ a : Fin (k + 1), cycPred a ≠ a := fun a e => by
    have := congrArg Fin.val e; rw [cycPred_val] at this; split_ifs at this <;> omega
  simp only [torus, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> intro e
  · exact hs _ (congrArg Prod.fst e)
  · exact hp _ (congrArg Prod.fst e)
  · exact hs _ (congrArg Prod.snd e)
  · exact hp _ (congrArg Prod.snd e)

/-- **On the torus with at least two positions per ring, a link is a down hop iff it is not an
up hop**, as in the simulator (which calls every link that is not up a down hop). -/
theorem torusUD_down_iff_not_up {k : ℕ} (hk : 1 ≤ k) (ρ : TorusV k) {u v : TorusV k}
    (h : v ∈ (torusAt k ρ).nbrs u) :
    (torusUD k ρ).key u < (torusUD k ρ).key v ↔ ¬ (torusUD k ρ).key v < (torusUD k ρ).key u := by
  have hne : (torusUD k ρ).key v ≠ (torusUD k ρ).key u :=
    fun e => torus_nbr_ne hk h (torusUD_key_inj k ρ e)
  omega

/-! ### The escape -/

/-- **The up*/down* escape on the torus is connected**: every vertex reaches every destination
by a legal up*/down* path. -/
theorem torus_ud_reach (k : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown) (u d : TorusV k) :
    UDReach (torus k).nbrs U.key false u d :=
  U.reach u d

/-- **The escape dependency relation of up*/down* routing on the torus, with the phase in the
channel, is well-founded.** -/
theorem torus_ud_escDep_wf (k : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown) :
    WellFounded (flip U.EscDep) :=
  U.escDep_wf

/-! ### Detours -/

/-- **The torus of every size with the up*/down* escape, detours and at most `B` returns is
correct**: deadlock free and livelock free under every valid selection function, and starvation
free under strongly fair scheduling, for every root, up*/down* escape and choice of
intermediates. -/
theorem torus_ud_detour_correct (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown)
    (W : TorusV k → TorusV k → List (Option (TorusV k))) :
    (U.esc.net B W).Correct ∧ (U.esc.net B W).StarvationFree :=
  U.esc.correct B W

/-- **Correct under throttled sources.** -/
theorem torus_ud_detour_correct_of_sourceSel (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown)
    (W : TorusV k → TorusV k → List (Option (TorusV k)))
    {sel : Selection (GChan (TorusV k)) (DetHdr (TorusV k))}
    (hsel : (U.esc.net B W).SourceSel U.esc.escape (fun c => c.isInj) sel) :
    (U.esc.net B W).DeadlockFreeWith sel ∧ (U.esc.net B W).LivelockFreeWith sel ∧
      (U.esc.net B W).StarvationFreeWith sel :=
  EscapeLayer.correct_of_sourceSel hsel

/-- **Delivery under saturation**: under every valid selection, every packet is delivered along
every channel-fair run. -/
theorem torus_ud_detour_underLoad (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown)
    (W : TorusV k → TorusV k → List (Option (TorusV k)))
    {sel : Selection (GChan (TorusV k)) (DetHdr (TorusV k))} (hsel : (U.esc.net B W).ValidSel sel) :
    (U.esc.net B W).StarvationFreeUnderLoad sel (fun _ => False) :=
  EscapeLayer.underLoad hsel

/-- **Hop bound**: at most `dist s w` hops towards the intermediate, then less than
`(B + 1) * rankBound`. -/
theorem torus_ud_detour_hops_le (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown)
    (W : TorusV k → TorusV k → List (Option (TorusV k)))
    {s d w : TorusV k} {ls : List Unit} {q' : GChan (TorusV k) × DetHdr (TorusV k)}
    (h : (U.esc.net B W).packetLTS.Path (.inj s, (d, some w, B)) ls q') :
    ls.length ≤ (torus k).dist s w + (B + 1) * U.esc.rankBound :=
  EscapeLayer.hops_le_some h

/-- **Valiant's routing on the torus with the up*/down* escape is correct**, and delivers every
packet under saturation along every channel-fair run. -/
theorem torus_ud_valiant_correct (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown) :
    (U.esc.net B (torusAt k ρ).anyDetour).Correct ∧
      (U.esc.net B (torusAt k ρ).anyDetour).StarvationFree ∧
      ∀ sel, (U.esc.net B (torusAt k ρ).anyDetour).ValidSel sel →
        (U.esc.net B (torusAt k ρ).anyDetour).StarvationFreeUnderLoad sel (fun _ => False) :=
  ⟨(U.esc.correct B _).1, (U.esc.correct B _).2, fun _ hsel => EscapeLayer.underLoad hsel⟩

/-! ### History-dependent strategies -/

/-- **Any history-dependent choice on the torus with the up*/down* escape is safe**: any
intermediate of `W` (chosen by `σ.admit` from any history) and any admissible choice among the
free minimal hops on virtual channel 1, the escape hop as fallback. -/
theorem torus_ud_choice_safe (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown)
    (W : TorusV k → TorusV k → List (Option (TorusV k))) {H : Type*}
    {σ : Strategy (GChan (TorusV k)) (DetHdr (TorusV k)) H}
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧ σ.sel h = refineSel (U.esc.openSel B W) choose) :
    (U.esc.net B W).StrategySafe σ (fun _ => False) :=
  EscapeLayer.choice_safe hσ

/-- **The `lx` throttle on the torus with the up*/down* escape** is deadlock, livelock and
starvation free, and delivers every packet outside the injection channels along every
channel-fair run. -/
theorem torus_ud_lx_correct (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown)
    (W : TorusV k → TorusV k → List (Option (TorusV k))) (ball : TorusV k → List (TorusV k))
    {o lo hi : ℕ} (hlo : lo ≤ 8) (hhi : hi ≤ 8) :
    (U.esc.net B W).DeadlockFreeWith (U.esc.lxSel B W ball o lo hi) ∧
      (U.esc.net B W).LivelockFreeWith (U.esc.lxSel B W ball o lo hi) ∧
      (U.esc.net B W).StarvationFreeWith (U.esc.lxSel B W ball o lo hi) ∧
      (U.esc.net B W).StarvationFreeUnderLoad (U.esc.lxSel B W ball o lo hi) (fun c => c.isInj) :=
  have h : (U.esc.net B W).SourceSel U.esc.escape (fun c => c.isInj)
      (U.esc.lxSel B W ball o lo hi) :=
    EscapeLayer.lxSel_sourceSel (fun v => by rw [show ((torusAt k ρ).nbrs v).length = 4 from rfl]; omega)
      (fun v => by rw [show ((torusAt k ρ).nbrs v).length = 4 from rfl]; omega)
  ⟨(EscapeLayer.correct_of_sourceSel h).1, (EscapeLayer.correct_of_sourceSel h).2.1,
    (EscapeLayer.correct_of_sourceSel h).2.2, EscapeLayer.underLoad_of_sourceSel h⟩

/-- **Every history-dependent throttle on the torus with the up*/down* escape and Valiant's
intermediates is safe**: thresholds `thr h f s ≤ 8` and escape blocking `block h f s`, both
read from anything (the configuration, a snapshot, any history), any admissible choice among
the free hops of a tier. -/
theorem torus_ud_throttle_safe (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown) {H : Type*}
    {σ : Strategy (GChan (TorusV k)) (DetHdr (TorusV k)) H}
    (thr : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → TorusV k → ℕ)
    (block : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → TorusV k → Bool)
    (hthr : ∀ h f s, thr h f s ≤ 8)
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧
      σ.sel h = refineSel (U.esc.throttleSel B (torusAt k ρ).anyDetour (thr h) (block h)) choose) :
    (U.esc.net B (torusAt k ρ).anyDetour).StrategySafe σ (fun c => c.isInj) :=
  EscapeLayer.throttle_safe (torusAt k ρ).anyDetour_ne (torusAt_dist_step k ρ) thr block
    (fun h f s v => by rw [torusAt_nbrs_length]; exact hthr h f s) hσ

/-- **The simulated combined scheme with the up*/down* escape** (`csim` of
`scripts/xp_combo.py` with `thr=lx…` and `thr2=lx…`, as `comboStrategy`): the snapshot `snap h`,
the per-source flag `spread h s`, the choice `choose h` among the free hops of a tier, the
injection rule `admit`; the share signal, the threshold and the own-router test read from the
snapshot. -/
noncomputable def udComboStrategy (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown) {H : Type*}
    (init : H)
    (update : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) →
      Act (GChan (TorusV k)) (DetHdr (TorusV k)) → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → H)
    (admit : H → GChan (TorusV k) → DetHdr (TorusV k) → Prop)
    (snap : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)))
    (spread : H → TorusV k → Bool) (ball₁ ball₂ : TorusV k → List (TorusV k))
    (o₁ lo₁ hi₁ o₂ lo₂ hi₂ : ℕ)
    (choose : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → GChan (TorusV k) →
      DetHdr (TorusV k) → List (GChan (TorusV k) × DetHdr (TorusV k)) →
      List (GChan (TorusV k) × DetHdr (TorusV k))) :
    Strategy (GChan (TorusV k)) (DetHdr (TorusV k)) H where
  init := init
  sel h := refineSel (U.esc.throttleSel B (torusAt k ρ).anyDetour
    (fun _ s => if spread h s then (torusAt k ρ).lxThr ball₂ o₂ lo₂ hi₂ (snap h) s
      else (torusAt k ρ).lxThr ball₁ o₁ lo₁ hi₁ (snap h) s)
    (fun _ s => if spread h s then (torusAt k ρ).lxBlock ball₂ o₂ (snap h) s
      else (torusAt k ρ).lxBlock ball₁ o₁ (snap h) s)) (choose h)
  admit := admit
  update := update

/-- **The simulated combined scheme with the up*/down* escape is safe** on the torus of every
size, for every root and up*/down* escape, state type and update, snapshot, spread flags,
neighbourhoods, share thresholds, thresholds up to 8, admissible choices among the free hops and
choices of intermediates. -/
theorem torus_ud_combo_safe (k B : ℕ) (ρ : TorusV k) (U : (torusAt k ρ).UpDown) {H : Type*}
    (init : H)
    (update : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) →
      Act (GChan (TorusV k)) (DetHdr (TorusV k)) → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → H)
    (admit : H → GChan (TorusV k) → DetHdr (TorusV k) → Prop)
    (snap : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)))
    (spread : H → TorusV k → Bool) (ball₁ ball₂ : TorusV k → List (TorusV k))
    {o₁ lo₁ hi₁ o₂ lo₂ hi₂ : ℕ} (h₁ : lo₁ ≤ 8 ∧ hi₁ ≤ 8) (h₂ : lo₂ ≤ 8 ∧ hi₂ ≤ 8)
    (choose : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → GChan (TorusV k) →
      DetHdr (TorusV k) → List (GChan (TorusV k) × DetHdr (TorusV k)) →
      List (GChan (TorusV k) × DetHdr (TorusV k)))
    (hch : ∀ h, ChoiceOK (choose h)) :
    (U.esc.net B (torusAt k ρ).anyDetour).StrategySafe
      (udComboStrategy k B ρ U init update admit snap spread ball₁ ball₂ o₁ lo₁ hi₁ o₂ lo₂ hi₂
        choose)
      (fun c => c.isInj) :=
  torus_ud_throttle_safe k B ρ U _ _ (fun h _ s => by
      split
      · exact (torusAt k ρ).lxThr_le h₂.1 h₂.2 _ _
      · exact (torusAt k ρ).lxThr_le h₁.1 h₁.2 _ _)
    fun h => ⟨choose h, hch h, rfl⟩

/-! ### The escape of the simulations -/

/-- **The torus of every size with the escape of the simulations** (up*/down* from the centre,
key `(level, number)`, first shortest legal next hop in port order) with detours and at most `B`
returns is correct. -/
theorem simUD_detour_correct (k B : ℕ) (W : TorusV k → TorusV k → List (Option (TorusV k))) :
    ((simUD k).esc.net B W).Correct ∧ ((simUD k).esc.net B W).StarvationFree :=
  torus_ud_detour_correct k B _ _ W

/-- **Every history-dependent throttle with the escape of the simulations is safe.** -/
theorem simUD_throttle_safe (k B : ℕ) {H : Type*}
    {σ : Strategy (GChan (TorusV k)) (DetHdr (TorusV k)) H}
    (thr : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → TorusV k → ℕ)
    (block : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → TorusV k → Bool)
    (hthr : ∀ h f s, thr h f s ≤ 8)
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧ σ.sel h =
      refineSel ((simUD k).esc.throttleSel B (torusAt k (centre k)).anyDetour (thr h) (block h))
        choose) :
    ((simUD k).esc.net B (torusAt k (centre k)).anyDetour).StrategySafe σ (fun c => c.isInj) :=
  torus_ud_throttle_safe k B _ _ thr block hthr hσ

/-- **The simulated combined scheme with the escape of the simulations is safe** on the torus of
every size (the `8 × 8` and `16 × 16` schemes of `xp_combo.py` and `xp_torus16.py`). -/
theorem simUD_combo_safe (k B : ℕ) {H : Type*} (init : H)
    (update : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) →
      Act (GChan (TorusV k)) (DetHdr (TorusV k)) → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → H)
    (admit : H → GChan (TorusV k) → DetHdr (TorusV k) → Prop)
    (snap : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)))
    (spread : H → TorusV k → Bool) (ball₁ ball₂ : TorusV k → List (TorusV k))
    {o₁ lo₁ hi₁ o₂ lo₂ hi₂ : ℕ} (h₁ : lo₁ ≤ 8 ∧ hi₁ ≤ 8) (h₂ : lo₂ ≤ 8 ∧ hi₂ ≤ 8)
    (choose : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → GChan (TorusV k) →
      DetHdr (TorusV k) → List (GChan (TorusV k) × DetHdr (TorusV k)) →
      List (GChan (TorusV k) × DetHdr (TorusV k)))
    (hch : ∀ h, ChoiceOK (choose h)) :
    ((simUD k).esc.net B (torusAt k (centre k)).anyDetour).StrategySafe
      (udComboStrategy k B (centre k) (simUD k) init update admit snap spread ball₁ ball₂ o₁ lo₁
        hi₁ o₂ lo₂ hi₂ choose)
      (fun c => c.isInj) :=
  torus_ud_combo_safe k B _ _ init update admit snap spread ball₁ ball₂ h₁ h₂ choose hch

#assert_standard_axioms torusAt_dep_bfs centre_idx_8 centre_idx_16 torusUD_up_iff torusUD_nxt
#assert_standard_axioms torusUD_key_inj torusUD_down_iff_not_up
#assert_standard_axioms torus_ud_reach torus_ud_escDep_wf torus_ud_detour_correct
#assert_standard_axioms torus_ud_detour_correct_of_sourceSel torus_ud_detour_underLoad
#assert_standard_axioms torus_ud_detour_hops_le torus_ud_valiant_correct torus_ud_choice_safe
#assert_standard_axioms torus_ud_lx_correct torus_ud_throttle_safe torus_ud_combo_safe
#assert_standard_axioms simUD_detour_correct simUD_throttle_safe simUD_combo_safe

end AsyncLean.Examples
