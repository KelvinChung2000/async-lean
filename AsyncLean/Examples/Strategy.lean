/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.GraphDetour
import AsyncLean.Examples.Saturation
import AsyncLean.Routing.StrategyDetour
import AsyncLean.AxiomAudit

/-!
# Example: history-dependent strategies on the torus and the mesh

Instances of `AsyncLean.Routing.Strategy` and `AsyncLean.Routing.StrategyDetour` for the schemes
of the simulations (`scripts/xp_combo.py`, `scripts/xp_ramp.py`).  A strategy has a state of any
type `H` (smoothed link prices, learned latencies, per-source recent destinations, the snapshot of
the network taken at the start of the cycle, controller state, a random generator), updated by any
rule; each theorem holds for every such state and update.

## The torus with detours (`(torus k).detourNet B anyDetour`)

* `torus_dist_step` : on the torus every vertex other than `t` has a neighbour strictly closer to
  `t` under the wraparound distance.
* `torus_choice_safe` : **any history-dependent choice of the intermediate at the source** (the
  strategy's `admit`: tolls, learned latencies, price tables, recent-destination counters) and
  **any history-dependent choice among the free minimal hops** (`Network.ChoiceOK`), with the
  escape hop as fallback, is safe (`Network.StrategySafe` with no throttled source: deadlock and
  livelock free, every packet delivered under sustained load and under strong fairness, both
  relative to the selection in force).  `priceStrategy`, `torus_price_safe` : the cheapest hop
  under any history-dependent score.
* `torus_lxSel_sourceSel`, `torus_lx_correct` : the escape-share throttle `lx` evaluated on the
  current configuration (threshold `hi` when at least `o` % of the occupied channels around the
  source are escape channels, else `lo`; no direct injection into an escape channel while the
  share is high and the source's own router is not empty) satisfies `Network.SourceSel` — a source
  lets its packet go once the rest of the network is empty — so the existing theorems apply:
  deadlock, livelock and starvation free, and delivery under load outside the sources.
* `torus_throttle_safe` : **every history-dependent throttle** — thresholds up to 8 and any
  escape-blocking rule, both read from anything — with any history-dependent choice among the
  free hops and any choice of intermediates, is safe (packets held at a throttling source are
  delivered under strong fairness, not under channel fairness alone).
* `comboStrategy`, `torus_combo_safe` : the simulated scheme `csim` with `thr=lx…` and
  `thr2=lx…` exactly as simulated: the share signal, the threshold *and the own-router test* read
  from the snapshot taken at the start of the cycle, the controller chosen by the source's
  recent destinations, the hop chosen by any rule (prices), the intermediate by any rule (tolls).

## The mesh (`duatoMesh k`)

`duatoTiers_correct` needs a tier list containing `escTier k g` for one fixed `g ≤ 8`; a tier
whose threshold depends on the configuration is not of that form.

* `duatoTiers_append_correct` : appending `escTier k 8` to any tier list makes
  `duatoTiers_correct` apply verbatim.  When the list already has an escape tier gated with a
  threshold `≤ 8` and no blocking rule, the appended tier never changes the selection (whatever
  it admits, the gated escape tier admitted first); with the escape-blocking rule it may (it
  admits the escape hop while the rule refuses it, if nothing else is free).
* `Mesh.gatedTiers`, `Mesh.gatedTiers_sourceSel` : the tiers of `tieredMesh` through the source
  gate of the simulation, with any thresholds `≤ 8` and any blocking rule that is off when every
  link channel is empty, satisfy `Network.SourceSel`; `Mesh.meshLxThr`, `Mesh.meshLxBlock` : the
  `lx` signal on the mesh.
* `duatoMesh_strategy_safe`, `duatoMesh_gated_safe` : every strategy on Duato's mesh whose
  selections satisfy it — for example the gated tiers with thresholds read from history (a
  snapshot, recent destinations) and the blocking rule read from the current configuration, with
  any choice among the free hops — is safe.  The blocking rule read from a snapshot is not
  covered on the mesh (it is on the torus).
-/

namespace AsyncLean.Examples

open Network Mesh

/-! ### The wraparound distance -/

/-- The vertices of the `(k + 1) × (k + 1)` torus. -/
abbrev TorusV (k : ℕ) := Fin (k + 1) × Fin (k + 1)

theorem cyc_mod {x y n : ℕ} (hx : x < n) (hy : y < n) :
    (x + n - y) % n = if y ≤ x then x - y else x + n - y := by
  split_ifs with h
  · rw [show x + n - y = (x - y) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

theorem cycDist_val {k : ℕ} (a b : Fin (k + 1)) :
    cycDist a b = min (if b.val ≤ a.val then a.val - b.val else a.val + (k + 1) - b.val)
      (if a.val ≤ b.val then b.val - a.val else b.val + (k + 1) - a.val) := by
  unfold cycDist
  rw [cyc_mod a.isLt b.isLt, cyc_mod b.isLt a.isLt]

theorem cycSucc_val {k : ℕ} (a : Fin (k + 1)) :
    (cycSucc a).val = if a.val = k then 0 else a.val + 1 := by
  unfold cycSucc; split_ifs <;> rfl

theorem cycPred_val {k : ℕ} (a : Fin (k + 1)) :
    (cycPred a).val = if a.val = 0 then k else a.val - 1 := by
  unfold cycPred; split_ifs <;> simp

/-- One step forward or one step back brings a coordinate strictly closer to any other. -/
theorem cycDist_step {k : ℕ} {a b : Fin (k + 1)} (h : a ≠ b) :
    cycDist (cycSucc a) b < cycDist a b ∨ cycDist (cycPred a) b < cycDist a b := by
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.val ≠ b.val := fun e => h (Fin.ext e)
  rw [cycDist_val, cycDist_val, cycDist_val, cycSucc_val, cycPred_val]
  split_ifs <;> omega

/-- **On the torus every vertex other than `t` has a neighbour strictly closer to `t`** under the
wraparound distance. -/
theorem torus_dist_step (k : ℕ) :
    ∀ u t : TorusV k, u ≠ t → ∃ v ∈ (torus k).nbrs u, (torus k).dist v t < (torus k).dist u t := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have hd : ∀ a b : TorusV k, (torus k).dist a b = cycDist a.1 b.1 + cycDist a.2 b.2 :=
    fun _ _ => rfl
  by_cases hx : x = x'
  · subst hx
    have hy : y ≠ y' := fun e => h (by rw [e])
    rcases cycDist_step hy with h1 | h1
    · exact ⟨(x, cycSucc y), by simp [torus], by rw [hd, hd]; dsimp only; omega⟩
    · exact ⟨(x, cycPred y), by simp [torus], by rw [hd, hd]; dsimp only; omega⟩
  · rcases cycDist_step hx with h1 | h1
    · exact ⟨(cycSucc x, y), by simp [torus], by rw [hd, hd]; dsimp only; omega⟩
    · exact ⟨(cycPred x, y), by simp [torus], by rw [hd, hd]; dsimp only; omega⟩

theorem torus_nbrs_length (k : ℕ) (v : TorusV k) : ((torus k).nbrs v).length = 4 := rfl

/-! ### Choices among the minimal hops and of the intermediate -/

/-- **Any history-dependent choice on the torus with detours is safe**: whatever intermediate
each source chooses (`σ.admit`, from tolls, learned latencies, price tables or recent-destination
counters; any intermediate of `W`) and whatever admissible choice it makes among the free
minimal hops on virtual channel 1 (the escape hop as fallback), the strategy is deadlock and
livelock free, and every packet is delivered under sustained load and under strong fairness
(both relative to the selection in force). -/
theorem torus_choice_safe (k B : ℕ) (W : TorusV k → TorusV k → List (Option (TorusV k)))
    {H : Type*} {σ : Strategy (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) H}
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧
      σ.sel h = refineSel ((torus k).openSel B W) choose) :
    ((torus k).detourNet B W).StrategySafe σ (fun _ => False) :=
  (torus k).detour_strategy_safe_of_escapeSel fun h => by
    obtain ⟨choose, hch, he⟩ := hσ h
    rw [he]
    exact (torus k).refine_openSel_escapeSel hch

/-- **The price strategy**: in state `h`, the cheapest free minimal hop under the score
`score h` (smoothed link prices plus propagated route costs, learned latencies, …), else the
escape hop; the intermediate chosen by `admit`; the state updated by `update`. -/
def priceStrategy (k B : ℕ) {H : Type*} (init : H)
    (update : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) →
      Act (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) →
      Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → H)
    (admit : H → GChan (TorusV k) → GraphData.DetHdr (TorusV k) → Prop)
    (score : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → GChan (TorusV k) →
      GraphData.DetHdr (TorusV k) → GChan (TorusV k) × GraphData.DetHdr (TorusV k) → ℕ) :
    Strategy (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) H where
  init := init
  sel h := refineSel ((torus k).openSel B (torus k).anyDetour) (minChoice (score h))
  admit := admit
  update := update

/-- **The price strategy is safe** on the torus of every size, with Valiant's intermediates, for
every state type, update, injection rule and score. -/
theorem torus_price_safe (k B : ℕ) {H : Type*} (init : H)
    (update : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) →
      Act (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) →
      Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → H)
    (admit : H → GChan (TorusV k) → GraphData.DetHdr (TorusV k) → Prop)
    (score : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → GChan (TorusV k) →
      GraphData.DetHdr (TorusV k) → GChan (TorusV k) × GraphData.DetHdr (TorusV k) → ℕ) :
    ((torus k).detourNet B (torus k).anyDetour).StrategySafe
      (priceStrategy k B init update admit score) (fun _ => False) :=
  torus_choice_safe k B _ fun h => ⟨_, minChoice_ok (score h), rfl⟩

/-! ### The escape-share throttle -/

/-- **The `lx` throttle on the torus satisfies Duato's condition with throttled sources**: a
source lets its packet go once the rest of the network is empty, for every neighbourhood `ball`,
share threshold `o` and thresholds `lo, hi ≤ 8` (`lx2_4_36_2`: `lo = 2`, `hi = 4`, `o = 36`). -/
theorem torus_lxSel_sourceSel (k B : ℕ) (W : TorusV k → TorusV k → List (Option (TorusV k)))
    (ball : TorusV k → List (TorusV k)) {o lo hi : ℕ} (hlo : lo ≤ 8) (hhi : hi ≤ 8) :
    ((torus k).detourNet B W).SourceSel (torus k).detEscape (fun c => c.isInj)
      ((torus k).lxSel B W ball o lo hi) :=
  (torus k).lxSel_sourceSel (fun v => by rw [torus_nbrs_length]; omega)
    (fun v => by rw [torus_nbrs_length]; omega)

/-- **The torus with detours under the `lx` throttle** (read from the current configuration) is
deadlock free, livelock free and starvation free, and delivers every packet outside the
injection channels along every channel-fair run. -/
theorem torus_lx_correct (k B : ℕ) (W : TorusV k → TorusV k → List (Option (TorusV k)))
    (ball : TorusV k → List (TorusV k)) {o lo hi : ℕ} (hlo : lo ≤ 8) (hhi : hi ≤ 8) :
    ((torus k).detourNet B W).DeadlockFreeWith ((torus k).lxSel B W ball o lo hi) ∧
      ((torus k).detourNet B W).LivelockFreeWith ((torus k).lxSel B W ball o lo hi) ∧
      ((torus k).detourNet B W).StarvationFreeWith ((torus k).lxSel B W ball o lo hi) ∧
      ((torus k).detourNet B W).StarvationFreeUnderLoad ((torus k).lxSel B W ball o lo hi)
        (fun c => c.isInj) :=
  have h := torus_lxSel_sourceSel k B W ball hlo hhi
  ⟨((torus k).detour_correct_of_sourceSel h).1, ((torus k).detour_correct_of_sourceSel h).2.1,
    ((torus k).detour_correct_of_sourceSel h).2.2, (torus k).detour_underLoad_of_sourceSel h⟩

/-- **Every history-dependent throttle on the torus with Valiant's intermediates is safe**: in
state `h` the strategy throttles with thresholds `thr h f s ≤ 8` and escape blocking
`block h f s` — both arbitrary, read from the configuration, a snapshot or any history — and
picks among the free hops of a tier with any admissible choice.  It is deadlock and livelock
free, delivers every packet outside the injection channels along every run channel fair relative
to the selection in force, and every packet along every run strongly fair relative to it. -/
theorem torus_throttle_safe (k B : ℕ) {H : Type*}
    {σ : Strategy (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) H}
    (thr : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → TorusV k → ℕ)
    (block : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → TorusV k → Bool)
    (hthr : ∀ h f s, thr h f s ≤ 8)
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧
      σ.sel h = refineSel ((torus k).throttleSel B (torus k).anyDetour (thr h) (block h)) choose) :
    ((torus k).detourNet B (torus k).anyDetour).StrategySafe σ (fun c => c.isInj) :=
  (torus k).detour_strategy_safe_of_sourceSelOn (torus k).anyDetour_ne fun h => by
    obtain ⟨choose, hch, he⟩ := hσ h
    rw [he]
    exact refineSel_sourceSelOn ((torus k).throttleSel_sourceSelOn (torus_dist_step k)
      (fun f s v => by rw [torus_nbrs_length]; exact hthr h f s))
      (((torus k).detourNet B (torus k).anyDetour).tieredSel_freeOnly _) hch

/-- **The simulated combined scheme** (`csim` of `scripts/xp_combo.py` with `thr=lx…` and
`thr2=lx…`): the state provides the snapshot `snap h` of the network taken at the start of the
cycle, the per-source flag `spread h s` (more than two distinct recent destinations), the choice
`choose h` among the free hops of a tier (prices), and the injection rule `admit` (tolls,
learned latencies).  A source uses the `lx` controller `(ball₂, o₂, lo₂, hi₂)` when `spread`, and
`(ball₁, o₁, lo₁, hi₁)` otherwise; the share signal, the threshold and the own-router test are
read from the snapshot, the free channels from the current configuration. -/
def comboStrategy (k B : ℕ) {H : Type*} (init : H)
    (update : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) →
      Act (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) →
      Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → H)
    (admit : H → GChan (TorusV k) → GraphData.DetHdr (TorusV k) → Prop)
    (snap : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)))
    (spread : H → TorusV k → Bool) (ball₁ ball₂ : TorusV k → List (TorusV k))
    (o₁ lo₁ hi₁ o₂ lo₂ hi₂ : ℕ)
    (choose : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → GChan (TorusV k) →
      GraphData.DetHdr (TorusV k) → List (GChan (TorusV k) × GraphData.DetHdr (TorusV k)) →
      List (GChan (TorusV k) × GraphData.DetHdr (TorusV k))) :
    Strategy (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) H where
  init := init
  sel h := refineSel ((torus k).throttleSel B (torus k).anyDetour
    (fun _ s => if spread h s then (torus k).lxThr ball₂ o₂ lo₂ hi₂ (snap h) s
      else (torus k).lxThr ball₁ o₁ lo₁ hi₁ (snap h) s)
    (fun _ s => if spread h s then (torus k).lxBlock ball₂ o₂ (snap h) s
      else (torus k).lxBlock ball₁ o₁ (snap h) s)) (choose h)
  admit := admit
  update := update

/-- **The simulated combined scheme is safe** on the torus of every size: for every state type
and update, snapshot, spread flags, neighbourhoods, share thresholds, thresholds up to 8,
admissible choices among the free hops and choices of intermediates. -/
theorem torus_combo_safe (k B : ℕ) {H : Type*} (init : H)
    (update : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) →
      Act (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) →
      Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → H)
    (admit : H → GChan (TorusV k) → GraphData.DetHdr (TorusV k) → Prop)
    (snap : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)))
    (spread : H → TorusV k → Bool) (ball₁ ball₂ : TorusV k → List (TorusV k))
    {o₁ lo₁ hi₁ o₂ lo₂ hi₂ : ℕ} (h₁ : lo₁ ≤ 8 ∧ hi₁ ≤ 8) (h₂ : lo₂ ≤ 8 ∧ hi₂ ≤ 8)
    (choose : H → Config (GChan (TorusV k)) (GraphData.DetHdr (TorusV k)) → GChan (TorusV k) →
      GraphData.DetHdr (TorusV k) → List (GChan (TorusV k) × GraphData.DetHdr (TorusV k)) →
      List (GChan (TorusV k) × GraphData.DetHdr (TorusV k)))
    (hch : ∀ h, ChoiceOK (choose h)) :
    ((torus k).detourNet B (torus k).anyDetour).StrategySafe
      (comboStrategy k B init update admit snap spread ball₁ ball₂ o₁ lo₁ hi₁ o₂ lo₂ hi₂ choose)
      (fun c => c.isInj) :=
  torus_throttle_safe k B _ _ (fun h _ s => by
      split
      · exact (torus k).lxThr_le h₂.1 h₂.2 _ _
      · exact (torus k).lxThr_le h₁.1 h₁.2 _ _)
    fun h => ⟨choose h, hch h, rfl⟩

/-! ### The mesh -/

/-- **Appending `escTier k 8`** to any tier list makes `duatoTiers_correct` apply: Duato's mesh
under the resulting tiered selection is deadlock, livelock and starvation free, whatever the
other tiers read. -/
theorem duatoTiers_append_correct (k : ℕ) (tiers : List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)) :
    (duatoMesh k).DeadlockFreeWith ((duatoMesh k).tieredSel (tiers ++ [Mesh.escTier k 8])) ∧
      (duatoMesh k).LivelockFreeWith ((duatoMesh k).tieredSel (tiers ++ [Mesh.escTier k 8])) ∧
      (duatoMesh k).StarvationFreeWith ((duatoMesh k).tieredSel (tiers ++ [Mesh.escTier k 8])) :=
  duatoTiers_correct k le_rfl (List.mem_append_right _ List.mem_cons_self)

namespace Mesh

/-- The escape channel of a packet: XY on virtual channel 0. -/
def escCh (k c d : ℕ) : ℕ := ch (head k c) (xy k (head k c) d) 0

/-- **The source gate of the simulation on the mesh** (`Ctrl.gate` of `scripts/xp_ramp.py`):
from an injection channel, the hop `q` only towards a router with at least `g` of its 8 outgoing
channels free, and only on virtual channel 1 when `block`. -/
def meshGate (k g : ℕ) (block : Bool) (f : Config ℕ ℕ) (c : ℕ) (q : ℕ × ℕ) : Bool :=
  dir c != 4 || (decide (g ≤ freeOut f (head k q.1)) && (!block || q.1 % 2 == 1))

/-- The tiers of `tieredMesh` through the source gate, with threshold `thr f s` and escape
blocking `block f s` for the router `s = node c` of the channel: the preferred hop, the escape
hop, any hop on virtual channel 1. -/
def gatedTiers (k : ℕ) (thr : Config ℕ ℕ → ℕ → ℕ) (block : Config ℕ ℕ → ℕ → Bool) :
    List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool) :=
  [fun f c d q => meshGate k (thr f (node c)) (block f (node c)) f c q &&
      (q.1 == prefCh k c d || (dir c == 4 && q.1 == escCh k c d)),
   fun f c d q => meshGate k (thr f (node c)) (block f (node c)) f c q && q.1 == escCh k c d,
   fun f c _ q => meshGate k (thr f (node c)) (block f (node c)) f c q && q.1 % 2 == 1]

/-- **The gated tiers satisfy Duato's condition with throttled sources**, on every network whose
permitted hops include the XY escape hop, for thresholds up to 8 and any blocking rule that is
off when every link channel is empty. -/
theorem gatedTiers_sourceSel {k : ℕ} (N : Network ℕ ℕ)
    (hesc : ∀ c d, (escCh k c d, d) ∈ N.route c d) {thr : Config ℕ ℕ → ℕ → ℕ}
    {block : Config ℕ ℕ → ℕ → Bool} (hthr : ∀ f s, thr f s ≤ 8)
    (hblock : ∀ f s, (∀ c, ¬ dir c = 4 → f c = none) → block f s = false) :
    N.SourceSel (xyEscape k) (fun c => dir c = 4) (N.tieredSel (gatedTiers k thr block)) :=
  N.tieredSel_sourceSel (fun c d q hq => by
      simp only [xyEscape, List.mem_singleton] at hq; subst hq; exact hesc c d)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun f c d q hc hq => by
      simp only [xyEscape, List.mem_singleton] at hq; subst hq
      simp [meshGate, hc, escCh])
    (fun f c d q _ he hq => by
      simp only [xyEscape, List.mem_singleton] at hq; subst hq
      simp [meshGate, freeOut_eq he, hthr, hblock f _ he, escCh])

/-- The link channels leaving router `v` (both virtual channels). -/
def meshOut (v : ℕ) : List ℕ := (List.range 4).flatMap fun dr => [ch v dr 0, ch v dr 1]

/-- **The escape-share signal on the mesh**: at least `o` % of the occupied link channels
leaving the routers of `ball s` are on virtual channel 0. -/
def meshShareHigh (ball : ℕ → List ℕ) (o : ℕ) (f : Config ℕ ℕ) (s : ℕ) : Bool :=
  decide (o * max 1 (((ball s).flatMap meshOut).countP fun c => (f c).isSome) ≤
    100 * (((ball s).flatMap meshOut).countP fun c => (f c).isSome && c % 2 == 0))

/-- The `lx` threshold on the mesh: `hi` while the escape share is high, `lo` otherwise. -/
def meshLxThr (ball : ℕ → List ℕ) (o lo hi : ℕ) (f : Config ℕ ℕ) (s : ℕ) : ℕ :=
  if meshShareHigh ball o f s then hi else lo

/-- The `lx` escape blocking on the mesh: while the escape share is high and the source's own
router has an occupied outgoing channel. -/
def meshLxBlock (ball : ℕ → List ℕ) (o : ℕ) (f : Config ℕ ℕ) (s : ℕ) : Bool :=
  meshShareHigh ball o f s && (meshOut s).any fun c => (f c).isSome

theorem meshLxThr_le {ball : ℕ → List ℕ} {o lo hi m : ℕ} (hlo : lo ≤ m) (hhi : hi ≤ m)
    (f : Config ℕ ℕ) (s : ℕ) : meshLxThr ball o lo hi f s ≤ m := by
  unfold meshLxThr; split <;> assumption

/-- The `lx` blocking on the mesh is off when every link channel is empty. -/
theorem meshLxBlock_of_empty {ball : ℕ → List ℕ} {o : ℕ} {f : Config ℕ ℕ}
    (hf : ∀ c, ¬ dir c = 4 → f c = none) (s : ℕ) : meshLxBlock ball o f s = false := by
  have : ((meshOut s).any fun c => (f c).isSome) = false := by
    rw [List.any_eq_false]
    intro c hc
    simp only [meshOut, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    obtain ⟨dr, hdr, rfl | rfl⟩ := hc
    · have : f (ch s dr 0) = none :=
        hf _ (by rw [dir_ch (by omega : dr < 5) (by omega : (0 : ℕ) < 2)]; omega)
      simp [this]
    · have : f (ch s dr 1) = none :=
        hf _ (by rw [dir_ch (by omega : dr < 5) (by omega : (1 : ℕ) < 2)]; omega)
      simp [this]
  simp [meshLxBlock, this]

end Mesh

/-- **Every strategy on Duato's mesh whose selections satisfy Duato's condition with throttled
sources (on the legal pairs) is safe**: deadlock and livelock free, every packet outside the
injection channels delivered along every run channel fair relative to the selection in force,
and every packet along every run strongly fair relative to it. -/
theorem duatoMesh_strategy_safe (k : ℕ) {H : Type*} {σ : Strategy ℕ ℕ H}
    (hσ : ∀ h, (duatoMesh k).SourceSelOn (wfLegal k) (xyEscape k) (fun c => dir c = 4) (σ.sel h)) :
    (duatoMesh k).StrategySafe σ (fun c => dir c = 4) :=
  Strategy.safe (Mesh.duato_closed k) (wf_pairs_finite k) (xyEscape k)
    (fun _ _ _ _ => by simp [xyEscape]) (wf_wf k) (fun _ _ _ _ _ hq => Mesh.esc_not_source hq)
    (fun _ _ _ _ _ hq => Mesh.duato_not_source hq) (wfDist k)
    (fun _ _ _ hl ha hq => Mesh.duato_dist hl ha hq) hσ

/-- **History-dependent throttles on Duato's mesh are safe**: in state `h` the strategy uses the
gated tiers with thresholds `thr h f s ≤ 8` (read from anything: a snapshot of the escape share,
the source's recent destinations) and an escape-blocking rule `block h f s` that is off when
every link channel of `f` is empty (for example `Mesh.meshLxBlock` on the current
configuration), and picks among the free hops of a tier with any admissible choice. -/
theorem duatoMesh_gated_safe (k : ℕ) {H : Type*} {σ : Strategy ℕ ℕ H}
    (thr : H → Config ℕ ℕ → ℕ → ℕ) (block : H → Config ℕ ℕ → ℕ → Bool)
    (hthr : ∀ h f s, thr h f s ≤ 8)
    (hblock : ∀ h f s, (∀ c, ¬ dir c = 4 → f c = none) → block h f s = false)
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧
      σ.sel h = refineSel ((duatoMesh k).tieredSel (Mesh.gatedTiers k (thr h) (block h))) choose) :
    (duatoMesh k).StrategySafe σ (fun c => dir c = 4) :=
  duatoMesh_strategy_safe k fun h => by
    obtain ⟨choose, hch, he⟩ := hσ h
    rw [he]
    exact refineSel_sourceSelOn ((Mesh.gatedTiers_sourceSel (duatoMesh k)
      (fun _ _ => by simp [duatoMesh, Mesh.escCh]) (hthr h) (hblock h)).sourceSelOn _)
      ((duatoMesh k).tieredSel_freeOnly _) hch

/-- **The `lx` throttle on Duato's mesh, with the controller chosen by history, is safe**: in
state `h` a source uses the `lx` controller `(ball₂, o₂, lo₂, hi₂)` when `spread h s` and
`(ball₁, o₁, lo₁, hi₁)` otherwise, evaluated on the current configuration, with any admissible
choice `choose h` among the free hops of a tier. -/
theorem duatoMesh_lx_safe (k : ℕ) {H : Type*} (init : H)
    (update : H → Config ℕ ℕ → Act ℕ ℕ → Config ℕ ℕ → H) (admit : H → ℕ → ℕ → Prop)
    (spread : H → ℕ → Bool) (ball₁ ball₂ : ℕ → List ℕ) {o₁ lo₁ hi₁ o₂ lo₂ hi₂ : ℕ}
    (h₁ : lo₁ ≤ 8 ∧ hi₁ ≤ 8) (h₂ : lo₂ ≤ 8 ∧ hi₂ ≤ 8)
    (choose : H → Config ℕ ℕ → ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ))
    (hch : ∀ h, ChoiceOK (choose h)) :
    (duatoMesh k).StrategySafe
      { init := init, admit := admit, update := update
        sel := fun h => refineSel ((duatoMesh k).tieredSel (Mesh.gatedTiers k
          (fun f s => if spread h s then Mesh.meshLxThr ball₂ o₂ lo₂ hi₂ f s
            else Mesh.meshLxThr ball₁ o₁ lo₁ hi₁ f s)
          (fun f s => if spread h s then Mesh.meshLxBlock ball₂ o₂ f s
            else Mesh.meshLxBlock ball₁ o₁ f s))) (choose h) }
      (fun c => dir c = 4) :=
  duatoMesh_gated_safe k _ _
    (fun h f s => by
      split
      · exact Mesh.meshLxThr_le h₂.1 h₂.2 f s
      · exact Mesh.meshLxThr_le h₁.1 h₁.2 f s)
    (fun h f s hf => by
      split <;> exact Mesh.meshLxBlock_of_empty hf s)
    fun h => ⟨choose h, hch h, rfl⟩

#assert_standard_axioms torus_dist_step torus_choice_safe torus_price_safe torus_lxSel_sourceSel
#assert_standard_axioms torus_lx_correct torus_throttle_safe torus_combo_safe
#assert_standard_axioms duatoTiers_append_correct duatoMesh_strategy_safe duatoMesh_gated_safe
#assert_standard_axioms duatoMesh_lx_safe Mesh.gatedTiers_sourceSel

end AsyncLean.Examples
