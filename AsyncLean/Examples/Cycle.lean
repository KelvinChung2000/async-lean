/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.UpDown
import AsyncLean.Routing.Cycle
import AsyncLean.AxiomAudit

/-!
# Example: the cycle models of the simulators on the mesh and the torus

Instances of `AsyncLean.Routing.Cycle` for the schemes of the simulations, in both cycle models
of `scripts/xp_arbiter.py` (`chain = none`: `Network.NoChainCycle`; `chain = seq`:
`Network.SeqCycle`).  Runs of cycles use any selection a strategy may use (`Strategy.Uses`), so
the strategy's state may be updated by any rule, once per cycle or otherwise.

## The west-first mesh (`westFirstMesh k`, the tier strategies of `westFirstMesh_modes_safe`)

* `westFirstMesh_modes_cycles` : for every size, every tier strategy switched by any rule: in
  both cycle models, no deadlock (a work-conserving cycle moves a packet), no livelock, drain
  within a uniform number of cycles once injections stop, every hop a routing step from a legal
  pair; in the no-chaining model, every packet outside the injection channels delivered along
  every run that is channel fair at the cycle level.
* `westFirstMesh_throughput` : **the injection limit** — under every selection and strategy, in
  either cycle model, a node injects at most `K` packets in `K` cycles, and the `k × k` mesh
  delivers at most `k * k * K` packets in its first `K` cycles.

## The torus with the escape of the simulations (`simUD k`, the combined scheme `udComboStrategy`)

* `simUD_combo_cycles`, `simUD_throughput` : the same.

## The bound is attained (`Network.Saturated`)

* `Saturated.sat_run` : a run of the no-chaining model of the two-channel network of
  `AsyncLean.Routing.Saturation` that injects a packet in every cycle and, from cycle `2` on,
  delivers one in every cycle: the injection limit (one packet per injection channel and per
  cycle) is attained, so a scheme that reaches it — as dimension-order routing and our schemes do
  under neighbour traffic in the simulations — cannot be beaten.
-/

namespace AsyncLean.Examples

open Network Mesh GraphData

/-! ### The west-first mesh -/

/-- The packets of the mesh are injected into the injection channel `ch s 4 0` of a node. -/
theorem westFirstMesh_inject {k : ℕ} {q : ℕ × ℕ} (hq : q ∈ (westFirstMesh k).inject) :
    ∃ s < k * k, q.1 = ch s 4 0 := by
  simp only [westFirstMesh, turnDuatoMesh, allPairs, List.mem_flatMap, List.mem_range,
    List.mem_map, List.mem_filter] at hq
  obtain ⟨s, hs, d, -, rfl⟩ := hq
  exact ⟨s, hs, rfl⟩

/-- No escape hop of the mesh leads into an injection channel. -/
theorem westFirstMesh_esc_not_inject {k c d : ℕ} {q : ℕ × ℕ} (hq : q ∈ xyEscape k c d) (p : ℕ) :
    (q.1, p) ∉ (westFirstMesh k).inject := fun hm => by
  obtain ⟨s, -, hs⟩ := westFirstMesh_inject hm
  exact Mesh.esc_not_source hq
    (by rw [show q.1 = ch s 4 0 from hs]; exact dir_ch (by omega) (by omega))

/-- The selections of a west-first tier strategy satisfy Duato's condition with throttled
sources on the legal pairs. -/
theorem westFirstMesh_modes_sourceSelOn (k : ℕ) {H : Type*} {σ : Strategy ℕ ℕ H}
    (tiers : H → List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)) (g : H → ℕ) (hg : ∀ h, g h ≤ 8)
    (ht : ∀ h, escTier k (g h) ∈ tiers h)
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧
      σ.sel h = refineSel ((westFirstMesh k).tieredSel (tiers h)) choose) :
    ∀ s, σ.Uses s →
      (westFirstMesh k).SourceSelOn (wfLegal k) (xyEscape k) (fun c => dir c = 4) s := by
  rintro _ ⟨h, rfl⟩
  obtain ⟨choose, hch, he⟩ := hσ h
  rw [he]
  exact refineSel_sourceSelOn ((tieredSel_sourceSel (westFirstMesh k) (k := k)
    (fun _ _ => by simp [westFirstMesh, turnDuatoMesh]) (hg h) (ht h)).sourceSelOn _)
    ((westFirstMesh k).tieredSel_freeOnly _) hch

/-- **The west-first tier strategies are safe in both cycle models of the simulator**: for every
size, every tier strategy switched by any rule (as `westFirstMesh_modes_safe`), both the
no-chaining and the sequential model satisfy `Network.CycleSafe` (no deadlock, no livelock,
bounded drain, hop bounds), and in the no-chaining model every packet outside the injection
channels is delivered along every run that is channel fair at the cycle level. -/
theorem westFirstMesh_modes_cycles (k : ℕ) {H : Type*} {σ : Strategy ℕ ℕ H}
    (tiers : H → List (Config ℕ ℕ → ℕ → ℕ → ℕ × ℕ → Bool)) (g : H → ℕ) (hg : ∀ h, g h ≤ 8)
    (ht : ∀ h, escTier k (g h) ∈ tiers h)
    (hσ : ∀ h, ∃ choose, ChoiceOK choose ∧
      σ.sel h = refineSel ((westFirstMesh k).tieredSel (tiers h)) choose) :
    (westFirstMesh k).CycleSafe (westFirstMesh k).NoChainCycle (wfLegal k) σ.Uses ∧
      (westFirstMesh k).CycleSafe (westFirstMesh k).SeqCycle (wfLegal k) σ.Uses ∧
      ∀ r : CycleRun (westFirstMesh k).NoChainCycle σ.Uses, r.ChannelFair (westFirstMesh k) →
        ∀ n c, ¬ dir c = 4 → r.st n c ≠ none → r.Delivered n c := by
  have hok := westFirstMesh_modes_sourceSelOn k tiers g hg ht hσ
  have hsub : ∀ s, σ.Uses s → ∀ f c p q, q ∈ s f c p → q ∈ (westFirstMesh k).route c p :=
    fun s hs => (hok s hs).sub
  have hconn : ∀ c p, wfLegal k c p → (westFirstMesh k).arrived c p = false → xyEscape k c p ≠ [] :=
    fun _ _ _ _ => by simp [xyEscape]
  have hR₁ : ∀ c p q, wfLegal k c p → (westFirstMesh k).arrived c p = false →
      q ∈ xyEscape k c p → ¬ dir q.1 = 4 := fun _ _ _ _ _ hq => Mesh.esc_not_source hq
  have hrk : ∀ c p q, wfLegal k c p → (westFirstMesh k).arrived c p = false →
      q ∈ (westFirstMesh k).route c p → wfDist k q.1 q.2 < wfDist k c p :=
    fun _ _ _ hl ha hq => by have := wf_dist hl ha hq; omega
  refine ⟨cycleSafe (wf_closed k) (wf_pairs_finite k) (xyEscape k) hconn (wf_wf k) hR₁ (wfDist k)
      hrk hok (noChain_sequential hsub),
    cycleSafe (wf_closed k) (wf_pairs_finite k) (xyEscape k) hconn (wf_wf k) hR₁ (wfDist k)
      hrk hok (seq_sequential hsub), fun r hfair => ?_⟩
  exact r.delivered_of_channelFair (wf_closed k) hok hconn (wf_wf k) hR₁
    (fun _ _ _ _ _ hq p => westFirstMesh_esc_not_inject hq p)
    (fun _ _ _ _ _ hq => Mesh.turnDuato_not_source (fun _ _ _ _ h => westFirst_sub h) hq)
    (wfDist k) hrk hfair

/-- **The injection limit on the mesh**: for every selection and strategy that only use
permitted hops, in either cycle model (any `M` whose cycles are sequences of single steps), the
node `s` injects at most `K` packets in any `K` consecutive cycles, and the `k × k` mesh delivers
at most `k * k * K` packets in its first `K` cycles: at most one packet per node and per cycle. -/
theorem westFirstMesh_throughput (k : ℕ)
    {M : Selection ℕ ℕ → Config ℕ ℕ → Cycle ℕ ℕ → Config ℕ ℕ → Prop} {ok : Selection ℕ ℕ → Prop}
    (hM : (westFirstMesh k).Sequential M ok) (r : CycleRun M ok) (K : ℕ) :
    (∀ s W, ∑ i ∈ Finset.range K, ((r.cyc (W + i)).injects.map (·.1)).count (ch s 4 0) ≤ K) ∧
      ∑ i ∈ Finset.range K, (r.cyc i).ejects.length ≤ k * k * K := by
  have hchan : {c | ∃ p, wfLegal k c p}.Finite :=
    ((wf_pairs_finite k).image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩
  let I : Finset ℕ := (Finset.range (k * k)).image fun s => ch s 4 0
  have hI : ∀ q ∈ (westFirstMesh k).inject, q.1 ∈ I := fun q hq => by
    obtain ⟨s, hs, he⟩ := westFirstMesh_inject hq
    exact Finset.mem_image.2 ⟨s, Finset.mem_range.2 hs, he.symm⟩
  have hcard : I.card ≤ k * k := Finset.card_image_le.trans (by simp)
  refine ⟨fun s W => r.sum_count_inject_le hM _ W K, ?_⟩
  have := r.sum_ejects_le_start (wf_closed k) (T := hchan.toFinset)
    (fun c p h => hchan.mem_toFinset.2 ⟨p, h⟩) hM hI K
  exact this.trans (Nat.mul_le_mul_right K hcard)

/-! ### The torus with the escape of the simulations -/

/-- The packets of the detour network are injected into injection channels. -/
theorem escapeLayer_inject {V : Type*} [DecidableEq V] {G : GraphData V} {E : G.EscapeLayer}
    {B : ℕ} {W : V → V → List (Option V)} {q : GChan V × DetHdr V} (hq : q ∈ (E.net B W).inject) :
    q.1.isInj = true := by
  simp only [EscapeLayer.net, List.mem_flatMap, List.mem_map] at hq
  obtain ⟨s, -, d, -, w, -, rfl⟩ := hq
  rfl

/-- **The simulated combined scheme with the escape of the simulations is safe in both cycle
models**: for every size and every parameter of `simUD_combo_safe`, both models satisfy
`Network.CycleSafe`, and in the no-chaining model every packet outside the injection channels is
delivered along every run that is channel fair at the cycle level. -/
theorem simUD_combo_cycles (k B : ℕ) {H : Type*} (init : H)
    (update : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) →
      Act (GChan (TorusV k)) (DetHdr (TorusV k)) →
        Config (GChan (TorusV k)) (DetHdr (TorusV k)) → H)
    (admit : H → GChan (TorusV k) → DetHdr (TorusV k) → Prop)
    (snap : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)))
    (spread : H → TorusV k → Bool) (ball₁ ball₂ : TorusV k → List (TorusV k))
    {o₁ lo₁ hi₁ o₂ lo₂ hi₂ : ℕ} (h₁ : lo₁ ≤ 8 ∧ hi₁ ≤ 8) (h₂ : lo₂ ≤ 8 ∧ hi₂ ≤ 8)
    (choose : H → Config (GChan (TorusV k)) (DetHdr (TorusV k)) → GChan (TorusV k) →
      DetHdr (TorusV k) → List (GChan (TorusV k) × DetHdr (TorusV k)) →
      List (GChan (TorusV k) × DetHdr (TorusV k)))
    (hch : ∀ h, ChoiceOK (choose h)) :
    let N := (simUD k).esc.net B (torusAt k (centre k)).anyDetour
    let σ := udComboStrategy k B (centre k) (simUD k) init update admit snap spread ball₁ ball₂ o₁
      lo₁ hi₁ o₂ lo₂ hi₂ choose
    N.CycleSafe N.NoChainCycle ((simUD k).esc.srcLegal B) σ.Uses ∧
      N.CycleSafe N.SeqCycle ((simUD k).esc.srcLegal B) σ.Uses ∧
      ∀ r : CycleRun N.NoChainCycle σ.Uses, r.ChannelFair N →
        ∀ n c, ¬ c.isInj → r.st n c ≠ none → r.Delivered n c := by
  intro N σ
  let E := (simUD k).esc
  let W := (torusAt k (centre k)).anyDetour
  have hW : ∀ s d w, some w ∈ W s d → w ≠ s := (torusAt k (centre k)).anyDetour_ne
  have hok : ∀ s, σ.Uses s → N.SourceSelOn (E.srcLegal B) E.escape (fun c => c.isInj) s := by
    rintro _ ⟨h, rfl⟩
    refine refineSel_sourceSelOn (EscapeLayer.throttleSel_sourceSelOn
      (torusAt_dist_step k (centre k)) fun f s v => ?_) (N.tieredSel_freeOnly _) (hch h)
    rw [torusAt_nbrs_length]
    split
    · exact (torusAt k (centre k)).lxThr_le h₂.1 h₂.2 _ _
    · exact (torusAt k (centre k)).lxThr_le h₁.1 h₁.2 _ _
  have hsub : ∀ s, σ.Uses s → ∀ f c p q, q ∈ s f c p → q ∈ N.route c p :=
    fun s hs => (hok s hs).sub
  have hconn : ∀ c p, E.srcLegal B c p → N.arrived c p = false → E.escape c p ≠ [] :=
    fun c p hl ha => EscapeLayer.esc_conn B W c p hl.1 ha
  have hR₁ : ∀ c p q, E.srcLegal B c p → N.arrived c p = false → q ∈ E.escape c p →
      ¬ q.1.isInj := fun c p q hl ha hq => EscapeLayer.esc_not_inj B W c p q hl.1 ha hq
  have hrk : ∀ c p q, E.srcLegal B c p → N.arrived c p = false → q ∈ N.route c p →
      E.detRank q.1 q.2 < E.detRank c p :=
    fun c p q hl ha hq => EscapeLayer.rank_lt B W c p q hl.1 ha hq
  refine ⟨cycleSafe (EscapeLayer.srcLegal_closed B hW) (EscapeLayer.srcLegal_finite B) E.escape
      hconn (EscapeLayer.srcLegal_wf B W) hR₁ E.detRank hrk hok (noChain_sequential hsub),
    cycleSafe (EscapeLayer.srcLegal_closed B hW) (EscapeLayer.srcLegal_finite B) E.escape
      hconn (EscapeLayer.srcLegal_wf B W) hR₁ E.detRank hrk hok (seq_sequential hsub),
    fun r hfair => ?_⟩
  exact r.delivered_of_channelFair (EscapeLayer.srcLegal_closed B hW) hok hconn
    (EscapeLayer.srcLegal_wf B W) hR₁
    (fun c p q hl ha hq p' hm =>
      hR₁ c p q hl ha hq (escapeLayer_inject (E := E) (B := B) (W := W) (q := (q.1, p')) hm))
    (fun _ _ _ _ _ hq => EscapeLayer.route_not_inj hq) E.detRank hrk hfair

/-- **The injection limit on the torus**: for every selection and strategy that only use
permitted hops, in either cycle model, the node `s` injects at most `K` packets in any `K`
consecutive cycles, and the `(k + 1) × (k + 1)` torus delivers at most `(k + 1) * (k + 1) * K`
packets in its first `K` cycles: at most one packet per node and per cycle. -/
theorem simUD_throughput (k B : ℕ)
    {M : Selection (GChan (TorusV k)) (DetHdr (TorusV k)) →
      Config (GChan (TorusV k)) (DetHdr (TorusV k)) → Cycle (GChan (TorusV k)) (DetHdr (TorusV k)) →
        Config (GChan (TorusV k)) (DetHdr (TorusV k)) → Prop}
    {ok : Selection (GChan (TorusV k)) (DetHdr (TorusV k)) → Prop}
    (hM : ((simUD k).esc.net B (torusAt k (centre k)).anyDetour).Sequential M ok)
    (r : CycleRun M ok) (K : ℕ) :
    (∀ s W, ∑ i ∈ Finset.range K, ((r.cyc (W + i)).injects.map (·.1)).count (GChan.inj s) ≤ K) ∧
      ∑ i ∈ Finset.range K, (r.cyc i).ejects.length ≤ (k + 1) * (k + 1) * K := by
  let E := (simUD k).esc
  have hfin := EscapeLayer.chans_finite (E := E) B
  let I : Finset (GChan (TorusV k)) := Finset.univ.image GChan.inj
  have hI : ∀ q ∈ (E.net B (torusAt k (centre k)).anyDetour).inject, q.1 ∈ I := fun q hq => by
    have h := escapeLayer_inject hq
    revert h
    cases q.1 with
    | inj s => intro; exact Finset.mem_image.2 ⟨s, Finset.mem_univ _, rfl⟩
    | link _ _ _ => simp [GChan.isInj]
  have hcard : I.card ≤ (k + 1) * (k + 1) := Finset.card_image_le.trans (by simp)
  refine ⟨fun s W => r.sum_count_inject_le hM _ W K, ?_⟩
  have := r.sum_ejects_le_start (EscapeLayer.closed (E := E) B (torusAt k (centre k)).anyDetour)
    (T := hfin.toFinset) (fun c p h => hfin.mem_toFinset.2 ⟨p, h⟩) hM hI K
  exact this.trans (Nat.mul_le_mul_right K hcard)

#assert_standard_axioms westFirstMesh_inject westFirstMesh_esc_not_inject
#assert_standard_axioms westFirstMesh_modes_sourceSelOn westFirstMesh_modes_cycles
#assert_standard_axioms westFirstMesh_throughput escapeLayer_inject simUD_combo_cycles
#assert_standard_axioms simUD_throughput

/-! ### The injection limit is attained -/

namespace SatCycle

/-- The first cycle: inject. -/
def cy0 : Cycle Bool Unit := ⟨[], [], [(false, ())]⟩

/-- The second cycle: forward, inject. -/
def cy1 : Cycle Bool Unit := ⟨[], [(false, true, ())], [(false, ())]⟩

/-- Every later cycle: eject, forward, inject (without chaining: the output channel is free at
the start of the move phase because its packet was ejected at the start of the cycle). -/
def cy2 : Cycle Bool Unit := ⟨[true], [(false, true, ())], [(false, ())]⟩

theorem step0 : Saturated.net.NoChainCycle Saturated.net.adaptive empty cy0 Saturated.cfgA where
  eject := by decide
  eject_nodup := by decide
  hop := by decide
  hop_src_nodup := by decide
  hop_tgt_nodup := by decide
  inject := by decide
  inject_nodup := by decide
  eq := by decide

theorem step1 :
    Saturated.net.NoChainCycle Saturated.net.adaptive Saturated.cfgA cy1 Saturated.cfgAB where
  eject := by decide
  eject_nodup := by decide
  hop m hm := by
    simp only [cy1, List.mem_singleton] at hm
    subst hm
    exact ⟨(), by decide, rfl, by decide, Saturated.cfgA, by decide⟩
  hop_src_nodup := by decide
  hop_tgt_nodup := by decide
  inject := by decide
  inject_nodup := by decide
  eq := by decide

theorem step2 :
    Saturated.net.NoChainCycle Saturated.net.adaptive Saturated.cfgAB cy2 Saturated.cfgAB where
  eject := by decide
  eject_nodup := by decide
  hop m hm := by
    simp only [cy2, List.mem_singleton] at hm
    subst hm
    exact ⟨(), by decide, rfl, by decide, Saturated.cfgAB, by decide⟩
  hop_src_nodup := by decide
  hop_tgt_nodup := by decide
  inject := by decide
  inject_nodup := by decide
  eq := by decide

/-- **A saturated run of the no-chaining model**: the source injects in every cycle; from cycle
`2` on, every cycle ejects one packet, forwards one and injects one. -/
def run : CycleRun Saturated.net.NoChainCycle (· = Saturated.net.adaptive) where
  st n := if n = 0 then empty else if n = 1 then Saturated.cfgA else Saturated.cfgAB
  cyc n := if n = 0 then cy0 else if n = 1 then cy1 else cy2
  sel _ := Saturated.net.adaptive
  start := rfl
  sel_ok _ := rfl
  step n := by
    rcases n with _ | _ | n
    · exact step0
    · exact step1
    · exact step2

/-- **The injection limit is attained**: the source injects exactly `K` packets in any `K`
cycles (`CycleRun.sum_count_inject_le` says at most `K`). -/
theorem run_inject (W K : ℕ) :
    ∑ i ∈ Finset.range K, ((run.cyc (W + i)).injects.map (·.1)).count false = K := by
  have h : ∀ n, ((run.cyc n).injects.map (·.1)).count false = 1 := by
    intro n
    simp only [run]
    split_ifs <;> decide
  simp [h]

/-- **One packet delivered per cycle**: from cycle `2` on, every window of `K` cycles delivers
exactly `K` packets — the throughput is one packet per injection channel and per cycle, the
largest any scheme can achieve (`CycleRun.sum_ejects_le`). -/
theorem run_ejects (W K : ℕ) (hW : 2 ≤ W) :
    ∑ i ∈ Finset.range K, (run.cyc (W + i)).ejects.length = K := by
  have h : ∀ i, (run.cyc (W + i)).ejects.length = 1 := by
    intro i
    simp only [run, show W + i ≠ 0 by omega, show W + i ≠ 1 by omega, ↓reduceIte]
    rfl
  simp [h]

/-- The arbitration of the saturated run is work conserving. -/
theorem run_workConserving (n : ℕ) :
    Saturated.net.WorkConserving (run.sel n) (run.st n) (run.cyc n) := by
  rcases n with _ | _ | n
  · show Saturated.net.WorkConserving Saturated.net.adaptive empty cy0
    exact ⟨by decide, fun _ c p hp => by simp [cy0, Cycle.mid, Cycle.ejActs, empty] at hp⟩
  · show Saturated.net.WorkConserving Saturated.net.adaptive Saturated.cfgA cy1
    exact ⟨by decide, fun h => absurd h (by decide)⟩
  · show Saturated.net.WorkConserving Saturated.net.adaptive Saturated.cfgAB cy2
    exact ⟨by decide, fun h => absurd h (by decide)⟩

end SatCycle

#assert_standard_axioms SatCycle.run_inject SatCycle.run_ejects SatCycle.run_workConserving

end AsyncLean.Examples
