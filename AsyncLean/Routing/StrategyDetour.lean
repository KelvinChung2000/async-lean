/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.GraphDetour
import AsyncLean.Routing.Strategy

/-!
# History-dependent strategies on the detour network of any graph

Instances of `AsyncLean.Routing.Strategy` on `GraphData.detourNet B W`
(`AsyncLean.Routing.GraphDetour`: a source-chosen intermediate from `W s d`, minimal adaptive hops
on virtual channel 1, tree escape on virtual channel 0, at most `B` returns from it).

## The selections of the simulation

`scripts/xp_combo.py` (`csim`) routes a packet in two tiers: the free minimal hops on virtual
channel 1 towards its target, else its escape hop; at a source both tiers go through a **source
gate** (`scripts/xp_ramp.py`, `Ctrl.gate`), and a choice (random, cheapest under link prices,
most free hops ahead) picks among the free hops of the tier.  Here:

* `GraphData.outChans v`, `GraphData.freeOut f v`, `GraphData.routerEmpty f v` — the link
  channels leaving router `v` (both virtual channels), how many of them are free, whether all are.
* `GraphData.srcGate g block f c q` — from an injection channel, the hop `q` only towards a
  router with at least `g` free outgoing channels, and not into an escape channel when `block`;
  other channels are not gated.
* `GraphData.throttleSel B W thr block` — the two tiers through the gate, with threshold
  `thr f s` and escape blocking `block f s` for the source `s` (any functions);
  `Network.refineSel` adds any choice among the free hops of a tier (`Network.minChoice`: the
  cheapest under any score).
* `GraphData.escShareHigh ball o f s` — the **escape-share signal** of the `lx` controller: at
  least `o` % of the occupied link channels leaving the routers of `ball s` are escape channels
  (virtual channel 0).  `GraphData.lxThr ball o lo hi` is the threshold `hi` when it is high and
  `lo` otherwise; `GraphData.lxBlock ball o` blocks the escape while it is high and the source's
  own router has an occupied outgoing channel (the rule of `nesc`).  `lx2_4_36_2` is
  `lo = 2`, `hi = 4`, `o = 36`, `ball s` the routers within distance 2 of `s`.

## Main results

For every graph `G`, budget `B` and choice of intermediates `W`:

* `GraphData.throttleSel_sourceSel` — with thresholds at most twice the degree of every router
  and a blocking rule that is off whenever every link channel is empty, the throttled selection
  satisfies `Network.SourceSel` (a source lets its packet go when the rest of the network is
  empty); `GraphData.lxSel_sourceSel` — in particular the `lx` throttle evaluated on the current
  configuration.
* `GraphData.throttleSel_sourceSelOn` — with **any** blocking rule (for example one read from a
  snapshot of the network taken at the start of the cycle, as the simulator does), when `dist`
  is a distance (every vertex other than `t` has a neighbour closer to `t`) and no source is its
  own intermediate: `Network.SourceSelOn` on `GraphData.srcLegal` (the legal pairs whose packet
  in an injection channel has not chosen that channel's vertex as intermediate).  A blocked
  source still has a free adaptive hop once the network is empty.
* `GraphData.openSel_escapeSel` — without throttling, the two tiers with any admissible choice
  never refuse a free escape hop.
* `GraphData.detour_strategy_safe_of_escapeSel`, `GraphData.detour_strategy_safe_of_sourceSel`,
  `GraphData.detour_strategy_safe_of_sourceSelOn` — every strategy whose selections all satisfy
  the respective condition is deadlock free, livelock free, delivers every packet (outside the
  sources, under throttling) along every run channel fair relative to the selection in force, and
  every packet along every run strongly fair relative to the selection in force
  (`Network.StrategySafe`).  The intermediate a source chooses (`Strategy.admit`) is arbitrary.
-/

namespace AsyncLean

open Network

namespace GraphData

variable {V : Type*} [DecidableEq V] (G : GraphData V)

/-- The headers of the detour network: destination, intermediate, return budget. -/
abbrev DetHdr (V : Type*) := V × Option V × ℕ

/-! ### Routers and the source gate -/

/-- The link channels leaving router `v`, on both virtual channels. -/
def outChans (v : V) : List (GChan V) :=
  (G.nbrs v).flatMap fun u => [.link v u false, .link v u true]

/-- The number of free link channels leaving router `v`. -/
def freeOut {P : Type*} (f : Config (GChan V) P) (v : V) : ℕ :=
  (G.outChans v).countP fun c => (f c).isNone

/-- Every link channel leaving router `v` is free. -/
def routerEmpty {P : Type*} (f : Config (GChan V) P) (v : V) : Bool :=
  (G.outChans v).all fun c => (f c).isNone

omit [DecidableEq V] in
theorem length_outChans (v : V) : (G.outChans v).length = 2 * (G.nbrs v).length := by
  have : ∀ l : List V, (l.flatMap fun u => [GChan.link v u false, .link v u true]).length =
      2 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
      omega
  exact this _

omit [DecidableEq V] in
theorem outChans_not_inj {v : V} {c : GChan V} (h : c ∈ G.outChans v) : c.isInj = false := by
  simp only [outChans, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨u, -, rfl | rfl⟩ := h <;> rfl

omit [DecidableEq V] in
/-- When every link channel is empty, every router has all its outgoing channels free. -/
theorem freeOut_of_empty {P : Type*} {f : Config (GChan V) P}
    (hf : ∀ c, ¬ c.isInj = true → f c = none) (v : V) :
    G.freeOut f v = 2 * (G.nbrs v).length := by
  rw [← G.length_outChans v, freeOut, List.countP_eq_length]
  intro c hc
  simp [hf c (by simp [G.outChans_not_inj hc])]

omit [DecidableEq V] in
/-- When every link channel is empty, every router is empty. -/
theorem routerEmpty_of_empty {P : Type*} {f : Config (GChan V) P}
    (hf : ∀ c, ¬ c.isInj = true → f c = none) (v : V) : G.routerEmpty f v = true := by
  simp only [routerEmpty, List.all_eq_true]
  intro c hc
  simp [hf c (by simp [G.outChans_not_inj hc])]

/-- **The source gate**: from an injection channel, the hop `q` is allowed only towards a router
with at least `g` free outgoing channels, and not into an escape channel when `block`.  Hops from
other channels are not gated. -/
def srcGate {P : Type*} (g : ℕ) (block : Bool) (f : Config (GChan V) P) (c : GChan V)
    (q : GChan V × P) : Bool :=
  !c.isInj || (decide (g ≤ G.freeOut f q.1.head) && (!block || !q.1.isEsc))

/-! ### The throttled selection -/

/-- The two tiers of the simulation, through the source gate with threshold `thr f s` and escape
blocking `block f s` for the source `s`: the hops on virtual channel 1 (the minimal adaptive
hops towards the target), then the escape hop (virtual channel 0). -/
def throttleTiers (thr : Config (GChan V) (DetHdr V) → V → ℕ)
    (block : Config (GChan V) (DetHdr V) → V → Bool) :
    List (Config (GChan V) (DetHdr V) → GChan V → DetHdr V → GChan V × DetHdr V → Bool) :=
  [fun f c _ q => G.srcGate (thr f c.head) (block f c.head) f c q && !q.1.isEsc,
   fun f c _ q => G.srcGate (thr f c.head) (block f c.head) f c q && q.1.isEsc]

/-- **The throttled two-tier selection** on the detour network: the free minimal hops on virtual
channel 1 that pass the source gate, else the escape hop if it passes the gate. -/
def throttleSel (B : ℕ) (W : V → V → List (Option V)) (thr : Config (GChan V) (DetHdr V) → V → ℕ)
    (block : Config (GChan V) (DetHdr V) → V → Bool) : Selection (GChan V) (DetHdr V) :=
  (G.detourNet B W).tieredSel (G.throttleTiers thr block)

/-- The two tiers without throttling (`thr = 0`, no blocking): the free minimal hops on virtual
channel 1, else the escape hop. -/
def openSel (B : ℕ) (W : V → V → List (Option V)) : Selection (GChan V) (DetHdr V) :=
  G.throttleSel B W (fun _ _ => 0) (fun _ _ => false)

theorem escHop_isEsc (c : GChan V) (d : V) : (G.escHop c d).1.isEsc = true := rfl

theorem detEscape_isEsc {c : GChan V} {p : DetHdr V} {q : GChan V × DetHdr V}
    (hq : q ∈ G.detEscape c p) : q.1.isEsc = true := by
  simp only [detEscape, List.mem_singleton] at hq
  subst hq; rfl

/-- The escape tier admits the escape hop from every channel outside the sources. -/
theorem escTier_non {thr : Config (GChan V) (DetHdr V) → V → ℕ}
    {block : Config (GChan V) (DetHdr V) → V → Bool} {f : Config (GChan V) (DetHdr V)}
    {c : GChan V} {p : DetHdr V} {q : GChan V × DetHdr V} (hc : ¬ c.isInj = true)
    (hq : q ∈ G.detEscape c p) :
    (G.srcGate (thr f c.head) (block f c.head) f c q && q.1.isEsc) = true := by
  simp [srcGate, hc, G.detEscape_isEsc hq]

/-- **The throttled selection satisfies Duato's condition with throttled sources**, whatever
the thresholds (at most twice the degree of every router) and whatever the blocking rule, as
long as it is off when every link channel is empty: a source lets its packet go once the rest of
the network is empty. -/
theorem throttleSel_sourceSel {B : ℕ} {W : V → V → List (Option V)}
    {thr : Config (GChan V) (DetHdr V) → V → ℕ} {block : Config (GChan V) (DetHdr V) → V → Bool}
    (hthr : ∀ f s v, thr f s ≤ 2 * (G.nbrs v).length)
    (hblock : ∀ f s, (∀ c, ¬ c.isInj = true → f c = none) → block f s = false) :
    (G.detourNet B W).SourceSel G.detEscape (fun c => c.isInj) (G.throttleSel B W thr block) :=
  (G.detourNet B W).tieredSel_sourceSel (fun _ _ _ hq => G.detEscape_sub hq)
    (List.mem_cons_of_mem _ List.mem_cons_self) (fun _ _ _ _ hc hq => G.escTier_non hc hq)
    (fun f c p q _ he hq => by
      simp [srcGate, G.freeOut_of_empty he, hthr, hblock f c.head he, G.detEscape_isEsc hq])

/-- **Without throttling, the two tiers never refuse a free escape hop.** -/
theorem openSel_escapeSel {B : ℕ} {W : V → V → List (Option V)} :
    (G.detourNet B W).EscapeSel G.detEscape (G.openSel B W) :=
  (G.detourNet B W).tieredSel_escapeSel (fun _ _ _ hq => G.detEscape_sub hq)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun _ _ _ _ hq => by simp [srcGate, G.detEscape_isEsc hq])

/-- **Any admissible choice among the free hops of the open tiers** (the cheapest under link
prices, under learned latencies, …) never refuses a free escape hop. -/
theorem refine_openSel_escapeSel {B : ℕ} {W : V → V → List (Option V)}
    {choose : Config (GChan V) (DetHdr V) → GChan V → DetHdr V →
      List (GChan V × DetHdr V) → List (GChan V × DetHdr V)} (hch : ChoiceOK choose) :
    (G.detourNet B W).EscapeSel G.detEscape (refineSel (G.openSel B W) choose) :=
  refineSel_escapeSel G.openSel_escapeSel ((G.detourNet B W).tieredSel_freeOnly _) hch

/-! ### Blocking read from a snapshot -/

/-- The legal pairs, refined: a packet in the injection channel of `s` does not have `s` as its
intermediate. -/
def srcLegal (B : ℕ) (c : GChan V) (p : DetHdr V) : Prop :=
  G.detLegal B c p ∧ ∀ s, c = .inj s → p.2.1 ≠ some s

/-- The refined legal pairs are closed when no source is its own intermediate. -/
theorem srcLegal_closed (B : ℕ) {W : V → V → List (Option V)}
    (hW : ∀ s d w, some w ∈ W s d → w ≠ s) : (G.detourNet B W).Closed (G.srcLegal B) where
  inject q hq := by
    refine ⟨(G.detour_closed B W).inject q hq, ?_⟩
    simp only [detourNet, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨s, -, d, -, w, hw, rfl⟩ := hq
    rintro s' hs' rfl
    cases hs'
    exact hW s d s hw rfl
  route c p q hl ha hq := by
    refine ⟨(G.detour_closed B W).route c p q hl.1 ha hq, ?_⟩
    intro s hs
    exact absurd (by rw [hs]; rfl) (G.detour_route_not_inj hq)

theorem srcLegal_wf (B : ℕ) (W : V → V → List (Option V)) :
    WellFounded (flip ((G.detourNet B W).Dep (G.srcLegal B) G.detEscape)) :=
  Subrelation.wf (fun ⟨p, p', hl, ha, hq⟩ => ⟨p, p', hl.1, ha, hq⟩) (G.detour_esc_wf B W)

theorem srcLegal_finite (B : ℕ) :
    {q : GChan V × DetHdr V | G.srcLegal B q.1 q.2}.Finite :=
  (G.detour_pairs_finite B).subset fun _ hq => hq.1

omit [DecidableEq V] in
/-- A packet that has not arrived, in the injection channel of `s`, in a refined legal pair, has
a target other than `s`. -/
theorem target_ne_of_srcLegal {B : ℕ} {s : V} {p : DetHdr V} (hl : G.srcLegal B (.inj s) p)
    (ha : s ≠ p.1) : s ≠ target p := by
  obtain ⟨d, w, b⟩ := p
  cases w with
  | none => simpa [target] using ha
  | some w =>
    simp only [target, Option.getD_some]
    exact fun h => hl.2 s rfl (by rw [h])

/-- **The throttled selection with any blocking rule** satisfies Duato's condition with
throttled sources on the refined legal pairs, when `dist` is a distance (every vertex other than
`t` has a neighbour closer to `t`): a blocked source, once the rest of the network is empty, has
a free minimal hop on virtual channel 1 towards a router with all its outgoing channels free.
The blocking rule may read anything — the configuration at the start of the cycle, the history. -/
theorem throttleSel_sourceSelOn {B : ℕ} {W : V → V → List (Option V)}
    (hdist : ∀ u t, u ≠ t → ∃ v ∈ G.nbrs u, G.dist v t < G.dist u t)
    {thr : Config (GChan V) (DetHdr V) → V → ℕ} {block : Config (GChan V) (DetHdr V) → V → Bool}
    (hthr : ∀ f s v, thr f s ≤ 2 * (G.nbrs v).length) :
    (G.detourNet B W).SourceSelOn (G.srcLegal B) G.detEscape (fun c => c.isInj)
      (G.throttleSel B W thr block) where
  sub _ _ _ _ h := ((G.detourNet B W).mem_tieredSel h).1
  conserving f c p _ _ hc _ := fun ⟨q, hq, hfree⟩ =>
    (G.detourNet B W).tieredSel_conserving (List.mem_cons_of_mem _ List.mem_cons_self)
      (G.detEscape_sub hq) hfree (G.escTier_non hc hq)
  source f c p hl ha hc _ he := fun ⟨q, hq, hfree⟩ => by
    cases hb : block f c.head with
    | false =>
      refine (G.detourNet B W).tieredSel_conserving (List.mem_cons_of_mem _ List.mem_cons_self)
        (G.detEscape_sub hq) hfree ?_
      simp [srcGate, G.freeOut_of_empty he, hthr, hb, G.detEscape_isEsc hq]
    | true =>
      obtain ⟨s, rfl⟩ : ∃ s, c = .inj s := by
        cases c with
        | inj s => exact ⟨s, rfl⟩
        | link _ _ _ => simp [GChan.isInj] at hc
      have hs : s ≠ target p :=
        G.target_ne_of_srcLegal hl (fun h => by simp [detourNet, GChan.head, h] at ha)
      obtain ⟨v, hv, hd⟩ := hdist s (target p) hs
      have hmem : (GChan.link s v true, (p.1, dropAt v p.2.1, (retHdr (.inj s) (p.1, p.2.2)).2)) ∈
          (G.detourNet B W).route (.inj s) p := by
        simp only [detourNet, List.mem_append]
        right
        simp only [mayReturn, GChan.isEsc, Bool.not_false, Bool.true_or, ↓reduceIte, detAdaptive,
          adaptiveHops, GChan.head, List.map_map, List.mem_map, List.mem_filter]
        exact ⟨v, ⟨hv, decide_eq_true hd⟩, rfl⟩
      refine (G.detourNet B W).tieredSel_conserving List.mem_cons_self hmem
        (he _ (by simp [GChan.isInj])) ?_
      simp [srcGate, G.freeOut_of_empty he, hthr, GChan.isEsc]

/-! ### The escape-share signal of the `lx` controller -/

/-- The number of occupied link channels leaving the routers of `vs`. -/
def occOut {P : Type*} (f : Config (GChan V) P) (vs : List V) : ℕ :=
  (vs.flatMap G.outChans).countP fun c => (f c).isSome

/-- The number of occupied escape channels (virtual channel 0) leaving the routers of `vs`. -/
def occEscOut {P : Type*} (f : Config (GChan V) P) (vs : List V) : ℕ :=
  (vs.flatMap G.outChans).countP fun c => (f c).isSome && c.isEsc

/-- **The escape-share signal**: at least `o` % of the occupied link channels leaving the routers
of `ball s` are escape channels (`cnt0 / max(1, cnt) ≥ o / 100` in `scripts/xp_ramp.py`). -/
def escShareHigh {P : Type*} (ball : V → List V) (o : ℕ) (f : Config (GChan V) P) (s : V) :
    Bool :=
  decide (o * max 1 (G.occOut f (ball s)) ≤ 100 * G.occEscOut f (ball s))

/-- The threshold of the `lx` controller: `hi` while the escape share is high, `lo` otherwise. -/
def lxThr {P : Type*} (ball : V → List V) (o lo hi : ℕ) (f : Config (GChan V) P) (s : V) : ℕ :=
  if G.escShareHigh ball o f s then hi else lo

/-- The escape blocking of the `lx` controller (the rule of `nesc`, in the high mode): no direct
injection into an escape channel while the escape share is high and the source's own router has
an occupied outgoing channel. -/
def lxBlock {P : Type*} (ball : V → List V) (o : ℕ) (f : Config (GChan V) P) (s : V) : Bool :=
  G.escShareHigh ball o f s && !G.routerEmpty f s

/-- **The `lx` throttle**, evaluated on the current configuration. -/
def lxSel (B : ℕ) (W : V → V → List (Option V)) (ball : V → List V) (o lo hi : ℕ) :
    Selection (GChan V) (DetHdr V) :=
  G.throttleSel B W (G.lxThr ball o lo hi) (G.lxBlock ball o)

omit [DecidableEq V] in
theorem lxThr_le {P : Type*} {ball : V → List V} {o lo hi m : ℕ} (hlo : lo ≤ m) (hhi : hi ≤ m)
    (f : Config (GChan V) P) (s : V) : G.lxThr ball o lo hi f s ≤ m := by
  unfold lxThr; split <;> assumption

omit [DecidableEq V] in
/-- The `lx` blocking is off when every link channel is empty. -/
theorem lxBlock_of_empty {P : Type*} {ball : V → List V} {o : ℕ} {f : Config (GChan V) P}
    (hf : ∀ c, ¬ c.isInj = true → f c = none) (s : V) : G.lxBlock ball o f s = false := by
  simp [lxBlock, G.routerEmpty_of_empty hf]

/-- **The `lx` throttle satisfies Duato's condition with throttled sources**, for every
neighbourhood, share threshold and pair of thresholds at most twice the least degree. -/
theorem lxSel_sourceSel {B : ℕ} {W : V → V → List (Option V)} {ball : V → List V}
    {o lo hi : ℕ} (hlo : ∀ v, lo ≤ 2 * (G.nbrs v).length) (hhi : ∀ v, hi ≤ 2 * (G.nbrs v).length) :
    (G.detourNet B W).SourceSel G.detEscape (fun c => c.isInj) (G.lxSel B W ball o lo hi) :=
  G.throttleSel_sourceSel (fun f s v => G.lxThr_le (hlo v) (hhi v) f s)
    (fun _ s hf => G.lxBlock_of_empty hf s)

/-! ### Strategies on the detour network -/

variable {H : Type*}

/-- **Every strategy on the detour network whose selections never refuse a free escape hop is
safe**, with no throttled source: deadlock and livelock free, and every packet is delivered
under sustained load and under strong fairness (both relative to the selection in force). -/
theorem detour_strategy_safe_of_escapeSel {B : ℕ} {W : V → V → List (Option V)}
    {σ : Strategy (GChan V) (DetHdr V) H}
    (hσ : ∀ h, (G.detourNet B W).EscapeSel G.detEscape (σ.sel h)) :
    (G.detourNet B W).StrategySafe σ (fun _ => False) :=
  Strategy.safe (G.detour_closed B W) (G.detour_pairs_finite B) G.detEscape
    (G.detour_esc_conn B W) (G.detour_esc_wf B W) (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ h => h) G.detRank (G.detour_rank_lt B W)
    (fun h => (hσ h).sourceSelOn _ _)

/-- **Every throttling strategy on the detour network is safe**: if every selection it uses
satisfies Duato's condition with throttled sources, it is deadlock and livelock free, delivers
every packet outside the injection channels under sustained load and every packet under strong
fairness (both relative to the selection in force). -/
theorem detour_strategy_safe_of_sourceSel {B : ℕ} {W : V → V → List (Option V)}
    {σ : Strategy (GChan V) (DetHdr V) H}
    (hσ : ∀ h, (G.detourNet B W).SourceSel G.detEscape (fun c => c.isInj) (σ.sel h)) :
    (G.detourNet B W).StrategySafe σ (fun c => c.isInj) :=
  Strategy.safe (G.detour_closed B W) (G.detour_pairs_finite B) G.detEscape
    (G.detour_esc_conn B W) (G.detour_esc_wf B W) (G.detour_esc_not_inj B W)
    (fun _ _ _ _ _ hq => G.detour_route_not_inj hq) G.detRank (G.detour_rank_lt B W)
    (fun h => (hσ h).sourceSelOn _)

/-- **Every throttling strategy on the refined legal pairs is safe**, when no source is its own
intermediate: as `detour_strategy_safe_of_sourceSel`, for selections that satisfy Duato's
condition with throttled sources only on `srcLegal` (such as the throttle with blocking read from
a snapshot, `throttleSel_sourceSelOn`). -/
theorem detour_strategy_safe_of_sourceSelOn {B : ℕ} {W : V → V → List (Option V)}
    (hW : ∀ s d w, some w ∈ W s d → w ≠ s) {σ : Strategy (GChan V) (DetHdr V) H}
    (hσ : ∀ h, (G.detourNet B W).SourceSelOn (G.srcLegal B) G.detEscape (fun c => c.isInj)
      (σ.sel h)) :
    (G.detourNet B W).StrategySafe σ (fun c => c.isInj) :=
  Strategy.safe (G.srcLegal_closed B hW) (G.srcLegal_finite B) G.detEscape
    (fun c p hl ha => G.detour_esc_conn B W c p hl.1 ha) (G.srcLegal_wf B W)
    (fun c p q hl ha hq => G.detour_esc_not_inj B W c p q hl.1 ha hq)
    (fun _ _ _ _ _ hq => G.detour_route_not_inj hq) G.detRank
    (fun c p q hl ha hq => G.detour_rank_lt B W c p q hl.1 ha hq) hσ

/-- Valiant's choice of intermediates never makes a source its own intermediate. -/
theorem anyDetour_ne (s d w : V) (h : some w ∈ G.anyDetour s d) : w ≠ s := by
  simp only [anyDetour, List.mem_cons, reduceCtorEq, List.mem_map, List.mem_filter,
    Option.some.injEq, false_or] at h
  obtain ⟨w', ⟨-, hw'⟩, rfl⟩ := h
  simpa using hw'

end GraphData

end AsyncLean
