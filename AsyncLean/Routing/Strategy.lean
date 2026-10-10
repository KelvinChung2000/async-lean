/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Saturation
import Mathlib.Basic.Finite.Prod

/-!
# History-dependent routing strategies

A `Network.Selection` reads only the current configuration.  The schemes that perform best in
simulation also read **history**: smoothed link prices, learned latencies, per-source counts of
recent destinations, the state of a feedback controller, a snapshot of the network taken at the
start of a clock cycle, a random generator.  This file proves that the safety theorems carry
over to such strategies, as long as *every selection the strategy may use* satisfies the
hypothesis of the configuration-only theorem.

## Two formulations

* `Network.Strategy C P H` — a strategy with a state `H` of any type (the history, or anything
  computed from it): an initial state, the selection `sel h` used in state `h`, the injections
  `admit h` it allows (for example the intermediate chosen at the source by link prices), and an
  update `update h f a f'` after each step.  `N.stratLTS σ` is the network under the strategy, a
  transition system on pairs (configuration, state).
* `Network.SelRun N ok` — a run under a **time-varying selection**: the selection `sel n` used at
  step `n` is arbitrary, as long as it satisfies `ok`.  Nothing constrains how it is chosen, so
  this covers histories updated nondeterministically, by an adversary, or at random.  Every run
  of a strategy is one (`Network.Strategy.toSelRun`), and the theorems are proved for `SelRun`s.

The injections of a run are unconstrained (any subset of `N.inject`, chosen by any rule), so a
history-dependent choice among the packets a source may inject is covered as it stands.

## The hypotheses

`Network.SourceSelOn legal R₁ src sel` is `Network.SourceSel R₁ src sel` (Duato's condition with
throttled sources) required only at the legal pairs whose packet has not arrived — the only pairs
at which a selection is ever consulted.  `SourceSel` implies it (`SourceSel.sourceSelOn`), and so
does `EscapeSel` (`EscapeSel.sourceSelOn`); the weaker form admits throttles that may refuse an
escape hop at a source while offering an adaptive one, which needs an invariant of the legal
pairs (used for the snapshot-based throttle of `AsyncLean.Routing.StrategyDetour`).

## Fairness relative to the selection in force

For a fixed selection, `LTS.Run.StronglyFair` and `Network.ChannelFair` speak of the actions
*enabled* in a configuration.  Under a time-varying selection the hops enabled at time `n` are
those offered by `sel n`, so the natural adaptation reads enabledness under the selection in
force at each step:

* `Network.SelRun.ChannelFair` — for every channel `c`: if infinitely often a hop out of `c` or
  the ejection from `c` is enabled *under the selection used at that step*, then infinitely
  often one is taken (a fair arbiter that only sees the hops it is offered).
* `Network.SelRun.StronglyFair` — for every configuration `f` and **move** `f —a→ f'`: if
  infinitely often the run is at `f` with `a` enabled under the selection used at that step,
  then infinitely often it takes `a` from `f`.  Injections are not constrained (a strategy may
  refuse them for ever).

These are *weaker* hypotheses than fairness with respect to the union of the admissible
selections (which a strategy that never offers some hop could not satisfy).  For a constant
selection, channel fairness is exactly `Network.ChannelFair` (`Network.SelRun.channelFair_ofRun`)
and strong fairness is implied by `LTS.Run.StronglyFair` (`Network.SelRun.stronglyFair_ofRun`;
it is weaker, since it says nothing about injections).  No stronger hypothesis than the old ones
is needed.

## Main results

With a closed legal set, a connected escape subfunction `R₁` with a well-founded dependency
graph and no escape hop into a source, a ranking function decreasing on every hop, and every
admissible selection satisfying `SourceSelOn legal R₁ src`:

* `Network.movable_of_sourceSelOn` — **deadlock freedom is a property of one configuration**:
  every non-empty configuration of legal packets can move under every such selection; so
  `Network.Strategy.movable`: in every reachable state `(f, h)` of a strategy with `f` non-empty,
  some packet can move under the selection `sel h` the strategy uses there.
* `Network.Strategy.livelockFree`, `Network.SelRun.infOften_not_move` — **livelock freedom**:
  no run of the strategy consists, from some point on, of moves only.
* `Network.SelRun.hop_packetStep` — every hop of every run is a routing step of the packet from
  a legal pair, so the **hop bounds** of the routing function (`Network.packet_hops_le`, the
  `detour_hops_le_*` theorems) hold for every packet of every run.
* `Network.SelRun.delivered_of_channelFair` — **delivery under load**: along every run that is
  channel fair relative to the selection in force, with injections going on for ever, every
  packet held outside the sources is delivered (no finiteness needed).
* `Network.SelRun.delivered_of_stronglyFair` — **starvation freedom**: with finitely many legal
  pairs, along every run that is strongly fair relative to the selection in force, every packet
  is delivered, those held back at a source included.  The proof does not go through the drain
  theorem (the selection changes along a drain): from a configuration that recurs, a move is
  enabled at each visit (deadlock freedom of the selection in force), finitely many moves exist,
  so one is enabled infinitely often and is taken; its target recurs, and the moves are
  well-founded (livelock freedom of the union of the admissible selections).
* `Network.Strategy.safe` — the four guarantees bundled for a strategy (`Network.StrategySafe`).

Generic building blocks for strategies: `Network.refineSel` (a history-dependent choice — the
cheapest hop under link prices, the one with the best learned latency — among the free hops a
selection offers keeps `SourceSelOn` and `EscapeSel`), `Network.minChoice` (the cheapest hops
under any score), `Network.tieredSel_escapeSel` (a tiered selection with a tier admitting every
escape hop never refuses one), `Network.unionSel` (the union of the admissible selections).

## What is not covered

Fairness is assumed, not constructed: whether a given arbiter is fair relative to the selection
in force is a property of the scheduler.  Strong fairness still makes a run revisit the empty
network (as in `AsyncLean.Routing.Saturation`); packets held back at a throttling source may
wait for ever under channel fairness alone.  A simulator in which a channel vacated in a cycle
cannot be re-entered in the same cycle refuses free escape hops for the rest of the cycle; that
is not a selection satisfying `SourceSelOn`, and is not covered.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*}

/-! ### Duato's condition on the legal pairs -/

section Defs

variable (N : Network C P)

/-- **Duato's condition with throttled sources, on the legal pairs**: `Network.SourceSel`,
required only for packets in legal pairs that have not arrived (the only packets a selection is
consulted for). -/
structure SourceSelOn (legal : C → P → Prop) (R₁ : C → P → List (C × P)) (src : C → Prop)
    (sel : Selection C P) : Prop where
  /-- Only permitted hops are offered. -/
  sub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p
  /-- Outside the sources, a free escape hop means a free hop is offered. -/
  conserving : ∀ f c p, legal c p → N.arrived c p = false → ¬ src c → f c = some p →
    (∃ q ∈ R₁ c p, f q.1 = none) → ∃ q ∈ sel f c p, f q.1 = none
  /-- At a source, when every channel outside the sources is empty, a free escape hop means a
  free hop is offered. -/
  source : ∀ f c p, legal c p → N.arrived c p = false → src c → f c = some p →
    (∀ c', ¬ src c' → f c' = none) → (∃ q ∈ R₁ c p, f q.1 = none) → ∃ q ∈ sel f c p, f q.1 = none

variable {N}

/-- `SourceSel` implies `SourceSelOn`, for every set of legal pairs. -/
theorem SourceSel.sourceSelOn {R₁ : C → P → List (C × P)} {src : C → Prop} {sel : Selection C P}
    (h : N.SourceSel R₁ src sel) (legal : C → P → Prop) : N.SourceSelOn legal R₁ src sel :=
  ⟨h.sub, fun f c p _ _ hs hp => h.conserving f c p hs hp,
    fun f c p _ _ hs hp he => h.source f c p hs hp he⟩

/-- A selection that never refuses a free escape hop satisfies `SourceSelOn`, for every set of
sources and of legal pairs. -/
theorem EscapeSel.sourceSelOn {R₁ : C → P → List (C × P)} {sel : Selection C P}
    (h : N.EscapeSel R₁ sel) (legal : C → P → Prop) (src : C → Prop) :
    N.SourceSelOn legal R₁ src sel :=
  (EscapeSel.sourceSel N h src).sourceSelOn legal

/-- A selection that only offers free channels. -/
def FreeOnly (sel : Selection C P) : Prop := ∀ f c p q, q ∈ sel f c p → f q.1 = none

end Defs

/-! ### Choices among the offered hops -/

section Choice

variable (N : Network C P)

/-- A **choice** among the hops a selection offers: `choose f c p l` picks some of the hops of
`l` (for example the cheapest under link prices that the strategy has learned). -/
def refineSel (sel : Selection C P)
    (choose : Config C P → C → P → List (C × P) → List (C × P)) : Selection C P :=
  fun f c p => choose f c p (sel f c p)

/-- A choice is **admissible** when it only picks offered hops, and picks one when one is
offered. -/
structure ChoiceOK (choose : Config C P → C → P → List (C × P) → List (C × P)) : Prop where
  /-- Only offered hops are picked. -/
  sub : ∀ f c p l q, q ∈ choose f c p l → q ∈ l
  /-- Some hop is picked when one is offered. -/
  ne_nil : ∀ f c p l, l ≠ [] → choose f c p l ≠ []

variable {N}

/-- An admissible choice among the free hops offered by a selection satisfying `SourceSelOn`
satisfies `SourceSelOn`. -/
theorem refineSel_sourceSelOn {legal : C → P → Prop} {R₁ : C → P → List (C × P)}
    {src : C → Prop} {sel : Selection C P} (hsel : N.SourceSelOn legal R₁ src sel)
    (hfree : FreeOnly sel) {choose : Config C P → C → P → List (C × P) → List (C × P)}
    (hch : ChoiceOK choose) : N.SourceSelOn legal R₁ src (refineSel sel choose) := by
  have key : ∀ f c p, (∃ q ∈ sel f c p, f q.1 = none) →
      ∃ q ∈ refineSel sel choose f c p, f q.1 = none := by
    rintro f c p ⟨q, hq, -⟩
    obtain ⟨q', hq'⟩ := List.exists_mem_of_ne_nil _ (hch.ne_nil f c p _ (List.ne_nil_of_mem hq))
    exact ⟨q', hq', hfree f c p q' (hch.sub f c p _ q' hq')⟩
  exact ⟨fun f c p q h => hsel.sub f c p q (hch.sub f c p _ q h),
    fun f c p hl ha hs hp he => key f c p (hsel.conserving f c p hl ha hs hp he),
    fun f c p hl ha hs hp hr he => key f c p (hsel.source f c p hl ha hs hp hr he)⟩

/-- An admissible choice among the free hops offered by a selection that never refuses a free
escape hop never refuses one either. -/
theorem refineSel_escapeSel {R₁ : C → P → List (C × P)} {sel : Selection C P}
    (hsel : N.EscapeSel R₁ sel) (hfree : FreeOnly sel)
    {choose : Config C P → C → P → List (C × P) → List (C × P)} (hch : ChoiceOK choose) :
    N.EscapeSel R₁ (refineSel sel choose) := by
  refine ⟨fun f c p q h => hsel.sub f c p q (hch.sub f c p _ q h), fun f c p hp he => ?_⟩
  obtain ⟨q, hq, -⟩ := hsel.conserving f c p hp he
  obtain ⟨q', hq'⟩ := List.exists_mem_of_ne_nil _ (hch.ne_nil f c p _ (List.ne_nil_of_mem hq))
  exact ⟨q', hq', hfree f c p q' (hch.sub f c p _ q' hq')⟩

/-- The hops of `l` of least score. -/
def minChoice (score : Config C P → C → P → C × P → ℕ) :
    Config C P → C → P → List (C × P) → List (C × P) :=
  fun f c p l => l.filter fun q => l.all fun q' => decide (score f c p q ≤ score f c p q')

theorem exists_min_score {α : Type*} (s : α → ℕ) :
    ∀ l : List α, l ≠ [] → ∃ q ∈ l, ∀ q' ∈ l, s q ≤ s q'
  | [], h => absurd rfl h
  | a :: l, _ => by
    by_cases hl : l = []
    · subst hl; exact ⟨a, List.mem_cons_self, fun q' hq' => by simp_all⟩
    · obtain ⟨m, hm, hmin⟩ := exists_min_score s l hl
      by_cases ham : s a ≤ s m
      · refine ⟨a, List.mem_cons_self, fun q' hq' => ?_⟩
        rcases List.mem_cons.1 hq' with rfl | hq'
        · exact le_rfl
        · exact ham.trans (hmin q' hq')
      · refine ⟨m, List.mem_cons_of_mem _ hm, fun q' hq' => ?_⟩
        rcases List.mem_cons.1 hq' with rfl | hq'
        · omega
        · exact hmin q' hq'

/-- **Choosing the cheapest hops**, under any score (link prices, learned latencies, tolls,
read from the strategy's history), is an admissible choice. -/
theorem minChoice_ok (score : Config C P → C → P → C × P → ℕ) : ChoiceOK (minChoice score) where
  sub _ _ _ _ _ h := (List.mem_filter.1 h).1
  ne_nil f c p l hl := by
    obtain ⟨q, hq, hmin⟩ := exists_min_score (score f c p) l hl
    refine List.ne_nil_of_mem (List.mem_filter.2 ⟨hq, ?_⟩)
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact hmin

/-- A tiered selection only offers free channels. -/
theorem tieredSel_freeOnly (tiers : List (Config C P → C → P → C × P → Bool)) :
    FreeOnly (N.tieredSel tiers) := fun _ _ _ _ h => (N.mem_tieredSel h).2

/-- **A tiered selection with a tier admitting every escape hop never refuses a free escape
hop**, whatever the other tiers prefer (and whatever they read: the configuration, or the
history through the strategy that builds the tier list). -/
theorem tieredSel_escapeSel {R₁ : C → P → List (C × P)}
    (hR : ∀ c p q, q ∈ R₁ c p → q ∈ N.route c p)
    {tiers : List (Config C P → C → P → C × P → Bool)} {t : Config C P → C → P → C × P → Bool}
    (ht : t ∈ tiers) (hadm : ∀ f c p q, q ∈ R₁ c p → t f c p q = true) :
    N.EscapeSel R₁ (N.tieredSel tiers) :=
  ⟨fun _ _ _ _ h => (N.mem_tieredSel h).1, fun f c p _ ⟨q, hq, hfree⟩ =>
    N.tieredSel_conserving ht (hR c p q hq) hfree (hadm f c p q hq)⟩

/-- **A tiered selection with a throttled escape tier satisfies Duato's condition with throttled
sources**: some tier admits every escape hop from a channel outside the sources, and from a
source whenever every channel outside the sources is empty. -/
theorem tieredSel_sourceSel {R₁ : C → P → List (C × P)} {src : C → Prop}
    (hR : ∀ c p q, q ∈ R₁ c p → q ∈ N.route c p)
    {tiers : List (Config C P → C → P → C × P → Bool)} {t : Config C P → C → P → C × P → Bool}
    (ht : t ∈ tiers) (hnon : ∀ f c p q, ¬ src c → q ∈ R₁ c p → t f c p q = true)
    (hsrc : ∀ f c p q, src c → (∀ c', ¬ src c' → f c' = none) → q ∈ R₁ c p → t f c p q = true) :
    N.SourceSel R₁ src (N.tieredSel tiers) :=
  ⟨fun _ _ _ _ h => (N.mem_tieredSel h).1,
    fun f c p hs _ ⟨q, hq, hfree⟩ =>
      N.tieredSel_conserving ht (hR c p q hq) hfree (hnon f c p q hs hq),
    fun f c p hs _ he ⟨q, hq, hfree⟩ =>
      N.tieredSel_conserving ht (hR c p q hq) hfree (hsrc f c p q hs he hq)⟩

end Choice

/-! ### Deadlock freedom is a property of one configuration -/

section Deadlock

variable [DecidableEq C] (N : Network C P)

/-- **Every non-empty configuration of legal packets can move** under every selection
satisfying Duato's condition with throttled sources on the legal pairs.  The configuration need
not be reachable under that selection: it may have been reached under other selections. -/
theorem movable_of_sourceSelOn {legal : C → P → Prop} {R₁ : C → P → List (C × P)}
    {src : C → Prop} {sel : Selection C P} (hsel : N.SourceSelOn legal R₁ src sel)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    {f : Config C P} (hf : Legal legal f) (hne : f ≠ empty) : N.Movable sel f := by
  have key : ∀ c, (¬ src c ∨ ∀ c', ¬ src c' → f c' = none) → ∀ p, f c = some p →
      N.Movable sel f := by
    intro c
    refine hwf.induction (C := fun c => (¬ src c ∨ ∀ c', ¬ src c' → f c' = none) →
      ∀ p, f c = some p → N.Movable sel f) c ?_
    intro c ih hc p hp
    have hl := hf c p hp
    cases harr : N.arrived c p with
    | true => exact ⟨.eject c, _, rfl, StepWith.eject hp harr⟩
    | false =>
      obtain ⟨⟨c', p'⟩, hq⟩ := List.exists_mem_of_ne_nil _ (hconn c p hl harr)
      cases hc' : f c' with
      | none =>
        have hfree : ∃ q ∈ R₁ c p, f q.1 = none := ⟨(c', p'), hq, hc'⟩
        have hoff : ∃ q ∈ sel f c p, f q.1 = none := by
          by_cases hs : src c
          · exact hsel.source f c p hl harr hs hp (hc.resolve_left (not_not.2 hs)) hfree
          · exact hsel.conserving f c p hl harr hs hp hfree
        obtain ⟨⟨c'', p''⟩, hq', hfree'⟩ := hoff
        exact ⟨.hop c c'' p'', _, rfl, StepWith.hop hp harr hq' hfree'⟩
      | some p'' => exact ih c' ⟨p, p', hl, harr, hq⟩ (Or.inl (hR₁ c p _ hl harr hq)) p'' hc'
  by_cases h : ∃ c p, ¬ src c ∧ f c = some p
  · obtain ⟨c, p, hs, hp⟩ := h
    exact key c (Or.inl hs) p hp
  · obtain ⟨c, p, hp⟩ := exists_of_ne_empty hne
    refine key c (Or.inr fun c' hc' => ?_) p hp
    cases h' : f c' with
    | none => rfl
    | some p' => exact absurd ⟨c', p', hc', h'⟩ h

variable {N}

/-- The target of a step is determined by its source and its action, whatever the selection. -/
theorem StepWith.target_eq {sel sel' : Selection C P} {f f₁ f₂ : Config C P} {a : Act C P}
    (h₁ : N.StepWith sel f a f₁) (h₂ : N.StepWith sel' f a f₂) : f₁ = f₂ := by
  cases h₁ <;> cases h₂ <;> rfl

end Deadlock

/-! ### The union of the admissible selections -/

section Union

variable (N : Network C P)

/-- The **union of the selections satisfying `ok`**, restricted to the permitted hops: every hop
some admissible selection offers. -/
noncomputable def unionSel (ok : Selection C P → Prop) : Selection C P := by
  classical exact fun f c p => (N.route c p).filter fun q => ∃ σ, ok σ ∧ q ∈ σ f c p

theorem mem_unionSel {ok : Selection C P → Prop} {f : Config C P} {c : C} {p : P}
    {q : C × P} : q ∈ N.unionSel ok f c p ↔ q ∈ N.route c p ∧ ∃ σ, ok σ ∧ q ∈ σ f c p := by
  classical
  simp only [unionSel, List.mem_filter, decide_eq_true_eq]

theorem unionSel_sub (ok : Selection C P → Prop) :
    ∀ f c p q, q ∈ N.unionSel ok f c p → q ∈ N.route c p :=
  fun _ _ _ _ h => ((N.mem_unionSel).1 h).1

variable {N} [DecidableEq C]

/-- A step under an admissible selection is a step under the union. -/
theorem StepWith.to_union {ok : Selection C P → Prop} {σ : Selection C P} (hσ : ok σ)
    (hsub : ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p) {f f' : Config C P} {a : Act C P}
    (h : N.StepWith σ f a f') : N.StepWith (N.unionSel ok) f a f' := by
  cases h with
  | inject h₁ h₂ => exact .inject h₁ h₂
  | hop h₁ h₂ h₃ h₄ =>
    exact .hop h₁ h₂ ((N.mem_unionSel).2 ⟨hsub _ _ _ _ h₃, σ, hσ, h₃⟩) h₄
  | eject h₁ h₂ => exact .eject h₁ h₂

end Union

/-! ### Runs under a time-varying selection -/

section Runs

variable [DecidableEq C] (N : Network C P)

/-- A **run under a time-varying selection**: the selection `sel n` used at step `n` is chosen
arbitrarily (by a history, a learner, a controller, an adversary) among the selections
satisfying `ok`.  Injections are arbitrary. -/
structure SelRun (ok : Selection C P → Prop) where
  /-- The `n`-th configuration. -/
  st : ℕ → Config C P
  /-- The `n`-th action. -/
  lab : ℕ → Act C P
  /-- The selection used at step `n`. -/
  sel : ℕ → Selection C P
  start : st 0 = empty
  sel_ok : ∀ n, ok (sel n)
  step : ∀ n, N.StepWith (sel n) (st n) (lab n) (st (n + 1))

variable {N}

namespace SelRun

variable {ok : Selection C P → Prop} (r : N.SelRun ok)

/-- The run, as a run of the network under the union of the admissible selections. -/
noncomputable def toRun (hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p) :
    (N.ltsWith (N.unionSel ok)).Run empty where
  st := r.st
  lab := r.lab
  start := r.start
  step n := StepWith.to_union (r.sel_ok n) (hsub _ (r.sel_ok n)) (r.step n)

/-- **Fairness of the channels, relative to the selection in force**: for every channel `c`, if
infinitely often a hop out of `c` or the ejection from `c` is enabled under the selection used
at that step, then infinitely often one is taken. -/
def ChannelFair : Prop :=
  ∀ c, LTS.InfOften (fun n => ∃ a f', Leaves c a ∧ N.StepWith (r.sel n) (r.st n) a f') →
    LTS.InfOften (fun n => Leaves c (r.lab n))

/-- **Strong fairness of the moves, relative to the selection in force**: if infinitely often
the run is at `f` with the move `a` (a hop or an ejection) to `f'` enabled under the selection
used at that step, then infinitely often it takes `a` from `f` to `f'`. -/
def StronglyFair : Prop :=
  ∀ f a f', a.IsMove → LTS.InfOften (fun n => r.st n = f ∧ N.StepWith (r.sel n) f a f') →
    LTS.InfOften (fun n => r.st n = f ∧ r.lab n = a ∧ r.st (n + 1) = f')

/-- The packet in channel `c` at time `n` is eventually ejected (as `Network.Delivered`). -/
inductive Delivered : ℕ → C → Prop
  | eject {n : ℕ} {c : C} : r.lab n = .eject c → Delivered n c
  | hop {n : ℕ} {c c' : C} {p' : P} : r.lab n = .hop c c' p' → Delivered (n + 1) c' →
      Delivered n c
  | wait {n : ℕ} {c : C} : r.lab n ≠ .eject c → (∀ c' p', r.lab n ≠ .hop c c' p') →
      Delivered (n + 1) c → Delivered n c

variable {r}

theorem delivered_of_toRun {hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p}
    {n : ℕ} {c : C} (h : N.Delivered (r.toRun hsub) n c) : r.Delivered n c := by
  induction h with
  | eject h => exact .eject h
  | hop h _ ih => exact .hop h ih
  | wait h₁ h₂ _ ih => exact .wait h₁ h₂ ih

variable (r)

/-- A packet that never leaves `c` after time `n` stays in `c`. -/
theorem stay_of_not_leave {n : ℕ} {c : C} {p : P} (hp : r.st n c = some p)
    (hne : ∀ m, n ≤ m → ¬ Leaves c (r.lab m)) : ∀ m, n ≤ m → r.st m c = some p := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => exact hp
  | succ d ih => exact stay_of_step (r.step (n + d)) (ih (by omega)) (hne _ (by omega))

/-- Every configuration of the run is legal. -/
theorem legal {legal : C → P → Prop} (hcl : N.Closed legal)
    (hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p) (n : ℕ) :
    Legal legal (r.st n) :=
  N.legal_of_reachable_sub hcl (N.unionSel_sub ok) ((r.toRun hsub).reachable n)

/-- **Every hop of the run is a routing step** of the packet that moves, from a legal pair: the
hop bounds of the routing function hold along every run. -/
theorem hop_packetStep {legal : C → P → Prop} (hcl : N.Closed legal)
    (hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p) {n : ℕ} {c c' : C} {p' : P}
    (h : r.lab n = .hop c c' p') :
    ∃ p, r.st n c = some p ∧ legal c p ∧ N.PacketStep (c, p) (c', p') := by
  have hst := r.step n
  rw [h] at hst
  generalize r.st (n + 1) = s' at hst
  cases hst with
  | hop hp harr hq _ =>
    exact ⟨_, hp, r.legal hcl hsub n c _ hp, harr, hsub _ (r.sel_ok n) _ _ _ _ hq⟩

/-- A run under a constant selection. -/
def ofRun {sel : Selection C P} (r : (N.ltsWith sel).Run empty) : N.SelRun (· = sel) where
  st := r.st
  lab := r.lab
  sel _ := sel
  start := r.start
  sel_ok _ := rfl
  step := r.step

/-- For a constant selection, strong fairness implies strong fairness relative to the
selection in force. -/
theorem stronglyFair_ofRun {sel : Selection C P} {r : (N.ltsWith sel).Run empty}
    (h : r.StronglyFair) : (ofRun r).StronglyFair := by
  intro f a f' _ hen
  obtain ⟨n, -, -, hst⟩ := hen 0
  exact h f a f' (fun M => let ⟨n, hn, hs, _⟩ := hen M; ⟨n, hn, hs⟩) hst

/-- For a constant selection, channel fairness is channel fairness relative to the selection in
force. -/
theorem channelFair_ofRun {sel : Selection C P} {r : (N.ltsWith sel).Run empty} :
    Network.ChannelFair r ↔ (ofRun r).ChannelFair :=
  Iff.rfl

end SelRun

variable (N)

/-- The pigeonhole principle for "infinitely often": if infinitely often some element of a finite
set has a property, some element has it infinitely often. -/
theorem infOften_exists_of_finite {α : Type*} {A : Set α} (hA : A.Finite) {Q : α → ℕ → Prop}
    (h : LTS.InfOften fun n => ∃ a ∈ A, Q a n) : ∃ a ∈ A, LTS.InfOften (Q a) := by
  by_contra hc
  push Not at hc
  have hb : ∀ a ∈ A, ∃ M, ∀ n, M ≤ n → ¬ Q a n := by
    intro a ha
    have := hc a ha
    unfold LTS.InfOften at this
    push Not at this
    exact this
  choose! M hM using hb
  obtain ⟨n, hn, a, ha, hq⟩ := h (hA.toFinset.sup M)
  exact hM a ha n (le_trans (Finset.le_sup (hA.mem_toFinset.2 ha)) hn) hq

/-- The moves out of a legal configuration lie in a finite set of actions, when there are
finitely many legal pairs. -/
theorem moves_finite {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) :
    ∃ A : Set (Act C P), A.Finite ∧ ∀ (σ : Selection C P) f a f',
      (∀ f c p q, q ∈ σ f c p → q ∈ N.route c p) → Legal legal f → a.IsMove →
      N.StepWith σ f a f' → a ∈ A := by
  refine ⟨(fun x : (C × P) × (C × P) => Act.hop x.1.1 x.2.1 x.2.2) ''
      ({q : C × P | legal q.1 q.2} ×ˢ {q : C × P | legal q.1 q.2}) ∪
      (fun x : C × P => Act.eject x.1) '' {q : C × P | legal q.1 q.2},
    (((Set.Finite.prod hfin hfin).image _).union (hfin.image _)), ?_⟩
  intro σ f a f' hsub hf ha hst
  cases hst with
  | inject => simp [Act.IsMove] at ha
  | @hop c c' p p' hp harr hq _ =>
    exact Or.inl ⟨((c, p), (c', p')), ⟨hf c p hp, hcl.route c p _ (hf c p hp) harr
      (hsub _ _ _ _ hq)⟩, rfl⟩
  | @eject c p hp _ => exact Or.inr ⟨(c, p), hf c p hp, rfl⟩

variable {N}

/-! ### Delivery -/

/-- **No packet outside the sources waits for ever, under load and a time-varying selection.**
Along every run that is channel fair relative to the selection in force, whatever the
injections, every packet held in a channel outside the sources leaves it.  As
`Network.exists_leave_of_channelFair`: the escape channel is free infinitely often, and whenever
it is free the selection in force at that step offers a free hop. -/
theorem SelRun.exists_leave_of_channelFair {legal : C → P → Prop} (hcl : N.Closed legal)
    {R₁ : C → P → List (C × P)} {src : C → Prop} {ok : Selection C P → Prop}
    (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (r : N.SelRun ok) (hfair : r.ChannelFair) :
    ∀ c, ¬ src c → ∀ n p, r.st n c = some p → ∃ m, n ≤ m ∧ Leaves c (r.lab m) := by
  have hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p := fun σ h => (hok σ h).sub
  intro c
  refine hwf.induction (C := fun c => ¬ src c → ∀ n p, r.st n c = some p →
    ∃ m, n ≤ m ∧ Leaves c (r.lab m)) c ?_
  intro c ih hsc n p hp
  by_contra hne
  push Not at hne
  have hstay := r.stay_of_not_leave hp hne
  suffices hen : LTS.InfOften
      (fun m => ∃ a f', Leaves c a ∧ N.StepWith (r.sel m) (r.st m) a f') by
    obtain ⟨m, hm, hl⟩ := hfair c hen n
    exact hne m hm hl
  have hl : legal c p := r.legal hcl hsub n c p hp
  cases harr : N.arrived c p with
  | true =>
    intro M
    exact ⟨max M n, le_max_left _ _, .eject c, _, rfl,
      StepWith.eject (hstay _ (le_max_right _ _)) harr⟩
  | false =>
    obtain ⟨⟨c', p'⟩, hq⟩ := List.exists_mem_of_ne_nil _ (hconn c p hl harr)
    have hsc' : ¬ src c' := hR₁ c p _ hl harr hq
    have hfree : ∀ M, ∃ m, M ≤ m ∧ n ≤ m ∧ r.st m c' = none := by
      intro M
      cases h' : r.st (max M n) c' with
      | none => exact ⟨max M n, le_max_left _ _, le_max_right _ _, h'⟩
      | some p'' =>
        obtain ⟨m, hm, hlm⟩ := ih c' ⟨p, p', hl, harr, hq⟩ hsc' _ p'' h'
        exact ⟨m + 1, by omega, by omega, leaves_free (r.step m) hlm⟩
    intro M
    obtain ⟨m, hMm, hnm, hm⟩ := hfree M
    have hpm := hstay m hnm
    obtain ⟨⟨c'', p''⟩, hq', hfree'⟩ := (hok _ (r.sel_ok m)).conserving (r.st m) c p hl harr hsc
      hpm ⟨(c', p'), hq, hm⟩
    exact ⟨m, hMm, .hop c c'' p'', _, rfl, StepWith.hop hpm harr hq' hfree'⟩

/-- **Delivery under load with a time-varying selection.**  With a closed legal set, a connected
escape subfunction `R₁` with a well-founded dependency graph and no escape hop into a source, no
hop at all into a source, a ranking function decreasing on every hop, and every admissible
selection satisfying `SourceSelOn legal R₁ src`: along every run that is channel fair relative to
the selection in force, with injections going on for ever, every packet held in a channel
outside the sources is delivered.  No finiteness is assumed. -/
theorem SelRun.delivered_of_channelFair {legal : C → P → Prop} (hcl : N.Closed legal)
    {R₁ : C → P → List (C × P)} {src : C → Prop} {ok : Selection C P → Prop}
    (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (hsrc : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (r : N.SelRun ok) (hfair : r.ChannelFair) :
    ∀ n c, ¬ src c → r.st n c ≠ none → r.Delivered n c := by
  have hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p := fun σ h => (hok σ h).sub
  intro n c hs hc
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hc
  exact SelRun.delivered_of_toRun (N.delivered_of_leave_rank hcl rk hrk hsrc (N.unionSel_sub ok)
    (r.toRun hsub) (r.exists_leave_of_channelFair hcl hok hconn hwf hR₁ hfair) n c p hs hp)

/-- **No packet waits for ever along a strongly fair run with a time-varying selection**, those
held back at a source included.  From a configuration that recurs, deadlock freedom of the
selection in force gives a move at each visit; there are finitely many moves, so one is enabled
infinitely often and (by strong fairness relative to the selection in force) taken infinitely
often; its target recurs.  The moves are well-founded (livelock freedom of the union of the
admissible selections), so following them the packet must leave its channel. -/
theorem SelRun.exists_leave_of_stronglyFair {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) {R₁ : C → P → List (C × P)} {src : C → Prop}
    {ok : Selection C P → Prop} (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (r : N.SelRun ok) (hfair : r.StronglyFair) :
    ∀ n c p, r.st n c = some p → ∃ m, n ≤ m ∧ Leaves c (r.lab m) := by
  have hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p := fun σ h => (hok σ h).sub
  intro n c p hp
  by_contra hne
  push Not at hne
  have hstay := r.stay_of_not_leave hp hne
  let R := r.toRun hsub
  have hchan : {c | ∃ p, legal c p}.Finite :=
    (hfin.image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩
  have hL : N.LivelockFreeWith (N.unionSel ok) :=
    N.livelockFreeWith_of_ranking hcl hchan rk hrk (N.unionSel_sub ok)
  obtain ⟨A, hA, hmemA⟩ := N.moves_finite hcl hfin
  have key : ∀ s, Acc ((N.ltsWith (N.unionSel ok)).IRel Act.IsMove) s →
      LTS.InfOften (fun m => r.st m = s) → False := by
    intro s hacc
    induction hacc with
    | intro s _ ih =>
      intro hs
      obtain ⟨m₀, hm₀, hsm₀⟩ := hs n
      have hsc : s c = some p := hsm₀ ▸ hstay m₀ hm₀
      have hne' : s ≠ empty := fun h => by simp [h, empty] at hsc
      have hen : LTS.InfOften (fun m => ∃ a ∈ A, r.st m = s ∧
          ∃ f', a.IsMove ∧ N.StepWith (r.sel m) s a f') := by
        intro M
        obtain ⟨m, hm, hsm⟩ := hs M
        obtain ⟨a, f', ha, hst⟩ := N.movable_of_sourceSelOn (hok _ (r.sel_ok m)) hconn hwf hR₁
          (r.legal hcl hsub m) (hsm ▸ hne')
        refine ⟨m, hm, a, hmemA _ _ _ _ (hsub _ (r.sel_ok m)) (r.legal hcl hsub m) ha hst, hsm,
          f', ha, hsm ▸ hst⟩
      obtain ⟨a, -, ha⟩ := infOften_exists_of_finite hA hen
      obtain ⟨m₁, -, -, f₁, hmv, hst₁⟩ := ha 0
      have ha' : LTS.InfOften (fun m => r.st m = s ∧ N.StepWith (r.sel m) s a f₁) := by
        intro M
        obtain ⟨m, hm, hsm, f', -, hst⟩ := ha M
        exact ⟨m, hm, hsm, StepWith.target_eq hst hst₁ ▸ hst⟩
      have htaken := hfair s a f₁ hmv ha'
      by_cases hl : Leaves c a
      · obtain ⟨m, hm, -, hlab, -⟩ := htaken n
        exact hne m hm (hlab ▸ hl)
      · refine ih f₁ ⟨a, hmv, StepWith.to_union (r.sel_ok m₁) (hsub _ (r.sel_ok m₁)) hst₁⟩ ?_
        intro M
        obtain ⟨m, hm, -, -, h⟩ := htaken M
        exact ⟨m + 1, by omega, h⟩
  obtain ⟨s, hs⟩ := R.exists_infOften (N.reachable_finite hcl hfin (N.unionSel_sub ok))
  obtain ⟨m, -, rfl⟩ := hs 0
  exact key _ (hL.acc (R.reachable m)) hs

/-- **Starvation freedom with a time-varying selection.**  With finitely many legal pairs, Duato's
condition with throttled sources on the legal pairs for every admissible selection and a ranking
function, every packet of every run that is strongly fair relative to the selection in force is
delivered, packets held back at a source included. -/
theorem SelRun.delivered_of_stronglyFair {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) {R₁ : C → P → List (C × P)} {src : C → Prop}
    {ok : Selection C P → Prop} (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (r : N.SelRun ok) (hfair : r.StronglyFair) :
    ∀ n c, r.st n c ≠ none → r.Delivered n c := by
  have hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p := fun σ h => (hok σ h).sub
  intro n c hc
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hc
  exact SelRun.delivered_of_toRun (N.delivered_of_leave_rank hcl rk hrk (src := fun _ => False)
    (fun _ _ _ _ _ _ h => h) (N.unionSel_sub ok) (r.toRun hsub)
    (fun c _ n p hp => r.exists_leave_of_stronglyFair hcl hfin hok hconn hwf hR₁ rk hrk hfair n c p
      hp) n c p not_false hp)

/-- **Livelock freedom with a time-varying selection**: every run injects infinitely often (no
run consists of moves only from some point on). -/
theorem SelRun.infOften_not_move {legal : C → P → Prop} (hcl : N.Closed legal)
    (hchan : {c | ∃ p, legal c p}.Finite) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {ok : Selection C P → Prop} (hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p)
    (r : N.SelRun ok) : LTS.InfOften (fun n => ¬ (r.lab n).IsMove) :=
  (r.toRun hsub).infOften_external_of_livelockFree
    (N.livelockFreeWith_of_ranking hcl hchan rk hrk (N.unionSel_sub ok))

end Runs

/-! ### Strategies with a state -/

/-- A **history-dependent routing strategy** with state `H` (the history, or anything computed
from it: link prices, learned latencies, recent destinations, controller state, a snapshot of the
network, a random generator).  In state `h` it routes with the selection `sel h`, lets the sources
inject the packets `admit h` allows, and after a step `f —a→ f'` moves to `update h f a f'`. -/
structure Strategy (C P H : Type*) where
  /-- The initial state. -/
  init : H
  /-- The selection used in each state. -/
  sel : H → Selection C P
  /-- The injections allowed in each state (for example, only the intermediate the source chose
  by link prices or learned latencies). -/
  admit : H → C → P → Prop
  /-- The new state after a step. -/
  update : H → Config C P → Act C P → Config C P → H

namespace Strategy

variable {H : Type*}

/-- The selections a strategy may use. -/
def Uses (σ : Strategy C P H) (sel : Selection C P) : Prop := ∃ h, σ.sel h = sel

end Strategy

section Strategies

variable [DecidableEq C] (N : Network C P) {H : Type*}

/-- The network under the strategy `σ`, as a transition system on (configuration, state). -/
def stratLTS (σ : Strategy C P H) : LTS (Config C P × H) (Act C P) where
  step s a s' := N.StepWith (σ.sel s.2) s.1 a s'.1 ∧ (∀ c p, a = .inject c p → σ.admit s.2 c p) ∧
    s'.2 = σ.update s.2 s.1 a s'.1

variable {N}

namespace Strategy

variable {σ : Strategy C P H}

/-- A run of the strategy, as a run under a time-varying selection (forgetting the state). -/
def toSelRun (r : (N.stratLTS σ).Run (empty, σ.init)) : N.SelRun σ.Uses where
  st n := (r.st n).1
  lab := r.lab
  sel n := σ.sel (r.st n).2
  start := by rw [r.start]
  sel_ok n := ⟨_, rfl⟩
  step n := (r.step n).1

/-- The configurations reachable under the strategy are reachable under the union of the
selections it uses. -/
theorem reachable_union (hsub : ∀ h f c p q, q ∈ σ.sel h f c p → q ∈ N.route c p)
    {s : Config C P × H} (h : (N.stratLTS σ).Reachable (empty, σ.init) s) :
    (N.ltsWith (N.unionSel σ.Uses)).Reachable empty s.1 := by
  induction h with
  | refl => exact LTS.Reachable.refl _
  | tail _ hst ih =>
    obtain ⟨a, ha, -, -⟩ := hst
    exact ih.tail ⟨a, StepWith.to_union ⟨_, rfl⟩ (hsub _) ha⟩

/-- **Deadlock freedom of a strategy**: in every reachable state `(f, h)` with `f` non-empty, some
packet can move under the selection `sel h` the strategy uses there. -/
theorem movable {legal : C → P → Prop} (hcl : N.Closed legal) {R₁ : C → P → List (C × P)}
    {src : C → Prop} (hσ : ∀ h, N.SourceSelOn legal R₁ src (σ.sel h))
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    {f : Config C P} {h : H} (hr : (N.stratLTS σ).Reachable (empty, σ.init) (f, h))
    (hne : f ≠ empty) :
    ∃ a f', a.IsMove ∧ (N.stratLTS σ).step (f, h) a (f', σ.update h f a f') := by
  have hl : Legal legal f := N.legal_of_reachable_sub hcl (N.unionSel_sub _)
    (reachable_union (fun h => (hσ h).sub) hr)
  obtain ⟨a, f', ha, hst⟩ := N.movable_of_sourceSelOn (hσ h) hconn hwf hR₁ hl hne
  refine ⟨a, f', ha, hst, fun c p he => ?_, rfl⟩
  subst he
  simp [Act.IsMove] at ha

/-- **Livelock freedom of a strategy**: no reachable state admits an infinite run of moves. -/
theorem livelockFree {legal : C → P → Prop} (hcl : N.Closed legal)
    (hchan : {c | ∃ p, legal c p}.Finite) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (hsub : ∀ h f c p q, q ∈ σ.sel h f c p → q ∈ N.route c p) :
    (N.stratLTS σ).LivelockFree Act.IsMove (empty, σ.init) := by
  intro s hs ⟨g, hg0, hg⟩
  refine N.livelockFreeWith_of_ranking hcl hchan rk hrk (N.unionSel_sub σ.Uses) s.1
    (reachable_union hsub hs) ⟨fun n => (g n).1, congrArg Prod.fst hg0, fun n => ?_⟩
  obtain ⟨a, ha, hst, -, -⟩ := hg n
  exact ⟨a, ha, StepWith.to_union ⟨_, rfl⟩ (hsub _) hst⟩

end Strategy

variable (N) in
/-- **The safety guarantees of a strategy** `σ` with throttled sources `src`: deadlock freedom
(in every reachable state some packet can move under the selection in force), livelock freedom,
delivery of every packet outside the sources along every run that is channel fair relative to
the selection in force (injections going on for ever), and delivery of every packet along every
run that is strongly fair relative to the selection in force. -/
structure StrategySafe (σ : Strategy C P H) (src : C → Prop) : Prop where
  deadlock : ∀ f h, (N.stratLTS σ).Reachable (empty, σ.init) (f, h) → f ≠ empty →
    ∃ a f', a.IsMove ∧ (N.stratLTS σ).step (f, h) a (f', σ.update h f a f')
  livelock : (N.stratLTS σ).LivelockFree Act.IsMove (empty, σ.init)
  underLoad : ∀ r : (N.stratLTS σ).Run (empty, σ.init), (Strategy.toSelRun r).ChannelFair →
    ∀ n c, ¬ src c → (r.st n).1 c ≠ none → (Strategy.toSelRun r).Delivered n c
  starvation : ∀ r : (N.stratLTS σ).Run (empty, σ.init), (Strategy.toSelRun r).StronglyFair →
    ∀ n c, (r.st n).1 c ≠ none → (Strategy.toSelRun r).Delivered n c

/-- **History-dependent strategies are safe** when every selection they use is: with a closed
legal set with finitely many pairs, a connected escape subfunction `R₁` with a well-founded
dependency graph and no escape hop into a source, no hop into a source, a ranking function
decreasing on every hop, and `SourceSelOn legal R₁ src (σ.sel h)` in every state `h`, the
strategy is deadlock free, livelock free, delivers every packet outside the sources under
sustained load (channel fairness relative to the selection in force) and every packet under
strong fairness relative to the selection in force. -/
theorem Strategy.safe {σ : Strategy C P H} {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) (R₁ : C → P → List (C × P)) {src : C → Prop}
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (hsrc : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (hσ : ∀ h, N.SourceSelOn legal R₁ src (σ.sel h)) : N.StrategySafe σ src := by
  have hok : ∀ s, σ.Uses s → N.SourceSelOn legal R₁ src s := by
    rintro _ ⟨h, rfl⟩; exact hσ h
  have hchan : {c | ∃ p, legal c p}.Finite :=
    (hfin.image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩
  exact ⟨fun _ _ hr hne => Strategy.movable hcl hσ hconn hwf hR₁ hr hne,
    Strategy.livelockFree hcl hchan rk hrk fun h => (hσ h).sub,
    fun r hfair => SelRun.delivered_of_channelFair hcl hok hconn hwf hR₁ hsrc rk hrk _ hfair,
    fun r hfair => SelRun.delivered_of_stronglyFair hcl hfin hok hconn hwf hR₁ rk hrk _ hfair⟩

end Strategies

end Network

end AsyncLean
