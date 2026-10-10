/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Strategy
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Clock cycles: the move models of the simulators

The theorems of `AsyncLean.Routing.Basic` and `AsyncLean.Routing.Strategy` are about the
step-by-step semantics: one packet moves at a time.  The simulators (`scripts/xp_arbiter.py`)
advance in clock cycles: ejection of the arrived packets at the start of a cycle, a move phase,
the injections at its end.  Two move models are formalised:

* `Network.SeqCycle` (`chain = seq`): the hops of the move phase happen one after another, each a
  single step under the selection in force in the configuration reached so far (a hop may enter
  a channel vacated earlier in the cycle); no packet moves twice.  It is a sequence of single
  steps by definition (`SeqCycle.path`).
* `Network.NoChainCycle` (`chain = none`): the hops happen **simultaneously**, each into a channel
  free at the start of the move phase, at most one hop out of and into each channel, each offered
  by the selection evaluated on the configuration the arbiter reads for that packet (the start of
  the move phase — `Cycle.ReadsStart` — or that plus the claims made earlier in the cycle, as the
  simulator's ghosts).  The effect is `simulApply`, defined channel by channel.

## Simultaneous moves are sequences of single steps

* `StepWith.after` : two enabled actions with distinct sources and targets commute (a target free
  at the start is not the source of any move).
* `path_simul`, `simulApply_perm` : simultaneous actions, performed one after another in any
  order, form a path of the step-by-step semantics ending at their simultaneous effect.
* `NoChainCycle.path_freeze` : a no-chaining cycle reading the start of the move phase is a path
  under one selection, `sel` frozen at that configuration (`freeze`); `NoChainCycle.path` : every
  no-chaining cycle is a path of the fully adaptive network (`route`).  Hence both models are
  `Network.Sequential` (`noChain_sequential`, `seq_sequential`).

## What transfers to runs of cycles (`Network.CycleRun`, a time-varying selection)

For every sequential cycle model (both models), with a closed legal set:

* `CycleRun.legal`, `CycleRun.hop_packetStep` : every configuration is legal and every hop is a
  routing step from a legal pair, so the hop bounds (`packet_hops_le`, the `detour_hops_le_*`
  theorems) hold for every packet;
* `WorkConserving.moves_pos` : **no deadlock** — a work-conserving cycle (every arrived packet is
  ejected; if nobody hops, the selection offered nobody a free hop) in a non-empty legal
  configuration moves a packet, under every selection satisfying `SourceSelOn`;
  `exists_noChainCycle` : some no-chaining cycle does;
* `CycleRun.pot_sum_le`, `CycleRun.card_moving_le`, `CycleRun.eventually_idle` : **no livelock**
  — without injections a cycle lowers the potential by its number of moves;
* `CycleRun.drain` : once injections stop, work-conserving cycles empty the network within
  `pot (r.st n)` cycles, bounded uniformly by `pot_le_bound` — no fairness needed;
* `CycleSafe`, `cycleSafe` : these, bundled, from the hypotheses of `Strategy.safe`.

Delivery while injections go on needs fairness, and the step-level fairness hypotheses do not
transfer as they stand:

* sequential model: its interleaving (`CycleRun.flatten`, `CycleRun.seqFlatten`) is a `SelRun`
  under the selections in force, so `seq_delivered_of_channelFair` and
  `seq_delivered_of_stronglyFair` are `SelRun.delivered_of_channelFair` and
  `SelRun.delivered_of_stronglyFair` verbatim, **assuming fairness of the interleaving**;
* no-chaining model: its interleaving is a run under frozen selections, which are not
  work conserving in the intermediate configurations (they may offer a hop into a channel
  claimed earlier in the cycle and decline one vacated in it), so `SourceSelOn` fails for them.
  Two statements are proved instead: `CycleRun.delivered_of_channelFair` under **cycle-level
  channel fairness** (`CycleRun.ChannelFair`: a channel whose packet may leave in infinitely many
  cycles — it has arrived, or the selection offers it a hop free at the start of the move
  phase — sees a departure in infinitely many cycles), with the extra hypothesis that no escape
  hop leads into an injection channel; and `noChain_delivered_of_interleaving` under channel
  fairness of the interleaving relative to the fully adaptive selection (a stronger hypothesis).

## The injection limit

In the packet model a channel holds one packet and the injections come at the end of a cycle, so:

* `CycleRun.count_inject_le_one`, `CycleRun.sum_count_inject_le` : at most one injection per
  channel and per cycle — a node (its injection channel) injects at most `T` packets in `T`
  cycles, in either cycle model, for every network, selection and strategy;
* `occ_path`, `CycleRun.occ_add_ejects` : packets are conserved;
* `CycleRun.sum_ejects_le`, `CycleRun.sum_ejects_le_start`, `CycleRun.throughput_le` : the
  packets delivered in `K` cycles are at most `I.card * K` from the empty network (`I` the
  injection channels), at most `occ + I.card * K` from any cycle: the long-run accepted throughput
  is at most one packet per injection channel and per cycle.  A scheme that achieves it (as
  dimension-order routing and our schemes do under neighbour traffic in the simulations) is
  optimal; `AsyncLean.Examples.Cycle` shows the bound is attained.

## What is not covered

The `full` model of the simulator (ordered passes repeated until nobody moves) is not treated
separately: its moves are single steps under the selection in force and no packet moves twice
in a cycle, so its cycles are cycles of `SeqCycle`.  Cycle-level
fairness, work conservation and fairness of the interleaving are hypotheses on the arbiter, not
derived from it.  Packets held at a throttled source are only covered by the strongly fair
statement of the sequential model.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*}

/-! ### Actions as functions -/

/-- The channel an action vacates. -/
def Act.src : Act C P → Option C
  | .inject _ _ => none
  | .hop c _ _ => some c
  | .eject c => some c

/-- The channel an action fills. -/
def Act.tgt : Act C P → Option C
  | .inject c _ => some c
  | .hop _ c' _ => some c'
  | .eject _ => none

/-- The content an action puts into the channel it fills. -/
def Act.put : Act C P → Option P
  | .inject _ p => some p
  | .hop _ _ p' => some p'
  | .eject _ => none

section Apply

variable [DecidableEq C]

/-- The effect of an action on a configuration. -/
def Act.apply : Act C P → Config C P → Config C P
  | .inject c p, f => Function.update f c (some p)
  | .hop c c' p', f => Function.update (Function.update f c none) c' (some p')
  | .eject c, f => Function.update f c none

theorem Act.apply_tgt {a : Act C P} {x : C} (h : a.tgt = some x) (f : Config C P) :
    a.apply f x = a.put := by
  cases a <;> simp_all [Act.tgt, Act.apply, Act.put]

theorem Act.apply_src {a : Act C P} {x : C} (h : a.src = some x) (h' : a.tgt ≠ some x)
    (f : Config C P) : a.apply f x = none := by
  cases a with
  | inject => simp [Act.src] at h
  | hop c c' p' =>
    simp only [Act.src, Option.some.injEq] at h
    simp only [Act.tgt, ne_eq, Option.some.injEq] at h'
    subst h
    simp [Act.apply, Function.update_of_ne (Ne.symm h')]
  | eject c =>
    simp only [Act.src, Option.some.injEq] at h
    subst h
    simp [Act.apply]

theorem Act.apply_other {a : Act C P} {x : C} (h : a.src ≠ some x) (h' : a.tgt ≠ some x)
    (f : Config C P) : a.apply f x = f x := by
  cases a with
  | inject c p =>
    simp only [Act.tgt, ne_eq, Option.some.injEq] at h'
    simp [Act.apply, Function.update_of_ne (Ne.symm h')]
  | hop c c' p' =>
    simp only [Act.src, ne_eq, Option.some.injEq] at h
    simp only [Act.tgt, ne_eq, Option.some.injEq] at h'
    simp [Act.apply, Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h')]
  | eject c =>
    simp only [Act.src, ne_eq, Option.some.injEq] at h
    simp [Act.apply, Function.update_of_ne (Ne.symm h)]

variable {N : Network C P}

/-- The target of a step is the effect of its action. -/
theorem StepWith.eq_apply {sel : Selection C P} {f f' : Config C P} {a : Act C P}
    (h : N.StepWith sel f a f') : f' = a.apply f := by
  cases h <;> rfl

/-- An enabled action vacates an occupied channel. -/
theorem StepWith.src_some {sel : Selection C P} {f : Config C P} {a : Act C P}
    (h : N.StepWith sel f a (a.apply f)) {x : C} (hx : a.src = some x) : f x ≠ none := by
  cases h with
  | inject => simp [Act.src] at hx
  | hop hp => simp only [Act.src, Option.some.injEq] at hx; subst hx; simp [hp]
  | eject hp => simp only [Act.src, Option.some.injEq] at hx; subst hx; simp [hp]

/-- An enabled action fills a free channel. -/
theorem StepWith.tgt_none {sel : Selection C P} {f : Config C P} {a : Act C P}
    (h : N.StepWith sel f a (a.apply f)) {x : C} (hx : a.tgt = some x) : f x = none := by
  cases h with
  | inject _ hfree => simp only [Act.tgt, Option.some.injEq] at hx; subst hx; exact hfree
  | hop _ _ _ hfree => simp only [Act.tgt, Option.some.injEq] at hx; subst hx; exact hfree
  | eject => simp [Act.tgt] at hx

/-- **Two enabled actions with distinct sources and distinct targets commute**: under a
selection that does not read the configuration, the second is still enabled after the first.
A target free at the start is not the source of either action. -/
theorem StepWith.after {S : Selection C P} (hS : ∀ g g', S g = S g') {h : Config C P}
    {a b : Act C P} (ha : N.StepWith S h a (a.apply h)) (hb : N.StepWith S h b (b.apply h))
    (hsrc : ∀ x, a.src = some x → b.src ≠ some x) (htgt : ∀ x, a.tgt = some x → b.tgt ≠ some x) :
    N.StepWith S (a.apply h) b (b.apply (a.apply h)) := by
  have hval : ∀ x, a.src ≠ some x → a.tgt ≠ some x → a.apply h x = h x :=
    fun x h₁ h₂ => Act.apply_other h₁ h₂ h
  -- the source of `b` and the target of `b` are untouched by `a`
  have hbs : ∀ x, b.src = some x → a.apply h x = h x := by
    intro x hx
    refine hval x (fun e => hsrc x e hx) (fun e => ?_)
    exact (hb.src_some hx) (ha.tgt_none e)
  have hbt : ∀ x, b.tgt = some x → a.apply h x = h x := by
    intro x hx
    refine hval x (fun e => (ha.src_some e) (hb.tgt_none hx)) (fun e => htgt x e hx)
  cases hb with
  | @inject c p hc hfree =>
    exact StepWith.inject hc (by rw [hbt c rfl]; exact hfree)
  | @hop c c' p p' hp harr hq hfree =>
    have e1 := hbs c rfl
    have e2 := hbt c' rfl
    refine StepWith.hop (by rw [e1]; exact hp) harr (by rw [hS (a.apply h) h]; exact hq)
      (by rw [e2]; exact hfree)
  | @eject c p hp harr =>
    exact StepWith.eject (by rw [hbs c rfl]; exact hp) harr

/-! ### Simultaneous actions -/

/-- **The simultaneous effect** of a list of actions on `g`: a channel filled by one of them
receives its content, a channel vacated by one of them (and filled by none) is free, every other
channel keeps its content.  It is meaningful when the actions have distinct sources and distinct
targets and each is enabled in `g` (`path_simul`). -/
def simulApply (g : Config C P) (as : List (Act C P)) : Config C P := fun x =>
  match as.find? (fun a => decide (a.tgt = some x)) with
  | some a => a.put
  | none => if ∃ a ∈ as, a.src = some x then none else g x

@[simp] theorem simulApply_nil (g : Config C P) : simulApply g [] = g := by
  funext x; simp [simulApply]

theorem mem_filterMap_of {α β : Type*} {f : α → Option β} {l : List α} {a : α} {b : β}
    (ha : a ∈ l) (h : f a = some b) : b ∈ l.filterMap f :=
  List.mem_filterMap.2 ⟨a, ha, h⟩

/-- In a list whose images under `f` are distinct, an image determines the element. -/
theorem eq_of_nodup_filterMap {α β : Type*} {f : α → Option β} :
    ∀ {l : List α}, (l.filterMap f).Nodup → ∀ {a b : α} {x : β}, a ∈ l → b ∈ l →
      f a = some x → f b = some x → a = b
  | [], _, _, _, _, ha, _, _, _ => absurd ha List.not_mem_nil
  | c :: l, hnd, a, b, x, ha, hb, hfa, hfb => by
    rw [List.filterMap_cons] at hnd
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · rw [hfa] at hnd
      exact absurd (mem_filterMap_of hb' hfb) (List.nodup_cons.1 hnd).1
    · rw [hfb] at hnd
      exact absurd (mem_filterMap_of ha' hfa) (List.nodup_cons.1 hnd).1
    · cases hc : f c with
      | none => rw [hc] at hnd; exact eq_of_nodup_filterMap hnd ha' hb' hfa hfb
      | some y =>
        rw [hc] at hnd
        exact eq_of_nodup_filterMap (List.nodup_cons.1 hnd).2 ha' hb' hfa hfb

/-- The simultaneous effect on a channel touched by no action. -/
theorem simulApply_of_not {g : Config C P} {as : List (Act C P)} {x : C}
    (h : ∀ a ∈ as, a.src ≠ some x ∧ a.tgt ≠ some x) : simulApply g as x = g x := by
  have h1 : as.find? (fun a => decide (a.tgt = some x)) = none := by
    rw [List.find?_eq_none]
    intro a ha
    simpa using (h a ha).2
  have h2 : ¬ ∃ a ∈ as, a.src = some x := fun ⟨a, ha, he⟩ => (h a ha).1 he
  simp only [simulApply, h1, h2, ite_false]

/-- The simultaneous effect on the channel an action fills, when targets are distinct. -/
theorem simulApply_of_tgt {g : Config C P} {as : List (Act C P)} {a : Act C P} {x : C}
    (hnd : (as.filterMap Act.tgt).Nodup) (ha : a ∈ as) (hx : a.tgt = some x) :
    simulApply g as x = a.put := by
  obtain ⟨b, hb⟩ : ∃ b, as.find? (fun a => decide (a.tgt = some x)) = some b := by
    cases h : as.find? (fun a => decide (a.tgt = some x)) with
    | some b => exact ⟨b, rfl⟩
    | none =>
      rw [List.find?_eq_none] at h
      exact absurd (by simpa using hx) (h a ha)
  have hbx : b.tgt = some x := by simpa using List.find?_some hb
  have := eq_of_nodup_filterMap hnd ha (List.mem_of_find?_eq_some hb) hx hbx
  subst this
  simp only [simulApply, hb]

/-- The simultaneous effect on a channel an action vacates and none fills. -/
theorem simulApply_of_src {g : Config C P} {as : List (Act C P)} {a : Act C P} {x : C}
    (ha : a ∈ as) (hx : a.src = some x) (hn : ∀ b ∈ as, b.tgt ≠ some x) :
    simulApply g as x = none := by
  have h1 : as.find? (fun a => decide (a.tgt = some x)) = none := by
    rw [List.find?_eq_none]
    intro b hb
    simpa using hn b hb
  have h2 : ∃ a ∈ as, a.src = some x := ⟨a, ha, hx⟩
  simp only [simulApply, h1, h2, ite_true]

/-- **The simultaneous effect does not depend on the order of the actions** (when their targets
are distinct). -/
theorem simulApply_perm {g : Config C P} {as as' : List (Act C P)} (hp : as.Perm as')
    (hnd : (as.filterMap Act.tgt).Nodup) : simulApply g as = simulApply g as' := by
  have hnd' : (as'.filterMap Act.tgt).Nodup := (hp.filterMap _).nodup_iff.1 hnd
  funext x
  by_cases h : ∃ a ∈ as, a.tgt = some x
  · obtain ⟨a, ha, hx⟩ := h
    rw [simulApply_of_tgt hnd ha hx, simulApply_of_tgt hnd' (hp.mem_iff.1 ha) hx]
  · push Not at h
    have h1 : as.find? (fun a => decide (a.tgt = some x)) = none :=
      List.find?_eq_none.2 fun a ha => by simpa using h a ha
    have h2 : as'.find? (fun a => decide (a.tgt = some x)) = none :=
      List.find?_eq_none.2 fun a ha => by simpa using h a (hp.mem_iff.2 ha)
    have h3 : (∃ a ∈ as, a.src = some x) ↔ ∃ a ∈ as', a.src = some x :=
      ⟨fun ⟨a, ha, e⟩ => ⟨a, hp.mem_iff.1 ha, e⟩, fun ⟨a, ha, e⟩ => ⟨a, hp.mem_iff.2 ha, e⟩⟩
    simp only [simulApply, h1, h2, h3]

variable {N : Network C P}

/-- Peeling off the first of a list of simultaneous actions. -/
theorem simulApply_cons {S : Selection C P} {g : Config C P} {a : Act C P} {as : List (Act C P)}
    (ha : N.StepWith S g a (a.apply g)) (has : ∀ b ∈ as, N.StepWith S g b (b.apply g))
    (hsrc : ∀ x, a.src = some x → ∀ b ∈ as, b.src ≠ some x)
    (htgt : ∀ x, a.tgt = some x → ∀ b ∈ as, b.tgt ≠ some x) :
    simulApply g (a :: as) = simulApply (a.apply g) as := by
  funext x
  by_cases hax : a.tgt = some x
  · have h1 : (a :: as).find? (fun a => decide (a.tgt = some x)) = some a :=
      List.find?_cons_of_pos (by simpa using hax)
    rw [simulApply_of_not fun b hb =>
        ⟨fun e => (has b hb).src_some e (ha.tgt_none hax), htgt x hax b hb⟩,
      Act.apply_tgt hax]
    simp only [simulApply, h1]
  · have h1 : (a :: as).find? (fun a => decide (a.tgt = some x)) =
        as.find? (fun a => decide (a.tgt = some x)) :=
      List.find?_cons_of_neg (by simpa using hax)
    simp only [simulApply, h1]
    split
    · rfl
    · by_cases hsx : a.src = some x
      · have hn : ¬ ∃ b ∈ as, b.src = some x := fun ⟨b, hb, he⟩ => hsrc x hsx b hb he
        have hp : ∃ b ∈ a :: as, b.src = some x := ⟨a, List.mem_cons_self, hsx⟩
        simp only [hp, hn, ↓reduceIte, Act.apply_src hsx hax]
      · have he : (∃ b ∈ a :: as, b.src = some x) ↔ ∃ b ∈ as, b.src = some x := by
          simp only [List.mem_cons, exists_eq_or_imp, hsx, false_or]
        rw [Act.apply_other hsx hax]
        simp only [he]

/-- **Simultaneous actions are a sequence of single steps.**  If every action of `as` is enabled
in `h` under a selection `S` that does not read the configuration (the adaptive selection, or a
selection frozen at a snapshot: `freeze`), and the actions have distinct sources and distinct
targets, then performing them one after another, in the order of the list, is a path of the
network from `h` to their simultaneous effect.  Any order gives the same result. -/
theorem path_simul {S : Selection C P} (hS : ∀ g g', S g = S g') :
    ∀ {h : Config C P} {as : List (Act C P)}, (∀ a ∈ as, N.StepWith S h a (a.apply h)) →
      (as.filterMap Act.src).Nodup → (as.filterMap Act.tgt).Nodup →
      (N.ltsWith S).Path h as (simulApply h as)
  | h, [], _, _, _ => by rw [simulApply_nil]; exact LTS.Path.nil _
  | h, a :: as, hen, hs, ht => by
    have ha := hen a List.mem_cons_self
    have has : ∀ b ∈ as, N.StepWith S h b (b.apply h) :=
      fun b hb => hen b (List.mem_cons_of_mem _ hb)
    have hsrc : ∀ x, a.src = some x → ∀ b ∈ as, b.src ≠ some x := by
      intro x hx b hb he
      rw [List.filterMap_cons, hx] at hs
      exact (List.nodup_cons.1 hs).1 (mem_filterMap_of hb he)
    have htgt : ∀ x, a.tgt = some x → ∀ b ∈ as, b.tgt ≠ some x := by
      intro x hx b hb he
      rw [List.filterMap_cons, hx] at ht
      exact (List.nodup_cons.1 ht).1 (mem_filterMap_of hb he)
    have hs' : (as.filterMap Act.src).Nodup := by
      rw [List.filterMap_cons] at hs
      split at hs
      · exact hs
      · exact (List.nodup_cons.1 hs).2
    have ht' : (as.filterMap Act.tgt).Nodup := by
      rw [List.filterMap_cons] at ht
      split at ht
      · exact ht
      · exact (List.nodup_cons.1 ht).2
    rw [simulApply_cons ha has hsrc htgt]
    exact LTS.Path.cons ha (path_simul hS (fun b hb => StepWith.after hS ha (has b hb)
      (fun x hx => hsrc x hx b hb) (fun x hx => htgt x hx b hb)) hs' ht')

end Apply

/-! ### Clock cycles -/

/-- **The data of one clock cycle**: the channels whose arrived packets are ejected at its start,
the hops of its move phase (source channel, target channel, header carried on) and the injections
at its end (channel, header). -/
structure Cycle (C P : Type*) where
  /-- The channels whose packets are ejected at the start of the cycle. -/
  ejects : List C
  /-- The hops of the move phase: source channel, target channel, new header. -/
  hops : List (C × C × P)
  /-- The injections at the end of the cycle. -/
  injects : List (C × P)

namespace Cycle

/-- The ejections, as actions. -/
def ejActs (cy : Cycle C P) : List (Act C P) := cy.ejects.map .eject

/-- The hops, as actions. -/
def hopActs (cy : Cycle C P) : List (Act C P) := cy.hops.map fun m => .hop m.1 m.2.1 m.2.2

/-- The injections, as actions. -/
def injActs (cy : Cycle C P) : List (Act C P) := cy.injects.map fun q => .inject q.1 q.2

/-- The actions of the cycle, phase after phase. -/
def acts (cy : Cycle C P) : List (Act C P) := cy.ejActs ++ cy.hopActs ++ cy.injActs

/-- The number of packet moves (ejections and hops) of the cycle. -/
def moves (cy : Cycle C P) : ℕ := cy.ejects.length + cy.hops.length

/-- The packet held in `c` leaves it in the cycle (it is ejected or hops on). -/
def Leaves (cy : Cycle C P) (c : C) : Prop := c ∈ cy.ejects ∨ ∃ c' p', (c, c', p') ∈ cy.hops

/-- The configuration at the start of the move phase, after the ejections. -/
def mid [DecidableEq C] (cy : Cycle C P) (f : Config C P) : Config C P := simulApply f cy.ejActs

/-- The configuration at the end of a move phase without chaining. -/
def post [DecidableEq C] (cy : Cycle C P) (f : Config C P) : Config C P :=
  simulApply (cy.mid f) cy.hopActs

@[simp] theorem ejActs_src (cy : Cycle C P) : cy.ejActs.filterMap Act.src = cy.ejects := by
  simp [ejActs, List.filterMap_map, Function.comp_def, Act.src]

@[simp] theorem ejActs_tgt (cy : Cycle C P) : cy.ejActs.filterMap Act.tgt = [] := by
  simp [ejActs, List.filterMap_map, Function.comp_def, Act.tgt]

@[simp] theorem hopActs_src (cy : Cycle C P) :
    cy.hopActs.filterMap Act.src = cy.hops.map (·.1) := by
  simp [hopActs, List.filterMap_map, Function.comp_def, Act.src]

@[simp] theorem hopActs_tgt (cy : Cycle C P) :
    cy.hopActs.filterMap Act.tgt = cy.hops.map (·.2.1) := by
  simp [hopActs, List.filterMap_map, Function.comp_def, Act.tgt]

@[simp] theorem injActs_src (cy : Cycle C P) : cy.injActs.filterMap Act.src = [] := by
  simp [injActs, List.filterMap_map, Function.comp_def, Act.src]

@[simp] theorem injActs_tgt (cy : Cycle C P) :
    cy.injActs.filterMap Act.tgt = cy.injects.map (·.1) := by
  simp [injActs, List.filterMap_map, Function.comp_def, Act.tgt]

end Cycle

section Models

variable [DecidableEq C] (N : Network C P)

/-- **A cycle of the no-chaining model** (`chain = none` of `scripts/xp_arbiter.py`) under the
selection `sel`, from `f` to `f'`:

* at its start, the arrived packets of `cy.ejects` (distinct channels) are ejected, giving the
  configuration `cy.mid f` at the start of the move phase;
* then the hops of `cy.hops` happen **simultaneously**: each moves a packet of `cy.mid f` that
  has not arrived along a hop offered by `sel` — evaluated on the configuration the arbiter reads
  for that packet (`cy.mid f` itself: `Cycle.ReadsStart`; or `cy.mid f` plus the claims made
  earlier in the cycle, as the simulator's ghosts do) — into a channel **free in `cy.mid f`**; at
  most one hop leaves each channel and at most one enters each channel (so every packet moves at
  most once).  The result is `cy.post f`;
* at its end, the injections of `cy.injects` (distinct channels, each free in `cy.post f`). -/
structure NoChainCycle (sel : Selection C P) (f : Config C P) (cy : Cycle C P)
    (f' : Config C P) : Prop where
  eject : ∀ c ∈ cy.ejects, ∃ p, f c = some p ∧ N.arrived c p = true
  eject_nodup : cy.ejects.Nodup
  hop : ∀ m ∈ cy.hops, ∃ p, cy.mid f m.1 = some p ∧ N.arrived m.1 p = false ∧
    cy.mid f m.2.1 = none ∧ ∃ g, (m.2.1, m.2.2) ∈ sel g m.1 p
  hop_src_nodup : (cy.hops.map (·.1)).Nodup
  hop_tgt_nodup : (cy.hops.map (·.2.1)).Nodup
  inject : ∀ q ∈ cy.injects, q ∈ N.inject ∧ cy.post f q.1 = none
  inject_nodup : (cy.injects.map (·.1)).Nodup
  eq : f' = simulApply (cy.post f) cy.injActs

/-- Every hop of the cycle is offered by `sel` evaluated on the configuration at the start of
the move phase (the snapshot read of the task statement, as opposed to the simulator's ghosts). -/
def Cycle.ReadsStart (sel : Selection C P) (f : Config C P) (cy : Cycle C P) : Prop :=
  ∀ m ∈ cy.hops, ∀ p, cy.mid f m.1 = some p → (m.2.1, m.2.2) ∈ sel (cy.mid f) m.1 p

/-- **A cycle of the sequential model** (`chain = seq`) under `sel`: the ejections, then the hops
one after another — each a single step of the semantics under `sel` in the configuration reached
so far, so a hop may enter a channel vacated earlier in the same cycle (chaining) — then the
injections; no packet moves twice in a cycle (no hop leaves the target of an earlier hop). -/
structure SeqCycle (sel : Selection C P) (f : Config C P) (cy : Cycle C P) (f' : Config C P) :
    Prop where
  path : (N.ltsWith sel).Path f cy.acts f'
  once : cy.hops.Pairwise fun m m' => m'.1 ≠ m.2.1

/-- The selection `sel` frozen at the configuration `g`: whatever the current configuration, it
offers what `sel` offers in `g`. -/
def freeze (sel : Selection C P) (g : Config C P) : Selection C P := fun _ => sel g

variable {N}

/-- **A no-chaining cycle is a sequence of single steps**, under every selection `S` that does
not read the configuration and offers every hop of the cycle. -/
theorem NoChainCycle.path_of {sel S : Selection C P} (hS : ∀ g g', S g = S g') {f f' : Config C P}
    {cy : Cycle C P} (h : N.NoChainCycle sel f cy f')
    (hoff : ∀ m ∈ cy.hops, ∀ p, cy.mid f m.1 = some p → (m.2.1, m.2.2) ∈ S (cy.mid f) m.1 p) :
    (N.ltsWith S).Path f cy.acts f' := by
  have h1 : (N.ltsWith S).Path f cy.ejActs (cy.mid f) := by
    refine path_simul hS (fun a ha => ?_) (by simpa using h.eject_nodup) (by simp)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    obtain ⟨p, hp, harr⟩ := h.eject c hc
    exact StepWith.eject hp harr
  have h2 : (N.ltsWith S).Path (cy.mid f) cy.hopActs (cy.post f) := by
    refine path_simul hS (fun a ha => ?_) (by simpa using h.hop_src_nodup)
      (by simpa using h.hop_tgt_nodup)
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
    obtain ⟨p, hp, harr, hfree, -⟩ := h.hop m hm
    exact StepWith.hop hp harr (hoff m hm p hp) hfree
  have h3 : (N.ltsWith S).Path (cy.post f) cy.injActs f' := by
    rw [h.eq]
    refine path_simul hS (fun a ha => ?_) (by simp) (by simpa using h.inject_nodup)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
    exact StepWith.inject (h.inject q hq).1 (h.inject q hq).2
  exact (h1.append h2).append h3

/-- **A no-chaining cycle is a sequence of single steps of the fully adaptive network**, in the
order of its lists, when the selection only offers permitted hops. -/
theorem NoChainCycle.path {sel : Selection C P}
    (hsub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p) {f f' : Config C P} {cy : Cycle C P}
    (h : N.NoChainCycle sel f cy f') : N.lts.Path f cy.acts f' :=
  h.path_of (S := N.adaptive) (fun _ _ => rfl) fun m hm p hp => by
    obtain ⟨p', hp', -, -, g, hg⟩ := h.hop m hm
    rw [hp] at hp'
    cases hp'
    exact hsub _ _ _ _ hg

/-- **A no-chaining cycle reading the start of the move phase is a sequence of single steps under
one selection**: `sel` frozen at that configuration. -/
theorem NoChainCycle.path_freeze {sel : Selection C P} {f f' : Config C P} {cy : Cycle C P}
    (h : N.NoChainCycle sel f cy f') (hr : cy.ReadsStart sel f) :
    (N.ltsWith (freeze sel (cy.mid f))).Path f cy.acts f' :=
  h.path_of (fun _ _ => rfl) hr

omit [DecidableEq C] in
/-- A frozen selection only offers permitted hops when the selection does. -/
theorem freeze_sub {sel : Selection C P} (hsub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p)
    (g : Config C P) : ∀ f c p q, q ∈ freeze sel g f c p → q ∈ N.route c p :=
  fun _ c p q h => hsub g c p q h

/-- A path under a selection that only offers permitted hops is a path of the fully adaptive
network. -/
theorem path_adaptive {sel : Selection C P} (hsub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p)
    {f f' : Config C P} {as : List (Act C P)} (h : (N.ltsWith sel).Path f as f') :
    N.lts.Path f as f' := by
  induction h with
  | nil => exact LTS.Path.nil _
  | cons hst _ ih =>
    refine LTS.Path.cons ?_ ih
    cases hst with
    | inject h₁ h₂ => exact .inject h₁ h₂
    | hop h₁ h₂ h₃ h₄ => exact .hop h₁ h₂ (hsub _ _ _ _ h₃) h₄
    | eject h₁ h₂ => exact .eject h₁ h₂

/-- **A sequential cycle is literally a sequence of single steps** under the selection in force. -/
theorem SeqCycle.path_lts {sel : Selection C P}
    (hsub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p) {f f' : Config C P} {cy : Cycle C P}
    (h : N.SeqCycle sel f cy f') : N.lts.Path f cy.acts f' :=
  path_adaptive hsub h.path

end Models

/-! ### Paths -/

theorem _root_.AsyncLean.LTS.Path.split {S L : Type*} {A : LTS S L} :
    ∀ {s s'' : S} {l₁ l₂ : List L}, A.Path s (l₁ ++ l₂) s'' →
      ∃ s', A.Path s l₁ s' ∧ A.Path s' l₂ s''
  | s, _, [], _, h => ⟨s, LTS.Path.nil _, h⟩
  | _, _, _ :: _, _, .cons hst h => by
    obtain ⟨s', h₁, h₂⟩ := LTS.Path.split h
    exact ⟨s', LTS.Path.cons hst h₁, h₂⟩

theorem _root_.AsyncLean.LTS.Path.exists_step {S L : Type*} {A : LTS S L} {s s' : S}
    {ls : List L} (h : A.Path s ls s') {l : L} (hl : l ∈ ls) :
    ∃ t t', A.Reachable s t ∧ A.step t l t' := by
  induction h with
  | nil => exact absurd hl List.not_mem_nil
  | cons hst _ ih =>
    rcases List.mem_cons.1 hl with rfl | hl
    · exact ⟨_, _, LTS.Reachable.refl _, hst⟩
    · obtain ⟨t, t', hr, ht⟩ := ih hl
      exact ⟨t, t', LTS.Reachable.head ⟨_, hst⟩ hr, ht⟩

section Runs

variable [DecidableEq C] (N : Network C P)

/-- **A run of a cycle model** `M` (`Network.NoChainCycle` or `Network.SeqCycle`) under a
time-varying selection: `st n` is the configuration at the start of cycle `n`, `cyc n` what
happens in it and `sel n` the selection in force during it, chosen arbitrarily (by a strategy's
history, a learner, an adversary) among those satisfying `ok`. -/
structure CycleRun (M : Selection C P → Config C P → Cycle C P → Config C P → Prop)
    (ok : Selection C P → Prop) where
  /-- The configuration at the start of cycle `n`. -/
  st : ℕ → Config C P
  /-- The ejections, hops and injections of cycle `n`. -/
  cyc : ℕ → Cycle C P
  /-- The selection in force during cycle `n`. -/
  sel : ℕ → Selection C P
  start : st 0 = empty
  sel_ok : ∀ n, ok (sel n)
  step : ∀ n, M (sel n) (st n) (cyc n) (st (n + 1))

/-- The cycles of the model `M` under the admissible selections are sequences of single steps of
the fully adaptive network. -/
def Sequential (M : Selection C P → Config C P → Cycle C P → Config C P → Prop)
    (ok : Selection C P → Prop) : Prop :=
  ∀ σ f cy f', ok σ → M σ f cy f' → N.lts.Path f cy.acts f'

variable {N}

/-- The no-chaining model is sequential, for selections that only offer permitted hops. -/
theorem noChain_sequential {ok : Selection C P → Prop}
    (hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p) :
    N.Sequential N.NoChainCycle ok :=
  fun _ _ _ _ hσ h => h.path (hsub _ hσ)

/-- The sequential model is sequential, for selections that only offer permitted hops. -/
theorem seq_sequential {ok : Selection C P → Prop}
    (hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p) :
    N.Sequential N.SeqCycle ok :=
  fun _ _ _ _ hσ h => h.path_lts (hsub _ hσ)

namespace CycleRun

variable {M : Selection C P → Config C P → Cycle C P → Config C P → Prop}
  {ok : Selection C P → Prop} (r : CycleRun M ok)

/-- The configuration at the start of every cycle is reachable in the fully adaptive network. -/
theorem reachable (hM : N.Sequential M ok) (n : ℕ) : N.lts.Reachable empty (r.st n) := by
  induction n with
  | zero => rw [r.start]
  | succ n ih => exact ih.trans (hM _ _ _ _ (r.sel_ok n) (r.step n)).reachable

/-- **Every configuration of the run is legal.** -/
theorem legal {legal : C → P → Prop} (hcl : N.Closed legal) (hM : N.Sequential M ok) (n : ℕ) :
    Legal legal (r.st n) :=
  N.legal_of_reachable hcl N.adaptive_valid (r.reachable hM n)

/-- **Every hop of every cycle is a routing step** of the packet that moves, from a legal pair:
the hop bounds of the routing function (`Network.packet_hops_le`) hold for every packet. -/
theorem hop_packetStep {legal : C → P → Prop} (hcl : N.Closed legal) (hM : N.Sequential M ok)
    {n : ℕ} {m : C × C × P} (hm : m ∈ (r.cyc n).hops) :
    ∃ p, legal m.1 p ∧ N.PacketStep (m.1, p) (m.2.1, m.2.2) := by
  have hmem : Act.hop m.1 m.2.1 m.2.2 ∈ (r.cyc n).acts := by
    simp only [Cycle.acts, Cycle.hopActs, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨m, hm, rfl⟩)
  obtain ⟨t, t', ht, hst⟩ := (hM _ _ _ _ (r.sel_ok n) (r.step n)).exists_step hmem
  have hrt := (r.reachable hM n).trans ht
  obtain ⟨p, hp, hps⟩ := StepWith.packetStep N N.adaptive_valid hst
  exact ⟨p, N.legal_of_reachable hcl N.adaptive_valid hrt _ _ hp, hps⟩

end CycleRun

end Runs

/-! ### The potential: livelock freedom and drain, cycle by cycle -/

section Potential

variable [DecidableEq C] {N : Network C P}

/-- The potential of a configuration over the channels `S`: the sum of the weights of their
contents (`0` for a free channel, one more than the rank of its packet otherwise). -/
def pot (S : Finset C) (rk : C → P → ℕ) (f : Config C P) : ℕ := ∑ c ∈ S, wt rk c (f c)

/-- **Every move decreases the potential**, when the rank decreases along every permitted hop and
`S` contains every channel of a legal pair. -/
theorem pot_lt_of_move {legal : C → P → Prop} (hcl : N.Closed legal) {S : Finset C}
    (hS : ∀ c p, legal c p → c ∈ S) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {f f' : Config C P} {a : Act C P} (hf : Legal legal f) (ha : a.IsMove)
    (hst : N.lts.step f a f') : pot S rk f' < pot S rk f := by
  change N.StepWith N.adaptive f a f' at hst
  cases hst with
  | inject => simp [Act.IsMove] at ha
  | @hop c c' p p' hp harr hq hfree =>
    have hl' : legal c' p' := hcl.route c p (c', p') (hf c p hp) harr hq
    have hne : c' ≠ c := by rintro rfl; simp [hp] at hfree
    have h1 := sum_update_add _ (wt rk) f (hS c p (hf c p hp)) none
    have h2 := sum_update_add _ (wt rk) (Function.update f c none) (hS c' p' hl') (some p')
    have hlt := hrk c p (c', p') (hf c p hp) harr hq
    rw [Function.update_of_ne hne, hfree] at h2
    rw [hp, wt_some, wt_none] at h1
    rw [wt_none, wt_some] at h2
    simp only at hlt
    unfold pot
    omega
  | @eject c p hp _ =>
    have h1 := sum_update_add _ (wt rk) f (hS c p (hf c p hp)) none
    rw [hp, wt_some, wt_none] at h1
    unfold pot
    omega

/-- Along a path of moves from a legal configuration, the potential drops by at least the number
of moves. -/
theorem pot_path {legal : C → P → Prop} (hcl : N.Closed legal) {S : Finset C}
    (hS : ∀ c p, legal c p → c ∈ S) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {f f' : Config C P} {as : List (Act C P)} (h : N.lts.Path f as f') (hf : Legal legal f)
    (has : ∀ a ∈ as, a.IsMove) : pot S rk f' + as.length ≤ pot S rk f := by
  induction h with
  | nil => simp
  | @cons g g' g'' a as hst _ ih =>
    have hlt := pot_lt_of_move hcl hS rk hrk hf (has a List.mem_cons_self) hst
    have := ih (N.legal_step hcl (fun _ _ _ _ h => h) hf hst)
      (fun b hb => has b (List.mem_cons_of_mem _ hb))
    simp only [List.length_cons]
    omega

omit [DecidableEq C] in
/-- A legal configuration of potential zero is empty. -/
theorem eq_empty_of_pot {legal : C → P → Prop} {S : Finset C} (hS : ∀ c p, legal c p → c ∈ S)
    (rk : C → P → ℕ) {f : Config C P} (hf : Legal legal f) (h0 : pot S rk f = 0) : f = empty := by
  funext c
  cases hc : f c with
  | none => rfl
  | some p =>
    have := Finset.single_le_sum (f := fun c => wt rk c (f c)) (fun _ _ => Nat.zero_le _)
      (hS c p (hf c p hc))
    simp only [hc, wt_some] at this
    unfold pot at h0
    omega

/-- **A uniform bound on the potential**: on legal configurations it is at most the sum, over a
finite set `T` containing the legal pairs, of the ranks plus one. -/
theorem pot_le_bound {legal : C → P → Prop} {S : Finset C} {T : Finset (C × P)}
    (hT : ∀ q : C × P, legal q.1 q.2 → q ∈ T) (rk : C → P → ℕ) {f : Config C P}
    (hf : Legal legal f) : pot S rk f ≤ ∑ q ∈ T, (rk q.1 q.2 + 1) := by
  classical
  have key : ∀ c ∈ S, wt rk c (f c) ≤ ∑ q ∈ T with q.1 = c, (rk q.1 q.2 + 1) := by
    intro c _
    cases hc : f c with
    | none => simp
    | some p =>
      have hm : (c, p) ∈ T.filter (·.1 = c) := Finset.mem_filter.2 ⟨hT (c, p) (hf c p hc), rfl⟩
      simpa using Finset.single_le_sum (f := fun q : C × P => rk q.1 q.2 + 1)
        (fun _ _ => Nat.zero_le _) hm
  calc pot S rk f ≤ ∑ c ∈ S, ∑ q ∈ T with q.1 = c, (rk q.1 q.2 + 1) := Finset.sum_le_sum key
    _ = ∑ q ∈ T with q.1 ∈ S, (rk q.1 q.2 + 1) :=
      Finset.sum_fiberwise_eq_sum_filter T S Prod.fst _
    _ ≤ ∑ q ∈ T, (rk q.1 q.2 + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.zero_le _

end Potential

/-! ### Deadlock freedom and drain, cycle by cycle -/

section CycleLiveness

variable [DecidableEq C] {N : Network C P}

variable (N) in
/-- The arbitration of a cycle is **work conserving** for the selection `sel`: every packet that
has arrived at the start of the cycle is ejected, and if no packet hops, the selection, evaluated
at the start of the move phase, offered no packet a hop into a channel free there.  (If nobody
hops, nobody claimed a channel, so whatever the arbiter reads is the start of the move phase:
the simulators, which try every packet, are work conserving in both models.) -/
structure WorkConserving (sel : Selection C P) (f : Config C P) (cy : Cycle C P) : Prop where
  eject : ∀ c p, f c = some p → N.arrived c p = true → c ∈ cy.ejects
  hop : cy.hops = [] → ∀ c p, cy.mid f c = some p → N.arrived c p = false →
    ∀ q ∈ sel (cy.mid f) c p, cy.mid f q.1 ≠ none

@[simp] theorem Cycle.mid_of_ejects_nil {cy : Cycle C P} (h : cy.ejects = []) (f : Config C P) :
    cy.mid f = f := by
  simp [Cycle.mid, Cycle.ejActs, h]

/-- **Deadlock freedom, cycle by cycle**: a work-conserving cycle in a non-empty configuration of
legal packets moves some packet, under every selection satisfying Duato's condition with
throttled sources on the legal pairs — in either cycle model (the statement only reads the
configuration at the start of the cycle and of its move phase). -/
theorem WorkConserving.moves_pos {legal : C → P → Prop} {R₁ : C → P → List (C × P)}
    {src : C → Prop} {sel : Selection C P} (hsel : N.SourceSelOn legal R₁ src sel)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    {f : Config C P} {cy : Cycle C P} (hf : Legal legal f) (hne : f ≠ empty)
    (hwc : N.WorkConserving sel f cy) : 0 < cy.moves := by
  by_contra h0
  have he : cy.ejects = [] := List.eq_nil_of_length_eq_zero (by unfold Cycle.moves at h0; omega)
  have hh : cy.hops = [] := List.eq_nil_of_length_eq_zero (by unfold Cycle.moves at h0; omega)
  obtain ⟨a, f', ha, hst⟩ := N.movable_of_sourceSelOn hsel hconn hwf hR₁ hf hne
  change N.StepWith sel f a f' at hst
  cases hst with
  | inject => simp [Act.IsMove] at ha
  | @hop c c' p p' hp harr hq hfree =>
    refine hwc.hop hh c p (by rw [Cycle.mid_of_ejects_nil he]; exact hp) harr (c', p')
      (by rw [Cycle.mid_of_ejects_nil he]; exact hq) ?_
    rw [Cycle.mid_of_ejects_nil he]; exact hfree
  | @eject c p hp harr =>
    have := hwc.eject c p hp harr
    rw [he] at this
    exact List.not_mem_nil this

/-- **Some no-chaining cycle moves a packet**: in a non-empty configuration of legal packets, a
cycle that ejects one arrived packet, or moves one packet along a hop the selection offers at the
start of the cycle, is a cycle of the no-chaining model. -/
theorem exists_noChainCycle {legal : C → P → Prop} {R₁ : C → P → List (C × P)}
    {src : C → Prop} {sel : Selection C P} (hsel : N.SourceSelOn legal R₁ src sel)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    {f : Config C P} (hf : Legal legal f) (hne : f ≠ empty) :
    ∃ cy f', N.NoChainCycle sel f cy f' ∧ cy.ReadsStart sel f ∧ 0 < cy.moves := by
  obtain ⟨a, f', ha, hst⟩ := N.movable_of_sourceSelOn hsel hconn hwf hR₁ hf hne
  change N.StepWith sel f a f' at hst
  cases hst with
  | inject => simp [Act.IsMove] at ha
  | @hop c c' p p' hp harr hq hfree =>
    let cy : Cycle C P := ⟨[], [(c, c', p')], []⟩
    refine ⟨cy, _, ⟨by simp [cy], by simp [cy], ?_, by simp [cy], by simp [cy], by simp [cy],
      by simp [cy], rfl⟩, ?_, by simp [cy, Cycle.moves]⟩
    · intro m hm
      simp only [cy, List.mem_singleton] at hm
      subst hm
      rw [Cycle.mid_of_ejects_nil rfl]
      exact ⟨p, hp, harr, hfree, f, hq⟩
    · intro m hm p₀ hp₀
      simp only [cy, List.mem_singleton] at hm
      subst hm
      rw [Cycle.mid_of_ejects_nil rfl] at hp₀ ⊢
      rw [hp] at hp₀
      cases hp₀
      exact hq
  | @eject c p hp harr =>
    let cy : Cycle C P := ⟨[c], [], []⟩
    refine ⟨cy, _, ⟨?_, by simp [cy], by simp [cy], by simp [cy], by simp [cy], by simp [cy],
      by simp [cy], rfl⟩, by simp [Cycle.ReadsStart, cy], by simp [cy, Cycle.moves]⟩
    intro c' hc'
    simp only [cy, List.mem_singleton] at hc'
    subst hc'
    exact ⟨p, hp, harr⟩

namespace CycleRun

variable {M : Selection C P → Config C P → Cycle C P → Config C P → Prop}
  {ok : Selection C P → Prop} (r : CycleRun M ok)

/-- **Livelock freedom, cycle by cycle**: a cycle without injections lowers the potential by at
least its number of moves. -/
theorem pot_moves_le {legal : C → P → Prop} (hcl : N.Closed legal) {S : Finset C}
    (hS : ∀ c p, legal c p → c ∈ S) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (hM : N.Sequential M ok) {n : ℕ} (hinj : (r.cyc n).injects = []) :
    pot S rk (r.st (n + 1)) + (r.cyc n).moves ≤ pot S rk (r.st n) := by
  have h := pot_path hcl hS rk hrk (hM _ _ _ _ (r.sel_ok n) (r.step n)) (r.legal hcl hM n) ?_
  · simpa [Cycle.acts, Cycle.ejActs, Cycle.hopActs, Cycle.injActs, hinj, Cycle.moves] using h
  · intro a ha
    simp only [Cycle.acts, Cycle.ejActs, Cycle.hopActs, Cycle.injActs, hinj, List.map_nil,
      List.append_nil, List.mem_append, List.mem_map] at ha
    rcases ha with ⟨c, -, rfl⟩ | ⟨m, -, rfl⟩ <;> rfl

/-- Over `T` cycles without injections, the potential drops by at least the number of moves. -/
theorem pot_sum_le {legal : C → P → Prop} (hcl : N.Closed legal) {S : Finset C}
    (hS : ∀ c p, legal c p → c ∈ S) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (hM : N.Sequential M ok) (n : ℕ) :
    ∀ T, (∀ i < T, (r.cyc (n + i)).injects = []) →
      pot S rk (r.st (n + T)) + ∑ i ∈ Finset.range T, (r.cyc (n + i)).moves ≤ pot S rk (r.st n)
  | 0, _ => by simp
  | T + 1, hinj => by
    have ih := pot_sum_le hcl hS rk hrk hM n T fun i hi => hinj i (by omega)
    have h := r.pot_moves_le hcl hS rk hrk hM (n := n + T) (hinj T (by omega))
    rw [Finset.sum_range_succ, show n + (T + 1) = n + T + 1 by omega]
    omega

/-- **Livelock freedom, cycle by cycle**: among `T` cycles without injections, at most
`pot S rk (r.st n)` move a packet. -/
theorem card_moving_le {legal : C → P → Prop} (hcl : N.Closed legal) {S : Finset C}
    (hS : ∀ c p, legal c p → c ∈ S) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (hM : N.Sequential M ok) (n T : ℕ) (hinj : ∀ i < T, (r.cyc (n + i)).injects = []) :
    ((Finset.range T).filter fun i => 0 < (r.cyc (n + i)).moves).card ≤ pot S rk (r.st n) := by
  have h := r.pot_sum_le hcl hS rk hrk hM n T hinj
  have h2 : ((Finset.range T).filter fun i => 0 < (r.cyc (n + i)).moves).card ≤
      ∑ i ∈ Finset.range T, (r.cyc (n + i)).moves := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ i ∈ (Finset.range T).filter (fun i => 0 < (r.cyc (n + i)).moves), 1
        ≤ ∑ i ∈ (Finset.range T).filter (fun i => 0 < (r.cyc (n + i)).moves),
            (r.cyc (n + i)).moves :=
          Finset.sum_le_sum fun i hi => (Finset.mem_filter.1 hi).2
      _ ≤ ∑ i ∈ Finset.range T, (r.cyc (n + i)).moves :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => Nat.zero_le _
  omega

/-- **Livelock freedom, cycle by cycle**: once injections stop for good, the network eventually
stops moving for good (it has drained, or it is stuck, which `drain` rules out). -/
theorem eventually_idle {legal : C → P → Prop} (hcl : N.Closed legal) {S : Finset C}
    (hS : ∀ c p, legal c p → c ∈ S) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (hM : N.Sequential M ok) (n : ℕ) (hinj : ∀ m, n ≤ m → (r.cyc m).injects = []) :
    ∃ m, n ≤ m ∧ ∀ m', m ≤ m' → (r.cyc m').moves = 0 := by
  by_contra hc
  push Not at hc
  have key : ∀ k, ∃ T, k ≤ ((Finset.range T).filter fun i => 0 < (r.cyc (n + i)).moves).card := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨T, hT⟩ := ih
      obtain ⟨m', hm', hmv⟩ := hc (n + T) (by omega)
      refine ⟨m' - n + 1, ?_⟩
      have hsub : insert (m' - n) ((Finset.range T).filter fun i => 0 < (r.cyc (n + i)).moves) ⊆
          (Finset.range (m' - n + 1)).filter fun i => 0 < (r.cyc (n + i)).moves := by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
          rw [show n + (m' - n) = m' by omega]
          omega
        · obtain ⟨hi, hp⟩ := Finset.mem_filter.1 hi
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by simp at hi; omega), hp⟩
      have hnot : m' - n ∉ (Finset.range T).filter fun i => 0 < (r.cyc (n + i)).moves := by
        intro h
        simp only [Finset.mem_filter, Finset.mem_range] at h
        omega
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at this
      omega
  obtain ⟨T, hT⟩ := key (pot S rk (r.st n) + 1)
  have := r.card_moving_le hcl hS rk hrk hM n T fun i _ => hinj (n + i) (by omega)
  omega

/-- **Drain, cycle by cycle**: once injections stop, with work-conserving arbitration and every
admissible selection satisfying Duato's condition with throttled sources on the legal pairs, the
network is empty after at most `pot S rk (r.st n)` cycles — no fairness is needed. -/
theorem drain {legal : C → P → Prop} (hcl : N.Closed legal) {S : Finset C}
    (hS : ∀ c p, legal c p → c ∈ S) {R₁ : C → P → List (C × P)} {src : C → Prop}
    (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (hM : N.Sequential M ok) (n B : ℕ) (hB : pot S rk (r.st n) ≤ B)
    (hquiet : ∀ i < B, (r.cyc (n + i)).injects = [] ∧
      N.WorkConserving (r.sel (n + i)) (r.st (n + i)) (r.cyc (n + i))) :
    r.st (n + B) = empty := by
  have key : ∀ k ≤ B, r.st (n + k) = empty ∨ pot S rk (r.st (n + k)) + k ≤ pot S rk (r.st n) := by
    intro k
    induction k with
    | zero => intro; right; simp
    | succ k ih =>
      intro hk
      have hq := hquiet k (by omega)
      have hdec := r.pot_moves_le hcl hS rk hrk hM (n := n + k) hq.1
      rw [show n + (k + 1) = n + k + 1 by omega]
      rcases ih (by omega) with he | hle
      · left
        refine eq_empty_of_pot hS rk (r.legal hcl hM _) ?_
        rw [he] at hdec
        have : pot S rk (empty : Config C P) = 0 := by simp [pot, empty]
        omega
      · by_cases he : r.st (n + k) = empty
        · left
          refine eq_empty_of_pot hS rk (r.legal hcl hM _) ?_
          rw [he] at hdec
          have : pot S rk (empty : Config C P) = 0 := by simp [pot, empty]
          omega
        · right
          have := hq.2.moves_pos (hok _ (r.sel_ok _)) hconn hwf hR₁ (r.legal hcl hM _) he
          omega
  rcases key B le_rfl with he | hle
  · exact he
  · exact eq_empty_of_pot hS rk (r.legal hcl hM _) (by omega)

end CycleRun

end CycleLiveness

/-! ### The injection limit -/

section Injection

variable [DecidableEq C] {N : Network C P}

theorem StepWith.inject_inv {S : Selection C P} {g g' : Config C P} {c : C} {p : P}
    (h : N.StepWith S g (.inject c p) g') :
    (c, p) ∈ N.inject ∧ g c = none ∧ g' = Function.update g c (some p) := by
  cases h with
  | inject h₁ h₂ => exact ⟨h₁, h₂, rfl⟩

/-- A path of injections enters distinct channels, each free at its start, with packets the
sources may inject. -/
theorem inject_path {S : Selection C P} : ∀ {qs : List (C × P)} {g g' : Config C P},
    (N.ltsWith S).Path g (qs.map fun q => Act.inject q.1 q.2) g' →
      (qs.map (·.1)).Nodup ∧ (∀ x, g x ≠ none → x ∉ qs.map (·.1)) ∧ ∀ q ∈ qs, q ∈ N.inject
  | [], _, _, _ => ⟨List.nodup_nil, fun _ _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
  | q :: qs, g, g', .cons hst hrest => by
    obtain ⟨hq, hfree, rfl⟩ := StepWith.inject_inv hst
    obtain ⟨hnd, hocc, hmem⟩ := inject_path hrest
    refine ⟨List.nodup_cons.2 ⟨hocc q.1 (by simp), hnd⟩, fun x hx hxm => ?_, fun q' hq' => ?_⟩
    · have hxq : x ≠ q.1 := by rintro rfl; exact hx hfree
      rcases List.mem_cons.1 hxm with h | h
      · exact hxq h
      · exact hocc x (by rwa [Function.update_of_ne hxq]) h
    · rcases List.mem_cons.1 hq' with rfl | h
      · exact hq
      · exact hmem q' h

namespace CycleRun

variable {M : Selection C P → Config C P → Cycle C P → Config C P → Prop}
  {ok : Selection C P → Prop} (r : CycleRun M ok)

/-- The injections of a cycle enter distinct channels (so at most one packet enters each channel
per cycle), with packets the sources may inject. -/
theorem injects_spec (hM : N.Sequential M ok) (n : ℕ) :
    ((r.cyc n).injects.map (·.1)).Nodup ∧ ∀ q ∈ (r.cyc n).injects, q ∈ N.inject := by
  obtain ⟨_, _, h⟩ := (hM _ _ _ _ (r.sel_ok n) (r.step n)).split
  obtain ⟨hnd, -, hmem⟩ := inject_path h
  exact ⟨hnd, hmem⟩

/-- **At most one injection per channel and per cycle.** -/
theorem count_inject_le_one (hM : N.Sequential M ok) (n : ℕ) (c : C) :
    ((r.cyc n).injects.map (·.1)).count c ≤ 1 :=
  List.nodup_iff_count_le_one.1 (r.injects_spec hM n).1 c

/-- **The injection limit**: in any `T` consecutive cycles, at most `T` packets are injected into
a given channel (the injection channel of a node, in the packet model: a node injects at most `T`
packets in `T` cycles). -/
theorem sum_count_inject_le (hM : N.Sequential M ok) (c : C) (W T : ℕ) :
    ∑ i ∈ Finset.range T, ((r.cyc (W + i)).injects.map (·.1)).count c ≤ T := by
  have := Finset.sum_le_card_nsmul (Finset.range T)
    (fun i => ((r.cyc (W + i)).injects.map (·.1)).count c) 1
    (fun i _ => r.count_inject_le_one hM (W + i) c)
  simpa using this

/-- A cycle injects at most one packet per injection channel. -/
theorem length_injects_le (hM : N.Sequential M ok) {I : Finset C}
    (hI : ∀ q ∈ N.inject, q.1 ∈ I) (n : ℕ) : (r.cyc n).injects.length ≤ I.card := by
  obtain ⟨hnd, hmem⟩ := r.injects_spec hM n
  rw [← List.length_map (f := (·.1)), ← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card fun c hc => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hc)
  exact hI q (hmem q hq)

/-- In `T` consecutive cycles, at most `I.card * T` packets are injected, `I` containing every
injection channel. -/
theorem sum_injects_le (hM : N.Sequential M ok) {I : Finset C} (hI : ∀ q ∈ N.inject, q.1 ∈ I)
    (W T : ℕ) : ∑ i ∈ Finset.range T, (r.cyc (W + i)).injects.length ≤ I.card * T := by
  have := Finset.sum_le_card_nsmul (Finset.range T) (fun i => (r.cyc (W + i)).injects.length)
    I.card (fun i _ => r.length_injects_le hM hI (W + i))
  simpa [mul_comm] using this

end CycleRun

/-! #### Conservation of packets -/

/-- The number of packets held in the channels of `S`. -/
def occ (S : Finset C) (f : Config C P) : ℕ := (S.filter fun c => f c ≠ none).card

/-- `1` for an ejection. -/
def Act.ejN : Act C P → ℕ
  | .eject _ => 1
  | _ => 0

/-- `1` for an injection. -/
def Act.injN : Act C P → ℕ
  | .inject _ _ => 1
  | _ => 0

/-- **A step conserves packets**: an injection adds one, an ejection removes one, a hop moves
one (counting in a set of channels holding every packet before and after). -/
theorem occ_step {S : Selection C P} {T : Finset C} {f f' : Config C P} {a : Act C P}
    (h : N.StepWith S f a f') (hf : ∀ c, f c ≠ none → c ∈ T) (hf' : ∀ c, f' c ≠ none → c ∈ T) :
    occ T f' + a.ejN = occ T f + a.injN := by
  cases h with
  | @inject c p _ hfree =>
    have e : T.filter (fun x => Function.update f c (some p) x ≠ none) =
        insert c (T.filter fun x => f x ≠ none) := by
      ext x
      by_cases hx : x = c
      · subst hx; simp [hf' x (by simp)]
      · simp [hx]
    have hn : c ∉ T.filter fun x => f x ≠ none := by simp [hfree]
    simp only [occ, e, Finset.card_insert_of_notMem hn, Act.ejN, Act.injN]
  | @hop c c' p p' hp _ _ hfree =>
    have hcc : c ≠ c' := by rintro rfl; simp [hp] at hfree
    have e1 : T.filter (fun x => f x ≠ none) =
        insert c (T.filter fun x => f x ≠ none ∧ x ≠ c) := by
      ext x
      by_cases hx : x = c
      · subst hx; simp [hp, hf x (by simp [hp])]
      · simp [hx]
    have e2 : T.filter (fun x => Function.update (Function.update f c none) c' (some p') x ≠ none)
        = insert c' (T.filter fun x => f x ≠ none ∧ x ≠ c) := by
      ext x
      by_cases hx : x = c'
      · subst hx; simp [hf' x (by simp)]
      · by_cases hxc : x = c
        · subst hxc; simp [hx]
        · simp [hx, hxc]
    have hn1 : c ∉ T.filter fun x => f x ≠ none ∧ x ≠ c := by simp
    have hn2 : c' ∉ T.filter fun x => f x ≠ none ∧ x ≠ c := by simp [hfree]
    simp only [occ, e1, e2, Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2,
      Act.ejN, Act.injN]
  | @eject c p hp _ =>
    have e : T.filter (fun x => f x ≠ none) =
        insert c (T.filter fun x => Function.update f c none x ≠ none) := by
      ext x
      by_cases hx : x = c
      · subst hx; simp [hp, hf x (by simp [hp])]
      · simp [hx]
    have hn : c ∉ T.filter fun x => Function.update f c none x ≠ none := by simp
    simp only [occ, e, Finset.card_insert_of_notMem hn, Act.ejN, Act.injN]

/-- **Packets are conserved along a path** of the fully adaptive network from a legal
configuration, counting in a set `T` containing every channel of a legal pair. -/
theorem occ_path {legal : C → P → Prop} (hcl : N.Closed legal) {T : Finset C}
    (hT : ∀ c p, legal c p → c ∈ T) {f f' : Config C P} {as : List (Act C P)}
    (h : N.lts.Path f as f') (hf : Legal legal f) :
    occ T f' + (as.map Act.ejN).sum = occ T f + (as.map Act.injN).sum := by
  have hsupp : ∀ g : Config C P, Legal legal g → ∀ c, g c ≠ none → c ∈ T := by
    intro g hg c hc
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hc
    exact hT c p (hg c p hp)
  induction h with
  | nil => simp
  | @cons g g' g'' a as hst _ ih =>
    have hg' := N.legal_step hcl (fun _ _ _ _ h => h) hf hst
    have h1 := occ_step hst (hsupp g hf) (hsupp g' hg')
    have h2 := ih hg'
    simp only [List.map_cons, List.sum_cons]
    omega

omit [DecidableEq C] in
@[simp] theorem Cycle.sum_ejN (cy : Cycle C P) : (cy.acts.map Act.ejN).sum = cy.ejects.length := by
  simp [Cycle.acts, Cycle.ejActs, Cycle.hopActs, Cycle.injActs, Function.comp_def, Act.ejN]

omit [DecidableEq C] in
@[simp] theorem Cycle.sum_injN (cy : Cycle C P) :
    (cy.acts.map Act.injN).sum = cy.injects.length := by
  simp [Cycle.acts, Cycle.ejActs, Cycle.hopActs, Cycle.injActs, Function.comp_def, Act.injN]

namespace CycleRun

variable {M : Selection C P → Config C P → Cycle C P → Config C P → Prop}
  {ok : Selection C P → Prop} (r : CycleRun M ok)

/-- **Conservation over `T` cycles**: the packets present at the end plus those ejected equal
the packets present at the start plus those injected. -/
theorem occ_add_ejects {legal : C → P → Prop} (hcl : N.Closed legal) {T : Finset C}
    (hT : ∀ c p, legal c p → c ∈ T) (hM : N.Sequential M ok) (W : ℕ) :
    ∀ K, occ T (r.st (W + K)) + ∑ i ∈ Finset.range K, (r.cyc (W + i)).ejects.length =
      occ T (r.st W) + ∑ i ∈ Finset.range K, (r.cyc (W + i)).injects.length
  | 0 => by simp
  | K + 1 => by
    have ih := occ_add_ejects hcl hT hM W K
    have h := occ_path hcl hT (hM _ _ _ _ (r.sel_ok (W + K)) (r.step (W + K)))
      (r.legal hcl hM (W + K))
    rw [Cycle.sum_ejN, Cycle.sum_injN] at h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, show W + (K + 1) = W + K + 1 by omega]
    omega

/-- **The throughput limit**: in any `K` consecutive cycles from cycle `W`, at most
`occ T (r.st W) + I.card * K` packets are delivered, `I` containing every injection channel —
for every network, selection and strategy, in either cycle model. -/
theorem sum_ejects_le {legal : C → P → Prop} (hcl : N.Closed legal) {T : Finset C}
    (hT : ∀ c p, legal c p → c ∈ T) (hM : N.Sequential M ok) {I : Finset C}
    (hI : ∀ q ∈ N.inject, q.1 ∈ I) (W K : ℕ) :
    ∑ i ∈ Finset.range K, (r.cyc (W + i)).ejects.length ≤ occ T (r.st W) + I.card * K := by
  have h1 := r.occ_add_ejects hcl hT hM W K
  have h2 := r.sum_injects_le hM hI W K
  omega

omit [DecidableEq C] in
/-- The packets in the network never exceed the channels of legal pairs. -/
theorem occ_le (T : Finset C) (f : Config C P) : occ T f ≤ T.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- **The throughput limit from the start**: in the first `K` cycles at most `I.card * K` packets
are delivered — at most one per injection channel and per cycle. -/
theorem sum_ejects_le_start {legal : C → P → Prop} (hcl : N.Closed legal) {T : Finset C}
    (hT : ∀ c p, legal c p → c ∈ T) (hM : N.Sequential M ok) {I : Finset C}
    (hI : ∀ q ∈ N.inject, q.1 ∈ I) (K : ℕ) :
    ∑ i ∈ Finset.range K, (r.cyc i).ejects.length ≤ I.card * K := by
  have h := r.sum_ejects_le hcl hT hM hI 0 K
  have h0 : occ T (r.st 0) = 0 := by simp [occ, r.start, empty]
  simpa [h0] using h

/-- **The long-run throughput is at most one packet per injection channel and per cycle**: for
every `m > 0`, over every window of `K ≥ m * T.card` cycles, `m` times the number of delivered
packets is at most `(m * I.card + 1) * K`: the delivery rate exceeds `I.card` by at most `1 / m`
per cycle. -/
theorem throughput_le {legal : C → P → Prop} (hcl : N.Closed legal) {T : Finset C}
    (hT : ∀ c p, legal c p → c ∈ T) (hM : N.Sequential M ok) {I : Finset C}
    (hI : ∀ q ∈ N.inject, q.1 ∈ I) (W K m : ℕ) (hK : m * T.card ≤ K) :
    m * ∑ i ∈ Finset.range K, (r.cyc (W + i)).ejects.length ≤ (m * I.card + 1) * K := by
  have h := r.sum_ejects_le hcl hT hM hI W K
  have h2 := occ_le T (r.st W)
  have h3 : m * ∑ i ∈ Finset.range K, (r.cyc (W + i)).ejects.length ≤
      m * T.card + m * (I.card * K) := by
    calc _ ≤ m * (occ T (r.st W) + I.card * K) := Nat.mul_le_mul_left m h
      _ ≤ m * (T.card + I.card * K) := Nat.mul_le_mul_left m (by omega)
      _ = _ := Nat.mul_add _ _ _
  calc _ ≤ m * T.card + m * (I.card * K) := h3
    _ ≤ K + m * (I.card * K) := by omega
    _ = (m * I.card + 1) * K := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.add_comm]

end CycleRun

end Injection

/-! ### Delivery under cycle-level fairness (no-chaining model) -/

section Delivery

variable [DecidableEq C] {N : Network C P}

/-- An ejected channel is free at the start of the move phase. -/
theorem Cycle.mid_of_mem_ejects {f : Config C P} {cy : Cycle C P} {c : C} (hc : c ∈ cy.ejects) :
    cy.mid f c = none :=
  simulApply_of_src (a := .eject c) (List.mem_map.2 ⟨c, hc, rfl⟩) rfl fun b hb => by
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hb
    simp [Act.tgt]

/-- A channel not ejected keeps its content until the start of the move phase. -/
theorem Cycle.mid_of_not_mem_ejects {f : Config C P} {cy : Cycle C P} {c : C}
    (hc : c ∉ cy.ejects) : cy.mid f c = f c :=
  simulApply_of_not fun b hb => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hb
    refine ⟨fun e => hc ?_, by simp [Act.tgt]⟩
    simp only [Act.src, Option.some.injEq] at e
    exact e ▸ hd

/-- A free channel is still free at the start of the move phase. -/
theorem Cycle.mid_of_none {f : Config C P} {cy : Cycle C P} {c : C} (hc : f c = none) :
    cy.mid f c = none := by
  by_cases he : c ∈ cy.ejects
  · exact Cycle.mid_of_mem_ejects he
  · rw [Cycle.mid_of_not_mem_ejects he, hc]

namespace NoChainCycle

variable {sel : Selection C P} {f f' : Config C P} {cy : Cycle C P}

theorem mid_of_some (h : N.NoChainCycle sel f cy f') {c : C} {p : P} (hc : f c = some p)
    (ha : N.arrived c p = false) : cy.mid f c = some p := by
  have he : c ∉ cy.ejects := fun he => by
    obtain ⟨p', hp', harr⟩ := h.eject c he
    rw [hc] at hp'; cases hp'; simp [ha] at harr
  rw [Cycle.mid_of_not_mem_ejects he, hc]

/-- The end of the cycle agrees with the end of the move phase outside the injected channels. -/
theorem eq_post (h : N.NoChainCycle sel f cy f') {x : C} (hx : ∀ q ∈ cy.injects, q.1 ≠ x) :
    f' x = cy.post f x := by
  rw [h.eq]
  refine simulApply_of_not fun b hb => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hb
  exact ⟨by simp [Act.src], by simpa [Act.tgt] using hx q hq⟩

/-- A hop lands: at the end of the cycle the packet is in the target channel. -/
theorem land (h : N.NoChainCycle sel f cy f') {m : C × C × P} (hm : m ∈ cy.hops) :
    f' m.2.1 = some m.2.2 := by
  have hpost : cy.post f m.2.1 = some m.2.2 :=
    simulApply_of_tgt (a := .hop m.1 m.2.1 m.2.2) (by simpa using h.hop_tgt_nodup)
      (List.mem_map.2 ⟨m, hm, rfl⟩) rfl
  rw [h.eq_post fun q hq e => by
    have := (h.inject q hq).2
    rw [e, hpost] at this
    simp at this]
  exact hpost

/-- A hop vacates its source channel, which is still free at the end of the cycle unless it is
an injection channel. -/
theorem vacate (h : N.NoChainCycle sel f cy f') {m : C × C × P} (hm : m ∈ cy.hops)
    (hinj : ∀ p, (m.1, p) ∉ N.inject) : f' m.1 = none := by
  obtain ⟨p, hp, -, -, -⟩ := h.hop m hm
  have hpost : cy.post f m.1 = none := by
    refine simulApply_of_src (a := .hop m.1 m.2.1 m.2.2) (List.mem_map.2 ⟨m, hm, rfl⟩) rfl
      fun b hb e => ?_
    obtain ⟨m', hm', rfl⟩ := List.mem_map.1 hb
    simp only [Act.tgt, Option.some.injEq] at e
    obtain ⟨-, -, -, hfree, -⟩ := h.hop m' hm'
    rw [e, hp] at hfree
    simp at hfree
  rw [h.eq_post fun q hq e => hinj q.2 (by rw [← e]; exact (h.inject q hq).1)]
  exact hpost

/-- A packet that does not leave its channel stays there. -/
theorem stay (h : N.NoChainCycle sel f cy f') {c : C} {p : P} (hc : f c = some p)
    (hl : ¬ cy.Leaves c) : f' c = some p := by
  have he : c ∉ cy.ejects := fun he => hl (Or.inl he)
  have hmid : cy.mid f c = some p := by rw [Cycle.mid_of_not_mem_ejects he, hc]
  have hpost : cy.post f c = some p := by
    rw [Cycle.post, simulApply_of_not fun b hb => ?_]
    · exact hmid
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hb
    refine ⟨fun e => hl (Or.inr ⟨m.2.1, m.2.2, ?_⟩), fun e => ?_⟩
    · simp only [Act.src, Option.some.injEq] at e
      subst e
      exact hm
    · simp only [Act.tgt, Option.some.injEq] at e
      obtain ⟨-, -, -, hfree, -⟩ := h.hop m hm
      rw [e, hmid] at hfree
      simp at hfree
  rw [h.eq_post fun q hq e => by
    have := (h.inject q hq).2
    rw [e, hpost] at this
    simp at this]
  exact hpost

/-- The header of a hop is offered to the packet the source channel holds at the start of the
cycle. -/
theorem hop_spec (h : N.NoChainCycle sel f cy f') {m : C × C × P} (hm : m ∈ cy.hops) {p : P}
    (hp : f m.1 = some p) : N.arrived m.1 p = false ∧ ∃ g, (m.2.1, m.2.2) ∈ sel g m.1 p := by
  obtain ⟨p', hp', harr, -, g, hg⟩ := h.hop m hm
  have he : m.1 ∉ cy.ejects := fun he => by rw [Cycle.mid_of_mem_ejects he] at hp'; simp at hp'
  rw [Cycle.mid_of_not_mem_ejects he, hp] at hp'
  cases hp'
  exact ⟨harr, g, hg⟩

end NoChainCycle

namespace CycleRun

variable {M : Selection C P → Config C P → Cycle C P → Config C P → Prop}
  {ok : Selection C P → Prop}

/-- In cycle `n` the packet held in `c` **may leave**: it has arrived, or the selection in force,
evaluated at the start of the move phase, offers it a hop into a channel free there. -/
def MayLeave (N : Network C P) (r : CycleRun M ok) (n : ℕ) (c : C) : Prop :=
  ∃ p, r.st n c = some p ∧ (N.arrived c p = true ∨
    ∃ q ∈ r.sel n ((r.cyc n).mid (r.st n)) c p, (r.cyc n).mid (r.st n) q.1 = none)

/-- **Cycle-level channel fairness**: for every channel, if infinitely often its packet may leave
in a cycle, then infinitely often a packet leaves it.  This is a property of the arbiter (a
round-robin or oldest-first arbiter among the requests it sees); it is not implied by the
fairness of the interleaving of single steps. -/
def ChannelFair (N : Network C P) (r : CycleRun M ok) : Prop :=
  ∀ c, LTS.InfOften (fun n => r.MayLeave N n c) → LTS.InfOften (fun n => (r.cyc n).Leaves c)

/-- The packet in channel `c` at the start of cycle `n` is eventually ejected: it is ejected in
cycle `n`, or hops on in cycle `n` and is then delivered, or stays and is delivered later. -/
inductive Delivered (r : CycleRun M ok) : ℕ → C → Prop
  | eject {n : ℕ} {c : C} : c ∈ (r.cyc n).ejects → Delivered r n c
  | hop {n : ℕ} {c c' : C} {p' : P} : (c, c', p') ∈ (r.cyc n).hops → Delivered r (n + 1) c' →
      Delivered r n c
  | wait {n : ℕ} {c : C} : ¬ (r.cyc n).Leaves c → Delivered r (n + 1) c → Delivered r n c

variable (r : CycleRun N.NoChainCycle ok)

/-- A packet that never leaves `c` after cycle `n` stays in `c`. -/
theorem stay_of_not_leave {n : ℕ} {c : C} {p : P} (hp : r.st n c = some p)
    (hne : ∀ m, n ≤ m → ¬ (r.cyc m).Leaves c) : ∀ m, n ≤ m → r.st m c = some p := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => exact hp
  | succ d ih => exact (r.step (n + d)).stay (ih (by omega)) (hne _ (by omega))

/-- **No packet outside the sources waits for ever in the no-chaining model**, along every run
that is channel fair at the cycle level, whatever the injections.  The escape channel of a
blocked packet is free at the start of the move phase infinitely often (by induction along the
escape dependencies: its occupant leaves, and a vacated escape channel is neither re-entered in
the same cycle nor refilled by an injection), and then the selection in force offers the packet
a free hop. -/
theorem exists_leave {legal : C → P → Prop} (hcl : N.Closed legal) {R₁ : C → P → List (C × P)}
    {src : C → Prop} (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (hR₁inj : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ∀ p', (q.1, p') ∉ N.inject)
    (hfair : r.ChannelFair N) :
    ∀ c, ¬ src c → ∀ n p, r.st n c = some p → ∃ m, n ≤ m ∧ (r.cyc m).Leaves c := by
  have hM : N.Sequential N.NoChainCycle ok := noChain_sequential fun σ h => (hok σ h).sub
  intro c
  refine hwf.induction (C := fun c => ¬ src c → ∀ n p, r.st n c = some p →
    ∃ m, n ≤ m ∧ (r.cyc m).Leaves c) c ?_
  intro c ih hsc n p hp
  by_contra hne
  push Not at hne
  have hstay := r.stay_of_not_leave hp hne
  suffices hen : LTS.InfOften (fun m => r.MayLeave N m c) by
    obtain ⟨m, hm, hl⟩ := hfair c hen n
    exact hne m hm hl
  have hl : legal c p := r.legal hcl hM n c p hp
  cases harr : N.arrived c p with
  | true =>
    intro M
    exact ⟨max M n, le_max_left _ _, p, hstay _ (le_max_right _ _), Or.inl harr⟩
  | false =>
    obtain ⟨⟨c', p'⟩, hq⟩ := List.exists_mem_of_ne_nil _ (hconn c p hl harr)
    have hsc' : ¬ src c' := hR₁ c p _ hl harr hq
    have hfree : ∀ M, ∃ m, M ≤ m ∧ n ≤ m ∧ (r.cyc m).mid (r.st m) c' = none := by
      intro M
      cases h' : r.st (max M n) c' with
      | none => exact ⟨max M n, le_max_left _ _, le_max_right _ _, Cycle.mid_of_none h'⟩
      | some p'' =>
        obtain ⟨m, hm, hlm⟩ := ih c' ⟨p, p', hl, harr, hq⟩ hsc' _ p'' h'
        rcases hlm with he | ⟨c₃, p₃, hh⟩
        · exact ⟨m, by omega, by omega, Cycle.mid_of_mem_ejects he⟩
        · refine ⟨m + 1, by omega, by omega, Cycle.mid_of_none ?_⟩
          exact (r.step m).vacate (m := (c', c₃, p₃)) hh (hR₁inj c p _ hl harr hq)
    intro M
    obtain ⟨m, hMm, hnm, hm⟩ := hfree M
    have hpm := hstay m hnm
    have hmid := (r.step m).mid_of_some hpm harr
    obtain ⟨⟨c'', p''⟩, hq', hfree'⟩ := (hok _ (r.sel_ok m)).conserving _ c p hl harr hsc hmid
      ⟨(c', p'), hq, hm⟩
    exact ⟨m, hMm, p, hpm, Or.inr ⟨_, hq', hfree'⟩⟩

/-- Waiting `d` cycles without leaving, then being delivered, is being delivered. -/
theorem delivered_of_wait {c : C} :
    ∀ d n, (∀ k, n ≤ k → k < n + d → ¬ (r.cyc k).Leaves c) → r.Delivered (n + d) c →
      r.Delivered n c
  | 0, _, _, h => h
  | d + 1, n, hstay, h => by
    have h' : r.Delivered (n + 1) c :=
      delivered_of_wait d (n + 1) (fun k hk hk' => hstay k (by omega) (by omega))
        (by rwa [show n + 1 + d = n + (d + 1) by omega])
    exact Delivered.wait (hstay n le_rfl (by omega)) h'

/-- **Delivery under load in the no-chaining model.**  With a closed legal set, a connected escape
subfunction `R₁` with a well-founded dependency graph and no escape hop into a source or into an
injection channel, no hop at all into a source, a ranking function decreasing on every hop, and
every admissible selection satisfying `SourceSelOn legal R₁ src`: along every run of the
no-chaining model that is channel fair at the cycle level, with injections going on for ever,
every packet held in a channel outside the sources is delivered. -/
theorem delivered_of_channelFair {legal : C → P → Prop} (hcl : N.Closed legal)
    {R₁ : C → P → List (C × P)} {src : C → Prop} (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (hR₁inj : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ∀ p', (q.1, p') ∉ N.inject)
    (hsrc : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (hfair : r.ChannelFair N) : ∀ n c, ¬ src c → r.st n c ≠ none → r.Delivered n c := by
  have hM : N.Sequential N.NoChainCycle ok := noChain_sequential fun σ h => (hok σ h).sub
  have hleave := r.exists_leave hcl hok hconn hwf hR₁ hR₁inj hfair
  suffices key : ∀ k n c p, rk c p = k → ¬ src c → r.st n c = some p → r.Delivered n c by
    intro n c hs hc
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hc
    exact key _ n c p rfl hs hp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n c p hk hs hp
    have hex := hleave c hs n p hp
    classical
    let m := Nat.find hex
    have hm : n ≤ m ∧ (r.cyc m).Leaves c := Nat.find_spec hex
    have hbefore : ∀ k, n ≤ k → k < m → ¬ (r.cyc k).Leaves c := fun k hk hkm hl =>
      Nat.find_min hex hkm ⟨hk, hl⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm.1
    have hstay : ∀ e, e ≤ d → r.st (n + e) c = some p := by
      intro e
      induction e with
      | zero => intro; exact hp
      | succ e ih' =>
        intro he
        exact (r.step (n + e)).stay (ih' (by omega)) (hbefore _ (by omega) (by omega))
    have hpm : r.st m c = some p := hd ▸ hstay d le_rfl
    refine r.delivered_of_wait d n (fun k hk hk' => hbefore k hk (by omega)) ?_
    rw [← hd]
    rcases hm.2 with he | ⟨c', p', hh⟩
    · exact Delivered.eject he
    · refine Delivered.hop hh ?_
      obtain ⟨harr, g, hg⟩ := (r.step m).hop_spec (m := (c, c', p')) hh hpm
      have hl := r.legal hcl hM m c p hpm
      have hq := (hok _ (r.sel_ok m)).sub _ _ _ _ hg
      exact ih _ (hk ▸ hrk c p (c', p') hl harr hq) (m + 1) c' p' rfl (hsrc c p _ hl harr hq)
        ((r.step m).land (m := (c, c', p')) hh)

end CycleRun

end Delivery

/-! ### The guarantees, bundled -/

section Bundle

variable [DecidableEq C] (N : Network C P)

/-- **The safety guarantees of a cycle model** `M` (`Network.NoChainCycle` or
`Network.SeqCycle`) for the admissible selections `ok`, on the legal pairs `legal`:

* `legal_st` : every configuration at the start of a cycle is legal;
* `progress` : **no deadlock** — a work-conserving cycle in a non-empty configuration moves some
  packet;
* `livelock` : **no livelock** — once injections stop for good, the network eventually stops
  moving for good;
* `drain` : **bounded drain** — some `B` (the potential bound) such that `B` work-conserving
  cycles without injections empty the network, from every cycle of every run;
* `hops` : every hop of every cycle is a routing step from a legal pair, so the hop bounds of
  the routing function hold for every packet. -/
structure CycleSafe (M : Selection C P → Config C P → Cycle C P → Config C P → Prop)
    (legal : C → P → Prop) (ok : Selection C P → Prop) : Prop where
  legal_st : ∀ r : CycleRun M ok, ∀ n, Legal legal (r.st n)
  progress : ∀ r : CycleRun M ok, ∀ n, r.st n ≠ empty →
    N.WorkConserving (r.sel n) (r.st n) (r.cyc n) → 0 < (r.cyc n).moves
  livelock : ∀ r : CycleRun M ok, ∀ n, (∀ m, n ≤ m → (r.cyc m).injects = []) →
    ∃ m, n ≤ m ∧ ∀ m', m ≤ m' → (r.cyc m').moves = 0
  drain : ∃ B, ∀ r : CycleRun M ok, ∀ n, (∀ i < B, (r.cyc (n + i)).injects = [] ∧
    N.WorkConserving (r.sel (n + i)) (r.st (n + i)) (r.cyc (n + i))) → r.st (n + B) = empty
  hops : ∀ r : CycleRun M ok, ∀ n, ∀ m ∈ (r.cyc n).hops,
    ∃ p, legal m.1 p ∧ N.PacketStep (m.1, p) (m.2.1, m.2.2)

variable {N}

/-- **Cycle models are safe** when the single-step semantics is: with a closed legal set with
finitely many pairs, a connected escape subfunction with a well-founded dependency graph and no
escape hop into a throttled source, a ranking function decreasing on every hop, every admissible
selection satisfying `SourceSelOn legal R₁ src`, and a cycle model whose cycles are sequences of
single steps (both models are: `noChain_sequential`, `seq_sequential`). -/
theorem cycleSafe {M : Selection C P → Config C P → Cycle C P → Config C P → Prop}
    {ok : Selection C P → Prop} {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) (R₁ : C → P → List (C × P)) {src : C → Prop}
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ) (hM : N.Sequential M ok) :
    N.CycleSafe M legal ok := by
  have hchan : {c | ∃ p, legal c p}.Finite :=
    (hfin.image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩
  have hS : ∀ c p, legal c p → c ∈ hchan.toFinset := fun c p h => hchan.mem_toFinset.2 ⟨p, h⟩
  have hT : ∀ q : C × P, legal q.1 q.2 → q ∈ hfin.toFinset := fun q h => hfin.mem_toFinset.2 h
  refine ⟨fun r n => r.legal hcl hM n, fun r n hne hwc => hwc.moves_pos (hok _ (r.sel_ok n)) hconn
    hwf hR₁ (r.legal hcl hM n) hne, fun r n hinj => r.eventually_idle hcl hS rk hrk hM n hinj,
    ⟨∑ q ∈ hfin.toFinset, (rk q.1 q.2 + 1), fun r n hq => r.drain hcl hS hok hconn hwf hR₁ rk hrk
      hM n _ (pot_le_bound hT rk (r.legal hcl hM n)) hq⟩,
    fun r n m hm => r.hop_packetStep hcl hM hm⟩

end Bundle

/-! ### The interleaving of a run of cycles -/

section Flatten

variable [DecidableEq C] {N : Network C P}

/-- The configuration reached by performing the first `j` actions of `as` from `g`. -/
def applyN (g : Config C P) (as : List (Act C P)) (j : ℕ) : Config C P :=
  (as.take j).foldl (fun g a => a.apply g) g

/-- A path, action by action. -/
theorem path_steps {S : Selection C P} : ∀ {g g' : Config C P} {as : List (Act C P)},
    (N.ltsWith S).Path g as g' →
      (∀ j (hj : j < as.length), N.StepWith S (applyN g as j) as[j] (applyN g as (j + 1))) ∧
        applyN g as as.length = g'
  | _, _, [], .nil _ => ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), rfl⟩
  | g, _, a :: as, .cons hst hrest => by
    have e := StepWith.eq_apply hst
    subst e
    obtain ⟨ih, hlast⟩ := path_steps hrest
    refine ⟨fun j hj => ?_, hlast⟩
    cases j with
    | zero => exact hst
    | succ j => exact ih j (by simpa using hj)

theorem path_nil_eq {S : Selection C P} {g g' : Config C P}
    (h : (N.ltsWith S).Path g [] g') : g' = g := by
  cases h; rfl

variable {M : Selection C P → Config C P → Cycle C P → Config C P → Prop}
  {ok ok' : Selection C P → Prop} (r : CycleRun M ok) (τ : ℕ → Selection C P)
  (hτ : ∀ n, ok' (τ n)) (hP : ∀ n, (N.ltsWith (τ n)).Path (r.st n) (r.cyc n).acts (r.st (n + 1)))
  (hinf : ∀ n, ∃ m, n ≤ m ∧ (r.cyc m).acts ≠ [])

namespace CycleRun

/-- The first cycle from `n` on in which something happens. -/
noncomputable def nextNE (n : ℕ) : ℕ := by
  classical exact Nat.find (hinf n)

omit [DecidableEq C] in
include hinf in
theorem nextNE_spec (n : ℕ) : n ≤ r.nextNE hinf n ∧ (r.cyc (r.nextNE hinf n)).acts ≠ [] := by
  classical exact Nat.find_spec (hinf n)

omit [DecidableEq C] in
include hinf in
theorem nextNE_min {n i : ℕ} (hi : n ≤ i) (hlt : i < r.nextNE hinf n) : (r.cyc i).acts = [] := by
  classical
  by_contra h
  exact Nat.find_min (hinf n) hlt ⟨hi, h⟩

include hP in
/-- Nothing happens in cycles `a, …, b - 1`: the configuration is unchanged. -/
theorem st_eq_of_idle {a : ℕ} : ∀ d, (∀ i, a ≤ i → i < a + d → (r.cyc i).acts = []) →
    r.st (a + d) = r.st a
  | 0, _ => rfl
  | d + 1, h => by
    have := st_eq_of_idle d fun i hi hi' => h i hi (by omega)
    have hp := hP (a + d)
    rw [h (a + d) (by omega) (by omega)] at hp
    rw [show a + (d + 1) = a + d + 1 by omega, path_nil_eq hp, this]

include hP in
theorem st_nextNE (n : ℕ) : r.st (r.nextNE hinf n) = r.st n := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (r.nextNE_spec hinf n).1
  rw [hd]
  exact r.st_eq_of_idle τ hP d fun i hi hi' => r.nextNE_min hinf hi (by omega)

/-- One step of the position (cycle, index of the action within the cycle). -/
noncomputable def adv (q : ℕ × ℕ) : ℕ × ℕ :=
  if q.2 + 1 < (r.cyc q.1).acts.length then (q.1, q.2 + 1) else (r.nextNE hinf (q.1 + 1), 0)

/-- The position of step `k` of the interleaving. -/
noncomputable def pos : ℕ → ℕ × ℕ
  | 0 => (r.nextNE hinf 0, 0)
  | k + 1 => r.adv hinf (pos k)

omit [DecidableEq C] in
theorem pos_lt (k : ℕ) : (r.pos hinf k).2 < (r.cyc (r.pos hinf k).1).acts.length := by
  induction k with
  | zero => exact List.length_pos_iff.2 (r.nextNE_spec hinf 0).2
  | succ k ih =>
    simp only [pos, adv]
    split_ifs with h
    · exact h
    · exact List.length_pos_iff.2 (r.nextNE_spec hinf _).2

/-- **The interleaving of a run of cycles**: the actions of the cycles one after another, each
step under the selection `τ n` of its cycle `n` (the selection in force for the sequential model,
the frozen selection or the adaptive one for the no-chaining model).  It needs infinitely many
cycles in which something happens. -/
noncomputable def flatten : N.SelRun ok' where
  st k := applyN (r.st (r.pos hinf k).1) (r.cyc (r.pos hinf k).1).acts (r.pos hinf k).2
  lab k := (r.cyc (r.pos hinf k).1).acts[(r.pos hinf k).2]'(r.pos_lt hinf k)
  sel k := τ (r.pos hinf k).1
  start := by
    simp only [pos, applyN, List.take_zero, List.foldl_nil]
    rw [r.st_nextNE τ hP hinf 0, r.start]
  sel_ok k := hτ _
  step k := by
    obtain ⟨hsteps, hlast⟩ := path_steps (hP (r.pos hinf k).1)
    have h := hsteps _ (r.pos_lt hinf k)
    simp only [pos, adv]
    split_ifs with hlt
    · exact h
    · have hj : (r.pos hinf k).2 + 1 = (r.cyc (r.pos hinf k).1).acts.length := by
        have := r.pos_lt hinf k; omega
      rw [hj, hlast] at h
      simp only [applyN, List.take_zero, List.foldl_nil]
      rw [r.st_nextNE τ hP hinf]
      exact h

omit [DecidableEq C] in
/-- Inside a cycle, the position advances by one action per step. -/
theorem pos_add {k n j : ℕ} (hk : r.pos hinf k = (n, j)) :
    ∀ d, j + d < (r.cyc n).acts.length → r.pos hinf (k + d) = (n, j + d)
  | 0, _ => hk
  | d + 1, h => by
    have ih := pos_add hk d (by omega)
    rw [show k + (d + 1) = k + d + 1 by omega]
    have hc : j + d + 1 < (r.cyc n).acts.length := by omega
    simp only [pos, adv, ih, hc, ↓reduceIte]
    rfl

omit [DecidableEq C] in
/-- **The interleaving reaches the start of every busy cycle.** -/
theorem exists_pos (n : ℕ) : ∃ k, r.pos hinf k = (r.nextNE hinf n, 0) := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨hle, hne⟩ := r.nextNE_spec hinf n
    rcases Nat.lt_or_ge n (r.nextNE hinf n) with hlt | hge
    · -- cycle `n` is idle: the next busy cycle from `n + 1` is the same
      have : r.nextNE hinf (n + 1) = r.nextNE hinf n := by
        classical
        refine le_antisymm ?_ ?_
        · exact Nat.find_min' (hinf (n + 1)) ⟨by omega, hne⟩
        · obtain ⟨h1, h2⟩ := r.nextNE_spec hinf (n + 1)
          exact Nat.find_min' (hinf n) ⟨by omega, h2⟩
      exact ⟨k, by rw [this, hk]⟩
    · have hn : r.nextNE hinf n = n := by omega
      rw [hn] at hk hne
      have hlen := List.length_pos_iff.2 hne
      refine ⟨k + ((r.cyc n).acts.length - 1) + 1, ?_⟩
      have h := r.pos_add hinf hk ((r.cyc n).acts.length - 1) (by omega)
      have hc : ¬ (((r.cyc n).acts.length - 1 + 1) < (r.cyc n).acts.length) := by omega
      simp only [pos, adv, h, Nat.zero_add, hc, ↓reduceIte]

include hP in
/-- Every configuration at the start of a cycle is a configuration of the interleaving. -/
theorem exists_flatten_st (n : ℕ) : ∃ k, (r.flatten τ hτ hP hinf).st k = r.st n := by
  obtain ⟨k, hk⟩ := r.exists_pos hinf n
  refine ⟨k, ?_⟩
  change applyN _ _ _ = _
  rw [hk]
  simp only [applyN, List.take_zero, List.foldl_nil]
  exact r.st_nextNE τ hP hinf n

end CycleRun

end Flatten

/-! ### Delivery under fairness of the interleaving -/

section Transfer

variable [DecidableEq C] {N : Network C P} {ok : Selection C P → Prop}

namespace CycleRun

/-- The interleaving of a run of the sequential model: a run under the time-varying selection,
each step under the selection in force in its cycle. -/
noncomputable abbrev seqFlatten (r : CycleRun N.SeqCycle ok)
    (hinf : ∀ n, ∃ m, n ≤ m ∧ (r.cyc m).acts ≠ []) : N.SelRun ok :=
  r.flatten r.sel r.sel_ok (fun n => (r.step n).path) hinf

/-- **Delivery under load in the sequential model**: when the interleaving of the cycles is
channel fair relative to the selection in force (`Network.SelRun.ChannelFair`), every packet
held outside the sources at the start of a cycle is delivered — `SelRun.delivered_of_channelFair`
applies verbatim, since a sequential cycle is literally a sequence of steps under the selection in
force. -/
theorem seq_delivered_of_channelFair {legal : C → P → Prop} (hcl : N.Closed legal)
    {R₁ : C → P → List (C × P)} {src : C → Prop} (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (hsrc : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (r : CycleRun N.SeqCycle ok) (hinf : ∀ n, ∃ m, n ≤ m ∧ (r.cyc m).acts ≠ [])
    (hfair : (r.seqFlatten hinf).ChannelFair) (n : ℕ) (c : C) (hs : ¬ src c)
    (hc : r.st n c ≠ none) :
    ∃ k, (r.seqFlatten hinf).st k = r.st n ∧ (r.seqFlatten hinf).Delivered k c := by
  obtain ⟨k, hk⟩ := r.exists_flatten_st r.sel r.sel_ok (fun n => (r.step n).path) hinf n
  exact ⟨k, hk, SelRun.delivered_of_channelFair hcl hok hconn hwf hR₁ hsrc rk hrk _ hfair k c hs
    (by rw [hk]; exact hc)⟩

/-- **Starvation freedom in the sequential model**: with finitely many legal pairs, when the
interleaving is strongly fair relative to the selection in force, every packet is delivered,
those held back at a source included. -/
theorem seq_delivered_of_stronglyFair {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) {R₁ : C → P → List (C × P)} {src : C → Prop}
    (hok : ∀ σ, ok σ → N.SourceSelOn legal R₁ src σ)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (r : CycleRun N.SeqCycle ok) (hinf : ∀ n, ∃ m, n ≤ m ∧ (r.cyc m).acts ≠ [])
    (hfair : (r.seqFlatten hinf).StronglyFair) (n : ℕ) (c : C) (hc : r.st n c ≠ none) :
    ∃ k, (r.seqFlatten hinf).st k = r.st n ∧ (r.seqFlatten hinf).Delivered k c := by
  obtain ⟨k, hk⟩ := r.exists_flatten_st r.sel r.sel_ok (fun n => (r.step n).path) hinf n
  exact ⟨k, hk, SelRun.delivered_of_stronglyFair hcl hfin hok hconn hwf hR₁ rk hrk _ hfair k c
    (by rw [hk]; exact hc)⟩

/-- The interleaving of a run of the no-chaining model, as a run of the fully adaptive network. -/
noncomputable abbrev noChainFlatten (r : CycleRun N.NoChainCycle ok)
    (hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p)
    (hinf : ∀ n, ∃ m, n ≤ m ∧ (r.cyc m).acts ≠ []) : N.SelRun (· = N.adaptive) :=
  r.flatten (fun _ => N.adaptive) (fun _ => rfl) (fun n => (r.step n).path (hsub _ (r.sel_ok n)))
    hinf

/-- **Delivery in the no-chaining model under fairness of the interleaving**: if the
interleaving of the cycles is channel fair *relative to the fully adaptive selection* (whenever a
permitted hop out of a channel into a free channel exists infinitely often, a packet leaves it
infinitely often), every packet is delivered.  This hypothesis is stronger than
`CycleRun.ChannelFair`: it ignores what the selection in force offers, which is why
`CycleRun.delivered_of_channelFair` is the theorem to use for selections that decline hops. -/
theorem noChain_delivered_of_interleaving {legal : C → P → Prop} (hcl : N.Closed legal)
    {R₁ : C → P → List (C × P)} (hR : ∀ c p q, q ∈ R₁ c p → q ∈ N.route c p)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁))) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    (r : CycleRun N.NoChainCycle ok)
    (hsub : ∀ σ, ok σ → ∀ f c p q, q ∈ σ f c p → q ∈ N.route c p)
    (hinf : ∀ n, ∃ m, n ≤ m ∧ (r.cyc m).acts ≠ [])
    (hfair : (r.noChainFlatten hsub hinf).ChannelFair) (n : ℕ) (c : C) (hc : r.st n c ≠ none) :
    ∃ k, (r.noChainFlatten hsub hinf).st k = r.st n ∧
      (r.noChainFlatten hsub hinf).Delivered k c := by
  obtain ⟨k, hk⟩ := r.exists_flatten_st (fun _ => N.adaptive) (fun _ => rfl)
    (fun n => (r.step n).path (hsub _ (r.sel_ok n))) hinf n
  have hk' : (r.noChainFlatten hsub hinf).st k = r.st n := hk
  refine ⟨k, hk', SelRun.delivered_of_channelFair (src := fun _ => False) hcl
    (fun σ hσ => ?_) hconn hwf (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h) rk hrk _ hfair k c
    not_false (by rw [hk']; exact hc)⟩
  subst hσ
  exact (ValidSel.escapeSel N N.adaptive_valid hR).sourceSelOn _ _

end CycleRun

end Transfer

end Network

end AsyncLean
