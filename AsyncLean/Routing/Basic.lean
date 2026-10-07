/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.LTS.Properties
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Finite.Basic

/-!
# Interconnection networks with dynamic routing

This file models a packet-switched interconnection network (a network on chip, a
multiprocessor interconnect, an asynchronous router mesh) whose packets are routed
*dynamically*: the routing function offers each packet a set of permitted next hops, and
which one is taken is decided at run time by a selection function that may look at the
whole state of the network (for example, it takes the least congested free channel).  It
proves that such a network can neither **deadlock** nor **livelock**, for *every*
work-conserving selection function at once.

## The model

* `Network C P` has channels `C` (each with a one-packet buffer: store-and-forward or
  virtual cut-through switching; a virtual channel is a channel of its own) and packet
  headers `P` (a destination, possibly with extra routing state such as a virtual-channel
  class, a dateline bit or a misrouting budget).  `route c p` lists the permitted hops of a
  packet with header `p` held in channel `c`, each with the header it carries on; adaptive
  routing offers several.  `arrived c p` says the packet is at its destination and may be
  ejected, and `inject` lists the packets the sources may inject.
* A `Selection` chooses, in each configuration, which of the permitted hops a packet may
  take now.  `ValidSel` asks that it only offers permitted hops and is *work conserving*:
  if a permitted channel is free, it offers a free one.  `adaptive` offers every permitted
  hop; `freeOnly` and `firstFree` are typical congestion-aware policies.
* `N.ltsWith sel` is the network as a transition system on configurations
  (`Config C P := C → Option P`): inject a packet into a free channel, forward a packet to
  a free channel offered by `sel`, or eject an arrived packet.

## The properties

* `DeadlockFree` : whatever the selection, whenever the network holds a packet some packet
  can move (be forwarded or ejected).  Together with livelock freedom this means the
  network always *drains*: `Correct.inevitablyEmpty`.
* `LivelockFree` : whatever the selection, there is no infinite run in which no new packet
  is injected: packets cannot keep moving forever without reaching their destinations.
* `PacketLivelockFree` : no injected packet can be routed forever (a property of the routing
  function alone; `packet_hops_le` bounds the number of hops of every packet).
* `Correct := DeadlockFree ∧ LivelockFree`.

## Main results

* `deadlockFree_of_escape` — **Duato's theorem**: if a routing subfunction (the *escape
  channels*) is connected and its channel dependency graph is acyclic, the fully adaptive
  network is deadlock free, even though the dependency graph of the full routing function
  may have cycles.
* `deadlockFreeWith_of_escape`, `livelockFreeWith_of_ranking` — the same for selection
  functions that may decline adaptive hops (`EscapeSel`: they never refuse a free escape hop),
  such as the congestion-aware `gatedSel`.
* `deadlockFree_of_cdg` — **Dally and Seitz's theorem**: an acyclic channel dependency
  graph rules out deadlock.
* `livelockFree_of_ranking`, `packetLivelockFree_of_ranking` — a ranking function that
  decreases on every permitted hop (the distance for minimal routing; distance plus a
  misrouting budget for bounded non-minimal routing) rules out livelock.
* `Correct.inevitablyEmpty`, `Correct.drain` — in a correct network every run without new
  injections ends with the network empty: every packet is delivered.
* `deadlockFree_iff_adaptive`, `livelockFree_iff_adaptive` — it suffices to consider the
  most nondeterministic selection `adaptive`; the results then hold for every policy.
* `packet_hops_eq` — when every hop decreases the ranking by exactly one (the distance, for
  minimal routing), every packet takes exactly that many hops.
* `wf_of_acyclic`, `wf_of_rank`, `wf_of_lexRank` — acyclicity of a dependency graph on finitely
  many channels, or a (lexicographic) numbering of the channels, gives the well-foundedness the
  theorems ask for.
* `staticDeadlockFree_iff_exists_escape`, `deadlockFree_iff_exists_escape` — Duato's condition
  is also **necessary**: when finitely many channels carry legal packets, every configuration
  of legal packets can move iff some connected routing subfunction has an acyclic dependency
  graph.

Starvation freedom under fair scheduling is in `AsyncLean.Routing.Fairness`, wormhole switching
in `AsyncLean.Routing.Wormhole`.

## Refutation

`runB` executes a list of actions on a list of occupied channels.
`not_deadlockFree_of_refuteB` turns a run that ends with every packet blocked into a proof
of `¬ DeadlockFree`; `not_livelockFree_of_refuteB` turns a cycle of moves back to a reachable
configuration into a proof of `¬ LivelockFree`.  Both checks are decided by the kernel.
-/

namespace AsyncLean

/-- An interconnection network with a (possibly adaptive) routing function.  Channels `C`
hold one packet each; packets carry a header `P`. -/
structure Network (C P : Type*) where
  /-- A packet with header `p` held in channel `c` has reached its destination. -/
  arrived : C → P → Bool
  /-- The permitted hops of a packet with header `p` in channel `c`: the next channel and
  the header the packet carries on.  Adaptive routing offers several. -/
  route : C → P → List (C × P)
  /-- The packets the sources may inject: the channel they enter and their header. -/
  inject : List (C × P)

namespace Network

variable {C P : Type*}

/-- A configuration: the header of the packet held in each channel, if any. -/
abbrev Config (C P : Type*) := C → Option P

/-- The empty network. -/
def empty : Config C P := fun _ => none

/-- A selection function: given the whole configuration, which of the permitted hops a
packet with header `p` in channel `c` may take now.  This is the *dynamic* part of adaptive
routing. -/
abbrev Selection (C P : Type*) := Config C P → C → P → List (C × P)

/-- The actions of a network. -/
inductive Act (C P : Type*) where
  /-- Inject a packet with header `p` into channel `c`. -/
  | inject (c : C) (p : P)
  /-- Forward the packet in channel `c` to channel `c'`, where it carries header `p'`. -/
  | hop (c c' : C) (p' : P)
  /-- Eject the (arrived) packet in channel `c`. -/
  | eject (c : C)
  deriving DecidableEq, Repr

/-- The action moves a packet already in the network (it is not an injection). -/
def Act.isMove : Act C P → Bool
  | .inject _ _ => false
  | _ => true

/-- The action moves a packet already in the network.  These are the "internal" actions for
livelock: a livelock is an infinite run without new injections. -/
def Act.IsMove (a : Act C P) : Prop := a.isMove = true

@[simp] theorem Act.isMove_inject (c : C) (p : P) : (Act.inject c p).isMove = false := rfl
@[simp] theorem Act.isMove_hop (c c' : C) (p' : P) : (Act.hop c c' p').isMove = true := rfl
@[simp] theorem Act.isMove_eject (c : C) : (Act.eject (P := P) c).isMove = true := rfl

variable (N : Network C P)

/-- One routing step of a single packet: from `q` it may go to `q'`. -/
def PacketStep (q q' : C × P) : Prop := N.arrived q.1 q.2 = false ∧ q' ∈ N.route q.1 q.2

/-- The route of a single packet as a transition system (all steps are internal). -/
def packetLTS : LTS (C × P) Unit where
  step q _ q' := N.PacketStep q q'

/-- No injected packet can be routed forever: every route from an injection reaches a pair
where the packet has arrived (or has no permitted hop). -/
def PacketLivelockFree : Prop :=
  ∀ q ∈ N.inject, N.packetLTS.LivelockFree (fun _ => True) q

/-- The channel dependency graph of the routing (sub)function `R` restricted to the pairs
satisfying `legal`: `Dep legal R c c'` iff a packet in `c` may request channel `c'`. -/
def Dep (legal : C → P → Prop) (R : C → P → List (C × P)) (c c' : C) : Prop :=
  ∃ p p', legal c p ∧ N.arrived c p = false ∧ (c', p') ∈ R c p

/-- `legal` contains every injected packet and is closed under routing: it
over-approximates the pairs a packet can occupy. -/
structure Closed (legal : C → P → Prop) : Prop where
  inject : ∀ q ∈ N.inject, legal q.1 q.2
  route : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → legal q.1 q.2

/-- Every packet of `f` is in a legal pair. -/
def Legal (legal : C → P → Prop) (f : Config C P) : Prop := ∀ c p, f c = some p → legal c p

section Semantics

variable [DecidableEq C]

/-- The steps of the network when packets are forwarded to the hops offered by `sel`. -/
inductive StepWith (sel : Selection C P) : Config C P → Act C P → Config C P → Prop
  | inject {f : Config C P} {c : C} {p : P} : (c, p) ∈ N.inject → f c = none →
      StepWith sel f (.inject c p) (Function.update f c (some p))
  | hop {f : Config C P} {c c' : C} {p p' : P} : f c = some p → N.arrived c p = false →
      (c', p') ∈ sel f c p → f c' = none →
      StepWith sel f (.hop c c' p') (Function.update (Function.update f c none) c' (some p'))
  | eject {f : Config C P} {c : C} {p : P} : f c = some p → N.arrived c p = true →
      StepWith sel f (.eject c) (Function.update f c none)

/-- The network as a transition system, under the selection function `sel`. -/
def ltsWith (sel : Selection C P) : LTS (Config C P) (Act C P) where
  step := N.StepWith sel

/-- The most nondeterministic selection: every permitted hop may be taken. -/
def adaptive : Selection C P := fun _ => N.route

/-- The network under fully adaptive routing. -/
abbrev lts : LTS (Config C P) (Act C P) := N.ltsWith N.adaptive

/-- `sel` is a valid selection function: it only offers permitted hops, and it is work
conserving — if a permitted channel is free, it offers a free channel. -/
structure ValidSel (sel : Selection C P) : Prop where
  sub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p
  conserving : ∀ f c p, f c = some p → (∃ q ∈ N.route c p, f q.1 = none) →
    ∃ q ∈ sel f c p, f q.1 = none

/-- **Duato's condition on a selection function** for the escape subfunction `R₁`: it only
offers permitted hops, and whenever an escape hop is free it offers a free hop.  Unlike
`ValidSel`, it may decline free adaptive hops, for example when the routers ahead are congested.
Duato's theorem only needs this (`deadlockFreeWith_of_escape`). -/
structure EscapeSel (R₁ : C → P → List (C × P)) (sel : Selection C P) : Prop where
  sub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p
  conserving : ∀ f c p, f c = some p → (∃ q ∈ R₁ c p, f q.1 = none) →
    ∃ q ∈ sel f c p, f q.1 = none

/-- Some packet of `f` can move. -/
def Movable (sel : Selection C P) (f : Config C P) : Prop :=
  ∃ a f', a.IsMove ∧ (N.ltsWith sel).step f a f'

/-- Under `sel`, whenever the network holds a packet, some packet can move. -/
def DeadlockFreeWith (sel : Selection C P) : Prop :=
  ∀ f, (N.ltsWith sel).Reachable empty f → f ≠ empty → N.Movable sel f

/-- Under `sel`, there is no infinite run without injections. -/
def LivelockFreeWith (sel : Selection C P) : Prop :=
  (N.ltsWith sel).LivelockFree Act.IsMove empty

/-- **Routing deadlock freedom**, for every valid selection function. -/
def DeadlockFree : Prop := ∀ sel, N.ValidSel sel → N.DeadlockFreeWith sel

/-- **Routing livelock freedom**, for every valid selection function. -/
def LivelockFree : Prop := ∀ sel, N.ValidSel sel → N.LivelockFreeWith sel

/-- Deadlock and livelock freedom under every dynamic routing policy. -/
def Correct : Prop := N.DeadlockFree ∧ N.LivelockFree

/-- From `f`, every run without injections is finite and ends with the network empty. -/
inductive InevitablyEmpty (sel : Selection C P) : Config C P → Prop
  | done : InevitablyEmpty sel empty
  | later {f : Config C P} : N.Movable sel f →
      (∀ a f', a.IsMove → (N.ltsWith sel).step f a f' → InevitablyEmpty sel f') →
      InevitablyEmpty sel f

/-! ### Selection functions -/

omit [DecidableEq C] in
theorem adaptive_valid : N.ValidSel N.adaptive :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

/-- Offer only the permitted channels that are free now (a packet waits if none is). -/
def freeOnly : Selection C P := fun f c p => (N.route c p).filter fun q => (f q.1).isNone

omit [DecidableEq C] in
theorem freeOnly_valid : N.ValidSel N.freeOnly where
  sub _ _ _ _ h := (List.mem_filter.1 h).1
  conserving _ _ _ _ := fun ⟨q, hq, hfree⟩ =>
    ⟨q, List.mem_filter.2 ⟨hq, by simp [hfree]⟩, hfree⟩

/-- Take the first permitted channel that is free now (a deterministic, congestion-aware
policy: the order of `route` is a priority order). -/
def firstFree : Selection C P := fun f c p =>
  ((N.route c p).find? fun q => (f q.1).isNone).toList

omit [DecidableEq C] in
theorem firstFree_valid : N.ValidSel N.firstFree where
  sub f c p q h := by
    simp only [firstFree, Option.mem_toList] at h
    exact List.mem_of_find?_eq_some h
  conserving f c p _ := fun ⟨q, hq, hfree⟩ => by
    obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1
      (List.find?_isSome.2 ⟨q, hq, by simp [hfree]⟩ :
        ((N.route c p).find? fun q => (f q.1).isNone).isSome)
    refine ⟨q', by simp [firstFree, hq'], ?_⟩
    simpa using List.find?_some hq'

/-! ### Basic facts -/

omit [DecidableEq C] in
theorem exists_of_ne_empty {f : Config C P} (h : f ≠ empty) : ∃ c p, f c = some p := by
  by_contra hc
  push Not at hc
  exact h (funext fun c => by
    cases hfc : f c with
    | none => rfl
    | some p => exact absurd hfc (hc c p))

/-- The legal pairs are an invariant of every selection that only offers permitted hops. -/
theorem legal_step {legal : C → P → Prop} (hcl : N.Closed legal) {sel : Selection C P}
    (hsel : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p) {f f' : Config C P} {a : Act C P}
    (hf : Legal legal f) (h : N.StepWith sel f a f') : Legal legal f' := by
  intro x px hx
  cases h with
  | @inject c p hinj _ =>
    by_cases hxc : x = c
    · subst hxc
      simp only [Function.update_self, Option.some.injEq] at hx
      cases hx
      exact hcl.inject _ hinj
    · rw [Function.update_of_ne hxc] at hx
      exact hf x px hx
  | @hop c c' p p' hp harr hq _ =>
    by_cases hxc' : x = c'
    · subst hxc'
      simp only [Function.update_self, Option.some.injEq] at hx
      cases hx
      exact hcl.route c p _ (hf c p hp) harr (hsel _ _ _ _ hq)
    · rw [Function.update_of_ne hxc'] at hx
      by_cases hxc : x = c
      · subst hxc; simp at hx
      · rw [Function.update_of_ne hxc] at hx
        exact hf x px hx
  | @eject c p _ _ =>
    by_cases hxc : x = c
    · subst hxc; simp at hx
    · rw [Function.update_of_ne hxc] at hx
      exact hf x px hx

theorem legal_of_reachable_sub {legal : C → P → Prop} (hcl : N.Closed legal)
    {sel : Selection C P} (hsel : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p) {f : Config C P}
    (h : (N.ltsWith sel).Reachable empty f) : Legal legal f :=
  h.invariant (fun _ _ h => by simp [empty] at h)
    (fun _ _ _ hf hst => N.legal_step hcl hsel hf hst)

theorem legal_of_reachable {legal : C → P → Prop} (hcl : N.Closed legal) {sel : Selection C P}
    (hsel : N.ValidSel sel) {f : Config C P} (h : (N.ltsWith sel).Reachable empty f) :
    Legal legal f :=
  N.legal_of_reachable_sub hcl hsel.sub h

/-- Every hop of the network is a routing step of the packet that moves. -/
theorem StepWith.packetStep {sel : Selection C P} (hsel : N.ValidSel sel)
    {f f' : Config C P} {c c' : C} {p' : P} (h : N.StepWith sel f (.hop c c' p') f') :
    ∃ p, f c = some p ∧ N.PacketStep (c, p) (c', p') := by
  cases h with
  | hop hp harr hq _ => exact ⟨_, hp, harr, hsel.sub _ _ _ _ hq⟩

/-! ### Every selection behaves like the adaptive one -/

theorem StepWith.to_adaptive {sel : Selection C P} (hsel : N.ValidSel sel)
    {f f' : Config C P} {a : Act C P} (h : N.StepWith sel f a f') :
    N.StepWith N.adaptive f a f' := by
  cases h with
  | inject h₁ h₂ => exact .inject h₁ h₂
  | hop h₁ h₂ h₃ h₄ => exact .hop h₁ h₂ (hsel.sub _ _ _ _ h₃) h₄
  | eject h₁ h₂ => exact .eject h₁ h₂

theorem reachable_to_adaptive {sel : Selection C P} (hsel : N.ValidSel sel)
    {f f' : Config C P} (h : (N.ltsWith sel).Reachable f f') : N.lts.Reachable f f' := by
  induction h with
  | refl => exact LTS.Reachable.refl _
  | tail _ hst ih => obtain ⟨a, ha⟩ := hst; exact ih.tail ⟨a, StepWith.to_adaptive N hsel ha⟩

/-- A configuration that can move under adaptive routing can move under every valid
selection (by work conservation). -/
theorem Movable.of_adaptive {sel : Selection C P} (hsel : N.ValidSel sel) {f : Config C P}
    (h : N.Movable N.adaptive f) : N.Movable sel f := by
  obtain ⟨a, f', ha, hst⟩ := h
  cases hst with
  | inject => simp [Act.IsMove] at ha
  | @hop c c' p p' hp harr hq hfree =>
    obtain ⟨⟨c'', p''⟩, hq', hfree'⟩ := hsel.conserving _ c p hp ⟨(c', p'), hq, hfree⟩
    exact ⟨.hop c c'' p'', _, rfl, StepWith.hop hp harr hq' hfree'⟩
  | @eject c p hp harr => exact ⟨.eject c, _, rfl, StepWith.eject hp harr⟩

/-- **Deadlock freedom for all selections reduces to adaptive routing.** -/
theorem deadlockFree_iff_adaptive : N.DeadlockFree ↔ N.DeadlockFreeWith N.adaptive :=
  ⟨fun h => h _ N.adaptive_valid, fun h _ hsel f hf hne =>
    Movable.of_adaptive N hsel (h f (N.reachable_to_adaptive hsel hf) hne)⟩

/-- **Livelock freedom for all selections reduces to adaptive routing.** -/
theorem livelockFree_iff_adaptive : N.LivelockFree ↔ N.LivelockFreeWith N.adaptive :=
  ⟨fun h => h _ N.adaptive_valid, fun h _ hsel =>
    LTS.LivelockFree.of_sub (fun _ _ _ hst => StepWith.to_adaptive N hsel hst) h⟩

/-! ### Deadlock freedom: Duato's and Dally–Seitz's theorems -/

/-- The core argument: with an escape subfunction `R₁` whose dependency graph is
well-founded, every configuration holding a packet can move.  By well-founded induction
along the dependencies: the packet in `c` is ejected, or its escape channel is free, or the
packet holding its escape channel can move. -/
theorem movable_of_escape {legal : C → P → Prop} {sel : Selection C P} {R₁ : C → P → List (C × P)}
    (hsel : ∀ f c p, legal c p → N.arrived c p = false → f c = some p →
      (∃ q ∈ R₁ c p, f q.1 = none) → ∃ q ∈ sel f c p, f q.1 = none)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁))) {f : Config C P} (hf : Legal legal f) :
    ∀ c p, f c = some p → N.Movable sel f := by
  intro c
  refine hwf.induction (C := fun c => ∀ p, f c = some p → N.Movable sel f) c ?_
  intro c ih p hp
  have hl := hf c p hp
  cases harr : N.arrived c p with
  | true => exact ⟨.eject c, _, rfl, StepWith.eject hp harr⟩
  | false =>
    obtain ⟨⟨c', p'⟩, hq⟩ := List.exists_mem_of_ne_nil _ (hconn c p hl harr)
    cases hc' : f c' with
    | none =>
      obtain ⟨⟨c'', p''⟩, hq', hfree⟩ := hsel f c p hl harr hp ⟨(c', p'), hq, hc'⟩
      exact ⟨.hop c c'' p'', _, rfl, StepWith.hop hp harr hq' hfree⟩
    | some p'' => exact ih c' ⟨p, p', hl, harr, hq⟩ p'' hc'

/-- **Duato's theorem** (store-and-forward / virtual cut-through switching).  Let `legal` be a
closed set of pairs.  If the routing subfunction `R₁ ⊆ route` (the escape channels) is
connected — it offers a hop to every legal packet that has not arrived — and its channel
dependency graph is well-founded (acyclic), then the network is deadlock free under every
selection function, although packets may use all of `route` adaptively. -/
theorem deadlockFree_of_escape {legal : C → P → Prop} (hcl : N.Closed legal)
    (R₁ : C → P → List (C × P))
    (hsub : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → q ∈ N.route c p)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁))) : N.DeadlockFree := by
  intro sel hsel f hf hne
  obtain ⟨c, p, hp⟩ := exists_of_ne_empty hne
  exact N.movable_of_escape (fun f c p hl ha hp ⟨q, hq, hfree⟩ =>
      hsel.conserving f c p hp ⟨q, hsub c p q hl ha hq, hfree⟩) hconn hwf
    (N.legal_of_reachable hcl hsel hf) c p hp

/-- **Duato's theorem for selections that may decline adaptive hops**: the network is deadlock
free under every selection that only offers permitted hops and never refuses a free escape
hop (`EscapeSel`), not only under work-conserving ones. -/
theorem deadlockFreeWith_of_escape {legal : C → P → Prop} (hcl : N.Closed legal)
    (R₁ : C → P → List (C × P))
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁))) {sel : Selection C P} (hsel : N.EscapeSel R₁ sel) :
    N.DeadlockFreeWith sel := by
  intro f hf hne
  obtain ⟨c, p, hp⟩ := exists_of_ne_empty hne
  exact N.movable_of_escape (fun f c p _ _ => hsel.conserving f c p) hconn hwf
    (N.legal_of_reachable_sub hcl hsel.sub hf) c p hp

omit [DecidableEq C] in
/-- A work-conserving selection never refuses a free escape hop. -/
theorem ValidSel.escapeSel {sel : Selection C P} (hsel : N.ValidSel sel)
    {R₁ : C → P → List (C × P)} (hR : ∀ c p q, q ∈ R₁ c p → q ∈ N.route c p) :
    N.EscapeSel R₁ sel :=
  ⟨hsel.sub, fun f c p hp ⟨q, hq, hfree⟩ => hsel.conserving f c p hp ⟨q, hR c p q hq, hfree⟩⟩

/-- A congestion-aware selection: the free escape hops, and those other free permitted hops that
`allow` admits (for example, only hops towards lightly loaded routers). -/
def gatedSel [DecidableEq P] (R₁ : C → P → List (C × P))
    (allow : Config C P → C → P → C × P → Bool) : Selection C P :=
  fun f c p => (N.route c p).filter fun q => (f q.1).isNone && (decide (q ∈ R₁ c p) || allow f c p q)

theorem gatedSel_escapeSel [DecidableEq P] {R₁ : C → P → List (C × P)}
    (hR : ∀ c p q, q ∈ R₁ c p → q ∈ N.route c p) (allow : Config C P → C → P → C × P → Bool) :
    N.EscapeSel R₁ (N.gatedSel R₁ allow) where
  sub _ _ _ _ h := (List.mem_filter.1 h).1
  conserving f c p _ := fun ⟨q, hq, hfree⟩ =>
    ⟨q, List.mem_filter.2 ⟨hR c p q hq, by simp [hfree, hq]⟩, hfree⟩

/-- **Dally and Seitz's theorem**: a connected routing function whose channel dependency graph
is well-founded (acyclic) is deadlock free. -/
theorem deadlockFree_of_cdg {legal : C → P → Prop} (hcl : N.Closed legal)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → N.route c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal N.route))) : N.DeadlockFree :=
  N.deadlockFree_of_escape hcl N.route (fun _ _ _ _ _ h => h) hconn hwf

omit [DecidableEq C] in
/-- On finitely many channels, an acyclic dependency graph is well-founded. -/
theorem wf_of_acyclic [Finite C] {r : C → C → Prop} (h : ∀ c, ¬ Relation.TransGen r c c) :
    WellFounded (flip r) := by
  have : WellFounded (Relation.TransGen (flip r)) := by
    have : IsTrans C (Relation.TransGen (flip r)) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
    have : Std.Irrefl (Relation.TransGen (flip r)) :=
      ⟨fun c hc => h c (Relation.transGen_swap.1 hc)⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  exact Subrelation.wf (fun h => Relation.TransGen.single h) this

omit [DecidableEq C] in
/-- A numbering of the channels that decreases along every dependency makes the dependency
graph well-founded. -/
theorem wf_of_rank {r : C → C → Prop} (rk : C → ℕ) (h : ∀ c c', r c c' → rk c' < rk c) :
    WellFounded (flip r) :=
  Subrelation.wf (fun {x y} hxy => h y x hxy) (InvImage.wf rk wellFounded_lt)

omit [DecidableEq C] in
/-- A lexicographic numbering of the channels (a pair of numbers) that decreases along every
dependency makes the dependency graph well-founded. -/
theorem wf_of_lexRank {r : C → C → Prop} (rk : C → ℕ × ℕ)
    (h : ∀ c c', r c c' → Prod.Lex (· < ·) (· < ·) (rk c') (rk c)) : WellFounded (flip r) :=
  Subrelation.wf (fun {x y} hxy => h y x hxy)
    (InvImage.wf rk (Prod.lex ⟨_, wellFounded_lt⟩ ⟨_, wellFounded_lt⟩).wf)

/-! ### Duato's condition is also necessary

Fix a closed set `legal` of pairs.  *Static* deadlock freedom asks that every non-empty
configuration of legal packets can move; it is what deadlock freedom means when every legal
configuration is reachable (`deadlockFree_iff_exists_escape`).  When finitely many channels
carry legal pairs it holds **iff** some connected routing subfunction has a well-founded (acyclic) dependency
graph (`staticDeadlockFree_iff_exists_escape`).  For the necessity, the escape subfunction is
built in stages: `stage n` holds the channels from which every legal packet has a permitted
hop into `stage (n - 1)`; deadlock freedom forces every channel into some stage, and the
escape hops are those that lead to an earlier stage. -/

/-- Every non-empty configuration of legal packets can move (under adaptive routing). -/
def StaticDeadlockFree (legal : C → P → Prop) : Prop :=
  ∀ f : Config C P, Legal legal f → f ≠ empty → N.Movable N.adaptive f

/-- The channels from which every legal packet that has not arrived has a permitted hop into
`stage n`. -/
def stage (legal : C → P → Prop) : ℕ → Set C
  | 0 => ∅
  | n + 1 => {c | ∀ p, legal c p → N.arrived c p = false → ∃ q ∈ N.route c p, q.1 ∈ stage legal n}

omit [DecidableEq C] in
theorem stage_subset_succ (legal : C → P → Prop) : ∀ n, N.stage legal n ⊆ N.stage legal (n + 1)
  | 0 => Set.empty_subset _
  | n + 1 => fun _ hc p hl ha =>
    let ⟨q, hq, hq'⟩ := hc p hl ha
    ⟨q, hq, stage_subset_succ legal n hq'⟩

omit [DecidableEq C] in
theorem stage_mono (legal : C → P → Prop) : Monotone (N.stage legal) :=
  monotone_nat_of_le_succ (N.stage_subset_succ legal)

omit [DecidableEq C] in
/-- When finitely many channels carry legal pairs, the stages stabilise. -/
theorem exists_stage_stable {legal : C → P → Prop} (hfin : {c | ∃ p, legal c p}.Finite) :
    ∃ m, N.stage legal (m + 1) = N.stage legal m := by
  have := hfin.to_subtype
  let g : ℕ → Set {c | ∃ p, legal c p} := fun n => {c | c.1 ∈ N.stage legal (n + 1)}
  have hout : ∀ c, (¬ ∃ p, legal c p) → ∀ n, c ∈ N.stage legal (n + 1) :=
    fun c hc n p hl => absurd ⟨p, hl⟩ hc
  have key : ∀ a b, a < b → g a = g b → N.stage legal (a + 2) = N.stage legal (a + 1) := by
    intro a b hab he
    refine le_antisymm (fun c hc => ?_) (N.stage_subset_succ legal (a + 1))
    by_cases hl : ∃ p, legal c p
    · have : (⟨c, hl⟩ : {c | ∃ p, legal c p}) ∈ g b :=
        N.stage_mono legal (show a + 2 ≤ b + 1 by omega) hc
      rw [← he] at this
      exact this
    · exact hout c hl _
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite g
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a + 1, key a b h he⟩
  · exact ⟨b + 1, key b a h he.symm⟩

/-- **Necessity of Duato's condition.**  If finitely many channels carry legal pairs and every
non-empty configuration of legal packets can move, then some connected routing subfunction has
a well-founded channel dependency graph. -/
theorem exists_escape_of_static {legal : C → P → Prop} (hfin : {c | ∃ p, legal c p}.Finite)
    (h : N.StaticDeadlockFree legal) :
    ∃ R₁ : C → P → List (C × P),
      (∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → q ∈ N.route c p) ∧
      (∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ []) ∧
      WellFounded (flip (N.Dep legal R₁)) := by
  classical
  obtain ⟨m, hm⟩ := N.exists_stage_stable hfin
  have hall : ∀ c, c ∈ N.stage legal m := by
    by_contra hc
    push Not at hc
    have hbad : ∀ c, c ∉ N.stage legal m → ∃ p, legal c p ∧ N.arrived c p = false ∧
        ∀ q ∈ N.route c p, q.1 ∉ N.stage legal m := by
      intro c hc'
      rw [← hm] at hc'
      simp only [stage, Set.mem_ofPred_eq, not_forall, not_exists, not_and] at hc'
      obtain ⟨p, hl, ha, hq⟩ := hc'
      exact ⟨p, hl, ha, fun q hmem => hq q hmem⟩
    obtain ⟨c₀, hc₀⟩ := hc
    have : Nonempty P := ⟨(hbad c₀ hc₀).choose⟩
    choose! pb hpb using hbad
    let f : Config C P := fun c => if c ∈ N.stage legal m then none else some (pb c)
    have hfl : Legal legal f := by
      intro c p hp
      by_cases hc : c ∈ N.stage legal m
      · simp [f, hc] at hp
      · simp only [f, hc, ite_false, Option.some.injEq] at hp
        exact hp ▸ (hpb c hc).1
    have hne : f ≠ empty := fun he => by
      have : f c₀ = none := by rw [he]; rfl
      simp [f, hc₀] at this
    obtain ⟨a, f', ha, hst⟩ := h f hfl hne
    change N.StepWith N.adaptive f a f' at hst
    cases hst with
    | inject => simp [Act.IsMove] at ha
    | @hop c c' p p' hp harr hq hfree =>
      by_cases hc : c ∈ N.stage legal m
      · simp [f, hc] at hp
      · simp only [f, hc, ite_false, Option.some.injEq] at hp
        subst hp
        have hc' := (hpb c hc).2.2 _ hq
        simp [f, hc'] at hfree
    | @eject c p hp harr =>
      by_cases hc : c ∈ N.stage legal m
      · simp [f, hc] at hp
      · simp only [f, hc, ite_false, Option.some.injEq] at hp
        subst hp
        simp [(hpb c hc).2.1] at harr
  let rk : C → ℕ := fun c => Nat.find (⟨m, hall c⟩ : ∃ n, c ∈ N.stage legal n)
  refine ⟨fun c p => (N.route c p).filter fun q => rk q.1 < rk c, ?_, ?_, ?_⟩
  · intro c p q _ _ hq
    exact (List.mem_filter.1 hq).1
  · intro c p hl ha
    have hc : c ∈ N.stage legal (rk c) := Nat.find_spec (⟨m, hall c⟩ : ∃ n, c ∈ N.stage legal n)
    cases hk : rk c with
    | zero => rw [hk] at hc; exact absurd hc (Set.notMem_empty c)
    | succ k =>
      rw [hk] at hc
      obtain ⟨q, hq, hq'⟩ := hc p hl ha
      have : rk q.1 ≤ k := Nat.find_min' _ hq'
      exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hq, by simp only [decide_eq_true_eq]; omega⟩)
  · refine wf_of_rank rk ?_
    rintro c c' ⟨p, p', -, -, hq⟩
    simpa using (List.mem_filter.1 hq).2

/-- **Duato's necessary and sufficient condition** (static form): when finitely many channels
carry legal pairs, every non-empty configuration of legal packets can move iff some connected
routing subfunction has a well-founded (acyclic) channel dependency graph. -/
theorem staticDeadlockFree_iff_exists_escape {legal : C → P → Prop}
    (hfin : {c | ∃ p, legal c p}.Finite) :
    N.StaticDeadlockFree legal ↔ ∃ R₁ : C → P → List (C × P),
      (∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → q ∈ N.route c p) ∧
      (∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ []) ∧
      WellFounded (flip (N.Dep legal R₁)) := by
  refine ⟨N.exists_escape_of_static hfin, ?_⟩
  rintro ⟨R₁, hsub, hconn, hwf⟩ f hf hne
  obtain ⟨c, p, hp⟩ := exists_of_ne_empty hne
  exact N.movable_of_escape (fun f c p hl ha hp ⟨q, hq, hfree⟩ =>
    N.adaptive_valid.conserving f c p hp ⟨q, hsub c p q hl ha hq, hfree⟩) hconn hwf hf c p hp

/-- **Duato's theorem as an equivalence**: if every configuration of legal packets is
reachable, the network is deadlock free (under every selection function) iff some connected
routing subfunction has an acyclic channel dependency graph. -/
theorem deadlockFree_iff_exists_escape {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {c | ∃ p, legal c p}.Finite) (hreach : ∀ f, Legal legal f → N.lts.Reachable empty f) :
    N.DeadlockFree ↔ ∃ R₁ : C → P → List (C × P),
      (∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → q ∈ N.route c p) ∧
      (∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ []) ∧
      WellFounded (flip (N.Dep legal R₁)) := by
  refine ⟨fun h => N.exists_escape_of_static hfin fun f hf hne =>
    (N.deadlockFree_iff_adaptive.1 h) f (hreach f hf) hne, ?_⟩
  rintro ⟨R₁, hsub, hconn, hwf⟩
  exact N.deadlockFree_of_escape hcl R₁ hsub hconn hwf

/-- Every legal configuration is reachable when every legal pair can be injected directly
(for example when the legal pairs are taken to be the injectable ones). -/
theorem reachable_of_injectable {legal : C → P → Prop} (hfin : {c | ∃ p, legal c p}.Finite)
    (hinj : ∀ c p, legal c p → (c, p) ∈ N.inject) :
    ∀ f, Legal legal f → N.lts.Reachable empty f := by
  classical
  suffices key : ∀ s : Finset C, ∀ f, Legal legal f → (∀ c, f c ≠ none → c ∈ s) →
      N.lts.Reachable empty f from
    fun f hf => key hfin.toFinset f hf fun c hc => by
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hc
      exact hfin.mem_toFinset.2 ⟨p, hf c p hp⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro f _ hs
    have : f = empty := funext fun c => by
      by_contra h; exact absurd (hs c h) (Finset.notMem_empty c)
    rw [this]
  | insert a s _ ih =>
    intro f hf hs
    have hf' : Legal legal (Function.update f a none) := by
      intro c p hp
      by_cases hc : c = a
      · subst hc; simp at hp
      · rw [Function.update_of_ne hc] at hp; exact hf c p hp
    have hr := ih (Function.update f a none) hf' fun c hc => by
      by_cases hca : c = a
      · subst hca; simp at hc
      · rw [Function.update_of_ne hca] at hc
        exact (Finset.mem_insert.1 (hs c hc)).resolve_left hca
    cases hfa : f a with
    | none => rwa [← hfa, Function.update_eq_self] at hr
    | some p =>
      have hst : N.lts.step (Function.update f a none) (.inject a p)
          (Function.update (Function.update f a none) a (some p)) :=
        StepWith.inject (hinj a p (hf a p hfa)) (by simp)
      rw [Function.update_idem, ← hfa, Function.update_eq_self] at hst
      exact hr.tail ⟨_, hst⟩

/-! ### Livelock freedom: ranking functions -/

/-- The weight of a channel's content: `0` if empty, one more than the rank of its packet
otherwise. -/
def wt (rk : C → P → ℕ) (c : C) : Option P → ℕ
  | none => 0
  | some p => rk c p + 1

omit [DecidableEq C] in
@[simp] theorem wt_none (rk : C → P → ℕ) (c : C) : wt rk c none = 0 := rfl
omit [DecidableEq C] in
@[simp] theorem wt_some (rk : C → P → ℕ) (c : C) (p : P) : wt rk c (some p) = rk c p + 1 := rfl

theorem sum_update_add (s : Finset C) (g : C → Option P → ℕ) (f : Config C P) {i : C}
    (hi : i ∈ s) (v : Option P) :
    (∑ x ∈ s, g x (Function.update f i v x)) + g i (f i) = (∑ x ∈ s, g x (f x)) + g i v := by
  have h1 := Finset.add_sum_erase s (fun x => g x (Function.update f i v x)) hi
  have h2 := Finset.add_sum_erase s (fun x => g x (f x)) hi
  have h3 : ∑ x ∈ s.erase i, g x (Function.update f i v x) = ∑ x ∈ s.erase i, g x (f x) :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  simp only [Function.update_self] at h1
  omega

/-- **Livelock freedom by a ranking function.**  If, on a closed set of pairs that uses
finitely many channels, every permitted hop strictly decreases the rank `rk` of the packet,
then under every selection function that only offers permitted hops there is no infinite run
without injections.  For
minimal routing take the distance to the destination; for bounded misrouting take the
distance plus a multiple of the remaining misrouting budget. -/
theorem livelockFreeWith_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {c | ∃ p, legal c p}.Finite) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {sel : Selection C P} (hsel : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p) :
    N.LivelockFreeWith sel := by
  have hs : ∀ c p, legal c p → c ∈ hfin.toFinset := fun c p h => hfin.mem_toFinset.2 ⟨p, h⟩
  refine LTS.LivelockFree.of_ranking (Legal legal) (fun _ _ h => by simp [empty] at h)
    (fun _ _ _ hf hst => N.legal_step hcl hsel hf hst)
    (fun f => ∑ c ∈ hfin.toFinset, wt rk c (f c)) ?_
  intro f a f' hf ha hst
  change N.StepWith sel f a f' at hst
  cases hst with
  | inject => simp [Act.IsMove] at ha
  | @hop c c' p p' hp harr hq hfree =>
    have hl' : legal c' p' := hcl.route c p (c', p') (hf c p hp) harr (hsel _ _ _ _ hq)
    have hne : c' ≠ c := by rintro rfl; simp [hp] at hfree
    have h1 := sum_update_add _ (wt rk) f (hs c p (hf c p hp)) none
    have h2 := sum_update_add _ (wt rk) (Function.update f c none) (hs c' p' hl') (some p')
    have hlt := hrk c p (c', p') (hf c p hp) harr (hsel _ _ _ _ hq)
    rw [Function.update_of_ne hne, hfree] at h2
    rw [hp, wt_some, wt_none] at h1
    rw [wt_none, wt_some] at h2
    simp only at hlt
    show ∑ x ∈ hfin.toFinset, wt rk x
        (Function.update (Function.update f c none) c' (some p') x) <
      ∑ x ∈ hfin.toFinset, wt rk x (f x)
    omega
  | @eject c p hp _ =>
    have h1 := sum_update_add _ (wt rk) f (hs c p (hf c p hp)) none
    rw [hp, wt_some, wt_none] at h1
    show ∑ x ∈ hfin.toFinset, wt rk x (Function.update f c none x) <
      ∑ x ∈ hfin.toFinset, wt rk x (f x)
    omega

/-- **Livelock freedom by a ranking function**, under every selection function that only
offers permitted hops. -/
theorem livelockFree_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {c | ∃ p, legal c p}.Finite) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.LivelockFree :=
  fun _ hsel => N.livelockFreeWith_of_ranking hcl hfin rk hrk hsel.sub

/-- `livelockFree_of_ranking` for a network with finitely many channels. -/
theorem livelockFree_of_ranking' [Finite C] {legal : C → P → Prop} (hcl : N.Closed legal)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.LivelockFree :=
  N.livelockFree_of_ranking hcl (Set.toFinite _) rk hrk

end Semantics

/-- **No packet is routed forever** when a ranking function decreases on every hop. -/
theorem packetLivelockFree_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.PacketLivelockFree := fun q hq =>
  LTS.LivelockFree.of_ranking (fun q => legal q.1 q.2) (hcl.inject q hq)
    (fun q _ q' hl hst => hcl.route q.1 q.2 q' hl hst.1 hst.2) (fun q => rk q.1 q.2)
    (fun q _ q' hl _ hst => hrk q.1 q.2 q' hl hst.1 hst.2)

/-- **Hop bound**: a packet in a legal pair `q` reaches its destination within `rk q` hops —
every route of `n` hops from `q` ends in a pair of rank at most `rk q - n`.  For minimal
routing with `rk` the distance, packets take at most as many hops as the distance. -/
theorem packet_hops_le {legal : C → P → Prop} (hcl : N.Closed legal) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {q q' : C × P} {ls : List Unit} (hq : legal q.1 q.2) (h : N.packetLTS.Path q ls q') :
    rk q'.1 q'.2 + ls.length ≤ rk q.1 q.2 := by
  revert hq
  induction h with
  | nil => intro; simp
  | cons hst _ ih =>
    intro hq
    have h1 := ih (hcl.route _ _ _ hq hst.1 hst.2)
    have h2 := hrk _ _ _ hq hst.1 hst.2
    simp only [List.length_cons]
    omega

/-- **Exact hop count**: if every permitted hop decreases `rk` by exactly one, a route of `n`
hops from `q` ends in a pair of rank `rk q - n`.  With `rk` the distance to the destination
(minimal routing), every packet takes exactly as many hops as the distance: a shortest path. -/
theorem packet_hops_eq {legal : C → P → Prop} (hcl : N.Closed legal) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p →
      rk q.1 q.2 + 1 = rk c p)
    {q q' : C × P} {ls : List Unit} (hq : legal q.1 q.2) (h : N.packetLTS.Path q ls q') :
    rk q'.1 q'.2 + ls.length = rk q.1 q.2 := by
  revert hq
  induction h with
  | nil => intro; simp
  | cons hst _ ih =>
    intro hq
    have h1 := ih (hcl.route _ _ _ hq hst.1 hst.2)
    have h2 := hrk _ _ _ hq hst.1 hst.2
    simp only [List.length_cons]
    omega

section Drain

variable [DecidableEq C]

/-- **Drain theorem.**  In a deadlock-free and livelock-free network, from every reachable
configuration every run without injections is finite and ends with the network empty. -/
theorem inevitablyEmpty {sel : Selection C P} (hD : N.DeadlockFreeWith sel)
    (hL : N.LivelockFreeWith sel) {f : Config C P} (hf : (N.ltsWith sel).Reachable empty f) :
    N.InevitablyEmpty sel f := by
  have hacc := LTS.LivelockFree.acc hL hf
  induction hacc with
  | intro f _ ih =>
    by_cases he : f = empty
    · subst he; exact .done
    · exact .later (hD f hf he) fun a f' ha hst => ih f' ⟨a, ha, hst⟩ (hf.tail ⟨a, hst⟩)

/-- From an `InevitablyEmpty` configuration, all packets can be delivered by moves only. -/
theorem InevitablyEmpty.drain {sel : Selection C P} {f : Config C P}
    (h : N.InevitablyEmpty sel f) :
    Relation.ReflTransGen ((N.ltsWith sel).IStep Act.IsMove) f empty := by
  induction h with
  | done => exact Relation.ReflTransGen.refl
  | later hm _ ih =>
    obtain ⟨a, f', ha, hst⟩ := hm
    exact Relation.ReflTransGen.head ⟨a, ha, hst⟩ (ih a f' ha hst)

variable {N}

theorem Correct.inevitablyEmpty (h : N.Correct) {sel : Selection C P} (hsel : N.ValidSel sel)
    {f : Config C P} (hf : (N.ltsWith sel).Reachable empty f) : N.InevitablyEmpty sel f :=
  N.inevitablyEmpty (h.1 sel hsel) (h.2 sel hsel) hf

/-- In a correct network, under every valid selection and from every reachable
configuration, all packets in the network can be delivered without injecting new ones. -/
theorem Correct.drain (h : N.Correct) {sel : Selection C P} (hsel : N.ValidSel sel)
    {f : Config C P} (hf : (N.ltsWith sel).Reachable empty f) :
    Relation.ReflTransGen ((N.ltsWith sel).IStep Act.IsMove) f empty :=
  (h.inevitablyEmpty hsel hf).drain

/-- A deadlock-free network that can inject some packet never gets stuck as a whole. -/
theorem DeadlockFree.lts (h : N.DeadlockFree) (hinj : N.inject ≠ []) {sel : Selection C P}
    (hsel : N.ValidSel sel) : (N.ltsWith sel).DeadlockFree empty := by
  refine LTS.deadlockFree_iff.2 fun f hf => ?_
  by_cases he : f = empty
  · subst he
    obtain ⟨⟨c, p⟩, hq⟩ := List.exists_mem_of_ne_nil _ hinj
    exact ⟨_, _, StepWith.inject hq rfl⟩
  · obtain ⟨a, f', -, hst⟩ := h sel hsel f hf he
    exact ⟨a, f', hst⟩

end Drain

/-! ### Refutation -/

section Refute

variable [DecidableEq C] [DecidableEq P]

/-- The configuration holding the packets of a list (the first entry for a channel wins). -/
def fill : List (C × P) → Config C P
  | [] => empty
  | q :: qs => Function.update (fill qs) q.1 (some q.2)

omit [DecidableEq P] in
theorem fill_eq_none {qs : List (C × P)} {c : C} : fill qs c = none ↔ c ∉ qs.map Prod.fst := by
  induction qs with
  | nil => simp [fill, empty]
  | cons q qs ih =>
    by_cases h : c = q.1
    · subst h; simp [fill]
    · simp [fill, ih, h]

omit [DecidableEq P] in
theorem mem_of_fill {qs : List (C × P)} {c : C} {p : P} (h : fill qs c = some p) :
    (c, p) ∈ qs := by
  induction qs with
  | nil => simp [fill, empty] at h
  | cons q qs ih =>
    by_cases hc : c = q.1
    · subst hc
      simp only [fill, Function.update_self, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · rw [fill, Function.update_of_ne hc] at h
      exact List.mem_cons_of_mem _ (ih h)

omit [DecidableEq P] in
theorem fill_filter (qs : List (C × P)) (c : C) :
    fill (qs.filter fun q => decide (q.1 ≠ c)) = Function.update (fill qs) c none := by
  induction qs with
  | nil => funext x; by_cases hx : x = c <;> simp [fill, empty, Function.update_apply, hx]
  | cons q qs ih =>
    by_cases hq : q.1 = c
    · rw [List.filter_cons_of_neg (by simpa using hq), ih, fill, hq, Function.update_idem]
    · rw [List.filter_cons_of_pos (by simpa using hq), fill, ih, fill,
        Function.update_comm hq]

/-- Execute actions on the list of occupied channels (under adaptive routing). -/
def runB : List (C × P) → List (Act C P) → Option (List (C × P))
  | qs, [] => some qs
  | qs, .inject c p :: as =>
    if (c, p) ∈ N.inject ∧ fill qs c = none then runB ((c, p) :: qs) as else none
  | qs, .hop c c' p' :: as =>
    match fill qs c with
    | some p =>
      if N.arrived c p = false ∧ (c', p') ∈ N.route c p ∧ fill qs c' = none then
        runB ((c', p') :: qs.filter fun q => decide (q.1 ≠ c)) as
      else none
    | none => none
  | qs, .eject c :: as =>
    match fill qs c with
    | some p => if N.arrived c p = true then runB (qs.filter fun q => decide (q.1 ≠ c)) as
      else none
    | none => none

theorem path_of_runB {qs qs' : List (C × P)} {as : List (Act C P)}
    (h : N.runB qs as = some qs') : N.lts.Path (fill qs) as (fill qs') := by
  induction as generalizing qs with
  | nil =>
    simp only [runB, Option.some.injEq] at h
    subst h; exact LTS.Path.nil _
  | cons a as ih =>
    cases a with
    | inject c p =>
      simp only [runB] at h
      split_ifs at h with hc
      exact LTS.Path.cons (StepWith.inject hc.1 hc.2) (ih h)
    | hop c c' p' =>
      simp only [runB] at h
      split at h
      · rename_i p hp
        split_ifs at h with hc
        have hst := StepWith.hop (N := N) (sel := N.adaptive) hp hc.1 hc.2.1 hc.2.2
        rw [← fill_filter] at hst
        exact LTS.Path.cons hst (ih h)
      · simp at h
    | eject c =>
      simp only [runB] at h
      split at h
      · rename_i p hp
        split_ifs at h with hc
        have hst := StepWith.eject (N := N) (sel := N.adaptive) hp hc
        rw [← fill_filter] at hst
        exact LTS.Path.cons hst (ih h)
      · simp at h

/-- Every packet of `qs` is blocked: it has not arrived and every permitted hop leads to an
occupied channel. -/
def stuckB (qs : List (C × P)) : Bool :=
  qs.all fun q => match fill qs q.1 with
    | some p => !N.arrived q.1 p && (N.route q.1 p).all fun q' => (fill qs q'.1).isSome
    | none => false

/-- A run from the empty network to a non-empty configuration in which every packet is
blocked. -/
def refuteDeadlockB (as : List (Act C P)) : Bool :=
  match N.runB [] as with
  | some qs => !qs.isEmpty && N.stuckB qs
  | none => false

variable {N} in
/-- **Refuting deadlock freedom**: exhibit a run to a configuration in which every packet is
blocked. -/
theorem not_deadlockFree_of_refuteB {as : List (Act C P)} (h : N.refuteDeadlockB as = true) :
    ¬ N.DeadlockFree := by
  unfold refuteDeadlockB at h
  split at h
  · rename_i qs hrun
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    obtain ⟨hne, hstuck⟩ := h
    intro hD
    have hr : N.lts.Reachable empty (fill qs) := (N.path_of_runB hrun).reachable
    have hfne : fill qs ≠ empty := by
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
      intro he
      have : fill qs q.1 = none := by rw [he]; rfl
      exact fill_eq_none.1 this (List.mem_map_of_mem hq)
    obtain ⟨a, f', ha, hst⟩ := hD _ N.adaptive_valid _ hr hfne
    have key : ∀ c p, fill qs c = some p →
        N.arrived c p = false ∧ ∀ q' ∈ N.route c p, fill qs q'.1 ≠ none := by
      intro c p hp
      have := (List.all_eq_true.1 hstuck) (c, p) (mem_of_fill hp)
      simp only [hp, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
        Option.isSome_iff_ne_none] at this
      exact this
    change N.StepWith N.adaptive _ a f' at hst
    cases hst with
    | inject => simp [Act.IsMove] at ha
    | hop hp _ hq hfree => exact (key _ _ hp).2 _ hq hfree
    | eject hp harr => simp [(key _ _ hp).1] at harr
  · simp at h

/-- The two lists describe the same configuration. -/
def sameB (qs qs' : List (C × P)) : Bool :=
  (qs ++ qs').all fun q => decide (fill qs q.1 = fill qs' q.1)

theorem fill_eq_of_sameB {qs qs' : List (C × P)} (h : sameB qs qs' = true) :
    fill qs = fill qs' := by
  funext c
  by_cases hc : c ∈ (qs ++ qs').map Prod.fst
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
    exact of_decide_eq_true ((List.all_eq_true.1 h) q hq)
  · simp only [List.map_append, List.mem_append, not_or] at hc
    rw [fill_eq_none.2 hc.1, fill_eq_none.2 hc.2]

/-- A run `pre` from the empty network, followed by a non-empty cycle `cyc` of moves that
returns to the same configuration. -/
def refuteLivelockB (pre cyc : List (Act C P)) : Bool :=
  !cyc.isEmpty && cyc.all Act.isMove &&
    match N.runB [] pre with
    | some qs => match N.runB qs cyc with
      | some qs' => sameB qs qs'
      | none => false
    | none => false

variable {N} in
/-- **Refuting livelock freedom**: exhibit a reachable configuration and a non-empty cycle of
moves (without injections) back to it. -/
theorem not_livelockFree_of_refuteB {pre cyc : List (Act C P)}
    (h : N.refuteLivelockB pre cyc = true) : ¬ N.LivelockFree := by
  unfold refuteLivelockB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨hne, hmv⟩, h⟩ := h
  split at h
  · rename_i qs hpre
    split at h
    · rename_i qs' hcyc
      intro hL
      have hp := N.path_of_runB hcyc
      rw [← fill_eq_of_sameB h] at hp
      refine LTS.not_livelockFree_of_cycle (N.path_of_runB hpre).reachable
        (hp.iStep_transGen (fun a ha => (List.all_eq_true.1 hmv) a ha) hne)
        ((N.livelockFree_iff_adaptive).1 hL)
    · simp at h
  · simp at h

end Refute

end Network

end AsyncLean
