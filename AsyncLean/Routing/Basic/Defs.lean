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
# Interconnection networks with dynamic routing, part 1: networks, selections and the properties

Part 1 of 5 of `AsyncLean.Routing.Basic`; that module has the overview.
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

end Semantics

end Network

end AsyncLean
