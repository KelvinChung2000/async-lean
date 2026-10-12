/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Basic.Refute

/-!
# Interconnection networks with dynamic routing

This module gathers 5 parts:

1. `Basic.Defs` — networks, selections and the properties;
2. `Basic.Facts` — selection functions and basic facts;
3. `Basic.Deadlock` — deadlock freedom, Duato and Dally–Seitz, and the converse;
4. `Basic.Livelock` — livelock freedom and draining;
5. `Basic.Refute` — refutation.

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
