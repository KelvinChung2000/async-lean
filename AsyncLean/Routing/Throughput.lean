/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Throughput.Planes
import AsyncLean.Routing.Throughput.Select
import AsyncLean.Routing.Throughput.Graph

/-!
# Packet throughput is bounded by the fluid model

This module gathers four parts: `Throughput.Timed` (placements, timed runs, the throughput bound,
delivery), `Throughput.Planes` (planes add their throughput), `Throughput.Select` (score-based
selections are safe) and `Throughput.Graph` (the networks of `GraphData` on their graph).

The packet networks of `AsyncLean.Routing.Basic` are transition systems: they say which moves
are possible, not when they happen, so they have no throughput.  These modules add time and prove
that **no packet network, under any routing and any selection, carries more than the fluid
model allows** (`Network.TimedRun.potential_bound`): the bridge between the packet networks and
`AsyncLean.Flow`.

## The model

* A **placement** (`Network.Placement`) puts the network on a graph: every channel holding a
  packet is at a vertex (`pos`), every header has a destination (`dest`), and the channels a
  packet can be forwarded to belong to links `u → v` (`link`): a hop from a channel at `u` goes
  to a channel of a link `u → v`, keeps the destination, and a packet is ejected only at its
  destination.  The capacity of a link is the number of its channels (`Placement.net`, a
  network of the fluid model).
* A **timed run** (`Network.TimedRun`) runs in rounds from the empty network: in round `t` a
  list of actions (injections, hops, ejections) takes the configuration of round `t` to that of
  round `t + 1`, and every channel receives at most one packet per round by a hop.  This is a
  synchronous network in which a channel forwards at most one packet per cycle; the selection
  is arbitrary.

## Main results

* `TimedRun.injected_le` : **the potential accounting.**  For every potential `φ d v ≥ 0` with
  `φ d d = 0` dropping by at most `len u v` along every link, the packets injected in `T` rounds,
  each weighted by the potential of its source, weigh at most
  `T * ∑ u v, cap u v * len u v + |C| * max φ`: every hop lowers the potential by at most the
  length of its link, every link carries at most its capacity per round, and the network holds
  at most `|C|` packets.
* `TimedRun.potential_bound` : **the packet bound.**  A timed run that sustains the load `ρ * dem`
  (it injects at least `T ρ dem s d - K` packets from `s` to `d` in the first `T` rounds)
  respects every potential bound of the fluid network of its placement:
  `ρ * ∑ s d, dem s d * φ d s ≤ ∑ u v, cap u v * len u v`.  `TimedRun.cut_bound` and
  `TimedRun.hop_bound` are the cut and hop forms.
* `Placement.restrict` : a selection whose hops stay on some of the channels is bounded by the
  fluid network of those channels alone (a selection that never uses some links loses their
  capacity).
* `TimedRun.ejected_ge` : a timed run delivers everything it injects but for the packets the
  network holds (at most its number of channels).
* `planesTimed`, `planesTimed_injected` : **planes add their throughput in time**: timed runs of the
  planes, side by side round by round, are a timed run of the plane network injecting the sum of
  what the planes inject.
* `GraphData.placement` : the networks of `GraphData` (`net`, `budgetNet`, `detourNet`) are
  placed on their graph, two channels per link (`GraphData.placement_cap`);
  `Network.planesPlacement` places `m` planes with `m` times the capacity.
* `scoreSel`, `scoreSel_valid`, `Correct.scoreSel` : choosing among the free permitted hops
  those of largest score (backlog differences, as backpressure does) is a valid selection, so
  every correct network stays deadlock and livelock free under it.
-/
