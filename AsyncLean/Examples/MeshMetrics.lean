/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshMetrics.Latency

/-!
# Optimal mesh routing, metric by metric

This module gathers 3 parts:

1. `MeshMetrics.OneVC` — one virtual channel, correct for every size;
2. `MeshMetrics.OneVCMaximal` — one virtual channel, maximal for every size; north-last;
3. `MeshMetrics.Latency` — latency, XY routing and routing tables.

"Most adaptive" depends on the yardstick: which hops count, on how many virtual channels.  This
file fixes the yardstick by the cost one wants to optimise and proves, for every mesh size, what
the optimum is and which routing function reaches it.

## Latency: hop count

* `hops_lower_bound` : on a `k × k` mesh, a packet that only moves between neighbouring nodes
  needs at least as many hops as the distance from its source to its destination, **whatever
  the routing function**.
* Every mesh family (`MeshFamily`) — XY, the turn-model meshes on one or two virtual channels —
  meets the bound exactly (`family_hops`), so none can be beaten on hop count.

## Buffers: one virtual channel

* With a single virtual channel per link (the fewest buffers a mesh can have), the west-first
  and north-last turn models (`westFirst1`, `northLast1`) are deadlock and livelock free for
  every size, under store-and-forward and wormhole switching (`westFirst1_correct`,
  `westFirst1_wormholeCorrect`, and the same for north-last), and take shortest paths.
* They are **maximally adaptive** among the minimal routing functions on one virtual channel
  (`minimalHops1`), for every size (`westFirst1_maximal_all`, `northLast1_maximal_all`), and
  XY routing is not (`xyMesh_not_maximal_all`).  On two virtual channels, `westFirstMesh` and
  `northLastMesh` are maximal (`AsyncLean.Examples.MeshMaximal`).

## Routing tables

* `table_lower_bound` : on any mesh of size at least 3, a deadlock-free minimal routing function
  needs at least 4 different routing decisions at an inner router.
* XY routing makes exactly as few (`xy_table`), so it is optimal for routing-table size.  Every
  turn-model mesh decides from the relative position of the destination alone, so it needs at
  most 8 decisions per router, independent of the size (`turnDuato_table`).
-/
