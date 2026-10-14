/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Examples.MeshMaximal.Packet

/-!
# Maximally adaptive routing on meshes of every size

This module gathers 3 parts:

1. `MeshMaximal.Windows` — windows;
2. `MeshMaximal.Certificates` — the window certificates and a single packet;
3. `MeshMaximal.Packet` — following the packet; maximal for every size.

`AsyncLean.Examples.OptimalRouting` checks, mesh by mesh, that the west-first and north-last
meshes are maximally adaptive.  Here the same is proved **for every size `k`**.

## The argument

A hop the west-first mesh does not permit, but a minimal routing function `N` permits, is a
northward or southward hop on virtual channel 0 of a packet `P` that still has to go west
(`wf_extra`).  For the north-last mesh it is a northward hop on virtual channel 0 of a packet
that still has to go east or west (`nl_extra`).  Follow `P` after the hop:

* while `N` lets it go on north (or south) on virtual channel 0, let it;
* it stops on virtual channel 0 in a column next to its destination's side, either in its
  destination's row (`top`) or with one more vertical hop left that `N` does not permit on
  virtual channel 0 (`caseB`).

Either way, a small group of packets around `P` (8 or 13 of them, in a 2 × 2 or 2 × 3 window)
blocks it and blocks itself: `P` closes a cycle of turns that the turn model alone forbids.
This group is found and checked by the kernel once, in a 3 × 3 mesh (`winCertB`), with `P`
frozen in its channel standing for a packet whose destination may lie far outside the window.
`Network.not_deadlockFree_of_runGoodB` carries the deadlock into the `k × k` mesh, at the
position of `P` (`emb`, `not_deadlockFree_of_winCertB`).  The induction on the vertical distance
left (`climbNW`, `climbSW`, `climbNE`) and the single-packet run to the extra hop
(`reachable_single`) complete the proof.

## Results

* `westFirstMesh_maximal_all k`, `northLastMesh_maximal_all k` : the west-first and the
  north-last meshes are maximally adaptive among the minimal routing functions on two virtual
  channels, for every size (under wormhole switching too, `MaximallyAdaptive.wormhole`).
* `no_common_improvement_all k` : no deadlock-free minimal routing function of any mesh of size
  at least 2 is at least as adaptive as both.
-/
