/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Checker.BDD.Theorems

/-!
# Symbolic certificates: decision diagrams checked by the kernel

This module gathers 4 parts:

1. `BDD.Checks` — the certificate format and the trusted checker;
2. `BDD.Nodes` — basic lemmas and node invariants;
3. `BDD.Firing` — firing, walks and leaf conditions;
4. `BDD.Theorems` — soundness of the check.

A safe net's reachable markings are sets of places, and a *binary decision diagram* often
describes such a set in a size that grows with the structure of the net rather than with the
number of markings.  `PNet.checkBDD` checks properties of a safe net from decision diagrams
over the places, without enumerating any marking:

* the markings of the *invariant* diagram form an inductive invariant: it contains the
  initial marking and is closed under firing, and firing never marks a marked place;
* the leaves of a *data* diagram, which covers the invariant, carry a *witness* transition
  enabled at every marking reaching the leaf (deadlock freedom); for liveness, either a
  *linear potential* (weights on the places) that every witness decreases, or, lexicographically,
  a linear potential that each witness decreases or keeps while decreasing a *distance*, down to
  *hubs* from which a trace enables each transition;
* for livelock freedom, either a linear rank that every internal transition decreases, or,
  lexicographically, a linear rank that each internal transition decreases or keeps while
  decreasing a *rank* diagram.

Closure is checked transition by transition, by a joint walk of a diagram before and after
firing: a set of *triples* `(a, b, j)` — a node `a` read before firing, a node `b` read after,
and the number `j` of places touched by the transition already passed — each checked locally
against its successors (`PNet.tripleOk`).  Which markings reach which leaf is the semantics
`PNet.Reach`; `PNet.TClaim` is what a triple guarantees.  Every node also carries the places
known to be marked (`k1`) and unmarked (`k0`) on every path to it, so the kernel can see that
a witness is enabled, or that a hub is a single marking, from the leaf alone.

Most of a walk is *diagonal*: the same node before and after firing, above or below the
places the transition touches.  Each level reads one place (`vars`, inverted by `lvls`), so
below the touched places a diagonal triple holds by itself (`PNet.Reach.congr`), and a walk on
the invariant starts at the *cut* of the lowest level touched — the references first reached
at or below it, checked level by level once for all transitions (`PNet.cut_reach`).  A walk
showing that the data diagram covers the invariant stops at the first data leaf.

`PNet.of_checkBDD` turns a successful check into deadlock freedom, livelock freedom, liveness
and safety of the net, through the packed semantics of `AsyncLean.Checker.Packed`.  The
diagrams are computed by untrusted code (`PNet.BDDGen.mkBDDCert`), symbolically: reachability,
witnesses, ranks and distances are all computed on decision diagrams, and the weights by
linear programming.
-/
