/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Fairness
import AsyncLean.Checker.Explicit

/-!
# Checking routing functions

For a concrete network, `Network.Correct` follows from finitely many local checks on the
routing function (Duato's and Dally–Seitz's theorems and a ranking function), with no
exploration of the configurations of the network.  This file provides

* the **trusted checker** `Network.checkCert` and its soundness theorem
  `Network.correct_of_checkCert`.  A certificate is a table of the pairs (channel, header)
  that packets can occupy, each with a livelock rank, and a table of channel ranks that
  decrease along the dependency graph of an escape subfunction;
* the **untrusted search** `Network.mkPairs` / `Network.mkRanks`, which explores the pairs
  reachable by a single packet and computes longest-path ranks;
* the **diagnosis** `Network.diagnose`, which explains a failure: a packet with no permitted
  hop, a routing cycle (livelock) or a cycle of channel dependencies (potential deadlock),
  and when it can, a counterexample run together with the refutation theorem proving
  `¬ N.DeadlockFree` or `¬ N.LivelockFree`.

The `async_decide` and `async_routing` tactics (`AsyncLean.Checker.Tactic`) run the search,
embed the certificate in the proof and let the kernel run the checker.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*} [DecidableEq C] [DecidableEq P] (N : Network C P)

/-! ### The trusted checker -/

section Check

variable (cmpC : C → C → Ordering) (cmpQ : C × P → C × P → Ordering)

/-- The pair `q` is listed in the certificate. -/
def legalB (pairs : BTree ((C × P) × ℕ)) (q : C × P) : Bool := (pairs.findData cmpQ q).isSome

/-- The livelock rank of a pair (`0` if unlisted). -/
def pairRank (pairs : BTree ((C × P) × ℕ)) (q : C × P) : ℕ := (pairs.findData cmpQ q).getD 0

/-- The rank of a channel in the dependency graph (`0` if unlisted). -/
def chanRank (ranks : BTree (C × ℕ)) (c : C) : ℕ := (ranks.findData cmpC c).getD 0

/-- The local conditions at one pair `q`: unless the packet has arrived, every permitted hop
leads to a listed pair of smaller rank, and the escape function offers at least one hop,
each of them permitted and to a channel of smaller rank. -/
def checkPair (esc : C → P → List (C × P)) (pairs : BTree ((C × P) × ℕ))
    (ranks : BTree (C × ℕ)) (q : C × P) : Bool :=
  N.arrived q.1 q.2 ||
    ((N.route q.1 q.2).all (fun q' => legalB cmpQ pairs q' &&
        decide (pairRank cmpQ pairs q' < pairRank cmpQ pairs q)) &&
      !(esc q.1 q.2).isEmpty &&
      (esc q.1 q.2).all (fun q' => decide (q' ∈ N.route q.1 q.2) &&
        decide (chanRank cmpC ranks q'.1 < chanRank cmpC ranks q.1)))

/-- **The trusted checker**: every injected packet is listed, and the local conditions hold
at every listed pair. -/
def checkCert (esc : C → P → List (C × P)) (pairs : BTree ((C × P) × ℕ))
    (ranks : BTree (C × ℕ)) : Bool :=
  N.inject.all (legalB cmpQ pairs) && pairs.all fun e => N.checkPair cmpC cmpQ esc pairs ranks e.1

end Check

/-- What a passing certificate establishes: a closed, finite set of legal pairs, a connected
escape subfunction with a well-founded dependency graph, and a ranking function. -/
theorem spec_of_checkCert {N : Network C P} {cmpC : C → C → Ordering}
    {cmpQ : C × P → C × P → Ordering} {esc : C → P → List (C × P)}
    {pairs : BTree ((C × P) × ℕ)} {ranks : BTree (C × ℕ)}
    (h : N.checkCert cmpC cmpQ esc pairs ranks = true) :
    ∃ legal : C → P → Prop, N.Closed legal ∧ {q : C × P | legal q.1 q.2}.Finite ∧
      (∀ c p q, legal c p → N.arrived c p = false → q ∈ esc c p → q ∈ N.route c p) ∧
      (∀ c p, legal c p → N.arrived c p = false → esc c p ≠ []) ∧
      WellFounded (flip (N.Dep legal esc)) ∧
      ∃ rk : C → P → ℕ, ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p →
        rk q.1 q.2 < rk c p := by
  simp only [checkCert, Bool.and_eq_true, List.all_eq_true, BTree.all_eq_true] at h
  obtain ⟨hinj, hall⟩ := h
  let legal : C → P → Prop := fun c p => legalB cmpQ pairs (c, p) = true
  have hpair : ∀ c p, legal c p → N.arrived c p = false →
      (∀ q ∈ N.route c p, legalB cmpQ pairs q = true ∧
        pairRank cmpQ pairs q < pairRank cmpQ pairs (c, p)) ∧
      esc c p ≠ [] ∧
      (∀ q ∈ esc c p, q ∈ N.route c p ∧ chanRank cmpC ranks q.1 < chanRank cmpC ranks c) := by
    intro c p hl ha
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hl
    have := hall _ (BTree.mem_toList_of_findData hr)
    simpa [checkPair, ha, List.isEmpty_iff, and_assoc] using this
  refine ⟨legal, ⟨fun q hq => hinj q hq, fun c p q hl ha hq => ((hpair c p hl ha).1 q hq).1⟩,
    ?_, fun c p q hl ha hq => ((hpair c p hl ha).2.2 q hq).1,
    fun c p hl ha => (hpair c p hl ha).2.1, wf_of_rank (chanRank cmpC ranks) ?_,
    fun c p => pairRank cmpQ pairs (c, p), fun c p q hl ha hq => ((hpair c p hl ha).1 q hq).2⟩
  · refine (Finset.finite_toSet ((pairs.toList.map fun e => e.1).toFinset)).subset ?_
    rintro q hl
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hl
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨_, BTree.mem_toList_of_findData hr, rfl⟩
  · rintro c c' ⟨p, p', hl, ha, hq⟩
    exact ((hpair c p hl ha).2.2 _ hq).2

/-- **Soundness of the checker**: a certificate that passes `checkCert` proves that the network
is deadlock free and livelock free under every dynamic routing policy.  The comparison
functions only guide the search: any function is sound. -/
theorem correct_of_checkCert {N : Network C P} {cmpC : C → C → Ordering}
    {cmpQ : C × P → C × P → Ordering} {esc : C → P → List (C × P)}
    {pairs : BTree ((C × P) × ℕ)} {ranks : BTree (C × ℕ)}
    (h : N.checkCert cmpC cmpQ esc pairs ranks = true) : N.Correct := by
  obtain ⟨legal, hcl, hfin, hsub, hconn, hwf, rk, hrk⟩ := spec_of_checkCert h
  have hchan : {c | ∃ p, legal c p}.Finite :=
    (hfin.image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩
  exact ⟨N.deadlockFree_of_escape hcl esc hsub hconn hwf,
    N.livelockFree_of_ranking hcl hchan rk hrk⟩

/-- A passing certificate also proves **starvation freedom**: along every strongly fair run,
every packet is delivered. -/
theorem starvationFree_of_checkCert {N : Network C P} {cmpC : C → C → Ordering}
    {cmpQ : C × P → C × P → Ordering} {esc : C → P → List (C × P)}
    {pairs : BTree ((C × P) × ℕ)} {ranks : BTree (C × ℕ)}
    (h : N.checkCert cmpC cmpQ esc pairs ranks = true) : N.StarvationFree := by
  obtain ⟨legal, hcl, hfin, hsub, hconn, hwf, rk, hrk⟩ := spec_of_checkCert h
  exact N.starvationFree_of_escape_ranking hcl hfin esc hsub hconn hwf rk hrk

/-! ### Untrusted certificate search

Nothing below needs to be correct: a wrong answer only makes the check fail. -/

section Search

variable (cmpC : C → C → Ordering) (cmpQ : C × P → C × P → Ordering)

/-- The route of a single packet as an explicit transition system. -/
def packetExplicit : ExplicitLTS (C × P) Unit :=
  ⟨fun q => if N.arrived q.1 q.2 then [] else (N.route q.1 q.2).map fun q' => ((), q')⟩

/-- The pairs reachable by a single packet from the injections. -/
def explorePairs (fuel : ℕ) : BTree (C × P) :=
  (N.packetExplicit.exploreAux cmpQ fuel N.inject
    (N.inject.foldl (fun s q => if s.tree.find cmpQ q then s else s.push cmpQ q) {})).tree.rebalance

/-- Candidate pair table: the reachable pairs, ranked by the longest route to arrival. -/
def mkPairs (fuel : ℕ) : BTree ((C × P) × ℕ) :=
  N.packetExplicit.autoRank cmpQ (fun _ => true) (N.explorePairs cmpQ fuel)

/-- The dependency graph of `esc` on the listed pairs, as adjacency lists. -/
def depGraph (esc : C → P → List (C × P)) (pairs : BTree ((C × P) × ℕ)) : BTree (C × List C) :=
  ((pairs.toListAcc []).foldl (fun (acc : BStore (C × List C)) e =>
    let q := e.1
    if N.arrived q.1 q.2 then acc else
      let succs := (esc q.1 q.2).map Prod.fst
      acc.pushKV cmpC q.1 (succs ++ ((acc.tree.lookup cmpC q.1).getD []))) {}).tree

/-- The dependency graph as an explicit transition system on channels. -/
def depExplicit (g : BTree (C × List C)) : ExplicitLTS C Unit :=
  ⟨fun c => ((g.lookup cmpC c).getD []).map fun c' => ((), c')⟩

/-- Candidate channel ranks: the longest dependency chain from each channel. -/
def mkRanks (esc : C → P → List (C × P)) (pairs : BTree ((C × P) × ℕ)) : BTree (C × ℕ) :=
  let g := N.depGraph cmpC esc pairs
  (depExplicit cmpC g).autoRank cmpC (fun _ => true) (BTree.ofList ((g.toListAcc []).map Prod.fst))

/-- The escape subfunction that takes the *first* permitted hop: list the escape channel
first in `route` and Duato's theorem applies without naming it. -/
def firstHop : C → P → List (C × P) := fun c p => (N.route c p).take 1

end Search

/-! ### Diagnosis (untrusted) -/

section Diagnose

variable (cmpC : C → C → Ordering) (cmpQ : C × P → C × P → Ordering)

/-- Depth-first search for a cycle reachable from `a`: returns the visited path from the root,
ending with the first repeated node. -/
def dfsCycle {α : Type*} [DecidableEq α] (succ : α → List α) (cmp : α → α → Ordering) :
    ℕ → List α → BTree α → α → Option (List α) × BTree α
  | 0, _, done, _ => (none, done)
  | fuel + 1, path, done, a =>
    if path.contains a then (some (a :: path).reverse, done)
    else if done.find cmp a then (none, done)
    else
      let r := (succ a).foldl (fun (acc : Option (List α) × BTree α) b =>
        match acc.1 with
        | some _ => acc
        | none => dfsCycle succ cmp fuel (a :: path) acc.2 b) (none, done)
      match r.1 with
      | some c => (some c, r.2)
      | none => (none, r.2.insert cmp a)

/-- A cycle reachable from one of the `roots`. -/
def findCycle {α : Type*} [DecidableEq α] (succ : α → List α) (cmp : α → α → Ordering)
    (fuel : ℕ) (roots : List α) : Option (List α) :=
  (roots.foldl (fun (acc : Option (List α) × BTree α) a =>
    match acc.1 with
    | some _ => acc
    | none => dfsCycle succ cmp fuel [] acc.2 a) (none, .leaf)).1

/-- Breadth-first search for a route of a single packet from an injection to `goal`, through
pairs satisfying `ok`. -/
def bfsRoute (ok : C × P → Bool) (goal : C × P) :
    ℕ → List (List (C × P)) → BTree (C × P) → Option (List (C × P))
  | 0, _, _ => none
  | fuel + 1, frontier, seen =>
    match frontier.find? (fun path => path.head? == some goal) with
    | some path => some path.reverse
    | none =>
      let r := frontier.foldl (fun (acc : List (List (C × P)) × BTree (C × P)) path =>
        match path with
        | [] => acc
        | q :: _ => (N.packetExplicit.succ q).foldl (fun acc e =>
            if ok e.2 && !acc.2.find cmpQ e.2 then ((e.2 :: path) :: acc.1, acc.2.insert cmpQ e.2)
            else acc) acc) ([], seen)
      if r.1.isEmpty then none else bfsRoute ok goal fuel r.1 r.2

/-- A route from an injection to `goal` avoiding the channels `avoid`. -/
def routeTo (avoid : List C) (goal : C × P) (fuel : ℕ) : Option (List (C × P)) :=
  let ok := fun q : C × P => !avoid.contains q.1
  let starts := N.inject.filter ok
  N.bfsRoute cmpQ ok goal fuel (starts.map fun q => [q])
    (starts.foldl (fun t q => t.insert cmpQ q) .leaf)

/-- The actions of a single packet hopping along `qs`. -/
def hopsAlong : List (C × P) → List (Act C P)
  | q :: q' :: qs => .hop q.1 q'.1 q'.2 :: hopsAlong (q' :: qs)
  | _ => []

/-- The actions injecting a packet as `q₀` and moving it along `q₀ :: qs`. -/
def runAlong : List (C × P) → List (Act C P)
  | [] => []
  | q :: qs => .inject q.1 q.2 :: hopsAlong (q :: qs)

/-- Try to fill the channels of a dependency cycle with blocked packets, one packet at a
time, each routed from an injection through free channels. -/
def deadlockAttempt (cyc : List C) (fuel : ℕ) : Option (List (Act C P)) :=
  let pairs := (N.explorePairs cmpQ fuel).toListAcc []
  let pick := fun c : C => pairs.find? fun q => q.1 == c && !N.arrived q.1 q.2 &&
    (N.route q.1 q.2).all fun q' => cyc.contains q'.1
  let r := cyc.foldl (fun (acc : Option (List (Act C P) × List C)) c =>
    match acc, pick c with
    | some (as, occ), some q =>
      match N.routeTo cmpQ occ q fuel with
      | some path => some (as ++ runAlong path, c :: occ)
      | none => none
    | _, _ => none) (some ([], []))
  r.map Prod.fst

variable [Repr C] [Repr P]

private def actStr : Act C P → String
  | .inject c p => s!".inject {reprArg c} {reprArg p}"
  | .hop c c' p' => s!".hop {reprArg c} {reprArg c'} {reprArg p'}"
  | .eject c => s!".eject {reprArg c}"

private def actsStr (as : List (Act C P)) : String :=
  "[" ++ ", ".intercalate (as.map actStr) ++ "]"

private def pairStr (q : C × P) : String := s!"({reprStr q.1}, {reprStr q.2})"

private def pathStr (qs : List (C × P)) : String := " → ".intercalate (qs.map pairStr)

/-- Explain why `checkCert` fails for the escape function `esc`, with a counterexample and
its refutation theorem when one is found. -/
def diagnose (esc : C → P → List (C × P)) (fuel : ℕ := 100000) : String :=
  let pairs := (N.explorePairs cmpQ fuel).toListAcc []
  if pairs.length ≥ fuel then
    s!"more than {fuel} reachable (channel, header) pairs; increase the fuel"
  else
  let live := pairs.filter fun q => !N.arrived q.1 q.2
  match live.find? fun q => (N.route q.1 q.2).isEmpty with
  | some q =>
    let msg := s!"the packet {pairStr q} has not arrived and has no permitted hop."
    match N.routeTo cmpQ [] q fuel with
    | some path =>
      let as := runAlong path
      if N.refuteDeadlockB as then
        s!"DEADLOCK: {msg}\nProve it with: Network.not_deadlockFree_of_refuteB \
          (as := {actsStr as}) (by decide +kernel)"
      else s!"DEADLOCK: {msg}"
    | none => s!"DEADLOCK: {msg}"
  | none =>
  let succ := fun q : C × P => (N.packetExplicit.succ q).map Prod.snd
  match (findCycle succ cmpQ fuel N.inject).bind fun path => path.getLast?.map (path, ·) with
  | some (path, last) =>
    let pre := path.takeWhile (· != last)
    let cyc := (path.dropWhile (· != last))
    let preActs := runAlong (pre ++ [last])
    let cycActs := hopsAlong cyc
    let msg := s!"a packet can be routed {pathStr (pre ++ [last])} and then around the \
      cycle {pathStr cyc} forever."
    if N.refuteLivelockB preActs cycActs then
      s!"LIVELOCK: {msg}\nProve it with: Network.not_livelockFree_of_refuteB \
        (pre := {actsStr preActs}) (cyc := {actsStr cycActs}) (by decide +kernel)"
    else s!"LIVELOCK (routing cycle): {msg}"
  | none =>
  match live.find? fun q => (esc q.1 q.2).isEmpty ||
      !(esc q.1 q.2).all fun q' => decide (q' ∈ N.route q.1 q.2) with
  | some q => s!"the escape function is not a connected routing subfunction at the packet \
      {pairStr q}: it must offer at least one hop, and only permitted hops."
  | none =>
  let g := N.depGraph cmpC esc (N.mkPairs cmpQ fuel)
  let csucc := fun c : C => (g.lookup cmpC c).getD []
  match (findCycle csucc cmpC fuel ((g.toListAcc []).map Prod.fst)).bind
      fun cpath => cpath.getLast?.map (cpath, ·) with
  | some (cpath, last) =>
    let cyc := cpath.dropWhile (· != last)
    let cycStr := " → ".intercalate (cyc.map reprStr)
    match N.deadlockAttempt cmpQ cyc.tail fuel with
    | some as =>
      if N.refuteDeadlockB as then
        s!"DEADLOCK: the channel dependency cycle {cycStr} can be filled with blocked \
          packets by the run {actsStr as}.\nProve it with: Network.not_deadlockFree_of_refuteB \
          (as := {actsStr as}) (by decide +kernel)"
      else s!"POTENTIAL DEADLOCK: the channel dependency graph has the cycle {cycStr}. \
        With adaptive routing this need not be a deadlock: give an acyclic escape \
        subfunction with `async_routing (escape := R₁)` (Duato's theorem), or list the \
        escape hop first in `route`."
    | none => s!"POTENTIAL DEADLOCK: the channel dependency graph has the cycle {cycStr}. \
        With adaptive routing this need not be a deadlock: give an acyclic escape \
        subfunction with `async_routing (escape := R₁)` (Duato's theorem), or list the \
        escape hop first in `route`."
  | none => "the certificate check failed (a permitted hop that stays in the same channel?)"

end Diagnose

/-- `#eval N.explain` reports what `async_decide` finds for the network `N`: which theorem
proves it correct, or a counterexample with the theorem refuting correctness. -/
def explain [StateOrd C] [StateOrd P] [Repr C] [Repr P] (fuel : ℕ := 100000) : String :=
  let cmpC : C → C → Ordering := StateOrd.cmp
  let cmpQ : C × P → C × P → Ordering := StateOrd.cmp
  let pairs := N.mkPairs cmpQ fuel
  let ok := fun esc => N.checkCert cmpC cmpQ esc pairs (N.mkRanks cmpC esc pairs)
  if ok N.route then
    "deadlock and livelock free: acyclic channel dependency graph (Dally–Seitz) and a ranking"
  else if ok N.firstHop then
    "deadlock and livelock free: the first-listed hops are acyclic escape channels (Duato) and \
      a ranking"
  else N.diagnose cmpC cmpQ N.route fuel

end Network

end AsyncLean
