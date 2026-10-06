/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Wormhole
import AsyncLean.Routing.Check

/-!
# Checking wormhole routing

The trusted checker `Network.wcheckCert` for `Network.WormholeCorrect`, the untrusted search
for its certificates and a diagnosis of failures.  A certificate lists the legal pairs with
livelock ranks (as for store-and-forward switching), ranks for the escape channels `E` that
decrease along Duato's extended dependency graph, and for each pair a lower bound `lo` on the
rank of the escape channel the packet last passed:

* at a pair in an escape channel, `lo` is at most the rank of that channel;
* a hop to a non-escape channel does not increase `lo`;
* every escape channel requested from a pair has rank below its `lo`.

Then every edge `e → e'` of the extended dependency graph decreases the rank, so the graph is
acyclic (`wormholeCorrect_of_wcheckCert`).
-/

namespace AsyncLean

namespace Network

variable {C P : Type*} [DecidableEq C] [DecidableEq P] (N : Network C P)

/-! ### The trusted checker -/

section Check

variable (cmpC : C → C → Ordering) (cmpQ : C × P → C × P → Ordering)

/-- The local conditions at one pair `q` for the escape channels `E`. -/
def wcheckPair (E : C → Bool) (pairs : BTree ((C × P) × ℕ)) (ranks : BTree (C × ℕ))
    (lo : BTree ((C × P) × ℕ)) (q : C × P) : Bool :=
  (!E q.1 || decide (pairRank cmpQ lo q ≤ chanRank cmpC ranks q.1)) &&
    (N.arrived q.1 q.2 ||
      ((N.route q.1 q.2).all (fun q' => legalB cmpQ pairs q' &&
          decide (pairRank cmpQ pairs q' < pairRank cmpQ pairs q) &&
          (if E q'.1 then decide (chanRank cmpC ranks q'.1 < pairRank cmpQ lo q)
           else decide (pairRank cmpQ lo q' ≤ pairRank cmpQ lo q))) &&
        (N.route q.1 q.2).any fun q' => E q'.1))

/-- **The trusted wormhole checker.** -/
def wcheckCert (E : C → Bool) (pairs : BTree ((C × P) × ℕ)) (ranks : BTree (C × ℕ))
    (lo : BTree ((C × P) × ℕ)) : Bool :=
  N.inject.all (legalB cmpQ pairs) &&
    pairs.all fun e => N.wcheckPair cmpC cmpQ E pairs ranks lo e.1

end Check

/-- **Soundness of the wormhole checker**: a passing certificate proves deadlock and livelock
freedom under wormhole switching, for packets of every length and every selection function. -/
theorem wormholeCorrect_of_wcheckCert {N : Network C P} {cmpC : C → C → Ordering}
    {cmpQ : C × P → C × P → Ordering} {E : C → Bool} {pairs : BTree ((C × P) × ℕ)}
    {ranks : BTree (C × ℕ)} {lo : BTree ((C × P) × ℕ)}
    (h : N.wcheckCert cmpC cmpQ E pairs ranks lo = true) : N.WormholeCorrect := by
  simp only [wcheckCert, Bool.and_eq_true, List.all_eq_true, BTree.all_eq_true] at h
  obtain ⟨hinj, hall⟩ := h
  let legal : C → P → Prop := fun c p => legalB cmpQ pairs (c, p) = true
  have hpair : ∀ c p, legal c p → N.wcheckPair cmpC cmpQ E pairs ranks lo (c, p) = true := by
    intro c p hl
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hl
    exact hall _ (BTree.mem_toList_of_findData hr)
  have hesc : ∀ c p, legal c p → E c = true →
      pairRank cmpQ lo (c, p) ≤ chanRank cmpC ranks c := by
    intro c p hl hE
    have := hpair c p hl
    simp only [wcheckPair, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at this
    rcases this.1 with h | h
    · simp [hE] at h
    · exact h
  have hmove : ∀ c p, legal c p → N.arrived c p = false →
      (∀ q ∈ N.route c p, legalB cmpQ pairs q = true ∧
        pairRank cmpQ pairs q < pairRank cmpQ pairs (c, p) ∧
        (if E q.1 then chanRank cmpC ranks q.1 < pairRank cmpQ lo (c, p)
         else pairRank cmpQ lo q ≤ pairRank cmpQ lo (c, p))) ∧
      ∃ q ∈ N.route c p, E q.1 = true := by
    intro c p hl ha
    have := hpair c p hl
    simp only [wcheckPair, ha, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
      List.any_eq_true, decide_eq_true_eq] at this
    refine ⟨fun q hq => ?_, this.2.2⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := this.2.1 q hq
    refine ⟨h1, h2, ?_⟩
    split_ifs at h3 ⊢ <;> simpa using h3
  have hcl : N.Closed legal :=
    ⟨fun q hq => hinj q hq, fun c p q hl ha hq => ((hmove c p hl ha).1 q hq).1⟩
  -- along non-escape channels the bound `lo` only decreases
  have hne : ∀ e q, N.NE legal (fun c => E c = true) e q →
      legal q.1 q.2 ∧ pairRank cmpQ lo q ≤ chanRank cmpC ranks e := by
    intro e q hq
    induction hq with
    | base hl hE => exact ⟨hl, hesc _ _ hl hE⟩
    | @step q q' _ ha hr hE ih =>
      obtain ⟨h1, h2, h3⟩ := (hmove q.1 q.2 ih.1 ha).1 q' hr
      rw [ite_eq_right hE] at h3
      exact ⟨h1, h3.trans ih.2⟩
  refine ⟨N.wormholeDeadlockFree_of_escape (E := fun c => E c = true) hcl
    (fun c p hl ha => (hmove c p hl ha).2)
    (wf_of_rank (chanRank cmpC ranks) ?_),
    N.wormholeLivelockFree_of_ranking hcl (fun c p => pairRank cmpQ pairs (c, p))
      (fun c p q hl ha hq => ((hmove c p hl ha).1 q hq).2.1)⟩
  rintro e e' ⟨q, hq, ha, p', hr, hE⟩
  obtain ⟨hl, hlo⟩ := hne e q hq
  have h3 := ((hmove q.1 q.2 hl ha).1 (e', p') hr).2.2
  rw [ite_eq_left hE] at h3
  exact lt_of_lt_of_le h3 hlo

/-! ### Untrusted certificate search -/

section Search

variable (cmpC : C → C → Ordering) (cmpQ : C × P → C × P → Ordering)

/-- The channels of the first-listed hops: the default escape channels. -/
def firstHopChans (pairs : List (C × P)) : BTree C :=
  (pairs.foldl (fun (t : BStore C) q =>
    if N.arrived q.1 q.2 then t else
      match (N.route q.1 q.2).head? with
      | some q' => if t.tree.find cmpC q'.1 then t else t.push cmpC q'.1
      | none => t) {}).tree

/-- The pairs reachable from `starts` through hops to non-escape channels. -/
def neReach (E : C → Bool) : ℕ → List (C × P) → BTree (C × P) → BTree (C × P)
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, q :: stack, seen =>
    let r := (N.packetExplicit.succ q).foldl (fun (acc : List (C × P) × BTree (C × P)) e =>
      if E e.2.1 || acc.2.find cmpQ e.2 then acc else (e.2 :: acc.1, acc.2.insert cmpQ e.2))
      (stack, seen)
    neReach E fuel r.1 r.2

/-- For each escape channel, the pairs a packet holding it can reach through non-escape
channels. -/
def escReach (E : C → Bool) (pairs : List (C × P)) (fuel : ℕ) : List (C × List (C × P)) :=
  let escs := (pairs.filter fun q => E q.1).foldl (fun (l : List C) q =>
    if l.contains q.1 then l else q.1 :: l) []
  escs.map fun e =>
    let starts := pairs.filter fun q => q.1 == e
    (e, (N.neReach cmpQ E fuel starts (starts.foldl (fun t q => t.insert cmpQ q) .leaf)).toList)

/-- The extended dependency graph, as adjacency lists. -/
def extGraph (E : C → Bool) (reach : List (C × List (C × P))) : BTree (C × List C) :=
  (reach.foldl (fun (acc : BStore (C × List C)) r =>
    let succs := r.2.flatMap fun q =>
      if N.arrived q.1 q.2 then [] else ((N.route q.1 q.2).filter fun q' => E q'.1).map Prod.fst
    acc.pushKV cmpC r.1 succs) {}).tree

/-- Candidate certificate: escape-channel ranks and the bounds `lo`. -/
def mkWCert (E : C → Bool) (pairs : BTree ((C × P) × ℕ)) (fuel : ℕ) :
    BTree (C × ℕ) × BTree ((C × P) × ℕ) :=
  let ps := (pairs.toListAcc []).map Prod.fst
  let reach := N.escReach cmpQ E ps fuel
  let g := N.extGraph cmpC E reach
  let ranks := (depExplicit cmpC g).autoRank cmpC (fun _ => true)
    (BTree.ofList ((g.toListAcc []).map Prod.fst))
  let big := (ranks.toListAcc []).foldl (fun m e => max m (e.2 + 1)) 1
  let lo0 : BStore ((C × P) × ℕ) := ps.foldl (fun t q => t.pushKV cmpQ q big) {}
  let lo := reach.foldl (fun t r =>
    let d := chanRank cmpC ranks r.1
    r.2.foldl (fun t q => t.pushKV cmpQ q (min d ((t.tree.lookup cmpQ q).getD big))) t) lo0
  (ranks, lo.tree.rebalance)

/-- Membership in a tree of channels, as an escape predicate. -/
def inTree (t : BTree C) : C → Bool := fun c => t.find cmpC c

/-- The default escape channels: those of the first-listed hops of the listed pairs. -/
def firstHopEscapes (pairs : BTree ((C × P) × ℕ)) : BTree C :=
  N.firstHopChans cmpC ((pairs.toListAcc []).map Prod.fst)

end Search

/-! ### Diagnosis (untrusted) -/

section Diagnose

variable (cmpC : C → C → Ordering) (cmpQ : C × P → C × P → Ordering)

/-- A store-and-forward run as a wormhole run (for packets of length one). -/
def toWActs : List (Act C P) → List (WAct C P)
  | [] => []
  | .inject c p :: as => .inject c p :: toWActs as
  | .hop c c' p' :: as => .advance c c' p' :: toWActs as
  | .eject c :: as => .eject c :: toWActs as

variable [Repr C] [Repr P]

private def wactStr : WAct C P → String
  | .inject c p => s!".inject {reprArg c} {reprArg p}"
  | .advance c c' p' => s!".advance {reprArg c} {reprArg c'} {reprArg p'}"
  | .drain c => s!".drain {reprArg c}"
  | .eject c => s!".eject {reprArg c}"

private def wactsStr (as : List (WAct C P)) : String :=
  "[" ++ ", ".intercalate (as.map wactStr) ++ "]"

/-- Explain why `wcheckCert` fails for the escape channels `E`. -/
def wdiagnose (E : C → Bool) (fuel : ℕ := 100000) : String :=
  let pairs := (N.explorePairs cmpQ fuel).toListAcc []
  if pairs.length ≥ fuel then
    s!"more than {fuel} reachable (channel, header) pairs; increase the fuel"
  else
  let live := pairs.filter fun q => !N.arrived q.1 q.2
  let one : P → ℕ := fun _ => 0
  let sfx (as : List (WAct C P)) : String :=
    if N.wrefuteDeadlockB one as then
      s!"\nProve it with: Network.not_wormholeDeadlockFree_of_refuteB (tail := fun _ => 0) \
        (as := {wactsStr as}) (by decide +kernel)"
    else ""
  match live.find? fun q => (N.route q.1 q.2).isEmpty with
  | some q =>
    let msg := s!"DEADLOCK: the packet ({reprStr q.1}, {reprStr q.2}) has not arrived and has \
      no permitted hop."
    match N.routeTo cmpQ [] q fuel with
    | some path => msg ++ sfx (toWActs (runAlong path))
    | none => msg
  | none =>
  let succ := fun q : C × P => (N.packetExplicit.succ q).map Prod.snd
  match (findCycle succ cmpQ fuel N.inject).bind fun path => path.getLast?.map (path, ·) with
  | some (path, last) =>
    let pre := path.takeWhile (· != last)
    let cyc := path.dropWhile (· != last)
    let preActs := toWActs (runAlong (pre ++ [last]))
    let cycActs := toWActs (hopsAlong cyc)
    let msg := "LIVELOCK: a packet can be routed around a cycle forever."
    if N.wrefuteLivelockB one preActs cycActs then
      s!"{msg}\nProve it with: Network.not_wormholeLivelockFree_of_refuteB \
        (tail := fun _ => 0) (pre := {wactsStr preActs}) (cyc := {wactsStr cycActs}) \
        (by decide +kernel)"
    else msg
  | none =>
  match live.find? fun q => !(N.route q.1 q.2).any fun q' => E q'.1 with
  | some q => s!"the packet ({reprStr q.1}, {reprStr q.2}) has no permitted hop into an escape \
      channel."
  | none =>
  let g := N.extGraph cmpC E (N.escReach cmpQ E pairs fuel)
  let csucc := fun c : C => (g.lookup cmpC c).getD []
  match (findCycle csucc cmpC fuel ((g.toListAcc []).map Prod.fst)).bind
      fun cpath => cpath.getLast?.map (cpath, ·) with
  | some (cpath, last) =>
    let cyc := cpath.dropWhile (· != last)
    let cycStr := " → ".intercalate (cyc.map reprStr)
    let msg := s!"the extended channel dependency graph of the escape channels has the cycle \
      {cycStr}."
    match N.deadlockAttempt cmpQ cyc.tail fuel with
    | some as =>
      let was := toWActs as
      if N.wrefuteDeadlockB one was then s!"DEADLOCK: {msg}{sfx was}"
      else s!"POTENTIAL DEADLOCK: {msg} Choose other escape channels with \
        `async_routing (escape := E)`."
    | none => s!"POTENTIAL DEADLOCK: {msg} Choose other escape channels with \
        `async_routing (escape := E)`."
  | none => "the certificate check failed"

end Diagnose

/-- `#eval N.explainWormhole` reports what `async_decide` finds for `N` under wormhole
switching. -/
def explainWormhole [StateOrd C] [StateOrd P] [Repr C] [Repr P] (fuel : ℕ := 100000) :
    String :=
  let cmpC : C → C → Ordering := StateOrd.cmp
  let cmpQ : C × P → C × P → Ordering := StateOrd.cmp
  let pairs := N.mkPairs cmpQ fuel
  let ok := fun E => let r := N.mkWCert cmpC cmpQ E pairs fuel
    N.wcheckCert cmpC cmpQ E pairs r.1 r.2
  let fh := N.firstHopChans cmpC ((pairs.toListAcc []).map Prod.fst)
  if ok fun _ => true then
    "deadlock and livelock free under wormhole switching: acyclic channel dependency graph \
      (Dally–Seitz) and a ranking"
  else if ok fun c => fh.find cmpC c then
    "deadlock and livelock free under wormhole switching: the channels of the first-listed \
      hops are escape channels with an acyclic extended dependency graph (Duato) and a ranking"
  else N.wdiagnose cmpC cmpQ (fun _ => true) fuel

end Network

end AsyncLean
