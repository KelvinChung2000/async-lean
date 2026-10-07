/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Check

/-!
# Maximally adaptive routing

A routing function is *more adaptive* than another when it permits every hop the other permits,
and more.  More adaptivity is what a congestion-aware selection function exploits: it has more
free channels to choose from.  This file makes "no further improvement is possible" precise and
checkable.

## Comparing networks

* `N.Extends N'` : `N'` has the same arrivals and injections as `N` and permits every hop of `N`
  (at every pair where the packet has not arrived).
* `N.Within U` : every hop of `N` is a hop of `U`, for example a minimal hop on some virtual
  channel (`U` fixes the channels, the topology and, for minimal routing, the path lengths).
* `N.PairReachable q` : a packet of `N` can occupy the pair `q` (channel and header).
* `N.MaximallyAdaptive U` : every **deadlock-free** network within `U` that extends `N` permits
  no other hop than `N`, at any pair a packet of `N` can occupy.  In other words, *any* set of
  hops of `U` added to `N` introduces a deadlock.  Together with `N.Correct` and `N.Within U`,
  this says that `N` is a maximal element of the deadlock- and livelock-free routing functions
  within `U`, ordered by adaptivity.

## Results

* `not_deadlockFree_of_refuteBetweenB` : a run under a routing function `lo` that ends in a
  configuration where every packet is blocked under a routing function `hi` refutes deadlock
  freedom of every network permitting at least `lo` and at most `hi`.  This is the
  refutation `not_deadlockFree_of_refuteB` for a whole interval of routing functions at once.
* `not_deadlockFree_of_checkTree` : the same with case splits (`RefTree`) on whether a hop is
  permitted.
* `maximallyAdaptive_of_maxCheck` : soundness of the checker `maxCheck`, which lists the pairs a
  packet can occupy and, for every hop of `U` that `N` does not permit, a refutation tree.
* `MaximallyAdaptive.not_deadlockFree` : if `N` is maximally adaptive and `N₂` permits a hop
  that `N` does not, then **no** deadlock-free network within `U` extends both.  Two maximally
  adaptive networks that differ therefore have no common deadlock-free improvement: there is no
  routing function that is at least as adaptive as every maximal one.
* `not_maximallyAdaptive_of_extends` : a deadlock-free network that strictly extends `N`
  shows that `N` is not maximally adaptive.

The untrusted search `mkMaxCerts` builds the certificate (`async_decide` proves
`N.MaximallyAdaptive U` with it), and `explainMaximal` names a hop that can be added when the
search fails.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*}

/-! ### Comparing routing functions -/

/-- The network with the arrivals and injections of `N`, routed by `R`. -/
def withRoute (N : Network C P) (R : C → P → List (C × P)) : Network C P :=
  { N with route := R }

@[simp] theorem withRoute_arrived (N : Network C P) (R : C → P → List (C × P)) :
    (N.withRoute R).arrived = N.arrived := rfl

@[simp] theorem withRoute_inject (N : Network C P) (R : C → P → List (C × P)) :
    (N.withRoute R).inject = N.inject := rfl

@[simp] theorem withRoute_route (N : Network C P) (R : C → P → List (C × P)) :
    (N.withRoute R).route = R := rfl

theorem withRoute_congr {N N' : Network C P} (ha : N'.arrived = N.arrived)
    (hi : N'.inject = N.inject) (R : C → P → List (C × P)) : N'.withRoute R = N.withRoute R := by
  obtain ⟨a, r, i⟩ := N
  obtain ⟨a', r', i'⟩ := N'
  simp only at ha hi
  subst ha hi
  rfl

/-- `N'` has the arrivals and injections of `N` and permits every hop that `N` permits. -/
structure Extends (N N' : Network C P) : Prop where
  arrived : N'.arrived = N.arrived
  inject : N'.inject = N.inject
  route : ∀ c p q, N.arrived c p = false → q ∈ N.route c p → q ∈ N'.route c p

theorem Extends.refl (N : Network C P) : N.Extends N := ⟨rfl, rfl, fun _ _ _ _ h => h⟩

theorem Extends.trans {N N' N'' : Network C P} (h : N.Extends N') (h' : N'.Extends N'') :
    N.Extends N'' :=
  ⟨h'.arrived.trans h.arrived, h'.inject.trans h.inject, fun c p q ha hq =>
    h'.route c p q (by rw [h.arrived]; exact ha) (h.route c p q ha hq)⟩

/-- Every hop of `N` is a hop of `U`. -/
def Within (U : C → P → List (C × P)) (N : Network C P) : Prop :=
  ∀ c p q, N.arrived c p = false → q ∈ N.route c p → q ∈ U c p

/-- A packet of `N` can occupy the pair `q`: some route of a single packet from an injection
leads to `q`. -/
def PairReachable (N : Network C P) (q : C × P) : Prop :=
  ∃ q₀ ∈ N.inject, Relation.ReflTransGen N.PacketStep q₀ q

theorem pairReachable_of_mem_inject {N : Network C P} {q : C × P} (h : q ∈ N.inject) :
    N.PairReachable q :=
  ⟨q, h, Relation.ReflTransGen.refl⟩

theorem PairReachable.step {N : Network C P} {q q' : C × P} (h : N.PairReachable q)
    (hst : N.PacketStep q q') : N.PairReachable q' :=
  let ⟨q₀, h₀, hr⟩ := h
  ⟨q₀, h₀, hr.tail hst⟩

variable [DecidableEq C]

/-- `N` is **maximally adaptive** among the deadlock-free routing functions within `U`: a
deadlock-free network within `U` that extends `N` permits no further hop at any pair a packet
of `N` can occupy.  Equivalently, adding any non-empty set of hops of `U` to `N` (at pairs its
packets occupy) makes it deadlock. -/
def MaximallyAdaptive (U : C → P → List (C × P)) (N : Network C P) : Prop :=
  ∀ N' : Network C P, N.Extends N' → N'.Within U → N'.DeadlockFree →
    ∀ c p, N.PairReachable (c, p) → N.arrived c p = false → ∀ q ∈ N'.route c p, q ∈ N.route c p

/-- **No common improvement.**  If `N` is maximally adaptive within `U` and `N₂` permits a hop
`q` that `N` does not, at a pair a packet of `N` can occupy, then no deadlock-free network
within `U` permits every hop of both. -/
theorem MaximallyAdaptive.not_deadlockFree {U : C → P → List (C × P)} {N N₂ N' : Network C P}
    (hmax : N.MaximallyAdaptive U) {c : C} {p : P} {q : C × P} (hreach : N.PairReachable (c, p))
    (harr : N.arrived c p = false) (hq₂ : q ∈ N₂.route c p) (hqN : q ∉ N.route c p)
    (h₁ : N.Extends N') (h₂ : N₂.Extends N') (hU : N'.Within U) : ¬ N'.DeadlockFree := by
  intro hD
  have harr₂ : N₂.arrived c p = false := by rw [← h₂.arrived, h₁.arrived]; exact harr
  exact hqN (hmax N' h₁ hU hD c p hreach harr q (h₂.route c p q harr₂ hq₂))

/-- A deadlock-free network within `U` that extends `N` with a new hop, at a pair a packet of
`N` can occupy, shows that `N` is **not** maximally adaptive. -/
theorem not_maximallyAdaptive_of_extends {U : C → P → List (C × P)} {N N' : Network C P}
    (h : N.Extends N') (hU : N'.Within U) (hD : N'.DeadlockFree) {c : C} {p : P} {q : C × P}
    (hreach : N.PairReachable (c, p)) (harr : N.arrived c p = false) (hq' : q ∈ N'.route c p)
    (hq : q ∉ N.route c p) : ¬ N.MaximallyAdaptive U :=
  fun hmax => hq (hmax N' h hU hD c p hreach harr q hq')

/-! ### Refuting a whole interval of routing functions -/

/-- The fully adaptive steps of `N` are steps of every network extending it. -/
theorem StepWith.of_extends {N N' : Network C P} (h : N.Extends N') {f f' : Config C P}
    {a : Act C P} (hs : N.StepWith N.adaptive f a f') : N'.StepWith N'.adaptive f a f' := by
  cases hs with
  | inject h₁ h₂ => exact .inject (by rw [h.inject]; exact h₁) h₂
  | hop h₁ h₂ h₃ h₄ => exact .hop h₁ (by rw [h.arrived]; exact h₂) (h.route _ _ _ h₂ h₃) h₄
  | eject h₁ h₂ => exact .eject h₁ (by rw [h.arrived]; exact h₂)

theorem Path.of_extends {N N' : Network C P} (h : N.Extends N') {f f' : Config C P}
    {as : List (Act C P)} (hp : N.lts.Path f as f') : N'.lts.Path f as f' := by
  induction hp with
  | nil => exact LTS.Path.nil _
  | cons hst _ ih => exact LTS.Path.cons (StepWith.of_extends h hst) ih

variable [DecidableEq P]

/-- A run under the routing function `lo` from the empty network to a non-empty configuration
in which every packet is blocked under the routing function `hi`. -/
def refuteBetweenB (N : Network C P) (lo hi : C → P → List (C × P)) (as : List (Act C P)) :
    Bool :=
  match (N.withRoute lo).runB [] as with
  | some qs => !qs.isEmpty && (N.withRoute hi).stuckB qs
  | none => false

/-- **Refuting every routing function between `lo` and `hi` at once.**  If a run that only uses
hops of `lo` ends in a configuration where every packet is blocked even under `hi`, then every
network that permits the hops of `lo` and only hops of `hi` deadlocks. -/
theorem not_deadlockFree_of_refuteBetweenB {N : Network C P} {lo hi : C → P → List (C × P)}
    {as : List (Act C P)}
    (hlo : ∀ c p q, N.arrived c p = false → q ∈ lo c p → q ∈ N.route c p) (hhi : N.Within hi)
    (h : N.refuteBetweenB lo hi as = true) : ¬ N.DeadlockFree := by
  unfold refuteBetweenB at h
  split at h
  · rename_i qs hrun
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    obtain ⟨hne, hstuck⟩ := h
    intro hD
    have hext : (N.withRoute lo).Extends N := ⟨rfl, rfl, hlo⟩
    have hr : N.lts.Reachable empty (fill qs) :=
      (Path.of_extends hext ((N.withRoute lo).path_of_runB hrun)).reachable
    have hfne : fill qs ≠ empty := by
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
      intro he
      have : fill qs q.1 = none := by rw [he]; rfl
      exact fill_eq_none.1 this (List.mem_map_of_mem hq)
    obtain ⟨a, f', ha, hst⟩ := hD _ N.adaptive_valid _ hr hfne
    have key : ∀ c p, fill qs c = some p →
        N.arrived c p = false ∧ ∀ q' ∈ hi c p, fill qs q'.1 ≠ none := by
      intro c p hp
      have := (List.all_eq_true.1 hstuck) (c, p) (mem_of_fill hp)
      simp only [hp, withRoute_arrived, withRoute_route, Bool.and_eq_true, Bool.not_eq_true',
        List.all_eq_true, Option.isSome_iff_ne_none] at this
      exact this
    change N.StepWith N.adaptive _ a f' at hst
    cases hst with
    | inject => simp [Act.IsMove] at ha
    | hop hp harr hq hfree => exact (key _ _ hp).2 _ (hhi _ _ _ harr hq) hfree
    | eject hp harr => simp [(key _ _ hp).1] at harr
  · simp at h

/-- A refutation certificate for an interval of routing functions, which may split on whether a
hop is permitted. -/
inductive RefTree (C P : Type*) where
  /-- A run refuting the whole interval (`refuteBetweenB`). -/
  | leaf (as : List (Act C P))
  /-- Either the hop from `(c, p)` to `q` is permitted (`yes`) or it is not (`no`). -/
  | split (c : C) (p : P) (q : C × P) (yes no : RefTree C P)
  deriving Repr

/-- Permit the hop from `(c, p)` to `q` as well. -/
def addHop (R : C → P → List (C × P)) (c : C) (p : P) (q : C × P) : C → P → List (C × P) :=
  fun c' p' => if c' = c ∧ p' = p then q :: R c' p' else R c' p'

/-- Remove the hop from `(c, p)` to `q`. -/
def delHop (R : C → P → List (C × P)) (c : C) (p : P) (q : C × P) : C → P → List (C × P) :=
  fun c' p' => if c' = c ∧ p' = p then (R c' p').filter fun x => !decide (x = q) else R c' p'

/-- Check a refutation tree for the routing functions between `lo` and `hi`. -/
def checkTree (N : Network C P) :
    (C → P → List (C × P)) → (C → P → List (C × P)) → RefTree C P → Bool
  | lo, hi, .leaf as => N.refuteBetweenB lo hi as
  | lo, hi, .split c p q t₁ t₂ =>
    N.checkTree (addHop lo c p q) hi t₁ && N.checkTree lo (delHop hi c p q) t₂

theorem checkTree_congr {N N' : Network C P} (ha : N'.arrived = N.arrived)
    (hinj : N'.inject = N.inject) (t : RefTree C P) :
    ∀ lo hi, N'.checkTree lo hi t = N.checkTree lo hi t := by
  induction t with
  | leaf as => intro lo hi; simp only [checkTree, refuteBetweenB, withRoute_congr ha hinj]
  | split c p q t₁ t₂ ih₁ ih₂ => intro lo hi; simp only [checkTree, ih₁, ih₂]

/-- **Soundness of refutation trees**: every network that permits the hops of `lo` and only
hops of `hi` deadlocks. -/
theorem not_deadlockFree_of_checkTree {N : Network C P} (t : RefTree C P) :
    ∀ {lo hi : C → P → List (C × P)},
      (∀ c p q, N.arrived c p = false → q ∈ lo c p → q ∈ N.route c p) → N.Within hi →
      N.checkTree lo hi t = true → ¬ N.DeadlockFree := by
  induction t with
  | leaf as => intro lo hi hlo hhi h; exact not_deadlockFree_of_refuteBetweenB hlo hhi h
  | split c p q t₁ t₂ ih₁ ih₂ =>
    intro lo hi hlo hhi h
    simp only [checkTree, Bool.and_eq_true] at h
    by_cases hq : q ∈ N.route c p
    · refine ih₁ (fun c' p' q' ha hq' => ?_) hhi h.1
      unfold addHop at hq'
      split_ifs at hq' with hcp
      · obtain ⟨rfl, rfl⟩ := hcp
        rcases List.mem_cons.1 hq' with rfl | hq'
        · exact hq
        · exact hlo _ _ _ ha hq'
      · exact hlo _ _ _ ha hq'
    · refine ih₂ hlo (fun c' p' q' ha hq' => ?_) h.2
      unfold delHop
      split_ifs with hcp
      · obtain ⟨rfl, rfl⟩ := hcp
        refine List.mem_filter.2 ⟨hhi _ _ _ ha hq', ?_⟩
        have : q' ≠ q := fun he => hq (he ▸ hq')
        simpa using this
      · exact hhi _ _ _ ha hq'

/-! ### The trusted checker -/

section Check

variable (cmpQ : C × P → C × P → Ordering)

/-- **The trusted checker** for `N.MaximallyAdaptive U`.  `pairs` contains every injected pair
and is closed under the hops of `N`, so it contains every pair a packet can occupy; at every such
pair where the packet has not arrived, every hop of `U` that `N` does not permit has a
refutation tree in `certs` for the routing functions between `N` with that hop and `U`. -/
def maxCheck (N : Network C P) (U : C → P → List (C × P)) (pairs : BTree (C × P))
    (certs : List ((C × P) × (C × P) × RefTree C P)) : Bool :=
  N.inject.all (pairs.find cmpQ) &&
    pairs.all fun x => N.arrived x.1 x.2 ||
      ((N.route x.1 x.2).all (pairs.find cmpQ) &&
        (U x.1 x.2).all fun q => decide (q ∈ N.route x.1 x.2) ||
          certs.any fun e => decide (e.1 = x) && decide (e.2.1 = q) &&
            N.checkTree (addHop N.route x.1 x.2 q) U e.2.2)

end Check

/-- **Soundness of the checker**: a passing certificate proves that `N` is maximally adaptive
within `U`.  The comparison function only guides the search: any function is sound. -/
theorem maximallyAdaptive_of_maxCheck {N : Network C P} {cmpQ : C × P → C × P → Ordering}
    {U : C → P → List (C × P)} {pairs : BTree (C × P)}
    {certs : List ((C × P) × (C × P) × RefTree C P)}
    (h : N.maxCheck cmpQ U pairs certs = true) : N.MaximallyAdaptive U := by
  simp only [maxCheck, Bool.and_eq_true, List.all_eq_true, BTree.all_eq_true, Bool.or_eq_true,
    List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨hinj, hall⟩ := h
  have hmem : ∀ q, N.PairReachable q → q ∈ pairs.toList := by
    rintro q ⟨q₀, hq₀, hr⟩
    induction hr with
    | refl => exact BTree.mem_toList_of_find (hinj q₀ hq₀)
    | tail _ hst ih =>
      obtain ⟨ha, hq⟩ := hst
      rcases hall _ ih with ha' | ⟨hcl, -⟩
      · simp [ha] at ha'
      · exact BTree.mem_toList_of_find (hcl _ hq)
  intro N' hext hU hD c p hreach harr q hq
  by_contra hqN
  rcases hall _ (hmem _ hreach) with ha | ⟨-, hU'⟩
  · simp [harr] at ha
  have hqU : q ∈ U c p := hU c p q (by rw [hext.arrived]; exact harr) hq
  rcases hU' q hqU with hin | ⟨e, -, ⟨he₁, he₂⟩, hchk⟩
  · exact hqN hin
  rw [← checkTree_congr hext.arrived hext.inject] at hchk
  refine not_deadlockFree_of_checkTree e.2.2 (fun c' p' q' ha hq' => ?_) hU hchk hD
  have ha' : N.arrived c' p' = false := by rw [← hext.arrived]; exact ha
  unfold addHop at hq'
  split_ifs at hq' with hcp
  · obtain ⟨rfl, rfl⟩ := hcp
    rcases List.mem_cons.1 hq' with rfl | hq'
    · exact hq
    · exact hext.route _ _ _ ha' hq'
  · exact hext.route _ _ _ ha' hq'

/-! ### Untrusted certificate search

Nothing below needs to be correct: a wrong answer only makes the check fail.  For every hop of
`U` that `N` does not permit, the search looks for a configuration in which every packet is
blocked under `U` and that the network with the new hop can reach (`fillAll`).  When there is
none, it takes a configuration blocked under the routing function so far, splits on a hop of `U`
that would free one of its packets, and searches both branches. -/

section Search

variable (cmpC : C → C → Ordering) (cmpQ : C × P → C × P → Ordering)

/-- The greatest set of pairs every one of whose `hops` leads to a channel of the set. -/
def stuckPairs (hops : C → P → List (C × P)) : ℕ → List (C × P) → List (C × P)
  | 0, l => l
  | n + 1, l =>
    let s : BStore C := l.foldl (fun t x => t.push cmpC x.1) {}
    let l' := l.filter fun x => (hops x.1 x.2).all fun q => s.find cmpC q.1
    if l'.length = l.length then l else stuckPairs hops n l'

/-- Greedily fill the `pending` channels with packets from `opts`, preferring the packet whose
hops need the fewest new channels, until every hop of every packet is occupied. -/
def closeGreedy (hops : C → P → List (C × P)) (opts : C → List P) :
    ℕ → List (C × P) → List C → List (C × P)
  | 0, cfg, _ => cfg
  | _, cfg, [] => cfg
  | fuel + 1, cfg, c :: pending =>
    if cfg.any (·.1 == c) then closeGreedy hops opts fuel cfg pending else
    let fresh := fun d : P => ((hops c d).map Prod.fst).filter fun c' => !cfg.any (·.1 == c')
    match (opts c).foldl (fun (best : Option (P × ℕ)) d =>
        let n := (fresh d).length
        match best with
        | some (_, m) => if n < m then some (d, n) else best
        | none => some (d, n)) none with
    | none => cfg
    | some (d, _) => closeGreedy hops opts fuel ((c, d) :: cfg) (pending ++ fresh d)

/-- Route the packets of `items` into place one at a time, each from an injection through free
channels; returns the actions. -/
def placeAll (M : Network C P) (fuel : ℕ) :
    ℕ → List (C × P) → List C → List (Act C P) → Option (List (Act C P))
  | 0, _, _, _ => none
  | _, [], _, acc => some acc
  | n + 1, items, occ, acc =>
    match items.findSome? (fun it => (M.routeTo cmpQ occ it fuel).map (it, ·)) with
    | none => none
    | some (it, path) => placeAll M fuel n (items.erase it) (it.1 :: occ) (acc ++ runAlong path)

/-- A run filling the configuration `cfg` under the routing of `M`. -/
def fillAll (M : Network C P) (fuel : ℕ) (cfg : List (C × P)) : Option (List (Act C P)) :=
  match placeAll cmpQ M fuel (cfg.length + 1) cfg [] [] with
  | some as => some as
  | none => placeAll cmpQ M fuel (cfg.length + 1) cfg.reverse [] []

/-- A reachable configuration of `M` that contains `x`, in which every packet is blocked under
`hops`, and a run reaching it. -/
def blockedAt (M : Network C P) (hops : C → P → List (C × P)) (live : List (C × P))
    (fuel : ℕ) (x : C × P) : Option (List (C × P) × List (Act C P)) :=
  let kept := stuckPairs cmpC hops (live.length + 1) live
  if !kept.contains x then none else
  let opts := fun c => (kept.filter (·.1 == c)).map Prod.snd
  let cfg := closeGreedy hops opts (kept.length + 1) [x] ((hops x.1 x.2).map Prod.fst)
  (fillAll cmpQ M fuel cfg).map (cfg, ·)

/-- Search a refutation tree for the routing functions between `lo` and `hi`.  `old` holds the
pairs of `N` itself: a refutation must use one of the new pairs. -/
def solveTree (N : Network C P) (old : BStore (C × P)) (fuel : ℕ) :
    ℕ → (C → P → List (C × P)) → (C → P → List (C × P)) → Option (RefTree C P)
  | depth, lo, hi =>
    let M := N.withRoute lo
    let live := ((M.explorePairs cmpQ fuel).toListAcc []).filter fun x => !N.arrived x.1 x.2
    let news := live.filter fun x => !old.find cmpQ x
    match news.findSome? (blockedAt cmpC cmpQ M hi live fuel) with
    | some (_, as) => some (.leaf as)
    | none =>
      match depth with
      | 0 => none
      | d + 1 => news.findSome? fun x =>
        match blockedAt cmpC cmpQ M lo live fuel x with
        | none => none
        | some (cfg, _) =>
          let free := cfg.flatMap fun e =>
            ((hi e.1 e.2).filter fun q => !cfg.any (·.1 == q.1)).map (e, ·)
          match free.head? with
          | none => none
          | some ((c, p), q) => do
            let yes ← solveTree N old fuel d (addHop lo c p q) hi
            let no ← solveTree N old fuel d lo (delHop hi c p q)
            pure (.split c p q yes no)

/-- The hops of `U` that `N` does not permit, at the pairs its packets can occupy. -/
def extraHops (N : Network C P) (U : C → P → List (C × P)) (fuel : ℕ) :
    List ((C × P) × (C × P)) :=
  ((N.explorePairs cmpQ fuel).toListAcc []).flatMap fun x =>
    if N.arrived x.1 x.2 then [] else
      ((U x.1 x.2).filter fun q => !(N.route x.1 x.2).contains q).map (x, ·)

/-- The certificate for `maxCheck`: a refutation tree for every extra hop, or the first extra
hop for which none was found. -/
def mkMaxCerts (N : Network C P) (U : C → P → List (C × P)) (fuel : ℕ) (depth : ℕ := 2) :
    Except ((C × P) × (C × P)) (List ((C × P) × (C × P) × RefTree C P)) :=
  let old : BStore (C × P) :=
    ((N.explorePairs cmpQ fuel).toListAcc []).foldl (fun s x => s.push cmpQ x) {}
  (N.extraHops cmpQ U fuel).mapM fun (x, q) =>
    match solveTree cmpC cmpQ N old fuel depth (addHop N.route x.1 x.2 q) U with
    | some t => .ok (x, q, t)
    | none => .error (x, q)

/-- The certificate list, empty when the search fails (the check then fails). -/
def maxCerts (N : Network C P) (U : C → P → List (C × P)) (fuel : ℕ) (depth : ℕ := 2) :
    List ((C × P) × (C × P) × RefTree C P) :=
  match N.mkMaxCerts cmpC cmpQ U fuel depth with
  | .ok certs => certs
  | .error _ => []

variable [Repr C] [Repr P]

/-- Explain the outcome of the search for a maximality certificate. -/
def explainMaximal (N : Network C P) (U : C → P → List (C × P)) (fuel : ℕ := 100000)
    (depth : ℕ := 2) : String :=
  let extra := N.extraHops cmpQ U fuel
  match N.mkMaxCerts cmpC cmpQ U fuel depth with
  | .ok certs =>
    s!"maximally adaptive: each of the {extra.length} hops of U that the network does not \
      permit introduces a deadlock ({(certs.filter fun e => e.2.2 matches .split ..).length} \
      of them after a case split)"
  | .error (x, q) =>
    s!"no deadlock found when the hop {reprStr x} → {reprStr q} is added: the network may not \
      be maximally adaptive (check `N.withRoute (addHop N.route ...)` with `async_decide`)"

end Search

end Network

end AsyncLean
