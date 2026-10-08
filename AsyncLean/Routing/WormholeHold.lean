/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.WormholeFairness
import AsyncLean.Routing.WormholeCheck

/-!
# Wormhole deadlock freedom beyond Duato's condition

Duato's condition (`Network.wormholeDeadlockFree_of_escape`) is sufficient for deadlock freedom
under wormhole switching, and for store-and-forward switching it is also necessary
(`Network.staticDeadlockFree_iff_exists_escape`).  Under wormhole switching it is **not**
necessary (`Examples/DuatoWormhole.lean`): a channel that only packets at their destination
can hold never blocks anyone for long, but Duato's extended dependency graph still counts
the dependencies through it.

This file gives a sufficient condition that sees this, checkable on small networks:

* `Network.WChain` — the flits of a packet follow its route: each flit after the head holds a
  pair that has not arrived, and the flit before it holds one of its permitted hops.  So only
  a head can have arrived, and a packet at its destination can always drain or leave.
* `Network.wormholeDeadlockFree_of_holds` — for every nonempty set `H` of pairs that blocked
  heads could hold, some set `S ⊇ H` closed under "has a permitted hop into `S`" (it contains
  every flit of a packet whose head is in `H`) leaves a permitted hop of some head of `H`
  free.  Then no reachable configuration is stuck, for packets of every length and every
  selection function.
* `Network.wholdCheck` — the condition as a Boolean over the sublists of the pairs that have
  not arrived, for the kernel (`Network.wormholeDeadlockFree_of_wholdCheck`).
-/

namespace AsyncLean

namespace Network

variable {C P : Type*} (N : Network C P)

/-- The flits of every packet follow its route: the pair after each flit has not arrived, and
the flit's pair is one of its permitted hops. -/
def WChain (w : WConfig C P) : Prop :=
  ∀ x ∈ w, x.IsChain fun a b => N.arrived b.1 b.2 = false ∧ a ∈ N.route b.1 b.2

theorem wchain_step {tail : P → ℕ} {sel : WSelection C P} (hsel : N.WValidSel sel)
    {w w' : WConfig C P} {a : WAct C P} (hw : N.WChain w) (h : N.WStep tail sel w a w') :
    N.WChain w' := by
  cases h with
  | inject =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact List.isChain_singleton _
    · exact hw x hx
  | @advance l₁ l₂ c c' p p' rest harr hq _ =>
    intro x hx
    rcases mem_replace (y := (c, p) :: rest) hx with rfl | hx
    · refine List.IsChain.cons ((hw _ mem_mid).take _) ?_
      intro y hy
      cases n : tail p' with
      | zero => simp [n] at hy
      | succ n' =>
        rw [n, List.take_succ_cons, List.head?_cons, Option.mem_some_iff] at hy
        subst hy
        exact ⟨harr, hsel.sub _ _ _ _ hq⟩
    · exact hw x hx
  | @drain l₁ l₂ c p q rest _ =>
    intro x hx
    rcases mem_replace (y := (c, p) :: q :: rest) hx with rfl | hx
    · have := (hw _ mem_mid).take (rest.length + 1)
      have e : (q :: rest).dropLast = (q :: rest).take rest.length := by
        rw [List.dropLast_eq_take]; simp
      rwa [List.take_succ_cons, ← e] at this
    · exact hw x hx
  | eject _ => exact fun x hx => hw x (mem_of_mem_remove hx)

/-- Every flit of a packet whose head lies in `S` lies in `S`, when `S` contains every legal
pair that has not arrived and has a permitted hop into `S`. -/
theorem mem_of_chain {legal : C → P → Prop} {S : Set (C × P)}
    (hS : ∀ q : C × P, legal q.1 q.2 → N.arrived q.1 q.2 = false →
      (∃ q' ∈ N.route q.1 q.2, q' ∈ S) → q ∈ S) :
    ∀ {x : Worm C P} {a : C × P}, (a :: x).IsChain
      (fun a b => N.arrived b.1 b.2 = false ∧ a ∈ N.route b.1 b.2) →
      (∀ q ∈ x, legal q.1 q.2) → a ∈ S → ∀ q ∈ x, q ∈ S
  | [], _, _, _, _, q, hq => absurd hq List.not_mem_nil
  | b :: x, a, hc, hl, ha, q, hq => by
    rw [List.isChain_cons_cons] at hc
    have hb : b ∈ S := hS b (hl b List.mem_cons_self) hc.1.1 ⟨a, hc.1.2, ha⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hb
    · exact mem_of_chain hS hc.2 (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hb q hq

/-- **Wormhole deadlock freedom from blocking sets.**  `na` lists the legal pairs that have not
arrived.  If for every nonempty sublist `H` of `na` some set `S ⊇ H`, closed under having a
permitted hop into it, leaves a permitted hop of some pair of `H` on a channel outside `S`,
the network is deadlock free under wormhole switching, for packets of every length and every
selection function. -/
theorem wormholeDeadlockFree_of_holds {legal : C → P → Prop} (hcl : N.Closed legal)
    (na : List (C × P)) (hna : ∀ c p, legal c p → N.arrived c p = false → (c, p) ∈ na)
    (hchk : ∀ H : List (C × P), H.Sublist na → H ≠ [] → ∃ S : List (C × P),
      (∀ h ∈ H, h ∈ S) ∧ (∀ q ∈ na, (∃ q' ∈ N.route q.1 q.2, q' ∈ S) → q ∈ S) ∧
      ∃ h ∈ H, ∃ q ∈ N.route h.1 h.2, ∀ s ∈ S, s.1 ≠ q.1) :
    N.WormholeDeadlockFree := by
  classical
  intro tail sel hsel w hw hne
  have hinv : (N.wltsWith tail sel).Reachable [] w → WHeads legal w ∧ WLegal legal w ∧
      N.WChain w := fun h =>
    h.invariant (I := fun w => WHeads legal w ∧ WLegal legal w ∧ N.WChain w)
      ⟨fun _ hx => absurd hx List.not_mem_nil, fun _ hx => absurd hx List.not_mem_nil,
        fun _ hx => absurd hx List.not_mem_nil⟩
      fun _ _ _ ⟨hh, hl, hc⟩ hst =>
        ⟨N.wheads_step hcl hsel hh hst, N.wlegal_step hcl hsel hl hst, N.wchain_step hsel hc hst⟩
  obtain ⟨hh, hl, hc⟩ := hinv hw
  by_contra hmov
  -- every head has not arrived, and all its permitted hops are on occupied channels
  have hhead : ∀ c p rest, ((c, p) :: rest) ∈ w →
      N.arrived c p = false ∧ ∀ q ∈ N.route c p, w.Occ q.1 := by
    intro c p rest hx
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
    cases harr : N.arrived c p with
    | true =>
      cases rest with
      | nil => exact absurd ⟨.eject c, _, rfl, WStep.eject harr⟩ hmov
      | cons q rest => exact absurd ⟨.drain c, _, rfl, WStep.drain harr⟩ hmov
    | false =>
      refine ⟨rfl, fun q hq => ?_⟩
      by_contra hfree
      obtain ⟨⟨c'', p''⟩, hq', hfree'⟩ := hsel.conserving _ c p ⟨q, hq, hfree⟩
      exact hmov ⟨.advance c c'' p'', _, rfl, WStep.advance harr hq' hfree'⟩
  -- the heads
  let H := na.filter fun q => decide (∃ rest, (q :: rest) ∈ w)
  have hHne : H ≠ [] := by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil w hne
    obtain ⟨⟨c, p⟩, rest, rfl, hlg⟩ := hh x hx
    have hna' := hna c p hlg (hhead c p rest hx).1
    exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hna', decide_eq_true ⟨rest, hx⟩⟩)
  obtain ⟨S, hHS, hclS, h, hhH, q, hq, hfree⟩ := hchk H List.filter_sublist hHne
  -- every flit lies in `S`
  have hall : ∀ x ∈ w, ∀ s ∈ x, s ∈ S := by
    intro x hx s hs
    obtain ⟨⟨c, p⟩, rest, rfl, hlg⟩ := hh x hx
    have hcS : (c, p) ∈ S := hHS _ (List.mem_filter.2
      ⟨hna c p hlg (hhead c p rest hx).1, decide_eq_true ⟨rest, hx⟩⟩)
    rcases List.mem_cons.1 hs with rfl | hs
    · exact hcS
    · refine N.mem_of_chain (legal := legal) (S := {s | s ∈ S}) (fun q hq ha hex => ?_) (hc _ hx)
        (fun q hq => hl _ hx q (List.mem_cons_of_mem _ hq)) hcS s hs
      exact hclS q (hna q.1 q.2 hq ha) hex
  -- the head `h` is blocked on `q`, whose channel is held by a flit of `S`
  obtain ⟨rest, hx⟩ := of_decide_eq_true (List.mem_filter.1 hhH).2
  obtain ⟨y, hy, s, hs, hsq⟩ := (hhead h.1 h.2 rest hx).2 q hq
  exact hfree s (hall y hy s hs) hsq

/-! ### The Boolean check -/

section Check

variable [DecidableEq C] [DecidableEq P]

/-- One round of the closure: add the pairs of `na` with a permitted hop into `S`. -/
def holdStep (na S : List (C × P)) : List (C × P) :=
  S ++ na.filter fun q => !decide (q ∈ S) && (N.route q.1 q.2).any fun q' => decide (q' ∈ S)

/-- `n` rounds of the closure. -/
def holdN (na : List (C × P)) : ℕ → List (C × P) → List (C × P)
  | 0, S => S
  | n + 1, S => holdN na n (N.holdStep na S)

/-- The check for one set `H` of heads, with its closure `S`. -/
def blockB (na H S : List (C × P)) : Bool :=
  H.all (fun h => decide (h ∈ S)) &&
    na.all (fun q => !(N.route q.1 q.2).any (fun q' => decide (q' ∈ S)) || decide (q ∈ S)) &&
    H.any fun h => (N.route h.1 h.2).any fun q => S.all fun s => !decide (s.1 = q.1)

/-- **The blocking-set check** over the nonempty sublists of `na`. -/
def wholdCheck (na : List (C × P)) : Bool :=
  na.sublists.all fun H => H.isEmpty || N.blockB na H (N.holdN na na.length H)

theorem wormholeDeadlockFree_of_wholdCheck {legal : C → P → Prop} (hcl : N.Closed legal)
    (na : List (C × P)) (hna : ∀ c p, legal c p → N.arrived c p = false → (c, p) ∈ na)
    (h : N.wholdCheck na = true) : N.WormholeDeadlockFree := by
  refine N.wormholeDeadlockFree_of_holds hcl na hna fun H hH hne => ?_
  have := List.all_eq_true.1 h H (List.mem_sublists.2 hH)
  simp only [List.isEmpty_iff, hne, decide_false, Bool.false_or, blockB, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_false, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  obtain ⟨⟨hHS, hcl'⟩, h, hhH, q, hq, hfree⟩ := this.resolve_left id
  refine ⟨_, hHS, fun q' hq' ⟨q'', hq'', hS⟩ => ?_, h, hhH, q, hq, fun s hs => ?_⟩
  · rcases hcl' q' hq' with h1 | h1
    · exact absurd hS (h1 q'' hq'')
    · exact h1
  · simpa using hfree s hs

/-- **The blocking-set certificate**: the listed pairs `pairs` contain the injected pairs and
are closed under permitted hops, and the blocking-set check holds for those that have not
arrived. -/
def wholdCert (cmpQ : C × P → C × P → Ordering) (pairs : BTree ((C × P) × ℕ)) : Bool :=
  N.inject.all (legalB cmpQ pairs) &&
    pairs.all (fun e => N.arrived e.1.1 e.1.2 || (N.route e.1.1 e.1.2).all (legalB cmpQ pairs)) &&
    N.wholdCheck ((pairs.toList.map (·.1)).filter fun q => !N.arrived q.1 q.2)

theorem wormholeDeadlockFree_of_wholdCert {cmpQ : C × P → C × P → Ordering}
    {pairs : BTree ((C × P) × ℕ)} (h : N.wholdCert cmpQ pairs = true) :
    N.WormholeDeadlockFree := by
  simp only [wholdCert, Bool.and_eq_true, List.all_eq_true, BTree.all_eq_true] at h
  obtain ⟨⟨hinj, hall⟩, hchk⟩ := h
  have hmem : ∀ c p, legalB cmpQ pairs (c, p) = true → (c, p) ∈ pairs.toList.map (·.1) := by
    intro c p hl
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hl
    exact List.mem_map.2 ⟨_, BTree.mem_toList_of_findData hr, rfl⟩
  refine N.wormholeDeadlockFree_of_wholdCheck (legal := fun c p => legalB cmpQ pairs (c, p) = true)
    ⟨fun q hq => hinj q hq, fun c p q hl ha hq => ?_⟩ _ (fun c p hl ha => ?_) hchk
  · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hl
    have := hall _ (BTree.mem_toList_of_findData hr)
    simp only [ha, Bool.false_or, List.all_eq_true] at this
    exact this q hq
  · exact List.mem_filter.2 ⟨hmem c p hl, by simp [ha]⟩

end Check

end Network

end AsyncLean
