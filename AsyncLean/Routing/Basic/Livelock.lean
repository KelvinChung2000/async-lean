/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Basic.Deadlock

/-!
# Interconnection networks with dynamic routing, part 4: livelock freedom and draining

Part 4 of 5 of `AsyncLean.Routing.Basic`; that module has the overview.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*}

variable (N : Network C P)

section Semantics

variable [DecidableEq C]

/-! ### Livelock freedom: ranking functions -/

/-- The weight of a channel's content: `0` if empty, one more than the rank of its packet
otherwise. -/
def wt (rk : C → P → ℕ) (c : C) : Option P → ℕ
  | none => 0
  | some p => rk c p + 1

omit [DecidableEq C] in
@[simp] theorem wt_none (rk : C → P → ℕ) (c : C) : wt rk c none = 0 := rfl
omit [DecidableEq C] in
@[simp] theorem wt_some (rk : C → P → ℕ) (c : C) (p : P) : wt rk c (some p) = rk c p + 1 := rfl

theorem sum_update_add (s : Finset C) (g : C → Option P → ℕ) (f : Config C P) {i : C}
    (hi : i ∈ s) (v : Option P) :
    (∑ x ∈ s, g x (Function.update f i v x)) + g i (f i) = (∑ x ∈ s, g x (f x)) + g i v := by
  have h1 := Finset.add_sum_erase s (fun x => g x (Function.update f i v x)) hi
  have h2 := Finset.add_sum_erase s (fun x => g x (f x)) hi
  have h3 : ∑ x ∈ s.erase i, g x (Function.update f i v x) = ∑ x ∈ s.erase i, g x (f x) :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  simp only [Function.update_self] at h1
  omega

/-- **Livelock freedom by a ranking function.**  If, on a closed set of pairs that uses
finitely many channels, every permitted hop strictly decreases the rank `rk` of the packet,
then under every selection function that only offers permitted hops there is no infinite run
without injections.  For
minimal routing take the distance to the destination; for bounded misrouting take the
distance plus a multiple of the remaining misrouting budget. -/
theorem livelockFreeWith_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {c | ∃ p, legal c p}.Finite) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {sel : Selection C P} (hsel : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p) :
    N.LivelockFreeWith sel := by
  have hs : ∀ c p, legal c p → c ∈ hfin.toFinset := fun c p h => hfin.mem_toFinset.2 ⟨p, h⟩
  refine LTS.LivelockFree.of_ranking (Legal legal) (fun _ _ h => by simp [empty] at h)
    (fun _ _ _ hf hst => N.legal_step hcl hsel hf hst)
    (fun f => ∑ c ∈ hfin.toFinset, wt rk c (f c)) ?_
  intro f a f' hf ha hst
  change N.StepWith sel f a f' at hst
  cases hst with
  | inject => simp [Act.IsMove] at ha
  | @hop c c' p p' hp harr hq hfree =>
    have hl' : legal c' p' := hcl.route c p (c', p') (hf c p hp) harr (hsel _ _ _ _ hq)
    have hne : c' ≠ c := by rintro rfl; simp [hp] at hfree
    have h1 := sum_update_add _ (wt rk) f (hs c p (hf c p hp)) none
    have h2 := sum_update_add _ (wt rk) (Function.update f c none) (hs c' p' hl') (some p')
    have hlt := hrk c p (c', p') (hf c p hp) harr (hsel _ _ _ _ hq)
    rw [Function.update_of_ne hne, hfree] at h2
    rw [hp, wt_some, wt_none] at h1
    rw [wt_none, wt_some] at h2
    simp only at hlt
    show ∑ x ∈ hfin.toFinset, wt rk x
        (Function.update (Function.update f c none) c' (some p') x) <
      ∑ x ∈ hfin.toFinset, wt rk x (f x)
    omega
  | @eject c p hp _ =>
    have h1 := sum_update_add _ (wt rk) f (hs c p (hf c p hp)) none
    rw [hp, wt_some, wt_none] at h1
    show ∑ x ∈ hfin.toFinset, wt rk x (Function.update f c none x) <
      ∑ x ∈ hfin.toFinset, wt rk x (f x)
    omega

/-- **Livelock freedom by a ranking function**, under every selection function that only
offers permitted hops. -/
theorem livelockFree_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {c | ∃ p, legal c p}.Finite) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.LivelockFree :=
  fun _ hsel => N.livelockFreeWith_of_ranking hcl hfin rk hrk hsel.sub

/-- `livelockFree_of_ranking` for a network with finitely many channels. -/
theorem livelockFree_of_ranking' [Finite C] {legal : C → P → Prop} (hcl : N.Closed legal)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.LivelockFree :=
  N.livelockFree_of_ranking hcl (Set.toFinite _) rk hrk

end Semantics

/-- **No packet is routed forever** when a ranking function decreases on every hop. -/
theorem packetLivelockFree_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.PacketLivelockFree := fun q hq =>
  LTS.LivelockFree.of_ranking (fun q => legal q.1 q.2) (hcl.inject q hq)
    (fun q _ q' hl hst => hcl.route q.1 q.2 q' hl hst.1 hst.2) (fun q => rk q.1 q.2)
    (fun q _ q' hl _ hst => hrk q.1 q.2 q' hl hst.1 hst.2)

/-- **Hop bound**: a packet in a legal pair `q` reaches its destination within `rk q` hops —
every route of `n` hops from `q` ends in a pair of rank at most `rk q - n`.  For minimal
routing with `rk` the distance, packets take at most as many hops as the distance. -/
theorem packet_hops_le {legal : C → P → Prop} (hcl : N.Closed legal) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {q q' : C × P} {ls : List Unit} (hq : legal q.1 q.2) (h : N.packetLTS.Path q ls q') :
    rk q'.1 q'.2 + ls.length ≤ rk q.1 q.2 := by
  revert hq
  induction h with
  | nil => intro; simp
  | cons hst _ ih =>
    intro hq
    have h1 := ih (hcl.route _ _ _ hq hst.1 hst.2)
    have h2 := hrk _ _ _ hq hst.1 hst.2
    simp only [List.length_cons]
    omega

/-- **Exact hop count**: if every permitted hop decreases `rk` by exactly one, a route of `n`
hops from `q` ends in a pair of rank `rk q - n`.  With `rk` the distance to the destination
(minimal routing), every packet takes exactly as many hops as the distance: a shortest path. -/
theorem packet_hops_eq {legal : C → P → Prop} (hcl : N.Closed legal) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p →
      rk q.1 q.2 + 1 = rk c p)
    {q q' : C × P} {ls : List Unit} (hq : legal q.1 q.2) (h : N.packetLTS.Path q ls q') :
    rk q'.1 q'.2 + ls.length = rk q.1 q.2 := by
  revert hq
  induction h with
  | nil => intro; simp
  | cons hst _ ih =>
    intro hq
    have h1 := ih (hcl.route _ _ _ hq hst.1 hst.2)
    have h2 := hrk _ _ _ hq hst.1 hst.2
    simp only [List.length_cons]
    omega

section Drain

variable [DecidableEq C]

/-- **Drain theorem.**  In a deadlock-free and livelock-free network, from every reachable
configuration every run without injections is finite and ends with the network empty. -/
theorem inevitablyEmpty {sel : Selection C P} (hD : N.DeadlockFreeWith sel)
    (hL : N.LivelockFreeWith sel) {f : Config C P} (hf : (N.ltsWith sel).Reachable empty f) :
    N.InevitablyEmpty sel f := by
  have hacc := LTS.LivelockFree.acc hL hf
  induction hacc with
  | intro f _ ih =>
    by_cases he : f = empty
    · subst he; exact .done
    · exact .later (hD f hf he) fun a f' ha hst => ih f' ⟨a, ha, hst⟩ (hf.tail ⟨a, hst⟩)

/-- From an `InevitablyEmpty` configuration, all packets can be delivered by moves only. -/
theorem InevitablyEmpty.drain {sel : Selection C P} {f : Config C P}
    (h : N.InevitablyEmpty sel f) :
    Relation.ReflTransGen ((N.ltsWith sel).IStep Act.IsMove) f empty := by
  induction h with
  | done => exact Relation.ReflTransGen.refl
  | later hm _ ih =>
    obtain ⟨a, f', ha, hst⟩ := hm
    exact Relation.ReflTransGen.head ⟨a, ha, hst⟩ (ih a f' ha hst)

variable {N}

theorem Correct.inevitablyEmpty (h : N.Correct) {sel : Selection C P} (hsel : N.ValidSel sel)
    {f : Config C P} (hf : (N.ltsWith sel).Reachable empty f) : N.InevitablyEmpty sel f :=
  N.inevitablyEmpty (h.1 sel hsel) (h.2 sel hsel) hf

/-- In a correct network, under every valid selection and from every reachable
configuration, all packets in the network can be delivered without injecting new ones. -/
theorem Correct.drain (h : N.Correct) {sel : Selection C P} (hsel : N.ValidSel sel)
    {f : Config C P} (hf : (N.ltsWith sel).Reachable empty f) :
    Relation.ReflTransGen ((N.ltsWith sel).IStep Act.IsMove) f empty :=
  (h.inevitablyEmpty hsel hf).drain

/-- A deadlock-free network that can inject some packet never gets stuck as a whole. -/
theorem DeadlockFree.lts (h : N.DeadlockFree) (hinj : N.inject ≠ []) {sel : Selection C P}
    (hsel : N.ValidSel sel) : (N.ltsWith sel).DeadlockFree empty := by
  refine LTS.deadlockFree_iff.2 fun f hf => ?_
  by_cases he : f = empty
  · subst he
    obtain ⟨⟨c, p⟩, hq⟩ := List.exists_mem_of_ne_nil _ hinj
    exact ⟨_, _, StepWith.inject hq rfl⟩
  · obtain ⟨a, f', -, hst⟩ := h sel hsel f hf he
    exact ⟨a, f', hst⟩

end Drain

end Network

end AsyncLean
