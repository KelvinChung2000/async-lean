/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Basic.Facts

/-!
# Interconnection networks with dynamic routing, part 3: deadlock freedom, Duato and Dally–Seitz, and the converse

Part 3 of 5 of `AsyncLean.Routing.Basic`; that module has the overview.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*}

variable (N : Network C P)

section Semantics

variable [DecidableEq C]

/-! ### Deadlock freedom: Duato's and Dally–Seitz's theorems -/

/-- The core argument: with an escape subfunction `R₁` whose dependency graph is
well-founded, every configuration holding a packet can move.  By well-founded induction
along the dependencies: the packet in `c` is ejected, or its escape channel is free, or the
packet holding its escape channel can move. -/
theorem movable_of_escape {legal : C → P → Prop} {sel : Selection C P} {R₁ : C → P → List (C × P)}
    (hsel : ∀ f c p, legal c p → N.arrived c p = false → f c = some p →
      (∃ q ∈ R₁ c p, f q.1 = none) → ∃ q ∈ sel f c p, f q.1 = none)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁))) {f : Config C P} (hf : Legal legal f) :
    ∀ c p, f c = some p → N.Movable sel f := by
  intro c
  refine hwf.induction (C := fun c => ∀ p, f c = some p → N.Movable sel f) c ?_
  intro c ih p hp
  have hl := hf c p hp
  cases harr : N.arrived c p with
  | true => exact ⟨.eject c, _, rfl, StepWith.eject hp harr⟩
  | false =>
    obtain ⟨⟨c', p'⟩, hq⟩ := List.exists_mem_of_ne_nil _ (hconn c p hl harr)
    cases hc' : f c' with
    | none =>
      obtain ⟨⟨c'', p''⟩, hq', hfree⟩ := hsel f c p hl harr hp ⟨(c', p'), hq, hc'⟩
      exact ⟨.hop c c'' p'', _, rfl, StepWith.hop hp harr hq' hfree⟩
    | some p'' => exact ih c' ⟨p, p', hl, harr, hq⟩ p'' hc'

/-- **Duato's theorem** (store-and-forward / virtual cut-through switching).  Let `legal` be a
closed set of pairs.  If the routing subfunction `R₁ ⊆ route` (the escape channels) is
connected — it offers a hop to every legal packet that has not arrived — and its channel
dependency graph is well-founded (acyclic), then the network is deadlock free under every
selection function, although packets may use all of `route` adaptively. -/
theorem deadlockFree_of_escape {legal : C → P → Prop} (hcl : N.Closed legal)
    (R₁ : C → P → List (C × P))
    (hsub : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → q ∈ N.route c p)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁))) : N.DeadlockFree := by
  intro sel hsel f hf hne
  obtain ⟨c, p, hp⟩ := exists_of_ne_empty hne
  exact N.movable_of_escape (fun f c p hl ha hp ⟨q, hq, hfree⟩ =>
      hsel.conserving f c p hp ⟨q, hsub c p q hl ha hq, hfree⟩) hconn hwf
    (N.legal_of_reachable hcl hsel hf) c p hp

/-- **Duato's theorem for selections that may decline adaptive hops**: the network is deadlock
free under every selection that only offers permitted hops and never refuses a free escape
hop (`EscapeSel`), not only under work-conserving ones. -/
theorem deadlockFreeWith_of_escape {legal : C → P → Prop} (hcl : N.Closed legal)
    (R₁ : C → P → List (C × P))
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁))) {sel : Selection C P} (hsel : N.EscapeSel R₁ sel) :
    N.DeadlockFreeWith sel := by
  intro f hf hne
  obtain ⟨c, p, hp⟩ := exists_of_ne_empty hne
  exact N.movable_of_escape (fun f c p _ _ => hsel.conserving f c p) hconn hwf
    (N.legal_of_reachable_sub hcl hsel.sub hf) c p hp

omit [DecidableEq C] in
/-- A work-conserving selection never refuses a free escape hop. -/
theorem ValidSel.escapeSel {sel : Selection C P} (hsel : N.ValidSel sel)
    {R₁ : C → P → List (C × P)} (hR : ∀ c p q, q ∈ R₁ c p → q ∈ N.route c p) :
    N.EscapeSel R₁ sel :=
  ⟨hsel.sub, fun f c p hp ⟨q, hq, hfree⟩ => hsel.conserving f c p hp ⟨q, hR c p q hq, hfree⟩⟩

/-- A congestion-aware selection: the free escape hops, and those other free permitted hops that
`allow` admits (for example, only hops towards lightly loaded routers). -/
def gatedSel [DecidableEq P] (R₁ : C → P → List (C × P))
    (allow : Config C P → C → P → C × P → Bool) : Selection C P :=
  fun f c p => (N.route c p).filter fun q => (f q.1).isNone && (decide (q ∈ R₁ c p) || allow f c p q)

theorem gatedSel_escapeSel [DecidableEq P] {R₁ : C → P → List (C × P)}
    (hR : ∀ c p q, q ∈ R₁ c p → q ∈ N.route c p) (allow : Config C P → C → P → C × P → Bool) :
    N.EscapeSel R₁ (N.gatedSel R₁ allow) where
  sub _ _ _ _ h := (List.mem_filter.1 h).1
  conserving f c p _ := fun ⟨q, hq, hfree⟩ =>
    ⟨q, List.mem_filter.2 ⟨hR c p q hq, by simp [hfree, hq]⟩, hfree⟩

/-- **Dally and Seitz's theorem**: a connected routing function whose channel dependency graph
is well-founded (acyclic) is deadlock free. -/
theorem deadlockFree_of_cdg {legal : C → P → Prop} (hcl : N.Closed legal)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → N.route c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal N.route))) : N.DeadlockFree :=
  N.deadlockFree_of_escape hcl N.route (fun _ _ _ _ _ h => h) hconn hwf

omit [DecidableEq C] in
/-- On finitely many channels, an acyclic dependency graph is well-founded. -/
theorem wf_of_acyclic [Finite C] {r : C → C → Prop} (h : ∀ c, ¬ Relation.TransGen r c c) :
    WellFounded (flip r) := by
  have : WellFounded (Relation.TransGen (flip r)) := by
    have : IsTrans C (Relation.TransGen (flip r)) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
    have : Std.Irrefl (Relation.TransGen (flip r)) :=
      ⟨fun c hc => h c (Relation.transGen_swap.1 hc)⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  exact Subrelation.wf (fun h => Relation.TransGen.single h) this

omit [DecidableEq C] in
/-- A numbering of the channels that decreases along every dependency makes the dependency
graph well-founded. -/
theorem wf_of_rank {r : C → C → Prop} (rk : C → ℕ) (h : ∀ c c', r c c' → rk c' < rk c) :
    WellFounded (flip r) :=
  Subrelation.wf (fun {x y} hxy => h y x hxy) (InvImage.wf rk wellFounded_lt)

omit [DecidableEq C] in
/-- A lexicographic numbering of the channels (a pair of numbers) that decreases along every
dependency makes the dependency graph well-founded. -/
theorem wf_of_lexRank {r : C → C → Prop} (rk : C → ℕ × ℕ)
    (h : ∀ c c', r c c' → Prod.Lex (· < ·) (· < ·) (rk c') (rk c)) : WellFounded (flip r) :=
  Subrelation.wf (fun {x y} hxy => h y x hxy)
    (InvImage.wf rk (Prod.lex ⟨_, wellFounded_lt⟩ ⟨_, wellFounded_lt⟩).wf)

/-! ### Duato's condition is also necessary

Fix a closed set `legal` of pairs.  *Static* deadlock freedom asks that every non-empty
configuration of legal packets can move; it is what deadlock freedom means when every legal
configuration is reachable (`deadlockFree_iff_exists_escape`).  When finitely many channels
carry legal pairs it holds **iff** some connected routing subfunction has a well-founded (acyclic) dependency
graph (`staticDeadlockFree_iff_exists_escape`).  For the necessity, the escape subfunction is
built in stages: `stage n` holds the channels from which every legal packet has a permitted
hop into `stage (n - 1)`; deadlock freedom forces every channel into some stage, and the
escape hops are those that lead to an earlier stage. -/

/-- Every non-empty configuration of legal packets can move (under adaptive routing). -/
def StaticDeadlockFree (legal : C → P → Prop) : Prop :=
  ∀ f : Config C P, Legal legal f → f ≠ empty → N.Movable N.adaptive f

/-- The channels from which every legal packet that has not arrived has a permitted hop into
`stage n`. -/
def stage (legal : C → P → Prop) : ℕ → Set C
  | 0 => ∅
  | n + 1 => {c | ∀ p, legal c p → N.arrived c p = false → ∃ q ∈ N.route c p, q.1 ∈ stage legal n}

omit [DecidableEq C] in
theorem stage_subset_succ (legal : C → P → Prop) : ∀ n, N.stage legal n ⊆ N.stage legal (n + 1)
  | 0 => Set.empty_subset _
  | n + 1 => fun _ hc p hl ha =>
    let ⟨q, hq, hq'⟩ := hc p hl ha
    ⟨q, hq, stage_subset_succ legal n hq'⟩

omit [DecidableEq C] in
theorem stage_mono (legal : C → P → Prop) : Monotone (N.stage legal) :=
  monotone_nat_of_le_succ (N.stage_subset_succ legal)

omit [DecidableEq C] in
/-- When finitely many channels carry legal pairs, the stages stabilise. -/
theorem exists_stage_stable {legal : C → P → Prop} (hfin : {c | ∃ p, legal c p}.Finite) :
    ∃ m, N.stage legal (m + 1) = N.stage legal m := by
  have := hfin.to_subtype
  let g : ℕ → Set {c | ∃ p, legal c p} := fun n => {c | c.1 ∈ N.stage legal (n + 1)}
  have hout : ∀ c, (¬ ∃ p, legal c p) → ∀ n, c ∈ N.stage legal (n + 1) :=
    fun c hc n p hl => absurd ⟨p, hl⟩ hc
  have key : ∀ a b, a < b → g a = g b → N.stage legal (a + 2) = N.stage legal (a + 1) := by
    intro a b hab he
    refine le_antisymm (fun c hc => ?_) (N.stage_subset_succ legal (a + 1))
    by_cases hl : ∃ p, legal c p
    · have : (⟨c, hl⟩ : {c | ∃ p, legal c p}) ∈ g b :=
        N.stage_mono legal (show a + 2 ≤ b + 1 by omega) hc
      rw [← he] at this
      exact this
    · exact hout c hl _
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite g
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a + 1, key a b h he⟩
  · exact ⟨b + 1, key b a h he.symm⟩

/-- **Necessity of Duato's condition.**  If finitely many channels carry legal pairs and every
non-empty configuration of legal packets can move, then some connected routing subfunction has
a well-founded channel dependency graph. -/
theorem exists_escape_of_static {legal : C → P → Prop} (hfin : {c | ∃ p, legal c p}.Finite)
    (h : N.StaticDeadlockFree legal) :
    ∃ R₁ : C → P → List (C × P),
      (∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → q ∈ N.route c p) ∧
      (∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ []) ∧
      WellFounded (flip (N.Dep legal R₁)) := by
  classical
  obtain ⟨m, hm⟩ := N.exists_stage_stable hfin
  have hall : ∀ c, c ∈ N.stage legal m := by
    by_contra hc
    push Not at hc
    have hbad : ∀ c, c ∉ N.stage legal m → ∃ p, legal c p ∧ N.arrived c p = false ∧
        ∀ q ∈ N.route c p, q.1 ∉ N.stage legal m := by
      intro c hc'
      rw [← hm] at hc'
      simp only [stage, Set.mem_ofPred_eq, not_forall, not_exists, not_and] at hc'
      obtain ⟨p, hl, ha, hq⟩ := hc'
      exact ⟨p, hl, ha, fun q hmem => hq q hmem⟩
    obtain ⟨c₀, hc₀⟩ := hc
    have : Nonempty P := ⟨(hbad c₀ hc₀).choose⟩
    choose! pb hpb using hbad
    let f : Config C P := fun c => if c ∈ N.stage legal m then none else some (pb c)
    have hfl : Legal legal f := by
      intro c p hp
      by_cases hc : c ∈ N.stage legal m
      · simp [f, hc] at hp
      · simp only [f, hc, ite_false, Option.some.injEq] at hp
        exact hp ▸ (hpb c hc).1
    have hne : f ≠ empty := fun he => by
      have : f c₀ = none := by rw [he]; rfl
      simp [f, hc₀] at this
    obtain ⟨a, f', ha, hst⟩ := h f hfl hne
    change N.StepWith N.adaptive f a f' at hst
    cases hst with
    | inject => simp [Act.IsMove] at ha
    | @hop c c' p p' hp harr hq hfree =>
      by_cases hc : c ∈ N.stage legal m
      · simp [f, hc] at hp
      · simp only [f, hc, ite_false, Option.some.injEq] at hp
        subst hp
        have hc' := (hpb c hc).2.2 _ hq
        simp [f, hc'] at hfree
    | @eject c p hp harr =>
      by_cases hc : c ∈ N.stage legal m
      · simp [f, hc] at hp
      · simp only [f, hc, ite_false, Option.some.injEq] at hp
        subst hp
        simp [(hpb c hc).2.1] at harr
  let rk : C → ℕ := fun c => Nat.find (⟨m, hall c⟩ : ∃ n, c ∈ N.stage legal n)
  refine ⟨fun c p => (N.route c p).filter fun q => rk q.1 < rk c, ?_, ?_, ?_⟩
  · intro c p q _ _ hq
    exact (List.mem_filter.1 hq).1
  · intro c p hl ha
    have hc : c ∈ N.stage legal (rk c) := Nat.find_spec (⟨m, hall c⟩ : ∃ n, c ∈ N.stage legal n)
    cases hk : rk c with
    | zero => rw [hk] at hc; exact absurd hc (Set.notMem_empty c)
    | succ k =>
      rw [hk] at hc
      obtain ⟨q, hq, hq'⟩ := hc p hl ha
      have : rk q.1 ≤ k := Nat.find_min' _ hq'
      exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hq, by simp only [decide_eq_true_eq]; omega⟩)
  · refine wf_of_rank rk ?_
    rintro c c' ⟨p, p', -, -, hq⟩
    simpa using (List.mem_filter.1 hq).2

/-- **Duato's necessary and sufficient condition** (static form): when finitely many channels
carry legal pairs, every non-empty configuration of legal packets can move iff some connected
routing subfunction has a well-founded (acyclic) channel dependency graph. -/
theorem staticDeadlockFree_iff_exists_escape {legal : C → P → Prop}
    (hfin : {c | ∃ p, legal c p}.Finite) :
    N.StaticDeadlockFree legal ↔ ∃ R₁ : C → P → List (C × P),
      (∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → q ∈ N.route c p) ∧
      (∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ []) ∧
      WellFounded (flip (N.Dep legal R₁)) := by
  refine ⟨N.exists_escape_of_static hfin, ?_⟩
  rintro ⟨R₁, hsub, hconn, hwf⟩ f hf hne
  obtain ⟨c, p, hp⟩ := exists_of_ne_empty hne
  exact N.movable_of_escape (fun f c p hl ha hp ⟨q, hq, hfree⟩ =>
    N.adaptive_valid.conserving f c p hp ⟨q, hsub c p q hl ha hq, hfree⟩) hconn hwf hf c p hp

/-- **Duato's theorem as an equivalence**: if every configuration of legal packets is
reachable, the network is deadlock free (under every selection function) iff some connected
routing subfunction has an acyclic channel dependency graph. -/
theorem deadlockFree_iff_exists_escape {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {c | ∃ p, legal c p}.Finite) (hreach : ∀ f, Legal legal f → N.lts.Reachable empty f) :
    N.DeadlockFree ↔ ∃ R₁ : C → P → List (C × P),
      (∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → q ∈ N.route c p) ∧
      (∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ []) ∧
      WellFounded (flip (N.Dep legal R₁)) := by
  refine ⟨fun h => N.exists_escape_of_static hfin fun f hf hne =>
    (N.deadlockFree_iff_adaptive.1 h) f (hreach f hf) hne, ?_⟩
  rintro ⟨R₁, hsub, hconn, hwf⟩
  exact N.deadlockFree_of_escape hcl R₁ hsub hconn hwf

/-- Every legal configuration is reachable when every legal pair can be injected directly
(for example when the legal pairs are taken to be the injectable ones). -/
theorem reachable_of_injectable {legal : C → P → Prop} (hfin : {c | ∃ p, legal c p}.Finite)
    (hinj : ∀ c p, legal c p → (c, p) ∈ N.inject) :
    ∀ f, Legal legal f → N.lts.Reachable empty f := by
  classical
  suffices key : ∀ s : Finset C, ∀ f, Legal legal f → (∀ c, f c ≠ none → c ∈ s) →
      N.lts.Reachable empty f from
    fun f hf => key hfin.toFinset f hf fun c hc => by
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hc
      exact hfin.mem_toFinset.2 ⟨p, hf c p hp⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro f _ hs
    have : f = empty := funext fun c => by
      by_contra h; exact absurd (hs c h) (Finset.notMem_empty c)
    rw [this]
  | insert a s _ ih =>
    intro f hf hs
    have hf' : Legal legal (Function.update f a none) := by
      intro c p hp
      by_cases hc : c = a
      · subst hc; simp at hp
      · rw [Function.update_of_ne hc] at hp; exact hf c p hp
    have hr := ih (Function.update f a none) hf' fun c hc => by
      by_cases hca : c = a
      · subst hca; simp at hc
      · rw [Function.update_of_ne hca] at hc
        exact (Finset.mem_insert.1 (hs c hc)).resolve_left hca
    cases hfa : f a with
    | none => rwa [← hfa, Function.update_eq_self] at hr
    | some p =>
      have hst : N.lts.step (Function.update f a none) (.inject a p)
          (Function.update (Function.update f a none) a (some p)) :=
        StepWith.inject (hinj a p (hf a p hfa)) (by simp)
      rw [Function.update_idem, ← hfa, Function.update_eq_self] at hst
      exact hr.tail ⟨_, hst⟩

end Semantics

end Network

end AsyncLean
