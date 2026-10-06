/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Basic
import AsyncLean.LTS.Fairness
import Mathlib.Data.Set.Finite.Powerset

/-!
# Starvation freedom: every packet is delivered under fair scheduling

`Network.Correct` says the network can always make progress and drains once injection stops.
With injection going on forever, a packet could in principle wait forever while other packets
are injected and delivered (*starvation*).  Under a **strongly fair** scheduler this cannot
happen.

* `Network.Delivered r n c` — the packet held in channel `c` at time `n` of the run `r` is
  eventually ejected: it waits in `c`, hops on (and is then eventually ejected), or is
  ejected.  It follows the packet through the network without naming it.
* `Network.StarvationFree` — along every strongly fair run, under every valid selection
  function, every packet in the network is eventually delivered.
* `Network.delivered_of_ranking` — in a deadlock-free and livelock-free network with finitely
  many reachable configurations and a ranking function on packets, every packet of every
  strongly fair run is delivered.
* `Network.starvationFree_of_escape_ranking` — Duato's (or Dally and Seitz's) condition plus
  a ranking function and finitely many legal pairs imply starvation freedom.

The proof: while a packet sits in a channel `c`, the configuration keeps `c` occupied.  Some
configuration recurs infinitely often, and from it the network can drain (the drain
theorem), so from a configuration that recurs infinitely often some transition moves the
packet out of `c`.  Strong fairness forces that transition to be taken.  The ranking function
bounds the number of hops, so the packet is ejected after finitely many of them.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*} [DecidableEq C] (N : Network C P)

/-- The packet in channel `c` at time `n` of `r` is eventually ejected. -/
inductive Delivered {sel : Selection C P} (r : (N.ltsWith sel).Run empty) : ℕ → C → Prop
  | eject {n : ℕ} {c : C} : r.lab n = .eject c → Delivered r n c
  | hop {n : ℕ} {c c' : C} {p' : P} : r.lab n = .hop c c' p' → Delivered r (n + 1) c' →
      Delivered r n c
  | wait {n : ℕ} {c : C} : r.lab n ≠ .eject c → (∀ c' p', r.lab n ≠ .hop c c' p') →
      Delivered r (n + 1) c → Delivered r n c

/-- **Starvation freedom**: along every strongly fair run, under every valid selection
function, every packet in the network is eventually delivered. -/
def StarvationFree : Prop :=
  ∀ sel, N.ValidSel sel → ∀ r : (N.ltsWith sel).Run empty, r.StronglyFair →
    ∀ n c, r.st n c ≠ none → N.Delivered r n c

/-- The action moves the packet out of channel `c`. -/
def Leaves (c : C) : Act C P → Prop
  | .eject c' => c' = c
  | .hop c' _ _ => c' = c
  | .inject _ _ => False

omit [DecidableEq C] in
theorem leaves_iff {c : C} {a : Act C P} :
    Leaves c a ↔ a = .eject c ∨ ∃ c' p', a = .hop c c' p' := by
  cases a <;> simp [Leaves, eq_comm]

variable {N}

/-- A step that does not move the packet out of `c` keeps it there. -/
theorem stay_of_step {sel : Selection C P} {f f' : Config C P} {a : Act C P} {c : C} {p : P}
    (hst : N.StepWith sel f a f') (hp : f c = some p) (ha : ¬ Leaves c a) : f' c = some p := by
  cases hst with
  | @inject c₁ _ _ hfree =>
    have : c ≠ c₁ := by rintro rfl; simp [hp] at hfree
    rwa [Function.update_of_ne this]
  | @hop c₁ c₂ _ _ _ _ _ hfree =>
    have h1 : c ≠ c₂ := by rintro rfl; simp [hp] at hfree
    have h2 : c ≠ c₁ := fun h => ha h.symm
    rwa [Function.update_of_ne h1, Function.update_of_ne h2]
  | @eject c₁ _ _ _ =>
    rwa [Function.update_of_ne (fun h => ha h.symm : c ≠ c₁)]

/-- Along a drain from a configuration holding a packet in `c`, some step moves it out. -/
theorem exists_leave_of_drain {sel : Selection C P} {s : Config C P} {c : C} {p : P}
    (hs : s c = some p) (h : Relation.ReflTransGen ((N.ltsWith sel).IStep Act.IsMove) s empty) :
    ∃ s₁ a s₂, (N.ltsWith sel).Reachable s s₁ ∧ (N.ltsWith sel).step s₁ a s₂ ∧ Leaves c a := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing p with
  | refl => simp [empty] at hs
  | head hst _ ih =>
    obtain ⟨a, -, hst⟩ := hst
    by_cases ha : Leaves c a
    · exact ⟨_, a, _, LTS.Reachable.refl _, hst, ha⟩
    · obtain ⟨s₁, a', s₂, hr, h', ha'⟩ := ih (stay_of_step hst hs ha)
      exact ⟨s₁, a', s₂, LTS.Reachable.head ⟨a, hst⟩ hr, h', ha'⟩

variable (N)

/-- The packet in `c` at time `n` stays there until time `m` and then leaves. -/
theorem delivered_of_leave {sel : Selection C P} (r : (N.ltsWith sel).Run empty) {c : C} :
    ∀ d n, (∀ k, n ≤ k → k < n + d → ¬ Leaves c (r.lab k)) → N.Delivered r (n + d) c →
      N.Delivered r n c
  | 0, _, _, h => h
  | d + 1, n, hstay, h => by
    have h' : N.Delivered r (n + 1) c :=
      delivered_of_leave r d (n + 1) (fun k hk hk' => hstay k (by omega) (by omega))
        (by rwa [show n + 1 + d = n + (d + 1) by omega])
    have hl := hstay n le_rfl (by omega)
    refine Delivered.wait (fun he => hl (leaves_iff.2 (Or.inl he)))
      (fun c' p' hh => hl (leaves_iff.2 (Or.inr ⟨c', p', hh⟩))) h'

variable {N}

/-- In a network that drains, with finitely many reachable configurations, a packet cannot sit
in a channel forever along a strongly fair run. -/
theorem exists_leave {sel : Selection C P} (r : (N.ltsWith sel).Run empty)
    (hfin : {f | (N.ltsWith sel).Reachable empty f}.Finite) (hfair : r.StronglyFair)
    (hdrain : ∀ f, (N.ltsWith sel).Reachable empty f →
      Relation.ReflTransGen ((N.ltsWith sel).IStep Act.IsMove) f empty)
    {n : ℕ} {c : C} {p : P} (hp : r.st n c = some p) :
    ∃ m, n ≤ m ∧ Leaves c (r.lab m) := by
  by_contra hne
  push Not at hne
  have hstay : ∀ d, r.st (n + d) c = some p := by
    intro d
    induction d with
    | zero => exact hp
    | succ d ih => exact stay_of_step (r.step (n + d)) ih (hne _ (by omega))
  obtain ⟨s, hs⟩ := r.exists_infOften hfin
  obtain ⟨m₀, hm₀, rfl⟩ := hs n
  have hsc : r.st m₀ c = some p := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm₀
    exact hstay d
  obtain ⟨s₁, a, s₂, hr, hst, ha⟩ := exists_leave_of_drain hsc (hdrain _ (r.reachable m₀))
  obtain ⟨k, hk, -, hlab, -⟩ := hfair s₁ a s₂ (LTS.Run.infOften_of_reachable hfair hs hr) hst n
  exact hne k hk (hlab ▸ ha)

/-- **Every packet is delivered** along every strongly fair run of a deadlock-free,
livelock-free network with finitely many reachable configurations, when a ranking function
decreases on every hop. -/
theorem delivered_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {sel : Selection C P} (hsel : N.ValidSel sel) (hD : N.DeadlockFreeWith sel)
    (hL : N.LivelockFreeWith sel) (hfin : {f | (N.ltsWith sel).Reachable empty f}.Finite)
    (r : (N.ltsWith sel).Run empty) (hfair : r.StronglyFair) :
    ∀ n c p, r.st n c = some p → N.Delivered r n c := by
  have hdrain : ∀ f, (N.ltsWith sel).Reachable empty f →
      Relation.ReflTransGen ((N.ltsWith sel).IStep Act.IsMove) f empty :=
    fun f hf => (N.inevitablyEmpty hD hL hf).drain
  suffices key : ∀ k n c p, rk c p = k → r.st n c = some p → N.Delivered r n c from
    fun n c p hp => key _ n c p rfl hp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n c p hk hp
    have hex := exists_leave r hfin hfair hdrain hp
    classical
    let m := Nat.find hex
    have hm : n ≤ m ∧ Leaves c (r.lab m) := Nat.find_spec hex
    have hbefore : ∀ k, n ≤ k → k < m → ¬ Leaves c (r.lab k) := fun k hk hkm hl =>
      Nat.find_min hex hkm ⟨hk, hl⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm.1
    have hstay : ∀ e, e ≤ d → r.st (n + e) c = some p := by
      intro e
      induction e with
      | zero => intro; exact hp
      | succ e ih' =>
        intro he
        exact stay_of_step (r.step (n + e)) (ih' (by omega)) (hbefore _ (by omega) (by omega))
    have hpm : r.st m c = some p := hd ▸ hstay d le_rfl
    refine delivered_of_leave N r d n (fun k hk hk' => hbefore k hk (by omega)) ?_
    rw [← hd]
    rcases leaves_iff.1 hm.2 with he | ⟨c', p', hh⟩
    · exact Delivered.eject he
    · refine Delivered.hop hh ?_
      have hst := r.step m
      rw [hh] at hst
      change N.StepWith sel _ _ _ at hst
      generalize hs' : r.st (m + 1) = s' at hst
      cases hst with
      | hop hp' harr hq _ =>
        rw [hpm, Option.some.injEq] at hp'
        subst hp'
        have hl := N.legal_of_reachable hcl hsel (r.reachable m) c _ hpm
        refine ih _ (hk ▸ hrk c _ (c', p') hl harr (hsel.sub _ _ _ _ hq)) (m + 1) c' p' rfl ?_
        rw [hs']
        simp

/-- With finitely many legal pairs there are finitely many reachable configurations. -/
theorem reachable_finite {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) {sel : Selection C P} (hsel : N.ValidSel sel) :
    {f | (N.ltsWith sel).Reachable empty f}.Finite := by
  let graph : Config C P → Set (C × P) := fun f => {q | f q.1 = some q.2}
  refine Set.Finite.of_finite_image (f := graph) ?_ ?_
  · refine hfin.finite_subsets.subset ?_
    rintro _ ⟨f, hf, rfl⟩ q hq
    exact N.legal_of_reachable hcl hsel hf q.1 q.2 hq
  · intro f _ g _ hfg
    funext c
    cases hf : f c with
    | none =>
      cases hg : g c with
      | none => rfl
      | some p =>
        have : (c, p) ∈ graph g := hg
        rw [← hfg] at this
        exact absurd (hf.symm.trans this) (by simp)
    | some p =>
      have : (c, p) ∈ graph f := hf
      rw [hfg] at this
      exact this.symm

variable (N)

/-- **Starvation freedom from Duato's condition and a ranking function**: with finitely many
legal pairs, an acyclic escape subfunction and a ranking function that decreases on every hop,
every packet of every strongly fair run is delivered, under every selection function. -/
theorem starvationFree_of_escape_ranking {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) (R₁ : C → P → List (C × P))
    (hsub : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → q ∈ N.route c p)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁))) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.StarvationFree := by
  intro sel hsel r hfair n c hc
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hc
  have hchan : {c | ∃ p, legal c p}.Finite :=
    (hfin.image Prod.fst).subset fun c ⟨p, hl⟩ => ⟨(c, p), hl, rfl⟩
  exact delivered_of_ranking hcl rk hrk hsel
    (N.deadlockFree_of_escape hcl R₁ hsub hconn hwf sel hsel)
    (N.livelockFree_of_ranking hcl hchan rk hrk sel hsel)
    (reachable_finite hcl hfin hsel) r hfair n c p hp

end Network

end AsyncLean
