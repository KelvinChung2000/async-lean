/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Petri.Stubborn
import AsyncLean.LTS.Properties

/-!
# Stubborn sets for liveness and livelock freedom

`AsyncLean.Petri.Stubborn` shows that stubborn sets preserve deadlocks.  Two more kinds of
conditions make a reduced state space decide liveness and livelock freedom too.

**Liveness: the cycle proviso.**  A reduced state space may *ignore* a transition forever,
going round a cycle of other transitions.  The proviso forbids it: every marking `M` of the
reduced state space is either *fully expanded* (`S M` contains every enabled transition), or
some enabled transition of `S M` strictly decreases a measure `d` (a distance to a fully
expanded marking).  Then from every reachable marking the net can get back into the reduced
state space (`Net.catchUp`), so liveness of the reduced state space implies liveness of the
net (`Net.live_of_stubborn`).

**Livelock freedom: visibility.**  If every set `S M` that contains an enabled external
transition contains all the external ones, and every marking with an enabled internal
transition has an enabled internal transition in `S M`, then an infinite run of internal
transitions from a reachable marking yields one in the reduced state space
(`Net.livelockFree_of_stubborn`); a rank decreasing along its internal steps excludes it.
-/

namespace AsyncLean

namespace Net

variable {P T : Type*} {N : Net P T}

/-! ### Moving transitions of a stubborn set to the front -/

/-- The first transition of a stubborn set occurring in a path is enabled at its start and
can be fired first. -/
theorem stubborn_front {S : T → Prop} [DecidablePred S] {M M' : Marking P} {w : List T}
    (hS : N.Stubborn M S) (hp : N.lts.Path M w M') (hex : ∃ t ∈ w, S t) :
    ∃ t u v, S t ∧ N.Enabled M t ∧ w = u ++ t :: v ∧ (∀ t' ∈ u, ¬ S t') ∧
      N.lts.Path (N.fire M t) (u ++ v) M' := by
  obtain ⟨u, t, v, M₁, M₂, hw, hu, hSt, hpu, hstep, hpv⟩ := path_split hp hex
  have hent : N.Enabled M t := by
    by_contra hdis
    obtain ⟨p, hlt, hpost⟩ := hS.disabled t hSt hdis
    have := le_of_path (fun t' ht' => hpost t' (hu t' ht')) hpu
    have := hstep.1 p
    omega
  obtain ⟨hen₁, rfl⟩ := hstep
  have hpush := path_push hent (fun t' ht' => hS.enabled t hSt hent t' (hu t' ht')) hpu
    ⟨hen₁, rfl⟩
  cases hpush with
  | cons h₀ hrest₀ =>
    obtain ⟨-, rfl⟩ := h₀
    exact ⟨t, u, v, hSt, hent, hw, hu, hrest₀.append hpv⟩

/-- An enabled transition of a stubborn set commutes with a path avoiding the set. -/
theorem stubborn_commute {S : T → Prop} {M M' : Marking P} {w : List T} {tk : T}
    (hS : N.Stubborn M S) (hp : N.lts.Path M w M') (hno : ∀ t ∈ w, ¬ S t) (hSk : S tk)
    (henk : N.Enabled M tk) :
    N.Enabled M' tk ∧ N.lts.Path (N.fire M tk) w (N.fire M' tk) := by
  have hnc : ∀ t' ∈ w, N.NoConsume tk t' := fun t' ht' => hS.enabled tk hSk henk t' (hno t' ht')
  have hen' := enabled_of_path henk hnc hp
  refine ⟨hen', ?_⟩
  have := path_push henk hnc hp ⟨hen', rfl⟩
  cases this with
  | cons h₀ hrest =>
    obtain ⟨-, rfl⟩ := h₀
    exact hrest

/-! ### Liveness -/

/-- The cycle proviso at `M`: `S` is fully expanded, or an enabled transition of `S`
decreases `d`. -/
def Proviso (N : Net P T) (S : T → Prop) (d : Marking P → ℕ) (M : Marking P) : Prop :=
  (∀ t, N.Enabled M t → S t) ∨ ∃ t, S t ∧ N.Enabled M t ∧ d (N.fire M t) < d M

/-- **Catching up with the reduced state space.**  If the sets are stubborn and satisfy the
cycle proviso on an invariant of the reduced semantics, then from the end of any path
starting in the invariant the net can reach a marking that the reduced semantics reaches
too. -/
theorem catchUp (S : Marking P → T → Prop) [∀ M, DecidablePred (S M)] (d : Marking P → ℕ)
    (Inv : Marking P → Prop)
    (hstep : ∀ M t, Inv M → S M t → N.Enabled M t → Inv (N.fire M t))
    (hst : ∀ M, Inv M → N.Stubborn M (S M)) (hprov : ∀ M, Inv M → N.Proviso (S M) d M) :
    ∀ (n : ℕ) (w : List T) (M M' : Marking P), w.length = n → Inv M → N.lts.Path M w M' →
      ∃ Mr, (N.redLts S).Reachable M Mr ∧ N.lts.Reachable M' Mr := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro w
    -- an inner induction on the measure `d`
    suffices H : ∀ k M M', d M = k → w.length = n → Inv M → N.lts.Path M w M' →
        ∃ Mr, (N.redLts S).Reachable M Mr ∧ N.lts.Reachable M' Mr from
      fun M M' hn hI hp => H _ M M' rfl hn hI hp
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
      intro M M' hk hn hI hp
      have hS := hst M hI
      by_cases hex : ∃ t ∈ w, S M t
      · obtain ⟨t, u, v, hSt, hent, hw, -, hp'⟩ := stubborn_front hS hp hex
        have hred : (N.redLts S).step M t (N.fire M t) := ⟨hSt, hent, rfl⟩
        obtain ⟨Mr, h₁, h₂⟩ := ihn (u ++ v).length (by rw [← hn, hw]; simp) (u ++ v)
          (N.fire M t) M' rfl (hstep M t hI hSt hent) hp'
        exact ⟨Mr, LTS.Reachable.head ⟨t, hred⟩ h₁, h₂⟩
      · push Not at hex
        cases hp with
        | nil => exact ⟨M, LTS.Reachable.refl _, LTS.Reachable.refl _⟩
        | @cons _ M₁ _ t₁ w' h₁ hrest =>
          rcases hprov M hI with hfull | ⟨tk, hSk, henk, hd⟩
          · exact absurd (hfull t₁ h₁.1) (hex t₁ List.mem_cons_self)
          · have hp : N.lts.Path M (t₁ :: w') M' := .cons h₁ hrest
            obtain ⟨hen', hp'⟩ := stubborn_commute hS hp hex hSk henk
            obtain ⟨Mr, h₂, h₃⟩ := ihk (d (N.fire M tk)) (hk ▸ hd) (N.fire M tk) (N.fire M' tk)
              rfl hn (hstep M tk hI hSk henk) hp'
            have hred : (N.redLts S).step M tk (N.fire M tk) := ⟨hSk, henk, rfl⟩
            exact ⟨Mr, LTS.Reachable.head ⟨tk, hred⟩ h₂,
              LTS.Reachable.head ⟨tk, henk' hen'⟩ h₃⟩
where
  henk' {M' : Marking P} {tk : T} (h : N.Enabled M' tk) : N.lts.step M' tk (N.fire M' tk) :=
    ⟨h, rfl⟩

/-- **Liveness by partial-order reduction.**  Stubborn sets with the cycle proviso on an
invariant of the reduced semantics, from whose markings every transition can always be
enabled again: the net is live. -/
theorem live_of_stubborn (S : Marking P → T → Prop) [∀ M, DecidablePred (S M)]
    (d : Marking P → ℕ) (Inv : Marking P → Prop) {M₀ : Marking P} (h₀ : Inv M₀)
    (hstep : ∀ M t, Inv M → S M t → N.Enabled M t → Inv (N.fire M t))
    (hst : ∀ M, Inv M → N.Stubborn M (S M)) (hprov : ∀ M, Inv M → N.Proviso (S M) d M)
    (hlive : ∀ M, Inv M → ∀ t, ∃ M', N.lts.Reachable M M' ∧ N.Enabled M' t) :
    N.lts.Live M₀ := by
  have hinv : ∀ M M', Inv M → (N.redLts S).Reachable M M' → Inv M' := fun M M' hM h =>
    h.invariant hM fun M t M' hI ⟨hS, hen, he⟩ => he ▸ hstep M t hI hS hen
  have hfull : ∀ M M', (N.redLts S).Reachable M M' → N.lts.Reachable M M' := fun M M' h =>
    Relation.ReflTransGen.mono (fun _ _ ⟨t, _, hst⟩ => ⟨t, hst⟩) _ _ h
  intro t M hM
  obtain ⟨w, hw⟩ := hM.exists_path
  obtain ⟨Mr, h₁, h₂⟩ := catchUp S d Inv hstep hst hprov _ w M₀ M rfl h₀ hw
  obtain ⟨M', h₃, hen⟩ := hlive Mr (hinv M₀ Mr h₀ h₁) t
  exact ⟨M', h₂.trans h₃, (lts_enabled_iff).2 hen⟩

/-! ### Livelock freedom -/

/-- A divergent run as markings `f` and labels `g`. -/
theorem exists_labels_of_diverges {internal : T → Prop} {M : Marking P}
    (h : N.lts.Diverges internal M) :
    ∃ f : ℕ → Marking P, ∃ g : ℕ → T, f 0 = M ∧
      ∀ n, internal (g n) ∧ N.Enabled (f n) (g n) ∧ f (n + 1) = N.fire (f n) (g n) := by
  obtain ⟨f, hf0, hf⟩ := h
  choose g hg using hf
  exact ⟨f, g, hf0, fun n => ⟨(hg n).1, (hg n).2.1, (hg n).2.2⟩⟩

/-- A transition consuming none of the inputs of a divergent run's transitions keeps the run
going after it fires. -/
theorem diverges_fire {internal : T → Prop} {f : ℕ → Marking P} {g : ℕ → T} {tk : T}
    (hf : ∀ n, internal (g n) ∧ N.Enabled (f n) (g n) ∧ f (n + 1) = N.fire (f n) (g n))
    (hnc : ∀ n, N.NoConsume tk (g n)) (henk : N.Enabled (f 0) tk) :
    N.lts.Diverges internal (N.fire (f 0) tk) := by
  have hen : ∀ n, N.Enabled (f n) tk := by
    intro n
    induction n with
    | zero => exact henk
    | succ n ih =>
      rw [(hf n).2.2]
      exact enabled_fire_of_noConsume ih (hnc n)
  refine ⟨fun n => N.fire (f n) tk, rfl, fun n => ⟨g n, (hf n).1, ?_⟩⟩
  obtain ⟨hen', heq⟩ := fire_comm (hen n) (hf n).2.1 (hnc n)
  refine ⟨hen', ?_⟩
  change N.fire (f (n + 1)) tk = _
  rw [(hf n).2.2, heq]

/-- The number of external transitions in a list. -/
noncomputable def externals (internal : T → Prop) (w : List T) : ℕ :=
  by classical exact w.countP fun t => ¬ internal t

/-- **Livelock freedom by partial-order reduction.**  Stubborn sets satisfying the two
visibility conditions on an invariant of the reduced semantics, along whose internal reduced
steps a rank decreases: the net is livelock free. -/
theorem livelockFree_of_stubborn (internal : T → Prop) (S : Marking P → T → Prop)
    (Inv : Marking P → Prop) (r : Marking P → ℕ) {M₀ : Marking P} (h₀ : Inv M₀)
    (hstep : ∀ M t, Inv M → S M t → N.Enabled M t → Inv (N.fire M t))
    (hst : ∀ M, Inv M → N.Stubborn M (S M))
    (hV : ∀ M, Inv M → ∀ t, S M t → N.Enabled M t → ¬ internal t →
      ∀ t', ¬ internal t' → S M t')
    (hInt : ∀ M, Inv M → (∃ t, internal t ∧ N.Enabled M t) →
      ∃ t, S M t ∧ internal t ∧ N.Enabled M t)
    (hr : ∀ M t, Inv M → S M t → N.Enabled M t → internal t → r (N.fire M t) < r M) :
    N.lts.LivelockFree internal M₀ := by
  classical
  -- the core: no path from the invariant ends in a divergent marking
  have key : ∀ e k (w : List T) (M M' : Marking P), externals internal w = e → r M = k →
      Inv M → N.lts.Path M w M' → ¬ N.lts.Diverges internal M' := by
    intro e
    induction e using Nat.strong_induction_on with
    | _ e ihe =>
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ihk =>
        intro w M M' he hk hI hp hdiv
        have hS := hst M hI
        obtain ⟨f, g, hf0, hf⟩ := exists_labels_of_diverges hdiv
        -- the path continued by `n` steps of the run
        have hext : ∀ n, N.lts.Path M (w ++ (List.range n).map g) (f n) := by
          intro n
          induction n with
          | zero => simpa [hf0] using hp
          | succ n ih =>
            rw [List.range_succ, List.map_append, ← List.append_assoc]
            refine ih.append ?_
            simp only [List.map_cons, List.map_nil]
            exact .cons ⟨(hf n).2.1, (hf n).2.2⟩ (.nil _)
        have hextInt : ∀ n, externals internal (w ++ (List.range n).map g) = e := by
          intro n
          rw [← he, externals, externals, List.countP_append]
          simp only [Nat.add_eq_left]
          rw [List.countP_eq_zero]
          intro t ht
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 ht
          simpa using (hf i).1
        by_cases hex : ∃ t ∈ w, S M t
        · -- move the first transition of the set to the front
          obtain ⟨t, u, v, hSt, hent, hw, -, hp'⟩ := stubborn_front hS hp hex
          have hI' := hstep M t hI hSt hent
          by_cases hint : internal t
          · refine ihk (r (N.fire M t)) (hk ▸ hr M t hI hSt hent hint) (u ++ v) _ M' ?_ rfl hI'
              hp' hdiv
            rw [← he, hw, externals, externals]
            simp [List.countP_append, hint]
          · refine ihe (externals internal (u ++ v)) ?_ _ (u ++ v) _ M' rfl rfl hI' hp' hdiv
            rw [← he, hw, externals, externals]
            simp [List.countP_append, hint]
        · push Not at hex
          by_cases hexg : ∃ n, S M (g n)
          · -- a transition of the set occurs in the run: move it to the front
            let n := Nat.find hexg
            have hn : S M (g n) := Nat.find_spec hexg
            have hp₁ := hext (n + 1)
            have hmem : g n ∈ w ++ (List.range (n + 1)).map g :=
              List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 (by omega), rfl⟩)
            obtain ⟨t, u, v, hSt, hent, hw, hu, hp'⟩ := stubborn_front hS hp₁ ⟨g n, hmem, hn⟩
            have hI' := hstep M t hI hSt hent
            -- `t` is internal: it comes from the run
            have hint : internal t := by
              have : t ∈ w ++ (List.range (n + 1)).map g := by rw [hw]; simp
              rcases List.mem_append.1 this with h | h
              · exact absurd hSt (hex t h)
              · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h; exact (hf i).1
            have hdiv' : N.lts.Diverges internal (f (n + 1)) :=
              ⟨fun i => f (n + 1 + i), rfl, fun i =>
                ⟨g (n + 1 + i), (hf _).1, (hf _).2.1, by
                  show f (n + 1 + (i + 1)) = _
                  rw [show n + 1 + (i + 1) = n + 1 + i + 1 by omega]
                  exact (hf _).2.2⟩⟩
            refine ihk (r (N.fire M t)) (hk ▸ hr M t hI hSt hent hint) (u ++ v) _ (f (n + 1)) ?_
              rfl hI' hp' hdiv'
            have := hextInt (n + 1)
            rw [hw, externals] at this
            rw [externals]
            simp only [List.countP_append, List.countP_cons, hint, not_true_eq_false,
              decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at this ⊢
            omega
          · push Not at hexg
            -- no transition of the set occurs: fire an internal one of the set first
            have hfirst : ∃ t₁, N.Enabled M t₁ ∧ (t₁ ∈ w ∨ internal t₁) := by
              cases hp with
              | nil => exact ⟨g 0, hf0 ▸ (hf 0).2.1, Or.inr (hf 0).1⟩
              | cons h₁ _ => exact ⟨_, h₁.1, Or.inl List.mem_cons_self⟩
            obtain ⟨t₁, hen₁, ht₁⟩ := hfirst
            have hkey : ∃ tk, S M tk ∧ internal tk ∧ N.Enabled M tk := by
              by_cases hi₁ : internal t₁
              · exact hInt M hI ⟨t₁, hi₁, hen₁⟩
              · obtain ⟨tk, hSk, henk⟩ := hS.key ⟨t₁, hen₁⟩
                refine ⟨tk, hSk, ?_, henk⟩
                by_contra hik
                have := hV M hI tk hSk henk hik t₁ hi₁
                rcases ht₁ with h | h
                · exact hex t₁ h this
                · exact hi₁ h
            obtain ⟨tk, hSk, hik, henk⟩ := hkey
            obtain ⟨hen', hp'⟩ := stubborn_commute hS hp hex hSk henk
            have hdiv' : N.lts.Diverges internal (N.fire M' tk) := by
              have := diverges_fire (f := f) (g := g) hf
                (fun i => hS.enabled tk hSk henk (g i) (hexg i)) (hf0 ▸ hen')
              rwa [hf0] at this
            exact ihk (r (N.fire M tk)) (hk ▸ hr M tk hI hSk henk hik) w _ _ he rfl
              (hstep M tk hI hSk henk) hp' hdiv'
  intro M hM hdiv
  obtain ⟨w, hw⟩ := hM.exists_path
  exact key _ _ w M₀ M rfl rfl h₀ hw hdiv

end Net

end AsyncLean
