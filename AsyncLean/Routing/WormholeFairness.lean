/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.WormholeCheck
import AsyncLean.LTS.Fairness
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Basic.Finite.Prod

/-!
# Starvation freedom under wormhole switching

`Network.WormholeCorrect` says that the network can always make progress and drains once
injection stops, for packets of every length.  `Network.WormholeStarvationFree` says more:
along every **strongly fair** run, even if injection never stops, every packet in the network
is eventually delivered, for packets of every length and every valid selection function.

* `Network.WDelivered r n c` — the packet whose head is in channel `c` at time `n` of the run
  `r` is eventually ejected: its head waits in `c`, advances (and the packet is then
  eventually ejected), or the packet's last flit leaves from `c`.  It follows the packet by its
  head, without naming it.
* `Network.wreachable_finite` — with finitely many legal pairs, finitely many configurations
  are reachable, for packets of any length: no channel is ever held twice (`WExcl`).
* `Network.wormholeStarvationFree_of_ranking` — a correct network, finitely many legal pairs
  and a ranking function that decreases on every hop give starvation freedom.
* `Network.wormholeStarvationFree_of_escape_ranking` — from Duato's condition for wormhole
  switching and a ranking function; `Network.wormholeStarvationFree_of_wcheckCert` — from the
  checker of `async_decide`.

The proof is that of `Network.starvationFree_of_escape_ranking`: while the head of a packet
sits in `c`, the packet keeps it there.  Some configuration recurs infinitely often, and from
it the network can drain, so from a configuration that recurs infinitely often some step
moves that head out of `c`.  Strong fairness forces such a step.  Channels are held
exclusively, so the packet that advances from `c` is the one we follow, and the ranking
function bounds the number of its hops.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*}

/-! ### Exclusive channels and finitely many configurations -/

/-- Every pair a packet holds is legal. -/
def WLegal (legal : C → P → Prop) (w : WConfig C P) : Prop := ∀ x ∈ w, ∀ q ∈ x, legal q.1 q.2

/-- No channel is held twice. -/
def WExcl (w : WConfig C P) : Prop := (w.flatten.map Prod.fst).Nodup

theorem not_mem_of_not_occ {w : WConfig C P} {c : C} (h : ¬ w.Occ c) :
    c ∉ w.flatten.map Prod.fst := by
  intro hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
  obtain ⟨x, hx, hqx⟩ := List.mem_flatten.1 hq
  exact h ⟨x, hx, q, hqx, rfl⟩

theorem flatten_mid (l₁ l₂ : WConfig C P) (x : Worm C P) :
    (l₁ ++ x :: l₂).flatten = l₁.flatten ++ (x ++ l₂.flatten) := by
  simp [List.flatten_append]

theorem flatten_sub_mid {l₁ l₂ : WConfig C P} {x y : Worm C P} (h : x.Sublist y) :
    ((l₁ ++ x :: l₂).flatten.map Prod.fst).Sublist ((l₁ ++ y :: l₂).flatten.map Prod.fst) := by
  rw [flatten_mid, flatten_mid]
  exact ((List.Sublist.refl _).append (h.append (List.Sublist.refl _))).map _

variable (N : Network C P)

theorem wexcl_step {tail : P → ℕ} {sel : WSelection C P} {w w' : WConfig C P}
    {a : WAct C P} (hw : WExcl w) (h : N.WStep tail sel w a w') : WExcl w' := by
  unfold WExcl at *
  cases h with
  | @inject _ c p _ hfree =>
    simp only [List.flatten_cons, List.singleton_append, List.map_cons, List.nodup_cons]
    exact ⟨not_mem_of_not_occ hfree, hw⟩
  | @advance l₁ l₂ c c' p p' rest _ _ hfree =>
    have hsub := flatten_sub_mid (l₁ := l₁) (l₂ := l₂)
      (List.take_sublist (tail p') ((c, p) :: rest))
    have hout := not_mem_of_not_occ hfree
    simp only [flatten_mid, List.map_append] at hsub hout hw ⊢
    rw [List.map_cons, List.cons_append, List.nodup_middle, List.nodup_cons]
    exact ⟨fun hc => hout (hsub.subset hc), hw.sublist hsub⟩
  | @drain l₁ l₂ c p q rest _ =>
    exact hw.sublist (flatten_sub_mid ((List.dropLast_sublist _).cons_cons _))
  | @eject l₁ l₂ c p _ =>
    refine hw.sublist ?_
    rw [flatten_mid, List.flatten_append]
    simp only [List.map_append]
    exact (List.Sublist.refl _).append (List.sublist_append_right _ _)

theorem wlegal_step {legal : C → P → Prop} (hcl : N.Closed legal) {tail : P → ℕ}
    {sel : WSelection C P} (hsel : N.WValidSel sel) {w w' : WConfig C P} {a : WAct C P}
    (hw : WLegal legal w) (h : N.WStep tail sel w a w') : WLegal legal w' := by
  cases h with
  | @inject _ c p hinj _ =>
    intro x hx q hq
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [List.mem_singleton] at hq; subst hq; exact hcl.inject _ hinj
    · exact hw x hx q hq
  | @advance l₁ l₂ c c' p p' rest harr hsq _ =>
    intro x hx q hq
    rcases mem_replace (y := (c, p) :: rest) hx with rfl | hx
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact hcl.route c p _ (hw _ mem_mid _ List.mem_cons_self) harr (hsel.sub _ _ _ _ hsq)
      · exact hw _ mem_mid q (List.mem_of_mem_take hq)
    · exact hw x hx q hq
  | @drain l₁ l₂ c p q₀ rest _ =>
    intro x hx q hq
    rcases mem_replace (y := (c, p) :: q₀ :: rest) hx with rfl | hx
    · refine hw _ mem_mid q ?_
      rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.dropLast_subset _ hq)
    · exact hw x hx q hq
  | eject _ => exact fun x hx => hw x (mem_of_mem_remove hx)

/-- The invariants of reachable configurations: heads and pairs are legal, channels are held
exclusively. -/
theorem winv_reach {legal : C → P → Prop} (hcl : N.Closed legal) {tail : P → ℕ}
    {sel : WSelection C P} (hsel : N.WValidSel sel) {w : WConfig C P}
    (h : (N.wltsWith tail sel).Reachable [] w) :
    WHeads legal w ∧ WLegal legal w ∧ WExcl w :=
  h.invariant (I := fun w => WHeads legal w ∧ WLegal legal w ∧ WExcl w)
    ⟨fun _ hx => absurd hx List.not_mem_nil, fun _ hx => absurd hx List.not_mem_nil,
      List.nodup_nil⟩
    fun _ _ _ ⟨hh, hl, he⟩ hst =>
      ⟨N.wheads_step hcl hsel hh hst, N.wlegal_step hcl hsel hl hst, N.wexcl_step he hst⟩

/-- Lists of bounded length over a finite set. -/
theorem finite_lists {α : Type*} {S : Set α} (hS : S.Finite) :
    ∀ n, {l : List α | l.length ≤ n ∧ ∀ x ∈ l, x ∈ S}.Finite
  | 0 => (Set.finite_singleton []).subset fun l ⟨hl, _⟩ => by
      simpa using List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)
  | n + 1 => by
    refine ((Set.finite_singleton []).union
      ((Set.Finite.prod hS (finite_lists hS n)).image fun q => q.1 :: q.2)).subset ?_
    rintro (_ | ⟨x, l⟩) ⟨hl, hx⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨(x, l), ⟨hx x List.mem_cons_self, ?_, fun y hy => hx y
        (List.mem_cons_of_mem _ hy)⟩, rfl⟩
      simp only [List.length_cons] at hl
      show l.length ≤ n
      omega

theorem eq_of_flatten {α : Type*} :
    ∀ {a b : List (List α)}, a.flatten = b.flatten → a.map List.length = b.map List.length →
      a = b
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | x :: a, y :: b, hf, hl => by
    simp only [List.map_cons, List.cons.injEq] at hl
    simp only [List.flatten_cons] at hf
    obtain ⟨rfl, hf'⟩ := List.append_inj hf hl.1
    rw [eq_of_flatten hf' hl.2]

theorem length_le_flatten {α : Type*} {x : List α} :
    ∀ {w : List (List α)}, x ∈ w → x.length ≤ w.flatten.length
  | y :: w, h => by
    rw [List.flatten_cons, List.length_append]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := length_le_flatten h; omega

theorem count_le_flatten {α : Type*} :
    ∀ {w : List (List α)}, (∀ x ∈ w, x ≠ []) → w.length ≤ w.flatten.length
  | [], _ => le_rfl
  | y :: w, h => by
    rw [List.flatten_cons, List.length_append, List.length_cons]
    have hy : y.length ≠ 0 := fun h0 => h y List.mem_cons_self (List.eq_nil_of_length_eq_zero h0)
    have := count_le_flatten (w := w) fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

/-- **Finitely many configurations**: with finitely many legal pairs, finitely many
configurations are reachable under wormhole switching, for packets of any length. -/
theorem wreachable_finite {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) (tail : P → ℕ) {sel : WSelection C P}
    (hsel : N.WValidSel sel) : {w | (N.wltsWith tail sel).Reachable [] w}.Finite := by
  classical
  let K := hfin.toFinset.card
  let F : WConfig C P → List (C × P) × List ℕ := fun w => (w.flatten, w.map List.length)
  have hbound : ∀ w, (N.wltsWith tail sel).Reachable [] w → w.flatten.length ≤ K := by
    intro w hw
    obtain ⟨-, hl, he⟩ := N.winv_reach hcl hsel hw
    have hnd : w.flatten.Nodup := List.Nodup.of_map _ he
    rw [← List.toFinset_card_of_nodup hnd]
    refine Finset.card_le_card fun q hq => ?_
    rw [List.mem_toFinset] at hq
    obtain ⟨x, hx, hqx⟩ := List.mem_flatten.1 hq
    exact (Set.Finite.mem_toFinset _).2 (hl x hx q hqx)
  refine Set.Finite.of_finite_image (f := F) ?_ ?_
  · refine (Set.Finite.prod (finite_lists hfin K) (finite_lists (Finset.range (K + 1)).finite_toSet K)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hh, hl, -⟩ := N.winv_reach hcl hsel hw
    have hb := hbound w hw
    refine ⟨⟨hb, fun q hq => ?_⟩, ?_, fun n hn => ?_⟩
    · obtain ⟨x, hx, hqx⟩ := List.mem_flatten.1 hq
      exact hl x hx q hqx
    · rw [List.length_map]
      refine le_trans (count_le_flatten fun x hx => ?_) hb
      obtain ⟨h, rest, rfl, -⟩ := hh x hx
      exact List.cons_ne_nil _ _
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
      simp only [Finset.coe_range, Set.mem_Iio]
      have := (length_le_flatten hx).trans hb
      omega
  · intro a _ b _ hab
    simp only [F, Prod.mk.injEq] at hab
    exact eq_of_flatten hab.1 hab.2

/-! ### Following a packet by its head -/

/-- A packet of `w` has its head in channel `c`, with header `p`. -/
def WHead (w : WConfig C P) (c : C) (p : P) : Prop := ∃ rest, ((c, p) :: rest) ∈ w

/-- The packet whose head is in channel `c` at time `n` of `r` is eventually ejected. -/
inductive WDelivered {tail : P → ℕ} {sel : WSelection C P} (r : (N.wltsWith tail sel).Run []) :
    ℕ → C → Prop
  | eject {n : ℕ} {c : C} : r.lab n = .eject c → WDelivered r n c
  | advance {n : ℕ} {c c' : C} {p' : P} : r.lab n = .advance c c' p' →
      WDelivered r (n + 1) c' → WDelivered r n c
  | wait {n : ℕ} {c : C} : r.lab n ≠ .eject c → (∀ c' p', r.lab n ≠ .advance c c' p') →
      WDelivered r (n + 1) c → WDelivered r n c

/-- **Starvation freedom under wormhole switching**: along every strongly fair run, for packets
of every length and every valid selection function, every packet in the network is eventually
delivered. -/
def WormholeStarvationFree : Prop :=
  ∀ tail sel, N.WValidSel sel → ∀ r : (N.wltsWith tail sel).Run [], r.StronglyFair →
    ∀ n c p, WHead (r.st n) c p → N.WDelivered r n c

/-- The action moves the head of the packet in channel `c` out of it. -/
def WLeaves (c : C) : WAct C P → Prop
  | .eject c' => c' = c
  | .advance c' _ _ => c' = c
  | _ => False

theorem wleaves_iff {c : C} {a : WAct C P} :
    WLeaves c a ↔ a = .eject c ∨ ∃ c' p', a = .advance c c' p' := by
  cases a <;> simp [WLeaves, eq_comm]

variable {N}

/-- A step that does not move the head out of `c` keeps it there. -/
theorem whead_stay {tail : P → ℕ} {sel : WSelection C P} {w w' : WConfig C P} {a : WAct C P}
    {c : C} {p : P} (hst : N.WStep tail sel w a w') (h : WHead w c p) (ha : ¬ WLeaves c a) :
    WHead w' c p := by
  obtain ⟨rest, hx⟩ := h
  cases hst with
  | inject => exact ⟨rest, List.mem_cons_of_mem _ hx⟩
  | @advance l₁ l₂ c₀ c' p₀ p' rest₀ _ _ _ =>
    refine ⟨rest, ?_⟩
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with hx | hx | hx
    · exact Or.inl hx
    · simp only [List.cons.injEq, Prod.mk.injEq] at hx
      exact absurd hx.1.1.symm ha
    · exact Or.inr (Or.inr hx)
  | @drain l₁ l₂ c₀ p₀ q rest₀ _ =>
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | hx | hx
    · exact ⟨rest, List.mem_append_left _ hx⟩
    · simp only [List.cons.injEq, Prod.mk.injEq] at hx
      obtain ⟨⟨rfl, rfl⟩, -⟩ := hx
      exact ⟨_, mem_mid⟩
    · exact ⟨rest, by simp [hx]⟩
  | @eject l₁ l₂ c₀ p₀ _ =>
    refine ⟨rest, ?_⟩
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with hx | hx | hx
    · exact Or.inl hx
    · simp only [List.cons.injEq, Prod.mk.injEq] at hx
      exact absurd hx.1.1.symm ha
    · exact Or.inr hx

/-- Along a drain from a configuration with a head in `c`, some step moves it out. -/
theorem exists_wleave_of_drain {tail : P → ℕ} {sel : WSelection C P} {s : WConfig C P}
    {c : C} {p : P} (hs : WHead s c p)
    (h : Relation.ReflTransGen ((N.wltsWith tail sel).IStep WAct.IsMove) s []) :
    ∃ s₁ a s₂, (N.wltsWith tail sel).Reachable s s₁ ∧ (N.wltsWith tail sel).step s₁ a s₂ ∧
      WLeaves c a := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing p with
  | refl => obtain ⟨_, h⟩ := hs; exact absurd h List.not_mem_nil
  | head hst _ ih =>
    obtain ⟨a, -, hst⟩ := hst
    by_cases ha : WLeaves c a
    · exact ⟨_, a, _, LTS.Reachable.refl _, hst, ha⟩
    · obtain ⟨s₁, a', s₂, hr, h', ha'⟩ := ih (whead_stay hst hs ha)
      exact ⟨s₁, a', s₂, LTS.Reachable.head ⟨a, hst⟩ hr, h', ha'⟩

/-- In a network that drains, with finitely many reachable configurations, a head cannot sit
in a channel forever along a strongly fair run. -/
theorem exists_wleave {tail : P → ℕ} {sel : WSelection C P} (r : (N.wltsWith tail sel).Run [])
    (hfin : {w | (N.wltsWith tail sel).Reachable [] w}.Finite) (hfair : r.StronglyFair)
    (hdrain : ∀ w, (N.wltsWith tail sel).Reachable [] w →
      Relation.ReflTransGen ((N.wltsWith tail sel).IStep WAct.IsMove) w [])
    {n : ℕ} {c : C} {p : P} (hp : WHead (r.st n) c p) :
    ∃ m, n ≤ m ∧ WLeaves c (r.lab m) := by
  by_contra hne
  push Not at hne
  have hstay : ∀ d, WHead (r.st (n + d)) c p := by
    intro d
    induction d with
    | zero => exact hp
    | succ d ih => exact whead_stay (r.step (n + d)) ih (hne _ (by omega))
  obtain ⟨s, hs⟩ := r.exists_infOften hfin
  obtain ⟨m₀, hm₀, rfl⟩ := hs n
  have hsc : WHead (r.st m₀) c p := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm₀
    exact hstay d
  obtain ⟨s₁, a, s₂, hr, hst, ha⟩ := exists_wleave_of_drain hsc (hdrain _ (r.reachable m₀))
  obtain ⟨k, hk, -, hlab, -⟩ := hfair s₁ a s₂ (LTS.Run.infOften_of_reachable hfair hs hr) hst n
  exact hne k hk (hlab ▸ ha)

variable (N)

/-- The head in `c` at time `n` stays there until time `n + d` and then leaves. -/
theorem wdelivered_of_leave {tail : P → ℕ} {sel : WSelection C P}
    (r : (N.wltsWith tail sel).Run []) {c : C} :
    ∀ d n, (∀ k, n ≤ k → k < n + d → ¬ WLeaves c (r.lab k)) → N.WDelivered r (n + d) c →
      N.WDelivered r n c
  | 0, _, _, h => h
  | d + 1, n, hstay, h => by
    have h' : N.WDelivered r (n + 1) c :=
      wdelivered_of_leave r d (n + 1) (fun k hk hk' => hstay k (by omega) (by omega))
        (by rwa [show n + 1 + d = n + (d + 1) by omega])
    have hl := hstay n le_rfl (by omega)
    exact WDelivered.wait (fun he => hl (wleaves_iff.2 (Or.inl he)))
      (fun c' p' hh => hl (wleaves_iff.2 (Or.inr ⟨c', p', hh⟩))) h'

variable {N}

/-- **Every packet is delivered** along every strongly fair run of a deadlock-free,
livelock-free network under wormhole switching with finitely many reachable configurations,
when a ranking function decreases on every hop. -/
theorem wdelivered_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {tail : P → ℕ} {sel : WSelection C P} (hsel : N.WValidSel sel)
    (hD : N.WDeadlockFreeWith tail sel) (hL : N.WLivelockFreeWith tail sel)
    (hfin : {w | (N.wltsWith tail sel).Reachable [] w}.Finite)
    (r : (N.wltsWith tail sel).Run []) (hfair : r.StronglyFair) :
    ∀ n c p, WHead (r.st n) c p → N.WDelivered r n c := by
  have hdrain : ∀ w, (N.wltsWith tail sel).Reachable [] w →
      Relation.ReflTransGen ((N.wltsWith tail sel).IStep WAct.IsMove) w [] :=
    fun w hw => N.wdrain hD hL hw
  suffices key : ∀ k n c p, rk c p = k → WHead (r.st n) c p → N.WDelivered r n c from
    fun n c p hp => key _ n c p rfl hp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n c p hk hp
    have hex := exists_wleave r hfin hfair hdrain hp
    classical
    let m := Nat.find hex
    have hm : n ≤ m ∧ WLeaves c (r.lab m) := Nat.find_spec hex
    have hbefore : ∀ k, n ≤ k → k < m → ¬ WLeaves c (r.lab k) := fun k hk hkm hl =>
      Nat.find_min hex hkm ⟨hk, hl⟩
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm.1
    have hstay : ∀ e, e ≤ d → WHead (r.st (n + e)) c p := by
      intro e
      induction e with
      | zero => intro; exact hp
      | succ e ih' =>
        intro he
        exact whead_stay (r.step (n + e)) (ih' (by omega)) (hbefore _ (by omega) (by omega))
    have hpm : WHead (r.st m) c p := hd ▸ hstay d le_rfl
    refine wdelivered_of_leave N r d n (fun k hk hk' => hbefore k hk (by omega)) ?_
    rw [← hd]
    rcases wleaves_iff.1 hm.2 with he | ⟨c', p', hh⟩
    · exact WDelivered.eject he
    · refine WDelivered.advance hh ?_
      obtain ⟨-, hl, hex'⟩ := N.winv_reach hcl hsel (r.reachable m)
      have hst := r.step m
      rw [hh] at hst
      change N.WStep tail sel _ _ _ at hst
      generalize hs : r.st m = s at hst hpm hl hex'
      generalize hs' : r.st (m + 1) = s' at hst
      cases hst with
      | @advance l₁ l₂ _ _ py _ resty harr hq _ =>
        -- channels are held exclusively: the advancing packet is the one in `c`
        obtain ⟨rest, hx⟩ := hpm
        have hpy : (c, p) = (c, py) := by
          refine List.inj_on_of_nodup_map hex' ?_ ?_ rfl
          · exact List.mem_flatten.2 ⟨_, hx, List.mem_cons_self⟩
          · exact List.mem_flatten.2 ⟨_, mem_mid, List.mem_cons_self⟩
        cases hpy
        have hlt := hrk c p _ (hl _ mem_mid _ List.mem_cons_self) harr (hsel.sub _ _ _ _ hq)
        exact ih _ (hk ▸ hlt) (m + 1) c' p' rfl ⟨_, by rw [hs']; exact mem_mid⟩

/-- **Starvation freedom from correctness and a ranking function**: a network that is correct
under wormhole switching, with finitely many legal pairs and a ranking function that decreases
on every hop, delivers every packet of every strongly fair run, for packets of every length
and every selection function. -/
theorem wormholeStarvationFree_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal)
    (hfin : {q : C × P | legal q.1 q.2}.Finite) (h : N.WormholeCorrect) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.WormholeStarvationFree := by
  intro tail sel hsel r hfair n c p hp
  exact wdelivered_of_ranking hcl rk hrk hsel (h.1 tail sel hsel) (h.2 tail sel hsel)
    (N.wreachable_finite hcl hfin tail hsel) r hfair n c p hp

/-- **Starvation freedom from Duato's condition for wormhole switching and a ranking
function**, with finitely many legal pairs. -/
theorem wormholeStarvationFree_of_escape_ranking {legal : C → P → Prop} {E : C → Prop}
    (hcl : N.Closed legal) (hfin : {q : C × P | legal q.1 q.2}.Finite)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → ∃ q ∈ N.route c p, E q.1)
    (hwf : WellFounded (flip (N.ExtDep legal E))) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.WormholeStarvationFree :=
  wormholeStarvationFree_of_ranking hcl hfin
    ⟨N.wormholeDeadlockFree_of_escape hcl hconn hwf, N.wormholeLivelockFree_of_ranking hcl rk hrk⟩
    rk hrk

/-- A passing wormhole certificate (`Network.wcheckCert`) also proves **starvation freedom**
under wormhole switching. -/
theorem wormholeStarvationFree_of_wcheckCert [DecidableEq C] [DecidableEq P] {cmpC : C → C → Ordering}
    {cmpQ : C × P → C × P → Ordering} {E : C → Bool} {pairs : BTree ((C × P) × ℕ)}
    {ranks : BTree (C × ℕ)} {lo : BTree ((C × P) × ℕ)}
    (h : N.wcheckCert cmpC cmpQ E pairs ranks lo = true) : N.WormholeStarvationFree := by
  have hc := wormholeCorrect_of_wcheckCert h
  simp only [wcheckCert, Bool.and_eq_true, List.all_eq_true, BTree.all_eq_true] at h
  obtain ⟨hinj, hall⟩ := h
  let legal : C → P → Prop := fun c p => legalB cmpQ pairs (c, p) = true
  have hmove : ∀ c p, legal c p → N.arrived c p = false → ∀ q ∈ N.route c p,
      legalB cmpQ pairs q = true ∧ pairRank cmpQ pairs q < pairRank cmpQ pairs (c, p) := by
    intro c p hl ha q hq
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hl
    have := hall _ (BTree.mem_toList_of_findData hr)
    simp only [wcheckPair, ha, Bool.false_or, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at this
    obtain ⟨⟨h1, h2⟩, -⟩ := this.2.1 q hq
    exact ⟨h1, h2⟩
  have hcl : N.Closed legal :=
    ⟨fun q hq => hinj q hq, fun c p q hl ha hq => (hmove c p hl ha q hq).1⟩
  have hfin : {q : C × P | legal q.1 q.2}.Finite := by
    refine (Finset.finite_toSet ((pairs.toList.map fun e => e.1).toFinset)).subset ?_
    rintro q hl
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hl
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact ⟨_, BTree.mem_toList_of_findData hr, rfl⟩
  exact wormholeStarvationFree_of_ranking hcl hfin hc (fun c p => pairRank cmpQ pairs (c, p))
    fun c p q hl ha hq => (hmove c p hl ha q hq).2

end Network

end AsyncLean
