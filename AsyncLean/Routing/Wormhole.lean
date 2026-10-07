/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Basic

/-!
# Wormhole switching

Under *wormhole switching* a packet is a train of flits that spans several channels: its head
acquires channels one at a time while its tail still holds the channels behind it, and a
blocked head blocks the whole packet in place.  Deadlock freedom is then harder than for
store-and-forward switching: a packet can wait for a channel while holding many others.

## The model

A packet (`Worm`) is the list of channels it occupies, head first, each with the header the
packet carried when its head entered that channel.  A configuration (`WConfig`) is the list of
packets in the network.  With `tail p` the number of channels a packet with header `p` trails
behind its head (its length in flits minus one, for one-flit channel buffers):

* `inject` — a packet enters a free channel;
* `advance` — the head moves to a free channel offered by the selection function; the packet
  keeps at most `tail p' + 1` channels, so its last channel is released once it is stretched
  out;
* `drain` — at its destination, the packet releases its last channel;
* `eject` — the last flit leaves the network.

`WormholeDeadlockFree`, `WormholeLivelockFree` and `WormholeCorrect` quantify over **every
packet length function `tail`** and every work-conserving selection function.

## Main results

* `wormholeDeadlockFree_of_escape` — **Duato's theorem for wormhole switching**: if every legal
  packet that has not arrived may request an *escape channel* (a channel in `E`), and the
  *extended* channel dependency graph of the escape channels is acyclic, the network is
  deadlock free.  The extended graph `ExtDep` has an edge `e → e'` when a packet holding `e`
  may request `e'`, either directly or after passing through non-escape channels only (Duato's
  direct and indirect dependencies).
* `wormholeDeadlockFree_of_cdg` — **Dally and Seitz's theorem** for wormhole switching.
* `wormholeLivelockFree_of_ranking` — a ranking function that decreases on every hop rules out
  livelock, for packets of any length.
* `WormholeCorrect.drain` — every reachable configuration drains once injection stops.
* `deadlockFree_of_wormholeDeadlockFree` — one-flit packets behave like store-and-forward
  packets, so wormhole deadlock freedom implies store-and-forward deadlock freedom.
* `not_wormholeDeadlockFree_of_refuteB`, `not_wormholeLivelockFree_of_refuteB` — refutations
  from executable counterexample runs, decided by the kernel.
-/

namespace AsyncLean

namespace Network

variable {C P : Type*}

/-- A packet under wormhole switching: the channels it holds, head first, each with the header
the packet carried when its head entered it. -/
abbrev Worm (C P : Type*) := List (C × P)

/-- A configuration under wormhole switching: the packets in the network. -/
abbrev WConfig (C P : Type*) := List (Worm C P)

/-- Channel `c` is held by some packet. -/
def WConfig.Occ (w : WConfig C P) (c : C) : Prop := ∃ x ∈ w, ∃ q ∈ x, q.1 = c

/-- A selection function for wormhole switching. -/
abbrev WSelection (C P : Type*) := WConfig C P → C → P → List (C × P)

/-- The actions under wormhole switching. -/
inductive WAct (C P : Type*) where
  /-- A packet with header `p` enters channel `c`. -/
  | inject (c : C) (p : P)
  /-- The head of the packet in channel `c` moves to channel `c'` with header `p'`. -/
  | advance (c c' : C) (p' : P)
  /-- The arrived packet whose head is in `c` releases its last channel. -/
  | drain (c : C)
  /-- The last flit of the arrived packet in `c` leaves the network. -/
  | eject (c : C)
  deriving DecidableEq, Repr

/-- The action moves a packet already in the network. -/
def WAct.isMove : WAct C P → Bool
  | .inject _ _ => false
  | _ => true

/-- The action moves a packet already in the network (the internal actions for livelock). -/
def WAct.IsMove (a : WAct C P) : Prop := a.isMove = true

variable (N : Network C P)

/-- A valid wormhole selection function: it offers only permitted hops, and a free one
whenever a permitted channel is free. -/
structure WValidSel (sel : WSelection C P) : Prop where
  sub : ∀ w c p q, q ∈ sel w c p → q ∈ N.route c p
  conserving : ∀ w c p, (∃ q ∈ N.route c p, ¬ w.Occ q.1) → ∃ q ∈ sel w c p, ¬ w.Occ q.1

/-- Every permitted hop may be taken. -/
def wadaptive : WSelection C P := fun _ => N.route

theorem wadaptive_valid : N.WValidSel N.wadaptive := ⟨fun _ _ _ _ h => h, fun _ _ _ h => h⟩

/-- The steps under wormhole switching, with packets trailing `tail p` channels behind their
head. -/
inductive WStep (tail : P → ℕ) (sel : WSelection C P) :
    WConfig C P → WAct C P → WConfig C P → Prop
  | inject {w : WConfig C P} {c : C} {p : P} : (c, p) ∈ N.inject → ¬ w.Occ c →
      WStep tail sel w (.inject c p) ([(c, p)] :: w)
  | advance {l₁ l₂ : WConfig C P} {c c' : C} {p p' : P} {rest : Worm C P} :
      N.arrived c p = false → (c', p') ∈ sel (l₁ ++ ((c, p) :: rest) :: l₂) c p →
      ¬ WConfig.Occ (l₁ ++ ((c, p) :: rest) :: l₂) c' →
      WStep tail sel (l₁ ++ ((c, p) :: rest) :: l₂) (.advance c c' p')
        (l₁ ++ ((c', p') :: ((c, p) :: rest).take (tail p')) :: l₂)
  | drain {l₁ l₂ : WConfig C P} {c : C} {p : P} {q : C × P} {rest : Worm C P} :
      N.arrived c p = true →
      WStep tail sel (l₁ ++ ((c, p) :: q :: rest) :: l₂) (.drain c)
        (l₁ ++ ((c, p) :: (q :: rest).dropLast) :: l₂)
  | eject {l₁ l₂ : WConfig C P} {c : C} {p : P} : N.arrived c p = true →
      WStep tail sel (l₁ ++ [(c, p)] :: l₂) (.eject c) (l₁ ++ l₂)

/-- The network under wormhole switching as a transition system. -/
def wltsWith (tail : P → ℕ) (sel : WSelection C P) : LTS (WConfig C P) (WAct C P) where
  step := N.WStep tail sel

/-- Some packet of `w` can move. -/
def WMovable (tail : P → ℕ) (sel : WSelection C P) (w : WConfig C P) : Prop :=
  ∃ a w', a.IsMove ∧ (N.wltsWith tail sel).step w a w'

/-- Whenever the network holds a packet, some packet can move. -/
def WDeadlockFreeWith (tail : P → ℕ) (sel : WSelection C P) : Prop :=
  ∀ w, (N.wltsWith tail sel).Reachable [] w → w ≠ [] → N.WMovable tail sel w

/-- There is no infinite run without injections. -/
def WLivelockFreeWith (tail : P → ℕ) (sel : WSelection C P) : Prop :=
  (N.wltsWith tail sel).LivelockFree WAct.IsMove []

/-- **Wormhole deadlock freedom**, for packets of every length and every valid selection. -/
def WormholeDeadlockFree : Prop :=
  ∀ tail sel, N.WValidSel sel → N.WDeadlockFreeWith tail sel

/-- **Wormhole livelock freedom**, for packets of every length and every valid selection. -/
def WormholeLivelockFree : Prop :=
  ∀ tail sel, N.WValidSel sel → N.WLivelockFreeWith tail sel

/-- Deadlock and livelock freedom under wormhole switching. -/
def WormholeCorrect : Prop := N.WormholeDeadlockFree ∧ N.WormholeLivelockFree

/-! ### Escape channels and the extended dependency graph -/

/-- `NE legal E e q`: a packet whose head entered the escape channel `e` can have its head at
`q`, having passed since only through channels outside `E`. -/
inductive NE (legal : C → P → Prop) (E : C → Prop) (e : C) : C × P → Prop
  | base {p : P} : legal e p → E e → NE legal E e (e, p)
  | step {q q' : C × P} : NE legal E e q → N.arrived q.1 q.2 = false → q' ∈ N.route q.1 q.2 →
      ¬ E q'.1 → NE legal E e q'

/-- **Duato's extended channel dependency graph** of the escape channels `E`: `ExtDep e e'`
iff a packet holding `e` may request the escape channel `e'`, directly or after passing
through channels outside `E` only. -/
def ExtDep (legal : C → P → Prop) (E : C → Prop) (e e' : C) : Prop :=
  ∃ q, N.NE legal E e q ∧ N.arrived q.1 q.2 = false ∧ ∃ p', (e', p') ∈ N.route q.1 q.2 ∧ E e'

/-- The head of every packet is a legal pair. -/
def WHeads (legal : C → P → Prop) (w : WConfig C P) : Prop :=
  ∀ x ∈ w, ∃ h rest, x = h :: rest ∧ legal h.1 h.2

/-- Every escape channel a packet holds leads, along extended dependencies, to an escape
channel from which its head was reached through non-escape channels only. -/
def WEscapes (legal : C → P → Prop) (E : C → Prop) (w : WConfig C P) : Prop :=
  ∀ x ∈ w, ∀ h rest, x = h :: rest → ∀ q ∈ x, E q.1 →
    ∃ e₀, Relation.ReflTransGen (N.ExtDep legal E) q.1 e₀ ∧ N.NE legal E e₀ h

theorem mem_replace {α : Type*} {x y y' : α} {l₁ l₂ : List α} (h : x ∈ l₁ ++ y' :: l₂) :
    x = y' ∨ x ∈ l₁ ++ y :: l₂ := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  tauto

theorem mem_of_mem_remove {α : Type*} {x y : α} {l₁ l₂ : List α} (h : x ∈ l₁ ++ l₂) :
    x ∈ l₁ ++ y :: l₂ := by
  simp only [List.mem_append, List.mem_cons] at h ⊢
  tauto

theorem mem_mid {α : Type*} {y : α} {l₁ l₂ : List α} : y ∈ l₁ ++ y :: l₂ := by simp

theorem wheads_step {legal : C → P → Prop} (hcl : N.Closed legal) {tail : P → ℕ}
    {sel : WSelection C P} (hsel : N.WValidSel sel) {w w' : WConfig C P} {a : WAct C P}
    (hw : WHeads legal w) (h : N.WStep tail sel w a w') : WHeads legal w' := by
  cases h with
  | @inject _ c p hinj _ =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, _, rfl, hcl.inject _ hinj⟩
    · exact hw x hx
  | @advance l₁ l₂ c c' p p' rest harr hq _ =>
    intro x hx
    rcases mem_replace (y := (c, p) :: rest) hx with rfl | hx
    · obtain ⟨h, r, he, hl⟩ := hw _ mem_mid
      cases he
      exact ⟨_, _, rfl, hcl.route c p _ hl harr (hsel.sub _ _ _ _ hq)⟩
    · exact hw x hx
  | @drain l₁ l₂ c p q rest _ =>
    intro x hx
    rcases mem_replace (y := (c, p) :: q :: rest) hx with rfl | hx
    · obtain ⟨h, r, he, hl⟩ := hw _ mem_mid
      cases he
      exact ⟨_, _, rfl, hl⟩
    · exact hw x hx
  | eject _ => exact fun x hx => hw x (mem_of_mem_remove hx)

theorem wescapes_step {legal : C → P → Prop} {E : C → Prop} (hcl : N.Closed legal)
    {tail : P → ℕ} {sel : WSelection C P} (hsel : N.WValidSel sel) {w w' : WConfig C P}
    {a : WAct C P} (hh : WHeads legal w) (hw : N.WEscapes legal E w)
    (h : N.WStep tail sel w a w') : N.WEscapes legal E w' := by
  classical
  cases h with
  | @inject _ c p hinj _ =>
    intro x hx h' rest' hx' q hq hE
    rcases List.mem_cons.1 hx with rfl | hx
    · cases hx'
      rw [List.mem_singleton] at hq
      subst hq
      exact ⟨c, Relation.ReflTransGen.refl, NE.base (hcl.inject _ hinj) hE⟩
    · exact hw x hx h' rest' hx' q hq hE
  | @advance l₁ l₂ c c' p p' rest harr hsq _ =>
    intro x hx h' rest' hx' q hq hE
    rcases mem_replace (y := (c, p) :: rest) hx with rfl | hx
    · cases hx'
      obtain ⟨h₀, r₀, he₀, hl⟩ := hh _ mem_mid
      cases he₀
      have hroute := hsel.sub _ _ _ _ hsq
      have hl' : legal c' p' := hcl.route c p _ hl harr hroute
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨c', Relation.ReflTransGen.refl, NE.base hl' hE⟩
      · obtain ⟨e₀, hrt, hne⟩ := hw _ mem_mid _ _ rfl q (List.mem_of_mem_take hq) hE
        by_cases hc' : E c'
        · exact ⟨c', hrt.tail ⟨(c, p), hne, harr, p', hroute, hc'⟩, NE.base hl' hc'⟩
        · exact ⟨e₀, hrt, NE.step hne harr hroute hc'⟩
    · exact hw x hx h' rest' hx' q hq hE
  | @drain l₁ l₂ c p q₀ rest _ =>
    intro x hx h' rest' hx' q hq hE
    rcases mem_replace (y := (c, p) :: q₀ :: rest) hx with rfl | hx
    · cases hx'
      refine hw _ mem_mid _ _ rfl q ?_ hE
      rcases List.mem_cons.1 hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.dropLast_subset _ hq)
    · exact hw x hx h' rest' hx' q hq hE
  | eject _ => exact fun x hx => hw x (mem_of_mem_remove hx)

theorem winv_of_reachable {legal : C → P → Prop} {E : C → Prop} (hcl : N.Closed legal)
    {tail : P → ℕ} {sel : WSelection C P} (hsel : N.WValidSel sel) {w : WConfig C P}
    (h : (N.wltsWith tail sel).Reachable [] w) :
    WHeads legal w ∧ N.WEscapes legal E w :=
  h.invariant (I := fun w => WHeads legal w ∧ N.WEscapes legal E w)
    ⟨fun _ hx => absurd hx (List.not_mem_nil), fun _ hx => absurd hx (List.not_mem_nil)⟩
    fun _ _ _ ⟨hh, he⟩ hst => ⟨N.wheads_step hcl hsel hh hst, N.wescapes_step hcl hsel hh he hst⟩

/-- The head of a packet can move, or it requests an occupied escape channel. -/
theorem head_move {legal : C → P → Prop} {E : C → Prop} {tail : P → ℕ}
    {sel : WSelection C P} (hsel : N.WValidSel sel)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → ∃ q ∈ N.route c p, E q.1)
    {w : WConfig C P} {c : C} {p : P} {rest : Worm C P} (hx : (c, p) :: rest ∈ w)
    (hl : legal c p) :
    N.WMovable tail sel w ∨ ∃ e p', N.arrived c p = false ∧ (e, p') ∈ N.route c p ∧ E e ∧
      w.Occ e := by
  classical
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  cases harr : N.arrived c p with
  | true =>
    left
    cases rest with
    | nil => exact ⟨.eject c, _, rfl, WStep.eject harr⟩
    | cons q rest => exact ⟨.drain c, _, rfl, WStep.drain harr⟩
  | false =>
    obtain ⟨⟨e, p'⟩, hq, hE⟩ := hconn c p hl harr
    by_cases hocc : WConfig.Occ (l₁ ++ ((c, p) :: rest) :: l₂) e
    · exact Or.inr ⟨e, p', rfl, hq, hE, hocc⟩
    · obtain ⟨⟨c'', p''⟩, hq', hfree⟩ := hsel.conserving _ c p ⟨(e, p'), hq, hocc⟩
      exact Or.inl ⟨.advance c c'' p'', _, rfl, WStep.advance harr hq' hfree⟩

/-- **Duato's theorem for wormhole switching.**  If every legal packet that has not arrived may
request an escape channel, and the extended dependency graph of the escape channels is
well-founded (acyclic), the network is deadlock free for packets of every length and every
selection function. -/
theorem wormholeDeadlockFree_of_escape {legal : C → P → Prop} {E : C → Prop}
    (hcl : N.Closed legal)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → ∃ q ∈ N.route c p, E q.1)
    (hwf : WellFounded (flip (N.ExtDep legal E))) : N.WormholeDeadlockFree := by
  intro tail sel hsel w hw hne
  obtain ⟨hh, hesc⟩ := N.winv_of_reachable (E := E) hcl hsel hw
  have hwfT : WellFounded (flip (Relation.TransGen (N.ExtDep legal E))) :=
    Subrelation.wf (fun h => Relation.transGen_swap.2 h) hwf.transGen
  have key : ∀ e, E e → w.Occ e → N.WMovable tail sel w := by
    intro e
    refine hwfT.induction (C := fun e => E e → w.Occ e → N.WMovable tail sel w) e ?_
    intro e ih he hocc
    obtain ⟨y, hy, q, hq, rfl⟩ := hocc
    obtain ⟨⟨c, p⟩, rest, rfl, hl⟩ := hh y hy
    obtain ⟨e₀, hrt, hne₀⟩ := hesc _ hy _ _ rfl q hq he
    rcases N.head_move hsel hconn hy hl with hm | ⟨e'', p'', harr, hr, hE, hocc'⟩
    · exact hm
    · exact ih e'' (Relation.TransGen.tail' hrt ⟨(c, p), hne₀, harr, p'', hr, hE⟩) hE hocc'
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil w hne
  obtain ⟨⟨c, p⟩, rest, rfl, hl⟩ := hh x hx
  rcases N.head_move hsel hconn hx hl with hm | ⟨e'', -, -, -, hE, hocc⟩
  · exact hm
  · exact key e'' hE hocc

/-- **Dally and Seitz's theorem for wormhole switching**: a connected routing function whose
channel dependency graph is well-founded (acyclic) is deadlock free. -/
theorem wormholeDeadlockFree_of_cdg {legal : C → P → Prop} (hcl : N.Closed legal)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → N.route c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal N.route))) : N.WormholeDeadlockFree := by
  refine N.wormholeDeadlockFree_of_escape (E := fun _ => True) hcl
    (fun c p hl ha => ?_) (Subrelation.wf ?_ hwf)
  · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ (hconn c p hl ha)
    exact ⟨q, hq, trivial⟩
  · rintro e e' ⟨q, hne, harr, p', hq, -⟩
    cases hne with
    | base hl _ => exact ⟨_, p', hl, harr, hq⟩
    | step _ _ _ hE => exact absurd trivial hE

/-! ### Livelock freedom -/

/-- The weight of a packet: twice the rank of its head plus its length. -/
def wwt (rk : C → P → ℕ) : Worm C P → ℕ
  | [] => 0
  | h :: rest => 2 * rk h.1 h.2 + rest.length + 3

/-- **Livelock freedom under wormhole switching**: a ranking function that decreases on every
permitted hop rules out infinite runs without injections, for packets of every length. -/
theorem wormholeLivelockFree_of_ranking {legal : C → P → Prop} (hcl : N.Closed legal)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p) :
    N.WormholeLivelockFree := by
  intro tail sel hsel
  refine LTS.LivelockFree.of_ranking (WHeads legal)
    (fun _ hx => absurd hx (List.not_mem_nil)) (fun _ _ _ hh hst => N.wheads_step hcl hsel hh hst)
    (fun w => (w.map (wwt rk)).sum) ?_
  intro w a w' hh ha hst
  change N.WStep tail sel w a w' at hst
  cases hst with
  | inject => simp [WAct.IsMove, WAct.isMove] at ha
  | @advance l₁ l₂ c c' p p' rest harr hq _ =>
    obtain ⟨h₀, r₀, he₀, hl⟩ := hh _ mem_mid
    cases he₀
    have hlt := hrk c p _ hl harr (hsel.sub _ _ _ _ hq)
    have hlen : (((c, p) :: rest).take (tail p')).length ≤ rest.length + 1 := by
      simp [List.length_take]
    simp only at hlt
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, wwt]
    omega
  | @drain l₁ l₂ c p q rest _ =>
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, wwt,
      List.length_dropLast, List.length_cons]
    omega
  | eject _ =>
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, wwt,
      List.length_nil]
    omega

/-! ### Draining -/

/-- In a deadlock-free and livelock-free network, every reachable configuration drains: all
packets can be delivered by moves only. -/
theorem wdrain {tail : P → ℕ} {sel : WSelection C P} (hD : N.WDeadlockFreeWith tail sel)
    (hL : N.WLivelockFreeWith tail sel) {w : WConfig C P}
    (hw : (N.wltsWith tail sel).Reachable [] w) :
    Relation.ReflTransGen ((N.wltsWith tail sel).IStep WAct.IsMove) w [] := by
  have hacc := LTS.LivelockFree.acc hL hw
  induction hacc with
  | intro w _ ih =>
    by_cases he : w = []
    · subst he; exact Relation.ReflTransGen.refl
    · obtain ⟨a, w', ha, hst⟩ := hD w hw he
      exact Relation.ReflTransGen.head ⟨a, ha, hst⟩ (ih w' ⟨a, ha, hst⟩ (hw.tail ⟨a, hst⟩))

variable {N} in
/-- In a correct network, for packets of every length and every valid selection, all packets
of every reachable configuration can be delivered without new injections. -/
theorem WormholeCorrect.drain (h : N.WormholeCorrect) (tail : P → ℕ) {sel : WSelection C P}
    (hsel : N.WValidSel sel) {w : WConfig C P} (hw : (N.wltsWith tail sel).Reachable [] w) :
    Relation.ReflTransGen ((N.wltsWith tail sel).IStep WAct.IsMove) w [] :=
  N.wdrain (h.1 tail sel hsel) (h.2 tail sel hsel) hw

/-! ### One-flit packets: store-and-forward switching

Packets of one flit (`tail = fun _ => 0`) behave exactly like store-and-forward packets, so
wormhole deadlock freedom (which is for packets of every length) implies store-and-forward
deadlock freedom: `deadlockFree_of_wormholeDeadlockFree`.  Every refutation of store-and-forward
deadlock freedom therefore refutes wormhole deadlock freedom too. -/

section OneFlit

variable [DecidableEq C]

/-- The wormhole configuration `w` holds exactly the packets of the store-and-forward
configuration `f`, each as a one-flit packet. -/
def OneFlit (w : WConfig C P) (f : Config C P) : Prop :=
  (∀ x ∈ w, ∃ q, x = [q]) ∧ w.Nodup ∧ ∀ c p, f c = some p ↔ [(c, p)] ∈ w

omit [DecidableEq C] in
theorem OneFlit.occ {w : WConfig C P} {f : Config C P} (h : OneFlit w f) {c : C} :
    w.Occ c ↔ f c ≠ none := by
  constructor
  · rintro ⟨x, hx, q, hq, rfl⟩
    obtain ⟨q', rfl⟩ := h.1 x hx
    rw [List.mem_singleton] at hq
    subst hq
    rw [(h.2.2 q.1 q.2).2 hx]
    simp
  · intro hn
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hn
    exact ⟨_, (h.2.2 c p).1 hp, (c, p), List.mem_singleton_self _, rfl⟩

theorem OneFlit.erase {w : WConfig C P} {f : Config C P} (h : OneFlit w f) {l₁ l₂ : WConfig C P}
    {c : C} {p : P} (hw : w = l₁ ++ [(c, p)] :: l₂) :
    (∀ x ∈ l₁ ++ l₂, ∃ q, x = [q]) ∧ (l₁ ++ l₂).Nodup ∧
      ∀ c' p', Function.update f c none c' = some p' ↔ [(c', p')] ∈ l₁ ++ l₂ := by
  subst hw
  obtain ⟨h1, h2, h3⟩ := h
  rw [List.nodup_middle, List.nodup_cons] at h2
  refine ⟨fun x hx => h1 x (List.mem_append.2 ((List.mem_append.1 hx).imp id
    (List.mem_cons_of_mem _))), h2.2, fun c' p' => ?_⟩
  by_cases hc : c' = c
  · subst hc
    simp only [Function.update_self, reduceCtorEq, false_iff]
    intro hmem
    have hp' := (h3 c' p').2 (List.mem_append.2 ((List.mem_append.1 hmem).imp id
      (List.mem_cons_of_mem _)))
    have hp := (h3 c' p).2 (by simp)
    rw [hp] at hp'
    cases hp'
    exact h2.1 hmem
  · rw [Function.update_of_ne hc, h3]
    simp only [List.mem_append, List.mem_cons, List.cons.injEq, Prod.mk.injEq, and_true]
    constructor
    · rintro (h | ⟨rfl, -⟩ | h)
      · exact Or.inl h
      · exact absurd rfl hc
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- Every store-and-forward step is a step of one-flit packets. -/
theorem oneFlit_step {f f' : Config C P} {a : Act C P} (hs : N.StepWith N.adaptive f a f')
    {w : WConfig C P} (h : OneFlit w f) :
    ∃ b w', (N.wltsWith (fun _ => 0) N.wadaptive).step w b w' ∧ OneFlit w' f' := by
  cases hs with
  | @inject c p hinj hfree =>
    refine ⟨.inject c p, [(c, p)] :: w, WStep.inject hinj fun ho => h.occ.1 ho hfree,
      fun x hx => ?_, List.nodup_cons.2 ⟨fun hm => ?_, h.2.1⟩, fun c' p' => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨_, rfl⟩
      · exact h.1 x hx
    · rw [(h.2.2 c p).2 hm] at hfree; cases hfree
    · by_cases hc : c' = c
      · subst hc
        simp only [Function.update_self, Option.some.injEq, List.mem_cons, List.cons.injEq,
          Prod.mk.injEq, true_and, and_true]
        constructor
        · rintro rfl; exact Or.inl rfl
        · rintro (rfl | hm)
          · rfl
          · rw [(h.2.2 c' p').2 hm] at hfree; cases hfree
      · rw [Function.update_of_ne hc, h.2.2]
        simp [hc]
  | @hop c c' p p' hp harr hq hfree =>
    obtain ⟨l₁, l₂, hw⟩ := List.append_of_mem ((h.2.2 c p).1 hp)
    have hne : c' ≠ c := by rintro rfl; rw [hp] at hfree; cases hfree
    obtain ⟨e1, e2, e3⟩ := h.erase hw
    refine ⟨.advance c c' p', l₁ ++ [(c', p')] :: l₂, ?_, fun x hx => ?_, ?_, fun c₀ p₀ => ?_⟩
    · show N.WStep _ _ w _ _
      have := WStep.advance (N := N) (tail := fun _ => 0) (sel := N.wadaptive) (l₁ := l₁)
        (l₂ := l₂) (rest := []) harr hq (by rw [← hw]; exact fun ho => h.occ.1 ho hfree)
      rw [← hw] at this
      simpa using this
    · rcases List.mem_append.1 hx with hx | hx
      · exact e1 x (List.mem_append.2 (Or.inl hx))
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨_, rfl⟩
        · exact e1 x (List.mem_append.2 (Or.inr hx))
    · rw [List.nodup_middle, List.nodup_cons]
      refine ⟨fun hm => ?_, e2⟩
      have := (e3 c' p').2 hm
      rw [Function.update_of_ne hne, hfree] at this
      cases this
    · by_cases hc : c₀ = c'
      · subst hc
        simp only [Function.update_self, Option.some.injEq, List.mem_append, List.mem_cons,
          List.cons.injEq, Prod.mk.injEq, true_and, and_true]
        constructor
        · rintro rfl; exact Or.inr (Or.inl rfl)
        · rintro (hm | rfl | hm)
          · have := (e3 c₀ p₀).2 (List.mem_append.2 (Or.inl hm))
            rw [Function.update_of_ne hne, hfree] at this; cases this
          · rfl
          · have := (e3 c₀ p₀).2 (List.mem_append.2 (Or.inr hm))
            rw [Function.update_of_ne hne, hfree] at this; cases this
      · rw [Function.update_of_ne hc, e3]
        simp only [List.mem_append, List.mem_cons, List.cons.injEq, Prod.mk.injEq, and_true]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | ⟨rfl, -⟩ | h)
          · exact Or.inl h
          · exact absurd rfl hc
          · exact Or.inr h
  | @eject c p hp harr =>
    obtain ⟨l₁, l₂, hw⟩ := List.append_of_mem ((h.2.2 c p).1 hp)
    refine ⟨.eject c, l₁ ++ l₂, ?_, h.erase hw⟩
    rw [hw]
    exact WStep.eject harr

theorem oneFlit_reachable {f : Config C P} (hf : N.lts.Reachable empty f) :
    ∃ w, (N.wltsWith (fun _ => 0) N.wadaptive).Reachable [] w ∧ OneFlit w f := by
  induction hf with
  | refl => exact ⟨[], LTS.Reachable.refl _, by simp, List.nodup_nil, by simp [empty]⟩
  | tail _ hst ih =>
    obtain ⟨w, hw, h⟩ := ih
    obtain ⟨a, ha⟩ := hst
    obtain ⟨b, w', hst', h'⟩ := N.oneFlit_step ha h
    exact ⟨w', hw.tail ⟨b, hst'⟩, h'⟩

/-- **Wormhole deadlock freedom implies store-and-forward deadlock freedom**: packets of one
flit behave like store-and-forward packets. -/
theorem deadlockFree_of_wormholeDeadlockFree (h : N.WormholeDeadlockFree) : N.DeadlockFree := by
  refine N.deadlockFree_iff_adaptive.2 fun f hf hne => ?_
  obtain ⟨w, hw, hof⟩ := N.oneFlit_reachable hf
  obtain ⟨c, p, hp⟩ := exists_of_ne_empty hne
  have hwne : w ≠ [] := by
    intro he
    have := (hof.2.2 c p).1 hp
    rw [he] at this
    cases this
  obtain ⟨a, w', ha, hst⟩ := h (fun _ => 0) N.wadaptive N.wadaptive_valid w hw hwne
  change N.WStep (fun _ => 0) N.wadaptive w a w' at hst
  cases hst with
  | inject => simp [WAct.IsMove, WAct.isMove] at ha
  | @advance l₁ l₂ c c' p p' rest harr hq hfree =>
    obtain ⟨q, hx⟩ := hof.1 _ (List.mem_append.2 (Or.inr (List.mem_cons_self ..)))
    simp only [List.cons.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    have hp' := (hof.2.2 c p).2 (List.mem_append.2 (Or.inr (List.mem_cons_self ..)))
    have hfree' : f c' = none := by
      by_contra hn
      exact hfree (hof.occ.2 hn)
    exact ⟨.hop c c' p', _, rfl, StepWith.hop hp' harr hq hfree'⟩
  | @drain l₁ l₂ c p q rest harr =>
    obtain ⟨q', hx⟩ := hof.1 _ (List.mem_append.2 (Or.inr (List.mem_cons_self ..)))
    simp at hx
  | @eject l₁ l₂ c p harr =>
    have hp' := (hof.2.2 c p).2 (List.mem_append.2 (Or.inr (List.mem_cons_self ..)))
    exact ⟨.eject c, _, rfl, StepWith.eject hp' harr⟩

end OneFlit

/-! ### Refutation -/

section Refute

variable [DecidableEq C] [DecidableEq P]

/-- Channel `c` is held by a packet of `w`. -/
def occB (w : WConfig C P) (c : C) : Bool := w.any fun x => x.any fun q => decide (q.1 = c)

omit [DecidableEq P] in
theorem occB_eq_false {w : WConfig C P} {c : C} : occB w c = false ↔ ¬ w.Occ c := by
  simp [occB, WConfig.Occ]

/-- Split off the packet whose head is in channel `c`. -/
def splitAt (c : C) : WConfig C P → Option (WConfig C P × Worm C P × WConfig C P)
  | [] => none
  | x :: w =>
    if (x.head?.map Prod.fst) = some c then some ([], x, w)
    else (splitAt c w).map fun r => (x :: r.1, r.2.1, r.2.2)

omit [DecidableEq P] in
theorem splitAt_spec {c : C} {w l₁ l₂ : WConfig C P} {x : Worm C P}
    (h : splitAt c w = some (l₁, x, l₂)) : w = l₁ ++ x :: l₂ := by
  induction w generalizing l₁ with
  | nil => simp [splitAt] at h
  | cons y w ih =>
    simp only [splitAt] at h
    split_ifs at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
    · obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      rw [ih hr]
      rfl

/-- Execute actions under wormhole switching (adaptive selection). -/
def wrunB (tail : P → ℕ) : WConfig C P → List (WAct C P) → Option (WConfig C P)
  | w, [] => some w
  | w, .inject c p :: as =>
    if (c, p) ∈ N.inject ∧ occB w c = false then wrunB tail ([(c, p)] :: w) as else none
  | w, .advance c c' p' :: as =>
    match splitAt c w with
    | some (l₁, (c₀, p) :: rest, l₂) =>
      if c₀ = c ∧ N.arrived c p = false ∧ (c', p') ∈ N.route c p ∧ occB w c' = false then
        wrunB tail (l₁ ++ ((c', p') :: ((c, p) :: rest).take (tail p')) :: l₂) as
      else none
    | _ => none
  | w, .drain c :: as =>
    match splitAt c w with
    | some (l₁, (c₀, p) :: q :: rest, l₂) =>
      if c₀ = c ∧ N.arrived c p = true then
        wrunB tail (l₁ ++ ((c, p) :: (q :: rest).dropLast) :: l₂) as
      else none
    | _ => none
  | w, .eject c :: as =>
    match splitAt c w with
    | some (l₁, [(c₀, p)], l₂) =>
      if c₀ = c ∧ N.arrived c p = true then wrunB tail (l₁ ++ l₂) as else none
    | _ => none

theorem wpath_of_runB {tail : P → ℕ} {w w' : WConfig C P} {as : List (WAct C P)}
    (h : N.wrunB tail w as = some w') : (N.wltsWith tail N.wadaptive).Path w as w' := by
  induction as generalizing w with
  | nil =>
    simp only [wrunB, Option.some.injEq] at h
    subst h; exact LTS.Path.nil _
  | cons a as ih =>
    cases a with
    | inject c p =>
      simp only [wrunB] at h
      split_ifs at h with hc
      exact LTS.Path.cons (WStep.inject hc.1 (occB_eq_false.1 hc.2)) (ih h)
    | advance c c' p' =>
      simp only [wrunB] at h
      split at h
      · rename_i l₁ c₀ p rest l₂ hs
        split_ifs at h with hc
        obtain ⟨rfl, harr, hq, hfree⟩ := hc
        obtain rfl := splitAt_spec hs
        exact LTS.Path.cons (WStep.advance harr hq (occB_eq_false.1 hfree)) (ih h)
      · simp at h
    | drain c =>
      simp only [wrunB] at h
      split at h
      · rename_i l₁ c₀ p q rest l₂ hs
        split_ifs at h with hc
        obtain ⟨rfl, harr⟩ := hc
        obtain rfl := splitAt_spec hs
        exact LTS.Path.cons (WStep.drain harr) (ih h)
      · simp at h
    | eject c =>
      simp only [wrunB] at h
      split at h
      · rename_i l₁ c₀ p l₂ hs
        split_ifs at h with hc
        obtain ⟨rfl, harr⟩ := hc
        obtain rfl := splitAt_spec hs
        exact LTS.Path.cons (WStep.eject harr) (ih h)
      · simp at h

/-- Every packet of `w` is blocked: its head has not arrived and every permitted hop leads to
a held channel. -/
def wstuckB (w : WConfig C P) : Bool :=
  w.all fun x => match x with
    | (c, p) :: _ => !N.arrived c p && (N.route c p).all fun q => occB w q.1
    | [] => false

/-- A run (with packets trailing `tail p` channels) from the empty network to a non-empty
configuration in which every packet is blocked. -/
def wrefuteDeadlockB (tail : P → ℕ) (as : List (WAct C P)) : Bool :=
  match N.wrunB tail [] as with
  | some w => !w.isEmpty && N.wstuckB w
  | none => false

variable {N} in
/-- **Refuting wormhole deadlock freedom** by a run, for some packet lengths `tail`, ending
with every packet blocked. -/
theorem not_wormholeDeadlockFree_of_refuteB (tail : P → ℕ) {as : List (WAct C P)}
    (h : N.wrefuteDeadlockB tail as = true) : ¬ N.WormholeDeadlockFree := by
  unfold wrefuteDeadlockB at h
  split at h
  · rename_i w hrun
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
    obtain ⟨hne, hstuck⟩ := h
    intro hD
    obtain ⟨a, w', ha, hst⟩ :=
      hD tail _ N.wadaptive_valid w (N.wpath_of_runB hrun).reachable hne
    have key : ∀ c p rest, (c, p) :: rest ∈ w →
        N.arrived c p = false ∧ ∀ q ∈ N.route c p, w.Occ q.1 := by
      intro c p rest hx
      have := (List.all_eq_true.1 hstuck) _ hx
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at this
      exact ⟨this.1, fun q hq => by
        have := this.2 q hq
        by_contra hc
        rw [← occB_eq_false] at hc
        simp [hc] at this⟩
    change N.WStep tail N.wadaptive w a w' at hst
    cases hst with
    | inject => simp [WAct.IsMove, WAct.isMove] at ha
    | advance _ hq hfree => exact hfree ((key _ _ _ mem_mid).2 _ hq)
    | drain harr => simp [(key _ _ _ mem_mid).1] at harr
    | eject harr => simp [(key _ _ _ mem_mid).1] at harr
  · simp at h

/-- A run `pre` from the empty network, then a non-empty cycle `cyc` of moves back to the same
configuration. -/
def wrefuteLivelockB (tail : P → ℕ) (pre cyc : List (WAct C P)) : Bool :=
  !cyc.isEmpty && cyc.all WAct.isMove &&
    match N.wrunB tail [] pre with
    | some w => decide (N.wrunB tail w cyc = some w)
    | none => false

variable {N} in
/-- **Refuting wormhole livelock freedom** by a cycle of moves, for some packet lengths. -/
theorem not_wormholeLivelockFree_of_refuteB (tail : P → ℕ) {pre cyc : List (WAct C P)}
    (h : N.wrefuteLivelockB tail pre cyc = true) : ¬ N.WormholeLivelockFree := by
  unfold wrefuteLivelockB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨hne, hmv⟩, h⟩ := h
  split at h
  · rename_i w hpre
    intro hL
    exact LTS.not_livelockFree_of_cycle (N.wpath_of_runB hpre).reachable
      ((N.wpath_of_runB (of_decide_eq_true h)).iStep_transGen
        (fun a ha => (List.all_eq_true.1 hmv) a ha) hne)
      (hL tail _ N.wadaptive_valid)
  · simp at h

end Refute

end Network

end AsyncLean
