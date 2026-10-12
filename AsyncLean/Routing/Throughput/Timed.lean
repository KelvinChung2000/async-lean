/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Lanes
import AsyncLean.Flow.Backpressure

/-!
# Packet networks in time, part 1: placements, timed runs and the ceiling

A placement (`Network.Placement`) puts a packet network on a graph; a timed run
(`Network.TimedRun`) runs it in rounds in which every channel receives at most one packet.  The
potential accounting (`TimedRun.injected_le`) gives the ceiling: a timed run sustaining
`ρ * dem` respects every bound of the fluid network of its placement, under any selection
(`TimedRun.ceiling`, `cut_ceiling`, `hop_ceiling`).  A timed run delivers all it injects but for
what the network holds (`TimedRun.ejected_ge`).

See `AsyncLean.Routing.Throughput` for the overview.
-/

namespace AsyncLean

namespace Network

open Finset

variable {C P V : Type*}

/-- The channel a hop forwards a packet to. -/
def Act.hopTarget : Act C P → Option C
  | .hop _ c' _ => some c'
  | _ => none

/-- A **placement** of the network on the vertices `V`: where the packets in the channels are,
where the headers go, and which link each channel belongs to (`none`: no link, as for an
injection channel or a channel no hop uses).  A packet is ejected only at its destination. -/
structure Placement (N : Network C P) (V : Type*) where
  /-- The vertex a packet in the channel has reached. -/
  pos : C → V
  /-- The destination of a header. -/
  dest : P → V
  /-- The link `u → v` the channel belongs to. -/
  link : C → Option (V × V)
  /-- A packet is ejected at its destination. -/
  arrived : ∀ c p, N.arrived c p = true → pos c = dest p

variable {N : Network C P}

namespace Placement

variable (L : N.Placement V)

/-- The hops offered by `sel` follow the placement: a hop from a channel at `u` goes to a
channel of a link `u → v` and keeps the destination. -/
def Respects (sel : Selection C P) : Prop :=
  ∀ f c p q, N.arrived c p = false → q ∈ sel f c p →
    L.link q.1 = some (L.pos c, L.pos q.1) ∧ L.dest q.2 = L.dest p

/-- The placement **fits** the network: every permitted hop follows it. -/
def Fits : Prop :=
  ∀ c p q, N.arrived c p = false → q ∈ N.route c p →
    L.link q.1 = some (L.pos c, L.pos q.1) ∧ L.dest q.2 = L.dest p

/-- A placement that fits the network is respected by every selection that offers only
permitted hops. -/
theorem Fits.respects {L : N.Placement V} (h : L.Fits) {sel : Selection C P}
    (hsub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p) : L.Respects sel :=
  fun f c p q ha hq => h c p q ha (hsub f c p q hq)

/-- **Restricting a placement** to the channels satisfying `used`: the other channels lose
their link.  A selection that offers only used channels respects the restriction. -/
def restrict (used : C → Prop) [DecidablePred used] : N.Placement V where
  pos := L.pos
  dest := L.dest
  link c := if used c then L.link c else none
  arrived := L.arrived

theorem restrict_respects {L : N.Placement V} {sel : Selection C P} (h : L.Respects sel)
    {used : C → Prop} [DecidablePred used] (hused : ∀ f c p q, q ∈ sel f c p → used q.1) :
    (L.restrict used).Respects sel := by
  intro f c p q ha hq
  obtain ⟨h1, h2⟩ := h f c p q ha hq
  refine ⟨?_, h2⟩
  show (if used q.1 then L.link q.1 else none) = _
  rw [ite_eq_left (hused f c p q hq), h1]
  rfl

/-- The **fluid network of a placement**: the capacity of a link is the number of its
channels. -/
noncomputable def net [Fintype C] [DecidableEq V] : Fluid.Net V where
  cap u v := ((univ.filter fun c => L.link c = some (u, v)).card : ℚ)
  cap_nonneg _ _ := Nat.cast_nonneg _

/-- The potential of a channel's content towards its destination. -/
def cval (φ : V → V → ℚ) (c : C) (o : Option P) : ℚ := o.elim 0 fun p => φ (L.dest p) (L.pos c)

/-- The **potential of a configuration**: every packet weighs the potential of its position
towards its destination. -/
def pot [Fintype C] (φ : V → V → ℚ) (f : Config C P) : ℚ := ∑ c, L.cval φ c (f c)

/-- The weight of an action: an injection weighs the potential of its source. -/
def injW (φ : V → V → ℚ) : Act C P → ℚ
  | .inject c p => φ (L.dest p) (L.pos c)
  | _ => 0

/-- The length of the link of a channel (`0` without a link). -/
def lenOf (len : V → V → ℚ) (c : C) : ℚ := (L.link c).elim 0 fun e => len e.1 e.2

/-- The length of the link a hop uses. -/
def hopLen (len : V → V → ℚ) (a : Act C P) : ℚ := (Act.hopTarget a).elim 0 (L.lenOf len)

end Placement

section Accounting

variable [Fintype C] [DecidableEq C] (L : N.Placement V)

theorem sum_update_cval (φ : V → V → ℚ) (f : Config C P) (c₀ : C) (o : Option P) :
    L.pot φ (Function.update f c₀ o) = L.pot φ f - L.cval φ c₀ (f c₀) + L.cval φ c₀ o := by
  unfold Placement.pot
  have e : ∀ c, L.cval φ c (Function.update f c₀ o c) =
      Function.update (fun c => L.cval φ c (f c)) c₀ (L.cval φ c₀ o) c := fun c => by
    by_cases h : c = c₀
    · subst h; simp
    · simp [h]
  simp only [e]
  rw [sum_update_of_mem (mem_univ c₀), ← add_sum_erase _ _ (mem_univ c₀)]
  rw [sdiff_singleton_eq_erase]
  ring

variable {L}

/-- **One step of the accounting**: the weight of an action is at most the gain in potential
plus the length of the link it uses. -/
theorem step_injW {sel : Selection C P} (hsel : L.Respects sel)
    {φ len : V → V → ℚ} (hφd : ∀ d, φ d d = 0)
    (hφ : ∀ d c u v, L.link c = some (u, v) → φ d u - φ d v ≤ len u v)
    {f f' : Config C P} {a : Act C P} (h : (N.ltsWith sel).step f a f') :
    L.injW φ a ≤ L.pot φ f' - L.pot φ f + L.hopLen len a := by
  change N.StepWith sel f a f' at h
  cases h with
  | @inject c p _ hfree =>
    rw [sum_update_cval, hfree]
    simp [Placement.injW, Placement.hopLen, Act.hopTarget, Placement.cval]
  | @hop c c' p p' hp harr hq hfree =>
    have hcc : c' ≠ c := by rintro rfl; rw [hp] at hfree; cases hfree
    obtain ⟨hl, hd⟩ := hsel f c p (c', p') harr hq
    rw [sum_update_cval, sum_update_cval, Function.update_of_ne hcc, hfree, hp]
    simp only [Placement.injW, Placement.hopLen, Act.hopTarget, Placement.cval,
      Option.elim, Placement.lenOf]
    rw [hl]
    simp only at hd ⊢
    rw [hd]
    have := hφ (L.dest p) c' (L.pos c) (L.pos c') hl
    linarith
  | @eject c p hp harr =>
    rw [sum_update_cval, hp]
    have := L.arrived c p harr
    simp [Placement.injW, Placement.hopLen, Act.hopTarget, Placement.cval, this, hφd]

/-- **The accounting along a run**: the weight injected is at most the gain in potential plus
the lengths of the links the hops use. -/
theorem path_injW {sel : Selection C P} (hsel : L.Respects sel)
    {φ len : V → V → ℚ} (hφd : ∀ d, φ d d = 0)
    (hφ : ∀ d c u v, L.link c = some (u, v) → φ d u - φ d v ≤ len u v)
    {f f' : Config C P} {as : List (Act C P)} (h : (N.ltsWith sel).Path f as f') :
    (as.map (L.injW φ)).sum ≤ L.pot φ f' - L.pot φ f + (as.map (L.hopLen len)).sum := by
  induction h with
  | nil => simp
  | cons hst _ ih =>
    have := step_injW hsel hφd hφ hst
    simp only [List.map_cons, List.sum_cons]
    linarith

omit [Fintype C] in
/-- The lengths used by the hops of a list are the channel lengths times how often the hops
reach the channel. -/
theorem sum_hopLen [Fintype C] (len : V → V → ℚ) (as : List (Act C P)) :
    (as.map (L.hopLen len)).sum =
      ∑ c, L.lenOf len c * (as.countP fun a => a.hopTarget = some c) := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
    have e : L.hopLen len a = ∑ c, L.lenOf len c * (if a.hopTarget = some c then 1 else 0) := by
      unfold Placement.hopLen
      cases ht : a.hopTarget with
      | none => simp
      | some c₀ =>
        simp only [Option.elim, Option.some.injEq, mul_ite, mul_one, mul_zero]
        rw [sum_ite_eq]; simp
    rw [e, ← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    by_cases h : a.hopTarget = some c <;> simp [h]; ring

omit [Fintype C] in
/-- In a round in which every channel receives at most one packet, the hops use at most the
total length of the channels. -/
theorem round_hopLen [Fintype C] {len : V → V → ℚ} (hlen : ∀ u v, 0 ≤ len u v)
    {as : List (Act C P)} (h : ∀ c, (as.countP fun a => a.hopTarget = some c) ≤ 1) :
    (as.map (L.hopLen len)).sum ≤ ∑ c, L.lenOf len c := by
  rw [sum_hopLen]
  refine sum_le_sum fun c _ => ?_
  have h0 : 0 ≤ L.lenOf len c := by
    unfold Placement.lenOf; cases L.link c with
    | none => exact le_rfl
    | some e => exact hlen e.1 e.2
  have h1 : ((as.countP fun a => a.hopTarget = some c : ℕ) : ℚ) ≤ 1 := by exact_mod_cast h c
  nlinarith

end Accounting

/-- A **timed run** of the network under the selection `sel`: rounds of actions from the empty
network, every channel receiving at most one packet per round by a hop. -/
structure TimedRun [DecidableEq C] (N : Network C P) (sel : Selection C P) where
  /-- The configuration at the start of round `t`. -/
  conf : ℕ → Config C P
  /-- The actions of round `t`. -/
  acts : ℕ → List (Act C P)
  start : conf 0 = empty
  path : ∀ t, (N.ltsWith sel).Path (conf t) (acts t) (conf (t + 1))
  /-- Every channel receives at most one packet per round by a hop. -/
  once : ∀ t c, ((acts t).countP fun a => a.hopTarget = some c) ≤ 1

namespace TimedRun

variable [DecidableEq C] {sel : Selection C P} (R : N.TimedRun sel)

/-- The action injects a packet from `s` for `d`. -/
def isInj (L : N.Placement V) [DecidableEq V] (s d : V) : Act C P → Bool
  | .inject c p => decide (L.pos c = s ∧ L.dest p = d)
  | _ => false

/-- The packets injected from `s` for `d` in the first `T` rounds. -/
def injected (L : N.Placement V) [DecidableEq V] (T : ℕ) (s d : V) : ℕ :=
  ∑ t ∈ range T, (R.acts t).countP (isInj L s d)

omit [DecidableEq C] in
/-- The weight of an action is the sum over the pairs it injects. -/
theorem injW_eq (L : N.Placement V) [Fintype V] [DecidableEq V] (φ : V → V → ℚ)
    (a : Act C P) : L.injW φ a = ∑ s, ∑ d, (if isInj L s d a then φ d s else 0) := by
  cases a with
  | inject c p =>
    simp only [Placement.injW, isInj, decide_eq_true_eq]
    rw [sum_eq_single (L.pos c) (fun s _ hs => by simp [Ne.symm hs]) (by simp),
      sum_eq_single (L.dest p) (fun d _ hd => by simp [Ne.symm hd]) (by simp)]
    simp
  | hop => simp [Placement.injW, isInj]
  | eject => simp [Placement.injW, isInj]

omit [DecidableEq C] in
/-- The weight of a list of actions, pair by pair. -/
theorem sum_injW (L : N.Placement V) [Fintype V] [DecidableEq V] (φ : V → V → ℚ)
    (as : List (Act C P)) :
    (as.map (L.injW φ)).sum = ∑ s, ∑ d, ((as.countP (isInj L s d) : ℕ) : ℚ) * φ d s := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, ih, injW_eq L φ a, List.countP_cons]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun s _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    split_ifs <;> push_cast <;> ring

variable [Fintype C]

/-- **The potential accounting of a timed run.**  The packets injected in the first `T` rounds,
each weighted by the potential of its source, weigh at most `T` times the total channel length
plus `|C|` times a bound on the potential. -/
theorem injected_le (L : N.Placement V) (hsel : L.Respects sel) [Fintype V] [DecidableEq V]
    {φ len : V → V → ℚ}
    (hlen : ∀ u v, 0 ≤ len u v) (hφd : ∀ d, φ d d = 0)
    (hφ : ∀ d c u v, L.link c = some (u, v) → φ d u - φ d v ≤ len u v)
    {M : ℚ} (hM0 : 0 ≤ M) (hM : ∀ d v, φ d v ≤ M) (T : ℕ) :
    ∑ s, ∑ d, (R.injected L T s d : ℚ) * φ d s ≤
      T * ∑ c, L.lenOf len c + Fintype.card C * M := by
  have hround : ∀ t, ∑ s, ∑ d, ((R.acts t).countP (isInj L s d) : ℚ) * φ d s ≤
      L.pot φ (R.conf (t + 1)) - L.pot φ (R.conf t) + ∑ c, L.lenOf len c := fun t => by
    rw [← sum_injW]
    have h1 := path_injW (L := L) hsel hφd hφ (len := len) (R.path t)
    have h2 := round_hopLen (L := L) hlen (R.once t)
    linarith
  have hpot0 : L.pot φ (R.conf 0) = 0 := by
    simp [Placement.pot, R.start, empty, Placement.cval]
  have hpotT : L.pot φ (R.conf T) ≤ Fintype.card C * M := by
    calc L.pot φ (R.conf T) ≤ ∑ _c : C, M :=
          sum_le_sum fun c _ => by
            unfold Placement.cval
            cases R.conf T c with
            | none => simpa [Option.elim] using hM0
            | some p => exact hM _ _
      _ = Fintype.card C * M := by simp [sum_const, card_univ]
  have hsum : ∑ s, ∑ d, (R.injected L T s d : ℚ) * φ d s =
      ∑ t ∈ range T, ∑ s, ∑ d, ((R.acts t).countP (isInj L s d) : ℚ) * φ d s := by
    have e : ∀ s d, (R.injected L T s d : ℚ) * φ d s =
        ∑ t ∈ range T, ((R.acts t).countP (isInj L s d) : ℚ) * φ d s := fun s d => by
      rw [injected, Nat.cast_sum, sum_mul]
    simp only [e]
    calc ∑ s, ∑ d, ∑ t ∈ range T, ((R.acts t).countP (isInj L s d) : ℚ) * φ d s
        = ∑ s, ∑ t ∈ range T, ∑ d, ((R.acts t).countP (isInj L s d) : ℚ) * φ d s :=
          sum_congr rfl fun s _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hsum]
  calc ∑ t ∈ range T, ∑ s, ∑ d, ((R.acts t).countP (isInj L s d) : ℚ) * φ d s
      ≤ ∑ t ∈ range T, (L.pot φ (R.conf (t + 1)) - L.pot φ (R.conf t) + ∑ c, L.lenOf len c) :=
        sum_le_sum fun t _ => hround t
    _ = L.pot φ (R.conf T) - L.pot φ (R.conf 0) + T * ∑ c, L.lenOf len c := by
        rw [sum_add_distrib, sum_range_sub (fun t => L.pot φ (R.conf t)), sum_const,
          card_range, nsmul_eq_mul]
    _ ≤ T * ∑ c, L.lenOf len c + Fintype.card C * M := by linarith

omit [DecidableEq C] in
/-- The total channel length is the fluid capacity times the length. -/
theorem sum_lenOf (L : N.Placement V) [Fintype V] [DecidableEq V] (len : V → V → ℚ) :
    ∑ c, L.lenOf len c = ∑ u, ∑ v, L.net.cap u v * len u v := by
  have e : ∀ c, L.lenOf len c = ∑ u, ∑ v, (if L.link c = some (u, v) then len u v else 0) :=
    fun c => by
      unfold Placement.lenOf
      cases h : L.link c with
      | none => simp
      | some e =>
        simp only [Option.elim, Option.some.injEq]
        rw [sum_eq_single e.1 (fun u _ hu => sum_eq_zero fun v _ =>
            ite_eq_right (fun h' => hu (by rw [h']))) (by simp),
          sum_eq_single e.2 (fun v _ hv => ite_eq_right (fun h' => hv (by rw [h']))) (by simp)]
        simp
  simp only [e]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  simp only [Placement.net, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]

/-- **The packet ceiling.**  A timed run that sustains the load `ρ * dem` (at least
`T ρ dem s d - K` packets injected from `s` for `d` in the first `T` rounds, for every `T`)
respects every potential bound of the fluid network of its placement: whatever the routing and
the selection, the packet network carries no more than the fluid model allows. -/
theorem ceiling (L : N.Placement V) (hsel : L.Respects sel) [Fintype V] [DecidableEq V] {dem : V → V → ℚ} {ρ K : ℚ}
    (hload : ∀ T s d, T * ρ * dem s d - K ≤ R.injected L T s d)
    (len : V → V → ℚ) (hlen : ∀ u v, 0 ≤ len u v) (φ : V → V → ℚ) (hφd : ∀ d, φ d d = 0)
    (hφ : ∀ d u v, 0 < L.net.cap u v → φ d u - φ d v ≤ len u v)
    (hφ0 : ∀ d v, 0 ≤ φ d v) {M : ℚ} (hM : ∀ d v, φ d v ≤ M) :
    ρ * ∑ s, ∑ d, dem s d * φ d s ≤ ∑ u, ∑ v, L.net.cap u v * len u v := by
  have hφ' : ∀ d c u v, L.link c = some (u, v) → φ d u - φ d v ≤ len u v := by
    intro d c u v hc
    apply hφ d u v
    show (0 : ℚ) < ((univ.filter fun c => L.link c = some (u, v)).card : ℚ)
    exact_mod_cast card_pos.2 ⟨c, by simp [hc]⟩
  set Φ := ∑ s, ∑ d, dem s d * φ d s with hΦ
  set Kc := ∑ u, ∑ v, L.net.cap u v * len u v with hKc
  set Sφ := ∑ s, ∑ d, φ d s with hSφ
  have hSφ0 : 0 ≤ Sφ := sum_nonneg fun s _ => sum_nonneg fun d _ => hφ0 d s
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hT : ∀ T : ℕ, (T : ℚ) * (ρ * Φ) ≤ T * Kc + (Fintype.card C * max M 0 + K * Sφ) := by
    intro T
    have h1 := R.injected_le L hsel hlen hφd hφ' hM0
      (fun d v => (hM d v).trans (le_max_left _ _)) T
    rw [sum_lenOf] at h1
    have h2 : ∑ s, ∑ d, ((T : ℚ) * ρ * dem s d - K) * φ d s ≤
        ∑ s, ∑ d, (R.injected L T s d : ℚ) * φ d s :=
      sum_le_sum fun s _ => sum_le_sum fun d _ =>
        mul_le_mul_of_nonneg_right (hload T s d) (hφ0 d s)
    have h3 : ∑ s, ∑ d, ((T : ℚ) * ρ * dem s d - K) * φ d s = T * (ρ * Φ) - K * Sφ := by
      simp only [hΦ, hSφ, sub_mul, sum_sub_distrib, mul_sum]
      congr 1
      · exact sum_congr rfl fun s _ => sum_congr rfl fun d _ => by ring
    linarith
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T, hT'⟩ := Fluid.exists_nat_gt_rat
    ((Fintype.card C * max M 0 + K * Sφ) / (ρ * Φ - Kc))
  have hpos : 0 < ρ * Φ - Kc := by linarith
  have := hT T
  rw [div_lt_iff₀ hpos] at hT'
  have := mul_sub (T : ℚ) (ρ * Φ) Kc
  linarith

/-- **The cut ceiling** for packets: a timed run sustaining `ρ * dem` carries across every cut
at most the number of channels leaving it. -/
theorem cut_ceiling (L : N.Placement V) (hsel : L.Respects sel) [Fintype V] [DecidableEq V] {dem : V → V → ℚ} {ρ K : ℚ}
    (hload : ∀ T s d, T * ρ * dem s d - K ≤ R.injected L T s d)
    (S : V → Prop) [DecidablePred S] :
    ρ * ∑ s, ∑ d, (if S s ∧ ¬ S d then dem s d else 0) ≤
      ∑ u, ∑ v, if S u ∧ ¬ S v then L.net.cap u v else 0 := by
  have key := R.ceiling L hsel hload (fun u v => if S u ∧ ¬ S v then 1 else 0)
    (fun u v => by split_ifs <;> norm_num)
    (fun d v => if S v ∧ ¬ S d then 1 else 0) (fun d => by simp)
    (fun _ u v _ => by
      by_cases hu : S u <;> by_cases hv : S v <;> split_ifs <;> simp_all)
    (fun d v => by split_ifs <;> norm_num) (M := 1) (fun d v => by split_ifs <;> norm_num)
  have e1 : ∑ s, ∑ d, dem s d * (if S s ∧ ¬ S d then (1 : ℚ) else 0) =
      ∑ s, ∑ d, (if S s ∧ ¬ S d then dem s d else 0) :=
    sum_congr rfl fun s _ => sum_congr rfl fun d _ => by split_ifs <;> simp
  have e2 : ∑ u, ∑ v, L.net.cap u v * (if S u ∧ ¬ S v then (1 : ℚ) else 0) =
      ∑ u, ∑ v, (if S u ∧ ¬ S v then L.net.cap u v else 0) :=
    sum_congr rfl fun u _ => sum_congr rfl fun v _ => by split_ifs <;> simp
  rw [e1, e2] at key
  exact key

/-- **The hop ceiling** for packets: a timed run sustaining `ρ * dem` has
`ρ * ∑ s d, dem s d * dist s d ≤ ∑ u v, cap u v` for every nonnegative hop distance of the
fluid network of its placement. -/
theorem hop_ceiling (L : N.Placement V) (hsel : L.Respects sel) [Fintype V] [DecidableEq V] {dem : V → V → ℚ} {ρ K : ℚ}
    (hload : ∀ T s d, T * ρ * dem s d - K ≤ R.injected L T s d)
    {dist : V → V → ℚ} (hd : Fluid.IsHopDistance L.net dist) (hd0 : ∀ u v, 0 ≤ dist u v) :
    ρ * Fluid.hopDemand dem dist ≤ ∑ u, ∑ v, L.net.cap u v := by
  have hM : ∀ d v, dist v d ≤ ∑ a, ∑ b, dist a b := fun d v =>
    (single_le_sum (f := fun b => dist v b) (fun b _ => hd0 v b) (mem_univ d)).trans
      (single_le_sum (f := fun a => ∑ b, dist a b) (fun a _ => sum_nonneg fun b _ => hd0 a b)
        (mem_univ v))
  have := R.ceiling L hsel hload (fun _ _ => 1) (fun _ _ => zero_le_one)
    (fun d v => dist v d) hd.1 (fun d u v hc => hd.2 u v d hc) (fun d v => hd0 v d) hM
  simpa [Fluid.hopDemand] using this

end TimedRun


/-! ### Delivery -/

namespace TimedRun

variable [DecidableEq C] [Fintype C] {sel : Selection C P} (R : N.TimedRun sel)

/-- The number of occupied channels. -/
noncomputable def occ (f : Config C P) : ℕ := (univ.filter fun c => (f c).isSome).card

/-- The packets ejected (delivered) in the first `T` rounds. -/
def ejected (T : ℕ) : ℕ := ∑ t ∈ range T, (R.acts t).countP Act.isEject

/-- An action injects a packet. -/
def Act.isInject : Act C P → Bool
  | .inject _ _ => true
  | _ => false

/-- The packets injected in the first `T` rounds. -/
def injectedAll (T : ℕ) : ℕ := ∑ t ∈ range T, (R.acts t).countP Act.isInject

omit [Fintype C] in
theorem occ_update [Fintype C] (f : Config C P) (c : C) (o : Option P) :
    (occ (Function.update f c o) : ℤ) =
      occ f - (if (f c).isSome then 1 else 0) + (if o.isSome then 1 else 0) := by
  unfold occ
  have e : ∀ g : Config C P, ((univ.filter fun c => (g c).isSome).card : ℤ) =
      ∑ c', (if (g c').isSome then 1 else 0) := fun g => by
    rw [card_filter]; push_cast; rfl
  rw [e, e]
  have e2 : ∀ c', (if (Function.update f c o c').isSome then (1 : ℤ) else 0) =
      Function.update (fun c' => if (f c').isSome then (1 : ℤ) else 0) c
        (if o.isSome then 1 else 0) c' := fun c' => by
    by_cases h : c' = c
    · subst h; simp
    · simp [h]
  simp only [e2]
  rw [sum_update_of_mem (mem_univ c), ← add_sum_erase _ _ (mem_univ c), sdiff_singleton_eq_erase]
  ring

omit [Fintype C] in
/-- Every step changes the number of packets in the network by its injections less its
ejections. -/
theorem step_occ [Fintype C] {f f' : Config C P} {a : Act C P}
    (h : (N.ltsWith sel).step f a f') :
    (occ f' : ℤ) = occ f + (if Act.isInject a then 1 else 0) - (if a.isEject then 1 else 0) := by
  change N.StepWith sel f a f' at h
  cases h with
  | @inject c p _ hfree => rw [occ_update, hfree]; simp [Act.isInject, Network.Act.isEject]
  | @hop c c' p p' hp _ _ hfree =>
    have hcc : c' ≠ c := by rintro rfl; rw [hp] at hfree; cases hfree
    rw [occ_update, occ_update, Function.update_of_ne hcc, hfree, hp]
    simp [Act.isInject, Network.Act.isEject]
  | @eject c p hp _ => rw [occ_update, hp]; simp [Act.isInject, Network.Act.isEject]

omit [Fintype C] in
theorem path_occ [Fintype C] {f f' : Config C P} {as : List (Act C P)}
    (h : (N.ltsWith sel).Path f as f') :
    (occ f' : ℤ) = occ f + (as.countP Act.isInject : ℕ) - (as.countP Network.Act.isEject : ℕ) := by
  induction h with
  | nil => simp
  | cons hst _ ih =>
    rw [ih, step_occ hst, List.countP_cons, List.countP_cons]
    split_ifs <;> push_cast <;> ring

/-- **Everything injected is delivered, but for what the network holds**: in the first `T`
rounds at least the injected packets less the number of channels are delivered. -/
theorem ejected_ge (T : ℕ) : (R.injectedAll T : ℤ) - Fintype.card C ≤ R.ejected T := by
  have h : ∀ T, (occ (R.conf T) : ℤ) = R.injectedAll T - R.ejected T := by
    intro T
    induction T with
    | zero => simp [occ, R.start, empty, injectedAll, ejected]
    | succ T ih =>
      rw [path_occ (R.path T), ih]
      simp only [injectedAll, ejected, sum_range_succ]
      push_cast; ring
  have h1 : occ (R.conf T) ≤ Fintype.card C := card_le_univ _
  have := h T
  omega

end TimedRun

end Network

end AsyncLean
