/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Source

/-!
# Delivery under saturation: channel fairness

The starvation-freedom theorems of `AsyncLean.Routing.Fairness` and `AsyncLean.Routing.Source`
assume a **strongly fair** run (`LTS.Run.StronglyFair`): every transition `s —l→ s'` whose source
state recurs infinitely often is taken infinitely often.  In a finite deadlock- and livelock-free
network this makes the run revisit *every* reachable configuration infinitely often, the empty
network included, so those theorems say nothing about a network that is kept loaded.

This file replaces state-based fairness by fairness of the individual channels, and proves that
every packet is delivered **even if injection never stops**.

## Channel fairness

`LTS.Run.StronglyFairFor r E` is strong fairness for a *set of labels* `E`: if infinitely often
some label of `E` is enabled, a label of `E` is taken infinitely often.  A run of a network is
**channel fair** (`Network.ChannelFair`) when, for every channel `c`, it is strongly fair for the
set of actions that move the packet out of `c` (the hops `hop c _ _` and the ejection
`eject c`, i.e. `Network.Leaves c`): a channel whose packet is offered a way out infinitely often
(by the selection function, into a free channel, or because it has arrived) does get its packet
out.  This is the guarantee of a fair (for example round-robin) arbiter at each router output; it
mentions neither configurations nor injections.  Injections are unconstrained: they may happen at
every step.

Channel fairness does not make the network drain.  A run in which every channel that holds a
packet sees a departure infinitely often is channel fair whatever its injections, so the
network may stay loaded forever: `Network.Saturated.run` is a channel-fair run of a two-channel
network that injects infinitely often and never returns to the empty network, and it is *not*
strongly fair (`Network.Saturated.not_stronglyFair`).  Conversely, with finitely many reachable
configurations every strongly fair run is channel fair (`LTS.Run.stronglyFairFor_of_stronglyFair`),
so the theorems below strengthen the earlier ones.

## Main results

* `Network.leaves_free` : a step that moves the packet out of `c` leaves `c` free.
* `Network.exists_leave_of_channelFair` : with a closed legal set, a connected escape subfunction
  `R₁` with a well-founded dependency graph, no escape hop into a source channel, and a selection
  satisfying Duato's condition with throttled sources (`Network.SourceSel`), every packet held in
  a channel outside the sources leaves it, along every channel-fair run.  By well-founded induction
  on the escape dependencies: the packet's escape channel is free infinitely often (it is empty, or
  its own packet leaves it), and whenever it is free the selection offers the packet a free hop.
* `Network.delivered_of_leave` : if every packet outside the sources leaves its channel, no hop
  leads into a source and a ranking function decreases on every hop, every packet outside the
  sources is delivered (`Network.Delivered`).
* `Network.StarvationFreeUnderLoad sel src` : along every channel-fair run of `N` under `sel`,
  with arbitrary injections, every packet held in a channel outside `src` is delivered.
* `Network.starvationFreeUnderLoad_of_source` : Duato's condition with throttled sources, a ranking
  function and no hop into a source give `StarvationFreeUnderLoad sel src`.  No finiteness is
  needed.
* `Network.starvationFreeUnderLoad_of_escape` : under a selection that never refuses a free
  escape hop (`Network.EscapeSel`), *every* packet is delivered (`src` is empty).
* `Network.starvationFreeWith_of_underLoad` : with finitely many reachable configurations,
  `StarvationFreeUnderLoad sel (fun _ => False)` implies the earlier `StarvationFreeWith sel`.
* `Network.Saturated.run_channelFair`, `Network.Saturated.run_infOften_inject`,
  `Network.Saturated.run_ne_empty`, `Network.Saturated.not_stronglyFair` : non-vacuity and
  separation, on a two-channel network.

## What is not covered

Packets held in a **throttling source** (a channel of `src` under `SourceSel`) are not covered,
and genuinely may starve under saturation: `SourceSel` only obliges a source to release its
packet when every other channel is empty, which a saturated network never is, so the throttle
may stay shut for ever while channel fairness holds.  Under a selection satisfying `EscapeSel`
(no throttling) every packet is delivered.  The model has one buffer per channel and no queue
before an injection channel, so nothing is said about packets not yet injected.
-/

namespace AsyncLean

namespace LTS

namespace Run

variable {S L : Type*} {A : LTS S L} {s₀ : S}

/-- **Strong fairness for a set of labels** `E`: if infinitely often some label of `E` is
enabled, then infinitely often a label of `E` is taken. -/
def StronglyFairFor (r : A.Run s₀) (E : L → Prop) : Prop :=
  InfOften (fun n => ∃ l s', E l ∧ A.step (r.st n) l s') → InfOften (fun n => E (r.lab n))

/-- With finitely many reachable states, strong fairness over transitions implies strong
fairness for every set of labels: some state at which a label of `E` is enabled recurs
infinitely often, and the transition it enables is then taken infinitely often. -/
theorem stronglyFairFor_of_stronglyFair {r : A.Run s₀} (hfin : {s | A.Reachable s₀ s}.Finite)
    (hfair : r.StronglyFair) (E : L → Prop) : r.StronglyFairFor E := by
  intro hen
  choose φ hφ using hen
  have := hfin.to_subtype
  let f : ℕ → {s | A.Reachable s₀ s} := fun k => ⟨r.st (φ k), r.reachable _⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  have hrec : ∀ N, ∃ k, N ≤ k ∧ f k = y := by
    intro N
    by_contra hc
    push Not at hc
    exact hinf ((Set.finite_lt_nat N).subset fun k hk => Nat.lt_of_not_le fun h => hc k h hk)
  obtain ⟨k₀, -, hk₀⟩ := hrec 0
  obtain ⟨-, l, s', hl, hst⟩ := hφ k₀
  have hy₀ : r.st (φ k₀) = y.1 := by rw [← hk₀]
  have hvis : InfOften (fun n => r.st n = y.1) := by
    intro N
    obtain ⟨k, hk, hfk⟩ := hrec N
    exact ⟨φ k, le_trans hk (hφ k).1, by rw [← hfk]⟩
  intro N
  obtain ⟨n, hn, -, hlab, -⟩ := hfair y.1 l s' hvis (hy₀ ▸ hst) N
  exact ⟨n, hn, show E (r.lab n) by rw [hlab]; exact hl⟩

end Run

end LTS

namespace Network

variable {C P : Type*} [DecidableEq C] {N : Network C P}

/-- A run is **channel fair** when, for every channel `c`, it is strongly fair for the actions
that move the packet out of `c` (a hop out of `c` or the ejection from `c`): if one of them is
enabled infinitely often, one of them is taken infinitely often.  Injections are unconstrained. -/
def ChannelFair {sel : Selection C P} (r : (N.ltsWith sel).Run empty) : Prop :=
  ∀ c, r.StronglyFairFor (Leaves c)

/-- With finitely many reachable configurations, every strongly fair run is channel fair. -/
theorem channelFair_of_stronglyFair {sel : Selection C P} {r : (N.ltsWith sel).Run empty}
    (hfin : {f | (N.ltsWith sel).Reachable empty f}.Finite) (hfair : r.StronglyFair) :
    ChannelFair r :=
  fun c => LTS.Run.stronglyFairFor_of_stronglyFair hfin hfair (Leaves c)

/-- A step that moves the packet out of `c` leaves `c` free. -/
theorem leaves_free {sel : Selection C P} {f f' : Config C P} {a : Act C P} {c : C}
    (hst : N.StepWith sel f a f') (ha : Leaves c a) : f' c = none := by
  cases hst with
  | inject => exact ha.elim
  | @hop c₁ c₂ _ _ hp _ _ hfree =>
    change c₁ = c at ha
    subst ha
    have : c₁ ≠ c₂ := by rintro rfl; simp [hp] at hfree
    rw [Function.update_of_ne this, Function.update_self]
  | eject =>
    change _ = c at ha
    subst ha
    exact Function.update_self _ _ _

/-- A packet that never leaves `c` after time `n` stays in `c`. -/
theorem stay_of_not_leave {sel : Selection C P} (r : (N.ltsWith sel).Run empty) {n : ℕ} {c : C}
    {p : P} (hp : r.st n c = some p) (hne : ∀ m, n ≤ m → ¬ Leaves c (r.lab m)) :
    ∀ m, n ≤ m → r.st m c = some p := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction d with
  | zero => exact hp
  | succ d ih => exact stay_of_step (r.step (n + d)) (ih (by omega)) (hne _ (by omega))

/-- **No packet waits for ever, under load.**  Let `legal` be closed, `R₁` a connected escape
subfunction with a well-founded dependency graph and no escape hop into a source channel, and let
the selection satisfy Duato's condition with throttled sources.  Along every channel-fair run,
whatever the injections, every packet held in a channel outside the sources leaves it.

By well-founded induction on the escape dependencies.  Suppose the packet `p` stays in `c` from
time `n` on.  If it has arrived, its ejection is enabled at every step.  Otherwise its escape
channel `c'` (outside the sources) is free infinitely often: at any time it is empty, or the
packet it holds leaves it (induction hypothesis), which frees it.  Whenever `c'` is free, the
selection offers `p` a free hop.  Either way a hop out of `c` or the ejection from `c` is enabled
infinitely often, so channel fairness makes `p` leave, a contradiction. -/
theorem exists_leave_of_channelFair {legal : C → P → Prop} (hcl : N.Closed legal)
    {R₁ : C → P → List (C × P)} {src : C → Prop} {sel : Selection C P}
    (hsel : N.SourceSel R₁ src sel)
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (r : (N.ltsWith sel).Run empty) (hfair : ChannelFair r) :
    ∀ c, ¬ src c → ∀ n p, r.st n c = some p → ∃ m, n ≤ m ∧ Leaves c (r.lab m) := by
  intro c
  refine hwf.induction (C := fun c => ¬ src c → ∀ n p, r.st n c = some p →
    ∃ m, n ≤ m ∧ Leaves c (r.lab m)) c ?_
  intro c ih hsc n p hp
  by_contra hne
  push Not at hne
  have hstay := stay_of_not_leave r hp hne
  suffices hen : LTS.InfOften (fun m => ∃ a f', Leaves c a ∧ (N.ltsWith sel).step (r.st m) a f') by
    obtain ⟨m, hm, hl⟩ := hfair c hen n
    exact hne m hm hl
  have hl : legal c p := N.legal_of_reachable_sub hcl hsel.sub (r.reachable n) c p hp
  cases harr : N.arrived c p with
  | true =>
    intro M
    exact ⟨max M n, le_max_left _ _, .eject c, _, rfl,
      StepWith.eject (hstay _ (le_max_right _ _)) harr⟩
  | false =>
    obtain ⟨⟨c', p'⟩, hq⟩ := List.exists_mem_of_ne_nil _ (hconn c p hl harr)
    have hsc' : ¬ src c' := hR₁ c p _ hl harr hq
    have hfree : ∀ M, ∃ m, M ≤ m ∧ n ≤ m ∧ r.st m c' = none := by
      intro M
      cases h' : r.st (max M n) c' with
      | none => exact ⟨max M n, le_max_left _ _, le_max_right _ _, h'⟩
      | some p'' =>
        obtain ⟨m, hm, hlm⟩ := ih c' ⟨p, p', hl, harr, hq⟩ hsc' _ p'' h'
        exact ⟨m + 1, by omega, by omega, leaves_free (r.step m) hlm⟩
    intro M
    obtain ⟨m, hMm, hnm, hm⟩ := hfree M
    have hpm := hstay m hnm
    obtain ⟨⟨c'', p''⟩, hq', hfree'⟩ := hsel.conserving (r.st m) c p hsc hpm ⟨(c', p'), hq, hm⟩
    exact ⟨m, hMm, .hop c c'' p'', _, rfl, StepWith.hop hpm harr hq' hfree'⟩

variable (N) in
/-- **Delivery from departures and a ranking.**  If every packet held in a channel outside `src`
eventually leaves it, no hop leads into `src`, and a ranking function decreases on every hop, then
every packet held in a channel outside `src` is eventually delivered. -/
theorem delivered_of_leave_rank {legal : C → P → Prop} (hcl : N.Closed legal) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {src : C → Prop}
    (hsrc : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → ¬ src q.1)
    {sel : Selection C P} (hsub : ∀ f c p q, q ∈ sel f c p → q ∈ N.route c p)
    (r : (N.ltsWith sel).Run empty)
    (hleave : ∀ c, ¬ src c → ∀ n p, r.st n c = some p → ∃ m, n ≤ m ∧ Leaves c (r.lab m)) :
    ∀ n c p, ¬ src c → r.st n c = some p → N.Delivered r n c := by
  suffices key : ∀ k n c p, rk c p = k → ¬ src c → r.st n c = some p → N.Delivered r n c from
    fun n c p hs hp => key _ n c p rfl hs hp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n c p hk hs hp
    have hex := hleave c hs n p hp
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
    refine N.delivered_of_leave r d n (fun k hk hk' => hbefore k hk (by omega)) ?_
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
        have hl := N.legal_of_reachable_sub hcl hsub (r.reachable m) c _ hpm
        have hq' := hsub _ _ _ _ hq
        refine ih _ (hk ▸ hrk c _ (c', p') hl harr hq') (m + 1) c' p' rfl
          (hsrc c _ (c', p') hl harr hq') ?_
        rw [hs']
        simp

variable (N) in
/-- **Starvation freedom under load**: along every channel-fair run of `N` under `sel` — with
arbitrary injections, which may never stop — every packet held in a channel outside `src` is
eventually delivered.  With `src = fun _ => False`, every packet is. -/
def StarvationFreeUnderLoad (sel : Selection C P) (src : C → Prop) : Prop :=
  ∀ r : (N.ltsWith sel).Run empty, ChannelFair r →
    ∀ n c, ¬ src c → r.st n c ≠ none → N.Delivered r n c

variable (N) in
/-- **Delivery under saturation, with throttled sources.**  With a closed legal set, a connected
escape subfunction `R₁` whose dependency graph is well-founded and which never leads into a
source, no hop at all into a source, a ranking function that decreases on every hop, and a
selection satisfying Duato's condition with throttled sources, every packet outside the sources
is delivered along every channel-fair run, however many packets are injected meanwhile.  No
finiteness is assumed.  Packets held back in a source are not covered (see the module
docstring). -/
theorem starvationFreeUnderLoad_of_source {legal : C → P → Prop} (hcl : N.Closed legal)
    (R₁ : C → P → List (C × P)) {src : C → Prop}
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁)))
    (hR₁ : ∀ c p q, legal c p → N.arrived c p = false → q ∈ R₁ c p → ¬ src q.1)
    (hsrc : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → ¬ src q.1)
    (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {sel : Selection C P} (hsel : N.SourceSel R₁ src sel) : N.StarvationFreeUnderLoad sel src := by
  intro r hfair n c hs hc
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hc
  exact N.delivered_of_leave_rank hcl rk hrk hsrc hsel.sub r
    (exists_leave_of_channelFair hcl hsel hconn hwf hR₁ r hfair) n c p hs hp

variable (N) in
/-- **Delivery under saturation (Duato's condition).**  With a closed legal set, a connected
escape subfunction `R₁` with a well-founded dependency graph, a ranking function that decreases
on every hop, and a selection that never refuses a free escape hop, *every* packet is delivered
along every channel-fair run, with injections going on for ever. -/
theorem starvationFreeUnderLoad_of_escape {legal : C → P → Prop} (hcl : N.Closed legal)
    (R₁ : C → P → List (C × P))
    (hconn : ∀ c p, legal c p → N.arrived c p = false → R₁ c p ≠ [])
    (hwf : WellFounded (flip (N.Dep legal R₁))) (rk : C → P → ℕ)
    (hrk : ∀ c p q, legal c p → N.arrived c p = false → q ∈ N.route c p → rk q.1 q.2 < rk c p)
    {sel : Selection C P} (hsel : N.EscapeSel R₁ sel) :
    N.StarvationFreeUnderLoad sel (fun _ => False) :=
  N.starvationFreeUnderLoad_of_source hcl R₁ hconn hwf (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ h => h) rk hrk (EscapeSel.sourceSel N hsel _)

/-- **The new guarantee is stronger**: with finitely many reachable configurations, delivery of
every packet along channel-fair runs implies delivery along strongly fair runs. -/
theorem starvationFreeWith_of_underLoad {sel : Selection C P}
    (hfin : {f | (N.ltsWith sel).Reachable empty f}.Finite)
    (h : N.StarvationFreeUnderLoad sel (fun _ => False)) : N.StarvationFreeWith sel :=
  fun r hfair n c hc => h r (channelFair_of_stronglyFair hfin hfair) n c not_false hc

/-! ### Non-vacuity: a saturated channel-fair run

A source channel `false` feeding an output channel `true`, where packets arrive.  The run
injects, forwards, injects, ejects, forwards, injects, ejects, … : after the first step the
network is never empty again, and it injects infinitely often.  Both channels see a departure
infinitely often, so the run is channel fair; but the configuration with one packet in the
output channel recurs while the ejection leading to the empty network is never taken from it,
so the run is not strongly fair. -/

namespace Saturated

/-- The two-channel network: inject into `false`, forward to `true`, eject from `true`. -/
def net : Network Bool Unit where
  arrived c _ := c
  route c _ := if c then [] else [(true, ())]
  inject := [(false, ())]

/-- One packet in the source channel. -/
def cfgA : Config Bool Unit := fun c => if c then none else some ()

/-- One packet in the output channel. -/
def cfgB : Config Bool Unit := fun c => if c then some () else none

/-- Both channels full. -/
def cfgAB : Config Bool Unit := fun _ => some ()

/-- The configurations of the run: empty, then `A, B, AB` periodically. -/
def st (n : ℕ) : Config Bool Unit :=
  if n = 0 then empty else if n % 3 = 1 then cfgA else if n % 3 = 2 then cfgB else cfgAB

/-- The actions of the run: inject, then `hop, inject, eject` periodically. -/
def lab (n : ℕ) : Act Bool Unit :=
  if n = 0 then .inject false () else if n % 3 = 1 then .hop false true ()
  else if n % 3 = 2 then .inject false () else .eject true

/-- The configurations are equal when they agree on both channels. -/
theorem cfg_ext {f g : Config Bool Unit} (h0 : f false = g false) (h1 : f true = g true) :
    f = g := by
  funext b; cases b <;> assumption

/-- Each step of the saturated run is a step of the network. -/
theorem step (n : ℕ) : (net.ltsWith net.adaptive).step (st n) (lab n) (st (n + 1)) := by
  change net.StepWith net.adaptive _ _ _
  by_cases h0 : n = 0
  · subst h0
    have e : Function.update empty false (some ()) = cfgA := cfg_ext rfl rfl
    rw [show st 0 = empty from rfl, show st (0 + 1) = cfgA from rfl,
      show lab 0 = .inject false () from rfl, ← e]
    exact StepWith.inject (by simp [net]) rfl
  · have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h3 with h | h | h
    · have e1 : st n = cfgAB := by simp [st, h0, h]
      have e2 : st (n + 1) = cfgA := by simp [st, show (n + 1) % 3 = 1 by omega]
      have e3 : lab n = .eject true := by simp [lab, h0, h]
      have e : Function.update cfgAB true none = cfgA := cfg_ext rfl rfl
      rw [e1, e2, e3, ← e]
      exact StepWith.eject rfl rfl
    · have e1 : st n = cfgA := by simp [st, h0, h]
      have e2 : st (n + 1) = cfgB := by
        simp [st, show (n + 1) % 3 = 2 by omega]
      have e3 : lab n = .hop false true () := by simp [lab, h0, h]
      have e : Function.update (Function.update cfgA false none) true (some ()) = cfgB :=
        cfg_ext rfl rfl
      rw [e1, e2, e3, ← e]
      exact StepWith.hop (p := ()) rfl rfl (by simp [adaptive, net]) rfl
    · have e1 : st n = cfgB := by simp [st, h0, h]
      have e2 : st (n + 1) = cfgAB := by
        simp [st, show (n + 1) % 3 = 0 by omega]
      have e3 : lab n = .inject false () := by simp [lab, h0, h]
      have e : Function.update cfgB false (some ()) = cfgAB := cfg_ext rfl rfl
      rw [e1, e2, e3, ← e]
      exact StepWith.inject (by simp [net]) rfl

/-- The saturated run. -/
def run : (net.ltsWith net.adaptive).Run empty where
  st := st
  lab := lab
  start := rfl
  step := step

/-- Every channel sees a departure infinitely often. -/
theorem run_leaves (c : Bool) : LTS.InfOften (fun n => Leaves c (run.lab n)) := by
  intro N
  cases c
  · refine ⟨3 * N + 1, by omega, ?_⟩
    simp [run, lab, show (3 * N + 1) % 3 = 1 by omega, Leaves]
  · refine ⟨3 * N + 3, by omega, ?_⟩
    simp [run, lab, show (3 * N + 3) % 3 = 0 by omega, Leaves]

/-- **The saturated run is channel fair.** -/
theorem run_channelFair : ChannelFair run := fun c _ => run_leaves c

/-- **The saturated run injects infinitely often.** -/
theorem run_infOften_inject : LTS.InfOften (fun n => run.lab n = .inject false ()) := by
  intro N
  refine ⟨3 * N + 2, by omega, ?_⟩
  simp [run, lab, show (3 * N + 2) % 3 = 2 by omega]

/-- **The saturated run never returns to the empty network.** -/
theorem run_ne_empty (n : ℕ) (hn : 0 < n) : run.st n ≠ empty := by
  intro h
  have := congrFun h true
  have h' := congrFun h false
  simp only [run, st, show n ≠ 0 by omega, ↓reduceIte, empty] at this h'
  split_ifs at this h' <;> simp_all [cfgA, cfgB, cfgAB]

/-- **The saturated run is not strongly fair**: the configuration with one packet in the output
channel recurs, but the ejection from it to the empty network is never taken. -/
theorem not_stronglyFair : ¬ run.StronglyFair := by
  intro hfair
  have hvis : LTS.InfOften (fun n => run.st n = cfgB) := by
    intro N
    refine ⟨3 * N + 2, by omega, ?_⟩
    simp [run, st, show (3 * N + 2) % 3 = 2 by omega]
  have hst : (net.ltsWith net.adaptive).step cfgB (.eject true) empty := by
    have e : Function.update cfgB true none = empty := cfg_ext rfl rfl
    rw [← e]
    exact StepWith.eject (p := ()) rfl rfl
  obtain ⟨n, -, -, -, h⟩ := hfair _ _ _ hvis hst 0
  exact run_ne_empty (n + 1) (by omega) h

/-- **Delivery under saturation, concretely**: on the saturated run every packet is delivered,
although the network is never empty again (an instance of
`Network.starvationFreeUnderLoad_of_escape`). -/
theorem run_delivered (n : ℕ) (c : Bool) (hc : run.st n c ≠ none) : net.Delivered run n c :=
  net.starvationFreeUnderLoad_of_escape (legal := fun _ _ => True) ⟨fun _ _ => trivial,
    fun _ _ _ _ _ _ => trivial⟩ net.route (fun c _ _ h => by cases c <;> simp_all [net])
    (Network.wf_of_rank (fun c => if c then 0 else 1) fun c c' ⟨_, _, _, ha, hq⟩ => by
      cases c <;> simp_all [net])
    (fun c _ => if c then 0 else 1) (fun c _ q _ ha hq => by cases c <;> simp_all [net])
    (ValidSel.escapeSel net net.adaptive_valid fun _ _ _ h => h) run run_channelFair n c
    not_false hc

end Saturated

end Network

end AsyncLean
