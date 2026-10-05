/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Stg.Basic
import AsyncLean.Checker.Petri
import AsyncLean.Checker.Invariant
import AsyncLean.Circuit.Basic

/-!
# Concrete signal transition graphs and their verified analysis

`Stg` is a plain-data STG: a `PNet` whose transitions carry signal edges (the `edge` field of
`PTrans`), a list of named signals with their roles, and the initial signal values.

* `Stg.model` is its abstract meaning as a `StgModel`, so the theory of
  `AsyncLean.Stg.Basic` applies;
* `Stg.explicit` is an executable state graph on `List ℕ × List Bool`, proved bisimilar to the
  abstract one (`Stg.bisim`);
* verified checks prove `Correct`, `Consistent`, `CSC`, `OutputPersistent`, and conformance of
  a gate-level implementation (`Conformant`), from certificates computed by untrusted code;
* `Stg.implementation_correct` then concludes that the circuit, closed by the environment the
  STG prescribes, never deadlocks, never livelocks, never starves an edge, and never produces
  an output the specification forbids.
-/

namespace AsyncLean

/-- States of the executable state graph: a marking and the signal values. -/
abbrev StgState := List ℕ × List Bool

/-- A concrete signal transition graph. -/
structure Stg where
  /-- The underlying Petri net; the `edge` field of each transition is its label. -/
  net : PNet
  /-- Signal names and roles; signal `z` is the `z`-th entry. -/
  signals : List (String × SigKind)
  /-- Initial signal values. -/
  initVal : List Bool

namespace Stg

variable (N : Stg)

/-- The label of a transition. -/
def edge (t : Fin N.net.trans.length) : Option (ℕ × Bool) := (N.net.tr t).edge

/-- Number of signals. -/
def nsig : ℕ := N.signals.length

/-- The role of a signal. -/
def kindOf (z : ℕ) : SigKind := (N.signals.getD z ("", .input)).2

/-- `z` is driven by the circuit. -/
def isNonInput (z : ℕ) : Bool := !decide (N.kindOf z = .input)

/-- Dummies and internal-signal edges. -/
def isInternal (t : Fin N.net.trans.length) : Bool :=
  match N.edge t with
  | none => true
  | some (z, _) => decide (N.kindOf z = .internal)

/-- The abstract STG. -/
def model : StgModel (Fin N.net.places) (Fin N.net.trans.length) where
  net := N.net.toNet
  lab := N.edge
  nsig := N.nsig
  kind := N.kindOf
  M₀ := N.net.M₀
  v₀ := fun z => N.initVal.getD z false

/-- Well-formedness: the net is well formed, there is one initial value per signal, and every
edge refers to an existing signal. -/
def wf : Bool :=
  N.net.wf && N.initVal.length == N.nsig &&
    N.net.trans.all fun t => match t.edge with
      | none => true
      | some (z, _) => decide (z < N.nsig)

/-! ### Executable state graph -/

/-- Apply a label to list-encoded signal values. -/
def updL (v : List Bool) : Option (ℕ × Bool) → List Bool
  | none => v
  | some (z, b) => v.set z b

/-- Executable successor function. -/
def succ (s : StgState) : List (Fin N.net.trans.length × StgState) :=
  (List.finRange N.net.trans.length).filterMap fun t =>
    if PNet.enabledL s.1 (N.net.tr t).pre then
      some (t, (PNet.fireL (N.net.tr t).pre (N.net.tr t).post 0 s.1, updL s.2 (N.edge t)))
    else none

/-- The executable state graph. -/
def explicit : ExplicitLTS StgState (Fin N.net.trans.length) := ⟨N.succ⟩

/-- Encoding of abstract states. -/
def enc (s : Marking (Fin N.net.places) × Val) : StgState :=
  (N.net.enc s.1, (List.range N.nsig).map s.2)

/-- Initial state of the executable state graph. -/
def init : StgState := (N.net.init, N.initVal)

/-- The state order used by the checker. -/
def stateCmp (a b : StgState) : Ordering :=
  match lexCmp a.1 b.1 with
  | .eq => Circuit.boolLexCmp a.2 b.2
  | o => o

variable {N}

theorem wf_spec (h : N.wf = true) :
    N.net.wf = true ∧ N.initVal.length = N.nsig ∧ N.model.WellLabelled := by
  simp only [wf, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hn, hl⟩, he⟩ := h
  refine ⟨hn, hl, fun t z b hlab => ?_⟩
  have := he (N.net.tr t) (List.getElem_mem _)
  change (N.net.tr t).edge = some (z, b) at hlab
  rw [hlab] at this
  exact (by simpa using this : z < N.nsig)

theorem nonInput_iff {z : ℕ} : N.model.NonInput z ↔ N.isNonInput z = true := by
  simp [StgModel.NonInput, isNonInput, model]

theorem internal_eq : N.model.Internal = fun t => N.isInternal t = true := by
  funext t
  simp only [StgModel.Internal, model, isInternal]
  cases h : N.edge t with
  | none => simp
  | some p => obtain ⟨z, b⟩ := p; simp

theorem updL_enc (v : Val) (l : Option (ℕ × Bool)) :
    updL ((List.range N.nsig).map v) l = (List.range N.nsig).map (StgModel.upd v l) := by
  cases l with
  | none => rfl
  | some p =>
    obtain ⟨z, b⟩ := p
    apply List.ext_getElem
    · simp [updL]
    · intro i h1 h2
      simp only [updL, List.getElem_set, List.getElem_map, List.getElem_range, StgModel.upd]
      by_cases hz : z = i
      · subst hz; simp
      · simp [hz, Ne.symm hz]

theorem getD_enc_val (v : Val) (z : ℕ) :
    ((List.range N.nsig).map v).getD z false = if z < N.nsig then v z else false := by
  split_ifs with h <;> simp [List.getD_eq_getElem?_getD, h]

theorem mem_succ_enc (hwf : N.wf = true) {s : Marking (Fin N.net.places) × Val}
    {t : Fin N.net.trans.length} {x : StgState} :
    (t, x) ∈ N.succ (N.enc s) ↔ N.model.net.Enabled s.1 t ∧
      x = N.enc (N.model.net.fire s.1 t, StgModel.upd s.2 (N.model.lab t)) := by
  have hpre := ((PNet.wf_spec (wf_spec hwf).1).2 t).1
  simp only [succ, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨t', h⟩
    split_ifs at h with hen
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨(PNet.enabledL_enc_iff hpre).1 hen, ?_⟩
    simp only [enc, PNet.fireL_enc, updL_enc]
    rfl
  · rintro ⟨hen, rfl⟩
    refine ⟨t, ?_⟩
    have hen' : PNet.enabledL (N.enc s).1 (N.net.tr t).pre = true :=
      (PNet.enabledL_enc_iff hpre).2 hen
    simp only [hen', ↓reduceIte]
    simp only [enc, PNet.fireL_enc, updL_enc]
    rfl

/-- The executable state graph is bisimilar to the abstract one. -/
theorem bisim (hwf : N.wf = true) : LTS.FunBisim N.model.sg N.explicit.toLTS N.enc := by
  refine ⟨fun s t x => ?_⟩
  change (t, x) ∈ N.succ (N.enc s) ↔ _
  rw [mem_succ_enc hwf]
  constructor
  · rintro ⟨hen, rfl⟩; exact ⟨_, ⟨hen, rfl⟩, rfl⟩
  · rintro ⟨s', ⟨hen, rfl⟩, rfl⟩; exact ⟨hen, rfl⟩

theorem enc_s₀ (hwf : N.wf = true) : N.enc N.model.s₀ = N.init := by
  obtain ⟨hn, hl, -⟩ := wf_spec hwf
  simp only [enc, init, StgModel.s₀, model, PNet.enc_M₀ hn, Prod.mk.injEq, true_and]
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- Reachable abstract states are encoded by reachable executable states. -/
theorem reachable_enc (hwf : N.wf = true) {s : Marking (Fin N.net.places) × Val}
    (hs : N.model.sg.Reachable N.model.s₀ s) : N.explicit.toLTS.Reachable N.init (N.enc s) := by
  have := (bisim hwf).reachable_map hs
  rwa [enc_s₀ hwf] at this

/-! ### Enabled edges -/

variable (N) in
/-- The enabled non-input edges of a state with successors `es`, in canonical order. -/
def edgesOf (es : List (Fin N.net.trans.length × StgState)) : List (ℕ × Bool) :=
  (List.range N.nsig).flatMap fun z =>
    if N.isNonInput z then
      [false, true].filterMap fun b =>
        if es.any (fun e => decide (N.edge e.1 = some (z, b))) then some (z, b) else none
    else []

theorem mem_edgesOf {es : List (Fin N.net.trans.length × StgState)} {z : ℕ} {b : Bool} :
    (z, b) ∈ N.edgesOf es ↔
      z < N.nsig ∧ N.isNonInput z = true ∧ ∃ e ∈ es, N.edge e.1 = some (z, b) := by
  simp only [edgesOf, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨z', hz', hmem⟩
    split_ifs at hmem with hni
    · simp only [List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false] at hmem
      obtain ⟨b', -, hb'⟩ := hmem
      split_ifs at hb' with hany
      simp only [Option.some.injEq, Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      simp only [List.any_eq_true, decide_eq_true_eq] at hany
      exact ⟨hz', hni, hany⟩
    · cases hmem
  · rintro ⟨hz, hni, hany⟩
    refine ⟨z, hz, ?_⟩
    have hany' : (es.any fun e => decide (N.edge e.1 = some (z, b))) = true := by
      simpa using hany
    simp only [hni, ↓reduceIte, List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨b, by cases b <;> simp, by simp [hany']⟩

theorem enabledEdge_iff (hwf : N.wf = true) {s : Marking (Fin N.net.places) × Val} {z : ℕ}
    {b : Bool} (hni : N.model.NonInput z) :
    N.model.EnabledEdge s z b ↔ (z, b) ∈ N.edgesOf (N.succ (N.enc s)) := by
  rw [mem_edgesOf]
  constructor
  · rintro ⟨t, hen, hl⟩
    refine ⟨(wf_spec hwf).2.2 t z b hl, nonInput_iff.1 hni, (t, _), (mem_succ_enc hwf).2
      ⟨hen, rfl⟩, hl⟩
  · rintro ⟨-, -, ⟨t, x⟩, hmem, hl⟩
    exact ⟨t, ((mem_succ_enc hwf).1 hmem).1, hl⟩

/-! ### Verified checks -/

variable (N)

/-- Check a certificate for `Correct`. -/
def checkCert (c : ExplicitLTS.Cert StgState) : Bool :=
  N.wf && N.explicit.checkCert stateCmp N.isInternal (List.finRange N.net.trans.length) N.init c

/-- Consistency at one state. -/
def consNode (s : StgState) (es : List (Fin N.net.trans.length × StgState)) : Bool :=
  es.all fun e => match N.edge e.1 with
    | none => true
    | some (z, b) => decide (s.2.getD z false = !b)

/-- Complete state coding at one state, against the valuation map `vmap`. -/
def cscNode (vmap : BTree (List Bool × List (ℕ × Bool))) (s : StgState)
    (es : List (Fin N.net.trans.length × StgState)) : Bool :=
  decide (vmap.findData Circuit.boolLexCmp s.2 = some (N.edgesOf es))

/-- Output persistence at one state; `look` gives the edges enabled at other states. -/
def persistNode (s : StgState) (es : List (Fin N.net.trans.length × StgState))
    (look : StgState → Option (List (ℕ × Bool))) : Bool :=
  decide (look s = some (N.edgesOf es)) &&
    (N.edgesOf es).all fun zb => es.all fun e =>
      (match N.edge e.1 with
        | some (z', _) => decide (z' = zb.1)
        | none => false) ||
      (match look e.2 with
        | some d => decide (zb ∈ d)
        | none => false)

/-- The gate driving `z`, if any. -/
def gateOf (gates : List Gate) (z : ℕ) : Option Gate := gates.find? fun g => decide (g.out = z)

/-- Restrict a valuation to the existing signals. -/
def restrict (w : Val) : Val := fun i => if i < N.nsig then w i else false

/-- The next-state functions of a gate-level implementation (a signal without a gate keeps
its value). -/
def gateFn (gates : List Gate) : ℕ → Val → Bool := fun z w =>
  match gateOf gates z with
  | some g => g.fn.eval (N.restrict w)
  | none => N.restrict w z

/-- Executable next-state functions. -/
def gateFnL (gates : List Gate) (z : ℕ) (v : List Bool) : Bool :=
  match gateOf gates z with
  | some g => g.fn.eval (Circuit.valL v)
  | none => v.getD z false

/-- Conformance of `gates` at one state. -/
def conformNode (gates : List Gate) (s : StgState)
    (es : List (Fin N.net.trans.length × StgState)) : Bool :=
  ((List.range N.nsig).all fun z => !N.isNonInput z ||
      decide (gateFnL gates z s.2 = s.2.getD z false) ||
      es.any fun e => decide (N.edge e.1 = some (z, gateFnL gates z s.2))) &&
  (es.all fun e => match N.edge e.1 with
    | none => true
    | some (z, b) => !N.isNonInput z ||
        (decide (gateFnL gates z s.2 = b) && decide (s.2.getD z false ≠ b)))

/-- Certificates for the invariant properties: per-state enabled edges, and the map from
signal values to enabled non-input edges. -/
abbrev InvCert := ExplicitLTS.InvCert StgState (List (ℕ × Bool)) ×
  BTree (List Bool × List (ℕ × Bool))

/-- Compute the invariant certificate (untrusted). -/
def mkInvCert (fuel : ℕ := 100000) : Stg.InvCert :=
  let c := N.explicit.mkInvCert stateCmp (fun s => N.edgesOf (N.succ s)) fuel N.init
  let vmap := ((c.toListAcc []).foldl (fun (st : BStore (List Bool × List (ℕ × Bool))) x =>
    st.pushKV Circuit.boolLexCmp x.1.2 x.2.2) {}).tree.rebalance
  (c, vmap)

/-- Compute the certificate for `Correct` (untrusted). -/
def mkCert (fuel : ℕ := 100000) : ExplicitLTS.Cert StgState :=
  N.explicit.mkCert stateCmp N.isInternal (List.finRange N.net.trans.length) fuel N.init

/-- Check consistency. -/
def checkConsistent (c : Stg.InvCert) : Bool :=
  N.wf && N.explicit.checkInv stateCmp (fun s es _ => N.consNode s es) N.init c.1

/-- Check complete state coding. -/
def checkCSC (c : Stg.InvCert) : Bool :=
  N.wf && N.explicit.checkInv stateCmp (fun s es _ => N.cscNode c.2 s es) N.init c.1

/-- Check output persistence. -/
def checkOutputPersistent (c : Stg.InvCert) : Bool :=
  N.wf && N.explicit.checkInv stateCmp (fun s es look => N.persistNode s es look) N.init c.1

/-- Check conformance of a gate-level implementation. -/
def checkConformant (gates : List Gate) (c : Stg.InvCert) : Bool :=
  N.wf && N.explicit.checkInv stateCmp (fun s es _ => N.conformNode gates s es) N.init c.1

variable {N}

theorem correct_of_checkCert {c : ExplicitLTS.Cert StgState} (h : N.checkCert c = true) :
    N.model.Correct := by
  simp only [checkCert, Bool.and_eq_true] at h
  obtain ⟨hd, hl, hv⟩ := ExplicitLTS.of_checkCert (List.mem_finRange) h.2
  rw [← enc_s₀ h.1] at hd hl hv
  refine ⟨(bisim h.1).deadlockFree_iff.1 hd, ?_, (bisim h.1).live_iff.1 hv⟩
  rw [internal_eq]
  exact (bisim h.1).livelockFree_iff.1 hl

/-- A checked node predicate holds at the encoding of every reachable abstract state. -/
theorem node_of_checkInv (hwf : N.wf = true) {D : Type}
    {P : StgState → List (Fin N.net.trans.length × StgState) → (StgState → Option D) → Bool}
    {c : ExplicitLTS.InvCert StgState D} (h : N.explicit.checkInv stateCmp P N.init c = true)
    {s : Marking (Fin N.net.places) × Val} (hs : N.model.sg.Reachable N.model.s₀ s) :
    P (N.enc s) (N.succ (N.enc s)) (c.look stateCmp) = true :=
  ExplicitLTS.of_checkInv h _ (reachable_enc hwf hs)

theorem consistent_of_check {c : Stg.InvCert} (h : N.checkConsistent c = true) :
    N.model.Consistent := by
  simp only [checkConsistent, Bool.and_eq_true] at h
  intro s hs t z b hen hl
  have := node_of_checkInv h.1 h.2 hs
  simp only [consNode, List.all_eq_true] at this
  have h' := this _ ((mem_succ_enc h.1).2 ⟨hen, rfl⟩)
  change (match N.edge t with | none => true | some (z, b) => _) = true at h'
  rw [show N.edge t = some (z, b) from hl] at h'
  simp only [decide_eq_true_eq] at h'
  have hz : z < N.nsig := (wf_spec h.1).2.2 t z b hl
  simp only [enc, getD_enc_val, hz, ↓reduceIte] at h'
  exact h'

theorem csc_of_check {c : Stg.InvCert} (h : N.checkCSC c = true) : N.model.CSC := by
  simp only [checkCSC, Bool.and_eq_true] at h
  intro s₁ s₂ h₁ h₂ hv z b hni
  have n₁ := node_of_checkInv h.1 h.2 h₁
  have n₂ := node_of_checkInv h.1 h.2 h₂
  simp only [cscNode, decide_eq_true_eq] at n₁ n₂
  have henc : (N.enc s₁).2 = (N.enc s₂).2 := by simp [enc, hv]
  rw [henc, n₂, Option.some.injEq] at n₁
  rw [enabledEdge_iff h.1 hni, enabledEdge_iff h.1 hni, n₁]

theorem outputPersistent_of_check {c : Stg.InvCert} (h : N.checkOutputPersistent c = true) :
    N.model.OutputPersistent := by
  simp only [checkOutputPersistent, Bool.and_eq_true] at h
  obtain ⟨hwf, hc⟩ := h
  intro s hs z b hni hen u s' hst hu
  have hn := node_of_checkInv hwf hc hs
  simp only [persistNode, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at hn
  obtain ⟨-, hall⟩ := hn
  have hmem := (enabledEdge_iff hwf hni).1 hen
  have hsucc : (u, N.enc s') ∈ N.succ (N.enc s) := (mem_succ_enc hwf).2 ⟨hst.1, by rw [hst.2]⟩
  rcases hall (z, b) hmem _ hsucc with hz | hlook
  · exfalso
    change (match N.edge u with | some (z', _) => decide (z' = z) | none => false) = true at hz
    cases he : N.edge u with
    | none => rw [he] at hz; cases hz
    | some p =>
      obtain ⟨z', b'⟩ := p
      rw [he] at hz
      simp only [decide_eq_true_eq] at hz
      subst hz
      exact hu b' he
  · have hs' : N.model.sg.Reachable N.model.s₀ s' := hs.tail ⟨u, hst⟩
    have hn' := node_of_checkInv hwf hc hs'
    simp only [persistNode, Bool.and_eq_true, decide_eq_true_eq] at hn'
    simp only [hn'.1, decide_eq_true_eq] at hlook
    exact (enabledEdge_iff hwf hni).2 hlook

theorem valL_enc (w : Val) : Circuit.valL ((List.range N.nsig).map w) = N.restrict w := by
  funext i
  simp only [Circuit.valL, getD_enc_val, restrict]

theorem gateFnL_enc (gates : List Gate) (z : ℕ) (w : Val) (hz : z < N.nsig) :
    gateFnL gates z ((List.range N.nsig).map w) = N.gateFn gates z w := by
  unfold gateFnL gateFn
  cases gateOf gates z with
  | some g => simp only [valL_enc]
  | none => simp only [getD_enc_val, restrict, hz, ↓reduceIte]

theorem gateFnL_enc' (gates : List Gate) {z : ℕ} (s : Marking (Fin N.net.places) × Val)
    (hz : z < N.nsig) : gateFnL gates z (N.enc s).2 = N.gateFn gates z s.2 :=
  gateFnL_enc gates z s.2 hz

theorem getD_enc' {z : ℕ} (s : Marking (Fin N.net.places) × Val) (hz : z < N.nsig) :
    (N.enc s).2.getD z false = s.2 z := by
  simp only [enc, getD_enc_val, hz, ↓reduceIte]

theorem conformant_of_check {gates : List Gate} {c : Stg.InvCert}
    (h : N.checkConformant gates c = true) : N.model.Conformant (N.gateFn gates) := by
  simp only [checkConformant, Bool.and_eq_true] at h
  obtain ⟨hwf, hc⟩ := h
  intro s hs
  have hn := node_of_checkInv hwf hc hs
  simp only [conformNode, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, List.any_eq_true] at hn
  obtain ⟨h1, h2⟩ := hn
  refine ⟨fun z hz hni hex => ?_, fun t z b hen hl hni => ?_⟩
  · have hz' : z < N.nsig := hz
    rcases h1 z hz' with ((hin | heq) | ⟨e, he, hlab⟩)
    · simp [nonInput_iff.1 hni] at hin
    · exfalso
      apply hex
      rw [gateFnL_enc' gates s hz', getD_enc' s hz'] at heq
      exact heq
    · rw [gateFnL_enc' gates s hz'] at hlab
      obtain ⟨t, x⟩ := e
      exact ⟨t, ((mem_succ_enc hwf).1 he).1, hlab⟩
  · have hz : z < N.nsig := (wf_spec hwf).2.2 t z b hl
    have h' := h2 _ ((mem_succ_enc hwf).2 ⟨hen, rfl⟩)
    change (match N.edge t with | none => true | some (z, b) => _) = true at h'
    rw [show N.edge t = some (z, b) from hl] at h'
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_true,
      decide_eq_true_eq] at h'
    rcases h' with hin | ⟨hF, hne⟩
    · simp [nonInput_iff.1 hni] at hin
    · rw [gateFnL_enc' gates s hz] at hF
      rw [getD_enc' s hz] at hne
      exact ⟨hF, hne⟩

/-- **The circuit implements the specification.**  If the gates conform to a correct STG,
the closed loop of circuit and environment never deadlocks, never livelocks and never
starves an edge, and every switching of a gate is allowed by the specification
(`StgModel.gate_switch_allowed`). -/
theorem implementation_correct {gates : List Gate} {c : Stg.InvCert}
    (hconf : N.checkConformant gates c = true) (hcorr : N.model.Correct) :
    (N.model.impl (N.gateFn gates)).DeadlockFree N.model.s₀ ∧
      (N.model.impl (N.gateFn gates)).LivelockFree N.model.Internal N.model.s₀ ∧
      (N.model.impl (N.gateFn gates)).Live N.model.s₀ :=
  (StgModel.impl_correct_iff (conformant_of_check hconf)).2 hcorr

/-! ### Verified refutations

Counterexamples are traces of transition indices from the initial state. -/

/-- Reachable executable states encode reachable abstract states. -/
theorem exists_of_reachable (hwf : N.wf = true) {x : StgState}
    (hx : N.explicit.toLTS.Reachable N.init x) :
    ∃ s, N.model.sg.Reachable N.model.s₀ s ∧ N.enc s = x := by
  rw [← enc_s₀ hwf] at hx
  exact (bisim hwf).reachable_lift hx

/-- Signals beyond the declared ones keep their initial value `false`. -/
theorem val_out_of_range (hwf : N.wf = true) {s : Marking (Fin N.net.places) × Val}
    (hs : N.model.sg.Reachable N.model.s₀ s) {z : ℕ} (hz : N.nsig ≤ z) : s.2 z = false := by
  refine hs.invariant (I := fun s => s.2 z = false) ?_ ?_
  · show N.initVal.getD z false = false
    have hl := (wf_spec hwf).2.1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (hl ▸ hz : N.initVal.length ≤ z)]
  · rintro s t s' hs' ⟨-, rfl⟩
    show StgModel.upd s.2 (N.edge t) z = false
    cases he : N.edge t with
    | none => exact hs'
    | some p =>
      obtain ⟨z', b⟩ := p
      have hz' : z' < N.nsig := (wf_spec hwf).2.2 t z' b he
      have : z ≠ z' := by omega
      simp [StgModel.upd, this, hs']

theorem val_eq_of_enc (hwf : N.wf = true) {s₁ s₂ : Marking (Fin N.net.places) × Val}
    (h₁ : N.model.sg.Reachable N.model.s₀ s₁) (h₂ : N.model.sg.Reachable N.model.s₀ s₂)
    (h : (N.enc s₁).2 = (N.enc s₂).2) : s₁.2 = s₂.2 := by
  funext z
  by_cases hz : z < N.nsig
  · have := congrArg (fun l => l.getD z false) h
    simpa [enc, getD_enc_val, hz] using this
  · rw [val_out_of_range hwf h₁ (by omega), val_out_of_range hwf h₂ (by omega)]

variable (N) in
/-- The state reached by firing the transitions with indices `ts`. -/
def run (ts : List ℕ) : Option StgState := N.explicit.runLabels N.init (N.net.toFins ts)

theorem reachable_of_run {ts : List ℕ} {x : StgState} (h : N.run ts = some x) :
    N.explicit.toLTS.Reachable N.init x :=
  (ExplicitLTS.path_of_followB h).reachable

variable (N) in
/-- Firing `ts` reaches a state enabling an edge of a signal that already has the target
value. -/
def refuteConsistent (ts : List ℕ) : Bool :=
  N.wf && match N.run ts with
    | some x => (N.succ x).any fun e => match N.edge e.1 with
      | some (z, b) => decide (x.2.getD z false = b)
      | none => false
    | none => false

theorem not_consistent_of_refute {ts : List ℕ} (h : N.refuteConsistent ts = true) :
    ¬ N.model.Consistent := by
  simp only [refuteConsistent, Bool.and_eq_true] at h
  obtain ⟨hwf, h⟩ := h
  split at h
  · rename_i x hx
    obtain ⟨s, hs, rfl⟩ := exists_of_reachable hwf (reachable_of_run hx)
    simp only [List.any_eq_true] at h
    obtain ⟨⟨t, x'⟩, hmem, hbad⟩ := h
    obtain ⟨hen, -⟩ := (mem_succ_enc hwf).1 hmem
    intro hcons
    cases he : N.edge t with
    | none => simp [he] at hbad
    | some p =>
      obtain ⟨z, b⟩ := p
      simp only [he, decide_eq_true_eq] at hbad
      have hz : z < N.nsig := (wf_spec hwf).2.2 t z b he
      have := hcons s hs t z b hen he
      rw [getD_enc' s hz] at hbad
      rw [hbad] at this
      cases b <;> simp at this
  · cases h

variable (N) in
/-- Firing `ts₁` and `ts₂` reaches states with the same signal values, where the first
enables the non-input edge `(z, b)` and the second does not. -/
def refuteCSC (ts₁ ts₂ : List ℕ) (z : ℕ) (b : Bool) : Bool :=
  N.wf && N.isNonInput z && match N.run ts₁, N.run ts₂ with
    | some x₁, some x₂ =>
      decide (x₁.2 = x₂.2) && decide ((z, b) ∈ N.edgesOf (N.succ x₁)) &&
        !decide ((z, b) ∈ N.edgesOf (N.succ x₂))
    | _, _ => false

theorem not_csc_of_refute {ts₁ ts₂ : List ℕ} {z : ℕ} {b : Bool}
    (h : N.refuteCSC ts₁ ts₂ z b = true) : ¬ N.model.CSC := by
  simp only [refuteCSC, Bool.and_eq_true] at h
  obtain ⟨⟨hwf, hni⟩, h⟩ := h
  split at h
  · rename_i x₁ x₂ hx₁ hx₂
    obtain ⟨s₁, hs₁, rfl⟩ := exists_of_reachable hwf (reachable_of_run hx₁)
    obtain ⟨s₂, hs₂, rfl⟩ := exists_of_reachable hwf (reachable_of_run hx₂)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at h
    obtain ⟨⟨hv, h₁⟩, h₂⟩ := h
    intro hcsc
    have hni' := nonInput_iff.2 hni
    have := (hcsc s₁ s₂ hs₁ hs₂ (val_eq_of_enc hwf hs₁ hs₂ hv) z b hni').1
      ((enabledEdge_iff hwf hni').2 h₁)
    exact h₂ ((enabledEdge_iff hwf hni').1 this)
  · cases h

variable (N) in
/-- Firing `ts` reaches a state enabling the non-input edge `(z, b)`, which firing the
transition with index `u` (not an edge of `z`) disables. -/
def refuteOutputPersistent (ts : List ℕ) (z : ℕ) (b : Bool) (u : ℕ) : Bool :=
  N.wf && N.isNonInput z && match N.run ts with
    | some x => decide ((z, b) ∈ N.edgesOf (N.succ x)) && (N.succ x).any fun e =>
        decide (e.1.val = u) &&
        (match N.edge e.1 with
          | some (z', _) => !decide (z' = z)
          | none => true) &&
        !decide ((z, b) ∈ N.edgesOf (N.succ e.2))
    | none => false

theorem not_outputPersistent_of_refute {ts : List ℕ} {z : ℕ} {b : Bool} {u : ℕ}
    (h : N.refuteOutputPersistent ts z b u = true) : ¬ N.model.OutputPersistent := by
  simp only [refuteOutputPersistent, Bool.and_eq_true] at h
  obtain ⟨⟨hwf, hni⟩, h⟩ := h
  split at h
  · rename_i x hx
    obtain ⟨s, hs, rfl⟩ := exists_of_reachable hwf (reachable_of_run hx)
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
    obtain ⟨hen, ⟨t, x'⟩, hmem, ⟨-, hnz⟩, hdis⟩ := h
    obtain ⟨hent, rfl⟩ := (mem_succ_enc hwf).1 hmem
    have hni' := nonInput_iff.2 hni
    intro hp
    have hnot : ∀ b', N.model.lab t ≠ some (z, b') := by
      intro b' hl
      change N.edge t = some (z, b') at hl
      simp [hl] at hnz
    have := hp s hs z b hni' ((enabledEdge_iff hwf hni').2 hen) t _ ⟨hent, rfl⟩ hnot
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hdis
    exact hdis ((enabledEdge_iff hwf hni').1 this)
  · cases h

/-- Conformance makes every node check succeed (completeness of `conformNode`). -/
theorem conformNode_of_conformant (hwf : N.wf = true) {gates : List Gate}
    (hc : N.model.Conformant (N.gateFn gates)) {s : Marking (Fin N.net.places) × Val}
    (hs : N.model.sg.Reachable N.model.s₀ s) :
    N.conformNode gates (N.enc s) (N.succ (N.enc s)) = true := by
  obtain ⟨h1, h2⟩ := hc s hs
  simp only [conformNode, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq, List.any_eq_true]
  refine ⟨fun z hz => ?_, fun e he => ?_⟩
  · by_cases hni : N.isNonInput z = true
    · by_cases hex : StgModel.Excited (N.gateFn gates) s.2 z
      · obtain ⟨t, hen, hl⟩ := h1 z hz (nonInput_iff.2 hni) hex
        refine Or.inr ⟨(t, _), (mem_succ_enc hwf).2 ⟨hen, rfl⟩, ?_⟩
        rw [gateFnL_enc' gates s hz]
        exact hl
      · refine Or.inl (Or.inr ?_)
        rw [gateFnL_enc' gates s hz, getD_enc' s hz]
        unfold StgModel.Excited at hex
        exact not_not.1 hex
    · exact Or.inl (Or.inl (by simpa using hni))
  · obtain ⟨t, x⟩ := e
    obtain ⟨hen, rfl⟩ := (mem_succ_enc hwf).1 he
    change (match N.edge t with | none => true | some (z, b) => _) = true
    cases hl : N.edge t with
    | none => rfl
    | some p =>
      obtain ⟨z, b⟩ := p
      have hz : z < N.nsig := (wf_spec hwf).2.2 t z b hl
      simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_true,
        decide_eq_true_eq]
      by_cases hni : N.isNonInput z = true
      · obtain ⟨hF, hne⟩ := h2 t z b hen hl (nonInput_iff.2 hni)
        refine Or.inr ⟨?_, ?_⟩
        · rw [gateFnL_enc' gates s hz]; exact hF
        · rw [getD_enc' s hz]; exact hne
      · exact Or.inl (by simpa using hni)

variable (N) in
/-- Firing `ts` reaches a state where the gates `gates` violate conformance. -/
def refuteConformant (gates : List Gate) (ts : List ℕ) : Bool :=
  N.wf && match N.run ts with
    | some x => !N.conformNode gates x (N.succ x)
    | none => false

theorem not_conformant_of_refute {gates : List Gate} {ts : List ℕ}
    (h : N.refuteConformant gates ts = true) : ¬ N.model.Conformant (N.gateFn gates) := by
  simp only [refuteConformant, Bool.and_eq_true] at h
  obtain ⟨hwf, h⟩ := h
  split at h
  · rename_i x hx
    obtain ⟨s, hs, rfl⟩ := exists_of_reachable hwf (reachable_of_run hx)
    intro hc
    rw [conformNode_of_conformant hwf hc hs] at h
    cases h
  · cases h

variable (N) in
/-- Firing `ts` reaches a deadlock of the state graph. -/
def refuteDeadlockFree (ts : List ℕ) : Bool :=
  N.wf && N.explicit.refuteDeadlockFreeB N.init (N.net.toFins ts)

variable (N) in
/-- Firing `ts` reaches a state from which the dummies / internal edges `cyc` cycle. -/
def refuteLivelockFree (ts cyc : List ℕ) : Bool :=
  N.wf && N.explicit.refuteLivelockFreeB N.isInternal N.init (N.net.toFins ts)
    (N.net.toFins cyc)

variable (N) in
/-- Firing `ts` reaches a state from which transition `t` can never fire again. -/
def refuteLive (ts : List ℕ) (t : Fin N.net.trans.length) (fuel : ℕ := 100000) : Bool :=
  N.wf && N.explicit.refuteLiveB stateCmp fuel N.init (N.net.toFins ts) t

theorem not_deadlockFree_of_refute {ts : List ℕ} (h : N.refuteDeadlockFree ts = true) :
    ¬ N.model.sg.DeadlockFree N.model.s₀ := by
  simp only [refuteDeadlockFree, Bool.and_eq_true] at h
  rw [← (bisim h.1).deadlockFree_iff, enc_s₀ h.1]
  exact ExplicitLTS.not_deadlockFree_of_refuteB h.2

theorem not_livelockFree_of_refute {ts cyc : List ℕ} (h : N.refuteLivelockFree ts cyc = true) :
    ¬ N.model.sg.LivelockFree N.model.Internal N.model.s₀ := by
  simp only [refuteLivelockFree, Bool.and_eq_true] at h
  rw [internal_eq, ← (bisim h.1).livelockFree_iff, enc_s₀ h.1]
  exact ExplicitLTS.not_livelockFree_of_refuteB h.2

theorem not_liveLabel_of_refute {ts : List ℕ} {t : Fin N.net.trans.length} {fuel : ℕ}
    (h : N.refuteLive ts t fuel = true) : ¬ N.model.sg.LiveLabel N.model.s₀ t := by
  simp only [refuteLive, Bool.and_eq_true] at h
  rw [← (bisim h.1).liveLabel_iff, enc_s₀ h.1]
  exact ExplicitLTS.not_liveLabel_of_refuteB h.2

variable (N) in
/-- Check conformance of `gates` and correctness of the specification together. -/
def checkImpl (gates : List Gate) (c : Stg.InvCert) (c' : ExplicitLTS.Cert StgState) : Bool :=
  N.checkConformant gates c && N.checkCert c'

theorem implementation_correct_of_check {gates : List Gate} {c : Stg.InvCert}
    {c' : ExplicitLTS.Cert StgState} (h : N.checkImpl gates c c' = true) :
    (N.model.impl (N.gateFn gates)).DeadlockFree N.model.s₀ ∧
      (N.model.impl (N.gateFn gates)).LivelockFree N.model.Internal N.model.s₀ ∧
      (N.model.impl (N.gateFn gates)).Live N.model.s₀ := by
  simp only [checkImpl, Bool.and_eq_true] at h
  exact implementation_correct h.1 (correct_of_checkCert h.2)

end Stg

end AsyncLean
