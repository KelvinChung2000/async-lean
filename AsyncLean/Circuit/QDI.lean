/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Circuit.Wires
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation

/-!
# Quasi-delay-insensitivity implies speed independence

Adding wire delays can only add behaviours: zero wire delay is one particular choice of delays.
This file makes that precise for `Circuit.withWires`.  A state `s` of `C` is simulated by the
*settled* state `settle s` of `C.withWires iso`, in which every wire carries the value of its
source; a gate firing of `C` is simulated by the same gate firing followed by the wires that
carry its new value.  Hence:

* `Circuit.deadlockFree_of_withWires`, `Circuit.livelockFree_of_withWires` — deadlock and
  livelock freedom under wire delays imply them without;
* `Circuit.speedIndependent_of_qdi` — **QDI implies speed independence**;
* `Circuit.correct_of_qdi` — a QDI circuit that is correct under wire delays is correct.

For the last two, persistence of the circuit with wires guarantees that a gate excited while
some wires are still in flight stays excited once they have all arrived, so every behaviour of
the wired circuit projects to a behaviour of `C`.
-/

namespace AsyncLean

namespace Circuit

variable {C : Circuit} {iso : List ℕ}

/-! ### Structure of the circuit with wires -/

theorem mem_branches {k i : ℕ} (h : (k, i) ∈ C.branches iso) : i < C.signals := by
  simp only [branches, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨_, _, _, ⟨_, h, _⟩, he⟩ := h
  cases he
  exact h.2

theorem withWires_length :
    (C.withWires iso).gates.length = C.gates.length + (C.branches iso).length := by
  simp [withWires]

variable (iso) in
/-- Gate `k` of `C` as a gate of the circuit with wires. -/
def liftG (k : Fin C.gates.length) : Fin (C.withWires iso).gates.length :=
  ⟨k, by rw [withWires_length]; omega⟩

/-- The `j`-th wire. -/
def wireG (j : Fin (C.branches iso).length) : Fin (C.withWires iso).gates.length :=
  ⟨C.gates.length + j, by rw [withWires_length]; omega⟩

theorem liftG_injective : Function.Injective (liftG (C := C) iso) := by
  intro a b h
  exact Fin.ext (by simpa [liftG, Fin.ext_iff] using h)

theorem liftG_ne_wireG (k : Fin C.gates.length) (j : Fin (C.branches iso).length) :
    liftG iso k ≠ wireG j := by
  intro h
  simp only [liftG, wireG, Fin.ext_iff] at h
  omega

theorem label_cases (g : Fin (C.withWires iso).gates.length) :
    (∃ k, g = liftG iso k) ∨ ∃ j, g = wireG j := by
  by_cases h : g.val < C.gates.length
  · exact Or.inl ⟨⟨g, h⟩, rfl⟩
  · have h2 := g.isLt
    have h3 := withWires_length (C := C) (iso := iso)
    have : g.val < C.gates.length + (C.branches iso).length := by omega
    exact Or.inr ⟨⟨g - C.gates.length, by omega⟩, Fin.ext (by simp [wireG]; omega)⟩

theorem gate_liftG (k : Fin C.gates.length) :
    (C.withWires iso).gate (liftG iso k) =
      { C.gate k with fn := (C.gate k).fn.rename (C.wireOf iso k) } := by
  simp [gate, withWires, liftG, List.getElem_append_left]

theorem gate_wireG (j : Fin (C.branches iso).length) :
    ((C.withWires iso).gate (wireG j)).out = C.signals + j ∧
    ((C.withWires iso).gate (wireG j)).fn = .var ((C.branches iso)[j]).2 ∧
    ((C.withWires iso).gate (wireG j)).internal = true := by
  simp [gate, withWires, wireG, List.getElem_append_right]

theorem wireOf_lt {k i : ℕ} :
    C.wireOf iso k i < C.signals + (C.branches iso).length ∨
      C.wireOf iso k i = C.signals + (C.branches iso).length := by
  unfold wireOf
  split_ifs with h
  · split
    · rename_i j hj
      obtain ⟨hj, -⟩ := List.idxOf?_eq_some_iff.1 hj
      omega
    · omega
  · exact Or.inr rfl

/-! ### Projected and settled states -/

/-- The signals of `C` in a state of the circuit with wires. -/
def proj (t : Fin (C.withWires iso).signals → Bool) : Fin C.signals → Bool :=
  fun x => t ⟨x, by simp [withWires]; omega⟩

variable (iso) in
/-- The settled state: every wire carries the value of its source. -/
def settle (s : Fin C.signals → Bool) : Fin (C.withWires iso).signals → Bool := fun x =>
  if h : x.val < C.signals then s ⟨x, h⟩
  else C.val s ((C.branches iso)[x.val - C.signals]'(by
    have := x.isLt; simp only [withWires] at this; omega)).2

@[simp] theorem proj_settle (s : Fin C.signals → Bool) : proj (settle iso s) = s := by
  funext x; simp [proj, settle]

theorem val_lt (t : Fin (C.withWires iso).signals → Bool) {i : ℕ} (hi : i < C.signals) :
    (C.withWires iso).val t i = C.val (proj t) i := by
  have hi' : i < (C.withWires iso).signals := by simp only [withWires]; omega
  simp only [val, proj, hi, hi', ↓reduceDIte]

/-- A gate of `C` reads, in a settled state, exactly what it reads in `C`. -/
theorem val_settle_wireOf (s : Fin C.signals → Bool) (k : ℕ) :
    (C.withWires iso).val (settle iso s) ∘ C.wireOf iso k = C.val s := by
  funext i
  simp only [Function.comp]
  unfold wireOf
  by_cases hi : i < C.signals
  · simp only [hi, ↓reduceIte]
    split
    · rename_i j hj
      obtain ⟨hj, hji, -⟩ := List.idxOf?_eq_some_iff.1 hj
      have h1 : C.signals + j < (C.withWires iso).signals := by simp only [withWires]; omega
      have h2 : ¬ C.signals + j < C.signals := by omega
      simp only [val, settle, h1, h2, ↓reduceDIte, Nat.add_sub_cancel_left, hji]
    · rw [val_lt _ hi, proj_settle]
  · have h1 : ¬ C.signals + (C.branches iso).length < (C.withWires iso).signals := by
      simp only [withWires]; omega
    simp only [hi, ↓reduceIte, val, h1, ↓reduceDIte]

theorem excited_liftG_iff (t : Fin (C.withWires iso).signals → Bool) (k : Fin C.gates.length)
    (hout : (C.gate k).out < C.signals) :
    (C.withWires iso).Excited t (liftG iso k) ↔
      (C.gate k).fn.eval ((C.withWires iso).val t ∘ C.wireOf iso k) ≠ C.val (proj t) (C.gate k).out := by
  simp only [Excited, gate_liftG, BExpr.eval_rename, val_lt t hout]

/-- In a settled state, a gate of `C` is excited exactly when it is excited in `C`. -/
theorem excited_settle_iff (s : Fin C.signals → Bool) (k : Fin C.gates.length)
    (hout : (C.gate k).out < C.signals) :
    (C.withWires iso).Excited (settle iso s) (liftG iso k) ↔ C.Excited s k := by
  rw [excited_liftG_iff _ _ hout, val_settle_wireOf, proj_settle]; rfl

theorem bool_eq_of_ne {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- Firing a gate of `C` in the circuit with wires has the same effect on the signals of `C`,
provided the gate is also excited in `C`. -/
theorem proj_fire_liftG {t : Fin (C.withWires iso).signals → Bool} {k : Fin C.gates.length}
    (hout : (C.gate k).out < C.signals) (h₁ : (C.withWires iso).Excited t (liftG iso k))
    (h₂ : C.Excited (proj t) k) :
    proj ((C.withWires iso).fire t (liftG iso k)) = C.fire (proj t) k := by
  funext x
  have h₁' := h₁
  simp only [Excited, gate_liftG, val_lt t hout] at h₁'
  simp only [proj, fire, gate_liftG]
  split_ifs with hx
  · exact bool_eq_of_ne h₁' h₂
  · rfl

theorem proj_fire_wireG (t : Fin (C.withWires iso).signals → Bool)
    (j : Fin (C.branches iso).length) :
    proj ((C.withWires iso).fire t (wireG j)) = proj t := by
  funext x
  have hx : x.val ≠ C.signals + j := by omega
  simp only [proj, fire, (gate_wireG j).1, hx, ↓reduceIte]

theorem enabled_iff_excited {D : Circuit} {s : Fin D.signals → Bool} {g : Fin D.gates.length} :
    D.lts.Enabled s g ↔ D.Excited s g :=
  ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩

theorem internal_liftG (k : Fin C.gates.length) :
    (C.withWires iso).Internal (liftG iso k) ↔ C.Internal k := by
  simp [Internal, gate_liftG]

theorem internal_wireG (j : Fin (C.branches iso).length) :
    (C.withWires iso).Internal (wireG j) := (gate_wireG j).2.2

/-! ### Settling the wires -/

/-- The signal carried by the `j`-th wire. -/
def wsig (j : Fin (C.branches iso).length) : Fin (C.withWires iso).signals :=
  ⟨C.signals + j, by simp only [withWires]; omega⟩

theorem src_lt (j : Fin (C.branches iso).length) : ((C.branches iso)[j]).2 < C.signals :=
  mem_branches (k := ((C.branches iso)[j]).1) (List.getElem_mem j.isLt)

theorem val_wsig (t : Fin (C.withWires iso).signals → Bool) (j : Fin (C.branches iso).length) :
    (C.withWires iso).val t (C.signals + j) = t (wsig j) := by
  have h : C.signals + j < (C.withWires iso).signals := (wsig j).isLt
  simp only [val, h, ↓reduceDIte]; rfl

theorem settle_wsig (s : Fin C.signals → Bool) (j : Fin (C.branches iso).length) :
    settle iso s (wsig j) = C.val s ((C.branches iso)[j]).2 := by
  have h : ¬ (wsig (C := C) (iso := iso) j).val < C.signals := by simp [wsig]
  simp only [settle, h, ↓reduceDIte]
  congr 2; simp [wsig]

theorem excited_wireG_iff (t : Fin (C.withWires iso).signals → Bool)
    (j : Fin (C.branches iso).length) :
    (C.withWires iso).Excited t (wireG j) ↔ t (wsig j) ≠ C.val (proj t) ((C.branches iso)[j]).2 := by
  simp only [Excited, (gate_wireG j).1, (gate_wireG j).2.1, BExpr.eval, val_lt t (src_lt j),
    val_wsig]
  exact ne_comm

theorem fire_wireG_wsig (t : Fin (C.withWires iso).signals → Bool)
    (j j' : Fin (C.branches iso).length) :
    (C.withWires iso).fire t (wireG j) (wsig j') =
      if j' = j then C.val (proj t) ((C.branches iso)[j]).2 else t (wsig j') := by
  simp only [fire, (gate_wireG j).1, (gate_wireG j).2.1, BExpr.eval, val_lt t (src_lt j)]
  by_cases h : j' = j
  · subst h; simp [wsig]
  · have : (wsig (C := C) (iso := iso) j').val ≠ C.signals + j := by
      simp only [wsig]; intro h'; exact h (Fin.ext (by omega))
    simp [this, h]

/-- One wire switching. -/
def WStep (t t' : Fin (C.withWires iso).signals → Bool) : Prop :=
  ∃ j, (C.withWires iso).lts.step t (wireG j) t'

/-- The wires that do not yet carry the value of their source. -/
noncomputable def unsettled (t : Fin (C.withWires iso).signals → Bool) :
    Finset (Fin (C.branches iso).length) := by
  classical
  exact Finset.univ.filter fun j => t (wsig j) ≠ C.val (proj t) ((C.branches iso)[j]).2

theorem mem_unsettled {t : Fin (C.withWires iso).signals → Bool}
    {j : Fin (C.branches iso).length} :
    j ∈ unsettled t ↔ t (wsig j) ≠ C.val (proj t) ((C.branches iso)[j]).2 := by
  classical
  simp [unsettled]

theorem eq_settle_of_unsettled (t : Fin (C.withWires iso).signals → Bool)
    (h : unsettled t = ∅) : t = settle iso (proj t) := by
  funext x
  by_cases hx : x.val < C.signals
  · simp [settle, hx, proj]
  · have hlt := x.isLt
    simp only [withWires] at hlt
    let j : Fin (C.branches iso).length := ⟨x - C.signals, by omega⟩
    have hj : j ∉ unsettled t := by simp [h]
    rw [mem_unsettled, not_not] at hj
    have hx' : x = wsig j := Fin.ext (by simp [wsig, j]; omega)
    rw [hx', hj, settle_wsig]

/-- From any state, the wires can all switch to the values of their sources. -/
theorem wsteps_settle (t : Fin (C.withWires iso).signals → Bool) :
    Relation.ReflTransGen WStep t (settle iso (proj t)) := by
  suffices key : ∀ n, ∀ t : Fin (C.withWires iso).signals → Bool, (unsettled t).card = n →
      Relation.ReflTransGen WStep t (settle iso (proj t)) from key _ t rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t hn
    by_cases he : unsettled t = ∅
    · rw [← eq_settle_of_unsettled t he]
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 he
      have hex : (C.withWires iso).Excited t (wireG j) := (excited_wireG_iff t j).2 (mem_unsettled.1 hj)
      obtain ⟨t', ht'⟩ : ∃ t', t' = (C.withWires iso).fire t (wireG j) := ⟨_, rfl⟩
      have hp : proj t' = proj t := ht' ▸ proj_fire_wireG t j
      have hsub : unsettled t' ⊂ unsettled t := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨j, hj, ?_⟩
          rw [mem_unsettled, not_not, hp, ht', fire_wireG_wsig]; simp
        · intro j' hj'
          rw [mem_unsettled, hp, ht', fire_wireG_wsig] at hj'
          split_ifs at hj' with h
          · subst h; exact absurd rfl hj'
          · exact mem_unsettled.2 hj'
      have := ih _ (hn ▸ Finset.card_lt_card hsub) t' rfl
      rw [hp] at this
      exact Relation.ReflTransGen.head ⟨j, hex, ht'⟩ this

theorem wsteps_proj_eq {t t' : Fin (C.withWires iso).signals → Bool}
    (h : Relation.ReflTransGen WStep t t') : proj t' = proj t := by
  induction h with
  | refl => rfl
  | tail _ hw ih => obtain ⟨j, -, rfl⟩ := hw; rw [proj_fire_wireG, ih]

theorem wsteps_reachable {t t' : Fin (C.withWires iso).signals → Bool}
    (h : Relation.ReflTransGen WStep t t') : (C.withWires iso).lts.Reachable t t' := by
  induction h with
  | refl => exact LTS.Reachable.refl _
  | tail _ hw ih => obtain ⟨j, hj⟩ := hw; exact ih.tail ⟨wireG j, hj⟩

theorem wsteps_iSteps {t t' : Fin (C.withWires iso).signals → Bool}
    (h : Relation.ReflTransGen WStep t t') :
    Relation.ReflTransGen ((C.withWires iso).lts.IStep (C.withWires iso).Internal) t t' := by
  induction h with
  | refl => exact .refl
  | tail _ hw ih => obtain ⟨j, hj⟩ := hw; exact ih.tail ⟨wireG j, internal_wireG j, hj⟩

/-! ### Simulation of `C` by the circuit with wires -/

/-- A step of `C` is simulated by the same gate followed by wire steps. -/
theorem step_sim (hout : ∀ g, (C.gate g).out < C.signals) {s s' : Fin C.signals → Bool}
    {k : Fin C.gates.length} (h : C.lts.step s k s') :
    (C.withWires iso).lts.step (settle iso s) (liftG iso k)
        ((C.withWires iso).fire (settle iso s) (liftG iso k)) ∧
      Relation.ReflTransGen WStep ((C.withWires iso).fire (settle iso s) (liftG iso k))
        (settle iso s') := by
  obtain ⟨hex, rfl⟩ := h
  have hex' := (excited_settle_iff (iso := iso) s k (hout k)).2 hex
  refine ⟨⟨hex', rfl⟩, ?_⟩
  have hp := proj_fire_liftG (hout k) hex' (by rwa [proj_settle])
  rw [proj_settle] at hp
  rw [← hp]
  exact wsteps_settle _

theorem s₀_withWires (hlen : C.init.length = C.signals) :
    (C.withWires iso).s₀ = settle iso C.s₀ := by
  funext x
  have hlt := x.isLt
  simp only [withWires] at hlt
  simp only [s₀, settle, withWires]
  split_ifs with hx
  · have : x.val < C.init.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
  · have hs : ((C.branches iso)[x.val - C.signals]'(by omega)).2 < C.signals := by
      simpa using src_lt (C := C) (iso := iso) ⟨x - C.signals, by omega⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : C.init.length ≤ x),
      hlen, List.getElem?_map, val]
    rw [List.getElem?_eq_getElem (by omega)]
    simp [hs, s₀, List.getD_eq_getElem?_getD]

variable (hwf : C.wf = true)
include hwf

theorem reachable_settle {s : Fin C.signals → Bool} (h : C.lts.Reachable C.s₀ s) :
    (C.withWires iso).lts.Reachable (C.withWires iso).s₀ (settle iso s) := by
  induction h with
  | refl => rw [s₀_withWires (wf_spec hwf).1]
  | tail _ hst ih =>
    obtain ⟨k, hk⟩ := hst
    obtain ⟨h1, h2⟩ := step_sim (wf_spec hwf).2 hk
    exact (ih.tail ⟨_, h1⟩).trans (wsteps_reachable h2)

omit hwf in
theorem isDeadlock_settle (hout : ∀ g, (C.gate g).out < C.signals) {s : Fin C.signals → Bool}
    (h : C.lts.IsDeadlock s) : (C.withWires iso).lts.IsDeadlock (settle iso s) := by
  intro g t ht
  rcases label_cases g with ⟨k, rfl⟩ | ⟨j, rfl⟩
  · exact h k _ ⟨(excited_settle_iff s k (hout k)).1 ht.1, rfl⟩
  · exact (excited_wireG_iff _ j).1 ht.1 (by rw [settle_wsig, proj_settle])

/-- Deadlock freedom under wire delays implies deadlock freedom. -/
theorem deadlockFree_of_withWires
    (h : (C.withWires iso).lts.DeadlockFree (C.withWires iso).s₀) :
    C.lts.DeadlockFree C.s₀ :=
  fun _ hs hd => h _ (reachable_settle hwf hs) (isDeadlock_settle (wf_spec hwf).2 hd)

/-- Livelock freedom under wire delays implies livelock freedom. -/
theorem livelockFree_of_withWires
    (h : (C.withWires iso).lts.LivelockFree (C.withWires iso).Internal (C.withWires iso).s₀) :
    C.lts.LivelockFree C.Internal C.s₀ := by
  rw [LTS.livelockFree_iff_acc] at h ⊢
  intro s hs
  have hacc := InvImage.accessible (settle iso) (h _ (reachable_settle hwf hs)).transGen
  refine Subrelation.accessible ?_ hacc
  intro a b hab
  obtain ⟨k, hk, hst⟩ := hab
  obtain ⟨h1, h2⟩ := step_sim (iso := iso) (wf_spec hwf).2 hst
  have : Relation.TransGen ((C.withWires iso).lts.IStep (C.withWires iso).Internal)
      (settle iso b) (settle iso a) :=
    Relation.TransGen.head' ⟨liftG iso k, (internal_liftG k).2 hk, h1⟩ (wsteps_iSteps h2)
  exact Relation.transGen_swap.2 this

omit hwf in
/-- In a persistent circuit with wires, a gate excited while wires are in flight stays excited
once they have all arrived. -/
theorem excited_settle_of_persistent
    (hP : (C.withWires iso).lts.Persistent (C.withWires iso).s₀)
    {t : Fin (C.withWires iso).signals → Bool}
    (ht : (C.withWires iso).lts.Reachable (C.withWires iso).s₀ t) {k : Fin C.gates.length}
    (h : (C.withWires iso).Excited t (liftG iso k)) :
    (C.withWires iso).Excited (settle iso (proj t)) (liftG iso k) := by
  have key : ∀ u, Relation.ReflTransGen WStep t u →
      (C.withWires iso).lts.Reachable (C.withWires iso).s₀ u ∧
        (C.withWires iso).Excited u (liftG iso k) := by
    intro u hu
    induction hu with
    | refl => exact ⟨ht, h⟩
    | tail _ hw ih =>
      obtain ⟨j, hj⟩ := hw
      exact ⟨ih.1.tail ⟨_, hj⟩, enabled_iff_excited.1
        (hP _ ih.1 _ _ _ (liftG_ne_wireG k j) (enabled_iff_excited.2 ih.2) hj)⟩
  exact (key _ (wsteps_settle t)).2

/-- In a persistent circuit with wires, every behaviour projects to a behaviour of `C`. -/
theorem reachable_proj (hP : (C.withWires iso).lts.Persistent (C.withWires iso).s₀)
    {t t' : Fin (C.withWires iso).signals → Bool}
    (ht : (C.withWires iso).lts.Reachable (C.withWires iso).s₀ t)
    (h : (C.withWires iso).lts.Reachable t t') : C.lts.Reachable (proj t) (proj t') := by
  induction h with
  | refl => exact LTS.Reachable.refl _
  | tail hr hst ih =>
    rename_i u v
    obtain ⟨g, hg⟩ := hst
    have hu := ht.trans hr
    rcases label_cases g with ⟨k, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨hex, rfl⟩ := hg
      have h2 : C.Excited (proj u) k :=
        (excited_settle_iff _ k ((wf_spec hwf).2 k)).1 (excited_settle_of_persistent hP hu hex)
      rw [proj_fire_liftG ((wf_spec hwf).2 k) hex h2]
      exact ih.tail ⟨k, h2, rfl⟩
    · obtain ⟨_, rfl⟩ := hg
      rw [proj_fire_wireG]
      exact ih

/-- **QDI implies speed independence.** -/
theorem speedIndependent_of_qdi (hQ : C.QDI iso) : C.SpeedIndependent := by
  intro s hs k k' s' hne hen hst
  have hout := (wf_spec hwf).2
  obtain ⟨h1, h2⟩ := step_sim (iso := iso) hout hst
  have hr := reachable_settle (iso := iso) hwf hs
  have hen' := (excited_settle_iff (iso := iso) s k (hout k)).2 (enabled_iff_excited.1 hen)
  have e1 := hQ _ hr _ _ _ (fun h => hne (liftG_injective h)) (enabled_iff_excited.2 hen') h1
  have e2 := excited_settle_of_persistent hQ (hr.tail ⟨_, h1⟩) (enabled_iff_excited.1 e1)
  have hp : proj ((C.withWires iso).fire (settle iso s) (liftG iso k')) = s' := by
    simpa using (wsteps_proj_eq h2).symm
  rw [hp] at e2
  exact enabled_iff_excited.2 ((excited_settle_iff s' k (hout k)).1 e2)

/-- **A QDI circuit that is correct under wire delays is correct.** -/
theorem correct_of_qdi (hQ : C.QDI iso) (hC : C.QDICorrect iso) : C.Correct := by
  obtain ⟨hD, hL, hLive⟩ := hC
  refine ⟨deadlockFree_of_withWires hwf hD, livelockFree_of_withWires hwf hL, ?_⟩
  intro k s hs
  have hr := reachable_settle (iso := iso) hwf hs
  obtain ⟨t, htr, hen⟩ := hLive (liftG iso k) _ hr
  refine ⟨proj t, by simpa using reachable_proj hwf hQ hr htr, ?_⟩
  exact enabled_iff_excited.2 ((excited_settle_iff _ k ((wf_spec hwf).2 k)).1
    (excited_settle_of_persistent hQ (hr.trans htr) (enabled_iff_excited.1 hen)))

end Circuit

end AsyncLean
