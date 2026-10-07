/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Circuit.Basic

/-!
# Combinational netlists as functions

A router's routing logic, an arbiter's priority encoder or a decoder is a *combinational*
netlist: gates without feedback, from input signals to output signals.  `Comb` is such a
netlist: signals `0 … nin - 1` are the inputs, and the gates, listed in topological order,
each drive one further signal from a Boolean expression (`BExpr`).

* `Comb.val c xs` evaluates the gates once, in order, from the input bits `xs`;
  `Comb.eval c xs` reads the outputs.
* `Comb.wf` checks that the netlist is well formed: every gate drives a fresh non-input
  signal and reads only inputs and signals driven by earlier gates, and every output is an
  input or driven.
* **`Comb.unique`**: in a well-formed netlist, *any* valuation consistent with the gates —
  any settled state of the hardware, whatever the gate delays — agrees with `Comb.eval` on
  the outputs.  So the netlist computes a function, and `Comb.eval` is it.
* `Comb.val_consistent`: the evaluation is itself consistent with every gate.
-/

namespace AsyncLean

namespace BExpr

/-- Every variable of the expression satisfies `S`. -/
def reads (S : ℕ → Bool) : BExpr → Bool
  | var i => S i
  | const _ => true
  | not e => e.reads S
  | and a b => a.reads S && b.reads S
  | or a b => a.reads S && b.reads S
  | xor a b => a.reads S && b.reads S

theorem eval_congr {S : ℕ → Bool} {v w : ℕ → Bool} (h : ∀ i, S i = true → v i = w i) :
    ∀ {e : BExpr}, e.reads S = true → e.eval v = e.eval w
  | var i, hr => h i hr
  | const _, _ => rfl
  | not e, hr => by simp only [eval, eval_congr h (e := e) hr]
  | and a b, hr => by
    simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, eval_congr h hr.1, eval_congr h hr.2]
  | or a b, hr => by
    simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, eval_congr h hr.1, eval_congr h hr.2]
  | xor a b, hr => by
    simp only [reads, Bool.and_eq_true] at hr
    simp only [eval, eval_congr h hr.1, eval_congr h hr.2]

end BExpr

/-- A combinational netlist: inputs `0 … nin - 1`, gates `(driven signal, function)` in
topological order, and the output signals. -/
structure Comb where
  nin : ℕ
  gates : List (ℕ × BExpr)
  outs : List ℕ
deriving Repr, Inhabited

namespace Comb

variable (c : Comb)

/-- The valuation with the input bits `xs` (and every other signal low). -/
def inputs (xs : List Bool) : ℕ → Bool := fun i => if i < c.nin then xs.getD i false else false

/-- Evaluate one gate. -/
def step (v : ℕ → Bool) (g : ℕ × BExpr) : ℕ → Bool :=
  fun i => if i = g.1 then g.2.eval v else v i

/-- **The evaluation** of the netlist on the input bits `xs`. -/
def val (xs : List Bool) : ℕ → Bool := c.gates.foldl step (c.inputs xs)

/-- The output bits. -/
def eval (xs : List Bool) : List Bool := c.outs.map (c.val xs)

/-- Gates in topological order, each driving a fresh signal. -/
def wfAux (nin : ℕ) : List ℕ → List (ℕ × BExpr) → Bool
  | _, [] => true
  | known, g :: gs => decide (nin ≤ g.1) && !known.contains g.1 &&
      g.2.reads (fun i => decide (i < nin) || known.contains i) && wfAux nin (g.1 :: known) gs

/-- **Well-formedness**: topological order, fresh outputs, outputs defined. -/
def wf : Bool :=
  wfAux c.nin [] c.gates && c.outs.all fun o => decide (o < c.nin) || c.gates.any (·.1 == o)

variable {c}

theorem foldl_step_of_not_mem {v : ℕ → Bool} {i : ℕ} :
    ∀ {gs : List (ℕ × BExpr)}, i ∉ gs.map Prod.fst → gs.foldl step v i = v i
  | [], _ => rfl
  | g :: gs, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, foldl_step_of_not_mem h.2]
    simp [step, Ne.symm h.1, h.1]

/-- The heart of `unique`: a consistent valuation agrees with the evaluation on the inputs, the
known signals and the gates still to evaluate. -/
theorem agree_aux {v : ℕ → Bool} (nin : ℕ) :
    ∀ (gs : List (ℕ × BExpr)) (known : List ℕ) (u : ℕ → Bool), wfAux nin known gs = true →
      (∀ i, (i < nin ∨ i ∈ known) → v i = u i) → (∀ g ∈ gs, v g.1 = g.2.eval v) →
      ∀ i, (i < nin ∨ i ∈ known ∨ i ∈ gs.map Prod.fst) → v i = gs.foldl step u i
  | [], known, u, _, hu, _, i, hi => by
    simp only [List.map_nil, List.not_mem_nil, or_false] at hi
    exact hu i hi
  | g :: gs, known, u, hw, hu, hg, i, hi => by
    simp only [wfAux, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨hge, hfresh⟩, hreads⟩, hrest⟩ := hw
    have hfresh' : g.1 ∉ known := fun h => by rw [List.contains_iff_mem.2 h] at hfresh; cases hfresh
    rw [List.foldl_cons]
    refine agree_aux nin gs (g.1 :: known) (step u g) hrest (fun j hj => ?_)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) i ?_
    · -- the evaluation of `g` agrees with `v` on the signals read so far
      by_cases hjg : j = g.1
      · subst hjg
        simp only [step, ↓reduceIte]
        rw [hg g List.mem_cons_self]
        refine BExpr.eval_congr (fun k hk => hu k ?_) hreads
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hk
        exact hk
      · simp only [step, hjg, ↓reduceIte]
        rcases hj with hj | hj
        · exact hu j (Or.inl hj)
        · exact hu j (Or.inr ((List.mem_cons.1 hj).resolve_left hjg))
    · rcases hi with hi | hi | hi
      · exact Or.inl hi
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hi))
      · simp only [List.map_cons, List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact Or.inr (Or.inl List.mem_cons_self)
        · exact Or.inr (Or.inr hi)

/-- **The netlist computes a function**: every valuation consistent with the gates and the
inputs agrees with the evaluation on the outputs. -/
theorem unique (hwf : c.wf = true) {xs : List Bool} {v : ℕ → Bool}
    (hin : ∀ i < c.nin, v i = xs.getD i false) (hg : ∀ g ∈ c.gates, v g.1 = g.2.eval v) :
    ∀ o ∈ c.outs, v o = c.val xs o := by
  simp only [wf, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.any_eq_true, beq_iff_eq] at hwf
  intro o ho
  refine agree_aux c.nin c.gates [] (c.inputs xs) hwf.1 (fun i hi => ?_) hg o ?_
  · rcases hi with hi | hi
    · simp [inputs, hi, hin i hi]
    · simp at hi
  · rcases hwf.2 o ho with h | ⟨g, hg', rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (List.mem_map_of_mem hg'))

theorem wfAux_out {nin : ℕ} : ∀ {gs : List (ℕ × BExpr)} {known : List ℕ},
    wfAux nin known gs = true → ∀ g ∈ gs, nin ≤ g.1 ∧ g.1 ∉ known
  | [], _, _ => by simp
  | g :: gs, known, hw => by
    simp only [wfAux, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨hge, hfresh⟩, -⟩, hrest⟩ := hw
    intro g₁ hg₁
    rcases List.mem_cons.1 hg₁ with rfl | hg₁
    · exact ⟨hge, fun h => by rw [List.contains_iff_mem.2 h] at hfresh; cases hfresh⟩
    · obtain ⟨h1, h2⟩ := wfAux_out hrest g₁ hg₁
      exact ⟨h1, fun h => h2 (List.mem_cons_of_mem _ h)⟩

theorem consistent_aux {nin : ℕ} : ∀ (gs : List (ℕ × BExpr)) (known : List ℕ) (u : ℕ → Bool),
    wfAux nin known gs = true → ∀ g ∈ gs, gs.foldl step u g.1 = g.2.eval (gs.foldl step u)
  | [], _, _, _, g, hg => by simp at hg
  | g :: gs, known, u, hw, g₁, hg₁ => by
    have hout := wfAux_out hw
    simp only [wfAux, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨hge, hfresh⟩, hreads⟩, hrest⟩ := hw
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hg₁ with rfl | hg₁
    · -- later gates leave alone what `g` reads and drives
      have hlater := wfAux_out hrest
      have hnot : ∀ i, (i < nin ∨ i ∈ g₁.1 :: known) → i ∉ gs.map Prod.fst := by
        intro i hi hm
        obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hm
        obtain ⟨h1, h2⟩ := hlater g' hg'
        rcases hi with hi | hi
        · omega
        · exact h2 hi
      rw [foldl_step_of_not_mem (hnot _ (Or.inr List.mem_cons_self))]
      simp only [step, ↓reduceIte]
      refine BExpr.eval_congr (fun k hk => ?_) hreads
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hk
      rw [foldl_step_of_not_mem (hnot k (hk.imp id (List.mem_cons_of_mem _)))]
      have : k ≠ g₁.1 := by
        rintro rfl
        rcases hk with hk | hk
        · omega
        · rw [List.contains_iff_mem.2 hk] at hfresh; cases hfresh
      simp [step, this]
    · exact consistent_aux gs (g.1 :: known) (step u g) hrest g₁ hg₁

/-- **The evaluation settles every gate.** -/
theorem val_consistent (hwf : c.wf = true) (xs : List Bool) :
    ∀ g ∈ c.gates, c.val xs g.1 = g.2.eval (c.val xs) := by
  simp only [wf, Bool.and_eq_true] at hwf
  exact consistent_aux c.gates [] (c.inputs xs) hwf.1

theorem val_input (hwf : c.wf = true) (xs : List Bool) {i : ℕ} (hi : i < c.nin) :
    c.val xs i = xs.getD i false := by
  simp only [wf, Bool.and_eq_true] at hwf
  unfold val
  have hnm : i ∉ c.gates.map Prod.fst := fun hm => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    have := (wfAux_out hwf.1 g hg).1
    omega
  rw [foldl_step_of_not_mem hnm]
  simp [inputs, hi]

end Comb

end AsyncLean
