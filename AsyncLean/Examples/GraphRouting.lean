/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Routing.Graph
import AsyncLean.AxiomAudit

/-!
# Example: adaptive routing beyond the mesh

`AsyncLean.Routing.Graph` makes minimal adaptive routing safe on every finite connected graph,
with tree routing along a spanning tree as the escape layer.  Two instances:

* `torus k` : the `(k + 1) × (k + 1)` torus (a mesh with wraparound links), with the distance
  with wraparound for the adaptive layer and a comb spanning tree (up each column to row 0, then
  west along row 0 to the corner).  `torus_correct k` : **for every size**, it is deadlock free
  and livelock free under every valid selection function and starvation free under strongly
  fair scheduling; `torus_correct_of_sourceSel` : the same under every selection that never
  refuses a free escape hop outside the sources and may throttle the sources.  The torus has
  cyclic channel dependencies on its wraparound links, which minimal adaptive routing uses; the
  escape layer avoids them.
* `petersen` : the Petersen graph (10 vertices, 3-regular, diameter 2, not a mesh, a torus
  or a ring), with its graph distance (`petersen_dist`) and a breadth-first spanning tree, all
  checked by `decide`.  `petersen_correct` : it is deadlock, livelock and starvation free;
  `petersen_adaptive` : its adaptive layer offers a hop to every packet that has not arrived.
-/

namespace AsyncLean.Examples

open Network

/-! ### The torus of every size -/

/-- The next coordinate on a ring of `k + 1` positions (with wraparound). -/
def cycSucc {k : ℕ} (a : Fin (k + 1)) : Fin (k + 1) :=
  if h : a.val = k then 0 else ⟨a.val + 1, by omega⟩

/-- The previous coordinate on a ring of `k + 1` positions (with wraparound). -/
def cycPred {k : ℕ} (a : Fin (k + 1)) : Fin (k + 1) :=
  if h : a.val = 0 then Fin.last k else ⟨a.val - 1, by omega⟩

/-- One step back undoes one step forward. -/
theorem cycPred_cycSucc {k : ℕ} (a : Fin (k + 1)) : cycPred (cycSucc a) = a := by
  unfold cycSucc cycPred
  by_cases h : a.val = k
  · simp only [h, ↓reduceDIte, Fin.val_zero]; ext; simp [h]
  · simp only [h, ↓reduceDIte]; ext; simp

/-- One step forward undoes one step back. -/
theorem cycSucc_cycPred {k : ℕ} (a : Fin (k + 1)) : cycSucc (cycPred a) = a := by
  unfold cycSucc cycPred
  by_cases h : a.val = 0
  · simp only [h, ↓reduceDIte, Fin.val_last]; ext; simp [h]
  · simp only [h, ↓reduceDIte]
    rw [dite_eq_right_of_eq_false (eq_false (by have := a.isLt; omega))]
    ext; simp; omega

/-- The distance between two coordinates on a ring of `k + 1` positions, with wraparound. -/
def cycDist {k : ℕ} (a b : Fin (k + 1)) : ℕ :=
  min ((a.val + (k + 1) - b.val) % (k + 1)) ((b.val + (k + 1) - a.val) % (k + 1))

/-- **The `(k + 1) × (k + 1)` torus**: each vertex has its four neighbours (with wraparound),
the adaptive layer uses the distance with wraparound, and the spanning tree goes up each column
to row 0 and then west along row 0 to the corner `(0, 0)`. -/
def torus (k : ℕ) : GraphData (Fin (k + 1) × Fin (k + 1)) where
  verts := (List.finRange (k + 1)).flatMap fun x => (List.finRange (k + 1)).map fun y => (x, y)
  mem_verts u := by simp
  nbrs u := [(cycSucc u.1, u.2), (cycPred u.1, u.2), (u.1, cycSucc u.2), (u.1, cycPred u.2)]
  symm u v h := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> simp [cycPred_cycSucc, cycSucc_cycPred]
  dist u d := cycDist u.1 d.1 + cycDist u.2 d.2
  root := (0, 0)
  par u := if u.2.val ≠ 0 then (u.1, cycPred u.2) else if u.1.val ≠ 0 then (cycPred u.1, 0)
    else (0, 0)
  dep u := u.1.val + u.2.val
  dep_root := rfl
  par_root := by simp
  dep_par u hu := by
    obtain ⟨x, y⟩ := u
    dsimp only
    by_cases hy : y.val = 0
    · have hx : x.val ≠ 0 := fun h => hu (Prod.ext (Fin.ext h) (Fin.ext hy))
      simp only [hy, hx, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte, cycPred,
        ↓reduceDIte, Fin.val_zero]
      omega
    · simp only [hy, ne_eq, not_false_eq_true, ↓reduceIte, cycPred, ↓reduceDIte]
      omega
  par_adj u hu := by
    obtain ⟨x, y⟩ := u
    by_cases hy : y.val = 0
    · have hx : x.val ≠ 0 := fun h => hu (Prod.ext (Fin.ext h) (Fin.ext hy))
      have hy' : y = 0 := Fin.ext hy
      subst hy'
      simp [hx]
    · simp [hy]

/-- **The torus of every size is correct**: deadlock free and livelock free under every valid
selection function, and starvation free under strongly fair scheduling. -/
theorem torus_correct (k : ℕ) : (torus k).net.Correct ∧ (torus k).net.StarvationFree :=
  (torus k).correct

/-- **The torus of every size is correct under throttled sources**: deadlock, livelock and
starvation free under every selection that never refuses a free escape hop outside the
injection channels and lets a source go once the rest of the network is empty. -/
theorem torus_correct_of_sourceSel (k : ℕ) {sel : Selection (GChan (Fin (k + 1) × Fin (k + 1)))
      (Fin (k + 1) × Fin (k + 1))}
    (hsel : (torus k).net.SourceSel (torus k).escape (fun c => c.isInj) sel) :
    (torus k).net.DeadlockFreeWith sel ∧ (torus k).net.LivelockFreeWith sel ∧
      (torus k).net.StarvationFreeWith sel :=
  (torus k).correct_of_sourceSel hsel

/-- Every hop of the torus network follows a link of the torus. -/
theorem torus_route_adj (k : ℕ) {c : GChan (Fin (k + 1) × Fin (k + 1))}
    {d : Fin (k + 1) × Fin (k + 1)} {q} (ha : (torus k).net.arrived c d = false)
    (h : q ∈ (torus k).net.route c d) :
    ∃ v ∈ (torus k).nbrs c.head, ∃ vc, q.1 = .link c.head v vc ∧ q.2 = d :=
  (torus k).route_adj ha h

/-! ### The Petersen graph -/

/-- The neighbours in the Petersen graph: the outer 5-cycle `0 … 4`, the spokes `i — i + 5`
and the inner pentagram `5 — 7 — 9 — 6 — 8 — 5`. -/
def petersenNbrs (u : Fin 10) : List (Fin 10) :=
  ([[1, 4, 5], [0, 2, 6], [1, 3, 7], [2, 4, 8], [3, 0, 9],
    [0, 7, 8], [1, 8, 9], [2, 5, 9], [3, 5, 6], [4, 6, 7]] : List (List (Fin 10))).getD u.val []

/-- **The Petersen graph**, with its graph distance and a breadth-first spanning tree rooted at
vertex 0. -/
def petersen : GraphData (Fin 10) where
  verts := List.finRange 10
  mem_verts := List.mem_finRange
  nbrs := petersenNbrs
  symm := by decide
  dist u d := if u = d then 0 else if d ∈ petersenNbrs u then 1 else 2
  root := 0
  par u := ([0, 0, 1, 4, 0, 0, 1, 5, 5, 4] : List (Fin 10)).getD u.val 0
  dep u := [0, 1, 2, 2, 1, 1, 2, 2, 2, 2].getD u.val 0
  dep_root := rfl
  par_root := rfl
  dep_par := by decide
  par_adj := by decide

/-- The distance of `petersen` is the graph distance: every vertex other than the destination
has a neighbour one step closer.  So the adaptive layer is minimal adaptive routing, and it
offers a hop to every packet that has not arrived. -/
theorem petersen_dist : ∀ u d, u ≠ d → ∃ v ∈ petersen.nbrs u, petersen.dist v d + 1 = petersen.dist u d := by
  decide

/-- **The Petersen graph is correct**: deadlock free and livelock free under every valid
selection function, and starvation free under strongly fair scheduling. -/
theorem petersen_correct : petersen.net.Correct ∧ petersen.net.StarvationFree :=
  petersen.correct

/-- With its graph distance, the adaptive layer of the Petersen graph offers a hop to every
packet that has not arrived. -/
theorem petersen_adaptive {c : GChan (Fin 10)} {d : Fin 10} (ha : petersen.net.arrived c d = false) :
    petersen.adaptiveHops c d ≠ [] :=
  petersen.adaptive_ne_nil petersen_dist ha

#assert_standard_axioms torus_correct torus_correct_of_sourceSel torus_route_adj
#assert_standard_axioms petersen_dist petersen_correct petersen_adaptive

end AsyncLean.Examples
