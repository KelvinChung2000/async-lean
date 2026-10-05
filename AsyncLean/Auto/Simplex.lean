/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.WellFounded

/-!
# An exact rational simplex solver (untrusted)

`Simplex.solve A b c` minimises `c · x` subject to `A x = b`, `x ≥ 0`, with exact rational
arithmetic, two phases and Bland's anti-cycling rule.  It is used to *find* structural
certificates (place invariants, ranking functions); the certificates are then checked by the
kernel, so this code needs no proof.
-/

namespace AsyncLean

namespace Simplex

/-- A tableau: rows of coefficients followed by the right-hand side, and the basic variable of
each row. -/
structure Tableau where
  rows : Array (Array Rat)
  basis : Array ℕ

/-- Pivot on row `r`, column `j`. -/
def pivot (t : Tableau) (r j : ℕ) : Tableau :=
  let row := t.rows[r]!
  let p := row[j]!
  let row := row.map (· / p)
  let rows := (Array.range t.rows.size).map fun i =>
    if i == r then row
    else
      let ri := t.rows[i]!
      let f := ri[j]!
      if f == 0 then ri else (Array.range ri.size).map fun k => ri[k]! - f * row[k]!
  { rows, basis := t.basis.set! r j }

/-- Run the simplex method minimising `cost`, only letting the columns `allowed` enter.
Returns `none` if the problem is unbounded or the iteration budget is exhausted. -/
def run (cost : Array Rat) (allowed : ℕ → Bool) (fuel : ℕ) (t : Tableau) : Option Tableau :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let ncols := cost.size
    let reduced (j : ℕ) : Rat :=
      cost[j]! - (Array.range t.rows.size).foldl
        (fun acc i => acc + cost[t.basis[i]!]! * t.rows[i]![j]!) 0
    match (List.range ncols).find? fun j => allowed j && !t.basis.contains j && reduced j < 0 with
    | none => some t
    | some j =>
      let rhs := ncols
      let cands := (List.range t.rows.size).filter fun i => t.rows[i]![j]! > 0
      match cands with
      | [] => none
      | i₀ :: is =>
        let ratio (i : ℕ) : Rat := t.rows[i]![rhs]! / t.rows[i]![j]!
        let best := is.foldl (fun b i =>
          if ratio i < ratio b || (ratio i == ratio b && t.basis[i]! < t.basis[b]!) then i else b) i₀
        run cost allowed fuel (pivot t best j)

/-- Minimise `c · x` subject to `A x = b`, `x ≥ 0`.  Returns an optimal `x`, or `none` if the
problem is infeasible or unbounded. -/
def solve (A : Array (Array Rat)) (b : Array Rat) (c : Array Rat) (fuel : ℕ := 10000) :
    Option (Array Rat) := do
  let m := A.size
  let n := c.size
  -- normalise to b ≥ 0 and add artificial variables
  let rows := (Array.range m).map fun i =>
    let a := A[i]!
    let s : Rat := if b[i]! < 0 then -1 else 1
    let art := (Array.range m).map fun k => if k == i then (1 : Rat) else 0
    ((Array.range n).map fun k => s * a[k]!) ++ art ++ #[s * b[i]!]
  let t : Tableau := { rows, basis := (Array.range m).map (n + ·) }
  -- phase 1
  let cost1 := ((Array.range n).map fun _ => (0 : Rat)) ++ (Array.range m).map fun _ => (1 : Rat)
  let t ← run cost1 (fun _ => true) fuel t
  let infeas := (Array.range m).foldl (fun acc i =>
    if t.basis[i]! ≥ n then acc + t.rows[i]![n + m]! else acc) (0 : Rat)
  if infeas > 0 then none
  -- drive artificial variables out of the basis where possible
  let t := (Array.range m).foldl (fun (t : Tableau) i =>
    if t.basis[i]! ≥ n then
      match (List.range n).find? fun j => t.rows[i]![j]! != 0 with
      | some j => pivot t i j
      | none => t
    else t) t
  -- phase 2, artificial columns frozen
  let cost2 := c ++ (Array.range m).map fun _ => (0 : Rat)
  let t ← run cost2 (fun j => j < n) fuel t
  return (Array.range n).map fun j =>
    match (Array.range m).find? fun i => t.basis[i]! == j with
    | some i => t.rows[i]![n + m]!
    | none => 0

/-- Scale a non-negative rational vector to natural numbers (by the lcm of the
denominators). -/
def toNat (x : Array Rat) : List ℕ :=
  let l := x.foldl (fun acc q => Nat.lcm acc q.den) 1
  x.toList.map fun q => (q * (l : Rat)).num.toNat

/-- Scale a rational vector to integers. -/
def toInt (x : Array Rat) : List ℤ :=
  let l := x.foldl (fun acc q => Nat.lcm acc q.den) 1
  x.toList.map fun q => (q * (l : Rat)).num

end Simplex

end AsyncLean
