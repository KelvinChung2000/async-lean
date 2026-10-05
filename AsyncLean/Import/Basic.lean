/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Stg.Concrete
import AsyncLean.Circuit.Basic

/-!
# Infrastructure for importing designs

Importers parse a design at elaboration time and define an ordinary Lean constant holding it
as a literal term (`defineDesign`).  The parsers are not verified and need not be: every
theorem is stated about the defined constant, whose value can be inspected with `#print`.
-/

namespace AsyncLean

open Lean Elab Command Meta

/-! ### Literals for design data -/

instance : ToExpr SigKind where
  toTypeExpr := mkConst ``SigKind
  toExpr
    | .input => mkConst ``SigKind.input
    | .output => mkConst ``SigKind.output
    | .internal => mkConst ``SigKind.internal

instance : ToExpr PTrans where
  toTypeExpr := mkConst ``PTrans
  toExpr t := mkAppN (mkConst ``PTrans.mk)
    #[toExpr t.name, toExpr t.pre, toExpr t.post, toExpr t.internal, toExpr t.edge]

instance : ToExpr PNet where
  toTypeExpr := mkConst ``PNet
  toExpr n := mkAppN (mkConst ``PNet.mk) #[toExpr n.places, toExpr n.trans, toExpr n.init]

instance : ToExpr Stg where
  toTypeExpr := mkConst ``Stg
  toExpr n := mkAppN (mkConst ``Stg.mk) #[toExpr n.net, toExpr n.signals, toExpr n.initVal]

/-- Literal syntax tree of a Boolean expression. -/
def BExpr.toExprAux : BExpr → Expr
  | .var i => mkApp (mkConst ``BExpr.var) (toExpr i)
  | .const b => mkApp (mkConst ``BExpr.const) (toExpr b)
  | .not e => mkApp (mkConst ``BExpr.not) e.toExprAux
  | .and a b => mkApp2 (mkConst ``BExpr.and) a.toExprAux b.toExprAux
  | .or a b => mkApp2 (mkConst ``BExpr.or) a.toExprAux b.toExprAux
  | .xor a b => mkApp2 (mkConst ``BExpr.xor) a.toExprAux b.toExprAux

instance : ToExpr BExpr := ⟨BExpr.toExprAux, mkConst ``BExpr⟩

instance : ToExpr Gate where
  toTypeExpr := mkConst ``Gate
  toExpr g := mkAppN (mkConst ``Gate.mk) #[toExpr g.name, toExpr g.out, toExpr g.fn, toExpr g.internal]

instance : ToExpr Circuit where
  toTypeExpr := mkConst ``Circuit
  toExpr c := mkAppN (mkConst ``Circuit.mk) #[toExpr c.signals, toExpr c.gates, toExpr c.init]

/-! ### Defining imported designs -/

/-- Define `name : type := value` as a reducible definition (so that, as with `abbrev`, the
sizes of the design unfold during instance search). -/
def defineDesign (name : Name) (type value : Expr) (doc : String) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let fullName := ns ++ name
  liftTermElabM do
    addAndCompile <| .defnDecl {
      name := fullName, levelParams := [], type, value
      hints := .abbrev, safety := .safe }
    setReducibleAttribute fullName
    addDocStringCore fullName doc
  logInfo m!"defined {fullName}"

/-- Read a file, resolving relative paths against the directory of the current source file. -/
def readDesignFile (path : String) : CommandElabM String := do
  let fp : System.FilePath := path
  let full ← if fp.isAbsolute then pure fp else do
    let here : System.FilePath := (← getFileName)
    pure ((here.parent.getD ".") / fp)
  unless ← full.pathExists do
    throwError "file not found: {full}"
  IO.FS.readFile full

/-! ### Small parsing helpers -/

/-- Split on whitespace, dropping empty pieces. -/
def words (s : String) : List String :=
  let ws := s.toList.foldr (fun c (acc : List (List Char)) =>
    if c.isWhitespace then [] :: acc
    else match acc with
      | [] => [[c]]
      | w :: rest => (c :: w) :: rest) [[]]
  ws.filterMap fun w => if w.isEmpty then none else some (String.ofList w)

/-- Remove everything from `marker` to the end of the line. -/
def stripComment (line marker : String) : String :=
  match line.splitOn marker with
  | first :: _ => first
  | [] => line

/-- Index of an element in a list. -/
def indexOf? {α : Type} [BEq α] (l : List α) (a : α) : Option ℕ := l.findIdx? (· == a)

end AsyncLean
