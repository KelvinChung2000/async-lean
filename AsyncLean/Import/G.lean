/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Import.Basic

/-!
# Importing STGs in the `.g` format

The `.g` (astg) format of Petrify and Workcraft:

```
.model celement
.inputs a b
.outputs c
.graph
a+ c+
b+ c+
c+ a- b-
a- c-
b- c-
c- a+ b+
.marking { <c-,a+> <c-,b+> }
.initial_state !a !b !c
.end
```

* `.inputs`, `.outputs`, `.internal` declare signals, `.dummy` declares dummy transitions;
* in `.graph`, each line lists a node followed by its successors; an arc between two
  transitions goes through an implicit place `<t,u>`, other nodes are explicit places;
* transitions are signal edges `z+` / `z-`, optionally with an instance suffix `z+/2`;
* `.marking { … }` lists the initially marked places (`p=2` for two tokens);
* `.initial_state` gives initial signal values (`a` or `a=1` for high, `!a` or `a=0` for
  low); signals not mentioned start low.

Comments start with `#`.  `stg_from_g name "file.g"` defines `name : Stg`;
`stg_from_g_text name "…"` reads the text directly.
-/

namespace AsyncLean

namespace Import.G

open Lean

/-- The raw contents of a `.g` file. -/
structure Raw where
  inputs : List String := []
  outputs : List String := []
  internals : List String := []
  dummies : List String := []
  arcs : List (String × String) := []
  marking : List String := []
  initial : List String := []

/-- Drop the last character. -/
def dropLast (s : String) : String := String.ofList s.toList.dropLast

/-- The node name without its instance suffix: `a+/2 ↦ a+`. -/
def baseName (t : String) : String := (t.splitOn "/").headD t

/-- The signal edge denoted by a transition name. -/
def parseEdge (sigs : List String) (t : String) : Option (ℕ × Bool) :=
  let b := baseName t
  if b.endsWith "+" then (indexOf? sigs (dropLast b)).map (·, true)
  else if b.endsWith "-" then (indexOf? sigs (dropLast b)).map (·, false)
  else none

/-- The tokens between `{` and `}`, with blanks inside `<…>` removed. -/
def markingTokens (line : String) : List String :=
  let inner := match line.splitOn "{" with
    | _ :: rest :: _ => (rest.splitOn "}").headD ""
    | _ => ""
  let (cs, _) := inner.toList.foldl (fun (acc : List Char × Bool) c =>
    if c == '<' then (acc.1 ++ [c], true)
    else if c == '>' then (acc.1 ++ [c], false)
    else if acc.2 && c.isWhitespace then acc
    else (acc.1 ++ [c], acc.2)) ([], false)
  words (String.ofList cs)

/-- Parse the lines of a `.g` file. -/
def parseRaw (content : String) : Except String Raw := do
  let mut raw : Raw := {}
  let mut inGraph := false
  for line in content.splitOn "\n" do
    let l := stripComment line "#"
    match words l with
    | [] => pure ()
    | kw :: rest =>
      if kw.startsWith "." then
        inGraph := false
        match kw with
        | ".inputs" => raw := { raw with inputs := raw.inputs ++ rest }
        | ".outputs" => raw := { raw with outputs := raw.outputs ++ rest }
        | ".internal" => raw := { raw with internals := raw.internals ++ rest }
        | ".dummy" => raw := { raw with dummies := raw.dummies ++ rest }
        | ".graph" => inGraph := true
        | ".marking" => raw := { raw with marking := markingTokens l }
        | ".initial_state" => raw := { raw with initial := rest }
        | _ => pure ()
      else if inGraph then
        raw := { raw with arcs := raw.arcs ++ rest.map fun t => (kw, t) }
      else
        throw s!"unexpected line outside .graph: {line}"
  return raw

/-- Build the STG. -/
def build (raw : Raw) : Except String Stg := do
  let sigs := raw.inputs ++ raw.outputs ++ raw.internals
  let signals := raw.inputs.map (·, SigKind.input) ++ raw.outputs.map (·, SigKind.output) ++
    raw.internals.map (·, SigKind.internal)
  let isT (t : String) : Bool := (parseEdge sigs t).isSome || raw.dummies.contains (baseName t)
  for t in (raw.arcs.flatMap fun a => [a.1, a.2]) do
    if (t.endsWith "~") then throw s!"toggle transitions are not supported: {t}"
  let nodes := (raw.arcs.flatMap fun a => [a.1, a.2]).eraseDups
  let trans := nodes.filter isT
  let explicitPlaces := nodes.filter (!isT ·)
  let implicitPlaces := (raw.arcs.filterMap fun a =>
    if isT a.1 && isT a.2 then some s!"<{a.1},{a.2}>" else none).eraseDups
  let places := explicitPlaces ++ implicitPlaces
  let pidx (p : String) : Except String ℕ :=
    match indexOf? places p with
    | some i => pure i
    | none => throw s!"unknown place {p}"
  let tidx (t : String) : ℕ := (indexOf? trans t).getD 0
  let mut pre : Array (List ℕ) := Array.replicate trans.length []
  let mut post : Array (List ℕ) := Array.replicate trans.length []
  for (a, b) in raw.arcs do
    if isT a && isT b then
      let p ← pidx s!"<{a},{b}>"
      post := post.modify (tidx a) (· ++ [p])
      pre := pre.modify (tidx b) (· ++ [p])
    else if isT a then
      post := post.modify (tidx a) (· ++ [← pidx b])
    else if isT b then
      pre := pre.modify (tidx b) (· ++ [← pidx a])
    else
      throw s!"arc between two places: {a} {b}"
  let mut init : Array ℕ := Array.replicate places.length 0
  for tok in raw.marking do
    let (p, k) := match tok.splitOn "=" with
      | [p, k] => (p, k.toNat?.getD 1)
      | _ => (tok, 1)
    let i ← pidx p
    init := init.modify i (· + k)
  let mut initVal : Array Bool := Array.replicate sigs.length false
  for tok in raw.initial do
    let (name, v) := if tok.startsWith "!" then (String.ofList (tok.toList.drop 1), false)
      else match tok.splitOn "=" with
        | [n, "0"] => (n, false)
        | [n, _] => (n, true)
        | _ => (tok, true)
    match indexOf? sigs name with
    | some i => initVal := initVal.set! i v
    | none => throw s!"unknown signal in .initial_state: {name}"
  let ptrans := (List.range trans.length).map fun i =>
    let t := trans.getD i ""
    { name := t, pre := pre.getD i [], post := post.getD i [], edge := parseEdge sigs t : PTrans }
  return { net := { places := places.length, trans := ptrans, init := init.toList }
           signals, initVal := initVal.toList }

/-- Parse a `.g` file. -/
def parse (content : String) : Except String Stg := do build (← parseRaw content)

end Import.G

open Lean Elab Command

/-- `stg_from_g name "file.g"` defines `name : Stg` from a `.g` file (path relative to the
current source file). -/
elab "stg_from_g " id:ident path:str : command => do
  let content ← readDesignFile path.getString
  match Import.G.parse content with
  | .ok stg =>
    let doc := s!"STG imported from `{path.getString}`."
    defineDesign id.getId (mkConst ``Stg) (toExpr stg) doc
  | .error e => throwError "stg_from_g: {e}"

/-- `stg_from_g_text name "…"` defines `name : Stg` from the text of a `.g` file. -/
elab "stg_from_g_text " id:ident text:str : command => do
  match Import.G.parse text.getString with
  | .ok stg => defineDesign id.getId (mkConst ``Stg) (toExpr stg) "STG imported from `.g` text."
  | .error e => throwError "stg_from_g_text: {e}"

end AsyncLean
