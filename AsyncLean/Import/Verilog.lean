/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Import.Basic

/-!
# Importing gate-level netlists from structural Verilog

The supported subset:

```verilog
module celem_impl (input a, input b, output c);
  wire x;
  assign c = a & b | c & (a | b);   // continuous assignment: one gate per signal
  nand g1 (x, a, b);                 // gate primitives: and or nand nor xor xnor not buf
  celem g2 (c, a, b);                // C-element (also c2, C2, c_element, muller_c)
endmodule
// async-lean init: c=0 x=1          // initial values (default 0)
```

Expressions use `~`/`!` (not), `&`, `^`, `|` (by increasing looseness), parentheses,
identifiers and the constants `0`, `1`, `1'b0`, `1'b1`.  Comments `//` and `/* */` are
allowed.  Buses, `always` blocks and named port connections are not supported.

* `gates_from_verilog name "file.v" for spec` defines `name : List Gate`, resolving signal
  names against the signals of the STG `spec` — the form used to check that a netlist
  implements an STG (`Stg.Conformant`);
* `circuit_from_verilog name "file.v"` defines a closed `name : Circuit` whose signals are
  the module's ports and wires (wires are internal); the environment must then be part of
  the netlist.
-/

namespace AsyncLean

namespace Import.Verilog

/-- Expressions over signal names. -/
inductive VExpr where
  | var (n : String)
  | const (b : Bool)
  | not (e : VExpr)
  | and (a b : VExpr)
  | or (a b : VExpr)
  | xor (a b : VExpr)
  deriving Inhabited

/-- A parsed module. -/
structure Module where
  inputs : List String := []
  outputs : List String := []
  wires : List String := []
  assigns : List (String × VExpr) := []
  init : List (String × Bool) := []

/-- Tokens. -/
inductive Tok where
  | ident (s : String)
  | num (b : Bool)
  | sym (c : Char)
  deriving Inhabited, BEq

/-- Extract `// async-lean init: …` pragmas. -/
def initPragmas (content : String) : List (String × Bool) :=
  (content.splitOn "\n").flatMap fun line =>
    match line.splitOn "async-lean init:" with
    | [_, rest] => (words rest).filterMap fun w => match w.splitOn "=" with
      | [n, "1"] => some (n, true)
      | [n, "0"] => some (n, false)
      | _ => none
    | _ => []

/-- Remove comments. -/
partial def stripComments : List Char → List Char
  | [] => []
  | '/' :: '/' :: rest => stripComments (rest.dropWhile (· != '\n'))
  | '/' :: '*' :: rest =>
    let rec skip : List Char → List Char
      | [] => []
      | '*' :: '/' :: r => r
      | _ :: r => skip r
    stripComments (skip rest)
  | c :: rest => c :: stripComments rest

/-- Tokenise. -/
partial def tokenize : List Char → Except String (List Tok)
  | [] => .ok []
  | c :: rest => do
    if c.isWhitespace then tokenize rest
    else if c.isAlpha || c == '_' then
      let n := (c :: rest).takeWhile fun d => d.isAlphanum || d == '_' || d == '$'
      return Tok.ident (String.ofList n) :: (← tokenize ((c :: rest).drop n.length))
    else if c.isDigit then
      let n := (c :: rest).takeWhile fun d => d.isAlphanum || d == '\''
      let s := String.ofList n
      let b ← match s with
        | "0" | "1'b0" | "1'h0" | "1'd0" => pure false
        | "1" | "1'b1" | "1'h1" | "1'd1" => pure true
        | _ => .error s!"unsupported constant {s}"
      return Tok.num b :: (← tokenize ((c :: rest).drop n.length))
    else if "(),;=&|^~!.#[]".contains c then
      if c == '[' then throw "buses are not supported"
      else return Tok.sym c :: (← tokenize rest)
    else throw s!"unexpected character {c}"

/-- Parser state. -/
abbrev P := StateT (List Tok) (Except String)

def peek : P (Option Tok) := do return (← get).head?
def next : P Tok := do
  match ← get with
  | t :: ts => set ts; return t
  | [] => throw "unexpected end of input"
def expectSym (c : Char) : P Unit := do
  match ← next with
  | .sym d => if c == d then pure () else throw s!"expected '{c}', found '{d}'"
  | .ident s => throw s!"expected '{c}', found {s}"
  | .num _ => throw s!"expected '{c}', found a constant"
def ident : P String := do
  match ← next with
  | .ident s => return s
  | _ => throw "expected an identifier"

mutual
partial def primary : P VExpr := do
  match ← next with
  | .ident s => return .var s
  | .num b => return .const b
  | .sym '(' => let e ← orExpr; expectSym ')'; return e
  | .sym '~' => return .not (← primary)
  | .sym '!' => return .not (← primary)
  | _ => throw "malformed expression"
partial def andExpr : P VExpr := do
  let mut e ← primary
  while (← peek) == some (.sym '&') do
    discard next; e := .and e (← primary)
  return e
partial def xorExpr : P VExpr := do
  let mut e ← andExpr
  while (← peek) == some (.sym '^') do
    discard next; e := .xor e (← andExpr)
  return e
partial def orExpr : P VExpr := do
  let mut e ← xorExpr
  while (← peek) == some (.sym '|') do
    discard next; e := .or e (← xorExpr)
  return e
end

/-- A comma-separated list of identifiers, up to `;`. -/
partial def identList : P (List String) := do
  let n ← ident
  match ← next with
  | .sym ',' => return n :: (← identList)
  | .sym ';' => return [n]
  | _ => throw "expected ',' or ';'"

/-- The expression of a gate primitive or C-element applied to inputs. -/
def gateExpr (kind : String) (out : String) (ins : List String) : Except String VExpr := do
  let vs := ins.map VExpr.var
  let fold (f : VExpr → VExpr → VExpr) : Except String VExpr :=
    match vs with
    | [] => .error s!"{kind} gate without inputs"
    | v :: rest => .ok (rest.foldl f v)
  match kind with
  | "and" => fold .and
  | "or" => fold .or
  | "xor" => fold .xor
  | "nand" => return .not (← fold .and)
  | "nor" => return .not (← fold .or)
  | "xnor" => return .not (← fold .xor)
  | "not" => match vs with | [v] => pure (.not v) | _ => .error "not gate takes one input"
  | "buf" => match vs with | [v] => pure v | _ => .error "buf gate takes one input"
  | _ => match vs with
    | [a, b] => pure (.or (.and a b) (.and (.var out) (.or a b)))
    | _ => .error "a C-element takes two inputs"

def primitives : List String :=
  ["and", "or", "xor", "nand", "nor", "xnor", "not", "buf", "celem", "c2", "C2", "c_element",
    "muller_c"]

/-- Parse module items until `endmodule`. -/
partial def items (m : Module) : P Module := do
  match ← next with
  | .ident "endmodule" => return m
  | .ident "input" => items { m with inputs := m.inputs ++ (← declList) }
  | .ident "output" => items { m with outputs := m.outputs ++ (← declList) }
  | .ident "wire" => items { m with wires := m.wires ++ (← identList) }
  | .ident "assign" => items { m with assigns := m.assigns ++ (← assignList) }
  | .ident k =>
    if primitives.contains k then
      -- optional instance name
      if (← peek) != some (.sym '(') then discard ident
      expectSym '('
      let out ← ident
      let mut ins : List String := []
      while (← peek) == some (.sym ',') do
        discard next; ins := ins ++ [← ident]
      expectSym ')'
      expectSym ';'
      match gateExpr k out ins with
      | .ok e => items { m with assigns := m.assigns ++ [(out, e)] }
      | .error err => throw err
    else throw s!"unsupported construct: {k}"
  | _ => throw "unexpected token in module body"
where
  declList : P (List String) := do
    if (← peek) == some (.ident "wire") || (← peek) == some (.ident "reg") then discard next
    identList
  assignList : P (List (String × VExpr)) := do
    let lhs ← ident
    expectSym '='
    let e ← orExpr
    match ← next with
    | .sym ',' => return (lhs, e) :: (← assignList)
    | .sym ';' => return [(lhs, e)]
    | _ => throw "expected ',' or ';' after an assignment"

/-- Parse an ANSI or plain port list `( … )`. -/
partial def ports (m : Module) (dir : Option String) : P Module := do
  match ← next with
  | .sym ')' => return m
  | .sym ',' => ports m dir
  | .ident "input" => ports m (some "input")
  | .ident "output" => ports m (some "output")
  | .ident "inout" => throw "inout ports are not supported"
  | .ident "wire" | .ident "reg" => ports m dir
  | .ident n =>
    match dir with
    | some "input" => ports { m with inputs := m.inputs ++ [n] } dir
    | some "output" => ports { m with outputs := m.outputs ++ [n] } dir
    | _ => ports m dir
  | _ => throw "malformed port list"

/-- Parse a module. -/
def parseModule (content : String) : Except String Module := do
  let toks ← tokenize (stripComments content.toList)
  let p : P Module := do
    match ← next with
    | .ident "module" => pure ()
    | _ => throw "expected 'module'"
    discard ident
    let m ← if (← peek) == some (.sym '(') then do discard next; ports {} none else pure {}
    expectSym ';'
    items m
  let (m, _) ← p.run toks
  return { m with init := initPragmas content }

/-- Translate an expression, resolving names. -/
def toBExpr (idx : String → Except String ℕ) : VExpr → Except String BExpr
  | .var n => return .var (← idx n)
  | .const b => return .const b
  | .not e => return .not (← toBExpr idx e)
  | .and a b => return .and (← toBExpr idx a) (← toBExpr idx b)
  | .or a b => return .or (← toBExpr idx a) (← toBExpr idx b)
  | .xor a b => return .xor (← toBExpr idx a) (← toBExpr idx b)

/-- Gates of a module, with signal indices taken from `signals`. -/
def gatesFor (m : Module) (signals : List String) (internalSig : String → Bool) :
    Except String (List Gate) :=
  let idx (n : String) : Except String ℕ :=
    match indexOf? signals n with
    | some i => .ok i
    | none => .error s!"unknown signal {n}"
  m.assigns.mapM fun (lhs, e) => do
    return { name := lhs, out := ← idx lhs, fn := ← toBExpr idx e, internal := internalSig lhs }

/-- A closed circuit from a module. -/
def circuit (m : Module) : Except String Circuit := do
  let signals := (m.inputs ++ m.outputs ++ m.wires ++ m.assigns.map (·.1)).eraseDups
  let gates ← gatesFor m signals fun n => !(m.inputs.contains n || m.outputs.contains n)
  let init := signals.map fun n => ((m.init.find? (·.1 == n)).map (·.2)).getD false
  return { signals := signals.length, gates, init }

end Import.Verilog

open Lean Elab Command Meta

unsafe def evalStgImpl (n : Name) : CommandElabM Stg := do
  liftTermElabM do evalConst Stg n

/-- Evaluate an `Stg` constant. -/
@[implemented_by evalStgImpl]
opaque evalStg (n : Name) : CommandElabM Stg

/-- `gates_from_verilog name "file.v" for spec` defines `name : List Gate` from a netlist,
resolving signal names against the signals of the STG `spec`. -/
elab "gates_from_verilog " id:ident path:str " for " spec:ident : command => do
  let content ← readDesignFile path.getString
  let specName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo spec
  let stg ← evalStg specName
  let names := stg.signals.map (·.1)
  match Import.Verilog.parseModule content >>= fun m =>
      Import.Verilog.gatesFor m names fun _ => false with
  | .ok gates =>
    for g in gates do
      if (stg.signals.getD g.out ("", .input)).2 == .input then
        throwError "gates_from_verilog: {g.name} is an input of the specification"
    let doc := s!"Gates imported from `{path.getString}`."
    defineDesign id.getId (toTypeExpr (List Gate)) (toExpr gates) doc
  | .error e => throwError "gates_from_verilog: {e}"

/-- `circuit_from_verilog name "file.v"` defines a closed `name : Circuit` from a netlist. -/
elab "circuit_from_verilog " id:ident path:str : command => do
  let content ← readDesignFile path.getString
  match Import.Verilog.parseModule content >>= Import.Verilog.circuit with
  | .ok c =>
    let doc := s!"Circuit imported from `{path.getString}`."
    defineDesign id.getId (mkConst ``Circuit) (toExpr c) doc
  | .error e => throwError "circuit_from_verilog: {e}"

end AsyncLean
