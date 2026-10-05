/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file LICENSE.
-/
import AsyncLean.Import.Basic

/-!
# Importing Petri nets in PNML

PNML is the ISO/IEC 15909-2 interchange format for Petri nets.  We read place/transition nets:
`<place id=…>` with an optional `<initialMarking><text>k</text></initialMarking>`,
`<transition id=…>` with an optional `<name><text>…</text></name>`, and
`<arc source=… target=…>` with an optional `<inscription><text>w</text></inscription>`.
Pages may be nested; other elements are ignored.

`pnet_from_pnml name "file.pnml"` defines `name : PNet`; transitions whose name appears in the
optional list `internal := ["…", …]` are marked internal.
-/

namespace AsyncLean

namespace Import.Xml

/-- A minimal XML tree. -/
inductive Node where
  | elem (tag : String) (attrs : List (String × String)) (children : List Node)
  | text (s : String)
  deriving Inhabited

/-- Decode the predefined entities. -/
def decode (s : String) : String :=
  ((((s.replace "&lt;" "<").replace "&gt;" ">").replace "&quot;" "\"").replace "&apos;" "'").replace
    "&amp;" "&"

/-- Skip characters up to and including the string `stop`. -/
partial def skipPast (stop : List Char) : List Char → List Char
  | [] => []
  | cs@(_ :: rest) => if stop.isPrefixOf cs then cs.drop stop.length else skipPast stop rest

/-- Read a name. -/
def readName (cs : List Char) : String × List Char :=
  let n := cs.takeWhile fun c => c.isAlphanum || c == '_' || c == '-' || c == ':' || c == '.'
  (String.ofList n, cs.drop n.length)

/-- Read the attributes of a tag, up to `>` or `/>`; returns whether the tag is self-closing. -/
partial def readAttrs (cs : List Char) (acc : List (String × String)) :
    Except String (List (String × String) × Bool × List Char) :=
  match cs.dropWhile Char.isWhitespace with
  | '/' :: '>' :: rest => .ok (acc.reverse, true, rest)
  | '>' :: rest => .ok (acc.reverse, false, rest)
  | [] => .error "unterminated tag"
  | cs =>
    let (n, rest) := readName cs
    if n.isEmpty then .error "malformed attribute" else
    match rest.dropWhile Char.isWhitespace with
    | '=' :: rest =>
      match rest.dropWhile Char.isWhitespace with
      | q :: rest =>
        if q == '"' || q == '\'' then
          let v := rest.takeWhile (· != q)
          readAttrs (rest.drop (v.length + 1)) ((n, decode (String.ofList v)) :: acc)
        else .error "unquoted attribute value"
      | [] => .error "unterminated attribute"
    | rest => readAttrs rest ((n, "") :: acc)

mutual

/-- Parse a sequence of nodes up to a closing tag (or the end). -/
partial def parseNodes (cs : List Char) (acc : List Node) :
    Except String (List Node × List Char) :=
  match cs with
  | [] => .ok (acc.reverse, [])
  | '<' :: '/' :: _ => .ok (acc.reverse, cs)
  | '<' :: '?' :: rest => parseNodes (skipPast ['?', '>'] rest) acc
  | '<' :: '!' :: '-' :: '-' :: rest => parseNodes (skipPast ['-', '-', '>'] rest) acc
  | '<' :: '!' :: rest => parseNodes (skipPast ['>'] rest) acc
  | '<' :: rest => do
    let (node, rest) ← parseElem rest
    parseNodes rest (node :: acc)
  | _ =>
    let t := cs.takeWhile (· != '<')
    let s := (String.ofList t).trimAscii.toString
    parseNodes (cs.drop t.length) (if s.isEmpty then acc else .text (decode s) :: acc)

/-- Parse an element after its `<`. -/
partial def parseElem (cs : List Char) : Except String (Node × List Char) := do
  let (tag, rest) := readName cs
  let (attrs, selfClosing, rest) ← readAttrs rest []
  if selfClosing then return (.elem tag attrs [], rest)
  let (children, rest) ← parseNodes rest []
  match rest with
  | '<' :: '/' :: rest =>
    let (tag', rest) := readName rest
    if tag' != tag then throw s!"mismatched closing tag {tag'} for {tag}"
    return (.elem tag attrs children, skipPast ['>'] rest)
  | _ => throw s!"unclosed element {tag}"

end

/-- Parse a document. -/
def parse (s : String) : Except String (List Node) := do
  let (nodes, _) ← parseNodes s.toList []
  return nodes

/-- The local part of a (possibly prefixed) tag. -/
def localName (tag : String) : String := (tag.splitOn ":").getLast!

/-- All elements with the given tag, in document order. -/
partial def findAll (tag : String) : Node → List Node
  | n@(.elem t _ cs) => (if localName t == tag then [n] else []) ++ cs.flatMap (findAll tag)
  | .text _ => []

/-- The value of an attribute. -/
def attr (n : Node) (a : String) : Option String :=
  match n with
  | .elem _ attrs _ => (attrs.find? (·.1 == a)).map (·.2)
  | .text _ => none

/-- The direct children with a given tag. -/
def children (n : Node) (tag : String) : List Node :=
  match n with
  | .elem _ _ cs => cs.filter fun c => match c with
    | .elem t _ _ => localName t == tag
    | .text _ => false
  | .text _ => []

/-- The concatenated text of a node. -/
partial def textOf : Node → String
  | .text s => s
  | .elem _ _ cs => String.join (cs.map textOf)

/-- The text of the `<text>` child of the first child with the given tag. -/
def childText (n : Node) (tag : String) : Option String :=
  match children n tag with
  | c :: _ => some ((match children c "text" with
      | t :: _ => textOf t
      | [] => textOf c).trimAscii.toString)
  | [] => none

end Import.Xml

namespace Import.Pnml

open Import.Xml

/-- Build a Petri net from a PNML document. -/
def build (doc : List Node) (internal : List String) : Except String PNet := do
  let all (tag : String) := doc.flatMap (findAll tag)
  let places := all "place"
  let trans := all "transition"
  let arcs := all "arc"
  let pid (n : Node) := (attr n "id").getD ""
  let pids := places.map pid
  let tids := trans.map pid
  let mut pre : Array (List ℕ) := Array.replicate trans.length []
  let mut post : Array (List ℕ) := Array.replicate trans.length []
  for a in arcs do
    let src := (attr a "source").getD ""
    let tgt := (attr a "target").getD ""
    let w := ((childText a "inscription").bind String.toNat?).getD 1
    match indexOf? pids src, indexOf? tids tgt, indexOf? tids src, indexOf? pids tgt with
    | some p, some t, _, _ => pre := pre.modify t (· ++ List.replicate w p)
    | _, _, some t, some p => post := post.modify t (· ++ List.replicate w p)
    | _, _, _, _ => throw s!"arc {src} → {tgt} must connect a place and a transition"
  let init := places.map fun p => ((childText p "initialMarking").bind String.toNat?).getD 0
  let ptrans := (List.range trans.length).map fun i =>
    let t := trans.getD i default
    let name := (childText t "name").getD (pid t)
    { name, pre := pre.getD i [], post := post.getD i [], internal := internal.contains name :
      PTrans }
  return { places := places.length, trans := ptrans, init }

/-- Parse a PNML document. -/
def parse (content : String) (internal : List String) : Except String PNet := do
  build (← Xml.parse content) internal

end Import.Pnml

open Lean Elab Command

/-- `pnet_from_pnml name "file.pnml"` (optionally `internal := ["t1", …]`) defines
`name : PNet` from a PNML file (path relative to the current source file). -/
syntax (name := pnetFromPnml) "pnet_from_pnml " ident str
  (" (" &"internal" " := " "[" str,* "]" ")")? : command

elab_rules : command
  | `(pnet_from_pnml $id $path $[ (internal := [$ints,*])]?) => do
    let content ← readDesignFile path.getString
    let internal := (ints.map fun xs => xs.getElems.toList.map (·.getString)).getD []
    match Import.Pnml.parse content internal with
    | .ok net =>
      let doc := s!"Petri net imported from `{path.getString}`."
      defineDesign id.getId (mkConst ``PNet) (toExpr net) doc
    | .error e => throwError "pnet_from_pnml: {e}"

end AsyncLean
