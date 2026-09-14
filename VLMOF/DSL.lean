import VLMOF.Source

namespace VLMOF.Source

/-! A small, lossless parser for the concrete declarative source language.
    Binding, lookup, and conformance deliberately remain outside this module. -/

inductive Tok where
  | word (s : String) (pos : Nat)
  | text (s : String) (pos : Nat)
  | number (s : String) (pos : Nat)
  | punct (s : String) (pos : Nat)
  | eof (pos : Nat)
  deriving Repr, DecidableEq

private def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'
private def isAlpha (c : Char) : Bool := c.isAlpha || c == '_'
private def isDigit (c : Char) : Bool := c.isDigit

partial def lexString : List Char → Nat → String → Except String (String × List Char × Nat)
  | [], p, _ => .error s!"unterminated string at {p}"
  | '"' :: cs, p, acc => .ok (acc, cs, p + 1)
  | '\\' :: [], p, _ => .error s!"unterminated escape at {p}"
  | '\\' :: c :: cs, p, acc =>
      match c with
      | '"' => lexString cs (p + 2) (acc.push '"')
      | '\\' => lexString cs (p + 2) (acc.push '\\')
      | 'n' => lexString cs (p + 2) (acc.push '\n')
      | 'r' => lexString cs (p + 2) (acc.push '\r')
      | 't' => lexString cs (p + 2) (acc.push '\t')
      | _ => .error s!"unsupported escape \\{c} at {p}"
  | c :: cs, p, acc => lexString cs (p + 1) (acc.push c)

partial def lex : List Char → Nat → List Tok → Except String (List Tok)
  | [], p, out => .ok (out.reverse ++ [.eof p])
  | c :: cs, p, out =>
      if isSpace c then lex cs (p + 1) out
      else if isAlpha c then
        let (tail, rest) := cs.span fun x => isAlpha x || isDigit x
        lex rest (p + tail.length + 1) (.word (String.ofList (c :: tail)) p :: out)
      else if isDigit c || (c == '-' && cs.head?.any isDigit) then
        let (tail, rest) := cs.span isDigit
        lex rest (p + tail.length + 1) (.number (String.ofList (c :: tail)) p :: out)
      else if c == '"' then
        match lexString cs (p + 1) "" with
        | .error e => .error e
        | .ok (s, rest, np) => lex rest np (.text s p :: out)
      else if c == ':' && cs.head? == some ':' then lex cs.tail! (p + 2) (.punct "::" p :: out)
      else if c == '.' && cs.head? == some '.' then lex cs.tail! (p + 2) (.punct ".." p :: out)
      else if "{}()[],;:*:@.".contains c then
        lex cs (p + 1) (.punct (String.singleton c) p :: out)
      else .error s!"unexpected character '{c}' at {p}"

private structure St where
  toks : Array Tok
  ix : Nat

private abbrev M (α : Type) := StateT St (Except String) α

private def here : M Nat := do
  let s ← get
  pure s.ix

private def peek : M Tok := do
  let s ← get
  pure (s.toks.getD s.ix (.eof 0))

private def advance : M Tok := do
  let t ← peek
  modify fun s => { s with ix := s.ix + 1 }
  pure t

private def skip : M Unit := do
  let _ ← advance
  pure ()

private def fail {α} (msg : String) : M α := throw msg

private def expectP (p : String) : M Unit := do
  match (← advance) with
  | .punct q _ => if q = p then pure () else fail s!"expected '{p}', found '{q}'"
  | t => fail s!"expected '{p}', found {repr t}"

private def expectWord (w : String) : M Unit := do
  match (← advance) with
  | .word q _ => if q = w then pure () else fail s!"expected keyword '{w}', found '{q}'"
  | t => fail s!"expected keyword '{w}', found {repr t}"

private def takeWord : M String := do
  match (← advance) with
  | .word s _ => pure s
  | t => fail s!"expected alias, found {repr t}"

private def takeString : M String := do
  match (← advance) with
  | .text s _ => pure s
  | t => fail s!"expected quoted display name, found {repr t}"

partial def qgo (xs : Name) : M Name := do
  let t ← peek
  match t with
  | .punct "::" _ => skip; qgo (xs ++ [← takeWord])
  | _ => pure xs

private def qualified : M Name := do
  let x ← takeWord
  qgo [x]

private def full (ctx : Name) (localName : String) : Name := ctx ++ [localName]

private def optionalAs (fallback : String) : M String := do
  let t ← peek
  match t with
  | .word "as" _ => skip; takeString
  | _ => pure fallback

private def parseUpper : M Upper := do
  match (← advance) with
  | .punct "*" _ => pure .unlimited
  | .number s _ =>
      match s.toNat? with
      | some n => pure (.finite n)
      | none => fail s!"malformed upper bound '{s}'"
  | t => fail s!"expected upper bound, found {repr t}"

private def parseMultiplicity : M Multiplicity := do
  expectP "["
  let lower ← match (← advance) with
    | .number s _ => match s.toNat? with | some n => pure n | none => fail s!"malformed lower bound '{s}'"
    | t => fail s!"expected lower bound, found {repr t}"
  expectP ".."
  let upper ← parseUpper
  expectP "]"
  let ordered ← match (← peek) with
    | .word "ordered" _ => skip; pure true
    | .word "unordered" _ => skip; pure false
    | t => fail s!"expected ordered or unordered, found {repr t}"
  let unique ← match (← peek) with
    | .word "unique" _ => skip; pure true
    | .word "nonunique" _ => skip; pure false
    | t => fail s!"expected unique or nonunique, found {repr t}"
  pure { lower := lower, upper := upper, isOrdered := ordered, isUnique := unique }

private def parseType : M ValueType := do
  let w ← takeWord
  match w with
  | "Boolean" => pure .boolean
  | "Integer" => pure .integer
  | "String" => pure .string
  | "enum" => .enumeration <$> qualified
  | _ => ValueType.reference <$> qgo [w]

private def parseProperty (ctx : Name) (owner : Owner) : M Property := do
  let a ← takeWord
  let name ← optionalAs a
  expectP ":"
  let ty ← parseType
  let mult ← parseMultiplicity
  let aggregation ← match (← peek) with
    | .word "composite" _ => skip; pure Aggregation.composite
    | _ => pure .none
  let isId ← match (← peek) with
    | .punct "(" _ => skip; expectWord "id"; expectP ")"; pure true
    | _ => pure false
  expectP ";"
  pure { alias := full ctx a, name, owner, type := ty, multiplicity := mult,
         aggregation, isId }

private structure Acc where
  model : Model
  snapshot : Instance

partial def parseClass (ctx : Name) (abstract : Bool) : M (Class × List Property) := do
  let a ← takeWord
  let name ← optionalAs a
  let supers ← match (← peek) with
    | .word "extends" _ =>
        skip; let rec go (xs : List Name) := do
          let q ← qualified
          let t ← peek
          if t == .punct "," 0 then skip; go (xs ++ [q]) else pure (xs ++ [q])
        go []
    | _ => pure []
  expectP "{"
  let owner : Owner := .class (full ctx a)
  let rec props (xs : List Property) := do
    let t ← peek
    match t with
    | .punct "}" _ => skip; pure xs.reverse
    | .word _ _ => props (xs.concat (← parseProperty (full ctx a) owner))
    | _ => fail s!"expected property or '}}', found {repr t}"
  let ps ← props []
  pure ({ alias := full ctx a, name, package := if ctx = [] then none else some ctx,
          isAbstract := abstract, directSupers := supers }, ps)

partial def parseEnum (ctx : Name) : M (Enumeration × List Literal) := do
  let a ← takeWord
  let name ← optionalAs a
  expectP "{"
  let rec lits (xs : List Literal) := do
    let t ← peek
    match t with
    | .punct "}" _ => skip; pure xs.reverse
    | .word _ _ =>
        let la ← takeWord; let ln ← optionalAs la; expectP ";"
        lits ({ alias := full (full ctx a) la, name := ln, enumeration := full ctx a } :: xs)
    | _ => fail s!"expected enumeration literal or '}}', found {repr t}"
  pure ({ alias := full ctx a, name, package := if ctx = [] then none else some ctx }, ← lits [])

partial def parseAssociation (ctx : Name) : M (Association × List Property) := do
  let a ← takeWord
  let name ← optionalAs a
  expectP "{"
  let owner := Owner.association (full ctx a)
  let rec ends (es : List Name) (ps : List Property) := do
    let t ← peek
    match t with
    | .word "end" _ =>
        skip; let ea ← takeWord; let en ← optionalAs ea; expectP ":"
        let ty ← qualified; let mult ← parseMultiplicity
        let aggregation ← match (← peek) with | .word "composite" _ => skip; pure Aggregation.composite | _ => pure .none
        expectP ";"
        ends (es ++ [full (full ctx a) ea])
          (ps ++ [{ alias := full (full ctx a) ea, name := en, owner, type := .reference ty,
                    multiplicity := mult, aggregation, isId := false }])
    | .word "ends" _ =>
        skip; let x ← qualified; expectP ","; let y ← qualified; expectP ";"
        expectP "}"; pure ({ alias := full ctx a, name, package := if ctx = [] then none else some ctx, ends := x :: y :: es }, ps)
    | _ => fail s!"expected association end or ends, found {repr t}"
  ends [] []

private def parseDecl (ctx : Name) : M Acc := do
  let abstract ← match (← peek) with | .word "abstract" _ => skip; pure true | _ => pure false
  match (← peek) with
  | .word "class" _ => skip; let (c, ps) ← parseClass ctx abstract; pure { model := { packages := [], classes := [c], properties := ps, associations := [], enumerations := [], literals := [] }, snapshot := { objects := [], observations := [] } }
  | .word "enum" _ => skip; let (e, ls) ← parseEnum ctx; pure { model := { packages := [], classes := [], properties := [], associations := [], enumerations := [e], literals := ls }, snapshot := { objects := [], observations := [] } }
  | .word "association" _ => skip; let (a, ps) ← parseAssociation ctx; pure { model := { packages := [], classes := [], properties := ps, associations := [a], enumerations := [], literals := [] }, snapshot := { objects := [], observations := [] } }
  | _ => fail "expected class, enum, or association declaration"

private def appendAcc (x y : Acc) : Acc :=
  { model := { packages := x.model.packages ++ y.model.packages, classes := x.model.classes ++ y.model.classes,
               properties := x.model.properties ++ y.model.properties, associations := x.model.associations ++ y.model.associations,
               enumerations := x.model.enumerations ++ y.model.enumerations, literals := x.model.literals ++ y.model.literals },
    snapshot := { objects := x.snapshot.objects ++ y.snapshot.objects, observations := x.snapshot.observations ++ y.snapshot.observations } }

partial def parsePackage (parent : Name) : M Acc := do
  let a ← takeWord; let name ← optionalAs a; expectP "{"; let path := full parent a
  let rec body (acc : Acc) := do
    let t ← peek
    match t with
    | .punct "}" _ => skip; pure acc
    | .word "package" _ => skip; body (appendAcc acc (← parsePackage path))
    | .word _ _ => body (appendAcc acc (← parseDecl path))
    | _ => fail s!"expected declaration or '}}', found {repr t}"
  let inner ← body { model := { packages := [], classes := [], properties := [], associations := [], enumerations := [], literals := [] }, snapshot := { objects := [], observations := [] } }
  pure { inner with model := { inner.model with packages := [{ alias := path, name, parent := if parent = [] then none else some parent }] ++ inner.model.packages } }

private def parseValue : M Value := do
  match (← advance) with
  | .word "true" _ => pure (.boolean true)
  | .word "false" _ => pure (.boolean false)
  | .number s _ => match s.toInt? with | some n => pure (.integer n) | none => fail s!"malformed integer '{s}'"
  | .text s _ => pure (.string s)
  | .punct "@" _ => .reference <$> qualified
  | .word w _ =>
      let q ← qgo [w]
      match q.reverse with
      | literal :: rest => pure (.enumeration rest.reverse [literal])
      | [] => fail "malformed enumeration value"
  | t => fail s!"expected value, found {repr t}"

partial def parseObject (snapshot : Instance) : M Instance := do
  let a ← takeWord; expectP ":"; let c ← qualified; expectP "{"
  let rec obs (xs : List Observation) := do
    let t ← peek
    match t with
    | .punct "}" _ => skip; pure xs
    | .word "observe" _ =>
        skip; let p ← qualified; expectP "="; expectP "["
        let rec vals (vs : List Value) := do
          let t ← peek
          if t == .punct "]" 0 then skip; pure vs.reverse
          else let v ← parseValue; let t ← peek; if t == .punct "," 0 then skip; vals (v :: vs) else vals (v :: vs)
        let vs ← vals []; expectP ";"; obs ({ object := [a], property := p, occurrences := vs } :: xs)
    | _ => fail s!"expected observe or '}}', found {repr t}"
  let os ← obs []
  pure { snapshot with objects := snapshot.objects.concat { alias := [a], classifier := c }, observations := snapshot.observations ++ os.reverse }

partial def parseTop : M Document := do
  let rec loop (acc : Acc) : M Acc := do
    match (← peek) with
    | .eof _ => pure acc
    | .word "package" _ => skip; loop (appendAcc acc (← parsePackage []))
    | .word "object" _ => skip; let s ← parseObject acc.snapshot; loop { acc with snapshot := s }
    | .word _ _ => loop (appendAcc acc (← parseDecl []))
    | t => fail s!"unsupported top-level token {repr t}"
  let a ← loop { model := { packages := [], classes := [], properties := [], associations := [], enumerations := [], literals := [] }, snapshot := { objects := [], observations := [] } }
  pure { model := a.model, snapshot := a.snapshot }

def parse (input : String) : Except String Document := do
  let ts ← lex input.toList 0 []
  let st := { toks := ts.toArray, ix := 0 }
  let (d, _) ← parseTop st
  pure d

namespace Examples

def nested : Except String Document := parse "package pets { package domestic { class Animal { name : String [0..1] unordered unique (id); } enum Mood { happy; } } class Person { pets : Pet [0..*] ordered nonunique; } association Ownership { end pet : Pet [0..1] unordered unique; end owner : Person [1..1] unordered unique composite; ends pets::pet, Ownership::owner; } }"

example : nested.isOk := by native_decide
example : (parse "class Broken { x : Integer [0..] unordered unique; }").isOk = false := by native_decide
example : (parse "class Broken { x : Integer [0..1] unordered unique; }").isOk := by native_decide

end Examples
end VLMOF.Source
