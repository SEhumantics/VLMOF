# Writing a source model

This document describes the concrete syntax accepted by `check-dsl`. Start with
a class and an object that observes one of its properties:

```text
class Book {
  inPrint : Boolean [0..1] unordered unique;
}
object book : Book {
  observe Book::inPrint = [false];
}
```

The value is explicitly present. Replacing `[false]` with `[]` denotes absence;
the optional bound permits either. Omitting the observation row entirely is a
different input: snapshots must give a row for every applicable property, including
an empty row for an absent optional value. Run a saved document with
`lake exe vlmof check-dsl path/to/model.dsl`.

## Grammar

The parser accepts whitespace separated declarations. Qualified names use `::`;
binding aliases are prefixed by enclosing package and member aliases. `as
"display"` changes only display metadata.

```text
document := { package | declaration | object }
package := "package" alias ["as" string] "{" { package | declaration } "}"
declaration := ["abstract"] class | enum | association
class := "class" alias ["as" string] ["extends" qualified {"," qualified}] "{" { property } "}"
enum := "enum" alias ["as" string] "{" { alias ["as" string] ";" } "}"
property := alias ["as" string] ":" type multiplicity ["composite"] ["(" "id" ")"] ";"
association := "association" alias ["as" string] "{" { end } "ends" qualified "," qualified ";" "}"
end := "end" alias ["as" string] ":" qualified multiplicity ["composite"] ";"
multiplicity := "[" nat ".." (nat | "*") "]" ("ordered" | "unordered") ("unique" | "nonunique")
type := "Boolean" | "Integer" | "String" | "enum" qualified | qualified
object := "object" alias ":" qualified "{" { "observe" qualified "=" "[" [ value {"," value} ] "]" ";" } "}"
value := "true" | "false" | signedNat | string | "@" qualified | qualified "::" alias
```

Malformed numbers and string escapes, missing punctuation, unsupported keywords,
abstract enums/associations, and malformed value separators produce positioned
`Except String` diagnostics. Association end membership is retained as a pair;
binding performs reference and ownership checks later.

## Semantic guarantee

The parser returns `Source.Document`; source satisfaction is independently defined
in [Source.Semantics](../VLMOF/Source/Semantics.lean).
[Source.Adequacy](../VLMOF/Source/Adequacy.lean)
proves `sourceSatisfies_iff_exists_accepted`: for a `LexicallyAdmissible` document,
source satisfaction holds exactly when actual elaboration succeeds and its Core
snapshot is accepted. Lexical admissibility requires nonempty, XML-valid declaration
and object aliases. It does not assume that declarations or observations conform.
The fixed-result theorem `sourceSatisfies_iff_accepted` additionally takes the actual
successful elaboration result.

This theorem starts at the AST, not the source bytes. Parsing and the claim that a
particular parsed document meets the lexical condition remain separate obligations.
Alias spelling is distinct from display metadata and from allocated Core identity.
