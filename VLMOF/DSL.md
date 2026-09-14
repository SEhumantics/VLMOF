# Declarative DSL grammar

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
