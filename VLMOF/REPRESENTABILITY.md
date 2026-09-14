# Source representability boundary

`Representability.lean` states the exact finite Core image of the symbolic source
language. The statement is deliberately narrower than “every Core record has source
text.” Raw Core records retain malformed and unnamed forms for diagnostics, while the
source language assigns qualified symbolic aliases and the binder allocates numeric
identities itself.

## Exact direct image

`canonicalSchema` and `canonicalSnapshot` are total structural functions. They do not
call `bindModel`, `bindInstance`, `elaborate`, or the checker. They copy source fields,
replace every resolved alias by the selected source-list position, and allocate each
declaration and object at its own list position.

The following theorems identify the executable result with those functions:

- `bindModel_eq_canonical`
- `bindInstance_eq_canonical`
- `elaborate_eq_canonical`

The last theorem uses `SourceSatisfies`, the independently defined symbolic semantics,
as a sufficient condition. It produces one specified Core pair rather than an
existentially chosen elaboration result.

`CanonicalSchemaIds` and `CanonicalSnapshotIds` expose the allocation invariant as
equalities with `[0, ..., length - 1]` for every typed declaration store and the object
store. The `noncanonicalSchema_not_directly_representable` and
`noncanonicalSnapshot_not_directly_representable` lemmas show that a Core artifact with
different stored IDs is not literally a binder output.

Every source declaration also has a display spelling, so a direct image has `some name`
in every metadata-name field. `FullyNamedSchema`, `bindModel_fullyNamed`, and
`unnamedClass_not_directly_representable` make this restriction explicit. An unnamed
Core declaration is a supported raw diagnostic form, but it has no direct source image.

## Typed identity renaming

`TypedIdRenaming` contains seven separate bijections: packages, classes, properties,
associations, enumerations, literals, and objects. `renameSchema` and `renameSnapshot`
apply them to declarations and every reference, including owners, types, association
ends, classifiers, enumeration occurrences, and object references. Keeping these maps
separate rules out accidental identification of values from different identity spaces.

`RepresentableModuloIds schema snapshot` means that the pair is obtained by applying
such a typed renaming to the canonical image of a document satisfying
`SourceSatisfies`. This is the formal represented domain. It does not claim that an
arbitrary Core pair is representable.

## Core-to-source reification

`CoreAliasAssignment` supplies qualified aliases independently of optional Core
metadata. `reifyModel`, `reifyInstance`, and `reifyDocument` then translate a Core pair
to symbolic source records. At schema level, `ModelReificationConditions` requires
only `ModelWellFormed` for the constructed source model and the structural schema
round trip. `model_reification_binds` proves that the actual binder returns the exact
requested schema, and `model_reification_target_wellFormed` derives its Core validity.
Neither theorem assumes binding success.

`ReificationConditions` is the corresponding full-document sufficient domain:

1. the constructed document satisfies the declarative source semantics;
2. its structural canonical schema is the requested schema;
3. its structural canonical snapshot is the requested snapshot.

`reification_elaborates` proves that the actual executable elaborator returns that exact
Core pair. No elaboration-success premise is stored in `ReificationConditions`.
`reification_target_conforms` separately derives Core conformance.

The round-trip equations expose rather than conceal the remaining obligations on an
alias assignment: declarations must have canonical typed IDs, aliases must resolve to
those positions, qualification must agree with package and ownership structure, and
metadata names must be present. The source-meaning field additionally requires the
snapshot observations and values to satisfy the symbolic constraints.

This module does not prove that every named conforming Core graph admits qualified
aliases. In particular, constructing globally unique lexical paths for arbitrary nested
package graphs is a separate finite naming theorem. The present result supplies a
checked reifier for explicit assignments and records the exact counterexamples (`none`
names and noncanonical direct IDs) instead of claiming blanket Core coverage.
