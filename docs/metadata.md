# Metadata pilot

`MetadataPilot.lean` represents class and scalar-attribute descriptions as ordinary
objects. The fixed vocabulary has ClassDescription and AttributeDescription classes,
eight ordinary properties, and a three-literal scalar-type enumeration. The common
snapshot checker validates these descriptions before interpretation. There is no
special acceptance branch for metadata.

The interpreter allocates class/property identities from descriptor object identities,
reads names, owners, types, finite bounds, ordering and uniqueness from the same
occurrence store, and constructs a schema. The fixture describes `Person.active :
Boolean [0..1]`; the interpreted schema validates a separate Person instance. Both
metadata conformance and application conformance are proved through the ordinary
checker correspondence and kernel reduction.

The general `text_ok_iff` theorem characterizes exact single-String observation;
`interpret_input_conforms` proves interpreted inputs passed common metadata
conformance; `interpretChecked_wellFormed` proves checked outputs satisfy the common
schema predicate. A dangling owner is rejected at metadata conformance. Reversed
integer bounds are well-typed metadata but fail interpreted schema validity. This
separates structural metadata typing from external semantic obligations.

Scope: concrete root classes and Boolean/Integer/String attributes with finite
nonnegative bounds (creation-valid positive upper checked afterward). This pilot
omits metadata for packages, inheritance, associations/reference-valued properties,
unlimited bounds, operations, reflection and self-description. It does not prove
that every conforming metadata snapshot expresses a valid schema, nor that the whole
EMOF metamodel describes itself. Empty display names and cross-field bound relations
remain constraints of the interpreted schema checker. No metadata vocabulary change
is inferred or performed by the interpreter.
