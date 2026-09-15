# Development

Keep changes small enough to explain and review. Explain a definition's modeling
purpose and source before presenting its proof. Document working behavior with
concrete examples; keep temporary plans and worker reports outside this repository.

Use the assigned worktree. Coordinate shared interface changes with the integrator.
Original specification downloads must stay unchanged. Archived implementations
are references to assess, not authoritative semantics. Preserve attribution when
adapting code. The language target is EMOF.

Run the checks relevant to the change and report their actual results. An independent
reviewer should form a source-based assessment before reading earlier review conclusions.

## Research code and documentation

Place definitions beside their mathematical purpose and nontrivial consequences.
Separate example fixtures from foundational model types. Organize modules by
concept and proof responsibility; do not add a new top-level file for every task.

Public definitions and theorems need useful docstrings: explain what a definition
means, why material assumptions are present, and the argument behind a nontrivial
result. A prose restatement of an identifier is not documentation. Private proof
groups should have enough context to follow their role in the public result.
Do not change theorem premises merely to simplify a refactor.

Keep commit hashes, run bookkeeping and review-stage labels in artifact records,
not the scientific argument. Automated checks establish only what they actually
test; they do not determine whether the author considers a revision ready for a
new review round.
