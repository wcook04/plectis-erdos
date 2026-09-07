# Proposed scalar and algebraic Lean components — UNCOMPILED

Copy `BlaschkeSectorConnector.lean` to `ErdosProblems/Erdos1041/` only in a complete checkout with the pinned Mathlib environment. It imports `Mathlib`. A suitable local check is:

```sh
lake env lean ErdosProblems/Erdos1041/BlaschkeSectorConnector.lean
```

This command was not run in this session: neither Lean nor Lake was installed. Treat possible elaboration or tactic failures as unresolved, not as a successful formal return. There are no `sorry` declarations or custom axioms in the proposed file.

The file states the norm-defect identity, a positivity and disc-retention implication, the quadratic and power pullbacks, the pointwise amplitude inequality, integrated scalar length consolidation, a reverse-triangle barrier component, the exact degree-24 rational comparisons, and the scalar comparison used by the already registered scaling consequence.

It does not formalise the analytic choice of square root, integration along the three-piece path, the sector separation argument, continuity of roots, or the infimum defining Lambda. Those are ordinary arguments in the report. In particular, the Lean scalar length consumer takes a supplied bound; it does not manufacture its geometric hypothesis. The printed-axiom commands are targets for a future local build, not saved outputs of a build made here.
