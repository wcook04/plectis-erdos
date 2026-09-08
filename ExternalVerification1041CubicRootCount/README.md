# Normalized cubic root count

For a complex number b satisfying |1 − b³/2| ≥ 1, the polynomial z³ − (3/2)bz² + 1 has two distinct roots in the closed unit disc. The proof applies the elementary Schur inequality to reciprocals of two hypothetical exterior roots; Vieta then forces |1 − b³/2| < 1. A repeated root would force the same expression to vanish.

The Challenge imports only Mathlib and states this exact conclusion. The Solution transports `ErdosProblems.Erdos1041.PaperCubicSchur.cubic_root_count` from the substantive source in the same repository. It does not claim a path construction, a length bound, the general-degree Erdős problem, or novelty.

The focused wrapper build and axiom audit passed on 8 September 2026. `AxiomAudit.lean` reports only `propext`, `Classical.choice`, and `Quot.sound` for the selected theorem, matching `comparator.json`. Supported-runner Comparator replay remains pending. Registry submission awaits a verified wrapper publication commit and operator approval.
