# Erdős #1049: Bézout–Plücker tail collapse

This package exposes a source-current conditional improvement to the endpoint-
jet collision mechanism. For rows `w n = (A n, B n)` over a commutative ring,
unit second coordinates and vanishing adjacent minors force every pairwise
minor to vanish. A determinant-one Bézout shear then places the whole family
on one line, so binary selector sums occupy at most `card R` values rather than
`(card R)^2`.

At the modulus `N = 2^S * 3^R`, with `R > 0`, this reduces the sufficient
selector width from the ambient two-channel threshold `2*S + 4*R` to
`S + 2*R`. The strongest selected theorem states that any tail satisfying the
unit-coordinate and adjacent-minor hypotheses has two distinct selectors on
`Fin k` with the same two-coordinate sum whenever `S + 2*R ≤ k`.

The antecedent is substantial and remains open for the actual q-Apéry or
Zudilin tail rows. The package proves no analytic-remainder nonvanishing or
decay, no irrationality at `3/2`, and no solution of Erdős #1049. It is a
conditional compression theorem, not a replacement for the unconditional
ambient four-jet collision or its bounded-fibre escape condition.

`Challenge.lean` imports only Mathlib and restates four exact source
interfaces from `ErdosProblems/Erdos1049/BezoutPluckerJets.lean`.
`Solution.lean` transports those declarations. The deliberate negative adds
an extra argument to the strongest endpoint and must be rejected by type.
Both configurations enable NanoDa and permit exactly `propext`, `Quot.sound`,
and `Classical.choice`.

This is a Palomar candidate package, not an acceptance, review, novelty,
publication, or submission claim. Project registration and terminal replay
remain separate integration steps.

Focused Lean replay was attempted through the guarded build on 2026-08-31 and
was deferred before compilation at the low-disk firewall: 1,369,374,720 bytes
free versus the 17,179,869,184-byte minimum. The exact re-entry condition is
to restore that floor and ensure no active owner holds the project build key.
