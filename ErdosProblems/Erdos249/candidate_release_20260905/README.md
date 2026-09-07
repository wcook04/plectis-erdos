# Candidate-ahead copies, 2026-09-06

Byte-identical copies from the release candidate at
`public-source-redacted://release-final-20260905`, branch
`release/final-20260905`, HEAD `8a28b2521e`. Both files have same-named
counterparts one directory up that this pass did not overwrite, so the union
is kept here with the disposition written down.

| file | this tree, one level up | release candidate | disposition |
|---|---|---|---|
| `TotientStrictPrimeEscape.lean` | 72 lines, 3 declarations: `DTWNaturalPrimeTailOrbitStrictGap`, `naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap`, `irrational_totient_series_of_naturalPrimeTailOrbitStrictGap` | 530 lines, 25 declarations; adds the whole tail-orbit phase calculus and the exact equivalence `totientTailOrbitCofinalNonpositive_iff_irrational` at line 445 | union, candidate is strictly ahead |
| `PeriodMultipleEscape.lean` | 475 lines | 566 lines; adds `pureDyadicEndpointError_add`, `exists_late_pureDyadicEndpointError_oneThird_excursion`, `exists_late_pureDyadicEndpointError_oneThird`, `exists_late_pureDyadicEndpointError_abs_gt`, and moves `totient_series_ne_rat_of_den_dvd_127_300` from line 453 to line 534 | union, candidate is strictly ahead |

The only other difference across every shared `#249` module is the namespace
rename `Erdos257PeriodNoncollapse` in this tree against `Erdos249257` in the
release candidate, which is mechanical.

## What must happen next

Merge the candidate's extra declarations into the files one level up, under
this tree's namespace, then delete this directory. Until that merge lands,
citing `TotientStrictPrimeEscape.lean:445` against this tree resolves to a
line inside a 72-line file and means nothing; the coordinate is valid only
against the release candidate or against the copy here.
