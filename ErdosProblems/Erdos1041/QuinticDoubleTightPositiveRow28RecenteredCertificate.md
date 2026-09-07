# Erdős 1041: recentered positive row-28 five-sheet certificate

## Exact theorem

This row continues the row-27 affine-predictor atlas on

\[
 \frac{510782638607598988776321604095665343002137748290698656005120847}
      {20132659200000000000000000000000000000000000000000000000000000000}
 \le t\le
 \frac{524204411407598988776321604095665343002137748290698656005120847}
      {20132659200000000000000000000000000000000000000000000000000000000},
\]

approximately \([0.025370848109702217,0.026037514776368887]\).  The
unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets there, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The center is the row-27 center plus \(1/2000\), with radius \(1/3000\).  The
exact checker is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row28_recentered.py
```

The replay proves strict Krawczyk self-maps, regular oriented carrier cells,
upper-half-plane disjointness and five-sheet exhaustion, five sign transports,
and five exact branch-overlap tests.  The overlap with row 27 is exactly
\(1/6000\), so rows 18--28 form a connected common-five-sheet interval.

The weakest displayed new bounds are

```text
|det D_(a,mu)(E1,E2)| > 76.7197445,
|Im(conj(p)q)|       > 0.0191379133,
upper-sheet separation > 0.0278880531,
weak-sheet excess       < -0.090422287.
```

All displayed decimals are readable approximations only; every acceptance
comparison in the checker is exact rational dyadic-disc arithmetic.

## Boundary

This additional cell asserts no sign beyond its right endpoint and does not
settle the remaining positive carrier, the selected-sheet cusp gap, the
complete double-tight atlas, `EX-W`, degree five, or unrestricted Erdős 1041.
