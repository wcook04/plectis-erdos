# Erdős 1041: recentered positive row-19 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{30016426431457080053185892813159226654366680929}
      {1572864000000000000000000000000000000000000000000}
 \le t\le
 \frac{31065002431457080053185892813159226654366680929}
      {1572864000000000000000000000000000000000000000000},
\]

approximately

```text
[0.01908392997198555, 0.019750596638652217],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row19_recentered.py
```

## Certificate

The cell is centered at

\[
 c_{19}=
 \frac{10180238143819026684395297604386408884788893643}
      {524288000000000000000000000000000000000000000000}
\]

and has radius `1/3000`.  The checker first replays the row-18 source
certificate, then uses its five exact carrier tubes as scouts for five new
independent affine-predictor Krawczyk cells.  On the new cells it proves a
nonzero carrier Jacobian, strict wall-orientation separation,
upper-half-plane containment, pairwise tube separation, and exhaustion by the
exact five-sheet carrier theorem.

The weak sheet is paid by exact recentered positive-gradient transport.  The
other four sheets use exact one-cell parameter hulls.  The resulting excess
upper bounds are

```text
-0.045197323,
-0.845449344,
-0.483217071,
-1.236001713,
-1.005391512.
```

The weakest new carrier gates are

```text
|det D_(a,mu)(E1,E2)| > 79.374047,
|Im(conj(p) q)|      > 0.0113982924,
upper-sheet separation > 0.0209220057.
```

All displayed decimals are readable approximations only.  Every acceptance
comparison uses exact rational dyadic-disc arithmetic.

The left endpoint lies strictly below the exact row-18 endpoint

\[
 R_{18}=
 \frac{150161123243754009918772429049078389634621647}
      {7864320000000000000000000000000000000000000000}.
\]

Their overlap width is exactly

\[
 \frac{15798217293721930568592996656451272557648471}
      {1572864000000000000000000000000000000000000000000}>0.
\]

Five fixed-parameter Krawczyk overlap tests identify the new sheets with the
five row-18 sheets.  Thus the two recentered certificates form a connected
common-five-sheet union ending at the new right endpoint above.

## Boundary

This is one additional positive carrier cell.  It asserts no sign beyond its
exact right endpoint and does not certify the selected-sheet-only gap near the
cusp, the remaining positive carrier, any negative regular interval, the
complete double-tight atlas, `EX-W`, degree five, or unrestricted Erdős 1041.
