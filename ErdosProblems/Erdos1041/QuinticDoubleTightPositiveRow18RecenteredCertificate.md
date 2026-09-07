# Erdős 1041: recentered positive row-18 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{144918243243754009918772429049078389634621647}
      {7864320000000000000000000000000000000000000000}
 \le t\le
 \frac{150161123243754009918772429049078389634621647}
      {7864320000000000000000000000000000000000000000},
\]

approximately

```text
[0.018427307541370903, 0.01909397420803757],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row18_recentered.py
```

## Certificate

The cell is centered at

\[
 c_{18}=
 \frac{49179894414584669972924143016359463211540549}
      {2621440000000000000000000000000000000000000000}
\]

and has radius `1/3000`.  For every one of the five upper sheets, the checker
proves an exact two-variable affine-predictor Krawczyk self-map, a nonzero
carrier Jacobian, strict wall-orientation separation, upper-half-plane
containment, and pairwise root-tube separation.  The exact carrier theorem
then makes the five tubes exhaustive.

The weak sheet is recentered and paid by exact positive-gradient transport.
The other four sheets use exact one-cell parameter hulls.  The resulting
excess upper bounds are

```text
-0.038949399,
-0.823813902,
-0.474889409,
-1.236006069,
-1.005248374.
```

The weakest carrier gates are

```text
|det D_(a,mu)(E1,E2)| > 79.6550504,
|Im(conj(p) q)|      > 0.0105981122,
upper-sheet separation > 0.020192072.
```

All displayed decimals are readable approximations only; every acceptance
comparison uses exact rational dyadic-disc bounds.

The left endpoint lies strictly below the former exact endpoint

\[
 T_{17}=
 \frac{12116785580404918688981310598233490936176657}
      {655360000000000000000000000000000000000000000}.
\]

The overlap width is exactly

\[
 \frac{483183721105014349003298129723501599498237}
      {7864320000000000000000000000000000000000000000}>0.
\]

Five fixed-parameter Krawczyk overlap tests identify the new sheets with the
five sheets in the final cell of
`QuinticDoubleTightPositiveDecadeContinuation.md`.  Thus the two exact
certificates have one connected common-five-sheet union, ending at the new
right endpoint above.

## Boundary

This is one recentered positive carrier cell.  It asserts no sign beyond its
exact right endpoint and does not certify the intervening selected-sheet-only
region near the cusp, the remaining positive carrier, any negative regular
interval, the complete double-tight atlas, `EX-W`, degree five, or unrestricted
Erdős 1041.
