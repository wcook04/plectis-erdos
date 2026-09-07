# Erdős 1041: recentered positive row-25 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{36971360140929392065196643144116378616908976118619705043865829}
      {1577058304000000000000000000000000000000000000000000000000000000}
 \le t\le
 \frac{38313537420929392065196643144116378616908976118619705043865829}
      {1577058304000000000000000000000000000000000000000000000000000000},
\]

approximately

```text
[0.023443242426203534, 0.02429430625599077],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row25_recentered.py
```

## Certificate

The cell is centered at

\[
 c_{25}=
 \frac{800903165551689192876524322215242098232105874864249043486507}
      {33554432000000000000000000000000000000000000000000000000000000}
\]

and has radius `1/2350`.  The checker replays the preceding source
certificate, then proves five new affine-predictor Krawczyk self-maps,
nonzero carrier Jacobians, strict wall-orientation separation,
upper-half-plane containment, pairwise tube separation, and five-sheet
exhaustion.

Exact recentered positive-gradient transport on the weak sheet and exact
one-cell parameter hulls on the robust sheets give the excess upper bounds

```text
-0.005613784,
-0.763980286,
-0.410084705,
-1.232933481,
-1.001165981.
```

The weakest new carrier gates are

```text
|det D_(a,mu)(E1,E2)| > 77.1236328,
|Im(conj(p) q)|      > 0.0155807442,
upper-sheet separation > 0.0256791704.
```

All displayed decimals are readable approximations only.  Every acceptance
comparison uses exact rational dyadic-disc arithmetic.

The exact overlap with the row-24 right endpoint has width

\[
 \frac{847101141295686148428977765944216588229446983829784054782121}
      {80429973504000000000000000000000000000000000000000000000000000000}>0.
\]

Five fixed-parameter Krawczyk overlap tests identify the new sheets with the
five row-24 sheets.  Thus the recentered positive certificates have a
connected common-five-sheet union ending at the new right endpoint above.

## Boundary

This is one additional positive carrier cell.  It asserts no sign beyond its
exact right endpoint and does not certify the selected-sheet-only gap near the
cusp, the remaining positive carrier, any negative regular interval, the
complete double-tight atlas, `EX-W`, degree five, or unrestricted Erdős 1041.
