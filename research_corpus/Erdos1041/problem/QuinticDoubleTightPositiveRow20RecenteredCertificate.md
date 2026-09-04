# Erdős 1041: recentered positive row-20 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{118019477858920695849180116434155238431624156093757}
      {5976883200000000000000000000000000000000000000000000}
 \le t\le
 \frac{122213781858920695849180116434155238431624156093757}
      {5976883200000000000000000000000000000000000000000000},
\]

approximately

```text
[0.01974599032802259, 0.0204477447139875],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row20_recentered.py
```

## Certificate

The cell is centered at

\[
 c_{20}=
 \frac{2107309295770538523669826604107986639151300984101}
      {104857600000000000000000000000000000000000000000000}
\]

and has radius `1/2850`.  This is the first adaptive widening: radius
`1/3000` no longer overlaps row 19, while `1/2850` restores a strict rational
overlap.  The checker replays the preceding source certificates, then proves
five new affine-predictor Krawczyk self-maps, nonzero carrier Jacobians,
strict wall-orientation separation, upper-half-plane containment, pairwise
tube separation, and five-sheet exhaustion.

Exact recentered positive-gradient transport on the weak sheet and exact
one-cell parameter hulls on the robust sheets give the excess upper bounds

```text
-0.037162281,
-0.818388778,
-0.470034276,
-1.235419673,
-1.004557681.
```

The weakest new carrier gates are

```text
|det D_(a,mu)(E1,E2)| > 79.0147311,
|Im(conj(p) q)|      > 0.0119848468,
upper-sheet separation > 0.0216428257.
```

All displayed decimals are readable approximations only.  Every acceptance
comparison uses exact rational dyadic-disc arithmetic.

The exact overlap with the row-19 right endpoint has width

\[
 \frac{9177126872069450975425418616607618323077145481}
      {1992294400000000000000000000000000000000000000000000}>0.
\]

Five fixed-parameter Krawczyk overlap tests identify the new sheets with the
five row-19 sheets.  Thus the recentered positive certificates have a
connected common-five-sheet union ending at the new right endpoint above.

## Boundary

This is one additional positive carrier cell.  It asserts no sign beyond its
exact right endpoint and does not certify the selected-sheet-only gap near the
cusp, the remaining positive carrier, any negative regular interval, the
complete double-tight atlas, `EX-W`, degree five, or unrestricted Erdős 1041.
