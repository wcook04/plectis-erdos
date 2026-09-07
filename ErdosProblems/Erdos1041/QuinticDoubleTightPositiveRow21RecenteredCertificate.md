# Erdős 1041: recentered positive row-21 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{4714457186469516218396195177553885577347512340797977}
      {230686720000000000000000000000000000000000000000000000}
 \le t\le
 \frac{4882229346469516218396195177553885577347512340797977}
      {230686720000000000000000000000000000000000000000000000},
\]

approximately

```text
[0.020436621520603857, 0.021163894247876583],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row21_recentered.py
```

## Certificate

The cell is centered at

\[
 c_{21}=
 \frac{436213024224501474399654107050353234304319303708907}
      {20971520000000000000000000000000000000000000000000000}
\]

and has radius `1/2750`.  The checker rebuilds the intervening carrier rows
from their exact source parameters, then proves five new affine-predictor
Krawczyk self-maps, nonzero carrier Jacobians, strict wall-orientation
separation, upper-half-plane containment, pairwise tube separation, and
five-sheet exhaustion.

Exact recentered positive-gradient transport on the weak sheet and exact
one-cell parameter hulls on the robust sheets give the excess upper bounds

```text
-0.033136970,
-0.810746393,
-0.462093727,
-1.234994817,
-1.003994028.
```

The weakest new carrier gates are

```text
|det D_(a,mu)(E1,E2)| > 78.6649279,
|Im(conj(p) q)|      > 0.0126682441,
upper-sheet separation > 0.0223988981.
```

All displayed decimals are readable approximations only.  Every acceptance
comparison uses exact rational dyadic-disc arithmetic.

The exact overlap with the row-20 right endpoint has width

\[
 \frac{146260460863106419613131034570046640764939980780711}
      {13149143040000000000000000000000000000000000000000000000}>0.
\]

Five fixed-parameter Krawczyk overlap tests identify the new sheets with the
five row-20 sheets.  Thus the recentered positive certificates have a
connected common-five-sheet union ending at the new right endpoint above.

## Boundary

This is one additional positive carrier cell.  It asserts no sign beyond its
exact right endpoint and does not certify the selected-sheet-only gap near the
cusp, the remaining positive carrier, any negative regular interval, the
complete double-tight atlas, `EX-W`, degree five, or unrestricted Erdős 1041.
