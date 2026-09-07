# Erdős 1041: recentered positive row-22 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{4701807008767005675638605208449425333552687080990418697}
      {222298112000000000000000000000000000000000000000000000000}
 \le t\le
 \frac{4869579168767005675638605208449425333552687080990418697}
      {222298112000000000000000000000000000000000000000000000000},
\]

approximately

```text
[0.02115090841962259, 0.021905625400754667],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row22_recentered.py
```

## Certificate

The cell is centered at

\[
 c_{22}=
 \frac{90296096014471805200728400159423119500994095867743749}
      {4194304000000000000000000000000000000000000000000000000}
\]

and has radius `1/2650`.  The checker rebuilds the intervening carrier rows
from their exact source parameters, then proves five new affine-predictor
Krawczyk self-maps, nonzero carrier Jacobians, strict wall-orientation
separation, upper-half-plane containment, pairwise tube separation, and
five-sheet exhaustion.

Exact recentered positive-gradient transport on the weak sheet and exact
one-cell parameter hulls on the robust sheets give the excess upper bounds

```text
-0.027604897,
-0.801992538,
-0.453615439,
-1.234537906,
-1.003382816.
```

The weakest new carrier gates are

```text
|det D_(a,mu)(E1,E2)| > 78.3016856,
|Im(conj(p) q)|      > 0.0133700054,
upper-sheet separation > 0.0231798932.
```

All displayed decimals are readable approximations only.  Every acceptance
comparison uses exact rational dyadic-disc arithmetic.

The exact overlap with the row-21 right endpoint has width

\[
 \frac{31753976139809482975011589127508450804072921563950533}
      {2445279232000000000000000000000000000000000000000000000000}>0.
\]

Five fixed-parameter Krawczyk overlap tests identify the new sheets with the
five row-21 sheets.  Thus the recentered positive certificates have a
connected common-five-sheet union ending at the new right endpoint above.

## Boundary

This is one additional positive carrier cell.  It asserts no sign beyond its
exact right endpoint and does not certify the selected-sheet-only gap near the
cusp, the remaining positive carrier, any negative regular interval, the
complete double-tight atlas, `EX-W`, degree five, or unrestricted Erdős 1041.
