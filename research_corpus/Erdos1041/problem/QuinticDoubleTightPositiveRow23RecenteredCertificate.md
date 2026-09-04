# Erdős 1041: recentered positive row-23 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{936478669624778847504089720483029872571994670075770758193}
      {42781900800000000000000000000000000000000000000000000000000}
 \le t\le
 \frac{970033101624778847504089720483029872571994670075770758193}
      {42781900800000000000000000000000000000000000000000000000000},
\]

approximately

```text
[0.021889599389300133, 0.022673913114790327],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row23_recentered.py
```

## Certificate

The cell is centered at

\[
 c_{23}=
 \frac{18691291874995663676550778833000585736705777844622956043}
      {838860800000000000000000000000000000000000000000000000000}
\]

and has radius `1/2550`.  The checker rebuilds the intervening carrier rows
from their exact source parameters, then proves five new affine-predictor
Krawczyk self-maps, nonzero carrier Jacobians, strict wall-orientation
separation, upper-half-plane containment, pairwise tube separation, and
five-sheet exhaustion.

Exact recentered positive-gradient transport on the weak sheet and exact
one-cell parameter hulls on the robust sheets give the excess upper bounds

```text
-0.020523485,
-0.792645425,
-0.437679615,
-1.234045132,
-1.002713078.
```

The weakest new carrier gates are

```text
|det D_(a,mu)(E1,E2)| > 77.9242763,
|Im(conj(p) q)|      > 0.0140897686,
upper-sheet separation > 0.0239864907.
```

All displayed decimals are readable approximations only.  Every acceptance
comparison uses exact rational dyadic-disc arithmetic.

The exact overlap with the row-22 right endpoint has width

\[
 \frac{36338031310178973797017940583555155921690712086420525171}
      {2267440742400000000000000000000000000000000000000000000000000}>0.
\]

Five fixed-parameter Krawczyk overlap tests identify the new sheets with the
five row-22 sheets.  Thus the recentered positive certificates have a
connected common-five-sheet union ending at the new right endpoint above.

## Boundary

This is one additional positive carrier cell.  It asserts no sign beyond its
exact right endpoint and does not certify the selected-sheet-only gap near the
cusp, the remaining positive carrier, any negative regular interval, the
complete double-tight atlas, `EX-W`, degree five, or unrestricted Erdős 1041.
