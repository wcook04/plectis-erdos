# Erdős 1041: recentered positive row-24 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{193968525124329221433346572139987183622402896705684546945951}
      {8556380160000000000000000000000000000000000000000000000000000}
 \le t\le
 \frac{200679411524329221433346572139987183622402896705684546945951}
      {8556380160000000000000000000000000000000000000000000000000000},
\]

approximately

```text
[0.022669460858121715, 0.023453774583611912],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row24_recentered.py
```

## Certificate

The cell is centered at

\[
 c_{24}=
 \frac{3869097418124102381046011218431121247498096013836951900901}
      {167772160000000000000000000000000000000000000000000000000000}
\]

and has radius `1/2550`.  The checker rebuilds the intervening carrier rows
from their exact source parameters, then proves five new affine-predictor
Krawczyk self-maps, nonzero carrier Jacobians, strict wall-orientation
separation, upper-half-plane containment, pairwise tube separation, and
five-sheet exhaustion.

Exact recentered positive-gradient transport on the weak sheet and exact
one-cell parameter hulls on the robust sheets give the excess upper bounds

```text
-0.030034880,
-0.806205609,
-0.453722937,
-1.234040884,
-1.002884344.
```

The weakest new carrier gates are

```text
|det D_(a,mu)(E1,E2)| > 77.5951422,
|Im(conj(p) q)|      > 0.0150495333,
upper-sheet separation > 0.0248505292.
```

All displayed decimals are readable approximations only.  Every acceptance
comparison uses exact rational dyadic-disc arithmetic.

The exact overlap with the row-23 right endpoint has width

\[
 \frac{38095200626548067471371956618790891996037309469604692649}
      {8556380160000000000000000000000000000000000000000000000000000}>0.
\]

Five fixed-parameter Krawczyk overlap tests identify the new sheets with the
five row-23 sheets.  Thus the recentered positive certificates have a
connected common-five-sheet union ending at the new right endpoint above.

## Boundary

This is one additional positive carrier cell.  It asserts no sign beyond its
exact right endpoint and does not certify the selected-sheet-only gap near the
cusp, the remaining positive carrier, any negative regular interval, the
complete double-tight atlas, `EX-W`, degree five, or unrestricted Erdős 1041.
