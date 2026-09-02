# Erdős 1041: recentered positive row-26 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{488972257807598988776321604095665343002137748290698656005120847}
      {20132659200000000000000000000000000000000000000000000000000000000}
 \le t\le
 \frac{505749473807598988776321604095665343002137748290698656005120847}
      {20132659200000000000000000000000000000000000000000000000000000000},
\]

approximately

```text
[0.024287514776368885, 0.02512084810970222],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row26_recentered.py
```

## Certificate

The cell is centered at

\[
 c_{26}=
 \frac{165786955269199662925440534698555114334045916096899552001706949}
      {6710886400000000000000000000000000000000000000000000000000000000}
\]

and has radius `1/2400`.  The checker replays the preceding source
certificate, then proves five new affine-predictor Krawczyk self-maps,
nonzero carrier Jacobians, strict wall-orientation separation,
upper-half-plane containment, pairwise tube separation, and five-sheet
exhaustion.

Exact recentered positive-gradient transport on the weak sheet and exact
one-cell parameter hulls on the robust sheets give the excess upper bounds

```text
-0.022067592,
-0.797294841,
-0.434943663,
-1.233222664,
-1.001856186.
```

The weakest new carrier gates are

```text
|det D_(a,mu)(E1,E2)| > 76.8083181,
|Im(conj(p) q)|      > 0.0167368169,
upper-sheet separation > 0.026620609.
```

All displayed decimals are readable approximations only.  Every acceptance
comparison uses exact rational dyadic-disc arithmetic.

The exact overlap with the row-25 right endpoint has width

\[
 \frac{6426335600482766630870493973556049044911501508986194078817591}
      {946234982400000000000000000000000000000000000000000000000000000000}>0.
\]

Five fixed-parameter Krawczyk overlap tests identify the new sheets with the
five row-25 sheets.  Thus the recentered positive certificates have a
connected common-five-sheet union ending at the new right endpoint above.

## Boundary

This is one additional positive carrier cell.  It asserts no sign beyond its
exact right endpoint and does not certify the selected-sheet-only gap near the
cusp, the remaining positive carrier, any negative regular interval, the
complete double-tight atlas, `EX-W`, degree five, or unrestricted Erdős 1041.
