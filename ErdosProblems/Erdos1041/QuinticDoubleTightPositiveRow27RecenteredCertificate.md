# Erdős 1041: recentered positive row-27 five-sheet certificate

## Exact theorem

On the rational interval

\[
 \frac{500716309007598988776321604095665343002137748290698656005120847}
      {20132659200000000000000000000000000000000000000000000000000000000}
 \le t\le
 \frac{514138081807598988776321604095665343002137748290698656005120847}
      {20132659200000000000000000000000000000000000000000000000000000000},
\]

approximately

```text
[0.02487084810970222, 0.025537514776368887],
```

the unordered quintic double-tight carrier has five pairwise-disjoint
upper-half-plane sheets, and the complete paired inverse-ray excess is
strictly negative on every sheet.

The exact replay is

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_quintic_double_tight_positive_row27_recentered.py
```

## Certificate

The cell is centered at the preceding row-26 center plus \(1/2000\), and has
radius \(1/3000\).  The checker replays row 26, then constructs five affine
predictor Krawczyk cells.  It checks their strict self-maps, nonzero carrier
Jacobians, strict wall orientation, upper-half-plane containment, pairwise
tube separation, and the inherited five-sheet exhaustion theorem.

It separately certifies the sign transport on the weak sheet and the four
robust-sheet macro transports.  Its five exact overlap tests with row 26
identify the sheets, with an exact overlap width \(1/4000\).  Consequently
rows 18 through 27 form one connected common-five-sheet positive carrier
interval ending at the displayed right endpoint.

All displayed decimals are readable approximations only.  Every acceptance
comparison is exact rational dyadic-disc arithmetic in the checker.

## Boundary

This is one additional regular positive carrier cell.  It asserts no sign
beyond its right endpoint and does not settle the remaining positive carrier,
the selected-sheet-only cusp gap, the complete double-tight atlas, `EX-W`,
degree five, or unrestricted Erdős 1041.
