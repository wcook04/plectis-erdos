# Erdős 1041: complete five-sheet macroscopic double-tight cell

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_double_tight_complete_large_cell.py`.

## Result

The checker upgrades the first macroscopic affine/gradient cell from one
weak carrier branch to the complete physical upper fibre.  On

```text
3/3125 <= t <= 13/12500,
```

it isolates all five upper-half-plane roots of the unordered critical-value
carrier, identifies their ordered `(t,a,mu)` branches by exact overlap at
`t=1/1000`, fixes every wall chamber, and applies exact gradient transport
to the paired inverse-ray excess on each branch.

The exact acceptance statement is

```text
mathcal E < -1/25   on the weak sheet,
mathcal E < -9/10  on each of the other four sheets.
```

on every one of the five physical sheets throughout the common interval.
More precisely, the five exact transported upper endpoints are

```text
-0.044810909,
-1.109187668,
-0.862564072,
-1.265086165,
-1.024674796.
```

For each sheet an affine-predictor Krawczyk map proves a unique regular
ordered carrier throughout the full interval.  Exact implicit
differentiation and positive wall-gradient integrals transport the exact
centre excess to the whole cell.  The two near-`mu_*` sheets use correction
radii `10^-8` and `10^-9`; this keeps their small wall cross-products
separated without shrinking the parameter interval.

The degree-ten carrier theorem supplies upper-sheet exhaustion after the
checker proves that the five certified parameter tubes are pairwise
disjoint and stay strictly in the upper half-plane.  Hence this is the
complete physical double-tight fibre over the stated interval, not a
selected-branch certificate.

All seventeen exact checker gates are green.  The interval width is
`1/12500=8*10^-5`, four times the first complete-cell run and four thousand
times the original affine seed cell.  This is one connected atlas cell; it
does not by itself cover the remaining four
regular carrier intervals or prove `EX-W`, `EX-U`, degree five, or the
unrestricted problem.
