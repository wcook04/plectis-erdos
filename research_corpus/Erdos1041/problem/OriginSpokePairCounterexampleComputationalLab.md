# Erdős 1041: four unsafe spokes to the origin

## Structural question

Every root lies strictly inside the unit disk, so any two root-to-origin
segments have combined Euclidean length below two.  If two such segments were
always contained in `|f|<1`, their broken line through the origin would solve
Erdős #1041 without critical-point or Reeb selection.

The exact witness below eliminates that shortcut.

## Rational witness

Put `r=99999/100000` and take the five distinct roots

```text
r,
r(-20+99i)/101,  r(-20-99i)/101,
r(-28+195i)/197, r(-28-195i)/197.
```

The four non-real directions lie on the unit circle because
`20^2+99^2=101^2` and `28^2+195^2=197^2`; multiplying by `r` puts every root
strictly inside the unit disk.

For each non-real root `z_j`, the checker evaluates the monic factored
polynomial exactly at a point `t z_j` on its spoke:

- `t=3/125` for the conjugate pair in directions `(-20±99i)/101`;
- `t=17/1000` for the conjugate pair in directions `(-28±195i)/197`.

In all four cases Gaussian rational arithmetic gives `|f(t z_j)|^2>1`.
Thus four of the five origin spokes exit the strict unit lemniscate.  At most
one spoke can be safe, so no pair of roots can be joined through the origin by
two contained straight spokes.

## Why this probe was selected

Numerical all-critical inverse-ray searches suggested a stronger aggregate
selection route: average the `n-1` critical hubs rather than accepting the
metric-selected hub.  A cheaper fixed-origin version initially survived broad
random sampling.  Its actual extremal variable is the derivative at `t=0` for
boundary-near roots.  One root near `+1` and two rational conjugate pairs just
past the imaginary axis make four spoke moduli initially increase; choosing
`r` sufficiently close to one converts that first-order prediction into the
four exact escapes above.

The result is one-way: the fixed-origin hub is unavailable.  It does not touch
the surviving all-critical inverse-ray aggregate, where the critical hubs are
adapted to the polynomial's branch structure, or the global Reeb route.

## Durable replay

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_origin_spoke_pair.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_origin_spoke_pair.py --check
```

The canonical receipt is
`state/formal_math/erdos257_period_noncollapse/erdos1041_origin_spoke_pair_counterexample_receipt.json`.
It binds the analytic hypothesis, exact Gaussian-rational computation,
falsifier, claim ceiling, source hashes, and consequence decisions.
