# Erdős 1041: no polynomial-independent length slack

## Discriminating computation

All-critical Newton-branch searches were run across degrees 5 through 8 and
against degree-5 perturbations of a boundary-near regular polygon.  Random
configurations retained short hubs.  In the regular-polygon stress family the
largest normalized minimum hub score rose from `0.636634506259` at perturbation
scale `0.2`, through `0.770749451305` at `0.05`, to `0.886171521074` at `0.01`.
The approach toward one selected a boundary-slack question rather than another
longer random audit.

## Exact family and result

The quadratic Cassini family already gives the exact obstruction.  Put

\[
  a_m=(m-1)/m,\qquad f_m(z)=z^2-a_m^2.
\]

Both roots lie strictly inside the unit disk, their distance is
`2 a_m = 2-2/m`, and every connecting curve has length at least that distance.
Thus the admissible lower bound approaches two from below.  Lean proves the
quantified consequence in
`not_exists_uniform_cassini_rootDistance_slack`: no fixed `delta>0` can replace
the target bound `2` by `2-delta` for every polynomial.

## Analytic consequence

This eliminates polynomial-independent slack as the currency for the generic
perturbation route.  A perturbation/root-transfer proof must preserve a strict
margin depending on the starting polynomial and chosen component; a global
budget cannot absorb the transfer.  The result does not obstruct the original
strict `<2` target or a data-dependent critical-hub selection theorem.

The exact family prefix and its theorem/analysis links are replayed by
`scripts/check_erdos1041_uniform_slack_no_go.py`; its canonical receipt is
`source-provenance://private-authoring-project/receipts/erdos1041_uniform_slack_no_go_receipt.json`.
