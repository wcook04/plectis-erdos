# Exact noncritical-hub connectors on the pinned degree-six and degree-nine witnesses

## Status

Assimilated 2026-09-05 from Type B return batch
`erdos1041_20260905_eight_return_stream_01`, sources
`.../sources/r01_inverse_fibre_curvature_polygonal_hub.md` section 6 and
`.../sources/r05_nodal_crofton_cyclic_pullbacks.md` sections 4 and 5. Both
return scripts were executed as given and both passed. Both certificates are
reproduced in exact rational arithmetic by
`scripts/check_erdos1041_pinned_witness_hub_connectors.py`, which also asserts
byte equality of the hexadecimal root data against
`QC_REFUTATION_WITNESSES` in
`scripts/check_erdos1041_straight_spoke_hub_criterion.py`. Erdos 1041 remains
open.

## Authority boundary

Two configurations, plus explicit `10^-9` root-coordinate neighbourhoods of
each, plus the cyclic pullback families over them. The containment proofs are
finite exact rational Bernstein certificates, so they are proofs about those
configurations rather than falsification evidence. No Lean module states them.
The two returns arrived independently, chose different degree-nine root pairs,
and reached different constants; the assimilation checks both and records the
comparison rather than merging them.

## Statements

Let `P_6` and `P_9` be the monic polynomials whose roots are the exact IEEE-754
hexadecimal literals in `QC_REFUTATION_WITNESSES`, zero-based in source order.
Every root has modulus below `9999999/10^7`, and both configurations are
near-Fekete: the roots sit within `6.95 * 10^-4` at `d = 6` and `1.38 * 10^-4` at
`d = 9` of a regular polygon inscribed in the unit circle.

**Theorem A (two segments through a fixed noncritical hub).** With

```text
h_6 = (3 + 2i)/25,        h_9 = -1/5 - 4i/25,
Gamma_6 = [a_0, h_6] + [h_6, a_1],
Gamma_9 = [a_5, h_9] + [h_9, a_6],
```

both hubs satisfy `f'(h) != 0` exactly, both broken lines stay in
`{|f| < 99999/100000}`, and

```text
length(Gamma_6) <= 29471595/2^24 < 1.757,
length(Gamma_9) <= 12825029/2^23 < 1.529.
```

**Theorem B (two radial arms and a chord).** With

```text
(i,j,t) = (0, 1, 19/100)   for P_6,
(i,j,t) = (6, 7, 29/100)   for P_9,
gamma_d : a_i -> t a_i -> t a_j -> a_j,
```

both paths stay in `{|P_d|^2 < 19999/20000}` and

```text
length(gamma_6) < 181/100,      length(gamma_9) < 1623/1000.
```

**Certificate shape.** On a segment `z(u) = A + uH`, `0 <= u <= 1`, the quantity
`|P_d(z(u))|^2` is a rational polynomial of degree `2d` in `u`, because every
input coordinate is a dyadic rational. Expanding in the Bernstein basis on
`[0,1]`, whose functions are nonnegative and sum to one, a bound on the
coefficients bounds the polynomial on the whole segment with no sampling, no
subdivision, no floating-point root isolation and no numerical integration.
Theorem A certifies `26 + 38 = 64` coefficients of the slack polynomial
`(99999/100000)^2 - |P_d|^2`, all strictly positive with the per-segment
minima above

```text
P_6 endpoint 0: 7919/10^8      P_6 endpoint 1: 5296/10^8
P_9 endpoint 5: 6823/10^8      P_9 endpoint 6: 2543/10^8.
```

Theorem B certifies `39 + 57 = 96` coefficients of `|P_d|^2` itself, all
strictly below the per-segment ceilings

```text
P_6: 999679/10^6, 999916/10^6, 999876/10^6
P_9: 999809/10^6, 999888/10^6, 999865/10^6,
```

each of which is below `19999/20000`. The length bounds of Theorem A come from
rounding each square root upward to a dyadic rational with denominator `2^24`.

**Explicit neighbourhoods.** Perturb each labelled root by at most
`delta = 10^-9`, keep the hub or the radial factor fixed, and interpolate the
endpoint displacements along the path. Each factor `z - a_k` moves by at most
`2 delta`, so telescoping gives

```text
|P_perturbed(z_perturbed) - P(z)| <= 2 d delta (2 + 2 delta)^(d-1),
```

which is `3.840000 * 10^-7` at `d = 6` and `4.608000 * 10^-6` at `d = 9`. Both
are below `10^-5`, and both are below `(1 - 19999/20000)/2 = 1/40000`, so both
containment certificates survive with room. The original root moduli are below
`9999999/10^7`, so the perturbed roots stay in the open unit disc, and the total
path length grows by at most `2 delta`.

**Theorem C (all cyclic powers).** The Theorem B paths lie in open half planes
missing the origin: `Re a_0, Re a_1 > 1/2 + delta` for `P_6` and
`-Im a_6, -Im a_7 > 1/2 + delta` for `P_9`. Lifting under a single holomorphic
branch of `w^(1/m)` therefore gives, for every integer `m >= 1`, two distinct
roots of `F_{d,m}(z) = P_d(z^m)` joined inside `{|F_{d,m}| < 1}` by a curve of
length

```text
ell_{d,m} < 2(1 - t^(1/m)) + (d_0 * 2^(1 - 1/m)/m) * t^(1/m) <= 2 - (2 - d_0) t,
```

with `(t, d_0) = (19/100, 1)` at `d = 6` and `(29/100, 7/10)` at `d = 9`, so
`ell_{6,m} < 1.81` and `ell_{9,m} < 1.623` in every degree `6m` and `9m`, with
`ell_{d,m} < 2(-log t + d_0)/m + O(m^-2)`. Perturbing every labelled root of
`F_{d,m}` by at most `epsilon_m = 1/(10^6 m 3^N)`, `N = dm`, keeps the
conclusion, with lengths below `1.811` and `1.624`. The general form of this
lift is recorded in `NodalCroftonBudgetAndCyclicPullbacks.md`.

## Proofs

The containment statements are the exact Bernstein inequalities themselves, and
they are verified by
`scripts/check_erdos1041_pinned_witness_hub_connectors.py` in
`fractions.Fraction` arithmetic throughout. The remaining points are the
following.

**Noncriticality is decided exactly.** Writing
`p(u) = f(h + u(a_j - h)) = sum_k p_k u^k`, the linear coefficient is
`p_1 = (a_j - h) f'(h)`. The direction is nonzero, so `p_1 != 0` is an exact
proof that `f'(h) != 0`. Both hubs pass. Both hub values are close to the
ceiling: `|f(h_6)| = 0.9999504` and `|f(h_9)| = 0.9999429`, so the certified
level `99999/100000 = 0.99999` leaves a margin near `4 * 10^-5` at the hub
itself. The certificate is tight, and a coarser level such as `999/1000` would
not have separated it.

**Length arithmetic.** In Theorem A the length is the sum of two Euclidean
distances, each rounded upward. In Theorem B, since all three segments are
radial or chordal in the same scaling,

```text
length(gamma_d) = (1-t)(|a_i| + |a_j|) + t |a_i - a_j|,
```

and the exact checks give `|a_i| < 1`, `|a_0 - a_1| < 1` at `d = 6` and
`|a_6 - a_7| < 7/10` at `d = 9`, so the displayed decimal bounds follow.

**The lift.** The half-plane hypothesis makes the path simply connected and
zero free, so one holomorphic `m`-th root branch covers it; the endpoints lift
to roots over distinct base roots and are therefore distinct; and containment is
exact because `|F_{d,m}(w^{1/m})| = |P_d(w)|`. The length estimate is the
general computation recorded in `NodalCroftonBudgetAndCyclicPullbacks.md`.

## Consumers

**The corpus negative result is untouched.** `StraightSpokeHubCriterionLab.md`
and the packet row `straight_spoke_hub_criterion_separation` record that on
exactly these two witnesses every admissible *critical* point carries at most one
open-contained straight spoke, so no critical point supplies a two-straight-spoke
path from degree six onward. Both theorems above use noncritical hubs, verified
exactly, so neither contradicts that result and neither weakens it. What they
show is that the mechanism elimination is specific to critical hubs.

**Comparison of recorded constants on the same two configurations.**

```text
source                                           d = 6      d = 9
StraightSpokeHubCriterionLab.md descending
  inverse-ray branch pair at a critical hub      1.763942   1.545995   (numerical)
partial_critical_cluster_monodromy moved-block
  mean over the admissible cluster               1.84327    1.63875    (numerical)
Theorem B, three segments                        1.81       1.623      (exact)
Theorem A, two segments through a hub            1.757      1.529      (exact)
```

Theorem A is the shortest certificate on record for both configurations, and it
is the first exact one. It beats the previously recorded numerical inverse-ray
values by `0.0069` at `d = 6` and `0.0170` at `d = 9`. Theorem B is longer than
Theorem A in both degrees and is retained because its half-plane geometry is
what lifts to all cyclic powers.

**Open producer `free_pair_geometric_mean_two_arm_selector`.** Its text already
says "Noncritical hubs are essential candidates", on the strength of
`CEGMQuarticFixedPairNoGo.md` and the `TiedNewtonFacePositiveFibreRationalRescue`
rational hub. Theorem A is direct positive evidence for that clause on the two
configurations the directory uses as its hardest tests, and it does so with the
FP-GM shape: a jointly selected pair `(a_i, a_j)` and hub `h` with
`|h - a_i| + |h - a_j| < 2` and both arms contained. The hubs were supplied, so
this is an existence witness rather than a selector. The producer still needs a
rule that produces such an `h` from the configuration.

**Open producer `fixed_safe_monodromy_block_average_lift_length`.** Its residual
is the partial-cluster moved-block average on these same two rows, reported as
`1.84327` and `1.63875` with an individual moved lift above two. Theorems A and
B settle the parent conclusion for these two configurations by a route that does
not pass through a moved block at all, so the producer's residual becomes a
question about the mechanism rather than about these witnesses. The producer text
should record that the pinned rows are no longer open instances of the parent
statement, and should keep the moved-block average open as the general mechanism.

`GroupedCriticalClusterMonodromy.md` records that these two witnesses have
critical values slightly outside the unit value disc, so a full-cluster lollipop
does not apply to them verbatim. Theorem A shows that a direct finite chart
reaches them anyway, which is the same lesson the producer text already draws
from `TiedNewtonFacePositiveFibreRationalRescue.md`.

## Claim boundary

Two configurations, their `10^-9` root neighbourhoods, and the cyclic pullback
families over them. The certificates prove the target conclusion for those
polynomials, and they supply no hub-selection rule, no criterion that identifies
`h` from the root data, and no statement about any other configuration. The
near-Fekete regime is where the directory expects the difficulty to sit, so these
are positive data points inside the hard regime rather than coverage of it. The
corpus's critical-hub no-go stands unmodified. Erdos 1041 remains open.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_pinned_witness_hub_connectors.py
```
