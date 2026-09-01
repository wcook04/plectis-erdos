# All-critical inverse-ray aggregate probe

## Why this is a different mechanism

The pointwise critical-hub route is already sharply delimited.  The metric-
selected critical point in the exact balanced quintic has two canonical
descending branches of combined length greater than `2.083996`, while another
critical point in the same polynomial has a much shorter hub.  Repeating a
search for the best point does not explain why some point must work.

The new candidate uses the complete critical tree.  For every admissible
simple critical point `c`, let `L_c` be the combined arc length of its two
descending inverse-ray branches to distinct roots.  Test

`sum_c L_c < 2 * number of admissible critical hubs`.

If true, averaging immediately gives one `L_c<2`, and both branches lie in the
strict lemniscate by their value-ray parameterization.  This would solve the
selection problem without coupling the hub to the failed pointwise metric
theorem.

## Discriminating computation

The checker continues both local branches at every admissible simple critical
point using

`f(z(u))=(1-u^2)f(c)`,

and integrates `|z'(u)|`.  Every branch is accepted only when its endpoint is
within `10^-5` of a distinct polynomial root and its maximum value-ray
residual is below `10^-6`.

The deterministic probe contains three structurally relevant families:

- mixed random and boundary-clustered roots in degrees 3 through 8;
- perturbations of boundary-near regular polygons in degrees 3 through 9 and
  four perturbation scales;
- the exact balanced quintic whose distinguished critical hub is already
  certified to exceed two.

All configured aggregates remain below the normalized threshold one.  The
regular cubic family approaches one from below as the perturbation shrinks,
so it supplies a sharp boundary model rather than a comfortable numerical
margin.  In the balanced quintic, the long edge is offset by two short edges;
its normalized aggregate is about `0.536`.

## Analytic target and claim boundary

This is finite numerical support, not mathematical progress by itself.  It
selects a precise theorem to prove or refute:

> Bound the total inverse-ray edge length of the admissible critical Reeb tree
> by twice its edge count, with strict data-dependent slack.

The raw radial-lift coarea average is now sharply delimited.  The exact area
formula controls the angular average of the complete inverse lift, but the
family `z^n+epsilon*z-r^n` makes all `n-1` simple critical-value arguments
coalesce.  Sampling the complete-lift function once per critical ray therefore
repeats one angular spike and already misses the desired `2(n-1)` scale.  See
`RadialLiftCoareaGapLab.md`.  A surviving proof needs an edge-disjoint or
multiplicity-aware Reeb charge before angular integration.  The Cassini
counterexample also forbids reusing the false
epsilon-sharp spanning-tree budget from the unrestricted drafts, and the
boundary-near regular family forbids polynomial-independent positive slack.
Any proof must therefore exploit the inverse-ray edge structure itself and
preserve a margin depending on the polynomial.

A numerical aggregate at least one would instead become a candidate for exact
certification and would eliminate the unweighted average mechanism.  Until
one of those one-way outcomes is obtained, Erdős #1041 remains open.

Replay:

```sh
python3 research_corpus/Erdos1041/scripts/check_erdos1041_inverse_ray_aggregate.py
python3 research_corpus/Erdos1041/scripts/check_erdos1041_inverse_ray_aggregate.py --check
```
