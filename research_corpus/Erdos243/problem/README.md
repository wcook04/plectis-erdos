# Erdős #243 reciprocal-tail rigidity API

This directory's reusable formal spine is
[`ReciprocalTailRigidity.lean`](ReciprocalTailRigidity.lean). It defines the
integer product-cleared state behind the reciprocal-tail argument and proves
several exact conditional consequences. The source is a project-local API,
not a claim that Erdős #243 is solved.

The newer [weighted LCM record-excess note](LcmRecordExcess.md) proves an
ordinary global equivalence: for any decreasing weight with divergent
integral, finiteness of the baseline-subtracted excess at LCM numerator records
forces the Sylvester endpoint. This includes logarithmically discounted sums.
The [finite Lean core](LcmRecordExcess.lean) isolates the crossing and charging
lemmas; it does not formalise the global analytic argument. The
[exact checker](scripts/check_lcm_record_excess.py) reproduces 6,008 bounded
seed–modulus cases. Establishing the required summability from rational
denominator feedback remains open; see `weighted_lcm_record_summability` in
the [research packet](research_packet.json).

## Source and namespace

The module imports only Mathlib order, finite-set, natural-number, `ZMod`,
filter, and ring tactics. Its namespace is
`ErdosProblems.Erdos243`. The observed source generation at this handoff is
`457d7df8b038bff8d61ca7b8b9a1a000bb9ae6a69564416bcc1582941d5d53fb`.
The #243 packet was modified by its source owner at observation time, so its
observed hash is recorded in the packet handoff but is not an immutable pin.

## Core data API

The state is expressed without division:

- `sylvesterNext a = a ^ 2 - a + 1` is the target successor;
- `nextDenState a D = a * D` is the product-cleared denominator update;
- `nextTailState a D C = a * C - D` is the reciprocal-tail update;
- `centeredState a D C = D - (a - 1) * C` is the Sylvester-centered error;
- `sylvesterDefect a aNext = aNext - sylvesterNext a` is the successor defect.

The first algebraic bridge is
`nextTailState_eq_sub_centered`. Common scaling is eliminated by
`nextDenState_scale`, `nextTailState_scale`, and `centeredState_scale`.
These are the lowest-dependency entry points for a consumer that needs only
the exact state algebra.

## Theorem layers and consumers

| Layer | Reusable declarations | Evidence boundary |
| --- | --- | --- |
| Defect transport | `sylvesterDefect_mul_nextTailState`, `sylvesterNext_eq_of_centered_zero`, `sylvesterNext_eventually_of_centered_zero` | Exact integer identities and a conditional eventual recurrence; no unrestricted #243 solution |
| Negative-state rigidity | `no_normalizedConstantNegative_orbit`, `no_constantNegative_orbit`, `no_eventuallyConstantNegative_orbit` | Excludes the named constant regimes only |
| Reduced-tail arithmetic | `reducedStep_coprime_currentFactor`, `reducedTail_pairwiseCoprime`, `reducedTail_wholeModulusAvoidance`, `no_boundedRise_reducedTail`, `no_eventuallyBoundedRise_reducedTail` | Exact coprimality and bounded-rise consequences under their hypotheses |
| GCD budget | `tailGcd_dvd_succ`, `tailGcd_strictGrowthCount_sublinear_of_tailSubexponential`, `tailGcd_exists_arbitrarilyLate_constBlock_of_normalizedVanishes` | A conditional sublinear-growth budget, not the missing global analytic bridge |
| Normalized-vanishing bridge | `tailState_tendsto_atTop_of_nonzero_normalizedVanishes`, `tailState_subexponential_of_normalizedVanishes`, `no_cofinallyBoundedNegative_of_normalizedVanishes`, `boundedNegativePart_eventually_zero` | Division-free conditional reasoning; normalized vanishing remains an input |
| Paper-facing endpoint | `boundedNegativePart_sylvesterNext_eventually` | Covers the bounded-negative regime only; cofinally unbounded negative excursions remain open |

The #243 research packet is the source-result authority for the exact result
IDs `product_cleared_tail_dynamics` and `scale_equivariance`, plus the other
packet-indexed declarations. The current source-generation handoff
([`erdos243_source_result_handoff.v1.json`](../../../docs/formal_math/review_routes/erdos243_source_result_handoff.v1.json))
also binds the packet's `dynamic_cancellation_payment` row to its five exact
declarations in `ReciprocalTailRigidity.lean`, and binds the conditional
`bounded_negative_part_rigidity` endpoint to its three exact declarations.
It also binds the conditional `eventual_nonnegative_state_rigidity` branch to
the exact `centeredState_eventually_zero` declaration. All three rows are
explicitly marked as missing packet anchor fields rather than silently treated
as source-complete. It further binds `constant_negative_orbit_excluded` to
the four exact constant-negative exclusion declarations, preserving the
distinction between that closed obstruction and variable negative excursions.
The handoff also binds `eventually_periodic_negative_magnitude_excluded` to
the three exact periodic-negative exclusion declarations, without treating
that restricted exclusion as a global negative-orbit result.
It also binds `bounded_rise_reduced_tail_excluded` to the exact
`no_boundedRise_reducedTail` declaration, preserving the reduced-tail and
bounded-increment hypotheses as a local obstruction boundary.
It further binds `cofinally_bounded_negative_branch_excluded` to its five
exact declarations, preserving bounded cofinal negative magnitudes and
normalized vanishing as explicit hypotheses rather than treating the
restricted branch exclusion as global.
The same handoff records the exact packet IDs `gap_product_criterion`,
`one_sided_sylvester_closure`, `lcm_weighted_undershoot`, and
`subcritical_one_over_n_threshold` as proof-pending or source-corollary-
pending accounting dispositions. Their statements remain discoverable, but
none is promoted without a formal anchor, current generation, named consumer,
and the stated re-entry condition.
It also binds the four packet IDs
`strict_gcd_growth_exponential_budget`,
`strict_gcd_growth_sublinear_under_subexponential_tail`,
`sublinear_tail_gcd_growth_from_normalized_vanishing`, and
`arbitrarily_late_constant_tail_gcd_blocks` to the existing
`subexponential_divisibility_chain_strict_growth` reviewer surface. They are
one subordinate nested-divisibility mechanism, not four new review families;
packet-generation parity must be refreshed before that reviewer projection is
treated as current.
The finite-horizon result remains authoritative in its sibling
[`erdos243_finite_horizon_source_result_handoff.v1.json`](../../../docs/formal_math/review_routes/erdos243_finite_horizon_source_result_handoff.v1.json);
this handoff federates that receipt by hash and does not duplicate its edge.
These result identities and their claim ceiling must be consumed before
treating a theorem as a new family. The existing reviewer surface is
[`erdos243_cancellation_free_curvature_interface.card.json`](../../../docs/formal_math/reviewer_cards/erdos243_cancellation_free_curvature_interface.card.json);
this README does not create a second reviewer card or paper lattice.

## Formal status and open boundary

Lean checking establishes the declarations named above under their explicit
hypotheses. It does not establish the source packet's analytic transfer,
global LCM-weighted theorem, exclusion of every aperiodic negative orbit, or
the original rigidity target. The cockpit currently records the open
producers `formalise_lcm_weighted_theorem`,
`global_lcm_repair_lower_bound`, `exclude_aperiodic_negative_state_orbits`,
and `reset_payment_lower_bound` among others. No theorem count, local build,
or API map is evidence of novelty, significance, priority, peer review, or a
solution of Erdős #243.

## Validation and reuse

From the repository root, use the problem-local cockpit and the owner build
route before relying on a declaration:

```sh
./repo-python -m system.lib.mathematical_working_memory --query "Erdos #243" --problem-cockpit --context-budget 12000
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --plan ErdosProblems.Erdos243.GlobalLcmHeight
./repo-pytest tests/test_erdos243_api_map.py --ignore-host-pressure
```

The source packet is a moving producer. If its bytes or result identities
change, refresh the source/result handoff before updating this API map; do not
silently turn an observed worktree state into an immutable generation.
