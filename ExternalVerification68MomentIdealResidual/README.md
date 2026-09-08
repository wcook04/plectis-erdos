# Exact attainable moments and residual transparency

For `D ≥ 2` and a prime `p` with `D/2 < p ≤ D`, the finite integer coefficient vectors supported on `n ≥ 2` and annihilating the divisor channels `2, ..., D` have moments exactly divisible by the explicit positive generator `minimumMoment D p`. The generator is attained by a primitive vector.

For a low-kernel decomposition with coefficient `t` and tail coordinates vanishing below `D`, the actual convergent residual equals

```text
t * channelLCM D * (factorialGapSeries - gapPrefixReal D) + coordinateMass z.
```

The Challenge copies the literal finite-support, channel, generator, residual, and tail-coordinate definitions using only Mathlib. Its prime-window, support, channel-vanishing, cutoff, and tail-coordinate hypotheses match the audited source endpoints. The Solution projects `exact_moment_ideal_with_primitive_attainment` and `residual_transparency` from the exported source modules.

These results identify the attainable ideal and the exact residual decomposition. They do not prove cofinal residual nonintegrality and do not solve Erdős #68. The private source endpoints compiled and were included in the clean Type B axiom audit. Public source export, wrapper elaboration, wrapper audit, deliberate-negative rejection, and supported-runner Comparator replay remain pending. Novelty is unassessed, Palomar qualification has not been run, and no submission has occurred.
