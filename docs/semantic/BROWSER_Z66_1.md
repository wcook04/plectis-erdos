# Z66_1: Period-67 and period-127 finite kill deposits and denominator exclusion

[All problems and zones](BROWSER.md)

<a id="node-d3a4d4d87f596cc8"></a>
## period_sixty_seven_has_one_locked_full_depth_certificate

Lean proves certifiedKill 67 300 67. Thus the matrix of the open depth-locked producer is inhabited at the single local choice d=67, N=300, and t=1.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: One local full-depth instance does not prove ApFullDepthEscape, gives no witness for other d or N, and does not assert that depth 67 is minimal or arithmetically distinguished.

- Lean declaration: [certifiedKill_67_300_fullDepth](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L498)

- outgoing **complements**: [Z66::periods_sixty_seven_and_one_hundred_twenty_seven_have_fixed_depth_eleven_kills](BROWSER_Z66_1.md#node-c285370019f95afe). Both nodes record the period-67/basepoint-300 cell at different depths: the depth-67 theorem exposes one locked-depth instance, while the depth-11 theorem records the shorter firing certificate.

<a id="node-c285370019f95afe"></a>
## periods_sixty_seven_and_one_hundred_twenty_seven_have_fixed_depth_eleven_kills

Lean proves certifiedKill 67 300 11 and certifiedKill 127 300 11. These are two exact kernel-checked central-residue certificates at the common basepoint 300 and depth 11.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: These two fixed cells establish no cofinal supply, do not propagate to multiples, adjacent periods, or other basepoints, and do not by themselves prove irrationality.

- Lean declaration: [certifiedKill_67_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L471)
- Lean declaration: [certifiedKill_127_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L490)

- incoming **complements**: [Z66::period_sixty_seven_has_one_locked_full_depth_certificate](BROWSER_Z66_1.md#node-d3a4d4d87f596cc8). Both nodes record the period-67/basepoint-300 cell at different depths: the depth-67 theorem exposes one locked-depth instance, while the depth-11 theorem records the shorter firing certificate.
- incoming **generated_by**: [Z66::the_period_one_hundred_twenty_seven_kill_excludes_its_fixed_denominator_class](BROWSER_Z66_1.md#node-50d5aafefa866599). The denominator exclusion applies the residual generic theorem totient_series_ne_rat_of_certifiedKill to certifiedKill_127_300.

<a id="node-50d5aafefa866599"></a>
## the_period_one_hundred_twenty_seven_kill_excludes_its_fixed_denominator_class

For every rational r, if r.den divides 2^300 * (2^127 - 1), then the binary totient series is not equal to r.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The result covers only denominators dividing the displayed fixed integer. It excludes no rational outside that divisor class, does not require or prove primality of 2^127-1, and does not establish irrationality.

- Lean declaration: [totient_series_ne_rat_of_den_dvd_127_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L534)

- outgoing **generated_by**: [Z66::periods_sixty_seven_and_one_hundred_twenty_seven_have_fixed_depth_eleven_kills](BROWSER_Z66_1.md#node-c285370019f95afe). The denominator exclusion applies the residual generic theorem totient_series_ne_rat_of_certifiedKill to certifiedKill_127_300.

