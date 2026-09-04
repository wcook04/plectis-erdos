# Z80_1: Period-multiple escape: finite certified kills and their denominator-class exclusions

[All problems and zones](BROWSER.md)

<a id="node-f3b9241d05b81e8c"></a>
## a_certified_kill_excludes_every_rational_in_its_fixed_denominator_divisor_class

PROVED GENERIC DENOMINATOR CONSUMER: for natural h, N, and L, a proof of certifiedKill h N L implies that the binary totient series differs from every rational r whose reduced denominator divides 2^N * (2^h - 1).

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem consumes a certified kill but does not produce one. For a fixed h and N it excludes only the displayed divisor class, gives no conclusion for denominators outside that class, and does not by itself prove irrationality.

- Lean declaration: [totient_series_ne_rat_of_certifiedKill](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L460)

- incoming **complements**: [Z80::six_periods_beyond_the_diagonal_bank_have_fixed_basepoint_kill_certificates](BROWSER_Z80_1.md#node-028383953b4c0e8f). The finite node supplies six concrete certified-kill inputs, while the generic node explains what denominator exclusion any such input supports.
- incoming **generated_by**: [Z80::seven_fixed_period_kills_exclude_their_corresponding_denominator_divisor_classes](BROWSER_Z80_1.md#node-edcbdf45b903028d). Each of the seven exclusion theorems is the generic consumer instantiated with its corresponding period/basepoint certificate; six certificates are in this zone and the period-67 certificate is already authored in Z66.

<a id="node-edcbdf45b903028d"></a>
## seven_fixed_period_kills_exclude_their_corresponding_denominator_divisor_classes

PROVED FINITE EXCLUSION PACKET: for each h in {67, 81, 97, 101, 121, 125, 128}, the binary totient series differs from every rational r whose reduced denominator divides 2^300 * (2^h - 1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The packet is the finite union of seven explicit divisor classes. It does not show that these classes exhaust rational denominators, does not extend a certificate along an arithmetic progression of periods, and does not establish irrationality or either open cofinal supply.

- Lean declaration: [totient_series_ne_rat_of_den_dvd_67_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L504)
- Lean declaration: [totient_series_ne_rat_of_den_dvd_81_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L509)
- Lean declaration: [totient_series_ne_rat_of_den_dvd_97_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L514)
- Lean declaration: [totient_series_ne_rat_of_den_dvd_101_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L519)
- Lean declaration: [totient_series_ne_rat_of_den_dvd_121_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L524)
- Lean declaration: [totient_series_ne_rat_of_den_dvd_125_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L529)
- Lean declaration: [totient_series_ne_rat_of_den_dvd_128_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L539)

- outgoing **generated_by**: [Z80::a_certified_kill_excludes_every_rational_in_its_fixed_denominator_divisor_class](BROWSER_Z80_1.md#node-f3b9241d05b81e8c). Each of the seven exclusion theorems is the generic consumer instantiated with its corresponding period/basepoint certificate; six certificates are in this zone and the period-67 certificate is already authored in Z66.
- outgoing **complements**: [Z80::six_periods_beyond_the_diagonal_bank_have_fixed_basepoint_kill_certificates](BROWSER_Z80_1.md#node-028383953b4c0e8f). The certificate node records the six still-uninterpreted finite inputs, while the exclusion node records their rational-value consequences together with the already-authored period-67 input.

<a id="node-028383953b4c0e8f"></a>
## six_periods_beyond_the_diagonal_bank_have_fixed_basepoint_kill_certificates

PROVED SIX FINITE CERTIFICATES: Lean proves certifiedKill 81 300 13, certifiedKill 97 300 13, certifiedKill 101 300 11, certifiedKill 121 300 10, certifiedKill 125 300 18, and certifiedKill 128 300 11.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: These are six isolated cells. They do not propagate to adjacent periods, multiples, other basepoints, or locked full depth; they establish neither PeriodMultipleKillSupply nor ApFullDepthEscape and do not prove irrationality.

- Lean declaration: [certifiedKill_81_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L474)
- Lean declaration: [certifiedKill_97_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L477)
- Lean declaration: [certifiedKill_101_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L480)
- Lean declaration: [certifiedKill_121_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L483)
- Lean declaration: [certifiedKill_125_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L486)
- Lean declaration: [certifiedKill_128_300](../../ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L493)

- outgoing **complements**: [Z80::a_certified_kill_excludes_every_rational_in_its_fixed_denominator_divisor_class](BROWSER_Z80_1.md#node-f3b9241d05b81e8c). The finite node supplies six concrete certified-kill inputs, while the generic node explains what denominator exclusion any such input supports.
- incoming **complements**: [Z80::seven_fixed_period_kills_exclude_their_corresponding_denominator_divisor_classes](BROWSER_Z80_1.md#node-edcbdf45b903028d). The certificate node records the six still-uninterpreted finite inputs, while the exclusion node records their rational-value consequences together with the already-authored period-67 input.

