# Z53_1: Arbitrary two-adic totient pulse blocks and exact carry transfer

[All problems and zones](BROWSER.md)

<a id="node-68e34f477b44d5ff"></a>
## a_zero_prefix_and_terminal_half_turn_force_a_half_turn_discrepancy

PROVED EXACT WINDOW TRANSFER: if 2<=K<=p, the terminal deltaTotient H p is 2^(K-1) modulo 2^K, and the preceding K-1 deltaTotient letters vanish modulo 2^K, then windowDiscrepancy H (p-K) K is congruent to 2^(K-1) modulo 2^K.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Landing at the centre of the residue circle is not enough to fire a certified kill: the certificate radius also grows with p, H, and K.

- Lean declaration: [windowDiscrepancy_modEq_half_of_twoAdic_pulse](../../Erdos249257/TotientTwoAdicPulseBlock.lean#L262)

- outgoing **transport_of**: [Z53::the_divisor_pattern_yields_a_zero_prefix_and_half_turn_delta_pulse](BROWSER_Z53_1.md#node-075c65e7235ceb43). The finite discrepancy recurrence transports the produced zero-prefix and terminal-pulse letters into the same half-turn residue.
- incoming **generated_by**: [Z53::eventual_tail_integrality_forces_cofinally_many_half_turn_representatives](BROWSER_Z53_1.md#node-05ae3615969612a8). Under eventual integrality, the carry recurrence transfers the window half-turn to an actual integer tail-difference representative.

<a id="node-965f8eefc1914f3e"></a>
## cofinally_many_primes_realise_the_two_adic_totient_divisor_pattern

PROVED CRT-DIRICHLET PRODUCER: for H,K,B with 2<=K<H, there is a prime p beyond B and H+K such that p is congruent to 1+2^(K-1) modulo 2^K, 2^K divides phi(p+H), and for every 1<=j<K it divides both phi(p-j) and phi(p-j+H).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem prescribes divisibility data for one finite block. It does not assert that the resulting discrepancy lies in a certificate's central arc.

- Lean declaration: [exists_prime_totient_twoAdic_pulse_divisors](../../Erdos249257/TotientTwoAdicPulseBlock.lean#L54)

- incoming **generated_by**: [Z53::the_divisor_pattern_yields_a_zero_prefix_and_half_turn_delta_pulse](BROWSER_Z53_1.md#node-075c65e7235ceb43). The deltaTotient congruences are obtained by subtracting the divisor-controlled endpoint totients from the prime totient.

<a id="node-05ae3615969612a8"></a>
## eventual_tail_integrality_forces_cofinally_many_half_turn_representatives

PROVED CONDITIONAL CONSEQUENCE: for 2<=K<H, if every H-shifted totient-tail difference is integral from N0 onward, then beyond every B there is a prime p and an integer representative z of totientTail (p+H)-totientTail p with z congruent to 2^(K-1) modulo 2^K.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This is compatible with eventual integrality and produces no contradiction. It diagnoses the modular shape of the rational branch; it does not prove irrationality or a central-arc certificate.

Open hypotheses: ["Eventual integrality of every H-shifted totient-tail difference from N0 onward."]

- Lean declaration: [eventual_integral_tailDiff_has_cofinal_twoAdic_half_pulse](../../Erdos249257/TotientTwoAdicPulseBlock.lean#L327)

- outgoing **generated_by**: [Z53::a_zero_prefix_and_terminal_half_turn_force_a_half_turn_discrepancy](BROWSER_Z53_1.md#node-68e34f477b44d5ff). Under eventual integrality, the carry recurrence transfers the window half-turn to an actual integer tail-difference representative.

<a id="node-075c65e7235ceb43"></a>
## the_divisor_pattern_yields_a_zero_prefix_and_half_turn_delta_pulse

PROVED PULSE BLOCK: for H,K,B with 2<=K<H, there is a prime p beyond B and H+K such that deltaTotient H p is congruent to 2^(K-1) modulo 2^K, while deltaTotient H (p-j) vanishes modulo 2^K for every 1<=j<K.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The pulse is an exact congruence statement, not a certified kill. Its prime position is necessarily large relative to the modulus scale.

- Lean declaration: [exists_prime_deltaTotient_twoAdic_pulseBlock](../../Erdos249257/TotientTwoAdicPulseBlock.lean#L211)

- outgoing **generated_by**: [Z53::cofinally_many_primes_realise_the_two_adic_totient_divisor_pattern](BROWSER_Z53_1.md#node-965f8eefc1914f3e). The deltaTotient congruences are obtained by subtracting the divisor-controlled endpoint totients from the prime totient.
- incoming **transport_of**: [Z53::a_zero_prefix_and_terminal_half_turn_force_a_half_turn_discrepancy](BROWSER_Z53_1.md#node-68e34f477b44d5ff). The finite discrepancy recurrence transports the produced zero-prefix and terminal-pulse letters into the same half-turn residue.

