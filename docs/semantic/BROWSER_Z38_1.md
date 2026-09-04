# Z38_1: Actual-LCM orbit arithmetic: exact descent, positivity, and residue bridges

[All problems and zones](BROWSER.md)

<a id="node-2786b4ed28260562"></a>
## arithmetic_word_residue_exactly_matches_diagonal_certificates

PROVED: reducing the actual-LCM arithmetic word modulo its diagonal modulus gives exactly the diagonal-window residue; arithmetic kill is equivalent to the symmetric diagonal residue certificate and implies the asymmetric fresh-loss residue certificate.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: These theorems translate a supplied arithmetic kill into certificate language. They do not prove that such kills occur cofinally.

- Lean declaration: [lcmDiagonalArithmeticWord_emod_eq_diagonalWindowResidue](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2059)
- Lean declaration: [lcmDiagonalArithmeticKill_iff_diagonalSymmetricResidueCert](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2074)
- Lean declaration: [diagonalFreshLossResidueCert_of_lcmDiagonalArithmeticKill](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2083)

- outgoing **complements**: [Z38::new_prime_frontier_controls_every_short_word_term](BROWSER_Z38_1.md#node-ac40cdad9bf2817d). The frontier controls the word's terms, while the residue bridges identify what modular property of the assembled word constitutes a diagonal certificate.
- incoming **generated_by**: [Z38::odd_guard_supply_transports_to_short_kills_and_fresh_loss](BROWSER_Z38_1.md#node-50e6f2b34d9fc330). The conditional supply maps consume the exact arithmetic-word and residue-certificate identifications.

<a id="node-0f6dc3562aced155"></a>
## diagonal_arithmetic_letter_is_the_exact_totient_increment

PROVED: the actual-LCM arithmetic letter is exactly the consecutive totient difference and the corresponding diagonal-window increment; at every divisor offset it is divisible by phi(j), and every positive even short offset at a power-of-two height divides the period LCM and therefore has that divisibility.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Divisibility by phi(j) constrains the letter arithmetically but does not certify a nonzero residue or a diagonal kill.

- Lean declaration: [lcmRayArithmeticLetter_eq_deltaTotient](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L298)
- Lean declaration: [diagonalWindowIncrement_eq_lcmRayArithmeticLetter](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L310)
- Lean declaration: [totient_dvd_lcmRayArithmeticLetter_of_dvd](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L322)
- Lean declaration: [even_short_offset_dvd_periodLcm_pow_two](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L337)
- Lean declaration: [totient_dvd_lcmRayArithmeticLetter_of_even_short_pow_two](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L366)

- outgoing **specialises**: [Z38::divisor_ray_letter_has_exact_overlap_descent](BROWSER_Z38_1.md#node-c17139b9f14ce1a0). The actual diagonal arithmetic letter is the coordinate-level specialisation of the overlap-aware divisor-ray difference.
- incoming **complements**: [Z38::short_offsets_are_divisors_or_descending_foreign_prime_powers](BROWSER_Z38_1.md#node-d1814a9a94604c36). Divisor offsets use the exact quotient-scale identity, while the remaining short offsets descend through a foreign-prime-power predecessor.

<a id="node-c17139b9f14ce1a0"></a>
## divisor_ray_letter_has_exact_overlap_descent

PROVED: an actual-LCM divisor-ray letter is exactly its clean quotient-scale core plus the upper overlap excess minus the lower overlap excess; equivalently, the ray's totient difference has an exact overlap-aware quotient-scale formula, recovering the clean delta identity when both excesses vanish.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The descent is exact for divisor offsets, but its correction terms need not vanish and the identity alone does not prove the coefficient is positive.

- Lean declaration: [lcmDivisorRayLetter_eq_cleanCore_add_overlapExcess](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L225)
- Lean declaration: [deltaTotient_divisor_ray_eq_overlapLetter](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L247)
- Lean declaration: [lcmDivisorRayLetter_eq_clean_delta](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L270)

- outgoing **generated_by**: [Z38::overlap_factor_exact_product_and_excess](BROWSER_Z38_1.md#node-dbe895edc947ba85). The divisor-ray descent is obtained by applying the exact overlap factorisation at the upper and lower endpoints.
- incoming **specialises**: [Z38::diagonal_arithmetic_letter_is_the_exact_totient_increment](BROWSER_Z38_1.md#node-0f6dc3562aced155). The actual diagonal arithmetic letter is the coordinate-level specialisation of the overlap-aware divisor-ray difference.

<a id="node-21286a404feeaf17"></a>
## every_short_actual_lcm_arithmetic_letter_is_positive

PROVED: divisor, foreign-prime-power, and genuinely new-prime offsets each satisfy explicit period-LCM bounds against their arithmetic letter; consequently every positive offset in the short window has a strictly positive letter, and uniformly H is less than 8t times that letter.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Positivity is proved only under the theorem's power-of-two and short-window hypotheses. Positive coefficients alone do not establish a nonzero diagonal residue or a cofinal kill supply.

- Lean declaration: [periodLcm_lt_four_mul_j_mul_lcmRayArithmeticLetter_divisor](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1040)
- Lean declaration: [lcmRayArithmeticLetter_divisor_pos](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1191)
- Lean declaration: [lcmRayArithmeticLetter_foreignPrimePower_bracket](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1207)
- Lean declaration: [newPrime_upper_endpoint_primeFactors_card_lt_quarter](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1443)
- Lean declaration: [periodLcm_lt_four_mul_lcmRayArithmeticLetter_newPrime](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1541)
- Lean declaration: [quarter_periodLcm_lt_lcmRayArithmeticLetter_newPrime](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1637)
- Lean declaration: [lcmRayArithmeticLetter_newPrime_pos](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1652)
- Lean declaration: [periodLcm_lt_four_mul_lcmRayArithmeticLetter_of_not_dvd](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1668)
- Lean declaration: [lcmRayArithmeticLetter_pos_of_lt_two_mul](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1703)
- Lean declaration: [periodLcm_lt_eight_mul_t_mul_lcmRayArithmeticLetter](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1906)

- outgoing **generated_by**: [Z38::short_offsets_are_divisors_or_descending_foreign_prime_powers](BROWSER_Z38_1.md#node-d1814a9a94604c36). The positivity proof splits on the complete divisor-versus-foreign-prime-power classification.
- outgoing **generated_by**: [Z38::rough_new_prime_support_retains_three_quarters_euler_density](BROWSER_Z38_1.md#node-ceb13a3ab9323377). The quantitative coefficient bounds consume the three-quarters Euler-density estimates for rough and relative-new-prime support.
- incoming **complements**: [Z38::terminal_totient_factor_cancels_in_two_step_carry](BROWSER_Z38_1.md#node-fc7046660c40e5a2). Coefficient positivity supplies a strong short-window fact, while the terminal calculation records that one tempting carry projection nevertheless cancels and cannot finish the residue argument alone.
- incoming **generated_by**: [Z38::positive_letters_force_strict_arithmetic_word_growth](BROWSER_Z38_1.md#node-2c4c0e6113ecd528). The more-than-doubling recurrence follows from appending a strictly positive next letter.

<a id="node-ac40cdad9bf2817d"></a>
## new_prime_frontier_controls_every_short_word_term

PROVED: at a genuinely new-prime offset the two actual-LCM ray endpoints are coprime and satisfy the complete new-prime frontier package; more generally every term of the short diagonal arithmetic word inherits the divisor-or-prime-power structural dichotomy.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The frontier controls term structure and size but does not choose a word length whose residue is nonzero.

- Lean declaration: [newPrime_lcmRay_endpoints_coprime](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1942)
- Lean declaration: [lcmRayArithmeticLetter_newPrime_frontier](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1960)
- Lean declaration: [lcmDiagonalArithmeticWord_term_divisor_or_primePower](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1979)

- outgoing **specialises**: [Z38::short_offsets_are_divisors_or_descending_foreign_prime_powers](BROWSER_Z38_1.md#node-d1814a9a94604c36). The word-level theorem transports the short-offset dichotomy term by term and isolates the full new-prime endpoint package.
- incoming **complements**: [Z38::arithmetic_word_residue_exactly_matches_diagonal_certificates](BROWSER_Z38_1.md#node-2786b4ed28260562). The frontier controls the word's terms, while the residue bridges identify what modular property of the assembled word constitutes a diagonal certificate.

<a id="node-50e6f2b34d9fc330"></a>
## odd_guard_supply_transports_to_short_kills_and_fresh_loss

PROVED CONDITIONAL TRANSPORT: an odd-guard half-word-band supply yields a short actual-LCM arithmetic-kill supply, and any such short-kill supply yields the corresponding diagonal fresh-loss projection supply.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The source explicitly does not prove the required cofinal odd-guard or short arithmetic-kill producer. This node is a stronger conditional input lane for the landed actual-orbit endpoint, not a proof of the open problem.

Open hypotheses: ["PowerTwoOddGuardHalfWordBandSupply", "PowerTwoActualLcmShortArithmeticKillSupply"]

- Lean declaration: [powerTwoActualLcmShortArithmeticKillSupply_of_oddGuardHalfWordBand](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2114)
- Lean declaration: [diagonalFreshLossProjectionSupply_of_shortArithmeticKill](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2141)

- outgoing **generated_by**: [Z38::arithmetic_word_residue_exactly_matches_diagonal_certificates](BROWSER_Z38_1.md#node-2786b4ed28260562). The conditional supply maps consume the exact arithmetic-word and residue-certificate identifications.

<a id="node-dbe895edc947ba85"></a>
## overlap_factor_exact_product_and_excess

PROVED: for x>0, phi(jx) is exactly phi(x) times an integral overlap factor; the factor equals phi(j) in the coprime case, is always at least phi(j), and every nonzero excess is witnessed by a prime whose full power in j is already saturated by x.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: This is an exact local factorisation. It does not by itself supply a nonzero residue, a cofinal arithmetic kill, or irrationality.

- Lean declaration: [totient_mul_eq_overlapFactor_mul](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L43)
- Lean declaration: [totientOverlapFactor_eq_totient_of_coprime](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L163)
- Lean declaration: [totient_le_totientOverlapFactor](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L169)
- Lean declaration: [exists_saturated_prime_of_overlapExcess_ne_zero](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L188)

- incoming **complements**: [Z38::relative_euler_product_exactly_measures_new_prime_support](BROWSER_Z38_1.md#node-678e313de141d965). The relative Euler product and the integral overlap factor are two exact normal forms for how shared and newly introduced prime support affect phi(jx).
- incoming **generated_by**: [Z38::divisor_ray_letter_has_exact_overlap_descent](BROWSER_Z38_1.md#node-c17139b9f14ce1a0). The divisor-ray descent is obtained by applying the exact overlap factorisation at the upper and lower endpoints.

<a id="node-2c4c0e6113ecd528"></a>
## positive_letters_force_strict_arithmetic_word_growth

PROVED: extending the diagonal arithmetic word appends exactly the next arithmetic letter, and within the short positive-letter range the successor word is strictly more than twice its predecessor.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Rapid integer growth does not prevent the word from lying in a forbidden congruence class; a residue producer is still required.

- Lean declaration: [lcmDiagonalArithmeticWord_succ](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2013)
- Lean declaration: [two_mul_lcmDiagonalArithmeticWord_lt_succ](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2026)

- outgoing **generated_by**: [Z38::every_short_actual_lcm_arithmetic_letter_is_positive](BROWSER_Z38_1.md#node-21286a404feeaf17). The more-than-doubling recurrence follows from appending a strictly positive next letter.

<a id="node-678e313de141d965"></a>
## relative_euler_product_exactly_measures_new_prime_support

PROVED: the prime factors of a product split into those already present and those new relative to the first factor; this gives an exact relative Euler-product formula for phi(jx), an exact quotient by phi(j), and, on an LCM divisor-ray endpoint, places every relative new prime above the period cutoff.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The formulas expose the exact relative density but do not ensure that the density is separated far enough from zero without the later roughness hypotheses.

- Lean declaration: [primeFactors_mul_eq_union_relative](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L84)
- Lean declaration: [totient_mul_eq_totient_mul_relativeEulerProduct](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L100)
- Lean declaration: [totient_mul_div_totient_eq_relativeEulerProduct](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L114)
- Lean declaration: [relativePrimeFactors_lcmDivisor_endpoint_gt](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L128)

- outgoing **complements**: [Z38::overlap_factor_exact_product_and_excess](BROWSER_Z38_1.md#node-dbe895edc947ba85). The relative Euler product and the integral overlap factor are two exact normal forms for how shared and newly introduced prime support affect phi(jx).
- incoming **specialises**: [Z38::rough_new_prime_support_retains_three_quarters_euler_density](BROWSER_Z38_1.md#node-ceb13a3ab9323377). The rough-support bounds turn the exact relative Euler product into a quantitative density lower bound.

<a id="node-ceb13a3ab9323377"></a>
## rough_new_prime_support_retains_three_quarters_euler_density

PROVED: a prime newly appearing beyond the period LCM does not divide that LCM and forces rough endpoint support; elementary Euler-product and support-cardinality bounds then show that sufficiently rough endpoints, and their relative-new-prime analogues, retain more than three quarters of their mass under the totient, with the required power-of-two height range made explicit.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: The three-quarters threshold depends on the stated roughness and height hypotheses. These estimates do not manufacture the new prime or the final modular certificate.

- Lean declaration: [newPrime_not_dvd_periodLcm](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L587)
- Lean declaration: [newPrime_lcmRay_endpoint_primeFactors_gt](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L599)
- Lean declaration: [one_sub_sum_le_prod_one_sub_rational](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L626)
- Lean declaration: [rough_primeFactors_card_power_le](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L652)
- Lean declaration: [totient_rational_lower_bound_of_primeFactors_gt](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L667)
- Lean declaration: [rough_primeFactors_card_lt_quarter_of_lt_two_pow](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L722)
- Lean declaration: [three_quarters_mul_lt_totient_of_rough_lt_two_pow](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L768)
- Lean declaration: [relativePrimeFactors_card_power_le](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L822)
- Lean declaration: [relativePrimeFactors_card_lt_quarter_of_lt_two_pow](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L843)
- Lean declaration: [three_quarters_lt_relativeEulerProduct_of_lt_two_pow](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L893)
- Lean declaration: [two_mul_le_periodLcm_add_lt_two_pow](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L974)

- outgoing **specialises**: [Z38::relative_euler_product_exactly_measures_new_prime_support](BROWSER_Z38_1.md#node-678e313de141d965). The rough-support bounds turn the exact relative Euler product into a quantitative density lower bound.
- incoming **generated_by**: [Z38::every_short_actual_lcm_arithmetic_letter_is_positive](BROWSER_Z38_1.md#node-21286a404feeaf17). The quantitative coefficient bounds consume the three-quarters Euler-density estimates for rough and relative-new-prime support.

<a id="node-d1814a9a94604c36"></a>
## short_offsets_are_divisors_or_descending_foreign_prime_powers

PROVED: every positive offset below twice the cutoff is either a divisor of the period LCM or a bare prime power; in the foreign-prime-power case its predecessor divides the period LCM, both relevant endpoints have no small prime factor, the arithmetic letter is exactly the predecessor-scale letter, and the predecessor quotient is strictly smaller.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The dichotomy is confined to the stated short window. It does not classify arbitrary offsets or itself give a cofinal family of useful residues.

- Lean declaration: [lcmRayArithmeticLetter_divisor_or_primePower](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L376)
- Lean declaration: [foreignPrimePower_predecessor_dvd_periodLcm](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L403)
- Lean declaration: [foreignPrimePower_predecessor_endpoint_primeFactors_gt](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L436)
- Lean declaration: [deltaTotient_foreignPrimePower_ray_eq_predecessorLetter](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L486)
- Lean declaration: [foreignPrimePower_predecessor_quotient_lt](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L520)
- Lean declaration: [lcmRayArithmeticLetter_divisor_or_predecessorPrimePower](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L546)

- outgoing **complements**: [Z38::diagonal_arithmetic_letter_is_the_exact_totient_increment](BROWSER_Z38_1.md#node-0f6dc3562aced155). Divisor offsets use the exact quotient-scale identity, while the remaining short offsets descend through a foreign-prime-power predecessor.
- incoming **generated_by**: [Z38::every_short_actual_lcm_arithmetic_letter_is_positive](BROWSER_Z38_1.md#node-21286a404feeaf17). The positivity proof splits on the complete divisor-versus-foreign-prime-power classification.
- incoming **specialises**: [Z38::new_prime_frontier_controls_every_short_word_term](BROWSER_Z38_1.md#node-ac40cdad9bf2817d). The word-level theorem transports the short-offset dichotomy term by term and isolates the full new-prime endpoint package.

<a id="node-fc7046660c40e5a2"></a>
## terminal_totient_factor_cancels_in_two_step_carry

PROVED BARRIER: the actual odd-half terminal correction admits a positive totient factorisation and the corresponding twice-totient divisor; substituting it into the exact two-step affine carry identity cancels the same factor, so this terminal projection supplies no independent corridor escape.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The no-go conclusion concerns this specific terminal-factor projection only. It does not rule out other residue, asymmetric-loss, or longer-window mechanisms.

- Lean declaration: [exists_pos_terminalTotient_factorization_of_actualOddHalfCorrection](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1748)
- Lean declaration: [two_mul_totient_dvd_actualOddHalfCorrection_sub_following_pair](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1800)
- Lean declaration: [two_mul_affineStep_eq_terminal_sub_carry_add_two](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1820)

- outgoing **complements**: [Z38::every_short_actual_lcm_arithmetic_letter_is_positive](BROWSER_Z38_1.md#node-21286a404feeaf17). Coefficient positivity supplies a strong short-window fact, while the terminal calculation records that one tempting carry projection nevertheless cancels and cannot finish the residue argument alone.

