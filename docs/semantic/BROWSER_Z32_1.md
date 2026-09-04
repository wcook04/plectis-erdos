# Z32_1: Erdős 269 three-prime running-LCM cells, shell digits, and cofinal residue frontier

[All problems and zones](BROWSER.md)

<a id="node-87230ef6945efe7a"></a>
## affine_recurrence_unrolls_over_exact_local_window

PROVED WINDOW NORMAL FORM: every integer affine recurrence A(n+1)=b(n)A(n)+e(n) unrolls across a finite window as A(lo+len)=W(lo,len)A(lo)+F(lo,len), where W is the accumulated product and F the recursively weighted forcing; multiplying every forcing digit by a constant multiplies F by the same constant.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem accepts arbitrary radix and forcing words. It neither derives them from the Erdős series nor supplies an escaping window.

- Lean declaration: [affineRecurrence_window](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L455)
- Lean declaration: [windowForcing_const_mul](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L469)

- incoming **specialises**: [Z32::difference_forcing_has_exact_summation_by_parts](BROWSER_Z32_1.md#node-5574ac97e15ca44a). The potential identity is the affine window forcing specialised to a discrete-difference digit word.
- incoming **specialises**: [Z32::integral_carry_has_exact_window_identity](BROWSER_Z32_1.md#node-05fdd15b1edeab4a). The carry identity is the affine recurrence normal form with forcing e(n)=-B m(n).

<a id="node-fcf163f064f2ee97"></a>
## cofinal_escape_rules_out_matching_positive_reduced_carry

PROVED CONDITIONAL EXTINCTION: if the denominator-dependent CofinalLocalWindowEscape predicate holds for radix b, digit word m, and bound K, then for every positive B coprime to 30 there is no everywhere-positive integer sequence d satisfying d(n+1)=b(n)d(n)-B m(n) and |d(n)|<=K(B,n).

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: CofinalLocalWindowEscape is a named Prop supplied as a hypothesis, not a proved theorem. The result also assumes the reduced carry recurrence and does not connect it to the original series.

Open hypotheses: ["CofinalLocalWindowEscape for the actual {2,3,5} dyadic radix, exact shell-multiplicity digits, and denominator-dependent carry bound"]

- Lean declaration: [no_positive_reducedCarry_of_cofinalLocalWindowEscape](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L645)

- outgoing **depends_on_open**: [Z32::integral_carry_has_exact_window_identity](BROWSER_Z32_1.md#node-05fdd15b1edeab4a). The conditional extinction theorem reduces one selected cofinal escape window to a congruence using the exact carry-window identity.
- outgoing **implies**: [Z32::least_positive_residue_excludes_bounded_positive_state](BROWSER_Z32_1.md#node-96c600fdfd654c9f). At the endpoint of the selected window, the cofinal predicate supplies exactly the residue-above-bound hypothesis consumed by the finite modular contradiction.
- outgoing **complements**: [Z32::common_smooth_carry_factor_cancels_conditionally](BROWSER_Z32_1.md#node-c152d251c183d627). The denominator reduction and the cofinal window producer are the two independent missing bridges needed before the finite reduced-carry contradiction can address the actual series.
- incoming **barrier_for**: [Z32::finite_dyadic_window_scan_does_not_supply_cofinal_escape](BROWSER_Z32_1.md#node-34af50771134795b). Success on 106666 bounded denominator/start pairs does not meet the consumer's universal denominator and arbitrarily-late-start quantifiers.

<a id="node-c152d251c183d627"></a>
## common_smooth_carry_factor_cancels_conditionally

PROVED CONDITIONAL REDUCTION: if every integral carry state c(n) has the form S d(n) for one nonzero smooth factor S, then S cancels from c(n+1)=b(n)c(n)-S B m(n); when S is positive, positivity and the sharp bound descend to d, and d inherits the exact local-window identity with reduced denominator B.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem never proves that the actual carry shares S. Therefore it does not by itself reduce an arbitrary hypothetical rational denominator to a factor coprime with 30.

Open hypotheses: ["the problem-specific rationality-to-carry identification, including proof that every actual denominator-cleared carry state is divisible by the absorbed {2,3,5}-smooth denominator factor"]

- Lean declaration: [integralCarry_cancel_commonFactor](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L581)
- Lean declaration: [reducedCarry_pos_le_of_commonFactor](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L601)
- Lean declaration: [reducedIntegralCarry_window](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L612)

- outgoing **depends_on_open**: [Z32::fixed_smooth_factor_is_absorbed_by_running_height](BROWSER_Z32_1.md#node-21b64e550d03ddcf). Height absorption supplies the intended smooth factor, but the cancellation theorem additionally needs the unproved fact that every actual carry state is divisible by it.
- outgoing **specialises**: [Z32::integral_carry_has_exact_window_identity](BROWSER_Z32_1.md#node-05fdd15b1edeab4a). After cancelling the common smooth factor, the reduced carry inherits the same exact window identity with multiplier B.
- incoming **complements**: [Z32::cofinal_escape_rules_out_matching_positive_reduced_carry](BROWSER_Z32_1.md#node-fcf163f064f2ee97). The denominator reduction and the cofinal window producer are the two independent missing bridges needed before the finite reduced-carry contradiction can address the actual series.

<a id="node-5574ac97e15ca44a"></a>
## difference_forcing_has_exact_summation_by_parts

PROVED SUMMATION-BY-PARTS FORM: when the forcing digit is the difference V(n+1)-V(n), its accumulated window forcing equals the terminal potential minus the accumulated base times the initial potential plus the exact weighted interior correction.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The identity exposes the forcing exactly but gives no sign, magnitude, or modular anti-concentration estimate for it.

- Lean declaration: [windowForcing_difference_eq_potential](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L439)

- outgoing **specialises**: [Z32::affine_recurrence_unrolls_over_exact_local_window](BROWSER_Z32_1.md#node-87230ef6945efe7a). The potential identity is the affine window forcing specialised to a discrete-difference digit word.
- incoming **complements**: [Z32::integral_carry_has_exact_window_identity](BROWSER_Z32_1.md#node-05fdd15b1edeab4a). When the exact shell digit is a difference of smooth-count potentials, the carry window consumes the summation-by-parts forcing formula directly.

<a id="node-2575911bd3e2da89"></a>
## dyadic_block_radix_has_exact_four_letter_alphabet

PROVED EXACT ALPHABET: in every open dyadic block (2^a,2^(a+1)) there is at most one internal power from each of the 3- and 5-channels; therefore the {2,3,5} block radix is exactly one of 2, 6, 10, or 30, and in particular lies between 2 and 30.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The alphabet determines the block bases only. It does not identify the actual series carry, control the block digits, or prove cofinal residue escape.

- Lean declaration: [dyadicInternalPower_exponent_unique](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L668)
- Lean declaration: [dyadicBlockBase235_cases](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L699)
- Lean declaration: [dyadicBlockBase235_mem_interval](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L711)

- incoming **generated_by**: [Z32::finite_dyadic_window_scan_does_not_supply_cofinal_escape](BROWSER_Z32_1.md#node-34af50771134795b). The checker constructs every tested block base from the exact four-letter {2,6,10,30} radix alphabet.

<a id="node-34af50771134795b"></a>
## finite_dyadic_window_scan_does_not_supply_cofinal_escape

EXACT COMPUTATIONAL EVIDENCE WITH A HARD CEILING: the integer-only checker reproduces the three displayed certificates and, for all 106666 pairs with B<=1000, gcd(B,30)=1, and 100<=a<=500, finds an escaping window of length at most 18 (largest first-success length 14); these bounded quantifiers do not establish CofinalLocalWindowEscape for unbounded B or arbitrarily late starts.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The barrier rejects only the inference from a bounded successful scan to a cofinal theorem. It does not refute CofinalLocalWindowEscape and it does not weaken any individual finite certificate.

Open hypotheses: ["a proof uniform in every positive B coprime to 30", "escape after every requested starting index rather than only 100<=a<=500", "the rationality-to-actual-carry identification and smooth-factor divisibility"]


- outgoing **generated_by**: [Z32::dyadic_block_radix_has_exact_four_letter_alphabet](BROWSER_Z32_1.md#node-2575911bd3e2da89). The checker constructs every tested block base from the exact four-letter {2,6,10,30} radix alphabet.
- outgoing **generated_by**: [Z32::true_shell_multiplicity_is_exact_count_difference](BROWSER_Z32_1.md#node-d9d29ff3ffcb7838). Its block digits are computed from exact differences of strict smooth-count potentials, the executable counterpart of the true-shell formula.
- outgoing **barrier_for**: [Z32::cofinal_escape_rules_out_matching_positive_reduced_carry](BROWSER_Z32_1.md#node-fcf163f064f2ee97). Success on 106666 bounded denominator/start pairs does not meet the consumer's universal denominator and arbitrarily-late-start quantifiers.

<a id="node-21b64e550d03ddcf"></a>
## fixed_smooth_factor_is_absorbed_by_running_height

PROVED ABSORPTION: for bases p,q,r>1, every fixed smooth value p^i q^j r^k divides the three-prime running height once the cutoff x reaches that smooth value.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Height divisibility does not imply that a denominator-cleared carry state shares the same factor.

- Lean declaration: [smooth3Val_dvd_threePrimeHeight_of_le](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L548)

- incoming **depends_on_open**: [Z32::common_smooth_carry_factor_cancels_conditionally](BROWSER_Z32_1.md#node-c152d251c183d627). Height absorption supplies the intended smooth factor, but the cancellation theorem additionally needs the unproved fact that every actual carry state is divisible by it.

<a id="node-05fdd15b1edeab4a"></a>
## integral_carry_has_exact_window_identity

PROVED CARRY NORMAL FORM: if c(n+1)=b(n)c(n)-B m(n), then c(lo+len)=W(lo,len)c(lo)-B F(lo,len); when m is a potential difference this has the corresponding exact weighted-potential expansion.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem assumes the recurrence. The unproved problem-specific bridge must still show that the actual three-prime series produces such a carry and these digits.

- Lean declaration: [integralCarry_window](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L480)
- Lean declaration: [integralCarry_window_potential](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L532)

- outgoing **specialises**: [Z32::affine_recurrence_unrolls_over_exact_local_window](BROWSER_Z32_1.md#node-87230ef6945efe7a). The carry identity is the affine recurrence normal form with forcing e(n)=-B m(n).
- outgoing **complements**: [Z32::difference_forcing_has_exact_summation_by_parts](BROWSER_Z32_1.md#node-5574ac97e15ca44a). When the exact shell digit is a difference of smooth-count potentials, the carry window consumes the summation-by-parts forcing formula directly.
- incoming **specialises**: [Z32::common_smooth_carry_factor_cancels_conditionally](BROWSER_Z32_1.md#node-c152d251c183d627). After cancelling the common smooth factor, the reduced carry inherits the same exact window identity with multiplier B.
- incoming **depends_on_open**: [Z32::cofinal_escape_rules_out_matching_positive_reduced_carry](BROWSER_Z32_1.md#node-fcf163f064f2ee97). The conditional extinction theorem reduces one selected cofinal escape window to a congruence using the exact carry-window identity.

<a id="node-b7fe1ea4c78e60f9"></a>
## kernel_235_has_exact_negative_one_fifteen_minor

PROVED FINITE RANK CERTIFICATE: on exponent coordinates (0,0),(1,0),(0,1),(1,1) with third exponent zero, the {2,3,5} reciprocal running-LCM kernel has determinant exactly -1/15; hence this restriction has rank two and the kernel cannot factor as f(i)g(j)h(k).

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: One nonzero 2x2 minor rules out rank one only. It proves no larger rank bound, analytic independence, irrationality, or transcendence.

- Lean declaration: [kernel_235_minor_eq_neg_one_fifteen](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L721)


<a id="node-96c600fdfd654c9f"></a>
## least_positive_residue_excludes_bounded_positive_state

PROVED FINITE CONSUMER: for positive modulus C, the canonical least positive representative of x modulo C lies in {1,...,C} and is congruent to x; hence no positive integer state with absolute value at most K can be congruent to x when that representative is strictly larger than K.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This theorem consumes one escaping residue. It gives no reason that such a residue exists for the actual radix/digit word.

- Lean declaration: [leastPositiveResidue_pos_le](../../ErdosProblems/Erdos269/ResidueEscape.lean#L31)
- Lean declaration: [leastPositiveResidue_modEq](../../ErdosProblems/Erdos269/ResidueEscape.lean#L52)
- Lean declaration: [no_bounded_positive_int_state_of_leastPositiveResidue](../../ErdosProblems/Erdos269/ResidueEscape.lean#L110)

- incoming **implies**: [Z32::cofinal_escape_rules_out_matching_positive_reduced_carry](BROWSER_Z32_1.md#node-fcf163f064f2ee97). At the endpoint of the selected window, the cofinal predicate supplies exactly the residue-above-bound hypothesis consumed by the finite modular contradiction.

<a id="node-d936fd2f0cc19f22"></a>
## pure_power_count_has_closed_log_floor_sum

PROVED PURE-POWER SPECIALISATION: at cutoff p^a with p>1 and positive q,r, each admissible (q,r)-pair contributes exactly a-log_p(q^j r^k) possible p-exponents, so the strict three-prime count is the explicit restricted logarithmic floor sum.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This counts a finite strict prefix. It neither orders the infinite jump series nor estimates its tail.

- Lean declaration: [strictPExponentFiber_card_at_pow](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L143)
- Lean declaration: [restrictedFloorSum_pow_eq_restrictedLogFloorSum](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L196)
- Lean declaration: [restrictedPurePowerCount_eq_fiberSum](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L355)
- Lean declaration: [restrictedPurePowerCount_eq_restrictedFloorSum](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L362)
- Lean declaration: [restrictedPurePowerCount_eq_restrictedLogFloorSum](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L370)

- outgoing **specialises**: [Z32::strict_smooth_count_has_exact_two_dimensional_floor_sum](BROWSER_Z32_1.md#node-de8129fa350925b6). The pure-power theorem evaluates the same exact fibre decomposition at x=p^a and closes each one-dimensional fibre by an integer logarithm.
- incoming **specialises**: [Z32::true_shell_multiplicity_is_exact_count_difference](BROWSER_Z32_1.md#node-d9d29ff3ffcb7838). At pure-power endpoints the two strict prefix counts become the explicit logarithmic floor sums V_q(b) and V_p(a).
- incoming **reformulates**: [Z32::restricted_log_floor_sum_has_exact_discrete_derivative](BROWSER_Z32_1.md#node-ad88ee6b2210f375). The discrete derivative identifies the exact change between consecutive pure-power floor-sum cells rather than merely re-evaluating each endpoint independently.

<a id="node-ad88ee6b2210f375"></a>
## restricted_log_floor_sum_has_exact_discrete_derivative

PROVED CELL-INCREMENT LAW: for p,q,r>1, the increment V_p(a+1)-V_p(a) of the restricted logarithmic floor sum is exactly the number of admissible (q,r)-pairs below p^(a+1).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This computes one exact cell increment. It does not supply residue escape, randomness, or any asymptotic law for the digit word.

- Lean declaration: [restrictedLogFloorSum_succ_sub](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L209)

- outgoing **reformulates**: [Z32::pure_power_count_has_closed_log_floor_sum](BROWSER_Z32_1.md#node-d936fd2f0cc19f22). The discrete derivative identifies the exact change between consecutive pure-power floor-sum cells rather than merely re-evaluating each endpoint independently.

<a id="node-de8129fa350925b6"></a>
## strict_smooth_count_has_exact_two_dimensional_floor_sum

PROVED FINITE NORMAL FORM: for positive first base p, the number of exponent triples with p^i q^j r^k < x is exactly both the sum of the cardinalities of its p-exponent fibres over admissible (q,r) pairs and the literal restricted two-dimensional floor sum built from those fibres.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The identity is finite and exact. It is not an asymptotic smooth-number estimate, a convergence theorem, or an irrationality statement.

- Lean declaration: [strictSmoothExponent_fiber_card](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L280)
- Lean declaration: [restrictedFiberCount_eq_restrictedFloorSum](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L316)
- Lean declaration: [smoothCountLT_eq_restrictedFiberCount](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L327)
- Lean declaration: [smoothCountLT_eq_restrictedFloorSum](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L347)

- incoming **specialises**: [Z32::pure_power_count_has_closed_log_floor_sum](BROWSER_Z32_1.md#node-d936fd2f0cc19f22). The pure-power theorem evaluates the same exact fibre decomposition at x=p^a and closes each one-dimensional fibre by an integer logarithm.
- incoming **reformulates**: [Z32::true_shell_multiplicity_is_exact_count_difference](BROWSER_Z32_1.md#node-d9d29ff3ffcb7838). A true shell is the set difference of two strict prefixes, so its cardinality is the difference of the two exact count normal forms.

<a id="node-d9d29ff3ffcb7838"></a>
## true_shell_multiplicity_is_exact_count_difference

PROVED TRUE-SHELL FORMULA: for x<=y the number of literal three-prime smooth exponent triples in [x,y) is the difference of the two strict counts, equivalently the difference of their restricted fibre counts or restricted floor sums; between pure-power endpoints p^a<=q^b it is exactly V_q(b)-V_p(a).

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The shell is the actual filtered set, but the formula remains finite. No cofinal distribution or anti-concentration of the resulting digits is proved.

- Lean declaration: [strictSmoothShell_card](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L90)
- Lean declaration: [strictSmoothShell_card_eq_restrictedFiberCount_sub](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L380)
- Lean declaration: [strictSmoothShell_card_eq_restrictedFloorSum_sub](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L390)
- Lean declaration: [strictSmoothShell_card_between_purePowers](../../ErdosProblems/Erdos269/RestrictedFloorSum.lean#L400)

- outgoing **reformulates**: [Z32::strict_smooth_count_has_exact_two_dimensional_floor_sum](BROWSER_Z32_1.md#node-de8129fa350925b6). A true shell is the set difference of two strict prefixes, so its cardinality is the difference of the two exact count normal forms.
- outgoing **specialises**: [Z32::pure_power_count_has_closed_log_floor_sum](BROWSER_Z32_1.md#node-d936fd2f0cc19f22). At pure-power endpoints the two strict prefix counts become the explicit logarithmic floor sums V_q(b) and V_p(a).
- incoming **generated_by**: [Z32::finite_dyadic_window_scan_does_not_supply_cofinal_escape](BROWSER_Z32_1.md#node-34af50771134795b). Its block digits are computed from exact differences of strict smooth-count potentials, the executable counterpart of the true-shell formula.

