# Z28_1: Actual-LCM orbit, carry-period, and fixed-rank totient frontier

[All problems and zones](BROWSER.md)

<a id="node-364197bab99bf738"></a>
## actual_lcm_orbit_nonintegrality_exact_frontier

PROVED EQUIVALENCE: irrationality of the binary totient series is equivalent to cofinally many non-integral actual-LCM tail orbits at power-of-two LCM heights; irrationality in fact makes every such orbit non-integral.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The equivalence identifies the exact endpoint but supplies no unconditional cofinal non-integrality witness.

- Lean declaration: [actualLcmTailOrbit_notMem_int_of_irrational](../../Erdos249257/TotientActualLcmOrbitNonintegrality.lean#L26)
- Lean declaration: [irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply](../../Erdos249257/TotientActualLcmOrbitNonintegrality.lean#L37)
- Lean declaration: [irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply](../../Erdos249257/TotientActualLcmOrbitNonintegrality.lean#L53)

- incoming **reformulates**: [Z28::lcm_arithmetic_word_exact_certificate_representation](BROWSER_Z28_1.md#node-8a53b0eac63fc25b). The arithmetic word identifies the finite residue certificate whose soundness rules out one actual-LCM orbit integrality event; cofinal such events feed the exact frontier.
- incoming **implies**: [Z28::cofinal_short_arithmetic_kills_imply_irrationality](BROWSER_Z28_1.md#node-5f7268d2ae1a8ff2). Every short arithmetic kill gives one non-integral actual-LCM orbit, and a cofinal supply supplies the right-hand side of the exact irrationality equivalence.
- incoming **specialises**: [Z28::top_edge_residue_gap_excludes_integral_tail_difference](BROWSER_Z28_1.md#node-eb30a101442047fb). At J=0 the localized non-integral tail difference is one actual-LCM orbit non-integrality event; a cofinal supply of such gaps would feed the exact frontier.

<a id="node-ab84c330f8769592"></a>
## carry_displacement_tail_integrality_equivalence

PROVED: for every positive multiplier and tempered integral totient carry, the multiplier divides the carry displacement u(N+k)-u(N) if and only if the totient-tail difference R_(N+k)-R_N is an integer; when divisible, quotienting the displacement by the multiplier recovers that integer tail difference exactly.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is an exact local correspondence for a given tempered carry; it neither proves that the totient series is rational nor supplies a non-integral tail difference.

- Lean declaration: [totient_carryShift_cast](../../Erdos249257/TotientTailCarryPeriod.lean#L64)
- Lean declaration: [carryShift_dvd_iff_tailDiff_mem_int](../../Erdos249257/TotientTailCarryPeriod.lean#L77)
- Lean declaration: [carryShift_ediv_cast_eq_tailDiff](../../Erdos249257/TotientTailCarryPeriod.lean#L106)

- incoming **transport_of**: [Z28::rationality_mod_period_and_unbounded_rank](BROWSER_Z28_1.md#node-d262f6f36738ed16). The common eventual period modulo the carry multiplier is obtained by transporting eventual integral tail differences through the exact divisibility equivalence.

<a id="node-53d07f21183b1b76"></a>
## cofinal_short_arithmetic_kill_producer_contract

PowerTwoActualLcmShortArithmeticKillSupply is the proposition that beyond every cutoff a0 there are an exponent a and depth L with a0<=a, L<2*2^a, and a certified actual-LCM arithmetic kill at scale 2^a.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: OPEN PRODUCER. Naming this proposition does not prove that any witnesses exist beyond the two finite exponents already checked, does not establish cofinality, and does not prove Erdős #249.

Open hypotheses: ["PowerTwoActualLcmShortArithmeticKillSupply"]

- Lean declaration: [PowerTwoActualLcmShortArithmeticKillSupply](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2107)


<a id="node-5f7268d2ae1a8ff2"></a>
## cofinal_short_arithmetic_kills_imply_irrationality

PROVED CONDITIONAL: a cofinal supply of short arithmetic kills at power-of-two actual-LCM heights yields cofinal actual-LCM orbit non-integrality and therefore irrationality of the binary totient series.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The cofinal supply is open. The theorem is a consumer for that supply, not evidence that such kills continue beyond the finite exponents currently checked.

Open hypotheses: ["PowerTwoActualLcmShortArithmeticKillSupply"]

- Lean declaration: [actualLcmTailOrbit_notMem_int_of_arithmeticKill](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2095)
- Lean declaration: [actualLcmOrbitNonintegralitySupply_of_shortArithmeticKill](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2152)
- Lean declaration: [irrational_totientSeries_of_shortArithmeticKillSupply](../../Erdos249257/TotientActualLcmShortKill.lean#L63)

- outgoing **implies**: [Z28::actual_lcm_orbit_nonintegrality_exact_frontier](BROWSER_Z28_1.md#node-364197bab99bf738). Every short arithmetic kill gives one non-integral actual-LCM orbit, and a cofinal supply supplies the right-hand side of the exact irrationality equivalence.
- outgoing **depends_on_open**: [Z28::lcm_arithmetic_word_exact_certificate_representation](BROWSER_Z28_1.md#node-8a53b0eac63fc25b). The conditional endpoint consumes the exact arithmetic-kill/certified-kill identification at each selected power-of-two scale; the only open input is the cofinal supply.
- incoming **finite_instance_of**: [Z28::short_arithmetic_kills_at_exponents_four_and_six](BROWSER_Z28_1.md#node-94578b37a1706eba). The witnesses at exponents four and six instantiate the local kill shape but do not satisfy the cofinal quantifier required by the conditional endpoint.
- incoming **complements**: [Z28::fixed_rank_curvature_primitive_archimedean_bound](BROWSER_Z28_1.md#node-3d591dba604e28c7). The fixed-rank curvature supplies quantitative actual-LCM arithmetic structure but stops at the nonvanishing of a primitive integer, whereas the short-kill route requires a cofinal residue-band exclusion.

<a id="node-cd0a86989347b7ea"></a>
## fixed_rank_curvature_dyadic_divisor_is_sharp

PROVED FINITE FAMILY: at the explicit dyadic fixture with base height 2 and odd offset 3, the scaled primitive three-rank curvature is exactly -2^(n+1) for every n, so the general forced divisor has no additional hidden factor of two.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This parametric fixture proves sharpness of the general dyadic divisor, not the behavior of fixed-rank curvature at actual power-of-two LCM heights.

- Lean declaration: [fixedRankSecondDifference_dyadic_fixture_exact](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L462)

- outgoing **finite_instance_of**: [Z28::fixed_rank_curvature_dyadic_scaling_and_divisibility](BROWSER_Z28_1.md#node-a78a64548d6025ee). The explicit base-height-two, offset-three family attains exactly the divisor forced by the general dyadic scaling theorem.

<a id="node-a78a64548d6025ee"></a>
## fixed_rank_curvature_dyadic_scaling_and_divisibility

PROVED: for an even base height H and odd offset j, scaling both by 2^(n+1) scales the primitive three-rank totient second difference by exactly 2^n; because the unscaled curvature is even, the scaled curvature is divisible by 2^(n+1).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The result gives a forced dyadic divisor under a scaled-offset hypothesis. It does not prove nonzero curvature or a residue-band certificate at cofinally many actual LCM heights.

- Lean declaration: [fixedRankSecondDifference_two_pow_succ_mul](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L392)
- Lean declaration: [two_pow_succ_dvd_fixedRankSecondDifference](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L447)

- incoming **finite_instance_of**: [Z28::fixed_rank_curvature_dyadic_divisor_is_sharp](BROWSER_Z28_1.md#node-cd0a86989347b7ea). The explicit base-height-two, offset-three family attains exactly the divisor forced by the general dyadic scaling theorem.
- incoming **complements**: [Z28::fixed_rank_curvature_primitive_archimedean_bound](BROWSER_Z28_1.md#node-3d591dba604e28c7). The dyadic theorem controls the forced two-adic factor, while the clean-ray theorem removes the local factor and bounds the remaining primitive integer in Archimedean size.

<a id="node-3d591dba604e28c7"></a>
## fixed_rank_curvature_primitive_archimedean_bound

PROVED: on every clean offset j with j^2<=2^a, the rank-one, rank-two, and rank-three endpoint totients differ from a common affine main term by relative error below 2/a; their second difference is therefore explicitly o(H), divisible by 2*phi(j), and after dividing by that local factor is an integer z with |z|<(8(H/j)+4)/a and z=0 or |z|>=1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The bound normalizes the remaining arithmetic obstruction but does not prove that the primitive integer z is nonzero, let alone that it supplies cofinally many tail-difference certificates.

- Lean declaration: [fixed_rank_clean_endpoint_totient_bounds](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L172)
- Lean declaration: [fixed_rank_secondDifference_abs_lt](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L567)
- Lean declaration: [exists_primitive_fixedRankCurvature_with_bound](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L637)

- outgoing **complements**: [Z28::fixed_rank_curvature_dyadic_scaling_and_divisibility](BROWSER_Z28_1.md#node-a78a64548d6025ee). The dyadic theorem controls the forced two-adic factor, while the clean-ray theorem removes the local factor and bounds the remaining primitive integer in Archimedean size.
- outgoing **complements**: [Z28::cofinal_short_arithmetic_kills_imply_irrationality](BROWSER_Z28_1.md#node-5f7268d2ae1a8ff2). The fixed-rank curvature supplies quantitative actual-LCM arithmetic structure but stops at the nonvanishing of a primitive integer, whereas the short-kill route requires a cofinal residue-band exclusion.

<a id="node-398ea8795265a1bf"></a>
## full_terminal_dyadic_staircase_is_impossible

PROVED BARRIER: in the positive short actual-LCM window, a full terminal dyadic staircase cannot coexist with a modulus wider than the directed carry room, because its last positive arithmetic letter would be both divisible by that modulus and strictly smaller than it.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem rules out the full letter-by-letter staircase under its room and short-window hypotheses. It does not rule out punctured staircases, nonzero terminal word residues, or every growing-precision producer.

- Lean declaration: [two_pow_dvd_windowDiscrepancy_of_terminalDyadicStaircase](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L210)
- Lean declaration: [lcmRayArithmeticLetter_lt_directedRoom](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L227)
- Lean declaration: [not_actualLcmTerminalDyadicStaircase_of_room](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L251)

- incoming **repair_of**: [Z28::top_edge_residue_gap_excludes_integral_tail_difference](BROWSER_Z28_1.md#node-eb30a101442047fb). The viable repair keeps a nonzero terminal word residue and asks only that it avoid the upper carry strip, instead of requiring every terminal letter to vanish at its dyadic place.

<a id="node-8a53b0eac63fc25b"></a>
## lcm_arithmetic_word_exact_certificate_representation

PROVED REPRESENTATION: the quotient-scale LCM arithmetic word is exactly the actual diagonal window discrepancy, so its symmetric residue-band predicate LcmDiagonalArithmeticKill(t,L) is equivalent to certifiedKill(periodLcm t, periodLcm t, L).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is an exact change of representation for each fixed t and L; it does not assert that the residue band fires.

- Lean declaration: [lcmDiagonalArithmeticWord_eq_windowDiscrepancy](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1998)
- Lean declaration: [lcmDiagonalArithmeticKill_iff_certifiedKill](../../Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2045)

- outgoing **reformulates**: [Z28::actual_lcm_orbit_nonintegrality_exact_frontier](BROWSER_Z28_1.md#node-364197bab99bf738). The arithmetic word identifies the finite residue certificate whose soundness rules out one actual-LCM orbit integrality event; cofinal such events feed the exact frontier.
- incoming **depends_on_open**: [Z28::cofinal_short_arithmetic_kills_imply_irrationality](BROWSER_Z28_1.md#node-5f7268d2ae1a8ff2). The conditional endpoint consumes the exact arithmetic-kill/certified-kill identification at each selected power-of-two scale; the only open input is the cofinal supply.

<a id="node-7438243fb2f67c23"></a>
## parity_coboundary_weight_representation

The parity countermodel coefficient is parityBaseWeight(n) plus twice the sparse large-power-of-two marker at n, minus four times the preceding marker. Natural subtraction is exact because every negative spike occurs on base weight four.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This is an artificial bounded sequence matching only selected coarse totient invariants. It is not Euler's totient sequence, and its rational series does not bear directly on the truth of Erdős #249.

- Lean declaration: [parityCoboundaryWeight](../../Erdos249257/TotientParityCoboundaryCountermodel.lean#L59)


<a id="node-d262f6f36738ed16"></a>
## rationality_mod_period_and_unbounded_rank

PROVED BARRIER: if the binary totient series is not irrational, one rationality-supplied tempered integral carry has a common eventual period modulo its positive multiplier on every dyadic section, while the rational span of its canonical level-e carry kernels still has rank at least 2^e-1 for every e.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem separates quotient periodicity from torsion-free rank. It does not prove rationality, and it does not rule out every possible arithmetic rank upper bound using additional totient structure.

- Lean declaration: [carrySectionsEventuallyPeriodicMod_of_shift_dvd](../../Erdos249257/TotientTailCarryPeriod.lean#L180)
- Lean declaration: [not_irrational_totientSeries_implies_eventual_mod_period](../../Erdos249257/TotientTailCarryPeriod.lean#L200)
- Lean declaration: [not_irrational_totientSeries_implies_mod_period_and_unbounded_rank](../../Erdos249257/TotientTailCarryPeriod.lean#L224)

- outgoing **transport_of**: [Z28::carry_displacement_tail_integrality_equivalence](BROWSER_Z28_1.md#node-ab84c330f8769592). The common eventual period modulo the carry multiplier is obtained by transporting eventual integral tail differences through the exact divisibility equivalence.
- incoming **complements**: [Z28::totient_parity_aperiodicity_rational_countermodel](BROWSER_Z28_1.md#node-978f48fd8c13c6b3). The countermodel blocks coarse coefficient-word invariants, while the carry theorem separately shows that the genuine rationality consequence is quotient periodicity rather than finite rational rank.

<a id="node-94578b37a1706eba"></a>
## short_arithmetic_kills_at_exponents_four_and_six

PROVED FINITE INSTANCES: short actual-LCM arithmetic kills fire at exponent a=4 with depth 23 and at exponent a=6 with depth 93, so the corresponding actual-LCM tail orbits are non-integral; the resulting bounded supply statement reaches only cutoffs a0<=6.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The witnesses are finite and the through-six theorem hard-codes the a=6 witness. They do not establish the cofinal short-arithmetic-kill supply, a witness at a=7, or irrationality.

- Lean declaration: [lcmDiagonalArithmeticKill_two_pow_four](../../Erdos249257/TotientActualLcmShortKill.lean#L18)
- Lean declaration: [lcmDiagonalArithmeticKill_two_pow_six](../../Erdos249257/TotientActualLcmShortKill.lean#L27)
- Lean declaration: [actualLcmTailOrbit_four_and_six_notMem_int](../../Erdos249257/TotientActualLcmShortKill.lean#L35)
- Lean declaration: [powerTwoActualLcmShortArithmeticKillSupply_through_six](../../Erdos249257/TotientActualLcmShortKill.lean#L54)

- outgoing **finite_instance_of**: [Z28::cofinal_short_arithmetic_kills_imply_irrationality](BROWSER_Z28_1.md#node-5f7268d2ae1a8ff2). The witnesses at exponents four and six instantiate the local kill shape but do not satisfy the cofinal quantifier required by the conditional endpoint.

<a id="node-eb30a101442047fb"></a>
## top_edge_residue_gap_excludes_integral_tail_difference

PROVED CONDITIONAL: in the positive short actual-LCM window, a terminal residue gap at any precision m<=K excludes integrality of the corresponding actual-LCM tail difference; a punctured dyadic staircase is one sufficient producer of that one-sided gap.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The consumer is local and conditional. No cofinal supply of top-edge gaps or punctured staircases is proved here, and the condition is weaker than a symmetric certified-kill band.

Open hypotheses: ["ActualLcmTopEdgeResidueGap a J K m, or a producer such as ActualLcmTerminalPuncturedDyadicStaircase a J K m"]

- Lean declaration: [actualLcmTopEdgeResidueGap_of_puncturedDyadicStaircase](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1115)
- Lean declaration: [actualLcmTailDiff_notMem_int_of_topEdgeResidueGap](../../Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1260)

- outgoing **repair_of**: [Z28::full_terminal_dyadic_staircase_is_impossible](BROWSER_Z28_1.md#node-398ea8795265a1bf). The viable repair keeps a nonzero terminal word residue and asks only that it avoid the upper carry strip, instead of requiring every terminal letter to vanish at its dyadic place.
- outgoing **specialises**: [Z28::actual_lcm_orbit_nonintegrality_exact_frontier](BROWSER_Z28_1.md#node-364197bab99bf738). At J=0 the localized non-integral tail difference is one actual-LCM orbit non-integrality event; a cofinal supply of such gaps would feed the exact frontier.

<a id="node-978f48fd8c13c6b3"></a>
## totient_parity_aperiodicity_rational_countermodel

PROVED BARRIER: there exists a natural-valued sequence c with c(n)<=6 and c(n)<=n, matching the parity of the Euler totient at every index, not eventually periodic, and carrying arbitrarily many cofinally located marker pairs with any prescribed separation, while its binary series is exactly 3/2 and hence rational.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The countermodel rules out deductions that use only the listed coarse coefficient-word invariants. It is not the totient sequence and does not rule out arguments using quantitative totient size, factorisation, or residue information.

- Lean declaration: [parityCoboundaryWeight_mod_two_eq_totient](../../Erdos249257/TotientParityCoboundaryCountermodel.lean#L194)
- Lean declaration: [parityCoboundaryWeight_le_six](../../Erdos249257/TotientParityCoboundaryCountermodel.lean#L227)
- Lean declaration: [tsum_parityCoboundaryWeight_eq_three_halves](../../Erdos249257/TotientParityCoboundaryCountermodel.lean#L359)
- Lean declaration: [exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs](../../Erdos249257/TotientParityCoboundaryCountermodel.lean#L457)
- Lean declaration: [parityCoboundaryWeight_not_eventually_periodic](../../Erdos249257/TotientParityCoboundaryCountermodel.lean#L487)
- Lean declaration: [exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel](../../Erdos249257/TotientParityCoboundaryCountermodel.lean#L637)

- outgoing **complements**: [Z28::rationality_mod_period_and_unbounded_rank](BROWSER_Z28_1.md#node-d262f6f36738ed16). The countermodel blocks coarse coefficient-word invariants, while the carry theorem separately shows that the genuine rationality consequence is quotient periodicity rather than finite rational rank.

