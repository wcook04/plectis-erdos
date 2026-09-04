# Z90_1: Erdős 249 window geometry: 2-adic locality, certificate descent, and ray limits

[All problems and zones](BROWSER.md)

<a id="node-d7135569a86f679c"></a>
## a_certified_subwindow_survives_inside_every_containing_window

PROVED WINDOW MONOTONICITY: a certificate at base N+j and depth k descends to base N at depth k+j. More generally, if [M+1,M+k] lies inside [N+1,N+L], then certifiedKill h M k implies certifiedKill h N L. Hence existence at any base M≥N descends to N, including ray cells descending to their diagonal base.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The transport moves certificates toward smaller bases or larger containing windows. It does not climb to a larger base, create a new period, or produce any certificate from scratch.

- Lean declaration: [certifiedKill_base_descent](../../ErdosProblems/Lift/AngleA2.lean#L189)
- Lean declaration: [certifiedKill_of_window_subset](../../ErdosProblems/Lift/AngleA2.lean#L230)
- Lean declaration: [exists_certifiedKill_of_base_le](../../ErdosProblems/Lift/AngleA2.lean#L240)
- Lean declaration: [exists_certifiedKill_diagonal_of_ray](../../ErdosProblems/Lift/AngleA2.lean#L248)
- Lean declaration: [lift_target_of_ray_cell](../../ErdosProblems/Lift/AngleA2.lean#L255)

- incoming **complements**: [Z90::the_low_k_bits_of_a_deep_window_are_exactly_the_far_end_depth_k_window](BROWSER_Z90_1.md#node-daf44245d9bad17d). The exact truncation congruence is the arithmetic input used to lift a certified far-end subwindow into a containing window with the same top.
- outgoing **complements**: [Z90::cofinal_certificate_supply_anywhere_above_the_lcm_diagonal_implies_irrationality](BROWSER_Z90_1.md#node-f4a737869de9c3e7). Window monotonicity turns each arbitrary supplied ray cell into the diagonal cell required by the existing irrationality reduction.
- incoming **barrier_for**: [Z90::certificate_base_descent_has_no_general_converse](BROWSER_Z90_1.md#node-f21bc41dec646d2e). The explicit finite counterexample blocks reversing the certified-window monotonicity law as an unconditional route to higher bases.
- incoming **finite_instance_of**: [Z90::the_period_five_certificate_descends_to_base_zero_at_depth_twenty_eight](BROWSER_Z90_1.md#node-510ef9f4a3d645da). The period-five certificate is a direct concrete instance of twelve-step base descent.

<a id="node-9d23e52a7f64f828"></a>
## a_nonzero_large_two_adic_factor_certifies_a_window_and_is_read_at_its_far_end

PROVED VALUATION CRITERION: if 2^v divides a window discrepancy, 2^L does not divide it, and 2^v exceeds the exclusion radius, then the window is certified. For a depth k+j window, the required 2^k divisibility may equivalently be supplied by the far-end depth-k window.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem does not establish either antecedent for the frontier windows. In particular it supplies no unexpectedly large 2-adic valuation.

Open hypotheses: ["A power-of-two divisibility bound large enough to exceed the window exclusion radius.", "Nondivisibility of the full discrepancy by its entire modulus, ensuring a nonzero residue."]

- Lean declaration: [certifiedKill_of_two_pow_dvd](../../ErdosProblems/Lift/AngleA2.lean#L353)
- Lean declaration: [certifiedKill_of_far_end_valuation](../../ErdosProblems/Lift/AngleA2.lean#L383)

- outgoing **complements**: [Z90::the_low_k_bits_of_a_deep_window_are_exactly_the_far_end_depth_k_window](BROWSER_Z90_1.md#node-daf44245d9bad17d). The valuation criterion becomes a far-end criterion precisely through the low-bit truncation equivalence.
- incoming **complements**: [Z90::prime_dilation_controls_at_most_k_over_p_plus_one_letters_in_any_depth_k_window](BROWSER_Z90_1.md#node-d9a4a8b7b7d5f6a8). The coverage ceiling quantifies how few far-end letters the exact dilation law controls, while the valuation criterion states the stronger window-wide arithmetic datum still needed.

<a id="node-f21bc41dec646d2e"></a>
## certificate_base_descent_has_no_general_converse

PROVED FINITE NO-GO: certifiedKill 1 0 5 holds, while certifiedKill 1 1 4 fails, even though the latter is the smaller contained window. Therefore certificate base descent cannot be reversed in general.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The counterexample rules out an unconditional converse only. It does not exclude a converse under additional arithmetic hypotheses or other mechanisms for climbing to larger bases.

- Lean declaration: [base_descent_converse_fails](../../ErdosProblems/Lift/AngleA2.lean#L333)

- outgoing **barrier_for**: [Z90::a_certified_subwindow_survives_inside_every_containing_window](BROWSER_Z90_1.md#node-d7135569a86f679c). The explicit finite counterexample blocks reversing the certified-window monotonicity law as an unconditional route to higher bases.

<a id="node-f4a737869de9c3e7"></a>
## cofinal_certificate_supply_anywhere_above_the_lcm_diagonal_implies_irrationality

PROVED CONDITIONAL REDUCTION: if for every threshold t₀ there is t≥t₀ and some base N≥periodLcm t carrying a certified kill at some depth, then the binary totient series is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem is only an implication. The required cofinal ray supply is not constructed here, and the result does not claim that base freedom makes that supply easier to prove.

Open hypotheses: ["A cofinal supply, over period-lcm indices, of at least one certifiedKill at an arbitrary base on or above each selected diagonal."]

- Lean declaration: [irrational_totient_series_of_lcm_ray_certificate_supply](../../ErdosProblems/Lift/AngleA2.lean#L263)

- incoming **complements**: [Z90::a_certified_subwindow_survives_inside_every_containing_window](BROWSER_Z90_1.md#node-d7135569a86f679c). Window monotonicity turns each arbitrary supplied ray cell into the diagonal cell required by the existing irrationality reduction.
- incoming **complements**: [Z90::diagonal_kill_existence_is_antitone_and_cofinal_supply_equals_total_supply](BROWSER_Z90_1.md#node-a29f400fe1b495ad). The antitone classification explains that cofinal diagonal supply is equivalent to total supply, sharpening the logical shape of the conditional reduction without proving its hypothesis.

<a id="node-a29f400fe1b495ad"></a>
## diagonal_kill_existence_is_antitone_and_cofinal_supply_equals_total_supply

PROVED LADDER CLASSIFICATION: integrality of a fixed-period tail difference propagates upward in the base. Consequently, if t≤s and a diagonal kill exists at periodLcm s, then one exists at periodLcm t; thus a cofinal supply of diagonal kills is equivalent to a kill at every index.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Antitonicity propagates certificates downward in t. It supplies no upward lift and does not prove that the predicate holds at any unbounded family of indices.

- Lean declaration: [tail_diff_int_of_base_le](../../ErdosProblems/Lift/AngleA2.lean#L275)
- Lean declaration: [exists_diagonalKill_antitone](../../ErdosProblems/Lift/AngleA2.lean#L296)
- Lean declaration: [diagonalKill_cofinal_iff_all](../../ErdosProblems/Lift/AngleA2.lean#L319)

- outgoing **complements**: [Z90::cofinal_certificate_supply_anywhere_above_the_lcm_diagonal_implies_irrationality](BROWSER_Z90_1.md#node-f4a737869de9c3e7). The antitone classification explains that cofinal diagonal supply is equivalent to total supply, sharpening the logical shape of the conditional reduction without proving its hypothesis.

<a id="node-d9a4a8b7b7d5f6a8"></a>
## prime_dilation_controls_at_most_k_over_p_plus_one_letters_in_any_depth_k_window

PROVED COVERAGE CEILING: among k consecutive offsets at any base, at most k/p+1 are divisible by p. On such covered offsets, when p is prime and coprime to the two source arguments, the lifted totient-difference letter equals (p-1) times the period-H letter; at p=67 and depth 100, at most two offsets are covered at every base.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The ceiling limits only information obtained from the displayed exact dilation law. It does not rule out control of uncovered letters by other congruences, correlations, or analytic arguments.

- Lean declaration: [ray_coverage_card_le](../../ErdosProblems/Lift/AngleA2.lean#L399)
- Lean declaration: [window_letter_dilation](../../ErdosProblems/Lift/AngleA2.lean#L427)
- Lean declaration: [window_letter_dilation_at](../../ErdosProblems/Lift/AngleA2.lean#L447)
- Lean declaration: [ray_coverage_at_67](../../ErdosProblems/Lift/AngleA2.lean#L459)

- outgoing **complements**: [Z90::a_nonzero_large_two_adic_factor_certifies_a_window_and_is_read_at_its_far_end](BROWSER_Z90_1.md#node-9d23e52a7f64f828). The coverage ceiling quantifies how few far-end letters the exact dilation law controls, while the valuation criterion states the stronger window-wide arithmetic datum still needed.

<a id="node-daf44245d9bad17d"></a>
## the_low_k_bits_of_a_deep_window_are_exactly_the_far_end_depth_k_window

PROVED LOCALITY PACKET: peeling the base letter expresses a depth-(L+1) discrepancy as a 2^L-weighted head plus the depth-L discrepancy at the next base. Iterating this gives A(h,N,k+j)≡A(h,N+j,k) mod 2^k, and therefore 2^k divides the deep discrepancy if and only if it divides the far-end depth-k discrepancy.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The congruence identifies where low-bit information lives; it does not provide any favorable valuation or nondivisibility at the far end.

- Lean declaration: [windowDiscrepancy_head_peel](../../ErdosProblems/Lift/AngleA2.lean#L123)
- Lean declaration: [windowDiscrepancy_emod_truncate](../../ErdosProblems/Lift/AngleA2.lean#L143)
- Lean declaration: [two_pow_dvd_windowDiscrepancy_iff](../../ErdosProblems/Lift/AngleA2.lean#L167)

- outgoing **complements**: [Z90::a_certified_subwindow_survives_inside_every_containing_window](BROWSER_Z90_1.md#node-d7135569a86f679c). The exact truncation congruence is the arithmetic input used to lift a certified far-end subwindow into a containing window with the same top.
- incoming **complements**: [Z90::a_nonzero_large_two_adic_factor_certifies_a_window_and_is_read_at_its_far_end](BROWSER_Z90_1.md#node-9d23e52a7f64f828). The valuation criterion becomes a far-end criterion precisely through the low-bit truncation equivalence.

<a id="node-510ef9f4a3d645da"></a>
## the_period_five_certificate_descends_to_base_zero_at_depth_twenty_eight

PROVED FINITE TRANSPORT: the certified period-five cell at base 12 and depth 16 descends to certifiedKill 5 0 28.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: One descended certificate provides no cofinal supply, no lift to other periods, and no irrationality conclusion.

- Lean declaration: [certifiedKill_five_zero_twentyeight](../../ErdosProblems/Lift/AngleA2.lean#L341)

- outgoing **finite_instance_of**: [Z90::a_certified_subwindow_survives_inside_every_containing_window](BROWSER_Z90_1.md#node-d7135569a86f679c). The period-five certificate is a direct concrete instance of twelve-step base descent.

