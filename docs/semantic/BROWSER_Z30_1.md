# Z30_1: Reciprocal-tail cancellation metabolism and finite negative-mass rigidity

[All problems and zones](BROWSER.md)

<a id="node-de7d567d0df6c18a"></a>
## actual_tail_gcd_growth_has_exact_dynamic_reduction

PROVED REPRESENTATION AND CLASSIFICATION: reducing consecutive exact tail states by their actual gcds gives a dynamic normalised cocycle whose factor is the quotient of successive gcds; that factor lies between gcd(a,v) and its square and equals one exactly when the current multiplier is coprime to the reduced denominator.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The result describes each actual cancellation event but supplies no global anti-shadowing theorem and no termination of changing-gcd behaviour.

- Lean declaration: [tailGcdGrowthFactor](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1469)
- Lean declaration: [dynamicReducedTail_step](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1481)
- Lean declaration: [tailGcdGrowthFactor_sandwich](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1547)
- Lean declaration: [tailGcdGrowthFactor_eq_one_iff](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1565)

- outgoing **specialises**: [Z30::cancellation_factor_is_trapped_by_old_prime_overlap](BROWSER_Z30_1.md#node-83324d93be61ca13). The actual quotient of successive tail gcds satisfies the abstract reduced-step equations, so the cancellation sandwich and equality criterion apply verbatim.
- incoming **complements**: [Z30::strict_divisibility_growth_spends_exponential_size](BROWSER_Z30_1.md#node-41f5be9b047ec009). The dynamic reduction identifies what a gcd-growth event costs locally, while the strict-growth count bounds how many such events fit inside a subexponential global size budget.

<a id="node-6de6d2a8acc42ef5"></a>
## bounded_tail_plus_normalised_vanishing_forces_integral_zero

PROVED CONDITIONAL DISCRETENESS LEMMA: if a natural tail C is uniformly bounded by M and an integral error E vanishes relative to C in division-free form, then E_n=0 for all sufficiently large n.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The lemma does not supply the tail bound or normalised vanishing. Those are separate inputs in the finite negative-mass chain.

Open hypotheses: ["a uniform bound on the tail state", "division-free normalised error vanishing"]

- Lean declaration: [eventually_zero_of_bounded_tail_normalizedVanishes](../../ErdosProblems/Erdos243/SparseResetRecovery.lean#L354)

- incoming **complements**: [Z30::negative_relative_mass_bounds_each_tail_step](BROWSER_Z30_1.md#node-bc7ccd7f3c7bcd95). The relative-mass estimate is the mechanism that will supply a uniform tail bound, while the discreteness lemma consumes that bound and normalised vanishing.
- incoming **implies**: [Z30::summable_relative_growth_bounds_tail_and_forces_zero](BROWSER_Z30_1.md#node-b7faab3a939e6872). Convergence of the finite products supplies the bounded-tail premise; the bounded integral state then forces eventual zero.

<a id="node-83324d93be61ca13"></a>
## cancellation_factor_is_trapped_by_old_prime_overlap

PROVED EXACT BOUNDS: in one dynamically reduced exact-tail step between coprime state pairs, the old overlap d=gcd(a,v) divides the removed cancellation factor h and h divides d^2; moreover h=1 exactly when a and v are coprime.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The sandwich controls one cancellation factor but does not force it to be one, make the tail gcd globally stable, or rule out an infinite non-Sylvester orbit.

- Lean declaration: [cancellationFactor_sandwich](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1100)
- Lean declaration: [cancellationFactor_eq_one_iff](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1182)

- incoming **specialises**: [Z30::actual_tail_gcd_growth_has_exact_dynamic_reduction](BROWSER_Z30_1.md#node-de7d567d0df6c18a). The actual quotient of successive tail gcds satisfies the abstract reduced-step equations, so the cancellation sandwich and equality criterion apply verbatim.

<a id="node-ac1710c8c9592d4b"></a>
## finite_negative_mass_exact_orbit_forces_sylvester_recurrence

PROVED CONDITIONAL PAPER ENDPOINT: for an exact positive reciprocal-tail state, finite normalised negative mass together with division-free normalised centred-error vanishing forces a_(n+1)=a_n^2-a_n+1 eventually.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The state-system hypotheses are not derived from the growth and rationality assumptions of Erdős #243. The problem remains open; any surviving orbit must escape through divergent normalised negative mass or failure of an analytic bridge.

Open hypotheses: ["the exact integer-tail model induced by the original reciprocal series", "summability of normalised negative mass", "division-free normalised centred-error vanishing"]

- Lean declaration: [sylvesterNext_eventually_of_summable_negativeRelativeMass](../../ErdosProblems/Erdos243/SparseResetRecovery.lean#L510)

- outgoing **implies**: [Z30::finite_normalised_negative_mass_forces_eventual_zero](BROWSER_Z30_1.md#node-5ac0eb1a4e248dbd). The paper-facing theorem first obtains eventual zero centred error from finite negative mass, then applies the already-authored defect-to-Sylvester recurrence theorem.
- outgoing **complements**: [Z30::normalised_vanishing_makes_tail_gcd_growth_sparse](BROWSER_Z30_1.md#node-7b2af7c0243a95ed). Both consume normalised vanishing: one uses summable negative mass to force complete rigidity, while the other obtains long cancellation-free windows without assuming mass summability.
- outgoing **depends_on_open**: [Z30::normalised_error_vanishing_forces_subexponential_tail_growth](BROWSER_Z30_1.md#node-00098065c71ea7bf). The shared analytic input, normalised vanishing, is explicit in both theorem families and remains unproved from the original Erdős #243 hypotheses.

<a id="node-5ac0eb1a4e248dbd"></a>
## finite_normalised_negative_mass_forces_eventual_zero

PROVED CONDITIONAL ENDPOINT: if C_n>0, C_(n+1)=C_n-E_n, the errors vanish relative to C in division-free form, and the series sum (-E_n)_+/C_n converges, then the integral error E_n is zero eventually.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Normalised vanishing and summability remain assumed. This theorem constrains the exact integer state system and does not prove Erdős #243.

Open hypotheses: ["summability of normalised negative mass from the original sequence hypotheses", "division-free normalised vanishing from the original sequence hypotheses"]

- Lean declaration: [eventually_zero_of_summable_negativeRelativeMass](../../ErdosProblems/Erdos243/SparseResetRecovery.lean#L488)

- outgoing **specialises**: [Z30::summable_relative_growth_bounds_tail_and_forces_zero](BROWSER_Z30_1.md#node-b7faab3a939e6872). The finite-negative-mass theorem instantiates the generic relative-growth factor with negativeRelativeMass.
- outgoing **implies**: [Z30::negative_relative_mass_bounds_each_tail_step](BROWSER_Z30_1.md#node-bc7ccd7f3c7bcd95). The one-step negative-mass inequality verifies the growth hypothesis needed by the summable product theorem.
- incoming **implies**: [Z30::finite_negative_mass_exact_orbit_forces_sylvester_recurrence](BROWSER_Z30_1.md#node-ac1710c8c9592d4b). The paper-facing theorem first obtains eventual zero centred error from finite negative mass, then applies the already-authored defect-to-Sylvester recurrence theorem.

<a id="node-bc7ccd7f3c7bcd95"></a>
## negative_relative_mass_bounds_each_tail_step

PROVED EXACT ONE-STEP BOUND: for positive C and C_(n+1)=C_n-E_n, defining delta_n=(-E_n)_+/C_n gives C_(n+1)<=C_n(1+delta_n); positive errors contribute zero mass and negative errors account exactly for the possible upward step.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: A pointwise growth bound does not imply that the product is bounded; summability of delta remains a separate hypothesis.

- Lean declaration: [negativeRelativeMass](../../ErdosProblems/Erdos243/SparseResetRecovery.lean#L372)
- Lean declaration: [tail_growth_le_one_add_negativeRelativeMass](../../ErdosProblems/Erdos243/SparseResetRecovery.lean#L378)

- outgoing **complements**: [Z30::bounded_tail_plus_normalised_vanishing_forces_integral_zero](BROWSER_Z30_1.md#node-6de6d2a8acc42ef5). The relative-mass estimate is the mechanism that will supply a uniform tail bound, while the discreteness lemma consumes that bound and normalised vanishing.
- incoming **generalises**: [Z30::summable_relative_growth_bounds_tail_and_forces_zero](BROWSER_Z30_1.md#node-b7faab3a939e6872). The generic product lemma accepts any nonnegative summable relative-growth factor satisfying the same one-step multiplicative inequality.
- incoming **implies**: [Z30::finite_normalised_negative_mass_forces_eventual_zero](BROWSER_Z30_1.md#node-5ac0eb1a4e248dbd). The one-step negative-mass inequality verifies the growth hypothesis needed by the summable product theorem.

<a id="node-00098065c71ea7bf"></a>
## normalised_error_vanishing_forces_subexponential_tail_growth

PROVED CONDITIONAL BRIDGE: the division-free bound K|E_n|<C_n gives the local inequality K C_(n+1)<(K+1)C_n; if such near-unit bounds eventually hold for every positive K, then every fixed power C_n^r is eventually below 2^n. Thus normalised centred-error vanishing implies subexponential tail growth for an exact orbit.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Normalised vanishing is assumed, not derived from rationality and a_(n+1)/a_n^2 tending to one. The theorem controls C but does not itself force E to vanish.

Open hypotheses: ["division-free normalised centred-error vanishing"]

- Lean declaration: [tailState_localNearUnitGrowth](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1986)
- Lean declaration: [tailState_eventually_localNearUnitGrowth_of_normalizedVanishes](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2011)
- Lean declaration: [exists_nearUnitPower_rate](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2028)
- Lean declaration: [subexponential_of_eventually_nearUnitGrowth](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2105)
- Lean declaration: [tailState_subexponential_of_normalizedVanishes](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2164)

- outgoing **depends_on_open**: [Z30::sublinear_strict_growth_forces_arbitrarily_late_constant_blocks](BROWSER_Z30_1.md#node-70f05f7ad8ed56ab). Normalised vanishing supplies the subexponential input needed for sparse gcd growth, but deriving normalised vanishing from Erdős #243 remains open.
- incoming **implies**: [Z30::normalised_vanishing_makes_tail_gcd_growth_sparse](BROWSER_Z30_1.md#node-7b2af7c0243a95ed). Subexponential tail growth bounds the positive tail gcd and therefore makes its strict divisibility growth count sublinear.
- incoming **depends_on_open**: [Z30::finite_negative_mass_exact_orbit_forces_sylvester_recurrence](BROWSER_Z30_1.md#node-ac1710c8c9592d4b). The shared analytic input, normalised vanishing, is explicit in both theorem families and remains unproved from the original Erdős #243 hypotheses.

<a id="node-7b2af7c0243a95ed"></a>
## normalised_vanishing_makes_tail_gcd_growth_sparse

PROVED CONDITIONAL CONSEQUENCE: along an exact positive natural tail, normalised centred-error vanishing makes strict growth of gcd(C_n,D_n) sublinear; therefore the actual tail gcd has arbitrarily late constant blocks of every prescribed finite length.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Sparse gcd growth and arbitrarily long constant blocks do not imply eventual gcd constancy. They do not close the unbounded divergent-mass excursion regime.

Open hypotheses: ["division-free normalised centred-error vanishing"]

- Lean declaration: [tailGcd_strictGrowthCount_sublinear_of_tailSubexponential](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1439)
- Lean declaration: [tailGcd_strictGrowthCount_sublinear_of_normalizedVanishes](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2180)
- Lean declaration: [tailGcd_exists_arbitrarilyLate_constBlock_of_normalizedVanishes](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2196)

- outgoing **implies**: [Z30::normalised_error_vanishing_forces_subexponential_tail_growth](BROWSER_Z30_1.md#node-00098065c71ea7bf). Subexponential tail growth bounds the positive tail gcd and therefore makes its strict divisibility growth count sublinear.
- outgoing **implies**: [Z30::sublinear_strict_growth_forces_arbitrarily_late_constant_blocks](BROWSER_Z30_1.md#node-70f05f7ad8ed56ab). The tail-gcd sublinear event count feeds the general constant-block theorem to produce actual late gcd plateaux.
- incoming **complements**: [Z30::finite_negative_mass_exact_orbit_forces_sylvester_recurrence](BROWSER_Z30_1.md#node-ac1710c8c9592d4b). Both consume normalised vanishing: one uses summable negative mass to force complete rigidity, while the other obtains long cancellation-free windows without assuming mass summability.

<a id="node-41f5be9b047ec009"></a>
## strict_divisibility_growth_spends_exponential_size

PROVED BUDGET: if G is a positive divisibility chain, r strict increases before an endpoint force 2^r G(0)<=G(n), with the same bound after any shifted index; consequently, if every fixed power G(n)^K is eventually below 2^n, then the strict-growth count is sublinear in the division-free sense K r(n)<n.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The conclusion is density-zero/sublinear growth, not eventual constancy. It requires a positive divisibility chain and the stated power-versus-2^n subexponential input.

- Lean declaration: [strictGrowthCount](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1201)
- Lean declaration: [pow_strictGrowthCount_mul_le](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1219)
- Lean declaration: [pow_strictGrowthCountFrom_mul_le](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1244)
- Lean declaration: [strictGrowthCount_sublinear_of_subexponential](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1256)

- outgoing **complements**: [Z30::actual_tail_gcd_growth_has_exact_dynamic_reduction](BROWSER_Z30_1.md#node-de7d567d0df6c18a). The dynamic reduction identifies what a gcd-growth event costs locally, while the strict-growth count bounds how many such events fit inside a subexponential global size budget.
- incoming **implies**: [Z30::sublinear_strict_growth_forces_arbitrarily_late_constant_blocks](BROWSER_Z30_1.md#node-70f05f7ad8ed56ab). The sublinear count produced by the exponential budget is exactly the hypothesis used to find arbitrarily late blocks without a strict step.

<a id="node-70f05f7ad8ed56ab"></a>
## sublinear_strict_growth_forces_arbitrarily_late_constant_blocks

PROVED COMPACTNESS SUBSTITUTE: if the strict-growth count of a positive divisibility chain is sublinear, then beyond every lower bound and for every finite length L there is a block of length L on which the chain is exactly constant.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Arbitrarily late constant blocks of each finite length do not imply one infinite constant tail or eventual gcd stabilisation.

Open hypotheses: ["sublinear strict-growth count for the chain under study"]

- Lean declaration: [exists_aligned_noStrictGrowthBlock_of_count_bound](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1314)
- Lean declaration: [exists_arbitrarilyLate_noStrictGrowthBlock_of_sublinear](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1362)
- Lean declaration: [exists_arbitrarilyLate_constBlock_of_sublinear](../../ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1394)

- outgoing **implies**: [Z30::strict_divisibility_growth_spends_exponential_size](BROWSER_Z30_1.md#node-41f5be9b047ec009). The sublinear count produced by the exponential budget is exactly the hypothesis used to find arbitrarily late blocks without a strict step.
- incoming **depends_on_open**: [Z30::normalised_error_vanishing_forces_subexponential_tail_growth](BROWSER_Z30_1.md#node-00098065c71ea7bf). Normalised vanishing supplies the subexponential input needed for sparse gcd growth, but deriving normalised vanishing from Erdős #243 remains open.
- incoming **implies**: [Z30::normalised_vanishing_makes_tail_gcd_growth_sparse](BROWSER_Z30_1.md#node-7b2af7c0243a95ed). The tail-gcd sublinear event count feeds the general constant-block theorem to produce actual late gcd plateaux.

<a id="node-b7faab3a939e6872"></a>
## summable_relative_growth_bounds_tail_and_forces_zero

PROVED CONDITIONAL PRODUCT LEMMA: if nonnegative relative-growth factors delta_n are summable and C_(n+1)<=C_n(1+delta_n), then C is eventually uniformly bounded; with division-free normalised error vanishing, the integral error E is eventually zero.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem does not establish summability for the centred state of an Erdős #243 orbit.

Open hypotheses: ["summability of the supplied nonnegative relative-growth factors", "division-free normalised error vanishing"]

- Lean declaration: [eventually_zero_of_summable_relativeGrowth](../../ErdosProblems/Erdos243/SparseResetRecovery.lean#L423)

- outgoing **generalises**: [Z30::negative_relative_mass_bounds_each_tail_step](BROWSER_Z30_1.md#node-bc7ccd7f3c7bcd95). The generic product lemma accepts any nonnegative summable relative-growth factor satisfying the same one-step multiplicative inequality.
- outgoing **implies**: [Z30::bounded_tail_plus_normalised_vanishing_forces_integral_zero](BROWSER_Z30_1.md#node-6de6d2a8acc42ef5). Convergence of the finite products supplies the bounded-tail premise; the bounded integral state then forces eventual zero.
- incoming **specialises**: [Z30::finite_normalised_negative_mass_forces_eventual_zero](BROWSER_Z30_1.md#node-5ac0eb1a4e248dbd). The finite-negative-mass theorem instantiates the generic relative-growth factor with negativeRelativeMass.

