# Z07_1: Mersenne-Lambert ladder, gcd moments and Stern-Brocot geometry: where the #249 constant sits

[All problems and zones](BROWSER.md)

<a id="node-0d994d7f3a201d49"></a>
## continuant_defect_sensitivity

Writing each positive run length as 1 + e_i, the run-boundary coordinates equal their Fibonacci values plus an exactly computed nonnegative defect polynomial; deleting every mixed monomial gives a linear lower bound, the linear part dominates term by term, and the ordered linear coefficients admit the uniform floor F_{r+1} per unit of total defect, so height >= F_{r+3} + F_{r+1} * sum e_i. A single defect e at position i is exactly linear with coefficient F_{i+2} F_{r-i+1} = F_{r+1} + F_i F_{r-i-1}, and the mixed term is strictly positive as soon as the newest and some older defect are both positive.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [runBoundaryPair_defectRunLengths](../../Erdos249257/SternBrocotRunGeometry.lean#L244)
- Lean declaration: [runHeight_defectRunLengths](../../Erdos249257/SternBrocotRunGeometry.lean#L263)
- Lean declaration: [runHeight_defect_fib_sum_lower](../../Erdos249257/SternBrocotRunGeometry.lean#L343)
- Lean declaration: [oneSiteWeight_eq_base_add](../../Erdos249257/SternBrocotRunGeometry.lean#L358)
- Lean declaration: [runHeight_oneSiteDefect](../../Erdos249257/SternBrocotRunGeometry.lean#L413)
- Lean declaration: [linearDefectPair_first_lt_exact_of_head_tail_pos](../../Erdos249257/SternBrocotRunGeometry.lean#L377)

- outgoing **generalises**: [Z07::fibonacci_height_floor](BROWSER_Z07_1.md#node-caa09694be865178). the exact defect expansion recovers the Fibonacci floor at zero defect and quantifies the gain away from the unit spine.

<a id="node-0c4e3b1e6a2be76d"></a>
## coprime_pair_mass_bridge

For 0 <= r < 1, summing r^{a+b} over coprime pairs with a >= 1 (b free) gives sum_n phi(n) r^n, and restricting to a, b >= 1 gives sum_n phi(n) r^n - r. At r = 1/2 the #249 constant is exactly the half-open coprime-pair mass, and S - 1/2 is the strictly positive coprime-pair mass.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Open hypotheses: ["irrationality of the coprime-pair mass sum_{gcd(a,b)=1, a,b>=1} 2^{-(a+b)} is unproved and equals S - 1/2, so it is exactly Erdos #249"]

- Lean declaration: [tsum_coprime_pair_pow_eq_tsum_totient_mul_pow](../../Erdos249257/GeometricCoprimality.lean#L120)
- Lean declaration: [tsum_pos_coprime_pair_pow](../../Erdos249257/GeometricCoprimality.lean#L182)

- outgoing **reformulates**: [Z07::lambert_positive_lift_of_249](BROWSER_Z07_1.md#node-31acef136518144f). same constant S, now as a two-variable visible-lattice mass instead of a Mersenne-weighted divisor series.
- incoming **implies**: [Z07::visible_point_count_totient](BROWSER_Z07_2.md#node-3b70ff2cf178e294). the finite antidiagonal count is the coefficient extracted by the antidiagonal regrouping.
- incoming **finite_instance_of**: [Z07::induced_run_layer_masses](BROWSER_Z07_1.md#node-2f90e778c640aa02). computes the depth-0 and depth-1 run strata of the same positive coprime-pair mass exactly.
- incoming **equivalent_to**: [Z01::visible_lattice_coprimality](BROWSER_Z01_2.md#node-b0d79ae7dbb72785). totient_series_eq_half_add_visible_coprime_pairs and tsum_pos_coprime_pair_pow both state S - 1/2 = base-2 mass of coprime pairs, via card_antidiagonal_filter_pos_coprime.
- incoming **specialises**: [Z01::visible_lattice_coprimality](BROWSER_Z01_2.md#node-b0d79ae7dbb72785). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18229 `totient_series_eq_half_add_visible_coprime_pairs := GeometricCoprimality.tsum_pos_coprime_pair_pow`; Z07 states the coprime-pair mass identity for every 0 <= r < 1, Z01 keeps only the r = 1/2 instance.

<a id="node-caa09694be865178"></a>
## fibonacci_height_floor

An alternating word with r nonempty runs has run-boundary coordinates at least F_{r+2} and F_{r+1} and height at least F_{r+3}, in both run and tree coordinates; the all-unit spine attains equality, with run-boundary pair exactly (F_{r+2}, F_{r+1}) and height exactly F_{r+3}.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [runBoundaryPair_fib_lower](../../Erdos249257/SternBrocotRunGeometry.lean#L158)
- Lean declaration: [runHeight_fib_lower](../../Erdos249257/SternBrocotRunGeometry.lean#L185)
- Lean declaration: [runBoundaryPair_replicate_one](../../Erdos249257/SternBrocotRunGeometry.lean#L200)
- Lean declaration: [runHeight_replicate_one](../../Erdos249257/SternBrocotRunGeometry.lean#L214)

- incoming **implies**: [Z07::run_coordinate_normalisation](BROWSER_Z07_1.md#node-669163a5d938cf84). the tree-facing form of the floor is obtained by transporting the run-coordinate floor along sbHeight_runWord.
- incoming **generalises**: [Z07::continuant_defect_sensitivity](BROWSER_Z07_1.md#node-0d994d7f3a201d49). the exact defect expansion recovers the Fibonacci floor at zero defect and quantifies the gain away from the unit spine.
- incoming **reformulates**: [Z07::fibonacci_partial_sum_denominator_scale](BROWSER_Z07_1.md#node-c0e53492ea173d95). records that the accumulated denominator exponent sits exactly two below the same F_{r+3} height scale.
- incoming **reformulates**: [Z01::stern_brocot_run_geometry](BROWSER_Z01_2.md#node-95bba30642ae44bd). stern_brocot_run_height_fib_lower / stern_brocot_unit_run_height_eq_fib and runHeight_fib_lower / runHeight_replicate_one are the same Fibonacci run-height floor with equality on the all-unit spine.
- incoming **alias_of**: [Z01::stern_brocot_run_geometry](BROWSER_Z01_2.md#node-95bba30642ae44bd). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18391/18399 re-export `SternBrocotRunGeometry.runHeight_fib_lower` and `runHeight_replicate_one`; identical Fibonacci floor and spine equality.

<a id="node-c0e53492ea173d95"></a>
## fibonacci_partial_sum_denominator_scale

The sum of F_{j+2} for j < r equals F_{r+3} - 2; i.e. the natural denominator exponent accumulated along the unit-run spine sits exactly two below the minimum run-height scale.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [naturalRunDenominatorExponent_add_two](../../Erdos249257/SternBrocotRunGeometry.lean#L491)

- outgoing **reformulates**: [Z07::fibonacci_height_floor](BROWSER_Z07_1.md#node-caa09694be865178). records that the accumulated denominator exponent sits exactly two below the same F_{r+3} height scale.
- incoming **alias_of**: [Z01::stern_brocot_run_geometry](BROWSER_Z01_2.md#node-95bba30642ae44bd). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18421 `stern_brocot_natural_run_denominator_exponent_add_two := SternBrocotRunGeometry.naturalRunDenominatorExponent_add_two`.

<a id="node-9e283154d7db3cb9"></a>
## finite_atom_determinant_clearing_barrier

For a square matrix whose (i,j) entry is a Mersenne tail atom of conductor d_j at index idx(i,j), the determinant equals an integer determinant of 2-power entries divided by the product of the column Mersenne denominators; hence multiplying by that product recovers an integer exactly, and whenever the integer numerator determinant is nonzero the cleared quantity has absolute value at least one. The same holds with integer column weights, the weights simply multiplying the numerator determinant.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Rules out ONLY this: manufacturing a nonzero cleared value smaller than 1 from a square minor in which each column carries exactly one Mersenne denominator, when the integer numerator determinant is nonzero. It does NOT rule out: (a) the numerator determinant being zero (the degenerate case that any real attack must handle); (b) the RATIO between the cleared integer and the size of the clearing product prod_j (2^{d_j} - 1) being small, which is precisely the quantity a Diophantine irrationality argument needs — the theorem bounds the integer, never the ratio; (c) non-square or rectangular linear forms; (d) minors whose columns carry more than one conductor or a shared denominator; (e) limiting/infinite-tail constructions where the number of atoms grows with the horizon; (f) any non-determinantal certificate. It is not an irrationality statement for the totient series, as the module docstring states. MODELLING GAP: nothing in the Lean ties these matrices to #249. The conductors d, the index array idx and the weights w are arbitrary; grep confirms MersenneTailAtoms.lean never mentions primWeight, the totient, or any object from MersenneLambertLadder (which it imports but does not use), so the docstring's 'in the totient application the weights are v * A(d_j)' is documentation, not formalised content. The atom step law mersenneTailAtom_step is also unused by every theorem in the module.

- Lean declaration: [det_mersenneAtomMatrix](../../Erdos249257/MersenneTailAtoms.lean#L94)
- Lean declaration: [mersenneAtom_denominatorProduct_mul_det](../../Erdos249257/MersenneTailAtoms.lean#L122)
- Lean declaration: [one_le_abs_mersenneAtom_cleared_det](../../Erdos249257/MersenneTailAtoms.lean#L138)
- Lean declaration: [weightedMersenneAtom_denominatorProduct_mul_det](../../Erdos249257/MersenneTailAtoms.lean#L158)
- Lean declaration: [one_le_abs_weightedMersenneAtom_cleared_det](../../Erdos249257/MersenneTailAtoms.lean#L181)

- outgoing **barrier_for**: [Z07::lambert_positive_lift_of_249](BROWSER_Z07_1.md#node-31acef136518144f). targets the finite pointed-atom determinant route to a small nonzero integer out of the primitive-conductor Mersenne expansion.

<a id="node-e13974d93e7d6998"></a>
## gcd_divisibility_factorisation

For every positive d, the base-2 mass of the set of pairs (a,b) with a, b >= 1 and d dividing both is exactly 1/(2^d - 1)^2 — the divisibility event on the pair factorises into the two coordinate events.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq](../../Erdos249257/GcdMomentCalculus.lean#L266)

- outgoing **reformulates**: [Z07::squared_kernel_zeta_rung](BROWSER_Z07_1.md#node-94b26f9d541d4fcd). supplies the probability reading P(d | gcd) = 1/(2^d - 1)^2 of the squared kernel; it is a gloss, not used in the rung's proof.
- incoming **reformulates**: [Z01::gcd_moment_squared_lambert](BROWSER_Z01_1.md#node-1e4f5f5eeed01a3b). Shared declaration tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq: each pair-divisibility event has base-2 mass 1/(2^d-1)^2, the probabilistic reading of the squared Mersenne reciprocal.
- incoming **alias_of**: [Z01::gcd_moment_squared_lambert](BROWSER_Z01_1.md#node-1e4f5f5eeed01a3b). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18328 `tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq := GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`; Z07's node is exactly this single base-2 statement.

<a id="node-6cd68e0a2e072191"></a>
## gcd_layer_normalisation

For 0 <= r < 1, summing the strictly positive coprime-pair mass evaluated at r^{g+1} over all g >= 0 gives (r/(1-r))^2, the whole positive-quadrant mass; at r = 1/2 the layer masses sum to 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tsum_gcd_layer_pos_coprime_pow](../../Erdos249257/GeometricCoprimality.lean#L328)
- Lean declaration: [tsum_gcd_layer_pos_coprime_half_eq_one](../../Erdos249257/GeometricCoprimality.lean#L480)

- incoming **implies**: [Z07::totient_lambert_tail_evaluation](BROWSER_Z07_1.md#node-97f6265ebaa98171). after the layer/antidiagonal Fubini swap the layer sum collapses onto the tail Lambert value.
- outgoing **implies**: [Z07::reduced_direction_law](BROWSER_Z07_1.md#node-5096670b26a83467). expanding each Mersenne reciprocal as its geometric layer series and swapping reduces the slope-mass sum to the layer normalisation at r = 1/2.
- incoming **specialises**: [Z01::visible_lattice_coprimality](BROWSER_Z01_2.md#node-b0d79ae7dbb72785). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18269 `tsum_visible_coprime_gcd_layers_eq_one := GeometricCoprimality.tsum_gcd_layer_pos_coprime_half_eq_one`; Z07 owns the general-r gcd-layer identity of which this is the r = 1/2 evaluation.

<a id="node-2f90e778c640aa02"></a>
## induced_run_layer_masses

Exact run heights at small parameters: a single run of length n has height n + 2 and two alternating runs of lengths m, n have height (m+1)(n+1) + 1. Consequently the depth-0 stratum carries base-2 mass 1/4 and the two orientations of a single positive run together carry mass exactly 1/2.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The word 'stratum' is not earned by the Lean. zeroRunMass and oneRunMass are DEFINITIONS: zeroRunMass := (1/2)^runHeight [] and oneRunMass := sum_n 2 * (1/2)^runHeight [n+1], where the factor 2 for 'the two orientations' is stipulated in the definition, not derived. No declaration in this module, in CertificateKernel (which only re-exports the two values verbatim at lines 18412-18417), or anywhere else in the repository proves that these quantities are the layers of the positive coprime-pair mass sum_{gcd(a,b)=1} 2^{-(a+b)}, nor that distinct run words give distinct pairs, nor that the layers are disjoint or exhaustive. So 'the depth-0 stratum carries mass 1/4' is a statement about a defined real number, not a proved decomposition of the #249 constant.

- Lean declaration: [runHeight_single](../../Erdos249257/SternBrocotRunGeometry.lean#L440)
- Lean declaration: [runHeight_pair](../../Erdos249257/SternBrocotRunGeometry.lean#L446)
- Lean declaration: [zeroRunMass_eq_quarter](../../Erdos249257/SternBrocotRunGeometry.lean#L462)
- Lean declaration: [oneRunMass_eq_half](../../Erdos249257/SternBrocotRunGeometry.lean#L467)

- outgoing **finite_instance_of**: [Z07::coprime_pair_mass_bridge](BROWSER_Z07_1.md#node-0c4e3b1e6a2be76d). computes the depth-0 and depth-1 run strata of the same positive coprime-pair mass exactly.
- incoming **alias_of**: [Z01::stern_brocot_run_geometry](BROWSER_Z01_2.md#node-95bba30642ae44bd). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18405/18411/18415 re-export `SternBrocotRunGeometry.runHeight_pair`, `zeroRunMass_eq_quarter`, `oneRunMass_eq_half`.

<a id="node-31acef136518144f"></a>
## lambert_positive_lift_of_249

For 0 <= r < 1, sum_{d>=1} A(d) r^d/(1-r^d) = sum_{n>=1} phi(n) r^n with A = phi * mu >= 0; at r = 1/2 this says the #249 constant S = sum phi(n)/2^n equals the positive Erdos-Borwein-shaped series sum_{d>=1} A(d)/(2^d - 1). The identity relocates #249 into the positive Mersenne-reciprocal family; it decides nothing about irrationality.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: known_classical.

Open hypotheses: ["irrationality of sum_{n>=1} phi(n)/2^n (Erdos #249) is unproved; the identity transports it to the equally unproved irrationality of sum_{d>=1} A(d)/(2^d - 1)", "whether the Erdos 1948 congruence mechanism tolerates a weight with A(p) = p - 2 is not proved anywhere in the corpus (stated as open in the module docstring)"]

- Lean declaration: [tsum_primWeight_lambert](../../Erdos249257/MersenneLambertLadder.lean#L471)
- Lean declaration: [tsum_primWeight_div_two_pow_sub_one](../../Erdos249257/MersenneLambertLadder.lean#L601)

- outgoing **specialises**: [Z07::signed_linear_growth_lambert_engine](BROWSER_Z07_1.md#node-f365b709a4311782). the positive lift is the engine at w = A, using A * zeta = phi.
- incoming **equivalent_to**: [Z07::moebius_square_lens_of_249](BROWSER_Z07_1.md#node-a9f26d2d7d41fdbc). both are exact identities for the same open constant S, so each is irrational precisely when the other is.
- incoming **reformulates**: [Z07::coprime_pair_mass_bridge](BROWSER_Z07_1.md#node-0c4e3b1e6a2be76d). same constant S, now as a two-variable visible-lattice mass instead of a Mersenne-weighted divisor series.
- incoming **barrier_for**: [Z07::primweight_unbounded](BROWSER_Z07_1.md#node-264ae9c1322e8d89). documented as blocking the corpus's bounded eventually-periodic weighted Erdos-series engine from consuming the positive lift; the Lean statement itself scopes no engine.
- incoming **barrier_for**: [Z07::primitive_euler_index_no_lift_barrier](BROWSER_Z07_1.md#node-0913ec3431f6b924). forbids a single fixed integer index for the integral Euler/Witt realisation of the primitive determinant attached to the positive lift.
- incoming **barrier_for**: [Z07::finite_atom_determinant_clearing_barrier](BROWSER_Z07_1.md#node-9e283154d7db3cb9). targets the finite pointed-atom determinant route to a small nonzero integer out of the primitive-conductor Mersenne expansion.
- incoming **equivalent_to**: [Z01::totient_series_moebius_square_lens](BROWSER_Z01_2.md#node-b089feaf4597b079). Shared declaration tsum_primWeight_div_two_pow_sub_one_eq_totient_series: S = sum_d (phi*mu)(d)/(2^d-1), the positive Erdos-Borwein-shaped lift of #249.
- outgoing **transport_of**: [Z01::support_coefficient_representation](BROWSER_Z01_2.md#node-950d0bc2e85796ab). tsum_primWeight_div_two_pow_sub_one puts S = sum_d A(d)/(2^d-1) with A = phi*mu >= 0, i.e. relocates #249 into the weighted Erdos-series family weightedErdosSeries_eq_tsum_weightedCoeff that Z01 normalises; the weight A is unbounded (primWeight_not_bounded), so it escapes the settled periodic/bounded-weight members.

<a id="node-76e8be10a56dc445"></a>
## lambert_rung_moebius_rational

For 0 <= r < 1, sum_{d>=1} mu(d) r^d/(1-r^d) = r; in particular sum_{d>=1} mu(d)/(2^d - 1) = 1/2 exactly.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tsum_moebius_lambert](../../Erdos249257/MersenneLambertLadder.lean#L442)
- Lean declaration: [tsum_moebius_div_two_pow_sub_one_eq_half](../../Erdos249257/MersenneLambertLadder.lean#L587)

- outgoing **specialises**: [Z07::signed_linear_growth_lambert_engine](BROWSER_Z07_1.md#node-f365b709a4311782). the mu rung is the engine at w = mu, using mu * zeta = eps.
- incoming **barrier_for**: [Z10::mobius_sign_truncation_overshoots_one_half](BROWSER_Z10_2.md#node-5310e365367dca64). tsum_negativeMobius_eq_half_add_positiveMobiusTail is literally the sign split of tsum_moebius_div_two_pow_sub_one_eq_half (sum mu(d)/(2^d - 1) = 1/2); half_lt_tsum_negativeMobius then shows the negative-Mobius Boolean truncation exceeds 1/2 by at least 1/63, so the rational Lambert rung cannot be converted into a Boolean Mersenne support realising 1/2.
- incoming **equivalent_to**: [Z01::lambert_ladder_rational_rungs](BROWSER_Z01_1.md#node-4d6cc8cc64c5cf91). Shared declaration tsum_moebius_div_two_pow_sub_one_eq_half: the rational rung L(mu) = 1/2.
- incoming **specialises**: [Z01::lambert_ladder_rational_rungs](BROWSER_Z01_1.md#node-4d6cc8cc64c5cf91). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18106 `tsum_moebius_div_two_pow_sub_one_eq_half := MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half`, the r = 1/2 case of Z07's r-parametric `tsum_moebius_lambert`.

<a id="node-d6a59f5238058fa9"></a>
## lambert_rung_totient_rational

For 0 <= r < 1, sum_{d>=1} phi(d) r^d/(1-r^d) = sum_{n>=1} n r^n; in particular sum_{d>=1} phi(d)/(2^d - 1) = 2 exactly.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tsum_totient_lambert](../../Erdos249257/MersenneLambertLadder.lean#L428)
- Lean declaration: [tsum_totient_div_two_pow_sub_one_eq_two](../../Erdos249257/MersenneLambertLadder.lean#L575)

- outgoing **specialises**: [Z07::signed_linear_growth_lambert_engine](BROWSER_Z07_1.md#node-f365b709a4311782). the phi rung is the engine at w = phi, using phi * zeta = Id.
- incoming **specialises**: [Z07::totient_lambert_tail_evaluation](BROWSER_Z07_1.md#node-97f6265ebaa98171). the tail evaluation is the phi rung with its d = 1 term peeled off.
- incoming **equivalent_to**: [Z01::lambert_ladder_rational_rungs](BROWSER_Z01_1.md#node-4d6cc8cc64c5cf91). Shared declaration tsum_totient_div_two_pow_sub_one_eq_two: the rational rung L(phi) = 2.
- incoming **specialises**: [Z01::lambert_ladder_rational_rungs](BROWSER_Z01_1.md#node-4d6cc8cc64c5cf91). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18101 `tsum_totient_div_two_pow_sub_one_eq_two := MersenneLambertLadder.tsum_totient_div_two_pow_sub_one_eq_two`, which Z07 owns as the r = 1/2 evaluation of the r-parametric identity `tsum_totient_lambert` (sum phi(d) r^d/(1-r^d) = sum n r^n for 0 <= r < 1).

<a id="node-0752c5744baee041"></a>
## locked_residual_countermodel

Taking the residual weights to be the inverse pivot phases (unit modulus when the pivots are unit modulus), any row with exponent one becomes identically 1 while the coefficient-side determinant is untouched; so a nonzero minor and the presence of the locked bad first-harmonic row coexist at every rank.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out ONLY residual-BLIND standalone certificates: criteria that look at rank, determinant nonvanishing, or determinant magnitude of the residual-weighted monomial matrix and nothing else, as evidence that the exponent-one row does not reconstruct the phase 1. It does NOT rule out, as the module docstring states, determinants whose rows satisfy an additional arithmetic coupling identity; nor certificates that inspect the residual values themselves, nor non-determinantal certificates, nor criteria at a fixed non-unit residual normalisation. Nothing here bears on the irrationality of the #249 constant. MODELLING GAP: ResidualGaugeObstruction.lean imports only Mathlib and never mentions the totient, primWeight, a Mersenne denominator, or any other #249 object; e, z and W are arbitrary. Which real proof strategy is being closed is therefore fixed entirely by the docstring's vocabulary ('supplier column', 'first-harmonic certificate', 'distinguished phase 1'), none of which is a Lean definition. The theorem is a true statement about arbitrary complex monomial matrices; its status as a barrier for a #249 method family is an unverified identification, and the earlier corpus incident (a barrier published as closing a method family that a weaker third engine escaped) is the precise failure mode to guard here.

- Lean declaration: [residualMonomialMatrix_locked_row_one](../../Erdos249257/ResidualGaugeObstruction.lean#L85)
- Lean declaration: [locked_reconstruction_preserves_nonzero_minor](../../Erdos249257/ResidualGaugeObstruction.lean#L94)

- incoming **implies**: [Z07::residual_gauge_determinant_factorisation](BROWSER_Z07_1.md#node-9c5d62622df1cbfa). the countermodel is the diagonal-gauge factorisation evaluated at the inverse pivot phases.
- incoming **generalises**: [Z07::row_dependent_residual_countermodel](BROWSER_Z07_1.md#node-ca634ef766da9059). extends the countermodel from column-only gauges to residuals varying across rows as well.

<a id="node-6fd380f7bc24b94d"></a>
## mersenne_tail_atom_carry

For the periodic tail atom omega_d(N) = 2^{N mod d}/(2^d - 1), one has 2*omega_d(N) - omega_d(N+1) = 1 when d divides N+1 and 0 otherwise: the atom doubles except at its unique wrap point, where the Mersenne numerator contributes exactly one carry.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [mersenneTailAtom_step](../../Erdos249257/MersenneTailAtoms.lean#L28)


<a id="node-cf88b87fcf275c78"></a>
## moebius_divisor_sum_substrate

Elementary Mobius facts used by the ladder: |mu(n)| <= 1; sum_{e|n} mu(e) = [n = 1]; sum_{e|n} mu(e)(n/e) = phi(n); and the totient recast as an integer-valued arithmetic function.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [abs_moebius_le_one](../../Erdos249257/MersenneLambertLadder.lean#L396)
- Lean declaration: [sum_divisors_moebius](../../Erdos249257/MersenneLambertLadder.lean#L402)
- Lean declaration: [sum_divisors_moebius_mul_div](../../Erdos249257/MersenneLambertLadder.lean#L412)
- Lean declaration: [totientZ](../../Erdos249257/MersenneLambertLadder.lean#L239)


<a id="node-ef429d05803186c1"></a>
## moebius_incidence_unimodularity_barrier

The finite Mobius incidence matrix on jet coordinates q, ..., q^N, with entry mu((i+1)/(j+1)) when (j+1) divides (i+1) and 0 otherwise, is lower triangular with unit diagonal, has determinant 1, is a unit over the integers, has linearly independent columns, and its mulVec map is injective; hence the only integer coefficient vector whose companion jet vanishes at horizon N is zero.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: Rules out ONLY a nontrivial integer-linear relation among the finitely many Mobius companion jets at a fixed horizon N — i.e. a rank reduction / incidence quotient of the finite jet matrix. It does NOT establish, and the module docstring explicitly disclaims, the global statement that 1, the totient series, and finitely many Mobius dilates are linearly independent over Q(q); that needs separate analytic number theory. It also does not constrain relations with coefficients in Q(q) or in a larger ring, relations involving the constant 1 or the series value itself (the matrix has no such row/column), or any relation at a horizon-independent limit. No irrationality statement for #249 follows. MODELLING GAP: the phrase 'companion jet' is not defined in Lean. incidenceMobiusMatrix N is DEFINED entry-by-entry as mu((i+1)/(j+1)) on the divisibility pattern; there is no Lean object for the Mobius companion series M_mu(q^r), no theorem identifying this matrix with the jet matrix of any actual series, and the module (which imports MersenneLambertLadder) uses nothing from it and never mentions primWeight or the totient. So the reading 'the only integer coefficient vector whose companion jet vanishes at horizon N is zero' rests on an unformalised identification; what is machine-checked is that one explicitly written unitriangular integer matrix is invertible.

- Lean declaration: [incidenceMobius_det_eq_one](../../Erdos249257/IncidenceQuotientHermitePade.lean#L56)
- Lean declaration: [mobiusCompanionJet_linearIndependent](../../Erdos249257/IncidenceQuotientHermitePade.lean#L68)
- Lean declaration: [mobiusCompanionJetMap_eq_zero_iff](../../Erdos249257/IncidenceQuotientHermitePade.lean#L81)
- Lean declaration: [finiteIncidenceQuotientRelation_iff](../../Erdos249257/IncidenceQuotientHermitePade.lean#L97)

- outgoing **barrier_for**: [Z07::moebius_square_lens_of_249](BROWSER_Z07_1.md#node-a9f26d2d7d41fdbc). rejects a finite rank reduction among Mobius companion jets, i.e. the incidence-quotient shortcut in a Hermite-Pade attack on the Mobius lens.

<a id="node-a9f26d2d7d41fdbc"></a>
## moebius_square_lens_of_249

For 0 <= r < 1, sum_{d>=1} mu(d) r^d/(1-r^d)^2 = sum_{n>=1} phi(n) r^n (via mu * Id = phi); at r = 1/2 this gives S = 1/2 + sum_{d>=1} mu(d)/(2^d - 1)^2, together with absolute convergence of both Mersenne and squared-Mersenne Mobius series. Equivalently the level-2 Mobius rung L2(mu) = S - 1/2.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: known_classical.

Open hypotheses: ["irrationality of sum_{d>=1} mu(d)/(2^d - 1)^2 is unproved and is equivalent to Erdos #249 by this identity"]

- Lean declaration: [tsum_moebius_lambert_sq](../../Erdos249257/MersenneLambertLadder.lean#L491)
- Lean declaration: [tsum_totient_half_pow_eq_half_add_moebius_sq](../../Erdos249257/MersenneLambertLadder.lean#L665)
- Lean declaration: [summable_moebius_div_mersenne_sq](../../Erdos249257/MersenneLambertLadder.lean#L637)

- outgoing **specialises**: [Z07::signed_linear_growth_lambert_engine](BROWSER_Z07_1.md#node-f365b709a4311782). the squared lens is the squared engine at w = mu, using mu * Id = phi.
- outgoing **equivalent_to**: [Z07::lambert_positive_lift_of_249](BROWSER_Z07_1.md#node-31acef136518144f). both are exact identities for the same open constant S, so each is irrational precisely when the other is.
- incoming **barrier_for**: [Z07::moebius_incidence_unimodularity_barrier](BROWSER_Z07_1.md#node-ef429d05803186c1). rejects a finite rank reduction among Mobius companion jets, i.e. the incidence-quotient shortcut in a Hermite-Pade attack on the Mobius lens.
- incoming **equivalent_to**: [Z01::totient_series_moebius_square_lens](BROWSER_Z01_2.md#node-b089feaf4597b079). totient_series_eq_half_add_moebius_mersenne_square and tsum_totient_half_pow_eq_half_add_moebius_sq are the same identity S = 1/2 + sum_d mu(d)/(2^d-1)^2, so irrationality of S and of the squared-Mersenne Moebius series are interchangeable.
- incoming **transport_of**: [Z05::squared_mersenne_enclosure_of_actual_diagonal](BROWSER_Z05_2.md#node-b188d68d0d565e58). The enclosure centre Z_H + C_H(1/2 + sum_{d<=D} mu(d)/(2^d-1)^2) is the finite truncation of totientSeries_eq_pnat_half_pow, the same identity Z07 proves as tsum_totient_half_pow_eq_half_add_moebius_sq.

<a id="node-fb2deb554e2d9398"></a>
## primitive_conductor_weight_arithmetic

A = phi * mu (Dirichlet convolution) is multiplicative, satisfies A * zeta = phi, so sum_{e|n} A(e) = phi(n); A(p^k) = phi(p^k) - phi(p^{k-1}), A(p) = p - 2, A(p^2) = (p-1)^2, A(2) = 0, A >= 0 pointwise, and A(n) <= phi(n).

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [primWeight](../../Erdos249257/MersenneLambertLadder.lean#L252)
- Lean declaration: [primWeight_mul_zeta](../../Erdos249257/MersenneLambertLadder.lean#L259)
- Lean declaration: [sum_divisors_primWeight](../../Erdos249257/MersenneLambertLadder.lean#L263)
- Lean declaration: [primWeight_apply_prime_pow](../../Erdos249257/MersenneLambertLadder.lean#L272)
- Lean declaration: [primWeight_apply_prime](../../Erdos249257/MersenneLambertLadder.lean#L297)
- Lean declaration: [primWeight_nonneg](../../Erdos249257/MersenneLambertLadder.lean#L370)
- Lean declaration: [primWeight_le_totient](../../Erdos249257/MersenneLambertLadder.lean#L385)
- Lean declaration: [primWeight_apply_prime_sq](../../Erdos249257/PrimitiveDeterminantLift.lean#L69)


<a id="node-221906fd83d1c2d2"></a>
## primitive_euler_coordinate_clearing_criterion

For n nonzero, a positive integer D clears the normalised primitive coordinate A(n)/n (i.e. D * A(n)/n is an integer) if and only if n divides D * A(n).

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [integral_primEulerCoord_iff_dvd](../../Erdos249257/PrimitiveDeterminantLift.lean#L40)

- outgoing **implies**: [Z07::primitive_euler_index_no_lift_barrier](BROWSER_Z07_1.md#node-0913ec3431f6b924). the barrier applies the Q-to-Z clearing criterion at n = p and n = p^2.

<a id="node-0913ec3431f6b924"></a>
## primitive_euler_index_no_lift_barrier

If a positive integer D clears every normalised primitive Euler coordinate A(n)/n for 1 <= n <= N, then every odd prime p <= N divides D, every prime with p^2 <= N contributes p^2 to D, 4 divides D once N >= 4, and consequently the two-tier primorial lcm_{p<=N} localIndex(N,p) divides D. Hence no fixed positive integer D clears all normalised primitive coordinates simultaneously.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out ONLY a single horizon-INDEPENDENT positive integer index clearing A(n)/n for all n, i.e. an integral lift in the ordinary integral Euler/Witt-coordinate category. It does NOT rule out: (a) horizon-dependent indices — indeed twoTierPrimorial N is itself a candidate at each finite N, so the whole finite-jet family remains clearable; (b) any non-Euler normalisation of the primitive determinant (e.g. dividing by something other than n, or p-adic/Witt coordinates with different denominators); (c) the general Dieudonne-Dwork theorem for arbitrary integral power-series jets, which the module docstring explicitly separates from this result; (d) determinant realisations that never require simultaneous clearing. It proves nothing about the irrationality of the #249 constant.

- Lean declaration: [oddPrime_dvd_index_of_integral_jet](../../Erdos249257/PrimitiveDeterminantLift.lean#L97)
- Lean declaration: [primeSq_dvd_index_of_integral_jet](../../Erdos249257/PrimitiveDeterminantLift.lean#L111)
- Lean declaration: [four_dvd_index_of_integral_jet](../../Erdos249257/PrimitiveDeterminantLift.lean#L127)
- Lean declaration: [twoTierPrimorial_dvd_of_integral_jet](../../Erdos249257/PrimitiveDeterminantLift.lean#L148)
- Lean declaration: [no_fixed_integral_primitive_euler_index](../../Erdos249257/PrimitiveDeterminantLift.lean#L169)

- incoming **implies**: [Z07::primweight_prime_dold_defect](BROWSER_Z07_1.md#node-81c12a95341c017a). p not dividing A(p) and A(p^2) are the exact local inputs to the index divisibility obligations.
- incoming **implies**: [Z07::primitive_euler_coordinate_clearing_criterion](BROWSER_Z07_1.md#node-221906fd83d1c2d2). the barrier applies the Q-to-Z clearing criterion at n = p and n = p^2.
- outgoing **barrier_for**: [Z07::lambert_positive_lift_of_249](BROWSER_Z07_1.md#node-31acef136518144f). forbids a single fixed integer index for the integral Euler/Witt realisation of the primitive determinant attached to the positive lift.
- outgoing **barrier_for**: [Z01::totient_series_moebius_square_lens](BROWSER_Z01_2.md#node-b089feaf4597b079). This node presents #249 as the Lambert value of the primitive-conductor weight A = phi * mu; no_fixed_integral_primitive_euler_index shows no horizon-independent positive integer clears the normalised coordinates A(n)/n, since every odd prime p <= N and every p^2 <= N must divide it. Any denominator-clearing attack mounted on that presentation must therefore be horizon-dependent. Scope: only the ordinary integral Euler/Witt normalisation is closed.

<a id="node-81c12a95341c017a"></a>
## primweight_prime_dold_defect

At every odd prime p, p does not divide A(p) = p - 2; equivalently A(p)/p is not the image of an integer in Q. Also p does not divide A(p^2) = (p-1)^2.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [primWeight_prime_dold_defect](../../Erdos249257/MersenneLambertLadder.lean#L333)
- Lean declaration: [primWeight_div_prime_not_integer](../../Erdos249257/MersenneLambertLadder.lean#L347)
- Lean declaration: [prime_not_dvd_primWeight_prime_sq](../../Erdos249257/PrimitiveDeterminantLift.lean#L79)

- outgoing **implies**: [Z07::primitive_euler_index_no_lift_barrier](BROWSER_Z07_1.md#node-0913ec3431f6b924). p not dividing A(p) and A(p^2) are the exact local inputs to the index divisibility obligations.

<a id="node-264ae9c1322e8d89"></a>
## primweight_unbounded

For every natural B there is a prime p with A(p) > B; hence no uniform natural bound holds for the primitive-conductor weight A.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [primWeight_unbounded_on_primes](../../Erdos249257/MersenneLambertLadder.lean#L311)
- Lean declaration: [primWeight_not_bounded](../../Erdos249257/MersenneLambertLadder.lean#L321)

- outgoing **barrier_for**: [Z07::lambert_positive_lift_of_249](BROWSER_Z07_1.md#node-31acef136518144f). documented as blocking the corpus's bounded eventually-periodic weighted Erdos-series engine from consuming the positive lift; the Lean statement itself scopes no engine.

<a id="node-ce6ed2a2cab9d134"></a>
## rectangular_leibniz_determinant_expansion

For matrices M over a commutative ring with index types iota and kappa, det(M * N) equals the sum over all maps p : iota -> kappa of det(i,j -> M i (p j)) times the product over i of N (p i) i; non-injective maps are retained in the sum.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

Scope: Dead scaffolding: a repository-wide grep finds exactly one occurrence of det_mul_rectangular, its own declaration. Together with signed_hankel_scaffolding this means the whole SignedQMomentObstruction module contributes no proved statement about any #249 object.

- Lean declaration: [det_mul_rectangular](../../Erdos249257/SignedQMomentObstruction.lean#L29)


<a id="node-5096670b26a83467"></a>
## reduced_direction_law

The sum of 1/(2^{a+b} - 1) over all coprime pairs (a,b) with a, b >= 1 equals exactly 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tsum_pos_coprime_inv_mersenne_eq_one](../../Erdos249257/GcdMomentCalculus.lean#L349)

- incoming **implies**: [Z07::gcd_layer_normalisation](BROWSER_Z07_1.md#node-6cd68e0a2e072191). expanding each Mersenne reciprocal as its geometric layer series and swapping reduces the slope-mass sum to the layer normalisation at r = 1/2.
- outgoing **reformulates**: [Z07::stern_brocot_cylinder_law](BROWSER_Z07_1.md#node-efa27d01040f40cb). the total reduced-slope mass 1 is exactly the root value M(1,1) = 1 of the cylinder closed form.
- incoming **alias_of**: [Z01::gcd_moment_squared_lambert](BROWSER_Z01_1.md#node-1e4f5f5eeed01a3b). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18338 `tsum_visible_coprime_inv_mersenne_eq_one := GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one`; same base-2 statement, renamed.

<a id="node-9c5d62622df1cbfa"></a>
## residual_gauge_determinant_factorisation

The residual-weighted monomial matrix (i,j) -> W_j z_j^{e_i} equals the monomial matrix (i,j) -> z_j^{e_i} right-multiplied by diag(W); hence its determinant is the monomial determinant times the product of the W_j, nonvanishing is preserved whenever that product is nonzero, and determinant magnitude is preserved when every W_j has unit modulus.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [residualMonomialMatrix_eq_mul_diagonal](../../Erdos249257/ResidualGaugeObstruction.lean#L36)
- Lean declaration: [det_residualMonomialMatrix](../../Erdos249257/ResidualGaugeObstruction.lean#L47)
- Lean declaration: [det_residualMonomialMatrix_ne_zero_iff](../../Erdos249257/ResidualGaugeObstruction.lean#L55)
- Lean declaration: [norm_det_residualMonomialMatrix](../../Erdos249257/ResidualGaugeObstruction.lean#L64)

- outgoing **implies**: [Z07::locked_residual_countermodel](BROWSER_Z07_1.md#node-0752c5744baee041). the countermodel is the diagonal-gauge factorisation evaluated at the inverse pivot phases.

<a id="node-ca634ef766da9059"></a>
## row_dependent_residual_countermodel

Allowing the residual to vary across rows as well as columns, the explicit choice W(i,j) = z_j^{i}/z_j^{e_i} (every entry of unit modulus when the pivots are) reconstructs the ordinary consecutive-power (Vandermonde-shaped) matrix exactly, for arbitrary requested exponents; in particular its zeroth row is identically 1.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out ONLY fixed-rank nonzero-minor certificates that are blind to a row-dependent unit residual. It does NOT rule out certificates using an additional arithmetic coupling law between rows (the module docstring says exactly this), certificates that constrain the residual by an independent identity, or any argument that does not go through minor nonvanishing. It is not an irrationality statement. Same MODELLING GAP as locked_residual_countermodel: the module contains no #249 object at all, so the identification of 'fixed-rank nonzero-minor certificate' with these arbitrary complex monomial matrices is documentation, not Lean. Note also the reconstruction is exact only for nonzero pivots (hz : z j != 0 is required), and rowReconstruction_zero_row_one constrains the row indexed 0, not the row with exponent one — the two countermodels pin different rows.

- Lean declaration: [rowResidualMonomialMatrix_reconstructs_phasePowerMatrix](../../Erdos249257/ResidualGaugeObstruction.lean#L124)
- Lean declaration: [rowReconstruction_zero_row_one](../../Erdos249257/ResidualGaugeObstruction.lean#L145)

- outgoing **generalises**: [Z07::locked_residual_countermodel](BROWSER_Z07_1.md#node-0752c5744baee041). extends the countermodel from column-only gauges to residuals varying across rows as well.

<a id="node-669163a5d938cf84"></a>
## run_coordinate_normalisation

Words in the two mediant moves, applied from (1,1) with the list head acting last, always reach a coprime pair with both coordinates positive; recoding a word as alternating runs of lengths n_1, ..., n_r turns the mediant action into the continuant recurrence (A,B) -> (nA + B, A), and the resulting run-boundary pair is literally the Stern-Brocot pair up to a coordinate swap for a newest right run, with equal height and the same coprimality.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [sbPair_runWord](../../Erdos249257/SternBrocotRunGeometry.lean#L125)
- Lean declaration: [sbHeight_runWord](../../Erdos249257/SternBrocotRunGeometry.lean#L144)
- Lean declaration: [sbPair_coprime](../../Erdos249257/SternBrocotRunGeometry.lean#L66)
- Lean declaration: [runBoundaryPair_coprime](../../Erdos249257/SternBrocotRunGeometry.lean#L150)

- outgoing **implies**: [Z07::fibonacci_height_floor](BROWSER_Z07_1.md#node-caa09694be865178). the tree-facing form of the floor is obtained by transporting the run-coordinate floor along sbHeight_runWord.
- incoming **alias_of**: [Z01::stern_brocot_run_geometry](BROWSER_Z01_2.md#node-95bba30642ae44bd). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18380 `stern_brocot_pair_of_run_lengths := SternBrocotRunGeometry.sbPair_runWord`; the run/tree coordinate identification the Z01 node quotes is Z07's node.

<a id="node-7de71afe1ff5017d"></a>
## signed_hankel_scaffolding

Declarations only: a finite signed moment matrix over an arbitrary finite atom type, a truncated signed q = 1/2 moment sequence, and the Hankel matrix and Hankel determinant of a moment sequence. No property of any of these is proved.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [finiteSignedMomentMatrix](../../Erdos249257/SignedQMomentObstruction.lean#L47)
- Lean declaration: [truncatedMoment](../../Erdos249257/SignedQMomentObstruction.lean#L108)
- Lean declaration: [hankelMatrix](../../Erdos249257/SignedQMomentObstruction.lean#L113)
- Lean declaration: [hankelDet](../../Erdos249257/SignedQMomentObstruction.lean#L117)

- incoming **depends_on_open**: [Z07::unique_dyadic_terminal_parity](BROWSER_Z07_2.md#node-5f9952c1561d172c). the parity lemma is the intended non-vanishing certificate for the Hankel route, but no declaration anywhere instantiates its hypotheses on the actual #249 moment data.

<a id="node-f365b709a4311782"></a>
## signed_linear_growth_lambert_engine

For any real weight w with |w(d)| <= d on positive arguments and any 0 <= r < 1, the double series over positive pairs regroups along divisor antidiagonals, giving sum_d w(d) r^d/(1-r^d) = sum_n (sum_{e|n} w(e)) r^n, sum_d w(d) r^d/(1-r^d)^2 = sum_n (sum_{e|n} w(e)(n/e)) r^n, and sum_d w(d) (r^d/(1-r^d))^2 = sum_n (sum_{e|n} w(e)(n/e - 1)) r^n. Summability rides the AM-GM majorant d*m <= d^2 + m^2.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [summable_lambert_pair](../../Erdos249257/MersenneLambertLadder.lean#L66)
- Lean declaration: [tsum_lambert_pair_regroup](../../Erdos249257/MersenneLambertLadder.lean#L112)
- Lean declaration: [tsum_lambert_linear_weight](../../Erdos249257/MersenneLambertLadder.lean#L153)
- Lean declaration: [tsum_lambert_linear_weight_sq](../../Erdos249257/MersenneLambertLadder.lean#L194)
- Lean declaration: [tsum_lambert_linear_weight_sq_pure](../../Erdos249257/GcdMomentCalculus.lean#L105)

- incoming **specialises**: [Z07::lambert_rung_totient_rational](BROWSER_Z07_1.md#node-d6a59f5238058fa9). the phi rung is the engine at w = phi, using phi * zeta = Id.
- incoming **specialises**: [Z07::lambert_rung_moebius_rational](BROWSER_Z07_1.md#node-76e8be10a56dc445). the mu rung is the engine at w = mu, using mu * zeta = eps.
- incoming **specialises**: [Z07::lambert_positive_lift_of_249](BROWSER_Z07_1.md#node-31acef136518144f). the positive lift is the engine at w = A, using A * zeta = phi.
- incoming **specialises**: [Z07::moebius_square_lens_of_249](BROWSER_Z07_1.md#node-a9f26d2d7d41fdbc). the squared lens is the squared engine at w = mu, using mu * Id = phi.
- incoming **specialises**: [Z07::squared_kernel_zeta_rung](BROWSER_Z07_1.md#node-94b26f9d541d4fcd). pure-squared engine at w = 1, divisor coefficient sigma - tau.
- incoming **specialises**: [Z07::squared_kernel_totient_rung](BROWSER_Z07_1.md#node-03deb2c00196d21f). pure-squared engine at w = phi, divisor coefficient Pillai's P(n) - n.

<a id="node-03deb2c00196d21f"></a>
## squared_kernel_totient_rung

For 0 <= r < 1, sum_{d>=1} phi(d) (r^d/(1-r^d))^2 = sum_n (P(n) - n) r^n where P = phi * Id is Pillai's gcd-sum function; at r = 1/2 this is sum_{d>=1} phi(d)/(2^d - 1)^2 = sum_{n>=1} (P(n) - n) 2^{-n}.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tsum_totient_lambert_sq_pure](../../Erdos249257/GcdMomentCalculus.lean#L168)
- Lean declaration: [tsum_totient_div_mersenne_sq_eq_gcd_moment_series](../../Erdos249257/GcdMomentCalculus.lean#L235)

- outgoing **specialises**: [Z07::signed_linear_growth_lambert_engine](BROWSER_Z07_1.md#node-f365b709a4311782). pure-squared engine at w = phi, divisor coefficient Pillai's P(n) - n.
- incoming **reformulates**: [Z01::gcd_moment_squared_lambert](BROWSER_Z01_1.md#node-1e4f5f5eeed01a3b). Shared declaration tsum_totient_div_mersenne_sq_eq_gcd_moment_series: the totient-weighted squared Lambert transform is the Pillai gcd-sum coefficient series.
- incoming **specialises**: [Z01::gcd_moment_squared_lambert](BROWSER_Z01_1.md#node-1e4f5f5eeed01a3b). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18318 `tsum_totient_div_mersenne_sq_eq_gcd_moment_series := GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series`, the r = 1/2 case of Z07's `tsum_totient_lambert_sq_pure`.

<a id="node-94b26f9d541d4fcd"></a>
## squared_kernel_zeta_rung

For 0 <= r < 1, sum_{d>=1} (r^d/(1-r^d))^2 = sum_n (sigma(n) - tau(n)) r^n; at r = 1/2, sum_{d>=1} 1/(2^d - 1)^2 = sum_{n>=1} (sigma(n) - tau(n)) 2^{-n}.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [tsum_one_lambert_sq_pure](../../Erdos249257/GcdMomentCalculus.lean#L140)
- Lean declaration: [tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series](../../Erdos249257/GcdMomentCalculus.lean#L216)

- outgoing **specialises**: [Z07::signed_linear_growth_lambert_engine](BROWSER_Z07_1.md#node-f365b709a4311782). pure-squared engine at w = 1, divisor coefficient sigma - tau.
- incoming **reformulates**: [Z07::gcd_divisibility_factorisation](BROWSER_Z07_1.md#node-e13974d93e7d6998). supplies the probability reading P(d | gcd) = 1/(2^d - 1)^2 of the squared kernel; it is a gloss, not used in the rung's proof.
- incoming **specialises**: [Z01::gcd_moment_squared_lambert](BROWSER_Z01_1.md#node-1e4f5f5eeed01a3b). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18308 `tsum_inv_mersenne_sq_eq_sigma_sub_tau_series := GcdMomentCalculus.tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series`, the r = 1/2 case of Z07's `tsum_one_lambert_sq_pure`.

<a id="node-efa27d01040f40cb"></a>
## stern_brocot_cylinder_law

The closed form M(a,b) = 1/((2^a - 1)(2^b - 1)) is positive and satisfies the exact telescoping mediant recursion M(a,b) = 1/(2^{a+b} - 1) + M(a+b, b) + M(a, a+b); the two children carry at most 2/3 of the parent mass; and the depth-d finite unfolding of the recursion approximates M(a,b) from below with error at most (2/3)^d M(a,b), hence converges to M(a,b) at that explicit geometric rate.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: NAMING GAP, checked against the Lean: cylinderMass is DEFINED as the closed form 1/((2^a-1)(2^b-1)) and sternBrocotDepthMass is DEFINED as a finite recursion on pairs; no declaration in this module or elsewhere proves that either quantity equals the mass of the Stern-Brocot subtree rooted at (a,b), or that the nodes enumerated by the recursion are distinct, or that they exhaust any set of coprime pairs. Every theorem here is therefore an identity/limit about two explicitly defined real-valued functions. The only point of contact with the #249 constant is that the root value M(1,1) = 1 coincides numerically with the separately proved reduced_direction_law; the coincidence is not formalised as a bijection.

- Lean declaration: [cylinderMass_split](../../Erdos249257/GcdMomentCalculus.lean#L474)
- Lean declaration: [cylinderMass_children_le](../../Erdos249257/GcdMomentCalculus.lean#L514)
- Lean declaration: [sternBrocotDepthMass_error](../../Erdos249257/GcdMomentCalculus.lean#L525)
- Lean declaration: [tendsto_sternBrocotDepthMass](../../Erdos249257/GcdMomentCalculus.lean#L560)

- incoming **reformulates**: [Z07::reduced_direction_law](BROWSER_Z07_1.md#node-5096670b26a83467). the total reduced-slope mass 1 is exactly the root value M(1,1) = 1 of the cylinder closed form.
- incoming **alias_of**: [Z01::gcd_moment_squared_lambert](BROWSER_Z01_1.md#node-1e4f5f5eeed01a3b). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18346/18358 re-export `GcdMomentCalculus.sternBrocotDepthMass_error` and `tendsto_sternBrocotDepthMass`; Z01 carries two of the four declarations Z07 owns (the mediant split and the child-mass bound stay in Z07).

<a id="node-97f6265ebaa98171"></a>
## totient_lambert_tail_evaluation

For 0 <= r < 1, sum_{n>=1} n r^n = r/(1-r)^2, and the totient Lambert series with its d = 1 term peeled off evaluates to sum_{n>=2} phi(n) r^n/(1-r^n) = r/(1-r)^2 - r/(1-r).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tsum_pnat_mul_geometric](../../Erdos249257/GeometricCoprimality.lean#L244)
- Lean declaration: [tsum_totient_lambert_tail](../../Erdos249257/GeometricCoprimality.lean#L301)

- outgoing **specialises**: [Z07::lambert_rung_totient_rational](BROWSER_Z07_1.md#node-d6a59f5238058fa9). the tail evaluation is the phi rung with its d = 1 term peeled off.
- outgoing **implies**: [Z07::gcd_layer_normalisation](BROWSER_Z07_1.md#node-6cd68e0a2e072191). after the layer/antidiagonal Fubini swap the layer sum collapses onto the tail Lambert value.

