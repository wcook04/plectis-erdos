# Z09_2: Dyadic totient kernel, curvature carries and prime-jump / dilation transport

[All problems and zones](BROWSER.md)

<a id="node-9b0e6250c3b11982"></a>
## migration_sign_reversal_fixture

At the first new-prime jump d = 5, H = 12, p = 5 the transition channel equals 10228/961, positive, while its post-jump part alone equals -12/31, negative: the pre-jump migration term reverses the sign.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [residueHeckeDefect_five_twelve](../../Erdos249257/PrimeJumpMigration.lean#L58)
- Lean declaration: [postJumpResidueChannel_five_twelve](../../Erdos249257/PrimeJumpMigration.lean#L66)


<a id="node-34d4c2cf7a110d24"></a>
## old_channel_moment_annihilation

Any finite real coefficient vector whose zeroth and first moments both vanish annihilates every old affine residue channel, that is every channel index d dividing H, when applied to the kernel values at the scaled points m_i H. In particular the first-order transport defect vanishes on divisor channels, and the primitive joint (3,5) observable with coefficients (1, -3, -2, 4) at the vertices (15, 3, 5, 1) kills every such channel.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [oldChannel_affine_moment_annihilation](../../Erdos249257/JointExponentTransport.lean#L36)
- Lean declaration: [joint35_oldChannel_zero](../../Erdos249257/JointExponentTransport.lean#L71)
- Lean declaration: [residueTransportDefect_eq_zero_of_dvd](../../Erdos249257/ExponentOnlyTransport.lean#L112)

- incoming **reformulates**: [Z09::prime_jump_channel_migration](BROWSER_Z09_2.md#node-4d560a7f19bf7cb0). Both say that channels already dividing H cancel in a moment-balanced transport; they are stated on two different residue kernels.
- outgoing **depends_on_open**: [Z09::residue_kernel_affine_state](BROWSER_Z09_2.md#node-faec282c31eee28a). The annihilation is exactly the vanishing of the zeroth and first moments against the affine state decomposition.

<a id="node-4635adba5e7b5488"></a>
## parity_separated_determinant_criterion

A square matrix of naturals carrying a per-column 2-adic depth, with an odd diagonal depth quotient and even off-diagonal depth quotients, has nonzero determinant over the rationals: the depth quotient reduces to the identity matrix modulo two.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [paritySeparatedMatrix_det_ne_zero](../../Erdos249257/TotientMahlerDefect.lean#L823)

- incoming **depends_on_open**: [Z09::finite_level_dyadic_totient_independence](BROWSER_Z09_1.md#node-b015a5eb93d9819b). The rows are turned into a nonzero minor by the mod-2 unipotence determinant criterion.

<a id="node-2a33d82327ac8f44"></a>
## positive_rational_height_inequality

If a positive rational x is smaller than 2/M with M positive, and N divides the absolute value of its reduced numerator, then N M < 2 den(x). Specialising N to 2^r and M to a Mersenne number 2^n - 1 gives the denominator lower bound used by synchronised tails.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [positiveRat_numDivisor_mul_lt_two_mul_den](../../Erdos249257/AdelicHeightObstruction.lean#L77)
- Lean declaration: [positiveRat_twoPow_mul_lt_two_mul_den](../../Erdos249257/AdelicHeightObstruction.lean#L96)
- Lean declaration: [positiveRat_mersenne_height](../../Erdos249257/AdelicHeightObstruction.lean#L103)

- outgoing **reformulates**: [Z09::scalar_localisation_height_barrier](BROWSER_Z09_2.md#node-e79c79b3968927cf). The Archimedean half of the same height bookkeeping: what the localiser gains 2-adically it pays in denominator size.

<a id="node-6c66f057b6bd1c17"></a>
## prime_dilation_cocycle

For a prime p and any m, phi(p m) = (p-1) phi(m) plus phi(m) when p divides m and plus zero otherwise.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [totient_mul_prime_cocycle](../../Erdos249257/SquareCRTCube.lean#L38)

- outgoing **implies**: [Z09::square_crt_correction_suppression](BROWSER_Z09_2.md#node-bd0c4154984286a0). The correction-free branch of the cocycle is what the square congruence arranges on the finite horizon.

<a id="node-4d560a7f19bf7cb0"></a>
## prime_jump_channel_migration

The contribution of a residue channel d to the prime-jump commutator equals its post-jump value plus the pre-jump value of the same channel transported with coefficient -p; and every carrier d already dividing H cancels exactly in the commutator.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [residueHeckeDefect_eq_postJump_add_migration](../../Erdos249257/PrimeJumpMigration.lean#L38)
- Lean declaration: [residueHeckeDefect_eq_zero_of_dvd](../../Erdos249257/PrimeJumpMigration.lean#L46)

- outgoing **reformulates**: [Z09::old_channel_moment_annihilation](BROWSER_Z09_2.md#node-34d4c2cf7a110d24). Both say that channels already dividing H cancel in a moment-balanced transport; they are stated on two different residue kernels.

<a id="node-2c40e055cd75aba9"></a>
## prime_jump_finite_certificate_12_5_15

The sharp prime-jump certificate holds at H = 12, p = 5, L = 15 by kernel computation.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [primeJumpSharpKill_twelve_five](../../Erdos249257/PrimeJumpWindow.lean#L186)

- outgoing **finite_instance_of**: [Z09::prime_jump_window_sharp_radius](BROWSER_Z09_2.md#node-5b3fe97761cc63bd). A single kernel-checked value of the decidable prime-jump certificate at H = 12, p = 5, L = 15.

<a id="node-02a652f88d203b04"></a>
## prime_jump_supply_implies_249

If for every threshold there is a larger lcm height t together with a positive p and a depth L at which the sharp prime-jump certificate holds, then sum phi(n)/2^n is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : forall t0, exists t, t0 <= t and exists p L, 0 < p and primeJumpSharpKill (periodLcm t) p L"]

- Lean declaration: [irrational_totient_series_of_primeJumpSharpKill_supply](../../Erdos249257/PrimeJumpWindow.lean#L193)

- outgoing **depends_on_open**: [Z09::prime_jump_window_sharp_radius](BROWSER_Z09_2.md#node-5b3fe97761cc63bd). The endpoint consumes the sharp non-integrality criterion; the supply is an unproved inline hypothesis.

<a id="node-5b3fe97761cc63bd"></a>
## prime_jump_window_sharp_radius

The prime-jump commutator J(H,p) = D(pH) - p D(H) of diagonal totient-tail differences splits at every depth L into the exact four-vertex integer window over 2^L plus a remainder of size at most 3 p H + (p+1)(L+2); a window residue mod 2^L strictly inside the complementary band therefore proves J(H,p) is not an integer. The radius is 3pH rather than the 4pH belonging to the two-cell disjunction.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [primeJumpTailCommutator_eq_window_add_remainder](../../Erdos249257/PrimeJumpWindow.lean#L91)
- Lean declaration: [primeJumpTailCommutator_notMem_int_of_sharpKill](../../Erdos249257/PrimeJumpWindow.lean#L178)

- incoming **finite_instance_of**: [Z09::prime_jump_finite_certificate_12_5_15](BROWSER_Z09_2.md#node-2c40e055cd75aba9). A single kernel-checked value of the decidable prime-jump certificate at H = 12, p = 5, L = 15.
- incoming **depends_on_open**: [Z09::prime_jump_supply_implies_249](BROWSER_Z09_2.md#node-02a652f88d203b04). The endpoint consumes the sharp non-integrality criterion; the supply is an unproved inline hypothesis.

<a id="node-5ce42d820e10c75d"></a>
## prime_ray_cyclotomic_open_sockets

Three named and unproved predicates on a cyclotomic layer function C along a prime ray m q: eventual nontrivial layers coprime to m q; a bounded-degree exact-order consumer for every rational prime divisor of a layer; and escape of large layers from every prescribed finite prime support.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: These are dead sockets. Grepping both libraries finds each of the three names exactly once, at its own definition site; no theorem anywhere derives one, assumes one, or produces any conditional implication from them. Listing them as open antecedents records named obligations, not a proof route: nothing in the corpus would follow even if all three were proved.

Open hypotheses: ["PrimeRayLayerSupply C m : eventual nontrivial layers C(m q) > 1 coprime to m q for all large primes q. Defined at PrimeRayCyclotomicCurvature.lean:88, proved nowhere, consumed nowhere.", "BoundedDegreeOrderConsumer C m d : every rational prime divisor p of C(m q) satisfies m q | p^k - 1 for some 1 <= k <= d. Defined at PrimeRayCyclotomicCurvature.lean:95, proved nowhere, consumed nowhere.", "FinitePrimeSupportEscape C m : large prime-ray layers avoid every prescribed finite prime set. Defined at PrimeRayCyclotomicCurvature.lean:102, proved nowhere, consumed nowhere."]

- Lean declaration: [PrimeRayLayerSupply](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L95)
- Lean declaration: [BoundedDegreeOrderConsumer](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L102)
- Lean declaration: [FinitePrimeSupportEscape](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L151)


<a id="node-0b905695e89a37be"></a>
## rationality_forces_unbounded_carry_rank

If sum phi(n)/2^n is rational then there exist a positive multiplier v and a tempered integral carry orbit u for phi such that, for every e, the rational span of the dyadic carry sections of u through level e has rank at least 2^e - 1.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [not_irrational_totientSeries_implies_unbounded_carryRank](../../Erdos249257/TotientCarryKernelRigidity.lean#L275)
- Lean declaration: [not_irrational_totientSeries_implies_unbounded_carryRank_unconditional](../../Erdos249257/TotientCarryKernelRigidity.lean#L300)

- outgoing **specialises**: [Z09::finite_level_carry_anti_compression](BROWSER_Z09_1.md#node-321a6939105b78f6). The rationality-supplied tempered orbit is fed into the finite-level rank bound at every level.
- outgoing **transport_of**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). not_irrational_totientSeries_implies_unbounded_carryRank is the composition of the rank bound with binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit instantiated at c = Nat.totient.

<a id="node-faec282c31eee28a"></a>
## residue_kernel_affine_state

The exact Moebius residue kernel is affine in the scale coordinate: K(d, N) = N times a slope plus an intercept, where both slope and intercept depend on N only through N mod d and are periodic with period d. On divisor channels the diagonal increment collapses to the linear form mu(d) H / (d (2^d - 1)). Consequently the four-vertex H to 3H transport of the increment splits into a slope block and an intercept block, and both blocks are present.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [transportResidueKernel_eq_affineState](../../Erdos249257/ExponentOnlyTransport.lean#L141)
- Lean declaration: [residueSlope_add_period](../../Erdos249257/ExponentOnlyTransport.lean#L153)
- Lean declaration: [residueIntercept_add_period](../../Erdos249257/ExponentOnlyTransport.lean#L158)
- Lean declaration: [transportResidueIncrement_of_dvd](../../Erdos249257/ExponentOnlyTransport.lean#L92)
- Lean declaration: [residueTransportDefect_three_eq_affineState](../../Erdos249257/ExponentOnlyTransport.lean#L176)

- incoming **depends_on_open**: [Z09::old_channel_moment_annihilation](BROWSER_Z09_2.md#node-34d4c2cf7a110d24). The annihilation is exactly the vanishing of the zeroth and first moments against the affine state decomposition.

<a id="node-e79c79b3968927cf"></a>
## scalar_localisation_height_barrier

Let x be a rational, H a divisor of its reduced denominator, and c an integer such that the reduced denominator of c x divides H. Then the complementary factor den(x)/H divides |c|, so H c x equals an integer multiple of the original reduced numerator. Moreover any rational-linear channel that annihilates every scalar relation is the evaluation map times one fixed vector. Scalar denominator clearing therefore transfers the discarded denominator into the coefficient rather than erasing it.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out only SCALAR denominator clearing, by a single integer multiplier, discarding the complementary reduced denominator; and, via the descender lemma, only rational-LINEAR channels that kill every scalar relation and hit 1. It does not rule out: localisers using several rationals jointly, non-linear or non-rational channels, arguments that let the coefficient grow and pay the Archimedean cost, or any argument that does not attempt denominator clearing at all. It proves no irrationality statement for any support.

- Lean declaration: [scalarLocalization_complement_dvd](../../Erdos249257/AdelicHeightObstruction.lean#L23)
- Lean declaration: [scalarLocalization_divisor_dvd_coefficient](../../Erdos249257/AdelicHeightObstruction.lean#L45)
- Lean declaration: [scalarLocalization_integer_eq_mul_num](../../Erdos249257/AdelicHeightObstruction.lean#L56)
- Lean declaration: [linearDescender_eq_smul_eval](../../Erdos249257/AdelicHeightObstruction.lean#L120)

- incoming **reformulates**: [Z09::positive_rational_height_inequality](BROWSER_Z09_2.md#node-2a33d82327ac8f44). The Archimedean half of the same height bookkeeping: what the localiser gains 2-adically it pays in denominator size.
- incoming **repair_of**: [Z11::rational_denominator_divisor_survival](BROWSER_Z11_1.md#node-541429c78c537b38). The barrier shows scalar clearing transfers the discarded reduced denominator into the coefficient (scalarLocalization_complement_dvd). survivingDivisor_dvd_scaled_divInt_den does that bookkeeping exactly rather than trying to avoid it: for C dividing D and coprime to |a|, C/gcd(C,h) divides the denominator of (h*a)/D, so a scalar multiplier h cancels precisely gcd(C,h) of C and no more.
- incoming **transport_of**: [Z12::relation_invariant_channel_determinant_barrier](BROWSER_Z12_2.md#node-0bf69d60c69b92a2). Both nodes are the rank-one collapse of relation-invariant linear channels: Z09 states it for a single scalar localiser (linearDescender_eq_smul_eval, AdelicHeightObstruction.lean) and Z12 for a family indexed by iota (relationInvariantLinearChannels_det_eq_zero, HalfTrappingReturnCarry.lean), the multi-channel instance of the same descender.

<a id="node-5a73c48ee4d9ed48"></a>
## separated_minor_rank_criterion

A finite family of sequences with a square evaluation matrix of nonzero determinant is linearly independent over the rationals, and the span of the canonical level-e family then has finite rank exactly 2^e + 1, which is the cardinality of the canonical index.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [linearIndependent_of_separatedMinorCertificate](../../Erdos249257/TotientMahlerDefect.lean#L91)
- Lean declaration: [finrank_canonicalTotientKernel_eq_of_linearIndependent](../../Erdos249257/TotientMahlerDefect.lean#L102)
- Lean declaration: [finrank_canonicalTotientKernel_eq_of_certificate](../../Erdos249257/TotientMahlerDefect.lean#L111)
- Lean declaration: [card_totientCanonicalIndex](../../Erdos249257/TotientMahlerDefect.lean#L61)


<a id="node-bd0c4154984286a0"></a>
## square_crt_correction_suppression

Imposing a square congruence n congruent to A + p a modulo p^2 makes the cofactor at every shift h with p not dividing a + h coprime to p, so the dilation correction vanishes and phi(n + p h - A) = (p-1) phi(a + p t + h). Distinct primes give pairwise-coprime square moduli, so finitely many such congruences can be imposed simultaneously with a least representative below the product, and the representative can be raised above any prescribed floor at a cost of less than one extra block. Consequently one common base removes every dilation correction on a prescribed finite horizon 1 <= h <= J whenever every construction prime exceeds J.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [totient_dilation_clean_of_square_residue](../../Erdos249257/SquareCRTCube.lean#L147)
- Lean declaration: [totient_dilation_clean_of_square_witness](../../Erdos249257/SquareCRTCube.lean#L169)
- Lean declaration: [totient_dilation_clean_of_square_modEq](../../Erdos249257/SquareCRTCube.lean#L197)
- Lean declaration: [exists_squareCRT_base_of_distinct_primes](../../Erdos249257/SquareCRTCube.lean#L247)
- Lean declaration: [exists_large_squareCRT_base](../../Erdos249257/SquareCRTCube.lean#L263)
- Lean declaration: [exists_squareCRT_clean_totient_family](../../Erdos249257/SquareCRTCube.lean#L297)
- Lean declaration: [exists_squareCRT_clean_horizon](../../Erdos249257/SquareCRTCube.lean#L327)

- incoming **barrier_for**: [Z09::clean_square_cube_does_not_separate](BROWSER_Z09_1.md#node-051b33c6473646d1). Two kernel-checked clean cubes show correction suppression alone neither forces nor forbids a nonzero cube coefficient, so cleanness is not by itself a separation mechanism.
- incoming **implies**: [Z09::prime_dilation_cocycle](BROWSER_Z09_2.md#node-6c66f057b6bd1c17). The correction-free branch of the cocycle is what the square congruence arranges on the finite horizon.

<a id="node-2e9bb343b96c0e05"></a>
## squarefree_support_stability_under_exponent_jump

If p divides H then for every squarefree d, d divides p H if and only if d divides H; primality of p and the exponent are not needed. Hence the nonzero Moebius support is unchanged across H to p H.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [squarefree_dvd_mul_iff_of_dvd](../../Erdos249257/ExponentOnlyTransport.lean#L36)
- Lean declaration: [squarefree_dvd_prime_mul_iff_of_prime_dvd](../../Erdos249257/ExponentOnlyTransport.lean#L56)
- Lean declaration: [mobius_ne_zero_dvd_mul_iff_of_dvd](../../Erdos249257/ExponentOnlyTransport.lean#L62)


<a id="node-5f016a0c0fed7ab2"></a>
## three_transport_alias_of_exponent_only_commutator

The balanced boundary word of ThreeTransportBoundary and the four-vertex transport commutator of ExponentOnlyTransport are the same real-valued function of H, definitionally.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [threeTransportTail_eq_commutator](../../Erdos249257/ThreeTransportBoundary.lean#L166)

- outgoing **alias_of**: [Z09::three_transport_window_certificate](BROWSER_Z09_2.md#node-1c4f511c806cea73). The balanced word and the exponent-only commutator are the same function, proved by rfl.

<a id="node-b4731719f77c06d5"></a>
## three_transport_finite_certificate_60_12

At the lcm height H = lcm(1..6) = 60 and depth L = 12 the balanced boundary window equals 19316, and the sharp separation certificate holds there by kernel computation.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [threeTransportWindow_60_12](../../Erdos249257/ThreeTransportBoundary.lean#L197)
- Lean declaration: [sharpThreeTransportCert_60_12](../../Erdos249257/ThreeTransportBoundary.lean#L203)

- outgoing **finite_instance_of**: [Z09::three_transport_window_certificate](BROWSER_Z09_2.md#node-1c4f511c806cea73). A single kernel-checked value of the decidable certificate predicate at H = 60, L = 12.

<a id="node-b3014c9cc270353e"></a>
## three_transport_supply_implies_249

If sharp balanced-boundary certificates exist at arbitrarily large lcm heights and arbitrary depths, then sum phi(n)/2^n is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["RoughnessBoundaryLatticeSupply : forall t0, exists t L, t0 <= t and sharpThreeTransportCert (periodLcm t) L"]

- Lean declaration: [irrational_totientSeries_of_roughnessBoundaryLatticeSupply](../../Erdos249257/ThreeTransportBoundary.lean#L177)

- outgoing **depends_on_open**: [Z09::three_transport_window_certificate](BROWSER_Z09_2.md#node-1c4f511c806cea73). The endpoint consumes the non-integrality criterion; the supply itself is unproved.
- incoming **reformulates**: [Z09::exponent_only_three_transport_supply_implies_249](BROWSER_Z09_1.md#node-4e06b69878dd4980). Same four-vertex observable and same flatness contradiction; the difference is that the hypothesis is stated as bare non-integrality on a 3^a tower rather than as a decidable window certificate.

<a id="node-1c4f511c806cea73"></a>
## three_transport_window_certificate

For the balanced four-ray word (R_(6H) - R_(3H)) - 3 (R_(2H) - R_H), 2^L times the word equals an exact integer depth-L window plus a shifted remainder of absolute value at most 9H + 4L + 4; the window obeys the input-driven doubling recurrence; and a window residue mod 2^L strictly inside the complementary band proves the word is not an integer. Any such certificate also forces 2^L to exceed twice the radius.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [two_pow_mul_threeTransport_eq_window_add_shifted](../../Erdos249257/ThreeTransportBoundary.lean#L67)
- Lean declaration: [abs_threeTransportShiftedTail_le](../../Erdos249257/ThreeTransportBoundary.lean#L86)
- Lean declaration: [abs_threeTransportDrive_le](../../Erdos249257/ThreeTransportBoundary.lean#L48)
- Lean declaration: [threeTransportWindow_succ](../../Erdos249257/ThreeTransportBoundary.lean#L102)
- Lean declaration: [threeTransport_notMem_int_of_cert](../../Erdos249257/ThreeTransportBoundary.lean#L126)
- Lean declaration: [sharpThreeTransportCert_depth_floor](../../Erdos249257/ThreeTransportBoundary.lean#L119)

- outgoing **specialises**: [Z09::generic_window_residue_gap_soundness](BROWSER_Z09_1.md#node-6c029622c10f1cc6). Same lattice-separation argument, re-proved inline for the balanced boundary word.
- incoming **depends_on_open**: [Z09::three_transport_supply_implies_249](BROWSER_Z09_2.md#node-b3014c9cc270353e). The endpoint consumes the non-integrality criterion; the supply itself is unproved.
- incoming **finite_instance_of**: [Z09::three_transport_finite_certificate_60_12](BROWSER_Z09_2.md#node-b4731719f77c06d5). A single kernel-checked value of the decidable certificate predicate at H = 60, L = 12.
- incoming **alias_of**: [Z09::three_transport_alias_of_exponent_only_commutator](BROWSER_Z09_2.md#node-5f016a0c0fed7ab2). The balanced word and the exponent-only commutator are the same function, proved by rfl.
- outgoing **transport_of**: [Z06::endpoint_certificate_soundness](BROWSER_Z06_1.md#node-552175c811881922). two_pow_mul_threeTransport_eq_window_add_shifted is the balanced four-ray analogue of windowDiscrepancy_div_eq, closed by the identical residue-band separation; the same stencil substitution produces the curvature, prime-jump and joint(3,5) certificates.

<a id="node-0fe9be464c7d5625"></a>
## totient_two_adic_scaling

For odd m and any t, phi(2^(t+1) m) = 2^t phi(m); and for any j, phi(2^j (2n)) = 2^j phi(2n). Doubling an already even argument multiplies the totient by two exactly.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [totient_two_pow_succ_mul_of_odd](../../Erdos249257/TotientMahlerDefect.lean#L120)
- Lean declaration: [totient_two_pow_mul_two](../../Erdos249257/TotientMahlerDefect.lean#L140)

- incoming **specialises**: [Z09::dyadic_channel_odd_core_reduction](BROWSER_Z09_1.md#node-64ab511bdb80e535). The channel reductions are the two-adic scaling identities read on the sequences n |-> phi(2^j n + r).

