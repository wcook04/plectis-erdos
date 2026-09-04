# Z09_1: Dyadic totient kernel, curvature carries and prime-jump / dilation transport

[All problems and zones](BROWSER.md)

<a id="node-cafcebbeee7d0516"></a>
## affine_step_centred_completion

For any even modulus M = 2R with R positive, any residue class a modulo M, any multiplier b and any incoming state e, there is a digit c in the class a modulo M with the affine step e' = b e + c satisfying |e'| at most R.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [residueClass_step_has_centred_completion](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L62)

- outgoing **generalises**: [Z09::fixed_precision_tropical_no_go](BROWSER_Z09_1.md#node-81c415e101ea6ff3). The prime-ray lemma is the tropical one-step recentring with the valuation-unit dressing replaced by an arbitrary residue class modulo an even modulus.

<a id="node-cd6a6ef40a5f9729"></a>
## all_base_canonical_range_in_full_truncation

For every integer base k at least two and positive depth e, every member of the canonical all-base totient family occurs literally among the complete base-k kernel sections through level e.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This is the easy range inclusion. It does not prove that the complete truncation lies in the canonical span or that either family is independent.

- Lean declaration: [range_canonicalAllBaseTotientKernelFamily_subset_throughLevel](../../Erdos249257/TotientKernelConditional.lean#L165)

- outgoing **generated_by**: [Z09::all_base_totient_kernel_arithmetic_index](BROWSER_Z09_1.md#node-77bc5b5c52180281). The certified level and residue bounds embed every canonical coordinate into the complete through-level index.
- incoming **generated_by**: [Z09::all_base_totient_canonical_span_equality](BROWSER_Z09_1.md#node-dfa049e80d394698). The reverse inclusion follows from the literal occurrence of every canonical channel in the complete truncation.

<a id="node-cd5983471950940f"></a>
## all_base_totient_canonical_rank_of_linear_independence

For every integer base k at least two and every depth e, if the canonical all-base totient family indexed by TotientKernelIndex k e is linearly independent over the rationals, then the rank of its rational span is exactly k^e + 1.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This theorem does not prove its linear-independence hypothesis. It therefore does not establish unconditional all-base rank or a basis and has no consequence for irrationality of the totient series.

Open hypotheses: ["hcanon : LinearIndependent Q (canonicalAllBaseTotientKernelFamily k e). This is a free theorem hypothesis. The corpus does not prove it for arbitrary k; the paper derives it from Martin's external positive-density theorem, which is not formalised."]

- Lean declaration: [finrank_canonicalAllBaseTotientKernel_eq_of_linearIndependent](../../Erdos249257/TotientKernelConditional.lean#L203)

- outgoing **depends_on_open**: [Z09::all_base_totient_kernel_arithmetic_index](BROWSER_Z09_1.md#node-77bc5b5c52180281). The checked index cardinality gives k^e + 1 once the theorem's explicit, externally discharged linear-independence hypothesis is supplied.
- incoming **generated_by**: [Z09::all_base_totient_truncation_rank_of_linear_independence](BROWSER_Z09_1.md#node-2812f8ce567f9d90). After rewriting the full span as the canonical span, the conditional canonical rank theorem gives the result.

<a id="node-dfa049e80d394698"></a>
## all_base_totient_canonical_span_equality

For every integer base k at least two and positive depth e, the rational span of every base-k totient section through level e equals the rational span of the canonical family indexed by TotientKernelIndex k e.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Span equality supplies an upper bound from the canonical index. It does not prove that the canonical family is linearly independent or that the rank is k^e + 1.

- Lean declaration: [span_allBaseTotientKernelThroughLevelFamily_eq_canonical](../../Erdos249257/TotientKernelConditional.lean#L185)

- outgoing **generated_by**: [Z09::all_base_totient_channel_mem_canonical_span](BROWSER_Z09_1.md#node-11025fcd5d18f7f8). One inclusion is exactly the theorem that every complete-kernel channel belongs to the canonical span.
- outgoing **generated_by**: [Z09::all_base_canonical_range_in_full_truncation](BROWSER_Z09_1.md#node-cd6a6ef40a5f9729). The reverse inclusion follows from the literal occurrence of every canonical channel in the complete truncation.
- incoming **generated_by**: [Z09::all_base_totient_truncation_rank_of_linear_independence](BROWSER_Z09_1.md#node-2812f8ce567f9d90). The unconditional span equality transports the conditional exact-rank conclusion from the canonical family to the actual complete truncation.

<a id="node-11025fcd5d18f7f8"></a>
## all_base_totient_channel_mem_canonical_span

Let k be at least two. If j is at most e and r is below k^j, then the base-k totient section n |-> phi(k^j n + r) belongs to the rational span of the canonical family indexed by TotientKernelIndex k e.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Membership in the canonical span gives no linear independence and no rank lower bound.

- Lean declaration: [allBaseTotientKernelSeq_mem_span_canonical_of_le](../../Erdos249257/TotientKernelConditional.lean#L102)

- outgoing **generated_by**: [Z09::all_base_totient_residue_scalar_step](BROWSER_Z09_1.md#node-f975179647a7be5a). The recursive spanning proof lowers every residue divisible by k using the scalar step until a head channel or a nonmultiple coordinate is reached.
- outgoing **generated_by**: [Z09::all_base_totient_kernel_arithmetic_index](BROWSER_Z09_1.md#node-77bc5b5c52180281). The nonmultiple branch uses the arithmetic node's unique quotient/nonzero-digit coordinate theorem.
- incoming **generated_by**: [Z09::all_base_totient_canonical_span_equality](BROWSER_Z09_1.md#node-dfa049e80d394698). One inclusion is exactly the theorem that every complete-kernel channel belongs to the canonical span.

<a id="node-77bc5b5c52180281"></a>
## all_base_totient_kernel_arithmetic_index

For every integer base k at least two, Lean proves the zero-residue scaling identity, an exact division-free composite-base reduction, unique quotient/nonzero-digit coordinates for each positive fixed-level residue not divisible by k, and cardinality k^e + 1 of the resulting finite-level index.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This node does not assert all-base linear independence, span equality, a basis of section functions, finite-level rank, Martin's positive-density theorem, or irrationality of the totient series.

- Lean declaration: [totient_pow_mul_eq](../../Erdos249257/TotientKernelReduction.lean#L60)
- Lean declaration: [totient_pow_mul_affine_gcd_cross_eq](../../Erdos249257/TotientKernelReduction.lean#L117)
- Lean declaration: [totientKernelSectionIndex_spec](../../Erdos249257/TotientKernelIndex.lean#L124)
- Lean declaration: [existsUnique_totientKernelResidueAtLevel](../../Erdos249257/TotientKernelIndex.lean#L213)
- Lean declaration: [card_totientKernelIndex](../../Erdos249257/TotientKernelIndex.lean#L277)

- incoming **specialises**: [Z09::all_base_totient_reduction_scalar_nonzero](BROWSER_Z09_1.md#node-846cbd4b2820924c). The nonzero rational scalar is obtained by exact division of the arithmetic node's cross-multiplied composite-base identity; positivity of its denominator justifies the division.
- incoming **reformulates**: [Z09::all_base_totient_residue_scalar_step](BROWSER_Z09_1.md#node-f975179647a7be5a). The function equality is the exact rational-division form of the cross-multiplied affine gcd identity, with the coefficient constant along the section.
- incoming **generated_by**: [Z09::all_base_totient_channel_mem_canonical_span](BROWSER_Z09_1.md#node-11025fcd5d18f7f8). The nonmultiple branch uses the arithmetic node's unique quotient/nonzero-digit coordinate theorem.
- incoming **generated_by**: [Z09::all_base_canonical_range_in_full_truncation](BROWSER_Z09_1.md#node-cd6a6ef40a5f9729). The certified level and residue bounds embed every canonical coordinate into the complete through-level index.
- incoming **depends_on_open**: [Z09::all_base_totient_canonical_rank_of_linear_independence](BROWSER_Z09_1.md#node-cd5983471950940f). The checked index cardinality gives k^e + 1 once the theorem's explicit, externally discharged linear-independence hypothesis is supplied.

<a id="node-846cbd4b2820924c"></a>
## all_base_totient_reduction_scalar_nonzero

For every positive integer base k and every residue r, the rational scalar phi(k) gcd(k,r) / phi(gcd(k,r)) is nonzero.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Nonvanishing of the scalar is an arithmetic fact. It does not assert spanning, linear independence, rank, a basis, or irrationality.

- Lean declaration: [totientKernelReductionScalar_ne_zero](../../Erdos249257/TotientKernelConditional.lean#L35)

- outgoing **specialises**: [Z09::all_base_totient_kernel_arithmetic_index](BROWSER_Z09_1.md#node-77bc5b5c52180281). The nonzero rational scalar is obtained by exact division of the arithmetic node's cross-multiplied composite-base identity; positivity of its denominator justifies the division.

<a id="node-f975179647a7be5a"></a>
## all_base_totient_residue_scalar_step

For every positive integer base k, level j at least one, and residue r, the function n |-> phi(k^(j+1)n + kr) equals the constant rational scalar phi(k) gcd(k,r) / phi(gcd(k,r)) times the function n |-> phi(k^j n + r).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The identity holds for every residue r, including r = 0. It is one reduction step and does not by itself assert termination, independence, rank, or irrationality.

- Lean declaration: [allBaseTotientKernelSeq_mul_residue_step](../../Erdos249257/TotientKernelConditional.lean#L54)

- outgoing **reformulates**: [Z09::all_base_totient_kernel_arithmetic_index](BROWSER_Z09_1.md#node-77bc5b5c52180281). The function equality is the exact rational-division form of the cross-multiplied affine gcd identity, with the coefficient constant along the section.
- incoming **generated_by**: [Z09::all_base_totient_channel_mem_canonical_span](BROWSER_Z09_1.md#node-11025fcd5d18f7f8). The recursive spanning proof lowers every residue divisible by k using the scalar step until a head channel or a nonmultiple coordinate is reached.

<a id="node-2812f8ce567f9d90"></a>
## all_base_totient_truncation_rank_of_linear_independence

For every integer base k at least two and positive depth e, if the canonical all-base totient family is linearly independent over the rationals, then the rational span of all base-k totient sections through level e has rank exactly k^e + 1.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The conclusion is conditional on explicit linear independence. Lean does not discharge that hypothesis, formalise Martin's theorem, construct an unconditional all-base basis, or prove irrationality of the totient series.

Open hypotheses: ["hcanon : LinearIndependent Q (canonicalAllBaseTotientKernelFamily k e). This is a free theorem hypothesis. The corpus does not prove it for arbitrary k; the paper derives it from Martin's external positive-density theorem, which is not formalised."]

- Lean declaration: [finrank_allBaseTotientKernelThroughLevelFamily_eq_of_linearIndependent](../../Erdos249257/TotientKernelConditional.lean#L215)

- outgoing **generated_by**: [Z09::all_base_totient_canonical_rank_of_linear_independence](BROWSER_Z09_1.md#node-cd5983471950940f). After rewriting the full span as the canonical span, the conditional canonical rank theorem gives the result.
- outgoing **generated_by**: [Z09::all_base_totient_canonical_span_equality](BROWSER_Z09_1.md#node-dfa049e80d394698). The unconditional span equality transports the conditional exact-rank conclusion from the canonical family to the actual complete truncation.

<a id="node-bb7451d9a436838b"></a>
## alternating_cube_insertion_cancellation

If inserting a fixed coordinate into any subset of a finite set leaves the term unchanged, then the alternating sum over the powerset of the enlarged set vanishes.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [alternating_powerset_sum_eq_zero_of_insert_invariant](../../Erdos249257/SquareCRTCube.lean#L363)


<a id="node-ce4185cc29a85233"></a>
## carry_derivative_totient_transport

For any integer sequence satisfying the exact binary-orbit recurrence u(N+1) = 2u(N) - v c(N+1), the discrete carry derivative 2u(n-1) - u(n) equals v c(n) at every positive n. For c = phi this recovers the scaled totient, inherits multiplicativity in coprime and gcd-corrected form, and identifies every positive-residue dyadic totient channel, scaled by v, with the two-term difference 2 u(2^j n + r - 1) - u(2^j n + r) of adjacent carry sections.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [carryDerivative_eq_scaledCoeff_of_recurrence](../../Erdos249257/TotientCarryKernelRigidity.lean#L29)
- Lean declaration: [totient_temperedOrbit_derivative](../../Erdos249257/TotientCarryKernelRigidity.lean#L43)
- Lean declaration: [totient_carryDerivative_coprime_mul](../../Erdos249257/TotientCarryKernelRigidity.lean#L52)
- Lean declaration: [totient_carryDerivative_gcd_mul](../../Erdos249257/TotientCarryKernelRigidity.lean#L68)
- Lean declaration: [totient_carryKernel_diff](../../Erdos249257/TotientCarryKernelRigidity.lean#L94)
- Lean declaration: [canonicalCarryDifferenceFamily_eq_smul_totient](../../Erdos249257/TotientCarryKernelRigidity.lean#L182)

- incoming **depends_on_open**: [Z09::finite_level_carry_anti_compression](BROWSER_Z09_1.md#node-321a6939105b78f6). The carry differences that realise the independent totient channels are supplied by the carry-derivative identity.

<a id="node-4bcbcbc0bbd6364c"></a>
## checkerboard_unique_joint_annihilator

The two-by-two checkerboard functional F(1,1) - F(1,0) - F(0,1) + F(0,0) annihilates every additively separable background u(i) + v(j), and any two-by-two coefficient array whose row sums and column sums all vanish is a scalar multiple of the checkerboard.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [checkerboard_separable](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L26)
- Lean declaration: [checkerboard_unique](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L32)


<a id="node-051b33c6473646d1"></a>
## clean_square_cube_does_not_separate

Explicit kernel-checked witnesses: at n = 52 with primes 13 and 5 the square-localised one-dimensional cube is correction-free at both vertices and both controlled shifts, and its second finite coefficient actualOneCubeCoeff 52 26 18 vanishes; at n = 27 with primes 3 and 5 an equally clean cube has second coefficient -4. Correction suppression alone therefore neither forces nor forbids a nonzero cube coefficient at these parameters.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Read the Lean, not the prose. Of the six conjuncts in squareCRT_clean_block_can_vanish two are tautologies: '52 = 52 [MOD 13^2]' is reflexivity of Nat.ModEq, and 'actualOneCubeCoeff 52 13 13 = 0' holds for every n whatsoever because the two shifts are equal (phi(n+13) - phi(n+13)); the same is true of 'actualOneCubeCoeff 27 3 3 = 0' in the nonzero witness. Only one genuine coefficient evaluation is carried in each witness. The 'neither forces nor forbids' reading is an inference from two data points at k = 1, J = 2; no general no-go is formalised, and this node is not a barrier_no_go.

- Lean declaration: [squareCRT_clean_block_can_vanish](../../Erdos249257/SquareCRTCube.lean#L459)
- Lean declaration: [squareCRT_vanishing_countermodel_is_clean](../../Erdos249257/SquareCRTCube.lean#L468)
- Lean declaration: [squareCRT_clean_block_can_be_nonzero](../../Erdos249257/SquareCRTCube.lean#L477)
- Lean declaration: [squareCRT_nonzero_countermodel_is_clean](../../Erdos249257/SquareCRTCube.lean#L485)

- outgoing **barrier_for**: [Z09::square_crt_correction_suppression](BROWSER_Z09_2.md#node-bd0c4154984286a0). Two kernel-checked clean cubes show correction suppression alone neither forces nor forbids a nonzero cube coefficient, so cleanness is not by itself a separation mechanism.

<a id="node-0d4f8c6350cc2866"></a>
## compressed_adjoint_contradiction_consumer

There is no data consisting of positive Q and v, a nonzero integer A and an integer boundary with Q*v*A = boundary and |boundary| < Q*v: a nonzero multiple of Q*v has absolute value at least Q*v.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [false_of_compressedAdjointCertificate](../../Erdos249257/TotientMahlerDefect.lean#L1183)


<a id="node-262a9ac93456a358"></a>
## crt_dirichlet_parity_row

For every dyadic depth e and every normalised affine channel i, there exists an odd input n, congruent to a prescribed base residue modulo 2^(e+3), at which the value of channel i is prime and every other channel value is divisible by a distinct prime congruent to one modulo 2^(e+3). Hence at that row phi of the target value has exact 2-adic depth strictly below e+2, while phi of every other channel value is divisible by 2^(e+2).

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [exists_totientAffinePrimeRow](../../Erdos249257/TotientMahlerDefect.lean#L513)
- Lean declaration: [exists_totientAffineParityRow](../../Erdos249257/TotientMahlerDefect.lean#L729)

- incoming **depends_on_open**: [Z09::finite_level_dyadic_totient_independence](BROWSER_Z09_1.md#node-b015a5eb93d9819b). Placeholder-free dependency: the independence proof consumes the parity rows; no open hypothesis is involved, the edge records which construction carries it.

<a id="node-f31d7ed219857fdf"></a>
## curvature_drive_common_carrier_identity

For every common carrier g, g times the curvature drive at offset s equals 3 L(g, 2H+s) - 2 L(g, H+s) - L(g, 4H+s), where L(g, n) = phi(g) n - g phi(n) is the scaled rough loss. No divisibility or factorisation hypothesis is needed.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [curvatureDrive_commonCarrier](../../Erdos249257/CurvatureCarry.lean#L323)

- outgoing **reformulates**: [Z09::curvature_window_split_sharp_radius](BROWSER_Z09_1.md#node-1c36e925ab9f840b). A denominator-free rewriting of the same drive letters through the scaled rough loss.

<a id="node-4dbf85504d92caa7"></a>
## curvature_residue_gap_nonintegrality

If at some depth L the curvature window residue modulo 2^L lies strictly between the sharp radius 6H + 3L + 3 and 2^L minus that radius, then the affine curvature Q(H) of the totient tail is not an integer.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Non-vacuity is not established. sharpCurvatureCert is decidable, but no witness of sharpCurvatureCert H L is exhibited at any (H, L) anywhere in either library - unlike the three-transport analogue (sharpThreeTransportCert_60_12) and the prime-jump analogue (primeJumpSharpKill_twelve_five), which do have kernel-checked witnesses and therefore do yield unconditional non-integrality facts. This node yields no non-integrality fact about any concrete curvature value.

- Lean declaration: [curvature_notMem_int_of_sharpCurvatureCert](../../Erdos249257/CurvatureCarry.lean#L159)

- outgoing **depends_on_open**: [Z09::curvature_window_split_sharp_radius](BROWSER_Z09_1.md#node-1c36e925ab9f840b). The separation argument needs the exact split and the sharp remainder radius.
- incoming **depends_on_open**: [Z09::curvature_supply_implies_249](BROWSER_Z09_1.md#node-17aef27819f16e76). The conditional endpoint consumes the non-integrality criterion against lcm-cone flatness.
- outgoing **specialises**: [Z09::generic_window_residue_gap_soundness](BROWSER_Z09_1.md#node-6c029622c10f1cc6). Same lattice-separation argument, re-proved inline for the curvature word.

<a id="node-17aef27819f16e76"></a>
## curvature_supply_implies_249

If sharp curvature certificates exist at arbitrarily large lcm heights - either at the fixed log-scaled depth, or at arbitrary depth, or produced by curvature phase certificates - then sum phi(n)/2^n is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The three supply hypotheses are not three independent routes. CurvaturePhaseCertificate carries the field 'sharp : sharpCurvatureCert H (m + exitOffset)', so irrational_totientSeries_of_phaseCertificateSupply is a field projection into the any-depth consumer (CurvatureCarry.lean:308-314) and adds no arithmetic content; the log-scaled-depth supply is a specialisation of the any-depth supply. Effectively one socket. Furthermore no witness of sharpCurvatureCert exists anywhere in the corpus at any (H, L), so none of the three supplies is known to be satisfiable even once.

Open hypotheses: ["SharpCurvatureSupply : forall t0, exists t, t0 <= t and sharpCurvatureCert (periodLcm t) (Nat.log2 (periodLcm t) + 10)", "SharpCurvatureAnyDepthSupply : forall t0, exists t L, t0 <= t and sharpCurvatureCert (periodLcm t) L", "CurvaturePhaseCertificateSupply : forall t0, exists t m r, t0 <= t and Nonempty (CurvaturePhaseCertificate (periodLcm t) m r)"]

- Lean declaration: [irrational_totientSeries_of_sharpCurvatureSupply](../../Erdos249257/CurvatureCarry.lean#L206)
- Lean declaration: [irrational_totientSeries_of_sharpCurvatureAnyDepthSupply](../../Erdos249257/CurvatureCarry.lean#L234)
- Lean declaration: [irrational_totientSeries_of_phaseCertificateSupply](../../Erdos249257/CurvatureCarry.lean#L308)

- outgoing **depends_on_open**: [Z09::curvature_residue_gap_nonintegrality](BROWSER_Z09_1.md#node-4dbf85504d92caa7). The conditional endpoint consumes the non-integrality criterion against lcm-cone flatness.

<a id="node-ee0d98218527ec39"></a>
## curvature_window_doubling_recurrence

The depth-L curvature window satisfies the exact input-driven doubling recurrence W(L+1) = 2 W(L) + drive(L+1), and the affine carry orbit launched at depth m from the genuine prefix window reproduces the curvature window at every later depth.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [curvatureWindow_succ](../../Erdos249257/CurvatureCarry.lean#L259)
- Lean declaration: [curvatureCarryOrbit_curvatureWindow](../../Erdos249257/CurvatureCarry.lean#L283)

- outgoing **reformulates**: [Z09::curvature_window_split_sharp_radius](BROWSER_Z09_1.md#node-1c36e925ab9f840b). The window is re-presented as an affine carry orbit driven by the fresh totient letters.

<a id="node-1c36e925ab9f840b"></a>
## curvature_window_split_sharp_radius

For the affine curvature Q(H) = R_(4H) - 3 R_(2H) + 2 R_H of the totient tail, 2^L Q(H) equals the exact integer depth-L curvature window plus a shifted remainder whose absolute value is at most 6H + 3L + 3 whenever H is positive; the fresh integer letter at offset s is bounded by 6H + 3s. The remainder bound rests only on phi(n) <= n - 1, sharpened to R_M <= M + 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [two_pow_mul_curvature_eq_window_add_shifted](../../Erdos249257/CurvatureCarry.lean#L119)
- Lean declaration: [abs_curvatureShiftedTail_le](../../Erdos249257/CurvatureCarry.lean#L137)
- Lean declaration: [abs_curvatureDrive_le](../../Erdos249257/CurvatureCarry.lean#L46)
- Lean declaration: [totientTail_le_succ](../../Erdos249257/CurvatureCarry.lean#L66)

- incoming **depends_on_open**: [Z09::curvature_residue_gap_nonintegrality](BROWSER_Z09_1.md#node-4dbf85504d92caa7). The separation argument needs the exact split and the sharp remainder radius.
- incoming **reformulates**: [Z09::curvature_window_doubling_recurrence](BROWSER_Z09_1.md#node-ee0d98218527ec39). The window is re-presented as an affine carry orbit driven by the fresh totient letters.
- incoming **reformulates**: [Z09::curvature_drive_common_carrier_identity](BROWSER_Z09_1.md#node-f31d7ed219857fdf). A denominator-free rewriting of the same drive letters through the scaled rough loss.

<a id="node-64ab511bdb80e535"></a>
## dyadic_channel_odd_core_reduction

Every canonical dyadic section n |-> phi(2^j n + r) with r < 2^j is an explicit rational scalar multiple of an odd-core channel: a zero residue reduces to phi(n) or phi(2n), and an even positive residue 2^(t+1) s with s odd reduces to 2^t times the channel at level j - (t+1) and residue s. Consequently every dyadic section lies in the span of the odd-core family.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [totientKernel_zero_residue](../../Erdos249257/TotientMahlerDefect.lean#L160)
- Lean declaration: [totientKernel_even_residue_reduce](../../Erdos249257/TotientMahlerDefect.lean#L169)
- Lean declaration: [totientKernelSeq_zero_mem_span_oddCore](../../Erdos249257/TotientMahlerDefect.lean#L1303)
- Lean declaration: [totientKernelSeq_mem_span_oddCore](../../Erdos249257/TotientMahlerDefect.lean#L1338)

- outgoing **specialises**: [Z09::totient_two_adic_scaling](BROWSER_Z09_2.md#node-0fe9be464c7d5625). The channel reductions are the two-adic scaling identities read on the sequences n |-> phi(2^j n + r).
- incoming **depends_on_open**: [Z09::dyadic_section_basis_classification](BROWSER_Z09_1.md#node-334668b3e5b6c1b9). Spanning comes from the odd-core reduction; independence from the finite-level theorem.

<a id="node-334668b3e5b6c1b9"></a>
## dyadic_section_basis_classification

The odd-core family is linearly independent and spans every dyadic section of Euler's totient, so it is an explicit basis of the span of the full dyadic kernel. Equivalently, the only rational linear relations among dyadic sections of phi are those generated by the two elementary two-adic scaling identities.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [linearIndependent_oddCoreTotientKernelFamily](../../Erdos249257/TotientMahlerDefect.lean#L1265)
- Lean declaration: [span_range_fullTotientKernel_eq_span_range_oddCore](../../Erdos249257/TotientMahlerDefect.lean#L1380)
- Lean declaration: [totientDyadicSectionBasis](../../Erdos249257/TotientMahlerDefect.lean#L1392)

- outgoing **generalises**: [Z09::full_dyadic_kernel_infinite_dimensional](BROWSER_Z09_1.md#node-5cafd211f74a6382). The explicit basis determines the whole relation module and in particular implies the span is infinite dimensional.
- outgoing **depends_on_open**: [Z09::dyadic_channel_odd_core_reduction](BROWSER_Z09_1.md#node-64ab511bdb80e535). Spanning comes from the odd-core reduction; independence from the finite-level theorem.

<a id="node-3c8892f7f35cb8c4"></a>
## euler_sieve_local_identities

Elementary local identities behind the Euler-sieve approximation: 1 - 2/p + 1/p^2 = (1 - 1/p)^2 and 1 - 2/p^2 + 1/p^4 = (1 - 1/p^2)^2 for positive p; and the second difference of the prime-power divisor-sum row sigma_p equals p^(e+1) (p - 1), the prime-power totient row, with first difference p - 1.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [muSqEulerFactor_one](../../ErdosProblems/Erdos249/FiniteEulerSieve.lean#L28)
- Lean declaration: [muSqEulerFactor_two](../../ErdosProblems/Erdos249/FiniteEulerSieve.lean#L36)
- Lean declaration: [sigmaPrimePow_firstDiff](../../ErdosProblems/Erdos249/FiniteEulerSieve.lean#L44)
- Lean declaration: [sigmaPrimePow_secondDiff](../../ErdosProblems/Erdos249/FiniteEulerSieve.lean#L51)


<a id="node-4e06b69878dd4980"></a>
## exponent_only_three_transport_supply_implies_249

If for every threshold there is an exponent a at least 2 with the balanced four-vertex transport commutator at the lcm height periodLcm(3^a - 1) failing to be an integer, then sum phi(n)/2^n is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["ExponentOnlyThreeTransportSupply : forall t0, exists a, 2 <= a and t0 <= 3^a - 1 and threeTransportTailCommutator (periodLcm (3^a - 1)) not in Set.range ((coe) : Int -> Real)"]

- Lean declaration: [irrational_totient_series_of_exponentOnlyThreeTransportSupply](../../Erdos249257/ExponentOnlyTransport.lean#L205)

- outgoing **reformulates**: [Z09::three_transport_supply_implies_249](BROWSER_Z09_2.md#node-b3014c9cc270353e). Same four-vertex observable and same flatness contradiction; the difference is that the hypothesis is stated as bare non-integrality on a 3^a tower rather than as a decidable window certificate.

<a id="node-321a6939105b78f6"></a>
## finite_level_carry_anti_compression

Let v be positive and u a tempered binary carry orbit for phi with multiplier v. If the canonical level-e dyadic totient family is linearly independent, then the rational span of the carry sections through level e has rank at least 2^e - 1. Temperedness is used only to supply the exact recurrence.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The rank bound quantifies over a class of objects that is not known to be inhabited: if Erdos #249 is true then no tempered binary carry orbit for phi exists and both evidence theorems are vacuous. The only discharge available in the corpus is from the negation of #249 (see rationality_forces_unbounded_carry_rank), so this node proves nothing about the actual totient series on its own. The linear-independence hypothesis is genuinely discharged in corpus by finite_level_dyadic_totient_independence; the orbit hypothesis is not.

Open hypotheses: ["IsTemperedBinaryOrbit Nat.totient v u : the existence of a positive multiplier v and an integer sequence u obeying u(N+1) = 2 u(N) - v phi(N+1) together with the temperedness bound. Both evidence theorems carry this as a free hypothesis. No such orbit is constructed anywhere in the corpus, and by not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit its existence is EQUIVALENT to rationality of sum phi(n)/2^n, that is to the FAILURE of Erdos #249."]

- Lean declaration: [finrank_canonicalCarryKernel_ge_of_linearIndependent](../../Erdos249257/TotientCarryKernelRigidity.lean#L211)
- Lean declaration: [finrank_canonicalCarryKernel_ge_of_certificate](../../Erdos249257/TotientCarryKernelRigidity.lean#L245)

- outgoing **depends_on_open**: [Z09::carry_derivative_totient_transport](BROWSER_Z09_1.md#node-ce4185cc29a85233). The carry differences that realise the independent totient channels are supplied by the carry-derivative identity.
- incoming **specialises**: [Z09::rationality_forces_unbounded_carry_rank](BROWSER_Z09_2.md#node-0b905695e89a37be). The rationality-supplied tempered orbit is fed into the finite-level rank bound at every level.
- outgoing **transport_of**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). The node's free hypothesis IsTemperedBinaryOrbit Nat.totient v u is, by not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit, equivalent to rationality of sum phi(n)/2^n, i.e. to failure of Erdos #249.
- outgoing **depends_on_open**: [Z11::rationality_iff_tempered_orbit](BROWSER_Z11_1.md#node-e4f918bdb6539d80). the free hypothesis IsTemperedBinaryOrbit phi v u is, by this equivalence instantiated at c = phi, logically equivalent to rationality of sum phi(n)/2^n, i.e. to the FAILURE of Erdos #249; so no producer can exist and the theorem is vacuous if #249 is true.

<a id="node-b015a5eb93d9819b"></a>
## finite_level_dyadic_totient_independence

For every e, the canonical family of 2^e + 1 dyadic sections of Euler's totient through level e (the two zero-residue base channels and every odd residue at levels 1..e) is linearly independent over the rationals, and its span has rank exactly 2^e + 1.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [exists_separatedMinorCertificate_totientAffineOddFamily](../../Erdos249257/TotientMahlerDefect.lean#L882)
- Lean declaration: [linearIndependent_totientAffineOddFamily](../../Erdos249257/TotientMahlerDefect.lean#L927)
- Lean declaration: [linearIndependent_canonicalTotientKernelFamily](../../Erdos249257/TotientMahlerDefect.lean#L935)
- Lean declaration: [finrank_canonicalTotientKernel_eq](../../Erdos249257/TotientMahlerDefect.lean#L989)

- outgoing **depends_on_open**: [Z09::crt_dirichlet_parity_row](BROWSER_Z09_1.md#node-262a9ac93456a358). Placeholder-free dependency: the independence proof consumes the parity rows; no open hypothesis is involved, the edge records which construction carries it.
- outgoing **depends_on_open**: [Z09::parity_separated_determinant_criterion](BROWSER_Z09_2.md#node-4635adba5e7b5488). The rows are turned into a nonzero minor by the mod-2 unipotence determinant criterion.
- incoming **specialises**: [Z09::full_dyadic_kernel_infinite_dimensional](BROWSER_Z09_1.md#node-5cafd211f74a6382). Infinite dimensionality is the finite-level rank 2^e + 1 instantiated at e equal to a hypothetical ambient finrank.

<a id="node-81c415e101ea6ff3"></a>
## fixed_precision_tropical_no_go

Fix any positive number u of retained unit bits. Then for every finite word of 2-adic valuation-unit symbols with odd units and every initial carry state, there is a compatible carry orbit whose state after every prefix stays within the symmetric radius 2^(valuation + u - 1). Bounded local valuation-unit data alone therefore never excludes all finite centred carry completions.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Rules out only the bounded local signature at a FIXED precision u, with the symbol word treated as free data. It does not rule out: precision u growing with the depth; arithmetic relations among the high quotients; exact rough-prime or factorisation labels on the digits; joint constraints linking symbols at different offsets; or the question whether the ACTUAL curvature drive digits admit such completions. It excludes no certificate supply, and settles nothing about #249.

- Lean declaration: [vu_step_has_centred_completion](../../Erdos249257/TropicalCurvatureCarry.lean#L69)
- Lean declaration: [vu_word_has_prefix_locked_completion](../../Erdos249257/TropicalCurvatureCarry.lean#L115)
- Lean declaration: [fixedPrecisionTropicalNoGo](../../Erdos249257/TropicalCurvatureCarry.lean#L137)

- incoming **generalises**: [Z09::affine_step_centred_completion](BROWSER_Z09_1.md#node-cafcebbeee7d0516). The prime-ray lemma is the tropical one-step recentring with the valuation-unit dressing replaced by an arbitrary residue class modulo an even modulus.

<a id="node-272bda2cbb01131a"></a>
## four_point_divisor_layer_identity

Given the four explicit divisor-layer factorisations of A at q, r q, s q and r s q in terms of layer functions C, the product A(r s q) A(q) equals A(r q) A(s q) C(r s) C(r s q).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [fourPoint_layer_identity](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L45)


<a id="node-5cafd211f74a6382"></a>
## full_dyadic_kernel_infinite_dimensional

The rational span of all dyadic sections n |-> phi(2^j n + r) of Euler's totient is not finite dimensional.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [not_finiteDimensional_span_fullTotientKernel](../../Erdos249257/TotientMahlerDefect.lean#L1145)

- outgoing **specialises**: [Z09::finite_level_dyadic_totient_independence](BROWSER_Z09_1.md#node-b015a5eb93d9819b). Infinite dimensionality is the finite-level rank 2^e + 1 instantiated at e equal to a hypothetical ambient finrank.
- incoming **generalises**: [Z09::dyadic_section_basis_classification](BROWSER_Z09_1.md#node-334668b3e5b6c1b9). The explicit basis determines the whole relation module and in particular implies the span is infinite dimensional.

<a id="node-6c029622c10f1cc6"></a>
## generic_window_residue_gap_soundness

Generic modular soundness: if a real number equals an integer A divided by 2^L plus a remainder e with |e 2^L| at most R, and A mod 2^L lies strictly between R and 2^L - R, then the real number is not an integer.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [notMem_int_of_window_remainder_bound](../../Erdos249257/PrimeJumpWindow.lean#L53)

- incoming **specialises**: [Z09::curvature_residue_gap_nonintegrality](BROWSER_Z09_1.md#node-4dbf85504d92caa7). Same lattice-separation argument, re-proved inline for the curvature word.
- incoming **specialises**: [Z09::three_transport_window_certificate](BROWSER_Z09_2.md#node-1c4f511c806cea73). Same lattice-separation argument, re-proved inline for the balanced boundary word.
- incoming **specialises**: [Z09::joint35_cone_window_certificate](BROWSER_Z09_1.md#node-e0453b8e36d74a09). Same lattice-separation argument, re-proved inline for the joint cone word.
- outgoing **reformulates**: [Z06::endpoint_certificate_soundness](BROWSER_Z06_1.md#node-552175c811881922). notMem_int_of_window_remainder_bound (PrimeJumpWindow.lean) is the stencil-free abstraction of the truncate-then-separate argument of tail_diff_notMem_int_of_certifiedKill; the endpoint certificate is its (h,N) instance.
- incoming **specialises**: [Z06::endpoint_certificate_soundness](BROWSER_Z06_1.md#node-552175c811881922). Z09's `notMem_int_of_window_remainder_bound` is the generic criterion (x = A/2^L + e with |e 2^L| <= R and A mod 2^L strictly inside (R, 2^L - R) implies x not an integer); Z06's `tail_diff_notMem_int_of_certifiedKill` is that criterion at x = R_{N+h} - R_N, A = the depth-L window discrepancy and R = N+h+L+2, the remainder bound supplied by `tail_diff_eq_increment_prefix_add_shifted` and `abs_tail_diff_lt`.

<a id="node-e0453b8e36d74a09"></a>
## joint35_cone_window_certificate

For the four-vertex cone observable R_(15H) - 3 R_(3H) - 2 R_(5H) + 4 R_H, 2^L times the observable equals an exact integer depth-L window plus a shifted remainder of size at most 19H + 5L + 5; the window obeys the input-driven doubling recurrence; and a window residue mod 2^L inside the complementary band proves the observable is not an integer. The associated eight-vertex transport tail expands into four diagonal differences.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Non-vacuity is not established: no witness of sharpJoint35ConeCert is exhibited at any (H, L) anywhere in either library, so the criterion yields no non-integrality fact about any concrete joint (3,5) cone value. The eight-vertex joint35TransportTail_expand is an unfolding identity only; it carries no bound and no certificate.

- Lean declaration: [two_pow_mul_joint35Cone_eq_window_add_shifted](../../Erdos249257/JointExponentTransport.lean#L127)
- Lean declaration: [abs_joint35ConeShiftedTail_le](../../Erdos249257/JointExponentTransport.lean#L148)
- Lean declaration: [joint35Cone_notMem_int_of_cert](../../Erdos249257/JointExponentTransport.lean#L172)
- Lean declaration: [joint35ConeWindow_succ](../../Erdos249257/JointExponentTransport.lean#L246)
- Lean declaration: [joint35TransportTail_expand](../../Erdos249257/JointExponentTransport.lean#L259)

- outgoing **specialises**: [Z09::generic_window_residue_gap_soundness](BROWSER_Z09_1.md#node-6c029622c10f1cc6). Same lattice-separation argument, re-proved inline for the joint cone word.
- incoming **depends_on_open**: [Z09::joint35_supply_implies_249](BROWSER_Z09_1.md#node-9c279fbb368b55e6). The endpoint consumes the joint cone non-integrality criterion; the supply is unproved and has no finite instance in this module.

<a id="node-9c279fbb368b55e6"></a>
## joint35_supply_implies_249

If sharp joint (3,5) cone certificates exist at arbitrarily large lcm heights above t = 5 and arbitrary depth, then sum phi(n)/2^n is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["AnchoredJoint35ConeSupply : forall t0, exists t L, max t0 5 <= t and sharpJoint35ConeCert (periodLcm t) L"]

- Lean declaration: [irrational_totient_series_of_anchoredJoint35ConeSupply](../../Erdos249257/JointExponentTransport.lean#L217)

- outgoing **depends_on_open**: [Z09::joint35_cone_window_certificate](BROWSER_Z09_1.md#node-e0453b8e36d74a09). The endpoint consumes the joint cone non-integrality criterion; the supply is unproved and has no finite instance in this module.

