# erdos_1049 mathematical frontier

Generated from the exported research packet. Read the strongest applicable
result before attempting a proof; superseded results remain history.

Determine irrationality of the rational-base Lambert values, with 3/2 as the first resistant explicit base.

## Established results and their evidence

### pade_threshold_law_over_rational_bases

The scalar q-Apery Pade family has a closed-form critical exponent over rational bases. The source recurrence's seeds are q-generic - L_0=0, L_1=-q(q+2)/(q-1), R_0=1, R_1=-(q^2+q-1), recovered from the Casoratian - and with them L_j/R_j converges to sum_(n>=1) 1/(q^n-1) at EVERY rational q>1, matched to 57-295 decimal digits over ten bases, so cross-base comparison is legitimate. Writing q=a/b in lowest terms and using a three-point estimator that cancels the linear term exactly: log|R_j| ~ (3/2)log(a/b) j^2 (1e-8), log den(R_j) ~ (3/2)log2 j^2 (1e-14), log|rho_j - rho| ~ -3 log(a/b) j^2 (1e-7), the content removed in passing to the primitive vector is O(1) with maximum 59 over all bases and indices, and log|B_j| ~ kappa log a j^2 where KAPPA DEPENDS ONLY ON THE NUMERATOR a, never on b (q=3/2 gives 1.80446 and q=3 gives 1.80393; q=5/2 gives 1.80415 and q=5/3 gives 1.80324). Over 40 estimates the mean is kappa = 1.803946 against 3/2 + 3/pi^2 = 1.8039635, agreement 1.8e-5. The 3/pi^2 = 1/(2 zeta(2)) is the phi-weighted primitive cyclotomic part, and this is confirmed TERM BY TERM rather than as a fitted constant: the decomposition log|B_j| = log a ((3/2) j^2 + sum_(i<=j) phi(i)) + O(j) predicts the per-step increment (log|B_j| - log|B_(j-1)|)/log a - (3j - 3/2) = phi(j) + O(1), and since phi swings violently (phi(59)=58 against phi(60)=16) tracking it is a mechanism test. Measured at q=3/2 over j=40..66: correlation 0.98922, slope 0.9905, with the residual following every swing (j=48 phi=16 residual 12.7; j=53 phi=52 residual 53.5; j=59 phi=58 residual 59.5; j=60 phi=16 residual 16.7). The closed form GAP = (3/pi^2 - 3/2) log a + 3 log b also reproduces the measured GAP VALUE, not just its sign, to about 0.002 at every base including both razor-thin boundary pairs. Hence the linear forms tend to zero exactly when log b / log a < 1 - kappa/3 = 1/2 - 1/pi^2 = 0.3986788, i.e. a > b^2.50828. CALIBRATION: the instrument reproduces the recorded landscape - closes at q=2 and q=3 (Erdos 1948 / Borwein), closes at q=7/2 (Bundschuh-Vaananen), fails at q=5/2 and at q=3/2 (the open case), and calls both razor-thin boundary pairs correctly (14/3 fails at +0.141 while 16/3 closes at -0.020; 31/4 fails at +0.053 while 33/4 closes at -0.023). Those two pairs pin the constant: a kappa outside (1.7889, 1.8106) would mis-call them. GAP<0 is the height-versus-decay balance, not a complete irrationality proof; nonvanishing remains a separate obligation, and 3/pi^2 is a numerical identification rather than a derivation. Evidence: PadeThresholdLawLab.md, formal_math/probes/erdos1049_pade_threshold_law.py.

Evidence/status: measured_asymptotic_law_calibrated_against_every_known_base_six_falsifiers_passing


### casoratian_closed_form_and_block_structure_theorem

The Casoratian of the source recurrence telescopes in closed form: W_j = L_(j+1)R_j - L_jR_(j+1) = -3^(j+1)(3^(j+1)+2^(j+2)) / (2^(j+1)(3^(j+1)-2^(j+1))), checked against exact rationals for j <= 46. Dividing by R_jR_(j+1) makes rho_j = L_j/R_j an explicit telescoping sum, and for p >= 5 the only p-adic poles of the increments sit at j == -1 mod d, d = ord_p(3/2). Hence the loss set is a union of whole intervals [dK, dK+d-1] -- the BLOCK STRUCTURE IS NOW A THEOREM, not a measurement, under the standing hypothesis that R_j is a p-adic unit. Summing the polar increments with 3^(dK)-2^(dK) = 2^(dK) K pi u_K, u_K == 1 mod p^eps, derives the harmonic numbers rather than observing them: rho_j = rho_(j0) - (c/pi) H_(floor(j/d)) + p-integral, so p | B_j iff v_p(H_(floor(j/d))) < eps. Same identity over R gives an exact series for the target constant and confirms lim L_j/R_j = sum_(n>=1) 2^n/(3^n-2^n) to 123 decimal digits. Evidence: CasoratianBlockLawProof.md, formal_math/probes/erdos1049_casoratian_block_law.py, 122 primes below 700 to index 420, all six falsifiers passing.

Evidence/status: proved_from_a_closed_form_casoratian_with_six_falsifiers_passing


### coordinatewise_corridor_obstruction

A literal coordinatewise transfer of the integer-base congruence corridor forces an exponential-versus-linear inequality and is impossible at base 3/2.

Evidence/status: lean_checked

- [RationalBaseLambert.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalBaseLambert.lean)

claim_boundary: The result refutes only the literal coordinatewise corridor transfer at base 3/2. It does not rule out non-coordinatewise selector mechanisms, prove irrationality, or establish a cofinal q-Apery construction.

### three_mul_lt_two_pow_succ_consumer

For every natural x at least 2, 3*x < 2^(x+1). This is the exact exponential-versus-linear arithmetic producer consumed by coordinatewiseCorridor_implies_pow_lt_linear and threeHalves_no_coordinatewiseCorridor; it formalizes the strict boundary that kills a literal coordinatewise transfer at base 3/2.

Evidence/status: lean_checked_arithmetic_producer_and_corridor_consumer

- [RationalBaseLambert.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalBaseLambert.lean)

claim_boundary: The theorem is an elementary arithmetic inequality and does not establish the q-Apery analytic estimate, a non-scalar recombination, or irrationality at base 3/2. Its downstream no-go rules out only the literal coordinatewise corridor route.

### rational_base_cleared_tail_recurrence

The exact denominator-cleared rational-base tail satisfies U_(N+1)=r U_N-B c_(N+1) s^(N+1); for s>=2 with positive data the forcing magnitude is at least 2^(N+1), while at s=1 the tax collapses exactly.

Evidence/status: lean_checked

- [RationalBaseLambert.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalBaseLambert.lean)

claim_boundary: The recurrence is unconditional under the theorem's nonzero-r hypothesis; the 2^(N+1) lower bound additionally assumes natural s>=2, B>=1, and coeff(N+1)>=1. This is an exact denominator-clearing and forcing-growth result only: it does not prove irrationality at 3/2, supply rational-base asymptotics, or show that the forcing term cannot be canceled by a separate analytic argument.

### seven_halves_height_criterion

At q=7/2, Lean checks both the literal Bundschuh--Vaananen Archimedean height condition log(7)/log(7/2) < (1/2+1/pi^2)^(-1) and its transformed logarithmic certificate.

Evidence/status: external_theorem_with_lean_checked_parameter_specialization

- [RationalBaseLambert.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalBaseLambert.lean)

claim_boundary: The five named Lean declarations prove the 7/2 numerical admission condition in source-facing and transformed forms. The external analytic irrationality theorem, its inherited hypotheses, and the implication from this admission condition remain source-backed rather than kernel-internal; this row does not extend the theorem to 3/2 or unrestricted rational bases.

### seven_halves_arithmetic_certificate

The exact integer comparison 2^18 < 7^7, logarithmic consequence log(2)/log(7) < 7/18, strict pi margin, height-region membership, and literal source-facing Archimedean height condition at 7/2 are Lean-checked. The external analytic theorem itself remains source-backed.

Evidence/status: lean_checked_arithmetic_certificate

- [RationalBaseLambert.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalBaseLambert.lean)

claim_boundary: The six named declarations prove the elementary power comparison, logarithmic estimate, pi-margin inequality, height-region membership, and source-facing numerical admission condition at 7/2. They do not formalize or reprove the external Bundschuh--Vaananen irrationality theorem or inherited hypotheses, nor establish irrationality for 3/2 or unrestricted rational bases.

### rational_pade_homogenisation

The rational-base Pade construction can be homogenised over integer numerator and denominator parameters.

Evidence/status: advisory_exact_algebra_pending_lean


### rational_pade_denominator_exponent_bounds

After doubling exponents, every P-summand denominator exponent is bounded by 3n^2-n via the factor (n-k)(3n-k-1), and the Q-maximum gap is exactly 2(n+m(m-1)).

Evidence/status: lean_checked

- [RationalPadeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean)

claim_boundary: The Lean declarations prove the stated denominator-exponent inequalities for the packet's integer-indexed Pade expressions. They do not prove convergence, irrationality, optimality of the bound, or the full rational-base Pade construction.

### rational_pade_exterior_sign_consumers

When both Padé errors are positive, either alternating sign pattern on the first coefficients forces the adjacent exterior determinant to have the corresponding strict sign. These are explicit determinant nonvanishing consumers under the source hypotheses, closing sign-driven cancellation in both orientations without asserting that the source construction supplies those hypotheses at every index.

Evidence/status: lean_checked_sign_consumer

- [RationalPadeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean)

claim_boundary: The sign consumers apply only to the displayed integer coefficient signs and positive-error assumptions. They do not establish those assumptions for the full q-Apery/Zudilin family, quantify determinant height or local divisibility, control the analytic remainder, or prove irrationality at base 3/2.

### zudilin_rational_homogenisation_height_region

For coprime integers a > b >= 1 with log(b)/log(a) < C_0/C_1 = 0.40568302138..., the value h_{a/b}(1) = sum_{m>=1} 1/((a/b)^m - 1) = sum_{n>=1} tau(n) (b/a)^n is irrational. In particular F((31/4)^r) is irrational for every r >= 1. Proof: with a_j = alpha_j n + 1, b = 27n + 2 for (14,12,14;27), N = 15n, M_n = 266n^2 + 34n + 1: (i) Zudilin 2004 Lemma 7 in Z[p]; (ii) elementary degree count and positivity; (iii) Zudilin Lemmas 1 and 2 give (K_n - W_n)/n^2 -> C_0 and K_n/n^2 -> C_1; hence b^{W_n} Lambda_n(a/b) is a positive element of Z h + Z whose logarithm over n^2 tends to C_1 log b - C_0 log a < 0.

Evidence/status: upgraded_2026_09_02_to_ordinary_complete_proof_citing_published_lemmas_see_superseded_by

Superseded by **['zudilin_rational_base_region_theorem']**. Use that stronger result.


### zudilin_rational_base_region_theorem

THEOREM A (region). Let a > b >= 1 be coprime integers with b^mu < a, mu = C_1/C_0 = 2.464978683574975037454488275535521581878..., equivalently log b / log a < theta* = 1/mu = 0.40568302138406054101566030557693017464819107867787.... Then F(a/b) = sum_{m>=1} 1/((a/b)^m - 1) is irrational. In the normalisation of Zudilin 2016 Sec. 2 (p = r/s, log|r| > c log|s|) the constant is c = mu, the irrationality-exponent bound of Zudilin 2004 Theorem 1 itself. Consequences: the strip s^mu < r < s^{mu_BV} (mu_BV = 2 pi^2/(pi^2-2) = 2.508284761994...) of bases beyond Bundschuh-Vaananen 1994 Theorem 2 is infinite; new bases with s <= 12 are 31/4; 53/5, 54/5, 56/5; 83/6, 85/6, 89/6; 122/7,...,131/7 (9 bases); 169/8,...,183/8 (odd r, 8 bases); 15, 12, 37, 17 bases for s = 9, 10, 11, 12; none for s = 2, 3. 31/4 is the new base of smallest denominator and smallest numerator. Among coprime a/b with a <= 60 the region has 137 members; closest misses 52/5 (theta = 0.407324), 51/5, 29/4 (0.411694); tightest members 53/5 (margin 0.000313), 31/4 (0.001985), 54/5.

Evidence/status: ordinary_complete_proof_citing_published_lemmas_finite_part_lean_checked


claim_boundary: The theorem proves irrationality only on the region; it says nothing about F(3/2) (theta = 0.630930, gap 0.225247 above theta*), negative bases, or any base with b^mu >= a. Not kernel-checked; not published; no independent review. Priority: extends Bundschuh-Vaananen 1994 Theorem 2 (second half, p. 177, region 1/2 - 1/pi^2 = 0.398679); Zudilin 2016 Sec. 2 announced the rational-base shape with an unspecified computable c; Matala-aho-Vaananen-Zudilin 2006 treats integer p only and states (p. 880) that its methods do not sharpen Zudilin 2004; Duverney 1996 Theorem 2 (0.23201) is weaker (prior_art_adjudication_2026_09_02.md, addendum dea7d99cff).

### thirtyone_four_irrational_ordinary_theorem

THEOREM B. F(31/4) is irrational, and so is F((31/4)^r) for every integer r >= 1. Here log 4 / log 31 = 0.4036981731... < 81/200 < theta*, 4^mu = 30.4835... < 31 < 4^{mu_BV} = 32.3696..., so 31/4 lies outside the Bundschuh-Vaananen region and inside Theorem A's; it is the first base (smallest denominator and numerator) beyond the published region.

Evidence/status: ordinary_complete_proof_citing_published_lemmas_parameter_facts_lean_checked


claim_boundary: An instance of Theorem A; carries exactly its evidence class and attribution.

### archimedean_homogenisation_cap_by_dirichlet

THEOREM C (Archimedean cap). For any sequence (U_n, V_n) in Z[x]^2 with U_n(x)F(x) - V_n(x) != 0, deg U_n, deg V_n <= delta n^2 (1+o(1)), and log|U_n(x)F(x) - V_n(x)| = -sigma n^2 log x (1+o(1)) for every real x > 1 with sigma, delta independent of x (every p-uniform Pade-type family, Zudilin's included), the homogenised forms b^{deg U_n}(U_n F - V_n)(a/b) tend to 0 exactly on log b/log a < sigma/(sigma+delta), and sigma/(sigma+delta) <= 1/2. Hence no such family proves irrationality of F(a/b) unless b^2 < a; none reaches 3/2 (theta = 0.630930). For Zudilin's family sigma = C_0, delta = C_1 - C_0, so the threshold is exactly 1/mu: the rational-base threshold of a p-uniform family is the reciprocal of its integer-base irrationality-exponent bound (theta* = 1/mu_Zudilin, 1/2 - 1/pi^2 = 1/mu_BV).

Evidence/status: broken_as_first_printed_missing_coefficient_height_hypothesis_superseded

Superseded by **['archimedean_homogenisation_cap_with_coefficient_height']**. Use that stronger result.


claim_boundary: Says nothing about families whose smallness exponent depends on the base, about content-constrained constructions, or about rank >= 3 with full linear independence; it does not prove or disprove irrationality of F(3/2).

### archimedean_homogenisation_cap_with_coefficient_height

THEOREM C (Archimedean cap; corrected). Let (U_n, V_n) in Z[x]^2 be any sequence such that, for constants sigma, delta > 0 and h >= 0 independent of n and of the base: (1) Lambda_n(x) := U_n(x) F(x) - V_n(x) != 0 for every real x > 1; (2) deg U_n, deg V_n <= delta n^2 (1+o(1)); (3) log max(H(U_n), H(V_n)) <= h n^2 (1+o(1)), H(P) = largest absolute value of a coefficient of P (coefficient height); (4) log|Lambda_n(x)| = -sigma n^2 log x (1+o(1)) for every real x > 1. Then the homogenised forms b^{deg U_n} Lambda_n(a/b) tend to 0 exactly on log b/log a < sigma/(sigma+delta), and sigma <= delta, i.e. sigma/(sigma+delta) <= 1/2. Hence no such family proves irrationality of F(a/b) unless b^2 < a; in particular none reaches 3/2. For Zudilin's family sigma = C_0, delta = C_1 - C_0, and hypothesis (3) holds with h = 0 (log H(U_n) = 18.43, 46.73, 72.02, log H(V_n) = 21.54, 50.70, 76.49 for n = 1, 2, 3, i.e. O(n); adv_theorem_c_heights.log; also the paper's (25) is the value bound |A_n(p)| <= |p|^{C_1 n^2 + O(n)}), so the threshold is exactly 1/mu: the rational-base threshold of a base-uniform family with bounded coefficient height is the reciprocal of its integer-base irrationality-exponent bound (theta* = 1/mu_Zudilin, 1/2 - 1/pi^2 = 1/mu_BV).

Evidence/status: proof_backed_no_go_mechanism_independent_corrected_2026_09_02


claim_boundary: Says nothing about families whose smallness exponent depends on the base, whose coefficient height grows faster than exp(O(n^2)), about content-constrained constructions, or about rank >= 3 with full linear independence; that every Pade-type construction satisfies (1)-(4) is a definition of the class considered, verified only for Zudilin's family. It does not prove or disprove irrationality of F(3/2).

### thirtyone_four_two_fifths_log_lower_bound

The elementary integer comparison 31²<4⁵ yields the strict logarithmic lower bound 2/5<log(4)/log(31). This is the rational height boundary used to separate the 31/4 family from the older Bundschuh–Väänänen margin.

Evidence/status: lean_checked_elementary_height_boundary

- [ZudilinHeightRegion.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean)

claim_boundary: Only this finite logarithmic inequality is formalized; it is not a published Zudilin rational-base theorem, does not prove membership in the analytic height region by itself, and says nothing about irrationality of the associated Lambert value.

### bundschuh_vaanen_margin_two_fifths_consumer

The old Bundschuh--Vaananen margin satisfies 1/2 - 1/pi^2 < 2/5. The exact strict inequality is consumed by AdelicHeightBridge.threeHalves_bv_height_gap_gt_threeThirteenths, providing its quantitative positive gap while preserving the distinction between the elementary margin and the external analytic height theorem.

Evidence/status: lean_checked_height_margin_consumer

- [ZudilinHeightRegion.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean)

claim_boundary: This theorem only compares the elementary pi margin with 2/5. It does not establish the external Bundschuh--Vaananen irrationality theorem, membership for a rational base, a Padé height estimate, or irrationality at base 3/2.

### thirtyone_four_outside_bundschuh_vaanen_boundary

The rational base 31/4 lies outside the older Bundschuh–Väänänen height region: its exact lower boundary 2/5 < log(4)/log(31) exceeds the strict margin 1/2−1/pi² < 2/5. This is a Lean-checked method-applicability boundary, distinct from the newer 81/200 height-region membership result.

Evidence/status: lean_checked_method_boundary_consumer

- [ZudilinHeightRegion.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean)

claim_boundary: The exclusion only says that the older analytic criterion cannot be applied at 31/4. It does not prove rationality or irrationality of the associated Lambert value, and it does not invalidate the separately recorded newer 81/200 parameter contour or its external asymptotic dependencies.

### thirtyone_four_power_family

For every r>=1, the logarithmic height ratio of (31/4)^r is exactly reduced to the ratio for 31/4 and satisfies the 81/200 cutoff. The common-power invariance, exact threshold certificate 4^200<31^81, and separation from the older Bundschuh-Vaananen region are Lean-checked; irrationality of F((31/4)^r) for every r >= 1 now follows from the region theorem zudilin_rational_base_region_theorem (ordinary complete proof citing Zudilin 2004 Lemma 7 (with Lemmas 3, 4's (16), 5 and identity (9)-(11); Lemmas 1-2 not needed); not kernel-checked); membership of every power in the full contour region, not only in the 81/200 sub-region, is Lean-checked in RationalBaseContour.lean (thirtyoneFour_power_mem_zudilinContourRegion). ATTRIBUTION CORRECTION 2026-08-11: 81/200 must NOT be described as a source-backed or published Zudilin threshold. Zudilin 2004 proves an integer-base irrationality-exponent bound on a parameter cone; it states no rational-base height theorem at this or any cutoff. 81/200 is an elementary rational sub-boundary of this packet's own authored homogenisation contour 0.40568302138..., which consumes Zudilin 2004 Lemma 7 (in Z[p]) and Lemma 2 and is otherwise elementary (derived and adversarially verified 2026-09-02; see zudilin_rational_homogenisation_height_region). The public problem note already words this correctly - it verifies membership and exclusion for log b/log a < 81/200 and explicitly cites no analytic irrationality theorem for that cutoff - and this packet is now aligned with the note.

Evidence/status: ordinary_theorem_citing_zudilin_2004_lemmas_with_lean_checked_contour_membership_of_all_powers

- [ZudilinHeightRegion.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean)

claim_boundary: The named Lean declarations prove the parameter facts (power comparison, ratio cutoff, region membership, power invariance). They do not formalize the analytic steps of the region theorem; the irrationality of F((31/4)^r) is an ordinary theorem citing Zudilin 2004 Lemma 7 (with Lemmas 3, 4's (16), 5 and identity (9)-(11); Lemmas 1-2 not needed) (see zudilin_rational_base_region_theorem), not a kernel-checked statement.

### three_halves_outside_published_height_regions

Exact arithmetic proves 3^81<2^200 and hence 81/200<log(2)/log(3). Therefore the explicit base 3/2 lies outside the 81/200 cutoff and outside the weaker Bundschuh-Vaananen height region. Of these two, only Bundschuh-Vaananen is a published analytic theorem: their Theorem 2 in the alpha=-1 case requires lambda < (1/2 + 1/pi^2)^(-1), equivalently log(b)/log(a) < 1/2 - 1/pi^2 = 0.398678816..., and it genuinely covers non-integer rational bases including 7/2. The 81/200 cutoff is this packet's own elementary sub-boundary and is not a published criterion. Reaching 3/2 requires a threshold strictly beyond log(2)/log(3) = 0.630929753..., so the gap to the published frontier is about 0.2323, not an incremental shave.

Evidence/status: lean_checked_source_boundary

- [ZudilinHeightRegion.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinHeightRegion.lean)

claim_boundary: The cited Lean declarations prove the exact power comparison, logarithmic ratio inequalities, and membership or exclusion predicates encoded in this source. They do not prove the external analytic irrationality theorem, the published attribution beyond the packet's recorded statement, or irrationality of the base-3/2 Lambert value.

### three_pow_forty_one_upper_certificate

Lean proves 3^41<2^65, the exact integer certificate underlying the #1049 logarithmic ratio bound log(3)/log(2)<65/41.

Evidence/status: lean_checked_upper_power_certificate

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: Only the integer power comparison is formalized; it does not prove the logarithmic consequence independently, an analytic height theorem, or irrationality of the base-3/2 Lambert value.

### two_pow_sixty_four_sharpness_certificate

Lean proves 2^64<3^41, recording that the exponent 65 in the companion upper certificate cannot be lowered to 64. This is the exact sharpness boundary for the #1049 rational logarithmic upper bound.

Evidence/status: lean_checked_sharpness_boundary

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: Only the integer power comparison is formalized; it does not prove a logarithmic lower bound, an analytic height theorem, or irrationality of the base-3/2 Lambert value.

### log_three_div_log_two_sharp_upper_consumer

Lean proves log(3)/log(2)<65/41 from the exact integer certificate 3^41<2^65. This is the sharp rational upper bound used by the #1049 quantitative three-halves frontier calculations.

Evidence/status: lean_checked_sharp_ratio_upper_bound

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: Only the logarithmic arithmetic inequality; no analytic height theorem, approximating forms, or irrationality conclusion.

### forty_one_sixty_five_reciprocal_ratio_consumer

From the sharp upper certificate log(3)/log(2)<65/41, Lean derives the reciprocal inequality 41/65 < log(2)/log(3). This exact ratio bridge is the arithmetic input used by the packet's three-halves height and published-frontier gap calculations.

Evidence/status: lean_checked_reciprocal_ratio_bridge

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: This is only a reciprocal logarithmic inequality. It does not prove the analytic height theorem, an irrationality result, or any statement about the existence or decay of approximating forms.

### three_halves_bv_gap_consumer

Lean proves the explicit quantitative separation (3/13) < log(2)/log(3) - (1/2 - 1/pi^2). The bound combines the sharp integer certificate 41/65 < log(2)/log(3) with the source's published-frontier margin below 2/5, showing that base 3/2 misses the Bundschuh–Väänänen threshold by more than 3/13.

Evidence/status: lean_checked_quantitative_published_frontier_gap

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: This is only an exact arithmetic gap statement relative to the named published frontier. It does not reprove the external Bundschuh–Väänänen analytic theorem, establish a rational-base irrationality conclusion, or rule out nonrectangular, higher-rank, or different integral constructions.

### three_halves_hankel_charge_threshold_consumer

Lean proves the exact charge ceiling ((log 3/log 2)-1)/3 < 8/41. This is the rational threshold consequence of the sharp 41/65 logarithmic certificate and records that, starting from raw cubic charge 4, more than 39/41 must be removed before a three-halves Hankel route can meet the stated height budget.

Evidence/status: lean_checked_quantitative_hankel_consumer

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: This is only an exact arithmetic threshold comparison. It does not prove a Hankel determinant construction, any divisibility or cancellation at the required charge, an analytic irrationality theorem, or irrationality of the base-3/2 Lambert value.

### rectangular_hermite_pade_threshold_no_go

For every rho>=0 and sigma>=1+rho, the standard rectangular simultaneous two-function Hermite-Pade threshold is at most 1/2-1/pi^2, with equality exactly at rho=0 and sigma=1. Lean checks the exact cleared polynomial identity, nonpositivity, equality characterization, and threshold inequality; the packet's additional hypothesis rho<=1 is unnecessary.

Evidence/status: lean_checked_and_strengthened

- [HermitePadeNoGo.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/HermitePadeNoGo.lean)

claim_boundary: The five named declarations prove the exact inequalities and equality characterization for the explicit rectangular Hermite-Pade exponent model defined in the cited Lean source, with no upper bound on rho. They do not construct approximating polynomials or remainders, prove that every rational-base method has this model, supply an analytic irrationality theorem, or decide the arithmetic nature of the Lambert value at 3/2.

### three_halves_rectangular_hp_gap_consumer

For every rectangular Hermite-Pade parameter pair rho,sigma with 0<=rho and 1+rho<=sigma, Lean proves the explicit gap 3/13 < log(2)/log(3) - hpThreshold rho sigma. This composes the sharp Bundschuh-Vaananen frontier gap with the rectangular threshold bound and shows that no admissible rectangular parameter choice recovers even the first 3/13 of the missing three-halves height.

Evidence/status: lean_checked_quantitative_rectangular_consumer

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: This is a conditional quantitative no-go for the named rectangular threshold. It does not prove the external analytic theorem, construct an irrationality form, address nonrectangular or higher-rank systems, or establish irrationality of the base-3/2 Lambert value.

### three_halves_local_valuation_obstruction

The returned all-n formulas assert (v3(U_n),v3(V_n))=(2n^2,0), (v2(U_n),v2(V_n))=(0,1), and for m>n, v2(Delta_n,m)=K_n and v3(Delta_n,m)=2n^2. Lean now checks the determinant/error identity, transfer of every divisor common to the two U channels or the two V channels, and nonvanishing from positive errors plus alternating coefficient signs. Exact Fraction arithmetic reproduces the valuation formulas and nonvanishing for 1<=n<m<=4; the all-n Zudilin valuation inputs remain source-dependent.

Evidence/status: advisory_all_n_valuation_claim_with_lean_checked_abstract_exterior_core_and_exact_low_index_reproduction

- [RationalPadeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean)

claim_boundary: The cited Lean declarations prove the algebraic determinant/error identity, content and common-divisor transfer, and sign-based nonvanishing under their explicit hypotheses. They do not prove the asserted all-n 2-adic or 3-adic valuation formulas, the Zudilin valuation inputs, the exact low-index Fraction computations, or irrationality of the #1049 Lambert value.

### adjacent_exterior_determinant_core

For Delta=U_n V_m-U_m V_n and L_j=U_j S-V_j, Lean proves Delta=U_m L_n-U_n L_m. Every divisor common to U_n and U_m divides Delta, every divisor common to V_n and V_m divides Delta, and positive errors with either alternating sign pattern on U_n,U_m force Delta to be strictly positive or strictly negative and hence nonzero.

Evidence/status: lean_checked

- [RationalPadeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean)

claim_boundary: The five named declarations prove the exact determinant/error identity, common-divisor transfer, and sign-based nonvanishing under their displayed integer and positive-error hypotheses. They do not establish the all-index Pade error signs, the returned 2-adic or 3-adic valuation formulas, any determinant height gain, the analytic irrationality estimate, or irrationality of the #1049 Lambert value.

### primitive_pade_content_no_go

Rowwise multiplication of a Pade coefficient pair scales its analytic error by exactly the same content, and independent contents c_n,c_m factor from the exterior determinant as exactly c_n*c_m; the natural absolute determinant height acquires that same product. At homogeneous base (3,2), if the left polynomial has unit top endpoint and the right polynomial has unit constant endpoint, any common multiplier of the two specialised channels is divisible by neither 2 nor 3. Therefore the missing 2-adic/3-adic gain cannot come from row content and must survive primitive normalisation.

Evidence/status: lean_checked

- [RationalPadeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean)

claim_boundary: The named declarations establish the exact row-content and exterior-determinant factorisations together with the stated base-point 2-adic/3-adic obstruction. They do not provide the missing uniform determinant lower bound, an irrationality proof for Erdős #1049, or a conclusion for arbitrary Pade families beyond the explicit hypotheses.

### adjacent_exterior_archimedean_no_go

For the adjacent pair m=n+1, the returned local gain is approximately 380.309012 n^2, exceeding the previously missing 134.988791 n^2, but the determinant height is approximately 491.159 n^2. The normalized exponent therefore remains positive by approximately 110.850 n^2, so the raw adjacent determinant does not prove irrationality at 3/2.

Evidence/status: advisory_asymptotic_calculation_not_lean_checked


### zudilin_cone_endpoint_exponent_arithmetic

Lean proves the doubled normalizing exponent, the exact bottom exponent 2(a2-a1)(a0+a2-b), and strict first-difference formulas that make a2 the unique bottom exponent and b-1 the unique raw-degree endpoint under the source cone hypotheses. The exact verifier reproduces these conclusions over all 750 finite test tuples.

Evidence/status: lean_checked_with_exact_finite_enumeration

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The Lean declarations prove the endpoint exponent identities and strict first-difference formulas under the explicit source-cone hypotheses, with the finite verifier covering 750 tuples. They do not prove the full irrationality argument, the analytic approximation estimates, or that the cone hypotheses hold for every homogenized Pade family.

### three_halves_homogeneous_endpoint_obstruction

For any integral polynomial, homogeneous evaluation at (3,2) reduces modulo 3 to its constant coefficient times 2^W and modulo 2 to its top coefficient times 3^W. A unit constant or top coefficient therefore prevents the corresponding local divisor, and Lean exposes exact ZMod endpoint-jet interfaces for higher-power additive cancellation. The cyclotomic specialization is now explicit: homogeneous evaluations of cyclotomic polynomials at a reduced positive pair are coprime to the product of the two base coordinates.

Evidence/status: lean_checked_abstract_consumer


### four_jet_binary_pigeonhole_kernel

For any n integral coefficient pairs, the exact target of the two bottom 3-adic and two top 2-adic endpoint jets has cardinality (3^R)^2(2^S)^2. If R>0 and 4R+2S<=n, the 2^n binary selector space is therefore strictly larger, so two distinct subsets have the same four-jet signature. Their indicator-vector difference is nonzero with coefficients in {-1,0,1} and cancels all four endpoint jets. The rank threshold is sufficient rather than optimal, and the theorem does not prove that this vector avoids the polynomial-pair or analytic-remainder nullspace.

Evidence/status: lean_checked_abstract_kernel_existence

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The three named declarations prove the exact finite four-jet signature cardinality and the resulting binary-selector collision under the stated rank inequality, yielding a nonzero {-1,0,1} endpoint-jet annihilator. They do not prove the threshold is optimal, show the annihilator avoids the coefficient-pair or analytic-remainder nullspace, construct a full Padé/Zudilin method, or establish irrationality at 3/2.

### binary_row_collision_of_anchor_det_zero_consumer

For a finite family of pairs over a finite commutative ring, if an anchor pair has coprime coordinates and every row has zero determinant against that anchor, then a strict cardinality inequality between the ring and the Boolean selector space yields two distinct selectors with equal vector sums. The proof decomposes every row as a scalar multiple of the anchor and applies pigeonhole to the scalar sums.

Evidence/status: lean_checked_binary_collision_kernel_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on finite commutative-ring and finite-index instances, IsCoprime anchor coordinates, vanishing anchor minors, and the explicit cardinality inequality. It does not show that an actual q-Apery or Padé family supplies these hypotheses, identify a nonzero selector difference outside the polynomial-pair or analytic-remainder nullspace, control the real analytic remainder, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### anchor_det_zero_forces_all_det_zero_consumer

For a finite family of pairs over a commutative ring, if an anchor pair has coprime coordinates and every row has zero determinant against that anchor, then every pairwise minor in the family is zero. Each row is a scalar multiple of the anchor, so vanishing against one unimodular anchor propagates to the full determinantal family.

Evidence/status: lean_checked_anchor_minor_propagation_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on IsCoprime anchor coordinates and the explicit vanishing of every anchor minor. It does not show that an actual q-Apery or Padé family supplies such an anchor, produce the modular cardinality inequality for a selector collision, control the real analytic remainder, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### zmod_binary_row_collision_of_anchor_det_zero_consumer

Let N be nonzero, let a finite row family w map into (ZMod N)², and suppose the first coordinate a of an anchor row is a unit while every anchor minor a*(w i).2 - b*(w i).1 vanishes. If N < 2^(cardinality of the row index type), then two distinct Boolean selectors have equal row sums. Because the anchor makes every row pairwise collinear, the selector target has cardinality card (ZMod N), not card (ZMod N)², giving the endpoint-jet collision threshold used by the moving-tail route.

Evidence/status: lean_checked_anchor_determinant_collision_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on a nonzero modulus, finite decidable row indices, a unit anchor coordinate, vanishing anchor minors, and the explicit cardinality inequality. It does not prove that an actual q-Apery or Padé row family supplies such an anchor or vanishing minors, control the real analytic remainder of the resulting selector difference, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### three_halves_common_multiplier_endpoint_obstruction

If an integer common multiplier divides both homogeneous evaluations at (3,2), while the first polynomial has a unit top endpoint and the second has a unit constant endpoint, Lean proves that the multiplier is divisible by neither 2 nor 3. This is the exact conditional exclusion of common endpoint content needed before seeking determinant-specific local gain; it does not claim that every homogenized construction has these endpoint units or that the remaining determinant/analytic argument proves irrationality.

Evidence/status: lean_checked_abstract_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: This theorem rules out only a shared scalar factor supported at 2 or 3 under its explicit endpoint hypotheses. It does not establish those hypotheses for every #1049 Padé/Zudilin pair, control non-scalar recombinations, supply the analytic remainder estimate, or prove irrationality at base 3/2.

### general_homogeneous_endpoint_coprimality

For coprime natural coordinates a and b, a polynomial with unit constant and top coefficients has homogeneous evaluation at (a,b) coprime to the full product a*b. This general endpoint-coprimality interface subsumes the separate numerator and denominator exclusions and makes clear that any useful 2-adic or 3-adic gain in the reduced rational-base construction must be determinant-specific rather than inherited from a common endpoint factor.

Evidence/status: lean_checked_general_endpoint_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The result is conditional on coprime coordinates and both unit endpoint coefficients. It does not prove those endpoint hypotheses for every #1049 Padé/Zudilin row, control non-scalar recombinations or analytic remainders, or establish irrationality at base 3/2.

### homEval_isCoprime_left_endpoint_consumer

For coprime natural coordinates a and b, a unit constant coefficient makes the homogeneous evaluation homEval(a,b,W,P) coprime to the numerator coordinate a. This is the numerator-side consumer used by homEval_isCoprime_mul_of_endpoint_units and isolates the exact local endpoint condition needed before any determinant-specific gain can be claimed.

Evidence/status: lean_checked_numerator_endpoint_coprimality_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The result is conditional on a.Coprime b and P.coeff 0 being 1 or -1. It does not establish the endpoint hypothesis for a Padé/Zudilin construction, control the denominator endpoint or non-scalar recombinations, provide an analytic remainder estimate, or prove irrationality at base 3/2.

### homEval_isCoprime_right_endpoint_consumer

For coprime natural coordinates a and b, a unit top coefficient makes the homogeneous evaluation homEval(a,b,W,P) coprime to the denominator coordinate b. This is the denominator-side consumer used by homEval_isCoprime_mul_of_endpoint_units and isolates the exact local endpoint condition needed before any determinant-specific gain can be claimed.

Evidence/status: lean_checked_denominator_endpoint_coprimality_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The result is conditional on a.Coprime b and P.coeff W being 1 or -1. It does not establish the endpoint hypothesis for a Padé/Zudilin construction, control the numerator endpoint or non-scalar recombinations, provide an analytic remainder estimate, or prove irrationality at base 3/2.

### three_not_dvd_homEvalThreeTwo_const_endpoint_consumer

For every width W and integer polynomial P whose constant coefficient is 1 or -1, the homogeneous evaluation homEvalThreeTwo W P is not divisible by 3. The proof reduces modulo 3 to the unit endpoint coefficient times 2^W, so the obstruction is an exact local 3-adic consequence of the constant endpoint condition.

Evidence/status: lean_checked_three_adic_endpoint_obstruction_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The result is conditional on the declared constant coefficient being 1 or -1. It does not establish that endpoint condition for a Padé/Zudilin coefficient polynomial, control divisibility by 2 or higher 3-adic valuations, prove a determinant-specific gain, supply an analytic remainder estimate, or prove irrationality at base 3/2.

### two_not_dvd_homEvalThreeTwo_top_endpoint_consumer

For every width W and integer polynomial P whose coefficient at W is 1 or -1, the homogeneous evaluation homEvalThreeTwo W P is not divisible by 2. The proof reduces modulo 2 to the unit top endpoint coefficient times 3^W, so the obstruction is an exact local 2-adic consequence of the declared top endpoint condition.

Evidence/status: lean_checked_two_adic_endpoint_obstruction_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The result is conditional on the declared top coefficient being 1 or -1. It does not establish that endpoint condition for a Padé/Zudilin coefficient polynomial, control divisibility by 3 or higher 2-adic valuations, prove a determinant-specific gain, supply an analytic remainder estimate, or prove irrationality at base 3/2.

### not_two_dvd_both_homEval_of_left_top_unit_consumer

For any width W and integer polynomials U and V, if U has top coefficient 1 or -1, then the two homogeneous evaluations at (3,2) cannot both be divisible by 2. The result transfers the single-channel top-endpoint obstruction to a pair of coefficient channels by contradiction.

Evidence/status: lean_checked_two_adic_pair_obstruction_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The result is conditional on the left polynomial's declared top coefficient being 1 or -1. It does not establish that endpoint condition for an actual Padé or q-Apery pair, exclude common divisibility by 3, control higher 2-adic valuations or determinant-specific gain, supply an analytic remainder estimate, or prove irrationality at base 3/2.

### not_three_dvd_both_homEval_of_right_const_unit_consumer

For any width W and integer polynomials U and V, if V has constant coefficient 1 or -1, then the two homogeneous evaluations at (3,2) cannot both be divisible by 3. The result transfers the single-channel constant-endpoint obstruction to a pair of coefficient channels by contradiction.

Evidence/status: lean_checked_three_adic_pair_obstruction_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The result is conditional on the right polynomial's declared constant coefficient being 1 or -1. It does not establish that endpoint condition for an actual Padé or q-Apery pair, exclude common divisibility by 2, control higher 3-adic valuations or determinant-specific gain, supply an analytic remainder estimate, or prove irrationality at base 3/2.

### homEval_mod_left_endpoint_consumer

For natural a, b, and W and every integer polynomial P, homogeneous evaluation at (a,b) satisfies homEval(a,b,W,P) modulo a = P.coeff 0 * b^W. Thus reduction modulo the numerator coordinate retains exactly the constant endpoint coefficient, with no primality assumption on the modulus.

Evidence/status: lean_checked_modular_endpoint_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: This is an exact modular identity for the abstract homogeneous evaluation. It does not construct the #1049 Padé/Zudilin coefficient polynomials, establish endpoint-unit hypotheses for them, control non-scalar recombinations or analytic remainders, or prove irrationality at base 3/2.

### homEval_mod_right_endpoint_consumer

For natural a, b, and W and every integer polynomial P, homogeneous evaluation at (a,b) satisfies homEval(a,b,W,P) modulo b = P.coeff W * a^W. Thus reduction modulo the denominator coordinate retains exactly the declared top-width coefficient, with no primality assumption on the modulus.

Evidence/status: lean_checked_modular_endpoint_consumer

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: This is an exact modular identity for the abstract homogeneous evaluation. It does not construct the #1049 Padé/Zudilin coefficient polynomials, establish endpoint-unit hypotheses for them, control non-scalar recombinations or analytic remainders, or prove irrationality at base 3/2.

### zudilin_scalar_cone_margin_no_go

Lean proves that a lower irrationality-exponent bound 2<=mu and a source upper bound mu<=C1/C0 force 2C0<=C1, and that C0<=0 or 2C0<=C1 with C1>0 makes C0 log 3-C1 log 2 strictly negative. The primary paper supplies the cone and integer-base C0/C1 upper bound. The returned assertion that every actual homogenized U/V pair has the required unit endpoints at all scales remains unformalized, so the full cone-wide rational-specialization theorem is not claimed as kernel-checked.

Evidence/status: source_backed_parameter_input_with_lean_checked_implication

- [ZudilinConeArithmetic.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean)

claim_boundary: The two named declarations prove only the scalar implication from the displayed exponent assumptions and the resulting negative margin. They do not formalize the primary-paper cone input, unit-endpoint hypotheses for actual homogenized forms, or irrationality of the 3/2 Lambert value.

### three_two_scalar_margin_explicit

For real C₀,C₁ with 0<C₀ and 2C₀≤C₁, Lean proves the quantitative scalar-cone deficit C₀ log 3-C₁ log 2 < -(17/41) C₀ log 2. Thus the positive-C₀ scalar ray misses the required height side by a fixed relative margin, not merely by sign. The theorem consumes the previously formalized log(3)/log(2)<65/41 inequality and is the exact scalar implication used by the packet's three-halves cone obstruction.

Evidence/status: lean_checked_scalar_consumer

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: This is only the conditional scalar inequality. It does not prove that an arbitrary #1049 homogenized pair lies in this cone, establish the source-side irrationality-exponent bound or endpoint hypotheses, analyze non-scalar recombinations, or prove irrationality at base 3/2.

### qapery_remainder_versus_integerisation_at_three_halves

Two different quantities behave oppositely at 3/2, and conflating them was the standing publication risk. Using an exact rational bracket for F(3/2) = sum 2^k/(3^k - 2^k) accurate to 525 bits, the RAW RATIO ERROR F(3/2) - A_n/B_n shrinks at every checked n, with log magnitude -2.54, -8.85, -17.33, -27.96, -40.78, -55.84, -73.19 for n = 1..7, normalising to about -1.5 per n^2. The q-Apery approximants therefore do converge to F(3/2) at a rational base, and converge quickly. The CLEARED INTEGER LINEAR FORM rho_n = B_n F(3/2) - A_n, after the source's Lemma 1 clearing and primitive normalisation, instead shrinks only at n = 1 and grows for every n from 2 to 7, with log|rho_n|/n^2 running 0.29, 0.55, 0.59, 0.70, 0.65, 0.73 and trending upward. The clearing multiplier costs roughly 2.2 per n^2 and overwhelms the 1.5 per n^2 the approximation supplies. The licensed statement is that this rational-base integerisation fails to produce small linear forms; the statement that the approximants fail to approximate F(3/2) is false and is now measured to be false.

Evidence/status: exact_rational_bracket_over_displayed_range


### little_q_legendre_kernel_identity

The Amdeberhan-Zeilberger denominator is the x = p^(n+1) evaluation of Van Assche's little q-Legendre polynomial: b_n(p) = P_n(p^(n+1) | p^-1), where P_n(x|q) = sum_k [n,k]_p [n+k,k]_p p^(-kn+k(k-1)/2) (-x)^k with p = 1/q. Van Assche states this himself - 'which is nearly the b_n found in [WZ, p. 277] (their b_n corresponds to P_n(p^(n+1)|q))' - and it is verified symbolically here for 0<=n<=6. Van Assche's own construction instead uses the x = p^n evaluation, forced by his Markov-function identity for the finite Lambert prefix. The two classical families therefore share ONE bivariate Pade kernel and differ by which moving diagonal they evaluate it on.

Evidence/status: source_stated_and_symbolically_verified


### qapery_van_assche_diagonal_nonequivalence

Sharing the kernel does NOT mean sharing the recurrence. Writing A_n(p) = P_n(p^n | p^-1) for Van Assche's diagonal, exact computation gives A_0 = 1, A_1 = -p, A_2 = p(p^4+p^3+p^2-p-1), and applying the Amdeberhan-Zeilberger operator L = y_2 N^2 + y_1 N + y_0 at n = 0 leaves the residual -p(p-1)^2(p+1)(p^5+2p^4+2p^3+2p^2+2), which is strictly negative for every real p > 1 and in particular nonzero. The residual is also nonzero at n = 1 and n = 2, while a control confirms the operator does annihilate the Amdeberhan-Zeilberger sequence itself at those indices. One nonzero residual suffices: Van Assche's diagonal does not satisfy the q-Apery scalar recurrence, so no measurement made on the q-Apery diagonal transfers to it by the shared-kernel identity alone.

Evidence/status: lean_checked_at_n_zero_with_additional_exact_symbolic_replay


### van_assche_diagonal_endpoint_shape

The Van Assche diagonal has deg A_n = n(3n-1)/2 and factors as A_n = p * Ahat_n with Ahat_n(0) = -1 and leading coefficient (-1)^n, verified exactly for 1<=n<=6. Its constant term is therefore ZERO, not a unit. Consequently the homogeneous evaluation of A_n at (3,2) has v_3 = 1 and v_2 = 0 at every checked n: it is NOT coprime to 6, unlike the q-Apery denominator. This is an explicit disconfirming example against any blanket statement that every member of the classical family has unit endpoints in its natural denominator coordinate. The endpoints become units only after removing the monomial factor p, and that monomial is arithmetically visible at p = 3/2.

Evidence/status: exact_arithmetic_over_displayed_range


### qapery_targets_the_same_lambert_value

The Amdeberhan-Zeilberger q-Apery construction targets h_q(1) = sum_{k>=1} 1/(q^k - 1), which is exactly F(t) of Erdos #1049 at t = q. The q-WZ route is therefore a direct integer-base predecessor of the #1049 linear-form programme rather than an independent approximation direction. Its sections 1.1-1.5 are polynomial identities in q that hold verbatim at q = 3/2; only the analytic section 1.6 and the denominator clearing of section 1.7 and Lemma 1 are base-dependent.

Evidence/status: source_verified_relation


### qapery_adjacent_casoratian_closed_form

For the source sequences a_n, b_n and the adjacent Casoratian W_n = a_{n+1} b_n - a_n b_{n+1}, the second-order recurrence gives W_{n+1} = (y_0(n)/y_2(n)) W_n, and with the source initial data a_0 = 0, b_0 = 1, a_1 = -q(q+2)/(q-1) the product telescopes to the exact closed form W_n = -q^(n+1)(q^(n+1)+2)/(q^(n+1)-1). The raw q-Apery approximants are therefore non-proportional for every real q > 1, including q = 3/2, so adjacent-pair collapse is not the obstruction at the rational base. Verified symbolically for n<=4 against the paper's own defining sums.

Evidence/status: exact_symbolic_computation_pending_lean


### qapery_three_halves_casoratian_shear

At q = 3/2 the closed form becomes W_n = -3^(n+1)(3^(n+1)+2^(n+2)) / (2^(n+1)(3^(n+1)-2^(n+1))). Both 3^(n+1)+2^(n+2) and 3^(n+1)-2^(n+1) are coprime to 6, so the reduced Casoratian has the exact valuations v3(W_n) = n+1 and v2(W_n) = -(n+1). The intrinsic determinant moves linearly toward 3-divisibility while moving equally far away from 2-integrality: a one-sided local shear rather than simultaneous 2-adic and 3-adic gain.

Evidence/status: exact_arithmetic_over_displayed_range


### qapery_denominator_endpoint_units_at_three_halves

The q-Apery denominator polynomial b_n(q) = sum_{k<=n} (-1)^k q^(k(k+1)/2) [n+k,k]_q [n,k]_q has a uniquely top-degree k = n summand, hence degree exactly n(3n+1)/2, constant coefficient 1 and leading coefficient (-1)^n. By the packet's own homogeneous endpoint theorem its evaluation at (3,2) is then coprime to both 2 and 3. The q-Apery denominator channel therefore satisfies the unit-endpoint hypotheses of the existing common-divisor exclusion, so this family is already inside the recorded obstruction rather than outside it.

Evidence/status: exact_arithmetic_over_displayed_range


### qapery_cleared_determinant_carries_determinant_specific_local_content

Applying the source's own Lemma 1 clearing factor and specialising at (3,2), the reduced denominator is exactly 2^(deg z_n) and carries no factor 3, and the specialised row content is coprime to 6 at every checked n. After primitive normalisation the adjacent exterior determinant is nonzero for 0<=n<=7 with v3(Delta) = n+1 and v2(Delta) = 3n^2+3n+1 at every checked n. This is the first explicit instance in a literature-standard family of simultaneous 2-adic and 3-adic determinant content at base 3/2 that is genuinely determinant-specific rather than row content, which is exactly the mechanism the existing scalar-content and common-divisor exclusions leave undecided. It is still not enough. Measured in nats, the certified local divisor v2 log 2 + v3 log 3 runs 1.79, 7.05, 16.47, 30.04, 47.77, 69.67, 95.72 against determinant heights 3.74, 9.88, 23.45, 42.27, 67.74, 96.81, 132.35, so gain minus cost is negative at every checked n, at -1.95, -2.83, -6.98, -12.23, -19.96, -27.14, -36.63. Normalised by n^2 the deficit is -2.83, -1.75, -1.36, -1.25, -1.09, -1.02 and still moving; extrapolating v2 ~ 3n^2 against a fitted height of about 3.24 n^2 leaves a persistent deficit near 1.1 per n^2, so the local divisor covers roughly two thirds of the determinant height. This is a determinant-only proxy: it excludes the analytic remainder term of Problem 8.5, which must be measured separately.

Evidence/status: exact_arithmetic_over_displayed_range_conjectural_all_n_formulas


### qapery_prefix_plucker_depth_irreversible_cap

For the actual primitive q-Apery rows at 3/2, w_0=(0,-1), w_1=(42,11), and w_2=(-88014,-22585). Their first determinant is 42, so every expanding prefix containing w_0,w_1 has common Plucker depth v2<=1 and v3<=1. The gcd of all three pairwise minors of w_0,w_1,w_2 is exactly 6; because adding rows only adds minors to this gcd, every later natural-prefix determinantal divisor must divide 6. Hence the rapidly growing adjacent depths (reaching v2=127 and v3=7 at the seventh adjacent pair) can never become growing family-wide congruence compression on the natural expanding prefix. The exact receipt is state/formal_math/erdos257_period_noncollapse/erdos1049_primitive_plucker_receipt.json.

Evidence/status: exact_integer_certificate_with_irreversible_extension_consequence


### exists_binary_collision_of_card_lt_consumer

For finite types ι and α, any map from Boolean selectors on ι into α has two distinct selectors with the same image whenever card α is strictly smaller than 2^card ι. This is the exact finite pigeonhole consumer used to turn a bounded scalar image into a selector collision.

Evidence/status: lean_checked_binary_pigeonhole_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on finite selector and codomain types and the explicit cardinality inequality. It does not construct the relevant q-Apery or Padé selector map, prove that a modular tail has the required image bound, identify a selector difference outside the polynomial-pair or analytic-remainder nullspace, control the real analytic remainder, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### exists_scalar_eq_of_det_eq_zero_consumer

For a coprime anchor pair (a,b) in a commutative ring, any pair (x,y) whose exterior minor a*y-b*x vanishes is a scalar multiple of the anchor: there is c with x=c*a and y=c*b. The proof constructs c from a Bézout witness for the anchor.

Evidence/status: lean_checked_scalar_witness_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on the coprimality witness and the single determinant equation. It does not prove that a particular q-Apery or Padé anchor is coprime, establish source recurrence or modular unit hypotheses, propagate one determinant condition across a sequence, produce a selector collision or identify a selector difference outside the polynomial-pair or analytic-remainder nullspace, control the real analytic remainder, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### isCoprime_of_isUnit_left_consumer

In a commutative ring, if a is a unit then a and b are coprime for every b. The proof supplies the explicit Bézout witness obtained from the inverse of a, making a unit coordinate an admissible Plücker anchor.

Evidence/status: lean_checked_unit_coprimality_anchor_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on a commutative ring and IsUnit a. It does not prove that a particular q-Apery or Padé coordinate is a unit, establish the source recurrence or modular denominator-channel hypotheses, imply any determinant vanishing or selector collision, control the real analytic remainder, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### adjacent_det_zero_forces_all_det_zero_consumer

For a sequence of pairs in a commutative ring whose second coordinates are units, vanishing of every adjacent minor forces every pairwise minor to vanish. Algebraically, each next row is a scalar multiple of the preceding row, so induction places the full sequence on the first row's line.

Evidence/status: lean_checked_adjacent_to_tail_propagation_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on a commutative ring, unit second coordinates at every index, and all-index adjacent-minor vanishing. It does not prove that an actual q-Apery or Padé tail supplies those hypotheses at every start, establish the modular unit facts from the source recurrence, produce a selector collision or identify a selector difference outside the polynomial-pair or analytic-remainder nullspace, control the real analytic remainder, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### zmod_tail_pair_det_zero_of_adjacent_det_zero_consumer

For a nonzero modulus N, a sequence of modular row pairs whose second coordinates are units and whose adjacent minors vanish has every pairwise minor equal to zero. The theorem is the exact ZMod consumer obtained by propagating adjacent collinearity through the full tail.

Evidence/status: lean_checked_tail_pair_propagation_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on the nonzero modulus, unit second coordinates, and all-index adjacent-minor vanishing. It does not prove that an actual q-Apery or Padé tail supplies those hypotheses at every start, produce a selector collision or identify a selector difference outside the polynomial-pair or analytic-remainder nullspace, control the real analytic remainder, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### zmod_binary_tail_collision_of_adjacent_det_zero_consumer

For a nonzero modulus N, a sequence of modular row pairs whose second coordinates are units and whose adjacent minors vanish admits two distinct Boolean selectors with equal vector sums whenever N is smaller than 2^k. The proof propagates adjacent collinearity to the full tail, reduces the selector image to one ZMod coordinate, and applies the finite binary pigeonhole bound.

Evidence/status: lean_checked_adjacent_tail_collision_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on the nonzero modulus, unit second coordinates, all-index adjacent-minor vanishing, and the explicit N<2^k inequality. It does not prove that an actual q-Apery or Padé tail supplies those hypotheses at every start, identify a selector difference outside the polynomial-pair or analytic-remainder nullspace, control the real analytic remainder, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### zmod_binary_tail_collision_of_two_three_depth_consumer

For a nonzero modulus 2^S 3^R with R>0, a sequence of modular row pairs whose second coordinates are units and whose adjacent minors vanish admits two distinct Boolean selectors with equal vector sums whenever S+2R is at most the selector width. The proof propagates adjacent collinearity to the full tail, collapses the selector image to one ZMod coordinate, and uses 3^R<4^R to establish the stated threshold.

Evidence/status: lean_checked_two_three_depth_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: The result is conditional on the nonzero modulus, unit second coordinates, all-index adjacent-minor vanishing, positive R, and the explicit width inequality. It does not prove that an actual q-Apery or Padé tail supplies those hypotheses at every start, identify a selector difference outside the polynomial-pair or analytic-remainder nullspace, control the real analytic remainder, establish an all-start quantitative construction, or prove irrationality at base 3/2.

### isCoprime_of_isUnit_right_consumer

In any commutative ring, if the second coordinate b of a pair (a,b) is a unit, then a and b are coprime. The theorem supplies the exact Bézout--Plücker anchor used to turn a determinant-zero relation into a scalar-multiple relation.

Evidence/status: lean_checked_unit_right_coprime_consumer

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: This is only a commutative-ring coprimality interface. It does not prove that an actual q-Apéry or Padé tail has unit second coordinates, establish adjacent-minor vanishing, propagate a tail, produce a selector collision, control the analytic remainder, or prove irrationality at base 3/2.

### qapery_moving_tail_plucker_opening

Deleting the early q-Apery anchors changes the mechanism rather than merely the horizon. The source Casoratian, exact denominator degree d_n=n(3n+1)/2, clearing-factor endpoint units, and primitive denominator-channel units give the all-index adjacent depths v2=3n^2+3n+1 and v3=n+1 after cancellation of the clearing degrees. Fixing s and reducing modulo M_s=2^(3s^2+3s+1)3^(s+1), every later adjacent minor vanishes and every denominator coordinate is a unit. Lean proves that this forces every pairwise tail minor to vanish and that width 3s^2+5s+3 already produces a nontrivial binary selector collision. Hence every finite window beginning at s has exact local determinantal depths (3s^2+3s+1,s+1), while the natural prefix remains capped by 6. This decisively opens arbitrarily wide non-prefix modular compression. The later qapery_selector_remainder_nullspace_escape certificate closes the finite structural nullspace ambiguity at starts 0,1,2,3,4; all-start quantitative control and irrationality at 3/2 remain unproved. The exact finite replay is state/formal_math/erdos257_period_noncollapse/erdos1049_primitive_plucker_receipt.json.

Evidence/status: exact_finite_family_wide_opening_with_lean_checked_propagation_interface

- [BezoutPluckerJets.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/BezoutPluckerJets.lean)

claim_boundary: This is a finite source-family and modular-algebra opening, not the irrationality proof. It is conditional on the recorded q-Apéry Casoratian, clearing-unit, primitive-denominator, and all-index depth facts; it leaves all-start quantitative control, analytic remainder separation for every start, and irrationality at base 3/2 unresolved.

### qapery_selector_remainder_nullspace_escape

Exact source-recurrence materialization, modular collinearity reduction, LLL selector recovery, and a rational bracket for F(3/2) produce moving-tail collisions at s=0,1,2,3 outside both nullspaces. At s=3 a support-12 signed selector has both integer coordinates divisible by 2^37*3^4, is not the zero coefficient pair, and has strictly positive analytic remainder. The extension does not count as a new mathematical opening merely for adding one finite start; it durably removes a false-negative mode by recording the exact LLL strength and modular-coordinate weight required after the default reduction failed. Thus the moving-tail congruence kernel is not structurally swallowed by either nullspace. What remains is an all-start quantitative theorem controlling selector support/height and real remainder; no irrationality conclusion is claimed. The durable receipt is state/formal_math/erdos257_period_noncollapse/erdos1049_qapery_selector_remainder_escape_receipt.json.

Evidence/status: exact_finite_mechanism_opening


### qapery_two_selector_exact_remainder_escape

At every certified moving-tail start s=0,1,2,3,4, two binary selectors have combined primitive coefficient pairs with nonzero exact determinant. Therefore their analytic remainders cannot vanish simultaneously for any real value. At s=4 the prior exact SymPy LLL basis exposed no cap-one vector, but fpylll BKZ-16 exposes six; the stored support-24 and support-28 pair independently replays to zero in both channels modulo 2^61*3^5. This eliminates the only observed separation between rank-two image supply and the binary-short search and makes backend-relative exposure plus exact replay part of the computational contract. The finite computation does not prove the all-start supply theorem, quantitative height control, or irrationality. Receipt: state/formal_math/erdos257_period_noncollapse/erdos1049_qapery_two_selector_escape_receipt.json.

Evidence/status: exact_finite_rank_two_mechanism_opening_with_lean_checked_consumer


### qapery_stored_selector_normalized_remainder_no_go

For a selector pair (A,B) divisible by its certified modulus M, write (A,B)=M(A',B'). If F=a/q were rational, q(B'F-A') would be an integer; noncollinearity ensures at least one of two normalized forms is nonzero, so both forms must tend to zero for an irrationality contradiction. Exact 30000-bit rational brackets show that both stored normalized selector remainders exceed one in absolute value at every start s=1,2,3,4. Their logarithmic lower bounds grow from about 64 at s=1 to more than 2600 at s=4. Thus the stored modular-only LLL/BKZ selector pairs cannot feed the rationality consumer. A surviving congruence construction must include normalized real remainder in the lattice objective itself.

Evidence/status: exact_consumer_level_mechanism_elimination


### qapery_joint_local_real_unimodular_opening

The analytic coordinate repairs the stored-selector consumer at every tested start s=0,1,2,3. Adjacent continued-fraction convergents to the ratio of the two normalized real forms give two new exact forms whose complete rational brackets exclude zero and lie strictly inside (-1,1). The adjacent coefficient matrices have determinant plus or minus one, so the magnitude of the exact normalized selector determinant is preserved. At s=3 the certified pair occurs at convergent indices 1104 and 1105 with coefficient bit lengths up to 2261. This is a genuine finite repair of the modular-only objective. The later qapery_unimodular_height_decay_obstruction shows that its generic continued-fraction extrapolation is not an independent irrationality mechanism.

Evidence/status: exact_finite_consumer_repair_with_rank_preservation


### qapery_unimodular_height_decay_obstruction

For normalized input rows with determinant Delta and denominator-coordinate height S=|B_0|+|B_1|, every unimodular recombination of coefficient height H whose two remainders are at most epsilon satisfies |Delta| <= 2 H epsilon S. Exact replay of the four existing starts, with no horizon extension, gives determinant-forced coefficient-height lower bounds with floor base-two logarithms 0,52,293,1873, versus observed heights 2,92,710,2260. Thus most of the 2261-bit start-3 cost is structural. More decisively, at a rational target F=a/q every nonzero integral remainder has size at least 1/q, while non-collinearity guarantees one of two remainders is nonzero. Lean therefore proves that two non-collinear integral forms cannot both tend to zero at a rational target. Generic continued-fraction optimization of the exact real-form ratio is not an independent route: proving its cofinal decay already proves irrationality. Any survivor must derive the recombinations, height upper bound, and decay from source-specific q-Apery structure without assuming an infinite continued fraction for that ratio.

Evidence/status: all_start_source_independent_no_go_with_lean_checked_height_and_rational_gaps


### qapery_tail_denominator_prime_support

For primitive q-Apery rows through index 255, the finite-tail denominator-coordinate gcd first becomes 211 at start five and subsequently acquires only factors supported by 3^s-2^s at their checked threshold. At every start through 15 this gcd equals the anchor Plucker gcd after division by M_s, although the full two-coordinate tail lattice remains primitive. Exact loss blocks for 5,7,13,19,23,29,97 show that fixed-prime infinite-tail persistence is the wrong extrapolation. Lean instead exposes the two consumers that a cofinal moving-window theorem would need: a common denominator divisor reduces the binary pigeonhole to one coordinate, and a prime occurring once in the exterior determinant forces one of two forms at a/q to have absolute value at least 1/q. The source-current consumer also accepts a retained prime-power tail hypothesis ell^r ∣ B, reducing it to the one-copy prime-support condition without changing the nonvanishing boundary.

Evidence/status: exact_finite_source_arithmetic_with_lean_checked_rational_gap_consumer

- [QAperyTailDenominator.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/QAperyTailDenominator.lean)

claim_boundary: The prime-power theorem is conditional on the explicit prime-power support, numerator nondivisibility, and denominator nondivisibility premises; it does not supply a cofinal moving-window theorem or close irrationality.

### fixed_diagonal_rational_clearing_obstruction

For every scalar evaluation exponent m>=n, Van Assche's little-q-Legendre coefficient P_n(p^m|p^-1) has degree n*m+n(n-1)/2 and unit leading coefficient. The target tail forces cyclotomic cutoff M=max(n,m-1)=m+O(1); multiplying by d_M preserves the unit endpoint, so at p=3/2 the P-coefficient has exact denominator 2^(D+E), with no hidden power-of-two cancellation. Composing that forced homogeneous cost with Van Assche's positive Markov-error bounds gives main term (n*m+n^2/2)log(4/3)+(3/pi^2)m^2 log 3>0, with only o(n^2)+o(m^2)+O(m+n) omitted. The adjacent second-kind identity Q_n P_(n-1)-P_n Q_(n-1)=-(p^n+1)/(p^n-1) further proves that the part of the primitive common content coprime to the clearing value divides 3^n+2^n. Exact counterexamples exclude the shortcut that all remaining content primes have order <=2n. Thus changing the outward evaluation alone cannot repair height; only clearing-supported cyclotomic-local multiplicities remain as a scalar escape.

Evidence/status: strengthened_to_all_outward_forced_clearing_with_coprime_content_divisor_reduction


### fixed_diagonal_resultant_content_reduction

On the original diagonal m=n, any odd common divisor of the two d_n-cleared homogeneous coefficient values divides Res_p(A_n,C_n). The cyclotomic part has an authored all-index local product law: for n=ar+b, C_n=(-1)^a(d_n/(p^r-1))P_b(p^b)K_(a,b) modulo Phi_r, with K_(a,b)=3H_a for b>0 and 3H_a-1/a for b=0. Q-Lucas factorizes each surviving coefficient into a classical block coefficient and the smaller diagonal P_b; a differentiated Chu-Vandermonde identity supplies the harmonic scalar. Direct replay covers every 1<=r<=n<=7. The exact product law then evaluates the clearing resultant without constructing C_n and first crosses the analytic budget at n=15: rate 0.776255453400277 versus 0.765461201033283. This occurs before the separate P-Q factor. Therefore the full resultant is too large to be a subcritical upper bound on content. The all-index local law remains an arithmetic map, but any scalar continuation must prove specialization-selective gcd bounds strictly below the resultant; otherwise the coupled selector architecture is required.

Evidence/status: authored_all_index_local_product_law_closing_full_resultant_height_route


### zudilin_normalized_hankel_qorder_factorial_pattern

For every rank N, Zudilin's normalized Hankel determinant V_N^* at x=z=1 has q-order exactly N(N-1)(2N-1)/6 and leading coefficient exactly (N!)^2(N+1)!/2^N. The source backward-shift induction sharpens on the associated grade: for w_n(H,t), the leading coefficient after j transforms is (-1)^j[X^(j-t)]H_0(X)^(-1). The actual t=0 tail has reciprocal (1+X)/(1-X)^4, every t>=1 tail has reciprocal 1/(1-X)^3, and summing 0<=t<=j gives D_j v_(j+l)^*=(-1)^j(j+1)^2(j+2)/2 q^(j(j+1)/2+jl)+higher terms. Lean now defines both actual associated tail ratios and reciprocals, proves their coefficient formulas, specializes the all-depth recurrence, and proves the exact zero-plus-positive tail row scalar. It also defines each exact normalized source tail and the coefficientwise finite-tail moment at x=z=1, proves that the tail has exact order (n+1)t, zero coefficients below that shift, and leading coefficient one, proves the exact consecutive-index source-tail identity T_(n+1,t)=X^t T_(n,t)U_(n,t), clears both moving denominator factors of U_(n,t), proves U_(n,t)-1 vanishes below degree n+1, and proves its first associated coefficient is -5 at t=0 and -3 at every t>0. Lean further proves the exact Gaussian-binomial operator recurrence D_(j+1)=(1-X^jN)D_j on arbitrary power-series sequences and the resulting transformed-moment recurrence. This closes the first nontrivial transformed row in every column: ord(D_1v_(l+1)^*)=l+1 with leading coefficient -6. Lean also proves the lower-unitriangular row matrix has determinant one and preserves every power-series Hankel determinant, proves a generic unique-minimum Leibniz-order bridge, then identifies the associated-grade matrix as a diagonal scaling of a power-series Vandermonde matrix, proves its exact determinant product and all-rank noncancellation, computes its exact order as sum_(j<N)j^2, closes 6*ord=N(N-1)(2N-1), and checks the exact scaled factorial product for the row coefficients; the focused AdelicHeightBridge build and final serialized replay pass. The sole remaining Lean boundary is the entrywise initial-monomial theorem for rows j>=2 and all columns, iterating these exact filtered step identities. Thus hidden normalized-Hankel q-order is eliminated at all ranks as a source of extra cubic analytic decay; arithmetic denominator extraction or a different integral model is now mandatory. The finite checker regression-tests every tail contribution through rank seven. Receipt: state/formal_math/erdos257_period_noncollapse/erdos1049_hankel_qorder_receipt.json.

Evidence/status: all_rank_source_proof_with_lean_checked_exact_source_tails_associated_reciprocals_filtered_source_operator_recurrence_complete_all_column_first_transformed_row_backward_shift_determinant_associated_grade_order_and_factorial_assembly

- [FilteredReciprocalStateLifting.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/FilteredReciprocalStateLifting.md)

### zudilin_specialized_scalar_content_factor_and_charge_ceiling

At x=z=1, put P_n=prod_(j<=n)(p^j-1) and L_n=prod_(d<=n)Phi_d(p). Directly from Zudilin's displayed formulas, every cleared form v_n has common coefficient factor p^(n+1)P_n^3/L_n: the shared A/B summand is a product of two Gaussian binomials, while L_n clears every remaining p^ell-1 denominator in B and C. Cyclotomic floor superadditivity then gives H_i H_j | H_(i+j) for H_n=P_n^3/L_n, so (prod_(i<N)H_i)^2 divides V_N(mu;p,1,1) at every rank. Its exact degree is 2 sum_(i<N)(3i(i+1)/2-sum_(d<=i)phi(d)) and is at most N^3-N. Lean proves 41(N^3-N)<39(4N^3-3N^2), decisively eliminating scalar row-and-column content as enough to meet the explicit 3/2 Hankel threshold. Additional primitive residual-matrix divisibility is mandatory. Receipt: state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_scalar_content_receipt.json.

Evidence/status: all_rank_source_factor_with_lean_checked_insufficiency


### zudilin_primitive_residual_border_factor_and_charge_no_go

After extracting H_iH_j from the (i,j) Hankel entry, the residual Phi_d exponent for i,j>=d is exactly 1 or 4. The primitive residual determinant therefore contains product_(1<=d,2d<N) Phi_d(p)^(N-2d), but scalar plus border content remains strictly below the required charge. The valuation bound is exact: reverse the first 2d indices and pair the remaining residue multiset antitonically to exhibit a permutation term of total Phi_d-order N-2d. Thus no nested argument using only entrywise valuations can force more; only cancellation among minimum-order terms can. Exact rank four has p^30 Phi_1^2. At rank five, the mu=0 and mu=1 specializations have gcd p^55 Phi_1^3 Phi_2; the forced-factor/specialization sandwich proves exact non-p coefficient content and no extra primitive factor without full bivariate expansion. Receipt: state/formal_math/erdos257_period_noncollapse/erdos1049_zudilin_residual_border_charge_receipt.json.

Evidence/status: all_rank_source_factor_with_lean_checked_combined_insufficiency


### zudilin_all_d_first_appearance_noncancellation

For every cyclotomic index d, the normalized first d by d cross block at the first appearance of Phi_d is the wrapped Hankel matrix H_(i,j)=a_(i+j mod d) K^[i+j>=d]. Its determinant is, up to the explicit permutation sign, Res(W(x),Kx^d-1). At a prime above 2, write d=2^a m with m odd and e=2^(a-1). The exact coefficient valuations admit a supporting affine slope that makes the anti-diagonal the unique minimum; its normalized determinant valuation is exactly 3aed. For odd d the corresponding minimum has valuation zero. Therefore the full cyclotomic first-appearance associated-graded residue is nonzero for every d. This kills the expanding homogeneous boundary mode and the previously open cancellation among minimum-order first-appearance terms. It does not prove extra cumulative divisibility beyond the first appearance, the cubic charge needed by the height inequality, or irrationality at 3/2. The proof and checker are ZudilinFirstBlockResultantProof.md and scripts/check_zudilin_first_block_resultant.py at source commit 8e15c843431a793369baaaf758e165535b2e9c6e.

Evidence/status: authored_all_d_boundary_mode_elimination_with_exact_regression


### window_divisor_supply_and_first_appearance_law

The step-1 predicate named by QAperyTailDenominatorLab - supply, for cofinally many starts s, a moving divisor across the exact window of width 3s^2+5s+3 - had never been evaluated. Building the primitive q-Apery rows to index 677 (anchored against the prior lab's 211 | B_j for 5 <= j <= 255) and taking the gcd of the denominator coordinates across each exact window: only s = 0,1,2,4 give gcd 1, all of them the earliest starts, and EVERY start in the upper half of the tested range carries a divisor - which is where cofinality lives. The divisor set grows with s: 19 at s=3, 211 at s=5 and 6, 71*211 at s=7 and 8, 71*211*1009 at s=9 and 10, 71*211*331*1009 at s=11, 211*331*1009*29927 at s=13, and 211*331*463*1009*29927 at s=14. The source-support claim is made exact by testing FIRST APPEARANCE rather than inherited membership - a prime carried over from an earlier start is not expected to divide 3^s-2^s at the later one - and on that reading the law is perfect, seven out of seven: 19|19 at s=3, 211|211 at s=5, 71|2059 at s=7, 1009|19171 at s=9, 331|175099 at s=11, 29927|1586131 at s=13, 463|4766585 at s=14. So step 1 is not the weak link: the residual on this route is a proof of what the computation shows rather than another change of target, which is what the previous two rounds each produced. The proof obligation is now specific: show that for every large s the prime p_s dividing 3^s-2^s selected at first appearance has no loss block meeting [s, s+3s^2+5s+3]; since a loss block has length ord_p(3/2) and the window is quadratic, this compares a multiplicative order against a quadratic window, and unlike a fixed-tail divisor theorem it is not already refuted by its own data. Finite computation over s <= 14, bounded by exact rational arithmetic on rows near 10^6 bits; neither cofinality nor irrationality is proved and base 3/2 remains open.

Evidence/status: exact_finite_evaluation_of_the_named_step_one_predicate

- [erdos1049_window_divisor_supply.py](formal_math/probes/erdos1049_window_divisor_supply.py)

### fixed_prime_infinite_tail_closes_step_one

Under the all-level monodromy premise (M), Step 1 of three_halves_pade_height_gap needs no moving prime and no effective form of Boyd's conjecture. 5 divides B_j for EVERY j >= 50, so for every start s >= 50 the whole window [s, s+3s^2+5s+3] lies inside a fixed prime's tail and the window gcd is divisible by 5^(1+floor(log_5(s/2))). The chain is: (L1) the descent lemma v_p(H_n)>=1 and n>=p imply v_p(H_floor(n/p))>=1, proved in two lines by splitting H_n into multiples and non-multiples of p, so J_p is a tree under n -> floor(n/p) with children in [pn,pn+p-1]; (A) that tree is EMPTY at level three for p=5, hence J_5={4,20,24} is finite and complete, and likewise J_3={2,7,22}, J_13={12,156,168}; (M) the monodromy lemma R_(j+P_N) = -R_j mod 5^N with P_N=ord_(5^N)(3/2)=2*5^(N-1), certified at N=1,2,3 over every available index with zero violations and with its determinant half a corollary of the Casoratian closed form (C); (C5) 5-adic continuity of g_m = lam^m(lam^m+2)/(u_m R_(2m-1)R_(2m)) with lam=q^2=9/4, which follows from (M) because the two sign flips cancel in the product R_(2m-1)R_(2m); (B) hence sum_(m<=K) g_m/m - g_* H_K lies in 5 Z_5, so v_5(rho_j)=v_5(H_floor(j/2))-1 whenever floor(j/2) is not in J_5. Verified exactly to index 300: the set of j>=2 with 5 not dividing B_j is exactly {8,9,40,41,48,49}, the three blocks J_5 predicts, v_5(B_j)=1-v_5(H_floor(j/2)) at every index off those blocks, and v_5(R_j)=0 everywhere so the block theorem's standing unit hypothesis is true at 5. The same argument gives independent fixed tails at p=13 (j>=676), p=17 (j>=4624) and p=23 (j>=253, where eps=2 collapses the loss set to the single Wolstenholme block). This closes step 1; it bounds no height and supplies no decay, so #1049 at base 3/2 remains open. Proof: FixedPrimeInfiniteTailProof.md.

Evidence/status: conditional_chain_monodromy_premise_certified_only_to_level_three

- [erdos1049_fixed_prime_infinite_tail.py](formal_math/probes/erdos1049_fixed_prime_infinite_tail.py)

### rank_budget_law_for_rational_bases

Under the explicitly assumed generic type-I decay, homogenisation, clearing, integrality, and nonvanishing model, numerical admission requires t := log b/log a < (r-1-kappa)/r. The rank-two calibration kappa=2/pi^2 reproduces the recorded threshold, while kappa=0 is the rigorous optimistic ceiling at every rank; carrying the observed rank-two kappa to higher ranks is only a calibration scenario and supplies no lower bracket. At q=3/2, rank two fails even at zero clearing, rank three passes only if kappa_3<0.10721, and rank four passes the observed-rank-two-kappa budget with a 0.06841 margin. These are admission tests, not auxiliary-family constructions or irrationality proofs. The finite PVA raw-height scan is a warning rather than an estimate of kappa_3 because no degree normalization or clearing/homogenisation decomposition is proved. Zudilin's cubic Hankel route remains a separate fixed-ratio cost problem: cubic decay does not identify it with rank four. The probe validates the displayed algebra and finite calibrations; it does not prove any family-specific asymptotic rate, integrality, nonvanishing, or endpoint theorem.

Evidence/status: derived_budget_law_validated_against_the_recorded_rank_two_threshold

- [erdos1049_rank_budget_law.py](formal_math/probes/erdos1049_rank_budget_law.py)

### four_jet_power_certificate_compiler

For any certified power inequality 3^p<2^q, positive repetition depth T, and rank budget 2qT+2S<=n, Lean produces distinct binary selectors with identical four-jet signatures at bottom depth pT and top depth S. This is the general compiler that turns an integer power certificate into the improved finite selector threshold, of which the rank-41 instance is one specialization.

Evidence/status: lean_checked_general_power_certificate_consumer

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: This is only a finite pigeonhole consumer. It does not instantiate the analytic remainder map, prove a bounded remainder-fibre estimate, supply a cofinal selector family, or establish irrationality for the open three-halves problem.

### four_jet_rank_41_threshold_consumer

For positive repetition depth T and selector-side depth S, whenever 130*T+2*S≤n, Lean produces two distinct binary selectors with identical four-jet signatures at bottom depth 41*T. The threshold is obtained from the exact power certificate 3^41<2^65.

Evidence/status: lean_checked_rank_41_selector_threshold

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: Only the finite selector-pigeonhole specialization is formalized; it does not supply analytic remainder separation, a cofinal selector family, or irrationality of the open three-halves Lambert value.

### four_jet_rank_41_threshold_optimality

For every selector-side depth S, 2^(129+2S) is strictly smaller than the four-jet signature space at bottom depth R=41. Thus the power-certificate collision threshold 130T+2S is exact for the rank-41 specialization: the counting argument cannot fire one row earlier, while the certified 3^41<2^65 bound fires at 130T+2S. This is a formal optimality boundary for the finite binary four-jet kernel, not a cofinal selector theorem, a remainder-separation theorem, or an irrationality proof.

Evidence/status: lean_checked_exact_counting_boundary

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: The declaration proves only the finite cardinality threshold and its one-row optimality. It does not supply the bounded-fibre estimate needed to separate the analytic remainder, nor any cofinal construction or conclusion for the open 3/2 case.

### bounded_fibre_four_jet_collision_bridge

For finite selector domain α, jet-signature codomain β, and analytic-remainder codomain γ, if every fibre of the remainder map has at most k points and card β * k < card α, Lean proves that two distinct selectors share the same jet signature but have different remainder values. This is the exact abstract finite bridge needed to turn a bounded-remainder-fibre estimate into a jet collision outside the analytic nullspace.

Evidence/status: lean_checked_abstract_finite_consumer

- [AdelicHeightBridge.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/AdelicHeightBridge.lean)

claim_boundary: The declaration is only an abstract finite counting implication. It does not instantiate f as the four-jet map, prove any uniform remainder-fibre bound k, supply a cofinal selector family, or establish an irrationality conclusion for the open 3/2 problem.

### zudilin_hankel_coefficient_leibniz_bridge_and_unique_minimiser

The determinant-level half of the sharp normalized Hankel order is now unconditional. (i) A coefficient analogue of the landed order lemma: if every entry of a power-series matrix vanishes below its own order e(i,j) with leading coefficient a(i,j), and one permutation uniquely minimises the total order, then the determinant's coefficient at that total order is the signed product of the leading coefficients - with NO nonvanishing hypothesis on a, unlike the order analogue. (ii) With entry order j(j+1)/2 + j*l, the reversing permutation uniquely minimises, by the single algebraic identity sum_i (sigma(i) + i - (N-1))^2 = 2 sum_i sigma(i) i - 2 sum_i rev(i) i, so the excess over the reversal IS a sum of squares, positive exactly when sigma is not the reversal. No transposition induction is needed. (iii) sign(revPerm) = (-1)^C(N,2) on Fin N, which Mathlib does not provide, derived by reading one leading determinant coefficient two ways. (iv) Hence the associated-graded determinant's coefficient at sum_(j<N) j^2 is exactly prod_(j<N) (j+1)^2(j+2)/2 = (N!)^2 (N+1)!/2^N, sharpening the landed nonvanishing to an exact value. (v) The row operation is identified with the actual V_N^* = det(v_(i+j)^*), so the endpoint is about the source object, not a stand-in.

Evidence/status: lean_checked

- [ZudilinSharpHankelCoefficient.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean)

claim_boundary: The ENDPOINT REMAINS CONDITIONAL. zudilinSharpHankelOrderAndCoeff_of_rowInitialMonomial assumes ZudilinRowInitialMonomial j for every j - that row j of the backward-shifted grid has its predicted initial monomial. That hypothesis is proved only for j <= 2 (zudilinRowInitialMonomial_of_le_two); rows j >= 3 are open. The hypothesis is ROW level and the conclusion is DETERMINANT level, so this is not the target restated. Zudilin 2016 (Res. Number Theory 2, Art. 15, section 4) proves the lower bound ord >= N(N-1)(2N-1)/6; equality and the leading coefficient are the new content and remain conditional on the row hypothesis. CORRECTION TO THE INCOMING RETURN: its section 8 is largely ALREADY LANDED - det_zudilinAssociatedLeadingMatrix is the product formula, det_zudilinAssociatedLeadingMatrix_ne_zero is the all-rank nonsingularity, and zudilinAssociatedLeadingOrderNat_eq_sum_sq is the exponent identity; only the coefficient extraction was missing. Its section 4 also overstates the gap: the COMBINATORIAL half of the reciprocal-state lemma is already kernel-checked as hankelAssociatedCoeff_eq_reciprocal at all depths for arbitrary a; only the ANALYTIC half - that the power-series objects realise that recurrence - is missing.

### zudilin_row_two_initial_monomial

Row j=2 of the backward-shifted grid has its predicted initial monomial: D_2 v_(2+l)^* has order exactly 2l+3 with coefficient 18 = 3^2*4/2, and the per-tail boundary contributions are exactly t=0 -> 14, t=1 -> 3, t=2 -> 1, t>2 -> 0. This is the first row past the landed j=1 case and exercises the same mechanism: the tail state moves down by one per backward shift, so only t <= j returns to the boundary.

Evidence/status: lean_checked

- [ZudilinSharpHankelCoefficient.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/ZudilinSharpHankelCoefficient.lean)

claim_boundary: A single row, not the general lemma. The general-j reciprocal-state lifting was NOT landed: it needs a genuine substitution homomorphism into PowerSeries (PowerSeries Z) plus a D_j induction over the whole state family, and shipping it half-done would have meant a sorry. Rows j >= 3 are open, so the all-rank endpoint stays conditional.

## Known failed routes

The scalar q-Apery Pade family is QUANTITATIVELY DEAD at 3/2, by a fixed positive proportion at every index, and the shortfall now has a closed form: GAP(3/2) = 3 log 2 - (3/2 - 3/pi^2) log 3 = 0.765461 per j^2, which is 38.6% of the height. Three families are ruled out outright rather than merely unpromising. (1) Bounded-rank recombination cannot close it, because a fixed positive proportion of a QUADRATIC quantity is out of reach of any finite-rank operation on the rows. (2) Content extraction cannot close it: the content actually removed in passing from (L_j,R_j) to the primitive (A_j,B_j) is O(1), with maximum 59 observed across ten bases and all indices, so the rows are already primitive and there is no hidden common factor to find. (3) A single window prime cannot close it: a window divisor is worth log p = O(s), linear, against a Theta(j^2) deficit. This is the quantitative reason the window divisor of HarmonicZeroBlockLawLab.md is usable only for the nonvanishing 1/q step and never for height reduction, and it now holds at every index rather than being read off the first few starts. It is the asymptotic form of the packet's standing warning against reading the natural expanding prefix as evidence of asymptotic compression: the prefix is not merely uncompressed at start 3, its compression is O(1) forever. Any route that closes 3/2 must supply arithmetic cancellation of positive density in j^2.

The block law as HarmonicZeroBlockLawLab.md stated it is false in two places, both corrected by CasoratianBlockLawProof.md and both CONSERVATIVE for the window-divisor certificate. (1) The selecting condition is v_p(H_K) >= eps with eps = v_p(3^d - 2^d), not membership in the Eswarathasan-Levine set J_p = { K : v_p(H_K) >= 1 }. These coincide exactly when eps = 1 and differ once p^2 | 3^d - 2^d; p = 23 is live in range, with d = 11, 3^11 - 2^11 = 23^2 * 331 and eps = 2. Raising the bar makes loss blocks rarer, hence window divisors more abundant. (2) Loss blocks are NOT wholly lost. The block-structure theorem assumes R_j is a p-adic unit, and R_j mod p is d-periodic with a nonempty zero set for 44 of the 122 primes below 700 (p = 11 at j == 1 mod 10; p = 137 at j == 7,43,105,118 mod 136). At such an index inside a loss block the telescoped increment picks up an extra pole and p | B_j after all. Exact rational witness: H_3 = 11/6 puts 3 in J_11 so [30,39] is recorded as a whole loss block, yet 11 | B_31. Since the R-zero set is a union of residue classes mod d and is a proper subset -- p cannot divide every R_j without the primitive vector failing to be primitive -- no loss block is ever covered entirely, so the window-divisor criterion and the 252-of-259 certified starts are unaffected. This is falsifier 6 of the probe and passes on all 122 primes.

The raw expanding q-Apery prefix at 3/2 misses by a QUADRATIC margin, measured: log|B_j| ~ 1.96 j^2 while log|B_j rho_infty - A_j| ~ +0.76 j^2, so the primitive integer forms diverge rather than decay. The closed-form Casoratian localises the cause exactly: the rational remainder R_j rho_infty - L_j = -R_j sum_(i>=j) W_i/(R_iR_(i+1)) is approximately W_j/R_(j+1), and |W_j| ~ (3/2)^(j+1) is only linear in the exponent while log|R_j| is quadratic, so the rational forms decay superbly and the entire deficit is the content cleared in passing to (A_j,B_j). A single window prime is worth log p = O(s) against a Theta(j^2) deficit, so the window divisor cannot serve as a height-reduction device and is only usable for the nonvanishing 1/q step. This quantifies the packet's standing warning against reading the natural expanding prefix as evidence of asymptotic compression.

The step-1 residual as WindowDivisorSupplyLab.md stated it is false. That lab required the first-appearance prime p_s | 3^s - 2^s to have no loss block meeting [s, s + 3s^2 + 5s + 3]. Under the identified block law (loss blocks are indexed by the Eswarathasan-Levine harmonic zeros J_p = { K : p | numerator(H_K) }) it fails at s = 2,4,6,8,10,12,18. Two distinct failure modes: for s = 2,4,6 the primitive prime satisfies p <= 3s+7, so the Wolstenholme block K = p-1 lands inside the window; for s = 8,10,12,18 the primitive primes 97, 11, 61, 577 are large but carry sporadic harmonic zeros at K = 11, 3, 10, 24. The earlier lab's seven-out-of-seven first-appearance table listed only the starts where a new prime entered the window gcd (3,5,7,9,11,13,14), so it could not see that at s = 6,8,10,12 the window divisor is inherited (211, entering at s=5) rather than source-supported. Its separate finding that only s = 0,1,2,4 have window gcd 1 is reproduced exactly by two independent methods and is unaffected.

The analytic-aware continued-fraction repair is finite and exact, but its generic all-start extrapolation is not an independent irrationality engine. Unimodularity preserves the row determinant, forcing |Delta| <= 2 H epsilon (|B_0|+|B_1|); at start 3 this already forces at least 1874 coefficient bits for the certified common ceiling. At a rational target a/q, non-collinearity forces one remainder to have size at least 1/q, so cofinal two-form decay itself entails irrationality. A surviving q-Apery route must produce source-specific recombinations and decay without assuming that the exact form ratio has an infinite continued fraction.

The integer-base proof cannot be transferred by clearing every coordinate independently at 3/2.

The positive result at 7/2 does not settle 3/2 or every rational base.

A reconstructed Pade identity is not an irrationality measure until the analytic error and denominator height are closed.

Rectangular two-function Hermite-Pade optimisation does not improve the classical threshold, and the available large 3-adic factor at 3/2 is one-sided rather than a common divisor of the rationality-forced integer form.

The adjacent exterior product repairs the common-local-divisor defect but still has a positive normalized Archimedean exponent of approximately 110.850 n^2.

Exterior products among the returned Zudilin permutation-orbit forms vanish because those forms are proportional over the base field; they do not provide independent approximation directions.

The returned unsaturated contiguous a0-shift Hankel ranks r<=13n+1 remain below the claimed local-versus-height threshold even under overgenerous common-divisor allowances.

Pure scalar parameter optimization cannot make the 3/2 product-formula margin positive once the source integer-base inequality 2C0<=C1 is admitted. Multiplicative q-factorial and cyclotomic factors are units at the primes 2 and 3 after homogeneous specialization; they cannot by themselves create the missing common local content.

Rowwise Pade content cannot supply the missing local gain: it factors exactly from both the error and the exterior determinant, contributes the same product to the absolute determinant height, and under the checked unit-endpoint hypotheses contains neither a factor 2 nor a factor 3 at homogeneous base (3,2).

The explicit base 3/2 lies outside both published height regions recorded in this packet: Lean checks the exact obstruction 3^81<2^200 and derives 81/200<log(2)/log(3), while the Bundschuh-Vaananen threshold is weaker. These exclusions do not decide the irrationality problem.

The cited Soundararajan paper arXiv:1901.05133 concerns integral factorial ratios and does not substantiate the return's q-Pochhammer valuation claim.

Adjacent-pair collapse is not the obstruction for the q-Apery family at 3/2: the exact Casoratian is nonzero for every real q > 1, so proposals to 'avoid collapse' by leaving that family are answering a question that does not arise there.

The q-Apery denominator channel cannot supply the missing local gain by row arithmetic. Its specialised rows are coprime to 6, its Lemma 1 clearing factor contributes only powers of 2 and never a factor 3 at base 3/2, and its unit endpoints place it squarely inside the recorded common-divisor exclusion.

Determinant-specific local content at 3/2 exists and is still not enough on the evidence so far. The cleared adjacent q-Apery determinant carries v3 = n+1 and v2 = 3n^2+3n+1 that are provably not row content, yet the Archimedean height grows faster over the checked range, leaving a positive normalised margin. Exhibiting determinant-specific arithmetic is therefore necessary but demonstrably not sufficient.

Growing adjacent q-Apery determinant valuations cannot be promoted to growing family-wide congruence compression on the natural prefix. The first determinant 42 already caps every future prefix at v2,v3<=1, and the first three rows have determinantal divisor 6, so every later prefix divisor must divide 6 regardless of all later adjacent valuations.

The stored moving-tail LLL/BKZ selector pairs cannot be reused unchanged as an analytic irrationality consumer. After exact division by their certified modulus, both noncollinear normalized forms exceed one in absolute value at every start s=1,2,3,4, with logarithmic lower bounds growing into the thousands. Modular collision, coefficient cap and nonvanishing do not control the required normalized real remainder; that coordinate must enter the construction objective.

A hand transcription of a font-broken primary source is not a safe input to a downstream computation. The local transcription of the q-Apery section 1.5 recurrence carried two independent errors that the authors' own LaTeX source does not have, and only symbolic replay of the recurrence distinguished them.

SUPERSEDED 2026-08-11 by the diagonal non-equivalence result below, and retained as the record of a wrong working hypothesis: 'q-WZ, little q-Legendre Pade and Borwein must be treated as candidate coordinate systems on one tightly coupled approximant module until exact equivalences, shifts and normalisations are proved.' The hedge was right but the null hypothesis was wrong. They are pullbacks of one kernel along different diagonals, which is a strictly weaker relation than one module.

The q-Apery measurements do NOT transfer to the other classical families. Van Assche's x = p^n diagonal fails the Amdeberhan-Zeilberger recurrence outright, so the exact Casoratian, the v_2 = 3n^2+3n+1 and v_3 = n+1 determinant valuations, the local-to-height deficit, the 19n^2/8 clearing exponent, and any primitive row-content calculation are all q-Apery-diagonal-specific until separately proved for each family. Pullback along a different moving diagonal does not preserve the minimal scalar recurrence, the integral lattice, or the local valuation balance.

The claim that every classical family member has unit endpoints after homogeneous rational specialisation is FALSE as stated. Van Assche's natural denominator P_n(p^n | p^-1) has zero constant term and carries a monomial factor p, giving v_3 = 1 rather than coprimality to 6 at (3,2). Any class-wide endpoint theorem must state its normalisation hypothesis explicitly. For Borwein's evaluation P_{n-1}(c p^(n+1) | p^-1) the top endpoint carries a power of c and is a unit only when c = +-1, so a class-wide statement must also state its parameter hypothesis.

81/200 is not a published theorem and must never be attributed to Zudilin. Zudilin 2004 proves an integer-base irrationality-exponent bound on a parameter cone and states no rational-base height theorem. The strongest directly published rational-base criterion located is Bundschuh-Vaananen at log(b)/log(a) < 1/2 - 1/pi^2 = 0.398678816..., which does cover non-integer rational bases. This packet previously wrote 'the source-backed Zudilin threshold 81/200' in two places; both are corrected. The public problem note was already worded correctly and needed no change.

A growing cleared integer form is not the same statement as divergent rational approximants. If C_n is a clearing multiplier, C_n(b_n F - a_n) can grow while F - a_n/b_n still tends to zero, because C_n b_n may outgrow the raw approximation error. Any measurement showing the cleared rational-base forms grow at 3/2 licenses only 'the selected rational-base integerisation fails to produce small linear forms', never 'the q-Apery approximants do not approximate F(3/2)'.

The earlier reported figure that the cleared q-Apery forms at 3/2 have log|rho_n|/n^2 near +1.51 at n = 12 falling toward +1.393 is NOT reproduced by our own measurement, which finds the ratio rising through 0.29, 0.55, 0.59, 0.70, 0.65, 0.73 for n = 2..7 on primitively normalised rows. Both agree the cleared forms grow; the trajectories differ and are probably measuring different normalisations, since the earlier figure used 2^W scaling rather than primitive normalisation. Do not quote the +1.393 limit as ours.

Nested cyclotomic entry valuations cannot improve the Zudilin residual border charge. For every d with 2d<N, the universal southeast argument forces order N-2d and an explicit residue-antitone permutation attains exactly N-2d. Any deeper factor must be genuine cancellation among minimum-order determinant terms, not a stronger assignment bound. The rank-five specialization sandwich additionally shows no extra primitive non-p coefficient content at the next discriminating rank.

Changing Van Assche's scalar little-q-Legendre evaluation to any outward exponent m>=n cannot by itself repair the rational-base height problem. The exact coefficient degree is n*m+n(n-1)/2, the target tail forces cyclotomic degree (3/pi^2)m^2+o(m^2), and the unavoidable homogeneous power-of-two denominator turns the source decay into the positive main term (n*m+n^2/2)log(4/3)+(3/pi^2)m^2 log 3. This covers fixed, linear, superlinear, and irregular outward offsets. The conclusion is pre-primitive: a common odd gcd of the two cleared coefficients can still divide the form. The exact adjacent second-kind determinant confines the part of this gcd coprime to the clearing value to a divisor of 3^n+2^n, so only clearing-supported prime powers can contribute quadratically. A stronger guess that their orders are <=2n is false, with exact witnesses reaching order 58 at n=8.

Hypothesis (H) of CasoratianBlockLawProof.md - c_K congruent to a fixed p-adic unit c modulo p^eps, independent of K - is FALSE at p=5. In the normalisation g_m = lam^m(lam^m+2)/(u_m R_(2m-1)R_(2m)), g_m mod 5 is the single value 2 but g_m mod 25 takes three values {2,7,17}, so (H) already fails at the second 5-adic digit, at the very prime the block-law probe certifies on. The derived conclusion survives: the telescoped sum needs only 5-adic CONTINUITY (C5), that g_m mod p^N depends only on m mod p^(N-1), equivalently that a unit g_* exists with v_p(g_(p^a t) - g_*) >= a+1 for all a and all t coprime to p. (C5) is strictly weaker, is true with g_* coherent across levels (2 mod 5, 17 mod 25, 17 mod 125, measured periods exactly 1,5,25), and is exactly sufficient because grouping m<=K by a=v_p(m) against H_K = sum_a p^-a sum_(p not dividing t <= K/p^a) 1/t makes every error term carry p^-a * p^(a+1) = p. Falsifier F7 of erdos1049_fixed_prime_infinite_tail.py pins the refutation so a later edit cannot silently reinstate (H). Separately, the recorded reading that Wolstenholme makes 'the refutation of fixed-prime infinite-tail persistence unconditional and classical' is a conflation of two tails: p-1 in J_p kills only the tail beginning at the first-appearance index j=d, never the tail beginning past the LAST loss block, which exists whenever J_p^(eps) is finite.

HOMOGENISATION CEILING: the content lane on the fixed diagonal cannot reach base 3/2, at any level of success. With rho_j = L_j/R_j, B_j = den(rho_j) and D_j = (3/2) j^2, the linear form decays iff log B_j < 2 D_j log(a/b), which at 3/2 is 1.21640 j^2. Three growth identities hold with ZERO drift under the exact second-difference estimator (agreement 3e-8, the float accuracy of the log routine on 10^5-bit integers): log num(R_j) = (3/2)log3 j^2, log den(R_j) = (3/2)log2 j^2, log|R_j| = (3/2)log(3/2) j^2. So den(R_j) is exactly the homogenisation power b^D_j. The measured content is ZERO: gcd(num R_j, num L_j) = 1 exactly at j = 40, 60, 80, 100, 120, and the whole cross content the primitive vector removes is the 2-power 1.04256 j^2 with odd remainder exactly 0.00000; B_j is coprime to 6 and log B_j = 1.98739 j^2 = (3/2)log3 + (3/pi^2)log3 with no cancellation. The Casoratian PROVES the bound: a prime p not dividing 6 that divides both numerators at j forces v_p(W_(j-1)) >= 1, and W_(j-1) = -3^j(3^j+2^(j+1))/(2^j(3^j-2^j)) forces p | 3^j+2^(j+1), so log gcd <= 2 j log 3 = O(j) = o(j^2). A gcd theorem can move the linear term and never the quadratic constant. Since B_j is a multiple of num(R_j)/gcd, decay requires D_j log a < 2 D_j (log a - log b) even with the clearing deleted entirely, i.e. a > b^2 -- and the degree exponent D_j CANCELS, so no diagonal, degree or growth rate moves the ceiling. At 3/2, a = 3 <= 4 = b^2 and the irreducible floor (3/2)log3 = 1.64792 j^2 already exceeds the 1.21640 j^2 budget on its own. Restoring the clearing C_j = (3/pi^2) j^2 log a reproduces the recorded threshold log b/log a < 1/2 - 1/pi^2 exactly, which DERIVES that law and identifies its 1/pi^2 as the cyclotomic term sum_(r<=n) phi(r) ~ 3n^2/pi^2; deleting the term moves the threshold to 1/2, the same statement as a > b^2. CONSEQUENCE FOR THE PORTFOLIO: producers outward_scalar_primitive_content_bound and the height half of three_halves_pade_height_gap are capped strictly below the target and cannot reach 3/2. Their maximum prize is the band b^2 < a with log b/log a >= 1/2 - 1/pi^2, smallest member 5/2, then 10/3, 11/3, 13/3, 14/3, 17/4 -- and whether 5/2 is open in the literature is a prior-art question to settle before spending on it. Reaching 3/2 requires imposing divisibility WHILE choosing the combination, i.e. producer congruence_constrained_adelic_hermite_pade, whose framing this result quantitatively vindicates: looking for content afterwards returns gcd = 1. Proof: HomogenisationCeilingProof.md; verifier formal_math/probes/erdos1049_homogenisation_ceiling.py; receipt state/formal_math/erdos257_period_noncollapse/erdos1049_homogenisation_ceiling_receipt.json.

## Open implications

### outward_scalar_primitive_content_bound

First prove or disprove the fixed-diagonal resultant height law. For m=n, let A_n,C_n in Z[p] be the two d_n-cleared coefficient polynomials. The exact homogeneous row content divides Res_p(A_n,C_n). The local endpoint formulas |Res(Phi_n,C_n)|=2^phi(n) and |Res(Phi_(n-1),C_n)|=3^phi(n-1) are now proved all-index. The first global product bound, cross-cyclotomic times prod_(r<=n)(floor(n/r)+1)^phi(r), is false at n=10 despite surviving n=9 narrowly. Derive the missing root-of-unity norm factor for r<=n-2 and prove that its aggregate constant plus the P-Q factor stays below (3/2)log(4/3)+(3/pi^2)log 3. Only after that fixed-diagonal theorem should the analysis return to arbitrary m>=n and the local law P_n C_r U_r^(-1) H_floor((m-1)/r). Do not assume v_ell(G)<=v_ell(D_M)+v_ell(3^n+2^n): (4,16,7) gives 2>1. Further computation must falsify a precise corrected factor, not extend the rank table alone.

Evidence/status: see the source; no formal status inferred


### three_halves_pade_height_gap

The fixed-prime route is conditional, not an unconditional closure of step 1. The finite harmonic descent gives J_5={4,20,24} by the two-line descent lemma plus an empty level-three check, with eps=v_5(3^2-2^2)=1 and loss blocks [8,9],[40,41],[48,49]. If the all-level q-Apery monodromy/continuity premise (M)/(C5) holds, the weighted transfer gives 5 | B_j for every j >= 50 and hence a window gcd divisible by 5^(1+floor(log_5(s/2))) for every start s >= 50. The premise is certified only at N<=3 and over the finite indices recorded in FixedPrimeInfiniteTailProof.md, so the available evidence does not prove an all-index q-Apery denominator tail or unconditionally close the window-divisor substep. No first-appearance prime, factoring of 3^s-2^s, or effective form of Boyd's heuristic is needed under that explicit conditional premise. Conditional fixed-tail data also exist at p=13 (j>=676), 17 (j>=4624) and 23 (j>=253). REMAINING: (a) feed only a proved or explicitly conditional window divisor into the Lean one-coordinate pigeonhole theorem - the 1/q-gap step wants a prime to the FIRST power in a two-row determinant, and v_5(B_j)=1 only when v_5(H_floor(j/2))=0, seen in range only at floor(j/2) in [100,104] and [120,124], so cofinality of the first-power condition is open and is a question about harmonic valuations, not about the recurrence; (b) derive recombination matrices, coefficient-height bounds and cofinal decay from q-Apery structure. The determinant inequality |Delta_s| <= 2 H_s epsilon_s (|B_(s,0)|+|B_(s,1)|) remains a mandatory falsifier, and the measured deficit log|B_j rho_inf - A_j| ~ +0.76 j^2 is untouched. Evidence: FixedPrimeInfiniteTailProof.md, CasoratianBlockLawProof.md Correction 3, formal_math/probes/erdos1049_fixed_prime_infinite_tail.py.

Evidence/status: see the source; no formal status inferred


### factor_extracted_hankel_against_explicit_thresholds

This remains the only supplied construction with cubic analytic decay, but four free-gain routes are now closed: hidden normalized q-order, scalar content, every determinant charge forced solely by residual entry valuations, and cancellation of the first-appearance minimum terms. The all-d wrapped-Hankel resultant proof shows that the first cyclotomic associated grade is nonzero for every d, killing the expanding homogeneous boundary mode outright. A surviving Hankel mechanism must therefore create cumulative charge strictly above first appearance: higher-valuation-layer cancellation of cubic density, a genuinely global norm or resultant factor not visible in the first block, or a different integral model. Further computation must decide one of those distinct mechanisms rather than extend ranks or revisit first-appearance assignments.

Evidence/status: see the source; no formal status inferred


### congruence_constrained_adelic_hermite_pade

The current architecture builds rows first and looks for divisibility afterwards, via gcds or four-jet collisions. Impose the 2-adic and 3-adic constraints WHILE choosing the combination instead: for a genuinely independent family of primitive rows, build the lattice whose constraints encode sum_j lambda_j R_j = 0 mod 2^S 3^R in both channels, with the real norm controlling coefficient height and analytic remainder. Smith normal form decides exact local feasibility; LLL or an adelic Siegel lemma searches for a short representative inside the congruence kernel. This is the arithmetic counterpart of the four-jet pigeonhole theorem, which guarantees a kernel but ignores both the norm and the analytic nullspace. Do not use the natural expanding q-Apery prefix as evidence for asymptotically compressed image size: its first three rows irreversibly cap the common Plucker divisor by 6. Falsifier: on a genuinely new noncollapsed deformation or non-prefix selection, compute the shortest primitive vector in each local kernel and reject the lane if every short vector lies in the polynomial-pair or remainder nullspace, if the full determinantal divisor stays bounded, or if the height exponent already exceeds the certified local gain.

Evidence/status: see the source; no formal status inferred


### nonrectangular_multiple_q_jacobi_systems

Postelmans-Van Assche build a COMMON denominator for two Markov functions via multiple little q-Jacobi polynomials, giving simultaneous approximations to zeta_q(1) and zeta_q(2) and proving linear independence of 1, zeta_q(1), zeta_q(2). That is type-II Hermite-Pade with genuinely higher rank, not another scalar evaluation of P_n, and it must not be closed by a scalar q-Apery measurement. This packet's rectangular two-function exponent no-go covers only that explicit rectangular shape; it does not cover nonrectangular multi-indices, varying evaluation diagonals, mixed type-I/type-II systems, congruence-constrained selection, or minors chosen for arithmetic rather than symmetry. Falsifier: over a grid of small (n,m), specialise the multiple polynomial and both numerators at 3/2, primitive-normalise the three-channel rows, and compute rank over Q, Smith normal forms mod 2^S and 3^R, principal and mixed minor valuations, and exact real remainders; reject a subfamily once its normalised local-to-height exponent is uniformly negative with no new minor direction.

Evidence/status: see the source; no formal status inferred


### published_height_region_formalisation

Verify the primary theorem precisely and formalise its elementary parameter inequalities without claiming the analytic theorem as Lean-proved.

Evidence/status: see the source; no formal status inferred


### zudilin_all_rank_sharp_q_order_and_coefficient

Verify and Lean-formalise the dogfood return's associated-graded claim that ord_q V_N^*=N(N-1)(2N-1)/6 and the leading coefficient is (N!)^2(N+1)!/2^N in every rank, using its determinant-preserving backward shifts and explicit initial-monomial matrix. Complete the currently unchecked row formula for j>=3 and consume it in factor_extracted_hankel_against_explicit_thresholds.

Evidence/status: see the source; no formal status inferred
