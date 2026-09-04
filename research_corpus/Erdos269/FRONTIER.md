# erdos_269 mathematical frontier

Generated from the exported research packet. Read the strongest applicable
result before attempting a proof; superseded results remain history.

Prove irrationality in the first unresolved support case with three distinct prime generators.

## Established results and their evidence

### running_lcm_height

For three pairwise-distinct primes and x>0, the literal Finset.lcm of the actual filtered smooth prefix equals the product of the three maximal pure prime powers; this height is at most x^3.

Evidence/status: lean_checked

- [ThreePrimeRunningLcm.lean](problem/ThreePrimeRunningLcm.lean)

claim_boundary: The named declarations prove the finite three-prime running-LCM identity and cubic upper bound under their explicit positivity and distinctness hypotheses. They do not prove the irrationality conclusion for Erdős #269, an unbounded residue escape, or a universal result beyond the stated three-prime height estimate.

### running_lcm_log_cell_constancy

For three pairwise-distinct primes and positive cutoffs, equality of the three natural-log coordinates forces equality of the literal smooth-prefix Finset.lcm; the associated rational lattice kernel is constant on the same cells.

Evidence/status: lean_checked

- [ThreePrimeRunningLcm.lean](problem/ThreePrimeRunningLcm.lean)

claim_boundary: This is a checked finite logarithmic-cell constancy result under the explicit prime and cutoff hypotheses. It does not order the infinite jump sequence, prove an irrationality conclusion, or supply an unbounded residue-escape theorem.

### kernel_not_rank_one

The {2,3,5} lattice kernel fails rank-one separation; the smallest 2x2 determinant is -1/15.

Evidence/status: lean_checked

- [ThreePrimeRunningLcm.lean](problem/ThreePrimeRunningLcm.lean)

### prime_power_jump_expansion

Every finite rectangular smooth-lattice sum groups exactly by its genuine running-LCM height, with coefficient equal to the corresponding height-fiber cardinality. Together with logarithmic-cell constancy, this is the finite core of the ordered prime-power-jump expansion; the infinite limit and explicit pure-power ordering remain to be formalized.

Evidence/status: lean_checked_finite_core

- [ThreePrimeRunningLcm.lean](problem/ThreePrimeRunningLcm.lean)

claim_boundary: This is a checked finite grouping identity for rectangular smooth-lattice sums. It does not justify passage to an infinite ordered expansion, establish pure-power ordering, or prove irrationality.

### single_coordinate_jump_ratio

For pairwise-distinct primes and positive cutoffs, advancing exactly one natural-log coordinate by one multiplies the literal smooth-prefix Finset.lcm by the corresponding base p, q, or r.

Evidence/status: lean_checked

- [ThreePrimeRunningLcm.lean](problem/ThreePrimeRunningLcm.lean)

claim_boundary: This is a checked one-coordinate finite transition law under the explicit positivity and distinctness hypotheses. It does not identify the globally ordered jump sequence or prove an irrationality conclusion.

### finite_pure_power_jump_enumeration

Positive power channels of distinct primes are disjoint; consequently, the union of the first n positive powers in each of three pairwise-distinct prime channels has exactly 3n elements.

Evidence/status: lean_checked

- [ThreePrimeRunningLcm.lean](problem/ThreePrimeRunningLcm.lean)

claim_boundary: This is an exact finite cardinality result for three distinct prime-power channels. It does not establish their order relative to one another in the infinite logarithmic sequence or prove irrationality.

### finite_jump_enumeration_with_origin

The common origin 1 lies in no positive prime-power channel, so adjoining it to the first n positive powers from three distinct prime channels gives exactly 3n+1 finite jump values.

Evidence/status: lean_checked

- [ThreePrimeRunningLcm.lean](problem/ThreePrimeRunningLcm.lean)

claim_boundary: This is an exact finite count after adjoining the origin to three positive prime-power channels. It does not prove a global jump enumeration, an infinite ordering statement, or irrationality.

### multiplicity_bound

For the actual filtered smooth exponent shell, fixing two coordinates is injective when the jump interval has multiplicative width at most the remaining base; if sorted heights sum to j, then 9 times the shell cardinality is at most (j+3)^2.

Evidence/status: lean_checked

- [ThreePrimeRunningLcm.lean](problem/ThreePrimeRunningLcm.lean)

claim_boundary: This is a checked finite shell multiplicity bound with its explicit interval and sorted-height hypotheses. It does not provide a sharp asymptotic, an infinite jump expansion, or an irrationality proof.

### actual_dyadic_block_radix_alphabet

Every interval (2^a,2^(a+1)) contains at most one pure power from each non-dyadic channel. Lean now identifies the four-symbol dyadicBlockBase235 with the exact successive ratio of both the computational threePrimeHeight and the literal smoothPrefixLcm along 2^a -> 2^(a+1). Consequently the actual compressed {2,3,5} dyadic radix lies in {2,6,10,30}, with no hidden larger base. The integer block digit and tail recurrence are not identified by this theorem.

Evidence/status: lean_checked

- [ThreePrimeRunningLcm.lean](problem/ThreePrimeRunningLcm.lean)

claim_boundary: The named declarations prove the exact successive-height ratio and the resulting four-symbol radix alphabet for the {2,3,5} dyadic block. They do not identify the integer block digit, prove the tail recurrence or escape dichotomy, or settle Erdős #269.

### actual_dyadic_radix_escape_fanin

Lean instantiates the bounded-radix dichotomy with the actual {2,3,5} dyadic height ratio. Every real affine orbit with integer digits and radix dyadicBlockBase235 either reaches an integer state or is cofinally at distance at least 1/31 from every integer. The generic theorem takes the digit sequence and recurrence as inputs; DyadicShellSummability now supplies both inputs for the genuine infinite source tail.

Evidence/status: lean_checked


### block_mass_combinatorial_engines

Lean checks the suffix-product telescope that expands each block height quotient and the exact Bellman fixed-point identity behind the quadratic state cap and its constant 27. These are the two algebraic engines used by the checker-level block-digit and state-cap derivations. They do not yet identify the actual integer block digit, derive its affine recurrence from the ordered {2,3,5} source, or prove Erdős #269.

Evidence/status: lean_checked_algebraic_engines


### dyadic_block_digit_half_height_mass

For every scale a and every actual {2,3,5}-smooth point in the half-open dyadic shell, Lean proves that the right-endpoint running height equals the point height times 2 and an odd suffix product. Lean now partitions that suffix at all scales by the unique new 3- and 5-power thresholds and sums it exactly as N+2*C3+4*C5+8*C35. Threshold order gives C35=C3 or C35=C5, hence the ordered source digit N+10*C3+4*C5 or N+2*C3+12*C5. This closes endpoint normalization, cell summation, and odd-jump ordering as analytic ambiguities. Independently, exact enumeration for 1<=a<=100 verifies sum_x H(2^(a+1))/H(x)=2*blockDigit(a), with 50,134 source values and zero failures; that finite horizon is not counted. Binding the ordered digit into the actual rationality carry recurrence remains open.

Evidence/status: lean_checked_all_scale_height_factorization_threshold_partition_and_ordered_digit


### finite_farey_certificate_235_M200

The M=200 finite box and cubic tail exclude every rational denominator below approximately 1.64e90, but do not exclude all denominators.

Evidence/status: independently_regenerated_exactly


### finite_denominator_exclusion

A separate exact truncation excludes rational denominators through 1,022,266.

Evidence/status: advisory_computation


### prime_channel_residue_escape_consumer

A positive tail state bounded by K cannot represent modulo C a canonical positive residue in (K,C]. Lean now checks both the original natural-state theorem and the integer-valued carry form, including positivity, the canonical interval 1,...,C, and congruence of the least-positive representative.

Evidence/status: lean_checked

- [ResidueEscape.lean](problem/ResidueEscape.lean)

### canonical_window_residue_equality

Any positive integral carry bounded by its positive modulus is exactly the least positive representative of its congruence class. Specializing the integral-carry window identity, Lean proves that the canonical residue of -B times the accumulated forcing modulo the absolute window base is exactly the endpoint carry whenever that carry lies in the canonical interval. This upgrades the local-window consumer from a contradiction inequality to an exact endpoint invariant.

Evidence/status: lean_checked

- [RestrictedFloorSum.lean](problem/RestrictedFloorSum.lean)

### fixed_window_residue_shortcut_counterexamples

Canonical window residues need not be coprime to the window base: (W,F,B)=(6,4,1) gives residue 2. Nor does a fixed window admit a denominator-independent positive lower bound: (60,47,37) and (3627970560000000,3526148954135949157,152854142178707) both give least positive residue 1. Therefore an escaping-window producer must genuinely choose its window in response to the reduced denominator.

Evidence/status: independently_regenerated_exact_arithmetic


### restricted_floor_sum_shell_formula

For positive bases, the strict three-prime smooth count is exactly a restricted two-dimensional sum of one-dimensional exponent fibers. At a pure p-power cutoff every fiber has the kernel-checked cardinality a - Nat.log p (q^j r^k), so Psi(p^a) = V_p(a); after a checked channel-swap bijection, every pure-power shell from p^a to q^b has exact multiplicity V_q(b) - V_p(a).

Evidence/status: lean_checked

- [RestrictedFloorSum.lean](problem/RestrictedFloorSum.lean)

### restricted_floor_sum_discrete_derivative

For bases p,q,r greater than one, V_p(a+1) - V_p(a) is exactly the cardinality W_p(a+1) of the admissible (q,r)-exponent pairs below p^(a+1). The proof kernel-checks the old-pair increment and new-pair Nat.log boundary separately.

Evidence/status: lean_checked

- [RestrictedFloorSum.lean](problem/RestrictedFloorSum.lean)

### pure_power_block_shadow_separation

True shell multiplicities satisfy exact pure-power block equations that every nontrivial upward rational shadow violates, furnishing a true-versus-shadow invariant absent from the earlier scalar recurrence.

Evidence/status: advisory_complete_derivation


### denominator_reduction_coprime_thirty

Every fixed {p,q,r}-smooth factor kernel-checkably divides the running three-prime height once the cutoff reaches it. If the integral carry states share that absorbed nonzero factor, Lean cancels it from the full recurrence, transfers positivity and the sharp upper bound through a positive factor, and derives the exact local-window identity with the reduced denominator. For {2,3,5}, the remaining denominator is the coprime-to-30 part.

Evidence/status: lean_checked_absorption_and_cancellation_core

- [RestrictedFloorSum.lean](problem/RestrictedFloorSum.lean)

### projective_two_window_residue_coherence

Two reduced endpoint carries from one rational candidate must satisfy d_a*H_b=d_b*H_a modulo the reduced denominator B. For B=11, exact actual windows ending at dyadic scales 4 and 7 have canonical carries 61 and 259, separately below bounds 150 and 398 and separately coprime to 11. Neither local size nor nonunit-residue consumer fires, but the height residues are 5 and 2 and the projective defect is 61*2-259*5=4 mod 11. Thus the pair is impossible. This opens cross-window projective incoherence as an independent denominator-elimination mechanism without supplying universal or cofinal quantifiers.

Evidence/status: lean_checked_consumer_with_exact_source_witness

- [check_erdos269_projective_window_pair.py](formal_math/erdos257_period_noncollapse/scripts/check_erdos269_projective_window_pair.py)

### projective_quotient_defect_factorization_and_small_band_no_go

Writing each canonical carry as d_i=k_i*M_i-B*F_i and endpoint height as H_i=S_i*M_i factors the projective cross-defect into M_1*M_2*(k_1*S_2-k_2*S_1) plus an exact multiple of B. The integer-only checker verifies this identity on every emitted pair. An exact B=7 pair has quotient defect 129120, centered residue -2 modulo 7, and original projective defect 1 modulo 7, falsifying the proposed quarter-modulus concentration while both carries satisfy the base-clear, short-bound, and denominator-coprimality gates. Thus quotient normalization remains the right computational observable, but a uniform small-centered-defect inequality is decisively unavailable. The bounded scan supplies no universal denominator or cofinal-window quantifier.

Evidence/status: lean_checked_factorization_with_exact_mechanism_counterexample

- [check_erdos269_projective_quotient_scan.py](formal_math/erdos257_period_noncollapse/scripts/check_erdos269_projective_quotient_scan.py)

### logarithmic_local_window_compression

The local forcing for any shell word of the form m_n = V_(n+1) - V_n kernel-checkably expands into the endpoint potential difference plus a recursively explicit weighted sum of the interior (b_n-1)V_n terms. Substitution into the integral-carry recurrence gives the exact division-free local-window numerator formula. The separate logarithmic window-length estimate and cofinal anti-concentration producer remain open.

Evidence/status: lean_checked_algebraic_core

- [RestrictedFloorSum.lean](problem/RestrictedFloorSum.lean)

### local_window_certificates_B_1_7_16

The durable integer-only checker reproduces the three reported local windows for B=1,7,16 exactly. A fresh bounded scan also found a consumer-firing window of length at most 14 for all 106,666 tested pairs with B<=1000 coprime to 30 and 100<=a<=500. Both statements are finite regression evidence, not cofinal escape.

Evidence/status: independently_regenerated_exactly


### weighted_affine_phase_carry_boundary

Beatty-weight exponents reindex exactly under every dn+s section; any supplied affine cone-count split therefore lifts to the target-faithful weighted phase coefficient identity. Exact integral carry decomposes into a canonical finite residue digit plus an unrestricted integral coboundary.

Evidence/status: lean_checked

- [WeightedPhaseCarry.lean](problem/WeightedPhaseCarry.lean)

### unit_carry_tail_splice_countermodel

For every multiplicative jump word with bases at least two, the coefficient base_n-1 is an exact reciprocal difference. Every finite true-prefix/unit-carry-tail splice has the corresponding telescoping rational partial-sum formula.

Evidence/status: lean_checked_finite_core

- [WeightedPhaseCarry.lean](problem/WeightedPhaseCarry.lean)

### function_faithful_observer_criterion

Kernel inclusion for an observer implies equality of full symbolic realizations, and an explicit factorization through a finite-dimensional observer forces the realised symbolic span to be finite-dimensional. Equality after one scalar evaluation is strictly weaker.

Evidence/status: lean_checked_abstract_core

- [WeightedPhaseCarry.lean](problem/WeightedPhaseCarry.lean)

### full_kernel_finite_observer_no_go

Every function-faithful observer into a finite-dimensional space forces the full symbolic realisation to have finite-dimensional range, without assuming a separately chosen readout factorisation. The already checked arbitrary-order nonsingular minors of the literal three-prime kernel therefore rule out every finite-dimensional function-faithful observer of that full kernel. This does not rule out an observer on a specially rank-collapsed reachable subspace; proving that collapse is now a necessary producer rather than an implicit hope.

Evidence/status: lean_checked_mechanism_elimination


### carry_lift_weighted_block_defect

The exact carry-lift recurrence telescopes over every finite block to an endpoint error difference plus the weighted interior defect sum (base_n-1)E_n. This formally isolates why bounded carry error does not imply ordinary unweighted ChannelBlockNull.

Evidence/status: lean_checked

- [CarryLiftExtinction.lean](problem/CarryLiftExtinction.lean)

### block_null_two_anchor_carry_extinction

For a surjective three-channel word, ordinary block-nullity plus genuine 2-to-3 and 2-to-5 zero anchors kills the entire carry-lift perturbation. The lift error then equals its nonzero initial error times the full base product and therefore has absolute value at least 2^N.

Evidence/status: lean_checked

- [CarryLiftExtinction.lean](problem/CarryLiftExtinction.lean)

### bounded_carry_lift_impossibility

No nontrivial carry lift can simultaneously have block-null perturbation, the two anchors, bases at least two, and uniformly bounded error. More generally, any proposed error bound that falls below 2^N at one index is impossible.

Evidence/status: lean_checked

- [CarryLiftExtinction.lean](problem/CarryLiftExtinction.lean)

### unit_accurate_first_block_obstruction

Any integer lift within one of four real states in (0,1) is binary; the two early anchors then force the first complete 2-channel block sum to equal one, contradicting block-nullity. This is independent of choosing floor, ceiling, or nearest-integer representatives.

Evidence/status: lean_checked

- [CarryLiftExtinction.lean](problem/CarryLiftExtinction.lean)

### bounded_radix_zero_or_cofinal_constant_escape

For every real affine orbit x_(a+1)=P_a*x_a-c_a with integral digits and 2<=P_a<=30, Lean proves that either one orbit value is an integer or, cofinally often, the value is at distance at least 1/31 from every integer. The proof checks exact witness alignment and exponential rebound of every nonzero near-integer error.

Evidence/status: lean_checked

- [BoundedRadixTailEscape.lean](problem/BoundedRadixTailEscape.lean)

### exact_cancellation_rationality_transport

If tau=X*S-A with nonzero integral X and a nonzero integral scale B makes B*tau integral, Lean constructs an explicit rational q with S=q.

Evidence/status: lean_checked_abstract_core

- [BoundedRadixTailEscape.lean](problem/BoundedRadixTailEscape.lean)

### canonical_local_window_residue_predicate

CofinalLocalWindowEscape requires the least positive residue of -B times the forcing modulo the positive window base to exceed the short bound, and the short bound is now explicitly allowed to depend on the reduced denominator B. The invalid absolute-numerator comparison and the denominator-independent bound interface have both been removed.

Evidence/status: lean_checked_definition_and_denominator_interface

- [RestrictedFloorSum.lean](problem/RestrictedFloorSum.lean)

### cofinal_local_window_reduced_carry_extinction

For every positive B coprime to 30, CofinalLocalWindowEscape contradicts any everywhere-positive reduced integral carry d_(n+1)=b_n d_n-Bm_n whose absolute state is bounded by the corresponding denominator-dependent shortBound(B,n). The proof unrolls one emitted window, passes from the integer identity to the least-positive residue congruence modulo the absolute window base, and invokes the finite residue consumer. Thus the bad-window bridge is now complete; the problem-specific producer remains open.

Evidence/status: lean_checked

- [RestrictedFloorSum.lean](problem/RestrictedFloorSum.lean)

### residue_delay_five_uniform_bound_counterexample

The exact integer checker tests 2,402,066 coprime denominator/anchor pairs with B<=10000 and 100<=a<=1000 and finds 31 cases whose first residue escape occurs more than five blocks after the base product first clears the denominator. The maximum observed delay is seven, attained at (B,a)=(1961,221),(7591,460),(7591,461); exact trajectory replay verifies zero modular lift at every step of all three longest traps. This decisively falsifies the proposed uniform delay-five producer. The compact durable witness is state/formal_math/erdos257_period_noncollapse/erdos269_residue_delay_five_nogo_receipt.json.

Evidence/status: exact_finite_counterexample


### affine_cylinder_delay_101_counterexample

For every requested depth d, the zero-lift inequalities reduce exactly to a rational interval max(F_t/M_t)<q/B<=min((9F_t+A_t)/(9M_t)), intersected with the exact denominator band making the initial window the first base-clear window. Lean proves the one-step nesting law, turns each quadratic one-shell mass bound into the required Bellman cap inequality, and composes consecutive jump factors without loss. The remaining analytic wiring is to identify the actual block digit with that ordered shell-mass composition. Exact integer checks through depth 200 show every cylinder collapsing to its final constraint; the depth-200 witness has a 181-digit denominator coprime to 30, first clears at length 206, and fires at length 406 after exact residue delay 200. Its maximum digit/capacity utilization is 7041/24200 and its minimum cap slack numerator is 299668. This extends finite cap falsification through K<=199 but is not counted as progress by itself: a longer finite horizon does not prove unbounded delay or arbitrary-depth denominator admissibility. The durable receipt is state/formal_math/erdos257_period_noncollapse/erdos269_affine_cylinder_depth_receipt.json.

Evidence/status: exact_finite_counterexample_with_structural_reduction


### bellman_shell_mass_composition

The quadratic shell bound 9*d<=(J+4)^2 implies 9*d+tailCap(J+1)<=b*tailCap(J) for every jump multiplier b>=2, and two such affine cap inequalities compose with compressed digit c*d+e and radix c*b. The all-scale threshold partition supplies the exact ordered suffix-mass coefficient patterns on the actual source. This deletes new cell-combinatorics and analytic-inequality search inside one-, two-, and three-jump dyadic blocks. The source digit and genuine infinite tail are now bound into the bounded-radix dichotomy; controlling the surviving exact-integral branch or its Farey phase remains open.

Evidence/status: lean_checked_analytic_wiring


### farey_band_nonmonotone_occupancy

A complete logarithmic floor-sum decision procedure counts all q/B in each exact affine-cylinder interval with B in the first-clear band and gcd(B,30)=1. At actual anchor a=100 it certifies occupied-to-empty adjacent first-clear shifts at depths 16, 24, and 50, the reverse polarity at depths 32, 40, 64, and 80, and six singleton bands. All compared cylinders are exactly nested. Therefore nesting, later first-clear length, and coarse interval width cannot propagate denominator admissibility; an arbitrary-depth producer must control the endpoint's arithmetic Farey phase or select anchors cofinally. This does not prove arbitrary-depth occupancy or irrationality. The durable receipt is state/formal_math/erdos257_period_noncollapse/erdos269_farey_band_receipt.json.

Evidence/status: exact_mechanism_elimination


### ordered_source_tail_affine_recurrence

Lean proves the literal real shell masses summable from an all-scale polynomial-geometric majorant, constructs their genuine infinite tsum tail, proves its exact first-shell decomposition, and instantiates the source-identified recurrence X_(a+1)=dyadicBlockBase235(a)X_a-d_a. Applying the bounded-radix theorem, this actual infinite normalized tail either reaches an exact integral state or returns cofinally to distance at least 1/31 from every integer. The exact-Fraction checker now also replays both summability majorants on forty source-faithful scales. The only surviving branch of this dichotomy is exclusion of exact integral normalized states; no irrationality theorem is claimed.

Evidence/status: lean_checked_actual_infinite_tail_dichotomy

- [check_erdos269_ordered_tail_recurrence.py](formal_math/erdos257_period_noncollapse/scripts/check_erdos269_ordered_tail_recurrence.py)

### denominator_one_post_clear_automaton

The sole exact-integral branch has a denominator-one local-window automaton. A proposed uniform three-transition rule survives every start through 2000 but fails exactly at a=2295: after first base-clear, canonical states 385235, 217423, 432920, and 1100228 all remain below their caps, and only the next state 8326020 escapes the cap 2514339. This exact delay-four source word decisively eliminates every proof that assumes escape within three post-clear transitions. All 3000 tested starts escape by total length at most 11, but that bounded horizon is not a theorem or a replacement cap conjecture.

Evidence/status: exact_three_transition_mechanism_elimination

- [check_erdos269_integral_tail_escape.py](formal_math/erdos257_period_noncollapse/scripts/check_erdos269_integral_tail_escape.py)

### phase_conditioned_source_linear_coboundary_no_go

An exact integral normalized tail would provide a coboundary d_a=b_a C_a-C_(a+1). The source-linear probe lets C_a be an arbitrary rational linear combination of 1, a, a^2 and the boundary and cumulative pair-count coordinates for all three channels, with independent coefficients for each actual radix phase 2, 6, 10, and 30. This 36-parameter class strictly contains the failed single-A2 proposal. On the actual initial source word, its coefficient system becomes inconsistent at equation 27: coefficient rank 26, augmented rank 27. A primitive integer left-null certificate pairs to zero with every candidate column but nontrivially with the actual digit vector. Thus direct finite-rank source-linear coboundaries are decisively eliminated; any integral tail must use nonlinear or unbounded-memory phase information, or only a later-onset formula. Erdős #269 remains open.

Evidence/status: exact_finite_rank_mechanism_elimination

- [check_erdos269_source_linear_coboundary.py](formal_math/erdos257_period_noncollapse/scripts/check_erdos269_source_linear_coboundary.py)

### phase_conditioned_source_quadratic_coboundary_no_go

The first source-specified nonlinear enlargement also fails exactly. Take every polynomial of total degree at most two in the eight nonconstant scale, boundary-count, and cumulative-count coordinates, with independent coefficients in radix phases 2, 6, 10, and 30. This gives 45 base monomials and 180 phase-conditioned coefficients. On the actual first 116 source equations the coefficient rank is 115 and the augmented rank is 116. A primitive 116-support integer left-null vector, with coefficients up to 788 bits, annihilates all 180 columns but pairs nontrivially with the actual digit word. Thus every direct phase-conditioned quadratic source coboundary is eliminated; any surviving source-coordinate integral carry must be degree at least three, nonpolynomial, unbounded-memory, or later-onset. Exact integral tails remain unexcluded.

Evidence/status: exact_nonlinear_functional_class_elimination

- [check_erdos269_source_quadratic_coboundary.py](formal_math/erdos257_period_noncollapse/scripts/check_erdos269_source_quadratic_coboundary.py)

### dyadic_radix_word_two_torus_coding

The dyadic radix word is identified exactly. A power of 3 lies in the shell [2^a, 2^(a+1)) exactly when floor(j log_2 3) = a, and likewise for 5, so b_a = 2 * 3^[a in B(log_2 3)] * 5^[a in B(log_2 5)] where B is the Beatty set. The two indicator sequences are Sturmian with slopes log_3 2 and log_5 2, so the radix word is their superposition: a coding of a rotation on the 2-torus by (log_3 2, log_5 2) under a product partition. Checked letter by letter against the literal source engine with 0 mismatches for a = 1..2600. Over 300,000 letters the radix frequencies match the independent-rotation prediction to five decimals (2: 0.21009 vs 0.21012; 6: 0.35924 vs 0.35920; 10: 0.15898 vs 0.15895; 30: 0.27169 vs 0.27173). The factor-complexity bound p(n) <= (n+1)^2 is immediate from the product structure, and equality is measured exactly for n = 1..22 (4, 9, 16, ..., 529) - the rank-2 rotation signature rather than the Sturmian n+1. Every retired functional attempt on the integral-tail branch treated this word as opaque. The source system is a cocycle over an ergodic 2-torus rotation whose angles are ratios of logarithms of 2, 3 and 5.

Evidence/status: ordinary_mathematical_identification_not_lean_checked

- [erdos269_torus_coding.py](probes/erdos269_torus_coding.py)

### product_sturmian_stammering_no_go

The Adamczewski-Bugeaud criterion (Schmidt Subspace Theorem on stammering expansions) needs prefixes that are (1+eps)-powers with eps bounded away from zero. For the product of two Sturmian words the period must serve both slopes at once, so the governing quantity is simultaneous approximation of (log_3 2, log_5 2). Measured against the literal 400,000-letter word at the record simultaneous denominators, the repetition exponents are 2.2615 at q = 65 and then 1.0089, 1.0115, 1.0085, 1.0074 at q = 7061, 7126, 15810, 45807: matched length tracks 1/||q alpha|| and grows like q^(1/2) while the period grows like q, so the exponent decays to 1 like 1 + O(q^-1/2). Dirichlet in dimension two caps simultaneous approximation at exponent 1/2 whereas the criterion needs exponent 1 for both slopes at the same denominator, a measure-zero condition on the slope pair. CLAIM BOUNDARY: this retires the route on measured evidence plus the Dirichlet cap, not as a theorem. A theorem needs an effective lower bound max(||q log_3 2||, ||q log_5 2||) >> q^(-1+delta); Laurent-Mignotte-Nesterenko for two logarithms gives only exp(-C (log B)^2), weaker than any fixed power, and the best known irrationality measure for log3/log2 gives only q^(-4.117). That gap is the precise external input the lane would require.

Evidence/status: transcendence_route_retired_on_measured_evidence_and_dirichlet_cap

- [erdos269_stammering.py](probes/erdos269_stammering.py)

### normalized_tail_diophantine_genericity

The normalized tail X_1 = sum over {2,3,5}-smooth s >= 2 of 1/H(s) was expanded to 13,109 airtight-certified partial quotients. Certification is by common prefix of the continued fractions of the two endpoints of the interval (F/B, (F+kappa)/B] that provably contains X_1, so no approximation heuristic enters: continued-fraction prefixes are cylinder memberships and cylinders are intervals. The engine truncation F/B was independently verified to equal the direct smooth-number sum exactly as rationals. Results: Gauss-Kuzmin frequencies 0.4208/0.1665/0.0917/0.0575 against 0.4150/0.1699/0.0931/0.0589; Levy constant 1.18869 against pi^2/(12 ln 2) = 1.18657; largest partial quotient 129,114; empirical irrationality exponent 2.005. X_1 is Diophantine-generic: there is no self-similar, automatic or algebraic continued-fraction structure to exploit, and no Liouville conspiracy at any scale below 22,483-bit denominators. Since a rational has a terminating expansion with all convergent denominators at most its own, the non-termination of the certified range proves X_1 is not rational with denominator below 2^22482 (about 10^6768). The series value is 1 + X_1, so the same exclusion applies to it.

Evidence/status: airtight_certified_finite_measurement_with_exact_denominator_exclusion

- [erdos269_continued_fraction.py](probes/erdos269_continued_fraction.py)

### lattice_first_hit_denominator_exclusion

Excluding every denominator q <= Q at window depth L is exactly the statement min{q >= 1 : (q*A) mod B <= W} > Q with A = (-F) mod B and W = Q*kappa/9: a first-hit of a rotation in an interval, solvable by the Stern-Brocot recursion in O(log B) rather than the O(Q) of a per-denominator scan. The recursion was brute-force verified on 4,000 random instances and the certificate was cross-checked sound against a direct 200,000-term denominator scan at ten depths. At depth 420 every odd denominator up to about 10^187 is excluded exactly. Across the measured depths the certified bound fits log2 Q = 0.4974 log2 B - 5.29, with fitted exponent within 0.5% of 1/2. This is an exact finite denominator screen plus a measured square-root law, not a theorem that residue bias never accumulates or that every escape/Farey argument is globally capped at sqrt(B_L). The later depth-200 affine-cylinder witness also shows that long delays occur at much larger denominators. A cofinal conclusion still requires an all-scale anti-concentration theorem, a scale-dependent escape law, or an arbitrary-depth admissibility theorem; deeper finite certificates alone do not supply that quantifier.

Evidence/status: exact_denominator_exclusion_and_measured_route_ceiling

- [erdos269_denominator_exclusion.py](probes/erdos269_denominator_exclusion.py)

### escape_is_generic_with_no_accumulation

An exact finite census checks 640,000 certificates: every odd denominator q <= 120 coprime to 30 against every start a <= 20,000. There are zero non-escaping pairs in this rectangle; the maximum escape depth is 18, concentrated at depths 10-13. Mean excess over the counting threshold log_8(q*kappa) is 0.97, and the largest is 7.09 at q=113, a=11569. This is evidence that the previously tested finite-feature functionals have no small-denominator delayed-conspiracy signal in the declared rectangle. It is not a genericity theorem, a no-accumulation theorem, or evidence that increasing lookahead cannot help. The later exact affine-cylinder witness affine_cylinder_delay_101_counterexample has a 181-digit denominator and remains trapped for 200 post-clear steps, so it refutes every uniform escape cap through 199 and supersedes the global extrapolation formerly attached to this census. Neither finite result excludes integral tails or proves an arbitrary-depth delay family.

Evidence/status: exact_finite_small_denominator_census_superseded_as_a_global_delay_claim

- [erdos269_escape_depth_law.py](probes/erdos269_escape_depth_law.py)

### projective_defect_equidistributes_across_far_pairs

Every admissible window endpoint - base clears the cap, residue does not escape it, residue coprime to B - was enumerated for all 133 denominators coprime to 30 in [7,500] across starts a <= 3000; the packet's B=11 witness is reproduced exactly (carries 61 and 259, heights 5 and 2 modulo 11, defect 4). Every denominator admits violating pairs, at fractions from 0.828 at B=7 to 0.988 at B=499. Admissible endpoints occur at density about one per two starts and persist to the top of every range (latest admissible start 2992-3000 for every B), and violating pairs exist with both starts above 2963 for every B. Two structural facts. First, SAME-START pairs are always coherent, P = 1.0000 exactly at every tested B, so any construction must pair different starts - a constraint not previously recorded. Second, for different starts the residual coherence is purely short-range: neighbouring endpoints give coherence 1.23x, 2.06x and 6.42x uniform at B = 7, 101, 499, while endpoints separated by half the list give 1.18x, 1.10x and 0.92x, i.e. equidistributed. The producer's construction is therefore abundant rather than scarce, and what it needs is a proof of two things: that admissible endpoints occur cofinally, and that the projective defect equidistributes modulo B across far-separated pairs. Together with the integral-tail branch's need for anti-concentration of (-qF_L) mod B_L, BOTH remaining routes reduce to the same missing analytic input about the torus-rotation cocycle. Finite enumeration; no cofinal quantifier is supplied.

Evidence/status: exact_enumeration_reducing_the_projective_producer_to_equidistribution

- [erdos269_projective_cofinality.py](probes/erdos269_projective_cofinality.py)

### torus_fourier_representation_of_the_value

The VALUE, not only the digit word, has an explicit torus-analytic form. With L = log_2 s, theta = log_2 3, phi = log_2 5, the running height satisfies 1/H(s) = 2^{L} 3^{L/theta} 5^{L/phi} / s^3 with braces the fractional part - verified to maximum relative error 1.5e-14 over 4,000 smooth s. Summing over the smooth lattice s = 2^i 3^j 5^k gives S = sum W(L)/(8^i 27^j 125^k) with W the value of a bounded function at the 3-torus point ({L},{L/theta},{L/phi}). Because 2^x 3^y 5^z factorises, each Fourier mode turns the (i,j,k) sum into a product of three ordinary geometric series: writing lambda = m1 + m2/theta + m3/phi, the mode contributes c(m1)c'(m2)c''(m3) divided by (1-e(lambda)/8)(1-e(lambda theta)/27)(1-e(lambda phi)/125), with c(m)=1/(ln2-2 pi i m), c'(m)=2/(ln3-2 pi i m), c''(m)=4/(ln5-2 pi i m). W jumps wherever a coordinate hits zero and the Fourier series converges there to the midpoint; those points are exactly the three coordinate axes of the lattice, contributing 9-1=8 at the origin plus ((p-1)/2) sum_n 1/H(p^n) on each axis. The axis terms total exactly 1/2 by a telescope - at each prime power the height multiplies by p, so (p-1)/H(p^n) = 1/H(p^n -1) - 1/H(p^n), and summing over every prime power gives sum_p (p-1) sum_n 1/H(p^n) = 1/H(1) = 1, checked exactly in rationals with truncated value exactly 1 - 1/H(last). Hence S = lim_M [triple Fourier partial sum] - 17/2. Corrected partial sums give errors 7.04e-2, 5.31e-2, 2.09e-2, 9.87e-3, 4.39e-3 at M = 20, 40, 80, 160, 320: monotone and halving as M doubles, the 1/M rate a jump-discontinuous Fourier series gives. This is the first representation of the value as an explicit analytic object; each mode is governed by lambda = m1 + m2 log_3 2 + m3 log_5 2, a linear form in logarithms of 2, 3 and 5, placing the arithmetic exactly where the torus reading predicted. CLAIM BOUNDARY: an exact representation, not an irrationality argument. The triple sum is only conditionally summable - sum |c c' c''| diverges like (log M)^3 - so it converges as a symmetric limit and needs regularisation before any Diophantine estimate could be extracted.

Evidence/status: ordinary_tensor_dirichlet_jordan_completion_pending_independent_review

- [erdos269_torus_fourier_representation.py](probes/erdos269_torus_fourier_representation.py)

### running_height_prime_power_telescope

sum over p in {2,3,5} of (p-1) sum_(n>=1) 1/H(p^n) = 1 exactly. Proof: the running height changes only at prime powers, where it multiplies by p, so (p-1)/H(p^n) = 1/H(p^n - 1) - 1/H(p^n); summing that telescope over every prime power collapses to 1/H(1) = 1. Verified in exact rational arithmetic: the sum truncated at 10^40 equals 1 - 1/H(last), so the residual is exactly the truncation term. The identity is what makes the axis jump-correction of the torus Fourier representation exactly 1/2, hence the total correction exactly 17/2.

Evidence/status: exact_elementary_identity

- [erdos269_torus_fourier_representation.py](probes/erdos269_torus_fourier_representation.py)

### prime_power_boundary_clearing

For p in {2,3,5}, m >= 1 and every {2,3,5}-smooth x < p^m, p*H(x) divides H(p^m); equivalently the whole rational prefix below p^m clears against H(p^m)/p. Clearing therefore holds at ALL THREE prime-power boundary families, not only at powers of two, so rationality puts q*U_{p,m} in Z for U_{p,m} = (H(p^m)/p) T(p^m) at every boundary. Exact check: 2,609 (p,m,s) triples through p^9, zero failures.

Evidence/status: lean_checked

- [RationalLatticeReduction.lean](problem/RationalLatticeReduction.lean)

### all_scale_rational_lattice

If S = p/q then every normalized dyadic tail state X_a = (H(2^a)/2) T_a is (1/q)-integral simultaneously, with explicit integer witness p*(H(2^a)/2) - q*(cleared prefix). No exceptional scale exists under rationality.

Evidence/status: lean_checked

- [RationalLatticeReduction.lean](problem/RationalLatticeReduction.lean)

### rational_tail_state_collision_target

If S is rational then two DISTINCT scales carry normalized tail states differing by an integer (pigeonhole on (1/q)Z mod 1). Contrapositive: pairwise incongruence of the X_a mod 1 implies irrationality. Since X_{a'} - X_a in Z is equivalent to (B_{a'} - B_a) S in Z, the criterion is an iff. This is the correct general-denominator target; the exceptional-integral-state branch is the sub-case X_a = 0 mod 1 and can only ever reach q = 1.

Evidence/status: lean_checked

- [RationalLatticeReduction.lean](problem/RationalLatticeReduction.lean)

### prime_power_jump_identity_with_counts

S = sum_{p in {2,3,5}} sum_{m>=1} (p-1) N(p^m)/H(p^m) with N(x) = #{s smooth : 1 <= s < x}; the N-weighted refinement of the landed telescope sum_p (p-1) sum_m 1/H(p^m) = 1. Exact finite form at every prime-power boundary R: sum_{h<R} 1/H(h) = sum_{t<R} (p_t - 1) N(t)/H(t) + p_R N(R)/H(R), verified exactly at the last 40 prime powers below 2^202 (zero failures) and, with A(x) = #{2 <= s < x} in place of N, the sum is exactly S - 1 (the dropped term is the telescope). Exhibits S as three one-dimensional prime-power series with three-dimensional irrational-simplex lattice-count coefficients, which is why no one-slope Hecke-Mahler theorem applies.

Evidence/status: exact_checker

- [erdos269_width_and_bridge.py](probes/erdos269_width_and_bridge.py)

### prime_power_boundary_ladder_recurrence

On the merged ordered boundary ladder r_1 < r_2 < ... the tails obey U_{j+1} = p_j U_j - C_j with PRIME multiplier p_j in {2,3,5} and UNWEIGHTED gap count C_j, a strictly more elementary recurrence than the dyadic one with radices in {2,6,10,30} and {1,3,5,15}-weighted digits. Verified over 200 consecutive steps with zero failures; at dyadic boundaries it reproduces the dyadic states to 15 digits (U at 2^5 = 5.64900580461722 = X_5; U at 2^200 = 3596.0361820664 = X_200). Cocycle equivalence: S is rational iff some Q >= 1, index J and polynomially bounded integer sequence satisfy n_{j+1} = p_j n_j - Q C_j.

Evidence/status: exact_checker


### two_sided_normalized_state_bounds

Rigorous all-start bounds: (1/60)(floor(a/(2 log_2 3))+1)(floor(a/(2 log_2 5))+1) <= X_a <= a^2 + 6a + 11. The lower bound is Omega(a^2), so the tail state is genuinely unbounded and the hypothesis X_{a+1} < b_a fails cofinally.

Evidence/status: exact_checker


### tail_orbit_mod_one_equidistribution_measurement

Over a <= 1200 with exact digits and truncation bound 1.3e-56: all 1200 fractional parts {X_a} are pairwise distinct, min gap 8.834e-07 at (830,979), min distance to Z 9.697e-04 at a=545 decaying like 1/a, 20-bin chi^2 = 8.0 on 19 df, and |Weyl(h)| = 0.0139/0.0074/0.0114 for h=1,2,3 against 1/sqrt(N) = 0.0289. The orbit behaves like a low-discrepancy equidistributed sequence, and equidistribution mod 1 would imply irrationality via the collision target.

Evidence/status: measurement


### normalized_state_quadratic_width

All-scale explicit width for the genuine half-height normalized tail state: trueNormalizedState m <= 90 (m+1)^2 for every m, hence the cubic form 40 (m+4)^3 named in the longitudinal record. Proof: X_m = sum_n d_(m+n)/(b_m...b_(m+n)) <= sum_n 15 (m+n+1)^2 / 2^(n+1) <= 15 (m+1)^2 sum_n (n+1)^2/2^(n+1) = 90 (m+1)^2, using the Lean digit majorant 15(a+1)^2, every radix >= 2, (m+n+1) <= (m+1)(n+1), and the exact value sum_n (n+1)^2 r^n = 2/(1-r)^3 - 1/(1-r)^2. Measured sup_a X_a/(a+1)^2 = 0.905 (attained at a = 0, X_0 = S/2), so the constant is crude by two orders of magnitude; the exact_checker bound a^2+6a+11 remains sharper but is not Lean.

Evidence/status: lean_checked

- [NormalizedStateWidth.lean](problem/NormalizedStateWidth.lean)
- [erdos269_width_and_bridge.py](probes/erdos269_width_and_bridge.py)

claim_boundary: An explicit polynomial enclosure of the true state; no rationality hypothesis; no irrationality conclusion.

### rationality_to_reduced_carry_bridge

Paper Problem prob:bridge269 (actual rationality-to-carry identification) is closed. If the value S - 1 = dyadicShellTsumTailR235 1 equals p/q with q = 2^α 3^β 5^γ B, gcd(B,30) = 1, then from the explicit onset a₀ = α+1+2β+3γ the reduced carry d_a = (q X_a)/(2^α 3^β 5^γ), X_a = trueNormalizedState a, is an integer with d_(a+1) = b_a d_a - B m_a for the actual radix word b_a = dyadicBlockBase235 a and the actual ordered digit m_a = dyadicOrderedBlockDigit235 a, and 0 < d_a <= B·90(a+1)^2. The onset-aware residue consumer then turns the paper's producer (9.5) into irrationality: CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun B n => B * 90 (n+1)^2) implies Irrational (S - 1) and Irrational S, S = dyadicShellTsumTailR235 0 = 1 + dyadicShellTsumTailR235 1. The extinction theorem is thereby a theorem about the actual series; the only unproved input is the cofinal local-window escape itself.

Evidence/status: lean_checked

- [RationalityCarryBridge.lean](problem/RationalityCarryBridge.lean)

claim_boundary: The bridge is unconditional; the irrationality conclusion is conditional on the named Prop ActualCofinalLocalWindowEscape, which is not proved. The short bound is the Lean width B·90(n+1)^2, not the paper's K^{235}(B,a) = floor(B(ν_a^2+10ν_a+27)/9); the sharper bound would follow from a sharper Lean digit majorant and is not needed for the reduction. Erdős #269 remains open.

### window_escape_equivalence

ActualCofinalLocalWindowEscape is equivalent to irrationality of the {2,3,5} running-LCM series; the equivalence holds for every short bound dominated by c(B)(n+1)^2. RationalityCarryBridge supplies the forward implication; this module proves the converse unconditionally, so actualCofinalLocalWindowEscape_iff gives ActualCofinalLocalWindowEscape <-> Irrational (dyadicShellTsumTailR235 1) and actualCofinalLocalWindowEscape_iff_irrational_value gives the headline form against dyadicShellTsumTailR235 0. The mechanism is the real window identity trueNormalizedState_window, the exact pinning near_integer_of_residue_le_general for an arbitrary short bound, and exists_pow_gt_quadratic: window bases grow at least like 2^len, so an exponential eventually beats any quadratic short bound.

Evidence/status: lean_checked

- [CofinalWindowEscapeEquivalence.lean](problem/CofinalWindowEscapeEquivalence.lean)
- [erdos269_window_escape_equivalence.py](probes/erdos269_window_escape_equivalence.py)

claim_boundary: It proves an equivalence of two propositions and proves neither of them; Erdos #269 remains open. The content is a no-go for the producer as a reduction: ActualCofinalLocalWindowEscape is not a weaker, more tractable statement, and proving it is literally proving Erdos #269. Any further effort on the producer must be justified as an attack on the target itself.

### paper_digit_formula_equals_lean_threshold_digit

The paper's checker digit (9.1), m_a = A_2(a+1) + sum_{(p,e) in I_a} (p-1) σ_a(p,e) (C_p(e) - C_2(a)), with A_p(e) = #{(i,j): q^i r^j < p^e} and C_p(e) = sum_{u<=e} A_p(u) = #{smooth x < p^e}, equals the Lean ordered digit dyadicOrderedBlockDigit235 a = N + 10 C3 + 4 C5 (3-jump first) or N + 2 C3 + 12 C5 (5-jump first), and both equal (H(2^(a+1))/2) sum_{shell a} 1/H(h): exact for every 0 <= a <= 200, zero mismatches. The identification is definitional once C_p(e) - C_2(a) is read as the shell-relative threshold count #{2^a <= x < p^e} and A_2(a+1) as the shell cardinality; the Lean theorems dyadicHalfClearedMass235_eq_orderedBlockDigit235 and half_threePrimeHeight_mul_dyadicShellMassR235 already prove the cleared-mass identity for every a. The 'remains analytic' caveat in BlockMassEngines.lean and HalfHeightDenominatorTransport.lean predates DyadicBlockThresholdPartition (2026-08-27) and is superseded.

Evidence/status: exact_checker_with_definitional_transcription

- [erdos269_width_and_bridge.py](probes/erdos269_width_and_bridge.py)

claim_boundary: The all-a identity paper-(9.1) = Lean digit is a transcription plus a finite exact check to a = 200; the Lean-checked object is the threshold-count digit and its cleared-mass identity.

## Known failed routes

No finite separated-factor decomposition represents the literal three-prime kernel.

Direct p-adic convergence fails because denominators carry unbounded contributions from the other prime channels.

Standard Cantor-series criteria do not instantiate on the jump ordering.

A positive scalar tail bound or finitely many carry bits cannot exclude rationality at arbitrary denominator height.

Finite Farey exclusion is not an unbounded irrationality proof.

The pure-power block equations exclude nontrivial upward rational shadows but do not exclude every rational tail state.

The local residue certificates at B = 1, 7, and 16 do not establish cofinal anti-concentration for arbitrary denominators.

Polynomially bounded integral carry, finite carry residues, or a rational scalar specialisation do not by themselves furnish a function-faithful finite quotient.

The literal full three-prime kernel admits no finite-dimensional function-faithful observer: faithfulness would force finite realised rank, while its nonsingular minors have arbitrary order. Any surviving finite-observer route must first prove a genuine finite-rank collapse on the source-reachable subspace; restricting the state space without that theorem is not progress.

The carry recurrence supplies a weighted block defect, not ordinary unweighted ChannelBlockNull; bounded endpoint error alone does not remove the interior weighted term.

Canonical small-error integer lifts cannot satisfy both early anchors and the first complete 2-channel block-null equation: the forced block sum is one.

The canonical window residue is not generally coprime to the window base, and fixed windows can have admissible reduced denominators whose least positive residue is exactly one. A universal bounded-length or denominator-independent window rule is therefore unavailable.

The exact dyadic checker can certify bounded rectangles of denominator/start pairs, but no finite rectangle supplies the universal B or cofinal-a quantifiers. Its value is to test and falsify candidate window rules against the exact residue consumer.

Uniform escape within five blocks after the dyadic window base first exceeds B is false: 31 exact counterexamples occur in the B<=10000, 100<=a<=1000 adversarial scan, with maximum delay seven.

Small uniform post-clear delay is decisively unavailable: exact affine-cylinder reconstruction produces residue delay 101 at the actual anchor a=100 and therefore falsifies every cap K<=100. This is not evidence for cap 101 and does not prove unbounded delay; the next producer must control delay as a function of denominator height or prove/refute arbitrary-depth admissible cylinders.

Individual canonical residues can both satisfy the local size and coprimality constraints while being globally incompatible with one rational numerator. For B=11 the exact carries 61 and 259 pass both local tests but violate the required height-weighted projective congruence by 4 modulo 11. One-window admissibility is therefore strictly incomplete.

Quotient normalization exactly factors every projective cross-defect, but its centered residues are not uniformly small: an exact locally admissible B=7 pair already has centered quotient defect -2, outside the quarter-modulus band. A direct small-error ceiling inequality is therefore unavailable; the producer must control full modular discrepancy.

The denominator-one integral-tail automaton does not escape uniformly within three transitions after first base-clear: the exact source word at a=2295 remains cap-admissible for four transitions. A fixed-three modular classification is therefore unavailable.

No radix-phase-conditioned polynomial of total degree at most two in the eight nonconstant direct source coordinates solves the integral-tail coboundary. The exact 180-column system has a primitive left-null separator on the first 116 actual equations. Higher-degree, nonpolynomial, unbounded-memory, and later-onset mechanisms remain open.

The Adamczewski-Bugeaud stammering route is retired for the three-prime radix word. Repetition exponents at the record simultaneous-approximation denominators decay to 1 like 1 + O(q^-1/2), a full power short of the criterion's requirement, because two rationally independent slopes cap simultaneous approximation at Dirichlet exponent 1/2. Closing it as a theorem needs an effective bound max(||q log_3 2||, ||q log_5 2||) >> q^(-1+delta) that current linear-forms-in-logarithms results do not supply.

No exceptional Diophantine structure exists in the normalized tail to carry a proof. 13,109 airtight-certified partial quotients are Gauss-Kuzmin distributed with a Levy constant within 0.9% of theory and irrationality exponent 2.005, so the delayed-carry conspiracy the retired Lyapunov, coboundary and observer attempts were searching for does not exist below 22,483-bit denominators (about 10^6768).

Deeper finite escape certificates cannot discharge the unbounded-height producer. The largest denominator excludable at window depth L is Theta(sqrt(B_L)) - measured exponent 0.4974 over 420 depths - which is the best-approximation barrier, and B_L grows only exponentially in depth.

The premise shared by every retired functional attempt on the integral-tail branch is false in the measured range: escape delay does not accumulate. 640,000 exact certificates give zero non-escaping pairs, maximum depth 18, and an extreme excess consistent with generic extreme-value behaviour, so there is no residue bias for a Lyapunov function, coboundary or finite observer to detect.

Same-start window pairs can never supply the projective producer: their shadow congruence holds identically, measured at P = 1.0000 across every denominator tested. Any construction must pair different starts, and the residual coherence among different-start pairs is short-range only.

The frozen-digit torus squeeze is invalid and is RETRACTED. Defining G_A(tau) with digits frozen at absolute indices A+j while only the radix phase moves does NOT satisfy G_A(tau_a) = X_a for a != A, so integrality on the orbit never lifts to the torus. Exact falsifier: X_2 = 0.855916114335898 against G_1(tau_2) = 0.538856461107848, defect 0.317; defect 152.5 at a=40. Structurally, the covariance Phi(T theta) = b_0(theta) Phi(theta) - d_0 needs the digit source to shift too, and the three-prime digit is a lattice count at the translated scale, growing like n^2, so it is not a function on a compact torus at all. Any valid torus argument must move the complete source and retain or eliminate the non-compact scale variable.

The two-sided residue annulus buys nothing. Adding the Omega(a^2) lower bound to the log-window residue test so that rho must lie in [lower(a+L), upper(a+L)] rather than merely below upper(a+L) excluded ZERO additional starts over 400 tested (271 excluded one-sided, 0 gained, 129 inconclusive). The lower bound sits a factor about 37 below the upper one and trims a negligible slice of an already thin target.

The local zero-gap extinction step is invalid: b_a | d_a plus positivity does NOT force X_{a+1} = 0. The correct local statement is X_a in Z iff b_a | X_{a+1}, and X_{a+1} < b_a fails cofinally because X_a = Omega(a^2). Already repaired in-tree as the quantitative zero_gap_digit_separation.

No bounded-level parity lemma exists for the B=1 corner. A*(r) = min{A : C_{p_r}(A) odd} along the convergents of log_2 3 is distributed Geometric(1/2) (1097 certified convergents; chi^2 = 1.09 on 7 d.f. over the eight cells with expected count above 4), so max A* grows like log_2 of the number of convergents: measured max A* = 13 at r = 978, with A* > 5 at 17 indices. The wave-7 measurement 'maximum 5 over all 86 members' reproduces exactly on r <= 85 and is a horizon artifact, not a constant level. Any proposal of the form 'some A <= K always works' is refuted in advance. See BlockKernelProgrammeLab.md E13 / section 14.2.

Baker/Matveev is NOT required for sliver-emptiness, and the wave-6 classification of it as 'Baker's home turf' cost the campaign the (MRL') detour. For A >= 1 every smooth 3^u 5^v is an integer distinct from 2^A, so |log_2(3^u 5^v) - A| >= log_2(1 + 2^-A) by unique factorization alone; both Lemma S slivers are empty once |p*log_2(3) - n| <= log_2(1 + 2^-(A+1)). Measured window A <~ log_2(p_r) against Matveev's p^((mu-1)/K) = p^(2.3e-11): at r = 124 that is A <= 200 versus A <= 1 (161 exact instances, 0 failures). At A = 0 the bound is FALSE (3^0 5^0 = 2^0) and the sliver carries a +1 defect. The wave-5/6 (MRL') measure-to-witness break nevertheless survives, since log_2(p) samples still fall short of the required ~p. See E12, E15 / section 14.1.

Larger finite continued-fraction exclusions of the value S add no mechanism to either terminal corner. Computing N shells bounds the tail by ~8^-N and therefore excludes reduced denominators only to about 10^(0.45 N), the same Theta(sqrt(B_L)) law already recorded above; a returned 10^1000 certificate at cutoff N = 2300 is exactly that law and is strictly weaker in kind than the section 9 block certificate at 10^105, which is structural. Denominator size is not progress.

The natural parity anchor for the B=1 shell-parity rung exists but is provably misaligned with the dyadic grid. For x = 3^i 5^j with c = log_2 x, the divisor involution d -> x^2/d on the perfect square x^2 forces #{smooth y : |log_2 y - c| < w} to be ODD whenever every smooth number within 2^w of x divides x^2 (balance conditions j*log_2(5) <= i*log_2(3) + log_2(3) - w and i*log_2(3) <= j*log_2(5) + log_2(5) - w). Verified: 212 balanced pairs at w=1/2, i,j<170, zero even; the balance hypothesis is load-bearing (unbalanced pairs split 313 odd / 330 even). Transfer to the dyadic shell [2^K, 2^(K+1)) gives s(K) = 1 + E (mod 2) with a single edge term E, but exact alignment would need 3^(2i) 5^(2j) = 2^(2K+1), impossible by unique factorization; the achievable offset is polynomial in the anchor size while forced emptiness needs 2^-K. Consequence: the anchor yields only sparse unconditional certificates -- exhaustive search over 7511 balanced anchors to K = 19015 found exactly five (K = 1, 41, 124, 254, 384), matching the 0.74*ln(X) heuristic. Do NOT expect a bounded-search proof from this route. See BlockKernelProgrammeLab.md section 15 (A23-A25).

## Open implications

### exclude_exact_integral_dyadic_tails

Exclude every exact integral state of the genuine normalized source tail X_a=H(2^a)T_a/2. Lean proves that this orbit either has such a state or returns cofinally 1/31-far from all integers. The denominator-one automaton remains the direct arithmetic representation, but the exact a=2295 source word kills every uniform three-transition post-clear proof, and exact left-null certificates now eliminate every direct phase-conditioned source potential of total degree at most two. Analyze longer surviving error cones through a genuinely nonlocal all-scale invariant, prove that an integral carry would force a finite-degree source potential, or move to nonpolynomial/unbounded-memory structure.

Evidence/status: see the source; no formal status inferred


### cofinal_projective_window_pair_incoherence

For every positive B coprime to 30, construct arbitrarily late pairs of exact dyadic windows whose canonical endpoint carries are individually within the analytic bounds but violate d_a*H_b=d_b*H_a modulo B. Equivalently after the Lean-checked exact factorization, force nonzero full modular discrepancy between the weighted ceiling quotients k_i*S_j. The B=11 pair opens the consumer, while the exact B=7 quarter-band counterexample rules out replacing this modular producer by a uniform small-centered-error inequality. Neither finite witness supplies the universal/cofinal producer.

Evidence/status: see the source; no formal status inferred


### carry_faithful_weighted_phase_observer

The full symbolic three-prime kernel cannot have a finite-dimensional function-faithful observer. To retain this route, use the all-scale true cone or block identities to prove that the actual rationality-reachable weighted phase subspace has finite realised rank, and only then construct a faithful finite observer on that collapsed subspace. Otherwise move to an infinite-dimensional or nonlinear observer.

Evidence/status: see the source; no formal status inferred


### bounded_residue_lift_balance

Construct, from the actual rationality carry, a bounded residue lift whose perturbation satisfies the required unweighted channel-block equations and the two genuine transition anchors, or replace ordinary block-nullity by a weighted rigidity theorem that consumes the exact block-defect identity.

Evidence/status: see the source; no formal status inferred


### unbounded_height_certificate

Replace one finite Farey bound by a family with denominator exclusion tending to infinity.

Evidence/status: see the source; no formal status inferred


### actual_cofinal_local_window_escape

Prove ActualCofinalLocalWindowEscape (RationalityCarryBridge.lean), the paper's (9.5): for every B >= 1 coprime to 30 and every a₀ there are lo >= a₀ and len >= 1 with lpr_{W}(-B·F) > B·90(lo+len+1)^2, W = b_lo...b_(lo+len-1), F the accumulated forcing of the actual ordered digits. By irrational_value_of_cofinalLocalWindowEscape this alone proves Erdős #269 at {2,3,5}. It is the B > 1 corner AND the B = 1 corner in one quantifier (B = 1 is included); the finite evidence is the 106,666-pair scan (B <= 1000, 100 <= a <= 500, window length <= 14) and the exact left-null / delay counterexamples recorded above, none of which supplies the cofinal quantifier.

Evidence/status: see the source; no formal status inferred
