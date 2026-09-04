# erdos_251 mathematical frontier

Generated from the exported research packet. Read the strongest applicable
result before attempting a proof; superseded results remain history.

Prove irrationality of the dyadic series built from consecutive prime gaps.

## Established results and their evidence

### free_pair_shift_and_redundant_plus_minus_two_wall

Three proved reductions that strictly weaken the recorded obligation. (1) FREE PAIRS: writing T_N = 2^(N+1)S - I_N with I_N integral, T_M - T_N is an integer for EVERY pair with M == N mod t, t = ord_d(2), not only for a fixed offset h; the recorded producer's fixed-offset form is the special case M = N+h, so the free-pair obligation is strictly weaker and the tail condition becomes a hitting problem on an unconstrained parameter rather than a correlation between windows at bounded distance. (2) THE +-2 WALL IS REDUNDANT: the packet's own reduction actual_prime_adjacent_mismatch_event_density lands on 'Delta = +2 with D in (1/2,1)', but D is an integer whenever t | h and no integer lies in (1/2,1), so the first component alone is already a contradiction. The wall was an artifact of small_adjacent_shift_consumer using the window (-1,1), which CONTAINS the integer 0 and therefore needs a second condition to exclude D = 0. Any integer-free window needs one condition. The sharpened producer is: for every t and every cutoff, cofinally many M == N mod t whose certified tail difference is non-integral. (3) STATE COMPRESSION: sum_(N<=X) T_N <= p_(X+1) + 2T_X, so by Markov a density 1-1/C subset of (X,2X] has T_N <= C log p_(2X); under rationality every T_N lies in (1/d)Z, so on that subset T takes at most dC log p_(2X) + 1 values and some single value is attained >>_(d,C) X/log X times. Rationality forces the prime-gap tail to be a finite-state object at every scale, so pairs with T_M = T_N exactly are abundant for free and the difficulty is entirely in producing a NON-integral difference. Verified: t <= 20, every residue class, 1,270,607 primes, leanest class 90,150 witnesses, latest witness index 1,270,520 of 1,270,540. Evidence: FreePairStateCompressionLab.md, formal_math/probes/erdos251_free_pair_and_state_compression.py.

Evidence/status: proved_reduction_with_four_falsifiers_passing


### first_finite_denominator_exclusion

The packet recorded no finite denominator exclusion. One is cheap because T_N is a TAIL: T_(n0) = U/2^P + T_(n0+P)/2^P exactly with U = sum_(k<=P) g_(n0+k) 2^(P-k), so if d*T_(n0) is an integer then dist(dU mod 2^P) <= d*Theta for any rigorous upper bound Theta on T_(n0+P). Theta is taken from the Lean-checked elementary estimate p_n <= 1250(n+1)^4, so no gap conjecture enters. By the best-approximation theorem the minimum of dist(dU mod 2^P) over d <= D is attained at a convergent denominator of U/2^P, which makes the certificate COMPLETE rather than a spot check. At 4096 tail bits and index 1266144 of 1270606: every odd d <= about 10^602 (2003 bits) is refuted, hence any rational S = a/b has b > 10^602. A first draft reported a bound exceeding 2^P, which is impossible; the probe now fails closed on that and verifies at every convergent denominator below the bound rather than at a few convenient small d.

Evidence/status: certified_complete_at_every_convergent_denominator


### gap_series_identity

For every finite horizon, summation by parts rewrites the zero-based prime partial sum as 2 plus the actual prime-gap dyadic partial sum minus the exact endpoint. At the infinite level, both the normalized prime series and the actual gap series are now kernel-checked summable, and Lean proves unconditionally the exact identity sum p_n/2^(n+1) = 2 + sum g_n/2^(n+1).

Evidence/status: lean_checked_infinite_unconditional

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

claim_boundary: The four named declarations prove unconditional summability of the normalized prime and consecutive-gap series, their exact infinite identity, and the irrationality equivalence under the supplied summability hypothesis. They do not prove irrationality of either series, a prime-gap distribution theorem, or any stronger denominator-growth conclusion.

### zero_based_factor_two_normalization

At both the termwise and infinite-sum levels, the zero-based displayed prime sum with denominator 2^i is exactly twice the normalized sum with denominator 2^(i+1). Under summability it equals 4 plus twice the normalized gap series, and its irrationality is equivalent to irrationality of the gap series.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

### polynomial_prime_growth_summability_adapter

Any natural polynomial upper bound p_n <= C(n+1)^k on the zero-based nth prime kernel-checks summability of the normalized prime series p_n/2^(n+1). Combined with the existing summation-by-parts theorem, the same bound supplies summability of the actual consecutive-prime-gap series and its exact infinite identity. No prime-growth theorem is assumed or imported by this adapter.

Evidence/status: lean_checked_conditional

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

### elementary_prime_bound_and_unconditional_convergence

Lean proves the explicit elementary estimate p_n <= 1250(n+1)^4. The proof bounds the central binomial coefficient by (2m)^pi(2m), compares it with 4^m at m=(n+5)^4, and converts the resulting prime-counting inequality to an nth-prime bound. Feeding this theorem into the polynomial adapter proves unconditional convergence of both dyadic series without importing the prime number theorem or any sorry-bearing analytic development.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

claim_boundary: The three named declarations prove the displayed elementary prime bound and the resulting summability statements in the cited Lean development. They do not prove the prime number theorem, sharpen the bound to the analytic optimum, establish the needed cofinal mismatch supply, or by themselves prove irrationality of the prime-gap series.

### integral_tail_shift_criterion

For every integer-digit dyadic tail recurrence, the exact h-step block identity holds and one h-step tail shift is integral if and only if (2^h-1) times the initial tail state is integral. The actual real prime-gap sum is now connected to this finite algebra by a checked rational-candidate tail representation.

Evidence/status: lean_checked_algebraic_core

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

claim_boundary: The three named declarations prove the exact finite recurrence, block identity, integrality equivalence, and rational-candidate bridge under their explicit hypotheses. They do not prove that any rational candidate exists for the genuine sum, establish a cofinal non-integrality or mismatch supply for actual prime gaps, or by themselves prove irrationality.

### odd_denominator_totient_shift

Given a dyadic tail recurrence and an index N whose rational tail state has odd reduced denominator d, the shift by Euler's totient phi(d) steps is integral; Euler's congruence supplies the explicit finite multiplier certificate.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

claim_boundary: The theorem is conditional on the recurrence and odd-denominator hypothesis. It does not show that a genuine prime-gap tail has such a rational state, establish a cofinal nonintegrality or mismatch supply for actual prime gaps, or prove irrationality of the prime-gap series.

### actual_gap_rational_candidate_recurrence

For every proposed rational value S, subtracting the first N+1 actual prime-gap terms and rescaling by 2^(N+1) gives an exact rational tail state satisfying T_(N+1)=2T_N-g_(N+1). This is algebraic and does not assume that S is the genuine infinite sum.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

### actual_real_to_rational_tail_representation

If the genuine real prime-gap sum equals a rational S, then at every N the cast of the rational candidate state is exactly 2^(N+1) times the real tsum beginning at index N+1. Lean also rewrites every rational candidate tail shift as the difference of two such scaled real tails and extracts the rational witness directly from non-irrationality.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

claim_boundary: The three named declarations provide the exact rational-candidate representation and scaled-tail identities under the explicit summability and non-irrationality hypotheses. They do not prove the required cofinal non-integrality or mismatch supply, and they do not by themselves establish irrationality of the prime-gap series.

### odd_denominator_candidate_anti_concentration

If a proposed rational value S has odd reduced denominator, its single Euler-period shift is integral at every actual prime-gap tail index. Since actual consecutive prime gaps are not eventually periodic, that fixed shift cannot eventually remain strictly between -1 and 1.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

claim_boundary: This is a conditional odd-denominator obstruction. It does not cover candidates with an even denominator, prove irrationality of the genuine series by itself, or establish the full denominator decomposition already recorded separately.

### full_denominator_candidate_shift_obstruction

For every rational candidate S, Lean splits its denominator into its exact power-of-two and odd parts, shifts past the dyadic part, and proves that the Euler-period shift attached to the odd part is eventually integral. Consequently every rational candidate has a positive fixed actual-gap tail shift which cannot eventually remain strictly between -1 and 1.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

### free_carry_telescoping

Arbitrary integer carries emit coefficients 2K_n-K_{n+1} whose dyadic partial sums telescope exactly.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

### tail_shift_integrality_propagation

For every integer-digit dyadic tail recurrence, a fixed h-step tail shift obeys the exact difference recurrence and, once integral, remains integral at every later index.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

### actual_prime_gaps_unbounded

The actual consecutive-prime-gap sequence is unbounded. The proof constructs factorial prime-free intervals, locates their bounding consecutive nth primes by the prime-counting/nth Galois connection, and obtains a gap larger than any prescribed M.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

### small_adjacent_shift_consumer

For any integer-digit dyadic tail recurrence, if two adjacent h-shifts both lie strictly between -1 and 1 and the corresponding digits differ, the two shifts cannot both be integral. Therefore a cofinal supply of such finite small-mismatch certificates rules out eventual integrality of that fixed shift.

Evidence/status: lean_checked

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

### prime_specific_eventual_integrality_exclusion

For the actual consecutive prime gaps, a cofinal supply of adjacent small-shift pairs with a mismatching gap difference rules out eventual integrality of the h-shift. A stronger global corollary says that eventual strict smallness for any positive h already suffices, since integrality would force eventual periodicity and actual prime gaps are Lean-checked to be unbounded.

Evidence/status: lean_checked_conditional_on_exact_local_supply

- [PrimeGapDyadicTail.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean)

### periodic_fractional_orbit_countermodel

A periodic fractional tail orbit is compatible with irregular, prime-like, and prescribed finite even-gap patterns because the integer carry is free.

Evidence/status: advisory_constructive_no_go


### positive_even_polynomial_gap_rational_tail_countermodel

The explicit word g_n=2(n^2+4n+2) is positive, even, polynomially growing, strictly increasing, unbounded, and nonperiodic. The integral orbit T_n=2(n+4)^2 satisfies T_(n+1)=2T_n-g_(n+1), while g_(n+1)-g_n=4n+10 is never ±2. Hence the h=1 adjacent-small-mismatch producer fails at every index in a rational positive-even polynomial tail. Coarse prime-gap properties cannot force the producer; genuinely consecutive-prime arithmetic or another external fractional-tail theorem is necessary. All eight named declarations pass the focused Lean/Lake authority check.

Evidence/status: lean_checked_exact_infinite_mechanism_elimination


### generic_schedule_nonintegrality_criterion

For any positive schedule that eventually dominates every index and is eventually divisible by every positive shift length, Lean proves that irrationality of the initial dyadic tail is equivalent to nonintegrality of the diagonal shifts at the schedule's own points. This replaces the all-basepoint/all-shift criterion by one predetermined sequence; the cofinal nonintegrality premise for the actual prime-gap target remains open.

Evidence/status: lean_checked_conditional_schedule_consumer

- [OrderLatticeDiagonal.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/OrderLatticeDiagonal.lean)

claim_boundary: The schedule theorem is an exact conditional criterion, not an irrationality proof for the consecutive-prime-gap series; it does not supply the required schedule misses.

### data_dependent_affine_cylinder_circularity

For every integer-digit dyadic tail recurrence, membership of the observed depth-r block in the affine lattice 2^r z + T_(N+r) is exactly even integrality of T_N and is independent of r. Cofinal affine-cylinder escape is therefore equivalent to the non-eventual-integrality conclusion it was meant to produce.

Evidence/status: lean_checked_exact_no_go

- [AffineCylinderCollapse.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/AffineCylinderCollapse.lean)

claim_boundary: The named declarations establish the exact affine-cylinder equivalence and its cofinal escape reformulation for the abstract integer-digit recurrence. They do not prove non-eventual integrality for the actual prime-gap series, supply the missing consecutive-prime arithmetic, or prove Erdős #251 irrationality.

### fixed_lattice_block_residue_second_circularity

For every dyadically dominated rational terminal bound, cofinal escape of observed blocks from the fixed lattice 2^r Z is equivalent to non-eventual integrality of the tail state. The reverse implication uses only rational denominator separation and the recurrence identity; it extracts no information from the prime-gap word. Exact balanced-orbit replay verifies the proof coordinates and is bound to the Lean declarations by the durable block-residue no-go receipt.

Evidence/status: lean_checked_with_exact_coordinate_regression

- [AffineCylinderCollapse.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/AffineCylinderCollapse.lean)

### actual_prime_adjacent_mismatch_event_density

The landed +-2 wall and sign-alignment theorems reduce the cofinal-adjacent-small-mismatch producer to a single event: Delta = +2 with D in (1/2,1), or Delta = -2 with D in (-1,-1/2), where D = T_(N+h) - T_N and Delta = g_(N+h+1) - g_(N+1). Measured over 6,841,648 primes (limit 1.2e8) and offsets h = 1..16, that event occurs for every offset, at density between 0.00418 and 0.008248, with +2 and -2 near-balanced, and continues to the top of the range (h=1: 56,427 events, last at prime 119,995,753). Band densities decline only at about the 1/log p cost of demanding Delta = +-2 - rescaled by log p they run 0.1767 -> 0.1315 with a decelerating drift - so the event count up to X still grows like X/(log X)^2. 3,200 hits across h = 1..8 were re-checked against the producer as literally written, both shifts strictly inside (-1,1) and g_(N+h+1) != g_(N+1), with zero violations; the median distance of a hit from its window boundary is 0.127 against a worst case of 6.1e-7, eight orders of magnitude above float64 resolution. This decides between the two live readings of the residual: the producer is TRUE in the actual primes, the polynomial gap countermodel does not generalise to them, and #251 needs a proof of cofinality rather than a different consumer. The missing input is a lower bound on the count of n <= X with g_(n+h+1) - g_(n+1) = +-2 and the weighted tail difference in the correct half-window - Hardy-Littlewood k-tuple correlation at a fixed offset plus dyadic-tail equidistribution - and specifically not any theorem about gap size, growth or periodicity. Finite measurement only; cofinality is not proved and the target irrationality remains open.

Evidence/status: finite_measurement_deciding_the_producer_is_true_in_the_actual_primes


### adjacent_mismatch_event_factorises_and_decorrelates

The landed shift_gt_half_of_digit_eq_two already forces D > 1/2 from a +2 digit given the successor constraint, so the two halves of the producer's event are not independent and the free part is D < 1. Conditioning on the digit and histogramming D separates the density into P(Delta = +-2) times P(D in window | Delta = +-2). Over 6,841,648 primes with Delta = +2 the digit rate is 0.06893, 0.05017, 0.05187, 0.05228, 0.05242, 0.05244 at offsets h = 1, 2, 3, 5, 8, 13 and the conditional in-window fraction is 0.05942, 0.04586, 0.04253, 0.04015, 0.04026, 0.03982. The tail factor is bounded away from zero - between 0.0398 and 0.0602 across every offset - and across six bands of N it drifts only by a factor 0.77 to 0.84, the same mild decline as the digit factor. So a proof does NOT need a joint statement about the digit and the tail: it can aim a Hardy-Littlewood count at the digit and a non-concentration statement at the tail, separately. The conditional structure is also offset-independent from h = 5 onwards, with the short/overshoot split converging to 0.46/0.50, while h = 1 is visibly different (the shift is pushed high, overshooting 72% of the time) and h = 2, 3 interpolate. The tail shift therefore decorrelates from the digit at offsets of about five, and a proof only has to treat small h specially. Finite measurement; cofinality is not proved and the target irrationality remains open.

Evidence/status: exact_finite_measurement_separating_the_two_factors

- [erdos251_conditional_shift_distribution.py](formal_math/probes/erdos251_conditional_shift_distribution.py)

### certified_continued_fraction_denominator_exclusion

The packet recorded no finite denominator exclusion and contained no continued-fraction content. If S is rational its expansion terminates and its reduced denominator is that of the last convergent, so a certified prefix of length n+1 forces q >= q_(n+1). Certified means each quotient is forced by an exact rational bracket: the interval expansion emits a quotient only when both endpoints agree, and the prefix stays genuine even if S is rational because at the step the expansion would end the endpoint floors differ and the algorithm halts. Bracketing the normalized zero-based prime series S = sum_(i>=0) p_i/2^(i+1) by the exact prefix through index B+128 at internal scale 2^(B+128), with the omitted tail bounded by this packet's own Lean-checked elementary estimate p_i <= 1250(i+1)^4 rather than a heuristic prime bound, and shifting down so the bracket is one unit wide, gives at B = 80000 bits: 23369 certified partial quotients and q >= 2^39998 > 10^12041, with the separation |q_n S - p_n| > 0 verified against the bracket. By gap_series_identity the actual prime-gap series is S - 2, an integer shift, so it has the same denominator and the same bound. The bracket was checked against an independent summation, and the module self-checks against e = [2;1,2,1,1,4,1,1,6,...] and the convergents 3, 22/7, 333/106, 355/113 of pi before every run.

Evidence/status: exact_finite_denominator_exclusion


### adjacent_small_mismatch_signed_two_window_normal_form

For any integer-digit dyadic tail recurrence whose digit difference is even, both adjacent h-shifts lie strictly in (-1,1) and the corresponding digits differ if and only if the digit difference is +2 with the first shift in (1/2,1), or -2 with the first shift in (-1,-1/2). The theorem is an exact local normal form; it does not assert that either event occurs cofinally for the actual prime gaps.

Evidence/status: lean_checked_exact_signed_two_window_equivalence

- [AffineShiftEscape.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/AffineShiftEscape.lean)

surviving_obligation: Prove cofinal occurrence of the signed ±2 half-window event, or provide another genuinely external fractional-tail obstruction; Erdős #251 remains open.

### factorial_diagonal_criterion

For every dyadic-tail recurrence in the #251 formal setting, irrationality of the initial value is equivalent to nonintegrality at every single factorial diagonal point (j!, j!). Equivalently, non-irrationality is witnessed by one integral factorial-diagonal point. The factorial schedule cofinally contains every positive shift and grows past every basepoint, so this replaces the original double quantifier by one exact predetermined sequence without changing the theorem's logical strength.

Evidence/status: lean_checked_factorial_schedule_consumer

- [OrderLatticeDiagonal.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/OrderLatticeDiagonal.lean)

claim_boundary: This is an exact schedule reformulation of the irrationality criterion. It does not prove that the actual prime-gap series is irrational, nor does it establish nonintegrality at any particular factorial point without a separate source-specific argument.

surviving_obligation: Supply a source-specific proof that every factorial diagonal point is nonintegral, or an equivalent cofinal escape for the actual prime-gap sequence; Erdős #251 remains open.

### polynomial_gap_countermodel_series_value_tsum

For the polynomial countermodel g_n = 2(n^2+4n+2), T_n = 2(n+4)^2, Lean proves the exact finite telescope sum_(j<=N) g_j/2^j = 32 - T_N/2^N in Q, the limit 2(N+4)^2/2^N -> 0, and hence HasSum (fun n => g_(n+1)/2^(n+1)) 32 and tsum_(n>=0) g_(n+1)/2^(n+1) = 32 in R, so the positive, even, strictly increasing, unbounded, nonperiodic gap series has the rational value 32. This was previously only the symbolic Python receipt in scripts/erdos251_polynomial_gap_countermodel.py; the 25/32 ratio bound is no longer load-bearing for the value.

Evidence/status: lean_checked_exact_series_value

- [PolynomialGapSeriesValue.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/PolynomialGapSeriesValue.lean)

claim_boundary: The countermodel is not the actual prime-gap word. The declarations establish the series value and rationality of the countermodel series only; they say nothing about the consecutive-prime-gap series and do not bear on Erdős #251 irrationality.

surviving_obligation: None for the countermodel value. Erdős #251 remains open.

### free_pair_lattice_and_irrationality_equivalence

(F) with converse: for any integer-digit dyadic tail recurrence, at and beyond an odd-denominator state with reduced denominator d, T_M - T_N is an integer iff N == M mod orderOf(2 : ZMod d); the offset M - N is free. Every rational-valued orbit therefore has a cutoff N0 and a positive modulus t with T_M - T_N in Z iff M == N mod t beyond N0 (exists_free_pair_lattice), in particular the rational candidate tail of every proposed rational value S of the prime-gap series. (P) is formalised as CofinalFreePairNonintegral T: for every t > 0 and every cutoff there are N, M beyond the cutoff with N == M mod t and T_M - T_N not an integer. Lean proves Irrational (T 0) <-> (P) for every real integer-digit dyadic tail orbit, that (P) is equivalent to the fixed-offset criterion CofinalNonintegralTailShifts, and, with the real tail primeGapRealTail N = 2^(N+1) sum_k g_(k+N+1)/2^(k+N+2) satisfying the recurrence with the actual prime gaps as digits and primeGapRealTail 0 = 2S - 1, that Irrational S <-> CofinalFreePairNonintegral primeGapRealTail for the actual consecutive-prime-gap series S.

Evidence/status: lean_checked_exact_equivalence

- [FreePairReduction.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/FreePairReduction.lean)

claim_boundary: Exact equivalence only. Nothing produces the congruent nonintegral pairs for the actual primes; Erdős #251 remains open. The modulus in the rational direction is orderOf(2 : ZMod d), which need not equal the totient used in earlier rows.

surviving_obligation: Produce, for every positive modulus t and every cutoff, a congruent pair of indices beyond the cutoff with nonintegral real tail difference for the actual prime gaps.

### kernel_denominator_floor

Every rational a/b equal to the zero-based prime series S = sum_{i>=0} p_i/2^(i+1) (p_0 = 2), and every rational equal to the prime-gap series S - 2 of Erdos #251, has denominator b >= 2^589 > 10^177. The floor is decided inside the Lean kernel: cert_10000 re-runs the 10^4 trial-division sieve with decide +kernel (no native_decide) and certCheck packages the four Farey inequalities around the bracket [prefix, prefix + 5000(c+1)^4/2^(c+1)]; the certificate c = 1229, X = 10000 comes from formal_math/probes/erdos251_kernel_denominator_certificate.py. Evidence class: kernel-checked Lean theorem (KernelDenominatorFloor.lean, commit 460934798b), strictly weaker than and distinct from the continued-fraction receipt q > 10^12041.

Evidence/status: lean_checked

- [KernelDenominatorFloor.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos251/KernelDenominatorFloor.lean)
- [erdos251_kernel_denominator_certificate.py](formal_math/probes/erdos251_kernel_denominator_certificate.py)

claim_boundary: A finite denominator exclusion only. It does not decide irrationality of the prime series or of the prime-gap series, and it is numerically weaker than the continued-fraction receipt q > 10^12041; its distinction is that the floor is decided inside the Lean kernel.

## Known failed routes

State compression does NOT close the route by word repetition, and the margin is recorded so the lane is not re-walked. Splitting the >>X/log X indices sharing one tail value v by their next L gaps costs at most 2^i v choices at step i, because T_(N+i) >= 2 forces g_(N+i) <= 2^i v; the product 2^(L(L+1)/2) v^L reaches X/log X only at L about 1.7 sqrt(log X). A repeated gap word of that length is well below the birthday threshold L about log X / log log X, so it is expected rather than contradictory.

Rationality controls only a fractional orbit and does not imply eventual periodicity of prime gaps.

Unbounded carries invalidate the automaticity shortcut.

Finite insertion of any fixed even gap word cannot establish a contradiction.

Global convergence of every fixed tail shift to zero is not required by the new consumer: cofinally many adjacent small-mismatch certificates suffice.

The data-dependent affine-cylinder escape is exactly the original integrality predicate at its basepoint, so changing depth or auditing more blocks cannot make it an independent producer.

Replacing the affine cylinder by the fixed lattice 2^r Z does not repair the mechanism under any dyadically dominated terminal bound: denominator separation forces the alleged escape from basepoint nonintegrality alone.

Positivity, evenness, polynomial growth, unboundedness, and nonperiodicity of a gap word do not force the h=1 adjacent-small-mismatch producer. The exact rational polynomial orbit g_n=2(n^2+4n+2), T_n=2(n+4)^2 has all those properties but every adjacent gap difference is 4n+10, never ±2.

No gap-magnitude, growth or periodicity theorem can supply the remaining producer, and the measurement now shows why looking for one was the wrong shape: the producer's event already occurs densely in the actual primes, so what is missing is a fixed-offset prime-gap correlation lower bound, not a bound on how large or how regular the gaps are.

## Open implications

### cofinal_adjacent_small_mismatch

For each fixed h >= 1 and every N0, produce N >= N0 such that both actual tail shifts T_(N+h)-T_N and T_(N+h+1)-T_(N+1) lie strictly between -1 and 1 while g_(N+h+1) != g_(N+1). The checked finite consumer then excludes eventual integrality of the h-shift.

Evidence/status: see the source; no formal status inferred


### actual_scaled_tail_smallness

Prove the required strict smallness for fixed differences of the actual scaled real tails. Convergence, the rational witness extraction, the exact real-to-rational tail equality, recurrence, and complete rational-denominator reductions are discharged; this is now the only analytic producer.

Evidence/status: see the source; no formal status inferred


### prime_theorem_to_local_smallness

Identify a theorem on consecutive primes strong enough to supply cofinally many adjacent small tail-shift pairs or another genuinely external fractional-tail obstruction. Isolated occurrence of a finite gap word is insufficient because both full infinite tails enter the inequalities, while adaptive and fixed-lattice block pullbacks are now Lean-checked circular.

Evidence/status: see the source; no formal status inferred


### cofinal_free_pair_nonintegrality

(P): for every positive modulus t and every cutoff, produce indices N, M beyond the cutoff with N == M mod t whose real scaled tails of the actual prime-gap series differ by a non-integer (CofinalFreePairNonintegral primeGapRealTail). Lean proves this is exactly equivalent to irrationality of the prime-gap series (irrational_primeGap_tsum_iff_cofinalFreePairNonintegral, row free_pair_lattice_and_irrationality_equivalence), so it is a restatement of the target, not a stronger sufficient input: the offset M - N is free and only one non-integral difference per (t, cutoff) is required.

Evidence/status: see the source; no formal status inferred
