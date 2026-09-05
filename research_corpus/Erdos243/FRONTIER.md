# erdos_243 mathematical frontier

Generated from the exported research packet. Read the strongest applicable
result before attempting a proof; superseded results remain history.

Under a_{n+1}/a_n^2 -> 1 and rational reciprocal sum, force eventual Sylvester recurrence.

## Established results and their evidence

### product_cleared_tail_dynamics

C_{n+1}=a_n C_n-D_n=C_n-E_n and Delta_n C_{n+1}=a_n^2 E_n-E_{n+1}.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)
- [ReciprocalTailRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean)

claim_boundary: The named declarations establish the exact local recurrence for the cleared tail state and the Sylvester-defect identity under their explicit integer hypotheses. They do not, by themselves, establish eventual return, exclusion of every negative-support orbit, the full #243 counterexample, or any asymptotic conclusion beyond these identities.

### centered_zero_forces_sylvester_step

If two consecutive centered errors vanish and the next product-cleared tail state is nonzero, the exact defect identity forces a_(n+1)=a_n^2-a_n+1.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)
- [ReciprocalTailRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean)

### eventual_centered_zero_forces_sylvester_recurrence

Along the exact product-cleared D/C orbit, eventual centered-state zero plus eventual nonvanishing of the next tail state forces a_(n+1)=a_n^2-a_n+1 eventually.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)
- [ReciprocalTailRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean)

### scale_equivariance

The D/C/E integer-state dynamics commute with common scaling, eliminating duplicate obstruction searches.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)
- [ReciprocalTailRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean)
- Declaration locators not uniquely resolved: nextDenState_scale, nextTailState_scale, centeredState_scale.

### eventual_nonnegative_state_rigidity

A nonnegative natural tail state satisfying C_{n+1}+E_n=C_n has E_n=0 eventually.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### gap_product_criterion

Eventual Sylvester recurrence is equivalent to eventual nonnegativity of the exact normalised gap-product state.

Evidence/status: advisory_complete_proof_pending_lean


### one_sided_sylvester_closure

Under rationality, the eventual tail cap, nonnegative gap, lower Sylvester step, and exact Sylvester recurrence are equivalent.

Evidence/status: advisory_complete_proof_pending_lean


### lcm_weighted_undershoot

If (L_{n-1}/a_n)*(a_n^2/a_{n+1}-1)_+ tends to zero, rationality forces eventual Sylvester recurrence.

Evidence/status: primary_source_corollary_matched_displayed_term_reindex_checked_pending_formal_transport


### subcritical_one_over_n_threshold

limsup n*(a_n^2/a_{n+1}-1)_+ < 1 is a sufficient strengthened hypothesis.

Evidence/status: superseded_by_one_over_n_threshold_verified

Superseded by **one_over_n_threshold_verified**. Use that stronger result.


### finite_horizon_factorial_residue_reduction

Survival through H constant-negative updates depends only on a_0 modulo (H+1)!, and can be propagated through shrinking factorial moduli without constructing the double-exponential orbit.

Evidence/status: lean_checked

- [FiniteHorizonResidue.lean](problem/FiniteHorizonResidue.lean)

### constant_negative_orbit_excluded

No eventually constant negative centered state exists. After removing gcd(C_0,|E|), every a_j would need a prime divisor of fixed |E|, but a prime used by one a_j forces every later a_k to be 1 modulo that prime; finite pigeonhole gives a contradiction. The normalized E=-1, C_0=1 branch also has the shorter contradiction at n=a_0-1.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### eventually_periodic_negative_magnitude_excluded

No positive eventually periodic negative-state magnitude survives in the exact natural tail regime e_n<a_n. If one prime divisor of the period drift occurs in two multipliers, it locks the entire later D/C/e tail; periodicity propagates that divisor to every phase. Finite-prime pigeonhole excludes the phase-primitive case, and strong induction after dividing out any common prime scale excludes every scale.

Evidence/status: lean_checked

- Declaration locators not uniquely resolved: no_phasePrimitivePeriodicNegative_orbit, no_periodicNegative_orbit, no_eventuallyPeriodicNegative_orbit.

### bounded_rise_reduced_tail_excluded

No exact reduced tail u_(n+1)+v_n=a_n*u_n, v_(n+1)=a_n*v_n with gcd(u_n,v_n)=1 can have u_n tend to infinity while u_(n+1)<=u_n+B for a fixed positive B. Reduced exactness forces pairwise-coprime multipliers and permanent whole-modulus avoidance; a shifted CRT block and first-crossing argument give the contradiction.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### cofinally_bounded_negative_branch_excluded

For the exact natural D/C tail, cofinally occurring positive negative-state magnitudes bounded by B force the divisibility-monotone gcd(C_n,D_n) to stabilise. Division by the stable gcd gives the reduced cocycle; division-free normalised vanishing of a globally nonzero magnitude forces C_n to tend to infinity; the CRT theorem then excludes the branch.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### bounded_negative_part_rigidity

Under exact natural D/C dynamics, eventual strict centring |E_n|<C_n, division-free normalised vanishing E_n/C_n->0, and eventual boundedness of (-E_n)_+, the signed centered state satisfies E_n=0 eventually; the composed boundedNegativePart_sylvesterNext_eventually consumer then yields a_(n+1)=a_n^2-a_n+1 eventually. Periodicity is not assumed. The proof derives zero absorption from the exact defect identity, sends the eventually nonnegative branch to natural-tail stabilisation, and sends the cofinally negative branch through gcd stabilisation, scale reduction, and the shifted CRT barrier. These hypotheses remain conditional and do not settle Erdős #243.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### dynamic_cancellation_payment

At every dynamically reduced exact tail step, with h_n=G_(n+1)/G_n and v_n=D_n/G_n, gcd(a_n,v_n) divides h_n and h_n divides gcd(a_n,v_n)^2. The source also kernel-checks the actual quotient cocycle h_n*u_(n+1)+v_n=a_n*u_n and h_n*v_(n+1)=a_n*v_n, plus h_n=1 iff a_n is coprime to v_n. Thus every gcd-growth step is exactly an old-prime reuse event.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### strict_gcd_growth_exponential_budget

For any positive divisibility chain G, if r strict increases occur in a finite interval then 2^r times the initial value is at most the endpoint value. Applied to G_n=gcd(C_n,D_n), this is the exact finite arithmetic core behind the advisory density-zero cancellation claim.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### strict_gcd_growth_sublinear_under_subexponential_tail

If every fixed power of a positive divisibility chain G_n is eventually below 2^n, then its strict-growth count is sublinear in the division-free form K*count(n)<n. For the exact D/C tail, the same conclusion holds for G_n=gcd(C_n,D_n) under the corresponding power-vs-2^n subexponential bound on C_n.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### local_near_unit_tail_growth_from_normalized_vanishing

The exact identity C_(n+1)=C_n-E_n and the pointwise normalized bound K*|E_n|<C_n directly imply K*C_(n+1)<(K+1)*C_n. Hence division-free normalized vanishing supplies this near-unit growth inequality eventually for every fixed K, with no density or limiting claim hidden in the step.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### subexponential_tail_from_near_unit_growth

If every prescribed integer rate eventually bounds one-step growth by q*C_(n+1)<(q+1)*C_n, then every fixed power C_n^K is eventually below 2^n. The proof chooses q with (q+1)^K<2*q^K, iterates the denominator-cleared inequality, and absorbs the finite prefix by geometric domination.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean)
- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### sublinear_tail_gcd_growth_from_normalized_vanishing

Along the exact positive natural D/C orbit, division-free normalized centered-state vanishing implies subexponential tail growth and therefore K times the strict-growth count of gcd(C_n,D_n) is eventually below n for every positive K. This is the complete kernel-checked consumer of the finite 2^r budget.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### arbitrarily_late_constant_tail_gcd_blocks

Sublinear strict-growth count forces arbitrarily late finite blocks with no strict-growth transitions. For a positive divisibility chain these blocks are constant, so normalized centered-state vanishing yields arbitrarily late blocks on which gcd(C_n,D_n) is exactly constant. This is a structural block producer, not a contradiction: the finite E=-1 family shows that block length alone cannot close the problem.

Evidence/status: lean_checked

- [ReciprocalTailRigidity.lean](problem/ReciprocalTailRigidity.lean)

### primitive_raw_next_coprimality_and_square_content

For a primitive reduced input q+v=a*u with gcd(u,v)=1, gcd(u,q)=1 and gcd(q,a*v)=gcd(q,a^2). More precisely, for d=gcd(a,v), the removed content is d*gcd(q/d,d). Thus the full content is controlled exactly by the square of the current multiplier, rather than only by a divisibility sandwich.

Evidence/status: lean_checked

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### primitive_numerator_second_order_recurrence

Two consecutive dynamically reduced steps satisfy a_n^2*u_n+h_n*h_(n+1)*u_(n+2)=h_n*(a_n+a_(n+1))*u_(n+1), while consecutive primitive numerators are coprime. This is the exact non-autonomous recurrence underlying the block-matrix and anti-shadowing routes.

Evidence/status: lean_checked

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### square_cancellation_normal_form

The source kernel-checks the quotient overlap formula and the quotient-free normal-form core: from a=d*alpha, q=d*omega, gcd(alpha,omega)=1, c=gcd(omega,d), d=b*c, and h=gcd(q,a^2), derive h=b*c^2, a=b*c*alpha, gcd(c,alpha)=1, denominator transport, c=v/gcd(v,vNext), and lcm(a,v)=c*vNext. A single convenience wrapper that manufactures every named quotient factor remains open, but the mathematical identities themselves are checked.

Evidence/status: lean_checked_explicit_factor_core_wrapper_open

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### cancellation_free_dual_remainder

On a cancellation-free step, the defect relation and p_(n+1)=p_n-e_n imply the exact signed identity (a_n^2-1+Delta_n)e_n-Delta_n*p_n=e_(n+1)-e_n. This is the changing-modulus residue interface for anti-shadowing.

Evidence/status: lean_checked

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### cancellation_free_curvature_square

The primitive second-order recurrence implies q_n^2+J_n=(a_(n+1)-a_n)p_n*p_(n+1), with q_n=a_n*p_n-p_(n+1) and J_n=p_n*p_(n+2)-p_(n+1)^2. The identity is exact but does not itself contradict the sharp quadratic approximation.

Evidence/status: lean_checked

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### excursion_matrix_square_determinant

For K=A-(a_r-1)B, alpha=A+(a_s-1)B, and beta=A(a_r-1)-(a_s-1)K, the centered-state excursion matrix [[alpha,beta],[-B,K]] has determinant alpha*K+beta*B=A^2.

Evidence/status: lean_checked

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### primitive_matrix_exact_gcd_payment

For a primitive integer input vector (x,y) and primitive second matrix row (r,s), gcd(px+qy,rx+sy)=gcd(ps-qr,rx+sy). This is the generic exact determinantal payment theorem consumed by the block-specific quotient result.

Evidence/status: lean_checked

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### excursion_block_exact_cancellation_payment

For the exact excursion data K=A-(a_r-1)B, alpha=A+(a_s-1)B, beta=A(a_r-1)-(a_s-1)K, sigma=gcd(A,B)>0, primitive reduced endpoint states, and common transfer scale Lambda, the source proves |Lambda|=sigma*gcd((A/sigma)^2,(K*u-B*e)/sigma). It derives gcd(B,K)=sigma, divisibility of every matrix entry by sigma, primitivity of the divided second row, and cancellation of the common sigma^2 from the square determinant inside Lean. At negative endpoints the signed coordinate is K*u+B*m.

Evidence/status: lean_checked

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### excursion_payment_multiplicative_accumulation

For any sequence of exact block scales Lambda_i satisfying Lambda_i*G_(t_i)=G_(t_(i+1)), the product of the first m payments times G_(t_0) is exactly G_(t_m). If G is bounded by a power-vs-2^n subexponential tail state C, then every fixed power of that whole payment product is eventually below 2^(t_m). This is the division-free multiplicative form of sublinear logarithmic cancellation mass. It budgets all sparse payments but does not itself force a contradiction.

Evidence/status: lean_checked

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### square_residue_record_payment

Whenever scale growth GStop=Lambda*GStart carries a larger scale-weighted record, the primitive magnitude satisfies mStart<Lambda*mStop. Substituting the exact excursion payment Lambda=sigma*gcd(A0^2,z) makes the square-residue gcd payment explicit. This is the order-theoretic record consequence of the determinant calculation, not a global exclusion of sparse large records.

Evidence/status: lean_checked

- [DynamicCancellation.lean](problem/DynamicCancellation.lean)

### sparse_reset_recovery_forest

First-recovery intervals are laminar. Every reset recovery contains a reset-aligned clean recovery obtained from its last reset, with arbitrary nesting handled exactly; distinct clean recoveries are ordered and disjoint.

Evidence/status: lean_checked

- [SparseResetRecovery.lean](problem/SparseResetRecovery.lean)

### division_free_weighted_recovery_payment

If K*|e_(r+i)|<u_(r+i) along a positive reduced interval, then K^L times the complete reset-factor product times u_(r+L) is strictly below (K+1)^L*u_r. At a recovery the endpoint height cancels, and on a clean recovery the product reduces exactly to the initial reset h_r.

Evidence/status: lean_checked

- [SparseResetRecovery.lean](problem/SparseResetRecovery.lean)

### summable_negative_relative_mass_termination

For the exact integral update C_(n+1)=C_n-E_n with positive C, division-free normalized vanishing plus summability of natAbs(min(E_n,0))/C_n forces E_n=0 eventually. The proof bounds the finite products of 1+delta_n, hence bounds C_n, and then uses integrality.

Evidence/status: lean_checked

- [SparseResetRecovery.lean](problem/SparseResetRecovery.lean)

### summable_negative_mass_sylvester_consumer

Along the exact product-cleared reciprocal-tail D/C orbit, positive natural tail states, division-free normalized centered-state vanishing, and summability of natAbs(min(E_n,0))/C_n force the original denominator sequence to satisfy a_(n+1)=a_n^2-a_n+1 eventually. This paper-facing theorem directly composes finite-negative-mass termination with the checked centered-zero-to-Sylvester endpoint; no extra eventual nonvanishing hypothesis is required because positivity supplies it.

Evidence/status: lean_checked

- [SparseResetRecovery.lean](problem/SparseResetRecovery.lean)

### bounded_tail_normalized_vanishing_consumer

A uniformly bounded natural tail state together with division-free normalized vanishing of an integral centered state forces that state to vanish eventually.

Evidence/status: lean_checked

- [SparseResetRecovery.lean](problem/SparseResetRecovery.lean)

### strict_rise_crt_barrier

A natural state tending to infinity with upward increments bounded by B cannot, at every strict rise, avoid all earlier members of an infinite pairwise-coprime modulus family. The proof uses B old moduli, a shifted consecutive CRT block, and the first crossing; avoidance away from strict rises is not assumed.

Evidence/status: lean_checked

- [LcmCriticalBoundary.lean](problem/LcmCriticalBoundary.lean)

### bounded_lcm_negative_arithmetic_core

For an exact LCM-state recurrence g_n U_(n+1)=U_n-V_n with V_n>=-B and centered identity V_n=D_n-(a_n-1)U_n, any old prime p>B is avoided by U_n at strict rises. Consequently the recurrence is inconsistent with U_n tending to infinity once an infinite pairwise-coprime family of such old primes is supplied. Derivation of that prime supply from the original analytic sequence hypotheses remains open in Lean.

Evidence/status: lean_checked_prime_supply_bridge_open

- [LcmCriticalBoundary.lean](problem/LcmCriticalBoundary.lean)

### weighted_lcm_block_debt_stabilisation

The exact multiplicatively weighted LCM recurrence telescopes over every finite block. Nonnegative endpoint debt plus a uniform within-block negative-debt bound makes U globally bounded along any proof-relevant cut partition; normalized integral digit vanishing then forces V_n=0 eventually.

Evidence/status: lean_checked

- [LcmCriticalBoundary.lean](problem/LcmCriticalBoundary.lean)

### primitive_finite_window_transfer

For the primitive recurrence u_(n+1)+v_n=a_n*u_n and v_(n+1)=a_n*v_n, define A as the finite block product and B by B_0=0, B_(k+1)=a_(r+k)B_k+A_k. Then u_(r+k)=A_k*u_r-B_k*v_r and v_(r+k)=A_k*v_r. Over the rationals this gives the exact saturated approximation identity u_r/v_r-B_k/A_k=u_(r+k)/(A_k*v_r) when both denominators are positive.

Evidence/status: lean_checked

- [PrimitivePrefixRigidity.lean](problem/PrimitivePrefixRigidity.lean)

### primitive_complete_prefix_overlap

For a complete primitive prefix with v_n=Q*A_n and centered error e_n=Q*A_n-(a_n-1)u_n, gcd(A_n,a_n-1) divides e_n. Consequently every earlier digit factor a_j with j<n contributes gcd(a_j,a_n-1) dividing e_n. This is an exact prefix-coherence constraint, not yet an unbounded anti-shadowing theorem.

Evidence/status: lean_checked

- [PrimitivePrefixRigidity.lean](problem/PrimitivePrefixRigidity.lean)

### reset_recovery_alignment_quantitative

The return supplies a quantitative refinement of last-reset clean-leaf extraction and subblock recovery alignment. Its qualitative alignment core is already Lean-checked in SparseResetRecovery; the new quantitative count has not yet been formalized.

Evidence/status: advisory_complete_pending_lean


### primitive_crt_limsup_rise_constant

The return proposes a strengthened primitive CRT consequence with limsup rise constant at least 1/log 2. The derivation depends on additional global growth bridges and is not used as a checked theorem.

Evidence/status: advisory_derivation_pending_growth_bridges_and_lean


### feedback_transport_realizability

The denominator-transport defect equals (u-e) times the failure of the centered quotient to generate the next multiplier. When u-e is nonzero, exact denominator transport holds if and only if aNext=a^2-a+1+Delta. Thus the square-residue congruence alone is strictly weaker than the true feedback orbit.

Evidence/status: lean_checked

- [FeedbackRealizability.lean](problem/FeedbackRealizability.lean)

### primitive_square_root_feedback

On a cancellation-free step, factorizations a*e=L*uNext+t and a*t=r*uNext+eNext, together with the square defect equation, force Delta=a*L+r. The same two quotients generate v=(a-1+L)uNext+t and aNext=a(a-1+L)+(r+1). The exact norm identity t^2-e*eNext=(r*e-L*t)uNext is also kernel-checked.

Evidence/status: lean_checked

- [FeedbackRealizability.lean](problem/FeedbackRealizability.lean)

### artificial_square_unit_not_realizable

For the artificial pattern a=u+2, e=-1, and centered quotient -(u+3), true feedback forces aNext=u(u+2). For u>=3 this differs from the fake linear continuation u+3, so the infinite square-residue model is formally separated from every realizable feedback orbit.

Evidence/status: lean_checked

- [FeedbackRealizability.lean](problem/FeedbackRealizability.lean)

### cumulative_lcm_overlap_relocation

Define the cumulative digit LCM Lambda_n, product-cleared scale D_n, and cumulative overlap debt M_n as the product of gcd(Lambda_j,a_j). Then M_n*Lambda_n=D_n at every finite horizon. Common content also factors as gcd(MY,M Lambda)=M*gcd(Y,Lambda), and any reduced payment h with G'=hG splits exactly as h*g=rho*g' when M'=rho*M. Thus LCM overlap is relocated into a permanent global scale rather than erased.

Evidence/status: lean_checked

- [GlobalLcmHeight.lean](problem/GlobalLcmHeight.lean)

### global_lcm_pseudo_euclidean_update

For F=Lambda-bY, a=b+1, and the raw lifted identity rho*YNext=aY-Lambda, Lean proves rho*YNext=Y-F. Its division-free amortized consumer shows K*rho*YNext<=(K+1)Y whenever K*(-F)<=Y, while positive F gives strict paid-height descent rho*YNext<Y.

Evidence/status: lean_checked

- [GlobalLcmHeight.lean](problem/GlobalLcmHeight.lean)

### returned_error_exact_telescope

For z=x-1/b, xNext=x-1/a, a=b+1, and bNext=a*b+Delta, the exact rational identity zNext=z+Delta/(a*b*bNext) holds whenever the three denominators are nonzero. This is an exact coordinate identity, not a well-founded termination measure.

Evidence/status: lean_checked

- [GlobalLcmHeight.lean](problem/GlobalLcmHeight.lean)

### returned_error_eventual_contraction

The return proposes that |zNext|/|z| tends to zero using normalized centering, subexponential reduced-numerator growth, and doubly exponential next-digit scale. The complete bridge into those hypotheses has not been formalized in the new module.

Evidence/status: advisory_pending_asymptotic_bridge_and_lean


### forced_excursion_mod13_cofinal_return_split

For the exact infinite clean-return family q0(k)=33+79833600*k, the forced 11->12 excursion has full height-12 payment 13 precisely for k mod 13 in {0,2,5,6,7,8,9,10}. Every lift in those eight classes collapses to primitive height one and hence enters the absorbing zero-centered Sylvester tail. Only k mod 13 in {1,3,4,11,12} survives to height 13.

Evidence/status: lean_checked_arithmetic_consumer_and_exact_polynomial_certificate

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### second_excursion_mod17_cofinal_return_split

On the surviving class k=1+13*t, the height-13 centered error is -4 and full payment 17 occurs precisely for t mod 17 in {8,9,13,14}, equivalently k mod 221 in {105,118,170,183}. Every lift in those four classes collapses to primitive height one and enters centered state zero forever; all thirteen complementary t-classes switch to centered error +2 or +4 at height 17, so none continues negative support. On the other four source classes modulo 13, height-13 payment is always 1 or 7 and never the full factor 14.

Evidence/status: lean_checked_arithmetic_consumer_and_exact_composite_modulus_certificate

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### payment_seven_boundary_cascade_cofinal_return

All sixteen height-13 payment-seven source classes modulo 182 have multiplier 7 modulo 42 and follow the universal cascade (13,-1)->(2,-1 tie)->(3,-1)->(1,0 forever), with payments 7,1,4. Thus every payment-seven cylinder reaches a cofinal Sylvester return; the height-two boundary mode is eliminated exactly.

Evidence/status: lean_checked_final_payment_and_exact_composite_modulus_certificate

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### payment_one_height_fourteen_sign_split

The 40 remaining payment-one cylinders refine into 600 classes modulo 2730. Exact quotient propagation traps w=q11/14 modulo 15 in {0,3}, so full payment 15 never occurs. All 240 w=3 classes pay five and switch to centered error +1 at height 3. All 360 w=0 classes pay one at heights 14 and 15 and reach height 16 with centered error -1. The height-14 homogeneous boundary mode is therefore split exactly, and only the height-16 subcylinders retain negative support.

Evidence/status: lean_checked_transition_identities_and_exact_composite_modulus_certificate

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### height_sixteen_mod17_cofinal_return_and_sign_split

The 360 height-16 cylinders refine into 6120 classes modulo 46410. Exact value-level quotient propagation restricts c mod 17 to {0,10,12}, with height-16 multiplier image {1,3,0}. The 1440 multiplier-zero classes pay 17 and collapse to the absorbing height-one tail; the 2520 multiplier-three classes switch to centered error +8 at height 17; only 2160 multiplier-one classes retain centered error -1.

Evidence/status: lean_checked_transition_identities_and_exact_complete_cylinder_certificate

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### height_seventeen_rigidity_and_height_eighteen_mod19_return

All 8640 mod-4 lifts of the 2160 height-17 cylinders have d=0 mod 4, so nontrivial payments 18, 9, and 2 are impossible: every lift pays one and reaches height 18 with error -1. The next multiplier image modulo 19 is exactly {0,1}; eleven of nineteen lifts per source class pay the full factor 19 and collapse to height one, while eight retain error -1 at height 19.

Evidence/status: lean_checked_transition_identities_and_exact_complete_cylinder_certificate

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### height_nineteen_payment_five_cofinal_return

The 69120 height-19 source classes refine into 691200 classes modulo 35271600. Their next parameter image modulo 10 is only {0,2,4,6,8}. The 184320 classes in residues {2,8} pay five, land at height four with centered error -1, then pay the full factor five and collapse to the absorbing height-one tail. The other 506880 classes pay one and reach height 20 with error -1.

Evidence/status: lean_checked_terminal_cascade_and_exact_complete_vectorized_cylinder

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### height_twenty_payment_seven_mode_elimination

The 506880 height-20 source cylinders refine into 10644480 classes modulo 740703600. Their complete payment image is {1,7}: 8211456 classes pay one, while 2433024 pay seven. Affine two-lift evaluation modulo 21 and 5 plus CRT classifies every quotient digit without evaluating the degree-1024 polynomial on every lift. All payment-seven classes are terminal for negative support: 2256075 return cofinally and 176949 switch positive. Only the payment-one classes reach height 21 with error -1.

Evidence/status: lean_checked_cascade_identities_and_exact_affine_complete_cylinder

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### height_twenty_one_payment_eleven_rigidity

The 8211456 height-20 survivors refine into 180652032 height-21 classes. Their quotient-parameter image modulo 22 is only {0,6}, so the payment image is exactly {1,11}: 120931560 classes pay one and reach height 22, while 59720472 pay eleven and land at height two. A complete three-lift refinement of the latter has singleton image r=6 mod 66; all 179161416 classes pay one at height two, reach height three with an even multiplier, pay the full factor four, and collapse to height one. The entire payment-eleven mode is eliminated by cofinal return.

Evidence/status: lean_checked_transition_identities_and_exact_affine_complete_cylinder

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### height_twenty_two_mod23_centered_state_split

The 120931560 height-22 source families logically refine into 2781425880 classes. Exact affine-period counting avoids materializing that expansion. The multiplier image modulo 23 is {0,1,15}: 2024012298 classes pay the full factor 23 and collapse to height one, 84115680 pay one but switch to centered error +5, and only 673297902 pay one and reach height 23 with error -1.

Evidence/status: lean_checked_transition_identities_and_exact_compressed_affine_residue_count

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

### height_twenty_three_factor24_singleton_mode

The 673297902 height-23 negative classes refine into 16159149648 logical lifts. Compression to 6699 joint affine source keys and 570 weighted height-22 keys plus generalized CRT modulo 255024 proves that every lift has divided quotient z=0 and multiplier 1 modulo 24. All generic payments 3,4,8,12,24 are absent; every class pays one and reaches height 24 with error -1.

Evidence/status: lean_checked_transition_identities_and_exact_weighted_key_composite_crt_count

- [CleanRecoveryLengthCounterexample.lean](problem/CleanRecoveryLengthCounterexample.lean)
- [CleanRecoveryLengthCounterexample.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CleanRecoveryLengthCounterexample.lean)

claim_boundary: This is a finite exact classification of the corrected height-23 source refinements. It does not classify the height-24 continuation or prove the unrestricted Erdos #243 theorem or eventual Sylvester recurrence.

### height_twenty_four_factor25_cofinal_opening

The 16159149648 height-24 negative classes refine into 403978741200 logical lifts. Exact reconstruction modulo 6375600 gives preceding-quotient image w mod 5={0,1,4}: the possible cofinal root w=2 is absent, but all 58762693440 realized w=4 lifts pay the full factor 25 and return cofinally. Another 23505077376 switch positive and 321710970384 remain negative. The generic error -9 mode is absent. This opens an actual cofinal mechanism and removes 20.364% of the incoming negative cylinder.

Evidence/status: lean_bound_full_payment_identities_and_exact_digest_cached_affine_census


### height_twenty_four_binary_parent_fiber_split

The complete parent-local factor-25 histogram has exactly two profiles. There are 10282880304 inert parents with 0 cofinal, 0 positive, and 25 negative children, eliminating uniform one-step contraction. The other 5876269344 active parents have exactly 10 cofinal, 4 positive, and 11 negative children. The retained source digit separates them exactly: t=0 mod 10 is inert and t in {4,6} is active; affine slope alone does not. All 257072007600 inert children have error -1, eliminating the error-specific raw factors 31 and 36 from the inert frontier and leaving only factor 26.

Evidence/status: exact_one_way_uniform_contraction_elimination_and_activation_route


### height_twenty_five_factor26_uniform_activation

The complete t=0, error=-1 inert subfamily refines into 6683872197600 logical factor-26 lifts. Exact aggregation reduces the actual parent support to 18 current-modulus residues, and exact comparison proves that the two new quotient parities have identical multiplier-residue multisets. Every one of the 257072007600 parents has immediate profile 0 cofinal, 4 positive, 22 negative, with multiplier multiset 1^8,13^14,15^4. The 14 multiplier-thirteen children then force height-two multiplier 150, full payment three, and cofinal return. Thus every effective parent profile is 14 cofinal, 4 positive, 8 negative, eliminating the all-negative boundary and contracting genuine continuation uniformly by 4/13. The preceding multiplier is odd, forcing the next multiplier odd and analytically eliminating immediate full factor-26 payment.

Evidence/status: lean_bound_parity_obstruction_and_exact_one_way_uniform_boundary_contraction


### height_twenty_six_factor27_singleton_mode

The 2056576060800 multiplier-one height-26 negative parents refine into 55527553641600 factor-27 lifts. Exhausting all 18 parent residues, both possible factor-26 quotient parities, four distinct surviving targets per parity, and all 27 source lifts gives the singleton images C=1 mod 702 and D=1 mod 27 on all 3888 source samples. Hence every logical refinement pays one and reaches height 27 with centered error -1; every generic factor-27 activation mode is absent.

Evidence/status: lean_bound_multiplier_identity_and_exact_complete_source_lift_elimination


### height_twenty_seven_factor28_uniform_activation

All 55527553641600 actual height-27 negative parents have the same factor-28 profile: 0 cofinal, 8 positive, and 20 continuing-negative children. Exhausting 108864 source samples gives q mod 28 in {0,4,12} and next multiplier E mod 28 in {1,21}. The q=4 class alone gives E=21, payment seven, height four, and centered error +1; q=0,12 give multiplier one and continue at height 28 with error -1. Thus factor 28 uniformly opens a positive-switch mechanism and contracts negative support by 5/7.

Evidence/status: lean_bound_residue_identities_and_exact_one_way_uniform_sign_switch


### height_twenty_eight_factor29_uniform_boundary_killing

All 1110551072832000 actual height-28 negative parents have the same factor-29 profile: 8 cofinal, 6 positive, and 15 continuing-negative children. Exhausting 2255040 source samples gives the quotient multiset 0^7,15^8,24^8,25^4,27^2 modulo 29. Class 15 forces full payment 29 and cofinal return; classes 25 and 27 switch positive; classes 0 and 24 survive with errors -1 and -6. Thus factor 29 kills the homogeneous boundary mode uniformly with continuation ratio 15/29 and splits the next frontier into raw factors 30 and 35.

Evidence/status: lean_bound_residue_identities_and_exact_one_way_uniform_cofinal_activation


### height_twenty_nine_factor30_35_exact_split

All 544320 actual (29,-1) source families are constant G=1 mod 30 and have profile (0,0,30), eliminating factor 30 as an activation mechanism. The 622080 actual (29,-6) families split exactly 1/5 inert with profile (0,0,35) and 4/5 active with profile (0,25,10). Every affine summary is checked on its full composite-modulus lift cylinder. The factor-35 weighted negative continuation is 3/7, the factor-29-plus-split continuation is 73/203, and the formerly inert factor-25 activation chain now has continuation 1460/18473.

Evidence/status: exact_complete_source_cylinder_rigidity_and_stratified_activation


### height_thirty_thirtyfive_factor31_41_field_activation

After exact transport of the height-29 multiplier into the declared parent state, every actual (30,-1) parent has factor-31 profile (4 cofinal,0 positive,27 negative), and every actual (35,-6) parent has factor-41 profile (2,39,0). All prior quotient divisors and both next source strides are units in the respective prime fields, so one complete 31-point or 41-point table transfers to every actual parent. Factor 41 kills the entire negative factor-35 branch. The factor-29 continuation is 189/899 and the formerly inert factor-25 chain continuation is 540/11687.

Evidence/status: exact_unit_stride_field_permutation_cofinal_return_and_branch_extinction


### height_thirtyone_error10_factor41_cofinal_activation

Every actual (31,-10) parent has corrected factor-41 profile (8 cofinal,21 positive,12 negative). The universal multiplier image contains zero eight times. Processing this multiplicity-eight factor-31 mode lowers that branch's effective continuation to 875/1271, the factor-29-through-current continuation to 6125/36859, and the formerly inert factor-25 chain continuation to 17500/479167.

Evidence/status: exact_unit_stride_field_permutation_and_uniform_cofinal_return


### height_fortyone_error20_factor61_cofinal_activation

Every actual (41,-20) parent has corrected factor-61 profile (4 cofinal,6 positive,51 negative). The universal multiplier image 0^4,4^9,18^10,28^6,31^14,33^2,43^10,45^6 contains four full-payment residues. Processing the multiplicity-four child gives factor-41 error-minus-ten continuation 692/2501, factor-31 continuation 53055/77531, factor-29-through-current continuation 371385/2248399, and formerly inert factor-25 chain continuation 1061100/29229187.

Evidence/status: exact_unit_stride_field_permutation_and_uniform_cofinal_return


### common_divisor_persistence_and_multiplier_overlap

Along the exact natural orbit from index N, a common divisor of C_n and D_n divides every later C_t and D_t and hence every later centred error E_t = D_t - (a_t - 1)C_t. In particular gcd(a_n, D_n) divides E_t for every t > n. On any counterexample, where E_t is eventually nonzero, the overlap of each multiplier with the accumulated denominator is therefore at most |E_t| for every later t, and at most the next negative magnitude.

Evidence/status: lean_checked

- [SlowRiseBarrier.lean](problem/SlowRiseBarrier.lean)
- [SlowRiseBarrier.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/SlowRiseBarrier.lean)

claim_boundary: Unconditional integer persistence; it neither bounds the overlap by itself nor excludes any orbit alone.

### bounded_crt_block

For pairwise coprime moduli m_0..m_{B-1} > 1 with product P there is x with P <= x < 2P and m_r | x + r for every r < B.

Evidence/status: lean_checked

- [SlowRiseBarrier.lean](problem/SlowRiseBarrier.lean)
- [SlowRiseBarrier.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/SlowRiseBarrier.lean)

claim_boundary: Finite CRT statement with an explicit height bound; it replaces the unbounded shift of exists_shifted_consecutiveMultiples.

### slow_rise_landing_barrier

Let T >= N, let m_0..m_{B-1} > 1 be pairwise coprime divisors of D_T with product P, let C_T < P, let C tend to infinity, and let C_{n+1} <= C_n + B at every n >= T with C_n < 2P. Then some C_{s+1} < 2P + B is divisible by a block modulus m_r, which then divides every later C_t, D_t and E_t (slowRise_landing). If moreover negative errors are cofinal and every negative error at t >= T with C_t < 2P + B is smaller than every m_r, there is a contradiction (no_slowNegative_of_coprimeBlock). No gcd stabilisation, periodicity or bounded negative part is assumed.

Evidence/status: lean_checked

- [SlowRiseBarrier.lean](problem/SlowRiseBarrier.lean)
- [SlowRiseBarrier.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/SlowRiseBarrier.lean)

claim_boundary: The rise bound is only required below 2P and the negative bound only below 2P + B; the choice of moduli on the canonical orbit and the log-log threshold are the ordinary-proof transfer in SlowNegativePartRigidity.md, not formalised.

### slow_rise_reduced_tail_excluded

No reduced exact tail (a,u,v) from index N with a_n > 1 and u_n tending to infinity can, for some B, satisfy u_{N+B} < prod_{i<B} a_{N+i} = P together with u_{n+1} <= u_n + B at every n >= N+B with u_n < 2P. This generalises no_boundedRise_reducedTail from a uniform rise bound to a rise bound required only below twice the product of B consecutive multipliers.

Evidence/status: lean_checked

- [SlowRiseBarrier.lean](problem/SlowRiseBarrier.lean)
- [SlowRiseBarrier.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/SlowRiseBarrier.lean)

claim_boundary: Reduced-tail theorem; it does not by itself supply the hypotheses on the canonical orbit.

### slow_negative_part_rigidity

Under the exact natural dynamics, positivity and division-free normalised vanishing, if for some delta in (0,1) every negative centred error eventually satisfies -E_n <= (1 - delta) log2 log2 C_n, then E_n = 0 eventually and a_{n+1} = a_n^2 - a_n + 1 eventually. The bounded-negative-part theorem is the constant-bound special case. Proof (Theorem 4 of the note): persistence bounds every multiplier overlap gcd(a_n, D_n) by the next negative magnitude, so at most log2 log2 C_n + 1; a burn count on the primes below that bound shows that all but O(T) indices in [T, 2^T] carry a new part above any fixed threshold; B such new parts are pairwise coprime divisors of D_{n_B+1} with product P satisfying log2 log2 (2P + B) <= 2T + B + O(1); the Lean landing theorem then contradicts the slow bound.

Evidence/status: ordinary_proof_over_lean_core

- [SlowNegativePartRigidity.md](problem/SlowNegativePartRigidity.md)
- [SlowNegativePartRigidity.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/SlowNegativePartRigidity.md)

claim_boundary: Conditional on normalised vanishing (supplied on the canonical orbit by Koizumi Cor. 10) and on the slow-negative hypothesis; the burn count and the transfer are ordinary proofs; Erdos #243 remains open.

### counterexample_loglog_negative_excursions

For the canonical state of any counterexample to Erdos #243, limsup_n (-E_n)_+ / log2 log2 C_n >= 1, and gcd(a_n, D_n) <= -E_t at the first negative index t > n. This is a quantitative strengthening of the frontier-profile clause limsup (-E_n) = infinity.

Evidence/status: ordinary_proof_over_lean_core

- [SlowNegativePartRigidity.md](problem/SlowNegativePartRigidity.md)
- [SlowNegativePartRigidity.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/SlowNegativePartRigidity.md)

claim_boundary: Necessary conditions on a counterexample; the constant 1 is the CRT-block constant of the method, not a proved sharp threshold for the problem.

### erdos_straus_quantity_bounded_form

Let Q_n = (a_1...a_{n-1}/a_n)(a_n^2/a_{n+1} - 1). If a_{n+1}/a_n^2 -> 1, sum 1/a_n is rational and limsup Q_n < infinity, then the sequence is eventually Sylvester; Erdos-Straus (product form, Koizumi Cor. 20(1)) require limsup Q_n <= 0. In Koizumi's coordinates Q_n = -(B_{n-1}/c_1) e_n + o(1), so the hypothesis is exactly a bounded negative part. The Erdos-Straus LCM quantity is Q_n / M_n with M_n | c_n exact.

Evidence/status: ordinary_proof

- [SlowNegativePartRigidity.md](problem/SlowNegativePartRigidity.md)
- [SlowNegativePartRigidity.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/SlowNegativePartRigidity.md)

claim_boundary: Original-coordinates form of the Lean-checked bounded-negative theorem composed with Koizumi's bridge; the LCM-prefactor strengthening limsup Q_n/M_n < infinity is not claimed.

### one_over_n_threshold_verified

If a_{n+1}/a_n^2 -> 1, sum 1/a_n is rational and limsup n (a_n^2/a_{n+1} - 1)_+ < 1, then the sequence is eventually Sylvester. The constant 1 is exactly the boundary of the Erdos-Straus method: the constant-negative template e_n = -1, c_n = c + n has n(-e_n)/c_n -> 1 and is excluded only by the prime-lock theorem. The hypothesis forces (-e_n)_+ <= C n^{-delta} -> 0, hence e_n >= 0 eventually (Koizumi Prop. 19(2)).

Evidence/status: ordinary_proof

- [SlowNegativePartRigidity.md](problem/SlowNegativePartRigidity.md)
- [SlowNegativePartRigidity.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/SlowNegativePartRigidity.md)

claim_boundary: Weaker than slow_negative_part_rigidity (its hypothesis implies a vanishing negative part); recorded as the explicit-constant sufficient condition in the language of the original problem; sharp for the method, not for the problem.

### cumulative_overlap_debt_divides_tail_numerator

With the unreduced tail C_n/D_n, the cumulative LCM scale Lambda_n and the overlap debt M_n=D_n/Lambda_n, the debt divides both the tail numerator and the centred state: M_n|C_n and M_n|E_n. Hence U_n=C_n/M_n and V_n=Lambda_n-(a_n-1)U_n are integral and satisfy the exact system rho_n U_(n+1)=U_n-V_n with rho_n=gcd(Lambda_n,a_n). The divisibility follows from the additive update alone: M_(n+1)=M_n rho_n divides a_n C_n through rho_n|a_n and divides D_n through rho_n|Lambda_n with M_n Lambda_n=D_n, so no subtraction and no positivity hypothesis enters.

Evidence/status: lean_checked

- [CumulativeLcmTransfer.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CumulativeLcmTransfer.lean)

claim_boundary: Exact identities for the LCM-normalized coordinates under explicit integer hypotheses. They establish integrality of the normalized state and its recurrence; they establish nothing about eventual return, the sign or size of V_n, or Erdos #243, and are not asymptotic.

### lcm_freshness_budget_and_pairwise_coprimality

Counting the steps with rho_n>1 by R(n) gives 2^R(n)<=M_n, and with 0<C_n also 2^R(n)<=C_n. Composed with the landed subexponential tail bound this gives R(n)=o(n): the LCM-fresh steps have density one. Any step with rho_j=1 has a_j coprime to every earlier multiplier, so the fresh multipliers form a pairwise-coprime family of whole moduli already present in the cumulative denominator. Freshness at the earlier index is not needed; only rho_j=1 at the later.

Evidence/status: lean_checked

- [CumulativeLcmTransfer.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CumulativeLcmTransfer.lean)

claim_boundary: The budget inequality genuinely requires 0<q and a_n>0: with a zero multiplier Lambda_n, rho_n and M_n all vanish and the bound is false. Density one is a counting statement about the multiplier sequence; it supplies moduli and excludes no orbit.

### normalised_coordinate_fresh_block_barrier

Given B pairwise-coprime moduli each exceeding B, all dividing Lambda_s for every s at or beyond T, the exact normalized step and centring identities, U_T below their product, a negative-part bound -B<=V_n on states with U_n below twice that product plus B, and U_n->infinity, a contradiction follows at the first crossing. The instantiated form takes the moduli to be the multipliers at LCM-fresh indices before T.

Evidence/status: lean_checked

- [CumulativeLcmTransfer.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/CumulativeLcmTransfer.lean)

claim_boundary: This is the shifted-CRT first-crossing barrier stated in the NORMALIZED (U,V,rho) coordinates. The raw-coordinate analogues were already landed: LcmCriticalBoundary.no_boundedNegative_lcmState_of_oldPrimeSupply is the same first-crossing contradiction for the LCM-cleared state, and SlowRiseBarrier.exists_consecutiveMultiples_between with slowRise_landing and no_slowNegative_of_coprimeBlock already supply the finite block with whole pairwise-coprime moduli and a rise bound needed only below 2P. What was missing, and what this adds, is the barrier for U, which does not satisfy the raw recurrence those consume. The analytic placement lemma - that B fresh moduli all exceeding B are present by time B+o(B) - is NOT formalized, and U_n->infinity is carried as a hypothesis throughout. This is a conditional barrier, not an exclusion of any orbit, and Erdos #243 remains open.

### fresh_prime_first_contact_requires_single_step_valuation_resonance

If a_j is LCM-fresh and p^e exactly divides a_j, first later contact p|U_t requires t>=j+2 and v_p(a_(t-1))=v_p(Lambda_(t-1))>=e. Thus the entire source prime power must be paid in one overlap step, with residual-unit cancellation modulo p; many smaller payments cannot create first contact. Whole-modulus retirement and disjoint CRT-wall cumulative bounds follow.

Evidence/status: ordinary_proof_verified_not_lean_formalized

- [R2CumulativePayment.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/R2CumulativePayment.md)

claim_boundary: Necessary contact condition, not a frequency theorem; global overlap-growth production remains open.

### strict_rise_loglog_lcm_ordinary_rigidity

Under the canonical exact LCM orbit and quadratic-growth hypotheses, if some delta in (0,1) bounds -V_n by (1-delta) log_2 log_2 max(4,U_n) at every sufficiently late strict rise, the orbit is eventually zero. The exact Q_n bridge shows finite upper limsup Q_n/M_n implies eventual Sylvester recurrence. Two consecutive gcd-payment-free steps force -u_n u_(n+2) to be a unit square modulo u_(n+1).

Evidence/status: ordinary_proof_verified_not_lean_formalized

- [R2CumulativePayment.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/R2CumulativePayment.md)

claim_boundary: The log-log or LCM-prefactor bound is an extra hypothesis. The unrestricted parent remains open.

## Known failed routes

Arbitrary finite deviations can be followed by an exact Sylvester tail, so no finite-prefix rule settles the problem.

The reverse one-sided inequality makes the tail state nondecreasing and removes the stabilization argument.

The critical constant-negative template sits at the 1/n boundary of the rate theorem, but is nevertheless excluded at every scale by the prime-nonrecurrence argument.

Every positive eventually periodic negative magnitude is also excluded once the exact tail has e_n<a_n. A surviving critical obstruction must therefore be genuinely aperiodic (or evade the eventual natural-bound bridge).

The entire bounded negative-part regime, periodic or aperiodic, is now Lean-closed under exact natural D/C dynamics, eventual strict centring, and division-free normalised vanishing. Any surviving obstruction must have cofinally unbounded negative excursions or fail one of those bridges.

Pairwise coprimality and permanent modular avoidance alone do not exclude an unbounded aperiodic walk. Exact dynamic reduction adds the missing constraint: gcd growth can occur only by old-prime reuse, while normalized centered-state vanishing now kernel-checks subexponential tail growth and hence a sublinear strict reuse count. What remains is not a density slogan but a structural theorem forcing too many reuse events, or a contradiction on a sufficiently long cancellation-free block.

Arbitrarily long cancellation-free blocks are not by themselves contradictory. For every finite height H and sufficiently late tail start c, an exact integer family has C_n=c+n, E_n=-1, gcd(C_n,D_n)=1, gcd(a_n,D_n)=1, and h_n=1 throughout the block, while 0<(a_n^2-a_(n+1))/a_n^2<2/(C_n+1). The exact verifier is scripts/verify_erdos243_cancellation_free_blocks.py. Any successful sparse-reuse argument must therefore use global prefix coherence or a quantitative block-length-versus-CRT-barrier statement.

Successive negative records need not descend: an exact finite family amplifies -m to -t^2*m after an h=1 step while both normalized errors can be made small, then lands at zero. Therefore no one-step record monotonicity or local normalized-error threshold can close the problem.

A cleanly introduced multiplier factor can be erased completely by maximal square cancellation at the next step and then land at zero; arbitrary finite horizons of such deletion are compatible with the local equations. Therefore a static CRT prime budget or an unweighted count of cancellation events cannot be the missing invariant.

The advisory sub-log-log CRT extension in the latest return is not yet kernel checked and is not used as a theorem. Even if proved, it treats an eventual h=1 branch; the unrestricted obstruction permits sparse but unbounded square-cancellation resets.

The earlier recovery-alignment gap is closed: every reset recovery contains a last-reset clean leaf, and distinct clean leaves are disjoint. This still does not yield a CRT contradiction because newly introduced whole multipliers can lie far above the entire recovery scale.

The exact block payments telescope, so their full multiplicative product has subexponential mass in physical time. This closes the vague logarithmic-budget accumulation step but still permits arbitrarily sparse payments of unbounded size; a lower bound connecting each repaired CRT obstruction to enough payment mass remains necessary.

The finite-window transfer makes the rational approximation route exact rather than contradictory: u_r/v_r-B/A=u_s/(A*v_r). Fixed-width resultant, Pell-type, and rational-approximation estimates therefore saturate on exact finite fixtures, including the E=-1 cancellation-free families. Any closure must use coherence across unbounded complete prefixes or a quantitative reset-payment lower bound.

The changing-modulus square-residue congruence admits an infinite artificial E=-1 orbit, so it cannot be the global invariant by itself. The Lean-checked transport-defect equivalence and two-stage quotient feedback identify exactly what that fake orbit omits: denominator transport and next-multiplier generation.

The cumulative-LCM lift turns reduced square erasure into exact global overlap relocation, but this does not make the resulting real-valued potentials well-founded. A divergent sequence of individually vanishing negative-mass charges can still finance arbitrarily sparse repairs while cumulative overlap remains subexponential.

Clean negative-prefix length cannot be charged directly to the next reset by a universal exponential bound: an exact primitive orbit has eight consecutive negative h=1 steps, with errors [-1,-1,-1,-1,-1,-1,-1,-4], followed by error -7 and payment h=2<2^8.

Aggregating successive raw resets does not restore a length charge: an exact primitive orbit has clean negative run lengths 7 and 1 before payments 2 and 2, so the payment product 4 is below both the total clean length 8 and 2^8. This leaves lower bounds using globally aligned complete recoveries or prefix arithmetic coherence open.

Complete clean-recovery alignment alone does not restore a length charge: the exact primitive orbit from (u,v)=(11,362) has a first return of length 9, no interior reset, and complete payment 4<9<2^9. Nor does passing to a pair of consecutive clean recoveries restore a cumulative length charge: the orbit from (19,14684) has two length-3 recoveries with payment product 4<6<2^6. A viable lower bound must use unbounded prefix arithmetic or changing residue/prime/overlap data, not the lengths and payments of any fixed local recovery fixture.

The exact primitive negative-to-negative feedback seed (u,v)=(9,62) sends primitive scale 9 to 5 while negative mass doubles from 1 to 2. Therefore m/u^alpha strictly increases for every real alpha>=0 on the same valid transition. The entire one-step nonnegative homogeneous Lyapunov family is unavailable even after imposing true denominator transport, strict centering, primitivity, and increasing multipliers.

The nine-step complete normalized return at height 11 is not an isolated small-scale fixture: for every k>=0, the primitive state (11,11*(33+79833600*k)-1) follows the same clean recovery and returns from normalized mass 1/11 to 1/11. Large initial quotient or denominator scale therefore cannot rescue strict recovery-level normalized-mass descent.

The normalized-return family cannot directly concatenate itself: exact coefficient propagation gives q6/990=-36 mod 1152, and the last three exact transition equations force q9=41472 mod 82944. Because q9 is divisible by 12, its next payment at height 11 is exactly one and the next height is 12. Thus every immediate same-height clean-cylinder switch is also impossible; an infinite construction must first survive an expanding boundary excursion.

The forced expanding excursion is unavailable on eight of the thirteen source-parameter classes. Exact degree-1024 quotient propagation and complete factorization of q10(k)+1 over F_13 show that k mod 13 in {0,2,5,6,7,8,9,10} pays the full factor 13 at height 12, collapses to primitive height one, and enters centered state zero forever. Any infinite negative-support construction inside this family must lie in the five classes {1,3,4,11,12}.

The next full-payment mechanism splits exactly. On k mod 13 in {3,4,11,12}, the height-13 error remains -1 but the payment is always 1 or 7, never the full factor 14. On k=1+13*t, the error is -4 and four classes t mod 17 in {8,9,13,14} pay 17, collapse to height one, and enter centered state zero forever; all thirteen complementary classes switch to centered error +2 or +4 at height 17. Thus the whole k=1 mod 13 branch is unavailable for continuing negative support. The exact partition modulo 221 is 140 zero-centered, 13 positive-centered, and 68 continuing-negative candidates.

The payment-seven height-two boundary cannot continue negative support. All sixteen classes modulo 182 have height-13 multiplier 7 modulo 42 and are forced through (13,-1)->(2,-1 tie)->(3,-1)->(1,0 forever), with payments 7,1,4. On the common modulus 3094 the family is now partitioned into 2232 zero-centered classes, 182 positive-centered classes, and only 680 continuing-negative candidates, all in the payment-one height-fourteen branch.

The payment-one height-fourteen branch is not homogeneous. Exact quotient propagation on its 600 classes modulo 2730 gives only w=q11/14 mod 15 in {0,3}, so full payment 15 is impossible. The 240 w=3 classes pay five and switch to centered error +1 at height 3; only the 360 w=0 classes survive, paying one at heights 14 and 15 and reaching height 16 with centered error -1. On the common modulus 46410 the family is partitioned into 33480 zero-centered, 6810 positive-centered, and 6120 continuing-negative candidates.

The height-16 survivors split exactly modulo 17. Their actual intermediate image is c mod 17 in {0,10,12}, giving multiplier residues {1,3,0}. The 1440 multiplier-zero classes pay 17 and collapse to height one, the 2520 multiplier-three classes switch to centered error +8, and only 2160 multiplier-one classes retain centered error -1 at height 17. The cumulative modulus-46410 partition is 34920 zero-centered, 9330 positive-centered, and 2160 continuing-negative candidates.

Every mod-4 lift of the height-17 survivors has d=0, so the generic payments 18, 9, and 2 never occur; all 8640 classes pay one and reach height 18 with error -1. At height 18 the exact multiplier image modulo 19 is only {0,1}: eleven of nineteen lifts per source class pay 19 and collapse to height one, while eight retain error -1 at height 19. The cumulative modulus-3527160 partition is 2748960 zero-centered, 709080 positive-centered, and 69120 continuing-negative candidates.

The height-19 payment image is exactly {1,5}; payments 20 and 4 never occur. The 184320 payment-five classes land at height four with error -1, where the next multiplier is automatically divisible by five, so every such class collapses to height one. Only 506880 payment-one classes reach height 20 with error -1. The cumulative modulus-35271600 partition is 27673920 zero-centered, 7090800 positive-centered, and 506880 continuing-negative candidates.

The height-20 payment image is exactly {1,7}; payments 21 and 3 never occur. Every one of the 2433024 payment-seven classes is terminal for negative support: 2256075 follow a forced cofinal cascade and 176949 switch to centered error +1. Only 8211456 payment-one classes reach height 21 with error -1. The cumulative modulus-740703600 partition is 583408395 zero-centered, 149083749 positive-centered, and 8211456 continuing-negative candidates.

The height-21 quotient-parameter image is exactly {0,6} modulo 22, so payments two and twenty-two never occur. The 120931560 payment-one classes reach height 22 with error -1. All 59720472 payment-eleven classes land at height two; after a complete three-lift refinement every one of the 179161416 lifts has multiplier 1 mod 6, so it reaches height three with an even multiplier and pays the full factor four. Every payment-eleven class returns cofinally, leaving only the height-22 payment-one branch.

The height-22 multiplier image modulo 23 is exactly {0,1,15}. Complete affine-period counting proves that 2024012298 of 2781425880 logical lifts pay the full factor 23 and collapse to height one; 84115680 pay one but switch to centered error +5; only 673297902 reach height 23 with error -1. The residue-counting certificate avoids materializing the 23-fold cylinder and remains exact for zero and nonzero lift slopes.

At height 23 the generic factor-24 algebra permits payments 1,3,4,8,12,24, but the complete actual source image is the singleton divided quotient z=0 and multiplier 1 modulo 24 on all 16159149648 logical refinements. Thus full collapse, positive switching, and every smaller-height branch are absent; all classes reach height 24 with error -1.

At height 24 the preceding quotient map c=12144w^2+21w eliminates the generic centered-error-minus-nine factor-25 mode. The actual preceding-quotient image modulo five is only {0,1,4}, eliminating the possible cofinal root w=2. The 58762693440 realized w=4 refinements nevertheless pay the full factor 25 and return cofinally; 23505077376 switch positive, while 321710970384 continue negative in errors -1,-6,-11. Thus factor 25 is a genuine partial boundary-killing mechanism but not a complete exclusion.

The aggregate factor-25 loss cannot be promoted to a uniform one-step contraction: exactly 10282880304 actual height-24 parents have 25 continuing-negative children and no cofinal or positive child. The complementary 5876269344 parents are rigidly active with profile 10 cofinal, 4 positive, 11 negative. Source digit t mod 10 separates the profiles exactly as 0 inert versus {4,6} active; affine slope alone does not. Any geometric-loss proof must establish activation of the successive inert subfamilies, not per-parent contraction at every factor.

The t=0 inert factor-25 image contains only centered error -1 on all 257072007600 negative children. Errors -6 and -11 occur exclusively in the already-active t in {4,6} branches. Consequently raw next-height factors 31 and 36 are absent from the inert frontier; its exact next source extension needs only factor 26.

Factor 26 has no immediate cofinal mode on the actual inert frontier: the preceding multiplier B=552c^2+22c+1 is odd, so the quotient relation 25C=24B^2-25B+26 forces C odd and prevents 26 from dividing C^2. Exact counting strengthens this no-go: all actual parents have the same immediate 0 cofinal, 4 positive, 22 negative profile. The fourteen multiplier-thirteen children per parent then force height-two multiplier 150 and full payment three, so the effective profile is 14 cofinal, 4 positive, 8 negative. The all-negative fiber mode is eliminated with uniform 4/13 continuation, but the (height,error)=(26,-1) multiplier-one state still carries the expanding negative boundary.

Factor 27 does not activate the surviving multiplier-one boundary. The complete actual source image is C=1 mod 702 and next multiplier D=1 mod 27 on all 3888 exhaustive source samples. Restoring exact weights, all 55527553641600 logical refinements pay one and reach height 27 with centered error -1. This eliminates every generic factor-27 payment, cofinal-return, and sign-switch mode and forces the next distinct probe to factor 28.

Factor 28 does activate every actual factor-27 parent but has no immediate cofinal child. The complete q-image modulo 28 is {0,4,12}: q=4 forces multiplier 21, payment seven, height four, and centered error +1, while q=0,12 preserve multiplier one and error -1 at height 28. Every parent has profile 0 cofinal, 8 positive, 20 negative, so the all-negative factor-28 mode is decisively eliminated and the exact negative continuation ratio is 5/7.

Factor 29 uniformly kills the homogeneous multiplier-one boundary. Every actual factor-28 parent has profile 8 cofinal, 6 positive, 15 negative. The exact quotient multiset modulo 29 is 0^7,15^8,24^8,25^4,27^2: class 15 pays the full factor 29, classes 25 and 27 switch positive, and the two surviving classes split into centered errors -1 and -6. The next computation must branch to raw factors 30 and 35 rather than continue a single homogeneous cylinder.

Factor 30 is uniformly inert on the actual (29,-1) source: all 544320 complete families have G=1 mod 30 and all thirty children remain negative. Factor 35 has no cofinal child and no uniform parentwise contraction, but it splits exactly one fifth inert and four fifths active; active families have profile 0 cofinal, 25 positive, 10 negative. This eliminates any generic factor-30 activation argument and any claim that factor 35 activates every source family, while establishing the exact weighted factor-35 continuation 3/7.

A prime-field image must classify the multiplier of the declared parent state, not the preceding height-29 multiplier. Omitting the exact factor-30/35 transport produced spurious zero-free profiles and a false successor frontier. The corrected computation restores that transport before applying unit-field permutation.

The corrected factor-31 profile is (4 cofinal,0 positive,27 negative), while the corrected factor-41 profile on (35,-6) is (2,39,0). Thus the factor-35 negative branch is completely extinct after factor 41, and the surviving factor-31 modes have raw factors 32,35,36,38,40,41.

Corrected descendant field propagation forces cofinal return again: (31,-10) has factor-41 profile (8,21,12), and its (41,-20) child has factor-61 profile (4,6,51). The remaining exact frontier is composite raw factors 32,35,36,38,40,57,64,66,75,76.

The coprimality route is capped at O(log C_n): for pairwise coprime old moduli with reciprocal sum at most 1/2, every window of length above 2^{k+1} (k the number of moduli below the window) contains an integer coprime to all of them, so a walk with rises O(2^k) = O(log u) for doubly exponential moduli avoids every old modulus forever (SlowNegativePartRigidity.md, Prop. 7; greedy witness in formal_math/probes/erdos243_crt_block_and_coprime_witness.py needs a maximal rise of 12 up to height 2e6 against Sylvester's numbers). The CRT block forces rises of order log2 log2 u only. Hence no argument using only pairwise coprimality and whole-modulus avoidance can exclude negative parts of order log C_n; the regime (1 - delta) log2 log2 C_n <= -E_n = o(C_n) needs the congruence E_n = D_n mod C_n beyond coprimality.

The Erdos-Straus LCM prefactor supplies no new sign information: M_n = q a_1...a_{n-1}/lcm divides c_n exactly, the LCM quantity is the product quantity divided by M_n, and both have the sign of e_n. Common-divisor persistence fails in LCM coordinates at cancellation steps (division by gcd(L_n, a_n)), so the bounded form limsup Q_n/M_n < infinity is not obtained.

## Open implications

### exclude_aperiodic_negative_state_orbits

Attack the sole remaining signed-state obstruction, now quantified: any counterexample has negative excursions with -E_n > (1 - delta) log2 log2 C_n infinitely often for every delta > 0 (slow_negative_part_rigidity, counterexample_loglog_negative_excursions), with divergent normalised negative mass and with every multiplier overlap gcd(a_n, D_n) bounded by the next negative magnitude. Coprimality-only arguments are capped at O(log C_n) rises, so the producer must use the congruence E_n = D_n (mod C_n) or a second landing mechanism. Attack the sole remaining signed-state obstruction: cofinally unbounded negative excursions in the exact dynamic cocycle. Corrected unit-field propagation kills the factor-35 branch, forces eight cofinal returns on (31,-10) at factor 41, and forces four more on its (41,-20) child at factor 61. The exact formerly inert factor-25 continuation is now 1061100/29229187. The next analytic producer is a source-conditioned negative-mass or cumulative-LCM transfer theorem consuming these contractions. Compute composite raw factors 32,35,36,38,40,57,64,66,75,76 with exact nonunit transport.

Evidence/status: see the source; no formal status inferred


### formalise_lcm_weighted_theorem

Kernel-check the analytic bridge into the now-checked LCM arithmetic core: strict ceiling, qW_n+V_n->0, log(g_n)/log(a_n)->0, and extraction of infinitely many distinct old primes from the original sequence hypotheses.

Evidence/status: see the source; no formal status inferred


### critical_boundary

Resolve the boundary n*(a_n^2/a_{n+1}-1)_+ approximately 1.

Evidence/status: see the source; no formal status inferred


### weighted_sparse_reset_lower_bound

Produce a quantitative lower bound connecting each repaired long-block CRT obstruction to prime-multiplicity or square-residue payment mass. The upper budget is now exact and multiplicatively accumulated; the missing direction is to prove that infinitely many repairs would force a payment product whose fixed power eventually exceeds 2^n.

Evidence/status: see the source; no formal status inferred


### current_scale_anti_shadowing

Exploit arithmetic at the recovery scale, rather than whole multipliers that already exceed every numerator on the clean leaf: prove a supply of useful current-scale factors or a global nonrecurrence theorem for the exact centered affine-multiplicative cocycle in the divergent normalized-negative-mass branch.

Evidence/status: see the source; no formal status inferred


### global_primitive_prefix_anti_shadowing

Upgrade the checked complete-prefix constraints gcd(A_n,a_n-1)|e_n and gcd(a_j,a_n-1)|e_n into an unbounded-prefix theorem. The needed conclusion must rule out indefinitely small nonzero centered errors while remaining compatible with every fixed finite E=-1 fixture.

Evidence/status: see the source; no formal status inferred


### primitive_modified_convergent_gcd_excess

Formalize the modified-convergent cross-error identity and then prove, on at least one globally coherent primitive block, that gcd(P,Q)>|e_endpoint|. The finite E=-1 fixtures realize equality for arbitrarily long local blocks, so the producer must consume unbounded prefix or recovery coherence rather than block length alone.

Evidence/status: see the source; no formal status inferred


### global_lcm_repair_lower_bound

Prove that every infinite arithmetically realizable normalized-vanishing nonterminal orbit forces cumulative overlap debt M_n to violate the checked subexponential budget: for some fixed K, 2^n<=M_n^K at arbitrarily large n. Equivalently, rule out a divergent but termwise vanishing global negative-mass budget financing only sparse overlap repairs.

Evidence/status: see the source; no formal status inferred


### reset_payment_lower_bound

Prove that repeatedly repairing the complete-prefix CRT obstructions across globally coherent reset recoveries consumes a quantitatively non-subexponential product of exact square-cancellation payments, contradicting the already checked subexponential payment budget. Exact witnesses rule out deriving this from one clean-prefix length, aggregate raw-reset lengths, one complete clean recovery, or the lengths and reset payments of a pair of consecutive clean recoveries. The producer must use unbounded complete-prefix arithmetic or changing residue/prime/overlap data across recoveries.

Evidence/status: see the source; no formal status inferred


### strict_rise_loglog_negative_lcm_rigidity

Formalize the ordinary strict-rise log-log LCM rigidity theorem now proved in R2CumulativePayment.md. Do not reprove it as new mathematics; the parent gap is the unconditional production of its rise bound.

Evidence/status: ordinary_proof_closed_lean_formalization_open
