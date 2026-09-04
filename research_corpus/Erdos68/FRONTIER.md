# erdos_68 mathematical frontier

Generated from the exported research packet. Read the strongest applicable
result before attempting a proof; superseded results remain history.

Prove that the Erdős #68 factorial-denominator series is irrational.

## Established results and their evidence

### companion_constant_unconditional_carry_law

Let C=sum_{n>=2}1/(n!(n!-1)) be the fixed companion constant, F_m=m!C_m the finite fractional carrier, delta_m=m!sum_{n>m}1/(n!(n!-1)) the scaled omitted tail, and sigma_m=[fract(m!C)<delta_m]. Lean proves F_m=m!C-delta_m with 0<delta_m<1/((m+1)!-1) for m>=2, the wrap identity floor(F_m)=floor(m!C)-sigma_m, and for every m>=3 the exact carry law b_m=(m-1-d_m(C))+sigma_m-m*sigma_(m-1), where d_m(C) is the canonical factorial digit of C. Consequences: a unit carry forces d_m(C) in {m-2,m-1}; a zero carry forces d_m(C) in {m-1,0}; if floor(m!C) avoids both residues -2 and -1 modulo m then b_m!=1, which is the previously named constant-only miss certificate with its tail hypothesis discharged; and the floor-stability hypothesis SecondLayerFloorStableAt C m of SecondLayerDigit is exactly delta_m<=fract(m!C), so away from wraps b_m=m-1-d_m(C). The exact probe finds no wrap through m=160 (smallest fract(m!C)/delta_m ratio 18.7) and verifies the identity at every 3<=m<=160. This makes the Erdős 68 carry sequence an exact function of one real constant plus an explicit sub-factorial exceptional indicator; it produces no cofinal miss and no irrationality claim.

Evidence/status: lean_checked_exact_identity_no_cofinal_claim

- [CompanionConstantCarryLaw.lean](problem/CompanionConstantCarryLaw.lean)

claim_boundary: Exact pointwise identity and unconditional certificate interface. No cofinal miss, non-concentration theorem, or irrationality is claimed.

### erdos_shift_family_uniform_companion_orbit_boundary

For every integer t>=-1 let S_t=sum_{n>=2}1/(n!+t) and C_t=sum_{n>=2}1/(n!(n!+t)). Lean proves the termwise identity 1/(n!+t)=1/n!-t/(n!(n!+t)), summability of both series, the decomposition S_t=(-t*C_t)+(e-2) in the anchored form of the generic fixed-orbit boundary, and hence: S_t is rational iff ceil(t*m!*C_t)==2 (mod m) for all sufficiently large m, and S_t is irrational iff that ceiling escapes the residue 2 cofinally. The member t=-1 is kernel-identified with the Erdős 68 series, where the condition is the existing floor(m!C)==-2 boundary; the member t=0 is kernel-identified with e-2, whose orbit ceil(0)=0 never lies in residue class 2 for m>=3, so the boundary reproves that e is irrational. This places Erdős's whole conjectured family (Erdős 1988, p. 102) under one explicit companion-orbit boundary extending Cantor's factorial-base criterion; it decides no member with t!=0. Finite evidence: residue-2 hits for t=1,2,3,5 through m=400 are [3,30,110], [3,13,61,227,377], [6,31,45,56], [11,14,20,28,29,309], consistent with a 1/m hit rate.

Evidence/status: lean_checked_family_equivalence_no_member_decided_except_t_zero

- [FactorialShiftFamilyOrbit.lean](problem/FactorialShiftFamilyOrbit.lean)

claim_boundary: Exact family equivalence for t>=-1 extending the Cantor 1869 / Galambos 1976 factorial-base criterion (prior-art disposition D1). Members t<=-2 are not formalised. No irrationality is claimed for any t!=0; prior art for the family boundary itself was not re-checked online this session.

### nonterminal_repeated_record_threshold_bridge

The first genuinely nonterminal repeated square record, q=971 from 361!-1 to 609!-1, composes with the actual successor predecessor-gap state. Exact Fraction recurrence at m=610 gives 971^2 dividing the reduced denominator, reduced numerator 41085 modulo 971^2, and a strictly positive cleared tail-free threshold margin. Thus nonterminal repeated-record amplification is not structurally detached from the Archimedean closing inequality. This is one finite composable certificate, not a theorem that records force thresholds, a cofinal supply theorem, or an irrationality proof.

Evidence/status: exact_finite_mechanism_opening_with_lean_checked_consumers

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

### canonical_factorial_digit_kernel

For every real x, Lean checks the exact floor formula d_m=floor(m*theta_(m-1)), the bounds 0<=d_m<m, the recurrence theta_(m+1)=(m+1)theta_m-d_(m+1), the finite telescoping factorial expansion with explicit remainder, and propagation from a zero remainder to an entirely zero digit tail.

Evidence/status: lean_checked

- [CanonicalFactorialDigits.lean](problem/CanonicalFactorialDigits.lean)

### finite_defect_automaton_algebra

For any exact rational centre recurrence F_m=m*F_(m-1)+1+epsilon_m-C_m, Lean checks that the integer ceiling defect code equals floor(m*delta_(m-1)-epsilon_m) and that delta_m=m*delta_(m-1)-epsilon_m-q_m. The specialization epsilon_m=1/(m!-1) is explicit; proving the finite-sum residual centre satisfies the premise remains separate.

Evidence/status: lean_checked

- [FiniteDefectAutomaton.lean](problem/FiniteDefectAutomaton.lean)

### strict_successor_prime_power_criterion

Lean checks the exact two-stage arithmetic criterion for N=kp*Nprev+1-b: p^k divides N iff there is a unique slot 0<=r<k with b=1+pr and p^(k-1) divides k*Nprev-r. It checks the k=2 specialization and, for odd primes, cancels the factor 2 in the first branch: a square hit lies exactly in either b=1 with p dividing Nprev, or b=1+p with p dividing 2*Nprev-1. The new literal-series specialization identifies N with the strict successor of the actual prefix at 2p and Nprev with the actual prefix at 2p-1, and packages failure of both branches at cofinally many odd primes as a direct Irrational theorem. The actual #68 factorial-gap tail is reindexed, positive, and bounded by the strict telescope tail(D)<1/D! for D>=2; the original series is exactly its rational prefix through D plus this tail. Consequently Lean checks the complete literal reduction for signed rational numerators: if the #68 series equals a/q, then for every prime p not dividing q and every k with q<=kp, p^k divides the strict factorial successor of the genuine prefix through kp. The sole remaining exponent-two producer is now the cofinal failure of the two explicit doubled-prime branches.

Evidence/status: lean_checked_complete_irrationality_criterion_miss_family_pending

- [StrictSuccessorArithmetic.lean](problem/StrictSuccessorArithmetic.lean)

### prime_block_integer_translation_collapse

The incomplete-exponential residue vector cancels after an exact integer translation. A full length-p hit block is equivalent to a scalar run in the strict-ceiling factorial-rounding orbit and to a single exceptionally small endpoint approximation at 2p-1.

Evidence/status: advisory_complete_derivation


### canonical_factorial_digit_equivalence

The canonical factorial digits d_m(S) are eventually zero if and only if S is rational; this is exactly equivalent to eventual integrality of the previously defined factorial tail state.

Evidence/status: advisory_complete_derivation


### koepf_schmersau_floor_criterion_boundary

Koepf--Schmersau Theorem 1.1 (printed p. 117) reduces irrationality to eventual equality floor(n s_n)=floor(n a), and Theorems 2.2--2.3 (printed pp. 119--120) produce that equality from n p_n s_n integral and a-s_n<1/(n p_n). For the natural Erdos 68 clearing scale p_n=lcm(k!-1:2<=k<=n), the derived identity gcd(n!-1,(n-1)!-1)=gcd((n-1)!-1,n-1) gives p_n>=((n!-1)((n-1)!-1))/(n-1). For n>=4 the first omitted term 1/((n+1)!-1) already exceeds 1/(n p_n), so this natural termwise clearing choice violates the source criterion's tail hypothesis. Smaller reduced-prefix denominators would require a new cancellation theorem and are not excluded.

Evidence/status: source_verified_derived_not_source_stated


### duverney_fast_series_boundary

Duverney Theorem 3.1 (printed pp. 285--286) requires two-sided quadratic growth c*u_n^2<=u_(n+1)<=c'*u_n^2. For u_n=n!-1 the ratio u_(n+1)/u_n^2 tends to zero, so the lower bound fails. Corollary 3.2 (printed p. 287) additionally requires convergence of sum |u_(n+1)/u_n^2-1| in the positive-term specialization, whereas these summands tend to one. Neither result applies to Erdos 68.

Evidence/status: source_verified_exact_hypothesis_failure


### kovac_tao_quadratic_perturbation_boundary

Specializing Kovač--Tao Lemma 5.1 (arXiv v4, pp. 14--15) to a_n=n!-1 and the integer intervals J_n=[a_n-(n^2+1),a_n] gives a rational reciprocal series with positive denominators b_n satisfying n!-n^2-2<=b_n<=n!-1. For n>=8 the single k=n+1 term proves the lemma's tail-overlap condition. Lean checks the exact cross-multiplied inequality: after x=n!, the difference is x^2-(2n^4+3n^3+4n^2+2)x+(n^6+2n^5+5n^4+6n^3+7n^2+2n+1)>0, using n!>2n^4+3n^3+4n^2+2. This sharpens the paper's unspecified o(a_n) Type-2 perturbation for the factorial-gap sequence to a one-sided quadratic window. It does not determine the rationality of the unperturbed left endpoint.

Evidence/status: source_verified_derived_not_source_stated_with_lean_checked_overlap_arithmetic

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### hancl_tijdeman_carry_factorial_bridge

Lean checks the exact identity Z_M/M!=Z_2/2!+sum_(3<=m<=M)(1-b_m)/m!, obtained by normalizing and telescoping the strict-successor recurrence. Thus carry defects are ordinary factorial-series coefficients. Hancl--Tijdeman Theorem 3.1 and Corollary 3.1 (printed pp. 390--391) classify polynomial-coefficient series over cumulative linear-product denominators, including ordinary factorial series, but not the original individual denominators m!-1. In the checked bridge, the classical factorial-series route still needs infinitely many nonzero coefficients 1-b_m, exactly the unresolved cofinal non-unit-carry producer.

Evidence/status: source_verified_and_lean_checked_derived_not_source_stated

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### erdos_straus_carry_coboundary_coordinate

Koutsoukou-Argyraki--Li--Paulson Theorem 3.1 (arXiv v2, pp. 4--5), formalizing Erdős--Straus Theorem 2.1, states that a cumulative-product series sum b_n/prod_(i<=n) alpha_i with |b_n|/(alpha_(n-1)alpha_n)->0 is rational iff eventually B b_n=c_n alpha_n-c_(n+1) for integers B>0,c_n with |c_(n+1)|<alpha_n/2. Their p. 6 reconstruction gives the explicit nearest-integer recursion and bounded remainder state; p. 7 says minor inequality corrections were required in two original consequences but did not change the statements. For the Lean-checked #68 expansion, alpha_m=m and b_m=1-factorialGapStepCarry(m). The existing sharp carry range -1<=factorialGapStepCarry(m)<=m-1 yields |b_m|<=m, and Lean proves the source asymptotic hypothesis. This criterion is applied only after the exact carry expansion to cumulative factorial denominators; it does not apply directly to the separate denominators m!-1 or supply the missing cofinal non-unit-carry producer.

Evidence/status: source_verified_and_lean_checked_hypothesis

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### erdos_straus_coboundary_finite_state_collapse

The sharp carry range makes the source coboundary much more rigid than a generic bounded-state obstruction. Put d_m=1-factorialGapStepCarry(m), so 2-m<=d_m<=2. Lean proves that if B>0 and eventually B d_m=m c_m-c_(m+1) with 2|c_(m+1)|<m, then every sufficiently late state lies in -B<c_m<=0: the coefficient and half-radix bounds first give -B<=c_m<=0, while equality at the lower endpoint would force c_(m+1)<=-2B and contradict the same weak bound at the next index. Lean also checks the finite-residue core: from any such tail, the first chosen index divisible by B sends the next state to zero, zero is absorbing, and d_m=0 eventually. Therefore every Erdős--Straus coboundary collapses to eventual unit carries rather than providing a separate obstruction.

Evidence/status: lean_checked_state_bound_and_finite_residue_collapse

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### strict_successor_carry_exact_characterization

Lean proves that the normalized strict successors Z_n/n! converge to the literal series S. Combining this limit with the exact carry recurrence gives both converses: S is non-irrational exactly when b_m=1 eventually, and S is irrational exactly when for every cutoff B some m>B has b_m!=1. Thus the carry route loses no implication; its sole remaining mathematical producer is cofinal non-unit carries.

Evidence/status: lean_checked_exact_equivalence_open_producer_pending

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### strict_successor_carry_search_through_300000

An exact GMP 6.3.0 integer computation certifies every strict-successor carry for 3<=m<=300000. The only unit carries are m=52,591,1030,1407,1438,2164,4258,10991,21236; in particular there are no further unit carries through 300000, and the carry at m=300000 is non-unit. The checked theorem rational_denominator_ge_of_nonunit_carry therefore gives S=a/q with q>0 only if q>=300000. This is a finite denominator exclusion, not a cofinal-carry theorem or an irrationality proof.

Evidence/status: locally_regenerated_exact_finite_only_with_lean_checked_consumer


### finite_defect_automaton

An integer-valued defect state q_m is computable from the divisor-factorial coefficients without prior knowledge of S, and S is rational if and only if q_m equals 1 for all sufficiently large m.

Evidence/status: advisory_complete_derivation

- [FiniteDefectAutomaton.lean](problem/FiniteDefectAutomaton.lean)

### prime_window_archimedean_modular_factorization

Every prime-window test factors into a sharp Archimedean strict-ceiling condition and a modular divisibility condition, exposing the missing coupling rather than treating congruences alone as decisive.

Evidence/status: advisory_complete_derivation


### canonical_product_log_derivative_identity

For E(z) = product_{n >= 2} (1 - z/n!), the genus-zero entire product satisfies -E'(1)/E(1) = S.

Evidence/status: advisory_complete_derivation


### scalar_canonical_product_height_no_go

The natural scalar linear form has coefficient Q_N = product_{2 <= n <= N} (n! - 1) and Q_N times the tail diverges; exact first-order interpolation, scalar residue weighting, the natural Wronskian, and rank-saturated consecutive jets all reassemble the same prohibitive denominator.

Evidence/status: advisory_complete_derivation


### factorial_gap_lcm_lower_bound

Let L_N=lcm_{2<=n<=N}(n!-1). Garaev--Luca--Shparlinski Theorem 12 bounds the number of solutions to n! congruent to a modulo an odd prime on an interval below that prime by O(N^(2/3)). Since every prime p dividing n!-1 satisfies n<p, the number m_p of factorial gaps through N carrying p is O(N^(2/3)). With E_p=max_{n<=N} v_p(n!-1), log product_{2<=n<=N}(n!-1) <= (max_p m_p) sum_p E_p log p = O(N^(2/3) log L_N). Stirling summation on the product therefore gives log L_N >> N^(4/3) log N. This is a checked derivation from the source theorem, not a theorem stated verbatim in the paper, and it obstructs scalar localizers with only exp(O(N log N)) denominator height.

Evidence/status: source_verified_derived_corollary_not_lean_checked


### floor_factorial_channel_arithmetic

For every positive d, Lean proves (d!)^(floor(i/d)) divides i!, defines the integral channel weight, and checks exact denominator cancellation. The consecutive channel event n*W_(d,n-1)-W_(d,n) vanishes whenever d does not divide n.

Evidence/status: lean_checked

- [FactorialChannelCertificate.lean](problem/FactorialChannelCertificate.lean)

### lambda34_finite_subunit_certificate

For the finite-support vector lambda=2e_3-e_4, Lean checks V_2=0, factorial moment -12, V_3=-2, V_4=11, and V_d=-12 for every d>=5. Under the exact rational tail enclosure 1/119<Theta_4<1/50, its residual lies strictly between -93/575 and -309/13685, hence is nonzero and subunit.

Evidence/status: lean_checked_finite_only

- [FactorialChannelCertificate.lean](problem/FactorialChannelCertificate.lean)

### primitive_cofactor_determinant_divisor_bottleneck

The returned corank-one cofactor construction reduces an unbounded certificate family to an appended-row determinant residual N(I,D) satisfying 0<|N(I,D)|<Delta(I,D), where Delta is the gcd of maximal minors. No unbounded family satisfying this inequality was obtained.

Evidence/status: advisory_exact_reduction_pending_lean


### weighted_projection_rigidity

For natural endpoint numerator Z congruent to a weighted numerator T modulo R, every divisor Q of R with Z<=B<Q has T mod Q=Z. Consequently two divisors Q1,Q2>B with unequal projected residues exclude such a bounded endpoint. Lean also checks the leave-one-out specialization Q=R/r and the quantitative fact that unequal projections force min(Q1,Q2)<=Z. For the actual reciprocal-tail sign Z+T congruent to 0, Lean now defines the canonical complementary projection ((Q-(T mod Q)) mod Q), proves that it equals Z mod Q, and transports projection disagreement through this sign-correct interface.

Evidence/status: lean_checked

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

### equal_leave_one_out_projections_collapse_to_global_residue

Lean proves that complementary projection commutes with passage from a positive full modulus R to every positive divisor Q. More generally, if rho<R and its projections modulo Q1 and Q2 agree while lcm(Q1,Q2)=R, their common value is rho. For the literal Erdős #68 block, pairwise-coprime private quotients imply that the leave-one-out moduli attached to any two distinct owners have lcm exactly R_p. Consequently equality of two coefficient-free complementary leave-one-out projections forces their common value to be the global complementary residue rho_p=(-T_p) mod R_p. This classifies the equality branch of the finite projection scan but does not prove projection disagreement, a lower bound for rho_p, a cofinal certificate family, or irrationality.

Evidence/status: lean_checked

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

### unconditional_complementary_pair_floor_reduction

Lean defines a generic projection-pair floor: if two least-residue projections agree, use their common value; otherwise use the smaller projection modulus. When the two moduli have lcm R and the full residue is below R, this branch-free score is always at most the full residue. For every literal Erdős #68 block and any two distinct private owners, Lean transports that theorem through the coefficient-free complementary projections and proves factorialBlockComplementaryPairFloor(p,i,j)<=rho_p. It packages the resulting endpoint contradiction and a complete irrationality reduction: it is enough to produce cofinally many prime blocks with two distinct owners for which (2p+1)L_p is smaller than 2p^2(2p-1)! times this pair floor. This removes projection disagreement as a separate hypothesis but does not supply the required cofinal scale inequality.

Evidence/status: lean_checked_complete_reduction_open_cofinal_pair_floor_producer

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

claim_boundary: The source proves an exact branch-free pair-floor reduction and the resulting conditional irrationality theorem. It does not provide the cofinal pair-owner scale inequality or an unconditional irrationality proof for Erdős #68.

### quotient_cancelled_collision_cap_reduction

For two private quotients r_i,r_j dividing R_p, Lean proves the exact cancellation identity min(R_p/r_i,R_p/r_j)*max(r_i,r_j)=R_p. Combining this with C_p R_p=L_p removes the full endpoint lcm and the near-full leave-one-out moduli from the two-projection scale comparison. The resulting endpoint contradiction and complete irrationality reduction require only complementary-projection disagreement and the local inequality (2p+1)C_p*max(r_i,r_j)<2p^2(2p-1)!. Lean then cancels the forced predecessor-factorial base as well: writing C_p=(p-1)!*Ctilde_p and (2p-1)!=(p-1)!*p(p+1)...(2p-1), it suffices to prove (2p+1)Ctilde_p*max(r_i,r_j)<2p^2*p(p+1)...(2p-1). The normalized core is positive and is exactly the pairwise collision core divided by its gcd with the base; q^e survives exactly when two gaps share q^(e+v_q(base)). Every such surviving power satisfies e+v_q((p-1)!)<q, and Lean now specializes this to the full normalized-core valuation: for every prime q in its support, v_q(Ctilde_p)+v_q((p-1)!)<q. In particular, every surviving q satisfies v_q((p-1)!)<q-1 and p-1<q(q-1)<q^2; equivalently, whenever k(k-1)<=p-1, the normalized core is coprime to k! and has no support in any complete low factorial channel. Thus the quantitative producer no longer has to control the multi-million-bit R_p or L_p, the automatic factorial portion of C_p, or any prime below this square-root cutoff: it must control the aggregate product of the remaining large prime powers, whose complete excess valuations are now explicitly capped, times two selected private quotients, and prove their coefficient-free projections disagree cofinally. The through-607 finite scan verifies the equivalent collision-cap inequality for its selected pair on every tested block, but its 503..607 extension has no new owner transition and no cofinal proof is claimed.

Evidence/status: lean_checked_complete_reduction_open_cofinal_collision_cap_and_projection_producer

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Cofinally control the aggregate product of the remaining support powers q^v_q(Ctilde_p), with q^2>p-1 and v_q(Ctilde_p)+v_q((p-1)!)<q, strongly enough for the normalized collision cap at a selected private quotient, and independently force the required complementary projection disagreement or global complementary-residue lower bound.

### upper_hit_normalized_collision_multiplicity_transfer

Lean proves that if a prime q hits any displayed factorial-gap denominator at an upper-half index n>=p, then q does not divide the predecessor-factorial base (p-1)!. Consequently predecessor-factorial normalization preserves every positive q-power in the collision core: q^e divides the normalized core if and only if q^e divides the full collision core. Combined with the exact two-hit characterization, a complete q^e contribution to the normalized core is therefore exactly a repeated full-power hit in two distinct displayed gaps, rather than an artifact of the distinguished base. This is the direct formal consumer for source-verified upper-half collision estimates, but it does not bound the aggregate product of all repeated powers, force a complementary projection or residue, or prove irrationality.

Evidence/status: lean_checked_exact_source_consumer_open_aggregate_repeated_hit_load

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

claim_boundary: Lean proves that an upper-half prime avoids the predecessor-factorial base and that its full repeated-hit prime-power load survives normalization exactly. This is a local transfer for each fixed prime power. It does not aggregate the moving collision-prime support, prove the normalized collision-product cap, force a complementary projection or residue, establish irrationality, or resolve Erdős 68.

surviving_obligation: Aggregate the repeated full-power loads across the moving large-prime support strongly enough for the normalized collision cap, while separately forcing the complementary projection disagreement or global complementary-residue lower bound cofinally.

### normalized_collision_hit_count_consumer

For a prime q already known to hit an upper-half factorial gap, Lean identifies normalized q-power load with a literal incidence count: q^e divides the normalized collision core exactly when more than one displayed gap is divisible by q^e. Hence any source-level bound giving at most one q^e-hit deletes that power from the normalized core, and equivalently forces its q-adic valuation below e. This turns external prime-power hit-count estimates into direct exponent-by-exponent normalized-core bounds. It does not itself supply a uniform at-most-one estimate, sum the surviving valuations over all moving primes and exponents, prove the normalized collision cap, or force the complementary residue.

Evidence/status: lean_checked_exact_incidence_consumer_open_uniform_aggregate_bound

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Prove uniform incidence estimates strong enough across all relevant large primes and exponents to bound the total normalized collision product, and independently force the complementary projection or residue cofinally.

### normalized_collision_repeated_hit_layer_count

For every prime q already known to hit an upper-half factorial gap, Lean computes the complete normalized q-valuation as a finite layer count: it is exactly the number of exponents e in [1,q-1] for which q^e divides at least two displayed factorial gaps. The earlier exponent-by-exponent incidence consumer is therefore aggregated without valuation loss into the exact local collision load. This does not bound the layer count, sum it uniformly over the moving prime support, control the resulting prime-power product strongly enough for the normalized collision cap, or supply the complementary residue.

Evidence/status: lean_checked_exact_local_valuation_aggregation_open_global_prime_product

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Prove uniform repeated-hit layer bounds strong enough across the moving prime support to force the normalized collision cap, and independently force the complementary projection or residue cofinally.

### normalized_collision_prime_power_hit_spacing_witness

Every positive normalized collision power q^e now yields an explicit pair of displayed factorial-gap hits i<j. Lean restores the distinguished-base valuation and proves q^(e+ord_q((p-1)!)) divides both i!-1 and j!-1 and is at most j^(j-i). A companion theorem turns any lower bound (2p-1)^d<q^(e+ord_q((p-1)!)) into the strict spacing conclusion d<j-i. Thus every local collision layer has a concrete pair-distance cost and can consume general-modulus factorial-hit spacing estimates directly. This does not bound the number of witness pairs or layers, aggregate their costs over moving primes, prove the normalized collision cap, supply the complementary residue, or resolve Erdős #68.

Evidence/status: lean_checked_two_commit_local_spacing_interface_open_global_pair_count

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Prove a uniform global bound on the number and aggregate prime-power weight of repeated-hit pairs strong enough for the normalized collision cap, and independently force the complementary projection or residue cofinally.

### endpoint_prime_normalized_collision_block_diameter_ceiling

For every prime q above the factorial-block endpoint 2p-1, if q divides the normalized collision core then its complete normalized valuation is strictly less than the block diameter 2p-3. Lean derives this from the landed distance consumer: q has zero valuation in the distinguished base, the full normalized q-power forces two hits separated by more than its exponent, and every pair in [2,2p-1] is separated by at most 2p-3. This strengthens the former prime-sized exponent ceiling to a block-sized ceiling precisely on the endpoint-prime support relevant to least-prime-factor inputs. It still does not bound how many such primes occur, control their aggregate product strongly enough for the normalized collision cap, supply the complementary residue, or resolve Erdős #68.

Evidence/status: lean_checked_exact_local_valuation_ceiling_open_global_prime_product

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Bound the number and aggregate size of endpoint-prime collision factors strongly enough for the normalized collision cap, and independently force the complementary projection or residue cofinally.

### universal_endpoint_prime_power_hit_packing

Lean now makes the factorial-gap metric bound universal. Any q^e shared by displayed gaps i<j satisfies q^e<=j^(j-i), without requiring q prime or the power to have been selected from the collision core. When q lies above the block endpoint and e>0, every pair of q^e-hits—not merely one chosen witness—is separated by more than e indices. This gives the repeated-hit layer interface a genuine packing structure: higher layers occupy increasingly separated positions. The theorem does not itself state or sum the resulting cardinality bound, control how many endpoint primes occur, estimate their aggregate prime-power product strongly enough for the normalized collision cap, or supply the complementary residue.

Evidence/status: lean_checked_universal_pairwise_spacing_interface_open_packing_aggregation

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Combine the exact per-layer hit-count inequality with the repeated-layer valuation identity and sum the resulting weighted bounds over moving endpoint primes strongly enough for the normalized collision cap; independently force the complementary projection or residue cofinally.

### endpoint_prime_power_hit_count_packing_bound

For p>=2, e>0, and every base q above the block endpoint 2p-1, Lean proves the exact packing inequality hitCount(q^e)*(e+1)<=2p+e-2 on the displayed factorial gaps. It thickens each hit into an interval of length e+1; universal pairwise spacing makes those intervals disjoint, and their union lies inside [2,2p-1+e]. This discharges the finite cardinality producer named by the preceding universal-packing result. The remaining problem is weighted and global: combine these layerwise counts with the exact normalized valuation identity, sum over exponents and moving endpoint primes, and control the resulting prime-power product strongly enough for the collision cap. No complementary-residue bound or irrationality conclusion follows yet.

Evidence/status: lean_checked_exact_layer_cardinality_bound_open_weighted_prime_sum

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Prove the weighted global aggregation over all endpoint primes strongly enough for the normalized collision cap, and independently force the complementary projection or residue cofinally.

### fixed_private_owner_factorial_base_absorption

Lean proves that any displayed denominator already dividing the distinguished base has private quotient exactly one. For the literal factorial block, once p>n!-1 the fixed denominator n!-1 divides (p-1)!, so r_n(p)=1. Equivalently, a nontrivial private quotient at index n forces p<=n!-1. This explains why the low-index maximizing pairs in the through-503 scan cannot stabilize into a cofinal certificate: for example the 719 factor owned at n=6 is absorbed once p>719. Every viable cofinal two-owner collision-cap argument must therefore select indices or prime factors escaping with p; a fixed pair of early owners is an intrinsically finite-range mechanism.

Evidence/status: lean_checked_no_go_boundary


### factor_split_private_modulus_projection_reduction

Lean removes the distinct-denominator requirement from the CRT closing route. For arbitrary divisors a,b of the full private modulus R_p, deleting a and b gives projection moduli R_p/a and R_p/b, the smaller projection modulus times max(a,b) is exactly R_p, and the collision-cap comparison cancels R_p exactly as before. Disagreement of the two coefficient-free complementary projections plus (2p+1)Ctilde_p*max(a,b)<2p^2*p(p+1)...(2p-1) is therefore a complete cofinal irrationality producer. If a and b are coprime, lcm(R_p/a,R_p/b)=R_p and the branch-free factor-pair floor is always at most the global complementary residue. Crucially, a and b may both divide one moving private quotient, so a successful certificate no longer needs two moving denominator indices. This is a strict strengthening of the owner-pair interface, not a proof that such split factors or the required projection bound occur cofinally.

Evidence/status: lean_checked_stronger_complete_reduction_open_cofinal_factor_producer


### tailored_prefix_private_power_to_factor_pair_bridge

Lean connects the source-backed canonical large prefix-private prime powers to the split-factor closing route without losing multiplicity. Unique support preserves every displayed q-adic valuation in the owner quotient, so the complete product M_m of all selected q^v_q(m!-1) divides the single quotient owned by m on the tailored block p=floor(m/2)+1, and hence M_m divides the full private modulus R_p. Each selected prime q is therefore an admissible divisor of R_p. The branch-free consumer needs only the coprime pair (1,q): its projection moduli are R_p and R_p/q, whose lcm is R_p. Thus two nontrivial selected primes are unnecessary. Lean computes the unit-pair floor exactly as min(rho_p,R_p/q), proves that its scale test is equivalent to the conjunction of two explicit inequalities, and now exposes a direct cofinal irrationality consumer taking those two premises: the global complementary-residue bound (2p+1)L_p<2p^2(2p-1)!rho_p and the local collision-core bound (2p+1)C_p q<2p^2(2p-1)!. The opaque floor premise is therefore eliminated, but neither quantitative bound is proved cofinally. The consumer also works for arbitrary natural p>=3, removing the prior mismatch with least-hit tailored blocks. Wilson now supplies bare cofinal prefix-private support unconditionally. Li--Lai plus the checked least-hit bridge remains the stronger quantitative route to the canonical large selection. This remains a conditional irrationality reduction, not a proof of either surviving estimate or of irrationality.

Evidence/status: lean_checked_source_consumer_connected_exact_scale_split_open_global_and_local_bounds


surviving_obligation: For cofinally supplied tailored blocks and a selected prefix-private prime q, prove both (2p+1)L_p<2p^2(2p-1)!rho_p and (2p+1)C_p q<2p^2(2p-1)!, or supply another checked producer feeding the same complementary-factor consumer.

### wilson_cofinal_prefix_private_factorial_gap_supply_and_reflection

Lean proves two complementary Wilson mechanisms for the factorial gaps. First, for every cutoff B, choose a prime q at least B!+5. Wilson gives q dividing (q-2)!-1; taking the least hit m for q forces m>B, because any hit m<=B would imply q<=m!-1<=B!. Thus cofinal prefix-private factorial-gap support is unconditional and no external largest-prime-factor theorem is needed for bare existence. A finite prime-product pigeonhole theorem gives a second supply route: if a finite product of distinct primes, each at least 5, exceeds the product of all factorial gaps through B, one chosen prime avoids every gap through B, and Wilson bounds its least hit by q-2. Neither theorem gives the two scale estimates required by the unit-factor irrationality consumer. Second, if n is odd, n<q, and q divides n!-1, Wilson reflection gives a second hit at q-n-1. When both indices lie in one factorial block and q<2n+1, Lean places q in the block collision core. Hence a linear-size prime factor at a later odd index is not automatically private support.

Evidence/status: lean_checked_exact_bridge_open_shared_producer


surviving_obligation: For a cofinal family of tailored blocks and selected private primes q, prove both (2p+1)L_p<2p^2(2p-1)!rho_p and (2p+1)C_p q<2p^2(2p-1)!, or feed the same checked complementary-factor consumer through another producer.

### li_lai_large_prefix_private_factorial_gap_anchors

Li Lai Theorem 1.1 (printed p. 391 / PDF p. 2) applies to f=-1: for every epsilon>0, a positive-lower-density set of n satisfies P(n!-1)>(1+9 log 2-epsilon)n. For each such prime q, taking the least m>=2 with q dividing m!-1 makes q coprime to every earlier factorial gap k!-1 and transfers the size bound from n to m. Lean checks this least-hit bridge as exists_large_prefix_private_factorialGap_hit. It also checks that q cannot divide (m+1)!-1 and therefore that q is uniquely supported on the tailored block [2,2p-1] with p=floor(m/2)+1; see prime_not_dvd_succ_factorial_sub_one_of_dvd, prefixPrivate_factorialGap_unique_in_tailoredBlock, and exists_large_unique_factorialBlock_hit in EndpointWeightedPrivateSupport.lean. The theorem cofinal_unique_factorialBlock_hits_of_cofinal_large_primes upgrades the pointwise construction to cofinally many tailored blocks by requesting the source prime beyond (2B+1)!. Thus the source plus Lean yields cofinally many uniquely supported upper-half anchors. The Wilson row now supplies bare cofinal prefix-private existence without this source. Li--Lai remains quantitatively stronger: it supplies positive lower density and the linear lower bound defining the canonical large-prime selection. Lean separately proves that the associated one-owner weighted projection is automatically nonzero, but the squared-factorial ceiling below shows that this abundant support cannot close the problem through a one-owner comparison on all sufficiently large blocks.

Evidence/status: source_verified_derived_cofinal_bridge_lean_checked

- Source unavailable in this snapshot: `annexes/li-lai-2026-largest-prime-divisor-shifted-factorials/source.pdf`.

claim_boundary: The positive-lower-density large-prime input is Li--Lai Theorem 1.1, source-verified at the cited location but not reproved in Lean. Lean verifies the conditional least-hit, prefix-private, tailored-block, and cofinal-transfer consequences. The result supplies cofinally many uniquely supported upper-half anchors; it does not prove the required global complementary-residue or pair-floor inequality, establish irrationality, or solve Erdős 68.

### unique_owner_projection_squared_factorial_ceiling

Lean checks factorialBlock_unique_owner_projection_lcm_ceiling: any one-owner closing inequality forces (2p+1)L_p < 2p^2((2p-1)!)^2 because the complementary owner residue is at most q, a supported q is at most n!-1, and n<=2p-1. Its checked companion factorialBlock_not_unique_owner_projection_of_lcm_ge excludes every one-owner certificate whenever the reverse squared-factorial LCM bound holds, independently of how unique support was produced. The source-verified Garaev--Luca--Shparlinski Theorem 12 yields, through annex note n003, log lcm_{2<=n<=N}(n!-1) >> N^(4/3) log N; this eventually dominates log((N!)^2) by a factor N^(1/3). The one-owner mechanism is therefore an asymptotically impossible closing route, not the remaining producer. The eventual comparison from the source-derived LCM corollary to the exact Lean ceiling is not itself Lean-checked.

Evidence/status: lean_checked_ceiling_source_verified_asymptotic_exclusion_not_fully_lean_checked

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

### luca_shparlinski_general_modulus_factorial_hit_bounds

Luca--Shparlinski Lemma 4 (printed p. 811 / PDF p. 4) proves T_f(y,x,p)<< (x-y)^(2/3) for primes p>x, while Lemma 5 and equation (2) (printed pp. 811--812 / PDF pp. 4--5) prove T_f(y,x,q)<< (x-y)log x/log q+1 for every integer q>=2. Specializing f=-1 and q=p^a bounds the number of endpoint-window indices k with p^a dividing k!-1 by O((x-y)log x/(a log p)+1). The source's final remark also gives r_p(x)<<x(log x)^2/log p for the aggregate p-adic order of the product of shifted factorials. These bounds control prime-power reuse and valuation mass, but they remain unweighted incidence estimates and do not force disagreement of the exact endpoint CRT projections.

Evidence/status: source_verified_derived_collision_control_not_solution


### klurman_munsch_short_interval_factorial_residue_bounds

Klurman--Munsch arXiv:1505.01198v1 proves that factorials on an interval of length N above the p^(1/4+epsilon) scale occupy at least sqrt(3N/2) residue classes modulo p, and Lemma 2.4 gives O(N^(3/4)) solutions to (n!)^2=P(n) mod p. Taking P=1 bounds the indices with n! congruent to +1 or -1 modulo one fixed prime, hence gives another per-modulus collision-multiplicity input for factorial gaps. For the live Erdős 68 route this is contextual rather than stronger: O(N^(3/4)) is weaker than the already assimilated Luca--Shparlinski O(N^(2/3)) prime-hit bound, and neither estimate controls the weighted aggregate collision core or endpoint CRT residue. The 2017 journal article supplies the final bibliographic record and average missing-value theorems, but it cites rather than reproduces the short-interval theorem and omits preprint Lemma 2.4; citations to those inputs must therefore use the arXiv version.

Evidence/status: source_verified_contextual_alternate_no_frontier_strengthening


### incremental_pairwise_collision_core_recurrence

Lean sharpens the exact insertion recurrence for the finite collision core and now derives its first global product/lcm bound. For positive denominators, the pairwise collision core times their lcm divides their literal product. After cancelling the distinguished base, the normalized full collision core satisfies the same divisibility. On the factorial block this gives the explicit inequality Ctilde_p <= product_{n in [2,2p-1]}(n!-1) / lcm_{n in [2,2p-1]}(n!-1). The recurrence removes pairwise rescans and the new theorem converts collision growth into a single classical product-versus-lcm ratio. This is a quantitative interface, not yet the needed asymptotic estimate: no theorem bounds that ratio strongly enough to imply (2p+1)C_p q<2p^2(2p-1)!, supplies the global complementary residue, forces projection disagreement, or proves irrationality.

Evidence/status: lean_checked_product_lcm_bound_open_asymptotic_ratio_producer


surviving_obligation: For cofinally supplied tailored blocks and selected prefix-private q, turn the exact product/lcm inequality into (2p+1)C_p q<2p^2(2p-1)! while separately proving the global complementary-residue bound. The new theorem isolates the missing arithmetic estimate in one classical ratio but does not establish its asymptotic size.

### collision_core_prime_power_hit_characterization

Lean now proves the valuation-sensitive converse missing from the original collision-core construction. For every positive prime power q^e omitted by the distinguished base, q^e divides the full collision core if and only if two distinct displayed denominators are both divisible by q^e. On the literal factorial block, any upper-half q-hit guarantees the base omission, so q^e|C_p is equivalent to two distinct indices i,j in [2,2p-1] satisfying q^e|i!-1 and q^e|j!-1. Primewise, the exponent of q in C_p is therefore exactly the second-largest displayed q-valuation. This gives Luca--Shparlinski's general-modulus hit bound a precise Lean-checked consumer: every prime-power layer of C_p is a repeated full-power hit. The source estimate still does not by itself bound the weighted product C_p*max(r_i,r_j) below factorial scale or force projection disagreement.

Evidence/status: lean_checked_exact_source_interface


### li_lai_luca_shparlinski_distinct_large_anchor_count

Fix epsilon>0 and c=1+9 log 2-epsilon. Li Lai gives delta>0 such that at least delta H indices n<=H satisfy P(n!-1)>cn for every sufficiently large H. Choose one such largest prime p_n for each event. Luca--Shparlinski's prime-hit bound, in the explicit f=-1 form t<=3H^(2/3)+2, shows that any fixed prime labels at most 3H^(2/3)+2 of these events: for p>H apply the bound on [2,H], while for p<=H every hit has n<p and the bound applies on [2,p-1]. Hence the selected events involve at least delta H/(3H^(2/3)+2)=Omega(H^(1/3)) distinct large primes. Passing each prime to its least factorial-gap hit gives Omega(H^(1/3)) distinct prime labels on prefix-private anchors up to H. This quantitatively strengthens the anchor supply but still does not determine near-full weighted CRT projections.

Evidence/status: source_verified_cross_source_derived_not_lean_checked


### weighted_primitive_support_decomposition

For a primitive signed rational sum, the returned valuation argument defines the collision core C, pairwise-coprime private quotients r_i, full private modulus R=product r_i, and weighted numerator T with gcd(T,R)=1 such that the displayed endpoint numerator Z is congruent to -T modulo R. Lean checks the factorial-gap support inputs, including that every prime divisor of n!-1 is larger than n and gcd(m!-1,n!-1)=gcd(m!-1,n.descFactorial(n-m)-1) for m<n. It defines the finite collision core as the lcm of the base denominator and every off-diagonal pairwise gcd, proves the pairwise and full cores are positive for positive inputs, proves every pairwise gcd divides this core, and proves that the quotients d_i/gcd(d_i,C) are pairwise coprime for every finite positive denominator family. It defines their product as the private modulus and proves that this product equals their lcm. Lean proves the weighted CRT survival kernel and specializes it to the canonical weights C/gcd(d_i,C), proving that the canonical collision-weighted numerator is coprime to the entire private modulus. It also proves the sharper local consequence: if a prime divides one private quotient, then pairwise private support excludes it from the leave-one-out product and the canonical gcd-reduced weight excludes it from the remaining factor, so the corresponding one-owner term is automatically nonzero modulo that prime. Lean proves the exact structural formula R=L/C for L=lcm(base,lcm_i d_i): every pairwise collision factor divides the denominator-family lcm, hence C divides L, while the binary deletion identity and its finite-family lift identify the quotient with the private-modulus product. It proves term by term that L/d_i equals the canonical collision weight C/gcd(d_i,C) times the leave-one-out product of the private quotients, so the weighted CRT numerator is literally the common-denominator reciprocal-tail numerator. Finally, under the positive-endpoint ordering, Lean defines Z as the base contribution minus this tail, proves Z+T is zero modulo R, and concludes gcd(Z,R)=1. For nontrivial R, it defines rho=Z mod R and proves 0<rho, rho<=Z, and rho<R, together with the integral Archimedean--CRT closing criterion: scale*Z<=budget*L and budget*L<scale*rho are incompatible. The remaining infinite theorem is quantitative: these explicit residues must satisfy the closing inequality on a cofinal family of factorial blocks.

Evidence/status: advisory_complete_derivation_with_lean_checked_collision_survival_and_endpoint_transport

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

### literal_factorial_block_private_residue_closing_criterion

Lean instantiates the generic collision-core machinery with the literal Erdős #68 prime block: base=(p-1)!, index set {2,...,2p-1}, denominator d_n=n!-1, and coefficient given by the actual strict successor of the (p-1)-prefix. It defines the literal L_p, C_p, R_p, reciprocal-tail numerator T_p, displayed endpoint numerator Z_p, least private residue rho_p, scale 2p^2(2p-1)!, and budget 2p+1. Lean also defines the exact rational endpoint gap E_p=K_{p-1}/(p-1)!-s_{2p-1} and allowance U_p=(2p+1)/(2p^2(2p-1)!), proves termwise that the literal reciprocal block is the actual prefix s_{2p-1}, proves E_p=Z_p/L_p whenever the natural difference is ordinary, and proves E_p>0 supplies that ordering automatically. Hence the endpoint window 0<E_p<=U_p cross-multiplies internally to the exact scaled upper bound. The analytic tail is split exactly into its first omitted term plus the tail after 2p; combining the strict telescope bound with (2p)!>=p+1 proves tail(2p-1)<U_p. If the full series is displayed as a/q with 0<q<=p-1, Lean proves that the strict-successor coefficient divided by (p-1)! equals the series, so E_p is exactly tail(2p-1) and the endpoint window follows. Every literal private quotient and its leave-one-out modulus now have named definitions; Lean proves each quotient divides R_p and each leave-one-out modulus divides R_p. It proves that projecting rho_p or Z_p to such a divisor agrees, and, using Z_p+T_p congruent to 0, that Z_p mod Q is exactly the coefficient-free complementary tail projection (Q-(T_p mod Q)) mod Q. The original two-projection consumer says that the endpoint window is impossible if two complementary tail projections disagree and (2p+1)L_p is smaller than 2p^2(2p-1)! times the smaller leave-one-out modulus. The stronger branch-free consumer defines the pair floor to be the common projection when the views agree and the smaller modulus when they disagree, proves this score is always at most rho_p, and closes the endpoint window whenever the same scale inequality holds with that score. A cofinal family of such unconditional pair-floor certificates proves Irrational factorialGapSeries without a separate disagreement hypothesis. The one-owner consumer remains a correct finite criterion, but Lean now proves it requires L_p below a squared-factorial ceiling; source-verified LCM growth eventually violates that ceiling. The sole viable remaining theorem in this route is therefore a cofinal lower-bound producer for the global residue or the unconditional pair floor.

Evidence/status: lean_checked

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

### global_complementary_tail_residue_reduction

Lean proves the exact global identity rho_p=((R_p-(T_p mod R_p)) mod R_p) whenever the literal endpoint gap is positive. Thus the least private residue itself is coefficient-free, not merely its leave-one-out projections. It packages the direct endpoint contradiction (2p+1)L_p<2p^2(2p-1)!rho_p entirely in terms of T_p and R_p, and proves that a cofinal family of prime blocks satisfying R_p>1 and this single global complementary-residue inequality implies Irrational factorialGapSeries. The two-projection disagreement criterion remains a sufficient local mechanism for the global lower bound, but selecting a pair is no longer part of the minimal open theorem.

Evidence/status: lean_checked_complete_reduction_open_integral_producer

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

claim_boundary: The named declarations establish the exact coefficient-free global residue identity and its conditional cofinal irrationality consumer. They do not produce the required cofinal lower bound for the global complementary residue, prove the endpoint scale inequality for infinitely many prime blocks, or independently prove Erdős #68 irrationality.

### collision_scaled_prefix_fractional_part_reduction

Lean proves C_p R_p=L_p, gcd(T_p,R_p)=1, and the exact rational identity T_p/R_p=C_p*s_(2p-1). For R_p>1, the normalized complementary residue rho_p/R_p is therefore exactly (floor(T_p/R_p)+1)-C_p*s_(2p-1), the positive gap from the collision-scaled genuine prefix to its next integer. After cancelling R_p from the global CRT inequality, Lean proves the complete fractional-part criterion: if cofinally many prime blocks satisfy (2p+1)C_p < 2p^2(2p-1)!*((floor(T_p/R_p)+1)-C_p*s_(2p-1)), then the Erdos #68 series is irrational. This removes L_p and the unnormalized residue from the minimal producer but does not prove the required cofinal lower bound.

Evidence/status: lean_checked_complete_reduction_open_fractional_part_producer

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

### collision_carry_dyadic_block_bridge

Lean proves that if factorialGapStepCarry(m)=1 for every p<=m<=2p, then the normalized strict successor is constant from p-1 through 2p. The strict-successor grid bound at 2p, together with the exact newly added term 1/((2p)!-1), places the p-block endpoint gap inside its explicit endpoint window. Therefore every global complementary-residue certificate, and equivalently every collision-ceiling fractional-part certificate, produces an explicit m in [p,2p] with non-unit carry. Using the exact carry/divisibility equivalence, Lean packages the same witness as a failure of m | strictFacTopRat(factorialGapPrefix(m),m). The same direct exact-miss bridge now applies to a uniquely supported upper-half prime satisfying its explicit owner-size inequality; the owner projection's nonvanishing is automatic. Cofinal certificates of either kind therefore land directly in the cofinal exact-prefix-miss predicate equivalent to Erdős #68. This merges the CRT and carry reductions at their minimal integral interface but leaves their common cofinal producer open.

Evidence/status: lean_checked_exact_bridge_open_shared_producer

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### erdos68_private_projection_scan_through_607

A deterministic pure-integer generator reconstructs L_p, C_p, every private quotient r_n, R_p, T_p, the global complementary residue rho_p=(-T_p) mod R_p, and the selected leave-one-out complementary projections for every prime 11<=p<=607. In all 107 blocks it verifies C_p R_p=L_p, the direct global closing inequality, projection disagreement, and the quotient-cancelled collision-cap certificate. The generator now maintains the exact prefix recurrence T'=T*(L'/L)+L'/d when L'=lcm(L,d), uses lcm_i gcd(d_n,d_i)=gcd(d_n,lcm_i d_i), and orders R_p/r_n by inverse r_n before performing huge divisions. A p<=503 replay reproduced all 92 prior rows, pair runs, and exact-payload digest bit-for-bit in 67.86 seconds. The p<=607 extension finished in 139.74 seconds. The maximizing pairs remain (6,8) through p=109, (6,9) through p=179, (9,7) through p=463, then (7,11) through p=607. Because 503..607 introduces no new transition, that extension is validation coverage rather than a new mathematical advance. The p<=607 exact-payload digest is 40e07ad98e336d349dfe2b2b74fa8fc5d5e42f51276ed21c98cd471d73fc8af8. This remains finite evidence, not a cofinal proof.

Evidence/status: locally_regenerated_exact_finite_only_with_lean_checked_consumer


### erdos68_private_owner_first_repeat_transition_law

An independent exact modular recurrence checker explains every observed private-projection pair transition. The selected owner prime 1753 has first later factorial-one hit 221, so the first prime block containing that collision is p=113; 719 repeats at 359 and exits at p=181; 2999 repeats at 932 and exits at p=467. These are exactly the three recorded pair-run boundaries. The current owner 5039 first repeats at 2519, giving first possible recurrence-driven expiry checkpoint p=1277, while 7853 first repeats at 7841, giving p=3923. Thus the finite staircase is governed by collision renewal at first repeated factorial hits, not by unexplained drift. The result opens a precise cofinal supply target: two owner primes whose next factorial-one hits remain beyond the active block, together with the already checked collision-cap and complementary-projection inequalities. It neither proves that such owners exist cofinally nor proves Erdős #68.

Evidence/status: locally_regenerated_exact_mechanism_map_with_lean_checked_consumer


### erdos68_terminal_wilson_private_owner_pairs

Lean proves that if the Wilson endpoint q-2 is the first factorial-one hit of a prime q>=5, then it is the only hit globally: prefix privacy excludes every smaller index, Wilson excludes q-1, and q divides every factorial from q onward. The reused exact recurrence engine finds 1,801 such terminal-first-hit primes among all 5,133 primes q<=50,000. It also finds 1,799 consecutive comparable pairs whose unique owner indices fit a common factorial block. For the exact canonical pair q=37,41, the globally unique owner indices 35,39 lie in block p=20; both factors divide the private modulus, their complementary projections disagree, and the complete factor-pair scale inequality closes. This fires the existing finite endpoint contradiction while bypassing repeated-hit renewal. The finite census proves no infinitude, density, cofinal certificate supply, cofinal miss, or irrationality theorem.

Evidence/status: lean_checked_global_uniqueness_with_exact_mechanism_pair


### cofinal_anchor_rationality_reduction

Lean checks the complete fixed/cofinal-anchor rationality reduction. For every displayed rational value a/q and every p with q<=p-1, the strict-successor coefficient divided by (p-1)! is exactly the full series; its literal endpoint gap is therefore the positive analytic tail through 2p-1 and satisfies the sharper allowance U_p. The collision-core transport identifies the least private residue with the single coefficient-free global complement ((R_p-(T_p mod R_p)) mod R_p), so any cofinal prime-block family with R_p>1 and (2p+1)L_p<2p^2(2p-1)!rho_p directly proves Irrational factorialGapSeries. Lean now also identifies rho_p/R_p with the gap from C_p*s_(2p-1) to its next integer and cancels L_p=C_p R_p, reducing the same criterion to a lower bound for that upper fractional complement. Unequal leave-one-out projections remain one sufficient mechanism.

Evidence/status: lean_checked_complete_reduction_open_fractional_part_producer

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

### rational_grid_zero_plateau_core

Lean checks the algebraic grid threshold: when qH=k+r and q(S-H)=u, the next q^(-1) grid point (k+1)/q lies below S exactly when 1<=r+u. It also proves the factorial plateau theorem: if H<G<=S, n!G is integral, and n!(S-H)<1, then the strict successor of n!H and the canonical floor of n!S equal the same grid integer.

Evidence/status: lean_checked

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### factorial_plateau_zero_digit_and_exit_carry

Consecutive plateau floors scaling by the next radix force the canonical factorial digit to be zero. Independently, any first-exit offset delta in [0,2) with carry b=-floor(delta) has the rigid alternatives b=0 or b=-1.

Evidence/status: lean_checked

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### first_crossing_gap_denominator_bounds

Lean defines the exact rational factorial-gap prefix, proves its one-step recurrence, and checks that any true crossing H_(tau-1)<G<=H_tau has 0<V=G-H_(tau-1)<=1/(tau!-1). Consequently every displayed positive rational representation V=a/v satisfies v>=tau!-1. Lean further proves the exact actual-prefix scaled-offset identity delta=tau!(H_tau-G)=1+1/(tau!-1)-tau!V, derives delta<2 from the true crossing geometry, and checks that the -1 exit carry is equivalent to V<=1/(tau!(tau!-1)). The complete actual-series wrapper therefore proves v>=tau!(tau!-1) on the -1 branch.

Evidence/status: lean_checked

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### zero_branch_search_through_100000

The return reports an independent GMP interval certificate with no zero-branch event at any index m<=100000 and hence excludes a rational representation with denominator below 100000. This is finite evidence only; the cited executable and source digest were not supplied as local artifacts in this turn.

Evidence/status: external_finite_certificate_not_locally_reproduced


### support_independent_channel_lcm_obstruction

Lean checks that every channel coefficient is congruent to its factorial coefficient modulo d!-1, hence d!-1 divides the difference between the factorial moment and the d-th channel numerator. A zero channel forces d!-1 to divide the moment, and annihilating every channel through D forces their least common multiple L_D to divide the moment.

Evidence/status: lean_checked

- [ChannelIntegralCongruence.lean](problem/ChannelIntegralCongruence.lean)

### factorial_gap_lcm_segment_bound

For k<D, Lean checks the exact finite inequality product_{n=D-k+1}^D(n!-1)<=L_D*D^choose(k+1,3), where choose(k+1,3)=k(k^2-1)/6. The proof factors the product through its lcm and all pairwise gcd collisions, proves gcd(m!-1,n!-1) divides n.descFactorial(n-m)-1, and sums the exact pair distances. This is an elementary derived theorem informed by the verified Garaev-Luca-Shparlinski factorial-congruence source, not a theorem stated verbatim there.

Evidence/status: lean_checked_derived_not_source_stated

- [ChannelIntegralCongruence.lean](problem/ChannelIntegralCongruence.lean)

### one_kernel_radius_preasymptotic_bridge

Lean checks the exact finite bridge behind the absolute-tail one-kernel obstruction. If 0<M, L_D divides M, and M<(R+1)!-1, then L_D<(R+1)!-1 and, for every k<D, ((D+1-k)!-1)^k<((R+1)!-1)*D^choose(k+1,3). Lean also applies global Stirling bounds to derive the explicit logarithmic constraint k*((D+1-k)log(D+1-k)-(D+1-k)-log 2)<(R+1)log(R+1)+choose(k+1,3)log D. On the cofinal square subsequence D=2t^2 with k=2t and t>=4096, Lean proves t^3<8(R+1), packages the sequence-level consequence that 8(R(t)+1)<=t^3 cannot hold eventually, and proves in Mathlib notation that the radius is not o(t^3), equivalently not o(D^(3/2)) after this reparameterization. This is an explicit derived cubic-radius obstruction; only the sharp constant 4sqrt(2)/9 remains advisory.

Evidence/status: lean_checked_derived_not_source_stated

- [ChannelIntegralCongruence.lean](problem/ChannelIntegralCongruence.lean)

### one_kernel_radius_three_halves_square_subsequence

A strengthened finite proof retains the lower bound D+1-k >= (15/8)t^2 on D=2t^2, k=2t. Lean proves that for t>=2^32 the channel hypotheses force 3t^3<2(R+1), equivalently R+1>(3/2)t^3, and packages the sequence-level consequence that the competing upper bound 2(R(t)+1)<=3t^3 cannot hold eventually. In D-coordinates the checked constant is 3/(4sqrt(2)), strictly below the advisory optimum 4sqrt(2)/9.

Evidence/status: lean_checked_derived_not_source_stated

- [ChannelIntegralCongruence.lean](problem/ChannelIntegralCongruence.lean)

### one_kernel_sharp_radius_log_constraint_boundary

Lean proves the exact collision identity 3*choose(2t+1,3)+t=4t^3 and then shows that, for t>=4, the existing square-subsequence logarithmic constraint is already satisfied whenever 9(R+1)=16t^3. On the infinite t divisible by 3 subsequence this is exactly R+1=(16/9)t^3, or the optimized constant 4sqrt(2)/9 in D=2t^2 coordinates. Therefore the present logarithmic constraint cannot force a strict lower bound at the sharp constant. The theorem does not prove the family of subcritical bounds; formalizing that liminf family, or strengthening the finite factorial-segment input, is the surviving one-kernel route.

Evidence/status: lean_checked_mechanism_elimination

- [ChannelIntegralCongruence.lean](problem/ChannelIntegralCongruence.lean)

### channel_affine_integral_normal_form

For every finite integer support and every d>=2, Lean produces an integer k with V_d=M+(d!-1)k. Consequently every zero-moment support variation changes the normalized d-th channel contribution by an integer only.

Evidence/status: lean_checked

- [ChannelIntegralCongruence.lean](problem/ChannelIntegralCongruence.lean)

### canonical_channel_kernel_D2_D12

Exact integer regeneration verifies the returned canonical primitive kernels for every 2<=D<=12: all channels 2 through D vanish, the factorial moment is L_D, and the coefficient content is one.

Evidence/status: locally_regenerated_exact_computation


### D9_channel_denominator_exclusion

Exact Fraction arithmetic reproduces the displayed D=9 vector with moment L_9=31540008254514077395 and verifies 1353/100000<R_9<1354/100000 after the stated prime-unit shift. This is a finite denominator exclusion, not an irrationality proof.

Evidence/status: locally_regenerated_exact_finite_only


### prime_unit_translator_arithmetic

For every prime p, Lean checks the coefficient-index pair (p,-1) on (p-1,p): its factorial moment is zero; every channel d<p vanishes via the exact quotient identity floor((p-1)/d)=floor(p/d); every channel d>p vanishes because both indices lie below d; and the p-channel numerator is exactly p!-1. Lean defines the full infinite real channel residual beyond D and proves that for D<p the translator residual is exactly 1, while scaling its coefficients by any integer z gives residual exactly z. It also proves the reciprocal factorial-gap series is summable, every finite-support residual is summable, and the full residual is additive both on a fixed finite support and across disjoint finite supports.

Evidence/status: lean_checked

- [PrimeUnitTranslator.lean](problem/PrimeUnitTranslator.lean)

### conditional_rank_two_nearest_integer_rounding

Given any finite-support integer vector that annihilates every channel 2 through D and has nonzero factorial moment, and any prime p>D, Lean constructs a disjoint-support enlargement by an integer multiple of the prime translator. The enlargement preserves every requested zero channel and the original nonzero factorial moment, while nearest-integer rounding makes the full infinite channel residual have absolute value at most 1/2. Under the additional exact hypothesis that the base residual is not an integer, Lean proves the rounded residual is strictly nonzero. This is the exact axiom-free rounding consequence of the returned rank-two architecture; proving the nonintegrality hypothesis remains an open producer.

Evidence/status: lean_checked_derived_not_source_stated

- [PrimeUnitTranslator.lean](problem/PrimeUnitTranslator.lean)

### cramer_nonzero_moment_channel_kernel_producer

For any finite support of size n+1, Lean defines the square augmented matrix with factorial moment as its first row and channel numerators 2 through n+1 as the remaining rows. Cramer's rule constructs an explicit integer coefficient vector whose factorial moment is exactly the matrix determinant and whose every channel row vanishes. Hence a single nonzero-determinant hypothesis produces the nonzero-moment channel-kernel direction required by the rank-two rounding theorem.

Evidence/status: lean_checked_derived_not_source_stated

- [PrimeUnitTranslator.lean](problem/PrimeUnitTranslator.lean)

### uniform_factorial_grid_rank_two_reduction

For every cutoff D>=2 and support threshold B, Lean now constructs a remote labelled finite support from D consecutive factorial-grid columns together with a prime translator pair, all indices greater than B. With the common square scale (D!)^2, it proves exact strict monotonicity of the integer factorial-root nodes, injectivity of their rational reciprocals, nonvanishing of every shifted Vandermonde determinant, exact equality between the normalized augmented channel/moment matrix and that shifted Vandermonde matrix, and therefore nonvanishing of the original integer augmented determinant. Cramer's rule then supplies a zero-channel vector with nonzero factorial moment, while the prime translator reduces its full residual to absolute value at most 1/2. Under the explicit hypothesis that the un-translated grid residual is not an integer, the new strict remote consequence also makes the translated residual nonzero while preserving the same support and moment conclusions. This closes the returned uniform determinant and rank-two Archimedean producers without a support-matroid basis exchange. The labelled construction uses D+2 coordinates rather than the advisory minimal D+1 after merging a duplicate prime predecessor; this does not affect the channel/moment/residual conclusions. Strict residual nonvanishing remains the sole unresolved producer in this route because the nonintegrality hypothesis is not supplied.

Evidence/status: lean_checked_derived_not_source_stated

- [PrimeUnitTranslator.lean](problem/PrimeUnitTranslator.lean)

### cramer_tail_determinant_and_eventual_nonvanishing

Lean now proves the exact adjugate identity that evaluating a Cramer vector against any row equals the determinant obtained by replacing the distinguished moment row by that row. Consequently every factorial-grid tail-channel numerator is one explicit row-replacement determinant, including channels whose floor quotients are not affine. Lean also proves that beyond the largest grid support index every such numerator equals the fixed nonzero factorial moment, so all channel numerators are eventually nonzero. This isolates the only difficult sign/cancellation region to the finite floor-discontinuous block between the cutoff and the largest support.

Evidence/status: lean_checked_derived_not_source_stated

- [PrimeUnitTranslator.lean](problem/PrimeUnitTranslator.lean)

### full_residual_mod_integers_classification

For every finite-support integer coefficient vector and every cutoff D>=1, Lean defines the universal factorial-gap tail T_D and a canonical finite integral correction, then proves R_D(c)=M(c)T_D+K for some integer K. If channels 2 through D vanish, Lean further proves R_D(c)=M(c)S+K, where S is the original Erdős #68 series. For the uniform factorial-grid Cramer kernel, M(c) is exactly the nonzero augmented determinant, so its residual modulo integers is det(A)S. This closes the previously advisory infinite-tail classification and proves that prime translation changes only the integral coordinate.

Evidence/status: lean_checked_derived_not_source_stated

- [PrimeUnitTranslator.lean](problem/PrimeUnitTranslator.lean)

### D3_rank_two_denominator_exclusion

Exact Fraction arithmetic verifies that c=(-40,55,-10,1) on support (3,4,5,6) annihilates channels 2 and 3, has moment 600, and satisfies 0.09925341997208298<L_3(c)<0.09925341997208300. This excludes denominators dividing 600 only.

Evidence/status: locally_regenerated_exact_finite_only


### cofinal_exact_prefix_divisibility_characterization

For every m>=3, Lean proves that the unit-carry condition is equivalent to the purely integral test m | strictFacTopRat(factorialGapPrefix(m),m). Consequently Erdős #68 is equivalent, in both directions, to cofinally many failures of this exact rational-prefix divisibility test. The CRT collision-ceiling route now has a direct checked consumer into this same predicate: one certificate at p produces a miss in [p,2p], and cofinal certificates produce cofinal misses. This removes the prime restriction, real predecessor gap, and real floor from the final producer interface, but does not prove the required cofinal certificates or misses.

Evidence/status: lean_checked_derived_not_source_stated

- [FactorialZeroPlateau.lean](problem/FactorialZeroPlateau.lean)

### prime_unit_carry_endpoint_cylinder_dichotomy

For every m>=2, Lean proves the exact relation strictFacTop(factorialGapPrefix(m),m)=facFloor(S,m)+h_m with h_m in {0,1}, and hence the exact carry identity b_m=1-d_m+m*h_(m-1)-h_m. A unit carry occurs exactly in one of two branches: the lower branch has canonical digit zero and both endpoint flags zero, equivalently m*theta_(m-1)<R_m; the upper branch has maximal canonical digit m-1 and both flags one, equivalently (m-1)+R_m<=m*theta_(m-1). Lean further eliminates the full-series remainder from the lower branch: if Delta_m is the strict-successor gap of the finite rational prefix through m-1, then Delta_m=R_(m-1)-theta_(m-1)+h_(m-1), and the lower branch is exactly 1+1/(m!-1)<m*Delta_m<=1+1/(m!-1)+R_m. It also proves the explicit tail bound R_m<2/m, so the purely finite-prefix threshold 1+1/(m!-1)+2/m<=m*Delta_m forces either a non-unit carry or the useful maximal-digit branch. Writing Q_m=(m-1)!*factorialGapPrefix(m-1), v_m=den(Q_m), and u_m=(floor(Q_m)+1)v_m-num(Q_m), Lean proves 1<=u_m<=v_m, gcd(u_m,v_m)=1, and Delta_m=u_m/v_m. The sufficient threshold is exactly the pure integer inequality ((m+2)m!-2)v_m<=m^2(m!-1)u_m. Lean also proves the exact reduced-gap recurrence Delta_(m+1)=m*Delta_m-1/(m!-1)-b_m. The integer carry does not affect its denominator transition: v_(m+1) divides v_m*(m!-1), while v_m divides m*v_(m+1)*(m!-1). Hence every prime q dividing v_m persists in v_(m+1) unless q divides m or m!-1. The recurrence is now retained at full multiplicity: any composite divisor d of v_m persists when d is coprime to the radix and new gap, while every divisor d of m!-1 coprime to v_m enters v_(m+1) in full. In particular, if q^e divides m!-1 and q is absent from v_m, then q^e divides v_(m+1). Prefix privacy excludes q from v_m, so every supplied prefix-private prime power enters in full; under m+1<q it also survives to v_(m+2). Conversely, if q divides m!-1 but not v_m, then q must enter v_(m+1); the persistence law iterates across every finite interval that avoids q in both the intervening radices and factorial gaps. Lean further proves that prefix privacy itself excludes q from v_m, so every prefix-private prime divisor of m!-1—including the existing least-hit anchors supplied from Li Lai's theorem—automatically enters v_(m+1). Under the explicit cofinal source hypothesis that arbitrarily remote n!-1 have a prime divisor q>n, Lean promotes those least hits to cofinally many m with m<q and q dividing v_(m+1). Li Lai's source-verified theorem supplies this hypothesis, so this is a source-plus-Lean cofinal actual-denominator anchor theorem. Under the one-unit-stronger hypothesis n+1<q, Lean now proves that the same least-hit prime is present simultaneously in v_(m+1) and v_(m+2): it cannot divide the intervening radix m+1, while simultaneous divisibility of m!-1 and (m+1)!-1 would force q to divide m. Li Lai's stronger linear factor q>(1+9 log 2-epsilon)n supplies this hypothesis after a finite threshold. This gives cofinally many two-step anchors, now with their complete supplied prime-power valuations, but not yet many anchors at one common remote endpoint. Reduced coprimality proves more generally that every nontrivial divisor d of v_m sees a nonzero least nonnegative residue u_m mod d, so the source-backed prime anchors give cofinally many nonzero actual numerator projections. Lean proves the quantitative CRT closer: if cofinally many denominator divisors d have projected residues large enough to satisfy ((m+2)m!-2)v_m<=m^2(m!-1)(u_m mod d), then the series is irrational. Any such certificate necessarily satisfies the strict size bound ((m+2)m!-2)v_m<m^2(m!-1)d, so a small isolated denominator prime is insufficient; the operative target is a large CRT divisor carrying a quantitatively large residue. Lean also connects this reduced pair to the existing block CRT route: the block endpoint gap at p is exactly u_p/(v_p*(p-1)!)-(factorialGapPrefix(2p-1)-factorialGapPrefix(p-1)), so the full endpoint window is equivalent to an explicit thin rational cylinder for u_p/v_p. Cofinally many threshold certificates imply irrationality directly. Cofinal prime escape from the lower cylinder is another checked sufficient condition. The denominator recurrence opens a prime-orbit producer with prime-power mass preserved, but no theorem yet builds cofinally many sufficiently large actual-denominator CRT divisors and proves the required numerator-residue lower bound.

Evidence/status: lean_checked_conditional_closer_producer_open

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

### prime_indices_do_not_automatically_meet_predecessor_threshold

With the recurrence indexed correctly—testing Delta_m before advancing to Delta_(m+1)—exact Fraction arithmetic shows that the tail-free predecessor-gap threshold holds at m=3 but already fails at the next prime m=5, where Delta_5=18/115 and the cleared right-minus-left margin is -42820. Therefore the universal every-prime assertion is false. This finite counterexample does not rule out an eventual-prime theorem permitting finitely many exceptions; indeed, the certified spectrum through 300000 has no prime failure after 23. It does not say that b_5 is a unit carry, and the strictly thinner prime lower-cylinder escape target also remains open.

Evidence/status: exact_finite_prime_supply_mechanism_elimination

- [check_erdos68_prime_predecessor_threshold.py](formal_math/erdos257_period_noncollapse/scripts/check_erdos68_prime_predecessor_threshold.py)

### reduced_denominator_prime_finset_crt_consumer

For any finite set S of distinct primes that each divide the actual reduced denominator v_m, Lean proves that the squarefree product d_S=prod(q in S) q divides v_m. If S is nonempty, then d_S>1 and reduced coprimality forces u_m mod d_S to be nonzero. Lean also proves synchronous interval persistence: if every q in S divides v_a and avoids each intervening radix j and factorial gap j!-1 for a<=j<b, then d_S divides v_b and u_b mod d_S is nonzero. The stronger composite form transports any full divisor d of v_a through such an interval whenever d is coprime to every intervening radix and gap, and returns a nonzero projection u_b mod d; prime-power valuations are not discarded during transport. Lean now also packages heterogeneous accumulation: a finite pairwise-coprime family of composite moduli may enter at different indices, each survive its own avoidance interval, and their full product divides one common remote v_n; positivity plus one nontrivial component gives a nonzero u_n projection modulo the entire product. The prefix-private entry theorem is finset-valued: every selected prefix-private prime factor of one m!-1 enters the same v_(m+1), so their squarefree product is one actual CRT modulus with a nonzero numerator projection. Lean defines the canonical set of all prime factors q of m!-1 with q>m+1 that are coprime to every earlier factorial gap, and its squarefree product D_m. If this set is nonempty, D_m divides both v_(m+1) and v_(m+2), and the combined numerator projection is nonzero at both endpoints. Under the explicit cofinal large-prime source hypothesis n+1<q, Lean proves these canonical sets are nonempty cofinally often and returns the two denominator divisibilities and both nonzero projections. The squarefree interface is no longer the multiplicity ceiling: Lean proves arbitrary composite-divisor entry and persistence under the exact coprimality hypotheses, so every prefix-private q^e dividing m!-1 enters v_(m+1) in full and survives to v_(m+2) when m+1<q. It defines the canonical multiplicity-sensitive same-gap modulus P_m as the product, over the same selected primes q, of q raised to its complete valuation in m!-1. Lean proves P_m divides m!-1, is coprime to v_m, divides both v_(m+1) and v_(m+2), and—when the selected set is nonempty—has nonzero numerator projections at both endpoints. Distinct P_m are automatically pairwise coprime because a prime first selected at a later gap is coprime to every earlier gap. Lean then defines a canonical endpoint accumulator from all source moduli that survive intact and proves it divides v_n. More sharply, it defines active source-prime pairs (m,q), retains each full q-adic valuation independently when it survives to n, proves all such prime-power components pairwise coprime, and proves their canonical componentwise product E_n divides v_n with u_n mod E_n nonzero whenever the active set is nonempty. Direct conditional irrationality theorems consume the projected-residue threshold modulo P_m, the whole-source accumulator, or the sharper componentwise E_n. This discharges the source-to-canonical bridge, same-gap prime-power assembly, composite interval persistence, heterogeneous common-endpoint assembly, canonical componentwise accumulation, and prime-power retention. The remaining producer is quantitative: prove cofinally that E_n captures enough of v_n and that u_n mod E_n meets the displayed threshold; mere nonvanishing is insufficient.

Evidence/status: lean_checked_conditional_closer_producer_open

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

### componentwise_accumulator_birth_survival_recurrence

Lean now makes the componentwise accumulator dynamic. For every already-born source pair (m,q) with m<n, membership at endpoint n+1 is equivalent to membership at n together with coprimality of q to the new radix n and new gap n!-1. The pairs born at source n and active at n+1 are exactly the canonical prefix-private primes of n!-1, because their avoidance interval is empty. Lean defines the surviving set, killed set, and born set and proves the exact disjoint decompositions Active_n=Survive_n union Kill_n and Active_(n+1)=Survive_n union Born_n. If S_n and K_n are the corresponding products and P_n is the full new prefix-private prime-power product, it follows kernel-checkably that E_n=S_n*K_n, E_(n+1)=S_n*P_n, and hence E_(n+1)*K_n=E_n*P_n. Defining the residual collision/re-entry cofactor C_n=v_n/E_n and the denominator reduction normalizer G_n=v_n*(n!-1)/v_(n+1), Lean proves both E_n*C_n=v_n and the exact residual recurrence C_(n+1)*G_n*P_n=C_n*(n!-1)*K_n. The cancellation side is also witnessed prime by prime: every old denominator prime colliding with n or n!-1 divides G_n, so every prime label in the killed set divides G_n, and the product of the distinct killed labels divides G_n. Lean now isolates multiplicity exactly. Set H_n=gcd(K_n,G_n), D_n=K_n/H_n, and R_n=G_n/H_n. The squarefree killed-prime product divides H_n, D_n and R_n are coprime, and cancellation gives the sharper recurrence C_(n+1)*R_n*P_n=C_n*(n!-1)*D_n. Finally set B_n=(n!-1)/P_n, the unselected part of the new factorial gap. Since P_n is positive and divides n!-1, Lean cancels it too and obtains the intrinsic recurrence C_(n+1)*R_n=C_n*B_n*D_n. Every prime divisor q of B_n is now proved to divide k!-1 for some 2<=k<n. The only apparent alternative from the definition is q=n+1; Wilson's theorem excludes it because n! is congruent to -1, not 1, modulo the prime n+1. Hence B_n has exclusively repeated support; every genuinely new prime entered P_n with its complete valuation. The repeat witness can moreover be chosen with k+1<n, q dividing the exact intervening collision n.descFactorial(n-k)-1, and q<=n^(n-k). Lean also proves that B_n retains q to the complete current-gap exponent v_q(n!-1), so the remaining birth-side obstruction is exactly repeated-prime multiplicity amplification rather than missing support. Taking q-factorizations of the intrinsic recurrence gives the exact additive conservation law c_(n+1)(q)+r_n(q)=c_n(q)+b_n(q)+d_n(q). Every prime q in D_n is now traced to an exact killed active source component a with label a.2=q, and Lean proves that q collides at the current transition through q dividing n or q dividing n!-1. Thus D_n has no mysterious prime support; only excess multiplicity on already tracked killed components remains. Because D_n and R_n are coprime, every defect prime has zero reduced-outflow valuation, its residual valuation grows strictly at the next endpoint, and the complete multiplicity-sensitive modulus D_n divides C_(n+1). For repeated-birth support, Lean now isolates the exact competing mechanism: if q divides B_n but not R_n, then the q-adic residual valuation grows strictly; conversely, failure of that growth forces q into R_n and supplies an explicit cancellation certificate. Globally and with full prime-power multiplicity, Lean proves B_n/gcd(B_n,R_n) divides C_(n+1), so the gcd is exactly the portion of repeated birth mass that can be lost to simultaneous outflow. More strongly, the entire overlap gcd(B_n,R_n), with multiplicity, divides the old reduced denominator v_n; primewise it therefore lies in the old accumulator E_n or old residual C_n. These two divisibilities combine into the two-time conservation law B_n divides v_n*C_(n+1), and hence B_n<=v_n*C_(n+1). If a repeated-birth prime is absent from v_n, cancellation is impossible and its residual valuation grows strictly. Consequently, if a prime newly enters C_(n+1) and was present in neither C_n nor D_n, Lean forces it into B_n and supplies the nonadjacent descending-factorial collision witness and power bound. Combining this with the exact killed-source certificate gives a complete classification of every genuinely new residual prime into repeated-gap inflow or killed-source defect inflow. Thus residual denominator mass has exactly two inflow mechanisms—repeated new-gap mass B_n and excess killed multiplicity D_n—and one outflow R_n, both globally and prime by prime. The numerical cofactor pattern is therefore an exact arithmetic dynamical system, not an unexplained finite artifact. The sharpened birth-side bottleneck is now the overlap of repeated-gap valuations with R_n; bounding that cancellation, repeated-prime multiplicity amplification, C_n, D_n, and the projected numerator residue cofinally remains open.

Evidence/status: lean_checked_derived_not_source_stated

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

### repeated_birth_multiplicity_amplification_survives

Lean now sharpens the repeated-birth/outflow overlap at full q-adic multiplicity. If q divides B_n, every active old q-component is killed at the same transition, so ord_q(E_n)=ord_q(K_n), while B_n retains exactly ord_q(n!-1). From H_n=gcd(K_n,G_n), R_n=G_n/H_n, E_n*C_n=v_n, and gcd(n!-1,G_n) dividing v_n, Lean proves that ord_q(R_n)>ord_q(C_n) forces ord_q(n!-1)<=ord_q(v_n). Contrapositively, genuine current-gap multiplicity amplification ord_q(v_n)<ord_q(n!-1) cannot be absorbed by normalized outflow. The exact intrinsic recurrence then forces the complete power q^ord_q(n!-1) to divide C_(n+1). Lean packages all such repeated primes into the canonical full-multiplicity product A_n=prod_{q|B_n, ord_q(v_n)<ord_q(n!-1)} q^ord_q(n!-1), proves A_n|B_n and A_n|C_(n+1), hence A_n|gcd(B_n,C_(n+1)) and A_n|v_(n+1). Whenever the amplification set is nonempty, A_n>1 and reduced coprimality gives u_(n+1) mod A_n != 0. Thus the remaining repeated-birth cancellation problem is confined to non-amplifying collisions where the current factorial-gap valuation does not exceed the whole old denominator valuation; a cofinal lower bound for A_n, or a quantitative bound on the non-amplifying exceptional mass, would feed an actual full-multiplicity denominator and numerator projection rather than only prime support.

Evidence/status: lean_checked_derived_not_source_stated

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

### repeated_factorial_gap_valuation_record_bridge

Lean proves that the reduced predecessor denominator v_n divides lcm_{2<=k<n}(k!-1). Therefore, if a repeated prime q reaches a strict new valuation record in n!-1, then ord_q(v_n)<ord_q(n!-1), its complete current power enters both C_(n+1) and the actual denominator v_(n+1), and the reduced next numerator is nonzero modulo that power. The square specialization is now connected exactly to the two verified source families. For every prime p, with W_p=((p-1)!+1)/p, Lean proves W_p congruent to 1 modulo p if and only if p^2 divides (p-2)!-1. A half-factorial +1 hit p|((p-1)/2)!-1 supplies the earlier repeated support; the Wilson congruence supplies the square hit at p-2; and a no-earlier-square condition makes it a strict valuation record. The joint theorem then forces p^2 into C_(p-1) and the actual denominator v_(p-1), with a nonzero reduced-numerator projection. Lean kernel-checks the first concrete instance p=107: Elia's half-factorial list independently contains 107, while the checked arithmetic gives 107|53!-1, W_107 congruent to 1 modulo 107, 107^2|105!-1, and no 2<=j<105 with 107^2|j!-1; hence 107^2|C_106, 107^2|v_106, and u_106 mod 107^2 is nonzero. Lean now also kernel-checks the first nonterminal instance: 971|361!-1, 971^2|609!-1, no 2<=j<609 has 971^2|j!-1, and 609<971-2; hence 971^2|C_610, 971^2|v_610, and u_610 mod 971^2 is nonzero without using the Wilson endpoint. The Wilson equivalence and both denominator consequences are derived, not statements made in either source, and the certificates are finite rather than a cofinal supply theorem.

Evidence/status: source_verified_crosswalk_and_lean_checked_derived_not_source_stated_with_exact_finite_certificate

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

### wilson_half_factorial_joint_scan_through_50000

A deterministic Eratosthenes sieve and exact modular-factorial scan checks every prime p<=50000. The generalized order-2 near-Wilson primes are exactly 2,3,11,107,4931, matching OEIS A079853. Among them, exactly p=107 and p=4931 also have p congruent to 3 modulo 4, ((p-1)/2)! congruent to +1 modulo p, and no earlier factorial k! with 2<=k<p-2 congruent to 1 modulo p^2. Independent unrestricted Python big-integer factorials recheck the terminal and half-factorial residues for all five near-Wilson primes. Thus the checked joint denominator-record pattern has a second exact finite event at p=4931, not only p=107. The p=4931 universal first-square scan is receipt authority rather than a Lean-kernel theorem. OEIS reports no other A079853 term below 4*10^11; that much larger external search bound was not locally reproduced.

Evidence/status: locally_regenerated_exact_finite_only_with_external_sequence_crosscheck


### arbitrary_factorial_gap_valuation_record_scan_through_1000000

A deterministic parallel C++ scan checks every one of the 78,498 primes q<=1,000,000 and every possible q-support index 2<=n<q using exact q^2 modular arithmetic. An independent Python q^3 implementation reproduces the complete 5,133-prime prefix through q=50,000, and unrestricted full-integer factorials independently reproduce every square-prime trace. Exactly six primes have any square hit q^2|n!-1, at (q,n)=(11,9),(31,15),(107,105),(571,112),(971,609),(4931,4929); there is no additional square hit from 50,000 through 1,000,000. Exactly three of these are strict valuation records after an earlier q-hit: q=107 from 53 to 105, q=971 from 361 to 609, and q=4931 from 2327 to 4929. There is no cube hit in the interval. The q=971 event is genuinely nonterminal because 609<971-2, so the arbitrary-index repeated-record family is strictly larger than the Wilson n=q-2 subfamily. Lean kernel-checks its complete square entry into the endpoint-610 reduced denominator and the resulting nonzero numerator projection; q=4931 remains receipt-authority finite evidence. Separately, Costa--Gerbicz--Harvey Table 1 is complete for 10^6<p<2*10^13 with least absolute Wilson residue |w_p|<=10 and contains no w_p=+1 row; their independent validation recomputed all 27,039,026 saved small residues with complete agreement. Since w_p=+1 is exactly W_p congruent to 1 modulo p, this source rules out every terminal Wilson square birth throughout that interval. It does not rule out nonterminal n! congruent to 1 modulo p^2 events such as q=971,n=609.

Evidence/status: locally_regenerated_exact_finite_only_with_source_verified_terminal_exclusion


### nonterminal_factorial_square_lift_linearization

Lean linearizes every arbitrary nonterminal square lift. If a prime q divides both k!-1 and n!-1 with k<n, then q also divides D-1 for the intervening descending-factorial block D=n.descFactorial(n-k). Writing k!=1+qA and D=1+qB, Lean proves q^2|n!-1 if and only if q|(A+B); equivalently A=(k!-1)/q and B=(D-1)/q cancel modulo q. This converts the opaque square-divisor event into a first-order quotient-balance target over the same interval collision already exposed by the exact gcd identity. Existing factorial-congruence sources bound or distribute hits modulo q but do not currently control this quotient balance modulo q, so the equivalence is a reduction rather than a cofinal supply theorem.

Evidence/status: lean_checked_exact_equivalence_open_distribution_producer_pending

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

### transition_normalizer_numerator_projection

Let G_m=v_m*(m!-1)/v_(m+1) be the exact natural-number factor cancelled when the raw denominator is reduced at the next step. Lean proves v_(m+1)*G_m=v_m*(m!-1) and the denominator-free numerator recurrence G_m*u_(m+1)=m*u_m*(m!-1)-v_m-b_m*v_m*(m!-1). Consequently every divisor d of m!-1 satisfies the exact entry congruence G_m*u_(m+1)=-v_m (mod d). Lean further proves that every genuinely new prime q is coprime to G_m; for each canonical prefix-private source it lifts this to the complete q-adic component q^ord_q(m!-1) and packages both invertibility and the full prime-power congruence. Thus the component's numerator class is exactly -v_m/G_m modulo its complete entering power, not merely nonzero. The remaining task is to combine these explicit component classes by CRT and prove their least nonnegative representative has the required Archimedean size.

Evidence/status: lean_checked_derived_not_source_stated

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

### componentwise_accumulated_private_power_finite_diagnostic

Exact Fraction arithmetic and complete factorization through n=39 distinguish the canonical accumulators sharply. The residual cofactor C_n=v_n/E_n is 23 on n=9..11, 4301=11*17*23 on n=12..17, 253=11*23 on n=18..22, 23 at n=23, 1 on n=24..27, 29 on n=28..29, 56699=31^2*59 on n=30..31, 1829=31*59 on n=32..37, and 96937=31*53*59 on n=38..39. Thus E_n recovers the full denominator and satisfies the irrationality threshold on n=24..27, while the missed mass elsewhere evolves in structured prime-collision blocks. The normalized killed multiplicity defect D_n=K_n/gcd(K_n,G_n) is nontrivial at only two transitions through n=39: D_11=11, where K_11=11^2*17, gcd(K_11,G_11)=11*17, and R_11=23; and D_29=31, where K_29=31^2*59, gcd(K_29,G_29)=31*59, and R_29=29. It is 1 at every other transition in this range. The intrinsic recurrence reproduces every cofactor change exactly. Its nontrivial inflow/outflow rows are (B_8,D_8,R_8)=(23,1,1), (B_11,D_11,R_11)=(17*23,11,23), (B_15,D_15,R_15)=(17,1,17), (B_17,D_17,R_17)=(1,1,17), (B_21,D_21,R_21)=(23,1,23), (B_22,D_22,R_22)=(1,1,11), (B_23,D_23,R_23)=(1,1,23), (B_27,D_27,R_27)=(29,1,1), (B_29,D_29,R_29)=(31*59,31,29), (B_31,D_31,R_31)=(1,1,31), and (B_37,D_37,R_37)=(53,1,1). Replacing prefix-private birth by first-fresh-at-m birth produces the same quotient pattern through 35, so that relaxation does not recover the residual mass. The coarser whole-source product at n=24 and n=25 is smaller than E_n by the exact factor 440886679217936976887 and fails the threshold. This is finite evidence only; it supplies no cofinal bound for C_n, B_n, D_n, or the projected residue.

Evidence/status: locally_regenerated_exact_finite_only


### endpoint_prime_truncated_repeated_hit_layers

For p>=2 and every prime q above the displayed endpoint 2p-1 that hits an upper factorial gap, Lean rewrites the complete normalized-collision valuation as the number of repeated-hit layers in the fixed interval 1<=e<=2p-4. The earlier exact identity used the a priori range 1<=e<=q-1; the hit-count packing inequality now proves that every repeated layer above 2p-4 is impossible. This closes the local layer-truncation step uniformly in q. It does not bound the number of endpoint primes, sum the surviving e log q weights, prove the normalized collision cap, supply the complementary residue, or resolve Erdős #68.

Evidence/status: lean_checked_exact_local_truncation_open_weighted_global_aggregation

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Prove the weighted global aggregation over endpoint primes strongly enough for the normalized collision cap, and independently force the complementary projection or residue cofinally.

### endpoint_prime_anchor_free_incidence_cutoff

For every prime q strictly above the displayed endpoint 2p-1 and every exponent e>0, Lean proves q^e divides the normalized factorial-block collision core if and only if q^e divides more than one displayed factorial gap. Unlike the preceding incidence theorem, this endpoint-prime form needs no chosen upper-hit index or anchor hypothesis. Hence any full-block at-most-one estimate for q^e forces the normalized q-valuation below e; at e=2, at-most-one q^2 incidence makes the endpoint-prime part squarefree. This exposes the exact source-to-consumer interface for future factorial-congruence estimates. It does not itself prove the uniform q^2 incidence premise, bound the number or product of endpoint primes, perform the weighted aggregation, supply the complementary residue, or resolve Erdős #68.

Evidence/status: lean_checked_anchor_free_endpoint_incidence_interface_open_uniform_source_bound

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Supply the uniform endpoint-prime incidence bound and weighted global product estimate required for the normalized collision cap, and independently force the complementary projection or residue cofinally.

### base_omitted_prime_anchor_free_incidence_cutoff

Lean generalizes the anchor-free normalized-collision interface from primes above the block endpoint to every prime q absent from the predecessor-factorial base (p-1)!. For every such q and every e>0, q^e divides the normalized collision core exactly when q^e hits more than one displayed factorial gap. Therefore an at-most-one q^e incidence estimate forces normalized q-valuation below e, and at-most-one q^2 incidence makes the q-part squarefree. Every prime q>=p is base-omitted, so the interface now covers the full moving prime range at and above the block parameter rather than only q>2p-1. It does not itself prove the incidence premise, control primes below p that already divide the base, aggregate the complete prime-power product, supply the complementary residue, or resolve Erdős #68.

Evidence/status: lean_checked_base_omitted_prime_incidence_interface_open_uniform_source_bound

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

surviving_obligation: Supply the uniform base-omitted-prime incidence bound and weighted global product estimate required for the normalized collision cap, and independently force the complementary projection or residue cofinally.

### universal_prime_power_spacing_and_global_block_diameter_ceiling

Lean globalizes the factorial-gap spacing mechanism to every prime. If q is prime and q^e divides two displayed gaps at indices i<j, then e<j-i; no endpoint or base-omission hypothesis is needed because any prime divisor of j!-1 is automatically larger than j. Consequently, for p>=2 and every prime q, the number of q^e hits satisfies hitCount(q^e)*(e+1)<=2p+e-2. Applying the same spacing theorem to the two-hit characterization of the normalized collision core gives a global primewise diameter ceiling: whenever q divides the normalized core, its complete normalized valuation plus its full valuation in the predecessor base (p-1)! is strictly less than 2p-3. This subsumes the earlier endpoint-only packing and diameter interfaces and extends the local ceiling to primes already present in the base. It does not bound how many collision primes occur, sum their weighted valuations, prove the normalized collision product cap, supply the complementary residue, or resolve Erdős #68.

Evidence/status: lean_checked_universal_local_spacing_open_weighted_global_aggregation

- [EndpointWeightedPrivateSupport.lean](problem/EndpointWeightedPrivateSupport.lean)

claim_boundary: Lean proves the primewise spacing, hit-count packing, and valuation-plus-base block-diameter ceilings for each fixed prime. These local inequalities do not bound the number of collision primes or sum their weighted valuations. They therefore do not prove the normalized collision-product cap, force the complementary residue, establish irrationality, or resolve Erdős 68.

surviving_obligation: Prove a weighted global aggregation over all collision primes strong enough for the normalized collision cap, and independently force the complementary projection or residue cofinally.

### wilson_reflection_normalized_collision_and_full_block_incidence_bridge

Lean now carries Wilson reflection through the predecessor-factorial normalization used by the live Erdős 68 collision interface. Let q be prime and n odd, with p<=n, both n and q-n-1 in the displayed factorial block, q<2n+1 so the reflected index is earlier, and q dividing n!-1. Then q divides the normalized factorial-block collision core and the full-block q-hit count is greater than one. The first theorem packages the existing reflected two-hit collision theorem with the upper-half base-omission theorem; the second exposes the resulting repeated incidence directly. This proves that such a reflected linear-size factor survives normalization, but it neither produces a suitable prime on a cofinal family of blocks nor bounds the weighted product of all collision primes, supplies the complementary residue, or resolves Erdős #68.

Evidence/status: lean_checked_reflection_to_normalized_core_open_weighted_global_aggregation

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

surviving_obligation: Prove a cofinal weighted global aggregation over all collision primes strong enough for the normalized collision cap, and independently force the complementary projection or residue.

### predecessor_gap_certificate_fires_generically

The tail-free predecessor-gap certificate had no computational coverage. Since u_m/v_m = floor(Q_m) + 1 - Q_m = 1 - frac(Q_m), the literal integer inequality ((m+2)m!-2)v_m <= m^2(m!-1)u_m is exactly the condition frac(Q_m) <= 1 - 1/m - 2/m^2 - 1/(m(m!-1)) on the fractional part of Q_m = (m-1)! sum_(n=2)^(m-1) 1/(n!-1). Evaluated in exact rational arithmetic for m = 3..210: 204 of 208 certificates FIRE, a rate of 0.9808, with exactly four failures at m = 5, 9, 23, 60 and none whatsoever beyond m = 60. If frac(Q_m) were uniform the expected failure count would be sum 1/m = 4.427, against 4 observed - a ratio of 0.904 - and failures would thin out like 1/m, which they do. So frac(Q_m) carries no arithmetic bias against the certificate. This separates two readings of the residual the packet could not distinguish: the certificate is not hard to satisfy and in need of a cleverer construction, it is satisfied almost always and in need of a non-concentration theorem. Since the producer requires only one m above each cutoff and 98% of m qualify, cofinality is supported by a very large margin in everything computed, and the missing analytic input is equidistribution - or merely non-concentration in the top 1/m of the unit interval - for frac(Q_m). Finite computation over m <= 210, bounded by exact rational arithmetic on denominators growing like the product of (n!-1); cofinality is not proved and #68 remains open.

Evidence/status: exact_finite_evaluation_separating_generic_from_delicate

- [erdos68_predecessor_gap_threshold.py](probes/erdos68_predecessor_gap_threshold.py)

### factorial_digit_level_sets_and_uniformity

Over 3<=m<=50000 the rounding digit D_m = m N_(m-1) - N_m of the strict-successor recurrence determines all three tracked families at once. D_m=-1 is exactly the failure set of the tail-free predecessor-gap threshold and exactly the zero set of the canonical factorial digit d_m(S); D_m=0 is exactly the unit-carry set and exactly the maximal set d_m(S)=m-1; D_m>=1 is everything else. The identities are A_m = m A_(m-1) - 1 - 1/(m!-1) - D_m, G_m = N_m/m! - S = sum_(j>m) D_j/j! so the endpoint flag f_m=[G_m>0] is one backward scan, d_m(S) = m f_(m-1) - f_m - D_m, and the threshold reduces to D_m + A_m >= 2/m. The GMP certificate stream at 708453 precision bits, cross-checked against exact Fraction arithmetic on m<=200 with 0 mismatches, gives 10 indices with D_m=-1 (5,9,23,60,470,3026,19222,27472,30324,35366), 9 with D_m=0 (52,591,1030,1407,1438,2164,4258,10991,21236, independently reproducing the landed strict-successor certificate), and 13 with D_m=m-2, against 9.897 expected for each. All 49996 reconstructed canonical digits lie in [0,m-1] with zero range violations. The threshold fires at every one of the nine unit carries, so the zero branch of factorialGapStepCarry_eq_one_iff_zero_or_maximal_branch is excluded there and d_m(S)=m-1 at all nine. This is exact finite computation over one range and settles no cofinal quantifier.

Evidence/status: exact_finite_structure_identification


### kempner_index_denominator_exclusion

rational_denominator_ge_of_nonunit_carry used its hypothesis q<=m-1 in exactly one line, to obtain q | (m-1)!. Generalising that hypothesis to the divisibility itself, with the size bound kept as a one-line corollary so no existing consumer changed, gives the Lean-checked rational_denominator_not_dvd_pred_factorial_of_nonunit_carry: a non-unit carry at m forces every displayed rational denominator to fail q | (m-1)!, equivalently its Smarandache function (also called the Kempner function) min{k : q | k!} is at least m. This is strictly stronger than m<=q, which leaves every (m-1)-smooth denominator of any magnitude open, including (m-1)! itself and the primorial below m. Lean-checked instantiation at the module's own index-60 exact prefix certificate: rational_denominator_not_dvd_fiftynine_factorial, no displayed denominator divides 59!, where the previous Lean-checked statement was 60<=q. Taking the landed GMP certificate's non-unit carry at m=300000 as finite input, the recorded exclusion q>=300000 strengthens to q not dividing 299999!, so a displayed denominator must carry a prime factor above 299999 or a prime power p^e with e exceeding the multiplicity of p in 299999!. The authority split is unchanged: a Lean-checked consumer with a finite GMP certificate as its input.

Evidence/status: lean_checked_consumer_with_finite_certificate_input


### certified_continued_fraction_denominator_exclusion

A certified continued-fraction prefix gives a denominator bound directly: if S is rational its expansion terminates and its reduced denominator is that of the last convergent, so a prefix of length n+1 forces q >= q_(n+1), with convergent denominators growing like e^(1.1866 n). Certified means each quotient is forced by a rigorous rational bracket lo <= 2^B S <= hi rather than read off a float: the interval expansion emits a quotient only when both endpoints agree, so there is no probably-correct tail. The prefix stays genuine even if S is rational, because at the step where the expansion would end the two endpoint floors differ (or the denominator hits zero) and the algorithm halts rather than emitting past it. The exclusion is best approximation of the second kind, |qS-p| >= |q_n S - p_n| for every 1 <= q < q_(n+1), and the probe verifies |q_n S - p_n| > 0 against the bracket instead of assuming it. The module self-checks against e = [2;1,2,1,1,4,1,1,6,...] and the convergents 3, 22/7, 333/106, 355/113 of pi before every run; that check caught a transposed p/q initialisation that would otherwise have produced a plausible-looking bound. Bracketing S = sum_(n>=2) 1/(n!-1) by lo = sum floor(2^B/(n!-1)) through the first index with n!-1 > 2^B, with each floor losing under 1 and the omitted tail under 2/((N+1)!-1) since (n+1)!-1 > (n+1)(n!-1), and taking B = 80000 bits, certifies 23449 partial quotients and gives q >= 2^39991 > 10^12039, with the separation |q_n S - p_n| > 0 verified. The packet's recorded exclusion was q >= 300000, so this is stronger by about 12034 orders of magnitude, and it costs 17 seconds. At B = 40000 the bound is 10^6019 in 2 seconds, so the published figure is not near a limit of the method. This does NOT subsume kempner_index_denominator_exclusion and is not ranked against it: q does not divide 299999! kills every 299999-smooth denominator of any magnitude, including numbers far above 10^12039, while saying nothing about size; the continued-fraction bound says nothing about smoothness. Together, a displayed denominator must exceed 10^12039 and also carry a prime factor above 299999 or a prime power beyond its multiplicity in 299999!. Structurally the certified quotients are generic: Levy's constant is matched to 0.38 percent, the Gauss-Kuzmin worst |z| over the first five values is 1.97, and the largest partial quotient is 35923, about 1.5n as Gauss-Kuzmin predicts for n terms, so there is no anomalous near-rational and no Liouville-flavoured candidate denominator.

Evidence/status: exact_finite_denominator_exclusion


### rank_two_producer_is_a_smoothness_exclusion_not_an_irrationality_route

erdos68_rank_two_strict_nonvanishing asks for det(A)*S nonintegral, with the landed identity R_D(c) = det(A)*S + K and the landed rounding bound |R| <= 1/2. Three facts the packet did not record. First, the output is a divisibility exclusion, not a size bound: if S = a/q in lowest terms then det(A)*S is integral exactly when q divides det(A), since gcd(a,q)=1, so det(A)*S nonintegral IS q not dividing det(A) - the same species as the Kempner-index statement q not dividing 299999!. Second, nonvanishing alone cannot yield irrationality: under S = a/q a nonzero R is a nonzero multiple of 1/q, hence |R| >= 1/q, and the only recorded smallness is |R| <= 1/2, which are compatible for every q >= 2. A linear-form argument needs 0 < |R| < 1/q, and the nearest-integer rounding is exactly what destroys that, consistent with scalar_canonical_product_height_no_go already recording that the natural scalar smallness diverges. Smallness is the missing half and nonvanishing is not a step toward it. Third, the certified continued-fraction bound q > 10^12039 gives unconditionally that N*S is nonintegral for every nonzero |N| <= 10^12039, so it discharges the producer's hypothesis outright on any grid instance with a determinant that small. Computing the augmented determinants literally from PrimeUnitTranslator.lean by fraction-free Bareiss, that covers grid size n <= 1 (2x2 and 3x3, determinants 10^6 to 10^1160 over t = 1,2,3,5) and stops at once: at n = 2 the 4x4 determinant is already 10^15208 at t = 1. At n = 0 the determinant has the closed form |det(A)| = 3(4t)!(4t+4)!/2^(2t+2), verified exactly against the Lean matrix at t = 1,2,3,5, so the producer's output there is q not dividing 3(4t)!(4t+4)!/2^(2t+2); since 299999! divides that number once 4t+4 >= 299999, and q not dividing B is stronger than q not dividing A when A divides B, proving nonvanishing at n = 0 for any t >= 74999 would strictly strengthen the landed Kempner exclusion. The producer is not broken, it is mis-filed: dead as an irrationality route, live as a smoothness-exclusion route with an explicit closed-form target.

Evidence/status: exact_finite_reclassification


### prime_grid_nonterminality_is_bounded_by_carry_certificate_depth

cofinal_prime_grid_nonterminality asks, for cofinally many primes p, that the least (p-1)!^(-1) grid point strictly above H_p differ from S. It is an instance of 'S is not this explicit rational': S = G_p forces S = k/(p-1)!, so the reduced denominator q divides (p-1)!. Both finite denominator exclusions landed today therefore discharge it over an explicit initial range. kempner_index_denominator_exclusion gives q not dividing 299999!, and for p-1 <= 299999 the factorial (p-1)! divides 299999!, so q | (p-1)! would give q | 299999!; hence G_p != S for every prime p <= 300000, the largest being 299993. certified_continued_fraction_denominator_exclusion gives q > 2^39991, and q | (p-1)! would force q <= (p-1)!, so it discharges the producer while (p-1)! <= 2^39991, that is for every prime p <= 3824, the largest being 3823, where (p-1)! has 12037 decimal digits. Kempner is the operative bound by two orders of magnitude. The consequence is structural rather than numeric: the Kempner exclusion follows from a single certified non-unit carry at index m, so the discharge extends to p <= m whenever the GMP carry certificate is run to depth m. This producer is not an independent open problem but a corollary of the carry certificate's depth - extending the certificate extends it mechanically - and what remains genuinely open is only the cofinal tail. It should be tracked against certificate depth rather than as a free-standing priority-1 producer.

Evidence/status: exact_finite_discharge_of_an_open_producer


### gap_scalar_normal_form_and_uniform_spectrum_to_300000

The three tracked digit families are exactly the level sets of one scalar t_m = m*factorialGapPredecessorGap m: Lean now proves the rearranged radix recurrence g_(m+1) = m*g_m - b_m - eps_m, the exact finite carry-stream expansion g_m = sum_(j=m)^J (b_j + eps_j)(m-1)!/j! + (m-1)!/J!*g_(J+1) with remainder in (0, (m-1)!/J!], the sharp three-window equivalence b_m = 1 iff 1+eps_m < t_m <= 2+eps_m, and the digit-stream certificate factorialGapStepCarry_ne_one_of_stream_domination: any finite block of certified digits whose weighted sum dominates (2+eps_m)/m yields a strict-successor divisibility miss at index m, one frontier miss of Erdos #68 per block. The expansion includes the (+1+eps) carry stream; the engine docstring previously omitted it, shifting reconstructed scalars by ~e/m and corrupting near-edge analysis (docstring fixed). The corrected reconstruction was run over the certified GMP stream to m=300000 with zero consistency violations: unit carries remain {52,591,1030,1407,1438,2164,4258,10991,21236} (last 21236), threshold failures D=-1 are {5,9,23,60,470,3026,19222,27472,30324,35366,65768} against ln-scale expectation ~11.5, and no index m>=61 approaches either decision edge closer than 1.65e-3 (at m=1724; null expectation of a closer event over the remaining range ~0.017). The digit-law collapse of the three producer families to one uniform-behaving scalar thereby extends from m<=50000 to the entire certified range m<=300000 at the scalar level.

Evidence/status: lean_checked_scalar_bridge_plus_certified_finite_census


### second_layer_finite_digit_and_floor_stability_boundary

Lean proves the exact finite decomposition factorialGapPrefix(m)=factorialExpPrefix(m)+factorialGapSecondLayerPrefix(m), the integral head recurrence E_m=m E_(m-1)+1, the floor identity removing E_m from the strict successor, and the finite second-layer digit law d_m(P2_m)=m-1-factorialGapStepCarry(m). The bridge to the infinite S2 is explicitly conditional on floor stability at m and m-1; a positive scaled tail below one does not by itself preserve a floor. Lean also proves that rational canonical factorial digits are eventually zero and therefore cannot be eventually maximal, correcting the stale desk-6 boundary. A repaired exact-Fraction probe through m=500 has zero finite-law failures, no negative carries, and certifies every infinite-floor comparison by checking the actual next-integer gap against the strict bound m!*tail2<1/m!; the smallest gap/bound ratio is 2 at m=2. This is a finite certificate and a corrected coordinate, not a cofinal floor-stability theorem or an irrationality proof.

Evidence/status: lean_checked_finite_identity_plus_exact_finite_no_crossing_census

- [SecondLayerDigit.lean](problem/SecondLayerDigit.lean)

### prime_pole_principal_residue_criterion

For prime q and a finite factorial-gap prefix through M, let e be the positive maximum of v_q(n!-1), and sum modulo q the inverses of the maximal-hit cofactors (n!-1)/q^e. Lean proves that the common-denominator numerator is congruent to the LCM cofactor times this principal residue, so the complete q^e survives reduced-prefix cancellation exactly when that residue is nonzero. At M=q-1 the Wilson endpoint does not guarantee survival: q=139 has maximal hits 69,122,137 with cofactors 6,49,73 and inverse sum zero, while q=2593 has hits 349,2243,2591 with cofactors 1508,1566,1678 and inverse sum zero. A local exact modular scan through q=3000 reproduces precisely these two cancellations and both complete payloads. The returned scan through 200000 is not locally regenerated. The result composes with the lower cylinder by placing its gap numerator in one prescribed residue class modulo p, but nonvanishing alone does not show that class misses the Archimedean interval. Focused Lean replay exited 0 on 2026-08-24.

Evidence/status: lean_checked_prime_pole_principal_residue_criterion

- [PrimePoleCriterion.lean](problem/PrimePoleCriterion.lean)

### quadratic_neighbour_affine_defect_rigidity

For a_n=n!-1, any integer sequence b_n with endpoint error e_n=a_n-b_n satisfies the exact affine-defect identity eta_n=b_(n+1)-(n+1)b_n-n=(n+1)e_n-e_(n+1). Lean checks both four-step forms: a positive one-sided error with eta_k<k, or a nonzero signed error with |eta_k|<k, for k=n,...,n+3 forces the corresponding error at n+4 beyond (n+4)^2+2. Consequently eventual strict sublinearity inside the quadratic window forces eventual equality with n!-1, while a cofinally nontrivial downward perturbation forces eta_n>=n cofinally. Lean also checks the exact finite factorial telescope for the affine defects. The returned infinite reciprocal weighted transform is not claimed as Lean-checked and, even if landed, its irrationality is equivalent to the original missing arithmetic input rather than a producer. The rigidity theorem sharply detects destruction of the endpoint recurrence but does not prove the weighted transform irrational. The private-prime thin-tail countermodel confirms that new support plus an arbitrarily small next tail is not by itself contradictory. Focused Lean replay exited 0 on 2026-08-24.

Evidence/status: lean_checked_two_sided_and_one_sided_affine_defect_rigidity

- [AffineDefectRigidity.lean](problem/AffineDefectRigidity.lean)

### threshold_failure_odd_prime_cutoff_finite_pattern

The tail-free threshold is D_m+A_m>=2/m: it fails outright for D_m=-1, holds outright for D_m>=1, and at D_m=0 requires the separate boundary condition A_m>=2/m. The source-bound exact GMP scalar-spectrum receipt lists all D_m=-1 events through m=300000 as {5,9,23,60,470,3026,19222,27472,30324,35366,65768}; a correctly indexed Fraction recurrence independently reproduces the prefix. Thus the only odd D_m=-1 events are 5,9,23. The certified D_m=0 indices are {52,591,1030,1407,1438,2164,4258,10991,21236}, and the digit-law receipt verifies A_m>=2/m at every one, including the odd indices 591,1407,10991. Hence the full threshold has no odd failure after 23 through the certified horizon. PrimeThresholdParity.lean kernel-checks the target composition: every sufficiently large odd threshold proves irrationality directly, and the purely discrete adjacent-carry conditions b_m>=1 and (b_m=1 -> b_(m+1)>=3) are sufficient. The D_m=-1 parity clause alone is insufficient without the unit-carry boundary clause. The finite pattern is not the cofinal two-carry theorem; an arithmetic mechanism or a counterexample beyond the current horizon is required.

Evidence/status: verified_exact_finite_pattern_with_lean_checked_two_carry_consumer


### carry_congruence_normal_form_unit_carry_is_one_floor_congruence

The strict successor splits exactly as N_m = E_m + floor(F_m) + 1 with E_m = sum_{n=2}^{m} m!/n! integer and F_m = sum_{n=2}^{m} (m!/n!)/(n!-1); every E_m summand except n=m is divisible by m so E_m = 1 mod m, giving the carry congruence normal form: unit carry at m iff floor(F_m) = -2 mod m. Moreover F_m = m!*C_m with C_m = sum_{n<=m} 1/(n!(n!-1)). Exact rational validation against the certified stream to m=600 covers 598 indices including both unit carries {52, 591}, with zero mismatches. Recorded pitfall: evaluating floor(m!*C_inf) with an early-truncated C_inf is invalid since missing terms contribute O(m!/n!(n!-1)). The complete CarryCongruenceNormalForm module now passes focused Lean validation.

Evidence/status: lean_checked_exact_floor_congruence_normal_form

- [CarryCongruenceNormalForm.lean](problem/CarryCongruenceNormalForm.lean)

### adjacent_unit_carry_window_prime_power_collision_law

Lean gives a pure finite integer criterion for consecutive unit carries at m and m+1: the cleared predecessor state lies in a positive interval of width exactly its common denominator. The positive offset has forced complementary residues modulo m!-1 and (m+1)!-1 and factors, under an adjacent unit pair, as the reduced predecessor numerator at m+2 times the two exact transition normalizers. Hence its q-adic valuation is the sum of the future numerator and both normalizer valuations. If q survives in the reduced denominator at m+2, reduced coprimality removes the future numerator contribution. More strongly, for every exponent e with q^e dividing (m+1)!-1, the complete q^e divides the two-normalizer product if and only if it divides the complementary old factor v_m*(m!-1). This identifies every available prime-power collision layer without assuming disjoint support. It does not prove that adjacent unit pairs are excluded cofinally: the surviving producer is now a bound showing that the complementary old factor cannot absorb all required layers along a cofinal family.

Evidence/status: lean_checked_exact_two_step_factorization_and_prime_power_collision_iff

- [AdjacentUnitCarryWindow.lean](problem/AdjacentUnitCarryWindow.lean)

### adjacent_unit_carry_two_step_factorization_no_go

Lean now checks the missing two-step denominator identity v_(m+2) G_(m+1) G_m = v_m (m!-1) ((m+1)!-1), independent of all carry values, and its exact integer-window form. Combined with the already checked adjacent-pair offset factorization, an assumed adjacent unit pair turns the window inequality into 0 < U_(m+2) <= v_(m+2), precisely the universal positivity and upper bound for the future reduced predecessor-gap numerator. Therefore cancellation-normalizer, surviving-denominator-prime, gcd-excess, and prime-power collision arguments applied only after assuming the pair cannot exclude it: their apparent obstruction is the reduced-fraction bound rewritten through a common positive factor. Exact arithmetic through m=500 independently found zero support-filtered prime-power escapes, as the identity predicts. A genuine producer must constrain the raw predecessor state before the adjacent-carry assumption, for example via Archimedean non-concentration or an independent prefix congruence.

Evidence/status: lean_checked_exact_telescoping_circularity

- [AdjacentUnitCarryWindow.lean](problem/AdjacentUnitCarryWindow.lean)

### companion_constant_telescope_and_lower_window_certificate

Lean checks two completions of the carry congruence normal form in CompanionConstantBridge: (1) the telescope identity sum' d_n + sum' 1/n! = S over n>=2 with d_n = 1/(n!(n!-1)), via the pointwise identity d_n + 1/n! = 1/(n!-1); naming the second series e-2 analytically this reads C_inf = S - e + 2. (2) If the finite weighted digit block through m+k plus its explicit remainder weight stays <= (1+eps_m)/m, then index m cannot be a unit carry. This is symmetric to the upper-jump certificate, so the two windows can certify either finite miss direction. Summability of d_n is proved by domination d_n <= (1/2)*a_n against the corpus lemma summable_one_div_factorial_sub_one. Focused direct Lean validation and explicit olean generation both exited 0 on 2026-08-24.

Evidence/status: lean_checked_telescope_and_lower_window_certificate

- [CompanionConstantBridge.lean](problem/CompanionConstantBridge.lean)

### companion_constant_full_floor_one_residue_normal_form

Let C=sum_{n>=2}1/(n!(n!-1))=S-e+2. Under a hypothetical rational value S=a/b, every sufficiently large m has m!(S+2) divisible by m, while m!e=E_m+r_m with E_m=sum_{n=0}^m m!/n!, E_m congruent to 1 modulo m, and 0<r_m<1. Hence floor(m!C) congruent to -2 modulo m eventually. Conversely, the congruence is exactly the canonical factorial-digit condition d_m(C)=m-2 for m>=3; if it holds eventually, the tail identity sum_{m>N}(m-2)/m!=1/N!-sum_{m>N}1/m! shows C+(e-2)=S is rational. Thus S is irrational exactly when floor(m!C) misses -2 modulo m cofinally. Lean checks the companion telescope, the corrected small-subtraction alternatives floor(J-delta) in {floor J,floor J-1}, their two-residue carry-miss consumer, the abstract rationality-side one-residue arithmetic core, and both pointwise directions between the -2 floor residue and the m-2 canonical digit. The complete infinite-tail equivalence is presently the analytic argument recorded in CarryCongruenceLab, not a claim that the cofinal miss producer has been proved. A dual-precision 6436/6536-digit run through m=2000 finds -2 exactly at {52,591,1030,1407,1438}, matching the independently certified unit-carry list; finite agreement is evidence only.

Evidence/status: lean_checked_arithmetic_and_digit_bridge_with_analytic_equivalence

- [ConstantOnlyMissCertificates.lean](problem/ConstantOnlyMissCertificates.lean)

### cofinal_prime_lower_endpoint_escape_irrationality_criterion

If cofinally many primes p satisfy factorialGapScaledTail p <= p * canonicalRemainder(factorialGapSeries, p - 1), then the factorial-gap series is irrational. This is a conditional consumer only: it does not prove the cofinal prime escape producer.

Evidence/status: lean_checked_conditional_irrationality_consumer

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

claim_boundary: The cofinal prime lower-endpoint escape premise remains an open producer; this theorem is not an unconditional irrationality proof and does not settle Erdos #68.

### cofinal_predecessor_gap_threshold_irrationality_criterion

If cofinally many integers m satisfy 1 + 1/(m! - 1) + 2/m <= m * factorialGapPredecessorGap m, then the factorial-gap series is irrational. The threshold is computed from a finite rational prefix and consumes the exact lower-branch gap criterion.

Evidence/status: lean_checked_conditional_finite_prefix_consumer

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

claim_boundary: The cofinal finite-prefix threshold producer remains open; this theorem is conditional and does not prove an unconditional irrationality result or settle Erdos #68.

### cofinal_large_prefix_private_modulus_two_step_crt_anchors

Under a cofinal supply of factorial gaps with a prime divisor larger than the next index, Lean proves that the full prefix-private modulus of selected prime powers divides the reduced predecessor denominators at two consecutive endpoints and that both endpoint numerator projections are nonzero modulo that modulus. This packages the one-prime two-step anchor into a composite-modulus CRT interface for the remaining Erdős #68 producer analysis.

Evidence/status: lean_checked_conditional_two_step_modulus_anchor_consumer

- [PrimeZeroBranch.lean](problem/PrimeZeroBranch.lean)

claim_boundary: The cofinal prime-divisor source hypothesis remains open; the theorem is a conditional denominator/numerator anchor and does not prove the Archimedean residue inequality, irrationality, or solve Erdős #68.

### rational_branch_multiplicative_fixed_modulus_rigidity

Write N m = strictFacTopRat (factorialGapPrefix m) m = floor(m! * P m) + 1. FactorialGapPlateauCore already proves the radix recurrence N m = m * N (m-1) + 1 - carry m together with carry m = 1 <-> m | N m. Lean now composes them: on the rational branch the carry is pinned to 1, the additive term vanishes identically, and the recurrence degenerates to the purely multiplicative N m = m * N (m-1). Hence past the branch threshold N j | N m for all j <= m, and j! * N m = m! * N j, so N m / m! is eventually constant. Consequently, if the series is not irrational then for EVERY fixed modulus d > 0 there is B with d | N m for all m > B; in particular N m is eventually even. The contrapositive is a producer family indexed by d: a cofinal failure of the single fixed congruence N m = 0 mod d proves irrationality, and at d = 2 it suffices that N m be odd infinitely often. The exact orbit probe measures the odd-N density at 0.5003 over 3 <= m <= 1499, so the d = 2 producer is not vacuous, and it re-derives the zero-defect indices 52, 591, 1030, 1407, 1438, which coincide exactly with the corpus unit carries.

Evidence/status: lean_checked_exact_rigidity_and_sufficient_producer_family_no_cofinal_claim

- [MultiplicativeSuccessorRigidity.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/MultiplicativeSuccessorRigidity.lean)
- Source/validation note: lake build; #print axioms reports [propext, Classical.choice, Quot.sound] for all seven declarations; no sorryAx.

claim_boundary: Every producer here is a SUFFICIENT condition, strictly stronger than the canonical open producer cofinal_exact_prefix_strict_successor_miss, which remains the exact equivalence and is NOT replaced. No cofinal statement is proved: nothing shows that N m is odd infinitely often, or that any fixed congruence fails cofinally. The content is a change of category, not a closure - the moving-modulus Archimedean shrinking-target test m | N m is replaced by a test against one modulus fixed in advance. The measured 0.5003 odd density is heuristic evidence about the producer and says nothing about the cofinal quantifier. Erdős 68 remains open.

## Known failed routes

Residue vectors, their recurrences, and window widths admit synthetic all-hit blocks and cannot by themselves prove irrationality.

Known pointwise prime congruences, prime-dilation congruences, parity, and the exact prime coefficient formula admit a synthetic rational countermodel.

Canonical digit normalization is an exact reformulation, not a stronger irrationality criterion by itself.

The source-verified Koepf--Schmersau floor criterion does not close Erdos 68 with the natural termwise lcm clearing scale: the last two factorial-gap denominators already make 1/(n p_n) smaller than the first omitted summand for n>=4. Any use of that criterion would need a separate theorem producing much smaller reduced-prefix denominators through cancellation.

Duverney's fast-series criteria do not apply: u_n=n!-1 has u_(n+1)/u_n^2 tending to zero rather than satisfying two-sided quadratic growth, and the positive-term Corollary 3.2 summands |u_(n+1)/u_n^2-1| tend to one rather than forming a convergent series.

Barreto--Kang--Kim--Kovac--Zhang's 2026 rapidly-converging-series theorems do not apply directly: their d=1 growth hypothesis requires a_n^(1/2^n) to be unbounded, while (n!-1)^(1/2^n) tends to one. Their Mahler/Proposition 12 proof isolates the exact surviving transfer target--prefix-clearing integers D_N with liminf D_N r_N=0--but the factorial-gap product clearing scale is too large, so a new low-height lcm or cancellation theorem is still required.

The checked carry-defect expansion is an exact bridge to ordinary factorial series, but Hancl--Tijdeman's source theorems do not themselves supply the missing cofinal producer. In the bridge, eventual unit carries are exactly an eventual zero coefficient tail, so applying a Cantor--Oppenheim-type criterion still requires proving b_m!=1 infinitely often.

The source-verified Erdős--Straus coboundary criterion is for cumulative-product denominators and does not apply directly to the separate denominators m!-1. Through the checked carry expansion its small-numerator hypothesis follows from the sharp carry bound. Lean now proves both the eventual canonical state interval -B<c_m<=0 and the finite-residue collapse from that interval to eventual zero defects. Thus this route closes back onto eventual unit carries and is not a separate source of cofinal non-unit carries.

Kovač--Tao's interval construction is a sharp growth-only obstruction for Erdos 68: there is already a rational reciprocal series after decreasing each denominator n!-1 by at most n^2+1. Consequently no argument stable under all one-sided quadratic perturbations can prove the unperturbed series irrational; a successful proof must use the exact factorial residue/endpoint structure.

Wilson quotients, harmonic sums, p-adic gamma identities, and factorial residues do not control the required Archimedean floor without an additional coupling theorem.

Fixed-denominator scalar canonical-product localizers and rank-saturated consecutive-jet Hermite-Pade systems pay the full factorial-gap denominator and cannot beat the natural tail.

The support-matroid layer cannot create an additional fractional cancellation coordinate: the checked congruence forces every normalized channel defect to be integral, and the now-formal full residual classification proves every channel-kernel residual modulo integers is only its factorial moment times the original scalar series.

Uniform tail-channel sign and direct total-positivity closure are false for the factorial-grid Cramer vector. Exact small cases and the general maximum-support floor pattern exhibit adjacent sign flips: nondividing channels introduce a sawtooth floor weight that destroys single-node Vandermonde evaluation. The surviving exact theorem is only eventual fixed nonzero sign beyond the largest support; strict residual nonvanishing still requires control of the signed finite floor-discontinuous block together with the factorial tail.

Factorial valuations and the full maximal-minor gcd cannot absorb the channel LCM tax: the checked LCM divisibility applies to the primitive kernel after every common cofactor divisor is removed. The exact finite LCM inequality, global Stirling reduction, floor-sqrt optimizing window, and explicit logarithmic radius constraint are Lean-checked. The square-subsequence specialization gives t^3<8(R+1) at D=2t^2; Lean rules out the eventual upper bound 8(R(t)+1)<=t^3 and proves the radius is not little-o of t^3 under the channel hypotheses.

The optimized one-kernel logarithmic constraint cannot yield a strict bound at its sharp constant: Lean proves it is already satisfied at 9(R+1)=16t^3, equivalently 4sqrt(2)/9 in D-coordinates. A surviving sharp result must be formulated as a subcritical/liminf statement or use a stronger finite factorial-segment inequality.

A zero canonical digit is not the same as a zero-cylinder hit: the reported exact data contain prime canonical zero digits at 5 and 23 while the zero-branch list is empty through 100000.

Primehood does not automatically imply the sufficient tail-free predecessor-gap threshold. Correctly indexed exact arithmetic gives prime failures at m=5 and m=23, falsifying the universal every-prime assertion. It does not rule out an eventual-prime theorem: the certified spectrum through 300000 has no later prime failure, and the sharper prime lower-cylinder escape condition also remains open.

The stronger proposed divisibility (m!-1) | den(V_m) fails at the reported strict events m=52 and m=591. Only the Archimedean first-crossing denominator lower bound survives.

Every fixed finite-prime or fixed-modulus tail argument has an exact topology obstruction: for a fixed Q and every n>=Q, n!-1 and its inverse are both -1 modulo Q, so the terms do not tend to zero Q-adically and Q consecutive tail residues cancel. A rational telescoping countermodel can have the same eventual residue at every prime power dividing Q while summing to a rational number. Any viable valuation route must therefore use growing primes or moduli together with an Archimedean coupling.

Luca--Shparlinski's source-verified prime and prime-power hit bounds control unweighted collision multiplicity and aggregate valuation load, but they do not determine weighted endpoint residues. They cannot alone produce the unequal CRT projections or cofinal non-unit carries required for Erdős 68.

Klurman--Munsch's short-interval value-set theorem and O(N^(3/4)) fixed-modulus hit bound are source-verified alternate incidence inputs, not a stronger collision-core estimate. The exponent is weaker than the existing O(N^(2/3)) Luca--Shparlinski prime-hit bound, and the 2017 journal version does not reproduce preprint Lemma 2.4.

The Lean-checked insertion recurrence makes exact collision-core scans incremental, but changing the cost of computing C_p does not bound C_p or its weighted endpoint projection. Larger finite audits remain finite evidence unless paired with a cofinal theorem.

A fixed pair of low-index private owners cannot underwrite the cofinal collision-cap reduction. Lean proves that once p exceeds a fixed factorial-gap denominator n!-1, that denominator divides the growing base (p-1)! and its private quotient becomes exactly one. Thus the small pairs observed through p=503 are finite-range only. The stronger factor-split reduction removes the need for two moving indices, but every selected nontrivial factor must still escape with p rather than remain fixed.

Garaev--García Theorem 1 (source-verified in annexes/garaev-garcia-2022-factorial-representations-mod-prime, final-journal PDF pp. 536 and 539--541) strengthens average-over-residue-class information: for J(lambda)=#{1<=n<=N:n! congruent to lambda mod p}, it bounds moments of J and gives J(lambda_k)<=3N^(2/3)k^(-1/3) for the kth-largest fiber. It does not improve the uniform fixed-fiber bound for lambda=1 without an independent rank bound, and it contains no prime-power valuation control. Therefore it does not strengthen the live collision-cap inequality, repeated-valuation producer, or claim ceiling; re-enter only if a future route aggregates many residue classes or controls the rank of the 1-fiber.

### digit_side_arithmetic_construction_route

There is no arithmetic bias in the Erdos 68 rounding digits from which a cofinal index family could be constructed. Over 49998 digits the normalized digit (D_m+1)/m is indistinguishable from Uniform[0,1): mean z=+0.02, variance 0.0829595 against 1/12, Kolmogorov-Smirnov sqrt(n)D=0.619 against 1.95 at the 0.1 percent level, lag-one correlation +0.00080 against an independence sd of 0.00447, and worst stratum |z|=1.00 across primality, parity and residues mod 5 and mod 6, versus a predeclared falsifier of |z|>4. Primality gives z=-0.55, which upgrades the correctly indexed m=5 counterexample from 'primality is not an automatic producer' to 'no tested arithmetic property of m biases the digit at all'. The Archimedean side of the prime-indexed producers therefore gains nothing from digit structure. What survives is a single non-concentration statement: for infinitely many m the scaled predecessor gap A_(m-1) = 1 - frac((m-1)! sum_(k<m) 1/(k!-1)) avoids the interval ((1+1/(m!-1))/m, (2+1/(m!-1))/m]. That is weaker than equidistribution and weaker than the tail-free threshold, which demands A_(m-1) >= (1+1/(m!-1)+2/m)/m and so overshoots the window it needs to miss.

Evidence/status: eliminated_by_exact_finite_measurement


### appended_channel_determinant_condition_is_unsatisfiable

erdos68_appended_channel_determinant_beats_determinantal_divisor asks for an index set whose appended-row determinant residual N satisfies 0 < |N| < Delta, with Delta the gcd of maximal minors, and primitive_cofactor_determinant_divisor_bottleneck records that no unbounded family satisfying it was obtained. No single instance satisfies it. Laplace expansion along the appended row writes N as an integer combination of the maximal minors of the unappended channel matrix; Delta divides all of them by definition, so Delta divides N, so N nonzero forces |N| >= Delta. The inequality is unsatisfiable over the integers and the recorded search failure is the expected outcome, not a hard open case. The conclusion is independent of the reading: with Delta the gcd over the unappended matrix, Delta divides N by the expansion; with Delta the gcd over the appended square matrix, the only maximal minor is N itself so Delta = |N| and |N| < Delta is false outright; and for channel matrices wider than k+1 columns with N a (k+1)-minor, the expansion still yields k-minors of the channel matrix, all divisible by Delta. Verified on 6000 nonzero appended determinants across channel shapes 2x3, 3x4, 3x5, 4x5, 4x6 and 5x6, taking every (k+1)-column selection rather than only the square case, with zero escaping Delta. Recorded alongside: N and Delta are defined only in packet prose, with no Lean declaration and no script in the repository defining either, which is how an unsatisfiable condition survived on the frontier - nothing could be checked against it.

Evidence/status: eliminated_by_elementary_integer_algebra


### active_band_equidistribution_statement_is_false

The requested full active-band equidistribution does not hold. The normalized active residues collapse weakly to a point mass at zero, with only sparse harmonic boundary layers. Any route requiring uniform mass across the band is false and must be replaced by a thin-target or exact residual-centre argument.

Evidence/status: eliminated_by_returned_asymptotic_and_finite_checks


### metric_borel_cantelli_does_not_decide_the_rational_seed

The metric Borel--Cantelli/no-repeat theorem is valid for almost every seed, but the rational seeds relevant to a hypothetical rational value coalesce onto the explicit exceptional orbit. The generic theorem therefore cannot be promoted to the required pointwise statement without a new arithmetic exclusion of that exceptional orbit.

Evidence/status: generic_theorem_complete_pointwise_application_blocked


### exact_E_layer_annihilation_pays_height_above_decay

Finite E-layer truncations are linearly independent, but exact column annihilation forces coefficient height large enough to dominate the available tail decay. The natural Hermite--Pade/E-function construction therefore cannot close irrationality at the recorded scale; only a genuinely different signed filter or a uniform packaged-layer measure could re-enter this lane.

Evidence/status: natural_E_function_route_eliminated_by_coefficient_height_tax


### eventually_maximal_canonical_rational_boundary_is_false

The old layered-digit lab treated rationality as an eventually maximal canonical factorial-digit tail. Under the floor convention used by the formal corpus, every rational number has an eventually zero canonical tail. The old m-2-c second-layer criterion came from a backwards finite carry with an imposed terminal condition and is not the canonical infinite rationality boundary. Lean replaces it with the exact finite law m-1-b_m plus an explicit infinite-floor stability hypothesis.

Evidence/status: eliminated_by_lean_checked_zero_tail_theorem

- [SecondLayerDigit.lean](problem/SecondLayerDigit.lean)

### odd_index_parity_cutoff_is_chance_consistent_and_expensive_to_extend

The eight D_m=-1 events after 23 through 300000 (60, 470, 3026, 19222, 27472, 30324, 35366, 65768) are all even. Under the already verified uniform-digit null the all-even probability is 1/256, and the pattern was noticed post hoc among several tested arithmetic properties, so its pre-registered significance is weaker. The companion carry law identifies D_m=-1 with d_m(C)=m-1 (or the near-integer wrap branch d_m(C)=0), and d_m(C)=floor(m*fract((m-1)!C)) is a sum of about m/2 reduced residues of descending-factorial products modulo the almost-coprime moduli n!-1, with no parity-sensitive mechanism. Extension is not cheap: the GMP interval certificate costs O(M^2 log M) bit operations because it carries bits(M!) precision at every step, so doubling the horizon costs about four times the landed 300000 run and is expected to add only about 0.7 new events. Classification: a finite pattern consistent with chance; not escalated to a producer and not a theorem. A single odd D_m=-1 beyond 300000 would falsify it outright.

Evidence/status: finite_pattern_classified_no_mechanism_no_theorem


### repeated_prime_power_record_route_is_wieferich_type_infinitude

The repeated-record producer requires infinitely many (q,n) with q^2 | n!-1 after an earlier q-hit. The heuristic count of q^2 | n!-1 events is sum_n sum_(q>n) q^-2 ~ sum_n 1/(n log n), diverging like log log N; the exact scan through q<=10^6 found six square hits and three strict records, matching that profile. This is the density profile of Wilson and Wieferich primes, whose infinitude is open, and no assimilated source (Luca--Shparlinski, Garaev--Luca--Shparlinski, Klurman--Munsch, Li Lai, Kellner, Costa--Gerbicz--Harvey) supplies even one q^2 hit infinitely often. The route is therefore a Wieferich-type infinitude statement strictly beyond the corpus's incidence inputs. This is a classification with a heuristic count, not a proof that the route is impossible.

Evidence/status: heuristic_classification_not_proof_backed_no_go


### wilson_endpoint_hit_does_not_imply_prime_pole_survival

The prime-pole criterion survives the reduction from the full denominator product to the running LCM exactly when the sum of inverse cofactors over the maximal p-adic hits in n! - 1 (n < p) is nonzero mod p. Wilson's theorem supplies the endpoint hit n = p - 2, which makes it tempting to treat pole survival as automatic at large primes. It is not. Exact computation finds complete cancellation at p = 139, where the maximal hits are n = 69, 122, 137 with cofactors 6, 49, 73 mod p, and at p = 2593, where they are n = 349, 2243, 2591 with cofactors 1508, 1566, 1678 mod p; in both cases the inverse cofactor sum is 0 mod p, so the top p-power dies under reduction. A viable prime route must therefore be an averaging or anti-concentration statement over primes that retains the full prefix, not a per-prime Wilson shortcut. This is a counterexample to the shortcut, not a proof that no prime route exists.

Evidence/status: exact_computation_backed_no_go_for_the_pole_survival_shortcut


## Open implications

### cofinal_repeated_birth_amplification_mass

Prove cofinally that the canonical amplification modulus A_n=prod_{q|B_n, ord_q(v_n)<ord_q(n!-1)} q^ord_q(n!-1) is nontrivial and quantitatively large, or instead bound the complementary non-amplifying repeated-prime mass. The LCM bridge reduces one clean source target to repeated prime-power records: a strict new q-adic record in n!-1 automatically satisfies the denominator-amplification inequality, and a first repeated square feeds an actual q^2 denominator and nonzero numerator projection. The terminal Wilson specialization is now sharply fenced. W_p congruent to 1 modulo p is equivalent to p^2|(p-2)!-1; the local scan finds terminal repeated records only at p=107 and p=4931 through 50000, while Costa--Gerbicz--Harvey's complete Table 1 plus independent residue recheck excludes W_p congruent to 1 modulo p for every 10^6<p<2*10^13. OEIS A079853 additionally reports no other term below 4*10^11, but that external bound was not locally reproduced. The broader exact scan of every prime q<=1,000,000 and every 2<=n<q discovers one genuinely nonterminal repeated square record, q=971 from 361!-1 to 609!-1, and no square event of any kind above q=4931 in that range. This proves that Wilson terminal sparsity does not exhaust the mechanism while also showing that arbitrary square lifts remain sparse among primes below one million. Exact successor arithmetic now adds an end-to-end finite bridge: at m=610, 971^2 divides the actual reduced denominator, its numerator projection is nonzero, and the cleared predecessor-gap threshold has positive margin. Lean now gives the exact first-order target: if q hits k!-1 and n!-1, then q^2|n!-1 is equivalent to cancellation modulo q between (k!-1)/q and the quotient of the intervening descending-factorial block minus one. Neither the verified Wilson papers nor the current factorial-congruence sources supplies a lower bound for this quotient-balance event or an infinitude theorem for arbitrary nonterminal square hits. Thus the surviving producer is a cofinal quantitative theorem coupling arbitrary-index quotient balances and repeated valuation records to the required numerator-to-denominator threshold, not a continued search confined to n=q-2. The q=971 bridge proves composability once, but nonvanishing alone still does not force the threshold in general.

Evidence/status: see the source; no formal status inferred


### cofinal_tailfree_predecessor_gap_threshold

Prove that for every cutoff B there is an integer m>B satisfying the pure integer inequality ((m+2)m!-2)v_m<=m^2(m!-1)u_m, where Q_m=(m-1)!*factorialGapPrefix(m-1), v_m=den(Q_m), and u_m=(floor(Q_m)+1)v_m-num(Q_m). Lean proves 1<=u_m<=v_m, gcd(u_m,v_m)=1, Delta_m=u_m/v_m, and exact equivalence between this integer inequality and 1+1/(m!-1)+2/m<=m*u_m/v_m. Cofinally many such certificates imply irrationality. This is a sufficient producer, not an equivalence, because 2/m is an elementary upper bound for the exact scaled tail R_m. Correctly indexed arithmetic shows prime failures at m=5 and m=23, so the universal all-primes shortcut is false. Through 300000 every D_m=-1 event after 23 is even, while every D_m=0 event clears its separate A_m>=2/m boundary. Thus the strictly weaker eventual-prime route remains open and would follow from the combined target-producing theorem D_m+A_m>=2/m for every odd m>=25. Proving only that D_m=-1 is impossible is not enough unless the D_m=0 boundary is also controlled.

Evidence/status: see the source; no formal status inferred


### cofinal_prime_lower_endpoint_cylinder_escape

Prove that for every cutoff B there is a prime p>B with R_p<=p*theta_(p-1), where theta_(p-1) is the canonical factorial remainder of S and R_p=p!*sum_{n>p}1/(n!-1). Equivalently, rule out the finite rational-prefix gap subwindow 1+1/(p!-1)<p*Delta_p<=1+1/(p!-1)+R_p. Lean proves this alone implies irrationality. The forbidden lower cylinder has length R_p/p=O(p^-2), so this target is strictly weaker than proving a prime miss of the whole unit-carry interval; an upper-cylinder hit already supplies the maximal canonical digit branch.

Evidence/status: see the source; no formal status inferred


### cofinal_exact_prefix_strict_successor_miss

Prove that cofinally many integers m fail m | strictFacTopRat(factorialGapPrefix(m),m); Lean proves this is exactly equivalent to Erdős #68. The new full-constant coordinate is an analytically equivalent version of the same producer: for C=sum_{n>=2}1/(n!(n!-1))=S-e+2, prove floor(m!C) not congruent to -2 modulo m cofinally. Lean checks the pointwise equivalence between that residue and the canonical digit d_m(C)=m-2, while the infinite-tail equivalence is recorded analytically. Prime-index misses and the fixed-k two-stage prime-power criterion remain sufficient special cases, but primes are no longer part of the exact frontier statement.

Evidence/status: see the source; no formal status inferred


### cofinal_prime_grid_nonterminality

For cofinally many primes p, prove that the least (p-1)!^(-1) grid point strictly above H_p is not equal to the target series S. Escape G_p>S is sufficient but stronger than necessary; a finite plateau G_p<S also excludes any fixed rational denominator once p is large.

Evidence/status: see the source; no formal status inferred


### first_crossing_gap_denominator_upper_bound

For cofinally many nonterminal prime plateaux, control cancellation in the first-crossing gap V_p strongly enough to contradict the lower bound den(V_p)>=tau_p!-1, or tau_p!(tau_p!-1) on a -1 exit.

Evidence/status: see the source; no formal status inferred


### actual_cross_index_archimedean_profinite_coupling

Find a global invariant of the true divisor-factorial coefficients that rules out eventual q_m = 1 and is absent from the synthetic congruence countermodels.

Evidence/status: see the source; no formal status inferred


### quadratic_perturbation_endpoint_rigidity

Exploit an arithmetic invariant of the exact endpoint denominators a_n=n!-1 that is destroyed by the Kovač--Tao rational selections b_n in [n!-n^2-2,n!-1]. The new quadratic-window theorem rules out growth-only or perturbation-stable arguments; the target invariant must couple the exact recurrence a_(n+1)=(n+1)a_n+n to either cofinal non-unit carries, a growing-modulus tail obstruction, or private-factor projection disagreement.

Evidence/status: see the source; no formal status inferred


### strict_subrank_vector_canonical_product

Construct or rule out an N-dependent, denominator-resonant, strict-subrank vector Hermite-Pade system that does not factor through scalar evaluation at z = 1 and does not reassemble the full factorial-gap lcm.

Evidence/status: see the source; no formal status inferred


### erdos68_appended_channel_determinant_beats_determinantal_divisor

Find arbitrarily far-out index sets whose channel matrix has corank one and nonzero appended factorial determinant, while the exact surviving-channel determinant residual is nonzero and has absolute value strictly below the gcd of maximal minors.

Evidence/status: see the source; no formal status inferred


### erdos68_cofinal_weighted_projection_disagreement

The most compressed producer is a fractional-part bound: for every cutoff B, choose a prime p>B with R_p>1 and prove (2p+1)C_p < 2p^2(2p-1)!*((floor(T_p/R_p)+1)-C_p*s_(2p-1)). Lean proves this is equivalent to the coefficient-free global inequality (2p+1)L_p<2p^2(2p-1)!((R_p-(T_p mod R_p)) mod R_p), localizes a non-unit carry inside [p,2p], and implies the target irrationality through the independently checked carry characterization. The local mechanism works at factor level: any two divisors a,b of R_p with disagreeing complementary projections close under the normalized collision cap (2p+1)Ctilde_p*max(a,b)<2p^2*p(p+1)...(2p-1), and coprime a,b give a branch-free factor-pair floor bounded by the global residue. A single source-selected prefix-private prime q instantiates this interface with (a,b)=(1,q), so neither two moving denominator indices nor two nontrivial selected primes are required. Lean computes that unit-pair floor exactly as min(rho_p,R_p/q) and proves its scale inequality equivalent to the conjunction of the global complementary-residue bound and the local collision-core bound (2p+1)C_p q<2p^2(2p-1)!. The through-503 exact scan verifies the stronger owner-disagreement branch on every tested prime but remains finite evidence. The source-verified Li Lai theorem plus the Lean-checked least-hit/successor bridge supplies cofinally many uniquely supported tailored blocks and hence cofinally many admissible unit-factor pairs. Separately, terminal-first-hit primes are globally unique, and the exact pair 37,41 in block p=20 closes the complementary-projection and factor-pair scale conditions outright; a cofinal family of analogous closing pairs would bypass collision renewal entirely. The checked squared-factorial ceiling still excludes the older one-owner comparison as an asymptotic closing mechanism; the unit-factor pair is a different branch-free consumer because one projection modulus is the full private modulus. Luca--Shparlinski supplies source-verified prime-power reuse bounds T_{-1}(y,x,p^a)<< (x-y)log x/(a log p)+1. No source or Lean theorem currently supplies either surviving cofinal estimate, a cofinal lower bound for the upper fractional complement, or the global complementary residue; the remaining coupling theorem must convert the available collision and incidence information into one of these certificates.

Evidence/status: see the source; no formal status inferred


### erdos68_scalar_factorial_tail_orbit_nonintegrality

Given a hypothetical reduced rational denominator b, produce D and a nonzero m divisible by lcm(b,L_D) such that m*T_D is nonintegral, equivalently choose k with 0<|m*T_D+k|<1. The returned residual classification identifies this as the exact remaining scalar producer after channel annihilation.

Evidence/status: see the source; no formal status inferred


### erdos68_one_kernel_radius_no_go

The present logarithmic constraint is Lean-checked to hold at exact sharp-radius equality 9(R+1)=16t^3, so it cannot force a strict 4sqrt(2)/9 bound in D-coordinates. The surviving one-kernel target is to prove every subcritical constant, equivalently the sharp liminf lower bound, or to strengthen the finite factorial-segment inequality enough to create strict sharp slack.

Evidence/status: see the source; no formal status inferred


### erdos68_rank_two_strict_nonvanishing

Using the Lean-checked uniform factorial-grid Cramer kernel and prime unit translator, prove that the nearest-integer-rounded residual is strictly nonzero. Uniform rank-two existence, remote support, determinant nonvanishing, reduction into [-1/2,1/2], and the exact identity R_D(c)=det(A)S+K are complete. Thus strict nonvanishing is now explicitly equivalent to proving det(A)S is nonintegral; direct uniform tail-sign/total-positivity closure is false because floor-discontinuous tail determinants change sign.

Evidence/status: see the source; no formal status inferred
