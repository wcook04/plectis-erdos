# erdos_249 mathematical frontier

Generated from the exported research packet. Read the strongest applicable
result before attempting a proof; superseded results remain history.

Prove that the binary totient series sum_{n>=1} phi(n)/2^n is irrational.

## Established results and their evidence

### totient_k_kernel_rank_k_to_e_plus_one

For every integer base k >= 2 and every e >= 1, the bounded-depth totient k-kernel has rational dimension k^e + 1, with the explicit canonical basis indexed by the zero channel together with residues r satisfying k does not divide r.

Evidence/status: authored_mathematics_exact_rank_with_conditional_lean_support

- [odd_slope_affine_totient_independence.md](docs/formal_math/odd_slope_affine_totient_independence.md)

### totient_k_kernel_canonical_basis_and_reduction_normal_form

The zero-residue sections reduce to the canonical F_(1,0) channel, and every composite-base residue with k dividing r admits the exact gcd-corrected reduction; these identities give unconditional canonical spanning and the relation normal form once the remaining independence statement is supplied.

Evidence/status: lean_checked_unconditional_reduction_and_spanning_not_full_basis

- [TotientKernelReduction.lean](formal_math/odd_slope_affine_totient/TotientKernelReduction.lean)

### totient_affine_independence_known_mechanism

The odd-slope affine totient family is linearly independent over Q by a sorry-free Lean formalisation of a corollary of Martin's 2006 domination theorem, using a finite determinant and CRT/Dirichlet separation mechanism.

Evidence/status: lean_checked_restricted_affine_independence_corollary

- [OddSlopeAffineTotient.lean](formal_math/odd_slope_affine_totient/OddSlopeAffineTotient.lean)
- [OddSlopeAffineTotient.lean](side_projects/odd_slope_affine_totient/OddSlopeAffineTotient.lean)

### strict_prime_orbit_escape_endpoint

A cofinal strict real-part gap below 9/10 on the natural prime tail orbit supplies an adaptive positive truncation budget, the existing point-escape certificate, and hence irrationality of the totient series.

Evidence/status: lean_checked

- [TotientStrictPrimeEscape.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/TotientStrictPrimeEscape.lean)
- [TotientStrictPrimeEscape.lean](problem/TotientStrictPrimeEscape.lean)

claim_boundary: The theorem is conditional on the cofinal strict real-part gap and the stated natural-prime-tail hypotheses. It does not prove that gap, identify the omitted original proof, or establish irrationality outside this conditional route.

### finite_euler_local_factors

The squared Mobius Euler factors at s=1 and s=2 and the exact second-difference conversion of the divisor-sum prime-power row to the totient row are formalized over Q and Z.

Evidence/status: lean_checked

- [FiniteEulerSieve.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/FiniteEulerSieve.lean)
- [FiniteEulerSieve.lean](problem/FiniteEulerSieve.lean)

claim_boundary: The two Euler-factor identities are exact rational identities for positive natural p, and the first- and second-difference identities are exact integer identities for the displayed finite sums. This row does not assert Euler-product convergence, an infinite sieve conclusion, or irrationality of the totient series.

### prime_ray_checkerboard_and_completion

The unique 2-by-2 joint annihilator, abstract four-scale divisor-layer identity, and affine residue-class recentering theorem are formalized independently of polynomial APIs.

Evidence/status: lean_checked

- [PrimeRayCyclotomicCurvature.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean)

claim_boundary: The Lean declarations formalize the Boolean checkerboard/separability uniqueness lemma, an exact four-factor divisor identity under supplied factorization hypotheses, and an affine congruence recentering lemma for M=2R with R>0. They do not prove the source-specific prime-ray divisibility hypotheses, the full totient irrationality theorem, or an analytic estimate.

### rational_geometric_model_falsifier

For every real 0 <= r < 1, the positive coprime-pair Lambert mass sum_{gcd(a,b)=1} r^(a+b)/(1-r^(a+b)) equals (r/(1-r))^2. The proof kernel-checks absolute summability, pair/layer sum interchange, and the exact geometric evaluation, showing that coprime restriction plus Stern-Brocot splitting and geometric decay alone cannot force irrationality.

Evidence/status: lean_checked

- [GeometricCoprimality.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/GeometricCoprimality.lean)

claim_boundary: The Lean theorem proves the exact positive geometric identity for the coprime-pair model. It does not formalize the full Erdos #249 totient series, any irrationality conclusion, or a claim that every Stern-Brocot decomposition has this geometric form.

### sharp_stern_brocot_cusp_frontier

A proposed Stern--Brocot root-frontier asymptotic alleges that a one-run cusp term plus two boundary two-run terms leave a nonnegative O(n^2 8^-n) remainder, with limits 2^n E_n -> 1 and 4^n(E_n-C_n) -> 7/3. The packet currently binds neither definitions of E_n and C_n, nor a proof, checker, or primary source, so this is unassessed rather than a completed proof pending Lean.

Evidence/status: unassessed_source_specific_asymptotic_missing_definitions_proof_and_anchor


### mobius_mersenne_hankel_ladder

The Mobius-Mersenne probabilities Theta_r are strictly log-concave for every r>=1. Lean proves r=1,2,3,4 through an exact five-atom enclosure and proves every r>=5 by a tail-contraction induction; hence every shifted 2x2 Hankel determinant is strictly negative. Higher fixed-order shifted determinants, infinite Hankel rank, and the superexponential common-denominator obstruction remain authored mathematics pending Lean.

Evidence/status: lean_checked_order_two

- [SignedQMomentObstruction.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/SignedQMomentObstruction.lean)

claim_boundary: The two named Lean declarations prove strict two-step log-concavity for every Mobius-Mersenne rung and negativity of the associated shifted 2x2 Hankel determinant. They do not prove higher fixed-order determinants, infinite Hankel rank, a common-denominator obstruction, or irrationality of the target series.

### mobius_mersenne_hankel_exact_verifier

A dependency-free exact rational verifier certifies the shifted 2x2 Hankel gaps r=1,2,3,4 from five atoms plus a rigorous geometric tail; it also certifies the r=5 perturbation margin 65005267/246872199168 and the exact tail-contraction identity B_r-4B_(r+1)=1/(2^r(2^r-1)(2^(r+1)-1)). These are the finite base and contraction data for a full Lean induction.

Evidence/status: exact_rational_checked


### mobius_mersenne_hankel_analytic_core

Every rung Theta_r with r>=1 is absolutely summable under the sharp termwise majorant (2^-r)^n. Lean identifies Theta_1=1/2 and Theta_2=S_phi-1/2, splits every rung into 1-3^-r plus its d>=3 tail, proves the exact tail enclosure |R_r| <= (2^-r)^2/(1-2^-r), and proves the dominant two-atom Hankel gap equals 4/3^(r+2).

Evidence/status: lean_checked

- [SignedQMomentObstruction.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/SignedQMomentObstruction.lean)

claim_boundary: The four named Lean declarations establish absolute summability, the exact two-atom-plus-tail decomposition and tail enclosure, and the dominant two-atom Hankel gap. They do not by themselves prove all-rung strict log-concavity, higher fixed-order determinants, infinite Hankel rank, a common-denominator obstruction, or irrationality of the target series.

### mobius_mersenne_eventual_strict_log_concavity

For every r>=5, Theta_r*Theta_(r+2) < Theta_(r+1)^2. Lean proves the exact tail-bound contraction B_(r+1)<B_r/4, the perturbation contraction E_(r+1)<E_r/4, the dominant-gap contraction M_(r+1)=M_r/3, the exact positive r=5 base margin, and the resulting negative shifted 2x2 Hankel determinants.

Evidence/status: lean_checked

- [SignedQMomentObstruction.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/SignedQMomentObstruction.lean)

claim_boundary: The named declarations establish eventual strict log-concavity of the Möbius–Mersenne rung sequence and the associated negative shifted Hankel determinants for r>=5. They do not prove linear independence of the full moment family, irrationality of the target series, or any conclusion beyond the displayed analytic and determinant inequalities.

### mobius_mersenne_all_rungs_strict_log_concavity

For every integer r>=1, Theta_r*Theta_(r+2) < Theta_(r+1)^2 and Theta_r*Theta_(r+2)-Theta_(r+1)^2<0. The remaining r=1,2,3,4 range is kernel-checked by splitting off d=1,...,5, bounding the residual tail by (2^-r)^5/(1-2^-r), and discharging the four exact rational inequalities.

Evidence/status: lean_checked

- [SignedQMomentObstruction.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/SignedQMomentObstruction.lean)

claim_boundary: The Lean declarations prove strict two-step log-concavity for every Mobius-Mersenne rung and negativity of the associated shifted 2x2 Hankel determinant. They do not prove higher fixed-order determinants, infinite Hankel rank, a common-denominator obstruction, or irrationality of the target series.

### finite_dyadic_hankel_valuation

Every finite truncated Mobius companion Hankel determinant has an exact 2-adic valuation determined by the largest squarefree support tuple.

Evidence/status: advisory_exact_finite_theorem_pending_lean


### finite_euler_sieve_tower

A proposed finite Euler-sieve approximation is alleged to have positive multiplicative coefficients, dense quadratic radial singularities, transcendental values at algebraic nomes through a fixed-level quasimodular special-value theorem, and local-uniform convergence to the #249 function. No exact sieve definition, proof-bearing local note, verifier, or theorem-level external source anchor is currently bound to this composite formulation, so none of those assertions is established by this packet.

Evidence/status: unassessed_source_specific_formulation_missing_exact_sieve_and_external_anchor


### totient_natural_boundary

The unit circle is a natural boundary for the ordinary Euler-totient generating function by the external Banks--Luca--Shparlinski irrationality result together with the Pólya--Carlson theorem. The source-specific claim of an explicit nonzero quadratic radial coefficient at every squarefree root of unity has no local proof or primary-source anchor here and remains unverified.

Evidence/status: external_natural_boundary_conclusion_supported_source_specific_mechanism_unverified


### metric_prime_escape

A dissociated Riesz product gives exponential measure decay for simultaneous lacunary phase locking, so the strict prime-escape producer holds for almost every real number.

Evidence/status: advisory_complete_proof_pending_lean


### locked_irrational_adversary

There is an explicit sparse irrational binary expansion whose prime-indexed phases remain above 9/10 eventually for every fixed shift; every finite binary prefix admits such a completion.

Evidence/status: advisory_explicit_counterexample


### prime_ray_cyclotomic_support

Under the published cyclic-resultant growth theorem, four-scale curvature isolates exponentially growing cyclotomic layers whose prime support escapes every finite set, with exact-order realisation in residue degree at most deg(f).

Evidence/status: authored_mathematics_external_growth_dependency


### bounded_degree_prime_ray_support_escape

Bounded-degree exact-order realisability gives the quantitative bound m*q < p^d for every prime p dividing the layer C(m*q), without a positivity assumption on m; equivalently, B^d <= m*q forces B < p. For a positive ray multiplier this forces the prime divisors on sufficiently remote prime-ray layers to avoid every prescribed finite set. If the layers are eventually nontrivial, their prime divisors are unbounded even after an arbitrary lower bound on the prime index. The finite-support proof gives the explicit cutoff 1 plus the sum of p^d over the forbidden primes.

Evidence/status: lean_checked

- [PrimeRayCyclotomicCurvature.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean)

claim_boundary: The Lean declarations prove the abstract bounded-degree order-consumer implication, finite-support escape, and unbounded-prime-divisor supply under explicit eventual nontriviality and order hypotheses. They do not prove the source-specific cyclic-resultant growth theorem, the full Erdos #249 irrationality theorem, or positivity of every target ray.

### x_minus_two_unbounded_prime_support

For the exact polynomial X-2, every prime divisor p of 2^q-1 at a prime index q has order exactly q modulo p and hence q divides p-1. The resulting degree-one order consumer and nontrivial layer supply instantiate the abstract theorem, proving unbounded prime divisors on cofinally remote prime indices without any external growth theorem.

Evidence/status: lean_checked

- [CyclotomicAnchoredKill.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean)

claim_boundary: The three declarations prove the exact order, nontrivial layer supply, and unbounded-prime-divisor conclusion for the Mersenne specialization at prime indices. They do not prove the general source-specific cyclic-resultant growth theorem, the full Erdos #249 irrationality theorem, or a phase-escape conclusion for arbitrary polynomial rays.

### cyclotomic_anchored_multiple_period_closure

An eventual integral h-tail difference telescopes to every multiple h*q. Therefore a cofinal supply of certified kills at prime-anchored starts p-1 and multiple periods h*q implies irrationality of the binary totient series.

Evidence/status: lean_checked_conditional_closure

- [PeriodMultipleEscape.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/PeriodMultipleEscape.lean)

claim_boundary: The three declarations prove the telescoping and the conditional equivalence or implication from an eventual integral tail plus certified period-multiple kills to irrationality. They do not prove the eventual integral-tail hypothesis, the cofinal certified-kill supply, the source-specific prime-ray growth theorem, or any unconditional Erdos #249 irrationality result.

### cyclotomic_331_denominator_exclusion

The exact certificates certifiedKill(30,300,13) and certifiedKill(30,330,10) are kernel-checked. The first excludes every rational whose denominator divides 2^300*(2^30-1); the second is the finite (h,q,p,N,L)=(6,5,331,330,10) model for the cofinal anchored residual.

Evidence/status: lean_checked

- [CyclotomicAnchoredKill.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean)

claim_boundary: The three named declarations formalize two exact finite certified-kill witnesses and the resulting denominator-divisibility exclusion for the binary totient series. They do not prove a cofinal supply of such certificates, the general cyclotomic growth or prime-production theorem, or unconditional irrationality of the full Erdos #249 series.

### canonical_full_mersenne_residue_normal_form

Erdos 249 is Lean-equivalent to FullMersenneCanonicalBasepointResidueGapSupply. For every prospective denominator 2^c v with v odd, it is enough and necessary to choose one positive H divisible by phi(v), put M=(2^H-1)/v, and force (-totientBlock(H,c)) mod M strictly between c+H+1 and M-(c+H+1). The free basepoint, prime-factor choice, analytic tail and carry trajectory have all been eliminated from this exact residual.

Evidence/status: lean_checked_equivalent_claim_ceiling

- [CyclotomicAnchoredKill.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean)
- [CyclotomicAnchoredKill.lean](problem/CyclotomicAnchoredKill.lean)

claim_boundary: The named definition and three theorems establish the exact equivalence between the canonical-basepoint residue-gap supply and irrationality, together with its implication into the centered supply. They do not prove that the supply holds, construct a cofinal residue gap, establish analytic tail estimates, or by themselves provide an unconditional Erdos #249 irrationality proof.

### totient_dyadic_odd_core_basis

For base 2, the two zero-residue totient sections together with one odd-residue section at each positive level form a Lean-checked basis of the rational span of the full dyadic totient kernel. The odd-core channel family is linearly independent, spans every dyadic section through exact zero/even reductions, and therefore gives the complete rational relation normal form for this base-2 kernel span.

Evidence/status: lean_checked_complete_base_two_kernel_basis_and_relation_normal_form

- [TotientMahlerDefect.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TotientMahlerDefect.lean)

### mersenne_divisor_centrality_one_way

For positive M|N, centrality of z mod M in the open radius-B arc implies centrality of z mod N: write z mod N=jM+(z mod M) with 0<=j<N/M. The converse fails on the actual totient block at (c,v,H)=(0,3,6): Q=82 and B=7, while (-Q) mod 63=44 is central but (-Q) mod 21=2 is endpoint-trapped. Therefore a pure-dyadic v=1 escape theorem cannot be quotient-projected to arbitrary odd denominators; v-specific arithmetic is genuinely necessary. Receipt: state/formal_math/erdos257_period_noncollapse/erdos249_mersenne_divisor_centrality_receipt.json.

Evidence/status: exact_arithmetic_theorem_and_actual_counterexample

- [check_mersenne_divisor_centrality.py](problem/scripts/check_mersenne_divisor_centrality.py)
- [erdos249_mersenne_divisor_centrality_receipt.json](receipts/erdos249_mersenne_divisor_centrality_receipt.json)

### canonical_residue_delay_four_and_five_no_go

The durable canonical-residue checker separates the first H where M>2(c+H+1) from actual residue entry. On 3,100 pairs with odd v<=200 and c<=30, (c,v)=(27,1) has post-clearance delay five, falsifying delay<=4. On the structurally targeted pure-dyadic axis v=1, c<=2000, 61 pairs have delay above five and the maximum is twelve at c=349: geometry clears at H=10, the residue remains endpoint-trapped through H=21, and it enters at H=22. Uniform post-clearance constants four and five are therefore false; merely enlarging the tested constant is not a proof route. Receipts: state/formal_math/erdos257_period_noncollapse/erdos249_canonical_mersenne_residue_receipt.json and erdos249_pure_dyadic_residue_delay_nogo_receipt.json.

Evidence/status: exact_finite_counterexamples_after_geometry_clearance


### hankel_single_value_schur_extraction

Bordering a finite signed Hankel block gives an exact rational linear form in Theta_2 and a signed Pade-kernel error identity. Every rank-saturated one-corner construction collapses to ordinary truncation, and the associated primitive prefix forms diverge rather than tend to zero.

Evidence/status: advisory_complete_proof_pending_lean


### finite_lambert_jet_rigidity

Any finite rational first-power Mobius-Lambert fold matching the required divisor sums is uniquely the ordinary totient truncation; finite scalar rationalisation cannot produce a new single-value obstruction.

Evidence/status: advisory_complete_proof_pending_lean


### uniform_rank_one_subrank_obstruction

For every e>=1 and cutoff Y>=4, the rank-one monomial quotient t_Y(e+2)^2/t_Y(2e+2) exceeds Theta_2 by more than 1/480. Every nonempty positive finite weighted average of these quotients has the same gap, and any integer form obtained from a rational representation p/q has absolute value greater than q/480. The Lean proof uses the uniform prefix error 1/3584 and a corrected five-atom enclosure for Theta_2; the inherited four-atom geometric-tail value 1/108 was false (the stated geometric majorant equals 1/48). A second Lean module sharpens the same family: the unique minimiser is (e,Y)=(1,5) with exact quotient 35076077250375200/37573118933633199, the uniform gap is more than 21/320, 1/16 is the optimal uniform unit fraction, and 1/15 fails at the minimiser.

Evidence/status: lean_and_dependency_free_exact_checked

- [RankOneSharpFloor.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/RankOneSharpFloor.lean)
- [RankOneSharpFloor.lean](problem/RankOneSharpFloor.lean)

### sharp_rank_one_schur_cone_floor

Among all admissible pairs e>=1, Y>=4, the rank-one monomial quotient is uniquely minimised at the five-atom first-depth kernel (e,Y)=(1,5). The gap to Theta_2 is more than 21/320 uniformly, so 1/16 is a valid uniform unit fraction while 1/15 is not. This prices the positive rank-one family exactly; it does not decide Erdős #249.

Evidence/status: lean_and_dependency_free_exact_checked

- [RankOneSharpFloor.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/RankOneSharpFloor.lean)
- [RankOneSharpFloor.lean](problem/RankOneSharpFloor.lean)

### finite_euler_sieve_sharp_tail

The finite Euler-sieve error has an exact positive smooth-rough factorisation, begins with coefficient 2 at the next omitted prime r_y, and at 1/2 is Theta(2^-r_y)=Q_y^(-log(2)/2+o(1)). Consequently a family-specific distance lower bound with exponent strictly below log(2)/2 would prove irrationality.

Evidence/status: advisory_complete_proof_pending_lean


### finite_euler_sieve_additive_anomaly_repair

Two positive integral additive repairs keep the same sharp convergence exponent while making the quasimodular anomaly uniformly nonzero: one raises level only by the next prime with O(r_y) added height, and one has exact anomaly 1/4 without increasing level. A generic fixed-anomaly, growing-level counterfamily shows that level, depth, anomaly, integrality, and finite-stage transcendence alone cannot yield the required lower bound.

Evidence/status: authored_mathematics_external_special_value_dependency


### pointwise_totient_boundary_mode_countermodel

Lean constructs an infinite constant-two word that is positive, even, inside every moving envelope based at c>=2, and pointwise totient-valued because phi(3)=2, while its fixed-quotient Mersenne endpoint error is identically zero at every depth. Therefore pointwise totient-image membership and elementary one-letter bounds cannot force endpoint escape; any successful anti-shadowing theorem must use relations tying the letters to their actual consecutive arguments.

Evidence/status: lean_checked_infinite_countermodel_with_exact_regression

- [PeriodMultipleEscape.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/PeriodMultipleEscape.lean)
- [PeriodMultipleEscape.lean](problem/PeriodMultipleEscape.lean)

### actual_totient_word_excludes_constant_two_boundary_mode

Lean proves that every shifted actual consecutive-totient word contains a letter different from 2. For any basepoint c, choose a prime p>=max(c+1,5) and place it at H=p-(c+1); then phi(c+H+1)=phi(p)=p-1>=4. Consequently the constant-two permanent boundary mode is impossible for the actual word at every shift. This kills the expanding homogeneous mode itself, not merely a finite prefix, while leaving inhomogeneous fixed-quotient boundary words open.

Evidence/status: lean_checked_all_shifts_homogeneous_mode_eliminated

- [PeriodMultipleEscape.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/PeriodMultipleEscape.lean)

### actual_totient_prime_positions_force_linear_endpoint_excursions

For every fixed basepoint c and quotient k, every prime argument p=c+H+1 forces c+H-k <= |E_(H+1)|+2|E_H|, and such prime positions occur beyond every requested height. Hence no bounded, periodic, or sublinear-error fixed-quotient boundary mode can occur for the actual consecutive-totient word. Any surviving permanent endpoint trap must use linear-size excursions inside the full moving envelope; this strictly strengthens the earlier exclusion of the homogeneous constant-two mode without proving endpoint escape.

Evidence/status: lean_checked_cofinal_quantitative_mechanism_elimination

- [PeriodMultipleEscape.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/PeriodMultipleEscape.lean)
- [PeriodMultipleEscape.lean](problem/PeriodMultipleEscape.lean)

### prime_successor_trap_forces_cofinal_preprime_bottom_lock

If p=c+H+1 is prime and the endpoint error remains below the upper moving boundary for the successor step, then 4E_H+p+phi(p+1) <= 4+3k. If the orbit remains upper-trapped at every height, such bottom-locked prime predecessors occur beyond every cutoff. Thus every permanent fixed-quotient trap is forced cofinally into a linearly negative pre-prime half-space; mechanisms without this directional bottom lock are eliminated, while endpoint escape itself remains open.

Evidence/status: lean_checked_cofinal_directional_mechanism_elimination

- [PeriodMultipleEscape.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/PeriodMultipleEscape.lean)
- [PeriodMultipleEscape.lean](problem/PeriodMultipleEscape.lean)

### single_prime_successor_lock_has_nonempty_exact_precursor_cone

At the exact c=490794 record word, the full integer preimage of the p=490829 prime-successor bottom-lock interval through all fourteen preceding actual totient letters contains exactly 35 geometry-boundary errors, 53685 through 53719. Every seed independently replays inside every endpoint window and reaches the bottom lock; the actual error 53713 is among them. Therefore a single bottom lock plus its exact intervening composite block does not force a backward lower-boundary crossing. Any surviving route must couple multiple locks or add a cross-gap arithmetic invariant.

Evidence/status: exact_finite_single_block_mechanism_elimination

- [check_prime_successor_precursor_cone.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_prime_successor_precursor_cone.py)

### two_prime_successor_locks_uniquely_determine_trapped_seed

At the exact c=349, k=167 record word, the complete geometry-boundary interval of 721 integer errors contracts to 362 seeds after the trapped successor of p=359 and to the unique seed E_10=-15 after the trapped successor of p=367. That seed is the actual record orbit and remains strictly endpoint-trapped through H=19, ending at E_19=-109 with minimum margin 238. Therefore two distinct prime-successor locks plus every exact intervening totient letter and endpoint bound can determine the orbit without forcing escape. Any surviving local route needs at least a third lock, or a genuinely global cross-gap invariant.

Evidence/status: verified_exact_two_lock_mechanism_elimination

- [check_two_prime_lock_precursor_cone.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_two_prime_lock_precursor_cone.py)

### three_prime_successor_locks_leave_nonempty_exact_precursor_cone

At the first exact three-lock word c=1858, k=1251, the complete geometry-boundary cone contracts 3743 -> 937 -> 234 -> 15 across the trapped successors of the distinct primes 1871, 1873, and 1877. The final complete interval is [-193,-179]; the actual seed E_12=-189 survives and reaches E_20=-741 with endpoint margin 1138. Thus three local prime-successor locks still do not force crossing, and lock count is not a monotone uniqueness mechanism. Any surviving local route needs an unbounded/cofinal lock family with genuinely global cross-gap coherence.

Evidence/status: verified_exact_three_lock_mechanism_elimination

- [check_three_prime_lock_precursor_cone.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/scripts/check_three_prime_lock_precursor_cone.py)
- [check_three_prime_lock_precursor_cone.py](problem/scripts/check_three_prime_lock_precursor_cone.py)

### actual_totient_word_excludes_eventually_affine_endpoint_modes

For every basepoint c and fixed quotient k, Lean proves that the pure-dyadic endpoint error cannot equal A*H+B at all sufficiently large heights. The endpoint recurrence would force the shifted totient letters to be affine. For arbitrarily late primes 2<p<q, the exact totient points (p,p-1), (q,q-1), and (2p,p-1) have affine determinant -p(q-p), which is nonzero. This deletes every eventually affine full-linear-envelope boundary mode, while genuinely non-affine linear-scale traps and Erdős #249 remain open.

Evidence/status: lean_checked_cofinal_exact_mechanism_elimination

- [TotientAffineModeEscape.lean](problem/TotientAffineModeEscape.lean)

### post_clear_delay_grows_like_log2_c

The pure-dyadic fixed-quotient trap has two parts. While (2^H-1)/2 <= c+H+1 the window is wider than the whole residue range and every H is trapped for free; that trivial prefix has length about log2(c). The informative quantity is the POST-CLEAR run: the longest run of consecutive H that have cleared that threshold, satisfy |E_H| <= c+H+1, and share one quotient k. Measured over c <= 1,400,000, the post-clear records are 15 at c=14177, 17 at c=50490, 18 at c=403191 and 19 at c=490794, with delay/log2(c) settling at 1.00-1.09. The last row is this packet's own recorded witness - same delay, same c - recovered from an independently written statistic, which pins the definition. The law is max{post-clear delay : c <= C} ~ log2 C. Consequently NO uniform delay cap can exist: cap 17 dies at c ~ 2^15.6, cap 19 at c ~ 2^18.9, and cap N at c ~ 2^N. The sequence of refuted caps recorded in this packet is that law playing out, not a sequence of near misses, and every future finite search will refute the next cap at exponentially greater cost for no new information. The redirected target is a growth law: after the window clears, the doubling recurrence E_(H+1) = 2E_H + phi(c+H+1) - k escapes a radius-c window within O(log c) steps, which is a statement about the number of consecutive near-cancellations between the doubling and the totient increment. Finite measurement over one range; it does not prove that no cap exists for all c, and the target irrationality of sum phi(n)/2^n remains open.

Evidence/status: exact_measurement_retiring_the_uniform_delay_cap_programme

- [erdos249_fixed_quotient_delay_law.py](formal_math/probes/erdos249_fixed_quotient_delay_law.py)
- [erdos249_fixed_quotient_delay_law.py](probes/erdos249_fixed_quotient_delay_law.py)

### supply_delay_two_parameter_law_and_diophantine_translation

The Lean-equivalent supply producer was measured only on the pure-dyadic axis v=1. Computing the FullMersenneCenteredResidueGap predicate literally over c<=60000 and odd v in {1,3,5,7,9,11,15,31} gives the two-parameter law max_(c<=C) delay(c,v) = ceil(log2(C)/phi(v)), exact in seven of eight moduli and one higher at v=1, with observed maxima 17,8,4,3,3,2,2,1. The packet's log2(C) law is the phi(v)=1 case. The Euler-multiple constraint phi(v)|H is a help rather than a restriction: between consecutive admissible heights the modulus multiplies by 2^phi(v) while the band radius grows only by phi(v), so the per-step failure probability is about 2^-phi(v) and the whole difficulty concentrates on small phi(v); at phi(v)>=12 the first geometrically possible height already works throughout the range. In height units the requirement stays uniformly small, the tallest height needed across 480000 instances being 60. From R_c = 2R_(c-1) - phi(c) with R_0 = S, the tail satisfies R_c = 2^c S - integer, so ||v R_c|| = ||v 2^c S||, and the Lean block identity 2^H R_c = totientBlock(H,c) + R_(c+H) (verified here exactly, difference 0 at (H,N)=(5,0),(11,37),(17,900)) makes failure at height H the condition ||v 2^c S|| <~ v c 2^-H. Hence H_min(c,v) = phi(v)*ceil(L/phi(v)) + O(phi(v)) with L = log2(v c / ||v 2^c S||), verified against the exact predicate to within one admissible step in every tested case. This is a finite coordinate translation and delay measurement, not evidence that the problem's frontier should be strengthened to an irrationality measure. Any quantitative distance estimate is a sufficient stronger route; a positive lower bound uniform over all odd v at fixed c is impossible for irrational S.

Evidence/status: exact_finite_measurement_with_lean_checked_pointwise_consumer

- [CyclotomicAnchoredKill.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/CyclotomicAnchoredKill.lean)

claim_boundary: Lean checks the per-instance implication from an exact factorization and centered residue gap to exclusion of every reduced denominator dividing 2^c v. The computation supplies finitely many candidate instances, not a universally quantified or cofinal gap supply, so Erdos #249 remains open.

### dyadic_family_denominator_exclusion_with_margin

Computing ||v 2^c S|| directly by the recurrence A_(c+1) = 2A_c + phi(c+J+1) mod 2^J at J=220, whose truncation error (c+J+2)2^-J is below 2^-202, gives min_(c<=200000) ||v 2^c S|| with -log2 of the minimum equal to 18.03, 18.17, 18.54, 18.54, 17.39, 19.11, 16.96, 17.78 for v = 1,3,5,7,9,11,15,31. Hence S is not a/(v 2^c) for any integer a, any c<=200000 and any of those odd v, with explicit margin at least 2^-19.11 and a truncation error 180 binary orders below it. This exclusion is direct and does not go through the supply producer. Against log2(C)=17.61 the products C*min lie in [0.354,1.569] for every modulus, so min_(c<=C) ||v 2^c S|| is of order 1/C with no dependence on v: the generic law. The phi(v) dependence of the delay law is an artifact of the admissible step size, not of the arithmetic. Consequently no uniform delay cap can hold - a cap of N steps asserts ||v 2^c S|| >= 2^(-N phi(v)-1) and is refuted at c about 2^(N phi(v)) on every axis, not only at v=1 - and no lower bound stronger than ||v 2^c S|| >> 1/c is available. The usable analytic target is ||v 2^c S|| >= c^-A for a fixed A>1 uniformly in odd v, which gives H <= (A+1)log2 c + log2 v + O(phi(v)) and settles the supply.

Evidence/status: exact_finite_denominator_exclusion


### certified_continued_fraction_denominator_exclusion

A certified continued-fraction prefix gives a denominator bound directly: if S is rational its expansion terminates and its reduced denominator is that of the last convergent, so a prefix of length n+1 forces q >= q_(n+1), with convergent denominators growing like e^(1.1866 n). Certified means each quotient is forced by a rigorous rational bracket lo <= 2^B S <= hi rather than read off a float: the interval expansion emits a quotient only when both endpoints agree, so there is no probably-correct tail. The prefix stays genuine even if S is rational, because at the step where the expansion would end the two endpoint floors differ (or the denominator hits zero) and the algorithm halts rather than emitting past it. The exclusion is best approximation of the second kind, |qS-p| >= |q_n S - p_n| for every 1 <= q < q_(n+1), and the probe verifies |q_n S - p_n| > 0 against the bracket instead of assuming it. The module self-checks against e = [2;1,2,1,1,4,1,1,6,...] and the convergents 3, 22/7, 333/106, 355/113 of pi before every run; that check caught a transposed p/q initialisation that would otherwise have produced a plausible-looking bound. Bracketing S = sum_(n>=1) phi(n)/2^n by the exact prefix lo = sum_(n<=B) phi(n) 2^(B-n) with omitted tail under sum_(n>B) n 2^-n = (B+2)2^-B, and taking B = 80000 bits, certifies 23438 partial quotients and gives q >= 2^39990 > 10^12039, with the separation |q_n S - p_n| > 0 verified. The packet held no continued-fraction content at all, and its finite exclusions were tied to specific cyclotomic certificates. At B = 40000 the bound is 10^6018 in half a second. This is complementary to dyadic_family_denominator_exclusion_with_margin rather than stronger: that result excludes the family v*2^c for c up to 200000 with an explicit margin, which reaches denominators of about 2^200000 inside a restricted family, while this excludes every denominator below 10^12039 without restriction. Structurally the certified quotients are generic: Levy's constant is matched to 0.33 percent, the Gauss-Kuzmin worst |z| over the first five values is 1.99, and the largest partial quotient is 29403, so the series approximates like a generic irrational and offers no anomalous convergent to test against the Mersenne machinery.

Evidence/status: exact_finite_denominator_exclusion


### positive_weighted_rank_one_floor_source_join

For every nonempty finite positive weighted family of rank-one Schur quotients in the admissible range, Lean proves that the weighted average still exceeds the target Theta_2 by more than 21/320. The sharp single-quotient floor therefore survives positive finite mixing, so any remaining #249 route must use off-diagonal coupling or signed cancellation rather than a positive rank-one average.

Evidence/status: lean_checked_source_current_consumer

- [RankOneSharpFloor.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/RankOneSharpFloor.lean)

claim_boundary: This is a sharp positive-family obstruction, not an irrationality proof for Erdős #249; the surviving off-diagonal or signed-cancellation producer remains open.

### actual_lcm_orbit_separation_quantitative_bridge

For each cutoff a₀, the explicit PowerTwoActualLcmOrbitSeparationSupply asks for an exponent a and odd canonical rank 2q+1 with a≥max(2,a₀), such that every integer z stays at least 1/32 plus the explicit raw-approximation error radius away from the actual LCM tail orbit R_(2H)-R_H, where H=lcm(1,...,2^a). The source proves the exact scaled-series identity, the raw-block identity, its elementary error bound, the half-word conversion, and the implication from this supply to the existing signed-margin producer and hence irrationality. The supply itself remains an open hypothesis.

Evidence/status: lean_checked_source_current_conditional_quantitative_bridge

- [TotientActualLcmOrbitSeparation.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/TotientActualLcmOrbitSeparation.lean)
- [TotientActualLcmOrbitSeparation.lean](shared_lean/TotientActualLcmOrbitSeparation.lean)

claim_boundary: Lean checks the approximation identities and the implication from the explicit cofinal separation supply to irrationality. It does not prove the separation supply, construct a cofinal odd-rank witness, prove unconditional irrationality, or replace the exact actual-LCM nonintegrality frontier.

### parity_perturbed_rational_control

There is a coefficient sequence c with c(n) <= n, c(n) = phi(n) at every odd n, -2 <= c(n) - phi(n) <= 1 at every n, and sum_(n>=1) c(n)/2^n = 5/4. Construction: xi = 5/4 - S lies in [-2/3, 1/3) because 9/8 <= S <= 3/2; its centred base-four digits d_m = floor(4 x_(m-1) + 2/3), x_m = 4 x_(m-1) - d_m, take values in {-2,-1,0,1} and sum to xi; c(2m) = phi(2m) + d_m. Variants with the same proof: digit set {-1,0,1,2} and value 3/2; the perturbation placed on odd arguments only with value 1; a perturbation supported on the density-zero set {n >= 4 : 2^floor(log2 log2 n) | n} (unbounded, greedy) with value 3/2. The probe certifies the first 1200 digits from an exact rational enclosure of S and checks the exact prefix of the control series against 5/4 to below 2^-2389. On 64 evaluation points the control's dyadic sections through level e have full rank 2^(e+1)-1 for e <= 4, above the totient's 2^e+1.

Evidence/status: lean_checked_and_probe_certified

- [ParityPerturbedRationalControl.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/ParityPerturbedRationalControl.lean)
- [ParityPerturbedRationalControl.lean](problem/ParityPerturbedRationalControl.lean)

claim_boundary: This is a rational control, not a statement about S. It shows that the odd values of phi together with the even values to within an additive 2 do not determine irrationality; equivalently the residue of phi(2m) modulo 4 can always be re-chosen to make the series rational. It does not bound ||v 2^c S||, does not touch the canonical residue-gap frontier, and says nothing about the Lambert or Pade routes.

### odd_agreeing_carry_rank_transfer

For any coefficient sequence c agreeing with phi at every odd argument and any tempered integral carry u of c with multiplier v >= 1, the carry sections u(2^j n + r), 1 <= j <= e, 0 <= r < 2^j, span a rational space of dimension at least 2^e - 1. The proof is the existing totient anti-compression proof with its only totient input, the odd canonical channels, retained. Applied to the parity-perturbed control this gives a tempered integral carry with dyadic section rank >= 2^e - 1 at every level and rational series 5/4: the conclusion of not_irrational_totientSeries_implies_unbounded_carryRank_unconditional is compatible with rationality.

Evidence/status: lean_checked

- [ParityPerturbedRationalControl.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/ParityPerturbedRationalControl.lean)
- [ParityPerturbedRationalControl.lean](problem/ParityPerturbedRationalControl.lean)

claim_boundary: Closes route (c), the carry-rank gap contradiction, in its stated generality: any argument in the carry coordinate must use phi at even arguments to within less than an additive 2. Answers the control request attached to the paper's open problem prob:carryrank; a positive answer for phi itself remains equivalent to Erdos #249.

### all_base_totient_kernel_rank_unconditional

For every integer k>=2 and e>=1 the bounded-depth k-kernel span of Euler's totient has dimension exactly k^e+1, UNCONDITIONALLY, with the canonical index {(0,0),(1,0)} union {(j,r): 1<=j<=e, 1<=r<k^j, k does not divide r} and a Basis on that index. The residue condition is k not dividing r, NOT gcd(k,r)=1: at a composite base a canonical residue may share a proper prime factor with k. Independence rests on an all-slope auxiliary-prime row: for pairwise non-proportional positive affine forms a_i n + b_i there is an odd prime ell and rows n_i making the totient evaluation matrix diagonal and nonsingular mod ell, with NO odd-slope and no primitivity hypothesis. The relation module has dimension sum_(1<=j<e) k^j. The same row gives linear independence of the affine family for n^q phi(n)^m, q>=0, m>=1.

Evidence/status: lean_checked

- [AllBaseTotientKernel.lean](formal_math/erdos257_period_noncollapse/Erdos257PeriodNoncollapse/AllBaseTotientKernel.lean)
- [AllBaseTotientKernel.lean](shared_lean/AllBaseTotientKernel.lean)

claim_boundary: PRIOR ART, and this is the load-bearing part: Greg Martin, 'Simultaneous inequalities among values of the Euler phi-function', arXiv:math/0603053, Theorem 1 already gives positive lower density of prescribed simultaneous dominance for arbitrary positive slopes, which SUBSUMES the linear-independence conclusion. The contribution here is a Lean formalisation by an independent finite-determinant proof, and removal of the odd-slope restriction that the 2-adic parity argument in TotientMahlerDefect.lean requires. It is NOT an original theorem. The rank formula, explicit basis and relation normal form have no located source and their novelty is UNASSESSED. This closes the gap named in docs/formal_math/odd_slope_affine_totient_independence.md, which recorded the unconditional all-base independence theorem, Basis and relation normal form as not in Lean. NOT landed: the syzygies are proved to LIE in the kernel and the kernel dimension is proved, but they are not proved to SPAN it; and the k^e+1 rank for n^q phi^m has only its independence half. Nothing here bears on Erdos #249, which asks for irrationality of sum phi(n)/2^n and remains untouched and open.

### mobius_mersenne_ladder_separation_and_no_finite_recurrence

The LITERAL Lambert rung sum_d mu(d)/(2^(rd)-1) equals 2^(-r) for every r>=1, one substitution q=(1/2)^r into the landed tsum_moebius_lambert. It is therefore log-AFFINE, its shifted Hankel determinants vanish at every order N>=2 (proved by exhibiting a kernel vector, since Matrix.det_eq_zero_of_row_eq_smul_row does not exist), and it is separated from the corpus's POWER rung mu(d)/(2^d-1)^r, which the landed mobiusMersenneTheta_strict_logConcave shows is strictly log-concave. Separately and substantively: the power ladder satisfies NO finite constant-coefficient linear recurrence, by atomic peeling against a summable majorant, in an eventual form taking an arbitrary starting index.

Evidence/status: lean_checked

- [MobiusMersenneLadderSeparation.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/MobiusMersenneLadderSeparation.lean)
- [MobiusMersenneLadderSeparation.lean](problem/MobiusMersenneLadderSeparation.lean)

claim_boundary: The separation is a NAMING fix, not a mathematical correction: the corpus's Lean has always been the power rung and mobiusMersenneTheta_strict_logConcave has always been about it; only a Type B statement digest printed the other sequence. The two ladders AGREE at r=1, both 1/2, so any separation argument starts at r=2. The no-recurrence theorem does NOT state infinite Hankel rank: deriving that needs Kronecker's theorem, which is not in the corpus, so the module says it in prose only. Also not landed: eventual nonvanishing of fixed-order shifted determinants, and the return's all-shift order-3-to-6 certificates. Nothing here bears on the irrationality target.

### effective_signed_atomic_hankel_asymptotics

For ordered nodes 1>=x_1>x_2>...>0, nonzero real a_j and A=sum |a_j|x_j<infinity, let X=product_(j<=N)x_j, Delta=product_(i<j<=N)(x_j-x_i), rho=x_(N+1)/x_N. The shifted moment determinant D_N(s) has leading term L(s)=(product_(j<=N)a_j) X^s Delta^2 and |D_N(s)/L(s)-1| <= A^N rho^(s-1)/(N! |product_(j<=N)a_j| X Delta^2), for s>=1. This proves effective eventual nonvanishing, eventual sign and infinite Hankel rank for the power Mobius-Mersenne ladder.

Evidence/status: ordinary_proof_verified_not_lean_formalized

- [SignedAtomicHankelAsymptotics.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/SignedAtomicHankelAsymptotics.md)
- [SignedAtomicHankelAsymptotics.md](problem/SignedAtomicHankelAsymptotics.md)

claim_boundary: Not nonvanishing at every shift and not irrationality of P_2. Literal Lambert rank one and all-base totient rank were already Lean-checked.

## Known failed routes

No positive bound depending only on c can hold for ||v*2^c*S|| uniformly over all positive odd v when S is irrational: odd multiples of the irrational number 2^c*S are dense modulo one. The former uniform-in-v c^-A proposal is impossible and is not a frontier producer.

Stern-Brocot telescoping plus geometric decay does not imply irrationality: the generic rational-x model has the same geometry and rational algebraic values.

A unit-circle natural boundary with integer coefficients does not imply irrationality at 1/2: (1-2z)S(z) has the same boundary and value zero at 1/2.

Generic lacunarity or irrationality does not imply the pointwise prime escape required at the named totient constant.

Finite transcendental Euler-sieve stages may converge to a rational number; the quasimodular depth coefficient vanishes while the level diverges.

Finite fixed-precision valuation/unit words admit arbitrary centred completions; the prime-ray producer needs finite-degree exact-order realisability plus the moving-characteristic Frobenius freeze.

Hankel nonvanishing controls the full derivative ladder but does not isolate Theta_2 with sufficiently compressed denominators.

Canonical rank-saturated one-corner Hankel extraction collapses exactly to truncation, and its primitive integer forms diverge; only a strictly sub-rank or genuinely vector-valued denominator-compressing kernel remains viable.

Every rank-one monomial strict-subrank quotient t_Y(e+2)^2/t_Y(2e+2), and every positive finite direct sum of them, stays more than 21/320 above Theta_2 for e>=1 and Y>=4, uniquely minimised at (e,Y)=(1,5). The coarser 1/480 certificate remains as a uniqueness-free uniform argument. Any surviving Schur route must therefore use genuine off-diagonal coupling or signed cancellation rather than positive rank-one averaging.

No Diophantine lower bound depending only on weight, level, depth, integral Fourier coefficients, nonzero anomaly, or finite-stage transcendence can close the finite Euler-sieve limit.

Unbounded exact-order prime support does not imply phase escape: rational specialisations can lock all compatible phases, and the named 331 layer itself supplies a period-kill certificate while its rigorously bounded depth-16 phase remains above 9/10.

Uniform canonical-residue escape within four, five, twelve, or seventeen heights after the central interval becomes nonempty is false. The exact pure-dyadic champion c=490794 remains endpoint-trapped for nineteen post-clearance heights. During that trap the nearest Mersenne quotient is fixed at k=327611 and the signed error follows E_(H+1)=2E_H+phi(c+H+1)-k, so the next producer is totient-word anti-shadowing in a moving interval rather than another guessed constant.

Pointwise totient-image membership, positivity, evenness, and the moving upper envelope do not imply endpoint escape. The Lean-checked constant-two word satisfies all of them and cancels the expanding fixed-quotient boundary mode forever. Consecutive-argument arithmetic is indispensable.

One prime-successor bottom lock does not force a backward lower-boundary crossing even when propagated through every exact intervening totient letter. The c=490794 record has a complete 35-seed admissible precursor cone, so a successful argument must couple multiple locks or introduce a genuinely cross-gap invariant.

Two distinct prime-successor locks do not force endpoint escape even when every exact intervening totient letter and moving endpoint bound is imposed. At c=349 the complete 721-seed interval contracts to the unique actual seed E_10=-15 by the second successor, yet that seed remains strictly trapped. Precursor uniqueness is therefore insufficient.

Three distinct prime-successor locks do not force endpoint escape or precursor uniqueness. At c=1858 the complete cone remains the 15-seed interval [-193,-179] through the third trapped successor, containing the actual seed -189. No proof based on any fixed finite local lock count is opened by the first three cases; the remaining producer must use unbounded/cofinal cross-gap coherence.

Pure-dyadic centrality modulo 2^H-1 does not descend to centrality modulo (2^H-1)/v. The actual (c,v,H)=(0,3,6) block is central modulo 63 and endpoint-trapped modulo 21. Only the reverse implication is valid, so the full odd-denominator producer cannot discard v-specific arithmetic.

No uniform cap on the pure-dyadic fixed-quotient delay can exist. The maximum post-clear delay over c <= C grows like log2 C - records 15, 17, 18, 19 at c = 14177, 50490, 403191, 490794 with ratio to log2(c) settling at 1 - so each cap is refuted at c about 2^cap. Further cap searches are guaranteed to refute the next cap and to produce nothing else.

The carry anti-compression conclusion is compatible with rationality. The parity-perturbed control c (c = phi on odd arguments, |c - phi| <= 2, c(n) <= n) has binary series 5/4 and a tempered integral carry whose dyadic section rank is at least 2^e - 1 at every level, exactly the conclusion that rationality of S forces for phi. No contradiction can be extracted from the rank gap 2^e - 1 versus 2^e + 1 without the even-argument values of phi modulo 4; route (c) is closed as stated and the paper's prob:carryrank control request is met.

Shifted-correlation asymptotics cannot carry the arithmetic content of the first-harmonic pivot. The parity-perturbed control satisfies the Balasubramanian-Giri-Srivastav Theorem 2.2 asymptotic for phi(n)/n with the same main term and the same O(log^2 x) error class (the perturbation moves the normalised correlation by at most 4 log x + 8 uniformly in |h| <= x/2, and the unnormalised one by at most 2x^2 + 6x against a main term of order x^3), and its series is 5/4. Any #249 argument whose only input about phi is a correlation asymptotic of this class, or any fixed finite family of k-point correlations with error >> x^k, applies verbatim to the control; the pivot must read phi(N+m) modulo 2^m directly.

Density-one agreement does not determine irrationality for supports of logarithmic gap: a coefficient sequence equal to phi off the density-zero set {1,2,3} U {n >= 4 : 2^floor(log2 log2 n) | n}, with c(n) <= n, has binary series 3/2 (greedy construction with the invariant L_n <= R_n <= U_n; capacity U_n - L_n >= 2^-n at every free n follows from gaps at most log2 n).

## Open implications

### totient_specific_moving_dyadic_escape

Prove FullMersenneCanonicalBasepointResidueGapSupply, the Lean-equivalent arithmetic normal form: for every c and positive odd v, find H>0 divisible by phi(v) such that the canonical residue (-totientBlock(H,c)) mod ((2^H-1)/v) lies in the central interval of radius c+H+1. On the pure-dyadic axis, the Lean-checked signed error E_H=totientBlock(H,c)-k(2^H-1) obeys E_(H+1)=2E_H+phi(c+H+1)-k while the nearest quotient k stays fixed. Exact computation through c<=1000000 finds delay nineteen at c=490794, ruling out caps through seventeen. Pointwise legal-letter methods, the constant-two mode, sublinear errors, and every eventually affine linear-scale error are eliminated. Actual prime positions cofinally force linear excursions; more directionally, if the successor remains upper-trapped then 4E_H+p+phi(p+1)<=4+3k, so any permanent trap is cofinally bottom-locked immediately before large primes. Complete exact cones now eliminate one-, two-, and three-local-lock forced crossing; at c=1858 three locks still leave 15 seeds. The sharp surviving local target must consume an unbounded/cofinal lock family through a genuinely global cross-gap invariant that excludes non-affine trapped precursors.

Evidence/status: see the source; no formal status inferred


### theta_two_denominator_compression

Construct a genuinely coupled off-diagonal or signed-cancellation vector Schur kernel whose reduced rational denominator q_(n,Y) satisfies 0 < q_(n,Y)*|Theta_2-R_(n,Y)| -> 0. Rank-saturated one-corner extraction and all positive rank-one monomial strict-subrank quotients, including their positive finite direct sums, are now excluded at the sharp floor 21/320 (unique minimiser (1,5)).

Evidence/status: see the source; no formal status inferred


### uniform_growing_level_specialisation

For the additively repaired finite Euler-sieve family, prove a family-specific distance lower bound with exponent kappa < log(2)/2 in the genuine level, exploiting cumulative Euler-product Fourier geometry rather than generic modular-form parameters.

Evidence/status: see the source; no formal status inferred


### cusp_frontier_formalisation

Kernel-check the explicit root-frontier remainder bound and its asymptotic corollaries as a sharp consumer of the run-geometry library.

Evidence/status: see the source; no formal status inferred


### general_prime_ray_polynomial_realisability

For polynomials beyond the now-closed X-2 case, formalize the cyclotomic resultant factorization, characteristic-p exact-order theorem, and Frobenius freeze before consuming the external Archimedean growth input.

Evidence/status: see the source; no formal status inferred


### fixed_order_power_ladder_eventual_hankel_nonvanishing

Formalize effective_signed_atomic_hankel_asymptotics from SignedAtomicHankelAsymptotics.md, including its effective exponential error bound. The ordinary theorem is closed; the parent gap remains denominator compression isolating P_2.

Evidence/status: ordinary_proof_closed_lean_formalization_open
