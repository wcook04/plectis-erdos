# erdos_1041 mathematical frontier

Generated from the exported research packet. Read the strongest applicable
result before attempting a proof; superseded results remain history.

If a monic polynomial f(z)=product_i(z-z_i) has all roots in the open unit disk, prove that two roots can be joined by a curve of length less than 2 contained in the open lemniscate |f|<1.

## Established results and their evidence

### free_point_torus_psh_reduction_2026_08_30

For every n>=2, the free-point inequality FP_(n-1) implies Conjecture (S)_n: if f is monic of degree n, its roots have minimum-enclosing-disk radius R, and c_1,...,c_(n-1) are its critical points with multiplicity, then sum_j |f(c_j)|^(1/n) <= (n-1)R. The symmetric critical-value functional Phi(a)=sum_(f_a'(c)=0)|f_a(c)|^(1/n) is continuous plurisubharmonic on the root polydisk: it is a sum of powers of holomorphic critical-value branches off the analytic collision locus and extends across that locus by local boundedness and psh removability. Iterated maximum principle moves the roots to the distinguished torus. There the exact identity |f(c_j)|=product_k|1-conj(c_j)c_k| converts FP_(n-1) into sum y_j<=n-1, and y^((n-1)/n)<=((n-1)y+1)/n gives the required exponent. Scaling restores R. Therefore the landed FP3 and FP4 theorems prove (S) in degrees four and five, and together with the earlier cases (S) is proved for n=2,3,4,5.

Evidence/status: ordinary_exact_all_degree_fp_to_separatrix_aggregate_bridge_with_green_deterministic_checker;_lean_scalar_kernel_elaboration_capacity_deferred

- [FreePointTorusPshReduction.md](problem/FreePointTorusPshReduction.md)
- [FreePointTorusPshReduction.lean](problem/FreePointTorusPshReduction.lean)
- [check_erdos1041_free_point_torus_psh_reduction.py](problem/scripts/check_erdos1041_free_point_torus_psh_reduction.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.FreePointTorusPshReduction.rpow_le_tangent_at_one, ErdosProblems.Erdos1041.FreePointTorusPshReduction.sum_rpow_le_card_of_sum_le_card, ErdosProblems.Erdos1041.FreePointTorusPshReduction.fp_exponent_mem_unit_interval, ErdosProblems.Erdos1041.FreePointTorusPshReduction.fp_exponent_bridge.

claim_boundary: The bridge is an ordinary exact analytic theorem. The Lean companion checks only its scalar exponent-conversion fan-in and remains pending focused elaboration; it does not formalize psh removability or the torus polynomial identity. The equality converse is not claimed. FP_m remains open for m>=5, Conjecture (S) does not imply the parent, and unrestricted Erdos 1041 remains open. No novelty or literature-priority claim is made.

### fp4_complete_2026_08_30

For arbitrary c_1,...,c_4 in the closed unit disk, put d_ij=|1-conj(c_i)c_j|, T_j=(product_k d_jk)^(1/4), and S_4=sum_j T_j. Then S_4<=4, with equality only when every c_j=0. The proof splits at max_j|c_j|^2=21/25. In the central region, the logarithmic energy/variance theorem combines with the exact row envelope (1-(21/25)t^2)(1+(21/25)t)^3<=12/5, certified by forty-eight positive Bernstein coefficients, and rational exponential bounds to give S_4<=4. In the outer region, K4 Hoelder gives S_4^4<=8W; the identity sum_(i<j)d_ij^2=6+sum u_j-|sum c_j|^2+sum_(i<j)u_i u_j, Cauchy over the three perfect matchings, and the bound on the three smaller pair products reduce W<32 to one variable. Its unique stationary point s=(-27+3sqrt(473))/50 has exact positive squared slack, completing the strict outer estimate.

Evidence/status: ordinary_exact_complete_fp4_theorem_with_deterministic_checker;_lean_scalar_kernel_elaboration_capacity_deferred

Superseded by **weighted_quadratic_free_point_all_degrees**. Use that stronger result.

- [FreePointZeroInsertionFP4Matching.md](problem/FreePointZeroInsertionFP4Matching.md)
- [FreePointFP4Complete.lean](problem/FreePointFP4Complete.lean)
- [check_erdos1041_free_point_zero_insertion_fp4.py](problem/scripts/check_erdos1041_free_point_zero_insertion_fp4.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.FreePointFP4Complete.three_mul_pairProduct_le_sum_sq, ErdosProblems.Erdos1041.FreePointFP4Complete.outer_radius_derivative_numerator_pos, ErdosProblems.Erdos1041.FreePointFP4Complete.outer_stationary_equation, ErdosProblems.Erdos1041.FreePointFP4Complete.outer_stationary_mem_interval, ErdosProblems.Erdos1041.FreePointFP4Complete.outer_stationary_radical_numerator_pos, ErdosProblems.Erdos1041.FreePointFP4Complete.outer_stationary_squared_slack_pos.

### fp_all_degrees_central_radius_2026_08_30

For every m put h_j=log T_j, q_r=sum_k c_k^r, E=(1/m)sum_(r>=1)|q_r|^2/r, L_j=-log(1-|c_j|^2), M_j=(1/m)sum_k -log(1-|c_j||c_k|), and C(t)=(exp(t)-1-t)/t^2 with C(0)=1/2. The logarithmic expansion gives sum h_j=-E, Cauchy gives h_j^2<=(E/m)L_j, and the triangle inequality gives |h_j|<=M_j. The sharp rowwise quadratic remainder exp(h_j)<=1+h_j+C(M_j)h_j^2 therefore proves FP_m whenever (1/m)sum_j C(M_j)L_j<=1, with equality only when every c_j=0. This strictly strengthens C(Lmax)Lbar<=1. Uniformly it holds for max_j|c_j|<=rho_*=sqrt(1-exp(-L_*))=0.8457729381..., where L_*>0 solves exp(L_*)=1+2L_* (equivalently L_*=-W_{-1}(-1/(2sqrt(e)))-1/2).

Evidence/status: ordinary_exact_all_degree_rowwise_adaptive_free_point_theorem_with_deterministic_checker

Superseded by **weighted_quadratic_free_point_all_degrees**. Use that stronger result.

- [FreePointZeroInsertionFP4Matching.md](problem/FreePointZeroInsertionFP4Matching.md)
- [check_erdos1041_free_point_zero_insertion_fp4.py](problem/scripts/check_erdos1041_free_point_zero_insertion_fp4.py)

### fp4_matching_stratum_2026_08_30

Let x_i=1-|c_i|^2, d_ij=|1-conj(c_i)c_j|, and T_i=(x_i product_(k ne i)d_ik)^(1/4) for four closed-unit-disk points. If the superunit graph {ij:d_ij>1} is a matching, then sum_i T_i<=4, with equality only when all c_i=0. After relabelling all cross edges between {1,2} and {3,4} are at most one. Each pair is bounded by d_ij^(1/4)(x_i^(1/4)+x_j^(1/4))<=2: its fourth power is at most 8(2-r^2-s^2)(1+rs)<=16 because 2-(2-r^2-s^2)(1+rs)=(r-s)^2+rs(r^2+s^2). A rational specimen has exactly the two superunit edges 12 and 34, so the stratum is genuinely larger than the all-small locus.

Evidence/status: ordinary_exact_fp4_subcase_with_symbolic_and_rational_checker

- [FreePointZeroInsertionFP4Matching.md](problem/FreePointZeroInsertionFP4Matching.md)
- [check_erdos1041_free_point_zero_insertion_fp4.py](problem/scripts/check_erdos1041_free_point_zero_insertion_fp4.py)

### first_critical_pair_energy_cone_no_go_2026_08_27

The returned first-critical pair-energy cone inequality is false already for the exact monic cubic p(c+w)=v+a w^2+w^3 with c=-1/2-i/100, a=-1/16-5i/6, and v=-1/32+i/160. Three disjoint rational Rouche disks certify that every root lies strictly in the unit disk, and exact critical-value comparison makes c the unique minimum-modulus critical point. For the two inverse branches p(z_+(s))=p(z_-(s))=v(1-s^2), the pair energy satisfies E-|c|^2=A s^2+O(s^4) with 0<A<K=|v/a|, so E'^2-4(E-|c|^2)(|M'|^2+|D'|^2)=4A(A-K)s^2+O(s^4)<0 for all sufficiently small positive s. The branch coordinate remains valid; only the proposed pointwise cone producer is retired.

Evidence/status: exact_gaussian_rational_cubic_counterexample_with_rouche_root_certificate

- [FirstCriticalPairEnergyNoGo20260827.md](problem/FirstCriticalPairEnergyNoGo20260827.md)
- [check_erdos1041_first_critical_pair_energy_no_go.py](problem/scripts/check_erdos1041_first_critical_pair_energy_no_go.py)

### orlicz_antichain_gram_pareto_selector_2026_08_26

For a k-root component, let U be the exact union of roots contaminated by an ancestral increment at least alpha or a Gram-row defect at least eta, and b=|U|. If b<=k-2, two roots outside U satisfy A_i,A_j<=S/(k-b-1) and the sharp same-pair complement-energy product inequality P^2(k-2)^(k-2)<=(q_iq_j)^2 Q_comp(i,j)^(k-2). If b<=k-3, two roots outside U satisfy A_i,A_j<=S/(k-b-2), q_i,q_j>=h_opt(B,P,k), and F_i,F_j>=h_opt^2, where h_opt is the largest threshold determined by B and P for which at most one charge is smaller. Replacing b by separate Orlicz and Gram Markov counts recovers return 003 as a coarse corollary. The returned four-leaf no-go is exact only for the abstract invariant ledger, and the Gram-good branch cannot replace the exceptional-root branch.

Evidence/status: ordinary_exact_overlap_sensitive_two_tier_strengthening_with_55053_row_rational_replay;_lean_elaboration_pending_low_disk_firewall

- [OrliczAntichainGramParetoSelector20260826.md](problem/OrliczAntichainGramParetoSelector20260826.md)
- [check_erdos1041_orlicz_antichain_gram_pareto_selector.py](problem/scripts/check_erdos1041_orlicz_antichain_gram_pareto_selector.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.OrliczAntichainGramParetoSelector20260826.two_survive_exact_union_count, ErdosProblems.Erdos1041.OrliczAntichainGramParetoSelector20260826.three_survive_exact_union_count, ErdosProblems.Erdos1041.OrliczAntichainGramParetoSelector20260826.pairTier_ageDenominator_strictly_better, ErdosProblems.Erdos1041.OrliczAntichainGramParetoSelector20260826.exactUnionCount_le_separateCounts, ErdosProblems.Erdos1041.OrliczAntichainGramParetoSelector20260826.sharpPair_product_transport, ErdosProblems.Erdos1041.OrliczAntichainGramParetoSelector20260826.individualHeavy_to_propagatedEnergy.

### cassini_nine_tenths_quantitative_tree_budget_slack

At the rational witness a=9/10, the Cassini elementary majorant misses the two-root distance by more than 4/25: 4(sqrt((9/10)^2+9/10)-9/10)+4/25 < 2(9/10). This is a quantitative instance of the tree-budget failure and makes the margin explicit for readers and downstream consumers.

Evidence/status: lean_checked_quantitative_refutation_consumer

- [CassiniTreeBudget.lean](problem/CassiniTreeBudget.lean)

claim_boundary: This is a single-witness quantitative refutation of the uniform tree-budget assertion. It does not prove the unrestricted Erdos 1041 claim, establish the replacement hub inequality, or transfer the slack to arbitrary root configurations without the separate geometric hypotheses.

### cassini_family_tree_budget_slack

For every real a>4/5, the Cassini elementary coarea majorant 4(sqrt(a^2+a)-a) is strictly below the two-root distance 2a. This is the family-wide inequality behind the quantitative a=9/10 witness and makes the tree-budget failure robust across the entire interval rather than a single numerical example.

Evidence/status: lean_checked_family_refutation_consumer

- [CassiniTreeBudget.lean](problem/CassiniTreeBudget.lean)

claim_boundary: This is a family-wide refutation of the displayed Cassini tree-budget bound. It does not prove the unrestricted Erdos 1041 theorem, supply the replacement hub inequality, or transfer the slack to arbitrary root configurations without the separate geometric hypotheses.

### five_centroid_distances_pair_selection

For five nonnegative distances with square-sum below 5, at least one of the ten pair sums is strictly below 2. This is the exact scalar pair-selection step behind the five-point centroid hub budget and exposes the finite combinatorial alternative without weakening the strict inequality.

Evidence/status: lean_checked_centroid_selector

- [CentroidHubBudget.lean](problem/CentroidHubBudget.lean)

claim_boundary: The lemma is only a scalar five-distance selector. It does not supply the geometric hypotheses that produce the five distances, prove the unrestricted Erdos 1041 hub inequality, or close the remaining attachment/critical-level allocation problem.

### sparse_defect_survivor_selector_2026_08_26

For F_(n,r)(z)=z^n-r^(n-1)z, one Gram-exceptional central root carries fraction (n-1)/n of the ER4 mass while every attachment age is zero; deleting it leaves only 1/n, even under any fixed determinant floor below e^(-1). This retires deletion-only Gram allocation but not Erdos 1041, because the exceptional root is a radial connector hub. For any survivor set S and the same two least-age survivors i,j, AM-GM strengthens the returned whole-component selector to P_S^2(s-2)^(s-2)<=(q_iq_j)^2 Q_comp(i,j)^(s-2)<=(q_iq_j)^2 Q_S^(s-2), with no deleted charge and equality on the star survivors. A separate returned componentwise trace no-go is not admitted because its supplied bundle omits the claimed trace certificate and names a checker for a different mechanism.

Evidence/status: ordinary_exact_actual_polynomial_no_go_and_strengthened_survivor_local_selector_with_exact_checker;_lean_elaboration_pending_low_disk_firewall

- [SparseDefectSurvivorSelector20260826.md](problem/SparseDefectSurvivorSelector20260826.md)
- [check_erdos1041_sparse_defect_survivor_selector.py](problem/scripts/check_erdos1041_sparse_defect_survivor_selector.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SparseDefectSurvivorSelector20260826.survivorProductSq_le_pairSq_mul_energyPow, ErdosProblems.Erdos1041.SparseDefectSurvivorSelector20260826.threeSurvivor_productSq_le, ErdosProblems.Erdos1041.SparseDefectSurvivorSelector20260826.er4_pair_transport, ErdosProblems.Erdos1041.SparseDefectSurvivorSelector20260826.starCentral_mass_fraction, ErdosProblems.Erdos1041.SparseDefectSurvivorSelector20260826.starSurvivor_mass_fraction, ErdosProblems.Erdos1041.SparseDefectSurvivorSelector20260826.starTwoSurvivor_mass_fraction_cross.

### six_return_joint_full_energy_charged_lifetime_and_sharp_gram

Six Type-B returns are reconciled against the current 1041 corpus. If no normalized closed root path has length at most two, the returned lifetime inequality strengthens to sum_v I_{k_v}(r_v)+(1/2)sum_v J_v+(1/4)sum_i sigma_i^2/|f'(a_i)|^2<n/4. Here J_v is the positive excess obtained by retaining the maximum of merge-propagated leaf energy and Bergman demand throughout node v's lifetime, and sigma_i is the truncated first attachment level of a singleton root component. Separately, a discriminant floor D>=delta gives the sharper normalized Vandermonde Gram estimate ||H-I||_F^2<=2 M_delta log(1/delta), where M_delta exp(1-M_delta)=delta; this removes one unnecessary power of M_delta from the return. The retained translated-cut, angular full-fibre action, pole budget, lifetime, antichain, comb, cubic no-go, and unicritical theorems leave one common pair/component allocation residual. Unrestricted Erdos 1041 remains open.

Evidence/status: ordinary_exact_joint_assimilation_with_two_strict_strengthenings_lean_checked_scalar_fanin_and_exact_replay

- [SixReturnJointAssimilation20260826.md](problem/SixReturnJointAssimilation20260826.md)
- [check_erdos1041_six_return_joint_assimilation.py](problem/scripts/check_erdos1041_six_return_joint_assimilation.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SixReturnJointAssimilation20260826.leafChargedLifetimeBudget, ErdosProblems.Erdos1041.SixReturnJointAssimilation20260826.fullEnergyChargedLifetimeBudget, ErdosProblems.Erdos1041.SixReturnJointAssimilation20260826.leafChargedLifetime_strictImprovement, ErdosProblems.Erdos1041.SixReturnJointAssimilation20260826.spectralDeviation_sum_le, ErdosProblems.Erdos1041.SixReturnJointAssimilation20260826.criticalPoleTrace_charge_nonneg.

### optimized_first_two_critical_level_bergman

Let the distinct-root monic degree-n polynomial have roots in the open unit disk and first two critical-value moduli 0<beta_1<beta_2. Put L=min(beta_2,1). If L^(2/n)(1/(n-1))^(2/n) log((L+beta_1)/(L-beta_1))<2, then two roots are joined inside {|f|<1} by a curve of length <2. The proof observes the first-merge two-root component at a regular t approaching L, uses the exterior-fibre area gap and connected-cluster Bergman theorem, and proves that t^(2/n)log((t+beta_1)/(t-beta_1)) is strictly decreasing. This strictly strengthens the returned geometric-mean-level theorem: its T=sqrt(beta_1 beta_2) satisfies T<L and its hypothesis bounds the same cost at T by 2R^2<2. A simpler sufficient condition is beta_1/L<tanh((n-1)^(2/n)). Unrestricted Erdos 1041 remains open in the rapid tied-level shell.

Evidence/status: ordinary_exact_all_degree_sufficient_theorem_with_lean_checked_scalar_kernel_and_symbolic_replay

- [FirstTwoCriticalOptimizedBergman.md](problem/FirstTwoCriticalOptimizedBergman.md)
- [check_erdos1041_first_two_critical_optimized_bergman.py](problem/scripts/check_erdos1041_first_two_critical_optimized_bergman.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.FirstTwoCriticalOptimizedBergman.derivativeBracket_neg, ErdosProblems.Erdos1041.FirstTwoCriticalOptimizedBergman.lengthSq_lt_four_of_cost_lt_two, ErdosProblems.Erdos1041.FirstTwoCriticalOptimizedBergman.optimizedCost_lt_two_of_returnedBudget, ErdosProblems.Erdos1041.FirstTwoCriticalOptimizedBergman.twoRootFibreConstant.

### finite_near_fekete_transverse_cones

For every fixed constant-free transverse cone h(0)=0 with a quantitative nonzero linear coefficient, the matched-asymptotic argument gives a uniform small-perturbation bound L < 2R and an open-disk corollary. The result closes a finite transverse shell, not the tangent directions, the D-away-from-one bulk, nonzero constant perturbations, or unrestricted Erdos #1041.

Evidence/status: ordinary_analytic_finite_transverse_shell_with_formal_transfer

- [NearFeketeTransverseClosure.md](problem/NearFeketeTransverseClosure.md)

### eventually_pos_of_scaled_deficit_tendsto_pos

A positive limit of the scaled transverse deficit implies that the deficit is eventually positive.

Evidence/status: lean_checked_eventual_sign_transfer

- [NearFeketeTransverseClosure.lean](problem/NearFeketeTransverseClosure.lean)

claim_boundary: The theorem is an eventual sign-transfer implication under its explicit limit premise. It does not prove the complex asymptotic premise, branch convergence, tangent control, or unrestricted Erdos #1041.

### eventually_length_lt_twice_radius

A positive transverse deficit yields eventual path length strictly less than twice the enclosing radius.

Evidence/status: lean_checked_eventual_length_transfer

- [NearFeketeTransverseClosure.lean](problem/NearFeketeTransverseClosure.lean)

claim_boundary: The theorem is a checked eventual length-transfer implication under its explicit positive-deficit premise. It does not prove the premise, branch convergence, tangent control, or unrestricted Erdos #1041.

### eventually_length_lt_two

An eventually subunit enclosing radius combined with the preceding transfer gives eventual path length strictly less than two.

Evidence/status: lean_checked_eventual_open_disk_transfer

- [NearFeketeTransverseClosure.lean](problem/NearFeketeTransverseClosure.lean)

claim_boundary: The theorem is only an eventual transfer from a subunit enclosing-radius premise to a strict length bound. It does not prove the premise, settle tangent directions or the bulk regime, or establish unrestricted Erdos #1041.

### newton_flow_value_equation

Away from a critical point, the complex Newton vector -f/f' cancels under the derivative: f'*(-f/f')=-f. Along any differentiable trajectory tangent to this field, the composite polynomial value therefore satisfies w'=-w.

Evidence/status: lean_checked

- [NewtonFlowRaySeparation.lean](problem/NewtonFlowRaySeparation.lean)

claim_boundary: The named declaration proves the local derivative identity and value ODE under its explicit differentiability and noncritical-point hypotheses. It does not prove global existence or uniqueness of a Newton trajectory, root-to-root branch selection, convex-hull invariance, an arclength bound, or unrestricted Erdős #1041.

### newton_descent_root_convex_hull_invariance

Let K be the convex hull of the roots. At a supporting line, rotate the outward normal to the positive real direction and write w_j for the root displacements. Then Re(w_j)>=0 implies Re(sum_j 1/w_j)>=0, hence the outward component of the Newton vector -(sum_j 1/w_j)^(-1) is nonpositive. Closed-convex viability makes K forward invariant for Newton descent. If a non-root critical point lies on a supporting face, reciprocal balance plus nonnegative summands forces every root displacement to lie on the supporting line; Lean checks this boundary rigidity. Therefore every canonical descending inverse-ray branch remains in K. For roots in the open unit disk this completely closes spatial containment, but not arclength: the corrected remaining producer is the sharp admissible-hub inequality min_{|f(c)|<1} L(c)<=2R.

Evidence/status: ordinary_analytic_proof_with_lean_checked_supporting_half_plane_and_boundary_rigidity

- [NewtonConvexHullInvariance.md](problem/NewtonConvexHullInvariance.md)
- [NewtonFlowRaySeparation.lean](problem/NewtonFlowRaySeparation.lean)

### newton_flow_exponential_first_integral

Along a Newton-flow trajectory, exp(t)f(z(t)) has derivative zero. This is the differential form of f(z(t))=exp(-t)f(z(0)).

Evidence/status: lean_checked

- [NewtonFlowRaySeparation.lean](problem/NewtonFlowRaySeparation.lean)

claim_boundary: The named declaration proves the local first-integral derivative identity under its explicit differentiability and flow hypotheses. It does not prove global existence or uniqueness of a Newton trajectory, root-to-root branch selection, convex-hull invariance, an arclength bound, or unrestricted Erdős #1041.

### value_ray_transport_containment_and_stretch_boundary

Let f be monic of degree at least two, let Gamma join distinct roots, and let its radial value cone C_lambda(Gamma) contain no critical value. Then the inverse lift of s f(z), s from 1 to lambda, is a continuous root-to-root transport with max |f| scaled by lambda; when lambda M<1 this repairs containment in the open lemniscate. Where defined away from roots, its derivative is N(z)/N(T_lambda z) for N=f'/f, so its length is the exact integral of the Newton-step ratio S(T_lambda z)/S(z), S=|f/f'|. For z^n-r^n the adjacent-chord midpoint reaches the sharpness radius at stop level one, while the pointwise sufficient contraction sign fails for every n at least three. Thus containment is available under cone avoidance, but neither a global length bound nor Erdős #1041 follows; the remaining obligation is integral metric control or a different global mechanism.

Evidence/status: ordinary_transport_and_stretch_proofs_with_exact_binomial_boundary_and_bounded_probe

- [NewtonFlowTransport.md](problem/NewtonFlowTransport.md)
- [erdos1041_newton_flow_transport.py](probes/erdos1041_newton_flow_transport.py)

### critical_value_ray_separation

The endpoints of any finite Newton-flow connection lie on the same oriented ray from zero. Consequently critical values on distinct positive rays cannot be joined by a Newton-flow saddle connection.

Evidence/status: lean_checked_consumer

- [NewtonFlowRaySeparation.lean](problem/NewtonFlowRaySeparation.lean)

claim_boundary: The named declarations prove the same-positive-ray consequence for a finite Newton-flow connection under their explicit hypotheses, including the resulting no-connection statement for distinct positive rays. They do not prove existence or uniqueness of trajectories, cover all critical-value configurations, establish global branch selection, or imply the unrestricted Erdős #1041 length bound.

### translated_ray_collision_parameterization

For distinct complex values a and b, every common translation beta for which a+beta and b+beta lie on the same positive ray has the explicit form beta=(r*a-b)/(1-r) for a real r>0 with r not equal to 1. Thus each pair contributes only a one-real-parameter forbidden locus.

Evidence/status: lean_checked

- [NewtonFlowRaySeparation.lean](problem/NewtonFlowRaySeparation.lean)

claim_boundary: The named declaration proves the explicit one-real-parameter form of the common-translation locus for one distinct pair under its stated hypotheses. It does not by itself prove finite-family avoidance, perturbation stability, a global Newton-flow construction, or the unrestricted Erdős #1041 conclusion.

### finite_planar_translation_avoidance

Every finite injective family of complex values admits an arbitrarily small common translation after which all values are nonzero and no two lie on the same positive ray. Lean enlarges each bad pair locus to a real affine line, proves every such line closed with dense complement in the complex plane, intersects the finitely many open dense complements, and chooses a point in the prescribed ball.

Evidence/status: lean_checked

- [NewtonFlowRaySeparation.lean](problem/NewtonFlowRaySeparation.lean)

### constant_perturbation_root_continuity

For a positive-degree monic split complex polynomial whose roots have norm at most rho, Lean specializes Mathlib's quantitative continuity-of-roots theorem to f+C(shift). If ((natDegree+1)*epsilon)^(natDegree)^(-1)+rho<1 and norm(shift)<epsilon, then every root of the perturbed polynomial still has norm strictly below one.

Evidence/status: lean_checked

- [NewtonFlowRaySeparation.lean](problem/NewtonFlowRaySeparation.lean)

### critical_value_level_separation

Every finite injective complex family admits an arbitrarily small common translation after which every value is nonzero, no two values lie on the same positive ray, and no two have equal norm. The equal-norm pair locus is explicitly a real affine line.

Evidence/status: lean_checked

- [LevelSeparation.lean](problem/LevelSeparation.lean)

claim_boundary: The result is a finite-family translation-avoidance theorem. It does not establish that a polynomial perturbation preserves the required root geometry, prove a critical-point path-length bound, or close the unrestricted Erdos #1041 statement.

### spoke_escapes_lemniscate_exact

For the exact degree-five model F(z)=(z-r)(z-ir)(z+ir)(z-rω)(z-rω̄), with r=999/1000 and ω=e^(2πi/3), the critical point 0 has |F(0)|=r^5<1 but the real spoke already exits the open unit lemniscate at z=r/10: |F(r/10)|=r^5·100899/100000>1, witnessed by the Lean-checked integer inequality 10^20 < 999^5·100899.

Evidence/status: lean_checked_exact_counterexample

- [CriticalTwoRootProximity.lean](problem/CriticalTwoRootProximity.lean)

claim_boundary: This is an exact mechanism counterexample to blanket fixed-spoke or star-shapedness completion from a logarithmic critical point. The two spokes toward ±ir remain safe, so it does not refute Erdos #1041, the existence of another root pair, or curved descending paths; it only forces the remaining argument to make a genuine branch or path selection.

### bernoulli_sharp_two_distance_kernel_consumer

For m∈ℕ and positive normalized distances a≤b with b≤m·a and a·b^m≤1, the exact Bernoulli kernel forces a+b≤2. This is the sharp scalar inequality that converts reciprocal critical balance and geometric-mean product control into the constant-2 two-distance bound.

Evidence/status: lean_checked_bernoulli_sharp_two_consumer

- [CriticalTwoRootProximity.lean](problem/CriticalTwoRootProximity.lean)

claim_boundary: This is an elementary normalized-distance implication, not the global polynomial theorem by itself. It does not supply the critical-point hypotheses, identify actual roots, prove lemniscate containment of spokes or curved connectors, resolve branch selection, or close unrestricted Erdos #1041.

### critical_pair_metric_scale

At a logarithmic critical point, if r is the positive geometric mean of the root distances, two distinct roots have total distance from that point at most 2r. This sharp scale result does not put either straight spoke inside the lemniscate.

Evidence/status: lean_checked_conditional

- [CriticalTwoRootProximity.lean](problem/CriticalTwoRootProximity.lean)

### global_disk_inverse_balance_budget_consumer

For real parameters N,t,δ,e with N≥2, t<1, 0<δ≤e≤1+t, δ≤1, e≤(N−1)δ, and the inverse-square disk estimate N≤(1−t²)(1/δ²+(N−1)/e²), the exact Lean kernel forces δ+e≤2. These are the scalar geometric inputs used by the global closed-unit-disk two-nearest-root budget.

Evidence/status: lean_checked_global_disk_inverse_balance_consumer

- [CriticalTwoRootProximity.lean](problem/CriticalTwoRootProximity.lean)

claim_boundary: This is the algebraic core of the global metric budget, not a proof of the unrestricted Erdos #1041 path theorem. It does not supply the polynomial-to-hypothesis instantiation, put the selected spokes or any replacement connector inside the lemniscate, or resolve branch selection and curved-path geometry; the packet's open containment boundary remains unchanged.

### global_critical_two_nearest_root_budget

For every monic polynomial of degree at least two whose roots lie in the closed unit disk, and every critical point c, two roots counted with multiplicity have total distance from c at most 2. If c is not a root, the two nearest roots work. Rotate c to t>=0, use the unit-disk constraints and reciprocal critical balance to obtain n<=(1-t^2)sum d_j^(-2), delta<=1, e<=(n-1)delta and e<=1+t. A hypothetical delta+e>2 gives 1-t^2<delta*e and hence n<e/delta+(n-1)delta/e, contradicting 1<=e/delta<=n-1. This globally closes the metric-budget subproblem B1 but supplies no contained path.

Evidence/status: ordinary_complete_global_metric_theorem_with_lean_checked_algebraic_core

- [GlobalCriticalTwoNearestBudget.md](problem/GlobalCriticalTwoNearestBudget.md)

### legacy_minimum_critical_descent_branch_reconciliation

The legacy quartic score 2.0068 was a branch-tracking error, not a counterexample. Exact recovery of the recorded eight-decimal Gaussian-rational roots and residual-gated inverse-value continuation lands the two descending branches at roots 0 and 1 with normalized total length 0.7385324012 at three step sizes. The receipt validates the historical computation only and is not used by the global metric proof.

Evidence/status: exact_root_recovery_with_residual_gated_numerical_regression

- [check_legacy_minimum_critical_descent_regression.py](problem/scripts/check_legacy_minimum_critical_descent_regression.py)
- [MinimumCriticalNewtonHubLab.md](problem/MinimumCriticalNewtonHubLab.md)

### cubic_minimal_critical_value_short_hub

The degree-three case of Erdős #1041 is proved. For a squarefree cubic, choose the critical point c of smaller critical-value modulus, write the other critical point as c+delta, choose alpha^3=f(c), and put b=delta/alpha. The normalized polynomial is P_b(w)=w^3-(3/2)b*w^2+1 and minimality gives |1-b^3/2|>=1. A Rouché/homotopy lemma proves that P_b has two roots in the closed unit disk. For each such root, the exact identity P_b(tw)=1-t^2-t^2(1-t)w^3 keeps the straight spoke below one, while scaling back gives combined length at most 2|f(c)|^(1/3)<2. The double-critical case is radial and follows from the mean squared root norm. Multiple roots are immediate. This settles cubics only; the all-degree problem remains open.

Evidence/status: ordinary_complete_degree_three_proof_with_lean_checked_consumer

- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.normalizedCubic_spoke_identity, ErdosProblems.Erdos1041.cubicSpoke_envelope_le_one, ErdosProblems.Erdos1041.normalizedCubic_spoke_norm_le_one, ErdosProblems.Erdos1041.two_small_normalized_roots_give_short_hub, ErdosProblems.Erdos1041.normalizedCubic_two_small_roots_fan_in.

### unique_nearest_straight_spoke_counterexample

There is an exact balanced five-root configuration with p=999/1000, a=(901/902)p, and roots a, plus or minus ip, and p(-451 plus or minus 780i)/901. All roots lie in the open unit disk, their reciprocal sum is zero, and a is the unique nearest root to the critical point 0. Yet at z=a/10 the monic factored polynomial has modulus 59875209312258922123673577759296931/59708022487203200000000000000000000>1. Therefore the nearest/second-nearest pair from the metric proof cannot in general be joined through the critical point by two straight spokes inside the lemniscate. This kills that completion, not Erdős #1041 or curved descending paths.

Evidence/status: lean_checked_exact_counterexample

- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.nearestSpoke_reciprocal_balance, ErdosProblems.Erdos1041.nearestSpoke_unique_nearest_normSq, ErdosProblems.Erdos1041.nearestSpoke_unique_nearest_spoke_escapes.

### metric_selected_newton_branch_hub_counterexample

For the same exact balanced quintic, the two canonical descending inverse-ray branches from the metric critical point 0 have combined length greater than 520999/250000=2.083996. An exact critical-level resultant excludes intervening critical values; exact rectangle root counts and boundary isolation identify the two half-level branch points; rational Rouche disks locate them; and triangle inequalities from either disk to every polynomial root give the strict length lower bound. Thus Newton containment does not repair the metric-selected critical point: any critical-hub proof needs a new critical-point selection principle or global Reeb geometry. Other critical points remain live, and Erdős #1041 remains open.

Evidence/status: exact_algebraic_topological_mechanism_elimination_not_lean_checked


### all_straight_root_pair_segments_counterexample

For the exact monic cubic f(z)=z^3-(99/100)^3, all three roots lie in the open unit disk, but every pair midpoint has polynomial value -9(99/100)^3/8 and hence modulus greater than one. Therefore every straight segment between distinct roots exits the strict unit lemniscate. Yet the broken line r to 0 to r*omega stays inside and has length 2r<2. This eliminates all direct root-chord proofs while opening an exact critical-point-hub mechanism; it does not force curvature and leaves Erdős #1041 open.

Evidence/status: lean_checked_exact_mechanism_elimination

- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.allStraightCubic_roots_in_unitDisk, ErdosProblems.Erdos1041.allStraightCubic_roots, ErdosProblems.Erdos1041.allStraightCubic_every_pair_midpoint_escapes.

### binomial_complementary_chord_short_path

For every n >= 2 and every nonzero a with |a|<1, two adjacent roots of z^n-a have an explicit polygonal path inside |z^n-a|<1 of length below 2. For n>=3, the adjacent-root chord is strictly contained below the exact threshold |a| <= 1/(1+cos(pi/n)^n); at and above it, a maximal inner crossing chord has closed containment with one midpoint touch, and radial contraction makes it strict without reaching length 2. The chord maximum, common transition, crossing-radius maximality, and strictification form one theorem stack. This settles the binomial subfamily only, makes no path-optimality claim, and does not select paths for arbitrary monic polynomials or settle Erdős #1041.

Evidence/status: ordinary_complete_all_degree_binomial_subfamily_proof_with_bounded_exact_replay

- [CrossingChordUpperBound.md](problem/CrossingChordUpperBound.md)
- [check_erdos1041_crossing_chord.py](problem/scripts/check_erdos1041_crossing_chord.py)

### quartic_core_factor_budget_radius_class

Let four selected roots lie in a disk D(h,R) with 0<R<1. If R^4 times the product over all unselected roots of (R+|z_k-h|) is at most 1, then the published degree-four Pendyala construction, translated and scaled, gives two selected roots joined inside |f|<1 by a polygonal path of length below 2R<2. The Lean declarations check the scalar and complex factor-budget fan-in, the uniform-radius identity, and the exact rational quintic budget witness; they do not formalize Pendyala's geometric construction or the whole analytic transport. Consequently every degree-n configuration of circumradius rho<2^(4/n-1) lies in the resulting radius class. This does not supply a favorable quartet/centre for arbitrary configurations, claim an optimal radius, or settle Erdős #1041.

Evidence/status: ordinary_all_degree_radius_class_transport_with_external_quartic_input_and_lean_checked_factor_budget

- [QuarticCoreRadiusCase.md](problem/QuarticCoreRadiusCase.md)
- [check_erdos1041_quartic_core_radius_case.py](problem/scripts/check_erdos1041_quartic_core_radius_case.py)
- [QuarticCoreRadiusCase.lean](problem/QuarticCoreRadiusCase.lean)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.quarticCore_factor_budget, ErdosProblems.Erdos1041.quarticCore_complex_factor_budget, ErdosProblems.Erdos1041.quarticCore_uniform_budget_identity, ErdosProblems.Erdos1041.quarticCore_uniform_factor_budget, ErdosProblems.Erdos1041.quarticCoreWitness_factor_budget.

### two_safe_origin_spokes_counterexample

Let r=99999/100000 and take roots r, r(-20 plus or minus 99i)/101, and r(-28 plus or minus 195i)/197. These are five distinct roots strictly inside the unit disk. Exact Gaussian-rational evaluation at t=3/125 on the first conjugate pair of root-to-origin spokes and t=17/1000 on the second pair gives |f(tz)|^2>1 in all four cases. Thus at most one root-to-origin spoke is contained in the strict unit lemniscate, decisively eliminating the tempting shortcut of selecting two safe spokes and joining their roots through the fixed hub 0. The all-critical inverse-ray and global Reeb routes remain open.

Evidence/status: exact_gaussian_rational_mechanism_elimination


### minimum_critical_straight_hub_counterexample

Minimal critical-value selection does not rescue straight critical spokes. Five explicit Gaussian-rational roots of common norm 999999/1000000 have four derivative roots isolated in pairwise disjoint exact Rouche disks. Rational interval evaluation proves that one critical-value modulus is strictly smallest and below one. At that first critical point, four of the five root spokes have named dyadic waypoints with exact lower bounds |f|^2>1, so at most one spoke is contained and no two-spoke straight hub exists. This eliminates only the straight completion of the canonical first-merge reduction. The same witness has numerical descending inverse-ray length about 1.755, so the curved first-merge theorem remains constructive.

Evidence/status: exact_gaussian_rational_interval_mechanism_elimination

- [check_minimum_critical_straight_hub.py](problem/scripts/check_minimum_critical_straight_hub.py)

### adaptive_mec_chord_or_radial_counterexample

The direct all-degree extension of Pendyala's quartic argument is false in degree five. Five explicit Gaussian-rational roots of norm 9999/10000 have minimum enclosing disk centered at zero, certified by positive rational barycentric weights on three unit directions. Exact factored evaluation at fourteen rational waypoints shows that every one of the ten root chords exits |f|<1 and that four of the five radial arms through the minimum-enclosing-disk center exit as well. Hence neither branch of the adaptive disjunction--one safe chord or two safe MEC radial arms--is available. This does not refute Erdős #1041; it forces a polynomial-adapted non-MEC hub, curved path, or global component/Reeb mechanism.

Evidence/status: exact_gaussian_rational_mechanism_elimination


### cassini_tree_budget_falsifier

Under the explicit coarea level-length majorant, the Cassini witness a=9/10 makes the proposed tree budget strictly shorter than the distance between its roots. Source-pinned replay shows that this is exactly the epsilon-sharp spanning-tree estimate asserted by Proposition 12 of the March unrestricted draft and Proposition 7 of the shorter unrestricted draft. Both load-bearing propositions are therefore false, independently of their different local-topology discussions. This refutes those candidate proofs, not Erdős #1041; the same quadratic has a straight root segment of length below two inside its lemniscate.

Evidence/status: lean_checked_source_linked_dual_draft_mechanism_elimination


### cassini_positive_attachment_deficit

At a=9/10, every connected root-spanning length exceeds the proposed coarea budget by more than 4/25. Therefore a strip proof cannot choose independently average-short Newton trajectories and repair their attachment mismatch inside arbitrarily small saddle neighbourhoods. In the Cassini flow only the critical-value-ray trajectory reaches the saddle; generic average-selected trajectories miss every sufficiently small saddle neighbourhood. This eliminates the additive-error strip-length fan-in with the unchanged 1/(2pi) coefficient, while leaving the compact Reeb decomposition and direct two-root path mechanisms open.

Evidence/status: lean_checked_mechanism_elimination


### cassini_no_uniform_length_slack

For the admissible quadratic family f_m(z)=z^2-((m-1)/m)^2, the two roots have distance 2-2/m. Lean proves the quantified consequence that no positive polynomial-independent delta can strengthen the target bound from 2 to 2-delta. Near-regular all-critical Newton-hub probes selected this exact boundary after their normalized minimum score approached one. Generic perturbation and root transfer must therefore preserve a data-dependent strict slack rather than spend a fixed global margin.

Evidence/status: lean_checked_exact_mechanism_elimination


### radial_lift_coarea_critical_ray_sampling_obstruction

If R(theta) is the total length of every inverse lift of the value-plane radius at angle theta, the area formula gives integral R(theta) dtheta = integral over |f|<1 of |f'|/|f| dA. This is only an angular L1 identity. The explicit family f_epsilon(z)=z^n+epsilon*z-r^n has n-1 simple critical points c with c^(n-1)=-epsilon/n and critical values -r^n-(n-1)c^n, so all critical-value arguments coalesce at pi. In the limit f_0=z^n-r^n the complete negative-ray lift has exact length n(r+(1-r^n)^(1/n)); charging it once per critical point already exceeds the desired 2(n-1) scale for r=9/10. Therefore the aggregate inverse-ray conjecture cannot follow by sampling the raw coarea angular average at every critical ray. The conjecture remains open only through a multiplicity-aware descending-edge or Reeb charge.

Evidence/status: exact_area_formula_and_explicit_family_mechanism_elimination


### finite_exceptional_linear_critical_value_perturbations

For every complex polynomial f of degree at least two, all but finitely many lambda make f+lambda*z have simple critical points with pairwise distinct critical values. The proof eliminates lambda from a collision pair (u,v): the divided-difference equations (f'(u)-f'(v))/(u-v)=0 and (f(u)-f(v))/(u-v)-f'(u)=0 have no common projective point at infinity, hence only finitely many affine solutions. Thus the one-coefficient perturbation supplies the genericity part of the former first producer arbitrarily close to zero.

Evidence/status: ordinary_algebraic_proof_not_lean_checked

- [erdos-1041-lemniscate-newton-flow.tex](paper/erdos-1041-lemniscate-newton-flow.tex)

### compact_barrier_stability_under_linear_constant_perturbation

For a compact protected set free of critical points, finitely many root discs with nonvanishing boundary values, and finitely many compact regular-level barriers, the explicit inequalities |lambda|<min_C|f'| and R|lambda|+|beta| below the root and level margins ensure that f+lambda*z+beta has no critical point in the protected set, preserves every root-disc zero count by Rouche's theorem, and remains on the same side of every designated level barrier. The protected-set noncriticality implication is separately Lean-checked; the Rouche and level-side implications remain ordinary proof.

Evidence/status: ordinary_algebraic_proof_with_lean_checked_protected_set_component

- [NewtonFlowRaySeparation.lean](problem/NewtonFlowRaySeparation.lean)
- [erdos-1041-lemniscate-newton-flow.tex](paper/erdos-1041-lemniscate-newton-flow.tex)

### protected_set_noncriticality_under_small_linear_perturbation

If lower is a uniform lower bound for the derivative norm on a protected set C and the linear-coefficient perturbation shift has norm below lower, then f'(z)+shift is nonzero for every z in C. This is exactly the protected-set noncriticality component of the compact-barrier argument.

Evidence/status: lean_checked_comparator_targeted

- [NewtonFlowRaySeparation.lean](problem/NewtonFlowRaySeparation.lean)

### straight_spoke_hub_criterion_separation

Two containment tests for a two-spoke critical hub had been used interchangeably and are different statements. The hub-sublevel test asks |f| <= |f(c)| on the spoke; the open-lemniscate test asks only |f| < 1, which is all the target needs because |f(c)| < 1 already. The landed degree-three theorem proves the sublevel form: its identity P_b(tw) = 1 - t^2 - t^2(1-t)w^3 gives |P_b(tw)| <= 1 - t^3, and |P_b| <= 1 is exactly |f| <= |f(c)|. The sublevel form is false from degree four. The exact Gaussian-rational quartic with roots (9999+4i)/10000, (-125+9998i)/10000, (-9999-14i)/10000 and (-23-9999i)/10000 has all roots strictly inside the open unit disk by the integer inequality a^2+b^2 < 10^8, and each of its two admissible critical points carries at most one sublevel-contained spoke, so the sublevel mechanism yields no two-spoke path at all. The same hubs carry three open-contained spokes with best pair 1.787689338 < 2, so the two criteria genuinely separate. The weaker criterion then fails as well two degrees later: witnesses at degree six and degree nine (stored as exact IEEE-754 hexadecimal literals, roots strictly inside the unit disk) have every admissible critical point carrying at most one open-contained spoke, verified at 60 digits with f' residuals near 1e-61. At those configurations no critical point supplies a two-straight-spoke path at all, while the two descending inverse-ray branches at the same hubs give 1.763942 and 1.545995. Segment maxima are located from the real roots of d|f|^2/dt along the segment rather than sampled. Verified in float64 and re-derived at 60 decimal digits. The critical points are located numerically, not by exact rational Rouche disks; margins are 1.72e-5 and 1.96e-5 on the second spoke and 1.22e-3 on the inadmissible hub, so a certified enclosure of radius below 1e-7 would close that gap.

Evidence/status: high_precision_witness_mechanism_elimination_not_lean_checked

- [check_erdos1041_straight_spoke_hub_criterion.py](problem/scripts/check_erdos1041_straight_spoke_hub_criterion.py)
- [StraightSpokeHubCriterionLab.md](problem/StraightSpokeHubCriterionLab.md)

### admissible_branch_length_reformulation

The surviving obligation must retain the polynomial-value threshold: min over admissible critical points c, meaning |f(c)|<1, of L(c) <= 2R. A short inverse-ray pair at an inadmissible hub need not lie in the target lemniscate, and scaling the roots changes critical values, so the earlier all-critical-point affine-invariant wording was insufficient. The corrected statement implies the target because roots in the open unit disk have R<1. Equality is attained and identifiable. Every monic quadratic gives equality exactly: with c the midpoint and d the half-difference, f(c+u)=u^2-d^2, so the descending pair is the root segment of length 2R and its critical value has modulus |d|^2<1. The family z^n-r^n gives equality too at its admissible central critical point. The per-hub strengthening L(c)<=2 max_k |z_k-c| is nevertheless false at an explicit admissible quartic hub with ratio 1.210001551, while the admissible minimum at that configuration is 0.306554. Thus the minimum over admissible hubs is load-bearing.

Evidence/status: corrected_obligation_plus_ordinary_equality_proofs_and_witness_elimination_not_lean_checked

- [check_erdos1041_invariant_branch_length.py](problem/scripts/check_erdos1041_invariant_branch_length.py)
- [CriticalTreeLengthCharge.md](problem/CriticalTreeLengthCharge.md)

### admissible_critical_forest_tangent_support_reduction

Let A be the admissible critical points, counted with multiplicity, and m=|A|. The stronger inequality sum_{c in A} L(c)<=2Rm would imply the required admissible minimum. For an edge from roots a,b, let U_a,U_b point from the roots toward its critical point and let K_e=integral kappa<z,N> ds. Exact differentiation gives 2R-L(e)=(R+<a,U_a>)+(R+<b,U_b>)+K_e. The endpoint deficits are nonnegative, and on a Newton half-edge d arg T=-Im((f''/f')dz). Thus the theorem is exactly nonnegativity of the combined endpoint-deficit plus signed-curvature charge. For a level-one component Omega containing k roots, f:Omega->D is proper of degree k; after a Riemann map phi:D->Omega, B=f o phi is a degree-k finite Blaschke product, the component has k-1 critical points by Riemann-Hurwitz, and its total critical-tree length is integral_{Gamma_B}|phi'|. The component lemma is therefore the trace bound integral_{Gamma_B}|phi'|<=2R(k-1), retaining the polynomial coupling and global R. The deterministic receipt evaluates 521 complete admissible-hub sets in degrees 3,4,5,6,8; the largest normalized admissible aggregate is 0.988850245227178. Curvature alone can be negative by 0.1613048394826284, root-star allocation is negative on a pinned quartic, and component-local circumradius fails on a pinned separated sextic. All survivals are falsifier results only.

Evidence/status: ordinary_exact_calculus_and_uniformization_reduction_plus_finite_aggregate_falsifier

- [CriticalTreeLengthCharge.md](problem/CriticalTreeLengthCharge.md)
- [check_erdos1041_invariant_branch_length.py](problem/scripts/check_erdos1041_invariant_branch_length.py)

### complete_cyclic_hub_orbit_correlation_cancellation

For complex nu,a,b, twice Im(nu*a)Im(nu*b) is normSq(nu) Re(a*conj(b)) minus the frequency-two term Re(nu^2*a*b). Therefore a finite unit family with sum nu^2=0 has doubled total correlation equal to its cardinality times Re(a*conj(b)), and the total is nonnegative whenever that surviving real correlation is nonnegative. Lean also proves the concrete cyclic form: if zeta^m=1, zeta^2 is not 1, and zeta and the seed have unit squared norm, then the orbit nu_i=zeta^i nu_0 has vanishing square moment and satisfies the same exact identity.

Evidence/status: lean_checked_exact_algebraic_kernel

- [NearFeketeHubOrbit.lean](problem/NearFeketeHubOrbit.lean)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.two_mul_im_mul_im, ErdosProblems.Erdos1041.two_mul_sum_im_mul_im_of_sum_sq_eq_zero, ErdosProblems.Erdos1041.two_mul_sum_im_mul_im_of_unit_sum_sq_eq_zero, ErdosProblems.Erdos1041.sum_im_mul_im_nonneg_of_unit_sum_sq_eq_zero, ErdosProblems.Erdos1041.cyclic_orbit_sum_sq_eq_zero, ErdosProblems.Erdos1041.two_mul_cyclic_orbit_sum_im_mul_im, ErdosProblems.Erdos1041.cyclic_orbit_sum_im_mul_im_nonneg.

### strong_completion_multi_seeded_pressure_and_cubic_sweep

Evidence on the STRONG completion named in MinimumCriticalNewtonHubLab.md, L_1 + L_2 <= 2 rho with rho = |f(c*)|^(1/n) at the minimum-critical hub, as distinct from the weak 2R completion that admissible_critical_forest_tangent_support_reduction pursues. The minimum-critical hub is admissible whenever the roots lie in the open unit disk, since Fekete gives |f(c*)| <= R^n < 1, so the strong statement does not need the separate admissibility qualifier. Its dedicated falsifier critical-scale-normalized-minimum-critical-newton-hub had reached 0.9495242630078684 on a canonical degree-five run. Five independent seedings -- near-extremal, uniform, clustered, near-collision and a combined restart -- drive the ratio to 0.999994283 at degree three without crossing one. The degree-three case is swept COMPLETELY rather than sampled: normalising gives P(u) = u^3 + s u^2 + 1 with critical points 0 and -2s/3 and P(-2s/3) = 1 + 4 s^3 / 27, so minimality is exactly |1 + 4 s^3 / 27| >= 1, and 2328 admissible parameters give maximum branch pair length 1.997967707 with zero violations. Two structural facts come with it. The extremum is a CUSP: at z^n - r^n the critical point has multiplicity n-1, and splitting it drops the ratio by a fractional power of the perturbation -- at degree five 1e-9 gives 0.99648, 1e-6 gives 0.98012, 1e-3 gives 0.88553 -- so a second-order variational argument at the extremum will not see the right behaviour. And every monic quadratic is a second exact equality family, L = |z1 - z2| = 2|d| with |f(c)| = |d|^2, hence L = 2|f(c)|^(1/2).

Evidence/status: finite_evidence_plus_complete_one_parameter_sweep_not_lean_checked

- [check_erdos1041_minimal_hub_metric_scale.py](problem/scripts/check_erdos1041_minimal_hub_metric_scale.py)
- [StraightSpokeHubCriterionLab.md](problem/StraightSpokeHubCriterionLab.md)

### turning_floor_at_simple_saddle

At a simple critical point c whose two descent branches reach roots a and b, with alpha_A, alpha_B the total variations of the tangent direction and phi the angle a-c and b-c subtend at c, alpha_A + alpha_B >= pi - phi, hence alpha_max >= (pi - phi)/2. Proof: the two descending directions at a simple saddle are exactly opposite, and a curve's chord direction lies in the convex hull of its tangent directions. Zero violations in 978 hubs, minimum slack 3.5e-4 rad. See TurningFloorRefutation.md.

Evidence/status: ordinary_proof_plus_finite_verification


### chord_deficit_length_identity

For a branch from p to q with unit tangent T and chord direction e, L = |q-p| + integral (1 - cos theta(s)) ds where theta(s) = angle(T(s), e), since integral T ds = q - p. Summing both branches at a hub gives L(c) = (d1 + d2) + D(c) with D(c) >= 0, exactly tight on z^n - r^n where D(c) -> 0. Restates MIN as: at some admissible hub D(c) < 2 - (d1 + d2). See TurningFloorRefutation.md.

Evidence/status: elementary_identity


### reciprocal_adjoint_resultant_power_sum_identity

For roots a_1..a_n in the open unit disk and f* the reciprocal adjoint, |Res(f, f*)| = prod_{j,k} |1 - conj(a_j) a_k| = exp(-sum_{m>=1} |p_m|^2 / m) <= 1 with p_m the power sums, equality iff f = z^n. Corollary: min_k |g(a_k)| <= 1, so a root-centred reciprocal sweep always exists, answering the precondition of transfer question 1 in ReciprocalSweepBoundaryLab.md. Novelty NOT claimed: plausibly classical Schur-Cohn material, priority search still required. See RootCentredReciprocalSweep.md.

Evidence/status: ordinary_proof


### extremal_family_sweep_component_separation

For f = z^n - r^n, g = f* = 1 - r^n z^n, every root has the same sweep level |g(a_k)| = 1 - r^(2n), and {|g| < 1} inside the disk has exactly n components each holding one root. Hence no root-to-root path exists inside {|g| < 1}; any such path in {|g| <= 1} passes through z = 0 and the shortest is the radial spoke pair of total length exactly 2r. The reciprocal sweep therefore recovers 2r exactly on the extremal family and offers no slack. See RootCentredReciprocalSweep.md.

Evidence/status: ordinary_proof_plus_finite_verification


### admissible_forest_aggregate_in_the_hard_regime

The admissible-forest aggregate sum_{c in A} L(c) <= 2 R m of CriticalTreeLengthCharge.md was measured over 521 bulk-drawn complete hub sets with maximum normalized ratio 0.988850245227178. But (A) is TIGHT on z^n - r^n and HardRegimeIsNearFekete.md shows the hard configurations are the near-Fekete ones, so a violation would live in the shell and the bulk maximum is not the relevant number. Measured inside the shell -- roots r(1+a_k)exp(i(2 pi k/n + t_k)) with r just below one, eight perturbation scales from 1e-2 to 1e-7 -- (A) holds at every scale and climbs monotonically toward one, with worst ratios 0.999984770, 0.999094123, 0.995004633 and 0.989932789 at degrees 3 to 6. Every shell configuration has exactly n-1 admissible hubs. A measurement risk had to be ruled out first: near-Fekete hubs are near-degenerate and the branch integrator under-reports at an exactly degenerate hub, so an under-reported aggregate would look safe precisely where it is tightest. Each arc is therefore integrated twice, by the level substitution f(z(u)) = (1-u^2) f(c) and independently through the square-root resolution xi^2 = f(c) - w. They agree to about 1e-15 down to perturbation 1e-4 and to 4e-8 at 1e-7, so the under-report does not reach the shell and the numbers can be read.

Evidence/status: finite_falsifier_survival_in_the_identified_hard_regime_with_independent_integrator_check

- [check_erdos1041_aggregate_near_fekete.py](problem/scripts/check_erdos1041_aggregate_near_fekete.py)
- [StraightSpokeHubCriterionLab.md](problem/StraightSpokeHubCriterionLab.md)

### centre_plus_polygon_merge_topology_closed_form

On f(z) = z(z^(n-1) - r^(n-1)) the merge-topology summed ratio has the closed form n mu (1/|f'(0)| + 1/|f'(r omega)|)/(2R) = n^((n-2)/(n-1))/2, independent of r, using mu = r^n (n-1)/n^(n/(n-1)), R = r, |f'(0)| = r^(n-1) and |f'(r omega^k)| = (n-1) r^(n-1). Values 1.259921 at n=4, 3.871318 at n=10, 13.340007 at n=30, asymptotically ~n/2. Derived by hand and verified against direct computation for n = 4..30 at r in {0.95, 0.999} to worst relative gap 5.5e-15. See MergeTopologyBoundRefutation.md.

Evidence/status: ordinary_proof_plus_finite_verification


### quantitative_fekete_stability_hadamard_defect

HardRegimeIsNearFekete.md names a stability estimate for the Fekete maximiser as the missing object joining its two halves. Here is one. With V_{ij}=a_j^i (i=0..n-1), G=VV^*, g_i=G_ii=sum_j|a_j|^{2i}, and Ghat=G/sqrt(g_i g_k), the identity det G = prod_{i<j}|a_i-a_j|^2 plus the scalar inequality log mu <= (mu-1)-(mu-1)^2/(2n) on (0,n] applied to the eigenvalues of Ghat (psd, unit diagonal, trace n, so spectrum in [0,n]) give prod_{i<j}|a_i-a_j|^2 <= (prod_i g_i) exp(-||Ghat-I||_F^2/(2n)), hence D <= exp(-||Ghat-I||_F^2/(2n)). Corollaries: (C1) g_i/n >= D for every i, so D near one forces every modulus near one; (C2) for roots on the unit circle, sum_{m=1}^{n-1}(n-m)|p_m|^2 <= n^3 log(1/D), so by Newton's identities D near one forces f close to z^n+e_n. Equality exactly at the regular n-gon on the unit circle. Fekete's own bound is the Hadamard step alone; this is its defect term.

Evidence/status: ordinary_complete_proof_not_lean_checked_novelty_not_claimed

- [check_erdos1041_near_fekete_cusp_law.py](problem/scripts/check_erdos1041_near_fekete_cusp_law.py)
- [NearFeketeCuspLaw.md](problem/NearFeketeCuspLaw.md)

### near_fekete_cusp_law_and_strict_local_maximality

For f = z^n - m + eps*h (deg h <= n-1, m = R^n), the critical points solve n z^{n-1} = -eps h'(z), so at leading order they form a regular (n-1)-gon of radius rho = (eps|h'(0)|/n)^{1/(n-1)} rotated by arg(-eps h'(0))/(n-1): ONLY h'(0) enters. Rescaling z = rho zeta and using eps = n rho^{n-1} gives f(z)+m = rho^n (zeta^n + n zeta), so the near field is the eps-free, R-free model g(zeta)=zeta^n+n zeta, whose critical points are exactly zeta^{n-1}=-1 with critical values (n-1)zeta_c. Matching to the far field (radial segments of z^n = m sigma, length R) gives L(c) = 2R - kappa_n(phi) rho + O(rho^2) with kappa_n(phi)=beta_1+beta_2 the renormalised near-field excess, phi = arg h'(0). Measured limits at phi=0 (which is where the minimum over phi sits): kappa_3=0.60802134, kappa_4=1.0301197, kappa_5=1.2585783, kappa_6=1.3989124, eight converged digits, identical at R=0.5 and R=0.9. Full direction sweeps give min_phi kappa_3=0.6080216 (max 0.8125984) and min_phi kappa_4=1.0301197 (max 1.1341439), 2pi/n-periodic, STRICTLY POSITIVE at every sampled direction. Random h confirm universality to six digits via arg h'(0). Hence z^n - mu is a strict local maximum of min_c L(c)/(2R) with value exactly 1, approached at rate eps^{1/(n-1)}.

Evidence/status: ordinary_scaling_proof_plus_high_precision_constants_not_lean_checked

- [check_erdos1041_near_fekete_cusp_law.py](problem/scripts/check_erdos1041_near_fekete_cusp_law.py)
- [NearFeketeCuspLaw.md](problem/NearFeketeCuspLaw.md)

### chord_deficit_polynomial_representation

TurningFloorRefutation.md reduces MIN to D(c) < 2 - (d1+d2) and states that 'the content would be an estimate for D(c) in terms of the polynomial, and none is offered'. This supplies the exact representation such an estimate must start from. Parametrising a descent half-edge by the value radius, f(z(rho)) = rho e^{i theta} gives dz = e^{i theta} d rho / f'(z), hence L_A = int_0^{|v|} |1/f'| d rho and c - a = e^{i theta} int_0^{|v|} (1/f') d rho. So the chord deficit of a branch is EXACTLY the triangle-inequality defect of the complex integral of 1/f' along the descent ray: D_A = int |1/f'| d rho - |int (1/f') d rho|. Since f is monic, f' = n prod_j (z - c_j) over the n-1 critical points, so L(c) = (1/n) sum_branches int_0^{|v|} d rho / prod_j |z(rho) - c_j| -- length and deficit are both integrals of the reciprocal product of distances to the CRITICAL POINTS, not the roots. Verified against tracked branches to 1e-9 (the start truncation), with L(c) - (d1+d2) = D(c) closing to 1e-16. Consequence: arg f' = sum_j arg(z - c_j), so the deficit is driven by the angles the branch subtends at the critical points weighted by ds, and D_A <= (1/2) int |1/f'| (arg(1/f') - beta)^2 d rho is precisely the weighted L^2 turning bound the refutation names as sufficient, written against the polynomial's own critical divisor. No estimate is claimed.

Evidence/status: ordinary_identity_plus_numerical_verification

- [StraightSpokeHubCriterionLab.md](problem/StraightSpokeHubCriterionLab.md)

### two_segment_containment_reduction

Erdos #1041 follows from a pure CONTAINMENT statement with no length integral. If for every monic f with roots in the open unit disk there are distinct roots a,b and a point h with max_[h,a]|f| < 1, max_[h,b]|f| < 1 and |h-a| + |h-b| < 2, then the polygonal path a -> h -> b settles the problem. Condition (iii) says exactly that h lies in the open ellipse with foci a,b and major axis 2, so the length obligation becomes a two-real-dimensional membership test on ONE POINT rather than a functional inequality along a curve: straight segments have zero chord deficit, so D(c), the turning floor, and the branch-length integral int_0^mu ds/|f'| all vanish from the statement. The ellipse always contains the chord [a,b], and always contains the origin since |a|+|b| < 2; when |a| = |b| = 1 the origin lies exactly ON the ellipse, so the two-radius broken line of the extremal family z^n - r^n is the boundary case of the whole mechanism. This is a SUFFICIENT family, so its failure would not refute the problem. Free-hub feasibility holds at every recorded hard witness (best hub max|f| = 0.943, 0.970, 0.005, 0.956, 0.99995, 0.99994 at the degree-3 witness, cubic z^3-(99/100)^3, degree-5 origin-spoke lab, degree-5 adaptive-MEC, and the degree-6 and degree-9 QC = infinity witnesses), including the two rows where chords and the centre hub are simultaneously empty and the two rows where no critical hub carries two spokes. Adversarial hill-climbing on V = min over pairs min over ellipse hubs max(max_[h,a]|f|, max_[h,b]|f|), roots capped at modulus one, cannot move V off one by more than about 5e-7 at any degree 3 through 9, with the regular polygon as maximiser and the optimal hub slightly off the origin. Neither reported row is a bound and they err oppositely: a sampled objective under-reports a maximum, while scoring the winning hub with the EXACT segment maximum over-reports the inner minimum because the hub comes from a finite grid, so the 1.0000005438 seen at n = 3 is inner-search truncation and not a failing configuration. Per negative_results entry 19 this is reported with a NEGATIVE CONTROL and a MARGIN GAP rather than as a bare supremum: the same searcher at the same budget and the same degree breaks the weaker chord-or-origin disjunction at n = 3, 5, 6 (V = 1.0098, 1.0012, 1.0003), so the false disjunction fails by 9.7e-3 where the free-hub residual is 5.4e-7, four orders of magnitude apart; the n = 3 return is the exact witness recorded above. Random sampling is worthless here -- 4000 draws from six structured families gave zero failures of the disjunction the adversarial searcher broke immediately. The conjecture is unproved and the search is capped at degree nine.

Evidence/status: elementary_reduction_plus_exact_witness_plus_calibrated_search

- [TwoSegmentContainmentReduction.md](problem/TwoSegmentContainmentReduction.md)

### near_fekete_cusp_positivity_n3_proved

kappa_3 > 0 is now PROVED, closing the binding instance of the one inequality NearFeketeCuspLaw.md section 8 lists as measured rather than proved. Two ingredients. (1) At n = 3 the near-field model's descending branches are an EXPLICIT ALGEBRAIC GRAPH. A branch satisfies Im g = 2 identically, i.e. 3X^2 Y - Y^3 + 3Y = 2; since Y^3 - 3Y + 2 = (Y-1)^2 (Y+2) this solves as X(Y) = (1-Y) sqrt((Y+2)/(3Y)) for Y > 0, with branch 1 the arc Y: 1 -> 0 (exit direction 0) and branch 2 the arc Y: 1 -> infinity (exit direction 2pi/3), and X'(Y) = -(Y^2+Y+1)/(sqrt3 Y^{3/2} sqrt(Y+2)) < 0. Integrating on this graph reproduces the recorded constants to every quoted digit: ex_1 = 1.235094261, ex_2 = 0.1568844275, kappa_3 = 0.6080213112 against the recorded 0.6080213113, and D_1 = 0.2350942613, D_2 = 0.02290983128. Im g - 2 vanishes to 3.9e-38 over 400 sampled points. This is special to n = 3: Im(zeta^n) = const is not solvable for X over Y at higher degree. (2) The L^2 chord-deficit estimate the same file names as the missing tool ('a proof needs the hypotenuse, i.e. a genuine L^2 estimate on dY/dX'). In the exit-aligned frame eta = e^{-i alpha} zeta = P + iQ with P monotone, sqrt(dP^2+dQ^2) <= dP + dQ^2/(2 dP) and r >= P and P(start) = cos(gamma) give D <= (1/2) int (dQ)^2/dP; the integrand is tan^2(tau - alpha) dP, so this is exactly the L^2 turning estimate, and it keeps the hypotenuse the |dX|+|dY| split discards (that split returns 2.634 against the true 1.392). Closing at n=3: on branch 1 the integrand is sqrt3 Y^{3/2} sqrt(Y+2)/(Y^2+Y+1) <= 3Y^{3/2} on [0,1], so I_1 <= 6/5 and D_1 <= 3/5; on branch 2, dP/dY = (sqrt3 + |X'|)/2 >= sqrt3/2 and dQ/dY = (sqrt3|X'| - 1)/2 = N/(2 Y^{3/2} sqrt(Y+2)) with N = (3Y^2+2Y+1)/(Y^2+Y+1+sqrt(Y^4+2Y^3)) <= 3/2 for Y >= 1 (equivalent to the termwise-positive 12Y^3+5Y^2+2Y-1 >= 0), so with Y+2 >= 3, I_2 <= sqrt3/16 and D_2 <= sqrt3/32. Hence kappa_3 = (cos gamma_1 + cos gamma_2) - (D_1+D_2) >= sqrt3/2 - 3/5 - sqrt3/32 = 15 sqrt3/32 - 3/5 = 0.211898816 > 0, equivalently J_3 <= 3.576 < 4. So z^3 - mu is a STRICT local maximum of min_c L(c)/(2R) in the aligned direction, first order in rho, no longer a measurement. SCOPE, and it is narrow. Only the phi = 0 ray direction at n = 3 is covered: the model is zeta^n + n e^{i phi} zeta, and the rotation zeta -> e^{i phi/(n-1)} zeta that normalises it to zeta^n + n zeta leaves a global phase e^{i n phi/(n-1)} on g, which is the descent-ray angle, so phi survives. NearFeketeCuspLaw.md MEASURES phi = 0 as min_phi kappa_3 and n = 3 as the binding degree; both remain measurements, so what is proved is positivity at the measured-worst instance, not the near-Fekete half. Lemma 2 is degree-free and is the reusable piece; a general-n proof needs a bound on int tan^2(tau - alpha) dP for zeta^n + n zeta, where the target cos gamma_1 + cos gamma_2 grows from sqrt3/2 towards 2 while the measured D_1+D_2 peaks at 0.3395 at n = 5. The D-bounded-away-from-1 half is untouched. Erdos #1041 remains open.

Evidence/status: proved_binding_case_of_a_previously_measured_inequality

- [NearFeketeCuspPositivityProof.md](problem/NearFeketeCuspPositivityProof.md)

### visibility_overlap_reduction_to_a_one_root_statement

Erdos #1041 follows from a ONE-ROOT statement carrying no separate length obligation. LEMMA (proved, elementary): if Omega is compact connected, a_1..a_k in Omega with k>=2, and S_j = {h in Omega : some path in Omega from h to a_j has length <= 1}, then the S_j are closed (Arzela-Ascoli plus lower semicontinuity of length) and nonempty, so if they COVER Omega they cannot be pairwise disjoint -- a finite disjoint closed cover of a connected space is a clopen partition. Hence some h lies in two of them and two roots are joined in Omega by a path of length <= 2. REDUCTION (proved): for monic g with roots in the CLOSED unit disk write mu = min_c |g(c)|. Fekete gives prod_c |g(c)| = |disc|/n^n <= 1 so mu <= 1; every component of a sublevel set carries a root; components of {|g|<lambda} are simply connected so crossing a critical level can only MERGE; hence for every lambda in [mu,1] the component Omega_lambda of {|g|<=lambda} containing the minimising critical point is compact, connected and carries k>=2 roots. So the hypothesis (COVER) -- for SOME lambda in [mu,1], every point of Omega_lambda lies within intrinsic distance 1 of a root inside it -- yields a pair path of length <= 2 at level <= 1, and the minimum-enclosing-disk normalisation g(w)=R^{-n} f(z_c+Rw) converts that into length <= 2R < 2 inside {|f| < 1}. Both strict inequalities come from R < 1, not from the hypothesis. WHY IT MATTERS: eight independent eliminations on file (negative_results 5, 8, 9, 11, 14, 18, 26, 37) all exhibit 'at most one' good object -- one contained spoke, one safe arm, one safe radial -- and none exhibits zero. Each kills a mechanism needing TWO objects at once. (COVER) needs one, by any path, so none of them applies to it; and because the constant 2 is produced by the lemma from the constant 1, no residual length inequality survives, unlike the descent producer min_c L(c) <= 2R. SHARPNESS (proved, closed form): on g = z^n - r^n the only critical point is 0 with mu = r^n, every radial segment satisfies |g(t r w)| = r^n(1-t^n) <= mu, and dist(0, root) = r = mu^{1/n} exactly, so (COVER) holds with EQUALITY at every degree and the lemma returns exactly 2r. RIGIDITY (proved): min_k |h - z_k| <= |g(h)|^{1/n} always, since the geometric mean of the distances is |g(h)|^{1/n}, with equality iff every root is equidistant from h. So the equality stratum of (COVER) is exactly ONE-SPOKE: for w_1..w_n on the unit circle some j has prod_k |t w_j - w_k| <= 1 for all t in [0,1]. Summing over j is the radial product identity of TwoSegmentLevelIdentity.md 4b and gives 'for each t some j'; ONE-SPOKE needs 'some j for each t' and that exchange is not supplied. n=2 is elementary; n>=3 is open. MEASUREMENT: 38 configurations (extremal family, the 3-degrees-from-hexagon witness, the stored origin-spoke, minimal-cubic and balanced-quintic witnesses, 10 random, 12 near-Fekete) by multi-source Dijkstra over the first-merge component with a 16-neighbour stencil and interior-admission on every move. A grid path is a genuine path so the numbers are UPPER bounds and '<= 1' is sound. Worst sup dist = 1.01886, worst scale-free ratio sup dist / mu^{1/n} = 1.02325, worst resulting pair geodesic 2.00400 at z^2-0.999^2 whose closed form is 1.998 -- all inside the measured 1.2 per cent grid band, and the rows reading exactly 1.0000 are the extremal family where equality is proved. (COVER) is NOT proved and no adversarial search against it has run. GENERALISED FORM AND ITS MEASUREMENT: the lemma needs the covering only on a compact CONNECTED subset Gamma of Omega carrying two roots, with paths allowed to run in all of Omega -- the two roles are separate, Omega should be as large as possible and Gamma as small as possible, and Gamma = Omega is the crudest admissible choice. The cheapest Gamma is the pair of descending Newton branches from c*, an ARC rather than a region. On that Gamma the hypothesis was tested in the STRONGEST form the lemma can consume -- every point of the arc must see one of the two roots by a STRAIGHT segment inside {|f| <= 1} -- and over 26 scored configurations at 283 sampled points per arc there were ZERO points seeing neither root, at least 155 points per row seeing BOTH, and the largest |h-a|+|h-b| over all overlap points was 1.91208 against a budget of 2, so the length is met with room and is never imposed separately. Twelve rows are excluded and receipted: two below degree three and ten with a degenerate minimising hub, which the closed-form arm settles instead.

Evidence/status: proved_reduction_plus_proved_equality_case_plus_measured_hypothesis

- [check_erdos1041_visibility_overlap.py](problem/scripts/check_erdos1041_visibility_overlap.py)
- [VisibilityOverlapReduction.md](problem/VisibilityOverlapReduction.md)

### capacity_geodesic_conjecture_and_its_equality_family

Erdos #1041 follows from a SCALE-FREE length bound at the first-merge level, with no unit-disk hypothesis. Write K_t = {|f| <= t}; cap(K_t) = t^{1/n} (LemniscateCapacityBudget.md (B)). Conjecture (C): if a component of K_t holds two roots then two of them are joined INSIDE it by a path of length <= 2 t^{1/n} = 2 cap(K_t). PROVED here: (C) implies #1041, by applying it at t = mu and using only the classical Fekete chain mu <= R^n, since then the path has length <= 2 mu^{1/n} <= 2R < 2 and lies in K_mu subset {|f|<1}; the ratio geo/(2 t^{1/n}) is an AFFINE INVARIANT, so the disk is a normalisation and not a hypothesis; (C) is an EQUALITY for f = (z-tau)^n - lambda at every n >= 2 and every lambda != 0, hence for EVERY quadratic -- an equality on a two-parameter family at every degree, not in a limit, proved by the sector argument on Dbar(lambda,|lambda|) which lies in |arg(w/lambda)| <= pi/2; and at t = mu the two lobes meet only at c*, so geo splits as geo(a,c*) + geo(b,c*). (C) sits STRICTLY between what is refuted and the target: geo <= L(c*) always, so the STRONG completion L(c*) <= 2 mu^{1/n} that negative_results entry 28 refutes would imply (C), and (C) implies TrueGeodesicLab.md's radius bound geo <= 2 max|z_i|. Measured with paths pinned through c* (so no neck-cutting artefact) and audited for containment, the ratio is below 1 at every stored hard witness -- QC degree-6 0.8610866, QC degree-9 0.7529590, exact cubic 0.8523585, quintic 0.0826093, quartic 0.8970902 -- and 0.9999999935 on z^3-(99/100)^3, whose exact value 1 is Theorem 2. CONTAINMENT CAVEAT: the relaxation admits moves on finitely many samples per segment, so two rows leak above the level by 1.4e-9 (QC degree-6) and 9.3e-10 (QC degree-9) relative; such a path is not literally in K_mu and is admissible only because shrinking it back costs O(leak) in length against margins of 0.139 and 0.247. The receipt gates on that coupling (a row may audit above 1 only with margin >= 1e-3); the equality row and the two smallest-margin rows audit at exactly 1.0; in the near-Fekete shell it rises to 1 FROM BELOW at every degree. Every reported geodesic is the length of an explicitly audited contained path, hence an upper bound, so ratios below 1 are witnesses. Receipt scripts/check_erdos1041_capacity_geodesic.py; note CapacityGeodesicConjecture.md.

Evidence/status: proved_reduction_plus_proved_equality_case_plus_measured_hypothesis

- [check_erdos1041_visibility_overlap.py](problem/scripts/check_erdos1041_visibility_overlap.py)
- [VisibilityOverlapReduction.md](problem/VisibilityOverlapReduction.md)

### capacity_geodesic_margin_is_first_order_in_the_critical_radius

The near-Fekete cusp is a COORDINATE, not an obstruction, for the capacity-geodesic objective. HardRegimeIsNearFekete.md records that a perturbative attack at the extremum 'must handle a fractional-power response, which is a materially harder object than a Hessian'. Proposition 4 (CapacityGeodesicConjecture.md section 7): for f_eps = z^n - m + eps h, with rho_crit = (eps|h'(0)|/n)^{1/(n-1)} the radius of the critical (n-1)-gon of near_fekete_cusp_law_and_strict_local_maximality, the METRIC SLACK satisfies 2 rho - (d_a + d_b) = rho_crit (cos th_a + cos th_b) + O(rho_crit^2) >= 2 cos^2(pi/n) rho_crit (1+o(1)) > 0, because mu = m + O(eps), eps = (n/|h'(0)|) rho_crit^{n-1} = o(rho_crit) for n >= 3, and the merging pair brackets the hub direction so th_a + th_b = 2 pi / n. So the slack is FIRST ORDER in rho_crit with an explicit positive slope, and (C) near the extremal needs only that the geodesic deficit geo - (d_a+d_b) is o(rho_crit). Measured along a fixed perturbation direction over seven decades: the slope of log(1 - geo/(2 rho)) against log rho_crit is 0.9981, 0.9747, 0.9645, 1.0067 at n = 3,4,5,6 (predicted 1), against log eps it is 0.4989, 0.3248, 0.2412, 0.2021 (predicted 1/(n-1) = 0.5, 0.3333, 0.25, 0.2), and the constant (1-ratio)/rho_crit lands inside the predicted band [cos^2(pi/n), cos(pi/n)] at every degree. Eliminating eps through the smooth Fekete maximum (1 - D ~ eps^2) gives the intrinsic form 1 - geo/(2 mu^{1/n}) ~ (1-D)^{1/(2(n-1))} -- the quantitative Fekete-stability object exact_results::quantitative_fekete_stability_hadamard_defect names, with the exponent attached.

Evidence/status: proved_reduction_plus_proved_equality_case_plus_measured_hypothesis

- [check_erdos1041_visibility_overlap.py](problem/scripts/check_erdos1041_visibility_overlap.py)
- [VisibilityOverlapReduction.md](problem/VisibilityOverlapReduction.md)

### radial_resultant_sweep_identity

For monic f with roots a_k, f* the reciprocal adjoint and ahat_j = a_j/|a_j|, -log|f*(z)| = sum_{m>=1}(1/m)Re(conj(p_m) z^m) gives sum_j -log|f*(t ahat_j)| = sum_{m>=1}(t^m/m)Re(conj(p_m) sigma_m) with sigma_m = sum_j ahat_j^m. If all |a_k| = r then p_m = r^m sigma_m and the right side is sum_{m>=1}((tr)^m/m)|sigma_m|^2 >= 0, so prod_j |f*(t ahat_j)| = exp(-sum_m ((tr)^m/m)|sigma_m|^2) <= 1, decreasing in t on [0,1/r). At t = r this is exactly reciprocal_adjoint_resultant_power_sum_identity (Theorem RS): the identity above is the whole radial sweep, not only its endpoint. Paired with the Blaschke majorant |f| <= |f*| on the closed disk and the harmonicity of log|f*| there, it gives: at EVERY radius t at least one root direction has |f(t ahat_j)| <= 1, with an explicit deficit. This is an L^1-in-t statement and the good index moves with t; the L^infinity upgrade is Form A', which negative_results 8/16 refute. Checked to 2.1e-13 over 72 (degree, radius, radial point) triples in degrees 2-9 with tail-bounded truncation. See RadialResultantSweep.md.

Evidence/status: ordinary_proof_plus_numerical_verification_novelty_not_claimed


### near_fekete_origin_spoke_balance_and_kernel

For a_k = omega^k(1+e_k), log|f(z)| = log|1-z^n| + Re Lambda(z) + O(eta^2) with Lambda(z) = sum_k e_k/(1 - z omega^{-k}), and the EXACT balance identity sum_j Lambda(t omega^j) = n Lambda(0)/(1-t^n): every harmonic m not divisible by n cancels across the n spokes. For a pure angular perturbation theta the functional is explicit: log|f(t omega^j)| - log(1-t^n) = P_j(t) + O(eta^2) with P_j(t) = sum_{l=1}^{floor((n-1)/2)} (theta_{j+l} - theta_{j-l}) g_l(t) and g_l(t) = t sin(2 pi l/n)/(1 - 2 t cos(2 pi l/n) + t^2) > 0 -- positive conjugate-Poisson kernels acting only on the ANTISYMMETRIC part of theta about j, with sum_j P_j == 0. Consequences: a perturbation symmetric about root j leaves that spoke exactly contained; the entry radius tau_j is the largest root of P_j(t) = -log(1-t^n); and on the leading harmonic tau_j = (cos psi_j)_+^{1/(n-1)}, psi = arg Ehat_1, a FRACTIONAL power of the perturbation, which is why the recorded entry radii are small. Verified: balance to 1.2e-13, expansion residual O(eta^2) (shrink 101.0 and 100.1 per decade), tau ratio 0.99847 at eta = 1e-5. See RadialResultantSweep.md.

Evidence/status: ordinary_first_order_proof_plus_numerical_verification


### form_a_cut_cusp_exponent_at_the_regular_gon

Rescaling z = s zeta with s^{n-1} = |Ehat_1| gives the eta-free, R-free near-field model of the ORIGIN-SPOKE route: W(zeta) = Re(e^{i psi} zeta) - Re(zeta^n) = Re H, harmonic, with W(0) = 0 so the good set is a half plane near the origin -- which is why the Form A-cut chord works at leading order (a linear function attains its maximum on a segment at an endpoint). At n = 3, psi = pi/3 the model is EXACTLY CRITICAL: the only admissible pair has chord maximum g(s) = s^3/8 - s/4 + 1/(8s), g'(s) = 0 iff 3s^4 - 2s^2 - 1 = 0 iff s = 1, and g(1) = 0 exactly, attained where both harmonics vanish separately. Degree three is the ONLY such degree: the number of fully good rays is the number of n-th roots of unity in a closed half plane, at least floor(n/2), which is >= 2 exactly when n >= 4, and two good rays make the whole staple strictly negative for small s. Measured consequence: the regular n-gon on the unit circle is a STRICT local maximum of the Form A-cut objective V with value exactly 1, and 1 - V ~ c_n eps^{n/(n-1)} -- median exponent 1.504 against 3/2 at n = 3 and 1.333 against 4/3 at n = 4 over nine directions each, none with V > 1. The exponent is below 2, so V has infinite second derivative there: a cusp, and no Hessian argument applies. This explains the 1.0000000 pin that TruncatedSpokeReduction.md sec 6 and TwoSegmentContainmentReduction.md sec 5 both record without an explanation. c_n is not proved positive. See RadialResultantSweep.md.

Evidence/status: near_field_model_proved_at_n3_plus_measured_exponent_not_proved


### bergman_segment_length_bound_and_capacity_window

AffineNormalisedModuli.md section 7 names 'a sharp replacement for the Koebe constants in Theorem R' as the object that would change the picture. Koebe is the wrong estimate: by Theorem B the descent arc is the image of a DIAMETER under the Riemann map psi : D -> Omega_t, and Area(Omega_t) = ||psi'||^2 in the Bergman space A^2(D), so length is an L^1 integral of psi' along a fixed curve and the sharp tool is the reproducing kernel. LEMMA A: for h in A^2(D) and 0 < q < 1, (int_{-q}^{q}|h| ds)^2 <= Lambda(q) ||h||^2 with Lambda(q) = int int ds ds'/(pi(1-s s')^2) = (2/pi) log((1+q^2)/(1-q^2)); the proof is Cauchy-Schwarz against Phi_u = int u(s) K_s ds plus POSITIVITY of the Bergman kernel on the real segment, which makes u = 1 optimal. Equality holds for h(z) = (1-q^2 z^2)^{-1}, whose primitive log((1+qz)/(1-qz))/(2q) is UNIVALENT, so 2/pi is sharp among conformal maps and not an artifact of the larger class. LEMMA B: the same estimate for an arbitrary curve gives length(Gamma) <= (1/2) len_hyp(Gamma) sqrt(Area(Omega)/pi) in any simply connected Omega. OBSERVATION: Theorem B never uses minimality of mu -- Riemann-Hurwitz gives chi = 1 = 2 - b, so a two-root component has exactly one branch point, which must be the hub -- so the machinery runs at EVERY Fekete-admissible hub, which is what admissible_branch_length_reformulation calls load-bearing. THEOREM C: if the component Omega of {|f| < t} at a critical point c with v = |f(c)| holds exactly two roots, then L(c) <= sqrt((2 Area(Omega)/pi) log((t+v)/(t-v))) <= t^{1/n} sqrt(2 log((t+v)/(t-v))). COROLLARY D fires at v/t < tanh(1) = 0.7615942 against Corollary R's v/t < tanh^2(1/8) = 0.0154637, a factor of 49.25 in the admissible level ratio before the true area replaces the Polya cap. The hypothesis is non-empty exactly when mu < R^n, i.e. when D < 1, so this is a quantitative form of HardRegimeIsNearFekete.md's split in which the room is spent against AREA rather than against the level ratio alone. THEOREM E: the binding case of Conjecture (C) of CapacityGeodesicConjecture.md is a component holding exactly two roots -- at the level where a component first holds two roots, two one-root lobes merge -- so Theorem C proves (C) whenever t >= coth(1) v = 1.3130353 v, confining the whole content of (C) to the level window [v, coth(1) v), a relative width of 31.3 percent. That window is DEGREE-FREE, because t^{1/n} cancels on both sides; every route through mu <= D^{1/(n-1)} instead gives a window that closes as n grows. CALIBRATION: on the quadratic equality family z^2 - d^2, where L = 2R exactly, Area = 2 t E(m = 1/t^2) with E the complete elliptic integral of the second kind, and (2 Area/pi) log((t+1)/(t-1)) = 4(1 + 1/(12 t^2) + O(t^-4)), so the bound is 2 sqrt(1 + 1/(12t^2)): strictly above the truth at every finite level and converging to it, verified at 40 digits with Richardson coefficient 0.08333333 against 1/12; float64 loses five digits to cancellation there. MEASURED, same hypothesis set: 104 of 108 configurations settled against Theorem R's 30, 74 settled only here and 0 lost, worst L/bound 0.981 over 1085 admissible (hub, level) pairs, and still firing at mu = 0.9998 on the near-Fekete shell with the reach improving as the degree rises. A NEW INSTRUMENT-DEFECT CLASS MEMBER: a grid's ROOT count of a sublevel component is not a safe witness for the two-root hypothesis, since the necks go sub-grid, while its CRITICAL-POINT count is, because Riemann-Hurwitz makes them the same statement; nine of eleven first-run violations read two roots while holding two critical points. Areas are now bracketed by erosion/dilation and calibrated against the closed-form Cassini area. Silent by construction on z^n - r^n, where every level above mu gives a component holding all n roots.

Evidence/status: proved_sharp_lemma_plus_proved_theorem_plus_measured_reach

- [check_erdos1041_bergman_segment_bound.py](problem/scripts/check_erdos1041_bergman_segment_bound.py)
- [BergmanSegmentLengthBound.md](problem/BergmanSegmentLengthBound.md)

### bergman_geodesic_moebius_invariance

BergmanSegmentLengthBound.md section 3 names the missing object for a k-root component: 'prod_j rho(zeta_c,zeta_j) = |f(c)|/t bounds the SMALLEST pseudohyperbolic distance and says nothing about the second'. Two identities close that. (1) The Bergman segment functional Lambda(gamma) = int int |dz||dz'|/(pi|1-conj(z')z|^2) is MOEBIUS INVARIANT, because |1-conj(sigma(z'))sigma(z)|^2 = |sigma'(z)||sigma'(z')||1-conj(z')z|^2 exactly. Hence Lemma A's closed form is not about segments: for the hyperbolic geodesic between two points at pseudohyperbolic distance rho, Lambda = (1/pi)log(1/(1-rho^2)). THEOREM C': for ANY simply connected Omega of finite area and a,b in Omega, the hyperbolic geodesic satisfies length^2 <= (Area(Omega)/pi) log(1/(1-rho_Omega(a,b)^2)); SHARP, attained on Omega = psi_q(D), psi_q = (1/2q)log((1+qz)/(1-qz)), a,b = psi_q(-+q), verified to 3e-7. Theorem C is the k=2 case VERBATIM (antipodality gives 1-rho^2 = ((t-v)/(t+v))^2) and its coth(1) threshold is recovered exactly. (2) LEMMA G: for a component Omega of {|f|<t} with roots a_1..a_k, sum_j g_Omega(z,a_j) = log(t/|f(z)|) exactly; expanding at a simple root gives the ROOT-CENTRED product identity prod_{j!=i} rho_Omega(a_i,a_j) = r_Omega(a_i)|f'(a_i)|/t =: P_i < 1, so min_{j!=i} rho_Omega(a_i,a_j) <= P_i^{1/(k-1)} -- a bound between two ROOTS, not from the hub. Theorem F, Corollary F' and Theorem E' follow, reducing to Theorem E at k=2. A Gram/Bessel inequality Area(Omega) >= pi c* G^{-1} c with |G_ij| = 1-rho_ij^2 sharpens the conformal-radius bound to r_Omega(a_i) <= sqrt(Area(1+S)/(pi k)), S = max_i sum_{j!=i}(1-rho_ij^2): on z^6-0.9^6 at t=1 that is 0.4235 against the exact 0.2648, where sqrt(Area/pi) gives 0.9776. SUBDOMAIN PRINCIPLE: Theorem C' has no hypothesis tying Omega to f, so any simply connected subdomain of {|f|<1} carrying two roots is admissible; the canonical choice is the union of two adjacent NEWTON BASINS. PROPOSITION S: on z^n-r^n the uniformiser Phi(z)^n = sigma(z^n) is rotation-equivariant and carries that subdomain onto the DISC SECTOR {|zeta|<1, arg in (-pi/n,3pi/n)} with the roots at R_0, R_0 omega, R_0 = r t^{-1/n}; so Area = (2/n)Area(Omega_t) EXACTLY and rho is elementary. Expanding, 1-rho^2 = (32a^2/(a^2-1)^2) eps^2 with a = cot^2(pi/8) = 3+2sqrt2 and 32a^2 = 544+384sqrt2 = (a^2-1)^2, so the constant is exactly 1 and 1-r_max(n) = Theta(n^{-1}e^{-2n}). MEASURED CUT-OFFS (mpmath, 50 digits): 1-r_max = 1.7e-2, 1.2e-3, 1.1e-4, 1.1e-5, 1.4e-7, 1.7e-8, 2.1e-9, 3.2e-11, 8.8e-15 at n = 3,4,5,6,8,9,10,12,16, successive ratios converging to e^2. This matters because Theorem C is SILENT BY CONSTRUCTION on z^n - r^n (no level ever gives a two-root component, BergmanSegmentLengthBound.md section 6), so the degenerate stratum has a non-empty criterion for the first time; the criterion is open in the roots so each firing row settles a neighbourhood, whose size is NOT quantified here. On the recorded hard witnesses Theorem F is VACUOUS (P_i >= 1 at every tested level) except the degree-5 origin-spoke lab (bound 0.061 at t=0.30). Erdos #1041 remains open; nothing here reaches the near-Fekete shell.

Evidence/status: ordinary_complete_proof_plus_exact_closed_forms_not_lean_checked_novelty_not_claimed

- [BergmanGeodesicInvariance.md](problem/BergmanGeodesicInvariance.md)
- [check_erdos1041_bergman_geodesic.py](problem/scripts/check_erdos1041_bergman_geodesic.py)

### form_a_cut_adjacent_good_pair_selector

TruncatedSpokeReduction.md proves Form A-cut -- three segments, NO length obligation -- and leaves the SELECTION open; form_a_cut_cusp_exponent_at_the_regular_gon records that its cusp constant c_n is not proved positive. The selector is now identified and proved sufficient AT LEADING ORDER for n >= 4. With a_k = omega^k(1+e_k), E_1 = sum_k e_k omega^{-k}, the near field is log|f(z)| = Re E_0 + Re(E_1 z) - Re(z^n) + R with CHECKED error orders: at sigma ~ eta^{1/(n-1)} both leading terms are ~eta^{n/(n-1)} while eta sigma^2, eta^2 and sigma^{2n} are strictly higher order for n >= 3 (n/(n-1) <= 2), so the model is asymptotically exact rather than formal. A root carries a GOOD RAY iff p_j := Re(E_1 a^_j) <= 0 -- a CLOSED half plane -- and then its entry radius is zero (Lemma 1). The good set is therefore a contiguous arc of at least floor(n/2) directions and contains two ADJACENT indices exactly when n >= 4 (Lemma 2); the recorded slope identity P_j'(0) = Re(E_1 omega^j) is the same statement. On the common-radius chord w(tau) = (1-tau)a^_i + tau a^_j the only positive term is -sigma^n Re(w^n), so the pair works for small sigma iff Re(w(tau)^n) < 0 implies (1-tau)p_i + tau p_j < 0. Along an ADJACENT chord arg(w^n) turns exactly once, so Re(w^n) < 0 only strictly inside (0,1), where the interpolant is strictly negative unless both directions lie on the line Re(E_1 zeta) = 0 -- impossible for adjacent directions at n >= 3. Hence EVERY adjacent good pair satisfies the criterion automatically (Lemma 3), and the two-dimensional free hub search is not needed near Fekete. n = 3 is exactly the degree where Lemma 2 gives one good ray, and is settled separately by CubicCriticalHub.md. REFUTED RIVAL: the rule one would guess first -- take the MOST ANTIPODAL good pair so the chord dips near the origin -- is FALSE at 45/48, failing by 1.0287764761 at n=10 eta=1e-1, 1.0003866137 at n=8 eta=1e-2 and 1.0000002022 at n=10 eta=1e-5, the last arbitrarily close to the regular polygon; the extreme rays of the good arc are the most marginal ones. MEASURED with EXACT segment maxima (real roots of d|f|^2/dt): the adjacent selector succeeds 70/70 on one seed stream over n=4..12 and eta=1e-1..1e-7, angular and mixed, and reproduces the free two-dimensional optimum to nine printed digits at 57 of the 70 rows. A second stream locates its boundary: at n=12 angular it crosses one between eta = 0.02 and 0.03 (1.002637 at 0.03, 0.999793 at 0.02) while the free optimum there is still 0.79, so the SELECTOR and not Form A-cut is what is near-Fekete-only. INSTRUMENT: a sampled 3001-point segment maximum reported 70/70 for the ANTIPODAL rule as well and missed the n=12 crossing -- negative_results entry 34's class at a fifth location; every number in the note is exact. SCOPE: the Proposition is leading order, has no explicit threshold eta_0(n), carries the modulus part of the perturbation only through the angular kernel identity, and does NOT prove c_n > 0. Erdos #1041 remains open.

Evidence/status: leading_order_proof_plus_refuted_rival_selector_plus_exact_measurement_not_lean_checked

- [FormACutAdjacentSelector.md](problem/FormACutAdjacentSelector.md)
- [check_erdos1041_form_a_cut_selector.py](problem/scripts/check_erdos1041_form_a_cut_selector.py)

### exact_component_capacity_green_defect

LemniscateCapacityBudget.md (D) and every consumer of Polya spend the INEQUALITY cap(C) <= cap(K_t) = t^{1/n} for a connected component C of {|f| < t}. The exact value is available. With Omega = Chat minus closure(C), n log cap(closure C) = log t - Sigma, where Sigma = sum over the roots z_j OUTSIDE C, with multiplicity, of g_Omega(z_j, infinity); equivalently cap(closure C) = t^{1/n} exp(-Sigma/n) with Sigma >= 0. Proof: no root lies on dC since roots have |f| = 0 != t; u(z) = log(|f|/t) + sum_{z_j not in C} g_Omega(z, z_j) has its root singularities cancel, is harmonic on Omega minus infinity, vanishes on dC and grows like n log|z| - log t + Sigma; subtracting n g_Omega(., infinity) leaves a bounded harmonic function vanishing on the boundary, hence zero, and reading it at infinity gives the identity. Sigma = 0 exactly when C holds every root, i.e. when {|f| < t} is connected, recovering cap(K_t) = t^{1/n}. CONSEQUENCE, with kappa := cap(Omega_t)/t^{1/n} = exp(-Sigma/n) and Area <= pi cap^2: Theorem C of BergmanSegmentLengthBound.md becomes L(c) <= kappa t^{1/n} sqrt(2 log((t+v)/(t-v))), so its Theorem E window narrows from relative width coth(1)-1 = 31.30% to coth(1/kappa^2)-1, and Corollary D's Erdos-1041 threshold moves from tanh(1) to tanh(1/kappa^2). This strictly dominates that file's Cassini area bound, which is capacity monotonicity applied to an oval CONTAINING Omega_t. MEASURED at a calibrated resolution (equilibrium-measure solver, worst known-capacity error 1.21e-4; identity residual 1.45e-4 against tolerance 1.21e-3; Sigma = 0 reproduces t^{1/n} to 7.24e-5): over 12 first-merge two-root components kappa has median 0.3891 and max 0.5811, giving windows of median 0.0006% and worst 0.5370%. LOAD-BEARING DISCLOSURE: every surviving measured row is a BULK configuration. The near-Fekete seeds produced no rows, so the corollary is UNMEASURED on the shell where the difficulty lives, and it is provably EMPTY on the extremal family z^n - lambda, where {|f| < t} is connected for t > v, so Sigma = 0 and kappa = 1. Erdos #1041 and conjecture (C) remain open.

Evidence/status: ordinary_complete_proof_plus_calibrated_measurement_not_lean_checked_novelty_not_claimed

- [ComponentCapacityFormula.md](problem/ComponentCapacityFormula.md)
- [check_erdos1041_component_capacity.py](problem/scripts/check_erdos1041_component_capacity.py)

### sharp_collinear_root_diameter_extremal

For n >= 2, put r_n = cos(pi/(2n)) and C_n = 1/(2^(n-1) r_n^n). Every monic degree-n polynomial whose zeros are collinear and have diameter D has an adjacent-root chord of length at most D on which |f| <= C_n (D/2)^n. Equivalently, the supremum over monic real-rooted degree-n polynomials of root diameter D of the minimum real critical-gap height is exactly C_n (D/2)^n. The endpoint-normalized scaled Chebyshev polynomial attains equality in every gap, so the constant is sharp. The proof normalizes the extreme roots to -1 and 1 and compares with q_*(x)=T_n(r_n x)/(2^(n-1)r_n^n). If every gap peak of q exceeded C_n, q-q_* would have the two endpoint zeros and one zero between every consecutive pair of alternating peaks: n distinct zeros despite degree at most n-1. This solves the all-degree collinear-root subcase of Erdos #1041 for the open unit disk, and also the closed-disk collinear case for n >= 3; degree two at roots -1,1 is the exact boundary obstruction. The ordinary proof covers the compactness choice of gap maxima, affine complex-to-real normalization, and Chebyshev equality configuration. Lean checks the load-bearing root-counting alternation theorem and the complete endpoint-normalized Chebyshev upper-bound adapter. Deterministic stress covered 20000 configurations per degree for n=2,...,10, 180000 total, with exact equality ratio one for the scaled Chebyshev family. No literature-priority claim is made.

Evidence/status: ordinary_complete_sharp_all_degree_subcase_proof_plus_lean_checked_alternation_and_chebyshev_adapter_novelty_not_claimed

- [check_erdos1041_collinear_chebyshev.py](problem/scripts/check_erdos1041_collinear_chebyshev.py)
- [CollinearRootCase.md](problem/CollinearRootCase.md)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SharpCollinearAlternation.exists_peak_le_of_monic_comparison, ErdosProblems.Erdos1041.SharpCollinearChebyshev.monicScaledChebyshev_isMonicOfDegree, ErdosProblems.Erdos1041.SharpCollinearChebyshev.eval_monicScaledChebyshev_neg_one, ErdosProblems.Erdos1041.SharpCollinearChebyshev.eval_monicScaledChebyshev_one, ErdosProblems.Erdos1041.SharpCollinearChebyshev.abs_eval_monicScaledChebyshev_le, ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound.

### unconditional_constant_factor_pair_geodesic

Let f be monic of degree n >= 2, let mu be the least critical-value modulus, and put rho = mu^(1/n). Zeros are listed with multiplicity. Two zero occurrences are joined by a possibly degenerate path of length at most (71/10)rho inside K_(2mu); when f is squarefree their zero locations are distinct. The proof is degree-free and uses the componentwise estimate H^1(partial C)^2 <= 2 pi k sigma A'(sigma), a regular-level mean-value choice above mu, the singleton boundary specialization sum_i mu^2/|f'(a_i)|^2<=rho^2 of the stronger fixed-level LC2 theorem, Koebe control on one-root lobes, and a cyclic boundary hop. At lambda=2 and r=3/20, exact rational bounds on the elementary constants give coefficient 66517563/9392500<71/10. The existing Python receipt is finite regression only. The sharp length-2 statement in the open unit lemniscate, containment at K_mu, and Conjecture P remain open.

Evidence/status: ordinary_complete_unconditional_proof_plus_finite_regression_not_lean_checked_not_independently_reviewed

- [UnconditionalConstantFactorBound.md](problem/UnconditionalConstantFactorBound.md)
- [check_erdos1041_constant_factor_bound.py](problem/scripts/check_erdos1041_constant_factor_bound.py)

### low_critical_high_arity_first_merge_closure

Let f be monic with all roots in the open unit disk, let mu be its least critical-value modulus, and let k be the number of roots in a minimizing first-merge component. Each of the following conditions implies that two distinct roots are joined by a path of length strictly less than 2 inside {|f|<1}: (i) mu<=1/2 and k>=17; (ii) mu<=1/4 and k>=12; (iii) mu<=1/8 and k>=10. The LC2-improved boundary-hop assembly uses respectively (lambda,r)=(2,13/100),(4,3/25),(8,11/100). Since lambda*mu<=1, multiplication by rho=mu^(1/n) cancels the high-level lambda^(1/n) factor. Exact rational certificates bound the three squared brackets strictly below 34, 24, and 20, so multiplication by 2/k puts each squared path length below 4. The regular working level can be chosen below 1 even at lambda*mu=1, giving strict containment.

Evidence/status: ordinary_complete_target_regime_proof_with_exact_rational_certificate_not_lean_checked_not_independently_reviewed

Superseded by **['low_critical_potential_closure_all_degrees_2026_09_05']**. Use that stronger result.

- [UnconditionalConstantFactorBound.md](problem/UnconditionalConstantFactorBound.md)
- [check_erdos1041_constant_factor_bound.py](problem/scripts/check_erdos1041_constant_factor_bound.py)

### low_critical_component_capacity_defect_closure

Let f be monic with all roots in the open unit disk, let mu<=1/2 be its least critical-value modulus, let C be the component of {|f|<2mu} containing a minimizing critical point, and put kappa=cap(closure C)/(2mu)^(1/n). If kappa<=1/3, two distinct roots are joined by a path of length strictly less than 2 inside {|f|<1}. The exact component-capacity formula multiplies the boundary and high-lift terms in the LC2-improved boundary-hop construction by kappa. Taking lambda=2 and r=1/20 gives coefficient at most 6518353/3285100=2-51847/3285100. Equivalently, the exterior Green defect sum Sigma at the roots excluded from C closes the target whenever Sigma>=n log 3.

Evidence/status: ordinary_complete_target_regime_proof_with_exact_rational_certificate_not_lean_checked_not_independently_reviewed

Superseded by **['low_critical_potential_closure_all_degrees_2026_09_05']**. Use that stronger result.

- [UnconditionalConstantFactorBound.md](problem/UnconditionalConstantFactorBound.md)
- [check_erdos1041_constant_factor_bound.py](problem/scripts/check_erdos1041_constant_factor_bound.py)

### low_critical_arity_capacity_lattice_closure

Let f be monic with all roots in the open unit disk, let k0 be the arity of a minimizing first-merge component, and let kappa be the normalized capacity of its containing lambda*mu-component. Retaining both the outer sqrt(2/k) factor and component capacity in the LC2-improved boundary-hop construction gives length<sqrt(2/k0)(A_lambda+B_lambda kappa). At mu<=1/2, (A_2,B_2)=(283/3610,52029/9100), with exact rational cutoffs for k0=2,...,16 equal to 1/3,2/5,12/25,1/2,7/12,16/25,2/3,7/10,3/4,4/5,5/6,7/8,9/10,33/35,39/40. At mu<=1/4, (A_4,B_4)=(849/3872,11975/2632), with cutoffs for k0=2,...,11 equal to 19/50,12/25,4/7,16/25,7/10,3/4,4/5,7/8,14/15,49/50. At mu<=1/8, (A_8,B_8)=(3113/15842,13427/3150), with cutoffs for k0=2,...,9 equal to 2/5,1/2,3/5,2/3,3/4,4/5,8/9,18/19. At mu<=1/64, lambda=64 and r=3/32 give sharpened exact cutoffs for k0=2,...,9 equal to 4/9,5/9,16/25,8/11,4/5,13/15,13/14,99/100, while every k0>=10 closes without a capacity defect. Every row is certified by an exact integer inequality (A_lambda+B_lambda*q_k)^2<2k.

Evidence/status: ordinary_complete_target_regime_proof_with_exact_rational_table_certificate_not_lean_checked_not_independently_reviewed

Superseded by **['low_critical_potential_closure_all_degrees_2026_09_05']**. Use that stronger result.

- [UnconditionalConstantFactorBound.md](problem/UnconditionalConstantFactorBound.md)
- [check_erdos1041_constant_factor_bound.py](problem/scripts/check_erdos1041_constant_factor_bound.py)

### capacity_saturation_radial_merge_bridge

Let U be a proper regular k-root component of {|f|<t} for a monic degree-n polynomial, let m=n-k, let B be its exterior degree-m finite Blaschke product, and put p=|B(0)|=cap(closure U)^n/t. If r is the largest modulus of a zero of B, define M_n(r)=max_(1<=x<=1/r) x^n(1-rx)/(x-r). Then an actual exterior radial curve joins U to an excluded root inside {|f|<=t M_n(r)}, so the next component merger satisfies b_next/t<=M_n(r)<=M_n(p^(1/m))<=p^(-(n-1)/m). The proof uses the exact spectator contraction |x-a|^2-|1-conj(a)x|^2=(x^2-1)(1-|a|^2)>=0 and monotonicity of M_n. Separately, the antipodal-fibre identity gives the exact saturation bound sum_j(n-|B'(zeta_j)|)<=n^2 Delta/(1+n Delta/m), Delta=(1-p)/(1+p)-m/n. Composing the source-current mu<=1/64,k0=9 cutoff q=99/100 with p<9/(2n-9) closes every proper top cell in degrees 10<=n<=459, strengthening the returned older degree-band computation. In the symmetric model B_s=(z^m-s)/(1-sz^m), the exact critical equation is y^2-[((n+m)s^2+(n-m))/(ns)]y+1=0 and the merge-height cusp has leading coefficient (sqrt(2)/3)(n^2-m^2)/(sqrt(n)m^(3/2)) epsilon^(3/2).

Evidence/status: ordinary_exact_multi_exterior_merge_ceiling_with_exact_integer_band_composition_symmetric_envelope_now_proved_in_sharp_symmetric_merge_envelope_and_exact_fibre_defect

Superseded by **['sharp_symmetric_merge_envelope_and_exact_fibre_defect']**. Use that stronger result.

- [CapacitySaturationBridge.md](problem/CapacitySaturationBridge.md)
- [check_erdos1041_capacity_saturation_bridge.py](problem/scripts/check_erdos1041_capacity_saturation_bridge.py)

### concyclic_alternation_theorem

Erdos #1041 is settled unconditionally for every monic f whose zeros lie on a CIRCLE of radius rho <= 2^{-1/n} (and, with no radius hypothesis, at n = 2). This is the circle companion of the collinear theorem of CollinearRootCase.md and uses the same mechanism in the only other chart where it exists. THEOREM C: let w_1..w_n be distinct on the unit circle, g = prod (z - w_k), A_1..A_n the open gap arcs, and q(z) = z^n - c with c = (-1)^{n+1} prod_k w_k. Then some gap satisfies |g| <= |q| pointwise on A_k. MECHANISM: a polynomial with zeros on a circle is self-inversive, so R[p](psi) = (-i)^n e^{-i(n psi + Phi)/2} p(e^{i psi}) is REAL for p = g and for every monic p in the same self-inversive class; and every monic member of that class has the SAME CONSTANT TERM as g, so g - q vanishes at 0 and has degree <= n-1, leaving at most n-2 zeros on the circle. If |g| > |q| somewhere in every gap, the sign of R[g-q] alternates across the n gaps and (using R[p](psi+2pi) = (-1)^n R[p](psi) to close the cycle) g - q acquires n distinct circle zeros. Contradiction. CONSEQUENCES on that same gap: max_{A_k}|g| <= 2, sharp at every degree since g = z^n - c gives exactly 2 on every gap; and A_k contains no zero of q, whose zeros are spaced 2pi/n, so its angular width is <= 2pi/n and |w_{k+1}-w_k| <= 2 sin(pi/n). LEMMA S (chord domination): u = log|g| is harmonic inside the disk, and on the open chord [w_k,w_{k+1}] the normal derivative towards the gap arc is sum_{j not in {k,k+1}} <z-w_j,N>/|z-w_j|^2 > 0, because a chord separates the two arcs and all other zeros lie on the far side; the two endpoint terms drop out since z - w_k and z - w_{k+1} are parallel to the chord. Hence max over the chord is never attained inside the circular segment, so max_chord |g| <= max_{A_k} |g|, strictly for n >= 3. That converts an arc statement, whose length rho*delta carries no bound, into a STRAIGHT SEGMENT of length <= 2 rho sin(pi/n) < 2 -- the length obligation of #1041 is discharged for free. COROLLARY: monic f, zeros on a circle of radius rho with 2 rho^n <= 1, gives two zeros joined by a segment of length <= 2 rho sin(pi/n) < 2 on which |f| < 1. New content begins at degree five (degrees 2,3,4 are already settled): admissible radii 0.8706, 0.8909, 0.9057, 0.9170 at n = 5,6,7,8, rising to 0.9659 at n = 20. SCOPE, load-bearing: the equality family of Theorem C is z^n - c, which is exactly this problem's own extremal family, so this route provably cannot reach rho -> 1 -- min over monic admissible q of max_{|z|=1}|q| IS 2 (sum R[q] over the n points where its top harmonic is +2: every lower harmonic cancels), and on the regular n-gon the chord maximum is rho^n(1+cos^n(pi/n)) > rho^n. On z^n - rho^n the components of {|f|<1} are n petals meeting only at the centre and the unique shortest admissible path is the radius pair of length exactly 2 rho, which is the near-Fekete cusp of near_fekete_cusp_law_and_strict_local_maximality and is untouched here. CALIBRATION: exact Gaussian-rational arm verifies the self-inversive coefficient identity b_j = (-1)^n W conj(b_{n-j}), that q lies in the same class with q(0) = g(0), that g-q has zero constant term, and both inequalities at exact points, at n = 4,5,6,7 in Fraction arithmetic. Float arm sweeps random, near-regular (perturbation 1e-1..1e-6) and two-cluster configurations at n = 2..12 with maxima located as polynomial roots and EVALUATED in the stable product form -- the degree-2n Laurent locator cancels catastrophically for clustered zeros and under-reports by up to 1e-8 relative, the direction that flatters containment, which is negative_results entries 24/34/41/44's class reproduced at a new location. Negative control per negative_results entry 19: the same searcher at the same budget pushes the neighbouring FALSE statement 'every gap arc has max|g| <= 2' over its threshold at every degree tested. CONJECTURE, calibrated not proved: the sharp CHORD constant is 1 + cos^n(pi/n), attained exactly at the regular n-gon; adversarial hill climbing converges to 1.124999, 1.249999, 1.346566 at n = 3,4,5 against 1.125, 1.25, 1.3465678 from several seedings. Granting it moves the admissible radius to (1+cos^n(pi/n))^{-1/n}, about 0.94 at every degree, still not to 1.

Evidence/status: ordinary_complete_sharp_proof_plus_exact_rational_witness_plus_calibrated_conjecture_not_lean_checked

- [ConcyclicAlternation.md](problem/ConcyclicAlternation.md)
- [check_erdos1041_concyclic_alternation.py](problem/scripts/check_erdos1041_concyclic_alternation.py)

### minimal_hub_window_join_inside_mu

If the minimising critical point c* of a squarefree monic f is simple and T* in (mu, +inf] is the two-root persistence level of its component (component root-counts jump only at critical-value moduli, so T* >= nu_2), then two roots are joined by a path INSIDE {|f| <= mu} -- the containment the constant-factor theorem reaches only at 2mu -- of length L <= inf_{mu<t<T*} t^{1/n} sqrt(2 log((t+mu)/(t-mu))) = T*^{1/n} sqrt(2 log((T*+mu)/(T*-mu))), with Psi_n(x) = x^{1/n} sqrt(2 log((x+1)/(x-1))) strictly decreasing via x = coth u (Psi^2 = 4u coth(u)^{2/n}); for n = 2 the limit is exactly 2 mu^{1/n}, optimal on the full quadratic equality family. Corollary: if T*/mu >= coth(1) the constant is <= sqrt(2) coth(1)^{1/n} mu^{1/n} <= 1.55 mu^{1/n}. Master bound min(8 [K_{2mu}], Psi_n(T*/mu) [K_mu]) dominates the recorded unconditional bounds unless T*/mu - 1 < ~2 e^{-32}. Spectral settling criterion: roots in disk radius R and nu_2/mu > x_n*, where Psi_n(x_n*) = 2 (x_2* = +inf; x_n* = 1.6064943, 1.4784372, 1.4289343, 1.4023941, 1.3857936, 1.3744142, 1.3598081 at n = 3,4,5,6,7,8,10; strictly decreasing to 1), settle Erdos #1041 for f with the join inside {|f| <= mu}. Compositional pullback: for P monic degree n with min(nu_2^P, |P(0)|)/mu_P > x_n*, every fibre f = P((z-h)^q), q >= 2, satisfies Erdos #1041, since f's critical spectrum is {P's critical values} union |P(0)| and x_{nq}* <= x_n* -- covering arbitrary-degree quotients without spoke selectors.

Evidence/status: ordinary_proof_on_quoted_directory_theorem_c_plus_two_elementary_lemmas_not_lean_checked

- [MinimalHubWindowJoin.md](problem/MinimalHubWindowJoin.md)
- [check_erdos1041_minimal_hub_window.py](problem/scripts/check_erdos1041_minimal_hub_window.py)

### primitive_quintic_closed_disk_two_tail_theorem

Let p(z)=z^5+a z^4+bz+c be monic and suppose all five roots lie in the closed unit disk. Then at least two distinct roots w satisfy |bw+c|<=1. If a!=0, two distinct roots satisfy the strict inequality; if a=0, every root is safe and |bw+c|=|w|^5. Abel summation converts each selected tail into a radial unit-sublevel path from the root to zero, so this settles the complete closed-disk primitive sparse quintic subproblem of Erdos #1041, including mixed interior/boundary root configurations. After rotating a to r>=0, the first three Newton sums are -r,r^2,-r^3. The harmonic extension H of the boundary cubic separator has exact total 5-2r and disk maximum 4-2r. An unsafe tail forces 5(1-s)<=2r(x+r/2); a two-variable completion of squares gives H<=2/31. Four unsafe roots would therefore score at most 4-2r+8/31<5-2r, contradiction. Lean checks the finite moment, disk-cap, unsafe-cap, two-selector, and zero-a equality arguments. SymPy checks the algebraic identities exactly; a deterministic 1,200-configuration Schur audit checked 6,000 roots, observed minimum safe-tail count two, and maximum unsafe score 0.020385883725163034<2/31.

Evidence/status: analytic_complete_lean_checked_exact_computation_closed_disk_subproblem_novelty_not_claimed

- [PrimitiveQuinticInteriorTail.md](problem/PrimitiveQuinticInteriorTail.md)
- [check_erdos1041_primitive_quintic_interior_tail.py](problem/scripts/check_erdos1041_primitive_quintic_interior_tail.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.primitiveBoundary_exists_two_tailEnergy_lt_one, ErdosProblems.Erdos1041.primitiveInteriorHarmonicSeparator_sum, ErdosProblems.Erdos1041.primitiveInteriorHarmonicSeparator_le_single, ErdosProblems.Erdos1041.primitiveInteriorHarmonicSeparator_le_of_tailEnergy_ge_one, ErdosProblems.Erdos1041.primitiveInterior_exists_two_tailEnergy_lt_one, ErdosProblems.Erdos1041.primitiveZeroCoefficient_tailEnergy_le_one.

### concyclic_potential_domination_kernel_and_certificate_criterion

For concyclic zeros: (i) Lean-checked factor bound log|1-w| <= |w|^2/2 - Re w (|w|<1) with multiplicative fan-in prod_i |z-v_i|^2 <= exp(n|z|^2 - 2 P(z)), P(z)=sum_i Re(z conj(v_i)), giving the sufficient cone certificate P(z) >= n|z|^2/2 ==> |g(z)| <= 1 on chords and spokes (ErdosProblems.Erdos1041.ConcyclicPotentialBound); (ii) exact Form-A-cut certificate criterion reducing V<=1 per configuration to finitely many one-dimensional polynomial containment checks; (iii) PROVEN INFEASIBILITY of first-moment-only certificates for n>=4: no (s,R) with R=|s_1|<=n satisfies the crude-tail spoke system, and even artificial spectral caps |s_m|<=beta fail in the near-regular shell where R,beta share scale -- any proof of V<=1 needs joint multi-harmonic bookkeeping.

Evidence/status: lean_checked_kernel_plus_exact_reduction_criterion_plus_proven_infeasibility_of_first_moment_certificates

- [check_erdos1041_concyclic_form_a_cut_certificate.py](problem/scripts/check_erdos1041_concyclic_form_a_cut_certificate.py)

### concyclic_concentric_alternation_counterexample

The concentric-alternation law Conjecture U is FALSE already for five distinct unit-circle roots. At s=3/20 the Gaussian-rational configuration w=(44/125+117i/125, -1809/2609+1880i/2609, -4/5-3i/5, 24/145-143i/145, 1012/1013-45i/1013) has, in every one of its five closed cyclic gaps, an explicit Gaussian-rational unit direction x_k with |prod_j((3/20)x_k-w_j)| > 1+(3/20)^5. The five exact squared margins are positive and range from 0.0019145 to 0.0191028. Therefore min_k max_{G_k} log|g(s exp(i psi))| > log(1+s^5), contrary to Conjecture U. This retires only the configuration-independent regular-polygon majorant. The Form-A-cut objective V<=1, the concyclic case, and unrestricted Erdos #1041 remain open.

Evidence/status: analytic_complete_exact_fraction_checked_lean_checked_rational_core

- [ConcyclicAlternationCounterexample.md](problem/ConcyclicAlternationCounterexample.md)
- [check_erdos1041_concyclic_alternation_counterexample.py](problem/scripts/check_erdos1041_concyclic_alternation_counterexample.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.ConcyclicAlternationCounterexample.all_points_unit, ErdosProblems.Erdos1041.ConcyclicAlternationCounterexample.root_gaps_are_minor, ErdosProblems.Erdos1041.ConcyclicAlternationCounterexample.test_points_in_gaps, ErdosProblems.Erdos1041.ConcyclicAlternationCounterexample.every_gap_exceeds_regular_bound.

### concyclic_smallest_gap_common_radius_selector_counterexample

The deterministic Form-A rule 'choose the unique smallest angular gap, then optimize only its common radius' is FALSE for five distinct unit-circle roots. For the rational half-angle parameters q=(1/1200,8/11,40/13,-83/27,-8/11), the w3,w4 gap is uniquely smallest by four exact positive squared-chord margins. Radius zero is inadmissible because |g(w4/10)|^2-1 is the positive rational 148116977372167593862092797/517567344770831203690000000000. At every 0<s<=1 the midpoint m=(w3+w4)/2 of the selected scaled chord satisfies |g(sm)|^2-1=s*(961/D)*A(s)>0: after degree elevation, 1260 A(s) has a degree-ten Bernstein expansion with eleven strictly positive integer coefficients. Hence no common radius works for that selected pair. This refutes only the smallest-gap selector; another pair may work, so Form A, the concyclic case, and Erdos #1041 remain open.

Evidence/status: analytic_complete_exact_fraction_checked_lean_checked_all_radius_obstruction

- [ConcyclicSmallestGapSelectorCounterexample.md](problem/ConcyclicSmallestGapSelectorCounterexample.md)
- [check_erdos1041_concyclic_smallest_gap_selector_counterexample.py](problem/scripts/check_erdos1041_concyclic_smallest_gap_selector_counterexample.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.ConcyclicSmallestGapSelectorCounterexample.roots_unit, ErdosProblems.Erdos1041.ConcyclicSmallestGapSelectorCounterexample.selected_chord_uniquely_shortest, ErdosProblems.Erdos1041.ConcyclicSmallestGapSelectorCounterexample.endpoint_four_full_spoke_unsafe, ErdosProblems.Erdos1041.ConcyclicSmallestGapSelectorCounterexample.midpoint_unsafe_at_every_positive_radius, ErdosProblems.Erdos1041.ConcyclicSmallestGapSelectorCounterexample.smallest_gap_common_radius_selector_fails.

### sextic_canonical_mixed_slice_connector

For every u>=0, the canonical degree-six homogeneous mixed model H_u(z)=Re(-i*u*z-z^2-z^6) has one explicit truncated connector in {H_u<=0}. Put q=(7+4sqrt(3))/27 and r=q^(1/4). The two outward ray tails in the sixth-root directions 1 and exp(-pi*i/3), from radius r to one, are nonpositive. On their chord, with w(t)=(1-t)+t exp(-pi*i/3), the carrier Re(w^2)+q Re(w^6) factors as q(t+1+sqrt(3))(t+1-sqrt(3))^2 C(t), where the four cubic Bernstein coefficients of C are strictly positive. Hence H_0(rw(t))<=0, with one exact double contact at t=sqrt(3)-1. The whole connector lies in the lower half-plane, so the additional term u Im(z) is nonpositive and the same connector works for every u>=0. Its normalized length is 2-r<2. This closes one complete sextic mixed-mode phase slice, not the full degree-six low-mode model or an actual-polynomial finite neighbourhood.

Evidence/status: analytic_complete_exact_symbolic_replay_lean_checked_square_bernstein_certificate

- [SexticCanonicalMixedSlice.md](problem/SexticCanonicalMixedSlice.md)
- [check_erdos1041_sextic_canonical_mixed_slice.py](problem/scripts/check_erdos1041_sextic_canonical_mixed_slice.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.radius_fourth, ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.cubic_bernstein_coefficients_pos, ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.chordCarrier_factor, ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.chordCarrier_nonneg, ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.canonicalSlice_connector_nonpos.

### sextic_square_contact_null_branch

The unique coefficient direction invisible to the four first-order square contacts at H_0(z)=Re(-z^2-z^6) continues as an exact algebraic zero-contact connector branch. Put s=sqrt(3), q0=(7+4s)/27 and beta*=(106+25s)/1221. For 0<=beta<=beta*, choose r^4=q0(1+(3/2)beta(s-1)), c=beta/r and u=3 beta r(2-s). Then H_beta(z)=Re(-i*u*z-z^2+i*c*z^3-z^6) has a nonpositive truncated connector on the adjacent sixth-root directions omega^2,omega^3. After division by r^2/2 the chord is the convex combination of its beta=0 certificate and a terminal factor (239+137s)/407 (t-1)(t-s+1)^2 P(t), where P has four strictly positive cubic Bernstein coefficients. The non-real ray is bounded by y^2(-86/9+17s/3)(beta-beta*)<=0. At beta=beta* this prescribed connector acquires a new ray-endpoint zero. Its length is 2-r<2. This does not assert optimal equality: all-pair computation finds a different adjacent connector with strict sampled margin for beta>0. The theorem covers one homogeneous sextic branch only, not the complete sextic model, finite transfer, or Erdos #1041.

Evidence/status: analytic_complete_exact_symbolic_replay_lean_checked_convex_endpoint_certificate

- [SexticNullBranch.md](problem/SexticNullBranch.md)
- [check_erdos1041_sextic_null_branch.py](problem/scripts/check_erdos1041_sextic_null_branch.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticNullBranch.branchRadius_fourth, ErdosProblems.Erdos1041.SexticNullBranch.endpointCubic_bernstein_coefficients_pos, ErdosProblems.Erdos1041.SexticNullBranch.endpointChord_factor, ErdosProblems.Erdos1041.SexticNullBranch.branchChord_nonpos, ErdosProblems.Erdos1041.SexticNullBranch.branchRay_nonpos, ErdosProblems.Erdos1041.SexticNullBranch.nullBranch_connector_nonpos.

### sextic_null_branch_strict_companion

For every parameter 0<=beta<=beta* on the sextic null branch, the opposite adjacent pair has a companion connector at the mirror radius rho^4=q0(1-(3/2)beta(sqrt(3)-1)). With R the original branch radius, put L=R/rho>=1 and M=rho/R<=1. The actual normalized chord is bounded above by branchChord(-beta): the L and M corrections both improve the sign. At -beta* this mirror chord factors as -(4943+2813sqrt(3))/10989 times (t-sqrt(3)+1)^2 times a quartic whose five Bernstein coefficients are strictly positive; convex interpolation with beta=0 proves the whole chord. On the non-real ray q(-beta)>=q(-beta*)>1/6 and y^6-1>=(3)(y^2-1), which absorbs all outward positive growth. Hence the companion chord and both ray tails are nonpositive and its length is 2-rho<2. For beta>0 the chord comparison is strict in its interior. This is a homogeneous sextic branch theorem, not the complete sextic atlas, finite transfer, or Erdos #1041.

Evidence/status: analytic_complete_exact_symbolic_replay_lean_checked_mirror_bernstein_certificate

- [SexticNullBranchCompanion.md](problem/SexticNullBranchCompanion.md)
- [check_erdos1041_sextic_null_branch_companion.py](problem/scripts/check_erdos1041_sextic_null_branch_companion.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticNullBranchCompanion.mirrorEndpoint_bernstein_coefficients_pos, ErdosProblems.Erdos1041.SexticNullBranchCompanion.mirrorEndpoint_factor, ErdosProblems.Erdos1041.SexticNullBranchCompanion.mirrorChord_nonpos, ErdosProblems.Erdos1041.SexticNullBranchCompanion.companionChord_nonpos, ErdosProblems.Erdos1041.SexticNullBranchCompanion.mirrorRay_nonpos, ErdosProblems.Erdos1041.SexticNullBranchCompanion.nullBranchCompanion_connector_nonpos.

### sextic_null_branch_uniform_stability_tube

Fix 0<epsilon<=beta<=beta* on the positive sextic null branch. At the mirror companion radius rho, put L=R/rho and M=rho/R. The exact radius identity q(beta)=L^4 q(-beta) implies L<2 and L-1>=(sqrt(3)-1)beta/5. On the first chord half t<=1/2, the canonical double-contact square is uniformly separated from zero: endpoint Bernstein floors give the mirror chord at most -1/100. On the second half, the radius-ratio correction gives at most -beta^2/10. Hence the actual normalized companion chord is at most -epsilon^2/10 throughout, and the outward selected ray has the stronger fixed bound -1/100. Any pointwise additive real error of size at most epsilon^2/20 therefore preserves strict negativity. This proves a finite-perturbation tube on every compact positive subbranch, but excludes beta=0, the remaining sextic faces, actual-polynomial coefficient bookkeeping, and unrestricted Erdos #1041.

Evidence/status: analytic_complete_exact_symbolic_replay_lean_checked_quantitative_actual_radius_margin

- [SexticNullBranchUniformMargin.md](problem/SexticNullBranchUniformMargin.md)
- [check_erdos1041_sextic_null_branch_uniform_margin.py](problem/scripts/check_erdos1041_sextic_null_branch_uniform_margin.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticNullBranchUniformMargin.actualRadius_linear_separation, ErdosProblems.Erdos1041.SexticNullBranchUniformMargin.mirrorChord_small_t_margin, ErdosProblems.Erdos1041.SexticNullBranchUniformMargin.companionChord_uniform_margin, ErdosProblems.Erdos1041.SexticNullBranchUniformMargin.mirrorRay_uniform_margin, ErdosProblems.Erdos1041.SexticNullBranchUniformMargin.companionRay_uniform_margin, ErdosProblems.Erdos1041.SexticNullBranchUniformMargin.uniformMargin_absorb_error.

### sextic_null_branch_transverse_selector

At the canonical sextic square-contact model, write a gauge-fixed tangent perturbation as Re((a1+i*b1)z-i*theta*z^2+i*c*z^3). At the four contacts z=a(+-1+-i), put p=a*a1, q=2*a^2*theta and r=-a*(b1+2*a^2*c). The four first variations are p+q+r, p-q-r, -p-q+r and -p+q-r. If m is their minimum, then m<=0 and p^2+q^2+r^2<=3m^2; the constant three is sharp. Their common kernel is exactly a1=theta=0 and b1=-2*a^2*c, the already-continued null line. Completing the square shows that a contact margin 45*delta^2 absorbs chord variation 3*delta*|t-t0| against canonical curvature -(t-t0)^2/20. Hence outside p^2+q^2+r^2<6075*delta^4 one canonical contact supplies the full local chord margin. This closes every first-order transverse direction and reduces beta->0 to a bounded second-order tube around one explicit branch; it does not prove that secondary atlas, finite transfer, or Erdos #1041.

Evidence/status: analytic_complete_exact_symbolic_replay_lean_checked_sharp_tetrahedral_selector

- [SexticNullBranchTransverseSelector.md](problem/SexticNullBranchTransverseSelector.md)
- [check_erdos1041_sextic_null_branch_transverse_selector.py](problem/scripts/check_erdos1041_sextic_null_branch_transverse_selector.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector.contact_sum_zero, ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector.contact_square_sum, ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector.transverseEnergy_le_three_contactMin_sq, ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector.transverse_contact_selector, ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector.transverse_coordinates_eq_zero_iff, ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector.quadratic_contact_absorption, ErdosProblems.Erdos1041.SexticNullBranchTransverseSelector.contactMin_le_neg_fortyFive_sq.

### sextic_null_branch_second_order_atlas

In the O(beta^2) tube around the canonical sextic null branch, let p,q,r be the three normalized second-order transverse contact coordinates. Optimizing the fourth-power truncation-radius slope gives two exact offsets o_plus=-117+(135/2)sqrt(3) and o_minus=-9+(9/2)sqrt(3). The four limiting connector maxima are o_plus+p+q+r, o_plus-p-q+r, o_minus-p+q-r, and o_minus+p-q-r. Their transverse terms sum to zero, so their average is -63+36sqrt(3)<-3/5. Hence for every real p,q,r at least one connector has normalized limiting maximum at most -3/5. The radius optimizers are exactly plus or minus (21+11sqrt(3))/54, obtained from complete squares with positive coefficient (2187/4)(97-56sqrt(3)). This closes the entire bounded second-order homogeneous atlas, but not its uniform finite-beta Taylor transfer, other sextic faces, actual-polynomial transfer, or unrestricted Erdos #1041.

Evidence/status: analytic_complete_exact_symbolic_replay_lean_checked_uniform_four_connector_cover

- [SexticNullBranchSecondOrderAtlas.md](problem/SexticNullBranchSecondOrderAtlas.md)
- [check_erdos1041_sextic_null_branch_second_order_atlas.py](problem/scripts/check_erdos1041_sextic_null_branch_second_order_atlas.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas.completedSquareFactor_pos, ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas.plusRawProfile_complete_square, ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas.minusRawProfile_complete_square, ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas.localQuadratic_le_completedSquare, ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas.profile_sum, ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas.secondOrder_four_connector_cover.

### sextic_null_branch_finite_transfer

Let s=sqrt(3), q0=(7+4s)/27, a0=(3/2)q0(s-1), k*=(21+11s)/54, h=(3-s)/2 and r0=q0^(1/4). For 0<beta<=10^-9 and normalized transverse coordinates |P|,|Q|,|U|<=78, put R^4=q0+a0 beta, a1=P r0/(2h), b1=-U r0/(2h), theta=Q/(4h^2), and H(z)=Re((-3i beta R(2-s)+beta^2(a1+i b1))z+(-1-i beta^2 theta)z^2+(i beta/R)z^3-z^6). Among the four adjacent pairs 0,2,3,5, using rho^4=q0+k* beta for 0,2 and rho^4=q0-k* beta for 3,5, one full truncated connector is nonpositive. Its normalized chord is at most -beta^2/2 and its length is 2-rho<2. The proof uses the exact second-order profiles, a global canonical floor -(2/5)(t-t_j)^2, outer scale |t-t_j|>=100 beta, and a local remainder coefficient 40,481,000<40,500,000, absorbed because 40,500,000 beta<1/20. This closes the exact finite-beta homogeneous canonical null core, not the remaining sextic faces, arbitrary actual-polynomial transfer, or unrestricted Erdos #1041.

Evidence/status: analytic_complete_exact_symbolic_replay_lean_checked_explicit_finite_beta_core

- [SexticNullBranchFiniteTransfer.md](problem/SexticNullBranchFiniteTransfer.md)
- [check_erdos1041_sextic_null_branch_finite_transfer.py](problem/scripts/check_erdos1041_sextic_null_branch_finite_transfer.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticNullBranchFiniteTransfer.remainder_absorbed, ErdosProblems.Erdos1041.SexticNullBranchFiniteTransfer.localEnvelope_transfer, ErdosProblems.Erdos1041.SexticNullBranchFiniteTransfer.outerEnvelope_transfer, ErdosProblems.Erdos1041.SexticNullBranchFiniteTransfer.finiteBeta_four_connector_cover, ErdosProblems.Erdos1041.SexticNullBranchFiniteTransfer.fixedRaySlack_absorb, ErdosProblems.Erdos1041.SexticNullBranchFiniteTransfer.adjacentConnectorLength_lt_two.

### sextic_null_branch_global_box_atlas

Let betaStar=(106+25sqrt(3))/1221 and use the exact homogeneous sextic family and normalized transverse cube |P|,|Q|,|U|<=78 of the finite-transfer theorem. For every 0<beta<=betaStar, at least one of the four limiting-profile-selected adjacent pairs 0,2,3,5 has a complete truncated connector in H<=0, with truncation fourth power q0 plus or minus kStar beta and total length 2-rho<2. The four affine selector cells reduce by reflection to 17 exact vertices. The sole central equalizer has profile -63+36sqrt(3)<-3/5; every other vertex has selected profile at most -78. Small beta is absorbed by separate central and noncentral margins. On [10^-6,betaStar], exact bivariate Bernstein certificates prove the Taylor upper polynomials nonpositive, with third-order budgets 1/2 and 300 respectively. Degree-20 binomial tails rigorously certify the sharp central remainder and radial monotonicity on both selected rays. This closes the complete finite homogeneous canonical null-box atlas, not other sextic faces, actual-polynomial transfer, or unrestricted Erdos #1041.

Evidence/status: analytic_complete_exact_symbolic_replay_lean_checked_full_canonical_parameter_interval

- [SexticNullBranchGlobalBoxAtlas.md](problem/SexticNullBranchGlobalBoxAtlas.md)
- [check_erdos1041_sextic_null_branch_global_box_atlas.py](problem/scripts/check_erdos1041_sextic_null_branch_global_box_atlas.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas.betaSplit_pos, ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas.central_smallBeta_transfer, ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas.noncentral_smallBeta_transfer, ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas.thirdOrder_vertex_transfer, ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas.convexVertex_transfer, ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas.rayDerivative_subset_transfer, ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas.four_way_minimum, ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas.profile_selector_cell.

### sextic_cubic_face_positive_radius_connector_no_go

For the pure cubic sextic model H(z)=Re(z^3-z^6), no positive equal-radius truncated-spoke connector between two non-antipodal sixth-root directions lies in H<=0. Every such pair has gap pi/3 or 2pi/3. At chord parameter 1/2 or 1/3 respectively, the chord crosses the half-step direction (2j+1)pi/6, where z^3=i*x for a nonzero real x and H(z)=x^2>0. Antipodal pairs have length exactly two and cannot yield the strict metric target. Therefore the proposed full positive-radius atlas for Re(Az+Bz^2+Cz^3-z^6), max(|A|,|B|,|C|)=1, is false on (A,B,C)=(0,0,1). The face itself remains solvable by the radius-zero origin connector and the cyclic-trinomial theorem; the consequence is a mandatory stratification, not a counterexample to Erdos #1041.

Evidence/status: ordinary_complete_exact_symbolic_replay_with_lean_checked_algebraic_core

- [SexticCubicFaceConnectorNoGo.md](problem/SexticCubicFaceConnectorNoGo.md)
- [check_erdos1041_sextic_cubic_face_connector_no_go.py](problem/scripts/check_erdos1041_sextic_cubic_face_connector_no_go.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticCubicFaceConnectorNoGo.cubicFaceValue_pos_of_cube_eq_mul_I, ErdosProblems.Erdos1041.SexticCubicFaceConnectorNoGo.adjacentMidpoint_cube, ErdosProblems.Erdos1041.SexticCubicFaceConnectorNoGo.adjacentMidpoint_cubicFaceValue_pos, ErdosProblems.Erdos1041.SexticCubicFaceConnectorNoGo.not_all_nonpos_of_halfStep_mem.

### sextic_cubic_radial_deficit_staple_cone

For G(z)=-Delta+Re(E1 z+E2 z^2+E3 z^3+E4 z^4+E5 z^5-z^6), assume 0<Delta<=1, |E3|<=1, and |E1|+|E2|+|E4|+|E5|<=Delta. Put s=Delta/4. One parity class of three sixth-root directions makes the cubic projection nonpositive. Each selected radial arm from s to unit radius is strictly negative because the nuisance modes spend at most Delta*t and the remaining -t^6 is strict. The complete disk |z|<=s has value at most -Delta/2. Hence any two selected rays joined inside that disk form a strict staple of length 2-(2-sqrt(3))s<2. This restores the radial deficit omitted by the deficit-free cubic-face atlas and closes a full-dimensional finite Fourier stability cone, not every cubic-dominant normalization or the actual-polynomial transfer.

Evidence/status: ordinary_complete_explicit_model_theorem_with_exact_replay_and_lean_checked_scalar_core

- [SexticCubicRadialDeficitCone.md](problem/SexticCubicRadialDeficitCone.md)
- [check_erdos1041_sextic_cubic_radial_deficit_cone.py](problem/scripts/check_erdos1041_sextic_cubic_radial_deficit_cone.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone.fourModes_le_linear, ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone.fourModes_le_delta_mul, ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone.innerDisk_margin, ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone.selectedRay_strict, ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone.exists_parity_sign_nonpos, ErdosProblems.Erdos1041.SexticCubicRadialDeficitCone.sameParity_staple_length_lt_two.

### sextic_first_mode_three_quarter_overlap

In the normalized paired sextic tangent model, let A=|E1|, B=|E2| with 0<=B<=1, and select the adjacent sixth-root directions whose first-mode projections are at most -A/2. If 3B<=4A, both complete selected rays are nonpositive. The worst normalized ray factors as -t P(t)/8, where P(t)=8t^5-3t^4+8t^3-8t+3. On t<=1/2 its six Bernstein controls after x=2t are 3, 11/5, 7/5, 7/10, 13/80, 1/16; on t>=1/2, x=2t-1 gives 16P=4x^5+17x^4+44x^3+70x^2-8x+1 and the quadratic equals 70(x-2/35)^2+27/35. The small adjacent chord remains strict under the existing scale conditions, with explicit residual margin A*u/48. Thus the unresolved mixed annulus shrinks from |E1|/|E2|<4/5 to |E1|/|E2|<3/4.

Evidence/status: analytic_complete_exact_rational_replay_lean_checked

- [SexticFirstModeThreeQuarterOverlap.md](problem/SexticFirstModeThreeQuarterOverlap.md)
- [check_erdos1041_sextic_first_mode_three_quarter_overlap.py](problem/scripts/check_erdos1041_sextic_first_mode_three_quarter_overlap.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SexticFirstModeThreeQuarterOverlap.threeQuarterPolynomial_pos, ErdosProblems.Erdos1041.SexticFirstModeThreeQuarterOverlap.normalizedThreeQuarterRay_nonpos, ErdosProblems.Erdos1041.SexticFirstModeThreeQuarterOverlap.pairedTangentRay_threeQuarter_nonpos, ErdosProblems.Erdos1041.SexticFirstModeThreeQuarterOverlap.threeQuarterChord_strict.

### two_root_path_length_lower_semicontinuity

Let K_n be the compact class of monic degree-n polynomials with all roots in the CLOSED unit disk, and for g in K_n let Lam(g) be the infimum of lengths of rectifiable curves inside {|g|<=1} joining two roots of g, minimised over ordered index pairs of the root list. Then Lam is LOWER semicontinuous on K_n, so {Lam<=2} is closed. Proof: roots in the closed unit disk give prod_j|z-b_j|>=(|z|-1)^n>=1 for |z|>=2, so every sublevel set {|g|<=1} lies in the fixed compact disk {|z|<=2}; constant-speed reparametrisation makes bounded-length competitors equi-Lipschitz there; Arzela-Ascoli plus lower semicontinuity of length transports a path to the limit polynomial. CONSEQUENCE (Corollary D): if Lam<=2 on any subset of K_n whose closure is K_n, then Lam<=2 on K_n. Since roots-in-the-open-disk, squarefree, finite-exceptional one-coefficient genericity, and any nonempty Zariski-open coefficient condition are each dense in K_n and may be conjoined, every genericity-dependent route in this directory may drop its transfer half. Composing with the recorded minimum-enclosing-disk normalisation of VisibilityOverlapReduction.md section 3, which supplies length<=2R<2 and |f|<=R^n<1 from R<1 alone and therefore spends no slack, gives Corollary S: to prove Erdos #1041 in degree n it suffices to prove Lam<=2 on SOME dense subclass of K_n. EXTREMAL VALUE: Lam(z^n-1)=2 exactly. The sublevel set is characterised by |z|^(2n)<=2Re(z^n), so off the origin Re(z^n)>0, which confines the punctured sublevel set to the n pairwise disjoint open sectors |arg z - 2 pi k/n|<pi/(2n); a path joining two roots therefore meets 0 and has length at least 1+1=2, while the radial pair path attains 2. EQUIVALENCE (Theorem Q): Erdos #1041 in degree n holds if and only if Lam<=2 on all of K_n, if and only if sup{Lam(g):g in K_n}=2, i.e. if and only if z^n-1 maximises Lam on K_n. Lam is lower semicontinuous, so it attains its minimum, not its maximum; the supremum is attained exactly when the conjecture holds.

Evidence/status: analytic_complete_exact_rational_replay_lean_checked

- [check_erdos1041_generic_sufficiency_closure.py](problem/scripts/check_erdos1041_generic_sufficiency_closure.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.GenericSufficiencyClosure.one_le_prod_norm_sub_of_two_le_norm, ErdosProblems.Erdos1041.GenericSufficiencyClosure.dist_le_of_tendsto, ErdosProblems.Erdos1041.GenericSufficiencyClosure.isClosed_sublevel_of_isOpen_superlevel, ErdosProblems.Erdos1041.GenericSufficiencyClosure.eq_univ_of_isClosed_of_dense, ErdosProblems.Erdos1041.GenericSufficiencyClosure.mul_lt_two_of_lt_one, ErdosProblems.Erdos1041.GenericSufficiencyClosure.pow_mul_lt_one_of_lt_one, ErdosProblems.Erdos1041.GenericSufficiencyClosure.normSq_sub_one_le_one_iff, ErdosProblems.Erdos1041.GenericSufficiencyClosure.re_pow_pos_of_ne_zero, ErdosProblems.Erdos1041.GenericSufficiencyClosure.normSq_radial_sub_one_le_one.

### reciprocal_newton_expansion

Let f(z)=prod_j(z-a_j) with every a_j nonzero, r=min_j|a_j|, and p_m=sum_j a_j^(-m). Then for |z|<r, log|f(z)|=log|f(0)|-Re sum_{m>=1}(p_m/m)z^m, absolutely convergent, with q=|z|/r and for every N>=0 the tail bounds |remainder|<=n q^(N+1)/((N+1)(1-q)), |T_N'|<=(n/r)q^N/(1-q), and |T_N''|<=(n/r^2)q^(N-1)(N/(1-q)+q/(1-q)^2). This is a TAYLOR series, not an asymptotic one, and it is controlled in C^2 where FormACutQuantitativeExpansion controls its remainder only in C^0. R2 (coefficients are rational in the coefficients of f): writing f=sum c_k z^k and chat_k=c_k/c_0, Newton's identity for the reversed polynomial gives sum_{j=0}^{m-1} chat_j p_{m-j} + m chat_m = 0, i.e. p_m = -m chat_m - sum_{j=1}^{m-1} chat_j p_{m-j}; equivalently f'=-f sum_{m>=0} p_{m+1} z^m as formal series. So the normalisation is rational, hence semialgebraic, with no root labelling. R3 (the bridge to the E_m coordinates already on file): with a_k=omega^k(1+e_k), eta=max|e_k|<1 and E_m^(j)=sum_k e_k^j omega^(-km), for 1<=m<=n-1 -p_m/m = E_m - ((m+1)/2)E_m^(2) + ((m+1)(m+2)/6)E_m^(3) - ..., general term (-1)^(j-1)(1/m)binom(m+j-1,j)E_m^(j), and |-p_m/m - E_m| <= n(m+1)eta^2/(2(1-eta)^(m+2)). THEREFORE the anchored nonlinear remainder R_anchor=O(eta^2|z|) of FormACutQuantitativeExpansion is not an error at all: it is the second and higher terms of an exact coefficient. This matters exactly when a quadratic correction carries the same Newton weight as a nominally active linear mode, which is what a tied face or a face switch produces. R4 (staple length): the equal-radius staple a_i -> s u_i -> s u_j -> a_j has length exactly |a_i|+|a_j|-s(2-|u_i-u_j|), hence at most |a_i|+|a_j|<2 for every admissible s including s=0, so moving root directions spend no margin. R5 (contact absorption): if F<=-kappa x^2+B|x|+V+eps with kappa>0 then F<=V+eps+B^2/(4 kappa), so a zero-margin contact survives exactly when V+eps+B^2/(4 kappa)<0; uniform convergence to a non-positive model is NOT sufficient, the countermodel being -x^2+eps. The recorded sextic instance is curvature -x^2/20 against transverse slope 3 delta |x|, costing exactly 45 delta^2.

Evidence/status: analytic_complete_exact_rational_replay_lean_checked

- [check_erdos1041_reciprocal_newton_expansion.py](problem/scripts/check_erdos1041_reciprocal_newton_expansion.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.norm_recipPowerSum_le, ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.tsum_geometric_tail, ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.newton_solve, ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.staple_length_eq, ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.staple_length_lt_two, ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.quadratic_contact_absorbs, ErdosProblems.Erdos1041.ReciprocalNewtonExpansion.contact_survives.

### attachment_aware_reeb_lane_ceiling

Call a component U of {|f|<1} carrying k>=2 roots RAY SEPARATED when its critical points are simple, its critical values v_c=rho_c exp(i theta_c) are nonzero, and their arguments and moduli are pairwise distinct. THEOREM 1: cutting the value disk along the OUTWARD slits J_c={r exp(i theta_c): rho_c<=r<1} leaves D-dagger star-shaped about 0, hence simply connected, so f restricted to its preimage in U is an unbranched k-fold covering splitting into exactly k sheets, one per root; each simple critical value transposes exactly two sheets, and k-1 transpositions acting transitively on k labels give a TREE T_f whose geometric realisation is the union of the canonical descending inverse-ray arcs A_c, each contained in {|f|<=rho_c}. Cutting instead along the COMPLETE critical rays leaves sectors with no branch value, so every preimage component maps biholomorphically and (-log|f|, arg f) is a real-analytic diffeomorphism onto a Euclidean strip: the Reeb regions are genuine strips, and the saddle neighbourhoods N_c(delta) have diameter and internal connector cost O(sqrt delta). THEOREM 2 (attachment rigidity): a Newton trajectory has f(gamma(t))=exp(-t) f(gamma(0)), so its value argument theta is frozen; meeting N_c(delta) forces rho_c |sin(theta-theta_c)| < delta and cos(theta-theta_c)>0 for delta<rho_c, an angular window of measure exactly 2 arcsin(delta/rho_c) <= pi delta/rho_c. The one identity behind this is rho^2-2 rho t c+t^2-rho^2 s^2=(t-rho c)^2. THEOREM 2': if f-v_c vanishes to order p at c then the window at physical radius eps is Theta(eps^p/rho_c) - the exponent is the ramification index. THEOREM 3 (lane ceiling): for local Newton skeletons whose non-trajectory connectors are confined to the shrinking neighbourhoods, the pair cost tends to min_c L(c) and the spanning cost to sum_c L(c). Hence Lam(f) <= min_c L(c) <= (1/m) sum_c L(c) and the Reeb/strip lane proves EXACTLY min_c L(c)<2 - no better and no worse than admissible_branch_length_reformulation. Independent strip averaging supplies no metric saving, which is why the recorded 4/25 Cassini attachment deficit cannot be repaired by finer local Morse bookkeeping: the strip average is an interior L1 quantity in the angular variable while attachment needs its boundary trace at theta_c. THEOREM 5 (extremal family, exact): for g=z^n-r^n the closest approach of the ray of angle theta to the hub is r if cos theta>=0 and r|sin theta|^(1/n) if cos theta<0, so for eps<r a trajectory meets B(0,eps) iff cos theta<0 and |sin theta|<(eps/r)^n. On the family that is extremal for the whole problem the attachable fraction of directions is the n-th power of eps/r. THEOREM 4 (root-star tangent law): at a simple root a the unit tangent of the incident arc A_c pointing into the arc is exactly exp(i(theta_c - arg f'(a))), so ray separation is precisely the statement that the geometric tree has no tangency at a root, and sum_i <a,U_a^(i)> = Re(a exp(i arg f'(a)) S_a) with S_a=sum_i exp(-i theta_{c_i}). COROLLARY 4a: the componentwise obligation (F) of CriticalTreeLengthCharge.md is exactly 2Rm + sum_{a in V(C)} Re(a exp(i arg f'(a)) S_a) + sum_{e in C} K_e >= 0. COROLLARY G: the four ray-separation hypotheses each exclude a proper closed real-analytic subset, so ray-separated polynomials are DENSE in the closed-disk class K_n; by GenericSufficiencyClosure Theorem L and Corollary S, proving min_c L(c)<=2 for ray-separated members of K_n proves Erdos #1041 in degree n. The genericity is therefore free.

Evidence/status: analytic_complete_exact_rational_replay_lean_checked

- [check_erdos1041_attachment_aware_reeb.py](problem/scripts/check_erdos1041_attachment_aware_reeb.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.AttachmentAwareReeb.rayDist_sq_identity, ErdosProblems.Erdos1041.AttachmentAwareReeb.attachment_window_sin, ErdosProblems.Erdos1041.AttachmentAwareReeb.attachment_window_cos_pos, ErdosProblems.Erdos1041.AttachmentAwareReeb.extremal_closest_approach_lower, ErdosProblems.Erdos1041.AttachmentAwareReeb.extremal_closest_approach_cos_nonneg, ErdosProblems.Erdos1041.AttachmentAwareReeb.extremal_closest_approach_attained, ErdosProblems.Erdos1041.AttachmentAwareReeb.extremal_window, ErdosProblems.Erdos1041.AttachmentAwareReeb.isTree_of_connected_of_card_eq, ErdosProblems.Erdos1041.AttachmentAwareReeb.exists_le_of_sum_le_card_mul, ErdosProblems.Erdos1041.AttachmentAwareReeb.rootStar_tangent_sum, ErdosProblems.Erdos1041.AttachmentAwareReeb.cassini_endpoint_deficit_zero.

### sextic_chord_covering_criterion_and_unit_band

For the paired homogeneous sextic tangent model H=Re(Az+Bz^2+iCz^3-conj(B)z^4-conj(A)z^5-z^6) on the adjacent unit chord z_j(x)=exp(i(2j+1)pi/6)(sqrt3+ix)/2, THEOREM 1 (normal form): 64 H(z_j(x)) = -64 + (1-x^2) N_j(x) with N_j(x)=x^4-44x^2+91+4p(21-x^2)+16 sqrt3 r x+10 sqrt3 u(5-x^2)+2 v x(29-x^2)-24 sqrt3 c, where alpha=A exp(i theta_j)=u+iv, beta=B exp(2 i theta_j)=p+ir, c=(-1)^j C. COROLLARY: H(omega^j)=-1 for every j and every (A,B,C), so all six root directions sit at identical depth and x=+-1 never binds. THEOREM 2 (decoupled covering criterion, exact iff): with W_j = N_j + 24 sqrt3 c_j - 64/(1-x^2) and S_j = sup_{|x|<1} W_j, some adjacent chord lies in {H<=0} for EVERY real C if and only if min_{j even} S_j + min_{j odd} S_j <= 0. The supplied pivot mechanism is the sufficient special case j'=j+3; mixed pairs are strictly stronger and are what the model uses once |A| grows. THEOREM 3 (unit band): |B|=1 and |A|<=1 imply that for every real C one of two antipodal adjacent unit chords carries H <= -1/256 along its whole length 1, certified by G1(t)=t^6+5t^5/8-43t^4+651t^3/8+91t^2-82t+15 >= 1/4 on [0,1] via a SIX-piece dyadic degree-six Bernstein certificate (two pieces provably do not suffice; min G1 = 0.264286 at t = 0.335121). This strictly contains the supplied band |A|<=3|B|/4 with margin 127/3072, so the residual closes with a quarter-width OVERLAP into the first-mode chart rather than meeting it at a point. THEOREM 4 (sharpness): the pivot T=25u/12 with the symmetrised gap is sharp at lambda* = min_t P(t)/(2t(1-t^2)sqrt(t^4+17t^2+841)) = 1.0153340671..., unique interior critical point t*=0.3371285327...; Cauchy-Schwarz is lossless and the symmetrisation is lossless because P(-t)-P(t)=48t(1-t^2)>=0 but arg A is adversarial; freeing the pivot raises the antipodal-pair threshold to 1.3880401... THEOREM 5 (antipodal barrier): (N_j+24 sqrt3 c_j)(0)+(N_{j+3}+24 sqrt3 c_{j+3})(0)=2(91+84p), so Re(beta)<=-9/28 is necessary for ANY antipodal pair, independent of A, C and the pivot; hence the antipodal mechanism cannot reach |B|<9/14 at the extremal second-mode phase and mixed pairs are mathematically necessary below it. THEOREM 6 (large first mode): with psi(chi)=max_{|x|<=1}[10 sqrt3 cos chi (5-x^2)+2 sin chi x(29-x^2)], every phase admits an even j within pi/6 and an odd j' within pi/3 of the reversed direction, giving psi(chi_j)<=-32 and psi(chi_j')<=8 sqrt3 via the exact factorisations (t-1)(t^2-14t-43)>=0 and (t-1)(t^2-4t-33)>=0 on [0,1]; hence min_even psi + min_odd psi <= 8 sqrt3 - 32 < 0 and criterion (4) holds for |A| >= 226/(32-8 sqrt3) = 12.46...

Evidence/status: analytic_complete_exact_rational_replay

- [check_erdos1041_sextic_chord_covering_criterion.py](problem/scripts/check_erdos1041_sextic_chord_covering_criterion.py)

### self_inversive_comparison_dual_and_selector_no_go

For a monic self-inversive comparison polynomial evaluated on the alternating unit-circle nodes of a concyclic polynomial, the exact gap-product/residue identity gives positive quadrature weights omega_j with sum omega_j=1 and weighted comparison ratios x_j satisfying sum omega_j x_j=1. Hence some ratio is at least one. More sharply, the evaluation image is the entire weighted affine hyperplane: for every nonempty proper candidate set S, two-level ratios can be chosen above one exactly on S and below one off S. Thus comparison-polynomial freedom alone has no geometric selector content; any successful use must impose an additional metric or containment functional. The dilation node identity and topological two-root-component consequence remain valid auxiliary tools.

Evidence/status: analytic_complete_deterministic_replay_lean_kernel_checked

- [SelfInversiveComparisonDual.md](problem/SelfInversiveComparisonDual.md)
- [check_erdos1041_self_inversive_comparison_dual.py](problem/scripts/check_erdos1041_self_inversive_comparison_dual.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SelfInversiveComparisonDual.exists_one_le_of_weightedAverage_eq_one, ErdosProblems.Erdos1041.SelfInversiveComparisonDual.prescribedCandidateRatios.

### critical_blaschke_pair_bound

For a degree-k finite Blaschke product critical at zero, order its zero radii r1<=r2<=... and put P=prod r_j. The critical polygon with side lengths q(r)=1/r-r gives q(r1)<=(k-1)q(r2), hence r2<=(k-1)r1 and r2^k<=(k-1)P. The sharp implicit lower envelope P>=x_k(r2)r2^(k-1) is stronger. Transferred to a polynomial lemniscate component and composed with the sharp Bergman geodesic estimate, this gives an explicit all-degree sufficient region, including the Polya-level condition ((k-1)|f(c)|)^(2/k)<=tanh(1). Higher critical multiplicity gives the exact moment cancellations sum(alpha_j^-q-conj(alpha_j)^q)=0 for q through the multiplicity. The estimate degenerates as P approaches one and does not settle the near-Fekete regime.

Evidence/status: analytic_complete_deterministic_replay_lean_kernel_checked

- [CriticalBlaschkePairBound.md](problem/CriticalBlaschkePairBound.md)
- [check_erdos1041_critical_blaschke_pair_bound.py](problem/scripts/check_erdos1041_critical_blaschke_pair_bound.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.CriticalBlaschkePairBound.secondRadius_pow_le, ErdosProblems.Erdos1041.CriticalBlaschkePairBound.secondRadius_le_of_q_balance.

### connected_cluster_bergman_certificate

Let C be a regular polynomial lemniscate component containing k zeros counted with multiplicity and at least two distinct zero locations. With A_C=Area(C) and q_C the maximum internal critical-value modulus divided by the level, the whole critical sublevel of the degree-k Blaschke uniformization is connected by Riemann-Hurwitz. Its cover by pseudohyperbolic discs therefore has an edge between unequal zero locations, yielding a pair at distance at most 2 q_C^(1/k)/(1+q_C^(2/k)). The sharp Bergman estimate gives length^2 <= (2A_C/pi) log((1+q_C^(2/k))/(1-q_C^(2/k))). Thus alpha_C log((1+q_C^(2/k))/(1-q_C^(2/k)))<=2 is a complete component certificate. The capacity form is q_C<=tanh(1/kappa_C^2)^(k/2). This handles arbitrary simultaneous ties without minimizing over marked hubs. The remaining CDF obligation is to force the certificate at some merge-tree node.

Evidence/status: analytic_complete_deterministic_replay_lean_kernel_checked

- [ConnectedClusterBergman.md](problem/ConnectedClusterBergman.md)
- [check_erdos1041_connected_cluster_bergman.py](problem/scripts/check_erdos1041_connected_cluster_bergman.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.ConnectedClusterBergman.overlap_defect_identity, ErdosProblems.Erdos1041.ConnectedClusterBergman.length_le_two_of_cluster_certificate, ErdosProblems.Erdos1041.ConnectedClusterBergman.length_le_two_mul_scale_of_normalized_certificate.

### connected_cluster_fixed_level_area_forcing

Fix a regular level 0<t<1 and list all multi-root components C_i of K_t. Put alpha_i=Area(C_i)/(pi t^(2/n)) and L_i=log((1+q_i^(2/k_i))/(1-q_i^(2/k_i))), where q_i is the largest internal critical-value modulus divided by t. The connected-cluster Bergman certificate gives a curve in C_i with length_i^2<=2 t^(2/n) alpha_i L_i, while disjointness and Polya give sum_i alpha_i<=1. Therefore the single fixed-level condition sum_i 2/L_i>=1 forces some alpha_i L_i<=2 and hence two roots joined inside K_t by a curve of length at most 2 t^(1/n)<2. The finite pigeonhole implication and its exact composition with the landed Bergman consumer are Lean checked. A deterministic descending-branch merge-tree probe certifies this scalar condition on three bulk configurations (maxima 2.2625, 3.0390, 1.2920 in degrees 4,6,8) but falsifies its universality on near-regular radius-0.999 perturbations in degrees 4,6,8,10 (maxima 0.3049, 0.2739, 0.3046, 0.6395). Those numerical rows refute only merge-level-only reciprocal-barrier forcing; actual component areas may still force a certificate, and Erdős #1041 remains open.

Evidence/status: ordinary_analytic_proof_with_lean_checked_finite_kernel_and_deterministic_scalar_falsifier

- [ConnectedClusterAreaForcing.md](problem/ConnectedClusterAreaForcing.md)
- [check_erdos1041_connected_cluster_area_forcing.py](problem/scripts/check_erdos1041_connected_cluster_area_forcing.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.ConnectedClusterAreaForcing.exists_cluster_certificate_of_area_sum, ErdosProblems.Erdos1041.ConnectedClusterAreaForcing.exists_length_le_two_of_area_forcing.

### tied_newton_face_complete_spoke_no_go_and_connector_rescue

For the quintic tied-face model H(z)=Re(z+10z^2-z^5), every fifth-root ray contains a point with H>0. Writing s=sqrt(5), the five restrictions have three conjugacy types q0=t+10t^2-t^5, q1=((s-1)/4)t-10((s+1)/4)t^2-t^5, and q2=-((s+1)/4)t+10((s-1)/4)t^2-t^5; positive witnesses occur at t=1/10, 1/1000, and 3/10 respectively. Thus a general tied Newton face need not have even one complete safe model spoke. The correct replacement succeeds on the same example: ray types 1 and 2 are strictly negative for every t>=2, and on the adjacent connector z(u)=2((1-u)omega+u omega^2) the exact quartic restriction satisfies H<=-5 for all 0<=u<=1, by a two-piece Bernstein certificate split at u=1/2. Lean checks the radical inequalities, five-ray assembly, no-safe-ray theorem, outward ray bounds, quartic Bernstein lemma, and connector margin. This closes the first tied face with a connector while proving complete-spoke selection cannot be the all-degree mechanism.

Evidence/status: exact_ordinary_root_of_unity_reduction_with_lean_checked_no_go_and_connector

- [TiedNewtonFaceTwoSpokeNoGo.lean](problem/TiedNewtonFaceTwoSpokeNoGo.lean)
- [TiedNewtonFaceTwoSpokeNoGo.md](problem/TiedNewtonFaceTwoSpokeNoGo.md)
- [check_erdos1041_tied_newton_face_two_spoke_no_go.py](problem/scripts/check_erdos1041_tied_newton_face_two_spoke_no_go.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceTwoSpokeNoGo.every_model_ray_has_positive_point, ErdosProblems.Erdos1041.TiedNewtonFaceTwoSpokeNoGo.no_complete_safe_model_ray, ErdosProblems.Erdos1041.TiedNewtonFaceTwoSpokeNoGo.chordAtTwo_le_neg_five, ErdosProblems.Erdos1041.TiedNewtonFaceTwoSpokeNoGo.exact_connector_rescues_tied_face.

claim_boundary: This is an exact obstruction-and-rescue theorem for the single quintic model H(z)=Re(z+10z^2-z^5): it rules out a complete safe fifth-root spoke and certifies one radius-two adjacent connector. It does not prove the compact tied-face connector theorem in arbitrary degree, transfer the model connector to a neighbourhood of a general polynomial, or solve the unrestricted Erdős 1041 problem.

### tied_newton_face_zero_critical_value_trace_and_two_end_merge

Let Q(z)=sum_(m in M) A_m z^m-z^n with every active degree 1<=m<n/2, and list the n-1 critical points c_i with multiplicity. The missing upper half of Q'/(-n) makes the Newton power sums sum_i c_i^m vanish for every active m. At a critical point, Q(c)=sum_m(1-m/n)A_m c^m, so sum_i Q(c_i)=0 exactly. Hence some critical point has Re Q(c)<=0. The local harmonic saddle has at least two negative sectors; every component of {Re Q<Re Q(c)} is unbounded by the maximum principle, so by level zero two distinct asymptotic negative root-direction ends lie in one connected component of {Re Q<=0}. Thus every all-degree low tied face has a safe topological connector. Lean checks the derivative-equation rewrite, finite trace cancellation, zero-sum left-half-plane selection, and their composition. The ordinary Newton-identity and harmonic-topology steps are written out in the companion proof. A bounded critical-hub straight-arm probe on 80 deterministic models in degrees 5..9 had zero sampled failures, but sampling is evidence only.

Evidence/status: all_degree_ordinary_analytic_topological_theorem_with_lean_checked_trace_kernel

- [TiedNewtonFaceCriticalTrace.md](problem/TiedNewtonFaceCriticalTrace.md)
- [check_erdos1041_tied_newton_face_critical_trace.py](problem/scripts/check_erdos1041_tied_newton_face_critical_trace.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceCriticalTrace.criticalEquation_div, ErdosProblems.Erdos1041.TiedNewtonFaceCriticalTrace.modelValue_eq_weightedCriticalValue, ErdosProblems.Erdos1041.TiedNewtonFaceCriticalTrace.weightedCriticalValue_sum_eq_zero, ErdosProblems.Erdos1041.TiedNewtonFaceCriticalTrace.exists_nonpositive_critical_value.

### tied_newton_face_negative_paired_critical_trace

Let Q(z)=sum_(m in M) A_m z^m-z^n with 1<=m<n/2, and let c_i be its n-1 critical points with multiplicity. Newton's identities one step beyond the leading zero-trace theorem give sum_i c_i^(n-m)=m(n-m)A_m/n for every active m. Disk tangency forces the complementary coefficient -conj(A_m)z^(n-m), whose total correction at the critical multiset is therefore exactly -m(n-m)|A_m|^2/n<0. On a rational tied face its gap is q(n-2m), so the maximal active low mode arrives first and cannot be cancelled at that order. Consequently either a leading critical value already has negative real part, or every leading real part is zero and the first paired correction is negative at some critical branch: every tied low face has a lexicographically negative saddle. Lean checks the negative norm-square trace and finite lexicographic selector; the exact Newton recurrence is replayed in degrees 5 through 40. At the sharp quintic equality u^3=27/320, x=(2u/3)(1-i sqrt(5)) has leading critical value on level zero and paired correction Re(x^3)=-7/20, exactly calibrating the theorem.

Evidence/status: all_degree_ordinary_analytic_newton_face_theorem_with_lean_checked_finite_kernel

- [TiedNewtonFacePairedTrace.md](problem/TiedNewtonFacePairedTrace.md)
- [check_erdos1041_tied_newton_face_paired_trace.py](problem/scripts/check_erdos1041_tied_newton_face_paired_trace.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFacePairedTrace.pairedCorrection_sum_eq_neg_normSq, ErdosProblems.Erdos1041.TiedNewtonFacePairedTrace.pairedCorrection_re_sum_neg, ErdosProblems.Erdos1041.TiedNewtonFacePairedTrace.exists_lexicographically_negative, ErdosProblems.Erdos1041.TiedNewtonFacePairedTrace.paired_trace_lexicographic_selector.

### adjacent_root_direction_ellipse_metric_cover

Let n>=3, R>0, and let omega_j,omega_(j+1) be adjacent n-th roots of unity bracketing the argument of c with |c|<=R. Then |R omega_j-c|+|R omega_(j+1)-c|<=2R. After rotating, the adjacent foci are (cos(pi/n), plus or minus sin(pi/n)); their major-axis-two ellipse has semiaxes cos(pi/n) and 1. The entire intervening unit-disk sector lies in that ellipse because cos(pi/n)>=1/2. Scaling gives the theorem. Lean checks a division-free formulation: sector data imply the quadratic ellipse inequality, ellipse membership implies the two-focus distance sum, and their composition. Consequently the tied Newton-face straight-arm route no longer needs a separate scattering-defect estimate: once a trace-selected hub c, radius R>=|c|, and two adjacent bracketing contained arms and tails are found, their length is automatically at most 2R. A stationary-polynomial probe on 96 normalized faces in degrees 5 through 8 had zero sampled failures for the combined selector; the sharp quintic equality chart has leading score zero and is made strict only by the already-landed paired correction. Computation is evidence only.

Evidence/status: all_degree_ordinary_euclidean_theorem_with_lean_checked_algebraic_kernel

- [TiedNewtonFaceAdjacentEllipse.md](problem/TiedNewtonFaceAdjacentEllipse.md)
- [check_erdos1041_tied_newton_face_adjacent_hub.py](problem/scripts/check_erdos1041_tied_newton_face_adjacent_hub.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceAdjacentEllipse.sector_ellipse_quadratic, ErdosProblems.Erdos1041.TiedNewtonFaceAdjacentEllipse.bracket_right_inequality, ErdosProblems.Erdos1041.TiedNewtonFaceAdjacentEllipse.ellipse_distance_sum_le_two_mul, ErdosProblems.Erdos1041.TiedNewtonFaceAdjacentEllipse.adjacent_sector_distance_sum_le_two_mul.

### barycentric_disc_envelope_and_descent_disc

Every polynomial lemniscate K_T is exactly the union, over positive product-one weights lambda, of the Euclidean discs (1/n)sum lambda_j|z-a_j|^2<=T^(2/n). In simplex coordinates their centers and squared radii are h(p)=sum p_j a_j and nT^(2/n)G(p)-V(p). For a FIXED point z, the feasible weight set is convex because nT^(2/n)G(p)-sum p_j|z-a_j|^2 is concave; no joint convexity in moving (p,z) is claimed. The inverse-square barycenter B(z)=z-conj(P(z))/S(z) carries the exact descent disc D(B,|z-B|) inside the |f(z)| sublevel and a Pythagorean descent inequality. Interpolating p to a root vertex gives an exact sufficient straight-arm certificate: V+s|a_i-h|^2 <= nT^(2/n)G(p)(1+s/((1-s)p_i))^(1/n) for all s<1. Composing the inverse-square special case with the ALREADY-LANDED geometric-mean theorem exists_two_roots_dist_sum_le_two_mul_geomMean, if S_c r2^2<=2n/(n-1), both nearest spokes lie in K_1, so a least-critical hub gives the sharp Erdos path after scaling. The critical ellipse itself is not new here. Arbitrary critical spokes are exactly refuted by the six-root family (z^2-r^2)(z^4+(6/5)r^2z^2+r^4), for which |f(r/2)|=(327/320)r^6. The remaining diffuse regime is a correlated feasible-disc-chain inequality.

Evidence/status: analytic_complete_deterministic_replay_lean_kernel_checked

- [BarycentricEnvelope.md](problem/BarycentricEnvelope.md)
- [check_erdos1041_barycentric_envelope.py](problem/scripts/check_erdos1041_barycentric_envelope.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.BarycentricEnvelope.inverseSquare_completedSquare, ErdosProblems.Erdos1041.BarycentricEnvelope.linearMixture_variance_factor, ErdosProblems.Erdos1041.BarycentricEnvelope.linearArm_certificate_transport.

### barycentric_nearest_two_sum_scale_consumer

If the first nearest radius r₁ is at most the second radius r₂ and the second radius is at most the geometric-mean scale ρ, Lean proves r₁+r₂≤2ρ. This is the exact scalar consumer for the sharp two-spoke radius budget in the barycentric-envelope route.

Evidence/status: lean_checked_nearest_two_radius_budget_consumer

- [BarycentricEnvelope.lean](problem/BarycentricEnvelope.lean)

claim_boundary: Only the ordered-real inequality is formalized; it does not prove nearest-root selection, geometric-mean control, disc containment, the critical ellipse theorem, or unrestricted Erdős #1041.

### barycentric_two_spoke_scale_transport_consumer

Given the sharp radius budget r₁+r₂≤2ρ and an upper scale bound ρ≤scale, Lean transports the budget to r₁+r₂≤2*scale. This is the scalar scale-transport consumer used after the nearest-two barycentric radius estimate.

Evidence/status: lean_checked_two_spoke_scale_transport

- [BarycentricEnvelope.lean](problem/BarycentricEnvelope.lean)

claim_boundary: Only the ordered-real scale transport is formalized; it does not prove either radius premise, disc containment, nearest-root selection, the global two-root theorem, or unrestricted Erdős #1041.

### critical_ellipse_minimax_finite_contact_reduction

For a fixed root pair and closed ellipse, the moving-hub two-segment level functional attains a minimum. Danskin's theorem and the convex Fermat rule say that at an interior minimizer zero lies in the convex hull of the active contact gradients g=(1-t)(Re(f'/f),-Im(f'/f)); on the boundary one adds the ellipse normal cone. Planar Caratheodory therefore reduces the active set to at most three contacts, each interior segment contact also satisfying Re((a-h)f'/f)=0. Corrected sharp form: two noncritical contacts on the two distinct arms force the arms to be collinear and cannot beat the root chord, but two contacts on the same arm may have opposed normal gradients and remain live. For nonparallel arms, a 2+1 balance of interior tangent contacts forces the singleton contact to be critical; a genuinely three-direction certificate therefore needs the common hub endpoint t=0 or the ellipse boundary normal. At a hub endpoint, the real logarithmic gradient equals S(h-B), where B is the inverse-square barycenter; a unit arm initially enters the certified descent disc centered at B exactly for length 2 max(0,(B-h) dot u). Thus the endpoint KKT sign is equivalent to local descent-disc containment. The stored degree-six, degree-nine, and exact degree-seven hard rows have interior optimized hubs, active common hub endpoints, and full near-active convex-hull residuals about 1e-8; their one-disc certified arm fractions are only about 1.6e-5 to 2.2e-4. The numerical optimization is evidence only. The reduction narrows CE--GM to finite semialgebraic critical-contact, same-arm opposing-pair, hub-endpoint, and boundary-normal systems but does not bound their level by Gcrit.

Evidence/status: corrected_analytic_complete_deterministic_probe_lean_algebra_kernel_checked

- [CriticalEllipseMinimaxStationarity.md](problem/CriticalEllipseMinimaxStationarity.md)
- [check_erdos1041_critical_ellipse_minimax_stationarity.py](problem/scripts/check_erdos1041_critical_ellipse_minimax_stationarity.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.twoContact_balance_opposed, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.logarithmicGradient_dot, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.parallel_of_common_nonzero_normal, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.twoContact_tangent_balance_forces_parallel, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.coefficients_zero_of_independent_balance, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.twoPlusOne_independentNormals_forces_singletonScale_zero, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.inverseSquare_logGradient_dot, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.descentDisc_ray_squaredDifference, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.ray_mem_descentDisc_of_le_projection, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.ray_mem_descentDisc_iff_le_projection, ErdosProblems.Erdos1041.CriticalEllipseMinimaxStationarity.threeContact_balance_residual.

### tied_newton_face_minimum_real_critical_selector_no_go

For Q(z)=-(379/256)z+3z^2-z^5, the critical point c0=1/4 uniquely minimizes the real parts of the four critical values, but no radial cutoff based at c0 can make both the finite positive-real arm and its outward tail lie in {Re Q<=0}. Exactly, Q'(z)=-(4z-1)(320z^3+80z^2+20z-379)/256 and Q(c0)=-47/256. The cubic factor has one real root r in (24/25,1), whose critical value is positive. For its nonreal conjugate roots x+/-iy, Viete gives 2x+r=-1/4 and x^2+y^2=379/(320r); their real critical-value gap above -47/256 reduces to (10460r^2+4245r-13644)/(12800r)>0. Thus c0 is the unique minimum-real hub. Yet Q(2/3)=6677/31104>0, and for every cutoff R the point 2/3 lies either on the arm [1/4,R] or on the tail [R,infinity]. Since every adjacent pair bracketing arg c0 contains the positive-real fifth-root direction, the greedy minimum-real selector cannot supply the adjacent arm-and-tail certificate.

Evidence/status: exact_quintic_selector_refutation_with_lean_checked_rational_kernel

- [TiedNewtonFaceMinimumRealSelectorNoGo.md](problem/TiedNewtonFaceMinimumRealSelectorNoGo.md)
- [check_erdos1041_tied_newton_face_minimum_real_selector_no_go.py](problem/scripts/check_erdos1041_tied_newton_face_minimum_real_selector_no_go.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceMinimumRealSelectorNoGo.derivative_factorization, ErdosProblems.Erdos1041.TiedNewtonFaceMinimumRealSelectorNoGo.real_cubic_criticalValue_gt_quarter, ErdosProblems.Erdos1041.TiedNewtonFaceMinimumRealSelectorNoGo.conjugate_pair_criticalValueRealPart_gt_quarter, ErdosProblems.Erdos1041.TiedNewtonFaceMinimumRealSelectorNoGo.no_safe_positive_real_cutoff.

### tied_newton_face_rational_hub_connector_rescue

The quintic Q(z)=-(379/256)z+3z^2-z^5 that refutes minimum-real plus angular bracketing has a strict rational connector in the same four-ended component. Take h=-3/5+9i/10, R=3/2, u=(57+176i)/185 and v=(-1431+1040i)/1769. The directions are exactly unit and lie strictly in negative fifth-degree asymptotic sectors. All six degree-five Bernstein controls on each arm h to Ru and h to Rv, and all six reciprocal-tail controls on each outward tail, are strictly negative; the largest is below -0.13. The squared arm lengths are 2601/1850 and 33309/88450, each below R^2, hence their sum is strictly below 2R=3. Lean checks the four Bernstein identities, their nonpositive-control consumer, reciprocal-tail transport, and the metric inequality.

Evidence/status: exact_rational_connector_with_lean_checked_bernstein_certificate

- [TiedNewtonFaceRationalHubRescue.md](problem/TiedNewtonFaceRationalHubRescue.md)
- [check_erdos1041_tied_newton_face_rational_hub_rescue.py](problem/scripts/check_erdos1041_tied_newton_face_rational_hub_rescue.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue.armU_nonpos, ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue.armV_nonpos, ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue.tailU_nonpos, ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue.tailV_nonpos, ErdosProblems.Erdos1041.TiedNewtonFaceRationalHubRescue.connector_length_lt_two_mul_radius.

### critical_ellipse_stationary_upper_bound_no_go_and_second_order_filter

Finite-contact KKT reduction is necessary but pointwise KKT upper-bound elimination is false. An exact monic quartic with all roots in the open unit disc has an interior one-contact critical stationary hub strictly above Gcrit, while a different feasible critical hub lies below Gcrit. The bad hub is an exact saddle: both arm directions and their mixed second-order term lie in one negative quadratic cone, and an explicit rational displacement lowers both complete arm maxima. A genuine simple-critical local minimizer with strict hub maxima must satisfy Re(conj(f(h))f''(h)(a-h)(b-h))>=0.

Evidence/status: exact_quartic_no_go_with_lean_checked_algebraic_kernel

- [CriticalEllipseStationaryNoGo.md](problem/CriticalEllipseStationaryNoGo.md)
- [check_erdos1041_critical_ellipse_stationary_no_go.py](problem/scripts/check_erdos1041_critical_ellipse_stationary_no_go.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.CriticalEllipseStationaryNoGo.derivative_factorization, ErdosProblems.Erdos1041.CriticalEllipseStationaryNoGo.badHub_above_geometricMean_squared, ErdosProblems.Erdos1041.CriticalEllipseStationaryNoGo.sameCone_descent_signs.

### barycentric_augmented_target_disc

At every nonroot z and target T>=|f(z)|, the disc centered at B=z-conj(P)/S with squared radius |z-B|^2+n(T^(2/n)-|f(z)|^(2/n))/(|f(z)|^(2/n)S) lies in {|f|<=T}. On a ray its exact reach is alpha+sqrt(alpha^2+sigma^2): strict target slack gives positive reach in every direction, while boundary slack zero stalls exactly at the endpoint KKT sign. The inverse-square barycentric flow satisfies -dF/dt>=2|z'|^2, which controls action but not arclength.

Evidence/status: ordinary_analytic_proof_with_lean_checked_scalar_kernel

- [BarycentricTargetDisc.md](problem/BarycentricTargetDisc.md)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.BarycentricTargetDisc.targetDisc_transport, ErdosProblems.Erdos1041.BarycentricTargetDisc.rayReach_pos_of_targetSlack, ErdosProblems.Erdos1041.BarycentricTargetDisc.boundary_stall, ErdosProblems.Erdos1041.BarycentricTargetDisc.energy_controls_action.

### barycentric_ray_reach_quadratic_identity

For σ²≥0, the ray-reach expression reach=α+√(α²+σ²) satisfies the exact quadratic identity reach²−2α·reach−σ²=0. This is the algebraic root equation used by the augmented target-disc reach calculation.

Evidence/status: lean_checked_ray_reach_quadratic_consumer

- [BarycentricTargetDisc.lean](problem/BarycentricTargetDisc.lean)

claim_boundary: The declaration proves only the quadratic identity; it does not prove reach positivity at strict slack, target-disc containment, boundary-stall behavior, action control, global arclength, or unrestricted Erdős #1041.

### tied_newton_face_nonadjacent_pair_no_go_and_strict_chart

For Q(z)=-(65/27)z+(100/27)z^2-z^5, the critical heights are 8/27,-32/81,4/81,4/81. Thus the unique two-ended negative component joins nonadjacent asymptotic sectors. It has the exact symmetric chart h=1/3,R=1/2,u=(5+12i)/13,v=conj(u): all arm and reciprocal-tail degree-five Bernstein controls are strictly negative, and each squared arm length is 1417/6084 with margin 2/117 below R^2, so total length is strictly below 2R=1. Quantitatively, the same fixed certificate survives A=-65/27+da+i ea, B=100/27+db+i eb whenever max(|da|,|ea|,|db|,|eb|)<=2/3. Exact l1 sensitivity leaves all 24 controls strictly negative; their largest upper control is -29/1053, while the metric margin is unchanged.

Evidence/status: exact_symmetric_quintic_and_quantitative_open_chart_with_lean_checked_bernstein_metric_and_box_kernel

- [TiedNewtonFaceNonAdjacentNoGo.md](problem/TiedNewtonFaceNonAdjacentNoGo.md)
- [check_erdos1041_tied_newton_face_non_adjacent_no_go.py](problem/scripts/check_erdos1041_tied_newton_face_non_adjacent_no_go.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceNonAdjacentNoGo.critical_heights, ErdosProblems.Erdos1041.TiedNewtonFaceNonAdjacentNoGo.armU_nonpos, ErdosProblems.Erdos1041.TiedNewtonFaceNonAdjacentNoGo.tailU_nonpos, ErdosProblems.Erdos1041.TiedNewtonFaceNonAdjacentNoGo.connector_length_lt_two_mul_radius, ErdosProblems.Erdos1041.TiedNewtonFaceNonAdjacentNoGo.open_chart_control_numerators_strict.

### fixed_nearest_pair_cegm_minimal_quartic_no_go

A monic quartic with all roots in the open unit disc has a unique least-critical-value point and a unique nearest-root pair whose two roots lie in distinct components of the Gcrit sublevel. A rational circle lies strictly above a separating rational level T with Gcrit<T<the final merge critical value. Hence no path of any shape, not only no two-arm hub, joins the prescribed pair at level Gcrit. Degrees two and three satisfy the fixed selector, so four is minimal.

Evidence/status: exact_minimal_degree_refutation_with_lean_checked_algebra_and_topological_consumer

- [CEGMQuarticFixedPairNoGo.md](problem/CEGMQuarticFixedPairNoGo.md)
- [check_erdos1041_cegm_quartic_fixed_pair_no_go.py](problem/scripts/check_erdos1041_cegm_quartic_fixed_pair_no_go.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.CEGMQuarticFixedPairNoGo.derivative_factorization, ErdosProblems.Erdos1041.CEGMQuarticFixedPairNoGo.critical_values, ErdosProblems.Erdos1041.CEGMQuarticFixedPairNoGo.separating_threshold, ErdosProblems.Erdos1041.CEGMQuarticFixedPairNoGo.path_crosses_circle.

### tied_newton_face_component_degree_selector_and_critical_hub_rescue

For every component U of {Re Q<0}, the restriction Q|U is a proper surjective map to the left half-plane whose degree equals the number of asymptotic negative ends and equals one plus the total ramification in U. Components are simply connected and their cyclic end sets form a noncrossing partition. On Q=-(379/256)z+3z^2-z^5, the component containing c0=1/4 has passport E(U)={1,2,3,4}, degree 4, ramification 3; the remaining end {0} is a degree-one component. The original critical point c0 strictly joins its true ends omega1,omega4 at R=1/2: six radical Bernstein controls are negative, both tails are negative, and the connector length is (1/2)sqrt(6-sqrt(5))<1. Thus the earlier no-go is angular component mismatch, not a bad hub. The renormalized intrinsic defect is nonincreasing and has a finite limit beta, but beta=0 need not be attained at finite radius. A sufficient horizontal-fibre producer must prove delta<0, a finite-radius connector directly, or non-strict delta<=0 plus equality rigidity.

Evidence/status: ordinary_analytic_component_theorem_with_exact_quintic_checker_and_lean_checked_finite_kernel

- [TiedNewtonFaceComponentSelector.md](problem/TiedNewtonFaceComponentSelector.md)
- [check_erdos1041_tied_newton_face_component_selector.py](problem/scripts/check_erdos1041_tied_newton_face_component_selector.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceComponentSelector.endCount_eq_one_add_ramification, ErdosProblems.Erdos1041.TiedNewtonFaceComponentSelector.renormalizedDefect_antitone, ErdosProblems.Erdos1041.TiedNewtonFaceComponentSelector.armPlus_neg, ErdosProblems.Erdos1041.TiedNewtonFaceComponentSelector.tailPlus_neg, ErdosProblems.Erdos1041.TiedNewtonFaceComponentSelector.connector_length_lt_two_mul_radius.

### tied_newton_face_horizontal_fibre_hubwise_no_go

For Q(z)=15z+5z^2-z^5, c=-1 is a simple negative critical point with Q(c)=-9. The conjugate horizontal-fibre lifts of (-infinity,-9) cross the imaginary axis at +/-i*15^(1/4), continue into the fifth-root sectors exp(+/-2pi i/5), and have renormalized total-length defect delta_Q(-1)>=(sqrt(5)-1)/2>0. Thus horizontal-fibre negativity is false hub by hub even among negative critical points.

Evidence/status: ordinary_analytic_exact_no_go_with_lean_checked_algebra_and_sign_kernel

- [TiedNewtonFaceHorizontalFibreHubwiseNoGo.md](problem/TiedNewtonFaceHorizontalFibreHubwiseNoGo.md)
- [check_erdos1041_tied_newton_face_horizontal_fibre_hubwise_no_go.py](problem/scripts/check_erdos1041_tied_newton_face_horizontal_fibre_hubwise_no_go.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceHorizontalFibreHubwiseNoGo.derivative_factorization, ErdosProblems.Erdos1041.TiedNewtonFaceHorizontalFibreHubwiseNoGo.negative_hub_data, ErdosProblems.Erdos1041.TiedNewtonFaceHorizontalFibreHubwiseNoGo.nonreal_critical_value_kernel, ErdosProblems.Erdos1041.TiedNewtonFaceHorizontalFibreHubwiseNoGo.crossing_below_hub, ErdosProblems.Erdos1041.TiedNewtonFaceHorizontalFibreHubwiseNoGo.projectionDefect_positive.

### tied_newton_face_all_fibre_product_and_velocity_moments

For any monic P of degree n and every simple fibre P(z_j(s))=s^n, the product of all inverse-branch speeds equals product over critical points d_k of s^n/|s^n-P(d_k)|. If Re P(d_k)<=0 for all k, this product is at most one, increases to one, and is independent of branch labels. Moreover the complete signed velocity moments satisfy sum_j z_j^ell z_j'=0 for ell=0,...,n-2 and equal n*s^(n-1) at ell=n-1. For P=Q(c)-Q with c minimizing Re Q on the critical set, the half-plane hypothesis is automatic.

Evidence/status: ordinary_exact_resultant_and_lagrange_theorem_with_lean_checked_half_plane_consumer

- [TiedNewtonFaceFibreProduct.md](problem/TiedNewtonFaceFibreProduct.md)
- [check_erdos1041_tied_newton_face_fibre_product.py](problem/scripts/check_erdos1041_tied_newton_face_fibre_product.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceFibreProduct.normSq_real_sub_ge, ErdosProblems.Erdos1041.TiedNewtonFaceFibreProduct.prod_factorSq_le_one, ErdosProblems.Erdos1041.TiedNewtonFaceFibreProduct.speedProductSq_le_one_of_identity, ErdosProblems.Erdos1041.TiedNewtonFaceFibreProduct.zeroSum_product_countermodel.

### positive_leftmost_fibre_quintic_rational_finite_connector_rescue

The quintic Q(z)=15z+5z^2-z^5 that has strictly positive defect at its unique leftmost critical fibre nevertheless has a strict rational finite connector. With h=-8/5, R=7/5, and u=(-3+4i)/5, v=conj(u), all six finite-arm and all six reciprocal-tail Bernstein controls are strictly negative (repeated by conjugacy), Re(u^5)=237/3125>0, and each squared arm length is 229/125 with margin 16/125 below R^2. The same fixed connector works for every Q_delta(z)=(15+da+i ea)z+(5+db+i eb)z^2-z^5 with max(|da|,|ea|,|db|,|eb|)<=1/6: every perturbed arm and tail Bernstein control remains strictly negative, with smallest certified margin 196/9375. Hence the central connector has length strictly below 2R throughout an explicit four-real-dimensional coefficient chart.

Evidence/status: exact_rational_noncritical_connector_and_four_parameter_open_chart_with_lean_checked_kernel

- [TiedNewtonFacePositiveFibreRationalRescue.md](problem/TiedNewtonFacePositiveFibreRationalRescue.md)
- [check_erdos1041_tied_newton_face_positive_fibre_rational_rescue.py](problem/scripts/check_erdos1041_tied_newton_face_positive_fibre_rational_rescue.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFacePositiveFibreRationalRescue.armU_nonpos, ErdosProblems.Erdos1041.TiedNewtonFacePositiveFibreRationalRescue.tailU_nonpos, ErdosProblems.Erdos1041.TiedNewtonFacePositiveFibreRationalRescue.squared_metric_margin, ErdosProblems.Erdos1041.TiedNewtonFacePositiveFibreRationalRescue.connector_length_lt_two_mul_radius, ErdosProblems.Erdos1041.TiedNewtonFacePositiveFibreRationalRescue.open_chart_control_linear_forms.

### tied_newton_face_block_l1_same_fixture_rational_connector_rescue

For the degree-six polynomial Q(z)=-z^6-3z^2-5997001/10^9 whose unique six-ended negative component exactly refutes pointwise component-block L1 contraction, the rational noncritical hub h=7/10+57i/80, cutoff R=5/4, and the supplied adjacent asymptotic directions give fourteen strictly negative arm/tail Bernstein controls. The connector length is approximately 1.2776427568 and is strictly below 2R. Thus the failed aggregate speed norm is unnecessary cost on its own falsifier.

Evidence/status: exact_rational_noncritical_connector_with_lean_checked_controls_and_metric_budget

- [TiedNewtonFaceBlockL1RationalRescue.md](problem/TiedNewtonFaceBlockL1RationalRescue.md)
- [check_erdos1041_tied_newton_face_block_l1_rational_rescue.py](problem/scripts/check_erdos1041_tied_newton_face_block_l1_rational_rescue.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalRescue.armU_controls_neg, ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalRescue.armV_controls_neg, ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalRescue.tailV_neg_of_fourthPower, ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalRescue.connector_length_lt_two_mul_radius.

### tied_newton_face_block_l1_rational_connector_chart

The same hub, end pair, and cutoff remain valid for P_{a,b}(z)=-z^6+a z^2+b throughout |a+3|<=1/192 and |b+5997001/10^9|<=1/192. Every load-bearing arm, reciprocal-tail, topology, and metric inequality is exact. The true controlling radius is 20577415197/3931840000000, so 1/192 works while 1/191 fails the worst template control.

Evidence/status: exact_two_parameter_strict_chart_with_lean_checked_sensitivity_kernel

- [TiedNewtonFaceBlockL1RationalChart.md](problem/TiedNewtonFaceBlockL1RationalChart.md)
- [check_erdos1041_tied_newton_face_block_l1_rational_chart.py](problem/scripts/check_erdos1041_tied_newton_face_block_l1_rational_chart.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalChart.parameter_signs, ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalChart.reciprocalIntegerRadius_sharp, ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalChart.perturbed_control_neg, ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1RationalChart.worstTailV_derivative_factor.

### tied_newton_face_block_l1_complete_polyhedral_template_cell

For the fixed block-L1 rational connector template in P_{a,b}(z)=-z^6+a z^2+b, strict feasibility is exactly the intersection -1875/128<a<0, b<0, and fourteen affine Bernstein half-planes T_{w,j}+a S_{w,j}+b<0. The lower envelope has eight active facets and seven exact transition points; the earlier 1/192 square is only an inscribed subset.

Evidence/status: exact_complete_fixed_template_cell_with_lean_checked_tail_and_topology_kernel

- [TiedNewtonFaceBlockL1PolyhedralCell.md](problem/TiedNewtonFaceBlockL1PolyhedralCell.md)
- [check_erdos1041_tied_newton_face_block_l1_polyhedral_cell.py](problem/scripts/check_erdos1041_tied_newton_face_block_l1_polyhedral_cell.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1PolyhedralCell.cell_control_neg, ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1PolyhedralCell.aMin_eq_derivative_threshold, ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1PolyhedralCell.tailV_derivative_factor, ErdosProblems.Erdos1041.TiedNewtonFaceBlockL1PolyhedralCell.topology_parameter_signs.

### tied_newton_face_all_degree_even_symmetric_diameter_cone

For every P(z)=-z^(2m)+sum a_k z^(2k)+b with all real a_k<=0 and b<0, P(x)<0 on the complete real axis. Hence opposite asymptotic ends lie in one negative component and [-R,R] is a contained connector of exact length 2R for every R>0. The entire block-L1 family a<=0,b<0 is included.

Evidence/status: ordinary_all_degree_connector_theorem_with_lean_checked_sign_and_metric_kernel

- [TiedNewtonFaceEvenSymmetricDiameter.md](problem/TiedNewtonFaceEvenSymmetricDiameter.md)
- [check_erdos1041_tied_newton_face_even_symmetric_diameter.py](problem/scripts/check_erdos1041_tied_newton_face_even_symmetric_diameter.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceEvenSymmetricDiameter.evenConeValue_neg, ErdosProblems.Erdos1041.TiedNewtonFaceEvenSymmetricDiameter.blockL1_realAxis_neg, ErdosProblems.Erdos1041.TiedNewtonFaceEvenSymmetricDiameter.diameter_length_eq_two_mul.

### tied_newton_face_all_degree_asymmetric_diameter_tube

For P(z)=-z^(2m)+sum a_k z^(2k)+b+sum c_j z^j with a_k<=0, b<0, j<2m, and R>=1, define A_R=sum |c_j|R^j and B_R=sum |c_j|/R^(2m-j). If A_R<-b and B_R<=1, then uniformly P(x)<=b+A_R<0 for every real x. The exact witness -z^6-1+(z+z^3+z^5)/100 has A_2=21/50, B_2=21/3200, and global margin 29/50. Composing this strict sign tube with ReciprocalNewtonExpansion R4 makes the moved-root staple length automatically less than two; only compactified containment remains for actual-polynomial transfer.

Evidence/status: ordinary_all_degree_two_scale_connector_theorem_with_exact_checker_and_lean_checked_domination_kernel

- [TiedNewtonFaceAsymmetricDiameterTube.md](problem/TiedNewtonFaceAsymmetricDiameterTube.md)
- [check_erdos1041_tied_newton_face_asymmetric_diameter_tube.py](problem/scripts/check_erdos1041_tied_newton_face_asymmetric_diameter_tube.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceAsymmetricDiameterTube.inner_domination_neg, ErdosProblems.Erdos1041.TiedNewtonFaceAsymmetricDiameterTube.outer_domination_neg, ErdosProblems.Erdos1041.TiedNewtonFaceAsymmetricDiameterTube.two_region_domination_neg, ErdosProblems.Erdos1041.TiedNewtonFaceAsymmetricDiameterTube.two_region_uniform_upper, ErdosProblems.Erdos1041.TiedNewtonFaceAsymmetricDiameterTube.rationalWitness_innerBudget, ErdosProblems.Erdos1041.TiedNewtonFaceAsymmetricDiameterTube.rationalWitness_outerBudget.

### tied_newton_face_all_degree_complex_rotated_diameter_tube

Let N=2m>0, let |u|=1 with u^N=1, and let Q(z)=-z^N+b+sum_{j<N} c_j z^j with arbitrary complex lower coefficients. For R>=1 and majorants d_j>=|c_j|, put A_R=sum d_j R^j and B_R=sum d_j/R^(N-j). If Re(b)+A_R<0 and B_R<=1, then uniformly Re Q(tu)<=Re(b)+A_R<0 for every real t. Thus the complete rotated diameter lies in the negative-real half-plane preimage. The genuinely complex witness N=4, u=i, R=2, b=-1, c_1=c_3=(1+i)/100, d_1=d_3=1/50 has A_R=1/5, B_R=1/80, and margin 4/5. ReciprocalNewtonExpansion R4 again makes the moved-root staple metric-free; transfer asks only for uniform compactified containment.

Evidence/status: ordinary_all_degree_complex_connector_theorem_with_exact_gaussian_rational_checker_and_lean_checked_domination_kernel

- [TiedNewtonFaceComplexDiameterTube.md](problem/TiedNewtonFaceComplexDiameterTube.md)
- [check_erdos1041_tied_newton_face_complex_diameter_tube.py](problem/scripts/check_erdos1041_tied_newton_face_complex_diameter_tube.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTube.realPart_le_norm, ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTube.rotatedMonomial_re_le, ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTube.uniformMargin_of_twoRegion, ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTube.witnessBudgets.

### tied_newton_face_complex_diameter_actual_polynomial_transfer

Let an even-degree near-Fekete sequence converge in reciprocal-Newton normalization to a strict complex rotated-diameter cell with Re(b)+A_R=-delta<0 and B_R<=1. For all sufficiently large sequence indices, the two actual roots approaching the opposite model directions are joined inside |f|<1 by the equal-radius staple at normalized cutoff 2R, and its length is strictly below two. Containment is proved in three ranges: compact moved-chord convergence preserving delta/2, half-leading mesoscopic domination with two 1/8 error budgets, and a fixed regular-polygon outer collar.

Evidence/status: ordinary_sequential_near_fekete_transfer_theorem_with_exact_checker_and_lean_checked_absorption_kernel

- [TiedNewtonFaceComplexDiameterTransfer.md](problem/TiedNewtonFaceComplexDiameterTransfer.md)
- [check_erdos1041_tied_newton_face_complex_diameter_transfer.py](problem/scripts/check_erdos1041_tied_newton_face_complex_diameter_transfer.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTransfer.compactMargin_absorbs, ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTransfer.mesoscopic_absorbs, ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTransfer.mesoscopic_neg, ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTransfer.outerCollar_absorbs, ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTransfer.transferredStaple_length_lt_two.

### actual_component_merge_tree_area_lower_bound

On every regular k-root component branch C(R), A(R)/R^(2/k) is nondecreasing. Propagating the inverse-derivative leaf masses through actual critical merges gives A_v(R)/(pi R^(2/k_v)) >= Q_v^(2/k_v)/k_v, where Q_v=k_v^k_v product_(a_i in v)1/|f'(a_i)| product_(c internal to v)|f(c)|^m_c. For a complete connected monic degree-k block, the resultant identity gives Q_v=1 and A(R)>=(pi/k)R^(2/k). At any regular forest cut, product_j Q_j=(product_j k_j^k_j)/(n^n product_(|f(c)|>R)|f(c)|^m_c), while summing the component lower bounds against Polya gives sum_j (Q_j^(2/k_j)/k_j)R^(2/k_j-2/n)<=1. A direct proof of branch monotonicity uses boundary Cauchy--Schwarz plus planar isoperimetry. These are actual multiscale forest laws, but the area statement is a lower bound and is not the small-area hypothesis in ConnectedClusterBergman.

Evidence/status: ordinary_exact_actual_component_theorem_with_exact_finite_checker

- [TypeBReturnAssimilation20260826.md](problem/TypeBReturnAssimilation20260826.md)
- [check_erdos1041_type_b_return_assimilation.py](problem/scripts/check_erdos1041_type_b_return_assimilation.py)

### arbitrary_modulus_root_ray_product_contraction

For f(z)=product_j(z-a_j), |a_j|<=1, p_m=sum_j a_j^m, and 0<=t<1, set E(t)=sum_(m>=1)t^m|p_m|^2/m, D_0=sum_j(1-|a_j|^2), and D_t=sum_i(1-t^2|a_i|^2). The ordered-pair factor identity gives product_i|f(t a_i)|=exp(-E(t)) product_(i,j)sqrt(1-X_ij), where X_ij=(1-|a_j|^2)(1-t^2|a_i|^2)/|1-t a_i conjugate(a_j)|^2. Consequently min_i|f(t a_i)|<=exp(-E(t)/n-D_0 D_t/(2n(1+t)^2))<=1. If at least one root is interior, the final inequality is strict for every t<1. Equality in the original product contraction occurs only when all roots lie on the unit circle. The good index may still move with t, so this quantitative open-cover margin does not produce a fixed spoke, compatible pair, or joining chord.

Evidence/status: ordinary_exact_all_degree_theorem_with_quantitative_strict_defect_and_exact_symbolic_rational_kernels

- [TypeBReturnAssimilation20260826.md](problem/TypeBReturnAssimilation20260826.md)
- [check_erdos1041_type_b_return_assimilation.py](problem/scripts/check_erdos1041_type_b_return_assimilation.py)

claim_boundary: This is a quantitative moving-index theorem. It does not provide a continuous or fixed index, two compatible outer tails, a contained joining chord, a common component, a COVER carrier, common-ancestry compensation, or unrestricted Erdős 1041.

### critical_arc_product_admissibility_quantifier_firewall

For simple generic critical points c, write v_c=f(c), L(c) for the canonical descending inverse-ray edge, A={c:|v_c|<1}, B={c:|v_c|>=1}, and q_c=L(c)/(2|v_c|^(1/n)). The proposed but UNPROVED all-critical inequality product_c L(c)<=2^(n-1)(product_c|v_c|)^(1/n) is exactly equivalent by the resultant identity to product_c L(c)<=(2^(n-1)/n)|Delta|^(2/n). It does not by itself prove Erdős 1041: the exact scalar data n=3, (|v_A|,L_A)=(1/16,3), (|v_B|,L_B)=(8,1) satisfy product|v|<1 and the proposed global length product inequality, yet the only short edge is inadmissible. The genuinely target-deciding conditional is product_(c in A)L(c)<=2^|A|(product_(c in A)|v_c|)^(1/n), which forces some admissible L(c)<2. Equivalently, the global conjecture becomes sufficient if product_(c in B)q_c>=1. No actual-polynomial counterexample to the global conjecture and no proof of either product premise is claimed.

Evidence/status: ordinary_exact_conditional_reduction_with_exact_rational_inference_no_go

- [TypeBReturnAssimilation20260826.md](problem/TypeBReturnAssimilation20260826.md)
- [check_erdos1041_type_b_return_assimilation.py](problem/scripts/check_erdos1041_type_b_return_assimilation.py)

claim_boundary: Exact: resultant normalization, admissible-subproduct sufficiency, compensation implication, and scalar failure of the all-index-to-admissible-index deduction. Unproved: the global critical-arc product inequality, the admissible subproduct inequality, and the inadmissible compensation premise. The scalar countermodel is not asserted to be polynomial-realizable.

### admissible_critical_arc_product_cellwise_log_psh_reduction

On any wall-free root-configuration cell with simple roots and critical points, nonzero critical values, fixed admissible critical set A, and fixed descending-arm continuation combinatorics, log Q_A=sum_(c in A)[log L(c)-log 2-(1/n)log|f(c)|] is plurisubharmonic. The proof packages the two holomorphic inverse-arm derivatives into the Banach space L1 direct-sum_1 L1, observes L(c) is its norm, uses that log of a holomorphic Banach-valued norm is psh, and subtracts the pluriharmonic critical-value term. Hence the target-deciding admissible product has no nonconstant generic interior maximum: its supremum moves to a root boundary, an admissibility wall, a saddle-connection wall, or a root/critical collision. Four guarded holomorphic quintic disks satisfy the sub-mean law, and a bounded 78-row unit-circle terminal search has no product above one (maximum 0.910417681941); these numerical rows are falsifier evidence only.

Evidence/status: ordinary_exact_cellwise_psh_reduction_with_guarded_quintic_falsifier_search

- [AdmissibleCriticalArcProductPshReduction.md](problem/AdmissibleCriticalArcProductPshReduction.md)
- [check_erdos1041_admissible_product_psh.py](problem/scripts/check_erdos1041_admissible_product_psh.py)

claim_boundary: Exact: cellwise logarithmic plurisubharmonicity and the per-cell terminal-stratum reduction. Numerical only: four quintic sub-mean rows and the bounded unit-circle terminal search. The psh germ is not asserted to extend through a saddle or admissibility wall; a dilation preserves fixed-label q factors but can change the admissible set. The admissible product inequality, every terminal-stratum certificate, degree five, and unrestricted Erdős 1041 remain open.

### saddle_wall_two_hub_metric_compression

On a simple saddle-connection wall let the lower saddle have outgoing arm lengths A,B, and let X be the upper saddle-to-lower-saddle stem plus the upper saddle's unaffected descending arm. The lower hub path has length A+B and the wall can continue the upper lift through either lower branch, with lengths X+A and X+B. Exact algebra gives (A+B) min(X+A,X+B) <= (A+B+X)^2/2, with slack [X^2+(A+B)|A-B|]/2; it also gives (A+B)sqrt((X+A)(X+B)) <= (A+B+X)^2/2 for the two one-sided continuations. If beta and gamma are the lower and upper critical-value moduli, the two normalized admissible-product factors therefore satisfy q_low q_high <= T^2/[8(beta gamma)^(1/n)], T=A+B+X. Thus T<=2sqrt(2)(beta gamma)^(1/(2n)) is one scalar sufficient certificate for the two-hub wall block.

Evidence/status: ordinary_exact_terminal_stratum_reduction_with_exact_fraction_replay

- [SaddleWallPairCompression.md](problem/SaddleWallPairCompression.md)
- [check_erdos1041_saddle_wall_pair_compression.py](problem/scripts/check_erdos1041_saddle_wall_pair_compression.py)

claim_boundary: Exact: the simple-wall arm-choice algebra, its explicit nonnegative slack, the geometric-mean two-sided form, the normalized sufficient total-length threshold, and the shape-retaining equivalent T^2-X^2-(A+B)|A-B|<=8(beta gamma)^(1/n). Imported: the standard inverse-ray decomposition when an upper lift meets one simple lower saddle. The sufficient total-length threshold is now exactly refuted as a universal polynomial-wall claim by symmetric_two_level_wall_admissible_product_and_scalar_no_go. Unproved: the shape-retaining condition for general walls, longer saddle spines, remaining admissible factors, either nearby one-sided cell, and every other terminal stratum. AP, degree five, and unrestricted Erdos 1041 remain open.

### symmetric_two_level_wall_admissible_product_and_scalar_no_go

For every m>=2 and 0<b<a<1, f(z)=(z^m-a^m)(z^m+b^m) has a central critical point of multiplicity m-1 at level beta=a^m b^m and m simple outer critical points at level gamma=((a^m+b^m)/2)^2, all on one descending ray. The limiting central merge edges have length 2b and every outer edge has length a+b. With r=b/a and n=2m, the complete admissible product is Q_m(r)=r^((m-1)/2)(1+r)^m/[2^(m-1)(1+r^m)]<=r^((m-1)/2)<=1 by midpoint convexity, strict for r<1 with equality only at the regular 2m-gon collision. In the quartic subfamily the former scalar total-three-arm threshold is false at r=9/10 by exact fourth-power gap 5836/625, although the true lower/upper normalized pair square is 3249/3620<1 with slack 371/3620. The exact general wall condition retains shape slack: T^2-X^2-(A+B)|A-B|<=8(beta gamma)^(1/n).

Evidence/status: ordinary_exact_subordinate_all_even_degree_ap_family_and_scalar_no_go_with_lean_source_pending_focused_validation

- [SymmetricTwoLevelWallFamily.md](problem/SymmetricTwoLevelWallFamily.md)
- [check_erdos1041_symmetric_two_level_wall.py](problem/scripts/check_erdos1041_symmetric_two_level_wall.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.SymmetricTwoLevelWall.quartic_pair_square_le_one, ErdosProblems.Erdos1041.SymmetricTwoLevelWall.quartic_full_product_square_le_one, ErdosProblems.Erdos1041.SymmetricTwoLevelWall.quartic_three_arm_threshold_false.

claim_boundary: Exact ordinary mathematics: critical points and levels, inverse-ray arm geometry, the all-even-degree AP formula and power-mean bound, equality case, quartic scalar-threshold counterexample, and shape-slack diagnosis. The Lean source states the quartic polynomial slack and rational no-go kernel, but focused validation was terminated by the canonical build firewall before any theorem diagnostic and is pending. The parent path conclusion for this centred-trinomial family was already proved by cyclic_trinomial_fiber_case_all_degrees; the new positive claim is AP on this structured wall. It does not prove AP on general walls, degree five, or unrestricted Erdos 1041.

### deep_low_critical_two_spoke_and_discriminant_class

Let c be a non-root critical point of a degree-n polynomial p and let a_1,a_2 be its two nearest roots. Critical balance gives |a_2-c|/|a_1-c|<=n-1. Direct factorization along the two segments yields a common amplification bound n*2^(n-2). Hence |p(c)|<=1/(n*2^(n-2)) puts both straight spokes inside {|p|<=1}; for roots in the closed unit disk their total length is at most 2 by GlobalCriticalTwoNearestBudget. Consequently the normalized discriminant class D<= (n*2^(n-2))^(-(n-1)) satisfies the closed theorem, and circumradius scaling proves the original strict theorem for open-disk roots in this class.

Evidence/status: ordinary_exact_all_degree_subcase_with_deterministic_scalar_regression_and_lean_scalar_validation_pending_capacity

- [LowCriticalTwoRootReduction20260826.md](problem/LowCriticalTwoRootReduction20260826.md)
- [check_erdos1041_low_critical_two_root_reduction.py](problem/scripts/check_erdos1041_low_critical_two_root_reduction.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.LowCriticalTwoRootReduction20260826.secondNearest_segment_envelope, ErdosProblems.Erdos1041.LowCriticalTwoRootReduction20260826.nearest_segment_envelope_le_common_budget.

### root_hull_metric_projection_contraction

Metric projection pi_K onto the convex hull K of the roots satisfies |pi_K(z)-a_j|<=|z-a_j| for every root, hence |f(pi_K(z))|<=|f(z)|, and is 1-Lipschitz. Every admissible path may therefore be confined to the root hull without increasing length or polynomial modulus.

Evidence/status: ordinary_exact_all_degree_geometric_reduction

- [TypeBReturnAssimilation20260826.md](problem/TypeBReturnAssimilation20260826.md)

### proper_component_capacity_gap

Let U be a regular component of {|f|<t} containing k<n roots of a monic degree-n polynomial. Every exterior root preimage xi_j satisfies |xi_j|>(n+1)/(n-1). Hence cap(closure U)<t^(1/n)((n-1)/(n+1))^((n-k)/n) and Area(U)/pi<t^(2/n)((n-1)/(n+1))^(2(n-k)/n). This yields the valid connected-cluster threshold q_U<=tanh(((n-1)/(n+1))^(-2(n-k)/n))^(k/2), and the corresponding explicit first-merge COVER criterion. The exterior boundary parameter cannot be identified with the interior Blaschke parameter without controlling conformal welding.

Evidence/status: ordinary_exact_component_theorem_with_lean_checked_scalar_kernel_and_exact_threshold_audit

- [ProperComponentCapacityGap.md](problem/ProperComponentCapacityGap.md)
- [check_erdos1041_proper_component_capacity_gap.py](problem/scripts/check_erdos1041_proper_component_capacity_gap.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.ProperComponentCapacityGap.exterior_poisson_peak_identity, ErdosProblems.Erdos1041.ProperComponentCapacityGap.exterior_radius_gt_degree_gap, ErdosProblems.Erdos1041.ProperComponentCapacityGap.degree_gap_mem_unit_interval.

### charged_lifetime_allocation_no_go_consumer

A strict uncharged slack always admits strictly positive node and leaf charges that still fit the charged budget; upper bounds on the actual node and leaf charges preserve that strict inequality; and for every positive component size k and requested margin, a positive energy E can be chosen with k*E/2 below the margin. Thus a scalar charged-lifetime ceiling alone cannot force a positive energy floor.

Evidence/status: lean_checked_charged_lifetime_allocation_no_go_consumer

- [ChargedLifetimeAllocationNoGo.lean](problem/ChargedLifetimeAllocationNoGo.lean)

claim_boundary: This is an exact real-algebra allocation obstruction. It does not assert that actual polynomial energies are freely prescribable, identify the analytic attachment functional, prove a lower energy bound, establish a weighted-tree selector, supply an unrestricted polynomial construction, or close unrestricted Erdős #1041.

### quartic_young_energy_fraction_lt_half_consumer

For the exact quartic witness, the Young-energy fraction is 144/769, strictly below the half-energy threshold 1/2. This isolates the rational strict inequality that drives the quartic local deficit before its exact positive margin is recorded separately.

Evidence/status: lean_checked_quartic_young_energy_fraction_consumer

- [AttachmentCoupledEnergySelector20260826.lean](problem/AttachmentCoupledEnergySelector20260826.lean)

claim_boundary: This is an exact rational inequality for one quartic witness. It does not prove the weighted-tree selector inequality, establish the full energy interpretation beyond the source analysis, bound the restored common-ancestry factor, prove a safe path or arm, or close unrestricted Erdos #1041.

### quartic_terminal_inner_ratio_gt_four_consumer

For the exact quartic witness, the terminal inner ratio is 144/25, and it is strictly greater than 4. This isolates the rational endpoint margin used by the attachment-coupled energy obstruction.

Evidence/status: lean_checked_quartic_terminal_inner_ratio_consumer

- [AttachmentCoupledEnergySelector20260826.lean](problem/AttachmentCoupledEnergySelector20260826.lean)

claim_boundary: The result is only an exact rational inequality for the quartic witness. It does not prove the weighted-tree selector inequality, establish the full quartic energy interpretation beyond the separately documented source, bound the restored common-ancestry factor, prove a safe path or arm, or close unrestricted Erdős #1041.

### quartic_young_energy_deficit_consumer

For the exact quartic Young-energy fraction 144/769, the deficit from the half-energy threshold is exactly 1/2 - 144/769 = 481/1538. This records a positive rational margin rather than only the qualitative strict inequality.

Evidence/status: lean_checked_quartic_young_energy_deficit_consumer

- [AttachmentCoupledEnergySelector20260826.lean](problem/AttachmentCoupledEnergySelector20260826.lean)

claim_boundary: The result is only an exact rational arithmetic identity for the quartic witness. It does not prove the weighted-tree selector inequality, establish the quartic energy interpretation beyond the separately documented source, bound the restored common-ancestry factor, prove a safe path or arm, or close unrestricted Erdős #1041.

### common_ancestry_discount_exact_consumer

For real β, w, A, and B, the common-ancestry discount factorizes exactly: β*w*exp(-2*(A+B)) = (β*exp(-2*B))*(w*exp(-2*A)). This isolates the common ancestry contribution in the singleton entrance-charge currency after the pair's tree distance has canceled it.

Evidence/status: lean_checked_common_ancestry_factorization_consumer

- [AttachmentCoupledEnergySelector20260826.lean](problem/AttachmentCoupledEnergySelector20260826.lean)

claim_boundary: The result is only an algebraic real-exponential factorization. It does not prove the weighted-tree selector inequality, bound the restored common factor below, establish a polynomial root or merge-tree budget, prove a safe path or arm, or close unrestricted Erdős #1041.

### attachment_coupled_energy_selector_and_transport_ceiling

For a rooted weighted leaf tree, C=sum_u x_u E_u(W-E_u), pair distance d(i,j) counting exactly the separating edges, and D=1-sum_i(w_i/W)^2, every lambda>0 admits distinct leaves with w_i w_j exp(-lambda d(i,j)) >= [D W^2/(k(k-1))] exp(-2 lambda C/(D W^2)) >= G^2 exp(-2 lambda C/(k(k-1)G^2)); the constants are sharp on equal-weight equal-edge stars. At the selected lowest common merge this gives the corresponding sharp two-term discounted sum. However exact entrance-energy propagation shows that transporting this local quantity into singleton charge restores the common factor beta_v^(2/k_v) exp(-2B_a(v)); the current abstract ledgers do not bound that factor below.

Evidence/status: ordinary_exact_weighted_tree_theorem_with_actual_polynomial_no_go_exact_checker_and_lean_scalar_kernel_pending_capacity

- [AttachmentCoupledEnergySelector20260826.md](problem/AttachmentCoupledEnergySelector20260826.md)
- [check_erdos1041_attachment_coupled_energy_selector.py](problem/scripts/check_erdos1041_attachment_coupled_energy_selector.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.quartic_terminal_inner_ratio_gt_four, ErdosProblems.Erdos1041.quartic_young_energy_fraction_lt_half, ErdosProblems.Erdos1041.quartic_young_energy_deficit, ErdosProblems.Erdos1041.common_ancestry_discount_exact.

### critical_spoke_synchronized_reciprocal_sweep

At a non-root critical point c put u_i=1/(a_i-c), S_m=sum_i u_i^m, and z_i(r)=c+r conjugate(u_i). Whenever r max_i|u_i|^2<1, sum_i log|p(z_i(r))/p(c)|=-sum_(m>=1)r^m|S_m|^2/m<=0, so the product of the sampled spoke ratios is at most one and at every synchronized reciprocal radius at least one sampled spoke point is safe. The Gaussian-integer reciprocal-balanced cubic u=(-3-2i,3i,3-i) has S_2=4+6i and exactly one initially descending spoke, proving that the moment mechanism cannot universally select a pair.

Evidence/status: ordinary_exact_analytic_theorem_with_gaussian_integer_scope_witness_and_independent_checker

- [CriticalSpokeMomentSweep20260826.md](problem/CriticalSpokeMomentSweep20260826.md)
- [check_erdos1041_critical_spoke_moment_sweep.py](problem/scripts/check_erdos1041_critical_spoke_moment_sweep.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.critical_spoke_witness_first_sign, ErdosProblems.Erdos1041.critical_spoke_witness_second_sign, ErdosProblems.Erdos1041.critical_spoke_witness_third_sign.

### orlicz_upper_bound_from_lifetime_consumer

Given positive size, the exact identity lifetime=size*phi, and a lifetime upper bound budget, Lean proves phi≤budget/size. This is the ordered-algebra consumer that translates an attachment-lifetime ceiling into the corresponding Orlicz-transform ceiling.

Evidence/status: lean_checked_lifetime_to_orlicz_upper_bound

- [AttachmentAgeLifetimeOrlicz.lean](problem/AttachmentAgeLifetimeOrlicz.lean)

claim_boundary: Only the real-algebra division step is formalized; it does not identify the analytic integral transform, prove the exact identity or convexity for a concrete attachment model, establish arbitrary-polynomial realizability, or close unrestricted Erdős #1041.

### weighted_orlicz_chain_consumer

Given positive total size, the analytic lower bound lifetime ≥ totalSize * Phi(weightedAge), and monotonicity Phi(totalAge) ≤ Phi(weightedAge), Lean proves totalSize * Phi(totalAge) ≤ lifetime. This is the exact scalar consumer that converts the weighted analytic lower bound into the floor-value chain bound. The child-size relation 2*totalAge ≤ weightedAge is upstream analytic context and is not consumed by this declaration.

Evidence/status: lean_checked_analytic_consumer_bridge

- [AttachmentAgeLifetimeOrlicz.lean](problem/AttachmentAgeLifetimeOrlicz.lean)

claim_boundary: The declaration checks only the ordered real-algebra consumer after the analytic transform and monotonicity comparison are supplied; it does not consume the child-size relation. It does not formalize the integral identity, prove the analytic hypotheses for arbitrary polynomial components, or close the unrestricted Erdős #1041 path theorem.

### second_age_tail_lower_consumer

Given 1<count and the tail inequality (count-1)*secondAge≤total, Lean proves secondAge≤total/(count-1). This is the exact ordered-age consumer for the sharp two-root threshold in the #1041 attachment-age route.

Evidence/status: lean_checked_second_age_threshold_consumer

- [AttachmentAgeLifetimeOrlicz.lean](problem/AttachmentAgeLifetimeOrlicz.lean)

claim_boundary: Only the elementary ordered-age division step is formalized; it does not prove the root-summed age/product identity, analytic attachment hypotheses, arbitrary-polynomial realization, or unrestricted Erdős #1041.

### orlicz_no_uniform_linear_lower_boundary

For an Orlicz transform sublinear at zero, Lean proves that no positive universal constant can lower-bound the transform linearly on all positive ages. This records the exact negative boundary for any attempted age-to-Orlicz linear shortcut in the #1041 route.

Evidence/status: lean_checked_negative_orlicz_boundary

- [AttachmentAgeLifetimeOrlicz.lean](problem/AttachmentAgeLifetimeOrlicz.lean)

claim_boundary: Only the ordered-real contradiction is formalized; it does not identify the analytic transform, prove sublinearity for a particular integral, or close unrestricted Erdős #1041.

### exterior_fibre_capacity_gap_scalar_kernel

For positive n and nonnegative m,p, the fibre reciprocal inequality m/n < (1-p)/(1+p) implies p < (n-m)/(n+m). Substituting m=n-k identifies the sharp constant k/(2*n-k), and for 0<k<n Lean proves that this constant lies strictly between zero and one. This is the exact scalar kernel used by the exterior-fibre capacity gap argument.

Evidence/status: lean_checked_analytic_consumer_bridge

- [ExteriorBlaschkeFibreCapacityGap.lean](problem/ExteriorBlaschkeFibreCapacityGap.lean)

claim_boundary: The declarations check only the rational real-algebra kernel and its positivity/upper bound. They do not formalize the finite-Blaschke harmonic-measure fibre identity, identify matching interior and exterior circle parameters, prove the analytic reciprocal-derivative estimate, or close unrestricted Erdős #1041.

### fixed_block_quadratic_budget_equivalence

On a fixed finite sheet block with normalized sheet-time measure, the infimum over positive lifetime weights lambda of A(lambda)E(lambda) is exactly the square of the average complete-lift length. Hence a limsup quadratic budget at most four is equivalent to an average whole-lift length bound at most two. If M and F are the moved and fixed sheets, a whole-block bound sum_B L<=C(|M|+|F|)-Delta gives the sharp quantitative compensation sum_M L<=C|M|+S_F-Delta and min_M L<=C+(S_F-Delta)/|M|, where S_F=C|F|-sum_F L is the unpaid fixed-sheet slack. Thus Delta>S_F is the exact strict-shortening interface; the earlier fixed-average-at-least-C criterion is only the Delta=0 zero-slack special case. The three-sheet transposition at Delta=0 attains the bound exactly, so its coefficient and denominator are sharp. Once a moved lift is selected inside the closed unit lemniscate, convex projection and compactness give a root-to-root path of length at most two.

Evidence/status: ordinary_exact_variational_equivalence_with_sharp_quantitative_fixed_slack_compensation_and_lean_kernel_pending_low_disk_validation

- [FixedBlockQuadraticBudgetEquivalence.md](problem/FixedBlockQuadraticBudgetEquivalence.md)

claim_boundary: The variational identity, conditional moved-sheet consumer, sharp quantitative fixed-slack compensation inequality, and sharp three-sheet equality model are proved by ordinary exact mathematics and replayed in exact rational finite models. FixedBlockCompensation.lean authors the finite allocation kernel, but its focused validation is deferred by the live low-disk guard and no Lean authority is claimed yet. No source-current theorem proves that a strict grouped-cluster, Bergman, circumradius, or Fekete margin dominates S_F/|M|, or constructs the fixed safe moved-sheet block with the required compensated average-length budget. That margin comparison is now the first unsupported downstream implication; unrestricted Erdős 1041 remains open.

### separate_critical_contour_no_go

For a ray-separated degree-k component, a thin lollipop contour around the fully resolved radial critical-value star has full-cycle monodromy, but its average complete-lift length has liminf at least (2/k) sum_c L(c). If every pairwise root chord exceeds k/(k-1), this lower bound exceeds two. Generic normalized cubics near an equilateral triangle and quartics near a square satisfy that strict criterion, so the canonical separate-slit derangement construction misses the fixed-block budget on actual hard-class examples.

Evidence/status: ordinary_exact_negative_result_for_resolved_critical_star_monodromy

- [SeparateCriticalContourNoGo.md](problem/SeparateCriticalContourNoGo.md)

claim_boundary: The planar covering and length-liminf theorem is proved by ordinary exact mathematics. It rules out only contours that separately resolve and circle every radial critical slit. It does not rule out grouping near-coincident critical values before contouring them, fixed safe moved blocks, fixed-sheet compensation, combined charge, COVER, FP--GM, or unrestricted Erdős 1041.

### grouped_critical_cluster_monodromy

For f_0(z)=z^n-r^n, 0<r<1, the value-plane lollipop that stems to and circles the whole critical-value cluster at radius q has full-cycle monodromy and every complete lift has exact length 2r-2(1-pi/n)q^(1/n). In every degree q can be chosen with the lollipop inside the open unit value disk and the lift length below two. The fixed loop, full-cycle monodromy, and strict individual lift bounds persist throughout an open coefficient neighbourhood of f_0, proving Erdős 1041 on an all-degree neighbourhood of every strict regular polygon.

Evidence/status: ordinary_exact_all_degree_local_positive_result

- [GroupedCriticalClusterMonodromy.md](problem/GroupedCriticalClusterMonodromy.md)

claim_boundary: The formula and coefficient-neighbourhood theorem are proved by ordinary exact mathematics. The neighbourhood is qualitative and shrinks as r tends to one; no source-current theorem converts the topology-sensitive discriminant lower bound into enough quantitative cluster control. The theorem also does not directly cover configurations whose full critical-value cluster crosses the unit value circle. Partial admissible clusters, complementary Bergman allocation, combined charge, COVER, FP--GM, and unrestricted Erdős 1041 remain open.

### partial_critical_cluster_monodromy

A value-plane Jordan contour enclosing exactly a connected edge subtree E of a ray-separated sheet tree has monodromy equal to one full cycle on the incident sheet block B and fixes the complement. Therefore an average complete-lift bound at most two on B conditionally solves the target by the fixed-block theorem. On the pinned degree-six and degree-nine near-Fekete witnesses, deterministic continuation finds unit-value-disk circles enclosing exactly the two and three admissible critical values, moved cycles of sizes three and four, and moved-block means about 1.84327 and 1.63875; the largest individual moved lift exceeds two in both rows.

Evidence/status: ordinary_exact_conditional_subtree_cycle_with_pinned_candidate_evidence

- [PartialCriticalClusterMonodromyLab.md](problem/PartialCriticalClusterMonodromyLab.md)

claim_boundary: The subtree-cycle theorem and conditional consumer are ordinary exact mathematics. The two witness length rows are floating-point candidate evidence with coarse/fine and geometric separation guards, not interval-certified instance proofs. No universal partial-cluster average bound or unrestricted Erdős 1041 proof is claimed.

### partial_cluster_preimage_perimeter_identity

For a proper degree-d polynomial preimage component W over a Jordan domain Q, the sum of the d complete lifted lollipop lengths is exactly 2 Lambda(alpha,W)+P(W), where Lambda is the total lifted access-stem length and P(W) is the boundary perimeter. Thus the partial-cluster moved-block criterion is exactly 2 Lambda+P(W)<=2d, and strict value-disk containment with 2 Lambda+P(W)<2d closes the parent theorem through the occupied subtree-cycle and fixed-block consumers.

Evidence/status: ordinary_exact_analytic_identity_with_exact_rational_regression

- [PartialClusterPreimagePerimeterIdentity.md](problem/PartialClusterPreimagePerimeterIdentity.md)

claim_boundary: The preimage-perimeter identity and its connected-subtree consumer are ordinary exact complex analysis. The exact rational checker verifies permutation bookkeeping and the regular-polygon specialization. No source-current theorem proves existence of an admissible isolating pair (Q,alpha) satisfying the strict inequality for every polynomial, nor the complementary Bergman/COVER dichotomy; unrestricted Erdős 1041 remains open.

### singleton_cluster_limit_equivalence

For an admissible simple critical point c, shrinking singleton critical-value circles have mean complete-lollipop length converging to the canonical two-arm inverse-ray length L(c). Hence any admissible c with L(c)<2 yields a strict partial-cluster certificate, making the componentwise combined-charge producer the singleton specialization of the preimage-perimeter route while preserving multi-critical clusters as a genuine fallback.

Evidence/status: ordinary_exact_singleton_limit_with_candidate_selection_evidence

- [AdaptiveClusterSelectionLab.md](problem/AdaptiveClusterSelectionLab.md)

claim_boundary: The singleton limit is ordinary exact local complex analysis. The 254-configuration adaptive selector sweep is deterministic floating-point candidate evidence only. It does not prove min_c L(c)<=2, interval-certify the sweep, establish the componentwise combined-charge inequality, or solve unrestricted Erdős 1041.

### scale_weighted_arithmetic_charge_bridge

For each nontrivial level-one component C, let A_C be its critical edges, s_c=|f(c)|^(1/n), and q(c)=L(c)/(2s_c). The componentwise arithmetic inequality |A_C|^(-1) sum_(c in A_C)q(c)<=1 implies the global target-deciding admissible product inequality by componentwise AM-GM and multiplication. Using 2R-L(c)=D_c+K_c, it is exactly equivalent on each component to sum_(c in A_C)(D_c+K_c)/(2s_c)>=sum_(c in A_C)(R/s_c-1). This strengthens the former global AQ/WSC candidate by forbidding cross-component compensation while retaining the full-root circumradius and external-root coupling.

Evidence/status: ordinary_exact_componentwise_am_gm_reduction_with_deterministic_floating_falsifier_survival

- [AdmissibleCriticalArcProductLab.md](problem/AdmissibleCriticalArcProductLab.md)

claim_boundary: The componentwise-to-global AM-GM implication and CAQ iff CWSC equivalence are ordinary exact algebra. CAQ/CWSC itself is UNPROVED. The deterministic floating checker found zero violations across 273 maximal admissible components in the 270-configuration base corpus and zero violations across 801 components in the independent fixed-seed 800-configuration stress corpus; the largest component means were 0.995680941647 and 0.999478637196. The simpler rule pairing every q(c)>1 with the next higher critical scale is numerically false on 89 base and 62 stress overspends. These computations are candidate/falsifier evidence only and do not interval-certify CAQ, prove CWSC, or solve unrestricted Erdos 1041.

### cut_scaled_subtree_arithmetic_potential

For an admissible merge node v, let beta_v be its critical modulus, b_v the modulus of its next admissible ancestor or the level-one cut, T_v the complete admissible rooted merge subtree below v, N_v=|T_v|=k_v-1, and q(u)=L(u)/(2 beta_u^(1/n)). The cut-scaled subtree assertion CSTA is Phi_v=(b_v^(1/n)/N_v) sum_(u in T_v)q(u)<=1. At a maximal level-one component it is exactly CAQ, and at a cherry it is exactly the occupied factor bound h_v<=1. If delta_v=N_v(1-Phi_v), x_v=(beta_v/b_v)^(1/n), and G_v=L(v)/2+N_v-1-N_v x_v, then exact algebra gives delta_v=x_v^(-1)(sum_i delta_(v_i)-G_v), where v_i are the admissible internal children. The graft debt further has the exact positive-liability decomposition C_v=x_v^N_v-N_v x_v+N_v-1=(1-x_v)^2 sum_(j=0)^(N_v-2)(N_v-1-j)x_v^j>=0 and O_v=max(0,L(v)/2-x_v^N_v)=x_v^N_v max(0,h_v-1), with G_v<=C_v+O_v. Therefore PGLS, sum_i delta_(v_i)>=C_v+O_v, is a stronger sufficient recursive step whose two liabilities are respectively the quadratic cut-scale convexity cost and positive multiplicative node overspend.

Evidence/status: ordinary_exact_recursive_reduction_with_deterministic_floating_falsifier_survival

- [AdmissibleCriticalArcProductLab.md](problem/AdmissibleCriticalArcProductLab.md)

claim_boundary: The CSTA endpoint identifications, CSTR recurrence, convexity factorization, and implication PGLS=>the needed graft inequality are ordinary exact algebra. CSTA and PGLS are UNPROVED, so this row does not prove CAQ/CWSC or unrestricted Erdos 1041. The naive unscaled assertion average_(u in T_v)q(u)<=1 is numerically false on the pinned near-tie quartic singleton. CSTA has zero violations across 1,252 base rooted subtrees and 4,288 independent fixed-seed stress rooted subtrees. PGLS likewise has zero violations; the largest measured positive-liability/child-slack ratios are 0.857114446951 and 0.960626426260. A fixed half-slack allocation is false: the convexity/overspend halves fail on 32/0 base nodes and 96/4 stress nodes. These computations are deterministic floating candidate/falsifier evidence only, not interval certification or proof authority.

### universal_radial_contour_sharp_criterion_no_go_2026_08_28

For P(z)=z^2-r^2 with r=5/6, the componentwise radial-contour expression proposed in return 002 is strictly greater than four. Before the two roots merge, the two one-root level loops have total perimeter at least 4(sqrt(r^2+s)-sqrt(r^2-s)); after merger the component perimeter is at least 4r. Hence the proposed expression is at least 4r+(4r/pi)J, where J=2sqrt(2)-2log(1+sqrt(2)). The elementary bounds J>=1/sqrt(2), pi<22/7, and 7/(22sqrt(2))>1/5 make this lower bound strictly greater than 4 at r=5/6.

Evidence/status: ordinary_exact_quadratic_counterexample_to_universal_sharp_component_criterion

- [TypeBReturnAssimilation20260828.md](problem/TypeBReturnAssimilation20260828.md)

claim_boundary: This exactly refutes only the universal sharp radial-contour criterion RC4 returned in artifact 002. It does not refute componentwise radial contours as one branch of a target-deciding dichotomy, a compensation theorem when the contour budget fails, grouped or partial-cluster monodromy, or unrestricted Erdos 1041.

### global_tree_admissible_product_2026_08_28

For monic f of degree n >= 2 with listed zeros in the closed unit disc and c_1..c_{n-1} the zeros of f', the incidence product R = prod_{i,j} |z_i - c_j| = prod_j |f(c_j)| <= 1, with equality exactly for rotations of the regular n-gon. Moreover, for EVERY tree T on n slots and EVERY bijection lambda: E(T) -> {1..n-1}, some placement pi satisfies prod_{uv in E(T)} |z_{pi(u)} - c_{lambda(uv)}| |z_{pi(v)} - c_{lambda(uv)}| <= R^(2/n) <= 1, with the forest refinement (bound (prod_{j in J} |f(c_j)|)^(2/n) for a labelled forest using label set J). The weighted products B(pi) = A(pi)/prod_e |f(c_{lambda(e)})|^(2/n) satisfy prod_pi B(pi) = 1 identically for every monic f, so min B <= 1 <= max B. Also prod_i dist(z_i, Z(f')) <= 1. Proof: f'(z_i) = prod_{k!=i}(z_i - z_k) and Hadamard on the Vandermonde matrix; each labelled incidence (i, j) occurs in exactly 2(n-1)! of the n! placement products.

Evidence/status: ordinary_exact_matching_theorem_without_containment

- [TypeBReturnAssimilation20260828.md](problem/TypeBReturnAssimilation20260828.md)
- [GlobalTreeAdmissibleProduct.md](problem/GlobalTreeAdmissibleProduct.md)
- [check_erdos1041_global_tree_admissible_product.py](problem/scripts/check_erdos1041_global_tree_admissible_product.py)

claim_boundary: Carries no sublevel containment: matched pairs need not have any contained arm (negative entries 12, 15, 16, 22, 25; CentroidHubCounterexample), so the theorem does not feed free_pair_geometric_mean_two_arm_selector (whose open premise is arm containment in {|f| <= Gcrit}), is not an admissible product in the (AP) sense of AdmissibleCriticalArcProductLab.md (entrance arcs, not Euclidean distances; hybrid falsifier 0.839217266469 vs 1.075474341153 untouched), and its single-point corollaries are dominated by the occupied per-point two-nearest budget d1+d2 <= 2|f(c)|^(1/n). The non-dominated content is the simultaneous matching quantifier over (T, lambda). Does not change the parent claim ceiling.

### component_lifetime_transport_identity_2026_08_28

For a degree-d component W of the lemniscate forest with lifetime (beta, delta), mean access L_W(t) = (1/2pi) int Lambda_theta dtheta and perimeter p_W(t) = H^1(dK_t(W)): (Lemma A) L_W(t) = (1/2pi) int_beta^t p_W(s) ds/s, so L_W'(t) = p_W(t)/(2 pi t); (Theorem B) d/dt (t^(1/pi) L_W(t)) = (1/(2 pi)) t^(1/pi - 1) (2 L_W(t) + p_W(t)), equivalently int_beta^delta (2 L_W + p_W - 2d) dnu = 2[t^(1/pi)(L_W - d)]_beta^delta with dnu(t) = (1/pi) t^(1/pi - 1) dt. The excess charge t^(1/pi)(L_W - d_W) is exactly additive across mergers, and summing over the forest telescopes to int_0^1 (2L + p - 2n) dnu = 2(L(1) - n) <= 0 via the occupied global inverse-fibre budget L(1) <= n. The weight alpha = 1/pi is forced by the coarea constant; the law is an identity, so no reweighting avoids the obstruction.

Evidence/status: ordinary_exact_transport_identity_with_singleton_slack_obstruction

- [TypeBReturnAssimilation20260828.md](problem/TypeBReturnAssimilation20260828.md)
- [ComponentLifetimeTransportIdentity.md](problem/ComponentLifetimeTransportIdentity.md)
- [check_erdos1041_global_tree_admissible_product.py](problem/scripts/check_erdos1041_global_tree_admissible_product.py)

claim_boundary: Not a parent producer: under the failure hypothesis every degree >= 2 component can satisfy 2 L_W + p_W > 2 d while degree-one singleton loops absorb the entire global negative defect, which is exactly the virtual-cut/grafting residual of AdmissibleCriticalArcProductLab.md; the universal pointwise form is refuted by universal_radial_contour_sharp_criterion_no_go_2026_08_28 (z^2 - (5/6)^2) and negative entry 65. Fixed-level specialization is the occupied (PP2) of PartialClusterPreimagePerimeterIdentity.md. Parent claim ceiling unchanged.

### exterior_root_product_covering_2026_08_29

Exterior root-product covering lemma (landed from return B of batch erdos1041_20260829_meanshift_fullparent, independently re-derived). For m>=1, b_1..b_m in D, 0<r<1, B=prod|b_j|, F(z)=prod_j (1-r conj(b_j) z)/(1-conj(b_j) z), the value Lambda=(1-r^m B)/(1-B) lies in F(closed unit disk); hence max_{|z|=1} prod_j |z-r b_j|/|z-b_j| >= Lambda, and the stronger Apollonius covering {|lambda: |lambda-1| < B |lambda-r^m|} subset F(D) holds. The constant is exact: for the symmetric configuration b_j = rho e^{i(theta+2pij/m)} the boundary modulus |F| is identically Lambda, and for m=1 the boundary maximum equals Lambda for every configuration. Landed WITHOUT a live parent consumer: the returned 'activated last-lobe reduction' that would consume it (obstruction (2) = exact negation of the lemma) appears nowhere in the corpus or packets and is unproved, so no parent ceiling change follows.

Evidence/status: ordinary_exact_auxiliary_theorem_with_lean_scalar_kernel_and_exact_sharpness

- [ExteriorRootProductCovering.md](problem/ExteriorRootProductCovering.md)
- [check_erdos1041_exterior_root_product_covering.py](problem/scripts/check_erdos1041_exterior_root_product_covering.py)

### aggregate_n3_psh_uniformity_closure_2026_08_30

For the exact cubic near-radial deficit D(phi) of AggregateN3InnerModelClosedForm, the wall-free arm aggregate has the locally uniform expansion Sigma_c L(c)=4-2|s|D(-3 arg s)+O(|s|^2). A general test-function tangent-cone lemma says that if a subharmonic function has u(re^{i theta})=u_0+r a(theta)+O(r^2) locally uniformly, then a+a''>=0 distributionally. Applying the landed per-cell plurisubharmonicity of the arm aggregate with a(theta)=-2D(-3theta) gives D+9D''<=0. Wronskian comparison against h(phi)=D(0)cos((phi-pi/2)/3)/cos(pi/6) proves D(phi)>=h(phi)>=D(0)>=(3pi-8)/16>0 on every phase. Thus the saddle-connection wall is the global phase minimum by proof and the former psh-uniformity residual is closed.

Evidence/status: ordinary_exact_subharmonic_tangent_cone_theorem_with_scalar_lean_source_pending_focused_validation

- [AggregateN3PshUniformityClosure.md](problem/AggregateN3PshUniformityClosure.md)
- [check_erdos1041_aggregate_n3_psh_uniformity.py](problem/scripts/check_erdos1041_aggregate_n3_psh_uniformity.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.AggregateN3PshUniformity.cubicPhase_tangent_coefficient, ErdosProblems.Erdos1041.AggregateN3PshUniformity.phase_curvature_of_tangent_nonneg, ErdosProblems.Erdos1041.AggregateN3PshUniformity.wronskian_derivative_kernel, ErdosProblems.Erdos1041.AggregateN3PshUniformity.wall_elementary_lower_bound_pos.

claim_boundary: Closes all-phase positivity only for the first-order near-radial AGG3 coefficient. The Banach-valued plurisubharmonicity, distributional tangent limit, uniform inverse-branch asymptotic, and calculus maximum principle are ordinary analytic mathematics. The scalar Lean source is present, but focused Lake validation is pending because the live firewall terminated the private-project build during an exclusive canonical-root release window before any theorem diagnostic. AGG3 away from the near-radial shell and unrestricted Erdos 1041 remain open; AGG is false for every recorded degree n>=4 witness.

### quintic_trace_max_universal_chamber_2026_08_30

For every non-pure low-mode quintic H(z)=z^5+b_2 z^2+b_1 z and nonzero trace-maximal critical hub c, put mu=b_2/c^3 and phi=arg(c^5). With z=c(1+x), H(c(1+x))-H(c)=c^5 x^2(x^3+5x^2+10x+10+mu), the other critical displacements solve 5x^3+20x^2+30x+20+2mu=0, and their selected-to-other value gaps are c^5 g(x) with g(x)=x^3(3x^2+10x+10)/2. Modulo the critical cubic this gap collapses further to g=x(2mu+20-3mu x)/5; after y=x+4/3 the critical cubic is depressed and the gap is bilinear. Trace-maximality is exactly the three half-plane inequalities Re(e^(i phi)g(x_j))>=0. The rightward pair excess factors exactly as E_pair(H,c)=|c| E_universal(mu,phi). A quantitative Rouche argument proves the universal chamber compact with |mu|<67500. On the real mu-axis the chamber is exactly [alpha_1,-10] union [alpha_2,alpha_3] union {50+30sqrt(3)}, where alpha_1,alpha_2,alpha_3 are the three real roots of 27M^5+5450M^4+23000M^3-105000M^2-700000M-1000000, isolated respectively in (-198,-197),(-4,-3),(5,6).

Evidence/status: ordinary_exact_compact_universal_reduction_with_lean_algebra_kernel_and_exact_real_axis_classification

- [QuinticTraceMaxUniversalChamber.md](problem/QuinticTraceMaxUniversalChamber.md)
- [check_erdos1041_quintic_trace_max_universal_chamber.py](problem/scripts/check_erdos1041_quintic_trace_max_universal_chamber.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.quintic_center_at_critical, ErdosProblems.Erdos1041.quintic_universal_shape_identity, ErdosProblems.Erdos1041.quintic_universal_derivative_identity, ErdosProblems.Erdos1041.quintic_universal_critical_gap, ErdosProblems.Erdos1041.quintic_universal_chamber_rational_budget.

claim_boundary: This is an exact compactification and a complete exact classification only of the real-mu chamber, not a proof of the universal excess inequality. Separate analytic certificates prove the one-face point mu=0, the isolated tangent point mu=50+30sqrt(3), and the entire allowed canonical mu=-10 phase arc. The chamber-wall reduction leaves EX-W, and the weighted wall-sheet maximum principle further reduces its regular sheets to one-real-dimensional double-tight branches plus gap-zero and triple-hub puncture limits. The real-scale transfer, degree five, and unrestricted Erdos 1041 remain open.

### quintic_tangent_curved_excess_certificate_2026_08_30

At the isolated tangent point (mu,phi)=(50+30sqrt(3),-pi/2) of the quintic trace-max universal chamber, the canonical curved rightward inverse-ray pair has strictly negative excess. In the real normal form G(V)=V^5+40V^2-60V with hub h=sqrt(3)-1, the two upward arms are the unique algebraic graphs P(A,t^2)=0 on A>0 and A<0. Exact resultants and Sturm isolation prove tangent-slope ranges 0<p_R<1 and 7/8<p_L<7/5, exactly one finite transverse extremum on each arm, and Osc_R<277/1000, Osc_L<63/2000. The support-oscillation lemma then gives E_pair<=-19517458527181/5000000000000000<0. Positive similarity proves E_universal(50+30sqrt(3),-pi/2)<0.

Evidence/status: ordinary_exact_curved_inverse_ray_excess_theorem_with_resultant_sturm_interval_certificate_and_lean_algebra_kernel

- [QuinticTangentCurvedExcessCertificate.md](problem/QuinticTangentCurvedExcessCertificate.md)
- [check_erdos1041_quintic_tangent_curved_excess.py](problem/scripts/check_erdos1041_quintic_tangent_curved_excess.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.quintic_universal_critical_gap_quadratic, ErdosProblems.Erdos1041.quintic_tangent_level_factor, ErdosProblems.Erdos1041.quintic_tangent_curved_excess_rational_fanin.

claim_boundary: This row proves the isolated tangent gauge orbit only. The full canonical mu=-10 phase arc is closed by a separate exact uniform certificate, but the remaining one-dimensional EX-W boundary and puncture obligations, real-scale transfer, degree five, and unrestricted Erdos 1041 remain open.

surviving_obligation: Certify the degree-ten double-tight wall branches and the gap-zero/triple-hub puncture limits, then discharge the actual-polynomial real-scale transfer. The degree-five theorem and unrestricted Erdos 1041 remain open.

### quintic_minus_ten_central_excess_certificate_2026_08_30

At the central point (mu,phi)=(-10,0) of the repeated-critical boundary of the quintic trace-max universal chamber, the limiting pair from the real simple-hub chamber is the conjugate pair of F(x)=x^3(x^2+5x+10)=s born in directions plus or minus 2pi/3. Writing x=a+ib and t=a/b reduces the entire upper branch to the quadratic equation (5t^4-10t^2+1)b^2+20t(t^2-1)b+10(3t^2-1)=0. A 256-cell exact rational tangent partition, exact Sturm slope exclusions, Bernstein tail bounds, and the support-oscillation identity prove E_universal(-10,0)<-2853/100000<0.

Evidence/status: ordinary_exact_repeated_critical_curved_pair_excess_theorem_with_sturm_bernstein_rational_interval_certificate_and_lean_algebra_kernel

- [QuinticMinusTenCentralExcessCertificate.md](problem/QuinticMinusTenCentralExcessCertificate.md)
- [check_erdos1041_quintic_minus_ten_central_excess.py](problem/scripts/check_erdos1041_quintic_minus_ten_central_excess.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.quintic_minusTen_cubic_degeneracy, ErdosProblems.Erdos1041.quintic_minusTen_level_curve_factor, ErdosProblems.Erdos1041.quintic_minusTen_level_curve_radial, ErdosProblems.Erdos1041.quintic_minusTen_terminal_one_factor, ErdosProblems.Erdos1041.quintic_minusTen_central_excess_rational_fanin.

claim_boundary: This row remains the sharper pointwise theorem at (mu,phi)=(-10,0); the full phase-arc theorem supplies uniform closure for the canonical pair. It does not identify every direction-dependent wall-sheet tract-pair limit or prove the remaining one-dimensional EX-W obligations, real-scale transfer, degree five, or unrestricted Erdos 1041.

surviving_obligation: The canonical mu=-10 phase arc has no surviving excess subarc. Certify the degree-ten double-tight wall branches and all exceptional puncture limits, then discharge the actual-polynomial real-scale transfer; degree five and unrestricted Erdos 1041 remain open.

### quintic_minus_ten_endpoint_excess_certificate_2026_08_30

Let phi_0=arctan(1/(2sqrt(2))), the two endpoints of the allowed phase arc on the mu=-10 repeated-critical stratum. At each point (mu,phi)=(-10,+-phi_0), the canonical limiting curved inverse-ray pair has excess below -1/80. Writing an upper arm as x=b(t+i) and q=tan(phi) gives the quadratic curve A_q(t)b^2+B_q(t)b+C_q(t)=0. For q=+-1/(2sqrt(2)), exact rational isolation of the cubic start direction and terminal degree-ten root, a 640-cell interval partition on each arm, and a full degree-120 eliminated Sturm polynomial bounding every unresolved transverse turn prove J_-<7/20 and J_+<11/40. Exact node-to-cell gluing, w=0 and w=1 endpoint attachment, and positive physical-ray orientation are checked on the selected branches. The support-oscillation fan-in gives E_universal(-10,+-phi_0)<-1/80<0.

Evidence/status: ordinary_exact_repeated_critical_endpoint_curved_pair_excess_theorem_with_resultant_sturm_rational_interval_certificate_and_lean_algebra_kernel

- [QuinticMinusTenEndpointExcessCertificate.md](problem/QuinticMinusTenEndpointExcessCertificate.md)
- [check_erdos1041_quintic_minus_ten_endpoint_excess.py](problem/scripts/check_erdos1041_quintic_minus_ten_endpoint_excess.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.quintic_minusTen_endpoint_level_curve_radial, ErdosProblems.Erdos1041.quintic_minusTen_endpoint_terminal_polynomial, ErdosProblems.Erdos1041.quintic_minusTen_endpoint_divided_difference, ErdosProblems.Erdos1041.quintic_minusTen_endpoint_transverse_factor, ErdosProblems.Erdos1041.quintic_minusTen_endpoint_excess_rational_fanin.

claim_boundary: This row remains the sharper pointwise theorem at the two endpoint phases phi=+-arctan(1/(2sqrt(2))); the full phase-arc theorem supplies uniform closure for the canonical pair. It does not identify every direction-dependent wall-sheet tract-pair limit or prove the remaining one-dimensional EX-W obligations, real-scale transfer, degree five, or unrestricted Erdos 1041.

surviving_obligation: The canonical mu=-10 phase arc has no surviving excess subarc. Certify the degree-ten double-tight wall branches and all exceptional puncture limits, then discharge the actual-polynomial real-scale transfer; degree five and unrestricted Erdos 1041 remain open.

### quintic_minus_ten_full_arc_excess_certificate_2026_08_30

Let phi_0=arctan(1/(2sqrt(2))). For every allowed phase |phi|<=phi_0 on the mu=-10 repeated-critical stratum, the canonical pair of limiting curved inverse-ray arms has universal excess below -1/100. For signed zeta=tan(phi), the fixed coordinates t=r(zeta)+(k(zeta)-r(zeta))y and w=b(k-t) reduce the selected arm to one quadratic equation S=0 on 0<=y<=1. The exact identities kY-X=-(k-t)^2 S_t and w_y=-(k-r)S_t/S_w give the nonnegative square-integrand formula tan(|theta|/2)|w_y|=(k-r)^3(1-y)^2 S_t^2/(S_w Delta). An outward-rounded 2^-80 dyadic atlas isolates and glues every selected branch, proves S_w,Y,Delta>0, bounds 64 phase anchors with 640 point cells per signed arm, and transports each anchor over its phase slab using exact first-order interval jets on 128 dual cells. The exact rational fan-in proves E_universal(-10,phi)<-1/100<0 uniformly. This closes EX-10.

Evidence/status: ordinary_exact_uniform_full_repeated_critical_phase_arc_excess_theorem_with_dyadic_interval_atlas_and_lean_algebra_status_firewall

- [QuinticMinusTenFullArcExcessCertificate.md](problem/QuinticMinusTenFullArcExcessCertificate.md)
- [check_erdos1041_quintic_minus_ten_full_arc_excess.py](problem/scripts/check_erdos1041_quintic_minus_ten_full_arc_excess.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.quintic_minusTen_fullArc_determinant_identity, ErdosProblems.Erdos1041.quintic_minusTen_fullArc_squared_integrand_identity, ErdosProblems.Erdos1041.quintic_minusTen_fullArc_excess_negative_of_atlas.

claim_boundary: This is an exact all-phase theorem only for the canonical pair on the universal mu=-10 repeated-critical stratum. The finite exact Python atlas is theorem authority; Lean supplies an algebraic replay/status firewall rather than an end-to-end proof. The separate wall-limit side-arm theorem, rather than an implicit identification with the canonical pair, closes the direction-dependent nonzero-active triple-hub limits. EX-W, model-to-real transfer, the degree-five real theorem, and unrestricted Erdos 1041 remain open.

surviving_obligation: The canonical mu=-10 phase arc and both mu* gap-zero phase fibres now have no surviving excess subarc. A later exact side-arm theorem also closes every nonzero-active wall-sheet puncture limit above mu=-10. Certify only the regular compact one-real-dimensional double-tight wall carrier, then discharge the model-to-real consumption law. Degree five and unrestricted Erdos 1041 remain open.

### quintic_minus_ten_wall_limit_side_arm_certificate_2026_08_30

At the two nonzero-gap wall phases on the mu=-10 triple-hub fibre, the three approach lobes limit to the tract pairs {T0,T1}, {T1,T4}, and {T0,T4}. The canonical pair has the earlier exact ceiling -1/80. For the single missing shallow arm, the upper q=-1/(2sqrt(2)) quadratic curve has start r=cot(phi0/3), terminal k=cot(phi0/5)>14, and transverse coordinate w=b(k-t). Exact coefficient signs give one global positive root 0<w<1. The degree-120 stationary eliminant factors as the degree-10 terminal polynomial times a degree-110 quotient having no root on [8.7899,14.7]; one exact section orients w_t>0. The outward arm therefore has support budget J<1 and excess e0<-13/15. Combining with the earlier individual arm bounds e_-<1/10 and e_+<-9/80 gives exact ceilings -23/30, -1/80, and -47/48 for all three tract pairs. Conjugation handles the opposite phase.

Evidence/status: ordinary_exact_all_nonzero_active_mu_minus_ten_wall_limit_resolution_theorem_with_degree_110_sturm_certificate

- [QuinticMinusTenWallLimitSideArmCertificate.md](problem/QuinticMinusTenWallLimitSideArmCertificate.md)
- [check_erdos1041_quintic_minus_ten_wall_limit_side_arm.py](problem/scripts/check_erdos1041_quintic_minus_ten_wall_limit_side_arm.py)

claim_boundary: The theorem covers all three wall-limit tract-pair resolutions only at the mu=-10 puncture. The separate exact endpoint and angular theorems close both mu* fibres. This row does not certify the ordinary double-tight carrier, EX-W, EX-U, model-to-real transfer, degree five, or unrestricted Erdos 1041.

surviving_obligation: Certify the ordinary compact one-dimensional double-tight wall branches to close EX-W; the two mu* gap-zero phase fibres are now closed separately. Model-to-real transfer, degree five, and unrestricted Erdos 1041 remain open.

### quintic_wall_sheet_subharmonic_reduction_2026_08_30

On the normalized critical-root cover mu(u)=-(5/2)(u+2)(u^2+2u+2), let lambda(u)=g(u) be a selected nonzero tight gap and choose the wall phase by exp(i phi)lambda=-eps i|lambda|. A local fifth root alpha^5=lambda, x=alpha y, and s=|lambda|tau turn the moving inverse ray into the fixed ray P(y)=eps i tau, where P=y^5+5cy^4+10c^2y^3+(10+mu)c^3y^2 and P-(y+c)^5=mu c^3y^2-5c^4y-c^5. The normalized excess U=mathcal E/|lambda|^(1/5) is a locally uniform limit of finite integrals of moduli of holomorphic inverse-branch derivatives minus a parameter-constant normalizer, hence is subharmonic on every regular lifted wall sheet. Sign(U)=sign(mathcal E), so the maximum principle reduces each two-real-dimensional regular sheet to its one-real-dimensional double-tight boundary plus limsup obligations at lambda=0 and mu=-10. The double-tight boundary has an exact degree-ten implicit cover P_t(x)=0 over the ordered real gap ratio t in [-1,1]; its only real root-branch events are t=(1-sqrt(3))/2,0,1.

Evidence/status: ordinary_exact_weighted_subharmonic_wall_sheet_reduction_with_exact_degree_ten_boundary_algebra_checker

- [QuinticWallSheetSubharmonicReduction.md](problem/QuinticWallSheetSubharmonicReduction.md)
- [check_erdos1041_quintic_wall_sheet_subharmonic_reduction.py](problem/scripts/check_erdos1041_quintic_wall_sheet_subharmonic_reduction.py)

claim_boundary: The weighted function U, not mathcal E itself, is proved subharmonic. The degree-ten critical-root polynomial is a valid implicit cover, while the later unordered critical-value theorem supplies the smaller atlas target. Separate exact theorems close all direction-dependent triple-hub and gap-zero limits; this row remains a genuine reduction, not a proof of EX-W or EX-U.

surviving_obligation: Execute only the disjoint compact truncations of the twenty regular unordered critical-value double-tight branches. Exact side-arm, mu* endpoint-plus-angular, and event-excision theorems close all exceptional fibres and relative neighborhoods of every interior carrier event. This sole remaining effective model-metric class closes EX-W; model-to-real transfer, degree five, and unrestricted Erdos 1041 remain open.

### quintic_double_tight_critical_value_carrier_2026_08_30

Let Q_mu(Y)=Y^3+A Y^2+B Y+C be the exact cubic whose roots are the three quintic critical gaps, with A=4(mu+4), B=-(12/25)(3mu^3-5mu^2-100mu-200), and C=(4/3125)(mu+10)^3(27mu^2+140mu+200). For an unordered double-tight pair {a,b}, kappa=ab/(a^2+b^2) lies in [-1/2,1/2]. Eliminating the pair gives the degree-ten carrier K=C^2(1+kappa)^3-ABC kappa(1+kappa)(1+4kappa)+(A^3C+B^3)kappa^2(1+2kappa)-A^2B^2kappa^3. In fact K is minus the product of kappa(u^2+v^2)-uv over the three unordered critical-gap pairs. The pair sum and chamber ray are recovered rationally on every regular fibre. Exact discriminant and denominator resultants prove that the complete physical event set is -1/2,(1-3sqrt(3))/13,0,(1+3sqrt(3))/13,1/2 and that each of the four regular intervals carries exactly five upper-half-plane mu branches. The compact substitution s=(r/(1-r))^10, x=r^5 y/(1-r)^2 turns each hub arm into one polynomial equation on 0<=r<=1, regular at both endpoints, and gives the exact finite excess identity e_arm=integral(|V|-Re(conj(eta)V))dr-Re(conj(eta)).

Evidence/status: ordinary_exact_compact_unordered_double_tight_critical_value_carrier_with_complete_event_resultants_and_hub_to_infinity_arm_chart

- [QuinticDoubleTightCriticalValueCarrier.md](problem/QuinticDoubleTightCriticalValueCarrier.md)
- [check_erdos1041_quintic_double_tight_critical_value_carrier.py](problem/scripts/check_erdos1041_quintic_double_tight_critical_value_carrier.py)

claim_boundary: This is a proved exact carrier and compactification, not the completed sign atlas. The transverse-square rationalization may be used only on cells where its denominator is proved positive; otherwise the original nonnegative square-root defect must be bounded. It does not prove EX-W, EX-U, model-to-real transfer, degree five, or unrestricted Erdos 1041.

surviving_obligation: Execute interval-Newton continuation and prove the uniform negative pair-excess bound only on the disjoint compact truncations of the twenty regular branches. The two mu* fibres, the mu=-10 fibre, and all relative neighborhoods of the three interior carrier events are already removed. This effective regular atlas is the sole remaining model-metric class before EX-W; model-to-real transfer, degree five, and unrestricted Erdos 1041 remain open.

### quintic_mustar_angular_fiber_reduction_2026_08_30

For mu*=(-70+10i sqrt(5))/27, F=x^2(x+(5+i sqrt(5))/3)^2(x+(5-2i sqrt(5))/3), and the nonzero critical gaps are collinear with ratio 2+sqrt(3). The exact allowed phase fibre is |phi-phi_c|<=pi/2, where exp(i phi_c)=(-19+5i sqrt(5))/(9sqrt(6)). For alpha^5 carrying the ray, Q_alpha(y)=alpha^-5 F(alpha y) has terminal defect Q_alpha-(y+alpha^-1)^5=mu*alpha^-3y^2-5alpha^-4y-alpha^-5. The normalized pair excess U(alpha)=mathcal E(phi(alpha))/|alpha| is subharmonic. On the fifth-root sector of opening L=pi/5, radial homogeneity writes U=A(theta)/r and gives A''+A>=0 distributionally. The Dirichlet Poincare inequality for L<pi places A below its sine interpolant. Hence endpoint bounds A(0),A(L)<=-a imply A<=-a on the entire sector because [sin(L-t)+sin(t)]/sin(L)>=1. Conjugation handles the other mu*.

Evidence/status: ordinary_exact_short_sector_subharmonic_maximum_principle_reducing_each_mustar_halfcircle_to_two_endpoint_rays

- [QuinticMuStarAngularFiberReduction.md](problem/QuinticMuStarAngularFiberReduction.md)
- [check_erdos1041_quintic_mustar_angular_fiber.py](problem/scripts/check_erdos1041_quintic_mustar_angular_fiber.py)

claim_boundary: The subharmonic angular maximum principle is an ordinary exact theorem, and its required endpoint hypotheses are now supplied by QuinticMuStarEndpointExcessCertificate.md. It does not prove the compact ordinary carrier, EX-W, EX-U, model-to-real transfer, degree five, or unrestricted Erdos 1041.

surviving_obligation: Both mu* gap-zero fibres are closed. Execute the compact ordinary double-tight atlas to close EX-W. Model-to-real transfer, degree five, and unrestricted Erdos 1041 remain open.

### quintic_mustar_endpoint_excess_certificate_2026_08_30

At mu*=(-70+10i sqrt(5))/27 the normalized endpoint level polynomial factors as P(u)=(u^2-1)^2(u+i sqrt(5)). The compact equation H_sigma=0 has H_y=((1-r)^8/r^5)P'(u), so longitudinal and transverse signs can be certified without quotient singularities. Exact resultant and Sturm filtering proves positive longitudinal speed on all four selected arms and transverse turn counts 1,0,0,0. The sole turn lies in a strict rational two-dimensional Krawczyk box and has Vmax<7/8. Exact terminal transverse and projection bounds then give E_+<547/500-147/100=-47/125 and E_-<7/6-47/30=-2/5, hence both endpoint pair excesses are below -3/8. No numerical quadrature is used.

Evidence/status: ordinary_exact_gap_zero_endpoint_curved_pair_excess_theorem_with_resultant_sturm_krawczyk_rational_interval_certificate

- [QuinticMuStarEndpointExcessCertificate.md](problem/QuinticMuStarEndpointExcessCertificate.md)
- [check_erdos1041_quintic_mustar_endpoint_excess.py](problem/scripts/check_erdos1041_quintic_mustar_endpoint_excess.py)

claim_boundary: This theorem proves the two endpoint curved-pair inequalities on one mu* fibre; the separate angular maximum principle and conjugation are required for full-fibre closure. It does not prove the ordinary double-tight atlas, EX-W, EX-U, model-to-real transfer, degree five, or unrestricted Erdos 1041.

surviving_obligation: The regular compact 4 x 5 x 2 x [0,1] double-tight atlas is the sole remaining model-metric obligation before EX-W. Model-to-real transfer, degree five, and unrestricted Erdos 1041 remain open.

### quintic_double_tight_event_excision_2026_08_30

On the exact degree-ten unordered double-tight carrier, every interior singular event fibre has a relative open neighborhood on which the selected pair excess is strictly negative. At kappa=(1-3sqrt(3))/13 and kappa=(1+3sqrt(3))/13, the exact double-root tangent cones have finite nonreal conjugate slopes and fresh outward-rounded dyadic-ball evaluations give E<-1/6 and E<-1 respectively at the incident triple-tight centres. At kappa=0, exact factorization and squarefree Newton charts exhaust the limiting fibres as mu=-10 and the conjugate pair mu*=(-70+-10i sqrt(5))/27; the earlier mu=-10 wall-limit and mu* endpoint-plus-angular theorems give strict negative limits. Local uniform continuity on every incident regular chart then supplies the required relative negative neighborhoods.

Evidence/status: ordinary_exact_event_excision_theorem_with_symbolic_newton_charts_continuity_and_dyadic_ball_point_certificates

- [QuinticDoubleTightCompactAtlas.md](problem/QuinticDoubleTightCompactAtlas.md)
- [check_erdos1041_quintic_double_tight_compact_atlas.py](problem/scripts/check_erdos1041_quintic_double_tight_compact_atlas.py)

claim_boundary: No numerical neighborhood radius, global monotonicity in kappa, or endpoint-domination theorem is claimed. Restricting the subharmonic wall function to the real carrier does not justify endpoint domination and tracked branches have interior bumps. This theorem does not prove the remaining regular subatlas, EX-W, EX-U, model-to-real transfer, degree five, or unrestricted Erdos 1041.

surviving_obligation: Prove a uniform negative pair-excess bound on the disjoint regular compact branch truncations, for example by interval Newton plus a derivative budget or a finite semialgebraic support-variation certificate. Then compose the model-to-real transfer. Degree five and unrestricted Erdos 1041 remain open.

### quintic_double_tight_positive_decade_continuation_2026_08_30

On the connected positive regular interval 4949/500000 <= t <= 12116785580404918688981310598233490936176657/655360000000000000000000000000000000000000000, the unordered quintic double-tight carrier has exactly five pairwise-disjoint upper-half-plane sheets and the complete selected-pair excess is strictly negative on every sheet. Eighteen exact rational affine-predictor rows give ninety strict two-variable Krawczyk carrier cells, twenty exact sign-transport macro blocks, and eighty-five consecutive-overlap uniqueness tests. The first row overlaps the earlier cusp continuation. The weakest certified excess is below -0.000846889; the weakest carrier determinant, wall-orientation cross, and upper-tube separation are respectively above 79.8120664, 0.00199119464, and 0.0107790003.

Evidence/status: ordinary_exact_common_five_sheet_krawczyk_continuation_and_negative_excess_certificate

- [QuinticDoubleTightPositiveDecadeContinuation.md](problem/QuinticDoubleTightPositiveDecadeContinuation.md)
- [check_erdos1041_quintic_double_tight_positive_decade_continuation.py](problem/scripts/check_erdos1041_quintic_double_tight_positive_decade_continuation.py)

claim_boundary: No sign, continuation, or sheet count is asserted beyond the exact displayed interval. This does not close the remaining regular quintic carrier, EX-W, degree five, or unrestricted Erdos 1041. The generic consequence-map matches on A_SEED and MU_SEED in eight sibling checkers are lexical variable-name collisions; those independent validators require no change.

surviving_obligation: Certify the remaining disjoint compact regular double-tight truncations outside the displayed interval, then compose the already-proved quintic model-to-real transfer and solve the surviving all-degree containment/selection splice.

### first_merge_critical_value_separation_certificate_2026_08_30

Let f be monic of degree n>=3 and let c be a nonzero simple critical hub. If every other critical point d satisfies |1-f(d)/f(c)|>=S>1, then after normalizing f(c)=1 the square-root resolution P(Z(xi))=1-xi^2 has no unresolved branch point in |xi|<sqrt(S), so either local saddle sheet continues holomorphically and injectively across that disk. The area formula, Polya's area-capacity inequality for {|P|<1+R^2}, and coefficient Cauchy-Schwarz give integral_{-1}^1 |Z'(xi)| dxi <= 2*(1+S)^(1/n)*sqrt(log(S/(S-1))). Hence the connector is shorter than two whenever (1+S)^(2/n)log(S/(S-1))<1. Exact convenient thresholds are S=4 for n>=3, S=3 for n>=4, and S=2 for n>=7. Scaling back produces two distinct roots joined inside {|f|<=|f(c)|}; with open-unit-disk roots the Fekete chain gives |f(c)|<1, proving Erdos 1041 for the polynomial.

Evidence/status: ordinary_exact_all_degree_parent_theorem_in_the_separated_simple_first_merge_regime

Superseded by **disk_family_critical_value_separation_2026_09_02**. Use that stronger result.

- [FirstMergeCriticalValueSeparationCertificate.md](problem/FirstMergeCriticalValueSeparationCertificate.md)
- [check_erdos1041_first_merge_critical_value_separation.py](problem/scripts/check_erdos1041_first_merge_critical_value_separation.py)

claim_boundary: The three convenient thresholds are sufficient, not claimed sharp; the exact condition is (1+S)^(2/n)log(S/(S-1))<1. The theorem requires a simple nonzero critical hub and gives no estimate below that curve or when the selected saddle is multiple. The consequence-map matches on the generic symbol D_2 outside this source are lexical collisions and do not change those consumers. The unrestricted problem remains open precisely because the clustered complement is not covered. SUPERSEDED 2026-09-02 by disk_family_critical_value_separation_2026_09_02, which improves every constant and frees the centre; this row is retained as history.

surviving_obligation: Cover the complementary clustered or near-tied critical-value regime below the exact terminal curve, including multiple saddles, by grouped resolved covers, partial-cluster monodromy, a moved-block/attachment inequality, or another global producer.

### disk_family_critical_value_separation_2026_09_02

Let f be monic of degree n>=3, c a simple non-root critical point, v=f(c), and normalize P(w)=f(c+|v|^(1/n)w)/v so that P(0)=1, P'(0)=0, with other critical values v_j=f(d_j)/v. Fix a real centre w0 in [0,1] and a radius S>max(w0,1-w0) with |v_j-w0|>=S for every j, and put p=w0(1-w0). Then the square-root resolution P(Z(xi))=1-xi^2 extends to a conformal bijection of the Cassini domain {|xi^2-(1-w0)|<S} onto the two-sheeted component U of {|P-w0|<S} containing 0, the endpoints Z(+-1) are distinct roots, the connector lies in {|P|<=1}, and len(Z([-1,1]))^2 <= 2 (S/(n-1))^(2/n) log((S^2+S+p)/(S^2-S+p)). The proof composes the Bergman segment inequality Lemma A (the connector is the image of the real diameter [-q,q], q^2=S/(S^2+p), under the composed uniformiser), Polya's Area(K)<=pi cap(K)^2 on closure(U), and the exterior-fibre product gap cap(closure U)^n/S<k/(2n-k) at k=2 for the proper regular component of the unimodular-leading lemniscate of P-w0. Hence two roots of f are joined inside {|f|<=|v|} by a path shorter than 2|v|^(1/n) whenever C(n,S,p)=(S/(n-1))^(2/n) log((S^2+S+p)/(S^2-S+p))<2; with open-unit-disk roots and |v|<1 (any simple minimising hub) this proves Erdos 1041 for f. Uniform thresholds: C<2 for every n>=3, every 4/3<=S<=2, every p in [0,1/4]; so separation 4/3 from any real centre of the value segment [0,1], in particular |1-v_j|>=4/3 or |v_j|>=4/3, suffices in every degree. Radius 2 at the branch centre works for every n>=3 (formerly n>=6) and radius 6/5 already at n=3. Exact per-degree endpoint thresholds S_n^*: 1.10892 (n=3), 1.07318 (4), 1.06981 (5), 1.07347 (6), 1.09994 (10), 1.25415 (100), tending to coth(1)=1.31303; interior centres are sharper (S_3^*(1/2)=0.63053).

Evidence/status: ordinary_exact_all_degree_parent_theorem_in_the_disk_separated_simple_hub_regime_with_lean_checked_threshold_kernel_and_recorded_adversarial_falsifier

- [DiskFamilyCriticalValueSeparation.md](problem/DiskFamilyCriticalValueSeparation.md)
- [DiskFamilyCriticalValueSeparation.lean](problem/DiskFamilyCriticalValueSeparation.lean)
- [check_erdos1041_disk_family_critical_value_separation.py](problem/scripts/check_erdos1041_disk_family_critical_value_separation.py)
- Declaration locators not uniquely resolved: ErdosProblems.Erdos1041.diskFamilyCoefficient_lt_two_of_uniform_separation, ErdosProblems.Erdos1041.diskFamilyCoefficient_radius_two_lt_two, ErdosProblems.Erdos1041.diskFamilyCoefficient_three_six_fifths_lt_two, ErdosProblems.Erdos1041.diskFamily_length_lt_two_of_squared_bound, ErdosProblems.Erdos1041.diskFamily_length_lt_two_of_uniform_separation.

claim_boundary: The thresholds are sufficient, not claimed sharp; equality in the Bergman step needs a specific derivative and equality in Polya needs a disk, neither attained by a polynomial component. The theorem needs a simple hub; it is silent at multiple saddles. Dubinin (J. Math. Sci. 193 (2013)) Theorem 1, the relative Polya inequality flagged by the 2026-09-02 prior-art pass, enters neither this proof nor the 2026-08-30 one; it is the branch monotonicity used by actual_component_merge_tree_area_lower_bound and should be cited there. Its full text was not obtained. No literature-priority claim. Unrestricted Erdos 1041 remains open.

surviving_obligation: Cover the near-tie lens, where the second critical value is within ratio coth(1) of the first in modulus and within about 82 degrees in argument; the extremal family sits at its centre and saturates the target, so no Bergman/Polya estimate with positive loss can close it and an exact near-Fekete argument is required. The three-sheeted resolved cover over a disk containing both 1 and v_2 is simply connected but its Bergman constant diverges like log(1/|1-v_2|).

### abel_control_polygon_and_all_degree_trinomial_conclusion

At a root zeta of a degree-n polynomial with coefficients c, the radial value obeys the Abel control-polygon identity sum_(j<n) (t^j - t^(j+1)) S_j(zeta) = p(t zeta) with S_j(zeta)=sum_(k<=j) c_k zeta^k; the weights are non-negative and sum to 1-t^n, giving the finite certificate |p(t zeta)| <= R (1-t^n) for R = max_(j<n) |S_j(zeta)|. Specialising to the monic trinomial z^n + a z^m + b with 1<=m<n, at a root one has the exact cancellation (t zeta)^n + a (t zeta)^m + b = b(1-t^m) + zeta^n (t^n - t^m), so every radial segment from 0 to every root stays strictly inside {|f|<1}. The constant bound |b|<1 is DERIVED from the root hypothesis by Vieta on the monic X^n + C a X^m + C b, not assumed. Hence for any two roots the packaged conclusion gives both radial segments inside the lemniscate together with |zeta_1|+|zeta_2|<2, with a completely unrestricted. The pivot form generalises the cancellation to an arbitrary intermediate exponent, eliminating a_m from the radial value and yielding the sufficient condition N_m(t) <= t^n + delta(1-t^m) with delta = 1-|a_0|.

Evidence/status: lean_checked

- [AbelControlPolygon.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/AbelControlPolygon.lean)

claim_boundary: This is an unconditional SOLVED FAMILY, not progress on the unrestricted problem: Erdos 1041 remains open. PRIOR OVERLAP, verified on disk before landing: CyclicTrinomialFiberCase.trinomialRoot_spoke_factorization and trinomialRoot_spoke_norm_lt_one_of_norm_lt_one already carried the three-term cancellation and the radial containment estimate in quotient-variable form, but with |c|<1 as a HYPOTHESIS and no geometric conclusion attached; cyclicTrinomial_two_short_fiber_displacements and EvenSymmetricTrinomialCase.two_short_displacements_give_short_hub already carried |zeta_1|+|zeta_2|<2; CyclicTetranomialCoefficientCase hand-instantiates the Abel factorisation at four terms; TrinomialInterpolationSpoke.interpolation_remainder_identity carries the pivot remainder in difference form. What is new here is the general-n partial-sum control-polygon identity, the R(1-t^n) certificate, the DERIVATION of |b|<1 from the roots, the packaged conclusion assuming only that all roots lie in the open disc, and the direct pivot form with its sufficient condition. No erdos1041Conclusion or shortRootPath predicate exists in the tree, so containment and length are stated directly. NOT landed: the Newton-face constant kappa_(n,q) and its scalar inner approximation.

### sextic_prescribed_spoke_guardrail

For f_r(z) = z^6 + (1/5) r^2 z^4 - (1/5) r^4 z^2 - r^6 = (z^2-r^2)(z^4 + (6/5) r^2 z^2 + r^4), every zero has modulus exactly r, and f_r(r/2) = -(327/320) r^6. Hence for 0<r<1 with r^6 > 320/327 every zero lies strictly inside the open unit disc while the prescribed spoke to the root r leaves the unit lemniscate. Exactly one intermediate coefficient cannot produce this: the Abel partial sums must leave the value disc and return, which needs at least two active intermediate modes.

Evidence/status: lean_checked

- [AbelControlPolygon.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/AbelControlPolygon.lean)

claim_boundary: This refutes a SELECTOR, not the problem. f_r is not a counterexample to Erdos 1041: a different cyclic fibre supplies a short path, since for the non-real root lambda of lambda^2 + (6/5) lambda + 1 one has |h(u lambda)| <= 1 on (0,1], so the two roots plus/minus r sqrt(lambda) are joined through 0 with length 2r < 2. That positive half is NOT formalised and is recorded here as prose only. It also marks the exact limit of the trinomial radial mechanism above. Previously the guardrail lived only as prose in BarycentricEnvelope.md section 5; BarycentricEnvelope.lean does not contain it.

### free_point_diameter_and_geodesic_all_degree

The free-point functional S_m = sum_j (prod_k |1 - conj(c_j) c_k|)^(1/m) is now STATED in Lean for the first time. Two unconditional all-degree theorems. On the real diameter, row-wise AM-GM gives the strictly stronger S_m <= m(1 - xbar^2) <= m, with equality only at the origin: equality forces xbar = 0, and then prod_k (1 - x_j x_k) <= (1 - x_j^2) e^(x_j^2) < 1 unless x_j = 0. On ANY hyperbolic geodesic psi_beta(x) = (x + i beta)/(1 - i beta x), the cleared Gram identity |1 - conj(psi(s)) psi(t)| sqrt(1+(beta s)^2) sqrt(1+(beta t)^2) = (1-beta^2)(1 - s t) holds exactly - the difference of the two sides is beta^2 (1 - s t)(I^2 + 1) - so every pseudo-distance is dominated by the corresponding real chord and S_m <= m(1 - xbar^2) <= m transfers. Landed for beta^2 <= 1, slightly more general than the beta < 1 of the source, since |beta| = 1 puts the configuration on the unit circle where S_m = 0.

Evidence/status: lean_checked

- [FreePointHilbertCertificate.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/FreePointHilbertCertificate.lean)

claim_boundary: NOVELTY OF THE GEODESIC STATEMENT IS UNASSESSED; no priority is claimed. Before this module no Lean file in ErdosProblems/Erdos1041 stated the free-point functional at all - FreePointFP4Complete is a scalar algebraic kernel and FreePointTorusPshReduction is an exponent bridge; the corpus's FP_m work lived in markdown companions with Python checkers. Moebius and Blaschke parametrisations appear in several companions but never attached to this functional. These are special configurations: a diameter and a geodesic. They say nothing about the general FP_m and nothing about Erdos 1041, which remains open - free-point control is an arithmetic mean of critical-value capacities and carries no implication to a single short root-to-root curve.

### free_point_hilbert_chord_and_central_radius_conditional

The Hilbert chord lemma is landed over a general real InnerProductSpace: with u the mean of the v_j and B any bound on their norms, the mean of exp(-<v_j,u>) is at most F_B(r) = cosh(Br) - (r/B) sinh(Br) at r = ||u||. F_B(r) < 1 for every r > 0 when B^2 <= 2, and F_B(B) = exp(-B^2), so the abstract method's constant 2 is anchored at both ends. The central radius sqrt(1 - e^(-2)) = 0.9298734950321937 satisfies -log(1 - rho^2) <= 2. The route avoids the source's derivative computation entirely: with x = Br and B^2 <= 2, F_B(r) <= cosh x - (x/2) sinh x, which halves to sinh t < t cosh t, so only one derivative is ever taken.

Evidence/status: lean_checked

- [FreePointHilbertCertificate.lean](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/FreePointHilbertCertificate.lean)

claim_boundary: THE CENTRAL-RADIUS THEOREM IS THE NAMED-HYPOTHESIS VERSION, NOT THE ELL-2 ONE. freePointSum_central_le_of_series assumes the energy identity and the Cauchy-Schwarz row bound as explicit hypotheses; those are exactly ROWCERT+ steps (i)-(iii) and are NOT discharged here. The ell^2 feature-map bridge - v(c) = (c, c^2/sqrt2, ...) with ||v(c)||^2 = -log(1-|c|^2) - was not attempted, and a finite-dimensional truncation was deliberately NOT substituted as a stand-in, because a truncated map does not satisfy that identity exactly and would need its own weaker radius plus a limit argument. Comparison, stated honestly: the corpus's per-m ROWCERT+ central radii are about 0.943806, 0.931680, 0.924452, 0.919669 for m = 3,4,5,6 tending to 0.896360, so the Hilbert radius 0.929873 is WEAKER at m = 3 and 4 - both already solved - and stronger for every m >= 5, uniform in m, with no box computation. Item 5's unique later root r_*(B) and the balanced-cone reduction are not landed; only the outer anchor F_B(B) = e^(-B^2) is.

### weighted_quadratic_free_point_all_degrees

For finitely many closed-disc points c_j and positive weights w_j summing to one, G(z)=product_k |1-conj(c_k)z|^{w_k} satisfies sum_j w_j G(c_j)^2 + sum_(nu>=1)(2nu-1)|a_nu|^2 <= 1, where a_nu are the Taylor coefficients of exp(sum_k w_k log(1-conj(c_k)z)). In particular sum_j w_j G(c_j)^2 <= 1-|sum_j w_j c_j|^2, with equality in the bound by one only at the origin configuration. Equal weights close FP_m for every m. The torus/psh bridge proves sum_j |f(w_j)|^{2/(n-1)} <= (n-1)R^{2n/(n-1)}, hence (S)_n in every degree.

Evidence/status: ordinary_proof_verified_not_lean_formalized

- [FreePointQuadraticAllDegrees.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/FreePointQuadraticAllDegrees.md)

claim_boundary: Ordinary analytic proof. The critical-value mean does not supply the missing root-to-root metric connector.

### robust_merge_scalar_separation_and_one_root_bergman

For every n>=2 and r with r^2 artanh(r^2)>2, an open coefficient neighbourhood of z^n-r^n fails the connected-cluster scalar at every regular multi-root level, while a strict full-cycle lollipop proves the parent on that neighbourhood. For a regular degree-k component C of |f|<t and h in C, some root a has d_C(h,a)^2 <= Area(C)/pi log(1/(1-(|f(h)|/t)^(2/k))). A strict uniform bound below one over a connected root-carrying continuum gives a length-below-two connector.

Evidence/status: ordinary_proof_verified_not_lean_formalized

- [R2MergeNodeSeparation.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/R2MergeNodeSeparation.md)

claim_boundary: The regular-polygon no-go was already known. Robustness and the explicit one-root composition are additional; no universal forcing or parent theorem is asserted.

### all_arity_unique_active_stationarity_exclusion

For m>=2, the fixed-product attached-ray selector has no positive-valued stationary point in a cell with a unique active ray, a unique nondegenerate interior radial optimizer, and all angular/radial constraints strict. Angular and radial stationarity force all points to coincide, contradicting unique activity. This removes every smooth single-active stationary stratum at every level, strengthening the returned level-one local-maximum exclusion.

Evidence/status: ordinary_proof_verified_not_lean_formalized

- [SmoothUniqueActiveContactExclusionAllArity.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/SmoothUniqueActiveContactExclusionAllArity.md)

claim_boundary: Does not remove multi-active switches, optimizer switches, closed boundaries or the regular orbit.

### low_critical_potential_closure_all_degrees_2026_09_05

Let f be a squarefree monic polynomial of degree n>=2 and mu its least critical-value modulus. If mu<=197/1000 then two distinct roots of f are joined by a rectifiable curve inside {|f|<1} of length strictly less than 2; no hypothesis on the root locations, the first-merge arity, or any component capacity is needed. Scale-free form: every squarefree monic f has two distinct roots joined inside {|f| < (1000/197) mu} by a curve of length below 2 ((1000/197) mu)^(1/n). The proof fixes a compact connected Gamma in K_mu through the least critical point, follows its ancestor component C_t, and plays two failure inequalities against each other at every level x=log(t/mu): COVER failure forces arity k(x) >= 2x/delta(a(x)) with delta(a)=-log(1-exp(-1/a)) and a(x)=Area(K_t)/pi (one-root Bergman plus the connected clopen-cover lemma), while boundary-hop failure forces the area growth a'(x) >= (1/(2 pi^2))[2 sqrt(k) - sqrt(2a(x+2))]_+^2 (averaged radial-lift lemma int L^2 <= Area/pi replacing Koebe, coarea, and the per-component perimeter inequality). Since a<=1 while t<1, the resulting differential inequality cannot survive past x=log(1000/197). The returned scalar potential V(a)=int_0^a delta gives 1/8; the exact comparison ODE with a grid over the initial area gives 197/1000 in every degree, and at fixed degree the Polya cap a<=(mu e^x)^(2/n) and the arity cap k<=n give larger thresholds, certified as mu<=1/3 (n=4), 3/10 (n=5), 1/4 (n=6), 199/1000 (n=7) in quick mode with the full-precision values recorded in the note.

Evidence/status: ordinary_complete_all_degree_target_regime_proof_with_exact_rational_certificate_not_lean_checked_not_independently_reviewed

- [LowCriticalPotentialClosure.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/LowCriticalPotentialClosure.md)
- [check_erdos1041_low_critical_potential_closure.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_low_critical_potential_closure.py)

claim_boundary: Ordinary mathematics plus an exact rational certificate (implicit lower-Euler comparison with directed rounding, truncated exponential series, integer square roots). Not Lean-checked, not independently reviewed. The regime 197/1000 < mu < 1 remains open: the mechanism cannot reach mu near 1 because the failure window (mu,1) shrinks to nothing, which is exactly the near-Fekete shell. Erdos 1041 remains open.

### chord_conditioned_bergman_geodesic_bound

Let Omega be simply connected with finite area A, a != b in Omega, Gamma their hyperbolic geodesic, L=length(Gamma), d=|a-b|, rho=rho_Omega(a,b), x=(1-sqrt(1-rho^2))/(1+sqrt(1-rho^2)), E=(A/pi)log(1/(1-rho^2)). Then E>=L^2>=d^2 and L^2-d^2 <= lam(x)(E-d^2), where lam(x) is the norm on h^perp of the Bergman restriction operator on [-sqrt x, sqrt x], equivalently the spectral gap of an explicit reversible Markov kernel. lam(x) is the optimal affine coefficient and is attained in the limit by conformal maps. Proved bounds: lam(x) <= min{x, b1(x), b2(x)} with b1(x)=(x-(1-x^2)artanh x)/x^2 < x and b2(x)=((1+x)artanh(sqrt x)-(1-x)arctan(sqrt x))/(4 sqrt x); and lam(x) >= 1 - log(1+x)/artanh(x). Two independent proofs are given, one by weighted Cauchy-Schwarz and one by refining the positivity step of Lemma A.

Evidence/status: ordinary_complete_proof_two_independent_routes_with_exact_rational_and_falsification_replay_novelty_not_claimed

- [ChordConditionedBergman.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/ChordConditionedBergman.md)
- [check_erdos1041_chord_conditioned_bergman.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_chord_conditioned_bergman.py)

claim_boundary: Ordinary mathematics throughout, including both proofs, both coefficient bounds, sharpness with univalence, and the lower bound. Optimality is optimality of the affine coefficient, not of the bound for each separately prescribed triple (A,d,rho). Every numerical value of lam(x) is floating point from a truncated principal compression of the exact matrix, so it is a lower estimate of lam and carries no proof authority. The claim that b1 is below b2 on (0,1) is a 10^-4 grid measurement plus the expansion b2-b1=(4/105)x^3+O(x^5); the note uses the min. No novelty is claimed against Bergman-space or Markov-chain literature. Erdos 1041 remains open.

### chord_conditioned_two_root_window_and_cluster_consumers

Consumers of the chord-conditioned bound. (i) For a two-root component of {|f|<t} with critical point c, v=|f(c)|, x=v/t, d=|a-b|, the descent arc satisfies L^2 <= (1-lam)d^2 + lam(2 Area/pi)log((t+v)/(t-v)) with lam=min{x,b1(x),b2(x)}. (ii) Over the persistence window v<t<T, F(t)=d^2+(v/t)(G(t)-d^2) is strictly decreasing, so L^2 <= (1-v/T)d^2+(v/T)G(T); the criterion q(G(T)-4) < (1-q)(4-d^2) with q=v/T retains the scalar condition G(T)<4 and adds a regime where G(T)>4 is paid for by the chord deficit. (iii) If t<=1, |a-b|<=1 and v/t<=17/20 then L^2 < 767/200 < 4 and L < 1.959. (iv) For a connected cluster with y=q_C^(2/k), L^2 <= (1-y)D_C^2 + (2 y A_C/pi)log((1+y)/(1-y)), which also improves the area coefficient by the factor y. Witness: f=z^3-pz-1/4 with u=1011/1600, p=u^2-1/(4u) has G(T)>4.0014 and F(T)<3.9996, so the corpus first-two-level criterion fails and the chord-conditioned one fires.

Evidence/status: ordinary_exact_sufficient_criteria_with_exact_rational_separating_witness

- [ChordConditionedBergman.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/ChordConditionedBergman.md)
- [check_erdos1041_chord_conditioned_bergman.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_chord_conditioned_bergman.py)

claim_boundary: All four consumers are ordinary proofs from the parent theorem plus already-landed corpus inputs (the degree-two normal form, the t-independent containment of the descent arc, the exterior-fibre area gap, the cluster selection, Polya's area bound). The 17/20 criterion and the cubic witness are certified by exact rational arithmetic. The source return's published proof chain for the 17/20 criterion contains one invalid step, bounding (1-b(x))d^2 by 3/10; the repaired monotone chain reaches the same constant and is what is landed. The witness is a strict improvement of one certificate on one polynomial; it is not a new degree range for the parent. Erdos 1041 remains open.

### chord_conditioned_moved_sheet_endpoint_charge

Let Z_j : D -> C, j=1..N, be holomorphic extensions of complete lifts along I=[-sqrt x, sqrt x] with images in the admissible lemniscate and endpoints Z_j(-sqrt x)=a_j, Z_j(sqrt x)=a_{tau(j)}. With L_j, d_j the lift lengths and endpoint chords, E_j the Dirichlet energy with multiplicity, M the moved set of size m, nfix=N-m, and Q=(4/pi)artanh(x) sum_j E_j, the chord-conditioned bound gives min_{j in M} L_j^2 <= (lam Q + (1-lam) sum_{j in M} d_j^2)/m. If Q <= 4N, then (1-lam) sum_{j in M}(4-d_j^2) > 4 lam nfix is sufficient for a moved lift of length below 2; with Q <= 4N - dE the condition becomes (1-lam) sum_{j in M}(4-d_j^2) + lam dE > 4 lam nfix.

Evidence/status: ordinary_conditional_implication_with_unsupplied_geometric_hypotheses

- [ChordConditionedBergman.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/ChordConditionedBergman.md)

claim_boundary: The three displays are ordinary implications from the parent theorem and summation. The holomorphic extensions Z_j and the energy budget Q <= 4N are NOT supplied here or by either return, and E_j may not be replaced by the area of a lemniscate component without a separate multiplicity estimate. This does not touch the launch problem of partial_cluster_preimage_perimeter_identity and does not settle Erdos 1041.

### sharp_symmetric_merge_envelope_and_exact_fibre_defect

Let U_t be a regular persistent component of {|f|<t} for monic f of degree n, holding k<n roots with multiplicity, m=n-k>=1, N=2n-k, p0=k/N, p(t)=cap(closure U_t)^n/t, B_t its exterior degree-m Blaschke product, h_t=n-|B_t'|. Then d log c/d log t = (1/2pi) int dtheta/h_t >= 1/k. Decomposing over complete boundary fibres, d log c/d log t = 1/n + (m/n) sqrt((1-p^2)/(k^2-N^2p^2)) + V(B_t) with V>=0 the fibre variance, whose exact value is the angular mean of (1/n^2)[sum_j 1/q_j - m^2/sum_j q_j], q_j=n/|B_t'(zeta_j)|-1. Hence if T is the first level at which U_t acquires an excluded root, log(T/t) <= Psi_{n,k}(p) = (1/m) int_p^{p0} sqrt(k^2-N^2u^2)/(u sqrt(1-u^2)) du = log F_{n,k}(p), F = y^{n/m}(1-py)/(y-p) with y>1 the larger root of y^2-((k+Np^2)/(np))y+1=0. V=0 exactly for B=Moebius(z^m). Equality holds for f=z^k(z^m-1). F ~ (m k^{k/m}/n^{n/m}) p^{-k/m} and F <= (p0/p)^{k/m}.

Evidence/status: ordinary_complete_exterior_analytic_theorem_with_exact_rational_algebra_and_deterministic_floating_replay_two_independent_derivations_not_lean_checked_not_independently_reviewed

- [SharpSymmetricMergeEnvelope.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/SharpSymmetricMergeEnvelope.md)
- [check_erdos1041_sharp_merge_envelope.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_sharp_merge_envelope.py)

claim_boundary: This is a level-parameter lifetime bound for one component, proved on the exterior model. It carries no metric conclusion and produces no curve. It proves equation (18) of CapacitySaturationBridge.md and supersedes that note's Theorem 3 for m>=2 while reproducing it exactly at m=1. It is not Lean-checked, has not been independently reviewed, and claims no novelty against the potential-theory literature: the capacity variation formula is the standard Hadamard shape derivative of the exterior Green function. Erdos 1041 remains open.

### ancestral_capacity_growth_and_capacity_to_arity_alternative

Following one component ancestry C_t with root count k(t) and capacity c(t), for 0<t0<S one has c(S) >= c(t0)(S/t0)^{1/k(S)}. The proof integrates d log c/d log t >= 1/k(t) on the finitely many regular intervals and adds the non-negative logarithmic capacity jumps at attachments, including simultaneous ones. Combined with c(S) <= cap(K_S) = S^{1/n}, if S<1 and c(t0)>q then k(S) > log(S/t0)/log(1/q). The statement refers to one actual ancestor, with no reassignment of capacity between components.

Evidence/status: ordinary_complete_proof_from_the_capacity_speed_identity_not_lean_checked

- [SharpSymmetricMergeEnvelope.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/SharpSymmetricMergeEnvelope.md)

claim_boundary: A capacity-to-arity conversion along a real ancestry. It supplies no metric input and no bound on access or perimeter, and it does not by itself force any merge node to cross either metric threshold in ExteriorBlaschkeFibreCapacityGap.md section 3. Erdos 1041 remains open.

### centred_circle_quadrinomial_connector_2026_09_05

Let p(z)=z^n+omega conj(a) z^(n-k)+a z^k+omega with |omega|=1, 1<=k<n/2, n>=4, and all n roots on |z|=1. Then two root occurrences are joined inside {|p|<=1} by a curve of length at most 2, via an exhaustive alternative: either two distinct roots satisfy |omega+a zeta^k|<=1, in which case the exact Abel identity p(t zeta)=(1-t^k)omega+(t^k-t^(n-k))S-(t^(n-k)-t^n)zeta^n gives |p(t zeta)|<=1-t^n on the whole spoke; or n=3k and |a|>sqrt(3), in which case two roots are joined by a unit-circle arc of length below 2 pi/(5k) on which |p|<3-sqrt(5)<1. Selection uses phase-crossing counting with N_-=k, Newton bounds A^2<=n/k and A<=2 for n>3k, and a 3x3 Gram determinant for 2k<n<3k. Scaling by r<1 gives strict Erdos 1041. Corollary: every monic degree n>=4 polynomial with at most four non-zero coefficients whose roots all have the same modulus r<1 satisfies Erdos 1041.

Evidence/status: ordinary_analytic_case_theorem_verified_not_lean_formalized

- [CentredCircleQuadrinomialConnector.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/CentredCircleQuadrinomialConnector.md)
- [check_erdos1041_centred_circle_quadrinomial.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_centred_circle_quadrinomial.py)

claim_boundary: Requires all roots on one circle centred at the origin. It is not a theorem about unrestricted Schur-stable quadrinomials, and it does not prove unrestricted Erdos 1041. Ordinary analytic proof, no Lean module. Sampling in the replay script is falsification evidence only.

### polar_derivative_schur_pointwise_critical_certificate_2026_09_05

Let f be monic of degree n with all roots in the open unit disc, q=f'/n=prod_j(z-c_j) with m=n-1, and q#(z)=prod_j(1-conj(c_j)z). Then sigma_f=(f-z q)/q# is analytic on a neighbourhood of the closed unit disc with |sigma_f|<1 there, so |f(c_j)| < prod_l |1-conj(c_l)c_j| STRICTLY at every critical point. Proof: Re(zeta f'/f)>n/2 on |zeta|=1 because 2(1-Re(conj(zeta)a_i))-|zeta-a_i|^2=1-|a_i|^2>0, hence |n f-zeta f'|<|f'|, and |q#|=|q| on the circle plus the maximum principle. Composing with the corpus equal-weight weighted free-point theorem gives (1/m)sum_j|f(c_j)|^(2/m)+D(g)+S(f)<=1 with g=(q#)^(1/m), D(g)=sum_(nu>=1)(2nu-1)|b_nu|^2 and the non-negative interior defect S(f)=(1/m)sum_j(1-|sigma_f(c_j)|^(2/m))|g(c_j)|^2; taking only b_1 gives the centroid form with |(1/n)sum_i a_i|^2.

Evidence/status: ordinary_analytic_theorem_verified_not_lean_formalized

- [CentredCircleQuadrinomialConnector.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/CentredCircleQuadrinomialConnector.md)
- [check_erdos1041_centred_circle_quadrinomial.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_centred_circle_quadrinomial.py)

claim_boundary: A pointwise critical-value estimate. It does not select a root pair and does not control the length of any joining curve. It strengthens the free-point aggregate route by an additive non-negative term and does not replace it; the corpus torus/psh bridge remains the source of the aggregate inequality. Ordinary analytic proof, no Lean module. The return stated the inequality with <=; the proof gives strict <.

### translated_non_adjacent_trinomial_2026_09_05

Let f(z)=(z-h)^n+A(z-h)^m+C with n>=4, 1<=m<=n-2, and h, A, C arbitrary complex. If all roots lie in a closed disc D(q,R), put H=|h-q| and sigma=sqrt(R^2-H^2). Then two listed roots are joined through h by two straight segments of total length at most 2 sigma with |f(h+t(a_l-h))|<=sigma^n(1-t^n) on each. Since m<=n-2 kills the w^(n-1) coefficient, h is the centroid, and Newton's identities give S_2=0 when m<=n-3 or S_3=0 when m=n-2; either vanishing moment forces at least two displacements of modulus at most sigma, by a centroid-balance and half-plane contradiction. Combined with |C|<=sigma^n and the trinomial cancellation identity P(tw)=(1-t^m)C-(t^m-t^n)w^n, this proves Erdos 1041 for every such polynomial with roots in the open unit disc, coprime exponent pairs and arbitrary translation included.

Evidence/status: ordinary_analytic_case_theorem_verified_not_lean_formalized

- [TranslatedNonAdjacentTrinomial.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/TranslatedNonAdjacentTrinomial.md)
- [check_erdos1041_translated_trinomial.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_translated_trinomial.py)

claim_boundary: Requires n>=4 and 1<=m<=n-2. It does not cover the translated adjacent family (z-h)^n+A(z-h)^(n-1)+C, where h is generally not the centroid, and it does not cover the translated coprime cubic n=3, m=1, where the vanishing coefficient would be the constant term. It does not prove unrestricted Erdos 1041. Ordinary analytic proof, no Lean module.

### centroid_moment_localisation_and_balanced_weight_duality_2026_09_05

For any points a_1..a_n in D(q,R) with centroid h, displacements w_j, H=|h-q| and sigma^2=R^2-H^2: (i) if S_2=0 and sigma>0 then the count of j with |w_j|<=sigma exceeds n(R+H)/(4R+2H)>=n/4, so it is at least floor(n/4)+1; (ii) for arbitrary n>=2 and H>0, the second smallest centroid distance obeys r_(2)^2 <= sigma^2 + min{D_0, D_2, D_3} with D_0=2H(R-H)/(n-1), D_2=[3(R-H)^2-(n-1)sigma^2-M_2]_+/(n-1), D_3=sqrt(2H(M_3)_+/(3(n-1))), where M_k=Re(e^(-ik theta)S_k) and theta=arg(h-q); hence r_(2)<=nR/sqrt(n^2-1), attained for every odd n; and M_3<=0 alone forces r_(2)<=sigma. (iii) The best obtainable R^2-|h-q|^2 equals max over balanced probability vectors p with sum_j p_j w_j=0 of sum_j p_j |w_j|^2, attained with support on at most three points.

Evidence/status: ordinary_analytic_theorem_verified_not_lean_formalized

- [TranslatedNonAdjacentTrinomial.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/TranslatedNonAdjacentTrinomial.md)
- [check_erdos1041_translated_trinomial.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_translated_trinomial.py)

claim_boundary: Pure point-configuration geometry. It supplies a second individual radius and an optimised enclosing scale. It does not supply containment for an arbitrary polynomial: applied to the exact quintic of CentroidHubCounterexample.md the derived coefficient budget stays above one at every pivot, so the certificate correctly does not fire. Ordinary analytic proof, no Lean module.

### moment_localised_coefficient_certificate_open_neighbourhood_2026_09_05

Let a monic degree-n polynomial have roots in D(q,R) and expand about its centroid as f(h+w)=w^n+sum_(k=1..n-2) b_k w^k + b_0. Choose U with r_(2)<=U from the signed-moment bound, so |b_0|<=sigma^n<=U^n. For any pivot m in 1..n-2, eliminating b_m w^m at a root gives f(h+tw)=(1-t^m)b_0+(t^n-t^m)w^n+sum_(k!=m) b_k(t^k-t^m)w^k, and the budget U^n + sum_(k!=m) |b_k| U^k d_km < 1, with d_km = (|k-m|/max(k,m))(min(k,m)/max(k,m))^(min(k,m)/|k-m|), implies U<1 and forces two roots joined through the centroid by a curve of length at most 2U<2 inside {|f|<1}. At a strict translated non-adjacent trinomial the sum vanishes at the trinomial pivot and the left side is sigma^n<1, so the certificate covers an open full-dimensional coefficient neighbourhood of every such instance.

Evidence/status: ordinary_analytic_theorem_verified_not_lean_formalized

- [TranslatedNonAdjacentTrinomial.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/TranslatedNonAdjacentTrinomial.md)
- [check_erdos1041_translated_trinomial.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_translated_trinomial.py)

claim_boundary: A sufficient finite coefficient test, not a characterisation. Verified to stay silent on the stored centroid-hub counterexample, where the pivot budgets are 1.16927981, 1.05490983 and 1.06166219. It does not close unrestricted Erdos 1041. Ordinary analytic proof, no Lean module.

### completed_trace_curvature_measure_and_polygonal_shortening

For monic f of degree n>=3 and 1<=p<=2, the Vandermonde-minor norm H_p(w)=n^(2-n-2/p)(sum_j |D_j(w)|^p)^(2/p) has mu_p=(1/2)Laplacian log H_p a positive measure of mass pi(n-1)(n-2)/n with log H_p equal to its logarithmic potential; if the roots lie in a disc of radius R then (1/E) int log|zeta| dmu_p <= n log R, sharp exactly at the regular n-gon, by Cauchy-Binet plus Hadamard on the n x (n-1) root matrix. Away from critical values mu_p = p V_p dA is the negative Gaussian curvature of the inverse-fibre metric rho_p^2|dw|^2, and each critical value carries the exact atom pi[m_v - 2(1-1/e_v)], zero at a simple critical point and pi(d-1)(d-2)/d at an isolated d-fold one. Replacing the value-plane circle by the regular d-gon at a d-fold critical point shortens the preimage-perimeter budget with coefficient 1-sin(pi/d) in place of 1-pi/d, with exact containment max_{P_s}|b-u^d| = b + s^d cos^d(pi/d); on z^n-r^n this gives L = 2r-2s(1-sin(pi/n)) under r^n+s^n cos^n(pi/n)<1, and an explicit coefficient neighbourhood by Rouche produces genuine connectors of length below 2.

Evidence/status: ordinary_analytic_all_degree_measure_theorem_plus_sharp_local_surgery_not_lean_checked

- [TraceCurvatureMeasureAndPolygonalShortening.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/TraceCurvatureMeasureAndPolygonalShortening.md)
- [check_erdos1041_polygonal_shortening.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_polygonal_shortening.py)

claim_boundary: Ordinary analytic mathematics, no Lean module, no priority claim; the prior-art status of the log-moment inequality is unassessed. The measure bound is global and supplies no per-block allocation of 2 Lambda(alpha,W)+Per(W); the polygonal surgery assumes an isolated d-fold critical value on a clean value segment and is not proved to be available in a general configuration; the coefficient neighbourhood is perturbative and degenerates as r tends to one. Erdos 1041 remains open.

### sharp_nodal_crofton_budget_and_high_cyclic_pullbacks

If every root of a monic degree-n f lies in the closed disc D(c,R), then for every phase the full inverse image of a value line satisfies H^1(f^{-1}(e^{i phi}R) cap D(c,R)) <= 2nR, with the exact decomposition 2nR - L = D_phi(f) + T_{phi,c}(R) into a Crofton line-count deficit and the excess length of the 2n exterior radial ends, both nonnegative. Equality holds exactly for f(c+w)=w^n+e^{i phi}b with b real. The proof uses a renormalised Crofton identity comparing the nodal set against its n asymptotic lines before passing to the limit, plus the exterior estimate Re((z-c)f'/f) > n/2 for |z-c| > R. The deficit is computed exactly on {Re z^n = 1} as (n-1)B(1-1/(2n),1/2). Separately, every monic P with roots in the open unit disc and P(0) nonzero has a constant C_P such that P(z^m) satisfies the target for every m > C_P, by lifting a winding-one loop in the component of {|P|<1} containing the origin, with length at most 2C_P/m.

Evidence/status: ordinary_analytic_sharp_all_degree_identity_plus_unconditional_pullback_family_not_lean_checked

- [NodalCroftonBudgetAndCyclicPullbacks.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/NodalCroftonBudgetAndCyclicPullbacks.md)
- [check_erdos1041_polygonal_shortening.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_polygonal_shortening.py)

claim_boundary: Ordinary analytic mathematics, no Lean module, no priority claim; the sharp constant and the equality rigidity are close to standard nodal results and their prior-art status is unassessed. The nodal identity bounds a whole inverse image and selects no component: on z^n-r^n at phase pi/2 the nodal set has n components with one root each and total length inside the disc tending to zero, so no strengthening of the scalar deficit at a prescribed phase can force two roots into one component. The pullback theorem has a base-dependent threshold. Erdos 1041 remains open.

### pinned_witness_noncritical_hub_connectors

The pinned degree-six and degree-nine QC_REFUTATION_WITNESSES now have exact positive connectors through noncritical hubs. Two straight segments through h_6=(3+2i)/25 and h_9=-1/5-4i/25 stay in {|f| < 99999/100000} with lengths at most 29471595/2^24 < 1.757 and 12825029/2^23 < 1.529, certified by 64 strictly positive Bernstein coefficients of the slack polynomial; both hubs satisfy f'(h) nonzero in exact Gaussian-rational arithmetic. The three-segment paths a_i -> t a_i -> t a_j -> a_j with t = 19/100 and 29/100 stay in {|f|^2 < 19999/20000} with lengths below 181/100 and 1623/1000, certified by 96 exact Bernstein inequalities. Both certificates survive explicit 1e-9 root-coordinate neighbourhoods. Because the three-segment paths lie in half planes missing the origin, every cyclic pullback P_d(z^m), m>=1, inherits a connector of length below 1.81 and 1.623 in degrees 6m and 9m.

Evidence/status: exact_rational_bernstein_positive_certificate_on_pinned_witnesses_not_lean_checked

- [PinnedWitnessNoncriticalHubConnectors.md](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/PinnedWitnessNoncriticalHubConnectors.md)
- [check_erdos1041_pinned_witness_hub_connectors.py](formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_pinned_witness_hub_connectors.py)

claim_boundary: Two configurations plus explicit neighbourhoods and their pullback families. Exact rational certificates, no Lean module. No hub-selection rule is supplied and no statement is made about any other configuration. The corpus critical-hub no-go (straight_spoke_hub_criterion_separation) concerns admissible critical points only and is untouched: both hubs are verified noncritical. Erdos 1041 remains open.

## Known failed routes

The universal scalar saddle-wall threshold T<=2sqrt(2)(beta gamma)^(1/(2n)) is FALSE for an actual polynomial wall. For f(z)=(z^2-a^2)(z^2+b^2) with b/a=9/10, the fourth-power threshold fails by exactly 5836/625. The true normalized lower/upper pair remains below one: its square is 3249/3620 with slack 371/3620, and the complete quartic AP product is also strictly below one. SCOPE: this retires only the total-length strengthening obtained by discarding the exact X^2 and arm-imbalance slack. The shape-retaining condition T^2-X^2-(A+B)|A-B|<=8(beta gamma)^(1/n), complete rooted-block compensation, AP, and unrestricted Erdos 1041 remain live. Exact checker: scripts/check_erdos1041_symmetric_two_level_wall.py; pending Lean source: SymmetricTwoLevelWall.lean.

The first-critical pair-energy cone inequality is FALSE already for an exact cubic with every root strictly in the open unit disk and a unique minimum-modulus critical point. For p(c+w)=v+a w^2+w^3 with c=-1/2-i/100, a=-1/16-5i/6, and v=-1/32+i/160, three exact rational Rouche disks certify the roots. Along the two local inverse branches, E-|c|^2=A s^2+O(s^4) with 0<A<K=|v/a|, and the proposed cone difference has leading term 4A(A-K)s^2<0. Exact checker: scripts/check_erdos1041_first_critical_pair_energy_no_go.py. SCOPE: this retires only the pointwise pair-energy producer; the descending-branch route, combined charge, COVER, and unrestricted Erdős 1041 remain open.

The terminal-node weighted-young entrance-energy lift is false for an actual polynomial. For F(z)=(z^2-1/100)(z^2-1/4), the inner and terminal merge moduli are 1/400 and 9/625, the inner and outer entrance energies are 625/576 and 1/4, and the only two terminal-young roots carry exactly 144/769<1/2 of total energy, with strict deficit 481/1538. The inequalities are exact and persist under small generic perturbation. The sharp attachment-coupled selector survives, but exact transport to the selected lowest common merge restores the common-ancestry discount, so localization alone does not close the metric consumer.

The retained scalar/tree ledger does not force both roots at the sharp two-young threshold A<=S/(k-1) to be individually h_cl-heavy. A minimal four-leaf labelled comb has top ages (2s,2s,s,0), makes roots 3 and 4 the exact two-young pair, and assigns exactly one of them below h_cl while satisfying the stated merge-product, energy-bridge, lifetime, and abstract H=I Gram identities. This is an abstract invariant-ledger countermodel, not an actual-polynomial realisation. It retires only the uncoupled deduction; the sharper pair-product guarantee survives for the same two roots, and three-young selection supplies two individually heavy roots.

Attachment youth has the opposite polarity for the direct root-centred Bergman consumer. Domain monotonicity from the singleton component gives r_Omega_t(a_i)>=q_i and hence the Green product P_i(t)>=sigma_i/t, which approaches a lower bound near one for a young root observed near component birth. The consumer needs an upper bound away from one, and charge heaviness cancels from this estimate. A different observation level or independent upper bound is required.

Deleting Gram-exceptional rows before assigning connector geometry is impossible as a degree-free allocation rule. For F_(n,r)(z)=z^n-r^(n-1)z with r close to one, a fixed determinant floor below e^(-1) permits exactly one exceptional central row, yet that root carries fraction (n-1)/n of the ER4 mass and every attachment age is zero; deleting it leaves only 1/n and any two surviving outer roots carry 2/[n(n-1)]. This is not a counterexample to Erdos 1041: the central root is the useful hub and the radial connector has length r<1. The surviving architecture must include an exceptional-root branch or retain all roots until geometry is assigned.

The full normalized sextic mixed model cannot be covered by positive equal-radius root-direction connectors. On H(z)=Re(z^3-z^6), every non-antipodal sixth-root chord crosses a half-step direction where z^3 is nonzero purely imaginary and H(z)=|z|^6>0; antipodal pairs have length exactly two. The pure cubic face is still solved by its radius-zero origin connector, so this refutes only the monolithic positive-radius atlas and forces a separate stable origin cone. Exact checker: scripts/check_erdos1041_sextic_cubic_face_connector_no_go.py; Lean core: SexticCubicFaceConnectorNoGo.lean.

The unique-smallest-angular-gap common-radius selector for Form A is FALSE at n=5. A rational half-angle pentagon makes w3,w4 the unique smallest gap, blocks radius zero on the w4 spoke, and blocks every positive radius at the selected chord midpoint. The latter is uniform: |g(sm)|^2-1 is a positive rational multiple of s times a polynomial whose degree-ten Bernstein coefficients are all strictly positive. Exact checker: scripts/check_erdos1041_concyclic_smallest_gap_selector_counterexample.py; Lean core: ConcyclicSmallestGapSelectorCounterexample.lean. SCOPE: angular gap size alone cannot select the pair. Another adjacent pair may still work; Form A, the concyclic case, and Erdos #1041 remain open.

Concentric-alternation Conjecture U is FALSE at n=5 and s=3/20. Five exact Gaussian-rational unit roots and five exact unit test directions place a strict violating point in every closed root gap; the squared margins above (1+s^5)^2 are 0.0019145, 0.0191028, 0.0078963, 0.0070978 and 0.0021883. Exact Fraction checker: scripts/check_erdos1041_concyclic_alternation_counterexample.py; rational core Lean-checked in ConcyclicAlternationCounterexample.lean. The earlier 930-check battery never entered this basin, which is negative_results entry 19 applying again. SCOPE: this refutes only the uniform regular-polygon majorant at prescribed radius. Form-A-cut V<=1 can choose its radius jointly with two spokes and remains open; the concyclic case and Erdos #1041 are untouched.

No polynomial-independent positive length slack is available, even for the quadratic Cassini family: root distances 2-2/m approach two. Any generic-perturbation reduction must preserve a starting-polynomial-dependent margin; a fixed global transfer budget is eliminated.

The same exact Cassini polynomial refutes the load-bearing tree-budget statements in both unrestricted drafts: Proposition 12 of the March manuscript and Proposition 7 of the shorter draft. At a=9/10 the component satisfies their Morse/distinct-critical-value hypotheses, but the true coarea budget is strictly below 41/25 while any connected set spanning the roots has length at least 9/5, a gap greater than 4/25. This is an independently checked polynomial counterexample to the printed metric propositions, stronger than the previously recorded local-sector criticism. It does not rule out a differently weighted Reeb theorem, a construction that explicitly pays attachment cost, or a direct two-root argument.

Pairwise distinct critical values or pairwise distinct critical-value moduli do not alone exclude saddle connections. What the Newton-flow identity naturally detects is pairwise distinct critical-value arguments.

A common constant translation preserves equality among initially equal critical values. The finite planar-avoidance theorem therefore closes ray separation only after a separate perturbation has made the critical-value family injective.

The checked critical-pair metric theorem cannot be completed by choosing its nearest and second-nearest roots and joining them to the critical point with straight segments. An exact balanced quintic makes the nearest root unique while its spoke exits the strict unit lemniscate. Any successful fan-in must use curved descending branches, another critical point, or the global component/Reeb geometry.

Curving the two spokes along the canonical descending inverse-ray branches at that same metric-selected critical point still does not close the argument. In the exact balanced quintic, one certified half-level waypoint on each branch forces their combined length above 2.083996. The surviving hub mechanism must select a different critical point using arc-length information, or use global component/Reeb geometry; mere Newton containment at the metric critical point is insufficient.

Direct root-chord selection is impossible in general: the exact cubic z^3-(99/100)^3 has all roots in the open unit disk, yet the midpoint of every distinct root pair lies outside |f|<1. The same cubic is joined by the two safe radial spokes through 0 with total length 99/50, so the result forces departure from a single chord but does not force curvature; it opens critical-point hubs and more general multi-segment or topological mechanisms.

The safe broken line through the origin in the cubic is not a universal replacement for direct chords. An exact five-root rational-complex configuration has four root-to-origin spokes with explicit waypoints satisfying |f|^2>1, leaving at most one safe spoke. Any fixed-origin two-spoke proof is therefore eliminated; hub selection must depend on the polynomial's critical or global component structure.

Selecting the critical point with minimum critical-value modulus still does not justify straight spokes. An exact degree-five Gaussian-rational witness has a unique first critical value below one but four unsafe root spokes from that critical point. The first-merge topology survives only with its curved inverse-ray branches or a different path.

Least-critical-value selection also fails for curved branch length itself. A pinned degree-four configuration has least-critical-value branch-pair length about 1.042608 at level 0.334325, while a later hub has shorter length about 0.841236 at level 0.362534. Thus the invariant target must retain the global minimum over critical hubs; first merge is not a valid uniform length selector.

Even allowing an adaptive choice between every root chord and every two-arm broken line through the minimum-enclosing-disk center does not extend the quartic proof. An exact degree-five Gaussian-rational configuration makes all ten chords unsafe and leaves at most one safe MEC radial arm. The unrestricted proof must use a polynomial-adapted non-MEC hub, curvature, or global component/Reeb geometry.

The exact radial-lift area identity controls an angular L1 average, not the discrete sum over critical-value rays. For f_epsilon(z)=z^n+epsilon*z-r^n, all n-1 simple critical-value arguments coalesce at pi, and repeating the limiting complete-ray lift majorant already exceeds the target 2(n-1) scale. Direct unweighted coarea-average sampling is eliminated; only a multiplicity-aware descending-edge or Reeb charge remains live for the aggregate conjecture.

The June 2026 quartic theorem does not close the unrestricted problem.

The degree-three theorem's own spoke inequality does not generalise. It proves containment in the hub sublevel set {|f| <= |f(c)|}, and an exact Gaussian-rational quartic with all roots in the open unit disk has, at every admissible critical point, at most one sublevel-contained straight spoke. The failure occurs in an arbitrarily small neighbourhood of the extremal family z^n - r^n, where the radial spokes satisfy |f(t z_k)| = r^n(1 - t^n) with equality only at t = 0, so sublevel containment there is marginal and a generic perturbation breaks it. A deterministic stress family breaks it at every degree from four to eight and never at degree three. This does not refute the weaker open-lemniscate containment, which survives on the same witness.

Selecting the two nearest roots at the minimal-critical-value hub and asking for sublevel-contained spokes is false: a degree-twelve configuration sends the second-nearest root's spoke to |f|/|f(c)| = 2.28318003178603 at t = 0.716, confirmed at 60 digits. The second-nearest root need not lie in a component adjacent to the hub.

Normalising at the minimal-critical-value hub does not put two roots inside the closed unit disk. With P(u) = 1 + u^2 R(u), P(0) = 1, P'(0) = 0 and |P(kappa)| >= 1 at every critical point, adversarial search drove the second-smallest root modulus to 1.080244757 at degree four and 1.037279478 at degree five. The length bound must come from the Lean-checked critical-pair metric scale's sum |u|_(1) + |u|_(2) <= 2, not from bounding each root.

The total inverse-ray tree length obeys no bound n|v|^{1/n}. The pure power z^n - r^n attains equality, which made the bound look canonical, but a degree-three edge configuration reaches ratio 1.065658. Relatedly the two branches that merge at a critical point are not a typical pair: their share of the total tree length reaches 0.999066 against an average share 2/n = 0.25 at degree eight. Any argument that bounds the whole inverse-ray tree and then takes two of n branches is eliminated.

Straight two-spoke paths through a single critical point are eliminated from degree five. The degree-five witness is a near-Fekete quintic: a 1e-5 angular perturbation of the fifth roots of unity at modulus 1 - 1e-9, angles 0.99998979, 0.2, 0.4, 0.6, 0.8 of a turn. Its four critical points sit at |c| about 0.05 with |f''| about 3e-3 -- the spread of the 4-fold critical point that z^5 - r^5 has at the origin -- and no critical hub carries two contained spokes: two have |f(c)| > 1 and are inadmissible, and the other two contain exactly one spoke each. It appeared at 1 failure in 1500 under near-Fekete seeding after a random degree-five sample of the same exact test had reported zero failures; the hard regime is the one HardRegimeIsNearFekete.md already identifies. Provenance is weaker than the witnesses below: it is recorded as a measurement in CriticalBudgetLab.md (commit 343ef99ad3), not stored as an exact IEEE-754 hexadecimal literal, and that commit shipped no probe and no receipt. Erdos #1041 is not refuted there -- the ORIGIN, which is not a critical point in this configuration, gives a certified two-segment path of length 1.999999998. So the honest degree-five statement needs the union of both hubs, and the two failure modes are disjoint: the exact rational MEC falsifier of AdaptiveMecDichotomyLab.md kills chord-plus-origin and is rescued by a critical hub at 1.218210, while this quintic kills the critical hubs and is rescued by the origin. Pendyala's quartic proof uses the origin route; the corpus's surviving front is the critical route. Witnesses at degree six and degree nine, with all roots strictly inside the open unit disk, have every admissible critical point carrying at most one root whose straight spoke stays in {|f| < 1}; verified at 60 digits with f' residuals near 1e-61 and with segment maxima located from the roots of d|f|^2/dt rather than sampled. The degree-six witness has two admissible hubs at |f(c)| = 0.99995098599675816247 and 0.99995927525097869638, each with exactly one contained spoke; the degree-nine witness has three, each with exactly one. Erdos #1041 is not refuted at those configurations: the descending inverse-ray branch pairs give 1.763942 and 1.545995, and grid geodesics give 1.668784 and 1.395432. This confirms negative result 4 rather than relaxing it, and leaves the descending-branch arc length as the quantity to bound.

Methodological: an adversarial supremum pinned just below a threshold is not evidence that the threshold is never crossed. Maximising the straight-spoke hub objective directly gave suprema 1.999999688 through 1.928588184 for degrees three to twelve, never reaching two, while a differently seeded search over the same space found configurations where the objective is infinite. Report which basin a search explored, not only its record value.

No hub-by-hub argument can prove the surviving branch-length obligation. The per-hub strengthening L(c) <= 2 max_k |z_k - c| is tight on both equality families -- every quadratic and z^n - r^n -- but false in general: a pinned degree-four witness, stored as exact IEEE-754 literals with all roots at modulus below 0.782955 and an admissible hub at |f(c)| = 0.0318, reaches ratio 1.210001551. It is neither a boundary nor a level-one degeneracy, and at that same configuration the admissible-minimum ratio is only 0.306554. The minimum over admissible critical points is therefore load-bearing rather than a convenience of the argument.

The exact charge identity does not split into separately nonnegative pieces. A deterministic complete-hub sweep finds normalized total signed curvature support -0.1613048394826284, while an IEEE-pinned quartic gives root-star charge/R -0.004211433878039096 with the allocation identity closing within 8.9e-16. Therefore neither curvature-only positivity nor nonnegative charge at each root can prove the aggregate. Cancellation must couple endpoint deficit and curvature above root-star scale.

An admissible component cannot be normalized using only the circumradius of its own roots. A pinned degree-six two-cluster configuration has an inadmissible central merger and two nontrivial admissible components; one component has normalized local-radius charge -0.00014178329316116844, even though its charge against the global root circumradius is positive. External roots remain in f'/f and are metric data for every Newton trajectory.

The level condition |f(c)| <= R^n does not by itself imply the strong completion. Applied at an arbitrary critical point it fails on about one percent of hubs, reaching ratio 1.0556 at degree six. What the discriminant/Fekete sandwich supplies is a bound at the MINIMUM-critical hub, and it is minimality -- every component of {|f| < |f(c*)|} still holding exactly one root -- rather than the level that the strong completion depends on.

Engine boundary for descending-branch integration: at a DEGENERATE critical point the two-branch substitution f(z(u)) = (1-u^2) f(c) is the wrong local model. All n preimages are equidistant from the hub and the field is stiff at the start, so descending_pair under-reports the length there -- on z^n - r^n it returns 1.7989 against the true 2r = 1.8 at degree six, and the deficit does not shrink with the start offset. The under-report is in the conservative direction for the length conjectures, but equality families must be asserted from their ordinary proofs rather than from the integrator.

The turning-inflation route is refuted at every degree n >= 3. The chain L(c) <= (d1+d2)/cos(alpha_max/2) <= 2R cannot close: the budget d1+d2 <= 2R is saturated exactly on z^n - r^n (max ratio 1.000000000000 over 24048 critical points), where phi = 2pi/n, so the turning floor forces alpha_max >= pi/2 - pi/n and the chain returns at best 2R sec(pi/4 - pi/(2n)) = 1.0353, 1.0824, 1.1223, 1.1547, 1.1810, 1.2027 times 2R for n = 3..8, equal to 2R only at n = 2. Not a basin record: the worst ratio increases monotonically as the extremal parameter eps -> 0 at every degree, and it fails on the bit-exact QC witnesses with no search (degree 6 gives 1.100817 and 1.138117 at both hubs). Supremum is +infinity, since alpha exceeds pi at 5/436 clean hubs (max 224.03 deg) making the bound vacuous. The recorded alpha = 0 on the extremal family holds only at the DEGENERATE hub of multiplicity n-1; a simple hub's two branches leave back-to-back and cannot follow two radii meeting at 2pi/n. Receipt scripts/check_erdos1041_turning_inflation.py.

The first-merge-hub conditional theorem's spoke claim is false. Its step 3, that each spoke [z_a, c*] stays inside {|f| < 1} at the least-critical-value hub, fails on this directory's own stored exact witnesses: at degree 6 a nearest-root spoke reaches |f| = 1.0000093332434161438 at t = 0.87625888 and at degree 9 it reaches 1.0000103851845920825 at t = 0.80548221, both above 1, so the nearest-pair broken line leaves the lemniscate. The length half does not fail there: d1+d2 is 1.717 and 1.498, well inside the budget. Containment breaks, not the budget. The adversarial attack on the claim topped out at 0.986769 and missed violations of size ~1e-5 at max root modulus 0.99999985. Receipt scripts/check_erdos1041_first_merge_hub_claims.py.

The reciprocal sweep cannot join two roots on the extremal family: {|g| < 1} splits into n components, one per root, meeting only at z = 0 where |g| = 1 exactly. So transfer question 2's root-attachment charge has nothing to charge there, independently of the 2*pi*n Crofton budget, and any sweep-based proof must supply its own component-crossing mechanism at level exactly one.

The recorded MIN and AVG ceilings are not ceilings. CriticalBudgetLab.md's table reads max min_c L_c as 1.852321 / 1.634226 / 1.592300 at n = 4,5,6 and max normalized aggregate as 0.904177 / 0.822727 / 0.746591 / 0.680409 at n = 4..7, concluding both are tight at n = 3 and only there. The extremal family z^n - r^n gives min_c L_c = 2r and normalized aggregate r at EVERY degree, so both suprema are attained in the limit r -> 1 at every n. Confirmed through the corpus's own machinery: perturbing the extremal family by 1e-9 at r = 0.999 gives minimum two-root budgets 1.998000, 1.996981, 1.998001 at n = 4,5,6. Consequence: no degree-dependent slack exists and any argument must be tight at every degree.

The strong statement L(c*) <= 2 rho, rho = T*^(1/n), is refuted at degree four with worst ratio 1.004246913 (mu = 0.9670225538632438 at 50 digits, L = 1.9917262723, 2 rho = 1.9833033547), pair and length identical across six tolerances 1e-8 to 1e-13 with endpoint error 1.7e-14. CAVEATS, load-bearing: the two smallest critical values agree to 2.30e-9 relative, at the runner-up hub the ratio is 0.9608, the violation dies under a 1e-3 perturbation (0/12), and every violation found has critical-value separation below about 1e-6; under a slightly wider tie-tolerant selector it would not stand. This is what MinimumCriticalNewtonHubLab.md predicted -- a crossing above one kills only the strong statement, and the scale-normalized 2R completion is untouched.

The merge-topology branch bound L_branch(c -> a) <= n|f(c)|/|f'(a)| is refuted at every degree and appears UNBOUNDED in the degree: max over hubs runs 1.069, 1.151, 1.258, 1.272, 1.416, 1.471, 1.438, 1.557, 1.613, 1.628, 1.721, 1.733 for n = 3..14, monotone with no ceiling. Equality on z^n - r^n confirmed to 1e-16. The c*-restricted form, which is what the paired route needs, also fails at degree 3 with ratio 1.006770882 (endpoint error 1.0e-14) and robustly: 12/12 perturbations at 1e-4 still violate. Recorded as apparently unbounded, not as a bound.

The summed merge-topology bound n mu (1/|f'(a)| + 1/|f'(b)|) <= 2R is refuted by an exact identity and is unbounded. On f(z) = z(z^(n-1) - r^(n-1)) the ratio equals n^((n-2)/(n-1))/2 independent of r, reaching 13.340007 at n=30. Also refuted at degree 3 (1.0162361) and on the bit-exact hex witnesses at 60 digits (1.00031579... degree 6, 1.00013757... degree 9) under both R conventions. Not a symmetry artifact: breaking the (n-1)-fold symmetry at eps=0.01 moves the degree-8 value only from 2.096481 to 2.074570. The failure is first order -- the ratio's excess grows linearly in the perturbation (~1.9x per doubling) while the Fekete deficit that would protect it grows superlinearly (~2.5x) -- so it fails in every neighbourhood of the extremal family.

Hub selection dominates the form of the bound: 196 of 197 observed symmetric-bound violations sit at NON-minimal hubs. At minimum-critical hubs there is 1 violation in 480 branches (worst 1.0068); at non-minimal hubs, 196 in 1466 (worst 1.5784), and the worst offenders all have |f(c)| about 0.99 or above.

RETRACTION, 2026-08-23 (commit b071f556b8 retracting 558e07a20d): a claim that the second-root premise is FALSE at degree four is withdrawn. It tested |w| <= 1, only the CRUDE sufficient form of criterion (SC) in GeneralSpokeIdentity.md. Against the sharp form max_t (1-t)|Q(t)| <= 1, two roots pass at all three stored witnesses and both spokes are contained. The correct sufficient condition is also weaker than stated: since spoke length is lambda|w_i| with lambda = |f(c)|^(1/n) < 1, two roots satisfying (SC) with |w_1|+|w_2| <= 2 suffice, and the sum never binds in sampling (35430/35430 at n=3, 23988/23988 at n=4, 7970/7970 at n=5). Configurations where fewer than two roots pass (SC) do exist from degree four, but at three examined directly two spokes were still contained, so SC failure does not establish containment failure. The degree-four boundary remains settled by StraightSpokeHubCriterionLab.md section 2, not by that commit.

Instrument defect class, both members biased the SAME way. A descending branch parameterised by f(z)=v(1-s^m) suffers (a) scale truncation -- a hub that is simple yet NEARLY degenerate, i.e. the entire near-Fekete regime, crosses many decades of |z-c| inside a vanishing range of s, and plain Gauss-Legendre on [0,1] silently drops the inner journey; and (b) loss of sigma to rounding once sigma < eps_mach, after which Newton collapses the branch back onto the hub. Both UNDER-report length, i.e. both flatter the surviving obligation min_c L(c) <= 2R. Fixes: a geometric mesh [0,2^-K],...,[1/2,1], and shifted coordinates solving Q(w)=f(c+w)-v = -v sigma whose constant term is exactly zero. With both, the integrator returns 2r to 3.9e-16 on the equality family z^n-r^n at n=3..7 -- the case where StraightSpokeHubCriterionLab.md records this directory's integrator returning 1.7989 against 1.8 at degree six -- and reproduces both stored hard witnesses (1.763941902 vs 1.763942, 1.545995147 vs 1.545995). Separately, an APPROXIMATE smallest enclosing circle inflates R, which sits in the obligation's denominator and again flatters the conjecture: Badoiu-Clarkson at 3000 steps returned R=1.0000724 for the degree-6 witness whose roots all have modulus 0.99999985. Compute the MEC exactly over pairs and triples.

The STRONG completion L(c*) <= 2|f(c*)|^{1/n} is NOT refuted near Fekete. A float64 similarity-normalised search reported a strong ratio 1.0000018874 at n=4 in the Fekete basin; certified at 50 digits on the near-Fekete family it is strictly below one at every point, rising to 1 from below as eps -> 0 (n=3: 0.99999980 at eps=1e-12; n=6: 0.99783784). The float64 reading was inside that engine's own error bar. Recorded because this directory has four prior retracted counterexamples of exactly this shape, and because a search-engine error bar must be certified rather than assumed.

The reported start-direction defect in system.lib.formal_math_lemniscate does not reproduce as a locator problem. A Taylor locator solving a_n d^n + ... + a_2 d^2 + u^2 v = 0 in d = z - c was added and compared with the level-root locator over 778 hubs spanning generic and near-Fekete configurations down to perturbation scale 1e-7: they agree in arc length to 1e-13 and in start direction to 1e-13. The residual angular error is real, not an artifact. At finite u the two descent directions are opposite only to order u, with correction O(u a_3/a_2), and a_2 = f''(c)/2 tends to zero as the hub approaches a degenerate one. Measured deviation from exactly-opposite at u = 1e-6: 1.6e-6 rad generic, 6.7e-2 rad on a near-Fekete shell at scale 1e-6, 1.7e-1 rad at scale 1e-7, identically for both locators. The operative rule is therefore a step-size criterion -- u small compared with |a_2/a_3| times the angular accuracy wanted -- and no choice of locator substitutes for it. descending_pair keeps its original default since changing it would move landed receipts for no measured gain.

The disjunction 'one safe root chord OR two safe radial arms through the minimum enclosing disc centre' fails already at DEGREE THREE, which is minimal: for n = 2 the chord between the two roots is always safe, since on [a,b] one has |f| = t(1-t)|a-b|^2 <= |a-b|^2/4 <= 1. The witness is L(7+24i)/25, L(7-24i)/25, -L with L = 999/1000, three Gaussian rationals of common modulus L < 1. Positive rational barycentric weights (25/64, 25/64, 7/32) annihilate the three unit directions, so the origin is strictly inside their hull and D(0,L) is the minimum enclosing disc, making the centre hub the origin. Exact rational evaluation gives |f|^2 > 1 at the midpoint of all three root chords and at t = 1/10 on two of the three origin spokes, so no chord is safe and at most one radial arm is safe. This lowers the recorded degree-five elimination adaptive_mec_chord_or_radial_counterexample to the minimal degree and supplies its mechanism: with all roots on a common circle of radius L, the spoke to a_j starts at |f(0)| = L^n and has initial log-derivative -Re(conj(p_1) a_j)/L, so only roots in the closed half plane Re(conj(p_1) z) >= 0 can carry a contained spoke, and that half plane can hold exactly one root even though sum_j Re(conj(p_1) a_j) = |p_1|^2 >= 0. The consequence is that the critical-hub family is NOT redundant: chords and the centre hub can be empty at the same configuration. Erdos #1041 is untouched; its degree-three case is proved in CubicCriticalHub.md by a critical-point hub.

Correction, 2026-08-24, to exact_results::two_safe_origin_spokes_counterexample. That entry records 'at most one safe root-to-origin spoke' for r=99999/100000 with roots r, r(-20+-99i)/101, r(-28+-195i)/197, having checked four of the five. Exact Gaussian-rational evaluation of the fifth gives ZERO safe spokes: each of the five carries a rational waypoint t in (0,1) with |f(t z_j)|^2 > 1, verified in Fraction arithmetic and stored in erdos1041_visibility_overlap_receipt.json. The witness is sharper than recorded. It is also the row that forces the visibility-overlap reduction to be stated on the FIRST-MERGE component rather than the component of the origin: all five roots sit at modulus r, so a path from 0 to a root has about 1e-5 of length budget while every straight spoke is excluded and the cheapest corridor detour costs about 7.7e-5. At mu = 0.00477 the first-merge component is a small neighbourhood of the two roots that are 3.2 degrees apart and does not contain the origin, so the reduction is unaffected -- but the level in (COVER) is not free.

The capacity-geodesic bound (C) does NOT halve per lobe under the minimum-critical-value hub selector, but the failure is confined to near-ties and the min-over-hubs form is untouched. At level mu the lobes meet only at c*, so geo = geo(a,c*) + geo(b,c*), inviting geo(a,c*) <= rho = mu^{1/n} on each lobe -- an equality on both extremal families and a ONE-lobe statement with f conformal onto a disk. An exact degree-four witness (roots stored as IEEE-754 hex in scripts/check_erdos1041_capacity_geodesic.py::PERLOBE_WITNESS, all four moduli in 0.98489..0.99841) has merging-pair d/rho = (0.9932938, 1.0003912) at the minimum-critical hub, so one merging root is strictly farther from c* than the geometric mean. The refutation is exact -- d is a distance between two computed points, and geo >= d -- but it is a SELECTOR result, not a statement about the problem: the two smallest critical values agree to 1.55e-6, at the runner-up hub the ratio is 0.9924758 and at the third 0.9988951, and a tie-guarded adversarial climb (rejecting critsep < 1.001) tops out at 0.9192 at n=4 and 0.8545 at n=5, falling to 0.6664 and 0.5582 at guard 1.2. This is the same shape as entry 28's own caveat and both of its checks were run. The pair budget holds at every hub of the witness (0.9968, 0.9660, 0.9518). Consequence for method: a min-critical-hub proof of (C) must spend the two lobes against each other. Consequence for gap 1 of FirstMergeReductionState.md: the same witness has merging pair != nearest pair, but only inside that tie -- over 440 bulk draws across six families and every tie-guarded climb the merging pair WAS the pair nearest c*, so no tie-free separation is on file and the gap is still open in the direction that matters.

Self-correction, 2026-08-24, same session, to visibility_overlap_reduction_to_a_one_root_statement. The first landed measurement of (COVER) fixed the level at lambda = 1.01*mu. Adversarial hill-climbing on that objective BREAKS it at degree three: roots -0.044684909847+0.962379872660i, -0.866609339080-0.498987227711i, 0.864151412519-0.503231891122i (two exactly on |z|=1), mu = 0.9577745241, give sup dist = 1.0349, stable under grid refinement from step 0.0174 through 0.0035 while the pair geodesic converges cleanly 1.7945 -> 1.7682, so it is NOT a discretisation artefact. It refutes only the FIXED-LEVEL reading. Scanning the level gives 0.9427 at 1.0005*mu, 0.9543 at 1.002*mu, 1.0349 at 1.01*mu, 0.9950 at 1.03*mu and 0.9937 at lambda = 1, so the existential statement holds there with 0.057 to spare. The constant is NOT MONOTONE in the level: raising it both adds points to cover and adds shortcuts, and at a further merge the shortcuts win discontinuously -- here the drop from 1.0349 to 0.9950 happens exactly when the third root joins the component. Consequence: any measurement of (COVER) that fixes a level will report false violations. With the level scanned, the 38-row corpus worst case improves from 1.01886 to 1.00578, the scale-free ratio from 1.02325 to 1.00678, and the worst pair geodesic from 2.00400 to 1.99800 -- the last being the exact closed form 2r at z^2 - 0.999^2, so the apparent excess above 2 was pure discretisation. Receipt arm `levels`.

Instrument-defect class, FIFTH reproduction, 2026-08-24, new cause. A probe that traces the descending Newton branch pair from c* and then scores a containment statement on the traced arc fails at a DEGENERATE minimising hub, and fails in the direction that looks like a refutation. On z^8 - 0.999^8 the sevenfold critical point at the origin resolves numerically into a cloud of radius 5.1e-3; the tracer starts from a spurious hub at -0.0016+0.0048i and the arc it returns contains points with |f| = 1.166 > 1 -- the traced curve has LEFT the lemniscate. Scored naively that reads as two points of the arc seeing neither root, i.e. as a covering failure, at precisely the family where the covering is provable in closed form (on z^n - r^n the branches are the radial segments and |f(s r w)| = r^n(1-s^n) <= r^n). This is negative_results entry 24's class with a different consequence: entry 24 records that a degenerate hub makes the two-branch substitution UNDER-report length, which flatters the conjecture; here it makes a containment probe OVER-report failure. General rule, not stated by entry 24: a traced curve must be verified to lie in the region before any containment statement is scored on it. Two guards are now in the receipt arm `path` -- reject a minimising hub with another critical point within 1e-3, and require max over the traced arc of |f| <= 1 before scoring -- and the excluded rows are receipted, never silently dropped, with the extremal family settled instead by the closed-form arm.

ONE-SPOKE is FALSE at n = 5, and the falsifier was already on file. The equality-stratum stress statement of visibility_overlap_reduction_to_a_one_root_statement -- for w_1..w_n on the unit circle some j has prod_k |t w_j - w_k| <= 1 for every t in [0,1] -- is refuted by an exact Gaussian-rational countermodel landed concurrently by codex_root at commit 9fede2b363 (checker formal_math/probes/erdos1041_one_spoke_countermodel.py) and RE-VERIFIED INDEPENDENTLY here in Fraction arithmetic and again by exact segment maxima. The five points 1, (-20+-99i)/101, (-28+-195i)/197 have squared moduli exactly 1, and at t = 339/1000, 1/1000, 1/1000, 1/500, 1/500 the five products are 1.000335336109477, 1.000124073322536 (twice) and 1.000171161469739 (twice), all above one; the exact maxima over [0,1] are 1.010340874179, 1.000778858212 (twice), 1.000387427136 (twice). Those five directions are exactly the ones of exact_results::two_safe_origin_spokes_counterexample, whose roots are r times them at r = 99999/100000, where this directory's own correction already records ZERO safe spokes -- so the refutation was in hand and was not connected to the statement it refutes. Sampling could not have found it: at n = 3 the two-dimensional configuration space was SWEPT over 519841 grid configurations with the objective never positive, so the failure is invisible at degree three, and 20000 randomised configurations at degrees 3 to 12 produced no violation at all with mean safe-spoke count 4.409. negative_results entry 19 applies to the file that recorded it. What survives from that search is only a negative: four natural crowding statistics pick a safe spoke 99.19, 98.87, 93.02 and 89.41 per cent of the time, so even where a safe spoke exists it is not named by any of them. SCOPE: this retires the ONE-SPOKE stress statement only. It is not a necessary condition for (COVER) -- the equality stratum needs |g(h)| = 1 hence lambda = 1, and at lambda = mu that stratum is empty away from the exact regular n-gon. The countermodel configuration has mu = 0.00477, its first-merge component is a small neighbourhood of the two roots that are 3.2 degrees apart and does not contain the centre, and both the covermu and path arms pass on it. The visibility-overlap lemma, the reduction, and Erdos #1041 are untouched.

Instrument defect, new location, same class as entry 34 and biased the same way. The Form A-cut hub radius s must be searched on a LOGARITHMIC grid: the optimum sits at s ~ eta^{1/(n-1)}, a fractional power of the perturbation, so a uniform grid on [tau, 1] with 200 points (step 5e-3) cannot resolve an optimum near 1e-2 and reports an INFLATED V, i.e. it errs against the mechanism. It corrupted the measured cusp exponent to 1.08 instead of 1.5 in one degree-three direction. With a log grid plus the endpoint s = tau the nine degree-three directions land in [1.501, 1.540]. A first exponent table computed on the uniform grid read 1.519/1.337/1.260/1.20/1.17 at n = 3..7 and is withdrawn.

Instrument-defect class, SIXTH reproduction, 2026-08-24, new location and new cause -- and a fix that generalises. rho_Omega(a,b) = exp(-g_Omega(a,b)) is the dangerous quantity in Theorem C' of BergmanGeodesicInvariance.md, and a grid Laplace solve for g places Dirichlet data on cells just OUTSIDE the mask, i.e. solves on a slightly LARGER domain, so g is too large, rho too small and the bound too small -- the direction that flatters the conjecture, as in entries 24, 34 and 41. In the regime that matters, a component pinched at a near-degenerate hub so that rho -> 1 and g -> 0, the O(dx) boundary error is the SAME SIZE as g. An unguarded run reported three settlements at the hardest recorded configurations -- near-Fekete quintic 1.681, degree-6 QC=infinity 1.515, degree-9 QC=infinity 1.353, all 'bound < 2' -- and a two-resolution Richardson guard with the verdict taken at min(g) - 2*spread turns ALL THREE into 'rho indistinguishable from 1', i.e. undecidable. The three settlements are RETRACTED. The fix is not a finer grid: Corollary G' expresses the same number through the CONFORMAL RADIUS, prod_{j!=i} rho_Omega(a_i,a_j) = r_Omega(a_i)|f'(a_i)|/t, and r_Omega is O(1), so the same solve delivers it to O(dx) RELATIVE accuracy and in the conservative direction -- measured above the closed form at every tested (n,r,t) by 0.6% to 2.6%, halving with dx. GENERAL RULE, extending the class: when a bound depends on a quantity only through its logarithm near a degeneracy, do not sample the quantity -- find an identity carrying it through a non-degenerate one. Separately, a float64 evaluation of the same closed-form reach reports spurious cut-offs at the 1e-15 level from n = 10 on; the recorded table is mpmath at 50 digits.

The most-antipodal-good-pair selector for Form A-cut is FALSE. The chord's only positive near-field term is -sigma^n Re(w^n), largest where the chord is farthest from the origin, so the natural rule is to take the two good rays that are most nearly antipodal. Exact segment maxima refute it at 3 of 48 near-Fekete configurations: V = 1.0287764761 (n=10, eta=1e-1, angular), 1.0003866137 (n=8, eta=1e-2) and 1.0000002022 (n=10, eta=1e-5) -- the last arbitrarily close to the regular polygon, so this is not a large-perturbation artefact. The mechanism is that the extreme rays of the good arc are the ones closest to the line Re(E_1 zeta) = 0, hence contribute the weakest negative linear term. The correct rule is the ADJACENT good pair (exact_results::form_a_cut_adjacent_good_pair_selector). Form A-cut itself is untouched: the free optimum is below one at every refuting row.

Instrument-defect class, SEVENTH reproduction, 2026-08-24, and the FIRST member that biases the OTHER way. Entries 24, 34, 41 and 44 all record instruments that UNDER-report and therefore flatter a conjecture. This one OVER-reports and manufactures refutations. On the wrapping gap A_n = (phi_n, phi_1 + 2 pi) of a concyclic configuration, a critical point selected by a test modulo 2 pi is returned in [0, 2 pi) and can therefore sit numerically BELOW the arc's left endpoint a = phi_n. Handed unlifted to a bracketed local refinement it inverts the bracket, and the refinement then reports values from OUTSIDE the arc. In a 660-configuration sweep of ConcyclicAlternation.md this produced 11 false violations of the theorem's own conclusion max_{A_k}|g| <= 2 -- readings of 2.42, 3.17, 3.59, 5.74 -- and an adversarial 'record' of 25.24 against a budget of 2, every one of them pure bookkeeping. A 4e5-point brute-force cross-check on 400 configurations returns worst 1.894 against the budget. FIX: after any modular selection from a cyclic interval, lift into that interval's own branch, psi <- a + ((psi - a) mod 2 pi), before any bracketed step. GENERAL RULE, extending the class: a selection defect can point either way, so an apparent REFUTATION deserves the same instrument audit that this directory already demands for an apparent confirmation. Receipt state/formal_math/erdos257_period_noncollapse/erdos1041_concyclic_alternation_receipt.json.

Instrument-defect class, same session, the ordinary under-reporting direction, at a new location. For zeros on the unit circle |g(e^{i psi})|^2 = x^{-n} P(x) with P = g*h of degree 2n, and the critical points solve x P'(x) - n P(x) = 0. That polynomial is the right LOCATOR and the wrong EVALUATOR: for clustered zeros it cancels catastrophically and returns values about 1e-8 relative below the truth, which flatters every containment statement scored on it. A second face of the same defect: filtering the locator's roots for the unit circle at | |x| - 1 | < 1e-6 silently DROPS true circle roots at ill-conditioned configurations, and a dropped critical point can only lower a reported maximum. Fix: locate with the polynomial, evaluate in the stable product form prod_k |2 sin((psi - phi_k)/2)| in log space; widen the circle filter to 1e-3; and add a dense grid safety net so the locator is never trusted alone.

The obvious Fekete-deficit split of the concyclic case is a BAD decomposition, and the chord family is why. With D = prod_{i<j}|w_i-w_j|^2 / n^n the deficit of a concyclic configuration, climbing min_k max over the chord [w_k,w_{k+1}] of |g| inside D-bins gives a clean monotone envelope whose crossing of the level 1 DECREASES with degree: D* is about 0.87, 0.68, 0.51, 0.42, 0.32 at n = 3,4,5,6,7. Below D* the plain chord already certifies Erdos #1041 at EVERY radius rho < 1, not only rho <= 2^{-1/n}. But the near-Fekete cusp analysis of NearFeketeCuspLaw.md is a leading-order expansion valid only as D -> 1, so the band D* < D < 1 is covered from neither side and it WIDENS with n. Consequence for method: a deficit split must use a path family whose objective reaches 1 at the regular n-gon -- the Form A-cut family of TruncatedSpokeReduction.md, whose concyclic objective is measured at exactly 1 there -- not the chord, whose objective is 1 + cos^n(pi/n) > 1 there. This does not weaken the radius-hypothesis corollary of concyclic_alternation_theorem, which never mentions the deficit.

The proposed two-segment level identity V_E=mu and its necessary condition SPOKE>=1 are FALSE. A degree-seven polynomial with seven exact dyadic roots strictly in the open unit disk has six critical points isolated by disjoint radius-1e-12 Rouche disks, a unique least critical value mu=0.8158048440849527910... separated from the next value 0.8163950933409540163..., and ZERO root spokes contained in {|f|<=mu}. Seven pinned dyadic waypoints give exact squared-value gaps from 2.83325e-5 to 8.77604e-3, while the complete interval-transfer errors are at most 1.61e-8. Any two-arm connection at the unique first-merge level must contain the merge point and hence a safe root subsegment, so V_E>mu. Exact Fraction checker: scripts/check_erdos1041_two_segment_level_identity_refutation.py; abstract gate implication Lean-checked in TwoSegmentLevelIdentityRefutation.lean. SCOPE: the weaker level-one free-hub conjecture V_E<=1, COVER, and Erdos #1041 are untouched; the witness has mu about 0.816 and ample room below level one.

Complete-spoke selection on a general tied near-Fekete Newton face is FALSE already in the exact quintic homogeneous model H(z)=Re(z+10z^2-z^5). Every fifth-root ray has an explicit positive waypoint: the three conjugacy types escape at t=1/10, 1/1000, and 3/10. The radical inequalities and the negation of a globally nonpositive ray are Lean checked. This is a mechanism no-go, not a counterexample to Form A-cut or Erdős #1041: on the same model, the adjacent ray types 1,2 are safe outward from radius 2 and their radius-two connector satisfies H<=-5 by an exact two-piece Bernstein certificate. The result therefore proves that truncated connectors are logically necessary on tied faces and closes this first face with the correct object.

Greedy minimum-real-critical-value selection is FALSE for adjacent tied-face containment. For Q(z)=-(379/256)z+3z^2-z^5, c=1/4 is proved to uniquely minimize Re Q over all four critical points, yet Q(2/3)=6677/31104>0 and every cutoff puts 2/3 on either the finite positive-real arm or its outward tail. Both adjacent pairs bracketing arg c contain that ray, so the selected hub can never furnish the required certificate. The derivative factorization, real-root comparison, Viete conjugate-pair gap, and cutoff dichotomy are Lean checked and symbolically replayed. SCOPE: this refutes only the ordering rule; another negative critical hub may work, and the existential adjacent selector and Erdős #1041 remain open.

Universal upper bounds for every finite-contact KKT system are FALSE. The exact quartic of CriticalEllipseStationaryNoGo.md has a one-contact critical KKT hub strictly above Gcrit, but it is a saddle and a different feasible hub lies below Gcrit. The corrected variational target is the minimum over the KKT locus, augmented by second-order necessary conditions; one above-threshold stationary branch does not refute FP-GM or Erdős #1041.

Universal adjacent pairing of the unique two-ended tied-face component is FALSE. The symmetric quintic Q(z)=-(65/27)z+(100/27)z^2-z^5 has exactly one negative critical point and its unique two-ended negative component joins nonadjacent sectors. The same component has a strict exact nonadjacent two-arm/tail connector, so adjacency is the false selector and free-pair geometry survives.

Fixed least-critical/two-nearest-root CE--GM is FALSE in minimal degree four. The exact unit-disc quartic of CEGMQuarticFixedPairNoGo.md has its selected roots in different components at level Gcrit, separated by a rational circle on which |g| is strictly larger. No hub or path of any shape rescues the fixed pair. The surviving statement is joint free-pair FP-GM; unrestricted Erdős #1041 remains open.

Horizontal-fibre negativity is FALSE hub by hub even on negative critical points, and the returned Leftmost-Fibre Inequality LF is false. For Q(z)=15z+5z^2-z^5, c=-1 is the unique leftmost critical point with Q(c)=-9; its conjugate lifts of the leftward real ray escape in sectors exp(+/-2pi i/5), and chord displacement forces delta_Q(c)>=(sqrt(5)-1)/2>0. SCOPE: this does not refute the existential producer min over all negative critical points delta_Q(c)<0. It proves broader minimization or a component aggregate is load-bearing and that paired-trace or leftmost-critical validity alone cannot select the metric hub.

Pointwise full-fibre L1 contraction is FALSE even under the strict critical-value half-plane hypothesis. For x=1001/1000, epsilon=x^3+3x-4=6003001/10^9, P(z)=z^6+3z^2-epsilon has every critical value on Re w=-epsilon<0. On the simple fibre P(z)=4 with s=2^(1/3), exact factorization through y=z^2 and rational radical bounds give sum_j |z_j'(s)| > 44510696/7409649 = 6+52802/7409649. SCOPE: the resultant product and signed moment identities remain true, and this does not refute component-block, externally weighted, weak-majorization, or integrated monodromy-loop inequalities. Those are now the live fibre-selector residuals.

Pointwise component-block L1 contraction is also FALSE in the exact target topology. For x=999/1000 and epsilon=x^3+3x-4=-5997001/10^9, Q(z)=-z^6-3z^2+epsilon has five simple critical points and every critical value has real part epsilon<0. The component passport gives 6 sheets minus 5 ramification units equals one component of {Re Q<0}, so the fibre Q=-4 is one six-ended monodromy block. The same exact factorization and rational radical certificate give sum_j |z_j'(2^(1/3))| > 6+52802/7409649. SCOPE: because the block is the entire fibre, complementary external-factor weighting is constant and cannot repair this specimen. The surviving fibre producers are internal two-sheet weak majorization, loop-dependent weights, or integrated monodromy action; unrestricted Erdős #1041 remains open.

The canonical fixed-point-free contour obtained by separately resolving every radial critical-value slit is metrically too expensive. For a ray-separated k-sheet component, its average complete-lift length has liminf at least (2/k) sum_c L(c), because the contour traverses both sides of every critical arm. A chord lower bound makes this exceed two for generic normalized cubics near an equilateral triangle and quartics near a square, even though the monodromy is a full cycle. Exact source and checker: SeparateCriticalContourNoGo.md and scripts/check_erdos1041_separate_critical_contour_no_go.py. SCOPE: only the fully resolved separate-slit lollipop is retired. Grouped critical-value contours, which can charge a near-coincident cluster once, remain live; Erdős 1041 is untouched.

The universal sharp componentwise radial-contour criterion RC4 returned on 2026-08-28 is FALSE already for P(z)=z^2-(5/6)^2. The multi-root component begins only at t=(5/6)^2 and has perimeter at least 10/3; below merger the two one-root level loops contribute at least 4(sqrt(r^2+s)-sqrt(r^2-s)). Exact integration gives a total lower bound 4r+(4r/pi)(2sqrt(2)-2log(1+sqrt(2)))>4 using only pi<22/7 and elementary radical inequalities. SCOPE: this retires only a universal RC4 estimate. A target-deciding dichotomy or compensation theorem, grouped or partial-cluster monodromy, and unrestricted Erdős 1041 remain open.

The pairwise-comonotonicity strengthening of FP radial monotonicity is FALSE exactly. For c=(-9/10,-3/4,-1/2,-1/4) and radial parameter x=1/4, A_1=454859867/819200000 < A_2=2588047/4194304 while G_1=1170425808/454859867 > G_2=26878032/12940235. Hence T_j=A_j^(1/4) and G_j are not similarly ordered, so the unweighted power-sum identity cannot be upgraded by a direct Chebyshev/rearrangement argument. SCOPE: the full weighted sum remains positive on the specimen, so RM and FP4 remain open; the live RM target is a global compensation identity or weighted power-sum representation.

Every unweighted four-column row-factor-permutation Holder proof of FP4 is obstructed exactly on the triangle-plus-origin family. The origin row is (1,1,1,1) and each triangle row permutes v=(D,D,1,x), D=sqrt(1+u+u^2), x=1-u. The aligned column sums 1+3v majorize every other assignment, so concavity of log makes their product the pointwise minimum over all row permutations. At u=1/6 this minimum is 329/2+14sqrt(43)=256+(28sqrt(43)-183)/2>256, with 28^2*43=33712>33489=183^2. SCOPE: this strictly extends the dedicated-x symmetric no-go to the complete unweighted permutation class. Weighted/product-merged M2, X, deletion schemes, RM, PM4, FP4, and unrestricted Erdos 1041 remain open.

Nonpositive quadratic branch energy is NOT a necessary bridge to the canonical pair L1 excess inequality, even at the exact quintic tangent orbit. In the normalized gauge G(V)=V^5+40V^2-60V, exact interval integration gives the canonical-pair quadratic energy Q_G>3833966005559069387/8181640000000000000. Since 40^(-1/3)>29/100, the original-gauge energy is >29/1000>0, while the existing exact tangent certificate proves the actual pair L1 excess is strictly negative (diagnostic values about +0.31205 versus -0.0363). Exact source and checker: QuinticTangentQuadraticBridgeObstruction.md and scripts/check_erdos1041_quintic_tangent_quadratic_bridge_obstruction.py. SCOPE: this kills only quadratic-energy nonpositivity as a necessary canonical-pair bridge. Direct L1, moved-block, entropy, and integrated monodromy routes remain live; unrestricted Erdos 1041 remains open.

The present square-root-free fixed-strip support schedule cannot extend the common positive quintic cusp collar beyond u=1/1000. On the exact microcell [1/1000,1001/1000000], all three upper carrier sheets are Krawczyk-isolated and exhaustive; the two strong sheets have support uppers -0.425739800 and -0.963900937, but the weak-sheet majorant is +0.556429559 and is already +0.549879571 at u=1/1000. Parameter refinement therefore cannot repair this fixed-strip schedule. Exact source and checker: QuinticWeightedCuspSupportBridge.md and scripts/check_erdos1041_quintic_weighted_cusp_support_bridge.py. SCOPE: this is a certificate-method obstruction, NOT a sign counterexample. The proved five-sheet collar 0<=u<=1/1000 remains valid with weakest transported excess upper -0.02354340; a sharper adaptive cone, direct L1, or different transport invariant is required.

The componentwise combined-charge inequality and the full admissible critical-arc product are both FALSE, on an OPEN family, not merely at an isolated specimen. On the blown-up saddle-wall quartic f(z)=z^4-a(s rho)^2 z^2+(b+i delta)(s rho)^3 z-s^4 with a=1, b=2/5, rho=1/50, delta=1e-6, s=0.99989 - four simple roots strictly inside the open unit disc, three simple critical points, every critical value admissible, one admissible component - the three canonical two-arm inverse-ray lengths sum to 6.000253120901 against 6R=5.999939963992, so by the exact tangent-support identity 2R-L(e)=D_e+K_e the component charge is -3.13e-04, and the admissible product is prod q_j=1.000451748764>1. SCOPE, and it is the whole point: this retires two proposed proof MECHANISMS, not Erdos 1041, which the same family SATISFIES - the shortest arm is 1.995615925599 below 2R=1.999979987997, giving a root-to-root path of length below 2 inside {|f|<1}. Every hub's two arms reach distinct roots. The order-sensitive trimmed product over the two smallest ratios is 0.998107041600<1 and survives; every differentiable symmetric monotone aggregate of the three ratios has the WRONG first-order sign, since the first-order vector ((x2+kappa)/2, kappa, (kappa-x2)/2) has positive coordinate sum 2 kappa while its smallest coordinate is negative. Exact checker: ErdosProblems/Erdos1041/scripts/check_saddle_wall_aggregate_refutation.py, receipt state/formal_math/erdos1041/saddle_wall_aggregate_refutation_receipt.json, stable across three tolerance settings with arm-sum spread 1.07e-12. METHOD WARNING: summing chords along a resampled polyline undercounts the curved continuation near the saddle by enough to put sum L BELOW 6R and reverse the finding; arc length must be carried as an integrated ODE state. Lean scalar kernel: ErdosProblems/Erdos1041/MechanismSeparationScalarKernel.lean, declarations wallBaux_one_third_factor, wallN_one_third_factor, wallN_nonneg, wallN_eq_cleared_slope, slope_defect_nonneg, sqrt_excess_le, curved_excess_lt_third, wall_sign_pattern, smooth_symmetric_aggregate_first_order_sign - the slope bound sigma^2<=1/3 that forces 3 kappa < x2, and the intercept algebra B1+B2+B3=-4 kappa with B2+B3=x2-3 kappa>0. NOT formalised: the arm-length continuation itself, which is finite computational evidence.

Universal merge-node forcing of the connected-cluster Bergman certificate is FALSE. The certificate itself remains CORRECT and its consumer ConnectedClusterBergman.length_le_two_of_cluster_certificate is untouched; what fails is the universal claim that every polynomial has SOME merge-tree node satisfying it. On z^n-r^n at r=99/100 the barrier alpha_C log((1+q^(2/k))/(1-q^(2/k))) is bounded below by r^2 artanh(r^2)=2.2543196280541 at EVERY regular level and in EVERY degree, with the exact rational certificate 2541/1250=2+41/1250 obtained from (1+x0)/(1-x0)=19801/199>64 and log 2>56/81. The degree-free petal-area bound Area(E_{n,r})>=pi r^2/2 comes from Jensen against int log(2 cos theta)=0 and is what makes the failure degree-independent. Threshold: x*=0.968364434984413, r*=0.984055097534896. SCOPE: the parent is TRUE on the same family - z^n-r^n has the two-spoke path through 0 of length 2r<2 - so this retires a proof route, not the problem, and two-node interpolation using the same scalar (alpha_C, q_C) certificate is excluded too, because the failure covers every regular level and not only critical levels. Lean scalar kernel: ErdosProblems/Erdos1041/MechanismSeparationScalarKernel.lean, declarations log_two_gt_56_div_81, regular_ratio_gt_sixty_four, log_sixty_four_gt, rational_cluster_margin, rational_cluster_margin_gt_two, clusterBarrierScalar, clusterBarrierScalar_mono, clusterBarrier_gt_two_of_lower_bounds, artanhWeight_strictMonoOn, artanhWeight_r_sq_gt_two. NOT formalised: the petal-area Jensen argument, the arm-length continuation, and Riemann-Hurwitz.

The unrestricted two-tail selector conjecture for tetranomials is FALSE. CyclicTetranomialCoefficientCase.md section 4 records, as evidence for a next selector conjecture, that an unrestricted probe over 6,348 configurations never found fewer than two roots with |c+b w^s|<1, and asks whether two roots must satisfy the tail bound |a w^r+w^m|<1 even when the coefficient budget fails. Take r=99/100 and F(z)=z^6+(5/2)r^2 z^4+(5/2)r^4 z^2+r^6. Its quotient w^3+(5/2)w^2+(5/2)w+1 factors as (w+1)(w^2+(3/2)w+1) with all roots unimodular, so every root of F has modulus r<1. At every quotient root the recorded tail is r^6(1+(5/2)zeta) with |zeta|=1, so its modulus is at least (3/2)r^6, and exactly (3/2)r^6-1 = 824440448203/2000000000000 > 0. ZERO roots satisfy the tail bound. SCOPE: this refutes the conjecture and its numerical evidence only; no proved theorem of that file is contradicted, since |b|+|c| = 3342970174401/1000000000000 > 1 there, and the sextic satisfies Erdos 1041 by the centred-circle quadrinomial arc certificate (CentredCircleQuadrinomialConnector.md), with a connector of length (r/2)arccos(3/4) < pi/5 on which |F| < 3-sqrt(5).

A universal tail or radial selector for four-term polynomials cannot exist as stated, because the exceptional exponent relation n=3k with |a|>sqrt(3) is exactly the family in which the radial certificate can fail at EVERY root while the target conclusion still holds through a non-radial short circular arc. SCOPE: this constrains the shape of any future selector; it says nothing about Erdos 1041 itself.

The sharp affine coefficient does not remove the pinching divergence of the Bergman route. Testing the reversible kernel of ChordConditionedBergman.md on the mean-zero function sgn gives lam(x) >= 1 - log(1+x)/artanh(x), hence lam(x)*log(1/(1-rho^2)) >= log(1/(1-rho^2)) - 4 log(1+x) -> infinity as x -> 1. Therefore no choice of the affine coefficient in L^2 - d^2 <= lam(E - d^2), including the optimal one, keeps the whole-component bound finite when the two marked points become hyperbolically separated at bounded area. On z^n - r^n at level 1 with r -> 1 the refined bound is ineffective at every fixed degree. SCOPE: a limitation of the estimate; that family is settled by its two radial arms of length 2r < 2, so it is not evidence against the parent.

The low-critical potential mechanism of LowCriticalPotentialClosure.md cannot reach mu close to 1 by any choice of constants: its two failure inequalities (COVER forces arity, boundary-hop forces area growth) need a failure window (mu,1) of logarithmic length at least about 1.61 to contradict Polya's area cap, because the extremal counterexample trajectory rides with forced arity between six and seven and area growth near 0.4 per unit of log t. The exact comparison ODE gives 0.19989 in every degree, so 1/5 is unreachable by this mechanism and the surviving regime 0.197 < mu < 1 requires a different tool. SCOPE: a limitation of the mechanism; the near-Fekete shell is addressed by other corpus results.

## Open implications

### free_pair_geometric_mean_two_arm_selector

Prove FP--GM: for a monic polynomial with roots in the closed unit disc, jointly choose distinct roots a_i,a_j and a hub h with |h-a_i|+|h-a_j|<=2 such that both hub arms lie in {|f|<=Gcrit}. Minimum-enclosing-disc scaling then gives length <2 and level <1 for open-disc roots. Do NOT prescribe the least-critical nearest pair: CEGMQuarticFixedPairNoGo.md refutes that selector in minimal degree four, with the selected roots in distinct Gcrit components. The finite KKT reduction remains usable only after the pair is included in the minimization; universal pointwise KKT upper bounds are also refuted by CriticalEllipseStationaryNoGo.md. Noncritical hubs are essential candidates. The augmented barycentric target disc gives exact local reach in every direction when target slack is positive, but its flow estimate controls action rather than arclength. Near Fekete, the component-degree theorem selects the complete noncrossing end block and removes angular adjacency. TiedNewtonFaceHorizontalFibreHubwiseNoGo.md proves that even the unique leftmost critical point can have delta_Q(c)>0, so do not demand HF negativity at every paired-trace or leftmost saddle. The same face is strictly rescued by TiedNewtonFacePositiveFibreRationalRescue.md using an unrelated rational noncritical hub; its fixed connector remains valid on the explicit coefficient box of l_infinity radius 1/6 with Bernstein margin 196/9375, confirming that direct finite charts are strictly more flexible than canonical fibres and already have transfer room. TiedNewtonFaceFibreProduct.md gives exact all-branch product contraction and the stronger moment system sum z_j^ell z_j'=0 through ell=n-2; product plus the zero moment is insufficient, so any fibre completion must exploit higher moments together with component monodromy. Otherwise prove min over all negative critical points delta_Q(c)<0, a component aggregate forcing a good point, or an all-degree finite intrinsic connector directly. The non-strict delta<=0 version still needs equality rigidity because zero may be approached from above. Then compose with a genuinely resolved finite near-Fekete transfer. Away from Fekete, connected-cluster Bergman, COVER, and combined charge remain independent consumers. Computation is falsifier evidence only. UPDATE 2026-09-05: PinnedWitnessNoncriticalHubConnectors.md supplies exact FP-GM shaped witnesses for the noncritical-hub clause on the two hardest stored configurations: fixed Gaussian hubs h_6=(3+2i)/25 and h_9=-1/5-4i/25, verified noncritical in exact arithmetic, both arms contained in {|f| < 99999/100000}, total lengths 29471595/2^24 < 1.757 and 12825029/2^23 < 1.529, valid on explicit 1e-9 root neighbourhoods. These are existence witnesses with the hub supplied; the producer still needs a rule producing h from the configuration, and the certified level leaves only about 4e-5 of margin at the hub value, so any selector must be quantitative at that scale.

Evidence/status: see the source; no formal status inferred

- [check_erdos1041_cegm_quartic_fixed_pair_no_go.py](problem/scripts/check_erdos1041_cegm_quartic_fixed_pair_no_go.py)

### fixed_safe_monodromy_block_average_lift_length

Prove the integrated monodromy producer in any one of its three exact forms. For every generic normalized hard polynomial, either (i) construct a fixed moved-sheet block B with |B|>=2 and based value-plane loops inside the closed unit disc whose average complete-lift length has limsup at most 2; (ii) construct a budgeted loop whose monodromy is fixed-point-free on B; or (iii) prove a whole-block average bound at most 2 together with a fixed-sheet average lower bound at least 2. FixedBlockQuadraticBudgetEquivalence.md proves that optimizing the returned lifetime weights gives exactly the average-length formulation and that (ii) or (iii) suffices to select a moved lift. Its sharp three-sheet countermodel shows nontrivial monodromy plus a whole-block average is not enough when a cheap fixed sheet absorbs the budget. SeparateCriticalContourNoGo.md proves that circling the fully resolved radial critical-value star gives a full cycle but double-charges every critical arm and misses the metric budget on generic cubic and quartic hard examples. GroupedCriticalClusterMonodromy.md supplies the exact repair locally in every degree: for z^n-r^n a single circle around the whole critical cluster has lift length 2r-2(1-pi/n)q^(1/n)<2 for a suitable q, and the full-cycle certificate persists on an open coefficient neighbourhood. PartialCriticalClusterMonodromyLab.md then proves that a contour enclosing any connected admissible edge subtree cycles exactly its incident moved block and fixes the complement. Pinned candidate computations on the stored degree-six and degree-nine hard witnesses isolate their two and three admissible critical values inside the unit value disk and report moved-block means 1.84327 and 1.63875, even though an individual moved lift exceeds two in each row. The exact residual is to prove or interval-certify this partial-cluster moved-block average, then convert failure into a complementary Bergman merge-node certificate or into quantitative merge-tree/discriminant cluster control. Once this producer is proved, whole-lift selection, convex projection, compactness, and strictification give Erdős 1041. The source-current full-fibre angular theorem does not imply any of the three forms because its short branches may spend compensation on monodromy-fixed sheets. Do not cite charged lifetime, complete fibre moments, the monodromy-loop representation, fixed-point-free topology, or the floating-point witness rows alone as if they supplied the missing metric allocation. UPDATE 2026-09-05: the pinned degree-six and degree-nine rows with moved-block means 1.84327 and 1.63875 are settled configurations (PinnedWitnessNoncriticalHubConnectors.md) and must not be credited as remaining evidence for this producer; the moved-block average stays open as the general mechanism. TraceCurvatureMeasureAndPolygonalShortening.md improves the local lollipop rung (coefficient 1-sin(pi/n) for 1-pi/n, admissibility relaxed by cos^n(pi/n), explicit coefficient box). ChordConditionedBergman.md adds the moved-sheet endpoint charge (1-lam) sum_M (4-d_j^2) > 4 lam nfix as an alternative currency, conditional on unsupplied holomorphic extensions and an energy budget. Neither supplies the moved-block metric allocation; the trace-curvature log-moment bound is global and must not be cited as bounding 2 Lambda(alpha,W)+Per(W) on one block.

Evidence/status: see the source; no formal status inferred

- [check_erdos1041_fixed_block_quadratic_budget.py](problem/scripts/check_erdos1041_fixed_block_quadratic_budget.py)

### sextic_second_mode_mixed_neighborhood_transfer

RESIDUAL BAND CLOSED 2026-08-25 by sextic_chord_covering_criterion_and_unit_band: the adjacent unit chord covers |A|<=|B| for EVERY real tangent cubic with margin 1/256 and connector length 1, strictly containing the old residual |E1|/|E2|<3/4 and overlapping the first-mode ray chart on a quarter-width band. The |E3|/rho^3<=470 compactness box and the mixed finite atlas are no longer needed for homogeneous coverage. WHAT REMAINS is the nonlinear actual-polynomial transfer alone. Its binding constant is NOT 127/3072: that holds only on |A|<=3|B|/4. The honest global constant is 1/768, set by the first-mode ray chart just above |A|=|B| where the connector has length 31/16 and length slack only 1/16; on |A|<=|B| the chord gives margin 1/256 with length slack 1. Absorb the origin-anchored O(eta^2|z|) remainder against 1/768, choosing the chord chart wherever |A|<=|B|.

Evidence/status: see the source; no formal status inferred

- [check_erdos1041_sextic_cubic_paired_deficit_cone.py](problem/scripts/check_erdos1041_sextic_cubic_paired_deficit_cone.py)

### critical_point_selection_with_inverse_ray_length_control

Prove the componentwise combined-charge lemma. For each nontrivial connected component C of the admissible critical forest, show sum_{e in C}(D_e+K_e)>=0, where D_e=(R+<a,U_a>)+(R+<b,U_b>) uses the global root circumradius R and K_e=integral_e kappa<z,N> ds. The exact identity 2R-L(e)=D_e+K_e then yields sum_{e in C}L(e)<=2R|E(C)|; summing and averaging gives min_{|f(c)|<1}L(c)<=2R, and R<1 solves the problem. On each Newton half-edge d arg T=-Im((f''/f')dz), so attack the component boundary using cyclic critical-ray order and the argument principle while retaining external-root factors in f'/f. Do not require K alone to be positive, allocate charge root by root, replace R by the component-root circumradius, take absolute curvature, drop admissibility, or sample raw angular coarea: each is now falsified or structurally insufficient.

Evidence/status: see the source; no formal status inferred

- [check_erdos1041_invariant_branch_length.py](problem/scripts/check_erdos1041_invariant_branch_length.py)

### one_root_covering_of_the_first_merge_component

Prove (COVER): for monic g with roots in the closed unit disk there is a level lambda in [mu,1] and a compact CONNECTED subset Gamma of the first-merge component of {|g| <= lambda} carrying two roots, such that every point of Gamma lies within intrinsic distance 1 of a root of g, paths being allowed to run in the whole component. By visibility_overlap_reduction_to_a_one_root_statement this settles Erdos #1041, with no separate length obligation. Take Gamma as SMALL as possible and the ambient as LARGE as possible: the cheapest Gamma is the descending Newton branch pair from c*, on which the covering was measured in its strongest form -- straight segments at level 1 -- with zero uncovered points over 26 scored rows at 283 points per arc, at least 155 overlap points per row, and worst overlap length 1.90422 against a budget of 2. Two guards are mandatory: the level is NOT monotone, so never fix one (a fixed 1.01*mu reads 1.0349 where 1.0005*mu reads 0.9427); and a traced arc must be verified to lie in {|g| <= 1} before scoring, since at a degenerate hub the tracer leaves the lemniscate and reports a false covering failure. Do NOT route through the equality-stratum statement ONE-SPOKE: it is FALSE at n = 5 and is not necessary for (COVER). Do NOT strengthen to straight segments in general, to the nearest root, or to the Newton descent (on z(z-1) the descent from e^{i pi/3} has length 1.366 while the straight segment to 0 has length exactly 1). UPDATE 2026-09-05: LowCriticalPotentialClosure.md shows what COVER failure alone buys when played against boundary-hop failure across the whole level window: an unconditional parent regime mu <= 197/1000 in every degree. COVER itself stays open; the exact obstruction to pushing the same mechanism further is recorded (the failure window must have logarithmic length about 1.61).

Evidence/status: see the source; no formal status inferred

- [check_erdos1041_visibility_overlap.py](problem/scripts/check_erdos1041_visibility_overlap.py)

### concyclic_form_a_cut_objective_below_one

Prove the concyclic case of Erdos #1041 in ONE inequality. For w_1..w_n distinct on the unit circle, g = prod(z - w_k), tau_j = sup{t in [0,1] : |g(t w_j)| > 1}, define the Form A-cut objective of TruncatedSpokeReduction.md, V = min over pairs (i,j), min over s >= max(tau_i, tau_j), of max over the chord [s w_i, s w_j] of |g|. Prove V <= 1. Because the Form A-cut path w_i -> s w_i -> s w_j -> w_j has length 2(1-s) + 2 s sin(theta_ij) <= 2 for EVERY admissible s, this settles Erdos #1041 for ALL concyclic zeros at EVERY radius rho < 1: scaling gives |f| = rho^n |g| <= rho^n < 1 on the path and length <= 2 rho < 2. Equality holds exactly at the regular n-gon, in the limit s -> 0, where the path degenerates to the pair of radii of length exactly 2 -- so this is the one path family that reaches the problem's own extremal configuration, which is why concyclic_alternation_theorem's chord family cannot replace it (its value there is 1 + cos^n(pi/n) > 1). ROUTE: the exact structure is unusually strong here. log|g| is HARMONIC on the open disk with log|g(0)| = 0 exactly, log|g(t zeta)| = -sum_m (t^m/m) Re(conj(sigma_m) zeta^m) with sigma_m the power sums, and radial_resultant_sweep_identity gives sum_j log|g(t w_j)| = -sum_m (t^m/m)|sigma_m|^2 <= 0 for every t, so at every radius some root direction is good -- the L^1 statement. The obligation is the L^infinity upgrade PLUS the connecting chord. Do NOT route through ONE-SPOKE (full radial spokes), which negative_results entry 42 refutes at n = 5; truncation at s > 0 deletes exactly the first-order germ at the origin that the refutation exploits. Do NOT route through a plain-chord Fekete-deficit split: the chord envelope crosses 1 at D* about 0.87, 0.68, 0.51, 0.42, 0.32 at n = 3..7, a threshold that FALLS with degree, while the near-Fekete cusp expansion is valid only as D -> 1, so the middle band is covered from neither side and widens with n. CALIBRATION landed 2026-08-24: adversarial hill climbing seeded on the regular n-gon at perturbation scales 1e-1 down to 1e-6 (adjacent pairs, s swept on a joint linear+geometric grid with local refinement) reaches V = 1.000000000000 at n = 3 and 0.999999999841, 0.999999999787, 0.999999997390 at n = 4, 5, 6 -- the maximum is the regular n-gon and the objective never crosses 1. Earlier random-configuration sweeps read worst V = 0.982, 0.854, 0.456, 0.554, 0.172, 0.239 at n = 3..8, so the constraint binds only in the near-regular shell, exactly as HardRegimeIsNearFekete.md predicts. The measurement is NOT a proof and negative_results entry 19 applies: a supremum pinned at a threshold is one basin. Degrees 7 to 10 of that sweep are NOT on file: the run that produced n = 3..6 was a scratchpad process and its remaining rows were never landed. Re-derive with ./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_concyclic_form_a_cut.py 7 -- it prints one row per degree and takes roughly ten minutes past n = 6 on an M4. Do not quote n >= 7 until that rerun exists. UPDATE 2026-08-25: degrees 7..10 adversarial rerun LANDED (seed 20260825): regular V = 1.000000000000 at every degree; worst near-regular excesses -4.588e-08 (n=10), -2.369e-08 (7), -1.167e-08 (8), -2.094e-08 (9), -1.839e-09 (6); never crosses 1 -- the do-not-quote-n>=7 stricture is discharged (measurement only, entry 19 applies). Exact certificate criterion + Lean potential-domination kernel landed (ConcyclicPotentialBound.lean, ConcyclicFormACutCertificate.md). First-moment-only certificates are PROVEN INFEASIBLE for n>=4 (mid-range spokes need multi-harmonic data), so the surviving route is joint cluster/cone bookkeeping: opposite-side clustering that inflates log(1+t) factors also rotates s_1 into the used gap, converting those factors to log(1-t) damping. Concentric-alternation law (Conjecture U): min_k max_{G_k} log|g(s e^{i psi})| <= log(1+s^n) at every s, equality iff regular -- measured at float-noise slack over 930 checks n=3..8 including adversarial shells (receipt erdos1041_concyclic_fac_certificate_receipt.json, PASS); NOT provable by transporting the s=1 alternation (no circle zeros at s<1, hence no sign input).

Evidence/status: see the source; no formal status inferred

- [check_erdos1041_concyclic_form_a_cut.py](problem/scripts/check_erdos1041_concyclic_form_a_cut.py)

### sextic_unrestricted_chord_covering_band

Prove the covering criterion min_{j even} S_j + min_{j odd} S_j <= 0 on the band 1 < |A| < 12.46 at |B|=1, the exact gap between the certified unit band (Theorem 3) and the large-first-mode theorem (Theorem 6) of SexticChordCoveringCriterion.md. Success would retire the first-mode ray chart entirely for the homogeneous model and give connector length 1 with length slack 1 everywhere, replacing slack 1/16. NOTHING IS UNCOVERED without it: the landed first-mode chart already handles |A|>=3|B|/4, so this is an architecture and transfer-constant improvement, not a coverage hole. ROUTE: the criterion decouples into two independent one-dimensional suprema, so attack S_j directly; mixed (non-antipodal) pairs are what wins here, and Theorem 5 proves the antipodal pair genuinely dies at Re(beta)=-9/28. Numerical diagnostic in the receipt shows the criterion at -32.1 at |A|=1 falling to -454 at |A|=5, with mixed pairs winning throughout; that is EVIDENCE FOR A PRODUCER, NOT A THEOREM, and must not be promoted without the invariant. Do not reuse the pivot T=25u/12: Theorem 4 proves it is sharp at 1.0153 and lossy relative to a free pivot, which itself only reaches 1.3880.

Evidence/status: see the source; no formal status inferred

- [check_erdos1041_sextic_chord_covering_criterion.py](problem/scripts/check_erdos1041_sextic_chord_covering_criterion.py)
