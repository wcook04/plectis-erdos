# Z95_1: Weighted free-point bounds, first-contact resonance and effective Hankel asymptotics

[All problems and zones](BROWSER.md)

<a id="node-a3ec961fe9b263de"></a>
## all_arity_unique_active_stationarity_exclusion

For m>=2, the fixed-product attached-ray selector has no positive-valued stationary point in a cell with a unique active ray, a unique nondegenerate interior radial optimizer, and all angular/radial constraints strict. Angular and radial stationarity force all points to coincide, contradicting unique activity. This removes every smooth single-active stationary stratum at every level, strengthening the returned level-one local-maximum exclusion.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Does not remove multi-active switches, optimizer switches, closed boundaries or the regular orbit.

- Ordinary mathematical proof (not Lean checked): [SmoothUniqueActiveContactExclusionAllArity.md](../../research_corpus/Erdos1041/formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/SmoothUniqueActiveContactExclusionAllArity.md)


<a id="node-180f53a250583adc"></a>
## effective_signed_atomic_hankel_asymptotics

For ordered nodes 1>=x_1>x_2>...>0, nonzero real a_j and A=sum |a_j|x_j<infinity, let X=product_(j<=N)x_j, Delta=product_(i<j<=N)(x_j-x_i), rho=x_(N+1)/x_N. The shifted moment determinant D_N(s) has leading term L(s)=(product_(j<=N)a_j) X^s Delta^2 and |D_N(s)/L(s)-1| <= A^N rho^(s-1)/(N! |product_(j<=N)a_j| X Delta^2), for s>=1. This proves effective eventual nonvanishing, eventual sign and infinite Hankel rank for the power Mobius-Mersenne ladder.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Not nonvanishing at every shift and not irrationality of P_2. Literal Lambert rank one and all-base totient rank were already Lean-checked.

- Ordinary mathematical proof (not Lean checked): [SignedAtomicHankelAsymptotics.md](../../research_corpus/Erdos249/formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos249/SignedAtomicHankelAsymptotics.md)

- outgoing **complements**: [Z37::every_shifted_order_two_hankel_minor_is_negative](BROWSER_Z37_1.md#node-d9dd702ae1d09576). The effective signed-atomic theorem gives every fixed order eventually in shift, while Z37 gives order two at every positive shift. Neither coverage statement is silently substituted for the other.

<a id="node-069a944580077782"></a>
## fresh_prime_first_contact_requires_single_step_valuation_resonance

If a_j is LCM-fresh and p^e exactly divides a_j, first later contact p|U_t requires t>=j+2 and v_p(a_(t-1))=v_p(Lambda_(t-1))>=e. Thus the entire source prime power must be paid in one overlap step, with residual-unit cancellation modulo p; many smaller payments cannot create first contact. Whole-modulus retirement and disjoint CRT-wall cumulative bounds follow.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Necessary contact condition, not a frequency theorem; global overlap-growth production remains open.

- Ordinary mathematical proof (not Lean checked): [R2CumulativePayment.md](../../research_corpus/Erdos243/formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/R2CumulativePayment.md)


<a id="node-5f7ca47a9a82aca7"></a>
## robust_merge_scalar_separation_and_one_root_bergman

For every n>=2 and r with r^2 artanh(r^2)>2, an open coefficient neighbourhood of z^n-r^n fails the connected-cluster scalar at every regular multi-root level, while a strict full-cycle lollipop proves the parent on that neighbourhood. For a regular degree-k component C of |f|<t and h in C, some root a has d_C(h,a)^2 <= Area(C)/pi log(1/(1-(|f(h)|/t)^(2/k))). A strict uniform bound below one over a connected root-carrying continuum gives a length-below-two connector.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The regular-polygon no-go was already known. Robustness and the explicit one-root composition are additional; no universal forcing or parent theorem is asserted.

- Ordinary mathematical proof (not Lean checked): [R2MergeNodeSeparation.md](../../research_corpus/Erdos1041/formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/R2MergeNodeSeparation.md)

- incoming **complements**: [Z95::weighted_quadratic_free_point_all_degrees](BROWSER_Z95_1.md#node-784fd18e307c0cd2). The all-degree critical-value mean supplies value control; the one-root Bergman bound addresses the separate intrinsic-length requirement. No implication to universal metric forcing is claimed.

<a id="node-efb38176b99918d6"></a>
## strict_rise_loglog_lcm_ordinary_rigidity

Under the canonical exact LCM orbit and quadratic-growth hypotheses, if some delta in (0,1) bounds -V_n by (1-delta) log_2 log_2 max(4,U_n) at every sufficiently late strict rise, the orbit is eventually zero. The exact Q_n bridge shows finite upper limsup Q_n/M_n implies eventual Sylvester recurrence. Two consecutive gcd-payment-free steps force -u_n u_(n+2) to be a unit square modulo u_(n+1).

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The log-log or LCM-prefactor bound is an extra hypothesis. The unrestricted parent remains open.

Open hypotheses: ["strict-rise logarithmic bound or bounded LCM prefactor, as stated"]

- Ordinary mathematical proof (not Lean checked): [R2CumulativePayment.md](../../research_corpus/Erdos243/formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos243/R2CumulativePayment.md)


<a id="node-784fd18e307c0cd2"></a>
## weighted_quadratic_free_point_all_degrees

For finitely many closed-disc points c_j and positive weights w_j summing to one, G(z)=product_k |1-conj(c_k)z|^{w_k} satisfies sum_j w_j G(c_j)^2 + sum_(nu>=1)(2nu-1)|a_nu|^2 <= 1, where a_nu are the Taylor coefficients of exp(sum_k w_k log(1-conj(c_k)z)). In particular sum_j w_j G(c_j)^2 <= 1-|sum_j w_j c_j|^2, with equality in the bound by one only at the origin configuration. Equal weights close FP_m for every m. The torus/psh bridge proves sum_j |f(w_j)|^{2/(n-1)} <= (n-1)R^{2n/(n-1)}, hence (S)_n in every degree.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Ordinary analytic proof. The critical-value mean does not supply the missing root-to-root metric connector.

- Ordinary mathematical proof (not Lean checked): [FreePointQuadraticAllDegrees.md](../../research_corpus/Erdos1041/formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/FreePointQuadraticAllDegrees.md)

- outgoing **complements**: [Z95::robust_merge_scalar_separation_and_one_root_bergman](BROWSER_Z95_1.md#node-5f7ca47a9a82aca7). The all-degree critical-value mean supplies value control; the one-root Bergman bound addresses the separate intrinsic-length requirement. No implication to universal metric forcing is claimed.

<a id="node-29f44e5ca1a0ca24"></a>
## zudilin_normalized_hankel_qorder_factorial_pattern

For every rank N, Zudilin's normalized Hankel determinant V_N^* at x=z=1 has q-order exactly N(N-1)(2N-1)/6 and leading coefficient exactly (N!)^2(N+1)!/2^N. The source backward-shift induction sharpens on the associated grade: for w_n(H,t), the leading coefficient after j transforms is (-1)^j[X^(j-t)]H_0(X)^(-1). The actual t=0 tail has reciprocal (1+X)/(1-X)^4, every t>=1 tail has reciprocal 1/(1-X)^3, and summing 0<=t<=j gives D_j v_(j+l)^*=(-1)^j(j+1)^2(j+2)/2 q^(j(j+1)/2+jl)+higher terms. Lean now defines both actual associated tail ratios and reciprocals, proves their coefficient formulas, specializes the all-depth recurrence, and proves the exact zero-plus-positive tail row scalar. It also defines each exact normalized source tail and the coefficientwise finite-tail moment at x=z=1, proves that the tail has exact order (n+1)t, zero coefficients below that shift, and leading coefficient one, proves the exact consecutive-index source-tail identity T_(n+1,t)=X^t T_(n,t)U_(n,t), clears both moving denominator factors of U_(n,t), proves U_(n,t)-1 vanishes below degree n+1, and proves its first associated coefficient is -5 at t=0 and -3 at every t>0. Lean further proves the exact Gaussian-binomial operator recurrence D_(j+1)=(1-X^jN)D_j on arbitrary power-series sequences and the resulting transformed-moment recurrence. This closes the first nontrivial transformed row in every column: ord(D_1v_(l+1)^*)=l+1 with leading coefficient -6. Lean also proves the lower-unitriangular row matrix has determinant one and preserves every power-series Hankel determinant, proves a generic unique-minimum Leibniz-order bridge, then identifies the associated-grade matrix as a diagonal scaling of a power-series Vandermonde matrix, proves its exact determinant product and all-rank noncancellation, computes its exact order as sum_(j<N)j^2, closes 6*ord=N(N-1)(2N-1), and checks the exact scaled factorial product for the row coefficients; the focused AdelicHeightBridge build and final serialized replay pass. The sole remaining Lean boundary is the entrywise initial-monomial theorem for rows j>=2 and all columns, iterating these exact filtered step identities. Thus hidden normalized-Hankel q-order is eliminated at all ranks as a source of extra cubic analytic decay; arithmetic denominator extraction or a different integral model is now mandatory. The finite checker regression-tests every tail contribution through rank seven. Receipt: state/formal_math/erdos257_period_noncollapse/erdos1049_hankel_qorder_receipt.json.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The full written argument is ordinary mathematics. Higher-row Lean formalization and the irrationality bridge remain open.

- Ordinary mathematical proof (not Lean checked): [FilteredReciprocalStateLifting.md](../../research_corpus/Erdos1049/formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1049/FilteredReciprocalStateLifting.md)


