# Z37_1: The signed Möbius–Mersenne moment ladder: exact two-atom curvature, controlled tails, and unconditional order-two Hankel negativity

[All problems and zones](BROWSER.md)

<a id="node-d9dd702ae1d09576"></a>
## every_shifted_order_two_hankel_minor_is_negative

For every r>=1, Θ_r Θ_{r+2}<Θ_{r+1}^2; equivalently, every shifted 2x2 Hankel determinant Θ_r Θ_{r+2}-Θ_{r+1}^2 of the full signed Möbius–Mersenne ladder is strictly negative.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Negative order-two Hankel minors show that (Θ_r) is not a positive-measure moment sequence. They are unrelated, without an additional theorem not present here, to whether Θ_2=S-1/2 or any other individual rung is rational.

- Lean declaration: [mobiusMersenneTheta_strict_logConcave](../../Erdos249257/SignedQMomentObstruction.lean#L730)
- Lean declaration: [mobiusMersenneTheta_hankel_two_neg](../../Erdos249257/SignedQMomentObstruction.lean#L740)

- outgoing **generalises**: [Z37::full_ladder_is_strictly_log_concave_from_rung_five](BROWSER_Z37_1.md#node-aa946dd750ec3246). The all-rung theorem contains the r>=5 result and extends it with the four finite certificates.
- outgoing **generalises**: [Z37::five_atom_certificate_closes_the_four_low_rungs](BROWSER_Z37_1.md#node-9547bb017f3f57f3). The all-rung theorem absorbs the separately verified r=1,2,3,4 cases into a uniform statement.
- outgoing **complements**: [Z37::first_two_ladder_rungs_locate_the_249_constant](BROWSER_Z37_1.md#node-510f55fc40be1246). The offset identity explains where #249 sits, while the Hankel theorem records only cross-rung curvature and explicitly does not settle that rung's rationality.
- incoming **complements**: [Z95::effective_signed_atomic_hankel_asymptotics](BROWSER_Z95_1.md#node-180f53a250583adc). The effective signed-atomic theorem gives every fixed order eventually in shift, while Z37 gives order two at every positive shift. Neither coverage statement is silently substituted for the other.

<a id="node-510f55fc40be1246"></a>
## first_two_ladder_rungs_locate_the_249_constant

The first ladder rung is exactly Θ_1=1/2, while the second is Θ_2=S-1/2 for S=sum_{n>=1} φ(n)2^{-n}, the Erdős #249 totient series.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The identities locate #249 inside the ladder. They do not show that Θ_2 or S is irrational.

Open hypotheses: ["The irrationality of S, equivalently of Θ_2 after adding the rational number 1/2, remains open."]

- Lean declaration: [mobiusMersenneTheta_one](../../Erdos249257/SignedQMomentObstruction.lean#L197)
- Lean declaration: [mobiusMersenneTheta_two_eq_totient_offset](../../Erdos249257/SignedQMomentObstruction.lean#L214)

- outgoing **specialises**: [Z37::mobius_mersenne_ladder_is_absolutely_convergent](BROWSER_Z37_1.md#node-4193ec8552848849). The exact first and second rungs specialise the convergent ladder and identify its connection to the #249 constant.
- incoming **complements**: [Z37::every_shifted_order_two_hankel_minor_is_negative](BROWSER_Z37_1.md#node-d9dd702ae1d09576). The offset identity explains where #249 sits, while the Hankel theorem records only cross-rung curvature and explicitly does not settle that rung's rationality.

<a id="node-9547bb017f3f57f3"></a>
## five_atom_certificate_closes_the_four_low_rungs

For 1<=r<5, Θ_r splits into the exact first-five-atom prefix 1-3^{-r}-7^{-r}-31^{-r} and a geometrically bounded residual; exact arithmetic checks of the resulting perturbation inequality prove strict log-concavity on all four low rungs.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is a finite base-case certificate for log-concavity. In particular, its r=2 instance does not decide the rationality of Θ_2 or the #249 constant.

- Lean declaration: [mobiusMersennePrefixFive](../../Erdos249257/SignedQMomentObstruction.lean#L569)
- Lean declaration: [mobiusMersenneTailAfterFive](../../Erdos249257/SignedQMomentObstruction.lean#L573)
- Lean declaration: [mobiusMersenneTailBoundFive](../../Erdos249257/SignedQMomentObstruction.lean#L577)
- Lean declaration: [mobiusMersenneTheta_eq_prefixFive_add_tail](../../Erdos249257/SignedQMomentObstruction.lean#L581)
- Lean declaration: [mobiusMersenneTailBoundFive_pos](../../Erdos249257/SignedQMomentObstruction.lean#L623)
- Lean declaration: [abs_mobiusMersenneTailAfterFive_le](../../Erdos249257/SignedQMomentObstruction.lean#L633)
- Lean declaration: [mobiusMersenneTheta_strict_logConcave_of_one_le_of_lt_five](../../Erdos249257/SignedQMomentObstruction.lean#L721)

- outgoing **complements**: [Z37::full_ladder_is_strictly_log_concave_from_rung_five](BROWSER_Z37_1.md#node-aa946dd750ec3246). The exact first-five-atom calculation covers precisely the four positive rungs omitted by the eventual contraction theorem.
- incoming **generalises**: [Z37::every_shifted_order_two_hankel_minor_is_negative](BROWSER_Z37_1.md#node-d9dd702ae1d09576). The all-rung theorem absorbs the separately verified r=1,2,3,4 cases into a uniform statement.

<a id="node-aa946dd750ec3246"></a>
## full_ladder_is_strictly_log_concave_from_rung_five

For every r>=5, the full infinite ladder satisfies Θ_r Θ_{r+2}<Θ_{r+1}^2: the two-atom positive gap survives the signed infinite tail perturbation.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Strict log-concavity is a structural analytic fact about the sequence of ladder values. It does not imply that any individual Θ_r is irrational.

- Lean declaration: [mobiusMersenneTheta_strict_logConcave_of_five_le](../../Erdos249257/SignedQMomentObstruction.lean#L534)

- outgoing **implies**: [Z37::tail_error_contracts_faster_than_the_dominant_gap](BROWSER_Z37_1.md#node-38b374de635425f4). The strict error-versus-gap margin is consumed by the perturbation inequality to preserve the positive Hankel gap on every rung at least five.
- incoming **complements**: [Z37::five_atom_certificate_closes_the_four_low_rungs](BROWSER_Z37_1.md#node-9547bb017f3f57f3). The exact first-five-atom calculation covers precisely the four positive rungs omitted by the eventual contraction theorem.
- incoming **generalises**: [Z37::every_shifted_order_two_hankel_minor_is_negative](BROWSER_Z37_1.md#node-d9dd702ae1d09576). The all-rung theorem contains the r>=5 result and extends it with the four finite certificates.

<a id="node-4193ec8552848849"></a>
## mobius_mersenne_ladder_is_absolutely_convergent

For r>=1, the Möbius–Mersenne atom μ(n+1)/(2^{n+1}-1)^r is bounded in norm by (2^{-r})^n; therefore the infinite ladder Θ_r is absolutely summable.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Absolute convergence only makes Θ_r and its finite-prefix decompositions well-defined. It supplies no irrationality or nonvanishing statement.

- Lean declaration: [mobiusMersenneTerm](../../Erdos249257/SignedQMomentObstruction.lean#L131)
- Lean declaration: [mobiusMersenneTheta](../../Erdos249257/SignedQMomentObstruction.lean#L136)
- Lean declaration: [norm_mobiusMersenneTerm_le_geometric](../../Erdos249257/SignedQMomentObstruction.lean#L155)
- Lean declaration: [summable_mobiusMersenneTerm](../../Erdos249257/SignedQMomentObstruction.lean#L185)

- incoming **specialises**: [Z37::first_two_ladder_rungs_locate_the_249_constant](BROWSER_Z37_1.md#node-510f55fc40be1246). The exact first and second rungs specialise the convergent ladder and identify its connection to the #249 constant.
- incoming **reformulates**: [Z37::two_atom_split_has_a_sharp_geometric_remainder](BROWSER_Z37_1.md#node-7cefa6829b1dd106). Absolute summability permits the ladder to be rewritten as its first two atoms plus the infinite residual.

<a id="node-38b374de635425f4"></a>
## tail_error_contracts_faster_than_the_dominant_gap

The closed tail bound B_r=1/(2^r(2^r-1)) is positive and contracts strictly faster than a factor 1/4. The induced Hankel perturbation budget E_r also contracts faster than 1/4, whereas the exact dominant gap G_r=4/3^{r+2} contracts by exactly 1/3; the verified base margin at r=5 therefore yields E_r<G_r for every r>=5.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The comparison proves enough room to preserve an order-two Hankel sign from rung 5 onward. It is not an irrationality estimate and gives no arithmetic denominator obstruction.

- Lean declaration: [mobiusMersenneTailBound](../../Erdos249257/SignedQMomentObstruction.lean#L330)
- Lean declaration: [mobiusMersenneHankelError](../../Erdos249257/SignedQMomentObstruction.lean#L334)
- Lean declaration: [mobiusMersenneDominantGap](../../Erdos249257/SignedQMomentObstruction.lean#L341)
- Lean declaration: [mobiusMersenneTailBound_pos](../../Erdos249257/SignedQMomentObstruction.lean#L344)
- Lean declaration: [mobiusMersenneTailBound_eq_geometric](../../Erdos249257/SignedQMomentObstruction.lean#L353)
- Lean declaration: [abs_mobiusMersenneTailAfterTwo_le_bound](../../Erdos249257/SignedQMomentObstruction.lean#L365)
- Lean declaration: [mobiusMersenneTailBound_sub_four_succ](../../Erdos249257/SignedQMomentObstruction.lean#L377)
- Lean declaration: [mobiusMersenneTailBound_succ_lt_quarter](../../Erdos249257/SignedQMomentObstruction.lean#L395)
- Lean declaration: [mobiusMersenneHankelError_succ_lt_quarter](../../Erdos249257/SignedQMomentObstruction.lean#L411)
- Lean declaration: [mobiusMersenneDominantGap_succ](../../Erdos249257/SignedQMomentObstruction.lean#L446)
- Lean declaration: [mobiusMersenneDominantGap_pos](../../Erdos249257/SignedQMomentObstruction.lean#L454)
- Lean declaration: [mobiusMersenneHankelError_lt_dominantGap](../../Erdos249257/SignedQMomentObstruction.lean#L461)
- Lean declaration: [mobiusMersenneTwoAtom_mem_unitInterval](../../Erdos249257/SignedQMomentObstruction.lean#L518)

- outgoing **transport_of**: [Z37::two_atom_model_has_exact_positive_hankel_gap](BROWSER_Z37_1.md#node-6f348bed3ecf5e32). The dominant gap is the exact positive margin transported through the quantified infinite-tail perturbation.
- outgoing **implies**: [Z37::two_atom_split_has_a_sharp_geometric_remainder](BROWSER_Z37_1.md#node-7cefa6829b1dd106). The closed bound packages the two-atom residual into the three-rung perturbation budget used by the Hankel comparison.
- incoming **implies**: [Z37::full_ladder_is_strictly_log_concave_from_rung_five](BROWSER_Z37_1.md#node-aa946dd750ec3246). The strict error-versus-gap margin is consumed by the perturbation inequality to preserve the positive Hankel gap on every rung at least five.

<a id="node-6f348bed3ecf5e32"></a>
## two_atom_model_has_exact_positive_hankel_gap

The two-atom model T_r=1-3^{-r} has exact shifted gap T_{r+1}^2-T_r T_{r+2}=4/3^{r+2}>0, hence is strictly log-concave at every nonnegative rung.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The theorem concerns the two-atom truncation, not yet the full infinite ladder and not the irrationality of any rung.

- Lean declaration: [mobiusMersenneTwoAtom_hankelGap](../../Erdos249257/SignedQMomentObstruction.lean#L311)
- Lean declaration: [mobiusMersenneTwoAtom_strict_logConcave](../../Erdos249257/SignedQMomentObstruction.lean#L320)

- outgoing **complements**: [Z37::two_atom_split_has_a_sharp_geometric_remainder](BROWSER_Z37_1.md#node-7cefa6829b1dd106). The exact curvature of the retained two-atom part is paired with the sharp enclosure of the omitted tail.
- incoming **transport_of**: [Z37::tail_error_contracts_faster_than_the_dominant_gap](BROWSER_Z37_1.md#node-38b374de635425f4). The dominant gap is the exact positive margin transported through the quantified infinite-tail perturbation.

<a id="node-7cefa6829b1dd106"></a>
## two_atom_split_has_a_sharp_geometric_remainder

For every r>=1, Θ_r splits exactly as (1-3^{-r}) plus the signed tail beginning at d=3, and the absolute value of that tail is at most (2^{-r})^2/(1-2^{-r}).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: This is an analytic decomposition. The tail bound alone neither determines the sign of Θ_r nor decides any rationality question.

- Lean declaration: [mobiusMersenneTwoAtom](../../Erdos249257/SignedQMomentObstruction.lean#L140)
- Lean declaration: [mobiusMersenneTailAfterTwo](../../Erdos249257/SignedQMomentObstruction.lean#L144)
- Lean declaration: [mobiusMersenneTheta_eq_twoAtom_add_tail](../../Erdos249257/SignedQMomentObstruction.lean#L234)
- Lean declaration: [abs_mobiusMersenneTailAfterTwo_le](../../Erdos249257/SignedQMomentObstruction.lean#L260)

- outgoing **reformulates**: [Z37::mobius_mersenne_ladder_is_absolutely_convergent](BROWSER_Z37_1.md#node-4193ec8552848849). Absolute summability permits the ladder to be rewritten as its first two atoms plus the infinite residual.
- incoming **complements**: [Z37::two_atom_model_has_exact_positive_hankel_gap](BROWSER_Z37_1.md#node-6f348bed3ecf5e32). The exact curvature of the retained two-atom part is paired with the sharp enclosure of the omitted tail.
- incoming **implies**: [Z37::tail_error_contracts_faster_than_the_dominant_gap](BROWSER_Z37_1.md#node-38b374de635425f4). The closed bound packages the two-atom residual into the three-rung perturbation budget used by the Hankel comparison.

