# Z52_1: Fixed-rank totient curvature: extremal-ordering socket, primitive affine kernel, and clean-LCM divisibility

[All problems and zones](BROWSER.md)

<a id="node-8ae427f97243a90f"></a>
## affine_three_rank_kernel_is_uniquely_generated_by_one_minus_two_one

Every integer triple annihilating the constant and linear moments has c1=c3, c2=-2c3, and l1 norm 4|c3|.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Kernel uniqueness gives no information about whether the associated totient curvature is nonzero and supplies no extra two-adic factor.

- Lean declaration: [affine_rank_three_kernel_classification](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L338)

- incoming **finite_instance_of**: [Z52::fixed_rank_second_difference_is_the_primitive_three_point_curvature](BROWSER_Z52_1.md#node-fc013e7ef6e97f52). The fixed-rank second difference uses the primitive classified coefficient vector obtained by setting c3=1, namely (1,-2,1).

<a id="node-e9b901640fa1dd9a"></a>
## clean_power_two_lcm_curvature_is_divisible_by_twice_the_local_totient

For a at least four, j positive, and j^2<=2^a, the integer 2φ(j) divides fixedRankSecondDifference (periodLcm(2^a)) j.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Divisibility does not prove nonzero curvature, the extremal supply, a residue certificate, or irrationality. It does not imply stronger two-adic divisibility.

- Lean declaration: [two_mul_totient_dvd_fixedRankSecondDifference](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L519)

- outgoing **specialises**: [Z52::fixed_rank_second_difference_is_the_primitive_three_point_curvature](BROWSER_Z52_1.md#node-fc013e7ef6e97f52). The divisibility theorem restricts the general curvature to clean offsets at power-two LCM heights and proves an arithmetic property of that specialization.
- outgoing **complements**: [Z52::middle_rank_totient_extremality_is_the_local_ordering_socket](BROWSER_Z52_1.md#node-78f30bbe0567d000). Divisibility constrains the size lattice of the curvature, while the open extremal-ordering socket would provide independent nonvanishing.

<a id="node-fc013e7ef6e97f52"></a>
## fixed_rank_second_difference_is_the_primitive_three_point_curvature

fixedRankSecondDifference H j is the integer φ(3H+j)-2φ(2H+j)+φ(H+j).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The definition supplies no sign, nonvanishing, divisibility, asymptotic bound, certificate, or progress on Erdős #249.

- Lean declaration: [fixedRankSecondDifference](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L256)

- outgoing **finite_instance_of**: [Z52::affine_three_rank_kernel_is_uniquely_generated_by_one_minus_two_one](BROWSER_Z52_1.md#node-8ae427f97243a90f). The fixed-rank second difference uses the primitive classified coefficient vector obtained by setting c3=1, namely (1,-2,1).
- incoming **complements**: [Z52::middle_rank_totient_extremality_is_the_local_ordering_socket](BROWSER_Z52_1.md#node-78f30bbe0567d000). The two strict-minimum inequalities force positive curvature and the two strict-maximum inequalities force negative curvature, as proved by the adjacent source theorems.
- incoming **specialises**: [Z52::clean_power_two_lcm_curvature_is_divisible_by_twice_the_local_totient](BROWSER_Z52_1.md#node-e9b901640fa1dd9a). The divisibility theorem restricts the general curvature to clean offsets at power-two LCM heights and proves an arithmetic property of that specialization.

<a id="node-78f30bbe0567d000"></a>
## middle_rank_totient_extremality_is_the_local_ordering_socket

MiddleRankTotientExtremal H j means that φ(2H+j) is strictly below both outer totients or strictly above both.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: Defining the socket does not assert it at any actual LCM height; sign and nonzero consequences are separate theorems.

Open hypotheses: ["for fixed j, cofinal occurrence of MiddleRankTotientExtremal at H=periodLcm(2^a), represented by the unproved PowerTwoLcmMiddleRankExtremalSupply j"]

- Lean declaration: [MiddleRankTotientExtremal](../../Erdos249257/TotientFixedRankLcmAsymptotic.lean#L267)

- outgoing **complements**: [Z52::fixed_rank_second_difference_is_the_primitive_three_point_curvature](BROWSER_Z52_1.md#node-fc013e7ef6e97f52). The two strict-minimum inequalities force positive curvature and the two strict-maximum inequalities force negative curvature, as proved by the adjacent source theorems.
- incoming **complements**: [Z52::clean_power_two_lcm_curvature_is_divisible_by_twice_the_local_totient](BROWSER_Z52_1.md#node-e9b901640fa1dd9a). Divisibility constrains the size lattice of the curvature, while the open extremal-ordering socket would provide independent nonvanishing.

