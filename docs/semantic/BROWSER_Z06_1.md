# Z06_1: Tail-period killer and the lcm cone: waves 20-25 of the #249 reduction chain (plus the Farey-gap and unit-gap side lanes)

[All problems and zones](BROWSER.md)

<a id="node-b0920e47da1189ae"></a>
## anchor_totient_scaling

If q divides H then phi(qH) = q phi(H); consequently, on the whole lcm ray with 2 <= q < t, the forcing letter satisfies phi((q+1)H) - phi(qH) = phi(H) exactly.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [totient_mul_eq_left_mul_totient_of_dvd](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L605)
- Lean declaration: [deltaTotient_periodLcm_anchor](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L635)

- incoming **depends_on_open**: [Z06::barrier_finite_rank_shift_algebra](BROWSER_Z06_1.md#node-9f93e6afd7e89d02). The pulse matches the exact whole-ray anchors only because phi(qH) = q phi(H) for q | H.

<a id="node-9f93e6afd7e89d02"></a>
## barrier_finite_rank_shift_algebra

For every t >= 3 there is a nonzero integer carry orbit that satisfies the exact affine recurrence, absorbs every homogeneous lower factor ideal phi(j) for j | lcm(1..t), respects the natural letter bound |a_i| <= 2H + i + 1 and the strip bound |c_i| < 2H + i + 2 at every horizon, and matches every prescribed whole-ray anchor letter (lcm_factorIdeal_sparseAnchor_not_sufficient). The same orbit survives every finite integer shift polynomial: for every finite list of shift/coefficient terms the transformed pair stays a dyadic coboundary with the exact cleared-prefix identity, inherits every lower factor ideal, and obeys weight-scaled uniform bounds (lcm_factorIdeal_finiteRank_shiftAlgebra_not_sufficient). This defeats finite-rank LINEAR shift observations of any rank, not just one rank-2 or rank-3 instance; note that the shift-algebra theorem transports a strictly SHORTER property list than the rank-1 theorem (see scope_caveat).

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The barrier defeats ONLY the named hypothesis class LcmFactorIdealAnchorAdmissible: affine recurrence + homogeneous factor-ideal divisibility + the natural letter/strip bounds + the sparse whole-ray anchor values, and their images under finite integer shift polynomials (linear observations). It does NOT rule out: (i) any argument using the actual arithmetic of totient differences at NON-anchor positions (the countermodel is explicitly synthetic and does not claim its compensation letters are realisable totient differences); (ii) nonlinear combinations such as determinants of several linear observations; (iii) infinite-rank or non-shift-algebraic operators; (iv) the residual recursive quotient identity on the ray; (v) the fresh Moebius channels that survive the two-divisible-axes cancellation threshold. In particular this barrier says nothing about the endpoint/survivor/menu certificate families of this zone, which use actual totient values, not factor-ideal-only data. (vi) ASYMMETRY between the two theorems, added by adversarial review (2026-07-25): only lcm_factorIdeal_sparseAnchor_not_sufficient establishes the full LcmFactorIdealAnchorAdmissible package. The finite-rank theorem lcm_factorIdeal_finiteRank_shiftAlgebra_not_sufficient concludes strictly less about the TRANSFORMED words (d,b): it gives the coboundary property, the cleared-prefix identity, factor-ideal divisibility, and weight-scaled uniform bounds |d| <= W*phi(H), |b| <= 2W*phi(H) - but it does NOT assert the natural letter bound |b_i| <= 2H + i + 1, does NOT assert the natural strip bound |d_i| < 2H + i + 2, and carries NO anchor-matching clause for the transformed words. So a strategy that reads finite-rank shift observations and then requires those transformed observations to satisfy the natural growing strip/letter bounds or to match prescribed anchors is NOT closed by this theorem. The phrase 'closes the finite-rank shift-algebra route' must be read as: closed for strategies that need only the transported properties actually listed in the Lean conclusion. This is exactly the weaker-third-engine gap that a barrier of this shape can hide, and it is recorded here rather than left to the reader.

- Lean declaration: [lcm_factorIdeal_sparseAnchor_not_sufficient](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L866)
- Lean declaration: [lcm_factorIdeal_finiteRank_shiftAlgebra_not_sufficient](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L798)
- Lean declaration: [LcmFactorIdealAnchorAdmissible](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L848)

- outgoing **depends_on_open**: [Z06::sparse_pulse_countermodel_construction](BROWSER_Z06_2.md#node-10099dc166b2a256). The countermodel is the engine of the no-go.
- outgoing **depends_on_open**: [Z06::anchor_totient_scaling](BROWSER_Z06_1.md#node-b0920e47da1189ae). The pulse matches the exact whole-ray anchors only because phi(qH) = q phi(H) for q | H.
- incoming **barrier_for**: [Z06::mobius_channel_old_new_boundary](BROWSER_Z06_1.md#node-89bbb62d0d4b419d). Old Moebius channels die under two d-divisible shift axes, so any surviving argument must exploit the fresh channels the barrier does not model.

<a id="node-05d318200f8fe921"></a>
## carry_orbit_survivor_soundness

If the tail difference at N is an integer d, then the integer orbit c_0 = d, c_{i+1} = 2 c_i - (phi(N+i+1+h) - phi(N+i+1)) equals R_{N+i+h} - R_{N+i} for every i and is therefore trapped in the strip |c_i| < N+i+h+2 forever. Hence the decidable survivorKill certificate (every integer candidate in the initial box escapes the strip within K steps) proves the tail difference is not an integer.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [carryOrbit_eq_tail_diff](../../Erdos249257/CarrySurvivorExtinction.lean#L393)
- Lean declaration: [tail_diff_notMem_int_of_survivorKill](../../Erdos249257/CarrySurvivorExtinction.lean#L428)
- Lean declaration: [survivorKill](../../Erdos249257/CarrySurvivorExtinction.lean#L412)

- outgoing **reformulates**: [Z06::endpoint_certificate_soundness](BROWSER_Z06_1.md#node-552175c811881922). Same non-integrality conclusion via the bounded integer orbit instead of the residue band; measured strictly stronger at one cell only.
- incoming **reformulates**: [Z08::adjacent_carry_state_is_carry_orbit](BROWSER_Z08_1.md#node-fa7d5cb5f5e3b353). adjacentCarryState_eq_carryOrbit identifies the adjacent carry state across a run of robust failures with carryOrbit at shifted base, the exact object of carryOrbit_eq_tail_diff and survivorKill.
- incoming **alias_of**: [Z01::certified_kill_soundness](BROWSER_Z01_1.md#node-ce3a6b8b2b87a632). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18505 `totient_tail_diff_not_int_of_survivor_kill := TotientTailPeriodKiller.tail_diff_notMem_int_of_survivorKill`.

<a id="node-ae74fd4330038e95"></a>
## certificate_family_comparisons_at_cells

Single-cell machine-checked comparisons between certificate families: the survivor certificate fires at (1,57,K=8) where every endpoint depth L <= 8 fails; rank-1 fires at (1,8,L=8) where no rank-2 certificate exists at depth <= 8 (rank-2 first fires at 9); the menu [1,3] at t=2 refutes at depth 8 where no pairwise certificate exists below depth 9; the menu [2,3,4] at t=2 refutes at depth 5 while every 2-vertex submenu and every relevant pairwise certificate is silent there.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [survivor_strict_at_equal_budget](../../Erdos249257/CarrySurvivorExtinction.lean#L568)
- Lean declaration: [rank2_kill_sound_but_not_shallower_at_cell](../../Erdos249257/LcmConeFlatness.lean#L626)
- Lean declaration: [cone_nonflat_strict_win_at_cell](../../Erdos249257/LcmConeNonflat.lean#L517)
- Lean declaration: [cone_nonflat_joint_win_at_cell](../../Erdos249257/LcmConeNonflat.lean#L530)

- outgoing **finite_instance_of**: [Z06::finite_kill_deposits](BROWSER_Z06_1.md#node-91eeb9cf682bd8dd). Single-cell comparisons of certificate families; census claims around them are probe-only.
- incoming **equivalent_to**: [Z01::engine_strength_separations](BROWSER_Z01_1.md#node-8f3c278e1c645ebc). Same four separation fixtures (survivor_strict_at_equal_budget, rank2_kill_sound_but_not_shallower_at_cell, cone_nonflat_strict_win_at_cell, cone_nonflat_joint_win_at_cell) under the two zones' naming.
- incoming **alias_of**: [Z01::engine_strength_separations](BROWSER_Z01_1.md#node-8f3c278e1c645ebc). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18548/18762/18845/18862 re-export `survivor_strict_at_equal_budget`, `rank2_kill_sound_but_not_shallower_at_cell`, `cone_nonflat_strict_win_at_cell`, `cone_nonflat_joint_win_at_cell`; the same four single-cell separations.

<a id="node-b7430ca307ffd27e"></a>
## certificate_supply_is_equivalent_to_249

Irrationality of the #249 series is EQUIVALENT to: every positive shifted tail difference being non-integral; equivalently every (h,N) admitting some certificate depth; equivalently the cofinal certificate supply; equivalently the one-parameter lcm-diagonal certificate supply. Moreover a single integral tail difference at a positive shift already makes the constant rational, since integrality of R_{N+h} - R_N is exactly integrality of 2^N (2^h - 1) S.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Every equivalence here has an open statement on BOTH sides. The zone's apparent progress (fewer parameters, one decidable predicate) is a change of coordinates on the same open problem.

- Lean declaration: [irrational_totient_series_iff_all_tail_diffs_nonintegral](../../Erdos249257/LcmConeFlatness.lean#L386)
- Lean declaration: [irrational_totient_series_iff_pointwise_certificates](../../Erdos249257/LcmConeFlatness.lean#L399)
- Lean declaration: [irrational_totient_series_iff_certificate_supply](../../Erdos249257/LcmConeFlatness.lean#L412)
- Lean declaration: [irrational_totient_series_iff_lcm_diagonal_certificate_supply](../../Erdos249257/LcmConeFlatness.lean#L426)
- Lean declaration: [tail_diff_mem_int_iff_scaled_series_mem_int](../../Erdos249257/LcmConeFlatness.lean#L327)
- Lean declaration: [not_irrational_of_tail_diff_mem_int](../../Erdos249257/LcmConeFlatness.lean#L357)

- outgoing **equivalent_to**: [Z06::reduction_pointwise_certificate_supply](BROWSER_Z06_1.md#node-eb9013360d8a36f2). The iff theorems show the wave-21 supply hypothesis is exactly #249, so the reduction adds no unconditional content.
- outgoing **equivalent_to**: [Z06::reduction_lcm_diagonal_supply](BROWSER_Z06_1.md#node-9bc987ebd91ed7a5). irrational_totient_series_iff_lcm_diagonal_certificate_supply proves the diagonal hypothesis is equivalent to #249.
- incoming **reformulates**: [Z08::tail_orbit_equals_scaled_series_orbit](BROWSER_Z08_2.md#node-d47ec06f23f8ca12). tail_diff_eq_scaled_totient_series_sub_prefix (PivotAntiReconstruction.lean:54) and tail_diff_mem_int_iff_scaled_series_mem_int (LcmConeFlatness.lean:327) are the same identity R_{N+h}-R_N = 2^N(2^h-1)S - integer prefix.
- incoming **equivalent_to**: [Z08::window_separated_pairs_equivalent_to_249](BROWSER_Z08_2.md#node-c5d275f2b251a636). dtwWindowSeparatedPairs_iff_irrational_totient_series (PivotAntiReconstruction.lean:1744) and irrational_totient_series_iff_certificate_supply (LcmConeFlatness.lean:412) are two proved equivalences with the same right-hand side Irrational (sum phi(n)/2^n).
- incoming **transport_of**: [Z17::n251_integrality_criterion](BROWSER_Z17_1.md#node-0102a98d308d7360). tailShift_integral_iff_scaledTail is the generic-digit form of tail_diff_mem_int_iff_scaled_series_mem_int: a shifted dyadic tail difference is an integer exactly when (2^h - 1) times the tail state is, instantiated at prime gaps rather than at phi.
- incoming **depends_on_open**: [Z08::window_separated_pairs_implies_249](BROWSER_Z08_2.md#node-71462c4ebdb6fa9c). the separated-pairs socket is proved equivalent to #249 in its own zone, and this node proves the certificate supply equally equivalent to #249; the antecedent is therefore the open problem itself, not a weaker intermediate, and no producer strictly below #249 can exist.
- incoming **alias_of**: [Z08::window_separated_pairs_equivalent_to_249](BROWSER_Z08_2.md#node-c5d275f2b251a636). `dtwWindowSeparatedPairs_iff_irrational_totient_series` (Z08) and `irrational_totient_series_iff_certificate_supply` (Z06) each prove their socket logically equivalent to Irrational (sum phi n / 2^n), so the two sockets are provably equivalent to each other; both are the open problem in different coordinates, not independent obligations.
- outgoing **specialises**: [Z17::n251_integrality_criterion](BROWSER_Z17_1.md#node-0102a98d308d7360). Z17's `ErdosProblems.Erdos251.tailShift_integral_iff_scaledTail` states for any dyadic tail obeying T(N+1) = 2T(N) - g(N+1) with integer digits that a shifted tail difference is integral exactly when (2^h - 1) times the tail state is; Z06's `tail_diff_mem_int_iff_scaled_series_mem_int` is that criterion for the totient tail, where the scaled state is 2^N (2^h - 1) S.

<a id="node-6447dcc2bfa839bd"></a>
## cone_window_small_prime_congruence

For a prime p <= t, p divides the cone window argument q*lcm(1..t) + s if and only if p divides the offset s.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [small_prime_dvd_cone_window_iff_dvd_offset](../../Erdos249257/LcmConeNonflat.lean#L70)


<a id="node-b5d0116c5f6ae00e"></a>
## dyadic_coboundary_shift_calculus

For the dyadic coboundary a = 2c - Ec, the depth-L cleared prefix equals 2^L c_n - c_{n+L} at every start and horizon; and the coboundary class is stable under every finite iterated forward difference and every finite integer shift polynomial, with divisibility inherited and uniform bounds growing only by 2^rank (resp. by the l1 weight of the coefficients).

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [dyadicClearedPrefix_dyadicCoboundary](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L115)
- Lean declaration: [iteratedForwardDifference_dyadicCoboundary](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L188)
- Lean declaration: [shiftLinearCombination_dyadicCoboundary](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L257)
- Lean declaration: [shiftLinearCombination_dyadicClearedPrefix](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L276)
- Lean declaration: [iteratedForwardDifference_dyadicClearedPrefix](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L201)

- incoming **reformulates**: [Z11::affine_carry_fixed_depth_reset](BROWSER_Z11_1.md#node-1ce1b5ef053ed69d). affineBinaryOrbit_sub / affineBinaryOrbit_mod_twoPow_eq and dyadicClearedPrefix_dyadicCoboundary are the same statement about the dyadic coboundary a = 2c - Ec: the depth-L cleared prefix is 2^L c_n - c_{n+L}, so depth-L residues ignore the initial carry.
- incoming **reformulates**: [Z17::n251_free_carry_barrier](BROWSER_Z17_1.md#node-f3051b3e0ee128e4). carryPartialSum_eq (partial sums of 2K(n) - K(n+1) telescope to K(0) - K(n)/2^n) is the #251 statement of the same dyadic coboundary / cleared-prefix identity as dyadicClearedPrefix_dyadicCoboundary.
- incoming **specialises**: [Z17::n251_free_carry_barrier](BROWSER_Z17_1.md#node-f3051b3e0ee128e4). `ErdosProblems.Erdos251.carryPartialSum_eq` (partial sums of the emitted word 2K(n) - K(n+1) telescope to K(0) - K(n)/2^n) is the base-point case of Z06's `dyadicClearedPrefix_dyadicCoboundary`, which computes the depth-L cleared prefix of a = 2c - Ec as 2^L c_n - c_{n+L} at every start and horizon.

<a id="node-2151751ccfb38f8d"></a>
## endpoint_certificate_completeness

Conversely, if R_{N+h} - R_N is a non-integer then some finite depth L certifies it. So an endpoint certificate exists at (h,N) exactly when the tail difference is non-integral; the same equivalence holds cell by cell on the lcm diagonal.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: RESTATEMENT (per-cell). Both sides of the equivalence are, for a general (h,N), unresolved: 'some depth certifies (h,N)' and 'R_{N+h} - R_N is a non-integer' are two names for the same open per-cell question, and by tail_diff_mem_int_iff_scaled_series_mem_int the right-hand side is exactly non-integrality of 2^N (2^h - 1) S. The theorem decides no cell; it only shows the finite certificate is not a lossy surrogate. Flagged as a restatement because it is a change of coordinates between two open statements, at the level of a single cell rather than of #249 as a whole; the zone-level restatement is certificate_supply_is_equivalent_to_249, and this node is what makes that one true. Adversarial-review note (2026-07-25): previously carried is_restatement_of_open_problem=false while its own caveat already conceded both sides were open.

- Lean declaration: [exists_certifiedKill_of_tail_diff_notMem_int](../../Erdos249257/LcmConeFlatness.lean#L156)
- Lean declaration: [exists_certifiedKill_iff_tail_diff_notMem_int](../../Erdos249257/LcmConeFlatness.lean#L316)
- Lean declaration: [periodLcm_diagonal_kill_iff_tail_diff_notMem_int](../../Erdos249257/LcmConeFlatness.lean#L439)

- outgoing **equivalent_to**: [Z06::endpoint_certificate_soundness](BROWSER_Z06_1.md#node-552175c811881922). Completeness converts soundness into an iff: a depth certifies (h,N) exactly when the tail difference is non-integral.
- incoming **equivalent_to**: [Z01::window_kill_completeness](BROWSER_Z01_2.md#node-82033994a112e164). totient_tail_window_kill_exists_iff_tail_diff_not_int (CertificateKernel.lean:18697) and exists_certifiedKill_iff_tail_diff_notMem_int (LcmConeFlatness.lean:316) are the same iff: a kill of some depth exists at (h,N) exactly when R_{N+h}-R_N is not an integer.
- incoming **equivalent_to**: [Z05::exact_full_target_pincer](BROWSER_Z05_1.md#node-faace0186be92bf5). foreignDiagonalDefect t is defined as diagonalTailDifference t - explicitLcmShadow t (DiagonalPincerDecomposition.lean), so diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget is integrality of R_{2H_t}-R_{H_t}, exactly the cell decided by periodLcm_diagonal_kill_iff_tail_diff_notMem_int.
- incoming **alias_of**: [Z01::window_kill_completeness](BROWSER_Z01_2.md#node-82033994a112e164). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18697 `totient_tail_window_kill_exists_iff_tail_diff_not_int := TotientTailPeriodKiller.exists_certifiedKill_iff_tail_diff_notMem_int`; the same iff.

<a id="node-3ca91ce92ac997b8"></a>
## endpoint_certificate_depth_floor

Any firing endpoint certificate must satisfy 2(N + h + L + 2) < 2^L. Hence no certificate supply can be realised at bounded depth: L must grow at least logarithmically in N + h.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Rules out only fixed-depth or sub-logarithmic-depth certificate families. It does NOT rule out depths growing like log2(N) or any faster growth, does not bound the minimal firing depth from above, and says nothing about the survivor, rank-2 or menu certificate families beyond their own analogous floors.

- Lean declaration: [certifiedKill_depth_floor](../../Erdos249257/TotientTailPeriodKiller.lean#L79)

- outgoing **barrier_for**: [Z06::reduction_pointwise_certificate_supply](BROWSER_Z06_1.md#node-eb9013360d8a36f2). No certificate supply can be realised at bounded depth; depth must grow at least logarithmically in N+h.
- incoming **repair_of**: [Z08::exponential_depth_pays_budgets](BROWSER_Z08_1.md#node-76014e1239285452). certifiedKill_depth_floor forbids only bounded or sub-logarithmic depth, requiring 2(N+h+L+2) < 2^L. exists_natural_window_depth_with_error produces, for any base and any positive error budget and beyond any prescribed threshold, a depth that satisfies the (strictly stronger) certificate room inequality and simultaneously drives the phase-truncation error below the budget, so the floor is met rather than violated.

<a id="node-101ab5d9b7510733"></a>
## endpoint_certificate_depth_monotonicity

Once an endpoint certificate fires at depth L it fires at every deeper depth L + k. The proof uses the exact depth recurrence A(L+1) = 2A(L) + (phi(N+L+1+h) - phi(N+L+1)) together with the bound |phi(n+h) - phi(n)| <= n + h.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [certifiedKill_succ](../../Erdos249257/CarrySurvivorExtinction.lean#L199)
- Lean declaration: [certifiedKill_add](../../Erdos249257/CarrySurvivorExtinction.lean#L242)
- Lean declaration: [windowDiscrepancy_succ](../../Erdos249257/CarrySurvivorExtinction.lean#L160)


<a id="node-552175c811881922"></a>
## endpoint_certificate_soundness

If the residue of the depth-L window discrepancy A_{h,N,L} modulo 2^L avoids the radius-(N+h+L+2) neighbourhood of 0, then R_{N+h} - R_N is not an integer.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tail_diff_notMem_int_of_certifiedKill](../../Erdos249257/TotientTailPeriodKiller.lean#L262)
- Lean declaration: [windowDiscrepancy_div_eq](../../Erdos249257/TotientTailPeriodKiller.lean#L241)
- Lean declaration: [certifiedKill](../../Erdos249257/TotientTailPeriodKiller.lean#L72)

- outgoing **depends_on_open**: [Z06::tail_strip_and_carry_recurrence](BROWSER_Z06_2.md#node-1bb6df87e4fcba59). Soundness uses the one-sided deep-tail bound derived from phi(n) <= n.
- incoming **equivalent_to**: [Z06::endpoint_certificate_completeness](BROWSER_Z06_1.md#node-2151751ccfb38f8d). Completeness converts soundness into an iff: a depth certifies (h,N) exactly when the tail difference is non-integral.
- incoming **reformulates**: [Z06::carry_orbit_survivor_soundness](BROWSER_Z06_1.md#node-05d318200f8fe921). Same non-integrality conclusion via the bounded integer orbit instead of the residue band; measured strictly stronger at one cell only.
- incoming **equivalent_to**: [Z01::certified_kill_soundness](BROWSER_Z01_1.md#node-ce3a6b8b2b87a632). Both nodes carry the same declaration tail_diff_notMem_int_of_certifiedKill (TotientTailPeriodKiller.lean); Z01 bundles the survivor and rank-two dresses of the identical truncation-and-residue-band soundness argument.
- incoming **reformulates**: [Z08::window_discrepancy_is_exact_tail_prefix](BROWSER_Z08_2.md#node-39d7ceb51308869b). tail_diff_eq_windowDiscrepancy_div_add_shifted (AdjacentPhaseSeparation.lean:54) is the same depth-L split of R_{N+h}-R_N used by windowDiscrepancy_div_eq inside tail_diff_notMem_int_of_certifiedKill.
- incoming **reformulates**: [Z09::generic_window_residue_gap_soundness](BROWSER_Z09_1.md#node-6c029622c10f1cc6). notMem_int_of_window_remainder_bound (PrimeJumpWindow.lean) is the stencil-free abstraction of the truncate-then-separate argument of tail_diff_notMem_int_of_certifiedKill; the endpoint certificate is its (h,N) instance.
- incoming **transport_of**: [Z09::three_transport_window_certificate](BROWSER_Z09_2.md#node-1c4f511c806cea73). two_pow_mul_threeTransport_eq_window_add_shifted is the balanced four-ray analogue of windowDiscrepancy_div_eq, closed by the identical residue-band separation; the same stencil substitution produces the curvature, prime-jump and joint(3,5) certificates.
- incoming **alias_of**: [Z01::certified_kill_soundness](BROWSER_Z01_1.md#node-ce3a6b8b2b87a632). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18447 `totient_tail_diff_not_int_of_certified_kill := TotientTailPeriodKiller.tail_diff_notMem_int_of_certifiedKill`.
- outgoing **specialises**: [Z09::generic_window_residue_gap_soundness](BROWSER_Z09_1.md#node-6c029622c10f1cc6). Z09's `notMem_int_of_window_remainder_bound` is the generic criterion (x = A/2^L + e with |e 2^L| <= R and A mod 2^L strictly inside (R, 2^L - R) implies x not an integer); Z06's `tail_diff_notMem_int_of_certifiedKill` is that criterion at x = R_{N+h} - R_N, A = the depth-L window discrepancy and R = N+h+L+2, the remainder bound supplied by `tail_diff_eq_increment_prefix_add_shifted` and `abs_tail_diff_lt`.

<a id="node-b783caa06199f509"></a>
## endpoint_survivor_fibre_equivalence

Under the dyadic-room condition 2(N+h+L+2) < 2^L, the endpoint certificate at (h,N,L) holds if and only if no integer z with |z| <= N+h+L+2 is congruent to the window discrepancy modulo 2^L.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [certifiedKill_iff_endpointSurvivor_empty](../../Erdos249257/CarrySurvivorExtinction.lean#L330)
- Lean declaration: [no_endpointSurvivor_of_certifiedKill](../../Erdos249257/CarrySurvivorExtinction.lean#L261)
- Lean declaration: [certifiedKill_of_no_endpointSurvivor](../../Erdos249257/CarrySurvivorExtinction.lean#L289)


<a id="node-26d6c281be7baa8e"></a>
## farey_mediant_gap_lemma

If a/b < r/s < c/d with b, d > 0 and the neighbours are unimodular (bc - ad = 1), then b + d <= s.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [farey_gap](../../Erdos249257/GapFareyBound.lean#L51)

- incoming **finite_instance_of**: [Z06::gap_denominator_rungs](BROWSER_Z06_1.md#node-36f3f6e03a170c3d). Each rung is the mediant lemma applied to one externally generated unimodular neighbour pair.

<a id="node-91eeb9cf682bd8dd"></a>
## finite_kill_deposits

Kernel-decided certificate firings and their non-integrality corollaries: endpoint kills for every h <= 8 at (N,L) = (12,16) and every h <= 16 at (14,9); a survivor kill at (1,12,7); lcm-diagonal kills at all scales t <= 8 with tabulated depths; off-diagonal cone cells at (t,q,m) = (2,3,1), (3,2,2), (3,1,3); a rank-2 kill at (1,8,9); menu refutations at (t,Q,L) = (1,[1,2,3],5), (2,[1,2,3,4],5), (3,[1,2,3],6).

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [certifiedKill_all_upto_sixteen](../../Erdos249257/CarrySurvivorExtinction.lean#L574)
- Lean declaration: [certifiedKill_periodLcm_diagonal_upto_six](../../Erdos249257/LcmDiagonalReduction.lean#L257)
- Lean declaration: [certifiedKill_lcm_cone_cells](../../Erdos249257/LcmConeFlatness.lean#L611)
- Lean declaration: [coneNonflatCert_cells](../../Erdos249257/LcmConeNonflat.lean#L506)

- incoming **finite_instance_of**: [Z06::unconditional_denominator_exclusion](BROWSER_Z06_2.md#node-a7dd11b48fa35258). The two exclusions are exactly the kernel-decided certificate blocks fed through the tail-period law.
- incoming **finite_instance_of**: [Z06::certificate_family_comparisons_at_cells](BROWSER_Z06_1.md#node-ae74fd4330038e95). Single-cell comparisons of certificate families; census claims around them are probe-only.
- incoming **equivalent_to**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). Same kernel-decided cells: endpoint kills for h<=8 at (12,16) and h<=16 at (14,9), lcm-diagonal kills through t=8, three off-diagonal cone cells and three certified menus.
- outgoing **finite_instance_of**: [Z01::erdos249_period_kill_supply_restatement](BROWSER_Z01_1.md#node-091f2dbf4dfd2e47). the deposited endpoint kills (h<=8 at (12,16), h<=16 at (14,9)), the survivor kill (1,12,7) and the lcm-diagonal kills at t<=8 are instances of three of the four supply forms this restatement quantifies cofinally.
- outgoing **finite_instance_of**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). the off-diagonal cone cells (t,q,m) = (2,3,1), (3,2,2), (3,1,3) and the rank-2 kill at (1,8,9) are firing instances of the certified-annihilator and rank-two clauses of this cone supply.
- outgoing **finite_instance_of**: [Z01::erdos249_cone_nonflat_supply_restatement](BROWSER_Z01_1.md#node-4653d6568a5b39ff). the menu refutations at (t,Q,L) = (1,[1,2,3],5), (2,[1,2,3,4],5), (3,[1,2,3],6) are firing vertex menus, the object whose cofinal existence is this restatement's sole hypothesis.
- incoming **depends_on_open**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). the only realised off-diagonal cone annihilators anywhere are the three cells (2,3,1), (3,2,2), (3,1,3) and the rank-2 kill (1,8,9) deposited here, all at t <= 3; nothing produces cells at arbitrarily large scale.
- incoming **depends_on_open**: [Z01::erdos249_cone_nonflat_supply_restatement](BROWSER_Z01_1.md#node-4653d6568a5b39ff). the only firing vertex menus in the corpus are the three deposited here at t = 1,2,3; the hypothesis needs one at arbitrarily large t and no node produces menus beyond these.
- incoming **alias_of**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18472/18555/18633/18749/18833 re-export `certifiedKill_all_small`, `certifiedKill_all_upto_sixteen`, `certifiedKill_periodLcm_diagonal_upto_six`, the lcm-cone cells and the coneNonflatCert cells; the Z01 fixture list is the re-exported subset of Z06's deposit list.

<a id="node-36f3f6e03a170c3d"></a>
## gap_denominator_rungs

For the (N=1, K) gap-certificate windows: every denominator q with 0 < q <= 248672326362367909 satisfies the K=120 gap certificate, and every q with 0 < q <= 79639646646701375323355774875831053 satisfies the K=240 one; in both cases the bound is sharp, the mediant denominator b+d being the exact first displayed failure.

Class: generated_certificate_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

- Lean declaration: [gap_check_window_1_120_le_248672326362367909](../../Erdos249257/GapFareyBound.lean#L88)
- Lean declaration: [gap_check_window_1_240_le_79639646646701375323355774875831053](../../Erdos249257/GapFareyBound.lean#L176)
- Lean declaration: [gap_check_window_1_120_first_failure](../../Erdos249257/GapFareyBound.lean#L144)
- Lean declaration: [gap_check_window_1_240_first_failure](../../Erdos249257/GapFareyBound.lean#L225)

- outgoing **finite_instance_of**: [Z06::farey_mediant_gap_lemma](BROWSER_Z06_1.md#node-26d6c281be7baa8e). Each rung is the mediant lemma applied to one externally generated unimodular neighbour pair.
- outgoing **finite_instance_of**: [Z01::erdos249_gap_supply_restatement](BROWSER_Z01_1.md#node-31a4afdc8be1ccc1). the K=120 and K=240 windows certify the gap inequality for every denominator q up to 2.48e17 and 7.96e34 respectively; the supply asks for a window at EVERY precision q, so the rungs are its bounded-q instance, and the recorded sharpness (the mediant denominator b+d is the first failure) shows those two windows cannot be pushed further.
- incoming **depends_on_open**: [Z01::erdos249_gap_supply_restatement](BROWSER_Z01_1.md#node-31a4afdc8be1ccc1). the rungs discharge the gap-certificate supply for all q up to 2.48e17 (K=120) and 7.96e34 (K=240) and are sharp there; beyond those denominators nothing in the corpus produces a window.

<a id="node-2b6c6005924da837"></a>
## lcm_cone_flatness_law

If the #249 series is rational then beyond some scale t1 the entire lcm cone is fractionally flat: for every t >= t1, every base multiplier q >= 1 and every step multiplier m, the difference R_{(q+m)H_t} - R_{q H_t} is an integer.

Class: reduction_or_transport. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [rational_totient_series_forces_lcm_cone_flatness](../../Erdos249257/LcmConeFlatness.lean#L90)

- incoming **depends_on_open**: [Z06::reduction_rank2_qray_supply](BROWSER_Z06_2.md#node-725e8c140eeebb35). Rank-2 supply is sound only because flatness forces both first differences integral on q-rays.
- incoming **depends_on_open**: [Z06::reduction_cone_nonflat_menu_supply](BROWSER_Z06_1.md#node-83d97029da15536b). The menu refuter contradicts joint flatness of the cone.
- incoming **equivalent_to**: [Z01::lcm_cone_flatness_law](BROWSER_Z01_1.md#node-ae87c97d6ef2cef3). Same theorem rational_totient_series_forces_lcm_cone_flatness, stated at LcmConeFlatness.lean:90 and re-exported at CertificateKernel.lean:18674; the two zones own one statement under one name.
- incoming **alias_of**: [Z01::lcm_cone_flatness_law](BROWSER_Z01_1.md#node-ae87c97d6ef2cef3). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18674 `rational_totient_series_forces_lcm_cone_flatness := TotientTailPeriodKiller.rational_totient_series_forces_lcm_cone_flatness` (owned at LcmConeFlatness.lean:90). The two nodes share the node id and the theorem.

<a id="node-190e1b1c4523c82a"></a>
## lcm_ray_divisibility_skeleton

periodLcm t = lcm(1..t) is positive, is divisible by every 1 <= h <= t, satisfies t <= periodLcm t, is monotone under divisibility in t, and any strict jump periodLcm(t+1) - periodLcm t is at least periodLcm t.

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [dvd_periodLcm](../../Erdos249257/CarrySurvivorExtinction.lean#L525)
- Lean declaration: [periodLcm_dvd_periodLcm](../../Erdos249257/LcmConeFlatness.lean#L67)
- Lean declaration: [periodLcm_strict_jump_sub_ge](../../Erdos249257/LcmDiagonalReduction.lean#L67)
- Lean declaration: [le_periodLcm](../../Erdos249257/LcmDiagonalReduction.lean#L81)

- incoming **depends_on_open**: [Z06::reduction_lcm_diagonal_supply](BROWSER_Z06_1.md#node-9bc987ebd91ed7a5). The diagonal argument needs h0 | H_t and t <= H_t simultaneously.
- incoming **specialises**: [Z06::lcm_ray_window_structure](BROWSER_Z06_1.md#node-4451a0a51d2089ac). Pins down the sparse exceptional set of non-divisors in (t, 2t).
- incoming **reformulates**: [Z05::periodLcm_strict_jump_classification](BROWSER_Z05_1.md#node-4f1dfa64497467e2). periodLcm_strict_jump_iff_succ_not_dvd and periodLcm_succ_eq_prime_mul_of_strict_jump sharpen the ray skeleton facts periodLcm_dvd_periodLcm and periodLcm_strict_jump_sub_ge to an exact prime-power jump classification of the same object.
- incoming **alias_of**: [Z01::lcm_cone_flatness_law](BROWSER_Z01_1.md#node-ae87c97d6ef2cef3). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18667 `period_lcm_dvd_period_lcm_of_le := TotientTailPeriodKiller.periodLcm_dvd_periodLcm`; the nesting clause the Z01 node attaches to the flatness law is a component of Z06's divisibility skeleton.

<a id="node-422ae61aee562243"></a>
## lcm_ray_totient_factorisation

If j divides H = lcm(1..t) and every prime of j still divides H/j, then phi(q H + j) = phi(j) * phi(q (H/j) + 1): the window totient on the ray splits into a known local factor and a cofactor whose argument is coprime to j.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [totient_periodLcm_ray_split](../../Erdos249257/LcmDiagonalReduction.lean#L208)
- Lean declaration: [totient_ray_split](../../Erdos249257/LcmDiagonalReduction.lean#L197)

- incoming **alias_of**: [Z01::lcm_ray_window_structure](BROWSER_Z01_2.md#node-74e2b93b64962549). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18622 `totient_period_lcm_ray_factorisation := TotientTailPeriodKiller.totient_periodLcm_ray_split`; the second conjunct of the Z01 node is exactly Z06's ray-factorisation node.

<a id="node-4451a0a51d2089ac"></a>
## lcm_ray_window_structure

For 0 < j < 2t, if j does not divide lcm(1..t) then j is a bare prime power p^k exceeding t. Below 2t every other window index divides the period.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [eq_prime_pow_of_not_dvd_periodLcm](../../Erdos249257/LcmDiagonalReduction.lean#L137)

- outgoing **specialises**: [Z06::lcm_ray_divisibility_skeleton](BROWSER_Z06_1.md#node-190e1b1c4523c82a). Pins down the sparse exceptional set of non-divisors in (t, 2t).
- incoming **equivalent_to**: [Z01::lcm_ray_window_structure](BROWSER_Z01_2.md#node-74e2b93b64962549). period_lcm_window_index_prime_pow_of_not_dvd and eq_prime_pow_of_not_dvd_periodLcm are the same classification: below 2t every window index divides lcm(1..t) except bare prime powers exceeding t.
- incoming **alias_of**: [Z01::lcm_ray_window_structure](BROWSER_Z01_2.md#node-74e2b93b64962549). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18613 `period_lcm_window_index_prime_pow_of_not_dvd := TotientTailPeriodKiller.eq_prime_pow_of_not_dvd_periodLcm` (owned at LcmDiagonalReduction.lean:137); same statement, shared node id.

<a id="node-543ed242df18c023"></a>
## menu_refuter_exactness

The menu certificate fires if and only if the depth-L menu arcs have no common point: a firing row denies every common point by an argmin argument, and a silent row makes its own left endpoint a common point.

Class: equivalence_or_classification. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [coneNonflatCert_iff_no_common_point](../../Erdos249257/LcmConeNonflat.lean#L339)
- Lean declaration: [not_coneCommonPoint_of_coneNonflatCert](../../Erdos249257/LcmConeNonflat.lean#L296)
- Lean declaration: [coneNonflatCert_of_not_coneCommonPoint](../../Erdos249257/LcmConeNonflat.lean#L328)

- outgoing **reformulates**: [Z06::menu_refuter_soundness](BROWSER_Z06_1.md#node-a8ce1315616306e2). Recasts firing as the combinatorial emptiness of the arc intersection, with no analytic tails.
- incoming **depends_on_open**: [Z06::menu_refuter_monotonicity_and_seed_lift](BROWSER_Z06_1.md#node-eead6993cd5ea533). Both monotonicity proofs route through the no-common-point characterisation.
- incoming **equivalent_to**: [Z01::menu_refuter_exactness_and_monotonicity](BROWSER_Z01_2.md#node-95967a6c8d05ed40). totient_tail_cone_nonflat_cert_iff_no_common_point and coneNonflatCert_iff_no_common_point are the same argmin exactness statement for the cone non-flatness menu certificate.
- incoming **alias_of**: [Z01::menu_refuter_exactness_and_monotonicity](BROWSER_Z01_2.md#node-95967a6c8d05ed40). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18900 re-exports `coneNonflatCert_iff_no_common_point`; the exactness half of the Z01 node is Z06's node.

<a id="node-eead6993cd5ea533"></a>
## menu_refuter_monotonicity_and_seed_lift

The menu certificate is monotone in depth (given floors at the base) and monotone in the menu (a firing sub-menu keeps firing for every supermenu at the same depth, no floor needed); combining these, a small seed menu firing at its own floor lifts to every supermenu at every deeper depth.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [coneNonflatCert_mono_of_le](../../Erdos249257/LcmConeNonflat.lean#L446)
- Lean declaration: [coneNonflatCert_supermenu](../../Erdos249257/LcmConeNonflat.lean#L479)
- Lean declaration: [coneNonflatCert_seed_lift](../../Erdos249257/LcmConeNonflat.lean#L492)
- Lean declaration: [coneCommonPoint_of_succ](../../Erdos249257/LcmConeNonflat.lean#L348)

- outgoing **depends_on_open**: [Z06::menu_refuter_exactness](BROWSER_Z06_1.md#node-543ed242df18c023). Both monotonicity proofs route through the no-common-point characterisation.
- incoming **alias_of**: [Z01::menu_refuter_exactness_and_monotonicity](BROWSER_Z01_2.md#node-95967a6c8d05ed40). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18908/18918/18930/18941 re-export `coneCommonPoint_of_succ`, `coneNonflatCert_mono_of_le`, `..._supermenu`, `..._seed_lift`; the monotonicity half of the Z01 node is Z06's node.

<a id="node-a8ce1315616306e2"></a>
## menu_refuter_soundness

For a finite menu Q of positive cone vertices at scale H and depth L, if every left endpoint P_L(q_i H) escapes some arc [P_L(q_j H), P_L(q_j H) + (q_j H + L + 2)] modulo 2^L, and each vertex satisfies the one-sided floor q H + L + 2 < 2^L, then some pair of menu vertices has a non-integral tail difference.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [exists_nonintegral_pair_of_coneNonflatCert](../../Erdos249257/LcmConeNonflat.lean#L126)
- Lean declaration: [coneNonflatCert](../../Erdos249257/LcmConeNonflat.lean#L108)
- Lean declaration: [windowNumerator](../../Erdos249257/LcmConeNonflat.lean#L81)

- incoming **reformulates**: [Z06::menu_refuter_exactness](BROWSER_Z06_1.md#node-543ed242df18c023). Recasts firing as the combinatorial emptiness of the arc intersection, with no analytic tails.
- incoming **alias_of**: [Z01::cone_nonflat_menu_refuter](BROWSER_Z01_1.md#node-18a57855d478e08e). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18801 `totient_tail_nonintegral_pair_of_cone_nonflat_cert := TotientTailPeriodKiller.exists_nonintegral_pair_of_coneNonflatCert`.

<a id="node-89bbb62d0d4b419d"></a>
## mobius_channel_old_new_boundary

The totient decomposes into Moebius divisor channels phi(n) = sum_{d|n} mu(d)(n/d), and any single channel is annihilated by two forward differences whose shift axes are both divisible by d, even with arbitrary further shifts before, between and after. Hence only channels not covered by such a divisible pair can contribute to a finite-rank shift-cube sum.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [rankTwo_mobiusTotientChannel_eq_zero_of_dvd](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L365)
- Lean declaration: [iteratedForwardDifference_mobiusTotientChannel_eq_zero_of_two_dvd](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L385)
- Lean declaration: [totient_eq_sum_mobiusTotientChannel](../../Erdos249257/LcmFactorIdealPulseObstruction.lean#L328)

- outgoing **barrier_for**: [Z06::barrier_finite_rank_shift_algebra](BROWSER_Z06_1.md#node-9f93e6afd7e89d02). Old Moebius channels die under two d-divisible shift axes, so any surviving argument must exploit the fresh channels the barrier does not model.

<a id="node-95058e2cbf8f7f44"></a>
## period_ray_telescoping

The tail difference at period m*h telescopes into m translated period-h differences; consequently integrality of every h-difference from N0 on forces integrality of every (m*h)-difference from N0 on.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [tail_diff_mul](../../Erdos249257/CarrySurvivorExtinction.lean#L458)
- Lean declaration: [tail_diff_mul_mem_int](../../Erdos249257/CarrySurvivorExtinction.lean#L471)

- incoming **transport_of**: [Z05::affine_scale_transport_of_diagonal](BROWSER_Z05_1.md#node-7cfbca3d206afacd). scaleDiagonalTailDifference_mul / diagonalCoefficient_mul express the tail difference along the ray H -> kH with an explicit affine coefficient; tail_diff_mul is the same ray telescoping in unscaled coordinates.
- incoming **alias_of**: [Z01::totient_tail_shift_and_period_law](BROWSER_Z01_2.md#node-f148b27a710470c2). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18513 `totient_tail_diff_multiple_telescope := TotientTailPeriodKiller.tail_diff_mul`; the same telescoping of the period-mh difference.

<a id="node-a1d74e04b71bd15d"></a>
## rank2_second_difference_soundness

A certified rank-2 residue (the second-difference window discrepancy avoiding a doubled radius-2(N+2h+L+2) band modulo 2^L) proves that (R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N) is not an integer.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [second_diff_notMem_int_of_certifiedRank2Kill](../../Erdos249257/LcmConeFlatness.lean#L493)
- Lean declaration: [certifiedRank2Kill](../../Erdos249257/LcmConeFlatness.lean#L484)

- incoming **alias_of**: [Z01::certified_kill_soundness](BROWSER_Z01_1.md#node-ce3a6b8b2b87a632). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18729 `totient_tail_second_diff_not_int_of_rank_two_kill := TotientTailPeriodKiller.second_diff_notMem_int_of_certifiedRank2Kill`.

<a id="node-83d97029da15536b"></a>
## reduction_cone_nonflat_menu_supply

If for arbitrarily large t some finite positive vertex menu on the lcm(1..t) cone fires the non-flatness certificate with its one-sided floors, then the #249 series is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : forall t0, exists t, t0 <= t and exists L Q, Q <> [] and (forall q in Q, 0 < q) and (forall q in Q, q * periodLcm t + L + 2 < 2^L) and coneNonflatCert (periodLcm t) L Q"]

- Lean declaration: [irrational_totient_series_of_lcm_cone_nonflat_supply](../../Erdos249257/LcmConeNonflat.lean#L209)

- outgoing **depends_on_open**: [Z06::lcm_cone_flatness_law](BROWSER_Z06_1.md#node-2b6c6005924da837). The menu refuter contradicts joint flatness of the cone.
- incoming **equivalent_to**: [Z01::erdos249_cone_nonflat_supply_restatement](BROWSER_Z01_1.md#node-4653d6568a5b39ff). Shared declaration irrational_totient_series_of_lcm_cone_nonflat_supply; identical firing-menu supply antecedent.
- incoming **finite_instance_of**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). the three certified cone non-flatness menus are firing coneNonflatCert (periodLcm t) L Q rows, the exact object the menu supply requires at arbitrarily large t.
- incoming **finite_instance_of**: [Z01::engine_strength_separations](BROWSER_Z01_1.md#node-8f3c278e1c645ebc). the recorded three-vertex menu that fires where every two-vertex sub-menu fails is a firing coneNonflatCert instance at one cell of the menu supply family, and it also shows that family is not exhausted by its two-vertex sub-cells.
- incoming **finite_instance_of**: [Z05::t_seven_finite_full_target_miss](BROWSER_Z05_2.md#node-7cc8cb692e7c3423). one of the three routes is the depth-13 two-vertex projection certificate, and two_vertex_certificate_forces_full_target_miss identifies the [1,2] menu with the generic cone non-flatness certificate; so this is a firing coneNonflatCert (periodLcm 7) 13 [1,2] cell of the menu supply.
- outgoing **depends_on_open**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). the three certified non-flatness menus recorded here are the corpus's entire stock of firing menus; the supply needs one per arbitrarily large scale.
- incoming **alias_of**: [Z01::erdos249_cone_nonflat_supply_restatement](BROWSER_Z01_1.md#node-4653d6568a5b39ff). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18812 `irrational_totient_series_of_lcm_cone_nonflat_supply := TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonflat_supply`; same firing-menu supply hypothesis.

<a id="node-0b5ba2e40a1dd8ec"></a>
## reduction_lcm_cone_supply

One certified annihilator anywhere on the two-multiplier lcm cone (h,N) = (m*H_t, q*H_t), at arbitrarily large scale, implies irrationality; the same holds with 'certificate' replaced by bare non-integrality of the cone difference. The wave-23 diagonal is the cell q = m = 1.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : forall t0, exists t, t0 <= t and exists q m L, 0 < q and certifiedKill (m * periodLcm t) (q * periodLcm t) L"]

- Lean declaration: [irrational_totient_series_of_lcm_cone_certificate_supply](../../Erdos249257/LcmConeFlatness.lean#L122)
- Lean declaration: [irrational_totient_series_of_lcm_cone_nonintegrality_supply](../../Erdos249257/LcmConeFlatness.lean#L462)

- outgoing **generalises**: [Z06::reduction_lcm_diagonal_supply](BROWSER_Z06_1.md#node-9bc987ebd91ed7a5). The diagonal is the cone cell q = m = 1.
- incoming **specialises**: [Z06::reduction_lcm_jump_supply](BROWSER_Z06_1.md#node-564a2d94fcffaa77). Jumps are the cone cells (q,m) = (1, H_{t+1}/H_t - 1).
- incoming **equivalent_to**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). Shared declarations irrational_totient_series_of_lcm_cone_certificate_supply / _nonintegrality_supply: one cone-annihilator supply obligation stated in two zones.
- incoming **finite_instance_of**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). the three killed lcm-cone cells are instances of certifiedKill (m*periodLcm t) (q*periodLcm t) L, the annihilator the two-multiplier cone supply asks for at arbitrarily large scale.
- outgoing **depends_on_open**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). the three killed lcm-cone cells here are the only certified annihilators on the cone outside the diagonal; they sit at bounded scale and produce nothing cofinal.
- incoming **alias_of**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18686/18718 re-export `irrational_totient_series_of_lcm_cone_certificate_supply` and `..._of_lcm_cone_nonintegrality_supply`; the two-multiplier cone supply is the same statement.

<a id="node-9bc987ebd91ed7a5"></a>
## reduction_lcm_diagonal_supply

Both free parameters disappear: irrationality follows from the single N-indexed decidable predicate P t := 'some depth certifies (h,N) = (lcm(1..t), lcm(1..t))' holding for infinitely many t. The survivor and pure non-integrality dresses of the same diagonal hypothesis are also recorded.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : forall t0, exists t, t0 <= t and exists L, certifiedKill (periodLcm t) (periodLcm t) L"]

- Lean declaration: [irrational_totient_series_of_lcm_diagonal_certificate_supply](../../Erdos249257/LcmDiagonalReduction.lean#L112)
- Lean declaration: [irrational_totient_series_of_lcm_diagonal_survivor_supply](../../Erdos249257/LcmDiagonalReduction.lean#L122)
- Lean declaration: [irrational_totient_series_of_lcm_diagonal_nonintegrality_supply](../../Erdos249257/LcmConeFlatness.lean#L451)

- incoming **equivalent_to**: [Z06::certificate_supply_is_equivalent_to_249](BROWSER_Z06_1.md#node-b7430ca307ffd27e). irrational_totient_series_iff_lcm_diagonal_certificate_supply proves the diagonal hypothesis is equivalent to #249.
- outgoing **specialises**: [Z06::reduction_lcm_ray_supply](BROWSER_Z06_1.md#node-4d62df0326f8fad7). Standing on the ray at N = H_t removes the position parameter.
- incoming **generalises**: [Z06::reduction_lcm_cone_supply](BROWSER_Z06_1.md#node-0b5ba2e40a1dd8ec). The diagonal is the cone cell q = m = 1.
- outgoing **depends_on_open**: [Z06::lcm_ray_divisibility_skeleton](BROWSER_Z06_1.md#node-190e1b1c4523c82a). The diagonal argument needs h0 | H_t and t <= H_t simultaneously.
- incoming **equivalent_to**: [Z05::supply_conditional_irrationality](BROWSER_Z05_2.md#node-e04cec5031f38bd6). diagonal_not_int_iff_foreignDiagonalDefect_misses_fullTarget unfolds FullTargetAvoidanceSupply into cofinal non-integrality of the lcm diagonal, which is verbatim the hypothesis of irrational_totient_series_of_lcm_diagonal_nonintegrality_supply.
- incoming **finite_instance_of**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). the lcm-diagonal cells killed for t<=6 and at t=7,8 are literally certifiedKill (periodLcm t) (periodLcm t) L, the decidable predicate P t whose cofinal truth is the diagonal supply hypothesis.
- incoming **alias_of**: [Z01::erdos249_period_kill_supply_restatement](BROWSER_Z01_1.md#node-091f2dbf4dfd2e47). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18595/18603 re-export `irrational_totient_series_of_lcm_diagonal_certificate_supply` and `..._survivor_supply`; identical diagonal supply hypothesis.
- incoming **alias_of**: [Z05::supply_conditional_irrationality](BROWSER_Z05_2.md#node-e04cec5031f38bd6). `diagonal_int_iff_foreignDiagonalDefect_hits_fullTarget` (DiagonalPincerDecomposition.lean:215) proves ForeignDiagonalDefectHitsFullTarget t is literally integrality of diagonalTailDifference t, so Z05's weakest socket FullTargetAvoidanceSupply is verbatim the cofinal diagonal non-integrality hypothesis of `irrational_totient_series_of_lcm_diagonal_nonintegrality_supply`; the eighteen-theorem family re-dresses that pre-existing supply rather than weakening it.

<a id="node-564a2d94fcffaa77"></a>
## reduction_lcm_jump_supply

Certified kills at the lcm jumps (h,N) = (H_{t+1} - H_t, H_t), at arbitrarily large t, imply irrationality; jumps are the cone cells (q,m) = (1, H_{t+1}/H_t - 1) and need no side condition.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : forall t0, exists t, t0 <= t and exists L, certifiedKill (periodLcm (t+1) - periodLcm t) (periodLcm t) L"]

- Lean declaration: [irrational_totient_series_of_lcm_jump_kill_supply](../../Erdos249257/LcmConeNonflat.lean#L241)

- outgoing **specialises**: [Z06::reduction_lcm_cone_supply](BROWSER_Z06_1.md#node-0b5ba2e40a1dd8ec). Jumps are the cone cells (q,m) = (1, H_{t+1}/H_t - 1).
- incoming **alias_of**: [Z01::erdos249_cone_supply_restatement](BROWSER_Z01_1.md#node-4007efd56b0e194f). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18824 `irrational_totient_series_of_lcm_jump_window_kill_supply := TotientTailPeriodKiller.irrational_totient_series_of_lcm_jump_kill_supply`; identical lcm-jump supply hypothesis.

<a id="node-4d62df0326f8fad7"></a>
## reduction_lcm_ray_supply

The whole 'for every period' obligation collapses onto the single one-parameter family h = lcm(1..t): certificates along that ray at arbitrarily large t and arbitrarily large N imply irrationality.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : forall t0 N0, exists t, t0 <= t and exists N, N0 <= N and exists K, survivorKill (periodLcm t) N K (endpoint variant with certifiedKill)"]

- Lean declaration: [irrational_totient_series_of_lcm_survivor_supply](../../Erdos249257/CarrySurvivorExtinction.lean#L540)
- Lean declaration: [irrational_totient_series_of_lcm_certificate_supply](../../Erdos249257/LcmDiagonalReduction.lean#L92)

- outgoing **specialises**: [Z06::reduction_multiple_period_supply](BROWSER_Z06_1.md#node-0818db056d314224). lcm(1..t) is a universal multiple, collapsing the ray family to one parameter.
- incoming **specialises**: [Z06::reduction_lcm_diagonal_supply](BROWSER_Z06_1.md#node-9bc987ebd91ed7a5). Standing on the ray at N = H_t removes the position parameter.
- incoming **alias_of**: [Z01::erdos249_period_kill_supply_restatement](BROWSER_Z01_1.md#node-091f2dbf4dfd2e47). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18538/18585 re-export `irrational_totient_series_of_lcm_survivor_supply` and `..._of_lcm_certificate_supply`; identical lcm-family supply hypothesis.

<a id="node-0818db056d314224"></a>
## reduction_multiple_period_supply

It suffices to kill, for each primitive period h0, some multiple m*h0 at arbitrarily large positions: a certificate (endpoint or survivor form) along any multiple of each primitive period implies irrationality.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : forall h0, 0 < h0 -> forall N0, exists m, 0 < m and exists N, N0 <= N and exists K, survivorKill (m * h0) N K (endpoint variant: exists L, certifiedKill (m * h0) N L)"]

- Lean declaration: [irrational_totient_series_of_multiple_survivor_supply](../../Erdos249257/CarrySurvivorExtinction.lean#L491)
- Lean declaration: [irrational_totient_series_of_multiple_certificate_supply](../../Erdos249257/CarrySurvivorExtinction.lean#L502)

- outgoing **generalises**: [Z06::reduction_pointwise_certificate_supply](BROWSER_Z06_1.md#node-eb9013360d8a36f2). Weakens the obligation from every period to one multiple per divisibility ray, using period-ray telescoping.
- incoming **specialises**: [Z06::reduction_lcm_ray_supply](BROWSER_Z06_1.md#node-4d62df0326f8fad7). lcm(1..t) is a universal multiple, collapsing the ray family to one parameter.
- outgoing **depends_on_open**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). the endpoint and survivor kills recorded here are the only realised multiples m*h0 carrying a firing certificate, and they sit at two fixed positions; nothing produces a kill at arbitrarily large N for a general primitive period.
- incoming **alias_of**: [Z01::erdos249_period_kill_supply_restatement](BROWSER_Z01_1.md#node-091f2dbf4dfd2e47). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18523/18530 re-export `irrational_totient_series_of_multiple_survivor_supply` and `..._of_multiple_certificate_supply`; identical one-kill-per-divisibility-ray hypothesis.

<a id="node-eb9013360d8a36f2"></a>
## reduction_pointwise_certificate_supply

If for every period h >= 1 and every threshold N0 there is some N >= N0 and depth L with a firing endpoint certificate, then the #249 series is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["hsupply : forall h, 0 < h -> forall N0, exists N, N0 <= N and exists L, certifiedKill h N L"]

- Lean declaration: [irrational_totient_series_of_certificate_supply](../../Erdos249257/TotientTailPeriodKiller.lean#L394)

- incoming **equivalent_to**: [Z06::certificate_supply_is_equivalent_to_249](BROWSER_Z06_1.md#node-b7430ca307ffd27e). The iff theorems show the wave-21 supply hypothesis is exactly #249, so the reduction adds no unconditional content.
- incoming **generalises**: [Z06::reduction_multiple_period_supply](BROWSER_Z06_1.md#node-0818db056d314224). Weakens the obligation from every period to one multiple per divisibility ray, using period-ray telescoping.
- incoming **barrier_for**: [Z06::endpoint_certificate_depth_floor](BROWSER_Z06_1.md#node-3ca91ce92ac997b8). No certificate supply can be realised at bounded depth; depth must grow at least logarithmically in N+h.
- incoming **equivalent_to**: [Z01::erdos249_period_kill_supply_restatement](BROWSER_Z01_1.md#node-091f2dbf4dfd2e47). Both nodes carry irrational_totient_series_of_certificate_supply; each is Erdos #249 with the open content moved into the same cofinal certificate-supply hypothesis.
- incoming **finite_instance_of**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). the fixture kills certifiedKill h 12 16 for h<=8 and certifiedKill h 14 9 for h<=16 are cells of the same predicate the pointwise supply quantifies as 'for every h and every N0 some N>=N0 with a firing depth'; only the two bases N=12,14 are realised.
- outgoing **depends_on_open**: [Z01::certified_kill_fixtures](BROWSER_Z01_1.md#node-f5235071542ebedb). the fixtures produce certifiedKill h N L only at the two bases N = 12 and N = 14 and only for h <= 8 and h <= 16; the supply demands arbitrarily large N for every h, and no node supplies a further base for any h.
- incoming **alias_of**: [Z01::erdos249_period_kill_supply_restatement](BROWSER_Z01_1.md#node-091f2dbf4dfd2e47). Erdos249257/CertificateKernel.lean is a re-export facade: the Z01 declaration is a one-line restatement whose proof term is literally the owning module's declaration. CertificateKernel.lean:18464 `irrational_totient_series_of_period_kill_supply := TotientTailPeriodKiller.irrational_totient_series_of_certificate_supply`; the two nodes carry the same free hypothesis verbatim.

