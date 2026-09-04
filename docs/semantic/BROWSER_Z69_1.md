# Z69_1: Erdős 269 running-LCM coordinates: prefix witnesses, jump channels, finite fibres, shells, and residue escape

[All problems and zones](BROWSER.md)

<a id="node-666ddddc0b092cc0"></a>
## finite_height_fibres_are_the_exact_coordinates_for_regrouping_the_kernel

smoothExponentBox hp hq hr is the rectangular box 0≤i≤hp, 0≤j≤hq, 0≤k≤hr. smoothPointHeight maps a triple to the three-prime height of its smooth value, and smoothHeightFiber p q r hp hq hr H filters the box to the triples whose point height is exactly H.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: These definitions form a finite full-box coordinate system, not the cutoff-filtered prefix and not an infinite series. They do not establish the already-authored fibre-sum normal form by themselves.

- Lean declaration: [smoothExponentBox](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L368)
- Lean declaration: [smoothPointHeight](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L373)
- Lean declaration: [smoothHeightFiber](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L377)

- outgoing **generated_by**: [Z69::smooth_prefix_coordinates_carry_the_exact_extremal_divisibility_witnesses](BROWSER_Z69_1.md#node-7cf77c8d8c13d71d). The point-height and fibre definitions apply the same smooth-value and logarithmic-height coordinates to a finite rectangular exponent domain.
- outgoing **complements**: [Z69::same_three_prime_log_cell_is_exact_coordinate_equality](BROWSER_Z69_1.md#node-ae3c945119879b01). Log cells explain why several lattice points can share a height, while fibres collect all points with one attained height without asserting that each fibre is a single cell.
- incoming **complements**: [Z69::smooth_exponent_shell_is_the_actual_interval_filtered_box](BROWSER_Z69_1.md#node-2df4da6e550bc91f). Both are finite exponent-box filters: fibres filter by exact running height, whereas shells filter smooth values by a half-open multiplicative interval.

<a id="node-6e911a8c098ed770"></a>
## finite_prime_power_channels_are_disjoint_and_share_only_the_origin

For a prime p, positivePrimePowers p count is the image of exponents 1 through count under e↦p^e, so it excludes 1. Positive-power channels of two distinct primes are disjoint. threePrimePositiveJumpSet is the union of the first count positive powers in the p, q, and r channels, and threePrimeJumpSetWithOrigin adjoins the single common origin 1.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This is a finite jump-coordinate system. It neither orders the union, passes to all powers, nor proves any statement about the infinite running-LCM series; the already-authored cardinality theorems remain in Z17.

- Lean declaration: [positivePrimePowers](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L204)
- Lean declaration: [one_not_mem_positivePrimePowers](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L219)
- Lean declaration: [positivePrimePowers_disjoint](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L229)
- Lean declaration: [threePrimePositiveJumpSet](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L243)
- Lean declaration: [threePrimeJumpSetWithOrigin](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L273)

- outgoing **complements**: [Z69::smooth_prefix_coordinates_carry_the_exact_extremal_divisibility_witnesses](BROWSER_Z69_1.md#node-7cf77c8d8c13d71d). The prefix coordinates describe the running value at a cutoff; the channel coordinates describe the finite set of pure-power events at which those logarithmic maxima can change.

<a id="node-e9f579b071d2655b"></a>
## residue_escape_window_is_the_strict_canonical_range_predicate

ResidueEscapesWindow C bound residue means exactly bound<residue≤C: the proposed residue lies strictly above the bounded-state window while remaining in the canonical positive residue range through the modulus.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The predicate does not produce an escaping residue. The denominator-dependent cofinal local-window escape theorem and the identification of the actual rational tail with a bounded carry remain open.

- Lean declaration: [ResidueEscapesWindow](../../ErdosProblems/Erdos269/ResidueEscape.lean#L71)

- outgoing **complements**: [Z69::tail_state_step_is_the_variable_base_integer_orbit_coordinate](BROWSER_Z69_1.md#node-5d74d8cccd8333ef). The affine step is the local recurrence coordinate, while the escape predicate is the finite modular condition consumed only after a bounded actual carry and an accumulated window have been supplied.

<a id="node-ae3c945119879b01"></a>
## same_three_prime_log_cell_is_exact_coordinate_equality

SameThreePrimeLogCell p q r x y means exactly that log_p x=log_p y, log_q x=log_q y, and log_r x=log_r y.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The definition alone states no constancy theorem and no ordering of cells. The height, LCM, and kernel constancy theorems remain separately authored in Z17.

- Lean declaration: [SameThreePrimeLogCell](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L163)

- outgoing **generated_by**: [Z69::smooth_prefix_coordinates_carry_the_exact_extremal_divisibility_witnesses](BROWSER_Z69_1.md#node-7cf77c8d8c13d71d). The cell predicate freezes exactly the three logarithmic coordinates used by threePrimeHeight and therefore by the reciprocal kernel coordinate.
- incoming **complements**: [Z69::finite_height_fibres_are_the_exact_coordinates_for_regrouping_the_kernel](BROWSER_Z69_1.md#node-666ddddc0b092cc0). Log cells explain why several lattice points can share a height, while fibres collect all points with one attained height without asserting that each fibre is a single cell.

<a id="node-2df4da6e550bc91f"></a>
## smooth_exponent_shell_is_the_actual_interval_filtered_box

smoothExponentShell p q r lo hi hp hq hr is the finite exponent box with bounds hp,hq,hr filtered to the triples whose smooth values lie in the half-open interval [lo,hi).

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The definition supplies no cardinality or tail estimate. Its bases and coordinate bounds are ordered parameters; the shell is not invariant under silently relabelling them.

- Lean declaration: [smoothExponentShell](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L500)

- outgoing **complements**: [Z69::finite_height_fibres_are_the_exact_coordinates_for_regrouping_the_kernel](BROWSER_Z69_1.md#node-666ddddc0b092cc0). Both are finite exponent-box filters: fibres filter by exact running height, whereas shells filter smooth values by a half-open multiplicative interval.
- incoming **complements**: [Z69::sorted_three_coordinate_heights_obey_the_exact_quadratic_budget](BROWSER_Z69_1.md#node-8a57e7042f053d93). The arithmetic inequality supplies the denominator-free final budget used after a short shell has been injected into its two smallest coordinate ranges.

<a id="node-7cf77c8d8c13d71d"></a>
## smooth_prefix_coordinates_carry_the_exact_extremal_divisibility_witnesses

The three-prime coordinate system consists of smooth3Val p q r i j k = p^i q^j r^k, the logarithmic height p^(log_p x) q^(log_q x) r^(log_r x), its reciprocal rational kernel at a smooth lattice point, the logarithmically bounded and cutoff-filtered exponent prefix, and the literal LCM of that prefix. Every value in the actual prefix divides the height, and for x nonzero each of the three maximal pure-power components occurs in the prefix.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: This node records the coordinates and the two divisibility directions' local witnesses, not the already-authored equality theorem itself. It proves no infinite reindexing, convergence, irrationality, or transcendence statement.

- Lean declaration: [smooth3Val](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L31)
- Lean declaration: [threePrimeHeight](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L36)
- Lean declaration: [threePrimeKernelQ](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L40)
- Lean declaration: [smoothPrefixExponents](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L46)
- Lean declaration: [smoothPrefixLcm](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L53)
- Lean declaration: [smooth3Val_dvd_threePrimeHeight_of_mem](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L59)
- Lean declaration: [pureFirst_mem_smoothPrefixExponents](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L84)
- Lean declaration: [pureSecond_mem_smoothPrefixExponents](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L97)
- Lean declaration: [pureThird_mem_smoothPrefixExponents](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L110)

- incoming **generated_by**: [Z69::same_three_prime_log_cell_is_exact_coordinate_equality](BROWSER_Z69_1.md#node-ae3c945119879b01). The cell predicate freezes exactly the three logarithmic coordinates used by threePrimeHeight and therefore by the reciprocal kernel coordinate.
- incoming **complements**: [Z69::finite_prime_power_channels_are_disjoint_and_share_only_the_origin](BROWSER_Z69_1.md#node-6e911a8c098ed770). The prefix coordinates describe the running value at a cutoff; the channel coordinates describe the finite set of pure-power events at which those logarithmic maxima can change.
- incoming **generated_by**: [Z69::finite_height_fibres_are_the_exact_coordinates_for_regrouping_the_kernel](BROWSER_Z69_1.md#node-666ddddc0b092cc0). The point-height and fibre definitions apply the same smooth-value and logarithmic-height coordinates to a finite rectangular exponent domain.

<a id="node-8a57e7042f053d93"></a>
## sorted_three_coordinate_heights_obey_the_exact_quadratic_budget

If a≤b≤c and a+b+c=j, then 9(a+1)(b+1)≤(j+3)^2.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Sorting is a theorem hypothesis, not a free relabelling of an asymmetric smooth shell. This arithmetic inequality alone neither bounds a shell nor estimates an infinite tail.

- Lean declaration: [sorted_pair_quadratic](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L629)

- outgoing **complements**: [Z69::smooth_exponent_shell_is_the_actual_interval_filtered_box](BROWSER_Z69_1.md#node-2df4da6e550bc91f). The arithmetic inequality supplies the denominator-free final budget used after a short shell has been injected into its two smallest coordinate ranges.

<a id="node-5d74d8cccd8333ef"></a>
## tail_state_step_is_the_variable_base_integer_orbit_coordinate

tailStateStep base digit state is the integer base*(state-digit), the one-step coordinate used for the variable-base tail orbit.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: No orbit is constructed or analysed here, and this definition is not identified with the actual #269 rational tail. The rationality-to-carry instantiation remains open.

- Lean declaration: [tailStateStep](../../ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L487)

- incoming **complements**: [Z69::residue_escape_window_is_the_strict_canonical_range_predicate](BROWSER_Z69_1.md#node-e9f579b071d2655b). The affine step is the local recurrence coordinate, while the escape predicate is the finite modular condition consumed only after a bounded actual carry and an accumulated window have been supplied.

