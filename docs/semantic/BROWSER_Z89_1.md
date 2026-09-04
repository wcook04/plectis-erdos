# Z89_1: Free-N totient walk: affine residue dynamics, outer-band escape, and the coarse-model barrier

[All problems and zones](BROWSER.md)

<a id="node-3c3feb3376ce29bd"></a>
## elementary_totient_bounds_give_the_exact_coarse_two_sided_step_budget

PROVED STEP BUDGET: Euler's totient satisfies 2≤phi(n) for n≥3. Consequently, whenever 2≤N+L, walkStep h N L lies between 2-(N+L) and N+h+L-2, and at every shifted basepoint N+j it lies between 2-(N+j+L) and N+j+h+L-2.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The interval is the complete information used by the later coarse model, but actual totient differences satisfy additional arithmetic constraints such as parity. The budget alone does not determine an actual orbit or force escape.

- Lean declaration: [two_le_totient](../../ErdosProblems/Half/FreeWalk1.lean#L170)
- Lean declaration: [walkStep_le](../../ErdosProblems/Half/FreeWalk1.lean#L176)
- Lean declaration: [walkStep_ge](../../ErdosProblems/Half/FreeWalk1.lean#L191)
- Lean declaration: [real_step_budget](../../ErdosProblems/Half/FreeWalk1.lean#L206)

- incoming **generated_by**: [Z89::thin_outer_failure_bands_conditionally_force_a_nearby_certified_kill](BROWSER_Z89_1.md#node-82857f20bf3c6e0b). The lower and upper step inequalities provide the one-step control that makes excess above either trapping radius double during a continuing failure run.
- incoming **complements**: [Z89::the_coarse_recurrence_and_size_budget_admit_permanently_trapped_model_walks](BROWSER_Z89_1.md#node-548d37fefaa454b7). The budget node states what elementary totient size information gives for the real walk; the trap node shows that this interval data, abstracted without finer arithmetic, still permits permanent model failures.

<a id="node-548d37fefaa454b7"></a>
## the_coarse_recurrence_and_size_budget_admit_permanently_trapped_model_walks

PROVED COARSE-MODEL BARRIER: AdmissibleRun contains an upper linear walk starting at N+L-1, a lower linear walk starting at codistance N+h+L-1, and every constant walk c in the interior interval -(N+h+L-2)≤c≤N+L-2 with step -c. Thus this abstract recurrence-plus-budget model has walks that fail forever, and its two escape thresholds are sharp to one unit.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: AdmissibleRun omits parity and finer arithmetic of actual totient differences. The exhibited walks are not proved to be genuine totient orbits; in particular the threshold witnesses use odd steps. The barrier exhausts a size-only proof strategy, not Erdős #249 and not every strengthened walk model.

- Lean declaration: [trap_upper](../../ErdosProblems/Half/FreeWalk1.lean#L427)
- Lean declaration: [trap_lower](../../ErdosProblems/Half/FreeWalk1.lean#L446)
- Lean declaration: [trap_interior](../../ErdosProblems/Half/FreeWalk1.lean#L469)
- Lean declaration: [no_absolute_bound_on_consecutive_failures](../../ErdosProblems/Half/FreeWalk1.lean#L489)
- Lean declaration: [thresholds_are_sharp](../../ErdosProblems/Half/FreeWalk1.lean#L501)

- outgoing **barrier_for**: [Z89::thin_outer_failure_bands_conditionally_force_a_nearby_certified_kill](BROWSER_Z89_1.md#node-82857f20bf3c6e0b). Permanent admissible traps one unit inside the thresholds block any extension from the proved outer bands to a global escape theorem using only the affine recurrence and coarse interval budget.
- outgoing **complements**: [Z89::elementary_totient_bounds_give_the_exact_coarse_two_sided_step_budget](BROWSER_Z89_1.md#node-3c3feb3376ce29bd). The budget node states what elementary totient size information gives for the real walk; the trap node shows that this interval data, abstracted without finer arithmetic, still permits permanent model failures.

<a id="node-2292e5a5ef43ab00"></a>
## the_reduced_window_discrepancy_obeys_an_exact_affine_recurrence_and_failure_arc_description

PROVED WALK COORDINATES: the residue rho_N=walkRes h N L is the canonical representative with 0≤rho_N<2^L, its codistance satisfies rho_N=2^L-walkCo h N L, and advancing N gives rho_(N+1)=(2*rho_N+walkStep h N L) mod 2^L. A certified kill fails exactly when rho_N lies in one of the two edge intervals of radius N+h+L+2.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: These identities describe the orbit and its failure set but do not show that any orbit enters an escape band, leaves the failure arc, or yields a cofinal supply of certified kills.

- Lean declaration: [walkRes_nonneg](../../ErdosProblems/Half/FreeWalk1.lean#L147)
- Lean declaration: [walkRes_lt](../../ErdosProblems/Half/FreeWalk1.lean#L150)
- Lean declaration: [walkRes_eq](../../ErdosProblems/Half/FreeWalk1.lean#L153)
- Lean declaration: [walkRes_succ](../../ErdosProblems/Half/FreeWalk1.lean#L159)
- Lean declaration: [not_certifiedKill_iff](../../ErdosProblems/Half/FreeWalk1.lean#L221)

- incoming **generated_by**: [Z89::thin_outer_failure_bands_conditionally_force_a_nearby_certified_kill](BROWSER_Z89_1.md#node-82857f20bf3c6e0b). Both escape inductions evolve the canonical residue or codistance through the exact affine recurrence and use the failure-arc equivalence to select the surviving edge branch.

<a id="node-052c633dc9f74730"></a>
## the_two_escape_bands_have_h_plus_six_residues_and_can_be_an_arbitrarily_small_fraction_of_the_failure_arc

PROVED COVERAGE ACCOUNTING: the upper escape band contains h+3 integers and the lower escape band contains 3, for h+6 covered residues in total. For every multiplier M there exists a basepoint N such that the full failure-arc count 2*(N+h+L)+5 exceeds M*(h+6).

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Despite its Lean name, coverage_fraction_tends_to_zero proves one existential basepoint for each multiplier. It does not formalize a limit, an eventual-for-all statement, or any classification of actual totient-walk residues.

- Lean declaration: [upperBand_card](../../ErdosProblems/Half/FreeWalk1.lean#L514)
- Lean declaration: [lowerBand_card](../../ErdosProblems/Half/FreeWalk1.lean#L520)
- Lean declaration: [coverage_fraction_tends_to_zero](../../ErdosProblems/Half/FreeWalk1.lean#L530)

- outgoing **complements**: [Z89::thin_outer_failure_bands_conditionally_force_a_nearby_certified_kill](BROWSER_Z89_1.md#node-82857f20bf3c6e0b). The counting node measures exactly how many edge residues the two conditional escape engines cover and records the existential dilution as N grows.

<a id="node-82857f20bf3c6e0b"></a>
## thin_outer_failure_bands_conditionally_force_a_nearby_certified_kill

PROVED CONDITIONAL ESCAPE ENGINE: under the explicit no-wrap room inequality, a failing residue in the upper band N+L≤rho_N≤N+h+L+2 forces a certified kill within K steps whenever h+3<2^(K-1), hence within log_2(h+3)+1 steps in the logarithmic form. Dually, codistance N+h+L≤walkCo≤N+h+L+2 forces a certified kill at N+1 or N+2.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The conclusions apply only after the stated room and outer-band hypotheses are proved. They cover neither the interior failure residues nor every basepoint, and therefore provide no global bound on failures and no proof of irrationality.

Open hypotheses: ["For a general upper-band application, the room inequality and the initial membership N+L≤walkRes h N L≤N+h+L+2.", "For a general lower-band application, the corresponding room inequality and N+h+L≤walkCo h N L≤N+h+L+2."]

- Lean declaration: [upperBand_run](../../ErdosProblems/Half/FreeWalk1.lean#L233)
- Lean declaration: [certifiedKill_of_upperBand](../../ErdosProblems/Half/FreeWalk1.lean#L282)
- Lean declaration: [certifiedKill_of_upperBand_log](../../ErdosProblems/Half/FreeWalk1.lean#L303)
- Lean declaration: [lowerBand_run](../../ErdosProblems/Half/FreeWalk1.lean#L321)
- Lean declaration: [certifiedKill_of_lowerBand](../../ErdosProblems/Half/FreeWalk1.lean#L388)

- outgoing **generated_by**: [Z89::the_reduced_window_discrepancy_obeys_an_exact_affine_recurrence_and_failure_arc_description](BROWSER_Z89_1.md#node-2292e5a5ef43ab00). Both escape inductions evolve the canonical residue or codistance through the exact affine recurrence and use the failure-arc equivalence to select the surviving edge branch.
- outgoing **generated_by**: [Z89::elementary_totient_bounds_give_the_exact_coarse_two_sided_step_budget](BROWSER_Z89_1.md#node-3c3feb3376ce29bd). The lower and upper step inequalities provide the one-step control that makes excess above either trapping radius double during a continuing failure run.
- incoming **barrier_for**: [Z89::the_coarse_recurrence_and_size_budget_admit_permanently_trapped_model_walks](BROWSER_Z89_1.md#node-548d37fefaa454b7). Permanent admissible traps one unit inside the thresholds block any extension from the proved outer bands to a global escape theorem using only the affine recurrence and coarse interval budget.
- incoming **complements**: [Z89::the_two_escape_bands_have_h_plus_six_residues_and_can_be_an_arbitrarily_small_fraction_of_the_failure_arc](BROWSER_Z89_1.md#node-052c633dc9f74730). The counting node measures exactly how many edge residues the two conditional escape engines cover and records the existential dilution as N grows.
- incoming **finite_instance_of**: [Z89::two_kernel_checked_cells_realise_the_lower_and_upper_escape_engines](BROWSER_Z89_1.md#node-af707b8216b79cac). The h=9 lower-band cell and h=30 upper-band cell discharge the respective hypotheses and realize their predicted nearby certified kills.

<a id="node-af707b8216b79cac"></a>
## two_kernel_checked_cells_realise_the_lower_and_upper_escape_engines

PROVED FINITE NON-VACUITY: at (h,N,L)=(9,9,10), walkCo=30, the lower-band theorem applies, the starting cell fails, and certifiedKill holds at N=10. At (30,1,10), walkRes=14, the upper-band theorem applies with K=7, the cells N=1 and N=2 fail, and certifiedKill holds at N=3.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The examples show only that both conditional engines have genuine inputs and nontrivial realizations. Two cells do not supply a uniform, cofinal, or density statement and do not prove irrationality.

- Lean declaration: [lowerBand_instance_data](../../ErdosProblems/Half/FreeWalk1.lean#L537)
- Lean declaration: [lowerBand_instance](../../ErdosProblems/Half/FreeWalk1.lean#L544)
- Lean declaration: [lowerBand_instance_realised](../../ErdosProblems/Half/FreeWalk1.lean#L553)
- Lean declaration: [upperBand_instance_data](../../ErdosProblems/Half/FreeWalk1.lean#L560)
- Lean declaration: [upperBand_instance](../../ErdosProblems/Half/FreeWalk1.lean#L567)
- Lean declaration: [upperBand_instance_realised](../../ErdosProblems/Half/FreeWalk1.lean#L576)

- outgoing **finite_instance_of**: [Z89::thin_outer_failure_bands_conditionally_force_a_nearby_certified_kill](BROWSER_Z89_1.md#node-82857f20bf3c6e0b). The h=9 lower-band cell and h=30 upper-band cell discharge the respective hypotheses and realize their predicted nearby certified kills.

