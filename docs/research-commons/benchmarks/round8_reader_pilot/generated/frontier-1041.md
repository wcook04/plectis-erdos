Erdős #1041 | source-bound frontier
Snapshot: sha256:dd6c9fa13a7010924a0de2e161509b881d36d017e9ab225fcb887f0804e3254b

Generated navigation over pinned owner bytes, not a new mathematical authority. Status strings are owner-reported, compilation is not replayed here, dependencies are not implications, and unbound relation text is excluded from inference.

Programme statement (verbatim, not a claim of unique maximal strength):
Using ani's explicit monic degree-seven polynomial, Lean proves that every preconnected subset of its strict unit lemniscate containing two distinct roots has one-dimensional Hausdorff measure greater than 2. This refutes the exact Formal Conjectures path-image-length statement and its total-variation counterpart. The reported family is not formalised, and independent human review of correspondence with the 1958 wording is not recorded.

Registered open obligations:
- remaining_open.erdos_1041_lemniscate_connection: Independently review whether the 1958 curve-length wording matches the exact Formal Conjectures path-image-length statement, whose negation is now Lean-checked using ani's explicit degree-seven polynomial. The checked one-dimensional Hausdorff-measure bound settles that formal statement negatively; the reported small-parameter family is not formalised.

Results explicitly named by the programme statement (not paginated):

Endpoint certificate signatures (source-listed; typed replay required):

Registered results (identifier order, never strength order):
- ani_degree_seven_total_variation_counterexample [formalised here]: For ani's explicit monic complex polynomial of degree seven, whose distinct roots lie in the open unit disc, every preconnected subset of the strict unit lemniscate containing two distinct roots has one-dimensional Hausdorff measure greater than 2. In particular, Lean proves the negation and answer(False) forms of the exact Formal Conjectures path-image-length statement. The total-variation bound also remains checked. This formalises one polynomial, not the reported small-parameter family; independent human review of correspondence with the 1958 wording is not recorded.
- newton_ray_separation_consumer [unconditional progress]: An explicit exponential-decay Newton connection can occur only when its endpoint values lie on the same positive ray; conversely, every finite injective complex family admits an arbitrarily small common translation making all values nonzero and all positive-ray arguments distinct. These are finite perturbative and conditional connection statements.

Known misreadings:
- c-1041-false-target: ani's theorem shows every preconnected set joining two roots of the degree-seven example has one-dimensional Hausdorff measure above 2, which refutes the claim that an intrinsic distance of 2 is attained only in the limit of z^n - r^n and refutes extremality of that family; it does not fix the value of any supremum. The recorded supremum came from grid searches over chosen families and carries the evidence class of a measurement about those families (erdos1041_counterexample_hausdorff).
- c-clause-vacuity-not-result-vacuity: Off the switch condition the maximality clause is vacuous (inner_chord_maximality_vacuous_off_switch), but the midpoint equality is still asserted there, and the added region is inhabited: the switch fails at n = 3, r = 1/2 (switch_fails_at_three_half), where the factored theorem gives the equality (inner_chord_midpoint_at_three_half).
- c-displayed-unused-vs-open-premise: The proof term is subcritical_perimeter_path applied to mul_nonneg hβ.le (Real.rpow_nonneg hμpos.le _) and hsplit. It uses hβ and hμpos, only to show the length budget β μ^(1/n) is nonnegative, and the open premise hsplit : SubcriticalSplitExists. The paper hypotheses hmonic, hsf, hdeg, hn, hμ and hperim are unused. The result stays conditional on hsplit.

Relations: 2 navigation rows; existing endpoint text is quarantined.
Recorded attempts: 1; paper-ledger rows: 52.
Use JSON for complete source references, relation observations and attempt boundaries.
Current argument graph: not_admitted_no_current_replay_receipt
Page: {"next":null,"offset":0,"order":"identifier_not_strength","returned":2,"total":2}
