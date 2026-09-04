# Z49_1: Totient tail carry period: no-go bounds, directed certificates, and mod-four pulse reduction

[All problems and zones](BROWSER.md)

<a id="node-d061d3e967b8baec"></a>
## a_mersenne_divisor_does_not_annihilate_integral_tail_shifts_by_itself

PROVED CONTROL COUNTERMODEL: for every 0<K<q with q dividing 2^K-1, the completely multiplicative control c(n)=n has rational binary series value 2 and, at every N, an integral K-shift equal to K that is nonzero modulo q.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The countermodel is c(n)=n, not phi(n). It proves that divisibility by a factor of 2^K-1 plus integrality alone is insufficient; a totient-specific restriction may still succeed.

- Lean declaration: [idCoeff_mersenneModulus_does_not_annihilate_tailShift](../../Erdos249257/TotientTailCarryPeriod.lean#L342)

- outgoing **complements**: [Z49::positive_four_multiple_shifts_have_cofinally_many_mod_four_totient_pulses](BROWSER_Z49_1.md#node-38b449fd2a265211). The control countermodel shows why a homogeneous Mersenne divisor is insufficient, while the mod-four theorem supplies genuinely totient-specific residue information.

<a id="node-f847311b66b3ba33"></a>
## absolute_adjugate_tail_estimates_have_a_universal_cost_floor

PROVED NO-GO: any finite rational row w that exactly isolates one totient channel, sum_i w_i*phi(x_i)=1, has totientAdjugateTailCost w x at least 3; therefore that cost can never satisfy the strict threshold cost<1.

Class: barrier_no_go. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: This excludes only the crude termwise absolute-tail budget. It does not exclude cancellation-sensitive inverse methods, other reconstruction norms, or Erdős #249 itself.

- Lean declaration: [three_le_totientAdjugateTailCost](../../Erdos249257/TotientTailCarryPeriod.lean#L266)
- Lean declaration: [not_totientAdjugateTailCost_lt_one](../../Erdos249257/TotientTailCarryPeriod.lean#L307)

- outgoing **complements**: [Z49::cofinal_mod_four_pulse_survivor_kills_would_imply_irrationality](BROWSER_Z49_1.md#node-faa279dd6df4a49d). The first node closes a crude global reconstruction route; the latter isolates a different residue-and-finite-state route with an explicit open producer.

<a id="node-b5ab6cee36f8ad62"></a>
## cofinal_directed_lcm_certificate_supply_is_an_open_diagonal_predicate

OPEN PREDICATE: CofinalDirectedLcmCertificateSupply requires that beyond every t0 there is t>=t0 and a depth L for which directedCertifiedKill (periodLcm t) (periodLcm t) L holds.

Class: infrastructure. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The definition has no inhabitant in this selected evidence. A later theorem in the source identifies its exact ceiling, but that theorem is outside this bounded role packet.

Open hypotheses: ["A cofinal supply of directed certificate depths on the diagonal cells (periodLcm t, periodLcm t)."]

- Lean declaration: [CofinalDirectedLcmCertificateSupply](../../Erdos249257/TotientTailCarryPeriod.lean#L866)

- outgoing **generated_by**: [Z49::directed_certified_kill_is_the_asymmetric_central_arc_predicate](BROWSER_Z49_1.md#node-f24a64f6ab6631ea). The supply predicate quantifies the directed certificate over cofinally many diagonal LCM cells.

<a id="node-faa279dd6df4a49d"></a>
## cofinal_mod_four_pulse_survivor_kills_would_imply_irrationality

OPEN CONDITIONAL REDUCTION: if for every h>0 and threshold B there is a prime p>B with deltaTotient (4*h) p congruent to 2 modulo 4 and some finite modFourPulseSurvivorKill at (4*h,p), then the totient series is irrational.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The arithmetic pulse theorem proves only the pulse part of the antecedent. The survivor-kill supply remains unproved, so this theorem does not settle Erdős #249.

Open hypotheses: ["For every h>0 and B, a cofinal mod-four pulse prime p together with a finite K satisfying modFourPulseSurvivorKill (4*h) p K."]

- Lean declaration: [irrational_totientSeries_of_cofinal_modFourPulseSurvivorKill](../../Erdos249257/TotientTailCarryPeriod.lean#L1066)

- outgoing **complements**: [Z49::positive_four_multiple_shifts_have_cofinally_many_mod_four_totient_pulses](BROWSER_Z49_1.md#node-38b449fd2a265211). The arithmetic theorem independently supplies the cofinal pulse-prime component, while the conditional reduction additionally requires the unproved finite survivor-kill component.
- incoming **complements**: [Z49::absolute_adjugate_tail_estimates_have_a_universal_cost_floor](BROWSER_Z49_1.md#node-f847311b66b3ba33). The first node closes a crude global reconstruction route; the latter isolates a different residue-and-finite-state route with an explicit open producer.

<a id="node-f24a64f6ab6631ea"></a>
## directed_certified_kill_is_the_asymmetric_central_arc_predicate

REPRESENTATION: directedCertifiedKill h N L requires the length-L discrepancy residue modulo 2^L to lie between the lower bound N+L+2 and the upper bound 2^L-(N+h+L+2), retaining the two directed tail radii separately.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The definition is decidable but does not assert that any cell fires. This selected role alone neither states soundness/completeness nor supplies a cofinal family.

- Lean declaration: [directedCertifiedKill](../../Erdos249257/TotientTailCarryPeriod.lean#L766)

- incoming **generated_by**: [Z49::cofinal_directed_lcm_certificate_supply_is_an_open_diagonal_predicate](BROWSER_Z49_1.md#node-b5ab6cee36f8ad62). The supply predicate quantifies the directed certificate over cofinally many diagonal LCM cells.

<a id="node-38b449fd2a265211"></a>
## positive_four_multiple_shifts_have_cofinally_many_mod_four_totient_pulses

PROVED ARITHMETIC SUPPLY: for every h>0 and threshold B, there is a prime p>B with deltaTotient (4*h) p congruent to 2 modulo 4.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: formalisation_only.

Scope: The theorem supplies only the arithmetic pulse. It does not kill the finite candidate states left by the carry recurrence and therefore does not imply irrationality alone.

- Lean declaration: [exists_prime_deltaTotient_four_mul_mod_four_two](../../Erdos249257/TotientTailCarryPeriod.lean#L384)

- incoming **complements**: [Z49::cofinal_mod_four_pulse_survivor_kills_would_imply_irrationality](BROWSER_Z49_1.md#node-faa279dd6df4a49d). The arithmetic theorem independently supplies the cofinal pulse-prime component, while the conditional reduction additionally requires the unproved finite survivor-kill component.
- incoming **complements**: [Z49::a_mersenne_divisor_does_not_annihilate_integral_tail_shifts_by_itself](BROWSER_Z49_1.md#node-d061d3e967b8baec). The control countermodel shows why a homogeneous Mersenne divisor is insufficient, while the mod-four theorem supplies genuinely totient-specific residue information.

