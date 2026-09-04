# Z73_1: Prime-ray order consumers, finite-support escape, and unbounded prime-divisor supply

[All problems and zones](BROWSER.md)

<a id="node-6ffc14283611b4fc"></a>
## bounded_degree_order_witnesses_force_eventual_escape_from_every_finite_prime_set

Let m>0. If every prime divisor p of every prime-index layer C(mq) has some exact-order witness exponent k with 1≤k≤d and mq dividing p^k-1, then for every finite set S of primes there is a threshold Q₀ such that no p in S divides C(mq) whenever q is prime and q≥Q₀.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: No nontrivial-layer or Archimedean growth hypothesis is needed for this exclusion step. Conversely, exclusion alone does not show that any layer has a prime divisor, produce a large divisor, prove a carry discrepancy, or imply irrationality.

Open hypotheses: ["Instantiate BoundedDegreeOrderConsumer C m d for the layer family of interest; positivity of m is the theorem's explicit arithmetic side condition."]

- Lean declaration: [finitePrimeSupportEscape_of_orderConsumer](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L165)

- incoming **generated_by**: [Z73::order_realisability_and_nontrivial_layer_supply_form_the_complete_abstract_prime_ray_producer](BROWSER_Z73_1.md#node-06e1571a030f5984). The complete producer first applies finitePrimeSupportEscape_of_orderConsumer to the bounded-degree order hypothesis.
- incoming **complements**: [Z73::nontrivial_layers_plus_finite_support_escape_force_remote_large_prime_divisors](BROWSER_Z73_1.md#node-7f5a1760a06704f4). The first theorem produces the finite-support escape interface from order witnesses; the second consumes that interface together with nontrivial layer supply.

<a id="node-7f5a1760a06704f4"></a>
## nontrivial_layers_plus_finite_support_escape_force_remote_large_prime_divisors

If C has eventual nontrivial clean layers on the prime ray mq and those layers eventually escape every prescribed finite prime support, then for every size bound B and prime-index lower bound N₀ there are primes q≥N₀ and p>B such that p divides C(mq).

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: The theorem consumes, rather than proves, both layer supply and finite-support escape. It is existential and supplies no effective least q or p; the coprimality component of PrimeRayLayerSupply is stronger than what this proof uses. No target avoidance, carry kill, or irrationality follows.

Open hypotheses: ["Instantiate PrimeRayLayerSupply C m, supplying eventual nontriviality of C(mq).", "Instantiate FinitePrimeSupportEscape C m for the same layer family."]

- Lean declaration: [unboundedPrimeDivisorSupply_of_layerSupply_of_finitePrimeSupportEscape](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L215)

- incoming **generated_by**: [Z73::order_realisability_and_nontrivial_layer_supply_form_the_complete_abstract_prime_ray_producer](BROWSER_Z73_1.md#node-06e1571a030f5984). The complete producer then supplies the derived finite-support escape and the assumed layer supply to the generic unbounded-prime-divisor bridge.
- outgoing **complements**: [Z73::bounded_degree_order_witnesses_force_eventual_escape_from_every_finite_prime_set](BROWSER_Z73_1.md#node-6ffc14283611b4fc). The first theorem produces the finite-support escape interface from order witnesses; the second consumes that interface together with nontrivial layer supply.

<a id="node-06e1571a030f5984"></a>
## order_realisability_and_nontrivial_layer_supply_form_the_complete_abstract_prime_ray_producer

Let m>0. If C has eventual nontrivial clean layers on the prime ray mq and every prime divisor of C(mq) has an exact-order witness in some degree k≤d, then the prime divisors of those layers are unbounded even after imposing an arbitrary lower bound on the prime index q.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: For the concrete X-2 layer, Z35 records unconditional supply and degree-one order hypotheses. For arbitrary layers, polynomial/resultant order realisability and Archimedean nontriviality remain inputs. Even unbounded prime support supplies only arithmetic anchors, not cofinal certified kills or irrationality of the binary totient series.

Open hypotheses: ["Instantiate PrimeRayLayerSupply C m for the layer family of interest.", "Instantiate BoundedDegreeOrderConsumer C m d for a uniform finite degree d; positivity of m is explicit."]

- Lean declaration: [unboundedPrimeDivisorSupply_of_orderConsumer](../../ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L242)

- outgoing **generated_by**: [Z73::bounded_degree_order_witnesses_force_eventual_escape_from_every_finite_prime_set](BROWSER_Z73_1.md#node-6ffc14283611b4fc). The complete producer first applies finitePrimeSupportEscape_of_orderConsumer to the bounded-degree order hypothesis.
- outgoing **generated_by**: [Z73::nontrivial_layers_plus_finite_support_escape_force_remote_large_prime_divisors](BROWSER_Z73_1.md#node-7f5a1760a06704f4). The complete producer then supplies the derived finite-support escape and the assumed layer supply to the generic unbounded-prime-divisor bridge.

