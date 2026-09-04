# Z07_2: Mersenne-Lambert ladder, gcd moments and Stern-Brocot geometry: where the #249 constant sits

[All problems and zones](BROWSER.md)

<a id="node-5f9952c1561d172c"></a>
## unique_dyadic_terminal_parity

Let s be a finite index set with an integer numerator u(i) and a natural dyadic exponent e(i) at each index. IF some m in s has odd u(m) and strictly largest exponent, THEN the cleared sum of u(i) * 2^{e(m) - e(i)} over s is odd, and in particular nonzero. The two hypotheses are free: nothing in the corpus exhibits a #249 moment family satisfying them.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

Scope: Classified conditional_implication rather than unconditional_object_theorem: the Lean statement is about arbitrary integer data (u, e) on an arbitrary finite index set and mentions no #249 object. It establishes nothing about the totient series, the primitive-conductor weight, or any Mersenne moment sequence until a family satisfying the unique-largest-odd-exponent hypothesis is exhibited, which the corpus never does. Read as a proof step for the 'signed-Hankel route', it is the conditional half of an argument whose antecedent is the entire difficulty.

Open hypotheses: ["existence of an index m whose dyadic exponent e(m) is strictly largest in the family and whose integer numerator u(m) is odd — for the intended signed Mobius / q = 1/2 Hankel moment family this is proved nowhere in the corpus; the hypothesis is supplied, never discharged", "no Lean declaration anywhere in the repository instantiates s, u, e on #249 moment data, so the implication is never fired"]

- Lean declaration: [scaled_dyadic_sum_odd](../../Erdos249257/SignedQMomentObstruction.lean#L78)
- Lean declaration: [scaled_dyadic_sum_ne_zero](../../Erdos249257/SignedQMomentObstruction.lean#L96)

- outgoing **depends_on_open**: [Z07::signed_hankel_scaffolding](BROWSER_Z07_1.md#node-7de71afe1ff5017d). the parity lemma is the intended non-vanishing certificate for the Hankel route, but no declaration anywhere instantiates its hypotheses on the actual #249 moment data.

<a id="node-3b70ff2cf178e294"></a>
## visible_point_count_totient

For every natural n, the number of pairs (a,b) with a + b = n, a > 0 and gcd(a,b) = 1 equals phi(n), uniformly and with no case split (n = 0 gives the empty filter, n = 1 gives exactly (1,0)).

Class: classical_formalised. Interpretation: authored_statement. Prior-art assessment: known_classical.

- Lean declaration: [card_antidiagonal_filter_pos_coprime](../../Erdos249257/GeometricCoprimality.lean#L56)

- outgoing **implies**: [Z07::coprime_pair_mass_bridge](BROWSER_Z07_1.md#node-0c4e3b1e6a2be76d). the finite antidiagonal count is the coefficient extracted by the antidiagonal regrouping.

