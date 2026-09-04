# Z62_1: Canonical adjacent-suffix slack and post-jump producer specialisation

[All problems and zones](BROWSER.md)

<a id="node-8937d50196796cb9"></a>
## canonical_adjacent_suffix_slack_is_the_minimum_two_sided_edge_margin

Let m=canonicalAdjacentSuffixDepth(t) and d=diagonalAdjacentSuffixResidue(t,0,m). Then canonicalAdjacentSuffixCentralSlack(t)=min(d-2^(m-5),(2^m-2^(m-5))-d). Nonnegativity is exactly the closed central band 2^(m-5)≤d≤2^m-2^(m-5), and the scalar is constant across equal periodLcm heights.

Class: representation_normalisation. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: The scalar definition proves no recurrence, monotonicity, equidistribution, or sign bias. Plateau invariance does not propagate slack across a strict jump.

- Lean declaration: [canonicalAdjacentSuffixCentralSlack](../../Erdos249257/DiagonalFreshLossBridge.lean#L2651)

- incoming **generated_by**: [Z62::post_jump_nonnegative_slack_is_an_open_cofinal_supply](BROWSER_Z62_1.md#node-64ac66d67d9d783d). The supply is exactly a cofinal nonnegativity condition on this scalar immediately after strict LCM jumps.
- incoming **generated_by**: [Z62::power_two_endpoints_form_an_open_post_jump_slack_specialisation](BROWSER_Z62_1.md#node-30a92db43ce531b3). The power-two producer restricts the same scalar sign condition to endpoints 2^a.

<a id="node-64ac66d67d9d783d"></a>
## post_jump_nonnegative_slack_is_an_open_cofinal_supply

CanonicalAdjacentSuffixPostJumpSlackSupply asks that beyond every threshold there be a strict LCM jump periodLcm(t)<periodLcm(t+1) whose new endpoint has 0≤canonicalAdjacentSuffixCentralSlack(t+1).

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Strict LCM jumps are cofinal, but the slack sign at those jumps is unproved. The predicate evaluates at t+1, not t; finite censuses cannot discharge the cofinal quantifier.

Open hypotheses: ["CanonicalAdjacentSuffixPostJumpSlackSupply"]

- Lean declaration: [CanonicalAdjacentSuffixPostJumpSlackSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2686)

- outgoing **generated_by**: [Z62::canonical_adjacent_suffix_slack_is_the_minimum_two_sided_edge_margin](BROWSER_Z62_1.md#node-8937d50196796cb9). The supply is exactly a cofinal nonnegativity condition on this scalar immediately after strict LCM jumps.
- incoming **implies**: [Z62::power_two_endpoints_form_an_open_post_jump_slack_specialisation](BROWSER_Z62_1.md#node-30a92db43ce531b3). canonicalAdjacentSuffixPostJumpSlackSupply_of_powerTwo uses periodLcm(2^a-1)<periodLcm(2^a) and reindexes each power-of-two witness as a post-jump witness.

<a id="node-30a92db43ce531b3"></a>
## power_two_endpoints_form_an_open_post_jump_slack_specialisation

CanonicalAdjacentSuffixPowerTwoPostJumpSlackSupply asks that for arbitrarily large exponents a≥2, 0≤canonicalAdjacentSuffixCentralSlack(2^a). The corresponding pre-jump index is 2^a-1, while slack is evaluated at the new endpoint 2^a.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Scope: Power-two indices remove the position search but do not prove nonnegative slack. Only the forward implication to general post-jump supply is proved; no converse or necessity for irrationality is available.

Open hypotheses: ["CanonicalAdjacentSuffixPowerTwoPostJumpSlackSupply"]

- Lean declaration: [CanonicalAdjacentSuffixPowerTwoPostJumpSlackSupply](../../Erdos249257/DiagonalFreshLossBridge.lean#L2693)

- outgoing **generated_by**: [Z62::canonical_adjacent_suffix_slack_is_the_minimum_two_sided_edge_margin](BROWSER_Z62_1.md#node-8937d50196796cb9). The power-two producer restricts the same scalar sign condition to endpoints 2^a.
- outgoing **implies**: [Z62::post_jump_nonnegative_slack_is_an_open_cofinal_supply](BROWSER_Z62_1.md#node-64ac66d67d9d783d). canonicalAdjacentSuffixPostJumpSlackSupply_of_powerTwo uses periodLcm(2^a-1)<periodLcm(2^a) and reindexes each power-of-two witness as a post-jump witness.

