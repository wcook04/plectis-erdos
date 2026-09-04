# Z12_3: Mersenne achievement set: greedy geometry, fat-Cantor structure, and the 1/2 membership question

[All problems and zones](BROWSER.md)

<a id="node-acd42d13a4214f3a"></a>
## terminal_scaled_vanishing_yields_half

If there is a sequence of normalized finite half words with depths tending to infinity whose absolute terminal carries divided by 2^depth tend to zero, then 1/2 belongs to the Mersenne achievement set and an infinite set with Mersenne sum 1/2 exists. The square-root-strip cofinal supply maps into this weaker interface, so it is a genuine weakening rather than a parallel restatement; but no such sequence is constructed.

Class: conditional_implication. Interpretation: authored_statement. Prior-art assessment: not_assessed.

Open hypotheses: ["S : HalfTerminalOnlyScaledVanishingSequence, i.e. depths tending to infinity with |integerHalfCarry (wordSupport (word n)) (depth n - 1)| / 2^(depth n) tending to zero"]

- Lean declaration: [half_mem_mersenneAchievementSet_of_terminalScaledVanishing](../../Erdos249257/TerminalOnlyScaledVanishing.lean#L165)
- Lean declaration: [exists_infinite_support_half_of_terminalScaledVanishing](../../Erdos249257/TerminalOnlyScaledVanishing.lean#L221)
- Lean declaration: [half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip_via_scaled](../../Erdos249257/TerminalOnlyScaledVanishing.lean#L236)

- outgoing **generalises**: [Z12::terminal_only_cofinal_yields_half](BROWSER_Z12_2.md#node-f8810011b82ac702). a named constructor maps every cofinal square-root-strip family into the scaled-vanishing interface, so the latter is strictly weaker
- outgoing **depends_on_open**: [Z16::certified_terminal_witnesses_51_52](BROWSER_Z16_1.md#node-4412dd0ecc306fff). the deepest terminal witnesses produced anywhere sit at depths 51 and 52; the antecedent needs a sequence of depths tending to infinity, which two depths cannot supply.

<a id="node-df685f4f83c123aa"></a>
## three_fourths_excluded

The value 3/4 is not in the Mersenne achievement set, certified by a level-one death certificate with zero lookahead.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [three_fourths_certifiedGreedyMersenneDeath](../../Erdos249257/GreedyAchievementSet.lean#L1778)
- Lean declaration: [three_fourths_not_mem_mersenneAchievementSet](../../Erdos249257/GreedyAchievementSet.lean#L1784)

- incoming **implies**: [Z12::certified_greedy_death_soundness](BROWSER_Z12_1.md#node-0c46f6d52d1ee5b9). 3/4 is excluded by a level-one instance of the certificate

<a id="node-d88c983df9c61dfd"></a>
## two_thirds_band_arithmetic_exclusions

An integral reciprocal never lies in the two-thirds band, because the pinning 2q < 3R < 2q + 2/3 leaves no room for a multiple of three. For a residual p/(2D) in lowest terms with p, D and q all odd, an unsafe single-skip run forces p >= 7: the band defect 6D - 2pq is divisible by four, and that congruence alone removes p in {1,3,5}.

Class: unconditional_object_theorem. Interpretation: authored_statement. Prior-art assessment: not_assessed.

- Lean declaration: [not_twoThirdsBand_of_int](../../Erdos249257/HalfGreedyTwoThirdsBand.lean#L185)
- Lean declaration: [seven_le_of_intBand_odd](../../Erdos249257/HalfGreedyTwoThirdsBand.lean#L231)

- incoming **implies**: [Z12::post_take_unsafe_band_characterisation](BROWSER_Z12_2.md#node-72c6fa3ca8098c3b). the exclusions are congruence consequences of the single-skip band pinning

<a id="node-0794cec8c83c05de"></a>
## two_thirds_escape_fixtures

Two exact rational fixtures at rank three: r = 37/280 lies in the relaxed escape window with sliver coordinate 2/5 and survives a further undoubled step, while r = 67/512 has sharp sliver coordinate 21/32 yet already exceeds the Mersenne tail at rank three. Together they show that the relaxed and doubled two-thirds tests are not equivalent to actual survival.

Class: finite_instance. Interpretation: authored_statement. Prior-art assessment: routine_corollary_or_specialisation.

- Lean declaration: [undoubled_twoThirds_relaxed_escape_fixture](../../Erdos249257/GreedyAchievementSet.lean#L2237)
- Lean declaration: [doubled_twoThirds_below_but_above_tail_fixture](../../Erdos249257/GreedyAchievementSet.lean#L2248)

- incoming **implies**: [Z12::mersenne_sliver_coordinate_dynamics](BROWSER_Z12_2.md#node-541f3045e1e0e512). the fixtures are evaluations of the sliver coordinate step map
- outgoing **finite_instance_of**: [Z12::post_take_unsafe_band_characterisation](BROWSER_Z12_2.md#node-72c6fa3ca8098c3b). the fixtures show the relaxed and doubled band tests are not equivalent to actual greedy survival

