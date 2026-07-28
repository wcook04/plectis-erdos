/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.DemandLedger.Hyp
import Erdos249257
import ErdosProblems.Erdos249.TotientStrictPrimeEscape

/-!
# The demand ledger

Machine-extracted from the semantic-corpus snapshot used to build this file.
Each recorded antecedent is the type of a named theorem hypothesis binder.
Walking that snapshot with `forallTelescope` and retaining closed `Prop` binders
produced the entries below; current semantic-corpus totals may be larger.

`docs/semantic/frontier.json` currently records 52 open antecedents in prose.
This checked-in ledger exposes 101 named closed `Prop`s, of which 23 are labelled
substantial statements and the rest are side conditions. Nothing here is transcribed: each entry is `hypOf%`
applied to the source theorem, so it is the kernel's own `Expr` or it fails to
elaborate.

Entries are ordered by statement size, substantial ones first.
-/

namespace DemandLedger

/-- **G101** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_lcm_cone_nonintegrality_supply`.
Frontier: OA249-lcm-cone-kill-supply, OA249-lcm-jump-kill-supply. Used by 2 conditional theorem(s). -/
def G101 : Prop := hypOf% Erdos249257.irrational_totient_series_of_lcm_cone_nonintegrality_supply hsupply

/-- **G093** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply`.
Frontier: OA249-lcm-cone-kill-supply, OA249-lcm-jump-kill-supply. Used by 2 conditional theorem(s). -/
def G093 : Prop := hypOf% Erdos249257.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply hsupply

/-- **G095** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonflat_supply`.
Frontier: OA249-cone-nonflat-menu-supply. Used by 2 conditional theorem(s). -/
def G095 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonflat_supply hsupply

/-- **G096** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_lcm_jump_window_kill_supply`.
Frontier: OA249-lcm-cone-kill-supply, OA249-lcm-jump-kill-supply. Used by 2 conditional theorem(s). -/
def G096 : Prop := hypOf% Erdos249257.irrational_totient_series_of_lcm_jump_window_kill_supply hsupply

/-- **G083** (#257, substantial) — antecedent `hsafe` of
`Erdos249257.half_mem_mersenneAchievementSet_of_actualBlockSafe`.
Frontier: OA257-greedy-block-safety-at-every-skip. Used by 1 conditional theorem(s). -/
def G083 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_actualBlockSafe hsafe

/-- **G100** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_lcm_cone_window_kill_supply`.
Frontier: OA249-lcm-cone-kill-supply, OA249-lcm-jump-kill-supply. Used by 2 conditional theorem(s). -/
def G100 : Prop := hypOf% Erdos249257.irrational_totient_series_of_lcm_cone_window_kill_supply hsupply

/-- **G099** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_qray_rank2_supply`.
Frontier: OA249-lcm-cone-kill-supply, OA249-lcm-jump-kill-supply, OA249-rank2-qray-supply. Used by 2 conditional theorem(s). -/
def G099 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_qray_rank2_supply hsupply

/-- **G090** (#249, substantial) — antecedent `hcert` of
`Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_low_carry_certificates`.
Frontier: OA249-block-certificate-supply, OA249-carry-aware-supply, OA249-low-carry-supply. Used by 1 conditional theorem(s). -/
def G090 : Prop := hypOf% Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_low_carry_certificates hcert

/-- **G089** (#249, substantial) — antecedent `hcert` of
`Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_carry_certificates`.
Frontier: OA249-block-certificate-supply, OA249-carry-aware-supply, OA249-low-carry-supply. Used by 1 conditional theorem(s). -/
def G089 : Prop := hypOf% Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_carry_certificates hcert

/-- **G076** (#257, substantial) — antecedent `hterminal` of
`Erdos249257.half_mem_mersenneAchievementSet_of_unboundedTerminalFalse`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G076 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_unboundedTerminalFalse hterminal

/-- **G097** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_certificate_supply`.
Frontier: OA249-pointwise-kill-supply, OA249-ray-and-multiple-kill-supply, OA249-lcm-diagonal-kill-supply. Used by 2 conditional theorem(s). -/
def G097 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_certificate_supply hsupply

/-- **G088** (#249, substantial) — antecedent `hcert` of
`Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_block_certificates`.
Frontier: OA249-block-certificate-supply, OA249-carry-aware-supply, OA249-low-carry-supply. Used by 1 conditional theorem(s). -/
def G088 : Prop := hypOf% Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_block_certificates hcert

/-- **G094** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_survivor_supply`.
Frontier: OA249-pointwise-kill-supply, OA249-ray-and-multiple-kill-supply, OA249-lcm-diagonal-kill-supply. Used by 2 conditional theorem(s). -/
def G094 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_survivor_supply hsupply

/-- **G085** (#257, substantial) — antecedent `hskip` of
`Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap`.
Frontier: OA257-channel-cap-at-skips. Used by 1 conditional theorem(s). -/
def G085 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap hskip

/-- **G084** (#257, substantial) — antecedent `hskip` of
`Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap`.
Frontier: OA257-channel-cap-at-skips. Used by 1 conditional theorem(s). -/
def G084 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap hskip

/-- **G103** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_lcm_window_kill_supply`.
Frontier: OA249-pointwise-kill-supply, OA249-ray-and-multiple-kill-supply, OA249-lcm-diagonal-kill-supply. Used by 2 conditional theorem(s). -/
def G103 : Prop := hypOf% Erdos249257.irrational_totient_series_of_lcm_window_kill_supply hsupply

/-- **G102** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_lcm_period_kill_supply`.
Frontier: OA249-pointwise-kill-supply, OA249-ray-and-multiple-kill-supply, OA249-lcm-diagonal-kill-supply. Used by 2 conditional theorem(s). -/
def G102 : Prop := hypOf% Erdos249257.irrational_totient_series_of_lcm_period_kill_supply hsupply

/-- **G073** (#257, substantial) — antecedent `htempered` of
`Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_tempered`.
Frontier: OA257-greedy-carry-upper-bound. Used by 1 conditional theorem(s). -/
def G073 : Prop := hypOf% Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_tempered htempered

/-- **G098** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.PrimeJumpWindow.irrational_totient_series_of_primeJumpSharpKill_supply`.
Frontier: OA249-prime-jump-supply. Used by 1 conditional theorem(s). -/
def G098 : Prop := hypOf% Erdos249257.PrimeJumpWindow.irrational_totient_series_of_primeJumpSharpKill_supply hsupply

/-- **G075** (#257, substantial) — antecedent `hbound` of
`Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G075 : Prop := hypOf% Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound hbound

/-- **G082** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_multiple_window_kill_supply`.
Frontier: OA249-pointwise-kill-supply, OA249-ray-and-multiple-kill-supply, OA249-lcm-diagonal-kill-supply. Used by 2 conditional theorem(s). -/
def G082 : Prop := hypOf% Erdos249257.irrational_totient_series_of_multiple_window_kill_supply hsupply

/-- **G091** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.irrational_tsum_totient_div_pow_two_of_gap_certificate_supply`.
Frontier: OA249-gap-certificate-supply. Used by 1 conditional theorem(s). -/
def G091 : Prop := hypOf% Erdos249257.irrational_tsum_totient_div_pow_two_of_gap_certificate_supply hsupply

/-- **G081** (#249, substantial) — antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_multiple_period_kill_supply`.
Frontier: OA249-pointwise-kill-supply, OA249-ray-and-multiple-kill-supply, OA249-lcm-diagonal-kill-supply. Used by 2 conditional theorem(s). -/
def G081 : Prop := hypOf% Erdos249257.irrational_totient_series_of_multiple_period_kill_supply hsupply

/-- **G092** (#249, small) — antecedent `hcert` of
`Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_low_carry_full_block_certificates`.
Frontier: OA249-block-certificate-supply, OA249-carry-aware-supply, OA249-low-carry-supply. Used by 1 conditional theorem(s). -/
def G092 : Prop := hypOf% Erdos249257.irrational_tsum_totient_div_pow_two_of_totient_low_carry_full_block_certificates hcert

/-- **G086** (#257, small) — antecedent `hseparate` of
`Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparation`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G086 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparation hseparate

/-- **G080** (#249, small) — antecedent `hsupply` of
`Erdos249257.irrational_totient_series_of_period_kill_supply`.
Frontier: OA249-pointwise-kill-supply, OA249-ray-and-multiple-kill-supply, OA249-lcm-diagonal-kill-supply. Used by 2 conditional theorem(s). -/
def G080 : Prop := hypOf% Erdos249257.irrational_totient_series_of_period_kill_supply hsupply

/-- **G078** (#257, small) — antecedent `hstages` of
`Erdos249257.SuffixCylinderTerminalOnlyBridge.exists_infinite_support_half_of_cofinalCylinderStages`.
Frontier: OA257-cofinal-cylinder-stages. Used by 2 conditional theorem(s). -/
def G078 : Prop := hypOf% Erdos249257.SuffixCylinderTerminalOnlyBridge.exists_infinite_support_half_of_cofinalCylinderStages hstages

/-- **G079** (#257, small) — antecedent `hodd` of
`Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_evenSeamSupply_escape`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G079 : Prop := hypOf% Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_evenSeamSupply_escape hodd

/-- **G017** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.irrational_totientSeries_of_threeScaleAffineEscapeSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G017 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.irrational_totientSeries_of_threeScaleAffineEscapeSupply hsupply

/-- **G077** (#257, small) — antecedent `hfull` of
`Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_fullStrip`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G077 : Prop := hypOf% Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_fullStrip hfull

/-- **G008** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateStrongBandSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G008 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateStrongBandSupply hsupply

/-- **G010** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPowerTwoPostJumpSlackSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G010 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPowerTwoPostJumpSlackSupply hsupply

/-- **G007** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateMarginSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G007 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateMarginSupply hsupply

/-- **G006** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateExactSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G006 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPenultimateExactSupply hsupply

/-- **G013** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_actualPenultimateEnvelopeMarginSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G013 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_actualPenultimateEnvelopeMarginSupply hsupply

/-- **G014** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_actualPenultimateSignedMarginSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G014 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_actualPenultimateSignedMarginSupply hsupply

/-- **G026** (#257, small) — antecedent `hsupply` of
`Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_cofinalSelectedWindowOrProtectedSeam`.
Frontier: no frontier record. Used by 2 conditional theorem(s). -/
def G026 : Prop := hypOf% Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_cofinalSelectedWindowOrProtectedSeam hsupply

/-- **G009** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPostJumpSlackSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G009 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixPostJumpSlackSupply hsupply

/-- **G025** (#257, small) — antecedent `hsupply` of
`Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_cofinalProtectedEvenSeamRealization`.
Frontier: no frontier record. Used by 2 conditional theorem(s). -/
def G025 : Prop := hypOf% Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_cofinalProtectedEvenSeamRealization hsupply

/-- **G004** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixJumpCentralSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G004 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixJumpCentralSupply hsupply

/-- **G005** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixJumpSlackSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G005 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixJumpSlackSupply hsupply

/-- **G003** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G003 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_canonicalAdjacentSuffixCentralSupply hsupply

/-- **G018** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalPincerDecomposition.irrational_totientSeries_of_fresh_prime_channel_avoidance_supply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G018 : Prop := hypOf% Erdos249257.DiagonalPincerDecomposition.irrational_totientSeries_of_fresh_prime_channel_avoidance_supply hsupply

/-- **G062** (#249, small) — antecedent `hpair` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotPairwiseReconstructionEnergy`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G062 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotPairwiseReconstructionEnergy hpair

/-- **G016** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_powerTwoOddGuardThreeRankBandSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G016 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_powerTwoOddGuardThreeRankBandSupply hsupply

/-- **G020** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalPincerDecomposition.irrational_totientSeries_of_upper_half_channel_avoidance_supply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G020 : Prop := hypOf% Erdos249257.DiagonalPincerDecomposition.irrational_totientSeries_of_upper_half_channel_avoidance_supply hsupply

/-- **G015** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_powerTwoOddGuardHalfWordBandSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G015 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_powerTwoOddGuardHalfWordBandSupply hsupply

/-- **G058** (#249, small) — antecedent `htwo` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_naturalPivotTwoModeCancellation`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G058 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_naturalPivotTwoModeCancellation htwo

/-- **G012** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_diagonalFreshLossProjectionSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G012 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_diagonalFreshLossProjectionSupply hsupply

/-- **G054** (#249, small) — antecedent `hsep` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_adjacentMiddleThirdSeparation`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G054 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_adjacentMiddleThirdSeparation hsep

/-- **G011** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G011 : Prop := hypOf% Erdos249257.DiagonalFreshLossBridge.irrational_totientSeries_of_diagonalAdjacentSuffixGapSupply hsupply

/-- **G022** (#257, small) — antecedent `hreturn` of
`Erdos249257.HalfCarryReachability.greedy_integerHalfCarry_scaled_tendsto_zero_of_cofinalStripReturn`.
Frontier: no frontier record. Used by 3 conditional theorem(s). -/
def G022 : Prop := hypOf% Erdos249257.HalfCarryReachability.greedy_integerHalfCarry_scaled_tendsto_zero_of_cofinalStripReturn hreturn

/-- **G027** (#257, small) — antecedent `hcofinal` of
`Erdos249257.HalfCarryReachability.half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip_via_scaled`.
Frontier: no frontier record. Used by 3 conditional theorem(s). -/
def G027 : Prop := hypOf% Erdos249257.HalfCarryReachability.half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip_via_scaled hcofinal

/-- **G053** (#249, small) — antecedent `hsupply` of
`Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_phaseCertificateSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G053 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_phaseCertificateSupply hsupply

/-- **G021** (#249, small) — antecedent `hsupply` of
`Erdos249257.ExponentOnlyTransport.irrational_totient_series_of_exponentOnlyThreeTransportSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G021 : Prop := hypOf% Erdos249257.ExponentOnlyTransport.irrational_totient_series_of_exponentOnlyThreeTransportSupply hsupply

/-- **G023** (#257, small) — antecedent `hcanonical` of
`Erdos249257.HalfCarryReachability.fullStripAt_even_of_evenSeamSupply_escape`.
Frontier: no frontier record. Used by 4 conditional theorem(s). -/
def G023 : Prop := hypOf% Erdos249257.HalfCarryReachability.fullStripAt_even_of_evenSeamSupply_escape hcanonical

/-- **G063** (#249, small) — antecedent `hvariance` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotReconstructionVariance`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G063 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotReconstructionVariance hvariance

/-- **G069** (#249, small) — antecedent `hsupply` of
`Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_roughnessBoundaryLatticeSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G069 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_roughnessBoundaryLatticeSupply hsupply

/-- **G019** (#249, small) — antecedent `hsupply` of
`Erdos249257.DiagonalPincerDecomposition.irrational_totientSeries_of_full_target_avoidance_supply`.
Frontier: OA249-lcm-diagonal-kill-supply. Used by 1 conditional theorem(s). -/
def G019 : Prop := hypOf% Erdos249257.DiagonalPincerDecomposition.irrational_totientSeries_of_full_target_avoidance_supply hsupply

/-- **G064** (#249, small) — antecedent `hmix` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotResidualDecorrelation`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G064 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotResidualDecorrelation hmix

/-- **G066** (#249, small) — antecedent `hpair` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotWindowPairwiseEnergy`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G066 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotWindowPairwiseEnergy hpair

/-- **G067** (#249, small) — antecedent `hsep` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotWindowSeparatedPairs`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G067 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotWindowSeparatedPairs hsep

/-- **G070** (#249, small) — antecedent `hsupply` of
`Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureAnyDepthSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G070 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureAnyDepthSupply hsupply

/-- **G024** (#257, small) — antecedent `hcofinal` of
`Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_cofinalAdmissibility`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G024 : Prop := hypOf% Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_cofinalAdmissibility hcofinal

/-- **G060** (#249, small) — antecedent `hgap` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_naturalPrimeTailOrbitGap`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G060 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_naturalPrimeTailOrbitGap hgap

/-- **G104** (#257, small) — antecedent `hbase` of
`Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_evenSeamSupply_escape`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G104 : Prop := hypOf% Erdos249257.HalfCarryReachability.exists_infinite_support_half_of_evenSeamSupply_escape hbase

/-- **G055** (#249, small) — antecedent `hsep` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_adjacentPhaseSeparation`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G055 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_adjacentPhaseSeparation hsep

/-- **G057** (#249, small) — antecedent `hpoint` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_naturalPivotPointEscape`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G057 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_naturalPivotPointEscape hpoint

/-- **G061** (#249, small) — antecedent `hmix` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotAntiReconstruction`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G061 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotAntiReconstruction hmix

/-- **G087** (#257, small) — antecedent `hseparate` of
`Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G087 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven hseparate

/-- **G042** (#249, small) — antecedent `hsupply` of
`Erdos249257.JointExponentTransport.irrational_totient_series_of_anchoredJoint35ConeSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G042 : Prop := hypOf% Erdos249257.JointExponentTransport.irrational_totient_series_of_anchoredJoint35ConeSupply hsupply

/-- **G059** (#249, small) — antecedent `hgap` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_naturalPivotWindowGap`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G059 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_naturalPivotWindowGap hgap

/-- **G056** (#249, side condition) — antecedent `hgap` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_first_harmonic_norm_gap`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G056 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_first_harmonic_norm_gap hgap

/-- **G068** (#249, side condition) — antecedent `hsep` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_windowSeparatedPairs`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G068 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_windowSeparatedPairs hsep

/-- **G065** (#249, side condition) — antecedent `hsep` of
`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotSeparatedPairs`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G065 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_pivotSeparatedPairs hsep

/-- **G028** (#257, side condition) — antecedent `hescape` of
`Erdos249257.HalfCarryReachability.fullStripAt_even_of_evenSeamSupply_escape`.
Frontier: no frontier record. Used by 2 conditional theorem(s). -/
def G028 : Prop := hypOf% Erdos249257.HalfCarryReachability.fullStripAt_even_of_evenSeamSupply_escape hescape

/-- **G039** (#257, side condition) — antecedent `hsupply` of
`Erdos249257.half_mem_mersenneAchievementSet_of_unsafeSkipElevenGcdOvershootSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G039 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_unsafeSkipElevenGcdOvershootSupply hsupply

/-- **G041** (#257, side condition) — antecedent `hsupply` of
`Erdos249257.half_mem_mersenneAchievementSet_of_unsafeSkipPrimitiveOvershootSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G041 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_unsafeSkipPrimitiveOvershootSupply hsupply

/-- **G071** (#249, side condition) — antecedent `hsupply` of
`Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G071 : Prop := hypOf% Erdos249257.TotientTailPeriodKiller.irrational_totientSeries_of_sharpCurvatureSupply hsupply

/-- **G072** (#249, side condition) — antecedent `hgap` of
`ErdosProblems.Erdos249.naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap`.
Frontier: no frontier record. Used by 2 conditional theorem(s). -/
def G072 : Prop := hypOf% ErdosProblems.Erdos249.naturalPivotPointEscape_of_naturalPrimeTailOrbitStrictGap hgap

/-- **G051** (#257, side condition) — antecedent `hmiddleEscape` of
`Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G051 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree hmiddleEscape

/-- **G038** (#257, side condition) — antecedent `hsupply` of
`Erdos249257.half_mem_mersenneAchievementSet_of_unsafeSkipActualRawMarginSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G038 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_unsafeSkipActualRawMarginSupply hsupply

/-- **G044** (#249, side condition) — antecedent `hsupply` of
`Erdos249257.primitiveReducedDenominatorUnitGapSupply_prime_power_projection`.
Frontier: OA249-unit-gap-supply. Used by 1 conditional theorem(s). -/
def G044 : Prop := hypOf% Erdos249257.primitiveReducedDenominatorUnitGapSupply_prime_power_projection hsupply

/-- **G029** (#257, side condition) — antecedent `hproducer` of
`Erdos249257.half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G029 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer hproducer

/-- **G031** (#257, side condition) — antecedent `hsupply` of
`Erdos249257.half_mem_mersenneAchievementSet_of_skippedActualRawMarginSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G031 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_skippedActualRawMarginSupply hsupply

/-- **G037** (#257, side condition) — antecedent `hthree` of
`Erdos249257.half_mem_mersenneAchievementSet_of_threeDepthTakeRunExcessBound`.
Frontier: no frontier record. Used by 2 conditional theorem(s). -/
def G037 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_threeDepthTakeRunExcessBound hthree

/-- **G040** (#257, side condition) — antecedent `hsupply` of
`Erdos249257.half_mem_mersenneAchievementSet_of_unsafeSkipGcdOvershootSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G040 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_unsafeSkipGcdOvershootSupply hsupply

/-- **G033** (#257, side condition) — antecedent `hsign` of
`Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G033 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative hsign

/-- **G034** (#257, side condition) — antecedent `hsupply` of
`Erdos249257.half_mem_mersenneAchievementSet_of_skippedRawBlockMarginSupply`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G034 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_skippedRawBlockMarginSupply hsupply

/-- **G035** (#257, side condition) — antecedent `hsafe` of
`Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamAlignmentZero`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G035 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamAlignmentZero hsafe

/-- **G030** (#257, side condition) — antecedent `hlong` of
`Erdos249257.halfGreedySkippedExcessBound_of_longTakeRun`.
Frontier: no frontier record. Used by 2 conditional theorem(s). -/
def G030 : Prop := hypOf% Erdos249257.halfGreedySkippedExcessBound_of_longTakeRun hlong

/-- **G052** (#257, side condition) — antecedent `hband` of
`Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G052 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape hband

/-- **G032** (#257, side condition) — antecedent `hbound` of
`Erdos249257.half_mem_mersenneAchievementSet_of_skipped_excessBound`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G032 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_skipped_excessBound hbound

/-- **G047** (#257, side condition) — antecedent `hcard` of
`Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerCardEscape`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G047 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerCardEscape hcard

/-- **G049** (#257, side condition) — antecedent `hsqrt` of
`Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerSqrtEscape`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G049 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerSqrtEscape hsqrt

/-- **G050** (#257, side condition) — antecedent `hmiddleEscape` of
`Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerTailEscape`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G050 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerTailEscape hmiddleEscape

/-- **G036** (#257, side condition) — antecedent `hescape` of
`Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape`.
Frontier: no frontier record. Used by 2 conditional theorem(s). -/
def G036 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape hescape

/-- **G046** (#257, side condition) — antecedent `hgap` of
`Erdos249257.tendsto_seamGreedyFiniteValue_half`.
Frontier: no frontier record. Used by 2 conditional theorem(s). -/
def G046 : Prop := hypOf% Erdos249257.tendsto_seamGreedyFiniteValue_half hgap

/-- **G048** (#257, side condition) — antecedent `hrow` of
`Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerRowEscape`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G048 : Prop := hypOf% Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerRowEscape hrow

/-- **G043** (#257, side condition) — antecedent `hstep` of
`Erdos249257.largestSkipLateAt_of_stepSocket`.
Frontier: no frontier record. Used by 3 conditional theorem(s). -/
def G043 : Prop := hypOf% Erdos249257.largestSkipLateAt_of_stepSocket hstep

/-- **G045** (#257, side condition) — antecedent `heventual` of
`Erdos249257.exists_last_false_terminal_of_eventuallyRight`.
Frontier: no frontier record. Used by 1 conditional theorem(s). -/
def G045 : Prop := hypOf% Erdos249257.exists_last_false_terminal_of_eventuallyRight heventual

end DemandLedger
