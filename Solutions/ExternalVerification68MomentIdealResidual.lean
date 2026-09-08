import ErdosProblems.Erdos68.PaperCompleteMomentIdeal
import ErdosProblems.Erdos68.PaperCompleteResidualIdentity

namespace Erdos249257.ExternalVerification68MomentIdealResidual

open Finsupp
open scoped BigOperators
noncomputable section

abbrev channelWeight := ErdosProblems.Erdos68.channelWeight
abbrev channelNumerator := ErdosProblems.Erdos68.channelNumerator
abbrev factorialMoment := ErdosProblems.Erdos68.factorialMoment
abbrev channelLCM := ErdosProblems.Erdos68.channelLCM
abbrev adjacentDifference := ErdosProblems.Erdos68.adjacentDifference
abbrev isolatedChannelUnit := ErdosProblems.Erdos68.isolatedChannelUnit
abbrev channelBasisColumn := ErdosProblems.Erdos68.PaperComplete.channelBasisColumn
abbrev channelSynthesis := ErdosProblems.Erdos68.PaperComplete.channelSynthesis
abbrev kernelCoordinates := ErdosProblems.Erdos68.PaperComplete.kernelCoordinates
abbrev canonicalKernel := ErdosProblems.Erdos68.PaperComplete.canonicalKernel
abbrev kernelOne := ErdosProblems.Erdos68.PaperComplete.kernelOne
abbrev channelScalar := ErdosProblems.Erdos68.PaperComplete.channelScalar
abbrev finiteScalarGcd := ErdosProblems.Erdos68.PaperComplete.finiteScalarGcd
abbrev minimumMoment := ErdosProblems.Erdos68.PaperComplete.minimumMoment
abbrev Admissible := ErdosProblems.Erdos68.PaperComplete.Admissible
abbrev LowChannels := ErdosProblems.Erdos68.PaperComplete.LowChannels
abbrev AttainsMoment := ErdosProblems.Erdos68.PaperComplete.AttainsMoment
abbrev PrimitiveVector := ErdosProblems.Erdos68.PaperComplete.PrimitiveVector
abbrev TailCoordinates := ErdosProblems.Erdos68.PaperComplete.TailCoordinates
abbrev fullResidualTerm := ErdosProblems.Erdos68.PaperComplete.fullResidualTerm
abbrev fullResidual := ErdosProblems.Erdos68.PaperComplete.fullResidual
abbrev integerEvaluation := ErdosProblems.Erdos68.PaperComplete.integerEvaluation
abbrev coordinateMass := ErdosProblems.Erdos68.PaperComplete.coordinateMass
abbrev factorialGapTailTerm := _root_.Erdos68.factorialGapTailTerm
abbrev factorialGapTail := _root_.Erdos68.factorialGapTail
abbrev factorialGapSeries := _root_.Erdos68.factorialGapSeries
abbrev gapPrefixReal := ErdosProblems.Erdos68.PaperComplete.gapPrefixReal

theorem exact_moment_ideal_with_primitive_attainment {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p ∧
    (∀ m : ℤ, AttainsMoment D m ↔ minimumMoment D p ∣ m) ∧
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ PrimitiveVector f :=
  ErdosProblems.Erdos68.PaperComplete.exact_moment_ideal_with_primitive_attainment
    hD hp hDp hpD

theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ) :=
  ErdosProblems.Erdos68.PaperComplete.residual_transparency hD t hz

end
end Erdos249257.ExternalVerification68MomentIdealResidual
