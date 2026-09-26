import Erdos249257
import ErdosProblems
import ErdosProblems.EightPaperR21Audit
import ErdosProblems.EightPaperRecoveryAudit
import ErdosProblems.Erdos1041.PaperCorrespondenceAudit
import ErdosProblems.Erdos1041.PaperTrinomialCoverageAuditR20
import ErdosProblems.Erdos1049.PaperCorrespondenceAudit
import ErdosProblems.Erdos1049.PaperR20.RecoveredProofAudit
import ErdosProblems.Erdos243.PaperCompleteR20.CubicArithmeticAudit
import ErdosProblems.Erdos243.PaperCompleteR20.CubicRecoveryAudit
import ErdosProblems.Erdos243.PaperCorrespondenceAudit
import ErdosProblems.Erdos249.PaperCompleteR20.CyclotomicRecoveryAudit
import ErdosProblems.Erdos249.PaperCompleteR20.DenominatorRecoveryAudit
import ErdosProblems.Erdos249.PaperCompleteR20.FiniteCarryCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR20.FiniteCertificateBatch
import ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodelEndpoint
import ErdosProblems.Erdos249.PaperCompleteR20.GridArcRealInterface
import ErdosProblems.Erdos249.PaperCompleteR20.LcmGridCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR20.MobiusSquareReduction
import ErdosProblems.Erdos249.PaperCompleteR20.RadicalDecomposition
import ErdosProblems.Erdos249.PaperCompleteR20.RationalSpacingCorrespondence
import ErdosProblems.Erdos249.PaperCompleteR20.SignedDyadicClearing
import ErdosProblems.Erdos249.PaperCompleteR20.TailDepthCorrespondence
import ErdosProblems.Erdos249.PaperCorrespondenceAudit
import ErdosProblems.Erdos249.PaperCorrespondenceAuditAdditive
import ErdosProblems.Erdos249.PaperCorrespondenceAuditRecovery
import ErdosProblems.Erdos251.PaperCompleteR20.ExactDenominator
import ErdosProblems.Erdos251.PaperCompleteR20.FiniteSeparation
import ErdosProblems.Erdos251.PaperCompleteR20.LocalTargetInterval
import ErdosProblems.Erdos251.PaperCompleteR20.SparseConstructionAudit
import ErdosProblems.Erdos251.PaperCorrespondenceAudit
import ErdosProblems.Erdos257.PaperCompleteR20.AchievementGeometry
import ErdosProblems.Erdos257.PaperCompleteR20.CofinalCarryCollapse
import ErdosProblems.Erdos257.PaperCompleteR20.GeneralRepairCorrespondence
import ErdosProblems.Erdos257.PaperCompleteR20.MersenneConstantDecimal
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowReal
import ErdosProblems.Erdos257.PaperCompleteR20.TerminalSetCorrespondence
import ErdosProblems.Erdos257.PaperCorrespondenceAudit
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditive
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave2
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave3
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave4
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave5
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave6
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave7
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave8
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave9
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave10
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave11
import ErdosProblems.Erdos257.PaperCorrespondenceAuditAdditiveWave12
import ErdosProblems.Erdos269.PaperCompleteR20.UniformRankAudit
import ErdosProblems.Erdos269.PaperCorrespondenceAudit
import ErdosProblems.Erdos68.PaperCorrespondenceAudit
import ErdosProblems.Erdos68.PaperCorrespondenceAuditAdditive

/-!
# Kernel probe: can the coverage targets be imported together?

The argument-graph export reads the two default library roots. Two thirds of
the declarations the paper-to-Lean ledger cites live in modules only the
coverage build compiles. This probe imports the default roots and every
coverage target in one environment and counts the corpus theorems by lane.
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut total := 0
  let mut modules : NameSet := {}
  for (name, info) in env.constants.toList do
    if let .thmInfo _ := info then
      if let some i := env.getModuleIdxFor? name then
        let m := env.header.moduleNames[i.toNat]!
        if (`ErdosProblems).isPrefixOf m || (`Erdos249257).isPrefixOf m then
          total := total + 1
          modules := modules.insert m
  IO.println s!"combined import ok: {total} corpus theorems in {modules.size} modules"
