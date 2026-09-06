-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
--
-- Problem-centric root for the Erdős Problems library.
--
-- `Erdos249257` holds the shared machinery: the certificate kernel, the greedy
-- achievement set, the Mersenne–Lambert ladder, and the carry systems both
-- problems are built on. This library holds the work that is stated per
-- problem and reads more naturally under the problem's own name.
--
-- Both Erdős Problem 249 (irrationality of ∑ φ(n)/2ⁿ) and Erdős Problem 257
-- (irrationality of ∑_{n∈A} 1/(2ⁿ−1) for every infinite A) are OPEN. Nothing
-- imported here decides either of them.
-- Keep the reviewed finite `t ≤ 82` certificate band inside the supported
-- root closure, so a clean root build re-elaborates its proof authority.

import ErdosProblems.AxiomAudit
import ErdosProblems.DemandLedger
import ErdosProblems.Erdos249.RankOneSharpFloor
import ErdosProblems.Erdos269.RestrictedFloorSum
import ErdosProblems.Root
import ErdosProblems.Skip.LadderT67
import ErdosProblems.Erdos68.GapScalarNormalForm
import ErdosProblems.Erdos68.PrimeThresholdParity
import ErdosProblems.Erdos68.AdjacentUnitCarryWindow
import ErdosProblems.Erdos243.RepairEntropy


-- Corpus union 2026-09-06: modules brought across from the private formal tree.
import ErdosProblems.Erdos1041.AbelControlPolygon
import ErdosProblems.Erdos1041.AggregateN3PshUniformity
import ErdosProblems.Erdos1041.CentroidHubCounterexample
import ErdosProblems.Erdos1041.DiskFamilyCriticalValueSeparation
import ErdosProblems.Erdos1041.DiskFamilyCriticalValueSeparationAxiomAudit
import ErdosProblems.Erdos1041.FreePointHilbertCertificate
import ErdosProblems.Erdos1041.MechanismSeparationScalarKernel
import ErdosProblems.Erdos1041.QuarticCoreRadiusCase
import ErdosProblems.Erdos1049.FixedDiagonalRationalClearing
import ErdosProblems.Erdos1049.RationalBaseContour
import ErdosProblems.Erdos1049.SoutheastBlockDeterminant
import ErdosProblems.Erdos1049.ZudilinSharpHankelCoefficient
import ErdosProblems.Erdos243.LcmRecordCrossing
import ErdosProblems.Erdos243.LcmRecordDivergence
import ErdosProblems.Erdos243.ProtectedEpochEnergy
import ErdosProblems.Erdos243.RecordIncrementBarrier
import ErdosProblems.Erdos243.SaturatedSquareTransport
import ErdosProblems.Erdos243.TwoModulusRecordCut
import ErdosProblems.Erdos249.MobiusMersenneLadderSeparation
import ErdosProblems.Erdos249.ParityPerturbedRationalControl
import ErdosProblems.Erdos249.PrefixValuationAndControlRigidity
import ErdosProblems.Erdos249.ResidueClassTotientSeries
import ErdosProblems.Erdos249.TotientAffineModeEscape
import ErdosProblems.Erdos251.FreePairReduction
import ErdosProblems.Erdos251.KernelDenominatorFloor
import ErdosProblems.Erdos257.AffineCocycleObstruction
import ErdosProblems.Erdos257.CenteredCarryPullbackBalance
import ErdosProblems.Erdos257.EndpointDivisorSignal
import ErdosProblems.Erdos257.FatalBorrowZeroFractionalSqueeze
import ErdosProblems.Erdos257.FourNinthsCoinCancellation
import ErdosProblems.Erdos257.FourNinthsMidpointCarryReachability
import ErdosProblems.Erdos257.FourNinthsNegativeCarryNoGo
import ErdosProblems.Erdos257.FourNinthsQuotientCompactness
import ErdosProblems.Erdos257.FourNinthsQuotientDefect
import ErdosProblems.Erdos257.FourNinthsSkippedTwoAdicAntiConcentration
import ErdosProblems.Erdos257.FourNinthsUpperSaturation
import ErdosProblems.Erdos257.PrimeSlackTwoValued
import ErdosProblems.Erdos257.SelectedFirstWindowQuotientLift
import ErdosProblems.Erdos257.SocketRunRationalCap
import ErdosProblems.Erdos257.TotientFourNinthsCylinderTransport
import ErdosProblems.Erdos257.TwentyOnePrimorialRepair
import ErdosProblems.Erdos257.TwentyOneRunningMaximumProducer
import ErdosProblems.Erdos257.TwentyOneSelectedDivisorHeightReduction
import ErdosProblems.Erdos269.CofinalWindowEscapeEquivalence
import ErdosProblems.Erdos269.HalfHeightDenominatorTransport
import ErdosProblems.Erdos269.IntegralRigidity
import ErdosProblems.Erdos269.NormalizedStateWidth
import ErdosProblems.Erdos269.PurePowerIrrationality
import ErdosProblems.Erdos269.RationalityCarryBridge
import ErdosProblems.Erdos68.AffineDefectRigidity
import ErdosProblems.Erdos68.BinaryCarryNormalForm
import ErdosProblems.Erdos68.CompanionConstantCarryLaw
import ErdosProblems.Erdos68.FactorialShiftFamilyOrbit
import ErdosProblems.Erdos68.HyperbolicPeeling
import ErdosProblems.Erdos68.MultiplicativeSuccessorRigidity
import ErdosProblems.Erdos68.RunCylinder
import ErdosProblems.Erdos68.ShrinkingTargetNormalForm
import ErdosProblems.IntModEq

-- Corpus union 2026-09-06: modules brought across from the private formal tree.
import ErdosProblems.Erdos243.PrimitiveRecordBarrier
-- ErdosProblems.Erdos1041.CollinearRootCase is deliberately NOT imported: it does
-- not elaborate against Mathlib v4.29.1 (8 errors, see wave5 A_union_build_report).
-- R keeps a byte-identical copy at research_corpus/Erdos1041/CollinearRootCase.lean.

/-!
# Problem-centric Erdős research library

This is the supported root for the problem-owned modules. The `Erdos249257`
library remains available as the reviewed #249/#257 corpus.
-/
