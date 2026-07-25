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
import ErdosProblems.Erdos249.FiniteEulerSieve
import ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature
import ErdosProblems.Erdos249.CyclotomicAnchoredKill
import ErdosProblems.Erdos249.PeriodMultipleEscape
import ErdosProblems.Erdos249.RankOneSubrankObstruction
import ErdosProblems.Erdos249.TotientStrictPrimeEscape
import ErdosProblems.Erdos257.HalfCounterexampleFrontier
import ErdosProblems.Erdos257.MersenneSubseriesRigidity
