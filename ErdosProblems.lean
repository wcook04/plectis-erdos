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

/-!
# Problem-centric Erdős research library

This is the supported root for the problem-owned modules. The `Erdos249257`
library remains available as the reviewed #249/#257 corpus.
-/
