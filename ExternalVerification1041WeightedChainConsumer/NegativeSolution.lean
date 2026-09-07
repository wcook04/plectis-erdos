/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041WeightedChainConsumer.Statements
import ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz

/-!
# Deliberate nearby mismatch for the #1041 weighted-chain consumer

The negative fixture adds an irrelevant proposition argument after the
challenge parameters.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041WeightedChainConsumer

theorem weighted_chain_consumer
    {lifetime totalSize phiAtWeighted phiAtFloor : ℝ}
    (hsize : 0 < totalSize)
    (hexact : lifetime ≥ totalSize * phiAtWeighted)
    (hmono : phiAtFloor ≤ phiAtWeighted)
    (hweak : True) :
    totalSize * phiAtFloor ≤ lifetime := by
  exact ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz.weighted_chain_consumer
    hsize hexact hmono

end Erdos249257.ExternalVerification1041WeightedChainConsumer
