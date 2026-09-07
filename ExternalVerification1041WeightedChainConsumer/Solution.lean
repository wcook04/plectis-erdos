/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041WeightedChainConsumer.Statements
import ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz

/-!
# Source transport for the #1041 weighted-chain consumer

The proof is the exact source theorem.  This fixture isolates the scalar
ordered-algebra step that transfers a weighted lifetime lower bound to the
floor value.
-/

namespace Erdos249257.ExternalVerification1041WeightedChainConsumer

theorem weighted_chain_consumer
    {lifetime totalSize phiAtWeighted phiAtFloor : ℝ}
    (hsize : 0 < totalSize)
    (hexact : lifetime ≥ totalSize * phiAtWeighted)
    (hmono : phiAtFloor ≤ phiAtWeighted) :
    totalSize * phiAtFloor ≤ lifetime := by
  exact ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz.weighted_chain_consumer
    hsize hexact hmono

end Erdos249257.ExternalVerification1041WeightedChainConsumer
