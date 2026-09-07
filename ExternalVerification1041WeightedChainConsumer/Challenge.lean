/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 weighted-chain consumer

The Challenge contains only the literal ordered-algebra statement.  It does
not import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041WeightedChainConsumer

/- Positivity and monotonicity transfer the weighted lifetime lower bound to
the floor value. -/
theorem weighted_chain_consumer
    {lifetime totalSize phiAtWeighted phiAtFloor : ℝ}
    (hsize : 0 < totalSize)
    (hexact : lifetime ≥ totalSize * phiAtWeighted)
    (hmono : phiAtFloor ≤ phiAtWeighted) :
    totalSize * phiAtFloor ≤ lifetime := by
  sorry

end Erdos249257.ExternalVerification1041WeightedChainConsumer
