/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification1041NewtonDerivative.Statements
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Deliberate nearby mismatch for the #1041 Newton-flow derivative kernel

The negative fixture adds an irrelevant proposition argument after the
challenge hypotheses.  It can reuse the source proof, but Comparator must
reject it before semantic acceptance.
-/

namespace Erdos249257.ExternalVerification1041NewtonDerivative

theorem newtonFlow_value_hasDerivAt
    {f f' z : ℂ → ℂ} {t : ℂ}
    (hf : HasDerivAt f (f' (z t)) (z t))
    (hz : HasDerivAt z (-f (z t) / f' (z t)) t)
    (hcritical : f' (z t) ≠ 0) (hweak : True) :
    HasDerivAt (fun s => f (z s)) (-f (z t)) t := by
  simpa [ErdosProblems.Erdos1041.newtonFlowVector] using
    (ErdosProblems.Erdos1041.newtonFlow_value_hasDerivAt hf hz hcritical)

end Erdos249257.ExternalVerification1041NewtonDerivative
