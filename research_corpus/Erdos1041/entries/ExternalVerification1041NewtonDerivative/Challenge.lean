/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 Newton-flow derivative kernel

The Challenge contains only the literal chain-rule conclusion.  It does not
import the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041NewtonDerivative

/-- Along a curve tangent to the complex Newton field, the polynomial value
has derivative equal to its own negative. -/
theorem newtonFlow_value_hasDerivAt
    {f f' z : ℂ → ℂ} {t : ℂ}
    (hf : HasDerivAt f (f' (z t)) (z t))
    (hz : HasDerivAt z (-f (z t) / f' (z t)) t)
    (hcritical : f' (z t) ≠ 0) :
    HasDerivAt (fun s => f (z s)) (-f (z t)) t := by
  sorry

end Erdos249257.ExternalVerification1041NewtonDerivative
