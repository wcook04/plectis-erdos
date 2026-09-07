/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the #1041 Newton-decay boundary

The Challenge contains only the literal theorem type.  It does not import
the project-local source module or expose its namespace vocabulary.
-/

namespace Erdos249257.ExternalVerification1041NewtonDecay

/-- A Newton-value connection with exact exponential decay is impossible when
the two endpoint values are not on the same positive ray. -/
theorem no_newtonConnection_of_not_samePositiveRay
    {startValue endValue : ℂ} {time : ℝ}
    (hrays : ¬ SamePositiveRay startValue endValue)
    (hconnection :
      endValue = (Real.exp (-time) : ℂ) * startValue) :
    False := by
  sorry

end Erdos249257.ExternalVerification1041NewtonDecay
