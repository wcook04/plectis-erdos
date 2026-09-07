/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.SaturatedSquareTransport

/-!
# Source transport for saturated square transport and its Legendre defect

Both source declarations are already stated in Mathlib-only vocabulary, so the
transport is the identity: each Challenge statement is the source statement,
applied directly.
-/
namespace Erdos249257.ExternalVerification243SaturatedSquareTransport

/-- **Saturated square transport, unnormalised form.**  The whole next reduced
numerator divides `hc * e * e' - v ^ 2`, with no hypothesis beyond the two
cocycle equations and the two centred-error definitions. -/
theorem saturated_square_transport_raw
    {a u v w hc u' v' : ℕ} {a' e e' : ℤ}
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (he : e = (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ))
    (he' : e' = (v' : ℤ) - (a' - 1) * (u' : ℤ)) :
    (u' : ℤ) ∣ (hc : ℤ) * e * e' - (v : ℤ) ^ 2 :=
  ErdosProblems.Erdos243.saturated_square_transport_raw hq hnum hden he he'

/-- **The Legendre defect obstructs a unit non-square part, and nothing more.**
If the centred-error product is a quadratic non-residue modulo a prime dividing
the next numerator, then the non-square part `b` of the removed content is not
`1`. No bound on the content follows. -/
theorem legendre_defect_forces_nonsquare_content
    {b s u' p : ℕ} {e e' : ℤ}
    (hdvd : (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2)
    (hpu : p ∣ u')
    (hnr : ¬ IsSquare ((e : ZMod p) * (e' : ZMod p))) :
    b ≠ 1 :=
  ErdosProblems.Erdos243.legendre_defect_forces_nonsquare_content hdvd hpu hnr

end Erdos249257.ExternalVerification243SaturatedSquareTransport
