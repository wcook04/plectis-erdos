/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for saturated square transport and its Legendre defect

Two source-independent propositions about one primitive step of a reciprocal
tail dynamic.  Write `w + v = a * u`, `w = hc * u'`, `a * v = hc * v'`, with
centred errors `e = v - (a - 1) * u` and `e' = v' - (a' - 1) * u'`.

The first proposition is an exact divisibility with **no hypothesis at all**
beyond those three equations and the two definitions: the whole next numerator
`u'` divides `hc * e * e' - v ^ 2`.  Transport is modulo `u'` itself, with the
full removed content, rather than modulo the largest divisor of `u'` coprime
to that content.

The second records the exact reach of the quadratic-character consequence: a
non-residue error product forces only that the non-square part `b` of the
removed content is not `1`.  It says nothing about the size of the content and
nothing at all when the content is a perfect square.  The negative half is the
point: quadratic-character counting cannot detect square deletion.

Boundary.  Neither statement bounds the cancellation factors or the orbit.
Erdős #243 remains open.
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
    (u' : ℤ) ∣ (hc : ℤ) * e * e' - (v : ℤ) ^ 2 := by
  sorry

/-- **The Legendre defect obstructs a unit non-square part, and nothing more.**
If the centred-error product is a quadratic non-residue modulo a prime dividing
the next numerator, then the non-square part `b` of the removed content is not
`1`. No bound on the content follows. -/
theorem legendre_defect_forces_nonsquare_content
    {b s u' p : ℕ} {e e' : ℤ}
    (hdvd : (u' : ℤ) ∣ (b : ℤ) * e * e' - ((b : ℤ) * (s : ℤ)) ^ 2)
    (hpu : p ∣ u')
    (hnr : ¬ IsSquare ((e : ZMod p) * (e' : ZMod p))) :
    b ≠ 1 := by
  sorry

end Erdos249257.ExternalVerification243SaturatedSquareTransport
