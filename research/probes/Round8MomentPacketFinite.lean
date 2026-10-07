import Mathlib

/-!
Finite algebraic regression candidates for round 8 packet 4.

STATUS: UNRUN in the receiver environment, which has no Lean/Lake executable.
These four elementary lemmas do not formalise the infinite interpolation,
Dirichlet continuation, density estimate or totient application.
Proposed home after Type A review: research/probes/Round8MomentPacketCanary.lean.
-/

namespace PlectisRound8MomentPacket

/-- The unweighted total of a signed second-difference packet is zero. -/
theorem second_packet_mass (M d : ℤ) : d * M - 2 * d * M + d * M = 0 := by
  ring

/-- Its first ordinary moment is zero; no dyadic weight appears here. -/
theorem second_packet_first_moment (n t M d : ℤ) :
    d * M * n - 2 * d * M * (n + t) + d * M * (n + 2 * t) = 0 := by
  ring

/-- Its next moment is generally nonzero: full moments are not preserved. -/
theorem second_packet_second_moment (n t M d : ℤ) :
    d * M * n ^ 2 - 2 * d * M * (n + t) ^ 2 + d * M * (n + 2 * t) ^ 2
      = 2 * d * M * t ^ 2 := by
  ring

/-- Ordinary-moment neutrality does not mean a zero generating-function value. -/
theorem second_packet_generating_polynomial (n t : ℕ) (M d z : ℚ) :
    d * M * (z ^ n - 2 * z ^ (n + t) + z ^ (n + t + t))
      = d * M * z ^ n * (1 - z ^ t) ^ 2 := by
  simp only [pow_add]
  ring

#print axioms second_packet_mass
#print axioms second_packet_first_moment
#print axioms second_packet_second_moment
#print axioms second_packet_generating_polynomial
#check second_packet_mass
#check second_packet_first_moment
#check second_packet_second_moment
#check second_packet_generating_polynomial

end PlectisRound8MomentPacket
