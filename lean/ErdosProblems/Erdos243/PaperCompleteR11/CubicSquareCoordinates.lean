import ErdosProblems.Erdos243.PaperCompleteR11.CubicScaleArithmetic

/-!
# Cubic square-root coordinate certificates

Candidate source; elaboration and axiom audit UNRUN.

In Q[α], with α^3=α-η, write β=x α^2+y α+z and β^2=α^2-1.
The three coordinate equations below are the exact coefficients of this
square identity. The polynomials b,d,w are the coefficients of the
characteristic polynomial of multiplication by α+β. The identities are
proved by explicit ideal-membership certificates; they are not additional
trace or norm hypotheses. Constructing the rational power basis from the
paper's actual irreducible cubic remains a separate formal obligation.

The exact sparse-polynomial certificates are also retained in
`evidence/cubic_square_polynomial_certificates.json`. Their independent
standard-library verification does not constitute Lean elaboration.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

def cubicCoordinateB (x z : ℚ) : ℚ := -2*x-3*z

def cubicCoordinateD (x y z η : ℚ) : ℚ :=
  3*η*x*y + 3*η*x + x^2 + 4*x*z - y^2 - 2*y + 3*z^2 - 1

def cubicCoordinateW (x y z η : ℚ) : ℚ :=
  -η^2*x^3 - η*x^2*y - η*x^2 - 3*η*x*y*z - 3*η*x*z +
    η*y^3 + 3*η*y^2 + 3*η*y + η - x^2*z - 2*x*z^2 + y^2*z + 2*y*z - z^3 + z

/-- Exact polynomial certificate 1, over the original three coordinate equations. -/
theorem cubic_coordinates_first_relation
    (x y z η : ℚ)
    (h1 : x^2 + 2*x*z + y^2 - 1 = 0)
    (h2 : 2*x*y + 2*y*z - η*x^2 = 0)
    (h3 : z^2 - 2*η*x*y + 1 = 0) :
    cubicCoordinateD x y z η + cubicCoordinateB x z * cubicCoordinateW x y z η = 0 := by
  unfold cubicCoordinateB cubicCoordinateD cubicCoordinateW
  linear_combination (8*η^2*x^2 - 10*η*x*y + 2*η*x - 7*η*y*z + 3*η*z + 2*x*z + 3*z^2 + 1) * h1 +
    (6*η*x^2 + 13*η*x*z + 2*η*y^2 - 6*η*y - 8*η - 2*y*z - 2*z) * h2 +
    (3*η*x*y + 3*η*x + 2*x*z - 2*y^2 - 2*y + 3*z^2) * h3

/-- Exact polynomial certificate 2, over the original three coordinate equations. -/
theorem cubic_coordinates_second_relation
    (x y z η : ℚ)
    (h1 : x^2 + 2*x*z + y^2 - 1 = 0)
    (h2 : 2*x*y + 2*y*z - η*x^2 = 0)
    (h3 : z^2 - 2*η*x*y + 1 = 0) :
    cubicCoordinateD x y z η * cubicCoordinateW x y z η +
      cubicCoordinateB x z * cubicCoordinateD x y z η +
      cubicCoordinateB x z + cubicCoordinateW x y z η = 0 := by
  unfold cubicCoordinateB cubicCoordinateD cubicCoordinateW
  linear_combination (-3*η^3*x^2*y - 3*η^3*x^2 - η^2*x^3 + 10*η^2*x^2*z + 9*η^2*x*y^2 + 18*η^2*x*y - 3*η^2*x + 6*η^2*y^2*z + 6*η^2*y*z - η*x^2*y - η*x^2 - 30*η*x*y*z - 4*η*x*z - η*y^3 - 5*η*y^2 - 35*η*y*z^2 - 10*η*y - 15*η*z^2 - 12*η - x^2*z - 4*x*z^2 - 2*x - y^2*z - 4*y*z - 4*z^3 - 7*z) * h1 +
    (-6*η^2*x*y*z - 6*η^2*x*z - 3*η^2*y^3 - 3*η^2*y^2 + 3*η^2*y + 3*η^2 + 12*η*x^2*z + 10*η*x*y^2 + 22*η*x*y + 23*η*x*z^2 + η*x + 19*η*y^2*z + 12*η*y*z - 7*η*z + 2*x*y*z + 4*x*z - 2*y - 2*z^2 - 6) * h2 +
    (6*η*x*y*z + 18*η*x*z - 12*η*y - 12*η + 8*x*y^2 + 16*x*y - 2*x*z^2 - 2*x + 8*y^2*z + 12*y*z - 3*z^3 - 7*z) * h3

/-- Exact polynomial certificate 3, over the original three coordinate equations. -/
theorem cubic_coordinates_middle_relation
    (x y z η : ℚ)
    (h1 : x^2 + 2*x*z + y^2 - 1 = 0)
    (h2 : 2*x*y + 2*y*z - η*x^2 = 0)
    (h3 : z^2 - 2*η*x*y + 1 = 0) :
    (cubicCoordinateW x y z η)^2 + 1 + (cubicCoordinateB x z)^2 +
      (cubicCoordinateD x y z η)^2 - 8*η*cubicCoordinateW x y z η = 0 := by
  unfold cubicCoordinateB cubicCoordinateD cubicCoordinateW
  linear_combination (η^4*x^4 - 2*η^4*x^3*z - η^4*x^2*y^2 + 4*η^4*x^2*z^2 + η^4*x^2 + 2*η^3*x^3*y + 2*η^3*x^3 + 2*η^3*x^2*y*z + 2*η^3*x^2*z + 2*η^3*x*y^3 - 4*η^3*x*y*z^2 - 2*η^3*x*y + 2*η^3*y^3*z - 8*η^3*y*z^3 - 2*η^3*y*z + 2*η^2*x^3*z + η^2*x^2*y^2 + 2*η^2*x^2*y - 40*η^2*x^2*z^2 + 45*η^2*x^2 - 20*η^2*x*y^2*z - 56*η^2*x*y*z - 4*η^2*x*z + η^2*y^4 + 6*η^2*y^3 + 16*η^2*y^2 - 4*η^2*y*z^2 + 18*η^2*y + 7*η^2 + 2*η*x^2*y*z + 2*η*x^2*z + 92*η*x*y*z^2 - 76*η*x*y + 18*η*x*z^2 + 18*η*x - 30*η*y^3*z - 54*η*y^2*z + 96*η*y*z^3 - 56*η*y*z + 30*η*z^3 + 42*η*z + x^2*z^2 + x^2 + 2*x*z^3 + 6*x*z - 15*y^2*z^2 - 15*y^2 - 28*y*z^2 - 28*y + 2*z^4 + 9*z^2 + 3) * h1 +
    (-4*η^3*x*y^2*z + 8*η^3*x*z^3 + 4*η^3*x*z - η^3*y^4 + 4*η^3*y^2*z^2 + 2*η^3*y^2 - 4*η^3*z^2 - η^3 + 6*η^2*x*y^3 + 8*η^2*x*y^2 + 2*η^2*x*y + 4*η^2*x*z^2 - 8*η^2*x + 2*η^2*y^2*z - 2*η^2*z - 40*η*x^2*z^2 + 44*η*x^2 - 20*η*x*y^2*z - 60*η*x*y*z - 82*η*x*z^3 + 80*η*x*z + 16*η*y^4 + 32*η*y^3 - 49*η*y^2*z^2 + 23*η*y^2 - 18*η*y*z^2 - 42*η*y + 23*η*z^2 - 53*η + 6*x*y*z^2 + 6*x*y + 12*x*z^2 + 12*x + 22*y*z^3 + 18*y*z + 52*z^3 + 48*z) * h2 +
    (-20*η*x*y*z^2 + 22*η*x*y - 54*η*x*z^2 + 12*η*x + 44*η*y*z + 36*η*z - 32*x*y^2*z - 80*x*y*z + 4*x*z + 16*y^4 + 32*y^3 - 48*y^2*z^2 - 12*y^2 - 108*y*z^2 - 24*y + z^4 + 8*z^2 + 5) * h3

/-- A square-root coordinate solution has nonzero norm parameter. -/
theorem cubic_coordinate_parameter_ne_zero
    (x y z η : ℚ)
    (h1 : x^2 + 2*x*z + y^2 - 1 = 0)
    (h2 : 2*x*y + 2*y*z - η*x^2 = 0)
    (h3 : z^2 - 2*η*x*y + 1 = 0) : cubicCoordinateW x y z η ≠ 0 := by
  intro hw
  have hfirst := cubic_coordinates_first_relation x y z η h1 h2 h3
  have hsecond := cubic_coordinates_second_relation x y z η h1 h2 h3
  have hmiddle := cubic_coordinates_middle_relation x y z η h1 h2 h3
  rw [hw] at hfirst hsecond hmiddle
  have hd : cubicCoordinateD x y z η = 0 := by nlinarith [hfirst]
  have hb : cubicCoordinateB x z = 0 := by rw [hd] at hsecond; nlinarith
  rw [hd, hb] at hmiddle
  norm_num at hmiddle

/-- Both reciprocal scale equations now follow from the square-root
coordinates; the coefficient relations are no longer separate premises. -/
theorem cubic_coordinate_scale_relations
    (x y z η : ℚ)
    (h1 : x^2 + 2*x*z + y^2 - 1 = 0)
    (h2 : 2*x*y + 2*y*z - η*x^2 = 0)
    (h3 : z^2 - 2*η*x*y + 1 = 0) :
    let w := cubicCoordinateW x y z η
    (w^2 + 1)^2 = 8*η*w^3 ∨ (w^2 + 1)^2 = 8*η*w := by
  have hfirst := cubic_coordinates_first_relation x y z η h1 h2 h3
  have hsecond := cubic_coordinates_second_relation x y z η h1 h2 h3
  have hmiddle := cubic_coordinates_middle_relation x y z η h1 h2 h3
  apply reciprocal_cubic_scale_relations (cubicCoordinateB x z)
    (cubicCoordinateD x y z η) (cubicCoordinateW x y z η) η
  · nlinarith
  · nlinarith
  · nlinarith

end ErdosProblems.Erdos243.PaperCompleteR11
