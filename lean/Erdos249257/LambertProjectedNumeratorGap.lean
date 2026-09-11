import Erdos249257.SquaredMersenneDiagonalEnclosure

/-!
# Exact numerator gaps for the squared-Mersenne projection

This companion isolates the finite arithmetic input needed by the canonical
Lambert enclosure.  It turns a lower bound for the reduced numerator after
clearing an arbitrary integer translate into a miss of the actual diagonal.
The theorem does not assert that such gaps occur cofinally; that is the
remaining arithmetic producer obligation.
-/

namespace Erdos249257.LambertProjectedNumeratorGap

open FullTargetPrimeAdjunctionNoGo
open SquaredMersenneDiagonalEnclosure

/-- **Exact reduced-numerator consumer.**  To separate the canonical rational
Lambert centre from every integer, it is enough to give a uniform lower bound
for the integer numerator left after clearing its reduced denominator.  This
is the direct socket for finite residue or centered-remainder arguments: the
analytic side only has to fit inside the same gap after denominator scaling. -/
theorem scaleFullTarget_miss_of_lambert_projected_num_gap
    {H D m : ℕ}
    (hgap : ∀ z : ℤ, (m : ℝ) ≤
      |((lambertProjectedDiagonalRat H D).num : ℝ) -
        (z : ℝ) * ((lambertProjectedDiagonalRat H D).den : ℝ)|)
    (hbound : lambertSquareComplementBound H D *
      ((lambertProjectedDiagonalRat H D).den : ℝ) < (m : ℝ)) :
    ¬ScaleFullTargetHit H := by
  apply scaleFullTarget_miss_of_lambert_projected_separation
  intro z
  have hden : (0 : ℝ) < (lambertProjectedDiagonalRat H D).den := by
    exact_mod_cast (lambertProjectedDiagonalRat H D).den_pos
  have hrepr :
      lambertProjectedDiagonal H D - (z : ℝ) =
        (((lambertProjectedDiagonalRat H D).num : ℝ) -
            (z : ℝ) * ((lambertProjectedDiagonalRat H D).den : ℝ)) /
          ((lambertProjectedDiagonalRat H D).den : ℝ) := by
    rw [lambertProjectedDiagonal, Rat.cast_def]
    field_simp
  rw [hrepr, abs_div, abs_of_pos hden]
  exact (lt_div_iff₀ hden).2 (hbound.trans_le (hgap z))

#print axioms scaleFullTarget_miss_of_lambert_projected_num_gap

end Erdos249257.LambertProjectedNumeratorGap
