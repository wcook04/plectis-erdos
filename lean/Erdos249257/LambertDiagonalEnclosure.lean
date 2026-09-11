import Erdos249257.ActualForeignResidueProjection

/-!
# Lambert diagonal enclosure

This module closes the topological step left after the finite foreign-residue
window estimate.  Once those finite windows converge to the actual omitted
foreign defect, the already-proved uniform geometric bound passes to the
limit and yields `ControlledForeignProjection`.

The convergence statement is deliberately exposed as the remaining analytic
input.  This module does not claim the Möbius/Lambert kernel identity, an
unbounded supply of separated projections, or irrationality on its own.
-/

namespace Erdos249257.LambertDiagonalEnclosure

open Filter
open FullTargetPrimeAdjunctionNoGo
open ActualForeignResidueProjection

/-- The exact analytic obligation connecting the finite residue windows to
the omitted part of the actual foreign defect. -/
def ForeignResidueTailLimit (H D : ℕ) : Prop :=
  Tendsto (fun L => foreignTailWindow H D L) atTop
    (nhds (scaleForeignDefect H - projectedForeignDefect H D))

/-- The uniform finite-window estimate survives the tail limit.  This is the
missing topology step between the finite geometric calculation and the
existing full-target enclosure consumer. -/
theorem controlledForeignProjection_of_tail_limit
    {H D : ℕ} (hcutoff : 2 * H ≤ D)
    (htail : ForeignResidueTailLimit H D) :
    ControlledForeignProjection H D := by
  unfold ControlledForeignProjection
  have htail' : Tendsto (fun L => foreignTailWindow H D L) atTop
      (nhds (scaleForeignDefect H - projectedForeignDefect H D)) := htail
  have habs : Tendsto (fun L => |foreignTailWindow H D L|) atTop
      (nhds |scaleForeignDefect H - projectedForeignDefect H D|) :=
    (continuous_abs.tendsto _).comp htail'
  exact le_of_tendsto' habs fun L =>
    abs_foreignTailWindow_le_foreignComplementBound hcutoff

/-- A tail-limit identity plus exact projected separation rules out a
full-target hit at the scale `H`. -/
theorem scaleFullTarget_miss_of_tail_limit
    {H D : ℕ} (hcutoff : 2 * H ≤ D)
    (htail : ForeignResidueTailLimit H D)
    (hseparation : ProjectedFullTargetSeparation H D) :
    ¬ScaleFullTargetHit H :=
  scaleFullTarget_miss_of_projected_separation
    (controlledForeignProjection_of_tail_limit hcutoff htail) hseparation

/-- Expanded separation form for generated exact-rational certificates. -/
theorem scaleFullTarget_miss_of_tail_limit_of_forall_int
    {H D : ℕ} (hcutoff : 2 * H ≤ D)
    (htail : ForeignResidueTailLimit H D)
    (hseparation : ∀ z : ℤ, foreignComplementBound H D <
      |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|) :
    ¬ScaleFullTargetHit H :=
  scaleFullTarget_miss_of_tail_limit hcutoff htail hseparation

#print axioms controlledForeignProjection_of_tail_limit
#print axioms scaleFullTarget_miss_of_tail_limit
#print axioms scaleFullTarget_miss_of_tail_limit_of_forall_int

end Erdos249257.LambertDiagonalEnclosure
