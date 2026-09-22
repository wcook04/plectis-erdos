import ErdosProblems.Erdos1041.PaperCompleteR21.LobeAndArity
import ErdosProblems.Erdos1041.PaperCompleteR21.PlanePerimeterBound
import ErdosProblems.Erdos1041.PaperCompleteR21.GammaQuarterBound

/-!
# Erdős 1041: `res:one-root-gamma-false`, unconditionally

`Lobe.one_root_gamma_false` (`LobeAndArity.lean`) proves the short-note
proposition `res:one-root-gamma-false`
(`paper/1041/erdos-1041-lemniscate-newton-flow.tex`, line 806) from two named
hypotheses.  Both are now theorems:

* `PlanePerimeterBound`, the plane encircling bound, is
  `plane_perimeter_bound` (`PlanePerimeterBound.lean`);
* `Real.Gamma (1 / 4) ≤ 3.63` is `gamma_quarter_le_363`
  (`GammaQuarterBound.lean`).

`one_root_gamma_false_unconditional` carries the statement of
`one_root_gamma_false` with the two hypothesis binders removed, character for
character.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Set

namespace Lobe

/-- The plane encircling bound, as a term of the `def` `PlanePerimeterBound`. -/
theorem planePerimeterBound : PlanePerimeterBound :=
  fun A x ρ hρ hA hball => plane_perimeter_bound A x ρ hρ hA hball

/-- **`res:one-root-gamma-false`, with no hypotheses.**  For `p(z) = z^8 - (3/2)z` and `C`
the component of `{|p| ≤ 1}` containing `0`: `C` contains exactly one zero of `p`, `C`
contains a neighbourhood of the closed disc of radius `5/8`, `H^1(∂C) > 5π/4`, and
`Γ(1/4)^2/(2√π) ≤ (π/2)(1+√2) < 5π/4`. -/
theorem one_root_gamma_false_unconditional :
    {z : ℂ | z ∈ lobeComponent ∧ lobePolynomial.eval z = 0} = {(0 : ℂ)} ∧
      (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) (5 / 8) ⊆ U ∧
        U ⊆ lobeComponent) ∧
      ENNReal.ofReal (5 * Real.pi / 4)
        < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) ∧
      Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)
        ≤ (Real.pi / 2) * (1 + Real.sqrt 2) ∧
      (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4 :=
  one_root_gamma_false planePerimeterBound gamma_quarter_le_363

end Lobe

end ErdosProblems.Erdos1041.PaperCompleteR21
