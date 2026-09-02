import Mathlib
import ErdosProblems.Erdos1049.BezoutPluckerJets

namespace Erdos249257.ExternalVerification1049BezoutPluckerJets

open scoped BigOperators

theorem anchor_det_zero_forces_all_det_zero {R : Type*} [CommRing R]
    {ι : Type*} (w : ι → R × R) {a b : R}
    (hab : IsCoprime a b) (hdet : ∀ i, a * (w i).2 - b * (w i).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  exact ErdosProblems.Erdos1049.BezoutPluckerJets.anchor_det_zero_forces_all_det_zero
    w hab hdet

theorem binary_row_collision_of_anchor_det_zero
    {R ι : Type*} [CommRing R] [Fintype R] [Fintype ι]
    (w : ι → R × R) {a b : R}
    (hab : IsCoprime a b) (hdet : ∀ i, a * (w i).2 - b * (w i).1 = 0)
    (hcard : Fintype.card R < 2 ^ Fintype.card ι) :
    ∃ s t : ι → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  exact ErdosProblems.Erdos1049.BezoutPluckerJets.binary_row_collision_of_anchor_det_zero
    w hab hdet hcard

theorem adjacent_det_zero_forces_all_det_zero {R : Type*} [CommRing R]
    (w : ℕ → R × R) (hunit : ∀ n, IsUnit (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  exact ErdosProblems.Erdos1049.BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero
    w hunit hadj

theorem zmod_binary_tail_collision_of_two_three_depth {R S k : ℕ}
    [NeZero (2 ^ S * 3 ^ R)]
    (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R))
    (hunit : ∀ n, IsUnit (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0)
    (hR : 0 < R) (hrank : S + 2 * R ≤ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  exact ErdosProblems.Erdos1049.BezoutPluckerJets.zmod_binary_tail_collision_of_two_three_depth
    w hunit hadj hR hrank

end Erdos249257.ExternalVerification1049BezoutPluckerJets
