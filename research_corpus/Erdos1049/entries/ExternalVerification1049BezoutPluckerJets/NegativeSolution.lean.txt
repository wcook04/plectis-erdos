import ExternalVerification1049BezoutPluckerJets.Challenge

namespace Erdos249257.ExternalVerification1049BezoutPluckerJets

open scoped BigOperators

theorem zmod_binary_tail_collision_of_two_three_depth {R S k : ℕ}
    [NeZero (2 ^ S * 3 ^ R)] (_extra : True)
    (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R))
    (hunit : ∀ n, IsUnit (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0)
    (hR : 0 < R) (hrank : S + 2 * R ≤ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry

end Erdos249257.ExternalVerification1049BezoutPluckerJets
