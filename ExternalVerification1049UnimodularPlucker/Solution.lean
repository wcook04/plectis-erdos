/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperFiniteAssembliesR7

/-!
# Trusted challenge for the unimodular Bézout--Plücker tail collapse

Let `R₀` be a commutative ring and let `w n = (A n, B n)` be a sequence of
rows in `R₀ × R₀`.  Assume every row is unimodular, meaning `IsCoprime (A n)
(B n)`, and assume every adjacent minor `A n * B (n+1) - B n * A (n+1)`
vanishes.  The first theorem proves that every pairwise minor vanishes.

The second theorem specialises to `R₀ = ZMod (2^S * 3^R)` with `R` positive
and produces two distinct binary selectors on `Fin k` with equal selected row
sums as soon as `S + 2R ≤ k`, so the sufficient width is `S + 2R` rather than
the ambient two-coordinate width `2S + 4R`.

Neither coordinate is assumed to be a unit, which is the point of the
unimodular hypothesis: `(2, 3)` is unimodular modulo `6` while neither entry
is invertible.  This is a structural lemma about integral rows.  It supplies
no irrationality conclusion and it does not settle Erdős Problem 1049.
-/

universe u

namespace Erdos249257.ExternalVerification1049UnimodularPlucker

/-- Vanishing adjacent minors of unimodular rows force every pairwise minor
to vanish, over an arbitrary commutative ring. -/
theorem adjacent_det_zero_forces_all_det_zero_of_isCoprime
    (R₀ : Type u) [CommRing R₀] (w : ℕ → R₀ × R₀)
    (hu : ∀ n, IsCoprime (w n).1 (w n).2)
    (ha : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  exact (ErdosProblems.Erdos1049.PaperR7.plucker_paper_statement).1 R₀ w hu ha

/-- The modular consequence: at width `S + 2R` two distinct binary selectors
already have equal selected sums. -/
theorem zmod_binary_tail_collision_of_isCoprime
    (R S k : ℕ) (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R))
    (hu : ∀ n, IsCoprime (w n).1 (w n).2)
    (ha : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0)
    (hR : 0 < R) (hk : S + 2 * R ≤ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  exact (ErdosProblems.Erdos1049.PaperR7.plucker_paper_statement.{0}).2 R S k w hu ha hR hk

end Erdos249257.ExternalVerification1049UnimodularPlucker
