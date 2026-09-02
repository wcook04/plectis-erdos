import Mathlib

/-! Deliberate theorem-interface mismatch for Comparator rejection. -/

namespace Erdos249257.ExternalVerification249BinaryCyclotomicAnchors

noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs

theorem exists_clean_binaryCyclotomicAnchor
    (h N₀ : ℕ) (hh : 0 < h) (_extra : True) :
    ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ binaryCyclotomicLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 := by
  sorry

end Erdos249257.ExternalVerification249BinaryCyclotomicAnchors
