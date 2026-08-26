import Mathlib.Data.Int.ModEq

/-!
# Exact division of integer congruences

The lemma in this module removes a common nonzero factor from two divisible
integers and from the modulus of a congruence.  It is independent of the
Erdős-problem developments that use it.
-/

namespace Int.ModEq

/-- Suppose that `d` divides `a` and `b`.  A congruence between `a` and `b`
modulo `d * m` descends, after exact division by the nonzero integer `d`, to a
congruence modulo `m`. -/
theorem ediv_of_dvd_of_modEq_mul_left
    {d m a b : ℤ} (hd : d ≠ 0)
    (ha : d ∣ a) (hb : d ∣ b)
    (h : a ≡ b [ZMOD d * m]) :
    a / d ≡ b / d [ZMOD m] := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  simpa [Int.mul_ediv_cancel_left _ hd] using h.mul_left_cancel' hd

end Int.ModEq
