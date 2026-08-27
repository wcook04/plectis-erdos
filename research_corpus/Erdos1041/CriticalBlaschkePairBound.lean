import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernel for the critical Blaschke pair bound

For a finite Blaschke product critical at the origin, the ordinary analytic
proof turns logarithmic differentiation into a closed polygon with side lengths
`q(r) = 1/r - r`.  The polygon inequality implies that the smallest two zero
radii obey `r₂ ≤ (k-1) r₁`.  Together with the product identity this module
checks the load-bearing power bound.

The Blaschke factor identity, Riemann-map transfer, and Bergman geodesic theorem
remain in the companion ordinary proof.  This module does not claim the
unrestricted Erdős theorem.
-/

namespace ErdosProblems.Erdos1041.CriticalBlaschkePairBound

/-- Multiplying the first-radius inequality by the remaining product gives the
explicit second-radius estimate `r₂^k ≤ (k-1)P`. -/
theorem secondRadius_pow_le
    {k : ℕ} (hk : 2 ≤ k)
    {r₁ r₂ P : ℝ}
    (hr₂ : 0 ≤ r₂)
    (hfirst : r₂ ≤ ((k - 1 : ℕ) : ℝ) * r₁)
    (hproduct : r₁ * r₂ ^ (k - 1) ≤ P) :
    r₂ ^ k ≤ ((k - 1 : ℕ) : ℝ) * P := by
  have htail : 0 ≤ r₂ ^ (k - 1) := pow_nonneg hr₂ _
  have hmul := mul_le_mul_of_nonneg_right hfirst htail
  have hscale : 0 ≤ ((k - 1 : ℕ) : ℝ) := by positivity
  have hproduct' := mul_le_mul_of_nonneg_left hproduct hscale
  have hexp : 1 + (k - 1) = k := by omega
  calc
    r₂ ^ k = r₂ * r₂ ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
    _ ≤ (((k - 1 : ℕ) : ℝ) * r₁) * r₂ ^ (k - 1) := hmul
    _ = ((k - 1 : ℕ) : ℝ) * (r₁ * r₂ ^ (k - 1)) := by ring
    _ ≤ ((k - 1 : ℕ) : ℝ) * P := hproduct'

/-- The elementary ratio step used after the Blaschke polygon inequality. -/
theorem secondRadius_le_of_q_balance
    {k : ℕ} (hk : 2 ≤ k)
    {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hr₁₂ : r₁ ≤ r₂) (hr₂one : r₂ < 1)
    (hbalance : (1 - r₁ ^ 2) / r₁ ≤
      ((k - 1 : ℕ) : ℝ) * ((1 - r₂ ^ 2) / r₂)) :
    r₂ ≤ ((k - 1 : ℕ) : ℝ) * r₁ := by
  have hgap : 0 < 1 - r₂ ^ 2 := by nlinarith [sq_nonneg r₂]
  have hmono : 1 - r₂ ^ 2 ≤ 1 - r₁ ^ 2 := by nlinarith
  have hkpos : 0 < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hbalance' : (1 - r₁ ^ 2) / r₁ ≤
      (((k - 1 : ℕ) : ℝ) * (1 - r₂ ^ 2)) / r₂ := by
    simpa [mul_div_assoc] using hbalance
  have hcross : (1 - r₁ ^ 2) * r₂ ≤
      (((k - 1 : ℕ) : ℝ) * (1 - r₂ ^ 2)) * r₁ :=
    (div_le_div_iff₀ hr₁ hr₂).mp hbalance'
  have hupper : (((k - 1 : ℕ) : ℝ) * (1 - r₂ ^ 2)) * r₁ ≤
      (((k - 1 : ℕ) : ℝ) * (1 - r₁ ^ 2)) * r₁ := by
    calc
      (((k - 1 : ℕ) : ℝ) * (1 - r₂ ^ 2)) * r₁ =
          (((k - 1 : ℕ) : ℝ) * r₁) * (1 - r₂ ^ 2) := by ring
      _ ≤ (((k - 1 : ℕ) : ℝ) * r₁) * (1 - r₁ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (le_of_lt (mul_pos hkpos hr₁))
      _ = (((k - 1 : ℕ) : ℝ) * (1 - r₁ ^ 2)) * r₁ := by ring
  have hgap₁ : 0 < 1 - r₁ ^ 2 := lt_of_lt_of_le hgap hmono
  have hchain := le_trans hcross hupper
  by_contra hnot
  have hstrict : ((k - 1 : ℕ) : ℝ) * r₁ < r₂ := lt_of_not_ge hnot
  have hstrict' := mul_lt_mul_of_pos_left hstrict hgap₁
  nlinarith

end ErdosProblems.Erdos1041.CriticalBlaschkePairBound
