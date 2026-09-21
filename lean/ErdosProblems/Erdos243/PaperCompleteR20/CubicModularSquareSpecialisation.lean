import ErdosProblems.Erdos243.PaperCompleteR11.CubicModularDensity
import ErdosProblems.Erdos243.PaperCompleteR11.CubicZeroDensityShape

/-!
# Erdős 243: modular square data forced by zero exceptional density

This is the exact local input to the Chebotarev specialisation.  If the cubic
profile has zero lower density of exceptions, every good finite-field root of
the depressed cubic has square `r² - 1`; otherwise the already proved
single-prime obstruction gives positive lower density immediately.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR20

open ErdosProblems.Erdos243.PaperCompleteR11

/-- Zero lower density forces the square condition at each good modular root.
This packages the orbit-to-local direction without any prime-production or
number-field hypothesis. -/
theorem zero_lower_density_forces_modular_root_square
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hzero : ZeroLowerDensity {n : ℕ | u n ≠ m * risingBinomial n + c})
    (r : ZMod p)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hfactor : 3 * (m : ZMod p) * r ≠ 0) :
    IsSquare (r ^ 2 - 1) := by
  by_contra hns
  have hdensity := integral_cubic_single_prime_density
    a u v m c T p hp hnum hden r hroot hfactor hns
  have hpR : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  exact (hzero.not_positive_lower_bound (1 / (p : ℝ))
    (one_div_pos.mpr hpR)) hdensity

/-- Natural-valued primitive orbits feed the same finite-field square
condition after the exact cast of both recurrences. -/
theorem natural_zero_lower_density_forces_modular_root_square
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (r : ZMod p)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hfactor : 3 * (m : ZMod p) * r ≠ 0) :
    IsSquare (r ^ 2 - 1) := by
  apply zero_lower_density_forces_modular_root_square
    (fun n ↦ (a n : ℤ)) (fun n ↦ (u n : ℤ)) (fun n ↦ (v n : ℤ))
    (m : ℤ) c T p hp
  · intro j hj
    exact_mod_cast hnum j hj
  · intro j hj
    exact_mod_cast hden j hj
  · exact hzero
  · simpa only [Int.cast_natCast] using hroot
  · simpa only [Int.cast_natCast] using hfactor

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.zero_lower_density_forces_modular_root_square
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.natural_zero_lower_density_forces_modular_root_square

end ErdosProblems.Erdos243.PaperCompleteR20
