import Erdos257PeriodNoncollapse.MersenneLambertLadder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #249: finite Euler-sieve algebra

Elementary finite-stage identities behind the Euler-sieve approximation to
the totient generating function.  No external transcendence theorem is
asserted as Lean authority here.
-/

namespace ErdosProblems.Erdos249.FiniteEulerSieve

open scoped BigOperators

/-- Local coefficients of the squared Möbius Euler factor. -/
def muSqLocal : ℕ → ℤ
  | 0 => 1
  | 1 => -2
  | 2 => 1
  | _ => 0

/-- The finite geometric sum `1 + p + ... + p^e` over the integers. -/
def sigmaPrimePow (p e : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (e + 1), (p : ℤ) ^ j

/-- The `s = 1` Euler factor controlling finite-stage quasimodular depth. -/
theorem muSqEulerFactor_one (p : ℕ) (hp : 0 < p) :
    (1 : ℚ) - 2 / (p : ℚ) + 1 / (p : ℚ) ^ 2
      = (1 - 1 / (p : ℚ)) ^ 2 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hp0]
  ring

/-- The `s = 2` Euler factor controlling the finite-stage radial coefficient. -/
theorem muSqEulerFactor_two (p : ℕ) (hp : 0 < p) :
    (1 : ℚ) - 2 / (p : ℚ) ^ 2 + 1 / (p : ℚ) ^ 4
      = (1 - 1 / (p : ℚ) ^ 2) ^ 2 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hp0]
  ring

/-- The first nontrivial local convolution coefficient. -/
theorem sigmaPrimePow_firstDiff (p : ℕ) :
    sigmaPrimePow p 1 - 2 * sigmaPrimePow p 0 = (p : ℤ) - 1 := by
  simp [sigmaPrimePow]
  ring

/-- The `μ * μ` second difference converts the divisor-sum prime-power row
to the prime-power totient row. -/
theorem sigmaPrimePow_secondDiff (p e : ℕ) :
    sigmaPrimePow p (e + 2)
      - 2 * sigmaPrimePow p (e + 1)
      + sigmaPrimePow p e
      = (p : ℤ) ^ (e + 1) * ((p : ℤ) - 1) := by
  simp only [sigmaPrimePow]
  rw [show
    (∑ j ∈ Finset.range (e + 3), (p : ℤ) ^ j)
      = (∑ j ∈ Finset.range (e + 2), (p : ℤ) ^ j)
        + (p : ℤ) ^ (e + 2) by
          rw [Finset.sum_range_succ]]
  rw [show
    (∑ j ∈ Finset.range (e + 2), (p : ℤ) ^ j)
      = (∑ j ∈ Finset.range (e + 1), (p : ℤ) ^ j)
        + (p : ℤ) ^ (e + 1) by
          rw [Finset.sum_range_succ]]
  ring

end ErdosProblems.Erdos249.FiniteEulerSieve
