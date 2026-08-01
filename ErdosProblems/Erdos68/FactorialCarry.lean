import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

open scoped BigOperators

/-!
# Erdős #68: factorial carries and prime windows

For

`S = ∑ n ≥ 2, 1 / (n! - 1)`,

expanding each summand geometrically and regrouping by `m = n * j`
produces the integral coefficient

`C_m = ∑_{d ∣ m, 2 ≤ d} m! / (d!)^(m/d)`.

This module begins the kernel-checked arithmetic layer of that reduction.  It
proves the multinomial divisibility behind integrality and isolates the exact
prime-window consumer.  The remaining producer is an unbounded supply of
missed windows for the actual centres and radii; no irrationality conclusion
is claimed here.
-/

namespace ErdosProblems.Erdos68

/-- Every summand in the factorial-divisor coefficient is integral. -/
theorem factorial_pow_dvd_factorial_of_dvd
    {d m : ℕ} (hd : d ∣ m) :
    d.factorial ^ (m / d) ∣ m.factorial := by
  have h := Nat.prod_factorial_dvd_factorial_sum
    (Finset.range (m / d)) (fun _ : ℕ => d)
  simpa [Finset.prod_const, Finset.sum_const, Nat.div_mul_cancel hd] using h

/-- Divisor-regrouped coefficient in the factorial expansion of Erdős #68. -/
def factorialCoeff (m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors.filter (fun d => 2 ≤ d),
    m.factorial / (d.factorial ^ (m / d))

/-- Every selected quotient in `factorialCoeff` cancels exactly. -/
theorem factorialCoeff_summand_mul
    {d m : ℕ} (hd : d ∈ m.divisors.filter (fun d => 2 ≤ d)) :
    d.factorial ^ (m / d) *
        (m.factorial / (d.factorial ^ (m / d))) = m.factorial := by
  have hdm : d ∣ m :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  exact Nat.mul_div_cancel'
    (factorial_pow_dvd_factorial_of_dvd hdm)

/-- The residue target at prime dilation `k * p`. -/
def primeDilationResidue (k : ℕ) : ℕ :=
  ∑ d ∈ k.divisors,
    k.factorial / (d.factorial ^ (k / d))

/-- A rational interval of length `U` meets one prescribed residue class
modulo `p`.  This is the exact finite predicate consumed by the #68 reduction. -/
def WindowHit (F U : ℚ) (p : ℕ) (a : ℤ) : Prop :=
  ∃ z : ℤ,
    Int.ModEq p z a ∧ F < z ∧ (z : ℚ) ≤ F + U

/-- An integral carry with the required congruence and real enclosure supplies
the corresponding prime-window hit. -/
theorem windowHit_of_integral_carry
    {F U : ℚ} {p : ℕ} {a z : ℤ}
    (hmod : Int.ModEq p z a)
    (hlower : F < z)
    (hupper : (z : ℚ) ≤ F + U) :
    WindowHit F U p a :=
  ⟨z, hmod, hlower, hupper⟩

/-- A single missed window excludes every integral carry satisfying both its
residue law and its exact enclosure. -/
theorem no_integral_carry_of_windowMiss
    {F U : ℚ} {p : ℕ} {a : ℤ}
    (hmiss : ¬ WindowHit F U p a) :
    ¬ ∃ z : ℤ,
      Int.ModEq p z a ∧ F < z ∧ (z : ℚ) ≤ F + U := by
  simpa [WindowHit] using hmiss

/-- If the interval radius is less than one, it contains at most one integer. -/
theorem integer_unique_in_short_window
    {F U : ℚ} (hU : U < 1) {z w : ℤ}
    (hzLower : F < z) (hzUpper : (z : ℚ) ≤ F + U)
    (hwLower : F < w) (hwUpper : (w : ℚ) ≤ F + U) :
    z = w := by
  by_contra hzw
  rcases lt_or_gt_of_ne hzw with hlt | hgt
  · have hsepZ : z + 1 ≤ w := by omega
    have hsepQ : (z : ℚ) + 1 ≤ (w : ℚ) := by exact_mod_cast hsepZ
    linarith
  · have hsepZ : w + 1 ≤ z := by omega
    have hsepQ : (w : ℚ) + 1 ≤ (z : ℚ) := by exact_mod_cast hsepZ
    linarith

end ErdosProblems.Erdos68
