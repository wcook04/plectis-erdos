import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Shifted-factorial gcd identity for factorial-gap lcm estimates

If `P : ℕ → ℤ` is any integer sequence, two values `i! + P i` and
`j! + P j` can share a prime factor only through the integer
`P j - (j!/i!) (P i)`.  Integer polynomials are the case used in the
ordinary-proof lcm growth theorem; the identity itself does not need the
polynomial structure.  The unperturbed family `P = 0` makes the difference
vanish, so the identity is vacuous and the lcm collapses to `N!`.

The module does not prove the `N^{3/2} log N` liminf, does not decide
rationality of any series, and does not replace the Lean-checked
`n! - 1` segment bound already in `ChannelIntegralCongruence`.
-/

namespace ErdosProblems.Erdos68

theorem factorial_mul_div_of_le {i j : ℕ} (hij : i ≤ j) :
    i.factorial * (j.factorial / i.factorial) = j.factorial :=
  Nat.mul_div_cancel' (Nat.factorial_dvd_factorial hij)

private theorem shifted_factorial_linear_combo
    (P : ℕ → ℤ) {i j : ℕ} (hij : i ≤ j) :
    (↑(j.factorial / i.factorial) : ℤ) * ((i.factorial : ℤ) + P i)
        - ((j.factorial : ℤ) + P j) =
      (↑(j.factorial / i.factorial) : ℤ) * P i - P j := by
  set Q := j.factorial / i.factorial
  have hQ : (i.factorial : ℤ) * (Q : ℤ) = (j.factorial : ℤ) := by
    exact_mod_cast factorial_mul_div_of_le hij
  have hQ' : (Q : ℤ) * (i.factorial : ℤ) = (j.factorial : ℤ) := by
    simpa [mul_comm] using hQ
  calc
    (Q : ℤ) * ((i.factorial : ℤ) + P i) - ((j.factorial : ℤ) + P j)
        = (Q : ℤ) * (i.factorial : ℤ) + (Q : ℤ) * P i
            - (j.factorial : ℤ) - P j := by ring
    _ = (j.factorial : ℤ) + (Q : ℤ) * P i - (j.factorial : ℤ) - P j := by
        rw [hQ']
    _ = (Q : ℤ) * P i - P j := by ring

/-- Two shifted factorials collide only through the explicit integer
`P j - (j!/i!) (P i)`. -/
theorem int_gcd_eval_shifted_factorial_dvd
    (P : ℕ → ℤ) {i j : ℕ} (hij : i < j) :
    (Int.gcd ((i.factorial : ℤ) + P i) ((j.factorial : ℤ) + P j) : ℤ) ∣
      P j - (↑(j.factorial / i.factorial) : ℤ) * P i := by
  set a := (i.factorial : ℤ) + P i
  set b := (j.factorial : ℤ) + P j
  set Q := j.factorial / i.factorial
  have hcomb : (Q : ℤ) * a - b = (Q : ℤ) * P i - P j := by
    simpa [a, b, Q] using shifted_factorial_linear_combo P hij.le
  have hdiv : (Int.gcd a b : ℤ) ∣ (Q : ℤ) * a - b :=
    Int.dvd_sub (Int.dvd_mul_of_dvd_right (Int.gcd_dvd_left a b))
      (Int.gcd_dvd_right a b)
  have htarget : P j - (Q : ℤ) * P i = -((Q : ℤ) * a - b) := by
    rw [hcomb]
    ring
  rw [htarget, Int.dvd_neg]
  exact hdiv

/-- Constant-shift specialisation: `gcd(i!+t, j!+t)` divides
`t ((j!/i!) - 1)`.  The factorial-gap case `t = -1` recovers a multiple of
the already-checked identity `gcd(i!-1, j!-1) ∣ (j!/i!) - 1`. -/
theorem int_gcd_shifted_factorial_dvd
    (t : ℤ) {i j : ℕ} (hij : i < j) :
    (Int.gcd ((i.factorial : ℤ) + t) ((j.factorial : ℤ) + t) : ℤ) ∣
      t * ((↑(j.factorial / i.factorial) : ℤ) - 1) := by
  have h := int_gcd_eval_shifted_factorial_dvd (fun _ => t) hij
  have hform :
      t * ((↑(j.factorial / i.factorial) : ℤ) - 1) =
        -(t - (↑(j.factorial / i.factorial) : ℤ) * t) := by
    ring
  rw [hform, Int.dvd_neg]
  exact h

/-- The unperturbed family makes the collision difference vanish, so the
gcd identity supplies no lcm gain: `lcm_{n ≤ N} n! = N!`. -/
theorem int_gcd_unperturbed_factorial
    {i j : ℕ} (hij : i ≤ j) :
    Int.gcd (i.factorial : ℤ) (j.factorial : ℤ) = i.factorial := by
  rw [Int.gcd_natCast_natCast, Nat.gcd_eq_left]
  exact Nat.factorial_dvd_factorial hij

theorem eval_shifted_collision_eq_zero_of_zero
    {i j : ℕ} :
    (0 : ℤ) - (↑(j.factorial / i.factorial) : ℤ) * (0 : ℤ) = 0 := by
  simp

#print axioms int_gcd_eval_shifted_factorial_dvd
#print axioms int_gcd_shifted_factorial_dvd
#print axioms int_gcd_unperturbed_factorial

end ErdosProblems.Erdos68
