import Mathlib

/-!
Finite algebraic part of the Round-8 #1049 calibrated countermodel.
The positive measures, exact denominators, Hankel order, and fixed-base
asymptotic are separate obligations. This file proves only the source-specific
mass normalization and the finite telescope, with no axioms or `sorry`.
-/

namespace ErdosProblems.Erdos1049.Round8CalibratedFinite

open Finset

def c (k : ℕ) : ℚ := ((k + 1 : ℕ) : ℚ) ^ 2 * ((k + 2 : ℕ) : ℚ) / 2
def d (k : ℕ) : ℚ := ((k + 1 : ℕ) : ℚ) * ((k + 2 : ℕ) : ℚ) / 2

def rationalSeed (w : ℚ) : ℚ := (1 + 2 * w) / (1 - w) ^ 4

def tailSeed (q w : ℚ) : ℚ :=
  rationalSeed w - 12 * q / (1 - w) ^ 3 -
    ∑ k ∈ range 32, (c k - 12 * q * d k) * w ^ k

def initialWeight (q : ℚ) : ℚ :=
  1 - (∑ k ∈ range 31, c (k + 1) * q ^ (k + 1)) * (1 - q) ^ 32 -
    tailSeed q q

def seed (q w : ℚ) : ℚ :=
  initialWeight q + (∑ k ∈ range 31, c (k + 1) * w ^ (k + 1)) *
    (1 - q) ^ 32 + tailSeed q w

def mu (q : ℚ) (n : ℕ) : ℚ := seed q (q ^ (n + 1))
def nu (q : ℚ) (n : ℕ) : ℚ := mu q n - q * mu q (n + 1)
def partialSum (q : ℚ) (n : ℕ) : ℚ := ∑ m ∈ range n, q ^ m * nu q m

theorem seed_at_parameter (q : ℚ) : seed q q = 1 := by
  unfold seed initialWeight
  ring

theorem mu_zero (q : ℚ) : mu q 0 = 1 := by
  simpa [mu] using seed_at_parameter q

theorem finite_telescope (q : ℚ) (a : ℕ → ℚ) (n : ℕ) :
    ∑ m ∈ range n, q ^ m * (a m - q * a (m + 1)) =
      a 0 - q ^ n * a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih, pow_succ]
      ring

theorem calibrated_partial_error (q : ℚ) (n : ℕ) :
    1 - partialSum q n = q ^ n * mu q n := by
  unfold partialSum nu
  rw [finite_telescope, mu_zero]
  ring

#print axioms seed_at_parameter
#print axioms mu_zero
#print axioms finite_telescope
#print axioms calibrated_partial_error
#check seed_at_parameter
#check finite_telescope
#check calibrated_partial_error

end ErdosProblems.Erdos1049.Round8CalibratedFinite
