import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the three-prime running-LCM coordinate

This module starts the problem-owned formalization of the first unresolved
three-prime case. It records the exact computational height used by the
running-LCM representation, its cubic majorant, the smallest non-separation
fixture for `{2,3,5}`, and the variable-base tail-state update.

No declaration here asserts irrationality or transcendence of a three-prime
value. The missing producer is still an infinite residue-escape or genuinely
higher-dimensional analytic theorem.
-/

namespace ErdosProblems.Erdos269

/-- The `{p,q,r}`-smooth lattice point with exponent vector `(i,j,k)`. -/
def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

/-- The product of the largest pure `p`-, `q`-, and `r`-powers not exceeding
`x`. For a `{p,q,r}`-smooth `x`, this is the running LCM of the smooth prefix. -/
def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

/-- The exact rational lattice kernel attached to the running-LCM height. -/
def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

/-- Each pure-power component of the height is at most `x`, so the three-prime
height is bounded by `x³`. -/
theorem threePrimeHeight_le_cube
    (p q r x : ℕ) (hx : x ≠ 0) :
    threePrimeHeight p q r x ≤ x ^ 3 := by
  have hp := Nat.pow_log_le_self p hx
  have hq := Nat.pow_log_le_self q hx
  have hr := Nat.pow_log_le_self r hx
  calc
    threePrimeHeight p q r x
        ≤ (x * x) * x := Nat.mul_le_mul (Nat.mul_le_mul hp hq) hr
    _ = x ^ 3 := by ring

/-! The first exact `{2,3,5}` kernel values. -/

@[simp] theorem kernel_235_origin :
    threePrimeKernelQ 2 3 5 0 0 0 = 1 := by
  have h2 : Nat.log 2 1 = 0 := Nat.log_of_lt (by norm_num)
  have h3 : Nat.log 3 1 = 0 := Nat.log_of_lt (by norm_num)
  have h5 : Nat.log 5 1 = 0 := Nat.log_of_lt (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

@[simp] theorem kernel_235_two :
    threePrimeKernelQ 2 3 5 1 0 0 = 1 / 2 := by
  have h2 : Nat.log 2 2 = 1 := by
    simpa using Nat.log_pow (b := 2) (by norm_num : 1 < 2) 1
  have h3 : Nat.log 3 2 = 0 := Nat.log_of_lt (by norm_num)
  have h5 : Nat.log 5 2 = 0 := Nat.log_of_lt (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

@[simp] theorem kernel_235_three :
    threePrimeKernelQ 2 3 5 0 1 0 = 1 / 6 := by
  have h2 : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h3 : Nat.log 3 3 = 1 := by
    simpa using Nat.log_pow (b := 3) (by norm_num : 1 < 3) 1
  have h5 : Nat.log 5 3 = 0 := Nat.log_of_lt (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

@[simp] theorem kernel_235_six :
    threePrimeKernelQ 2 3 5 1 1 0 = 1 / 60 := by
  have h2 : Nat.log 2 6 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h3 : Nat.log 3 6 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h5 : Nat.log 5 6 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  norm_num [threePrimeKernelQ, threePrimeHeight, smooth3Val, h2, h3, h5]

/-- The smallest exact witness that the three-prime kernel is not rank one.
The two sides are `1/60` and `1/12`. -/
theorem kernel_235_not_rankOne :
    threePrimeKernelQ 2 3 5 0 0 0 *
        threePrimeKernelQ 2 3 5 1 1 0 ≠
      threePrimeKernelQ 2 3 5 1 0 0 *
        threePrimeKernelQ 2 3 5 0 1 0 := by
  norm_num

/-- One step of the exact variable-base tail orbit from the jump expansion. -/
def tailStateStep (base digit state : ℤ) : ℤ :=
  base * (state - digit)

theorem tailStateStep_eq (base digit state next : ℤ) :
    next = tailStateStep base digit state ↔
      next = base * state - base * digit := by
  simp [tailStateStep, mul_sub]

end ErdosProblems.Erdos269
