import ErdosProblems.Erdos68.FactorialCarry
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-!
# Erdős 68: factorial-channel certificates

This module formalizes the floor-factorial channel arithmetic and the first
exact finite subunit certificate from the primitive-cofactor return.
-/

namespace ErdosProblems.Erdos68

/-- The floor-factorial channel denominator divides the ambient factorial. -/
theorem factorial_pow_floor_dvd_factorial
    (i d : ℕ) (hd : 0 < d) :
    d.factorial ^ (i / d) ∣ i.factorial := by
  have hdiv : d ∣ d * (i / d) := dvd_mul_right d (i / d)
  have hpow :=
    factorial_pow_dvd_factorial_of_dvd hdiv
  have hquot : (d * (i / d)) / d = i / d := by
    simpa [Nat.mul_comm] using Nat.mul_div_left (i / d) hd
  rw [hquot] at hpow
  exact hpow.trans
    (Nat.factorial_dvd_factorial (by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self i d))

/-- Integral weight of index `i` in the divisor channel `d`. -/
def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))

/-- The floor-channel denominator cancels exactly. -/
theorem channelWeight_mul_denominator
    (i d : ℕ) (hd : 0 < d) :
    d.factorial ^ (i / d) * channelWeight i d =
      i.factorial := by
  exact Nat.mul_div_cancel'
    (factorial_pow_floor_dvd_factorial i d hd)

/-- Finite-support integer numerator in channel `d`. -/
def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)

/-- The factorial moment of a finite-support coefficient vector. -/
def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)

/-- Sparse recurrence event between consecutive channel columns. -/
def channelEvent (d n : ℕ) : ℤ :=
  n * (channelWeight (n - 1) d : ℤ) -
    (channelWeight n d : ℤ)

/-- Away from a divisor event, consecutive channel columns obey the exact
factorial recurrence. -/
theorem channelEvent_eq_zero_of_not_dvd
    {d n : ℕ} (hd : 2 ≤ d) (hnd : ¬ d ∣ n) :
    channelEvent d n = 0 := by
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    exact hnd (hn0 ▸ dvd_zero d)
  have hdpos : 0 < d := by omega
  have hmodNe : n % d ≠ 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using hnd
  have hmodPos : 0 < n % d := Nat.pos_of_ne_zero hmodNe
  have hmodLt : n % d < d := Nat.mod_lt n hdpos
  have hnrepr : n / d * d + n % d = n := by
    simpa [Nat.mul_comm] using Nat.div_add_mod n d
  have hfloor : (n - 1) / d = n / d := by
    apply Nat.div_eq_of_lt_le
    · simpa [Nat.mul_comm] using
        (show n / d * d ≤ n - 1 by omega)
    · rw [Nat.add_mul, one_mul]
      omega
  have hdenDvd :
      d.factorial ^ (n / d) ∣ (n - 1).factorial := by
    rw [← hfloor]
    exact factorial_pow_floor_dvd_factorial (n - 1) d hdpos
  have hfac : n.factorial = n * (n - 1).factorial := by
    have hn : n - 1 + 1 = n := by omega
    simpa only [hn] using Nat.factorial_succ (n - 1)
  have hweight :
      channelWeight n d = n * channelWeight (n - 1) d := by
    rw [channelWeight, channelWeight, hfloor, hfac]
    symm
    exact (Nat.mul_div_assoc n hdenDvd).symm
  simp [channelEvent, hweight]

/-- The first exact primitive-cofactor certificate, supported on indices
`3,4` with coefficients `2,-1`. -/
noncomputable def lambda34 : ℕ →₀ ℤ :=
  Finsupp.single 3 2 - Finsupp.single 4 1

@[simp]
theorem lambda34_apply_three : lambda34 3 = 2 := by
  simp [lambda34]

@[simp]
theorem lambda34_apply_four : lambda34 4 = -1 := by
  simp [lambda34]

theorem lambda34_channel_two :
    channelNumerator lambda34 2 = 0 := by
  classical
  rw [channelNumerator, lambda34,
    Finsupp.sum_sub_index (by intros; ring)]
  norm_num [channelWeight]

theorem lambda34_factorialMoment :
    factorialMoment lambda34 = -12 := by
  classical
  rw [factorialMoment, lambda34,
    Finsupp.sum_sub_index (by intros; ring)]
  norm_num

theorem lambda34_channel_three :
    channelNumerator lambda34 3 = -2 := by
  classical
  rw [channelNumerator, lambda34,
    Finsupp.sum_sub_index (by intros; ring)]
  norm_num [channelWeight]

theorem lambda34_channel_four :
    channelNumerator lambda34 4 = 11 := by
  classical
  rw [channelNumerator, lambda34,
    Finsupp.sum_sub_index (by intros; ring)]
  norm_num [channelWeight]

theorem lambda34_channel_ge_five
    (d : ℕ) (hd : 5 ≤ d) :
    channelNumerator lambda34 d = -12 := by
  have h3 : 3 / d = 0 := Nat.div_eq_of_lt (by omega)
  have h4 : 4 / d = 0 := Nat.div_eq_of_lt (by omega)
  classical
  rw [channelNumerator, lambda34,
    Finsupp.sum_sub_index (by intros; ring)]
  norm_num [channelWeight, h3, h4]

/-- The exact finite residual after isolating the infinite factorial tail. -/
def lambda34ResidualOfTail (theta : ℚ) : ℚ :=
  9 / 115 - 12 * theta

/-- The elementary factorial-tail enclosure from the return gives a strict
nonzero subunit residual for the `(3,4)` certificate. -/
theorem lambda34_residual_bounds
    (theta : ℚ)
    (hlower : 1 / 119 < theta)
    (hupper : theta < 1 / 50) :
    (-93 / 575 : ℚ) < lambda34ResidualOfTail theta ∧
      lambda34ResidualOfTail theta < (-309 / 13685 : ℚ) ∧
      -1 < lambda34ResidualOfTail theta ∧
      lambda34ResidualOfTail theta < 0 := by
  unfold lambda34ResidualOfTail
  norm_num at hlower hupper ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end ErdosProblems.Erdos68
