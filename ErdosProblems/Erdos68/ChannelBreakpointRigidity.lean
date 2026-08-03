import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Channel breakpoint rigidity for Erdős problem 68

For a finite coefficient family whose indices all lie in one quotient band
`[k d, (k + 1) d)`, every factorial coefficient is the same fixed multiple
`(d!)^k` of its `d`-channel coefficient.  Hence cancellation of that channel
forces cancellation of the factorial moment.  In the first band, a nonzero
factorial moment together with channel cancellation requires at least one
support index to reach the breakpoint `2d`.

The namespace `Erdos68` is the finite-family presentation; it is distinct
from the Finsupp presentation in `ErdosProblems.Erdos68`.  No declaration
constructs a cancelling coefficient family, treats several channels
simultaneously, estimates a residual, or decides rationality of the #68
series.
-/

namespace Erdos68

/-- Factorial-weighted sum of a finite coefficient family. -/
def factorialMoment {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial

/-- The integer numerator of the `d`-th divisor channel. -/
def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial / d.factorial ^ (index j / d) : ℕ)

/-- `k` labelled blocks of size `d` inject into their union, so `(d!)^k`
divides `(kd)!`.  This is the exact divisibility behind quotient-band
rigidity. -/
theorem factorial_pow_dvd_factorial_mul (d k : ℕ) :
    d.factorial ^ k ∣ (k * d).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hmul : d.factorial ^ k * d.factorial ∣
          (k * d).factorial * d.factorial := Nat.mul_dvd_mul ih (dvd_refl _)
      have hstep : (k * d).factorial * d.factorial ∣
          (k * d + d).factorial :=
        Nat.factorial_mul_factorial_dvd_factorial_add (k * d) d
      simpa [pow_succ, Nat.succ_mul] using hmul.trans hstep

/-- On any single quotient band `[kd, (k+1)d)`, the `d`-channel coefficient
is the factorial coefficient divided by the fixed integer `(d!)^k`. -/
theorem channel_coefficient_band
    {d i k : ℕ} (hlo : k * d ≤ i) (hhi : i < (k + 1) * d) :
    d.factorial ^ k * (i.factorial / d.factorial ^ (i / d)) = i.factorial := by
  have hdiv : i / d = k := by
    apply Nat.div_eq_of_lt_le
    · simpa [mul_comm] using hlo
    · simpa [mul_comm] using hhi
  rw [hdiv]
  exact Nat.mul_div_cancel'
    ((factorial_pow_dvd_factorial_mul d k).trans
      (Nat.factorial_dvd_factorial hlo))

/-- Inside the first quotient band `[d, 2d)`, the `d`-channel coefficient is
exactly the factorial coefficient divided by `d!`. -/
theorem channel_coefficient_firstBand
    {d i : ℕ} (hlo : d ≤ i) (hhi : i < 2 * d) :
    d.factorial * (i.factorial / d.factorial ^ (i / d)) = i.factorial := by
  simpa using channel_coefficient_band (d := d) (i := i) (k := 1)
    (by simpa using hlo) (by simpa using hhi)

/-- If all support indices lie in one quotient band for channel `d`, the
factorial moment is `(d!)^k` times that channel numerator. -/
theorem factorialMoment_eq_factorial_pow_mul_channelNumerator_band
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) (d k : ℕ)
    (hlo : ∀ j, k * d ≤ index j) (hhi : ∀ j, index j < (k + 1) * d) :
    factorialMoment coeff index =
      (d.factorial ^ k : ℤ) * channelNumerator coeff index d := by
  unfold factorialMoment channelNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hcoeff := channel_coefficient_band (hlo j) (hhi j)
  have hcast : ((index j).factorial : ℤ) =
      (d.factorial ^ k : ℤ) *
        ((index j).factorial / d.factorial ^ (index j / d) : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ℤ)) hcoeff.symm
  rw [hcast]
  ac_rfl

/-- Channel cancellation inside one quotient band forces the corresponding
factorial moment to vanish. -/
theorem factorialMoment_eq_zero_of_channelNumerator_eq_zero_band
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) (d k : ℕ)
    (hlo : ∀ j, k * d ≤ index j) (hhi : ∀ j, index j < (k + 1) * d)
    (hchannel : channelNumerator coeff index d = 0) :
    factorialMoment coeff index = 0 := by
  rw [factorialMoment_eq_factorial_pow_mul_channelNumerator_band
    coeff index d k hlo hhi, hchannel, mul_zero]

/-- In the first quotient band, the factorial moment is `d!` times the
`d`-channel numerator. -/
theorem factorialMoment_eq_factorial_mul_channelNumerator_firstBand
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ)
    (hlo : ∀ j, d ≤ index j) (hhi : ∀ j, index j < 2 * d) :
    factorialMoment coeff index =
      (d.factorial : ℤ) * channelNumerator coeff index d := by
  unfold factorialMoment channelNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hcoeff := channel_coefficient_firstBand (hlo j) (hhi j)
  have hcast : ((index j).factorial : ℤ) =
      (d.factorial : ℤ) *
        ((index j).factorial / d.factorial ^ (index j / d) : ℕ) := by
    rw [← Nat.cast_mul]
    exact congrArg (fun n : ℕ => (n : ℤ)) hcoeff.symm
  rw [hcast]
  ac_rfl

/-- First-band channel cancellation forces the factorial moment to vanish. -/
theorem factorialMoment_eq_zero_of_channelNumerator_eq_zero_firstBand
    {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ)
    (hlo : ∀ j, d ≤ index j) (hhi : ∀ j, index j < 2 * d)
    (hchannel : channelNumerator coeff index d = 0) :
    factorialMoment coeff index = 0 := by
  rw [factorialMoment_eq_factorial_mul_channelNumerator_firstBand
    coeff index d hlo hhi, hchannel, mul_zero]

/-- If every support index is at least `d`, channel cancellation and a nonzero
factorial moment force some support index to be at least `2d`. -/
theorem exists_index_ge_two_mul_of_factorialMoment_ne_zero_of_channel_eq_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ)
    (hlo : ∀ j, d ≤ index j)
    (hchannel : channelNumerator coeff index d = 0)
    (hmoment : factorialMoment coeff index ≠ 0) :
    ∃ j, 2 * d ≤ index j := by
  by_contra h
  have hhi : ∀ j, index j < 2 * d := by
    intro j
    exact Nat.lt_of_not_ge (fun hj => h ⟨j, hj⟩)
  exact hmoment (factorialMoment_eq_zero_of_channelNumerator_eq_zero_firstBand
    coeff index d hlo hhi hchannel)

end Erdos68
