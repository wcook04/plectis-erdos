import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Erdős #68: canonical factorial digits

For the factorial-denominator series

`sum (n >= 2), 1 / (n! - 1)`.

the natural factorial-scale floors give a mixed-radix digit expansion.  This
module develops that expansion for an arbitrary real number: the digits lie
in their canonical ranges, the fractional remainders satisfy the radix
recurrence, and every finite truncation has an explicit remainder term.

The construction is independent of the particular series.  Applied to
Erdős #68, it reduces the digit approach to proving that the canonical
remainder never enters a terminal zero tail.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- Floor of the `m!`-scaled real number. -/
noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋

/-- Canonical radix-`m` factorial digit selected by the floor convention. -/
noncomputable def canonicalDigit (x : ℝ) (m : ℕ) : ℤ :=
  facFloor x m - (m : ℤ) * facFloor x (m - 1)

/-- Fractional remainder after truncation at factorial scale `m!`. -/
noncomputable def canonicalRemainder (x : ℝ) (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * x - (facFloor x m : ℝ)

/-! ## Rational inputs

For a rational number `a / q`, factorial scaling is integral once `q ≤ n`.
Consequently the canonical digit at radix `n + 1` vanishes.  This is a
termination criterion for rational inputs; it does not assert that the Erdős
#68 series is rational or supply recurrence estimates for its partial sums. -/

/-- Once `q ≤ n`, the floor of `n! (a / q)` is the explicitly cleared
integer `(n! / q) a`. -/
theorem facFloor_rat_eq_cleared
    (a : ℤ) {q n : ℕ}
    (hq : 0 < q) (hqn : q ≤ n) :
    facFloor (((a : ℚ) / (q : ℚ)) : ℝ) n =
      ((n.factorial / q : ℕ) : ℤ) * a := by
  have hqfac : q ∣ n.factorial := Nat.dvd_factorial hq hqn
  have hq0 : (q : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hcastDiv : (((n.factorial / q : ℕ) : ℚ)) =
      (n.factorial : ℚ) / (q : ℚ) :=
    Nat.cast_div hqfac hq0
  have hscaledQ :
      ((n.factorial : ℚ) * ((a : ℚ) / (q : ℚ))) =
        (((n.factorial / q : ℕ) : ℤ) * a : ℤ) := by
    calc
      ((n.factorial : ℚ) * ((a : ℚ) / (q : ℚ))) =
          (a : ℚ) * ((n.factorial : ℚ) / (q : ℚ)) := by
        field_simp [hq0]
      _ = (a : ℚ) * ((n.factorial / q : ℕ) : ℚ) := by
        rw [hcastDiv]
      _ = ((((n.factorial / q : ℕ) : ℤ) * a : ℤ) : ℚ) := by
        have h := congrArg (fun z : ℤ => (z : ℚ))
          (mul_comm a ((n.factorial / q : ℕ) : ℤ))
        simpa only [Int.cast_mul, Int.cast_natCast] using h
  have hscaledR :
      (n.factorial : ℝ) * (((a : ℚ) / (q : ℚ)) : ℝ) =
        ((((n.factorial / q : ℕ) : ℤ) * a : ℤ) : ℝ) := by
    exact_mod_cast hscaledQ
  unfold facFloor
  rw [hscaledR]
  exact Int.floor_intCast _

/-- Every rational number has an eventually zero canonical factorial-digit
tail, with its displayed denominator as an explicit threshold. -/
theorem canonicalDigit_eq_zero_of_rational
    (a : ℤ) {q n : ℕ}
    (hq : 0 < q) (hqn : q ≤ n) :
    canonicalDigit (((a : ℚ) / (q : ℚ)) : ℝ) (n + 1) = 0 := by
  have hqfac : q ∣ n.factorial := Nat.dvd_factorial hq hqn
  have hdiv : (n + 1).factorial / q =
      (n + 1) * (n.factorial / q) := by
    rw [Nat.factorial_succ, Nat.mul_div_assoc _ hqfac]
  unfold canonicalDigit
  rw [Nat.add_sub_cancel]
  rw [facFloor_rat_eq_cleared a hq (by omega),
    facFloor_rat_eq_cleared a hq hqn, hdiv]
  push_cast
  ring

private theorem factorial_eq_mul_pred_factorial (m : ℕ) (hm : 1 ≤ m) :
    m.factorial = m * (m - 1).factorial := by
  have hmsucc : m - 1 + 1 = m := by omega
  calc
    m.factorial = (m - 1 + 1).factorial := by rw [hmsucc]
    _ = (m - 1 + 1) * (m - 1).factorial := Nat.factorial_succ _
    _ = m * (m - 1).factorial := by rw [hmsucc]

/-- The canonical remainder is the ordinary fractional part of `m! * x`. -/
theorem canonicalRemainder_eq_fract (x : ℝ) (m : ℕ) :
    canonicalRemainder x m = Int.fract ((m.factorial : ℝ) * x) := by
  rw [Int.fract]
  rfl

/-- Every canonical factorial remainder is nonnegative. -/
theorem canonicalRemainder_nonneg (x : ℝ) (m : ℕ) :
    0 ≤ canonicalRemainder x m := by
  unfold canonicalRemainder facFloor
  exact sub_nonneg.mpr (Int.floor_le _)

/-- Every canonical factorial remainder is strictly below one. -/
theorem canonicalRemainder_lt_one (x : ℝ) (m : ℕ) :
    canonicalRemainder x m < 1 := by
  unfold canonicalRemainder facFloor
  linarith [Int.lt_floor_add_one ((m.factorial : ℝ) * x)]

/-- The next digit is the floor of the current remainder multiplied by the
next radix. -/
theorem canonicalDigit_eq_floor_mul_remainder
    (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    canonicalDigit x m =
      ⌊(m : ℝ) * canonicalRemainder x (m - 1)⌋ := by
  have hfacNat := factorial_eq_mul_pred_factorial m hm
  have hfac :
      (m.factorial : ℝ) =
        (m : ℝ) * ((m - 1).factorial : ℝ) := by
    exact_mod_cast hfacNat
  unfold canonicalDigit canonicalRemainder facFloor
  rw [hfac]
  have hrewrite :
      (m : ℝ) *
          (((m - 1).factorial : ℝ) * x -
            (⌊((m - 1).factorial : ℝ) * x⌋ : ℝ)) =
        (m : ℝ) * ((m - 1).factorial : ℝ) * x -
          (((m : ℤ) * ⌊((m - 1).factorial : ℝ) * x⌋ : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hrewrite, Int.floor_sub_intCast]

/-- Canonical factorial digits are nonnegative. -/
theorem canonicalDigit_nonneg (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ canonicalDigit x m := by
  rw [canonicalDigit_eq_floor_mul_remainder x m hm]
  exact Int.floor_nonneg.mpr
    (mul_nonneg (by positivity) (canonicalRemainder_nonneg x (m - 1)))

/-- A canonical radix-`m` factorial digit is strictly smaller than `m`. -/
theorem canonicalDigit_lt_radix (x : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    canonicalDigit x m < (m : ℤ) := by
  rw [canonicalDigit_eq_floor_mul_remainder x m hm, Int.floor_lt]
  push_cast
  have hmPos : (0 : ℝ) < m := by positivity
  nlinarith [canonicalRemainder_lt_one x (m - 1)]

/-- Exact remainder recurrence: multiply by the next radix and subtract the
new canonical digit. -/
theorem canonicalRemainder_recurrence (x : ℝ) (m : ℕ) :
    canonicalRemainder x (m + 1) =
      (m + 1 : ℝ) * canonicalRemainder x m -
        (canonicalDigit x (m + 1) : ℝ) := by
  have hfacNat : (m + 1).factorial = (m + 1) * m.factorial :=
    Nat.factorial_succ m
  have hfac :
      ((m + 1).factorial : ℝ) =
        (m + 1 : ℝ) * (m.factorial : ℝ) := by
    exact_mod_cast hfacNat
  unfold canonicalRemainder canonicalDigit facFloor
  rw [Nat.add_sub_cancel, hfac]
  push_cast
  ring

/-- Telescoping step for the factorial expansion. -/
theorem canonicalRemainder_div_factorial_step (x : ℝ) (m : ℕ) :
    canonicalRemainder x m / (m.factorial : ℝ) =
      (canonicalDigit x (m + 1) : ℝ) / ((m + 1).factorial : ℝ) +
        canonicalRemainder x (m + 1) / ((m + 1).factorial : ℝ) := by
  have hfacNat : (m + 1).factorial = (m + 1) * m.factorial :=
    Nat.factorial_succ m
  have hfac :
      ((m + 1).factorial : ℝ) =
        (m + 1 : ℝ) * (m.factorial : ℝ) := by
    exact_mod_cast hfacNat
  unfold canonicalRemainder canonicalDigit facFloor
  rw [Nat.add_sub_cancel]
  push_cast
  rw [hfac]
  field_simp
  ring

/-- Exact finite canonical factorial expansion with an explicit remainder. -/
theorem factorial_expansion_partial (x : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    x =
      (⌊x⌋ : ℝ) +
        ∑ m ∈ Finset.Icc 2 N,
          (canonicalDigit x m : ℝ) / (m.factorial : ℝ) +
      canonicalRemainder x N / (N.factorial : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
      simp [canonicalRemainder, facFloor]
  | succ N hN ih =>
      have hIcc :
          Finset.Icc 2 (N + 1) =
            insert (N + 1) (Finset.Icc 2 N) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      calc
        x =
            (⌊x⌋ : ℝ) +
              ∑ m ∈ Finset.Icc 2 N,
                (canonicalDigit x m : ℝ) / (m.factorial : ℝ) +
            canonicalRemainder x N / (N.factorial : ℝ) := ih
        _ =
            (⌊x⌋ : ℝ) +
              ∑ m ∈ Finset.Icc 2 N,
                (canonicalDigit x m : ℝ) / (m.factorial : ℝ) +
            ((canonicalDigit x (N + 1) : ℝ) /
                ((N + 1).factorial : ℝ) +
              canonicalRemainder x (N + 1) /
                ((N + 1).factorial : ℝ)) := by
              rw [canonicalRemainder_div_factorial_step]
        _ =
            (⌊x⌋ : ℝ) +
              ((canonicalDigit x (N + 1) : ℝ) /
                  ((N + 1).factorial : ℝ) +
                ∑ m ∈ Finset.Icc 2 N,
                  (canonicalDigit x m : ℝ) / (m.factorial : ℝ)) +
            canonicalRemainder x (N + 1) /
              ((N + 1).factorial : ℝ) := by ring
        _ =
            (⌊x⌋ : ℝ) +
              ∑ m ∈ Finset.Icc 2 (N + 1),
                (canonicalDigit x m : ℝ) / (m.factorial : ℝ) +
            canonicalRemainder x (N + 1) /
              ((N + 1).factorial : ℝ) := by
              rw [hIcc, Finset.sum_insert (by simp)]

/-- A zero remainder forces the next digit and next remainder to vanish. -/
theorem zero_remainder_step (x : ℝ) (m : ℕ)
    (hzero : canonicalRemainder x m = 0) :
    canonicalDigit x (m + 1) = 0 ∧
      canonicalRemainder x (m + 1) = 0 := by
  have hdigit :
      canonicalDigit x (m + 1) = 0 := by
    rw [canonicalDigit_eq_floor_mul_remainder x (m + 1) (by omega)]
    simp [hzero]
  refine ⟨hdigit, ?_⟩
  rw [canonicalRemainder_recurrence, hzero, hdigit]
  norm_num

/-- Once a canonical remainder is zero, every later remainder is zero. -/
theorem zero_remainder_add (x : ℝ) (m k : ℕ)
    (hzero : canonicalRemainder x m = 0) :
    canonicalRemainder x (m + k) = 0 := by
  induction k with
  | zero =>
      simpa using hzero
  | succ k ih =>
      rw [Nat.add_succ]
      exact (zero_remainder_step x (m + k) ih).2

/-- A zero remainder is an exact certificate for a terminating factorial-digit
tail. -/
theorem zero_remainder_forces_zero_digit_tail (x : ℝ) (m : ℕ)
    (hzero : canonicalRemainder x m = 0) :
    ∀ r > m, canonicalDigit x r = 0 := by
  intro r hr
  have hrEq : r = m + (r - m - 1) + 1 := by omega
  rw [hrEq]
  exact (zero_remainder_step x (m + (r - m - 1))
    (zero_remainder_add x m (r - m - 1) hzero)).1

end ErdosProblems.Erdos68
