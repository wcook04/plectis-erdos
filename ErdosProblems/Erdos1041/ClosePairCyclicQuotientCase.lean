import ErdosProblems.Erdos1041.QuarticQuotientFiberCase

/-!
# Erdős #1041: the arbitrary-degree close-pair cyclic quotient case

For a monic quotient polynomial with `m` roots in the open unit disk, a chord
between two roots a distance `d` apart has its two endpoint factors bounded by
`t(1-t)d²` and every remaining factor strictly below `2`.  Hence the chord is
safe whenever

`2^(m-2) d² < 4`.

The analytic companion lifts that chord through `w = (z-h)^q`.  This module
kernel-checks the exact factor budget and composes the previously checked
root-lift endpoint budget with an arbitrary cyclic exponent.
-/

namespace ErdosProblems.Erdos1041

/-- The scalar factor budget behind the close-pair chord theorem.  The
`m - 2` factors not belonging to the selected pair are each bounded by `2` in
the analytic application. -/
theorem closePair_chord_factor_budget {m : ℕ} {d t : ℝ}
    (hd : 0 ≤ d)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hclose : (2 : ℝ) ^ (m - 2) * d ^ 2 < 4) :
    t * (1 - t) * d ^ 2 * (2 : ℝ) ^ (m - 2) < 1 := by
  have hA : t * (1 - t) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (2 * t - 1)]
  have hB0 : 0 ≤ (2 : ℝ) ^ (m - 2) * d ^ 2 := by positivity
  have hmul :
      t * (1 - t) * ((2 : ℝ) ^ (m - 2) * d ^ 2) ≤
        ((1 : ℝ) / 4) * ((2 : ℝ) ^ (m - 2) * d ^ 2) :=
    mul_le_mul_of_nonneg_right hA hB0
  have hquarter :
      ((1 : ℝ) / 4) * ((2 : ℝ) ^ (m - 2) * d ^ 2) < 1 := by
    nlinarith
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (lt_of_le_of_lt hmul hquarter)

/-- In quotient degree five, the transparent threshold is `d² < 1/2`, i.e.
`d < 1/sqrt 2` for a nonnegative distance. -/
theorem quintic_closePair_chord_factor_budget {d t : ℝ}
    (hd : 0 ≤ d)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hclose : d ^ 2 < (1 : ℝ) / 2) :
    t * (1 - t) * d ^ 2 * (2 : ℝ) ^ (5 - 2) < 1 := by
  apply closePair_chord_factor_budget hd ht0 ht1
  norm_num
  nlinarith

/-- The metric fan-in for an arbitrary positive cyclic exponent.  Once the
analytic chord lift has length at most the two powered endpoint moduli, the
strict constant-two conclusion is automatic. -/
theorem closePair_cyclicLift_length_lt_two
    {q : ℕ} {a b length : ℝ}
    (hq : 1 ≤ q)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hlength : length ≤ a ^ ((q : ℝ)⁻¹) + b ^ ((q : ℝ)⁻¹)) :
    length < 2 := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  exact rootLift_length_lt_two_of_le_endpoint_budget
    (inv_pos.mpr hqpos) ha0 ha1 hb0 hb1 hlength

end ErdosProblems.Erdos1041
