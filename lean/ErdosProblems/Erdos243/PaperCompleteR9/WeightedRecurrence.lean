import ErdosProblems.Erdos243.PaperCompleteR9.CoefficientHeight

/-! The weighted endpoint follows from two consecutive zero errors; no
eventual division by the coefficient is used. -/
namespace ErdosProblems.Erdos243.PaperCompleteR9

theorem weighted_recurrence_of_zero_pair
    (a a' b b' L L' U U' ρ : ℤ) (hU : U ≠ 0)
    (hden : ρ * L' = a * L) (hnum : ρ * U' = U)
    (hzero : b * L = (a - 1) * U)
    (hzero' : b' * L' = (a' - 1) * U') :
    b * (a' - 1) = b' * a * (a - 1) := by
  apply mul_right_cancel₀ hU
  calc
    b * (a' - 1) * U = b * ρ * ((a' - 1) * U') := by rw [← hnum]; ring
    _ = b * ρ * (b' * L') := by rw [← hzero']
    _ = b' * a * (b * L) := by
      calc b * ρ * (b' * L') = b * b' * (ρ * L') := by ring
        _ = b * b' * (a * L) := by rw [hden]
        _ = b' * a * (b * L) := by ring
    _ = b' * a * (a - 1) * U := by rw [hzero]; ring

/-- The denominator identity is supplied by the actual lcm update. -/
theorem overlap_times_next_lcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    lcmOverlap q a n * cumulativeDigitLcm q a (n + 1) = a n * cumulativeDigitLcm q a n := by
  change Nat.gcd (cumulativeDigitLcm q a n) (a n) *
    Nat.lcm (cumulativeDigitLcm q a n) (a n) = a n * cumulativeDigitLcm q a n
  rw [Nat.gcd_mul_lcm, Nat.mul_comm]

/-- Full weighted recurrence from the same record-only bound, with no
coefficient nonvanishing premise and no supply hypothesis. -/
theorem coefficient_recurrence_of_record_bound
    (q : ℕ) (a U : ℕ → ℕ) (b V : ℕ → ℤ)
    (hq : 0 < q) (ha : ∀ n, 2 ≤ a n) (hU : ∀ n, 0 < U n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * (U (n + 1) : ℤ) = (U n : ℤ) - V n)
    (herror : ∀ n, V n = b n * (cumulativeDigitLcm q a n : ℤ) -
      ((a n : ℤ) - 1) * (U n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → IsStrictRecord U n → -(B : ℤ) ≤ V n)
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * (V n).natAbs < U n) :
    ∃ N, ∀ n, N ≤ n → b n * ((a (n + 1) : ℤ) - 1) =
      b (n + 1) * (a n : ℤ) * ((a n : ℤ) - 1) := by
  obtain ⟨N, hzero⟩ := coefficient_zero_of_record_bound q a U b V hq ha hU
    hstep herror hbound hvanish
  refine ⟨N, fun n hn ↦ ?_⟩
  apply weighted_recurrence_of_zero_pair
    (a n : ℤ) (a (n + 1) : ℤ) (b n) (b (n + 1))
    (cumulativeDigitLcm q a n : ℤ) (cumulativeDigitLcm q a (n + 1) : ℤ)
    (U n : ℤ) (U (n + 1) : ℤ) (lcmOverlap q a n : ℤ)
  · exact_mod_cast (Nat.ne_of_gt (hU n))
  · exact_mod_cast overlap_times_next_lcm q a n
  · simpa only [hzero n hn, sub_zero] using hstep n
  · have h := herror n
    rw [hzero n hn] at h
    omega
  · have h := herror (n + 1)
    rw [hzero (n + 1) (by omega)] at h
    omega

end ErdosProblems.Erdos243.PaperCompleteR9
