import Erdos249257.PowerTwoBitLift

/-!
# Centered-state meaning of one-bit lifting for Erdős #249

`PowerTwoBitLift` identifies the next binary bit with parity of the exact
quotient after a known divisibility.  The actual residual for #249 is phrased
instead in terms of `actualCenteredLift` and
`ActualPenultimateSignedMargin`.  This module closes that interface gap.

For a positive scale `M`, a multiple `z = M*q` has only two centered states
modulo `2*M`: zero when `q` is even, and the positive midpoint `M` when `q`
is odd.  A sub-edge correction cannot rescue the zero state.  Subject to the
natural midpoint margin budget, it always accepts the midpoint state.
Consequently the signed-margin socket is exactly the *failure* of the next
divisibility lift, rather than its success.

The results are universal integer geometry.  They do not assert that the
finite `t = 827` quotient supplies a cofinal family of actual states.
-/

namespace Erdos249257.DiagonalFreshLossBridge

/-- An even quotient puts its multiple at the zero centered state modulo
twice the known divisor. -/
theorem actualCenteredLift_mul_eq_zero_of_even
    {M q : ℤ} (hM : 0 < M) (hq : Even q) :
    actualCenteredLift (M * q) (2 * M) = 0 := by
  rcases hq with ⟨k, hk⟩
  have hmultiple : M * q = (2 * M) * k := by
    rw [hk]
    ring
  have hrem : (M * q) % (2 * M) = 0 := by
    rw [hmultiple]
    simp
  simp [actualCenteredLift, hrem, hM.le]

/-- An odd quotient puts its multiple at the positive midpoint centered state
modulo twice the known divisor. -/
theorem actualCenteredLift_mul_eq_midpoint_of_odd
    {M q : ℤ} (hM : 0 < M) (hq : Odd q) :
    actualCenteredLift (M * q) (2 * M) = M := by
  rcases hq with ⟨k, hk⟩
  have hdecomp : M * q = (2 * M) * k + M := by
    rw [hk]
    ring
  have hMlt : M < 2 * M := by omega
  have hrem : (M * q) % (2 * M) = M := by
    rw [hdecomp, Int.add_emod]
    simp [Int.emod_eq_of_lt hM.le hMlt]
  have hhalf : (2 * M) / 2 = M := by
    exact Int.mul_ediv_cancel_left M (by norm_num)
  simp [actualCenteredLift, hrem, hhalf]

/-- Exact centered-state classification after a known divisibility. -/
theorem actualCenteredLift_of_dvd_eq_ite_even
    {M z : ℤ} (hM : 0 < M) (hz : M ∣ z) :
    actualCenteredLift z (2 * M) =
      if Even (z / M) then 0 else M := by
  obtain ⟨q, rfl⟩ := hz
  have hquot : M * q / M = q := by
    exact Int.mul_ediv_cancel_left q hM.ne'
  rw [hquot]
  rcases Int.even_or_odd q with hq | hq
  · rw [if_pos hq]
    exact actualCenteredLift_mul_eq_zero_of_even hM hq
  · rw [if_neg (Int.not_even_iff_odd.mpr hq)]
    exact actualCenteredLift_mul_eq_midpoint_of_odd hM hq

/-- Under a sub-edge correction, the centered zero state cannot satisfy the
signed-margin socket. -/
theorem not_actualPenultimateSignedMargin_zero
    {e c : ℤ} (hc : |c| < e) :
    ¬ ActualPenultimateSignedMargin 0 c e := by
  rintro (⟨_, hmargin⟩ | ⟨hneg, _⟩)
  · simp only [abs_zero, mul_zero, zero_add, mul_zero] at hmargin
    omega
  · simp at hneg

/-- A positive midpoint satisfies the signed-margin socket whenever its
fourfold distance pays for the edge and the whole correction. -/
theorem actualPenultimateSignedMargin_midpoint
    {M e c : ℤ} (hM : 0 < M)
    (hbudget : e + |c| ≤ 4 * M) :
    ActualPenultimateSignedMargin M c e := by
  by_cases hc0 : 0 ≤ c
  · left
    constructor
    · exact mul_nonneg hM.le hc0
    · rw [abs_of_nonneg hc0] at hbudget
      rw [abs_of_nonneg hM.le, abs_of_nonneg hc0]
      omega
  · right
    have hcneg : c < 0 := lt_of_not_ge hc0
    constructor
    · exact mul_neg_of_pos_of_neg hM hcneg
    · rw [abs_of_nonneg hM.le]
      exact hbudget

/-- Main bridge: quotient oddness is exactly the signed-margin condition for
the centered lift modulo `2*M`, provided the correction is sub-edge and the
positive midpoint has enough margin. -/
theorem actualPenultimateSignedMargin_centeredLift_iff_quotient_odd
    {M z e c : ℤ} (hM : 0 < M) (hz : M ∣ z)
    (hc : |c| < e) (hbudget : e + |c| ≤ 4 * M) :
    ActualPenultimateSignedMargin (actualCenteredLift z (2 * M)) c e ↔
      Odd (z / M) := by
  rw [actualCenteredLift_of_dvd_eq_ite_even hM hz]
  rcases Int.even_or_odd (z / M) with hq | hq
  · rw [if_pos hq]
    constructor
    · exact fun h => (not_actualPenultimateSignedMargin_zero hc h).elim
    · exact fun hodd => (Int.not_even_iff_odd.mpr hodd hq).elim
  · rw [if_neg (Int.not_even_iff_odd.mpr hq)]
    constructor
    · exact fun _ => hq
    · exact fun _ => actualPenultimateSignedMargin_midpoint hM hbudget

/-- Divisibility version of the bridge: the signed margin is equivalent to
failure of the next factor-of-two lift. -/
theorem actualPenultimateSignedMargin_centeredLift_iff_not_twice_dvd
    {M z e c : ℤ} (hM : 0 < M) (hz : M ∣ z)
    (hc : |c| < e) (hbudget : e + |c| ≤ 4 * M) :
    ActualPenultimateSignedMargin (actualCenteredLift z (2 * M)) c e ↔
      ¬ 2 * M ∣ z := by
  rw [actualPenultimateSignedMargin_centeredLift_iff_quotient_odd
    hM hz hc hbudget]
  rw [← Int.not_even_iff_odd]
  obtain ⟨q, rfl⟩ := hz
  have hquot : M * q / M = q := by
    exact Int.mul_ediv_cancel_left q hM.ne'
  rw [hquot]
  constructor
  · intro hnotEven hdiv
    apply hnotEven
    exact (mul_two_dvd_mul_iff_even hM.ne').mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv)
  · intro hnotDiv hEven
    apply hnotDiv
    have hdiv := (mul_two_dvd_mul_iff_even hM.ne').mpr hEven
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv

/-! ## Concrete fourth-to-fifth-bit specialization -/

/-- At the `16`-to-`32` scale, the centered signed-margin socket is exactly
oddness of the fourth-bit quotient. -/
theorem actualPenultimateSignedMargin_centeredThirtyTwo_iff_quotient_odd
    {z e c : ℤ} (hz : (16 : ℤ) ∣ z)
    (hc : |c| < e) (hbudget : e + |c| ≤ 64) :
    ActualPenultimateSignedMargin (actualCenteredLift z 32) c e ↔
      Odd (z / 16) := by
  simpa using
    (actualPenultimateSignedMargin_centeredLift_iff_quotient_odd
      (M := (16 : ℤ)) (z := z) (e := e) (c := c)
      (by norm_num) hz hc (by norm_num at hbudget ⊢; exact hbudget))

/-- Equivalently, at the concrete scale it is precisely failure of the fifth
bit to vanish. -/
theorem actualPenultimateSignedMargin_centeredThirtyTwo_iff_not_thirtyTwo_dvd
    {z e c : ℤ} (hz : (16 : ℤ) ∣ z)
    (hc : |c| < e) (hbudget : e + |c| ≤ 64) :
    ActualPenultimateSignedMargin (actualCenteredLift z 32) c e ↔
      ¬ (32 : ℤ) ∣ z := by
  simpa using
    (actualPenultimateSignedMargin_centeredLift_iff_not_twice_dvd
      (M := (16 : ℤ)) (z := z) (e := e) (c := c)
      (by norm_num) hz hc (by norm_num at hbudget ⊢; exact hbudget))

#print axioms actualCenteredLift_of_dvd_eq_ite_even
#print axioms actualPenultimateSignedMargin_centeredLift_iff_quotient_odd
#print axioms actualPenultimateSignedMargin_centeredLift_iff_not_twice_dvd
#print axioms actualPenultimateSignedMargin_centeredThirtyTwo_iff_not_thirtyTwo_dvd

end Erdos249257.DiagonalFreshLossBridge
