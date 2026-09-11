import Erdos249257.DiagonalFreshLossBridge

/-!
# Exact one-bit lifting for the Erdős #249 signed-margin socket

`DiagonalFreshLossBridge` reduces the remaining power-of-two route to
`PowerTwoActualPenultimateSignedMarginSupply`.  Finite arithmetic at the
canonical `t = 827`, offset `1204` endpoint has already supplied four bits
of a relevant signed difference; the remaining finite question is the next
binary bit.  This module gives that statement its exact reusable form.

Once congruence modulo `2^k` is known, congruence modulo `2^(k+1)` is
equivalent to evenness of the exact quotient by `2^k`.  If the lift fails,
the residue is forced into the unique offset class `+2^k`.  The concrete
`16`-to-`32` specializations therefore reduce a fifth-bit certificate to one
cofactor-parity check, with no factorization or sign convention hidden in
the interface.

These are universal arithmetic theorems.  They do not promote the finite
`t = 827` evidence to a cofinal signed-margin supply.
-/

namespace Erdos249257

/-- Cancelling a nonzero common factor turns one extra factor of two into
parity of the remaining cofactor. -/
theorem mul_two_dvd_mul_iff_even {M q : ℤ} (hM : M ≠ 0) :
    M * 2 ∣ M * q ↔ Even q := by
  rw [mul_dvd_mul_iff_left hM]
  exact even_iff_two_dvd.symm

/-- Exact divisibility lift from `2^k` to `2^(k+1)`: after the known power of
two is divided out, only the parity of the integral quotient remains. -/
theorem two_pow_succ_dvd_iff_quotient_even
    {z : ℤ} {k : ℕ} (hk : (2 : ℤ) ^ k ∣ z) :
    (2 : ℤ) ^ (k + 1) ∣ z ↔ Even (z / (2 : ℤ) ^ k) := by
  have hpow : (2 : ℤ) ^ k ≠ 0 := by positivity
  have hz : (2 : ℤ) ^ k * (z / (2 : ℤ) ^ k) = z := by
    rw [mul_comm, Int.ediv_mul_cancel hk]
  calc
    (2 : ℤ) ^ (k + 1) ∣ z ↔
        (2 : ℤ) ^ k * 2 ∣ (2 : ℤ) ^ k * (z / (2 : ℤ) ^ k) := by
          rw [pow_succ, hz]
    _ ↔ Even (z / (2 : ℤ) ^ k) := mul_two_dvd_mul_iff_even hpow

/-- Congruence version of the exact one-bit lift. -/
theorem two_pow_succ_modEq_iff_quotient_even
    {x y : ℤ} {k : ℕ} (hk : Int.ModEq ((2 : ℤ) ^ k) x y) :
    Int.ModEq ((2 : ℤ) ^ (k + 1)) x y ↔
      Even ((y - x) / (2 : ℤ) ^ k) := by
  rw [Int.modEq_iff_dvd]
  exact two_pow_succ_dvd_iff_quotient_even hk.dvd

/-- A residue agreeing modulo `2^k` has exactly two possible classes modulo
`2^(k+1)`: the original class or its translate by `2^k`. -/
theorem two_pow_succ_modEq_or_offset
    {x y : ℤ} {k : ℕ} (hk : Int.ModEq ((2 : ℤ) ^ k) x y) :
    Int.ModEq ((2 : ℤ) ^ (k + 1)) x y ∨
      Int.ModEq ((2 : ℤ) ^ (k + 1)) x (y + (2 : ℤ) ^ k) := by
  let M : ℤ := (2 : ℤ) ^ k
  have hM : M ≠ 0 := by positivity
  obtain ⟨q, hq⟩ := hk.dvd
  rcases Int.even_or_odd q with hqEven | hqOdd
  · left
    rw [Int.modEq_iff_dvd, pow_succ]
    have hdiv : M * 2 ∣ M * q :=
      (mul_two_dvd_mul_iff_even hM).2 hqEven
    simpa [M, hq] using hdiv
  · right
    rw [Int.modEq_iff_dvd, pow_succ]
    have hdiv : M * 2 ∣ M * (q + 1) :=
      (mul_two_dvd_mul_iff_even hM).2 hqOdd.add_one
    have hnew : y + M - x = M * (q + 1) := by
      rw [show y + M - x = (y - x) + M by ring, hq]
      ring
    simpa [M, hnew] using hdiv

/-! ## The concrete fourth-to-fifth-bit socket -/

/-- If a signed difference is displayed as `16*c`, its fifth bit vanishes
exactly when the displayed cofactor is even. -/
theorem thirtyTwo_dvd_iff_even_sixteen_cofactor
    {z c : ℤ} (hz : z = 16 * c) :
    (32 : ℤ) ∣ z ↔ Even c := by
  subst z
  simpa using
    (mul_two_dvd_mul_iff_even (M := (16 : ℤ)) (q := c) (by norm_num))

/-- Quotient form of the `16`-to-`32` lift. -/
theorem thirtyTwo_dvd_iff_sixteen_quotient_even
    {z : ℤ} (hz : (16 : ℤ) ∣ z) :
    (32 : ℤ) ∣ z ↔ Even (z / 16) := by
  simpa using (two_pow_succ_dvd_iff_quotient_even (k := 4) hz)

/-- Fifth-bit agreement of two integers is exactly parity of their signed
fourth-bit quotient. -/
theorem modEq_thirtyTwo_iff_sixteen_quotient_even
    {x y : ℤ} (hxy : Int.ModEq 16 x y) :
    Int.ModEq 32 x y ↔ Even ((y - x) / 16) := by
  simpa using (two_pow_succ_modEq_iff_quotient_even (k := 4) hxy)

/-- Failure of the fifth-bit lift is exactly oddness of the same quotient. -/
theorem not_modEq_thirtyTwo_iff_sixteen_quotient_odd
    {x y : ℤ} (hxy : Int.ModEq 16 x y) :
    ¬ Int.ModEq 32 x y ↔ Odd ((y - x) / 16) := by
  rw [modEq_thirtyTwo_iff_sixteen_quotient_even hxy]
  exact Int.not_even_iff_odd

/-- Factor-certificate form adapted to a signed difference `P-N`; changing
the orientation of the difference does not change the parity test. -/
theorem modEq_thirtyTwo_iff_even_difference_cofactor
    {P N c : ℤ} (hfactor : P - N = 16 * c) :
    Int.ModEq 32 P N ↔ Even c := by
  rw [Int.modEq_iff_dvd]
  have hneg : N - P = 16 * (-c) := by
    rw [show N - P = -(P - N) by ring, hfactor]
    ring
  rw [thirtyTwo_dvd_iff_even_sixteen_cofactor hneg]
  simp

/-- Exhaustive concrete fifth-bit alternatives after fourth-bit agreement. -/
theorem modEq_thirtyTwo_or_offset_sixteen
    {x y : ℤ} (hxy : Int.ModEq 16 x y) :
    Int.ModEq 32 x y ∨ Int.ModEq 32 x (y + 16) := by
  simpa using (two_pow_succ_modEq_or_offset (k := 4) hxy)

/-- The offset class is not merely a possible failure class: under fourth-bit
agreement it is equivalent to failure of fifth-bit agreement. -/
theorem not_modEq_thirtyTwo_iff_offset_sixteen
    {x y : ℤ} (hxy : Int.ModEq 16 x y) :
    ¬ Int.ModEq 32 x y ↔ Int.ModEq 32 x (y + 16) := by
  constructor
  · intro hnot
    rcases modEq_thirtyTwo_or_offset_sixteen hxy with hsame | hoffset
    · exact (hnot hsame).elim
    · exact hoffset
  · intro hoffset hsame
    have hdiv : (32 : ℤ) ∣ 16 := by
      have hsub := dvd_sub hoffset.dvd hsame.dvd
      have heq : (y + 16 - x) - (y - x) = (16 : ℤ) := by ring
      rw [heq] at hsub
      exact hsub
    norm_num at hdiv

#print axioms two_pow_succ_dvd_iff_quotient_even
#print axioms two_pow_succ_modEq_or_offset
#print axioms modEq_thirtyTwo_iff_even_difference_cofactor
#print axioms not_modEq_thirtyTwo_iff_offset_sixteen

end Erdos249257
