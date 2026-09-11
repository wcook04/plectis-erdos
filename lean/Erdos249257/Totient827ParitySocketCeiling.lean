import Erdos249257.PowerTwoBitLift

/-!
# Parity does not decide the reduced Erdős #249 margin socket

`PowerTwoBitLift` isolates the fifth-bit question as parity of an integral
quotient.  The actual reduced margin socket asks for much more: a quotient
must be close to a multiple of a large even modulus.  This file records the
elementary obstruction precisely.  Under the numerical inequalities present
at the canonical `t = 827` row, each parity class contains both a point inside
the socket and a point outside it.

The result is deliberately abstract.  The current public Lean surface does
not expose the enormous `t = 827` margin constant, so no duplicate numeral is
introduced here.
-/

namespace Erdos249257

/-- The reduced signed-margin socket: `y` lies within strict radius `A / 16`
of some multiple of `m`, with the inequality kept integral. -/
def ReducedMarginSocket (m A y : ℤ) : Prop :=
  ∃ k : ℤ, 16 * |y - k * m| < A

/-- A midpoint of a positive even lattice is outside every socket whose
integral radius is strictly smaller than the midpoint distance. -/
theorem not_reducedMarginSocket_midpoint
    {r A : ℤ} (hr : 0 < r) (hA : A < 16 * r) :
    ¬ ReducedMarginSocket (2 * r) A r := by
  rintro ⟨k, hk⟩
  have habs : r ≤ |r - k * (2 * r)| := by
    by_cases hk0 : k ≤ 0
    · have hprod : k * (2 * r) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hk0 (by omega)
      rw [abs_of_nonneg (by omega)]
      omega
    · have hk1 : 1 ≤ k := by omega
      have hprod : 2 * r ≤ k * (2 * r) := by
        have := mul_le_mul_of_nonneg_right hk1 (by omega : 0 ≤ 2 * r)
        simpa using this
      rw [abs_of_nonpos (by omega)]
      omega
  have hscaled : 16 * r ≤ 16 * |r - k * (2 * r)| := by omega
  omega

/-- The successor of a midpoint is also outside when the radius is strictly
smaller than its distance `r - 1` from the next lattice point. -/
theorem not_reducedMarginSocket_midpoint_add_one
    {r A : ℤ} (hr : 1 ≤ r) (hA : A < 16 * r - 16) :
    ¬ ReducedMarginSocket (2 * r) A (r + 1) := by
  rintro ⟨k, hk⟩
  have habs : r - 1 ≤ |r + 1 - k * (2 * r)| := by
    by_cases hk0 : k ≤ 0
    · have hprod : k * (2 * r) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hk0 (by omega)
      rw [abs_of_nonneg (by omega)]
      omega
    · have hk1 : 1 ≤ k := by omega
      have hprod : 2 * r ≤ k * (2 * r) := by
        have := mul_le_mul_of_nonneg_right hk1 (by omega : 0 ≤ 2 * r)
        simpa using this
      rw [abs_of_nonpos (by omega)]
      omega
  have hscaled : 16 * (r - 1) ≤ 16 * |r + 1 - k * (2 * r)| := by omega
  omega

/-- Knowing only the parity of a reduced quotient cannot decide its margin
socket.  In each parity class there is both a socket hit and a socket miss.

The hits are `0` and `1`.  Writing the even modulus as `2*r`, the misses are
the adjacent central residues `r` and `r+1`; their parities are opposite, so
they cover the two classes in one order or the other. -/
theorem reducedMarginSocket_not_decided_by_parity
    {m A : ℤ} (hmEven : Even m) (hmPos : 0 < m)
    (h16A : 16 < A) (hA : A < 8 * m - 16) :
    (∃ yHit yMiss : ℤ,
        Even yHit ∧ Even yMiss ∧
          ReducedMarginSocket m A yHit ∧ ¬ ReducedMarginSocket m A yMiss) ∧
      (∃ yHit yMiss : ℤ,
        Odd yHit ∧ Odd yMiss ∧
          ReducedMarginSocket m A yHit ∧ ¬ ReducedMarginSocket m A yMiss) := by
  obtain ⟨r, hm⟩ := hmEven
  have hm' : m = 2 * r := by omega
  rw [hm'] at hmPos hA ⊢
  have hrPos : 0 < r := by omega
  have hrOne : 1 ≤ r := by omega
  have hA' : A < 16 * r - 16 := by nlinarith
  have hzero : ReducedMarginSocket (2 * r) A 0 := by
    refine ⟨0, ?_⟩
    norm_num
    omega
  have hone : ReducedMarginSocket (2 * r) A 1 := by
    refine ⟨0, ?_⟩
    simpa using h16A
  have hmid : ¬ ReducedMarginSocket (2 * r) A r :=
    not_reducedMarginSocket_midpoint hrPos (by omega)
  have hnext : ¬ ReducedMarginSocket (2 * r) A (r + 1) :=
    not_reducedMarginSocket_midpoint_add_one hrOne hA'
  rcases Int.even_or_odd r with hrEven | hrOdd
  · constructor
    · exact ⟨0, r, by norm_num, hrEven, hzero, hmid⟩
    · exact ⟨1, r + 1, by norm_num, hrEven.add_one, hone, hnext⟩
  · constructor
    · exact ⟨0, r + 1, by norm_num, hrOdd.add_one, hzero, hnext⟩
    · exact ⟨1, r, by norm_num, hrOdd, hone, hmid⟩

/-- Power-of-two specialization.  This is the form directly applicable to
the reduced modulus `2^1198` at the canonical `t = 827` row once its margin
constant is exported by the arithmetic certificate module. -/
theorem powerTwo_reducedMarginSocket_not_decided_by_parity
    {k : ℕ} {A : ℤ} (hk : 0 < k)
    (h16A : 16 < A) (hA : A < 8 * (2 : ℤ) ^ k - 16) :
    (∃ yHit yMiss : ℤ,
        Even yHit ∧ Even yMiss ∧
          ReducedMarginSocket ((2 : ℤ) ^ k) A yHit ∧
            ¬ ReducedMarginSocket ((2 : ℤ) ^ k) A yMiss) ∧
      (∃ yHit yMiss : ℤ,
        Odd yHit ∧ Odd yMiss ∧
          ReducedMarginSocket ((2 : ℤ) ^ k) A yHit ∧
            ¬ ReducedMarginSocket ((2 : ℤ) ^ k) A yMiss) := by
  apply reducedMarginSocket_not_decided_by_parity
  · exact Int.even_pow.mpr ⟨⟨1, rfl⟩, hk.ne'⟩
  · positivity
  · exact h16A
  · exact hA

#print axioms not_reducedMarginSocket_midpoint
#print axioms not_reducedMarginSocket_midpoint_add_one
#print axioms reducedMarginSocket_not_decided_by_parity
#print axioms powerTwo_reducedMarginSocket_not_decided_by_parity

end Erdos249257
