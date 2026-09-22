import Mathlib

/-! UNRUN. Exact coefficient and denominator arithmetic in the cubic
classification. These declarations do not construct a number-field basis or
supply a prime-specialisation theorem. -/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- Coefficient comparison for reciprocal cubic factors, without division. -/
theorem reciprocal_cubic_coefficient_factor
    {K : Type*} [Field K] (b d w : K)
    (h5 : b * w + d = 0)
    (h4 : d * w + b * d + b = -w) :
    (b * w - 1) * (b + w) = 0 := by
  linear_combination (b + w) * h5 - h4

/-- The scale denominator leaves only the primitive pair (1,1). -/
theorem coprime_sumSquares_square_dvd48
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime r s) (hd : (r ^ 2 + s ^ 2) ^ 2 ∣ 48) :
    r = 1 ∧ s = 1 := by
  have hbound : (r ^ 2 + s ^ 2) ^ 2 ≤ 48 := Nat.le_of_dvd (by decide) hd
  have hnorm : r ^ 2 + s ^ 2 ≤ 6 := by
    by_contra hnot
    have hge : 7 ≤ r ^ 2 + s ^ 2 := by omega
    have hh := Nat.mul_le_mul hge hge
    nlinarith
  have hr1 : 1 ≤ r := hr
  have hs1 : 1 ≤ s := hs
  have hr2 : r ≤ 2 := by
    by_contra hnot
    have hge : 3 ≤ r := by omega
    have hh := Nat.mul_le_mul hge hge
    have hh' := Nat.mul_le_mul hs1 hs1
    nlinarith
  have hs2 : s ≤ 2 := by
    by_contra hnot
    have hge : 3 ≤ s := by omega
    have hh := Nat.mul_le_mul hge hge
    have hh' := Nat.mul_le_mul hr1 hr1
    nlinarith
  interval_cases r <;> interval_cases s <;> norm_num at *

/-- At either surviving rational parameter ±1, η=6c/m has m=12.
Signs are handled explicitly; m is required positive. -/
theorem scale_twelve_of_unit_parameter (m : ℕ) (c w : ℤ)
    (hm : 0 < m) (hc : c = 1 ∨ c = -1) (hw : w = 1 ∨ w = -1)
    (heq : (m : ℤ) * (w ^ 2 + 1) ^ 2 = 48 * c * w) : m = 12 := by
  rcases hc with rfl | rfl <;> rcases hw with rfl | rfl <;> norm_num at heq <;> omega

/-- All three coefficient equations imply the two exact cleared scale
relations.  Neither branch assumes the desired value of the scale. -/
theorem reciprocal_cubic_scale_relations
    {K : Type*} [Field K] (b d w η : K)
    (h5 : b * w + d = 0)
    (h4 : d * w + b * d + b = -w)
    (h3 : w ^ 2 + 1 + b ^ 2 + d ^ 2 = 8 * η * w) :
    (w ^ 2 + 1) ^ 2 = 8 * η * w ^ 3 ∨
      (w ^ 2 + 1) ^ 2 = 8 * η * w := by
  have hfactor := reciprocal_cubic_coefficient_factor b d w h5 h4
  rcases mul_eq_zero.mp hfactor with hb | hb
  · left
    have hd : d = -1 := by linear_combination h5 - hb
    rw [hd] at h3
    linear_combination w ^ 2 * h3 - (b * w + 1) * hb
  · right
    have hb' : b = -w := by linear_combination hb
    rw [hb'] at h5 h3
    have hd : d = w ^ 2 := by linear_combination h5
    rw [hd] at h3
    linear_combination h3

/-- The denominator in the rational parameterisation is coprime to both
parameter coordinates, not merely to a selected finite set of primes. -/
theorem coprime_sumSquares_coordinates (r s : ℕ) (hcop : Nat.Coprime r s) :
    Nat.Coprime (r ^ 2 + s ^ 2) r ∧ Nat.Coprime (r ^ 2 + s ^ 2) s := by
  have hrr : r ∣ r ^ 2 := ⟨r, by ring⟩
  have hss : s ∣ s ^ 2 := ⟨s, by ring⟩
  constructor
  · rw [Nat.add_coprime_iff_right hrr]
    exact hcop.symm.pow_left 2
  · rw [Nat.add_coprime_iff_left hss]
    exact hcop.pow_left 2

/-- Clear-denominator integrality supplies the divisibility by 48 used in
the scale classification.  This was previously only an unproved input to
the finite square-divisor theorem. -/
theorem cubic_scale_denominator_dvd48
    (m r s : ℕ) (hcop : Nat.Coprime r s)
    (heq : m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r ^ 3 * s ∨
      m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r * s ^ 3) :
    (r ^ 2 + s ^ 2) ^ 2 ∣ 48 := by
  obtain ⟨hr, hs⟩ := coprime_sumSquares_coordinates r s hcop
  rcases heq with heq | heq
  · have hc : Nat.Coprime ((r ^ 2 + s ^ 2) ^ 2) (r ^ 3 * s) :=
      Nat.coprime_mul_iff_right.mpr ⟨(hr.pow_left 2).pow_right 3, hs.pow_left 2⟩
    apply hc.dvd_of_dvd_mul_right
    refine ⟨m, ?_⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using heq.symm
  · have hc : Nat.Coprime ((r ^ 2 + s ^ 2) ^ 2) (r * s ^ 3) :=
      Nat.coprime_mul_iff_right.mpr ⟨hr.pow_left 2, (hs.pow_left 2).pow_right 3⟩
    apply hc.dvd_of_dvd_mul_right
    refine ⟨m, ?_⟩
    simpa only [mul_assoc, mul_comm, mul_left_comm] using heq.symm

/-- The entire positive-integer end of the rational scale calculation,
including production of the divisor condition, is now one theorem. -/
theorem cubic_scale_nat_classification
    (m r s : ℕ) (hr : 0 < r) (hs : 0 < s) (hcop : Nat.Coprime r s)
    (heq : m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r ^ 3 * s ∨
      m * (r ^ 2 + s ^ 2) ^ 2 = 48 * r * s ^ 3) :
    r = 1 ∧ s = 1 ∧ m = 12 := by
  have hd := cubic_scale_denominator_dvd48 m r s hcop heq
  obtain ⟨hr1, hs1⟩ := coprime_sumSquares_square_dvd48 r s hr hs hcop hd
  refine ⟨hr1, hs1, ?_⟩
  rw [hr1, hs1] at heq
  rcases heq with heq | heq <;> norm_num at heq <;> omega

end ErdosProblems.Erdos243.PaperCompleteR11
