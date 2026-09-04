import ErdosProblems.Erdos1041.ClosePairCyclicQuotientCase

/-!
# Erdős #1041: the refined quintic close-pair kernel

The crude arbitrary-degree chord bound treats every nonselected root factor as
independently smaller than `2`.  For a quintic, the Hilbert-space chord
identity couples all three remaining factors to the selected pair distance.
If `y=t(1-t)d²`, the chord point has squared norm below `1-y`, so each remaining
factor is strictly below `1+sqrt(1-y)`.  The exact rational envelope

`y (1+sqrt(1-y))³ ≤ 31085/31104 < 1`

holds whenever `y≤5/36`, yielding the clean certificate `d²≤5/9`.
-/

namespace ErdosProblems.Erdos1041

/-- Strong convexity of squared complex norm along a chord, in exact form. -/
theorem complexChord_normSq_identity (a b : ℂ) (t : ℝ) :
    Complex.normSq ((((1 - t : ℝ) : ℂ) * a) + (t : ℂ) * b) =
      (1 - t) * Complex.normSq a + t * Complex.normSq b -
        t * (1 - t) * Complex.normSq (a - b) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

/-- Chord points between two open-unit-disk points have the strict radial
deficit supplied by their endpoint distance. -/
theorem complexChord_normSq_lt_one_sub
    {a b : ℂ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : Complex.normSq a < 1) (hb : Complex.normSq b < 1) :
    Complex.normSq ((((1 - t : ℝ) : ℂ) * a) + (t : ℂ) * b) <
      1 - t * (1 - t) * Complex.normSq (a - b) := by
  rw [complexChord_normSq_identity]
  have hleft : (1 - t) * Complex.normSq a ≤ (1 - t) * 1 :=
    mul_le_mul_of_nonneg_left ha.le (sub_nonneg.mpr ht1)
  by_cases htz : t = 0
  · simpa [htz] using ha
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htz)
    have hright : t * Complex.normSq b < t * 1 :=
      mul_lt_mul_of_pos_left hb htpos
    linarith

/-- The exact scalar envelope behind the improved quintic threshold.  In the
geometric application `s=sqrt(1-y)`; accepting `s²≤1-y` avoids making the
square-root API part of the trusted kernel. -/
theorem quintic_refined_chord_envelope
    {y s : ℝ}
    (hy0 : 0 ≤ y) (hyc : y ≤ (5 : ℝ) / 36)
    (hs0 : 0 ≤ s) (hsq : s ^ 2 ≤ 1 - y) :
    y * (1 + s) ^ 3 < 1 := by
  have hy1 : y ≤ 1 := by linarith
  have hcap0 : 0 ≤ 1 - y / 2 := by linarith
  have hcapSq : s ^ 2 ≤ (1 - y / 2) ^ 2 := by
    nlinarith [sq_nonneg y]
  have hsle : s ≤ 1 - y / 2 :=
    (sq_le_sq₀ hs0 hcap0).mp hcapSq
  have hsum0 : 0 ≤ 1 + s := by linarith
  have hsum : 1 + s ≤ 2 - y / 2 := by linarith
  have hpow : (1 + s) ^ 3 ≤ (2 - y / 2) ^ 3 :=
    pow_le_pow_left₀ hsum0 hsum 3
  have henvelope : y * (1 + s) ^ 3 ≤ y * (2 - y / 2) ^ 3 :=
    mul_le_mul_of_nonneg_left hpow hy0
  have hyfour : 0 ≤ y ^ 4 := by positivity
  have hpoly :
      y * (2 - y / 2) ^ 3 ≤ 8 * y - 6 * y ^ 2 + 3 * y ^ 3 / 2 := by
    nlinarith
  let c : ℝ := 5 / 36
  have hyc' : y ≤ c := by simpa [c] using hyc
  have hfactor :
      0 ≤ 8 - 6 * (c + y) + 3 * (c ^ 2 + c * y + y ^ 2) / 2 := by
    dsimp [c]
    nlinarith [sq_nonneg y]
  have hmaxSeed := mul_nonneg (sub_nonneg.mpr hyc') hfactor
  have hmax :
      8 * y - 6 * y ^ 2 + 3 * y ^ 3 / 2 ≤
        8 * c - 6 * c ^ 2 + 3 * c ^ 3 / 2 := by
    nlinarith
  have hc : 8 * c - 6 * c ^ 2 + 3 * c ^ 3 / 2 < 1 := by
    norm_num [c]
  exact lt_of_le_of_lt (henvelope.trans (hpoly.trans hmax)) hc

/-- If the selected quintic root pair has squared distance at most `5/9`,
the refined three-factor chord envelope is strictly below one at every chord
parameter. -/
theorem quintic_refined_closePair_factor_budget
    {d t s : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hd : d ^ 2 ≤ (5 : ℝ) / 9)
    (hs0 : 0 ≤ s)
    (hsq : s ^ 2 ≤ 1 - t * (1 - t) * d ^ 2) :
    t * (1 - t) * d ^ 2 * (1 + s) ^ 3 < 1 := by
  have htquarter : t * (1 - t) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (2 * t - 1)]
  have hy0 : 0 ≤ t * (1 - t) * d ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1)) (sq_nonneg d)
  have hscaled :
      t * (1 - t) * d ^ 2 ≤ ((1 : ℝ) / 4) * d ^ 2 :=
    mul_le_mul_of_nonneg_right htquarter (sq_nonneg d)
  have hyc : t * (1 - t) * d ^ 2 ≤ (5 : ℝ) / 36 := by
    nlinarith
  exact quintic_refined_chord_envelope hy0 hyc hs0 hsq

end ErdosProblems.Erdos1041
