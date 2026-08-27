import ErdosProblems.Erdos1041.PrimitiveQuinticBoundaryTail

/-!
# Erdős #1041: primitive-quintic closed-disk tails

The boundary cubic separator has a harmonic extension to the open unit disk.
Its sum over the five roots is still exactly `5 - 2 * r`, because only the
first three Newton sums occur.  A root whose full tail energy is at least one
contributes at most `2 / 31`, whereas an arbitrary disk point contributes at
most `4 - 2 * r`.  Four unsafe roots therefore miss the exact separator mass
by at least `23 / 31`.

This file formalizes the finite real-algebraic core, including the zero-`a`
closed-disk equality case.  The companion note derives its hypotheses from
the roots of the primitive sparse quintic `z^5 + a*z^4 + b*z + c` after
rotating `a` to a nonnegative real number.
-/

namespace ErdosProblems.Erdos1041

/-- Real-coordinate form of the harmonic extension of the boundary
separator.  Here `x = re z` and `s = |z|^2`. -/
noncomputable def primitiveInteriorHarmonicSeparator (r x s : ℝ) : ℝ :=
  primitiveBoundarySeparator r x +
    (1 - s) * (1 - r / 4 - 3 * x / 4)

/-- The harmonic separator still has total mass `5 - 2*r` under the first
three interior Newton-moment identities. -/
theorem primitiveInteriorHarmonicSeparator_sum
    {r : ℝ}
    {x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : ℝ}
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : (2 * x0 ^ 2 - s0) + (2 * x1 ^ 2 - s1) +
        (2 * x2 ^ 2 - s2) + (2 * x3 ^ 2 - s3) +
        (2 * x4 ^ 2 - s4) = r ^ 2)
    (hm3 : (4 * x0 ^ 3 - 3 * s0 * x0) +
        (4 * x1 ^ 3 - 3 * s1 * x1) +
        (4 * x2 ^ 3 - 3 * s2 * x2) +
        (4 * x3 ^ 3 - 3 * s3 * x3) +
        (4 * x4 ^ 3 - 3 * s4 * x4) = -r ^ 3) :
    primitiveInteriorHarmonicSeparator r x0 s0 +
        primitiveInteriorHarmonicSeparator r x1 s1 +
        primitiveInteriorHarmonicSeparator r x2 s2 +
        primitiveInteriorHarmonicSeparator r x3 s3 +
        primitiveInteriorHarmonicSeparator r x4 s4 = 5 - 2 * r := by
  simp only [primitiveInteriorHarmonicSeparator,
    primitiveBoundarySeparator]
  nlinarith

/-- The disk maximum of the harmonic separator is the boundary value
`4 - 2*r`.  The proof is purely algebraic in `x = re z` and
`s = |z|^2`; `x^2 <= s <= 1` is the real-coordinate disk constraint. -/
theorem primitiveInteriorHarmonicSeparator_le_single
    {r x s : ℝ} (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hxs : x ^ 2 ≤ s) :
    primitiveInteriorHarmonicSeparator r x s ≤ 4 - 2 * r := by
  have hxsone : x ^ 2 ≤ 1 := le_trans hxs hs1
  have hxlo : -1 ≤ x := by nlinarith [sq_nonneg (x + 1)]
  have hxhi : x ≤ 1 := by nlinarith [sq_nonneg (x - 1)]
  let A : ℝ := 1 - r / 4 - 3 * x / 4
  by_cases hA : 0 ≤ A
  · have hdefect : 1 - s ≤ 1 - x ^ 2 := by linarith
    have hcorr : (1 - s) * A ≤ (1 - x ^ 2) * A :=
      mul_le_mul_of_nonneg_right hdefect hA
    have hp1 : 0 ≤ (r - 2) * (x - 5) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have hp2 : 0 ≤ (1 - x) * (2 - x) :=
      mul_nonneg (by linarith) (by linarith)
    have hB : 0 ≤ r * x - 5 * r + x ^ 2 - 5 * x + 12 := by
      nlinarith
    have hprod :
        0 ≤ (x + 1) * (r * x - 5 * r + x ^ 2 - 5 * x + 12) :=
      mul_nonneg (by linarith) hB
    have hid :
        (4 - 2 * r) -
            (primitiveBoundarySeparator r x + (1 - x ^ 2) * A) =
          (x + 1) * (r * x - 5 * r + x ^ 2 - 5 * x + 12) / 4 := by
      simp only [primitiveBoundarySeparator, A]
      ring
    change primitiveBoundarySeparator r x + (1 - s) * A ≤ 4 - 2 * r
    nlinarith
  · have hAnonpos : A ≤ 0 := le_of_not_ge hA
    have hdefect0 : 0 ≤ 1 - s := by linarith
    have hcorr : (1 - s) * A ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdefect0 hAnonpos
    have hboundary :=
      primitiveBoundarySeparator_le_single hr0 hr2 hxlo hxhi
    change primitiveBoundarySeparator r x + (1 - s) * A ≤ 4 - 2 * r
    nlinarith

/-- The quantitative interior gain.  If the full root-tail energy
`s^4 * (s + r^2 + 2*r*x)` is unsafe, the harmonic separator is at most
`2/31`. -/
theorem primitiveInteriorHarmonicSeparator_le_of_tailEnergy_ge_one
    {r x s : ℝ} (hr : 0 < r) (hr2 : r < 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hxhi : x ≤ 1)
    (hunsafe : 1 ≤ s ^ 4 * (s + r ^ 2 + 2 * r * x)) :
    primitiveInteriorHarmonicSeparator r x s ≤ 2 / 31 := by
  have hspos : 0 < s := by
    by_contra hnot
    have hsle : s ≤ 0 := le_of_not_gt hnot
    have hs : s = 0 := le_antisymm hsle hs0
    subst s
    norm_num at hunsafe
  have hs4pos : 0 < s ^ 4 := pow_pos hspos 4
  have h4le3 : s ^ 4 ≤ s ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hs0 3) (sub_nonneg.mpr hs1)]
  have h3le2 : s ^ 3 ≤ s ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs1)]
  have h2les : s ^ 2 ≤ s := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hs4le2 : s ^ 4 ≤ s ^ 2 := le_trans h4le3 h3le2
  have hs4les : s ^ 4 ≤ s := le_trans hs4le2 h2les
  have hs4le1 : s ^ 4 ≤ 1 := le_trans hs4les hs1
  have hseries :
      5 * s ^ 4 ≤ 1 + s + s ^ 2 + s ^ 3 + s ^ 4 := by
    linarith
  let d : ℝ := x + r / 2
  have htailRewrite :
      s ^ 4 * (s + r ^ 2 + 2 * r * x) =
        s ^ 5 + 2 * r * d * s ^ 4 := by
    simp only [d]
    ring
  rw [htailRewrite] at hunsafe
  have hfactor :
      (1 - s) * (1 + s + s ^ 2 + s ^ 3 + s ^ 4) = 1 - s ^ 5 := by
    ring
  have hdefect0 : 0 ≤ 1 - s := by linarith
  have hseriesMul := mul_le_mul_of_nonneg_left hseries hdefect0
  have hscaled :
      5 * (1 - s) * s ^ 4 ≤ 2 * r * d * s ^ 4 := by
    nlinarith
  have hscaled' :
      (5 * (1 - s)) * s ^ 4 ≤ (2 * r * d) * s ^ 4 := by
    nlinarith
  have hdelta : 5 * (1 - s) ≤ 2 * r * d := by
    by_contra hnot
    have hgt : 2 * r * d < 5 * (1 - s) := lt_of_not_ge hnot
    have hmulgt :
        (2 * r * d) * s ^ 4 < (5 * (1 - s)) * s ^ 4 :=
      mul_lt_mul_of_pos_right hgt hs4pos
    linarith
  have hd0 : 0 ≤ d := by
    by_contra hnot
    have hdneg : d < 0 := lt_of_not_ge hnot
    have h2rpos : 0 < 2 * r := mul_pos (by norm_num) hr
    have hright : 2 * r * d < 0 := mul_neg_of_pos_of_neg h2rpos hdneg
    have hleft : 0 ≤ 5 * (1 - s) := by positivity
    linarith
  let A : ℝ := 1 - r / 4 - 3 * x / 4
  let u : ℝ := 1 - x
  have hsepRewrite :
      primitiveInteriorHarmonicSeparator r x s =
        -d * u ^ 2 + (1 - s) * A := by
    simp only [primitiveInteriorHarmonicSeparator,
      primitiveBoundarySeparator, d, u, A]
    ring
  by_cases hA : 0 < A
  · have hdeltaA :
        (5 * (1 - s)) * A ≤ (2 * r * d) * A :=
      mul_le_mul_of_nonneg_right hdelta hA.le
    have hcorr :
        (1 - s) * A ≤ ((2 * r / 5) * d) * A := by
      nlinarith
    let P : ℝ := -u ^ 2 + (2 * r / 5) * A
    have hsepP : primitiveInteriorHarmonicSeparator r x s ≤ d * P := by
      rw [hsepRewrite]
      simp only [P]
      nlinarith
    let D : ℝ := d - 38 / 31
    let U : ℝ := u - 3 / 31
    have hsos :
        0 ≤ (2 / 5 : ℝ) * (D + U / 4) ^ 2 +
          (31 / 40 : ℝ) * U ^ 2 := by positivity
    have hPid :
        (1 / 31 : ℝ) - P =
          (2 / 5 : ℝ) * (D + U / 4) ^ 2 +
            (31 / 40 : ℝ) * U ^ 2 := by
      simp only [P, D, U, d, u, A]
      ring
    have hPcap : P ≤ (1 / 31 : ℝ) := by nlinarith
    have hd2 : d ≤ 2 := by
      simp only [d]
      linarith
    by_cases hP : 0 ≤ P
    · have hdP : d * P ≤ (2 / 31 : ℝ) := calc
        d * P ≤ 2 * P := mul_le_mul_of_nonneg_right hd2 hP
        _ ≤ 2 * (1 / 31 : ℝ) :=
          mul_le_mul_of_nonneg_left hPcap (by norm_num)
        _ = 2 / 31 := by norm_num
      exact le_trans hsepP hdP
    · have hPnonpos : P ≤ 0 := le_of_not_ge hP
      have hdPnonpos : d * P ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hd0 hPnonpos
      exact le_trans hsepP (le_trans hdPnonpos (by norm_num))
  · have hAnonpos : A ≤ 0 := le_of_not_gt hA
    have hqnonpos : -d * u ^ 2 ≤ 0 := by
      calc
        -d * u ^ 2 = -(d * u ^ 2) := by ring
        _ ≤ 0 := neg_nonpos.mpr (mul_nonneg hd0 (sq_nonneg u))
    have hcorrnonpos : (1 - s) * A ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdefect0 hAnonpos
    rw [hsepRewrite]
    exact le_trans (add_nonpos hqnonpos hcorrnonpos) (by norm_num)

/-- Five energies contain two strict safe entries when every score has a
global cap, every unsafe entry has the sharper cap, and the total beats both
the one-safe and zero-safe extrema. -/
theorem five_exists_two_lt_one_of_score_caps
    {e0 e1 e2 e3 e4 h0 h1 h2 h3 h4 M U : ℝ}
    (hh0 : h0 ≤ M) (hh1 : h1 ≤ M) (hh2 : h2 ≤ M)
    (hh3 : h3 ≤ M) (hh4 : h4 ≤ M)
    (hu0 : 1 ≤ e0 → h0 ≤ U) (hu1 : 1 ≤ e1 → h1 ≤ U)
    (hu2 : 1 ≤ e2 → h2 ≤ U) (hu3 : 1 ≤ e3 → h3 ≤ U)
    (hu4 : 1 ≤ e4 → h4 ≤ U)
    (hone : M + 4 * U < h0 + h1 + h2 + h3 + h4) :
    (e0 < 1 ∧ e1 < 1) ∨ (e0 < 1 ∧ e2 < 1) ∨
      (e0 < 1 ∧ e3 < 1) ∨ (e0 < 1 ∧ e4 < 1) ∨
      (e1 < 1 ∧ e2 < 1) ∨ (e1 < 1 ∧ e3 < 1) ∨
      (e1 < 1 ∧ e4 < 1) ∨ (e2 < 1 ∧ e3 < 1) ∨
      (e2 < 1 ∧ e4 < 1) ∨ (e3 < 1 ∧ e4 < 1) := by
  by_contra htwo
  push Not at htwo
  rcases htwo with
    ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  by_cases he0 : e0 < 1
  · have he1 : 1 ≤ e1 := h01 he0
    have he2 : 1 ≤ e2 := h02 he0
    have he3 : 1 ≤ e3 := h03 he0
    have he4 : 1 ≤ e4 := h04 he0
    linarith [hu1 he1, hu2 he2, hu3 he3, hu4 he4]
  · have he0' : 1 ≤ e0 := le_of_not_gt he0
    by_cases he1 : e1 < 1
    · have he2 : 1 ≤ e2 := h12 he1
      have he3 : 1 ≤ e3 := h13 he1
      have he4 : 1 ≤ e4 := h14 he1
      linarith [hu0 he0', hu2 he2, hu3 he3, hu4 he4]
    · have he1' : 1 ≤ e1 := le_of_not_gt he1
      by_cases he2 : e2 < 1
      · have he3 : 1 ≤ e3 := h23 he2
        have he4 : 1 ≤ e4 := h24 he2
        linarith [hu0 he0', hu1 he1', hu3 he3, hu4 he4]
      · have he2' : 1 ≤ e2 := le_of_not_gt he2
        by_cases he3 : e3 < 1
        · have he4 : 1 ≤ e4 := h34 he3
          linarith [hu0 he0', hu1 he1', hu2 he2', hu4 he4]
        · have he3' : 1 ≤ e3 := le_of_not_gt he3
          by_cases he4 : e4 < 1
          · linarith [hu0 he0', hu1 he1', hu2 he2', hu3 he3']
          · have he4' : 1 ≤ e4 := le_of_not_gt he4
            linarith [hu0 he0', hu1 he1', hu2 he2', hu3 he3', hu4 he4']

/-- When the rotated fourth-degree coefficient is zero, the primitive tail
energy is simply `s^5`, so every closed-disk root is non-strictly safe. -/
theorem primitiveZeroCoefficient_tailEnergy_le_one
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ 4 * s ≤ 1 := by
  have h5le4 : s ^ 5 ≤ s ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg hs0 4) (sub_nonneg.mpr hs1)]
  have h4le3 : s ^ 4 ≤ s ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg hs0 3) (sub_nonneg.mpr hs1)]
  have h3le2 : s ^ 3 ≤ s ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs1)]
  have h2les : s ^ 2 ≤ s := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have h5le1 : s ^ 5 ≤ 1 :=
    le_trans h5le4 (le_trans h4le3 (le_trans h3le2 (le_trans h2les hs1)))
  nlinarith

/-- Finite interior moment theorem for the primitive sparse quintic.  The
conclusion gives two distinct root-tail energies strictly below one. -/
theorem primitiveInterior_exists_two_tailEnergy_lt_one
    {r : ℝ}
    {x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : ℝ}
    (hr : 0 < r) (hr2 : r < 2)
    (hs0 : 0 ≤ s0) (hs0one : s0 ≤ 1) (hx0s : x0 ^ 2 ≤ s0)
    (hs1 : 0 ≤ s1) (hs1one : s1 ≤ 1) (hx1s : x1 ^ 2 ≤ s1)
    (hs2 : 0 ≤ s2) (hs2one : s2 ≤ 1) (hx2s : x2 ^ 2 ≤ s2)
    (hs3 : 0 ≤ s3) (hs3one : s3 ≤ 1) (hx3s : x3 ^ 2 ≤ s3)
    (hs4 : 0 ≤ s4) (hs4one : s4 ≤ 1) (hx4s : x4 ^ 2 ≤ s4)
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : (2 * x0 ^ 2 - s0) + (2 * x1 ^ 2 - s1) +
        (2 * x2 ^ 2 - s2) + (2 * x3 ^ 2 - s3) +
        (2 * x4 ^ 2 - s4) = r ^ 2)
    (hm3 : (4 * x0 ^ 3 - 3 * s0 * x0) +
        (4 * x1 ^ 3 - 3 * s1 * x1) +
        (4 * x2 ^ 3 - 3 * s2 * x2) +
        (4 * x3 ^ 3 - 3 * s3 * x3) +
        (4 * x4 ^ 3 - 3 * s4 * x4) = -r ^ 3) :
    (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) := by
  let e0 := s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0)
  let e1 := s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1)
  let e2 := s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2)
  let e3 := s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3)
  let e4 := s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4)
  let h0 := primitiveInteriorHarmonicSeparator r x0 s0
  let h1 := primitiveInteriorHarmonicSeparator r x1 s1
  let h2 := primitiveInteriorHarmonicSeparator r x2 s2
  let h3 := primitiveInteriorHarmonicSeparator r x3 s3
  let h4 := primitiveInteriorHarmonicSeparator r x4 s4
  let M : ℝ := 4 - 2 * r
  let U : ℝ := 2 / 31
  have hx0hi : x0 ≤ 1 := by nlinarith [sq_nonneg (x0 - 1)]
  have hx1hi : x1 ≤ 1 := by nlinarith [sq_nonneg (x1 - 1)]
  have hx2hi : x2 ≤ 1 := by nlinarith [sq_nonneg (x2 - 1)]
  have hx3hi : x3 ≤ 1 := by nlinarith [sq_nonneg (x3 - 1)]
  have hx4hi : x4 ≤ 1 := by nlinarith [sq_nonneg (x4 - 1)]
  have hsum : h0 + h1 + h2 + h3 + h4 = 5 - 2 * r := by
    simpa [h0, h1, h2, h3, h4] using
      primitiveInteriorHarmonicSeparator_sum hm1 hm2 hm3
  have hone : M + 4 * U < h0 + h1 + h2 + h3 + h4 := by
    rw [hsum]
    simp only [M, U]
    norm_num
    linarith
  have htwo := five_exists_two_lt_one_of_score_caps
    (M := M) (U := U)
    (primitiveInteriorHarmonicSeparator_le_single hr.le hr2 hs0 hs0one hx0s)
    (primitiveInteriorHarmonicSeparator_le_single hr.le hr2 hs1 hs1one hx1s)
    (primitiveInteriorHarmonicSeparator_le_single hr.le hr2 hs2 hs2one hx2s)
    (primitiveInteriorHarmonicSeparator_le_single hr.le hr2 hs3 hs3one hx3s)
    (primitiveInteriorHarmonicSeparator_le_single hr.le hr2 hs4 hs4one hx4s)
    (fun he => primitiveInteriorHarmonicSeparator_le_of_tailEnergy_ge_one
      hr hr2 hs0 hs0one hx0hi (by simpa [e0] using he))
    (fun he => primitiveInteriorHarmonicSeparator_le_of_tailEnergy_ge_one
      hr hr2 hs1 hs1one hx1hi (by simpa [e1] using he))
    (fun he => primitiveInteriorHarmonicSeparator_le_of_tailEnergy_ge_one
      hr hr2 hs2 hs2one hx2hi (by simpa [e2] using he))
    (fun he => primitiveInteriorHarmonicSeparator_le_of_tailEnergy_ge_one
      hr hr2 hs3 hs3one hx3hi (by simpa [e3] using he))
    (fun he => primitiveInteriorHarmonicSeparator_le_of_tailEnergy_ge_one
      hr hr2 hs4 hs4one hx4hi (by simpa [e4] using he))
    hone
  simpa [e0, e1, e2, e3, e4] using htwo

end ErdosProblems.Erdos1041
