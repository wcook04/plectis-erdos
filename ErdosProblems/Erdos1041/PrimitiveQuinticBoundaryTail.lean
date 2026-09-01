import ErdosProblems.Erdos1041.TetranomialElementarySymmetricSelector

/-!
# Erdős #1041: primitive-quintic boundary tails

For the paraorthogonal boundary of `z^5 + a*z^4 + b*z + c`, the two
missing middle coefficients fix the first three real angular moments.  The
cubic separator below has total mass `5 - 2*r`, whereas one safe atom can
contribute at most `4 - 2*r`.  The exact unit gap forces two distinct safe
atoms.

The companion note derives these real moment hypotheses from Newton's
identities for the five unit-circle roots.  This module formalizes the
load-bearing finite extremal argument and its strict tail-energy consumer.
-/

namespace ErdosProblems.Erdos1041

/-- The phase-sensitive cubic separator for the safe arc
`x < -r/2`. -/
noncomputable def primitiveBoundarySeparator (r x : ℝ) : ℝ :=
  (-r / 2 - x) * (1 - x) ^ 2

/-- Substitution of the first three boundary moments collapses the total
separator mass to `5 - 2*r`. -/
theorem primitiveBoundarySeparator_sum
    {r x0 x1 x2 x3 x4 : ℝ}
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 =
      (5 + r ^ 2) / 2)
    (hm3 : x0 ^ 3 + x1 ^ 3 + x2 ^ 3 + x3 ^ 3 + x4 ^ 3 =
      -(r ^ 3 + 3 * r) / 4) :
    primitiveBoundarySeparator r x0 + primitiveBoundarySeparator r x1 +
        primitiveBoundarySeparator r x2 + primitiveBoundarySeparator r x3 +
        primitiveBoundarySeparator r x4 = 5 - 2 * r := by
  simp only [primitiveBoundarySeparator]
  nlinarith

/-- On `[-1,1]`, no single atom contributes more than `4 - 2*r` when
`0 <= r < 2`. -/
theorem primitiveBoundarySeparator_le_single
    {r x : ℝ} (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hxlo : -1 ≤ x) (hxhi : x ≤ 1) :
    primitiveBoundarySeparator r x ≤ 4 - 2 * r := by
  have hfirst : 0 ≤ x + 1 := by linarith
  have hrect : 0 ≤ (2 - r) * (3 - x) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : 0 ≤ 2 * (x - 1) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have hsecond :
      0 ≤ r * x - 3 * r + 2 * x ^ 2 - 6 * x + 8 := by
    nlinarith
  have hprod :
      0 ≤ (x + 1) *
        (r * x - 3 * r + 2 * x ^ 2 - 6 * x + 8) :=
    mul_nonneg hfirst hsecond
  have hid :
      (4 - 2 * r) - primitiveBoundarySeparator r x =
        (x + 1) *
          (r * x - 3 * r + 2 * x ^ 2 - 6 * x + 8) / 2 := by
    simp only [primitiveBoundarySeparator]
    ring
  have hdiff : 0 ≤ (4 - 2 * r) - primitiveBoundarySeparator r x := by
    rw [hid]
    positivity
  linarith

/-- Positivity of the separator puts the real part strictly in the safe
arc. -/
theorem lt_neg_half_of_primitiveBoundarySeparator_pos
    {r x : ℝ} (hpos : 0 < primitiveBoundarySeparator r x) :
    x < -r / 2 := by
  by_contra hnot
  have hleft : -r / 2 - x ≤ 0 := by linarith
  have hsquare : 0 ≤ (1 - x) ^ 2 := sq_nonneg _
  have hnonpos : primitiveBoundarySeparator r x ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg hleft hsquare
  linarith

/-- Five numbers whose sum exceeds a nonnegative common upper bound contain
two distinct positive entries. -/
theorem five_exists_two_pos_of_sum_gt_singleCap
    {q0 q1 q2 q3 q4 M : ℝ}
    (hM0 : 0 ≤ M)
    (hq0 : q0 ≤ M) (hq1 : q1 ≤ M) (hq2 : q2 ≤ M)
    (hq3 : q3 ≤ M) (hq4 : q4 ≤ M)
    (hsum : M < q0 + q1 + q2 + q3 + q4) :
    (0 < q0 ∧ 0 < q1) ∨ (0 < q0 ∧ 0 < q2) ∨
      (0 < q0 ∧ 0 < q3) ∨ (0 < q0 ∧ 0 < q4) ∨
      (0 < q1 ∧ 0 < q2) ∨ (0 < q1 ∧ 0 < q3) ∨
      (0 < q1 ∧ 0 < q4) ∨ (0 < q2 ∧ 0 < q3) ∨
      (0 < q2 ∧ 0 < q4) ∨ (0 < q3 ∧ 0 < q4) := by
  by_contra htwo
  push Not at htwo
  rcases htwo with
    ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  by_cases h0 : 0 < q0
  · have h1 : q1 ≤ 0 := h01 h0
    have h2 : q2 ≤ 0 := h02 h0
    have h3 : q3 ≤ 0 := h03 h0
    have h4 : q4 ≤ 0 := h04 h0
    linarith
  · have h0' : q0 ≤ 0 := le_of_not_gt h0
    by_cases h1 : 0 < q1
    · have h2 : q2 ≤ 0 := h12 h1
      have h3 : q3 ≤ 0 := h13 h1
      have h4 : q4 ≤ 0 := h14 h1
      linarith
    · have h1' : q1 ≤ 0 := le_of_not_gt h1
      by_cases h2 : 0 < q2
      · have h3 : q3 ≤ 0 := h23 h2
        have h4 : q4 ≤ 0 := h24 h2
        linarith
      · have h2' : q2 ≤ 0 := le_of_not_gt h2
        by_cases h3 : 0 < q3
        · have h4 : q4 ≤ 0 := h34 h3
          linarith
        · have h3' : q3 ≤ 0 := le_of_not_gt h3
          have h4' : q4 ≤ 0 := by
            by_contra h4
            have : 0 < q4 := lt_of_not_ge h4
            linarith
          linarith

/-- The finite moment separator theorem: five points in `[-1,1]` with the
primitive-quintic boundary moments contain two distinct real parts below
`-r/2`. -/
theorem primitiveBoundary_exists_two_realParts_lt
    {r x0 x1 x2 x3 x4 : ℝ}
    (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hx0lo : -1 ≤ x0) (hx0hi : x0 ≤ 1)
    (hx1lo : -1 ≤ x1) (hx1hi : x1 ≤ 1)
    (hx2lo : -1 ≤ x2) (hx2hi : x2 ≤ 1)
    (hx3lo : -1 ≤ x3) (hx3hi : x3 ≤ 1)
    (hx4lo : -1 ≤ x4) (hx4hi : x4 ≤ 1)
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 =
      (5 + r ^ 2) / 2)
    (hm3 : x0 ^ 3 + x1 ^ 3 + x2 ^ 3 + x3 ^ 3 + x4 ^ 3 =
      -(r ^ 3 + 3 * r) / 4) :
    (x0 < -r / 2 ∧ x1 < -r / 2) ∨
      (x0 < -r / 2 ∧ x2 < -r / 2) ∨
      (x0 < -r / 2 ∧ x3 < -r / 2) ∨
      (x0 < -r / 2 ∧ x4 < -r / 2) ∨
      (x1 < -r / 2 ∧ x2 < -r / 2) ∨
      (x1 < -r / 2 ∧ x3 < -r / 2) ∨
      (x1 < -r / 2 ∧ x4 < -r / 2) ∨
      (x2 < -r / 2 ∧ x3 < -r / 2) ∨
      (x2 < -r / 2 ∧ x4 < -r / 2) ∨
      (x3 < -r / 2 ∧ x4 < -r / 2) := by
  let q0 := primitiveBoundarySeparator r x0
  let q1 := primitiveBoundarySeparator r x1
  let q2 := primitiveBoundarySeparator r x2
  let q3 := primitiveBoundarySeparator r x3
  let q4 := primitiveBoundarySeparator r x4
  have hsumEq : q0 + q1 + q2 + q3 + q4 = 5 - 2 * r := by
    simpa [q0, q1, q2, q3, q4] using
      primitiveBoundarySeparator_sum hm1 hm2 hm3
  have hcap0 : 0 ≤ 4 - 2 * r := by linarith
  have hsum : 4 - 2 * r < q0 + q1 + q2 + q3 + q4 := by
    rw [hsumEq]
    linarith
  have htwo := five_exists_two_pos_of_sum_gt_singleCap hcap0
    (primitiveBoundarySeparator_le_single hr0 hr2 hx0lo hx0hi)
    (primitiveBoundarySeparator_le_single hr0 hr2 hx1lo hx1hi)
    (primitiveBoundarySeparator_le_single hr0 hr2 hx2lo hx2hi)
    (primitiveBoundarySeparator_le_single hr0 hr2 hx3lo hx3hi)
    (primitiveBoundarySeparator_le_single hr0 hr2 hx4lo hx4hi) hsum
  rcases htwo with h01 | h02 | h03 | h04 | h12 | h13 | h14 | h23 | h24 | h34
  · exact Or.inl ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h01.1,
      lt_neg_half_of_primitiveBoundarySeparator_pos h01.2⟩
  · exact Or.inr <| Or.inl ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h02.1,
      lt_neg_half_of_primitiveBoundarySeparator_pos h02.2⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h03.1,
        lt_neg_half_of_primitiveBoundarySeparator_pos h03.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h04.1,
        lt_neg_half_of_primitiveBoundarySeparator_pos h04.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h12.1,
        lt_neg_half_of_primitiveBoundarySeparator_pos h12.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h13.1,
        lt_neg_half_of_primitiveBoundarySeparator_pos h13.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h14.1,
        lt_neg_half_of_primitiveBoundarySeparator_pos h14.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h23.1,
        lt_neg_half_of_primitiveBoundarySeparator_pos h23.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h24.1,
        lt_neg_half_of_primitiveBoundarySeparator_pos h24.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨lt_neg_half_of_primitiveBoundarySeparator_pos h34.1,
        lt_neg_half_of_primitiveBoundarySeparator_pos h34.2⟩

/-- Strict tail-energy form of the boundary selector.  For `r>0`, the
inequality `x < -r/2` is exactly `1+r^2+2*r*x < 1`. -/
theorem primitiveBoundary_exists_two_tailEnergy_lt_one
    {r x0 x1 x2 x3 x4 : ℝ}
    (hr : 0 < r) (hr2 : r < 2)
    (hx0lo : -1 ≤ x0) (hx0hi : x0 ≤ 1)
    (hx1lo : -1 ≤ x1) (hx1hi : x1 ≤ 1)
    (hx2lo : -1 ≤ x2) (hx2hi : x2 ≤ 1)
    (hx3lo : -1 ≤ x3) (hx3hi : x3 ≤ 1)
    (hx4lo : -1 ≤ x4) (hx4hi : x4 ≤ 1)
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 =
      (5 + r ^ 2) / 2)
    (hm3 : x0 ^ 3 + x1 ^ 3 + x2 ^ 3 + x3 ^ 3 + x4 ^ 3 =
      -(r ^ 3 + 3 * r) / 4) :
    (1 + r ^ 2 + 2 * r * x0 < 1 ∧ 1 + r ^ 2 + 2 * r * x1 < 1) ∨
      (1 + r ^ 2 + 2 * r * x0 < 1 ∧ 1 + r ^ 2 + 2 * r * x2 < 1) ∨
      (1 + r ^ 2 + 2 * r * x0 < 1 ∧ 1 + r ^ 2 + 2 * r * x3 < 1) ∨
      (1 + r ^ 2 + 2 * r * x0 < 1 ∧ 1 + r ^ 2 + 2 * r * x4 < 1) ∨
      (1 + r ^ 2 + 2 * r * x1 < 1 ∧ 1 + r ^ 2 + 2 * r * x2 < 1) ∨
      (1 + r ^ 2 + 2 * r * x1 < 1 ∧ 1 + r ^ 2 + 2 * r * x3 < 1) ∨
      (1 + r ^ 2 + 2 * r * x1 < 1 ∧ 1 + r ^ 2 + 2 * r * x4 < 1) ∨
      (1 + r ^ 2 + 2 * r * x2 < 1 ∧ 1 + r ^ 2 + 2 * r * x3 < 1) ∨
      (1 + r ^ 2 + 2 * r * x2 < 1 ∧ 1 + r ^ 2 + 2 * r * x4 < 1) ∨
      (1 + r ^ 2 + 2 * r * x3 < 1 ∧ 1 + r ^ 2 + 2 * r * x4 < 1) := by
  have htwo := primitiveBoundary_exists_two_realParts_lt hr.le hr2
    hx0lo hx0hi hx1lo hx1hi hx2lo hx2hi hx3lo hx3hi hx4lo hx4hi
    hm1 hm2 hm3
  have convert {x : ℝ} (hx : x < -r / 2) : 1 + r ^ 2 + 2 * r * x < 1 := by
    nlinarith [mul_pos hr (sub_pos.mpr (show -r / 2 - x > 0 by linarith))]
  rcases htwo with h01 | h02 | h03 | h04 | h12 | h13 | h14 | h23 | h24 | h34
  · exact Or.inl ⟨convert h01.1, convert h01.2⟩
  · exact Or.inr <| Or.inl ⟨convert h02.1, convert h02.2⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨convert h03.1, convert h03.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨convert h04.1, convert h04.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨convert h12.1, convert h12.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨convert h13.1, convert h13.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨convert h14.1, convert h14.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨convert h23.1, convert h23.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨convert h24.1, convert h24.2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨convert h34.1, convert h34.2⟩

end ErdosProblems.Erdos1041
