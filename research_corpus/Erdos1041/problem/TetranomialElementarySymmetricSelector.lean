import ErdosProblems.Erdos1041.TetranomialTailProductSelector

/-!
# Erdős #1041: the second elementary-symmetric tail selector

The tail-resultant selector uses only the first elementary symmetric energy
`sum x_i`, where `x_i` is a squared tail norm.  This module checks the next
sharp layer for five tails.  If their product is at most one and their
pair-energy is below `6 + 4 * product`, then two tails are strictly below one.

The proof is a compression argument.  When `0 <= y <= 1 <= z`, replacing
`(y,z)` by `(y*z,1)` cannot increase the second elementary symmetric sum; the
drop is `(1-y)(z-1)` times the sum of the other variables.  Repeating leaves
`(product,1,1,1,1)`, whose pair-energy is `6 + 4 * product`.
-/

namespace ErdosProblems.Erdos1041

/-- The second elementary symmetric polynomial in five real variables. -/
def pairEnergy5 (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  x0 * x1 + x0 * x2 + x0 * x3 + x0 * x4 +
    x1 * x2 + x1 * x3 + x1 * x4 + x2 * x3 + x2 * x4 + x3 * x4

/-- Absorbing a large entry into the exceptional entry cannot increase the
five-variable pair energy. -/
theorem pairEnergy5_absorb
    {y z a b c : ℝ}
    (hy1 : y ≤ 1) (hz1 : 1 ≤ z)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    pairEnergy5 (y * z) 1 a b c ≤ pairEnergy5 y z a b c := by
  have hsum : 0 ≤ a + b + c := by positivity
  have hdrop : 0 ≤ (1 - y) * (z - 1) * (a + b + c) :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hz1)) hsum
  have hid :
      pairEnergy5 y z a b c - pairEnergy5 (y * z) 1 a b c =
        (1 - y) * (z - 1) * (a + b + c) := by
    simp only [pairEnergy5]
    ring
  linarith

/-- Sharp lower bound when four of five nonnegative entries are at least one
and the total product is at most one. -/
theorem pairEnergy5_lower_of_four_large
    {y z1 z2 z3 z4 : ℝ}
    (hy0 : 0 ≤ y)
    (hz1 : 1 ≤ z1) (hz2 : 1 ≤ z2) (hz3 : 1 ≤ z3) (hz4 : 1 ≤ z4)
    (hprod : y * z1 * z2 * z3 * z4 ≤ 1) :
    6 + 4 * (y * z1 * z2 * z3 * z4) ≤ pairEnergy5 y z1 z2 z3 z4 := by
  have hz10 : 0 ≤ z1 := le_trans (by norm_num) hz1
  have hz20 : 0 ≤ z2 := le_trans (by norm_num) hz2
  have hz30 : 0 ≤ z3 := le_trans (by norm_num) hz3
  have hz40 : 0 ≤ z4 := le_trans (by norm_num) hz4
  have hz234 : 1 ≤ z2 * z3 * z4 := by
    have hz23prod : 0 ≤ (z2 - 1) * (z3 - 1) :=
      mul_nonneg (sub_nonneg.mpr hz2) (sub_nonneg.mpr hz3)
    have hz23 : 1 ≤ z2 * z3 := by nlinarith
    have hz234prod : 0 ≤ (z2 * z3 - 1) * (z4 - 1) :=
      mul_nonneg (sub_nonneg.mpr hz23) (sub_nonneg.mpr hz4)
    nlinarith
  have hz34 : 1 ≤ z3 * z4 := by
    have hprod34 : 0 ≤ (z3 - 1) * (z4 - 1) :=
      mul_nonneg (sub_nonneg.mpr hz3) (sub_nonneg.mpr hz4)
    nlinarith
  have hy1 : y ≤ 1 := by
    calc
      y ≤ y * (z1 * z2 * z3 * z4) := by
        apply le_mul_of_one_le_right hy0
        have hz1234 : 1 ≤ z1 * (z2 * z3 * z4) := by
          have hprod1234 : 0 ≤ (z1 - 1) * (z2 * z3 * z4 - 1) :=
            mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr hz234)
          nlinarith
        simpa only [mul_assoc] using hz1234
      _ = y * z1 * z2 * z3 * z4 := by ring
      _ ≤ 1 := hprod
  have hyz1 : y * z1 ≤ 1 := by
    calc
      y * z1 ≤ (y * z1) * (z2 * z3 * z4) :=
        le_mul_of_one_le_right (mul_nonneg hy0 hz10) hz234
      _ = y * z1 * z2 * z3 * z4 := by ring
      _ ≤ 1 := hprod
  have hyz12 : y * z1 * z2 ≤ 1 := by
    calc
      y * z1 * z2 ≤ (y * z1 * z2) * (z3 * z4) :=
        le_mul_of_one_le_right (mul_nonneg (mul_nonneg hy0 hz10) hz20) hz34
      _ = y * z1 * z2 * z3 * z4 := by ring
      _ ≤ 1 := hprod
  have hyz123 : y * z1 * z2 * z3 ≤ 1 := by
    calc
      y * z1 * z2 * z3 ≤ (y * z1 * z2 * z3) * z4 :=
        le_mul_of_one_le_right
          (mul_nonneg (mul_nonneg (mul_nonneg hy0 hz10) hz20) hz30) hz4
      _ = y * z1 * z2 * z3 * z4 := by ring
      _ ≤ 1 := hprod
  have hdrop1 :
      0 ≤ (1 - y) * (z1 - 1) * (z2 + z3 + z4) := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hz1)) (by positivity)
  have hdrop2 :
      0 ≤ (1 - y * z1) * (z2 - 1) * (1 + z3 + z4) := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hyz1) (sub_nonneg.mpr hz2)) (by positivity)
  have hdrop3 :
      0 ≤ (1 - y * z1 * z2) * (z3 - 1) * (2 + z4) := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hyz12) (sub_nonneg.mpr hz3)) (by positivity)
  have hdrop4 :
      0 ≤ (1 - y * z1 * z2 * z3) * (z4 - 1) * 3 := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hyz123) (sub_nonneg.mpr hz4)) (by norm_num)
  have hdecomposition :
      pairEnergy5 y z1 z2 z3 z4 -
          (6 + 4 * (y * z1 * z2 * z3 * z4)) =
        (1 - y) * (z1 - 1) * (z2 + z3 + z4) +
        (1 - y * z1) * (z2 - 1) * (1 + z3 + z4) +
        (1 - y * z1 * z2) * (z3 - 1) * (2 + z4) +
        (1 - y * z1 * z2 * z3) * (z4 - 1) * 3 := by
    simp only [pairEnergy5]
    ring
  linarith

/-- Product-free base layer: the six mutual products of four entries at least
one already contribute six to the pair energy. -/
theorem pairEnergy5_lower_six_of_four_large
    {y z1 z2 z3 z4 : ℝ}
    (hy0 : 0 ≤ y)
    (hz1 : 1 ≤ z1) (hz2 : 1 ≤ z2) (hz3 : 1 ≤ z3) (hz4 : 1 ≤ z4) :
    6 ≤ pairEnergy5 y z1 z2 z3 z4 := by
  have pair_ge_one {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
    have hprod : 0 ≤ (a - 1) * (b - 1) :=
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
    nlinarith
  have h12 := pair_ge_one hz1 hz2
  have h13 := pair_ge_one hz1 hz3
  have h14 := pair_ge_one hz1 hz4
  have h23 := pair_ge_one hz2 hz3
  have h24 := pair_ge_one hz2 hz4
  have h34 := pair_ge_one hz3 hz4
  have hyz1 : 0 ≤ y * z1 := mul_nonneg hy0 (le_trans (by norm_num) hz1)
  have hyz2 : 0 ≤ y * z2 := mul_nonneg hy0 (le_trans (by norm_num) hz2)
  have hyz3 : 0 ≤ y * z3 := mul_nonneg hy0 (le_trans (by norm_num) hz3)
  have hyz4 : 0 ≤ y * z4 := mul_nonneg hy0 (le_trans (by norm_num) hz4)
  simp only [pairEnergy5]
  linarith

/-- Product-free five-entry second-layer selector. -/
theorem five_exists_two_lt_one_of_pairEnergy_lt_six
    {x0 x1 x2 x3 x4 : ℝ}
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (hx3 : 0 ≤ x3) (hx4 : 0 ≤ x4)
    (hpair : pairEnergy5 x0 x1 x2 x3 x4 < 6) :
    (x0 < 1 ∧ x1 < 1) ∨ (x0 < 1 ∧ x2 < 1) ∨
      (x0 < 1 ∧ x3 < 1) ∨ (x0 < 1 ∧ x4 < 1) ∨
      (x1 < 1 ∧ x2 < 1) ∨ (x1 < 1 ∧ x3 < 1) ∨
      (x1 < 1 ∧ x4 < 1) ∨ (x2 < 1 ∧ x3 < 1) ∨
      (x2 < 1 ∧ x4 < 1) ∨ (x3 < 1 ∧ x4 < 1) := by
  by_contra htwo
  push Not at htwo
  rcases htwo with
    ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  have contradict_of_four_large
      (y z1 z2 z3 z4 : ℝ)
      (hy0 : 0 ≤ y) (hz1 : 1 ≤ z1) (hz2 : 1 ≤ z2)
      (hz3 : 1 ≤ z3) (hz4 : 1 ≤ z4)
      (hreorderPair : pairEnergy5 y z1 z2 z3 z4 =
        pairEnergy5 x0 x1 x2 x3 x4) : False := by
    have hlower := pairEnergy5_lower_six_of_four_large hy0 hz1 hz2 hz3 hz4
    rw [hreorderPair] at hlower
    linarith
  by_cases h0 : x0 < 1
  · exact contradict_of_four_large x0 x1 x2 x3 x4 hx0
      (h01 h0) (h02 h0) (h03 h0) (h04 h0) rfl
  · have h0' : 1 ≤ x0 := le_of_not_gt h0
    by_cases h1 : x1 < 1
    · apply contradict_of_four_large x1 x0 x2 x3 x4 hx1 h0'
        (h12 h1) (h13 h1) (h14 h1)
      simp only [pairEnergy5]
      ring
    · have h1' : 1 ≤ x1 := le_of_not_gt h1
      by_cases h2 : x2 < 1
      · apply contradict_of_four_large x2 x0 x1 x3 x4 hx2 h0' h1'
          (h23 h2) (h24 h2)
        simp only [pairEnergy5]
        ring
      · have h2' : 1 ≤ x2 := le_of_not_gt h2
        by_cases h3 : x3 < 1
        · apply contradict_of_four_large x3 x0 x1 x2 x4 hx3 h0' h1' h2'
            (h34 h3)
          simp only [pairEnergy5]
          ring
        · have h3' : 1 ≤ x3 := le_of_not_gt h3
          apply contradict_of_four_large x4 x0 x1 x2 x3 hx4 h0' h1' h2' h3'
          simp only [pairEnergy5]
          ring

/-- The sharp five-entry `k=2` selector.  Pair energy below the compressed
boundary forces two distinct entries below one. -/
theorem five_exists_two_lt_one_of_pairEnergy_lt_six_add_four_prod
    {x0 x1 x2 x3 x4 : ℝ}
    (hx0 : 0 ≤ x0) (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (hx3 : 0 ≤ x3) (hx4 : 0 ≤ x4)
    (hprod : x0 * x1 * x2 * x3 * x4 ≤ 1)
    (hpair : pairEnergy5 x0 x1 x2 x3 x4 <
      6 + 4 * (x0 * x1 * x2 * x3 * x4)) :
    (x0 < 1 ∧ x1 < 1) ∨ (x0 < 1 ∧ x2 < 1) ∨
      (x0 < 1 ∧ x3 < 1) ∨ (x0 < 1 ∧ x4 < 1) ∨
      (x1 < 1 ∧ x2 < 1) ∨ (x1 < 1 ∧ x3 < 1) ∨
      (x1 < 1 ∧ x4 < 1) ∨ (x2 < 1 ∧ x3 < 1) ∨
      (x2 < 1 ∧ x4 < 1) ∨ (x3 < 1 ∧ x4 < 1) := by
  by_contra htwo
  push Not at htwo
  rcases htwo with
    ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  have contradict_of_four_large
      (y z1 z2 z3 z4 : ℝ)
      (hy0 : 0 ≤ y) (hz1 : 1 ≤ z1) (hz2 : 1 ≤ z2)
      (hz3 : 1 ≤ z3) (hz4 : 1 ≤ z4)
      (hprod' : y * z1 * z2 * z3 * z4 ≤ 1)
      (hreorderPair : pairEnergy5 y z1 z2 z3 z4 =
        pairEnergy5 x0 x1 x2 x3 x4)
      (hreorderProd : y * z1 * z2 * z3 * z4 =
        x0 * x1 * x2 * x3 * x4) : False := by
    have hlower := pairEnergy5_lower_of_four_large hy0 hz1 hz2 hz3 hz4 hprod'
    rw [hreorderPair, hreorderProd] at hlower
    linarith
  by_cases h0 : x0 < 1
  · have h1 : 1 ≤ x1 := h01 h0
    have h2 : 1 ≤ x2 := h02 h0
    have h3 : 1 ≤ x3 := h03 h0
    have h4 : 1 ≤ x4 := h04 h0
    exact contradict_of_four_large x0 x1 x2 x3 x4 hx0 h1 h2 h3 h4 hprod rfl rfl
  · have h0' : 1 ≤ x0 := le_of_not_gt h0
    by_cases h1 : x1 < 1
    · have h2 : 1 ≤ x2 := h12 h1
      have h3 : 1 ≤ x3 := h13 h1
      have h4 : 1 ≤ x4 := h14 h1
      apply contradict_of_four_large x1 x0 x2 x3 x4 hx1 h0' h2 h3 h4
      · simpa only [mul_assoc, mul_left_comm, mul_comm] using hprod
      · simp only [pairEnergy5]
        ring
      · ring
    · have h1' : 1 ≤ x1 := le_of_not_gt h1
      by_cases h2 : x2 < 1
      · have h3 : 1 ≤ x3 := h23 h2
        have h4 : 1 ≤ x4 := h24 h2
        apply contradict_of_four_large x2 x0 x1 x3 x4 hx2 h0' h1' h3 h4
        · simpa only [mul_assoc, mul_left_comm, mul_comm] using hprod
        · simp only [pairEnergy5]
          ring
        · ring
      · have h2' : 1 ≤ x2 := le_of_not_gt h2
        by_cases h3 : x3 < 1
        · have h4 : 1 ≤ x4 := h34 h3
          apply contradict_of_four_large x3 x0 x1 x2 x4 hx3 h0' h1' h2' h4
          · simpa only [mul_assoc, mul_left_comm, mul_comm] using hprod
          · simp only [pairEnergy5]
            ring
          · ring
        · have h3' : 1 ≤ x3 := le_of_not_gt h3
          apply contradict_of_four_large x4 x0 x1 x2 x3 hx4 h0' h1' h2' h3'
          · simpa only [mul_assoc, mul_left_comm, mul_comm] using hprod
          · simp only [pairEnergy5]
            ring
          · ring

/-- Complex-tail specialization: the five `x_i` are squared norms. -/
theorem five_exists_two_tail_normSq_lt_one_of_pairEnergy
    (t0 t1 t2 t3 t4 : ℂ)
    (hprod : Complex.normSq t0 * Complex.normSq t1 * Complex.normSq t2 *
        Complex.normSq t3 * Complex.normSq t4 ≤ 1)
    (hpair : pairEnergy5 (Complex.normSq t0) (Complex.normSq t1)
        (Complex.normSq t2) (Complex.normSq t3) (Complex.normSq t4) <
      6 + 4 * (Complex.normSq t0 * Complex.normSq t1 * Complex.normSq t2 *
        Complex.normSq t3 * Complex.normSq t4)) :
    (Complex.normSq t0 < 1 ∧ Complex.normSq t1 < 1) ∨
      (Complex.normSq t0 < 1 ∧ Complex.normSq t2 < 1) ∨
      (Complex.normSq t0 < 1 ∧ Complex.normSq t3 < 1) ∨
      (Complex.normSq t0 < 1 ∧ Complex.normSq t4 < 1) ∨
      (Complex.normSq t1 < 1 ∧ Complex.normSq t2 < 1) ∨
      (Complex.normSq t1 < 1 ∧ Complex.normSq t3 < 1) ∨
      (Complex.normSq t1 < 1 ∧ Complex.normSq t4 < 1) ∨
      (Complex.normSq t2 < 1 ∧ Complex.normSq t3 < 1) ∨
      (Complex.normSq t2 < 1 ∧ Complex.normSq t4 < 1) ∨
      (Complex.normSq t3 < 1 ∧ Complex.normSq t4 < 1) := by
  exact five_exists_two_lt_one_of_pairEnergy_lt_six_add_four_prod
    (Complex.normSq_nonneg t0) (Complex.normSq_nonneg t1)
    (Complex.normSq_nonneg t2) (Complex.normSq_nonneg t3)
    (Complex.normSq_nonneg t4) hprod hpair

/-- Complex-tail specialization of the product-free threshold. -/
theorem five_exists_two_tail_normSq_lt_one_of_pairEnergy_lt_six
    (t0 t1 t2 t3 t4 : ℂ)
    (hpair : pairEnergy5 (Complex.normSq t0) (Complex.normSq t1)
        (Complex.normSq t2) (Complex.normSq t3) (Complex.normSq t4) < 6) :
    (Complex.normSq t0 < 1 ∧ Complex.normSq t1 < 1) ∨
      (Complex.normSq t0 < 1 ∧ Complex.normSq t2 < 1) ∨
      (Complex.normSq t0 < 1 ∧ Complex.normSq t3 < 1) ∨
      (Complex.normSq t0 < 1 ∧ Complex.normSq t4 < 1) ∨
      (Complex.normSq t1 < 1 ∧ Complex.normSq t2 < 1) ∨
      (Complex.normSq t1 < 1 ∧ Complex.normSq t3 < 1) ∨
      (Complex.normSq t1 < 1 ∧ Complex.normSq t4 < 1) ∨
      (Complex.normSq t2 < 1 ∧ Complex.normSq t3 < 1) ∨
      (Complex.normSq t2 < 1 ∧ Complex.normSq t4 < 1) ∨
      (Complex.normSq t3 < 1 ∧ Complex.normSq t4 < 1) := by
  exact five_exists_two_lt_one_of_pairEnergy_lt_six
    (Complex.normSq_nonneg t0) (Complex.normSq_nonneg t1)
    (Complex.normSq_nonneg t2) (Complex.normSq_nonneg t3)
    (Complex.normSq_nonneg t4) hpair

/-- The pair energy of the exact factor-family tail pattern `0,A,A,B,B`.
Here `A` and `B` are the two conjugate squared-tail values. -/
theorem quarticFactor_pairEnergy_identity (r u : ℝ) :
    let q := r ^ 4
    let L := r ^ 2 + u ^ 2
    let M := Real.sqrt 2 * r * u
    let A := q ^ 2 * (L - M)
    let B := q ^ 2 * (L + M)
    pairEnergy5 0 A A B B =
      q ^ 4 * (6 * r ^ 4 + 8 * r ^ 2 * u ^ 2 + 6 * u ^ 4) := by
  dsimp
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [pairEnergy5]
  linear_combination -2 * (r ^ 4) ^ 4 * r ^ 2 * u ^ 2 * hsqrt

/-- Rational certificates for the strict-extension witness
`(z-41/100)(z^4+(63/64)^4)`. -/
theorem exactPrimitiveQuintic_secondLayer_certificates :
    let r : ℝ := 63 / 64
    let u : ℝ := 41 / 100
    let q : ℝ := r ^ 4
    q ^ 4 * (6 * r ^ 4 + 8 * r ^ 2 * u ^ 2 + 6 * u ^ 4) < 6 ∧
      4 * q ^ 2 * (r ^ 2 + u ^ 2) ≥ 4 ∧
      q * (1 + u) > 1 ∧
      r ^ 2 + u ^ 2 - (10 / 7 : ℝ) * r * u > 5 / 9 := by
  norm_num

/-- The rational upper comparison used to put every root-pair distance of the
strict-extension witness beyond the `5/9` close-pair certificate. -/
theorem sqrt_two_lt_ten_sevenths : Real.sqrt 2 < (10 : ℝ) / 7 := by
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith

end ErdosProblems.Erdos1041
