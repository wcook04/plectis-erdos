import ErdosProblems.Erdos1049.QBinomialAnalyticR16
import ErdosProblems.Erdos1049.PositiveSeriesFubiniR16
import ErdosProblems.Erdos1049.InfiniteMomentPositivityR10

/-!
# The literal source moments have a positive infinite discrete measure

New candidate; all elaboration, kernel checks, and axiom audits UNRUN.

The coefficients are constructed from finite convolutions of explicit
q-binomial and Euler coefficient sequences. The analytic identification is
proved, and then fed into the existing geometricMomentHankel_det_pos consumer.
No moment identity, coefficient positivity, or weight summability is assumed.

This module proves the source-to-measure and all-rank strict-positivity chain.
The uniform-in-rank two-sided comparison is authored downstream in
`ActualUniformBoundR16`; it is not inferred merely from this positivity theorem.
-/
namespace ErdosProblems.Erdos1049.PaperR16
open PaperR10 PaperR12 Filter
open scoped BigOperators Topology

noncomputable def momentAlpha (q : ℝ) (t : ℕ) : ℝ := (Real.sqrt q) ^ t
noncomputable def momentBeta (q : ℝ) (t : ℕ) : ℝ := (Real.sqrt q) ^ (t + 1)

lemma momentRoot_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ Real.sqrt q ∧ Real.sqrt q < 1 := by
  constructor
  · exact Real.sqrt_nonneg q
  · nlinarith [Real.sq_sqrt hq0.le, Real.sqrt_nonneg q]

lemma momentAlpha_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (t : ℕ) :
    0 ≤ momentAlpha q t ∧ momentAlpha q t ≤ 1 := by
  have h := momentRoot_bounds hq0 hq1
  exact ⟨pow_nonneg h.1 t, pow_le_one₀ h.1 h.2.le⟩

lemma momentBeta_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (t : ℕ) :
    0 ≤ momentBeta q t ∧ momentBeta q t ≤ 1 := by
  simpa [momentBeta, momentAlpha] using momentAlpha_bounds hq0 hq1 (t + 1)

lemma momentAlpha_sq {q : ℝ} (hq0 : 0 ≤ q) (t : ℕ) :
    momentAlpha q t ^ 2 = q ^ t := by
  unfold momentAlpha
  calc
    ((Real.sqrt q) ^ t) ^ 2 = ((Real.sqrt q) ^ 2) ^ t := by
      simp only [← pow_mul, Nat.mul_comm]
    _ = q ^ t := by rw [Real.sq_sqrt hq0]

lemma momentBeta_sq {q : ℝ} (hq0 : 0 ≤ q) (t : ℕ) :
    momentBeta q t ^ 2 = q * momentAlpha q t ^ 2 := by
  change momentAlpha q (t + 1) ^ 2 = _
  rw [momentAlpha_sq hq0, momentAlpha_sq hq0, pow_succ]
  ring

/-- The t=0 row is written in its cancelled form, so R_1 is not treated as a
nontrivial singular factor. Positive t rows have the seven factors in (12). -/
noncomputable def momentRowCoeff (q : ℝ) : ℕ → ℕ → ℝ
  | 0 =>
      coeffConv
        (coeffConv
          (coeffConv
            (coeffConv
              (coeffConv (inverseQCoeff q) (inverseQCoeff q))
              (inverseQCoeff q))
            (qBinomialRatioCoeff (Real.sqrt q) q))
          (eulerCoeff q))
        (coeffScale (eulerCoeff q) (Real.sqrt q))
  | t + 1 =>
      coeffConv
        (coeffConv
          (coeffConv
            (coeffConv
              (coeffConv
                (coeffConv (inverseQCoeff q)
                  (qBinomialRatioCoeff (momentAlpha q (t + 1)) q))
                (qBinomialRatioCoeff (momentBeta q (t + 1)) q))
              (coeffScale (eulerCoeff q) (momentAlpha q (t + 1))))
            (coeffScale (eulerCoeff q) (momentBeta q (t + 1))))
          (coeffScale (inverseQCoeff q) (q ^ (t + 1))))
        (coeffScale (inverseQCoeff q) (q ^ (t + 1)))

/-- A finite coefficient sum, not an unspecified Taylor coefficient or an
assumed positive atom supplier. -/
noncomputable def actualGamma (q : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal k,
    momentRowCoeff q p.1 p.2 / qPochhammerFinite q q p.1

lemma positiveSum_inverse {q w : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    PositiveSum (inverseQCoeff q) w (qPochhammerInfinity w q)⁻¹ := by
  refine ⟨fun n => (by have := (inverseQCoeff_bounds hq0 hq1 n).1; linarith), ?_⟩
  have hs : Summable (fun n => inverseQCoeff q n * w ^ n) :=
    qBinomialRatio_hasSum (a := 0) (by norm_num) (by norm_num) hq0 hq1 hw0 hw1
  have he : (∑' n, inverseQCoeff q n * w ^ n) = (qPochhammerInfinity w q)⁻¹ :=
    inverseQCoeff_eval hq0 hq1 hw0 hw1
  exact he ▸ hs.hasSum

lemma positiveSum_ratio {q a w : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    PositiveSum (qBinomialRatioCoeff a q) w
      (qPochhammerInfinity (a * w) q / qPochhammerInfinity w q) := by
  refine ⟨qBinomialRatioCoeff_nonneg ha0 ha1 hq0 hq1, ?_⟩
  have hs := qBinomialRatio_hasSum ha0 ha1 hq0 hq1 hw0 hw1
  have he : (∑' n, qBinomialRatioCoeff a q n * w ^ n) =
      qPochhammerInfinity (a * w) q / qPochhammerInfinity w q :=
    qBinomialRatio_eval ha0 ha1 hq0 hq1 hw0 hw1
  exact he ▸ hs.hasSum

lemma positiveSum_euler {q a w : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    PositiveSum (coeffScale (eulerCoeff q) a) w
      (coeffEval (eulerCoeff q) (a * w)) := by
  have haw0 := mul_nonneg ha0 hw0
  have haw1 : a * w ≤ 1 := by
    calc
      a * w ≤ 1 * w := mul_le_mul_of_nonneg_right ha1 hw0
      _ ≤ 1 := by simpa using hw1
  refine ⟨coeffScale_nonneg (eulerCoeff_nonneg hq0 hq1) ha0, ?_⟩
  have hs := (eulerCoeff_weighted_summable hq0 hq1 haw0 haw1).hasSum
  simpa only [coeffEval, coeffScale, mul_pow, mul_assoc] using hs

lemma positiveSum_scaledInverse {q a w : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    PositiveSum (coeffScale (inverseQCoeff q) a) w
      (qPochhammerInfinity (a * w) q)⁻¹ := by
  have haw0 := mul_nonneg ha0 hw0
  have haw1 : a * w < 1 := by
    have h : a * w ≤ w := by simpa using mul_le_mul_of_nonneg_right ha1 hw0
    exact h.trans_lt hw1
  have h := positiveSum_inverse hq0 hq1 haw0 haw1
  refine ⟨coeffScale_nonneg h.nonneg ha0, ?_⟩
  simpa only [coeffScale, mul_pow, mul_assoc] using h.sum

private lemma assemble_zero_row_value {P R E F T : ℝ} (hP : P ≠ 0)
    (h : R / P * E * F = T / P ^ 2) :
    P⁻¹ * P⁻¹ * P⁻¹ * (R / P) * E * F = T / (P ^ 3 * P ^ 2) := by
  calc
    _ = P⁻¹ ^ 3 * (R / P * E * F) := by ring
    _ = P⁻¹ ^ 3 * (T / P ^ 2) := by rw [h]
    _ = _ := by field_simp [hP]

private lemma assemble_positive_row_value {P D A B E F T : ℝ}
    (hP : P ≠ 0) (hD : D ≠ 0)
    (h : A / P * (B / P) * E * F = T / P ^ 2) :
    P⁻¹ * (A / P) * (B / P) * E * F * D⁻¹ * D⁻¹ = T / (P ^ 3 * D ^ 2) := by
  calc
    _ = P⁻¹ * (A / P * (B / P) * E * F) * D⁻¹ ^ 2 := by ring
    _ = P⁻¹ * (T / P ^ 2) * D⁻¹ ^ 2 := by rw [h]
    _ = _ := by field_simp [hP, hD]

/-- Exact analytic value of every explicitly constructed coefficient row. -/
theorem momentRowCoeff_positiveSum {q w : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) (t : ℕ) :
    PositiveSum (momentRowCoeff q t) w
      (qPochhammerInfinity (q ^ t * w ^ 2) q /
        ((qPochhammerInfinity w q) ^ 3 *
          (qPochhammerInfinity (q ^ t * w) q) ^ 2)) := by
  have hH := positiveSum_inverse hq0.le hq1 hw0 hw1
  have hr := momentRoot_bounds hq0 hq1
  cases t with
  | zero =>
      have hR := positiveSum_ratio hq0.le hq1 hr.1 hr.2.le hw0 hw1
      have hE1 := positiveSum_euler hq0.le hq1 (a := 1) (by norm_num) (by norm_num)
        hw0 hw1.le
      have hEr := positiveSum_euler hq0.le hq1 hr.1 hr.2.le hw0 hw1.le
      have hE : PositiveSum (eulerCoeff q) w (coeffEval (eulerCoeff q) w) := by
        -- `coeffScale (eulerCoeff q) 1` is a partial application; unfold it pointwise.
        have hscale : coeffScale (eulerCoeff q) 1 = eulerCoeff q := by
          funext n
          simp [coeffScale]
        simpa [hscale] using hE1
      have h := (((((hH.conv hH hw0).conv hH hw0).conv hR hw0).conv hE hw0).conv hEr hw0)
      refine ⟨h.nonneg, ?_⟩
      have hp := pairedEulerRatio_identity (a := 1) (b := Real.sqrt q)
        (by norm_num) (by norm_num) hr.1 hr.2.le hq0.le hq1 hw0 hw1
        (by simpa using Real.sq_sqrt hq0.le)
      have hR1 : coeffEval (qBinomialRatioCoeff 1 q) w = 1 := by
        rw [qBinomialRatio_eval (by norm_num) (by norm_num) hq0.le hq1 hw0 hw1]
        simp [(qPochhammerInfinity_pos w q).ne']
      rw [hR1, qBinomialRatio_eval hr.1 hr.2.le hq0.le hq1 hw0 hw1] at hp
      simp only [one_mul, one_pow] at hp
      have hv := assemble_zero_row_value (qPochhammerInfinity_pos w q).ne' hp
      have hsum := h.sum
      rw [hv] at hsum
      simpa only [momentRowCoeff, pow_zero, one_mul] using hsum
  | succ t =>
      have ha := momentAlpha_bounds hq0 hq1 (t + 1)
      have hb := momentBeta_bounds hq0 hq1 (t + 1)
      have hRa := positiveSum_ratio hq0.le hq1 ha.1 ha.2 hw0 hw1
      have hRb := positiveSum_ratio hq0.le hq1 hb.1 hb.2 hw0 hw1
      have hEa := positiveSum_euler hq0.le hq1 ha.1 ha.2 hw0 hw1.le
      have hEb := positiveSum_euler hq0.le hq1 hb.1 hb.2 hw0 hw1.le
      have hD := positiveSum_scaledInverse hq0.le hq1
        (pow_nonneg hq0.le (t + 1)) (pow_le_one₀ hq0.le hq1.le) hw0 hw1
      have h := ((((((hH.conv hRa hw0).conv hRb hw0).conv hEa hw0).conv hEb hw0)
        |>.conv hD hw0).conv hD hw0)
      refine ⟨h.nonneg, ?_⟩
      have hp := pairedEulerRatio_identity ha.1 ha.2 hb.1 hb.2 hq0.le hq1 hw0 hw1
        (momentBeta_sq hq0.le (t + 1))
      rw [momentAlpha_sq hq0.le,
        qBinomialRatio_eval ha.1 ha.2 hq0.le hq1 hw0 hw1,
        qBinomialRatio_eval hb.1 hb.2 hq0.le hq1 hw0 hw1] at hp
      have hv := assemble_positive_row_value (qPochhammerInfinity_pos w q).ne'
        (qPochhammerInfinity_pos (q ^ (t + 1) * w) q).ne' hp
      have hsum := h.sum
      rw [hv] at hsum
      simpa only [momentRowCoeff] using hsum

lemma momentRowCoeff_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (t k : ℕ) :
    0 ≤ momentRowCoeff q t k :=
  (momentRowCoeff_positiveSum hq0 hq1 (w := 0) (by norm_num) (by norm_num) t).nonneg k

@[simp] lemma inverseQCoeff_zero (q : ℝ) : inverseQCoeff q 0 = 1 := rfl

@[simp] lemma coeffScale_zero (c : ℕ → ℝ) (a : ℝ) : coeffScale c a 0 = c 0 := by
  simp [coeffScale]

@[simp] lemma momentRowCoeff_zero_degree (q : ℝ) (t : ℕ) : momentRowCoeff q t 0 = 1 := by
  cases t <;> simp [momentRowCoeff, qBinomialRatioCoeff]

lemma inverseQCoeff_le_zeroRow {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    inverseQCoeff q k ≤ momentRowCoeff q 0 k := by
  have hH : ∀ n, 0 ≤ inverseQCoeff q n := fun n => by
    have h := (inverseQCoeff_bounds hq0.le hq1 n).1
    linarith
  have hr := momentRoot_bounds hq0 hq1
  have hR := qBinomialRatioCoeff_nonneg hr.1 hr.2.le hq0.le hq1
  have hE := eulerCoeff_nonneg hq0.le hq1
  have hEr := coeffScale_nonneg hE hr.1
  have h2 := coeffConv_nonneg hH hH
  have h3 := coeffConv_nonneg h2 hH
  have h4 := coeffConv_nonneg h3 hR
  have h5 := coeffConv_nonneg h4 hE
  exact (left_le_coeffConv hH hH (by rfl) k).trans
    ((left_le_coeffConv h2 hH (by rfl) k).trans
      ((left_le_coeffConv h3 hR (by rfl) k).trans
        ((left_le_coeffConv h4 hE (by simp) k).trans
          (left_le_coeffConv h5 hEr (by simp) k))))

lemma actualGamma_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ actualGamma q k := by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (momentRowCoeff_nonneg hq0 hq1 p.1 p.2)
    (qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le p.1).le

/-- Every coefficient is positive, not only nonnegative. The zero-th outer
row alone already dominates the positive inverse-product coefficients. -/
theorem one_le_actualGamma {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    1 ≤ actualGamma q k := by
  have hz : (0, k) ∈ Finset.antidiagonal k := by simp
  have h := Finset.single_le_sum
    (fun p (_ : p ∈ Finset.antidiagonal k) =>
      div_nonneg (momentRowCoeff_nonneg hq0 hq1 p.1 p.2)
        (qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le p.1).le) hz
  have hrow : momentRowCoeff q 0 k ≤ actualGamma q k := by
    simpa only [qPochhammerFinite_zero, div_one] using h
  exact ((inverseQCoeff_bounds hq0.le hq1 k).1.trans
    (inverseQCoeff_le_zeroRow hq0 hq1 k)).trans hrow

lemma actualGeneratingTerm_nonneg {q w : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hw0 : 0 ≤ w) (t : ℕ) :
    0 ≤ actualGeneratingTerm q w t := by
  unfold actualGeneratingTerm
  exact div_nonneg
    (mul_nonneg (div_nonneg (pow_nonneg hw0 t)
      (qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le t).le)
      (qPochhammerInfinity_pos _ _).le) (sq_nonneg _)

lemma actualGeneratingTerm_bound {q w : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) (t : ℕ) :
    actualGeneratingTerm q w t ≤
      w ^ t / (qPochhammerInfinity q q * (qPochhammerInfinity w q) ^ 2) := by
  have hp : qPochhammerInfinity q q ≤ qPochhammerFinite q q t :=
    qPochhammerInfinity_le_finite hq0.le hq1 hq0.le hq1 t
  have hqt : q ^ t ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have harg0 := mul_nonneg (pow_nonneg hq0.le t) hw0
  have harg : q ^ t * w ≤ w := by simpa using mul_le_mul_of_nonneg_right hqt hw0
  have hd := qPochhammerInfinity_antitone_arg harg0 harg hw1 hq0.le hq1
  have hw20 := sq_nonneg w
  have hw21 : w ^ 2 < 1 := by nlinarith
  have hnum0 := mul_nonneg (pow_nonneg hq0.le t) hw20
  have hnum1 : q ^ t * w ^ 2 < 1 := by
    have h : q ^ t * w ^ 2 ≤ w ^ 2 := by
      simpa using mul_le_mul_of_nonneg_right hqt hw20
    exact h.trans_lt hw21
  have hn := qPochhammerInfinity_le_one hnum0 hnum1 hq0.le hq1
  have hP := qPochhammerInfinity_pos q q
  have hW := qPochhammerInfinity_pos w q
  have hD := qPochhammerInfinity_pos (q ^ t * w) q
  have hPt := qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le t
  have hden : qPochhammerInfinity q q * (qPochhammerInfinity w q) ^ 2 ≤
      qPochhammerFinite q q t * (qPochhammerInfinity (q ^ t * w) q) ^ 2 := by
    exact mul_le_mul hp ((sq_le_sq₀ hW.le hD.le).2 hd)
      (sq_nonneg _) hPt.le
  unfold actualGeneratingTerm
  calc
    _ = w ^ t * qPochhammerInfinity (q ^ t * w ^ 2) q /
        (qPochhammerFinite q q t * (qPochhammerInfinity (q ^ t * w) q) ^ 2) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ w ^ t / (qPochhammerFinite q q t *
        (qPochhammerInfinity (q ^ t * w) q) ^ 2) := by
      apply div_le_div_of_nonneg_right _ (mul_nonneg hPt.le (sq_nonneg _))
      simpa using mul_le_mul_of_nonneg_left hn (pow_nonneg hw0 t)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hw0 t)
      (mul_pos hP (sq_pos_of_pos hW)) hden

/-- General source generating-sum convergence, not only at q^(m+1). -/
theorem actualGeneratingTerm_summable {q w : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Summable (actualGeneratingTerm q w) := by
  apply summable_nonneg_dominated (actualGeneratingTerm_nonneg hq0 hq1 hw0)
    (actualGeneratingTerm_bound hq0 hq1 hw0 hw1)
  exact (hasSum_geometric_of_lt_one hw0 hw1).summable.div_const _

/-- A complete positive coefficient expansion of the actual analytic G_q.
The finite coefficient definition and the source generating function are
connected by convergent row sums and finite-antidiagonal regrouping. -/
theorem actualGamma_hasSum {q w : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    HasSum (fun k : ℕ => actualGamma q k * w ^ k) (actualGeneratingFunction q w) := by
  let f : ℕ → ℕ → ℝ := fun t k =>
    momentRowCoeff q t k / qPochhammerFinite q q t * w ^ (t + k)
  let v : ℕ → ℝ := fun t =>
    actualGeneratingTerm q w t / (qPochhammerInfinity w q) ^ 3
  have hf0 : ∀ t k, 0 ≤ f t k := by
    intro t k
    exact mul_nonneg
      (div_nonneg (momentRowCoeff_nonneg hq0 hq1 t k)
        (qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le t).le)
      (pow_nonneg hw0 _)
  have hrow : ∀ t, HasSum (f t) (v t) := by
    intro t
    have h := (momentRowCoeff_positiveSum hq0 hq1 hw0 hw1 t).sum.mul_left
      (w ^ t / qPochhammerFinite q q t)
    convert h using 1
    · ext k
      dsimp [f]
      rw [pow_add]
      ring
    · dsimp [v, actualGeneratingTerm]
      have hP := (qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le t).ne'
      have hW := (qPochhammerInfinity_pos w q).ne'
      have hD := (qPochhammerInfinity_pos (q ^ t * w) q).ne'
      field_simp [hP, hW, hD]
      <;> ring
  have hv : Summable v := (actualGeneratingTerm_summable hq0 hq1 hw0 hw1).div_const _
  have hrowsum : Summable (fun t => ∑' k, f t k) := by
    have he : (fun t => ∑' k, f t k) = v := funext (fun t => (hrow t).tsum_eq)
    rw [he]
    exact hv
  have hf := summable_rows_nonneg hf0 (fun t => (hrow t).summable) hrowsum
  have he : (∑' p : ℕ × ℕ, f p.1 p.2) = actualGeneratingFunction q w := by
    rw [tsum_product_eq_rows hf (fun t => (hrow t).summable) hrowsum]
    simp_rw [(hrow _).tsum_eq]
    simp only [v, actualGeneratingFunction, tsum_div_const]
  have h := hasSum_antidiagonal hf
  rw [he] at h
  refine h.congr_fun (fun k => ?_)
  unfold actualGamma
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpk : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
  simp only [f, hpk]

noncomputable def actualAtomWeight (q : ℝ) (k : ℕ) : ℝ :=
  (qPochhammerInfinity q q) ^ 4 * actualGamma q k * q ^ k

noncomputable def actualMomentHankel (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => actualMoment q (i.val + j.val)

/-- Source-to-measure identity with a HasSum witness for every moment. -/
theorem actualMoment_hasSum_atoms {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    HasSum (fun k : ℕ => actualAtomWeight q k * (q ^ k) ^ m) (actualMoment q m) := by
  have hw0 := pow_nonneg hq0.le (m + 1)
  have hw1 := positive_shift_power_lt_one hq0 hq1 (m + 1) (by omega)
  have h := (actualGamma_hasSum hq0 hq1 hw0 hw1).mul_left
    ((qPochhammerInfinity q q) ^ 4)
  rw [← actual_moment_generating_identity hq0 hq1 m] at h
  refine h.congr_fun (fun k => ?_)
  unfold actualAtomWeight
  have he : (m + 1) * k = k + k * m := by ring
  simp only [← pow_mul, he, pow_add]
  ring

lemma actualAtomWeight_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    0 < actualAtomWeight q k := by
  unfold actualAtomWeight
  exact mul_pos (mul_pos (pow_pos (qPochhammerInfinity_pos q q) 4)
    (lt_of_lt_of_le (by norm_num) (one_le_actualGamma hq0 hq1 k))) (pow_pos hq0 k)

lemma actualAtomWeight_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (actualAtomWeight q) := by
  simpa only [pow_zero, mul_one] using (actualMoment_hasSum_atoms hq0 hq1 0).summable

theorem actualMoment_eq_discreteMoment {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    actualMoment q m = discreteMoment (actualAtomWeight q) (fun k : ℕ => q ^ k) m :=
  (actualMoment_hasSum_atoms hq0 hq1 m).tsum_eq.symm

/-- The named canonical consumer is used with actual, proved suppliers.
There is no row-identity, atom-positivity, or convergence hypothesis here. -/
theorem actualMomentHankel_det_pos {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    0 < (actualMomentHankel q N).det := by
  have he : actualMomentHankel q N =
      discreteMomentHankel (actualAtomWeight q) (fun k : ℕ => q ^ k) N := by
    ext i j
    exact actualMoment_eq_discreteMoment hq0 hq1 (i.val + j.val)
  rw [he]
  exact geometricMomentHankel_det_pos (actualAtomWeight q) q
    (actualAtomWeight_summable hq0 hq1) (actualAtomWeight_pos hq0 hq1) hq0 hq1 N

@[simp] theorem actualMomentHankel_zero_rank (q : ℝ) :
    (actualMomentHankel q 0).det = 1 := by simp

end ErdosProblems.Erdos1049.PaperR16
