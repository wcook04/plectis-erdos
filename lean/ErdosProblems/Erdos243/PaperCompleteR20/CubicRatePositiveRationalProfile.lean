import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateRationalProfile

/-!
# Erdős 243: positivity of the rational cubic coefficient

The eventual cubic obtained from the literal ratio estimate has a nonnegative
leading coefficient because the original sequence is positive.  Vanishing of
that coefficient would make the sequence eventually constant, contradicting
the same literal ratio estimate at scale `n^3`.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

theorem leading_coefficient_pos_of_exact_eventual_cubic
    (C : ℕ → ℤ) (K B : ℝ) (N : ℕ)
    (hpos : ∀ n, 0 < C n)
    (hprofile : ∀ n, N ≤ n → (C n : ℝ) = K * risingCubic n + B)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    0 < K := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [inv_pow] using hbase.pow 3
  have hcubic : Tendsto (fun n : ℕ => (C n : ℝ) / (n : ℝ) ^ 3)
      atTop (nhds K) := by
    have hmodel : Tendsto
        (fun n : ℕ => K * (risingCubic n / (n : ℝ) ^ 3) +
          B * ((n : ℝ) ^ 3)⁻¹) atTop (nhds K) := by
      convert (tendsto_const_nhds.mul risingCubic_div_cube_tendsto_one).add
        (tendsto_const_nhds.mul hinv) using 1 <;> ring
    apply hmodel.congr'
    filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hprofile n hn⟩,
      eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    rw [hn]
    field_simp [hnpos.ne'] <;> ring
  have hKnonneg : 0 ≤ K := by
    apply ge_of_tendsto hcubic
    filter_upwards [] with n
    exact div_nonneg (by exact_mod_cast (le_of_lt (hpos n))) (by positivity)
  have hKne : K ≠ 0 := by
    intro hKzero
    have hsmall : ∀ᶠ n : ℕ in atTop,
        dist ((n : ℝ) ^ 3 * cubicRatioError (fun j => (C j : ℝ)) n) 0 < 1 :=
      (Metric.tendsto_nhds.1 hratio) 1 zero_lt_one
    obtain ⟨M, hM⟩ := eventually_atTop.1 hsmall
    let n := max (max N M) 1
    have hnN : N ≤ n := by simp [n]
    have hnM : M ≤ n := by simp [n]
    have hnpos : 0 < n := by simp [n]
    have hn1N : N ≤ n + 1 := by omega
    have hn := hprofile n hnN
    have hn1 := hprofile (n + 1) hn1N
    rw [hKzero, zero_mul, zero_add] at hn hn1
    have hCn : (C n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hpos n))
    have hB : B ≠ 0 := by
      rw [← hn]
      exact hCn
    have hbad := hM n hnM
    have herr : (n : ℝ) ^ 3 *
        cubicRatioError (fun j => (C j : ℝ)) n = -3 * (n : ℝ) ^ 2 := by
      simp only [cubicRatioError, hn, hn1, div_self hB]
      field_simp [hnpos.ne'] <;> ring
    rw [herr, Real.dist_eq, sub_zero] at hbad
    rw [abs_of_nonpos (by nlinarith [sq_nonneg (n : ℝ)] : -3 * (n : ℝ) ^ 2 ≤ 0)] at hbad
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hnpos]
  exact lt_of_le_of_ne hKnonneg (Ne.symm hKne)

theorem literal_ratio_error_gives_positive_rational_eventual_cubic
    (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A D : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (D : ℝ) := by
  obtain ⟨K, B, N, hprofile⟩ :=
    literal_ratio_error_gives_exact_eventual_cubic C hpos hratio
  have hKpos := leading_coefficient_pos_of_exact_eventual_cubic
    C K B N hpos hprofile hratio
  let m : ℤ := iterIntForwardDiff 3 C N
  have hm : (m : ℝ) = 6 * K := by
    have h0 := hprofile N (le_rfl)
    have h1 := hprofile (N + 1) (by omega)
    have h2 := hprofile (N + 2) (by omega)
    have h3 := hprofile (N + 3) (by omega)
    dsimp [m]
    simp only [iterIntForwardDiff, intForwardDiff, Int.cast_sub]
    simp [risingCubic] at h0 h1 h2 h3
    push_cast
    linear_combination h3 - 3 * h2 + 3 * h1 - h0
  let A : ℚ := (m : ℚ) / 6
  have hA : (A : ℝ) = K := by
    dsimp [A]
    push_cast
    linarith
  let D : ℚ := (C N : ℚ) - A *
    (N : ℚ) * ((N : ℚ) + 1) * ((N : ℚ) + 2)
  have hD : (D : ℝ) = B := by
    have h0 := hprofile N (le_rfl)
    dsimp [D]
    push_cast
    rw [hA]
    simp [risingCubic] at h0 ⊢
    linarith
  refine ⟨A, D, ?_, N, ?_⟩
  · have hAposR : (0 : ℝ) < (A : ℝ) := hA.symm ▸ hKpos
    exact_mod_cast hAposR
  · intro n hn
    rw [hprofile n hn, hA, hD]

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.leading_coefficient_pos_of_exact_eventual_cubic
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_positive_rational_eventual_cubic

end ErdosProblems.Erdos243.PaperCompleteR20
