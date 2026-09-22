import ErdosProblems.Erdos243.PaperCompleteR20.CubicRateProductAsymptotic

/-!
# Erdős 243: the integer endpoint of the cubic-rate argument

The literal multiplicative little-o hypothesis now reaches the discrete
conclusion directly: the third integer forward difference is eventually
constant.  All analytic limit and residual data are produced internally.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

theorem literal_ratio_error_gives_eventually_constant_third_difference
    (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by
  have hC : ∀ᶠ n in atTop, (C n : ℝ) ≠ 0 := by
    filter_upwards [] with n
    exact_mod_cast (ne_of_gt (hpos n))
  obtain ⟨K, r, hdecomp, hcubic, hsublinear⟩ :=
    cubic_size_and_residual_of_literal_ratio_error
      (fun n : ℕ => (C n : ℝ)) hC hratio
  exact cubic_ratio_and_residual_estimates_give_eventually_constant_third_difference
    C K r hpos hdecomp hcubic hratio hsublinear

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.literal_ratio_error_gives_eventually_constant_third_difference

end ErdosProblems.Erdos243.PaperCompleteR20
