/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos243.PaperCompleteR21.SquareSpecialisationUnconditional

/-!
# Formal Conjectures adapter for the Erdős 243 cubic-rate variant

This makes the reciprocal-series convergence implicit in the cubic-rate paper theorem explicit
in Lean, then exposes the zero-indexed theorem with `tsum`, as Formal Conjectures states it.
The index is not shifted: the `3/n` term and cubic-order remainder refer to the same `n` as
the public unconditional theorem.
-/

namespace ErdosProblems.Erdos243.FormalConjecturesAdapter

open Filter
open scoped Topology

/-- The cubic rate forces the reciprocal series to converge. -/
theorem summable_reciprocal_of_cubic_rate (a : ℕ → ℕ)
    (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ)))) atTop (𝓝 0)) :
    Summable (fun n : ℕ => 1 / (a n : ℝ)) := by
  have hgrowth := ErdosProblems.Erdos243.PaperCompleteR20.cubic_rate_gives_quadratic_growth
    a hrate
  have hratio := ErdosProblems.Erdos243.PaperCompleteR7.reciprocal_successive_ratio_tendsto_zero
    a ha hpos hgrowth
  have hnonzero : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (a n : ℝ) ≠ 0 :=
    Filter.Eventually.of_forall fun n =>
      ne_of_gt (one_div_pos.mpr (by exact_mod_cast hpos n))
  have hnorm : (fun n : ℕ => ‖(1 : ℝ) / (a (n + 1) : ℝ)‖ /
      ‖(1 : ℝ) / (a n : ℝ)‖) =
      (fun n : ℕ => ((1 : ℝ) / (a (n + 1) : ℝ)) /
        ((1 : ℝ) / (a n : ℝ))) := by
    funext n
    have hn : 0 < (1 : ℝ) / (a n : ℝ) :=
      one_div_pos.mpr (by exact_mod_cast hpos n)
    have hn1 : 0 < (1 : ℝ) / (a (n + 1) : ℝ) :=
      one_div_pos.mpr (by exact_mod_cast hpos (n + 1))
    simp only [Real.norm_eq_abs, abs_of_pos hn, abs_of_pos hn1]
  have hratio' : Tendsto (fun n : ℕ => ‖(1 : ℝ) / (a (n + 1) : ℝ)‖ /
      ‖(1 : ℝ) / (a n : ℝ)‖) atTop (𝓝 0) := by
    rw [hnorm]
    exact hratio
  exact summable_of_ratio_test_tendsto_lt_one (by norm_num : (0 : ℝ) < 1)
    hnonzero hratio'

/-- The statement of the Formal Conjectures zero-indexed cubic-rate variant. -/
theorem erdos_243_variants_cubic_rate (a : ℕ → ℕ)
    (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ)))) atTop (𝓝 0)) :
    Irrational (∑' n : ℕ, 1 / (a n : ℝ)) := by
  have hsum := summable_reciprocal_of_cubic_rate a ha hpos hrate
  exact ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional
    a ha hpos hrate _ hsum.hasSum

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional
#print axioms ErdosProblems.Erdos243.FormalConjecturesAdapter.erdos_243_variants_cubic_rate

end ErdosProblems.Erdos243.FormalConjecturesAdapter
