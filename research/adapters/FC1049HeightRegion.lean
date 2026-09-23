/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1049.PaperR17.SourceConsumers

/-!
# Formal Conjectures adapter for an Erdős 1049 rational-base solved variant

This theorem states the proposed Formal Conjectures proposition verbatim. The
source theorem uses a natural-number sum starting at exponent one; the adapter
only changes that index to positive naturals and applies the proved comparison
from the explicit height region to the source contour.
-/

namespace ErdosProblems.Erdos1049.FormalConjecturesAdapter

open ErdosProblems.Erdos1049 ErdosProblems.Erdos1049.PaperR7
  ErdosProblems.Erdos1049.PaperR17

/-- The explicit rational-base region in Formal Conjectures' series notation. -/
theorem erdos_1049_variants_rational_base_region_81_200 :
    ∀ a b : ℕ, 0 < b → b < a → a.Coprime b →
      Real.log b / Real.log a < (81 : ℝ) / 200 →
      Irrational (∑' n : ℕ+, 1 / ((((a : ℝ) / b) ^ (n : ℕ)) - 1)) := by
  intro a b hb hab _hcop hr
  change ZudilinHeightRegion a b at hr
  have hsource := rational_base_region a b hb hab
    (zudilinContourRegion_of_zudilinHeightRegion hr)
  rw [tsum_pnat_eq_tsum_succ]
  exact hsource

#print axioms erdos_1049_variants_rational_base_region_81_200

end ErdosProblems.Erdos1049.FormalConjecturesAdapter
