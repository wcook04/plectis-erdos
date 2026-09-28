-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.ArgumentGraph.AbduceCorpus
import ErdosProblems.ArgumentGraph.Results.Erdos249Endpoint

/-!
# Erdős #249: the count of good bases eliminated by abduction

`Results/Erdos249Endpoint.lean` proves by hand that a support of average first cosine at most
`9/10` gives the irrationality of `∑ φ(n)/2^n` (`irrational_totient_series_of_support_gap`), and
that the good-base gap at `603X/1000` gives such a support (`irrational_totient_series_of_goodBase_gap`).
Here the arithmetic of the second step is computed. `restate` reads the subset-barrier clause on
the good bases at the minimal depth, for arbitrarily large `X`, against one supplier, the count of
the good bases (`eventually_card_pivotGoodBases_gt`, which holds for all large `X`); it uses the
count at each frequent scale and eliminates it, and what is left is the good-base gap at
`603/1000 = 9/10 · 67/100`; `goodBaseClause_of_goodBaseGap` holds by definition only because the
computed restatement is that statement. The full chain from the support interface, where the depth
and the support are chosen as witnesses, is not in this module.

The first section records the calibrations of the `abduce` tactic: with the scale normalised to
one it recovers the thresholds `603/1000` (subset) and `57/100` (whole block) from the budgets
alone, and on the #249 clause it eliminates the count and leaves the bound in terms of `X`.
-/

open Filter Finset
open ErdosProblems.ArgumentGraph.Abduce Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Erdos249.PaperCompleteR21

namespace ErdosProblems.ArgumentGraph.Results.Erdos249Abduction

/-! ## Calibrations of `abduce` -/

/-- The subset calibration with the scale normalised to one: shares `m`, `b`, `u` of good, bad
and non-supplier bases, `g` the good-base cosine sum and `γ` its bound. Only `γ` is observable;
the threshold is computed. -/
theorem subset_threshold (m b u g γ : ℝ) (hp : m + b + u = 1) (hb0 : 0 ≤ b)
    (hb : b < 1 / 100) (hu0 : 0 ≤ u) (hu : u < 8 / 25) (hg1 : -m ≤ g) (hg2 : g ≤ m)
    (hγ : g ≤ γ) (hgap : γ ≤ 603 / 1000) : g ≤ 9 / 10 * m := by
  abduce [γ] using hp, hb0, hb, hu0, hu, hg1, hg2, hγ
  guard_target = γ ≤ 603 / 1000
  exact hgap

/-- The whole-block alternative pays for the complement: threshold `57/100`. -/
theorem whole_block_threshold (t g b u γ : ℝ) (ht : t ≤ g + b + u) (hb0 : 0 ≤ b)
    (hb : b < 1 / 100) (hu0 : 0 ≤ u) (hu : u < 8 / 25) (hγ : g ≤ γ) (hgap : γ ≤ 57 / 100) :
    t ≤ 9 / 10 := by
  abduce [γ] using ht, hb0, hb, hu0, hu, hγ
  guard_target = γ ≤ 57 / 100
  exact hgap

/-- The subset-barrier clause on the good bases, with the count as the only fact: the count is
eliminated and the bound on the cosine sum in terms of `X` is left. -/
theorem goodBase_clause (h X L : ℕ)
    (hcard : (67 / 100 : ℝ) * X < ((pivotGoodBases X L 26 (1 / 1000 : ℝ)).card : ℝ))
    (hgap : ∑ N ∈ pivotGoodBases X L 26 (1 / 1000 : ℝ), windowFirstCos h N L ≤
      603 / 1000 * (X : ℝ)) :
    ∑ N ∈ pivotGoodBases X L 26 (1 / 1000 : ℝ), windowFirstCos h N L ≤
      9 / 10 * ((pivotGoodBases X L 26 (1 / 1000 : ℝ)).card : ℝ) := by
  abduce using hcard
  guard_target = ∑ N ∈ pivotGoodBases X L 26 (1 / 1000 : ℝ), windowFirstCos h N L ≤
      603 / 1000 * (X : ℝ)
  exact hgap

/-! ## The clause for arbitrarily large scales -/

/-- The subset-barrier clause on the good bases at the minimal depth, for arbitrarily large
scales. -/
def GoodBaseClause : Prop :=
  ∀ h : ℕ, ∃ᶠ X in atTop,
    (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
      windowFirstCos h N (minimalDepth h 26 X)) ≤
      9 / 10 * ((pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ)).card : ℝ)

/-- The good-base gap for arbitrarily large scales, for every lag. -/
def GoodBaseGap : Prop :=
  ∀ h : ℕ, ∃ᶠ X in atTop,
    (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
      windowFirstCos h N (minimalDepth h 26 X)) ≤ 603 / 1000 * (X : ℝ)

/- `goodBaseClause_of_restated : restatement → GoodBaseClause`, computed. -/
set_option maxHeartbeats 4000000 in
restate goodBaseClause_of_restated for GoodBaseClause using eventually_card_pivotGoodBases_gt

/-- The restatement is the good-base gap. -/
theorem goodBaseClause_of_goodBaseGap (h : GoodBaseGap) : GoodBaseClause :=
  goodBaseClause_of_restated h

end ErdosProblems.ArgumentGraph.Results.Erdos249Abduction
