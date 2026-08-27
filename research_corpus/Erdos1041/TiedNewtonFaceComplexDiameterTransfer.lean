import ErdosProblems.Erdos1041.ReciprocalNewtonExpansion
import ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTube
import Mathlib.Tactic

/-!
# Erdős #1041: strict complex-diameter transfer kernel

The analytic companion proves compact convergence, reciprocal-tail rescaling,
and moving-ray assembly.  These lemmas formalize the load-bearing absorption
ledger and the metric-free endpoint composition.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTransfer

/-- A compact model margin survives any uniformly smaller transfer error. -/
theorem compactMargin_absorbs {delta model actual : ℝ}
    (hmodel : model ≤ -delta) (herr : |actual - model| < delta) : actual < 0 := by
  have hdiff : actual - model < delta :=
    lt_of_le_of_lt (le_abs_self (actual - model)) herr
  nlinarith

/-- Beyond twice the model cutoff, half-leading domination plus the two eighth
budgets leaves an exact eighth of the leading term. -/
theorem mesoscopic_absorbs {lead lower coeffError tailError actual : ℝ}
    (hlower : lower ≤ (1 / 2 : ℝ) * lead)
    (hcoeff : coeffError ≤ (1 / 8 : ℝ) * lead)
    (htail : tailError ≤ (1 / 8 : ℝ) * lead)
    (hactual : actual ≤ -(7 / 8 : ℝ) * lead + lower + coeffError + tailError) :
    actual ≤ -(1 / 8 : ℝ) * lead := by
  linarith

theorem mesoscopic_neg {lead lower coeffError tailError actual : ℝ}
    (hlead : 0 < lead) (hlower : lower ≤ (1 / 2 : ℝ) * lead)
    (hcoeff : coeffError ≤ (1 / 8 : ℝ) * lead)
    (htail : tailError ≤ (1 / 8 : ℝ) * lead)
    (hactual : actual ≤ -(7 / 8 : ℝ) * lead + lower + coeffError + tailError) :
    actual < 0 := by
  have h := mesoscopic_absorbs hlower hcoeff htail hactual
  linarith

/-- Uniform polynomial/direction convergence on a fixed collar preserves the
regular-polygon gap `gamma`. -/
theorem outerCollar_absorbs {gamma baseline error actual : ℝ}
    (hbaseline : baseline ≤ 1 - gamma)
    (herror : error < gamma) (hactual : actual ≤ baseline + error) :
    actual < 1 := by
  nlinarith

/-- R4 converts containment of the transferred staple into the strict target
length without spending any uniform margin. -/
theorem transferredStaple_length_lt_two {A B s c : ℝ}
    (hA : A < 1) (hB : B < 1) (hs : 0 ≤ s) (hc : c ≤ 2) :
    A + B - s * (2 - c) < 2 :=
  ReciprocalNewtonExpansion.staple_length_lt_two hA hB hs hc

theorem rationalBudgetLedger :
    (-(7 / 8 : ℝ) + 1 / 2 + 1 / 8 + 1 / 8) = -1 / 8 := by
  norm_num

end ErdosProblems.Erdos1041.TiedNewtonFaceComplexDiameterTransfer
