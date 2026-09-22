import ErdosProblems.Erdos243.PaperCompleteR20.CutoffWeightConstruction
import ErdosProblems.Erdos243.PaperCompleteR11.IntegralWeights

/-!
# Erdős 243: selecting the cutoff weights

This file supplies the choice step in the forward implication of the short-paper
weight criterion.  `GeometricPrefixVanish` is the cofinal epsilon formulation
used in the proof: beyond every prescribed integer one can find a cutoff at
which the normalised prefix mass is at most `2^-(k+1)`.  The recursively chosen
cutoffs are strictly increasing, grow at least geometrically, and satisfy the
required mass estimates.  Consequently the paper's cutoff weight has finite
weighted mass.

The final passage from this discrete `ENNReal` construction to a finite real
staircase with divergent improper integral is deliberately left to a separate
analytic endpoint: it needs the finite-partial-sum lower bound for the staircase,
not an additional density hypothesis.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open scoped BigOperators ENNReal

/-- Cofinal geometric instances of vanishing normalised prefix density.  This
is the exact epsilon sequence used by the paper's cutoff construction. -/
def GeometricPrefixVanish (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) : Prop :=
  ∀ k N : ℕ, ∃ Y : ℕ, N ≤ Y ∧
    cutoffPrefixMass u w Y ≤ ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ * (Y : ℝ≥0∞)

private noncomputable def chooseGeometricCutoff
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞)
    (h : GeometricPrefixVanish u w) (k N : ℕ) : ℕ :=
  Classical.choose (h k N)

private theorem chooseGeometricCutoff_spec
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞)
    (h : GeometricPrefixVanish u w) (k N : ℕ) :
    N ≤ chooseGeometricCutoff u w h k N ∧
      cutoffPrefixMass u w (chooseGeometricCutoff u w h k N) ≤
        ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ *
          (chooseGeometricCutoff u w h k N : ℝ≥0∞) :=
  Classical.choose_spec (h k N)

/-- Recursive cutoff selection.  At stage `k+1` it asks simultaneously for the
next geometric density bound, the lower bound `2^(k+2)`, and strict growth. -/
def selectedCutoffs
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞)
    (h : GeometricPrefixVanish u w) : ℕ → ℕ
  | 0 => chooseGeometricCutoff u w h 0 2
  | k + 1 => chooseGeometricCutoff u w h (k + 1)
      (max (2 ^ (k + 2)) (selectedCutoffs u w h k + 1))

@[simp] theorem selectedCutoffs_zero
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (h : GeometricPrefixVanish u w) :
    selectedCutoffs u w h 0 = chooseGeometricCutoff u w h 0 2 := rfl

@[simp] theorem selectedCutoffs_succ
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (h : GeometricPrefixVanish u w) (k : ℕ) :
    selectedCutoffs u w h (k + 1) = chooseGeometricCutoff u w h (k + 1)
      (max (2 ^ (k + 2)) (selectedCutoffs u w h k + 1)) := rfl

/-- Every selected cutoff is at least the paper's geometric lower bound. -/
theorem two_pow_le_selectedCutoffs
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (h : GeometricPrefixVanish u w) :
    ∀ k : ℕ, 2 ^ (k + 1) ≤ selectedCutoffs u w h k := by
  intro k
  cases k with
  | zero =>
      simpa using (chooseGeometricCutoff_spec u w h 0 2).1
  | succ k =>
      have hs := (chooseGeometricCutoff_spec u w h (k + 1)
        (max (2 ^ (k + 2)) (selectedCutoffs u w h k + 1))).1
      exact (le_max_left _ _).trans hs

/-- The selected cutoff sequence is strictly increasing. -/
theorem selectedCutoffs_strictMono
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (h : GeometricPrefixVanish u w) :
    StrictMono (selectedCutoffs u w h) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hs := (chooseGeometricCutoff_spec u w h (k + 1)
    (max (2 ^ (k + 2)) (selectedCutoffs u w h k + 1))).1
  have hnext : selectedCutoffs u w h k + 1 ≤ selectedCutoffs u w h (k + 1) :=
    (le_max_right _ _).trans hs
  omega

/-- The selected cutoffs satisfy the exact geometric prefix-mass estimate. -/
theorem selectedCutoffs_prefixMass
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (h : GeometricPrefixVanish u w)
    (k : ℕ) :
    cutoffPrefixMass u w (selectedCutoffs u w h k) ≤
      ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ *
        (selectedCutoffs u w h k : ℝ≥0∞) := by
  cases k with
  | zero => exact (chooseGeometricCutoff_spec u w h 0 2).2
  | succ k =>
      exact (chooseGeometricCutoff_spec u w h (k + 1)
        (max (2 ^ (k + 2)) (selectedCutoffs u w h k + 1))).2

/-- The cutoff weight chosen from vanishing prefix density has total weighted
mass at most one.  This is the complete constructive and Tonelli part of the
forward implication in `res:weights`. -/
theorem weighted_selectedCutoffWeight_le_one
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (h : GeometricPrefixVanish u w) :
    (∑' j : ℕ, w j * cutoffWeight (selectedCutoffs u w h) (u j)) ≤ 1 := by
  apply weighted_cutoffWeight_le_one_of_geometric_prefixMass
  · intro k
    have hk := two_pow_le_selectedCutoffs u w h k
    have : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
    omega
  · exact selectedCutoffs_prefixMass u w h

/-- In particular the weighted mass is finite, with no local-finiteness
assumption on the original prefix sums. -/
theorem weighted_selectedCutoffWeight_ne_top
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (h : GeometricPrefixVanish u w) :
    (∑' j : ℕ, w j * cutoffWeight (selectedCutoffs u w h) (u j)) ≠ ∞ := by
  exact ne_top_of_le_ne_top (by simp) (weighted_selectedCutoffWeight_le_one u w h)

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.two_pow_le_selectedCutoffs
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.selectedCutoffs_strictMono
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.weighted_selectedCutoffWeight_le_one

end ErdosProblems.Erdos243.PaperCompleteR20
