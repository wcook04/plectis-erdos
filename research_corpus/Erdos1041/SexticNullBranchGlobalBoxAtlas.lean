import ErdosProblems.Erdos1041.SexticNullBranchFiniteTransfer
import ErdosProblems.Erdos1041.SexticNullBranchUniformMargin

/-!
# Erdős #1041: the full finite sextic null-box atlas

The analytic companion checker reduces each limiting-profile selector cell to
its exact vertices and supplies bivariate Bernstein certificates for their
finite-beta two-jet upper polynomials.  This module formalizes the selector,
small-beta absorption, Taylor transfer, and convex-vertex assembly.
-/

namespace ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas

noncomputable section

open ErdosProblems.Erdos1041.SexticNullBranchSecondOrderAtlas

def betaSplit : ℝ := 1 / 1000000
def centralLocalBudget : ℝ := 56000
def noncentralLocalBudget : ℝ := 40500000

theorem betaSplit_pos : 0 < betaSplit := by
  norm_num [betaSplit]

/-- The central selector vertex retains more than one-half of its normalized
margin throughout the small-beta bridge. -/
theorem central_smallBeta_transfer {β profile actual : ℝ}
    (_hβ0 : 0 ≤ β) (hβ : β ≤ betaSplit)
    (hprofile : profile ≤ (-3 / 5 : ℝ))
    (hactual : actual ≤ β ^ 2 * (profile + centralLocalBudget * β)) :
    actual ≤ -(β ^ 2) / 2 := by
  have hsq : 0 ≤ β ^ 2 := sq_nonneg β
  have hbudget : centralLocalBudget * β ≤ (7 / 125 : ℝ) := by
    unfold centralLocalBudget betaSplit at *
    nlinarith
  have hsum : profile + centralLocalBudget * β ≤ (-68 / 125 : ℝ) := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hsum hsq
  nlinarith

/-- Every noncentral selector vertex starts with normalized margin at least
78, which absorbs the coarse all-box remainder through beta = 10^-6. -/
theorem noncentral_smallBeta_transfer {β profile actual : ℝ}
    (_hβ0 : 0 ≤ β) (hβ : β ≤ betaSplit)
    (hprofile : profile ≤ (-78 : ℝ))
    (hactual : actual ≤ β ^ 2 *
      (profile + noncentralLocalBudget * β)) :
    actual ≤ 0 := by
  have hsq : 0 ≤ β ^ 2 := sq_nonneg β
  have hbudget : noncentralLocalBudget * β ≤ (81 / 2 : ℝ) := by
    unfold noncentralLocalBudget betaSplit at *
    nlinarith
  have hsum : profile + noncentralLocalBudget * β ≤ 0 := by
    linarith
  exact hactual.trans (mul_nonpos_of_nonneg_of_nonpos hsq hsum)

/-- Taylor's theorem hands the finite-beta problem to a certified cubic
upper polynomial once a one-sided third-derivative budget is known. -/
theorem thirdOrder_vertex_transfer {actual twoJet β remainder : ℝ}
    (_hβ0 : 0 ≤ β)
    (htaylor : actual ≤ twoJet + remainder * β ^ 3)
    (hcertificate : twoJet + remainder * β ^ 3 ≤ 0) :
    actual ≤ 0 := by
  exact htaylor.trans hcertificate

/-- An affine chord value is nonpositive on a convex selector cell once it is
nonpositive at every vertex. -/
theorem convexVertex_transfer {n : ℕ} {weight value : Fin n → ℝ}
    {actual : ℝ} (hweight : ∀ i, 0 ≤ weight i)
    (hvalue : ∀ i, value i ≤ 0)
    (haffine : actual = ∑ i, weight i * value i) :
    actual ≤ 0 := by
  rw [haffine]
  exact Finset.sum_nonpos fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (hweight i) (hvalue i)

/-- For a normalized radial derivative `A*y^5 + B*y + C`, the four subset
inequalities suffice on `y ≥ 1`.  The analytic checker instantiates `y5`
with `y^5`. -/
theorem rayDerivative_subset_transfer {A B C y y5 : ℝ}
    (hy : 1 ≤ y) (hy5 : y ≤ y5) (hone : 1 ≤ y5)
    (hA : A ≤ 0) (hAB : A + B ≤ 0)
    (hAC : A + C ≤ 0) (hABC : A + B + C ≤ 0) :
    A * y5 + B * y + C ≤ 0 := by
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hy50 : 0 ≤ y5 := le_trans (by norm_num) hone
  by_cases hB : 0 ≤ B
  · have hBy : B * y ≤ B * y5 := mul_le_mul_of_nonneg_left hy5 hB
    by_cases hC : 0 ≤ C
    · have hCy : C ≤ C * y5 := by nlinarith
      have hsum : (A + B + C) * y5 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hABC hy50
      nlinarith
    · have hC0 : C ≤ 0 := le_of_not_ge hC
      have hsum : (A + B) * y5 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hAB hy50
      nlinarith
  · have hB0 : B ≤ 0 := le_of_not_ge hB
    have hBy : B * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hB0 hy0
    by_cases hC : 0 ≤ C
    · have hCy : C ≤ C * y5 := by nlinarith
      have hsum : (A + C) * y5 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hAC hy50
      nlinarith
    · have hC0 : C ≤ 0 := le_of_not_ge hC
      have hAy : A * y5 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA hy50
      linarith

/-- Four real profiles always have a minimizing selector cell. -/
theorem four_way_minimum (a b c d : ℝ) :
    (a ≤ b ∧ a ≤ c ∧ a ≤ d) ∨
    (b ≤ a ∧ b ≤ c ∧ b ≤ d) ∨
    (c ≤ a ∧ c ≤ b ∧ c ≤ d) ∨
    (d ≤ a ∧ d ≤ b ∧ d ≤ c) := by
  rcases le_total a b with hab | hba
  · rcases le_total c d with hcd | hdc
    · rcases le_total a c with hac | hca
      · exact Or.inl ⟨hab, hac, hac.trans hcd⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hca, hca.trans hab, hcd⟩))
    · rcases le_total a d with had | hda
      · exact Or.inl ⟨hab, had.trans hdc, had⟩
      · exact Or.inr (Or.inr (Or.inr ⟨hda, hda.trans hab, hdc⟩))
  · rcases le_total c d with hcd | hdc
    · rcases le_total b c with hbc | hcb
      · exact Or.inr (Or.inl ⟨hba, hbc, hbc.trans hcd⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hcb.trans hba, hcb, hcd⟩))
    · rcases le_total b d with hbd | hdb
      · exact Or.inr (Or.inl ⟨hba, hbd.trans hdc, hbd⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨hdb.trans hba, hdb, hdc⟩))

theorem profile_selector_cell (p q r : ℝ) :
    (profilePP p q r ≤ profileNP p q r ∧
      profilePP p q r ≤ profileNN p q r ∧
      profilePP p q r ≤ profilePN p q r) ∨
    (profileNP p q r ≤ profilePP p q r ∧
      profileNP p q r ≤ profileNN p q r ∧
      profileNP p q r ≤ profilePN p q r) ∨
    (profileNN p q r ≤ profilePP p q r ∧
      profileNN p q r ≤ profileNP p q r ∧
      profileNN p q r ≤ profilePN p q r) ∨
    (profilePN p q r ≤ profilePP p q r ∧
      profilePN p q r ≤ profileNP p q r ∧
      profilePN p q r ≤ profileNN p q r) := by
  exact four_way_minimum _ _ _ _

end

end ErdosProblems.Erdos1041.SexticNullBranchGlobalBoxAtlas
