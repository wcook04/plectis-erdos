import ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz

/-!
# Erdős 1041: sparse-defect survivor selector kernels

The companion note proves an actual-polynomial no-go for deleting Gram-bad
roots and strengthens the returned product-age selector to use only surviving
roots.  This module checks the algebraic fan-in and exact star fractions.  The
general finite AM--GM step and polynomial merge geometry remain in the
ordinary proof.
-/

namespace ErdosProblems.Erdos1041.SparseDefectSurvivorSelector20260826

/-- Once finite AM--GM bounds the complementary survivor product, multiplying
by the selected pair gives the squared survivor-local selector. -/
theorem survivorProductSq_le_pairSq_mul_energyPow
    {survivorProductSq pairSq complementProductSq complementCardPow
      complementEnergyPow : ℝ}
    (hpair : 0 ≤ pairSq)
    (hfactor : survivorProductSq = pairSq * complementProductSq)
    (hamgm : complementProductSq * complementCardPow ≤ complementEnergyPow) :
    survivorProductSq * complementCardPow ≤ pairSq * complementEnergyPow := by
  rw [hfactor, mul_assoc]
  exact mul_le_mul_of_nonneg_left hamgm hpair

/-- With exactly three survivors the complementary AM--GM step has one term,
so the sharp product inequality is immediate and carries no averaging loss. -/
theorem threeSurvivor_productSq_le
    {qi qj qk survivorProductSq survivorEnergy : ℝ}
    (hproduct : survivorProductSq = (qi * qj * qk) ^ 2)
    (henergy : qk ^ 2 ≤ survivorEnergy) :
    survivorProductSq ≤ (qi * qj) ^ 2 * survivorEnergy := by
  calc
    survivorProductSq = (qi * qj) ^ 2 * qk ^ 2 := by
      rw [hproduct]
      ring
    _ ≤ (qi * qj) ^ 2 * survivorEnergy :=
      mul_le_mul_of_nonneg_left henergy (sq_nonneg (qi * qj))

/-- ER4 transports a lower bound for the discounted energy product to the
same pair of entrance-charge squares. -/
theorem er4_pair_transport
    {betaPow zi zj qiSq qjSq lower : ℝ}
    (hbeta : 0 ≤ betaPow)
    (hi : qiSq = betaPow * zi)
    (hj : qjSq = betaPow * zj)
    (hlower : lower ≤ zi * zj) :
    betaPow ^ 2 * lower ≤ qiSq * qjSq := by
  rw [hi, hj]
  have hsq : 0 ≤ betaPow ^ 2 := sq_nonneg betaPow
  calc
    betaPow ^ 2 * lower ≤ betaPow ^ 2 * (zi * zj) :=
      mul_le_mul_of_nonneg_left hlower hsq
    _ = (betaPow * zi) * (betaPow * zj) := by ring

/-- In the star family the central root carries fraction `(n-1)/n` of the
ER4 mass. -/
theorem starCentral_mass_fraction
    {n : ℝ} (hn : n ≠ 0) :
    (n - 1) ^ 2 / (n * (n - 1)) = (n - 1) / n := by
  by_cases hn1 : n = 1
  · subst n
    norm_num
  · field_simp [hn, hn1]
    ring

/-- Deleting the central star root leaves exactly fraction `1/n`. -/
theorem starSurvivor_mass_fraction
    {n : ℝ} (hn : n ≠ 0) (hn1 : n ≠ 1) :
    (n - 1) / (n * (n - 1)) = 1 / n := by
  field_simp [hn, hn1]

/-- The central/outer entrance-charge ratio implies the exact total square
mass `n(n-1)q^2`. -/
theorem star_total_mass_identity {n q : ℝ} :
    ((n - 1) * q) ^ 2 + (n - 1) * q ^ 2 = n * (n - 1) * q ^ 2 := by
  ring

/-- Cross-multiplied form of the statement that any two equal outer rows of
the star carry fraction `2/[n(n-1)]` of the total ER4 mass. -/
theorem starTwoSurvivor_mass_fraction_cross {n q : ℝ} :
    (2 * q ^ 2) * (n * (n - 1)) =
      2 * (((n - 1) * q) ^ 2 + (n - 1) * q ^ 2) := by
  ring

end ErdosProblems.Erdos1041.SparseDefectSurvivorSelector20260826
