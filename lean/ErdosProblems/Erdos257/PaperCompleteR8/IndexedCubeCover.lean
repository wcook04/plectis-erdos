import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCubeCost

/-!
# Divisor-cube covers with the frame-index cost included

For the j-th row put B_j = j + 1 + sum_{p in P_j} 1/p and choose
2^alpha_j - 1 = 1/B_j. The product cost and the frame-index factor
together cost at most exp(1) * B_j / q_j. Thus a summable B_j/q_j
budget constructs an actual strengthened positive cover of the union.

This is the analytic step of the short paper's bounded-mass reverse
construction, reindexed from j >= 1 to j >= 0. It does not construct the
fresh prime rows or assert their reciprocal-mass bounds. Empty prime sets
and overlapping rows are allowed. Validation receipts bind exact source bytes.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

def indexedCubeBudget (j : ℕ) (P : Finset ℕ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) + primeReciprocalMass P

theorem indexedCubeBudget_ge_one (j : ℕ) (P : Finset ℕ) :
    1 ≤ indexedCubeBudget j P := by
  have hS : 0 ≤ primeReciprocalMass P := by
    unfold primeReciprocalMass
    exact sum_nonneg (fun p _ => by positivity)
  have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
  unfold indexedCubeBudget
  linarith

def indexedCubeExponent (j : ℕ) (P : Finset ℕ) : ℝ :=
  exponentFromIncrement (1 / indexedCubeBudget j P)

theorem indexedCubeExponent_bounds (j : ℕ) (P : Finset ℕ) :
    0 < indexedCubeExponent j P ∧ indexedCubeExponent j P ≤ 1 := by
  have hB := indexedCubeBudget_ge_one j P
  have hBpos : 0 < indexedCubeBudget j P := by linarith
  exact exponentFromIncrement_bounds (one_div_pos.mpr hBpos)
    ((div_le_one hBpos).mpr hB)

/-- The product and geometric factor share one exponential budget. -/
theorem indexed_cube_strengthened_cost_le (j q : ℕ) (P : Finset ℕ) (hq : 0 < q) :
    cubeProductCost q P ((2 : ℝ) ^ indexedCubeExponent j P - 1) *
      (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * indexedCubeExponent j P) /
      ((2 : ℝ) ^ indexedCubeExponent j P - 1) ≤
      Real.exp 1 * indexedCubeBudget j P / (q : ℝ) := by
  let B := indexedCubeBudget j P
  let z := 1 / B
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) (indexedCubeBudget_ge_one j P)
  have hz : 0 < z := one_div_pos.mpr hB
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : (2 : ℝ) ^ indexedCubeExponent j P = 1 + z :=
    two_rpow_exponentFromIncrement hz
  have hinc : (2 : ℝ) ^ indexedCubeExponent j P - 1 = z := by rw [hpow]; ring
  have hfactor : (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * indexedCubeExponent j P) ≤
      Real.exp (((j + 1 : ℕ) : ℝ) * z) := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_natCast, hpow]
    have hbase : 1 + z ≤ Real.exp z := by
      simpa only [add_comm] using Real.add_one_le_exp z
    exact (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + z) hbase (j + 1)).trans_eq
      (Real.exp_nat_mul z (j + 1)).symm
  have hsum : z * primeReciprocalMass P + ((j + 1 : ℕ) : ℝ) * z = 1 := by
    calc
      _ = (((j + 1 : ℕ) : ℝ) + primeReciprocalMass P) / B := by dsimp [z]; ring
      _ = 1 := div_self hB.ne'
  have hmul := mul_le_mul (cubeProductCost_le_exp q P z hz.le) hfactor
    (Real.rpow_nonneg (by norm_num) _) (div_nonneg (Real.exp_pos _).le hqR.le)
  have hexp : Real.exp (z * primeReciprocalMass P) / (q : ℝ) *
      Real.exp (((j + 1 : ℕ) : ℝ) * z) = Real.exp 1 / (q : ℝ) := by
    rw [div_mul_eq_mul_div, ← Real.exp_add, hsum]
  rw [hexp] at hmul
  rw [hinc]
  have hdiv := div_le_div_of_nonneg_right hmul hz.le
  exact hdiv.trans_eq (by dsimp [z, B]; field_simp [hB.ne', hqR.ne'])

def indexedCubeFrame (q : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (hq : ∀ j, 0 < q j) (hP : ∀ j p, p ∈ P j → Nat.Prime p) (j : ℕ) :
    FiniteCoverFrame :=
  cubeCoverFrame (q j) (P j) (indexedCubeExponent j (P j)) (hq j) (hP j)
    (indexedCubeExponent_bounds j (P j)).1 (indexedCubeExponent_bounds j (P j)).2

def indexedCubeCover (q : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (hq : ∀ j, 0 < q j) (hP : ∀ j p, p ∈ P j → Nat.Prime p) : PositiveCoverData where
  frame := fun j => (indexedCubeFrame q P hq hP j).support
  exponent := fun j => indexedCubeExponent j (P j)
  coefficient := fun j => (indexedCubeFrame q P hq hP j).coefficient
  frame_positive := fun j => (indexedCubeFrame q P hq hP j).positive
  exponent_bounds := fun j => indexedCubeExponent_bounds j (P j)
  coefficient_nonneg := fun j => (indexedCubeFrame q P hq hP j).coefficient_nonneg
  column_summable := fun j => (indexedCubeFrame q P hq hP j).column_summable
  majorises := fun j => (indexedCubeFrame q P hq hP j).majorises

theorem indexedCubeCover_strengthened (q : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (hq : ∀ j, 0 < q j) (hP : ∀ j p, p ∈ P j → Nat.Prime p)
    (hbudget : Summable (fun j => indexedCubeBudget j (P j) / (q j : ℝ))) :
    (indexedCubeCover q P hq hP).StrengthenedCostSummable := by
  apply Summable.of_nonneg_of_le _ _ (hbudget.mul_left (Real.exp 1))
  · intro j
    exact div_nonneg
      (mul_nonneg (positiveCover_cost_nonneg (indexedCubeCover q P hq hP) j)
        (Real.rpow_nonneg (by norm_num) _))
      (sub_pos.mpr (Real.one_lt_rpow (by norm_num)
        (indexedCubeExponent_bounds j (P j)).1)).le
  · intro j
    change (indexedCubeFrame q P hq hP j).cost *
      (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * indexedCubeExponent j (P j)) /
      ((2 : ℝ) ^ indexedCubeExponent j (P j) - 1) ≤ _
    rw [indexedCubeFrame, cubeCoverFrame_cost]
    simpa only [mul_div_assoc] using indexed_cube_strengthened_cost_le j (q j) (P j) (hq j)

/-- A summable indexed first-moment budget constructs the full cover, including
the frame-index factor. No row disjointness or growth hypothesis is hidden. -/
theorem hasStrengthenedPositiveCover_divisorCubes (q : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (hq : ∀ j, 0 < q j) (hP : ∀ j p, p ∈ P j → Nat.Prime p)
    (hbudget : Summable (fun j =>
      (((j + 1 : ℕ) : ℝ) + primeReciprocalMass (P j)) / (q j : ℝ))) :
    HasStrengthenedPositiveCover {a : ℕ | ∃ j, a ∈ divisorCube (q j) (P j)} := by
  exact ⟨indexedCubeCover q P hq hP, Set.Subset.refl _,
    indexedCubeCover_strengthened q P hq hP hbudget⟩

#print axioms indexed_cube_strengthened_cost_le
#print axioms hasStrengthenedPositiveCover_divisorCubes

end ErdosProblems.Erdos257.PaperCompleteR8
end
