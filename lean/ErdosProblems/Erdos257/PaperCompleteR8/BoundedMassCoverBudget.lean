import ErdosProblems.Erdos257.PaperCompleteR8.BoundedMassPrimeRows
import ErdosProblems.Erdos257.PaperCompleteR8.IndexedCubeCover

/-!
# A strengthened cover for the literal bounded-mass prime rows

The product window controls the first prime-reciprocal moment. Applying
`log x <= x - 1` to `q / 4^(j+1)` then bounds the indexed cover budget by
a linear polynomial times `4^(-(j+1))`. This uses the lower bound on q
only in a denominator comparison; it never upper-bounds log q by log 4^(j+1).

The resulting cover uses the actual rows selected in BoundedMassPrimeRows.
Reciprocal divergence and exclusion of every finite-prime weighted class
are separate conclusions. Validation authority is the exact source-hashed
Lean exit and axiom receipt, not this module's prose.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

/-- The existing exponential product estimate is sufficient with constant two. -/
theorem boundedMassPrimeRow_primeMass_le (j : ℕ) :
    primeReciprocalMass (boundedMassPrimeRow j).primes ≤
      2 * (Real.log (4 / 3) + Real.log ((boundedMassPrimeRow j).q : ℝ)) := by
  let R := boundedMassPrimeRow j
  have hP : ∀ p ∈ R.primes, Nat.Prime p := fun p hp => (R.primes_spec p hp).1
  have hq : (0 : ℝ) < R.q := by exact_mod_cast R.q_prime.pos
  have he : Real.exp (primeReciprocalMass R.primes / 2) ≤
      ∏ p ∈ R.primes, (1 + (1 : ℝ) / p) := by
    simpa [cubeProductCost] using
      cubeProductCost_exp_lower 1 R.primes 1 hP (by norm_num) (by norm_num)
  have hl : primeReciprocalMass R.primes / 2 ≤ Real.log ((4 / 3) * (R.q : ℝ)) :=
    (Real.le_log_iff_exp_le (by positivity)).mpr (he.trans R.product_upper.le)
  rw [Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0) hq.ne'] at hl
  change primeReciprocalMass R.primes ≤ _
  linarith

/-- A pointwise geometric majorant for the full indexed budget. -/
theorem boundedMassPrimeRow_indexedBudget_le (j : ℕ) :
    indexedCubeBudget j (boundedMassPrimeRow j).primes /
        ((boundedMassPrimeRow j).q : ℝ) ≤
      (((j + 1 : ℕ) : ℝ) * (1 + 2 * Real.log 4) +
        (2 * Real.log (4 / 3) + 2)) / (4 : ℝ) ^ (j + 1) := by
  let R := boundedMassPrimeRow j
  let A : ℝ := 4 ^ (j + 1)
  let C : ℝ := ((j + 1 : ℕ) : ℝ) * (1 + 2 * Real.log 4) + 2 * Real.log (4 / 3)
  have hq : (0 : ℝ) < R.q := by exact_mod_cast R.q_prime.pos
  have hA : 0 < A := by dsimp [A]; positivity
  have hAq : A ≤ (R.q : ℝ) := by
    dsimp [A]
    exact_mod_cast R.q_large
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogc : 0 ≤ Real.log (4 / 3) := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos hq hA)
  rw [Real.log_div hq.ne' hA.ne'] at hl
  have hlogA : Real.log A = ((j + 1 : ℕ) : ℝ) * Real.log 4 := by
    exact Real.log_pow 4 (j + 1)
  rw [hlogA] at hl
  have hmass := boundedMassPrimeRow_primeMass_le j
  have hbudget : indexedCubeBudget j R.primes ≤ C + 2 * ((R.q : ℝ) / A) := by
    dsimp [indexedCubeBudget, C]
    change primeReciprocalMass R.primes ≤ _ at hmass
    linarith
  calc
    indexedCubeBudget j R.primes / (R.q : ℝ) ≤
        (C + 2 * ((R.q : ℝ) / A)) / (R.q : ℝ) :=
      div_le_div_of_nonneg_right hbudget hq.le
    _ = C / (R.q : ℝ) + 2 / A := by field_simp
    _ ≤ C / A + 2 / A :=
      add_le_add (div_le_div_of_nonneg_left hC hA hAq) (le_refl _)
    _ = _ := by dsimp [C, A]; ring

/-- The constructed rows satisfy the exact hypothesis of IndexedCubeCover. -/
theorem boundedMassPrimeRows_indexedBudget_summable :
    Summable (fun j => indexedCubeBudget j (boundedMassPrimeRow j).primes /
      ((boundedMassPrimeRow j).q : ℝ)) := by
  have hg : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hng : Summable (fun j : ℕ => (j : ℝ) * (1 / 4 : ℝ) ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have hm : Summable (fun j : ℕ =>
      ((j : ℝ) * (1 + 2 * Real.log 4) + (2 * Real.log (4 / 3) + 2)) /
        (4 : ℝ) ^ j) := by
    have h := (hng.mul_left (1 + 2 * Real.log 4)).add
      (hg.mul_left (2 * Real.log (4 / 3) + 2))
    convert h using 1
    ext j
    rw [one_div_pow]
    ring
  have hshift := (summable_nat_add_iff 1).mpr hm
  apply Summable.of_nonneg_of_le _ _ hshift
  · intro j
    exact div_nonneg (le_trans (by norm_num) (indexedCubeBudget_ge_one j _))
      (Nat.cast_nonneg _)
  · exact boundedMassPrimeRow_indexedBudget_le

/-- The literal bounded-mass construction has a strengthened positive cover. -/
theorem boundedMassPrimeRows_hasStrengthenedPositiveCover :
    HasStrengthenedPositiveCover {a : ℕ | ∃ j,
      a ∈ divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes} := by
  apply hasStrengthenedPositiveCover_divisorCubes
    (fun j => (boundedMassPrimeRow j).q) (fun j => (boundedMassPrimeRow j).primes)
    (fun j => (boundedMassPrimeRow j).q_prime.pos)
    (fun j p hp => ((boundedMassPrimeRow j).primes_spec p hp).1)
  exact boundedMassPrimeRows_indexedBudget_summable

#print axioms boundedMassPrimeRows_indexedBudget_summable
#print axioms boundedMassPrimeRows_hasStrengthenedPositiveCover

end ErdosProblems.Erdos257.PaperCompleteR8
end
