import ErdosProblems.Erdos257.PaperCompleteR8.PositiveWeightPadding
import ErdosProblems.Erdos257.PaperCompleteR8.DyadicLogarithmicEvents
import Mathlib

/-! Finite positive divisor atoms, with exact costs and exact complete-period means.
Repeated atom conductors are allowed.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset

/-- Push finite atomic masses onto their actual positive conductors. -/
def finiteAtomicCoefficient {ι : Type*} (I : Finset ι) (d : ι → ℕ)
    (w : ι → ℝ) (a : ℕ) : ℝ :=
  ∑ i ∈ I, if a = d i then w i else 0

theorem finiteAtomicCoefficient_nonneg {ι : Type*} (I : Finset ι)
    (d : ι → ℕ) (w : ι → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i) (a : ℕ) :
    0 ≤ finiteAtomicCoefficient I d w a := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact hw i hi
  · exact le_rfl

theorem finiteAtomicCoefficient_column_summable {ι : Type*} (I : Finset ι)
    (d : ι → ℕ) (w : ι → ℝ) :
    Summable (fun a : ℕ => finiteAtomicCoefficient I d w a / (a : ℝ)) := by
  classical
  simp_rw [finiteAtomicCoefficient, Finset.sum_div]
  apply summable_sum
  intro i hi
  apply summable_of_ne_finset_zero (s := {d i})
  intro a ha
  have had : a ≠ d i := by simpa using ha
  simp [had]

theorem finiteAtomicCoefficient_cost {ι : Type*} (I : Finset ι)
    (d : ι → ℕ) (w : ι → ℝ) :
    (∑' a : ℕ, finiteAtomicCoefficient I d w a / (a : ℝ)) =
      ∑ i ∈ I, w i / (d i : ℝ) := by
  classical
  have hs : ∀ i ∈ I, Summable (fun a : ℕ =>
      (if a = d i then w i else 0) / (a : ℝ)) := by
    intro i hi
    apply summable_of_ne_finset_zero (s := {d i})
    intro a ha
    have had : a ≠ d i := by simpa using ha
    simp [had]
  simp_rw [finiteAtomicCoefficient, Finset.sum_div]
  rw [Summable.tsum_finsetSum hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tsum_eq_sum (s := {d i})]
  · simp
  · intro a ha
    have had : a ≠ d i := by simpa using ha
    simp [had]

/-- The conductor sum is literally the incidence sum of the finite atoms. -/
theorem finiteAtomicCoefficient_divisor_sum {ι : Type*} (I : Finset ι)
    (d : ι → ℕ) (w : ι → ℝ) (n : ℕ) (hn : 0 < n) :
    (∑ a ∈ n.divisors, finiteAtomicCoefficient I d w a) =
      ∑ i ∈ I, if d i ∣ n then w i else 0 := by
  classical
  unfold finiteAtomicCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : d i ∣ n
  · have hmem : d i ∈ n.divisors := Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩
    simp [hd, hmem]
  · have hmem : d i ∉ n.divisors := fun h => hd (Nat.dvd_of_mem_divisors h)
    simp [hd, hmem]

/-- The count of positive multiples at a complete period, including X=d. -/
theorem mean_divisibility_atom (d X : ℕ) (hd : 0 < d) (hX : 0 < X)
    (hperiod : d ∣ X) (w : ℝ) :
    (∑ n ∈ Icc 1 X, if d ∣ n then w else 0) / (X : ℝ) = w / (d : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_Icc_one_filter_dvd hd]
  rw [Nat.cast_div hperiod (by exact_mod_cast hd.ne')]
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  <;> ring

theorem mean_finite_divisor_atoms {ι : Type*} (I : Finset ι)
    (d : ι → ℕ) (w : ι → ℝ) (X : ℕ) (hX : 0 < X)
    (hd : ∀ i ∈ I, 0 < d i) (hperiod : ∀ i ∈ I, d i ∣ X) :
    (∑ n ∈ Icc 1 X, ∑ i ∈ I, if d i ∣ n then w i else 0) / (X : ℝ) =
      ∑ i ∈ I, w i / (d i : ℝ) := by
  classical
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  exact mean_divisibility_atom (d i) X (hd i hi) hX (hperiod i hi) (w i)

end ErdosProblems.Erdos257.PaperCompleteR8
end
