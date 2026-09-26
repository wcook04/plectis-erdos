import ErdosProblems.Erdos257.PaperCompleteR8.ReverseStrengthenedHost

/-!
# Cover-independent fixed-exponent means and the reverse host

The total-cost fixed-exponent class is stated literally, separately from
both variable-exponent classes. No estimate for a chosen decomposition is
mistaken for an obstruction to every decomposition.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

def finiteFractionalMean (F : Finset ℕ) (α : ℝ) (X : ℕ) : ℝ :=
  (∑ n ∈ Icc 1 X, ((F.filter (fun a => a ∣ n)).card : ℝ) ^ α) / X

/-- The old fixed-alpha positive-majorant class with finite *total* cost.
The stronger enumeration-weighted hypotheses imply this class, but are not
silently substituted for it. -/
def HasFixedExponentPositiveCover (A : Set ℕ) (α : ℝ) : Prop :=
  0 < α ∧ α ≤ 1 ∧ ∃ C : PositiveCoverData, A ⊆ C.host ∧
    (∀ j, C.exponent j = α) ∧ Summable C.cost

theorem finiteFractionalMean_le_total_cost (C : PositiveCoverData)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hconst : ∀ j, C.exponent j = α)
    (hs : Summable C.cost) (F : Finset ℕ) (hF : (F : Set ℕ) ⊆ C.host)
    (X : ℕ) (hX : 0 < X) :
    finiteFractionalMean F α X ≤ ∑' j, C.cost j := by
  classical
  obtain ⟨J, hFJ⟩ := exists_finite_frame_subcover F C.frame (fun a ha => hF ha)
  have hpoint : ∀ n : ℕ,
      ((F.filter (fun a => a ∣ n)).card : ℝ) ^ α ≤
        ∑ j ∈ J, (((C.frame j).filter (fun a => a ∣ n)).card : ℝ) ^ α := by
    intro n
    have hcov : ((F.filter (fun a => a ∣ n)).card : ℝ) ≤
        ∑ j ∈ J, (((C.frame j).filter (fun a => a ∣ n)).card : ℝ) := by
      exact_mod_cast divisor_count_le_sum_of_frame_cover F J C.frame hFJ n
    exact (Real.rpow_le_rpow (Nat.cast_nonneg _) hcov hα.le).trans
      (rpow_sum_le_sum_rpow J
        (fun j => (((C.frame j).filter (fun a => a ∣ n)).card : ℝ))
        (fun _ => Nat.cast_nonneg _) hα hα1)
  calc
    finiteFractionalMean F α X ≤
        (∑ n ∈ Icc 1 X, ∑ j ∈ J,
          (((C.frame j).filter (fun a => a ∣ n)).card : ℝ) ^ α) / X :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ => hpoint n)) (Nat.cast_nonneg X)
    _ = ∑ j ∈ J, (∑ n ∈ Icc 1 X,
          (((C.frame j).filter (fun a => a ∣ n)).card : ℝ) ^ α) / X := by
      rw [Finset.sum_comm, Finset.sum_div]
    _ ≤ ∑ j ∈ J, C.cost j := by
      apply Finset.sum_le_sum
      intro j hj
      apply cesaro_le_tsum_divisorMajorantCost
        (fun n => (((C.frame j).filter (fun a => a ∣ n)).card : ℝ) ^ α)
        (C.coefficient j) X hX (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (C.coefficient_nonneg j) (C.column_summable j)
      intro n hn
      simpa only [hconst j] using C.majorises j n hn
    _ ≤ _ := hs.sum_le_tsum J (fun j _ => positiveCover_cost_nonneg C j)

/-- Unbounded finite periodic alpha-means exclude every finite-total-cost
fixed-alpha cover, independently of all frame choices and overlaps. -/
theorem no_fixed_cover_of_unbounded_fractional_means (A : Set ℕ) (α : ℝ)
    (hlarge : ∀ T : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∃ X : ℕ, 0 < X ∧ T < finiteFractionalMean F α X) :
    ¬ HasFixedExponentPositiveCover A α := by
  rintro ⟨hα, hα1, C, hAC, hconst, hs⟩
  obtain ⟨F, hFA, X, hX, hT⟩ := hlarge (∑' j, C.cost j)
  exact (not_lt_of_ge
    (finiteFractionalMean_le_total_cost C hα hα1 hconst hs F (hFA.trans hAC) X hX)) hT

theorem reverseHost_unbounded_fixed_moments {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ T : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ reverseHost ∧
      ∃ X : ℕ, 0 < X ∧ T < finiteFractionalMean F α X := by
  intro T
  let z : ℝ := (2 : ℝ) ^ α - 1
  have hz : 0 < z := sub_pos.mpr (Real.one_lt_rpow (by norm_num) hα)
  have hz1 : z ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
    rw [Real.rpow_one] at hh
    dsimp [z]
    linarith
  let c : ℝ := z ^ 2 / 4
  have hc : 0 < c := div_pos (sq_pos_of_pos hz) (by norm_num)
  obtain ⟨j, hj, hT⟩ := exists_large_square_multiple c T hc 0
  let R := reverseRow j
  have hP : ∀ p ∈ R.primes, Nat.Prime p := fun p hp => (R.primes_large p hp).1
  have hm := mul_le_mul_of_nonneg_left R.square_mass_ratio hc.le
  have hprod := cubeProductCost_quadratic_lower R.q R.primes z hP hz.le hz1
  have hlow : c * (((j + 1 : ℕ) : ℝ) ^ 2) ≤ cubeProductCost R.q R.primes z := by
    exact hm.trans (by convert hprod using 1 <;> dsimp [c] <;> ring)
  refine ⟨(reverseFrame j).support, (fun a ha => ⟨j, ha⟩),
    R.q * R.primes.prod id, Nat.mul_pos R.q_prime.pos (prime_product_pos _ hP), ?_⟩
  change T < finiteFractionalMean (divisorCube R.q R.primes) α _
  unfold finiteFractionalMean
  rw [cube_fractional_mean R.q R.primes α R.q_prime.pos hP hα]
  exact hT.trans_le hlow

/-- The same single constructed support excludes every admissible fixed alpha. -/
theorem reverseHost_no_fixed_exponent_cover {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ¬ HasFixedExponentPositiveCover reverseHost α :=
  no_fixed_cover_of_unbounded_fractional_means reverseHost α
    (reverseHost_unbounded_fixed_moments hα hα1)

end ErdosProblems.Erdos257.PaperCompleteR8
end
