import ErdosProblems.Erdos269.PaperR7WindowResults

/-!
# Uniqueness for the full printed eight-scale width

The actual radix product grows as `8^k`, uniformly in the starting scale.
Keep that product in the homogeneous recurrence instead of replacing each
radix by two. This admits exactly the paper's `o(8^k)` width condition.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open PaperR7

theorem actual_orbit_difference (A : ℕ) (y : ℕ → ℝ)
    (hrec : ∀ n, A ≤ n → y (n + 1) =
      (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ))
    (k : ℕ) :
    y (A + k) - trueNormalizedState (A + k) =
      (actualWindowProduct A k : ℝ) * (y A - trueNormalizedState A) := by
  induction k with
  | zero => simp [actualWindowProduct]
  | succ k ih =>
    have h1 := hrec (A + k) (by omega)
    have h2 := dyadicNormalizedShellTsumTailR235_succ (A + k)
    have hts : ∀ n : ℕ, trueNormalizedState n =
        dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 n := fun _ => rfl
    have hdiff : y (A + k + 1) - trueNormalizedState (A + k + 1) =
        (dyadicBlockBase235 (A + k) : ℝ) *
          (y (A + k) - trueNormalizedState (A + k)) := by
      rw [h1, hts (A + k + 1), h2, hts (A + k)]
      ring
    have hprod : actualWindowProduct A (k + 1) =
        actualWindowProduct A k * dyadicBlockBase235 (A + k) := by
      simp only [actualWindowProduct, Finset.prod_range_succ]
    rw [show A + (k + 1) = A + k + 1 by omega, hdiff, ih, hprod]
    push_cast
    ring

theorem surviving_eight_scale_window_orbit_eq_true_state
    (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ)
    (hrec : ∀ n, A ≤ n → y (n + 1) =
      (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ))
    (hwin : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
      y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n)
    (hwidth : ∀ n, A ≤ n →
      (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧
      trueNormalizedState n ≤
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n)
    (hvanish : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 8 ^ k < ε) :
    y A = trueNormalizedState A := by
  by_contra hne
  have hepos : 0 < |y A - trueNormalizedState A| :=
    abs_pos.mpr (sub_ne_zero_of_ne hne)
  obtain ⟨k₀, hk₀⟩ := hvanish (|y A - trueNormalizedState A| / 30) (by positivity)
  have hprodpos : (0 : ℝ) < (actualWindowProduct A k₀ : ℝ) := by
    exact_mod_cast actualWindowProduct_pos A k₀
  have hdev : |y (A + k₀) - trueNormalizedState (A + k₀)| =
      (actualWindowProduct A k₀ : ℝ) * |y A - trueNormalizedState A| := by
    rw [actual_orbit_difference A y hrec, abs_mul, abs_of_pos hprodpos]
  have hlarge : (8 : ℝ) ^ k₀ / 15 * |y A - trueNormalizedState A| <
      |y (A + k₀) - trueNormalizedState (A + k₀)| := by
    rw [hdev]
    exact mul_lt_mul_of_pos_right (actualWindowProduct_geometric_bounds A k₀).1 hepos
  have hbound : |y (A + k₀) - trueNormalizedState (A + k₀)| ≤ width (A + k₀) := by
    obtain ⟨hy, hy'⟩ := hwin (A + k₀) (by omega)
    obtain ⟨hx, hx'⟩ := hwidth (A + k₀) (by omega)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hpow : (0 : ℝ) < (8 : ℝ) ^ k₀ := by positivity
  have hsmall : width (A + k₀) < |y A - trueNormalizedState A| / 30 * 8 ^ k₀ :=
    (div_lt_iff₀ hpow).mp (hk₀ k₀ le_rfl)
  nlinarith [mul_pos hpow hepos]

/-- The complete long-paper pinning proposition with the printed growth base. -/
theorem paper_pinning_and_eight_scale_rigidity :
    (∀ a : ℕ, trueNormalizedState a =
      ((dyadicOrderedBlockDigit235 a : ℝ) + trueNormalizedState (a + 1)) /
        (dyadicBlockBase235 a : ℝ) ∧ 0 < trueNormalizedState a) ∧
    (∀ a : ℕ, ∀ z : ℤ, trueNormalizedState a = (z : ℝ) →
      ∀ n, a ≤ n → ∃ w : ℤ, trueNormalizedState n = (w : ℝ)) ∧
    (∀ (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ),
      (∀ n, 0 < width n) →
      (∀ n, A ≤ n → y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ)) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 8 ^ k < ε) →
      y A = trueNormalizedState A) := by
  refine ⟨paper_pinning_and_rigidity.1, paper_pinning_and_rigidity.2.1, ?_⟩
  intro width A y _ hrec hwin hwidth hvanish
  exact surviving_eight_scale_window_orbit_eq_true_state width A y hrec hwin hwidth hvanish

#print axioms paper_pinning_and_eight_scale_rigidity

end ErdosProblems.Erdos269.PaperCompleteR20
