import ErdosProblems.Erdos257.PaperCompleteR8.AnalyticSeparationReturn
import ErdosProblems.Erdos257.PaperCompleteR8.FixedExponentCover

/-! # Paper-facing strict inclusion, incomparability and mixed host

The strengthened-but-not-old witness `reverseHost` is the squarefree divisor-cube host of
`ReverseStrengthenedHost`, not the paper's printed bounded-mass fresh-prime construction.
The unused `FinitePrefixGluing` import was removed; no declaration here used it. -/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open ErdosProblems.Erdos257.PaperCompleteR7
open Erdos249257

/-- The older cost actually dominates the strengthened cost term by term. -/
theorem strengthened_term_le_oldCostTerm (C : PositiveCoverData) (j : ℕ) :
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) /
        ((2 : ℝ) ^ C.exponent j - 1) ≤ C.oldCostTerm j := by
  let B : ℝ := (2 : ℝ) ^ C.exponent j
  let a : ℝ := C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j)
  have hB : 1 < B := Real.one_lt_rpow (by norm_num) (C.exponent_bounds j).1
  have ha : 0 ≤ a := mul_nonneg (positiveCover_cost_nonneg C j)
    (Real.rpow_nonneg (by norm_num) _)
  change a / (B - 1) ≤ a * B / ((B - 1) ^ 2)
  apply (div_le_div_iff₀ (by linarith : 0 < B - 1) (sq_pos_of_pos (by linarith))).mpr
  nlinarith

theorem oldCostSummable_strengthened (C : PositiveCoverData) (hC : C.OldCostSummable) :
    C.StrengthenedCostSummable := by
  apply Summable.of_nonneg_of_le _ (strengthened_term_le_oldCostTerm C) hC
  intro j
  exact div_nonneg (mul_nonneg (positiveCover_cost_nonneg C j)
    (Real.rpow_nonneg (by norm_num) _))
    (sub_pos.mpr (Real.one_lt_rpow (by norm_num) (C.exponent_bounds j).1)).le

theorem hasStrengthenedPositiveCover_of_old {A : Set ℕ} (hA : HasOldPositiveCover A) :
    HasStrengthenedPositiveCover A := by
  obtain ⟨C, hAC, hC⟩ := hA
  exact ⟨C, hAC, oldCostSummable_strengthened C hC⟩

/-- The class inclusion is strict with a constructed, squarefree witness. -/
theorem old_cover_class_strictly_smaller :
    (∀ A : Set ℕ, HasOldPositiveCover A → HasStrengthenedPositiveCover A) ∧
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ (∀ a ∈ A, Squarefree a) ∧
      HasStrengthenedPositiveCover A ∧ ¬ HasOldPositiveCover A :=
  ⟨fun _ => hasStrengthenedPositiveCover_of_old,
    reverseHost, reverseHost_infinite, reverseHost_positive, reverseHost_squarefree,
    reverseHost_has_strengthened_cover, reverseHost_no_old_cover⟩

/-- Both directions of incomparability and the mixed all-base hereditary
consumer use actual witnesses. The weighted-only witness is imported from
`AnalyticSeparationReturn`; this assembly is elaborated and axiom-audited as stated
in the file header. -/
theorem exists_incomparable_hosts_with_mixed_heredity :
    ∃ W V : Set ℕ,
      W.Infinite ∧ V.Infinite ∧ 0 ∉ W ∧ 0 ∉ V ∧
      FinitePrimeWeighted 2 W ∧ ¬ HasStrengthenedPositiveCover W ∧
      HasStrengthenedPositiveCover V ∧ ¬ HasOldPositiveCover V ∧
      (∀ α : ℝ, 0 < α → α ≤ 1 → ¬ HasFixedExponentPositiveCover V α) ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b V) ∧
      (∀ A : Set ℕ, A ⊆ W ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b A)) := by
  obtain ⟨W, hWi, hW0, hW, hWr, hWc, hWe, hWh⟩ :=
    exists_weighted_not_strengthened_host
  refine ⟨W, reverseHost, hWi, reverseHost_infinite, hW0, reverseHost_positive,
    hW, hWc, reverseHost_has_strengthened_cover, reverseHost_no_old_cover,
    (fun α hα hα1 => reverseHost_no_fixed_exponent_cover hα hα1),
    reverseHost_not_finitePrimeWeighted, ?_⟩
  exact mixedSupportClaim W reverseHost hW0 hW reverseHost_has_strengthened_cover

end ErdosProblems.Erdos257.PaperCompleteR8
end
