import ErdosProblems.Erdos257.PaperCompleteR8.DivisorCubeIncidence
import ErdosProblems.Erdos257.PaperCompleteR8.DyadicLogarithmicEvents
import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget
import ErdosProblems.Erdos257.PaperCompleteR8.DivisorFrameHostTransport
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn

/-!
# The actual weighted host lies outside every strengthened positive cover

The logarithmic growth supplier is proved from finite prime blocks and
exact integer periods. Neither unbounded moments, reciprocal divergence,
no-cover status, nor irrationality is assumed by the final existence theorem.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- A finite positive common period for all relevant exact-valuation events. -/
theorem exists_dyadic_event_period (P : ℕ → Finset ℕ) (J : Finset ℕ)
    (hP : ∀ k p, p ∈ P k → 0 < p) :
    ∃ X : ℕ, 0 < X ∧ ∀ k ∈ J, ∀ p ∈ P k, 2 * (2 ^ (k + 2) * p) ∣ X := by
  classical
  let D := J.biUnion (fun k => (P k).image (fun p => 2 * (2 ^ (k + 2) * p)))
  refine ⟨D.prod id, ?_, ?_⟩
  · apply Finset.prod_pos
    intro d hd
    obtain ⟨k, hk, hdk⟩ := Finset.mem_biUnion.mp hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hdk
    exact Nat.mul_pos (by decide) (Nat.mul_pos (Nat.pow_pos (by decide)) (hP k p hp))
  · intro k hk p hp
    exact Finset.dvd_prod_of_mem id
      (Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩)

/-- Exact mean of all block counts, before imposing the harmonic scale. -/
theorem mean_dyadicBlockCounts (P : ℕ → Finset ℕ) (J : Finset ℕ) (X : ℕ)
    (hP : ∀ k p, p ∈ P k → 0 < p) (hX : 0 < X)
    (hperiod : ∀ k ∈ J, ∀ p ∈ P k, 2 * (2 ^ (k + 2) * p) ∣ X) :
    (∑ n ∈ Icc 1 X, ∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) / X =
      ∑ k ∈ J, (∑ p ∈ P k, (1 : ℝ) / p) / (2 * (2 : ℝ) ^ (k + 2)) := by
  classical
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [dyadicBlockCount_cast]
  exact mean_prime_block_dyadic_events (P k) (k + 2) X (hP k) hX (hperiod k hk)

/-- Each prescribed row contributes at least one eighth to the event mean. -/
theorem harmonic_row_event_lower (P : Finset ℕ) (k : ℕ)
    (hS : (2 : ℝ) ^ k ≤ ∑ p ∈ P, (1 : ℝ) / p) :
    (1 / 8 : ℝ) ≤ (∑ p ∈ P, (1 : ℝ) / p) / (2 * (2 : ℝ) ^ (k + 2)) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * 2 ^ (k + 2))).2
  rw [pow_add]
  convert hS using 1 <;> ring

/-- Linear logarithmic growth at a genuine common finite period. -/
theorem dyadic_finite_logarithmic_growth (P : ℕ → Finset ℕ) (m : ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p)
    (hS : ∀ k, (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p) :
    ∃ X : ℕ, 0 < X ∧
      Real.exp 1 * Real.log 2 * (m : ℝ) / 8 ≤
        finiteLogarithmicMean
          ((Finset.range m).biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)) X := by
  classical
  let J := Finset.range m
  let F := J.biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)
  obtain ⟨X, hX, hperiod⟩ := exists_dyadic_event_period P J
    (fun k p hp => (hP k p hp).1.pos)
  refine ⟨X, hX, ?_⟩
  have havg := mean_dyadicBlockCounts P J X
    (fun k p hp => (hP k p hp).1.pos) hX hperiod
  have hrows : (m : ℝ) / 8 ≤
      ∑ k ∈ J, (∑ p ∈ P k, (1 : ℝ) / p) / (2 * (2 : ℝ) ^ (k + 2)) := by
    have h := Finset.sum_le_sum (s := J) (fun k _ => harmonic_row_event_lower (P k) k (hS k))
    simpa only [Finset.sum_const, nsmul_eq_mul, J, Finset.card_range, div_eq_mul_inv, one_mul] using h
  have hc : 0 ≤ Real.exp 1 * Real.log 2 := mul_nonneg (Real.exp_pos 1).le
    (Real.log_nonneg (by norm_num))
  have hpoint : ∀ n ∈ Icc 1 X,
      Real.exp 1 * Real.log 2 * (∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) ≤
        Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ) := by
    intro n hn
    have hp := dyadic_union_log_pointwise P J n (by
      have := (Finset.mem_Icc.mp hn).1
      omega) hP
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (Real.exp_pos 1).le
  have hmean : Real.exp 1 * Real.log 2 *
      ((∑ n ∈ Icc 1 X, ∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) / X) ≤
        finiteLogarithmicMean F X := by
    rw [← mul_div_assoc, Finset.mul_sum]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) (Nat.cast_nonneg X)
  rw [havg] at hmean
  have hscaled := mul_le_mul_of_nonneg_left hrows hc
  have htotal := hscaled.trans hmean
  simpa only [mul_div_assoc] using htotal

/-- The actual infinite host supplies arbitrarily large finite logarithmic means. -/
theorem dyadic_host_unbounded_finite_logarithmic_means (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p)
    (hS : ∀ k, (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p) :
    ∀ R : ℝ, ∃ F : Finset ℕ,
      (F : Set ℕ) ⊆ dyadicDivisorHost (fun k => (P k).prod id) ∧
      ∃ X : ℕ, 0 < X ∧ R < finiteLogarithmicMean F X := by
  intro R
  let c : ℝ := Real.exp 1 * Real.log 2 / 8
  have hc : 0 < c := div_pos (mul_pos (Real.exp_pos 1) (Real.log_pos (by norm_num)))
    (by norm_num)
  obtain ⟨m, hm⟩ := exists_nat_gt (R / c)
  have hRm : R < c * (m : ℝ) := by
    have h := (div_lt_iff₀ hc).mp hm
    simpa only [mul_comm] using h
  obtain ⟨X, hX, hbound⟩ := dyadic_finite_logarithmic_growth P m hP hS
  let F := (Finset.range m).biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)
  refine ⟨F, ?_, X, hX, ?_⟩
  · intro a ha
    obtain ⟨k, hk, hak⟩ := Finset.mem_biUnion.mp ha
    exact ⟨k, hak⟩
  · have heq : c * (m : ℝ) = Real.exp 1 * Real.log 2 * (m : ℝ) / 8 := by
      dsimp [c]
      ring
    rw [heq] at hRm
    exact hRm.trans_le hbound

/-- An elementary universal upper bound: logarithmic incidence costs at most
ordinary reciprocal mass. This includes cardinality zero without log-positive notation. -/
theorem finiteLogarithmicMean_le_reciprocal (F : Finset ℕ) (hF : 0 ∉ F)
    (X : ℕ) (hX : 0 < X) :
    finiteLogarithmicMean F X ≤ Real.exp 1 * (∑ a ∈ F, (1 : ℝ) / a) := by
  classical
  have hlogle : ∀ n : ℕ, Real.log (n : ℝ) ≤ (n : ℝ) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hh := Real.log_le_sub_one_of_pos hnpos
      linarith
  have hmean := cesaro_le_divisorMajorantCost
    (fun n => Real.log ((F.filter (fun a => a ∣ n)).card : ℝ)) F (fun _ => (1 : ℝ))
    X hX (fun a ha => Nat.pos_of_ne_zero (fun hz => hF (hz ▸ ha)))
    (fun _ _ => by norm_num) (fun _ => log_nat_nonneg _) (fun n _ => by
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using hlogle ((F.filter (fun a => a ∣ n)).card))
  rw [divisorMajorantCost_one] at hmean
  have h := mul_le_mul_of_nonneg_left hmean (Real.exp_pos 1).le
  simpa only [finiteLogarithmicMean, ← Finset.mul_sum, mul_div_assoc] using h

/-- Unbounded first logarithmic moments force reciprocal divergence. -/
theorem not_summable_reciprocal_of_unbounded_finite_means (A : Set ℕ) (hA0 : 0 ∉ A)
    (hlarge : ∀ R : ℝ, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∃ X : ℕ, 0 < X ∧ R < finiteLogarithmicMean F X) :
    ¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a)) := by
  classical
  intro hs
  obtain ⟨F, hFA, X, hX, hbig⟩ := hlarge
    (Real.exp 1 * ∑' a, Set.indicator A (fun a : ℕ => (1 : ℝ) / a) a)
  have hF0 : 0 ∉ F := fun h => hA0 (hFA h)
  have hsum : (∑ a ∈ F, (1 : ℝ) / a) ≤
      ∑' a, Set.indicator A (fun a : ℕ => (1 : ℝ) / a) a := by
    have heq : (∑ a ∈ F, (1 : ℝ) / a) =
        ∑ a ∈ F, Set.indicator A (fun a : ℕ => (1 : ℝ) / a) a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Set.indicator_of_mem (hFA ha) (fun a : ℕ => (1 : ℝ) / a)).symm
    rw [heq]
    exact hs.sum_le_tsum F (fun a _ => by
      by_cases ha : a ∈ A
      · rw [Set.indicator_of_mem ha]
        positivity
      · rw [Set.indicator_of_notMem ha])
  have hbound := (finiteLogarithmicMean_le_reciprocal F hF0 X hX).trans
    (mul_le_mul_of_nonneg_left hsum (Real.exp_pos 1).le)
  exact (not_lt_of_ge hbound) hbig

/-- No strengthened positive cover, with arbitrary positive weights, covers this host. -/
theorem no_logBudgetCover_dyadic_host (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p)
    (hS : ∀ k, (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p) :
    IsEmpty (LogBudgetCover (dyadicDivisorHost (fun k => (P k).prod id))) :=
  no_logBudgetCover_of_unbounded_finite_means _
    (dyadic_host_unbounded_finite_logarithmic_means P hP hS)

/-- The complete A_W endpoint, including its actual construction and all-base
heredity. There is no moment-growth or no-cover hypothesis in this theorem. -/
theorem exists_weighted_host_outside_every_logBudgetCover :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      ¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a)) ∧
      IsEmpty (LogBudgetCover A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B)) := by
  obtain ⟨P, hdis, hP, hinf, hzero, hweighted⟩ := exists_infinite_dyadic_weighted_host
  let A := dyadicDivisorHost (fun k => (P k).prod id)
  have hpr : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p := fun k p hp => (hP k).1 p hp
  have hscale : ∀ k, (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p := fun k => (hP k).2.1
  have hlarge := dyadic_host_unbounded_finite_logarithmic_means P hpr hscale
  refine ⟨A, hinf, hzero, hweighted,
    not_summable_reciprocal_of_unbounded_finite_means A hzero hlarge,
    no_logBudgetCover_dyadic_host P hpr hscale, ?_⟩
  exact divisibilityWeightedClaim.2 A hzero hweighted

end ErdosProblems.Erdos257.PaperCompleteR8
end
