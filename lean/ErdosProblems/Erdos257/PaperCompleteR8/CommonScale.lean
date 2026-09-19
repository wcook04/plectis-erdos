import ErdosProblems.Erdos257.PaperCompleteR8.DyadicKernel
import ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets

/-!
# Common-scale consumers for the actual two supports

This records an OPTIONAL STRONGER sufficient interface. It is not the exact
residual of mandate 1b: the cover proof controls a nonlinear test, not its raw
first moment. MixedGaugeConsumer supplies the corrected interface. Separate
irrationality conclusions or separate existential return times are never used.
NOT COMPILED in this return.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- A genuinely joint finite-mean supply. This is not asserted for weighted
or covered supports here. The scale inequality belongs to the hypothesis. -/
def JointDyadicMeanSupply (E V : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L R M : ℕ,
    0 < L ∧ 4 * L ≤ M ∧
    dyadicMean L R M (displacement 2 E) +
      dyadicMean L R M (displacement 2 V) < ε

/-- One progression point simultaneously controls both *actual* displacements. -/
theorem common_displacement_return (E V : Set ℕ)
    (L R M : ℕ) (hL : 0 < L) (hM : 0 < M) (ε : ℝ)
    (hbudget : dyadicMean L R M (displacement 2 E) +
      dyadicMean L R M (displacement 2 V) < ε) :
    ∃ N : ℕ, 0 < N ∧ L ∣ N ∧ L ≤ N ∧
      displacement 2 E N < ε ∧ displacement 2 V N < ε := by
  exact exists_common_progression_sample L R M hL hM
    (displacement 2 E) (displacement 2 V)
    (fun N => displacement_nonneg 2 E N (by norm_num))
    (fun N => displacement_nonneg 2 V N (by norm_num)) ε hbudget

/-- Stronger than extracting the two coordinates separately: the union's
whole displacement is below the SAME ε. -/
theorem union_return_of_common_mean_budget (E V : Set ℕ)
    (L R M : ℕ) (hL : 0 < L) (hM : 0 < M) (ε : ℝ)
    (hbudget : dyadicMean L R M (displacement 2 E) +
      dyadicMean L R M (displacement 2 V) < ε) :
    ∃ N : ℕ, 0 < N ∧ L ∣ N ∧ displacement 2 (E ∪ V) N < ε := by
  have hsum : dyadicMean L R M
      (fun N => displacement 2 E N + displacement 2 V N) < ε := by
    rw [dyadicMean_add]
    exact hbudget
  obtain ⟨j, m, _hjlo, _hjhi, _hm, hpoint⟩ :=
    exists_sample_lt_of_dyadicMean_lt L R M hM
      (fun N => displacement 2 E N + displacement 2 V N) ε hsum
  let N := (m + 1) * L
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos m) hL
  have hdiv : L ∣ N := ⟨m + 1, by dsimp [N]; ring⟩
  have hsmall : displacement 2 (E ∪ V) N < ε :=
    lt_of_le_of_lt (displacement_union_le 2 E V N (by norm_num)) hpoint
  exact ⟨N, hN, hdiv, hsmall⟩

/-- Full arithmetic consumer: all bases and every infinite thinning.
The remaining assumption is the stated joint analytic supply, not either
component's irrationality. -/
theorem hereditary_irrational_of_jointDyadicMeanSupply (E V : Set ℕ)
    (hsupply : JointDyadicMeanSupply E V) :
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A) := by
  apply all_base_hereditary_of_binary_returns (E ∪ V)
  intro ε hε
  obtain ⟨L, R, M, hL, hscale, hmean⟩ := hsupply ε hε
  obtain ⟨N, hN, _hdiv, hsmall⟩ :=
    union_return_of_common_mean_budget E V L R M hL (by omega) ε hmean
  exact ⟨N, hN, hsmall⟩

/-- An optional stronger weighted-plus-cover schedule obligation. Not the
exact remaining obligation: see MixedGaugeConsumer.WeightedDyadicMeanTarget. -/
def MixedDyadicSchedule_target : Prop :=
  ∀ E V : Set ℕ, 0 ∉ E → FinitePrimeWeighted 2 E →
    HasStrengthenedPositiveCover V → JointDyadicMeanSupply E V

/-- Conditional closure with the analytic premise visibly retained.
This does NOT assert MixedDyadicSchedule_target or MixedSupportClaim. -/
theorem mixedSupportClaim_of_schedule
    (hschedule : MixedDyadicSchedule_target) : MixedSupportClaim := by
  intro E V hE0 hE hV
  exact hereditary_irrational_of_jointDyadicMeanSupply E V (hschedule E V hE0 hE hV)

/-- Numerical scale consequence used to budget each common test. -/
theorem one_add_four_ratio_le_two (L M : ℕ) (hM : 0 < M) (hscale : 4 * L ≤ M) :
    1 + 4 * (L : ℝ) / M ≤ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hLR : 4 * (L : ℝ) ≤ M := by exact_mod_cast hscale
  have hratio : 4 * (L : ℝ) / M ≤ 1 := by
    apply (div_le_iff₀ hMR).2
    simpa only [one_mul] using hLR
  linarith only [hratio]

end ErdosProblems.Erdos257.PaperCompleteR8
end
