import ErdosProblems.Erdos243.PaperCompleteR20.CutoffWeightReverse
import Mathlib.Algebra.Order.Floor.Ring

/-! The real-cutoff lower limit in the paper agrees with its integer-cutoff
version. Extended-real prefix masses are retained until finiteness is proved. -/
noncomputable section
namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter Set
open scoped BigOperators ENNReal NNReal Topology

def realCutoffPrefixMass (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (X : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, if (u j : ℝ) ≤ X then w j else 0

theorem realCutoffPrefixMass_eq_floor (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞)
    {X : ℝ} (hX : 0 ≤ X) :
    realCutoffPrefixMass u w X = cutoffPrefixMass u w ⌊X⌋₊ := by
  unfold realCutoffPrefixMass cutoffPrefixMass
  apply tsum_congr
  intro j
  simp only [Nat.le_floor_iff hX]

/-- Zero lower density is unchanged by extending a nonnegative sequence as a
step function and using the actual real cutoff in the denominator. -/
theorem real_floor_ratio_liminf_zero_iff (A : ℕ → ℝ≥0∞) :
    Filter.liminf (fun X : ℝ => A ⌊X⌋₊ / ENNReal.ofReal X) atTop = 0 ↔
      Filter.liminf (fun N : ℕ => A N / (N : ℝ≥0∞)) atTop = 0 := by
  constructor
  · intro hreal
    apply le_antisymm _ bot_le
    apply (Filter.liminf_le_iff' (by isBoundedDefault) (by isBoundedDefault)).mpr
    intro ε hε
    apply Filter.frequently_atTop.mpr
    intro N
    have hhalf : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
    have hfreq := (Filter.liminf_le_iff' (by isBoundedDefault)
      (by isBoundedDefault)).mp (le_of_eq hreal) (ε / 2) hhalf
    obtain ⟨X, hX, hsmall⟩ := Filter.frequently_atTop.mp hfreq (max (N : ℝ) 2)
    have hX2 : (2 : ℝ) ≤ X := (le_max_right _ _).trans hX
    have hX0 : 0 ≤ X := by linarith
    have hfloor : N ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX0).mpr ((le_max_left _ _).trans hX)
    have hfloor1 : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).mpr (by linarith)
    have hXbound : X ≤ 2 * (⌊X⌋₊ : ℝ) := by
      have hlt := Nat.lt_floor_add_one X
      have hcast : (1 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hfloor1
      linarith
    have hENN : ENNReal.ofReal X ≤ 2 * (⌊X⌋₊ : ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hXbound
    have hmass : A ⌊X⌋₊ ≤ (ε / 2) * ENNReal.ofReal X :=
      (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr (by linarith))
        ENNReal.ofReal_ne_top).mp hsmall
    refine ⟨⌊X⌋₊, hfloor, ?_⟩
    apply (ENNReal.div_le_iff (by exact_mod_cast (show ⌊X⌋₊ ≠ 0 by omega))
      (by simp)).mpr
    calc
      A ⌊X⌋₊ ≤ (ε / 2) * ENNReal.ofReal X := hmass
      _ ≤ (ε / 2) * (2 * (⌊X⌋₊ : ℝ≥0∞)) := mul_le_mul_left' hENN _
      _ = ε * (⌊X⌋₊ : ℝ≥0∞) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
  · intro hnat
    apply le_antisymm _ bot_le
    apply (Filter.liminf_le_iff' (by isBoundedDefault) (by isBoundedDefault)).mpr
    intro ε hε
    apply Filter.frequently_atTop.mpr
    intro X
    have hfreq := (Filter.liminf_le_iff' (by isBoundedDefault)
      (by isBoundedDefault)).mp (le_of_eq hnat) ε hε
    obtain ⟨N, hN, hsmall⟩ := Filter.frequently_atTop.mp hfreq ⌈X⌉₊
    refine ⟨(N : ℝ), (Nat.le_ceil X).trans (by exact_mod_cast hN), ?_⟩
    simpa only [Nat.floor_natCast, ENNReal.ofReal_natCast] using hsmall

def RealPrefixLowerDensityZero (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) : Prop :=
  Filter.liminf (fun X : ℝ => realCutoffPrefixMass u w X / ENNReal.ofReal X) atTop = 0

theorem realPrefixLowerDensityZero_iff (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) :
    RealPrefixLowerDensityZero u w ↔ PrefixLowerDensityZero u w := by
  have heq : (fun X : ℝ => realCutoffPrefixMass u w X / ENNReal.ofReal X) =ᶠ[atTop]
      (fun X : ℝ => cutoffPrefixMass u w ⌊X⌋₊ / ENNReal.ofReal X) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    rw [realCutoffPrefixMass_eq_floor u w hX]
  unfold RealPrefixLowerDensityZero PrefixLowerDensityZero
  rw [Filter.liminf_congr heq]
  exact real_floor_ratio_liminf_zero_iff _

/-- The paper's criterion, with its real cutoff, arbitrary repeated positive
integer locations, finite real weights, and divergent improper integral. -/
theorem real_lowerDensityZero_iff_exists_admissible_real_weight
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j) :
    RealPrefixLowerDensityZero u (fun j => (w j : ℝ≥0∞)) ↔
      ∃ f : ℝ → ℝ,
        AntitoneOn f (Ici 1) ∧
        (∀ t : ℝ, 1 ≤ t → 0 ≤ f t) ∧
        PaperCompleteR11.IntegralUnbounded f ∧
        Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ)) := by
  rw [realPrefixLowerDensityZero_iff]
  exact lowerDensityZero_iff_exists_admissible_real_weight u w hu

#print axioms real_floor_ratio_liminf_zero_iff
#print axioms real_lowerDensityZero_iff_exists_admissible_real_weight
end ErdosProblems.Erdos243.PaperCompleteR20
