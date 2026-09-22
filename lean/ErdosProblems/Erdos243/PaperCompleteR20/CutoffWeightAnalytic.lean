import ErdosProblems.Erdos243.PaperCompleteR20.CutoffWeightForward
import ErdosProblems.Erdos243.PaperCompleteR11.IntegralWeights
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Erdős 243: the real cutoff staircase

This file converts the selected `ENNReal` cutoff weights to the finite real
nonincreasing staircase used in short-paper `res:weights`.  It isolates the
finite-sum lower bound which makes the improper integral divergent.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

/-- Geometric growth makes every cutoff weight finite, uniformly by one. -/
theorem cutoffWeight_le_one_of_two_pow
    (X : ℕ → ℕ) (hX : ∀ k, 2 ^ (k + 1) ≤ X k) (x : ℕ) :
    cutoffWeight X x ≤ 1 := by
  calc
    cutoffWeight X x ≤ ∑' k : ℕ, ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := by
      apply ENNReal.tsum_le_tsum
      intro k
      unfold cutoffAtom
      by_cases hx : x ≤ X k
      · rw [if_pos hx]
        apply ENNReal.inv_le_inv'
        exact_mod_cast hX k
      · simp [hx]
    _ = 1 := by
      simp_rw [ENNReal.inv_pow]
      rw [ENNReal.tsum_geometric_add_one]
      norm_num [ENNReal.one_sub_inv_two]
      exact ENNReal.inv_mul_cancel (by norm_num) (by simp)

theorem cutoffWeight_ne_top_of_two_pow
    (X : ℕ → ℕ) (hX : ∀ k, 2 ^ (k + 1) ≤ X k) (x : ℕ) :
    cutoffWeight X x ≠ ∞ :=
  ne_top_of_le_ne_top (by simp) (cutoffWeight_le_one_of_two_pow X hX x)

/-- The finite real staircase associated to integer cutoffs.  The `max` gives
a harmless total extension below the paper's domain `[1,∞)`. -/
def realCutoffWeight (X : ℕ → ℕ) (t : ℝ) : ℝ :=
  (cutoffWeight X ⌈max 1 t⌉₊).toReal

theorem realCutoffWeight_nonneg (X : ℕ → ℕ) (t : ℝ) :
    0 ≤ realCutoffWeight X t := ENNReal.toReal_nonneg

/-- The real staircase is nonincreasing on `[1,∞)`. -/
theorem realCutoffWeight_antitoneOn
    (X : ℕ → ℕ) (hX : ∀ k, 2 ^ (k + 1) ≤ X k) :
    AntitoneOn (realCutoffWeight X) (Ici 1) := by
  intro a ha b hb hab
  unfold realCutoffWeight
  apply ENNReal.toReal_mono (cutoffWeight_ne_top_of_two_pow X hX _)
  apply cutoffWeight_antitone
  apply Nat.ceil_mono
  exact max_le_max_left 1 hab

@[simp] theorem realCutoffWeight_nat
    (X : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    realCutoffWeight X n = (cutoffWeight X n).toReal := by
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [realCutoffWeight, max_eq_right hnreal, Nat.ceil_natCast]

private def realCutoffAtom (X : ℕ → ℕ) (k x : ℕ) : ℝ :=
  (cutoffAtom X k x).toReal

private theorem finiteAtoms_le_realCutoffWeight
    (X : ℕ → ℕ) (hX : ∀ k, 2 ^ (k + 1) ≤ X k)
    (s : Finset ℕ) (x : ℕ) :
    (∑ k ∈ s, realCutoffAtom X k x) ≤ (cutoffWeight X x).toReal := by
  change (∑ k ∈ s, (cutoffAtom X k x).toReal) ≤ _
  rw [← ENNReal.toReal_sum]
  · apply ENNReal.toReal_mono (cutoffWeight_ne_top_of_two_pow X hX x)
    exact ENNReal.sum_le_tsum s
  · intro k hk
    have hkpos : 0 < X k := lt_of_lt_of_le (pow_pos (by omega) _) (hX k)
    unfold cutoffAtom
    split <;> simp [hkpos.ne']

/-- Up to the `m`-th selected cutoff, the integer samples of the staircase
have mass at least `(m+1)/2`.  This is the finite Tonelli calculation behind
its divergent integral. -/
theorem selectedCutoffWeight_sample_lower_bound
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (h : GeometricPrefixVanish u w) (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) / 2 ≤
      ∑ n ∈ Finset.range (selectedCutoffs u w h m - 1),
        realCutoffWeight (selectedCutoffs u w h) (n + 2 : ℕ) := by
  let X := selectedCutoffs u w h
  have hX : ∀ k, 2 ^ (k + 1) ≤ X k := two_pow_le_selectedCutoffs u w h
  have hmono : StrictMono X := selectedCutoffs_strictMono u w h
  have hpoint : ∀ n, (∑ k ∈ Finset.range (m + 1), realCutoffAtom X k (n + 2)) ≤
      realCutoffWeight X (n + 2 : ℕ) := by
    intro n
    rw [realCutoffWeight_nat X (n + 2) (by omega)]
    exact finiteAtoms_le_realCutoffWeight X hX _ _
  calc
    ((m + 1 : ℕ) : ℝ) / 2 ≤
        ∑ k ∈ Finset.range (m + 1),
          ∑ n ∈ Finset.range (X m - 1), realCutoffAtom X k (n + 2) := by
      rw [show ((m + 1 : ℕ) : ℝ) / 2 =
        ∑ k ∈ Finset.range (m + 1), (1 / 2 : ℝ) by simp [div_eq_mul_inv]]
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
      have hle : X k ≤ X m := hmono.monotone hkm
      have hXk : 2 ≤ X k := by
        have hp : 0 < (2 : ℕ) ^ k := pow_pos (by omega) _
        have hb := hX k
        rw [pow_succ] at hb
        omega
      have hfilter : (Finset.range (X m - 1)).filter (fun n => n + 2 ≤ X k) =
          Finset.range (X k - 1) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [show (∑ n ∈ Finset.range (X m - 1), realCutoffAtom X k (n + 2)) =
          (X k - 1 : ℕ) * ((X k : ℝ)⁻¹) by
        simp only [realCutoffAtom, cutoffAtom, apply_ite, ENNReal.toReal_zero]
        rw [← Finset.sum_filter, hfilter]
        simp [ENNReal.toReal_inv, ENNReal.toReal_natCast]]
      have hkreal : (2 : ℝ) ≤ X k := by exact_mod_cast hXk
      rw [Nat.cast_sub (show 1 ≤ X k by omega)]
      norm_num only [Nat.cast_one]
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ (by linarith : (0 : ℝ) < X k)).2 (by linarith)
    _ = ∑ n ∈ Finset.range (X m - 1),
          ∑ k ∈ Finset.range (m + 1), realCutoffAtom X k (n + 2) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ n ∈ Finset.range (X m - 1),
          realCutoffWeight X (n + 2 : ℕ) :=
      Finset.sum_le_sum (fun n _ => hpoint n)

/-- The real weighted sample series of the selected staircase is summable.
This is the finite-weight side of the paper's forward implication. -/
theorem summable_weighted_selected_realCutoffWeight
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0)
    (hu : ∀ j, 0 < u j)
    (h : GeometricPrefixVanish u (fun j => (w j : ℝ≥0∞))) :
    Summable (fun j : ℕ => (w j : ℝ) *
      realCutoffWeight (selectedCutoffs u (fun j => (w j : ℝ≥0∞)) h) (u j : ℕ)) := by
  let X := selectedCutoffs u (fun j => (w j : ℝ≥0∞)) h
  let g : ℕ → ℝ≥0 := fun j => w j * (cutoffWeight X (u j)).toNNReal
  have hfinite : ∀ j, cutoffWeight X (u j) ≠ ∞ := by
    intro j
    exact cutoffWeight_ne_top_of_two_pow X
      (two_pow_le_selectedCutoffs u (fun j => (w j : ℝ≥0∞)) h) _
  have hmass := weighted_selectedCutoffWeight_ne_top u
    (fun j => (w j : ℝ≥0∞)) h
  have hgcoe : (∑' j : ℕ, (g j : ℝ≥0∞)) ≠ ∞ := by
    simpa only [g, ENNReal.coe_mul, ENNReal.coe_toNNReal (hfinite _)] using hmass
  have hg : Summable g := ENNReal.tsum_coe_ne_top_iff_summable.mp hgcoe
  change Summable (fun j : ℕ => (w j : ℝ) * realCutoffWeight X (u j : ℕ))
  refine (NNReal.summable_coe.mpr hg).congr ?_
  intro j
  change (w j : ℝ) * ((cutoffWeight X (u j)).toNNReal : ℝ) = _
  rw [realCutoffWeight_nat X (u j) (hu j)]
  rfl

/-- The selected real cutoff staircase has unbounded improper integral. -/
theorem selected_realCutoffWeight_integralUnbounded
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0∞) (h : GeometricPrefixVanish u w) :
    PaperCompleteR11.IntegralUnbounded
      (realCutoffWeight (selectedCutoffs u w h)) := by
  intro M
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * M)
  let X := selectedCutoffs u w h
  have hX : ∀ k, 2 ^ (k + 1) ≤ X k := two_pow_le_selectedCutoffs u w h
  have hXm : 1 ≤ X m :=
    (Nat.one_le_pow _ _ (by omega)).trans (hX m)
  refine ⟨X m, by exact_mod_cast hXm, ?_⟩
  have hanti := realCutoffWeight_antitoneOn X hX
  have hsum := selectedCutoffWeight_sample_lower_bound u w h m
  have hint := (hanti.mono (fun x hx => hx.1)).sum_le_integral
    (x₀ := (1 : ℝ)) (a := X m - 1)
  simp only [Nat.cast_sub hXm, Nat.cast_one, add_sub_cancel] at hint
  have hrewrite : (∑ i ∈ Finset.range (X m - 1),
      realCutoffWeight X (1 + (i + 1 : ℕ))) =
      ∑ n ∈ Finset.range (X m - 1), realCutoffWeight X (n + 2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    push_cast
    ring
  rw [hrewrite] at hint
  have hmreal : 2 * M < ((m + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  linarith

/-- Exact forward half of the paper's admissible-weight conclusion, expressed
with nonnegative-real input weights and the cofinal geometric form of vanishing
prefix density. -/
theorem exists_admissible_real_weight_of_geometricPrefixVanish
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j)
    (h : GeometricPrefixVanish u (fun j => (w j : ℝ≥0∞))) :
    ∃ f : ℝ → ℝ,
      AntitoneOn f (Ici 1) ∧
      (∀ t : ℝ, 1 ≤ t → 0 ≤ f t) ∧
      PaperCompleteR11.IntegralUnbounded f ∧
      Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ)) := by
  let X := selectedCutoffs u (fun j => (w j : ℝ≥0∞)) h
  refine ⟨realCutoffWeight X,
    realCutoffWeight_antitoneOn X
      (two_pow_le_selectedCutoffs u (fun j => (w j : ℝ≥0∞)) h),
    ?_, selected_realCutoffWeight_integralUnbounded u
      (fun j => (w j : ℝ≥0∞)) h,
    summable_weighted_selected_realCutoffWeight u w hu h⟩
  intro t ht
  exact realCutoffWeight_nonneg X t

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.realCutoffWeight_antitoneOn
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.selectedCutoffWeight_sample_lower_bound
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.selected_realCutoffWeight_integralUnbounded

end ErdosProblems.Erdos243.PaperCompleteR20
