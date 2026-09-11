import ErdosProblems.Erdos251.SparsePaperR11

/-! # The cumulative growth assertions for bounded and sublogarithmic corrections
Candidate source, UNRUN. The stability lemmas expose a PNT input only for the
original position sequence, never for the perturbed sequence being proved.
-/
noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR11.PerturbationGrowth
open SparsePolylog

def cumulativeCorrection (e : ℕ → ℕ) (n : ℕ) : ℝ := ∑ i ∈ range n, (e i : ℝ)
def scale (n : ℕ) : ℝ := (n : ℝ) * Real.log (n : ℝ)

theorem log_nat_tendsto : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem scale_pos {n : ℕ} (hn : 2 ≤ n) : 0 < scale n :=
  mul_pos (by exact_mod_cast (show 0 < n by omega))
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))

theorem constant_div_scale (C : ℝ) :
    Tendsto (fun n => C / scale n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_nat_tendsto
  simpa only [scale, zero_mul, mul_one_div, div_div] using h1.mul h2

theorem polylog_div_log_tendsto {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n => polylog ε n / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ (ε - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub] using
      (tendsto_rpow_neg_atTop (show 0 < 1 - ε by linarith)).comp log_nat_tendsto
  have hu : Tendsto (fun n : ℕ => (2 : ℝ) ^ ε * Real.log (n : ℝ) ^ (ε - 1)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul ((2 : ℝ) ^ ε)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    exact div_nonneg (Real.rpow_nonneg (log_argument_positive n).le _)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hnp : (0 : ℝ) < n := by linarith
    have hLP : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have harg : (n : ℝ) + 3 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hl := Real.log_le_log (by positivity : 0 < (n : ℝ) + 3) harg
    rw [Real.log_pow] at hl
    norm_num at hl
    have hb := Real.rpow_le_rpow (log_argument_positive n).le hl hε.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hLP.le] at hb
    calc
      polylog ε n / Real.log (n : ℝ) ≤ ((2 : ℝ) ^ ε * Real.log (n : ℝ) ^ ε) / Real.log (n : ℝ) :=
        div_le_div_of_nonneg_right hb hLP.le
      _ = (2 : ℝ) ^ ε * Real.log (n : ℝ) ^ (ε - 1) := by
        rw [Real.rpow_sub_one hLP.ne' ε]
        ring

theorem correction_is_sublogarithmic (e : ℕ → ℕ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    (he : ∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) :
    Tendsto (fun n => (e n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (polylog_div_log_tendsto hε hε1)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  · filter_upwards [he, eventually_ge_atTop (2 : ℕ)] with n hen hn
    exact div_le_div_of_nonneg_right hen
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))

/-- The finite exceptional prefix is retained explicitly in the upper bound. -/
theorem cumulative_polylog_bound (e : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε)
    (he : ∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      0 ≤ cumulativeCorrection e n ∧ cumulativeCorrection e n ≤ C + n * polylog ε n := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  let C : ℝ := ∑ i ∈ range N₀, (e i : ℝ)
  refine ⟨C, sum_nonneg (fun i _ => Nat.cast_nonneg _), ?_⟩
  intro n
  refine ⟨sum_nonneg (fun i _ => Nat.cast_nonneg _), ?_⟩
  have hpoint : ∀ i ∈ range n,
      (e i : ℝ) ≤ (if i < N₀ then (e i : ℝ) else 0) + polylog ε n := by
    intro i hi
    by_cases hlow : i < N₀
    · rw [if_pos hlow]
      have hnonneg : 0 ≤ polylog ε n := Real.rpow_nonneg (log_argument_positive n).le _
      linarith
    · rw [if_neg hlow, zero_add]
      exact (hN₀ i (by omega)).trans (polylog_mono hε.le (Nat.le_of_lt (mem_range.mp hi)))
  have hprefix : (∑ i ∈ range n, if i < N₀ then (e i : ℝ) else 0) ≤ C := by
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact mem_range.mpr (mem_filter.mp hi).2
    · intro i hi hnot
      exact Nat.cast_nonneg _
  have hsum := sum_le_sum hpoint
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  exact hsum.trans (add_le_add hprefix (le_refl _))

theorem cumulative_correction_negligible (e : ℕ → ℕ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1)
    (he : ∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) :
    Tendsto (fun n => cumulativeCorrection e n / scale n) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := cumulative_polylog_bound e hε he
  have hu : Tendsto (fun n => C / scale n + polylog ε n / Real.log (n : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_add] using (constant_div_scale C).add (polylog_div_log_tendsto hε hε1)
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact div_nonneg (hbound n).1 (scale_pos hn).le
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      cumulativeCorrection e n / scale n ≤ (C + n * polylog ε n) / scale n :=
        div_le_div_of_nonneg_right (hbound n).2 (scale_pos hn).le
      _ = C / scale n + polylog ε n / Real.log (n : ℝ) := by
        unfold scale
        field_simp [hnp.ne']

/-- The PNT premise concerns only the unmodified positions. -/
theorem polylog_positions_preserve_growth (p e : ℕ → ℕ) {ε : ℝ}
    (hp : Tendsto (fun n => (p n : ℝ) / scale n) atTop (𝓝 1))
    (hε : 0 < ε) (hε1 : ε < 1)
    (he : ∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) :
    Tendsto (fun n => ((p n + ∑ i ∈ range n, e i : ℕ) : ℝ) / scale n) atTop (𝓝 1) := by
  have h := hp.add (cumulative_correction_negligible e hε hε1 he)
  simpa only [Nat.cast_add, Nat.cast_sum, add_div, cumulativeCorrection, add_zero] using h

/-- Uniformly bounded perturbations need no sparse-support hypothesis. -/
theorem sandwich_preserves_growth (p P : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hp : Tendsto (fun n => p n / scale n) atTop (𝓝 1))
    (hlo : ∀ n, p n ≤ P n) (hhi : ∀ n, P n ≤ p n + M * n) :
    Tendsto (fun n => P n / scale n) atTop (𝓝 1) := by
  have hMlim : Tendsto (fun n : ℕ => M / Real.log (n : ℝ)) atTop (𝓝 0) :=
    (show Tendsto (fun _ : ℕ => M) atTop (𝓝 M) from tendsto_const_nhds).div_atTop
      log_nat_tendsto
  have hu : Tendsto (fun n => p n / scale n + M / Real.log (n : ℝ)) atTop (𝓝 1) := by
    simpa only [add_zero] using Tendsto.add hp hMlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hp hu
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right (hlo n) (scale_pos hn).le
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    calc
      P n / scale n ≤ (p n + M * n) / scale n :=
        div_le_div_of_nonneg_right (hhi n) (scale_pos hn).le
      _ = p n / scale n + M / Real.log (n : ℝ) := by
        unfold scale
        field_simp [hnp.ne']

#print axioms cumulative_correction_negligible
#print axioms sandwich_preserves_growth
end ErdosProblems.Erdos251.PaperR11.PerturbationGrowth
