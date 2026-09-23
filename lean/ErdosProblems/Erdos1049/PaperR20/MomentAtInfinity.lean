import ErdosProblems.Erdos1049.ActualMomentGeneratingR12
import Mathlib

/-!
# The literal coefficient moment tends to one at infinity

For fixed `m`, the zeroth summand in `actualMoment q m` tends to one as
`q → 0`.  The remaining positive summands are bounded directly by a geometric
series.  This proof uses only the finite products in the literal summand; no
limit theorem for the infinite q-Pochhammer product is needed.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Filter Topology
open scoped BigOperators
open PaperR10 PaperR12

noncomputable section

/-- When `q ≤ 1/2`, every factor in a shifted finite q-Pochhammer product is
at least `1/2`. -/
lemma half_pow_le_qPochhammerFinite {q : ℝ} (hq0 : 0 ≤ q)
    (hqhalf : q ≤ 1 / 2) (s n : ℕ) (hs : 1 ≤ s) :
    (1 / 2 : ℝ) ^ n ≤ qPochhammerFinite (q ^ s) q n := by
  unfold qPochhammerFinite
  calc
    (1 / 2 : ℝ) ^ n = ∏ _k ∈ Finset.range n, (1 / 2 : ℝ) := by simp
    _ ≤ ∏ k ∈ Finset.range n, (1 - q ^ s * q ^ k) := by
      apply Finset.prod_le_prod
      · intro k hk
        norm_num
      · intro k hk
        have hq1 : q ≤ 1 := hqhalf.trans (by norm_num)
        have hpow : q ^ (s + k) ≤ q := by
          simpa only [pow_one] using
            qpow_antitone hq0 hq1 (show 1 ≤ s + k by omega)
        rw [← pow_add]
        linarith

/-- Elementary finite-product majorant for each literal moment summand. -/
lemma actualMomentTerm_le_geometric {q : ℝ} (hq0 : 0 < q)
    (hqhalf : q ≤ 1 / 2) (m t : ℕ) :
    actualMomentTerm q m t ≤
      (2 : ℝ) ^ (m + 1) * q ^ ((m + 1) * t) := by
  have hq1 : q < 1 := hqhalf.trans_lt (by norm_num)
  have ha := qPochhammerFinite_nonneg_le_one hq0.le hq1.le hq0.le hq1.le m
  have hb := qPochhammerFinite_nonneg_le_one (pow_nonneg hq0.le (t + 1))
    (positive_shift_power_lt_one hq0 hq1 (t + 1) (by omega)).le hq0.le hq1.le m
  have hab : (qPochhammerFinite q q m) ^ 3 *
      qPochhammerFinite (q ^ (t + 1)) q m ≤ 1 := by
    calc
      _ ≤ 1 * qPochhammerFinite (q ^ (t + 1)) q m :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ ha.1 ha.2) hb.1
      _ ≤ 1 := by simpa using hb.2
  have hden := half_pow_le_qPochhammerFinite hq0.le hqhalf
    (m + t + 1) (m + 1) (by omega)
  have hdenpos : 0 < qPochhammerFinite (q ^ (m + t + 1)) q (m + 1) :=
    qPochhammerFinite_pos (pow_nonneg hq0.le _) (positive_shift_power_lt_one
      hq0 hq1 (m + t + 1) (by omega)) hq0.le hq1.le _
  unfold actualMomentTerm
  calc
    _ = q ^ ((m + 1) * t) * ((qPochhammerFinite q q m) ^ 3 *
          qPochhammerFinite (q ^ (t + 1)) q m) /
          qPochhammerFinite (q ^ (m + t + 1)) q (m + 1) := by ring
    _ ≤ q ^ ((m + 1) * t) /
          qPochhammerFinite (q ^ (m + t + 1)) q (m + 1) := by
      apply div_le_div_of_nonneg_right _ hdenpos.le
      simpa using mul_le_mul_of_nonneg_left hab (pow_nonneg hq0.le _)
    _ ≤ q ^ ((m + 1) * t) / (1 / 2 : ℝ) ^ (m + 1) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hq0.le _) (by positivity) hden
    _ = (2 : ℝ) ^ (m + 1) * q ^ ((m + 1) * t) := by
      rw [div_pow]
      norm_num [div_eq_mul_inv]
      ring

/-- The shifted moment tail is bounded by an explicit geometric tail. -/
lemma actualMoment_tail_le {q : ℝ} (hq0 : 0 < q) (hqhalf : q ≤ 1 / 2)
    (m : ℕ) :
    actualMoment q m - actualMomentTerm q m 0 ≤
      (2 : ℝ) ^ (m + 1) *
        (q ^ (m + 1) / (1 - q ^ (m + 1))) := by
  have hq1 : q < 1 := hqhalf.trans_lt (by norm_num)
  have hr0 : 0 ≤ q ^ (m + 1) := pow_nonneg hq0.le _
  have hr1 : q ^ (m + 1) < 1 :=
    positive_shift_power_lt_one hq0 hq1 (m + 1) (by omega)
  have hs := actualMomentTerm_summable hq0 hq1 m
  have hshift : Summable (fun t : ℕ => actualMomentTerm q m (t + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have hmajor : Summable (fun t : ℕ =>
      (2 : ℝ) ^ (m + 1) * (q ^ (m + 1)) ^ (t + 1)) := by
    exact ((hasSum_geometric_of_lt_one hr0 hr1).summable.mul_left
      ((2 : ℝ) ^ (m + 1))).comp_injective (add_left_injective 1)
  have hsplit := hs.sum_add_tsum_nat_add 1
  have heq : actualMoment q m - actualMomentTerm q m 0 =
      ∑' t : ℕ, actualMomentTerm q m (t + 1) := by
    unfold actualMoment
    simpa using congrArg (fun x : ℝ => x - actualMomentTerm q m 0) hsplit.symm
  rw [heq]
  calc
    _ ≤ ∑' t : ℕ, (2 : ℝ) ^ (m + 1) *
          (q ^ (m + 1)) ^ (t + 1) := by
      apply hshift.tsum_le_tsum _ hmajor
      intro t
      simpa [pow_mul, mul_assoc] using actualMomentTerm_le_geometric hq0 hqhalf m (t + 1)
    _ = (2 : ℝ) ^ (m + 1) *
          (q ^ (m + 1) / (1 - q ^ (m + 1))) := by
      have hgeom := tsum_geometric_of_lt_one hr0 hr1
      calc
        (∑' t : ℕ, (2 : ℝ) ^ (m + 1) *
            (q ^ (m + 1)) ^ (t + 1)) =
            (2 : ℝ) ^ (m + 1) *
              ∑' t : ℕ, (q ^ (m + 1)) ^ (t + 1) := tsum_mul_left
        _ = (2 : ℝ) ^ (m + 1) *
              (q ^ (m + 1) * ∑' t : ℕ, (q ^ (m + 1)) ^ t) := by
          congr 1
          rw [← tsum_mul_left]
          apply tsum_congr
          intro t
          rw [pow_succ]
          ring
        _ = _ := by rw [hgeom]; ring

lemma actualMoment_tail_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (m : ℕ) :
    0 ≤ actualMoment q m - actualMomentTerm q m 0 := by
  have hs := actualMomentTerm_summable hq0 hq1 m
  have hsplit := hs.sum_add_tsum_nat_add 1
  have heq : actualMoment q m - actualMomentTerm q m 0 =
      ∑' t : ℕ, actualMomentTerm q m (t + 1) := by
    unfold actualMoment
    simpa using congrArg (fun x : ℝ => x - actualMomentTerm q m 0) hsplit.symm
  rw [heq]
  exact tsum_nonneg fun t => (actualMomentTerm_pos hq0 hq1 m (t + 1)).le

/-- The zeroth literal summand is a finite rational expression continuous at
`q = 0`, where its value is one. -/
lemma actualMomentTerm_zero_tendsto_one (m : ℕ) :
    Tendsto (fun q : ℝ => actualMomentTerm q m 0) (𝓝 0) (𝓝 1) := by
  have hc : ContinuousAt (fun q : ℝ => actualMomentTerm q m 0) 0 := by
    unfold actualMomentTerm qPochhammerFinite
    fun_prop (disch := simp)
  convert hc.tendsto using 1
  simp [actualMomentTerm, qPochhammerFinite]

/-- For every fixed index, the literal analytic moment tends to one as
`q → 0` through positive values. -/
theorem actualMoment_tendsto_one (m : ℕ) :
    Tendsto (fun q : ℝ => actualMoment q m) (𝓝[>] 0) (𝓝 1) := by
  have hzero := actualMomentTerm_zero_tendsto_one m
  have hbound : Tendsto (fun q : ℝ =>
      (2 : ℝ) ^ (m + 1) * (q ^ (m + 1) / (1 - q ^ (m + 1))))
      (𝓝 0) (𝓝 0) := by
    have hpow : Tendsto (fun q : ℝ => q ^ (m + 1)) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id.pow (m + 1) :
        Tendsto (fun q : ℝ => q ^ (m + 1)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (m + 1))))
    have hden : Tendsto (fun q : ℝ => 1 - q ^ (m + 1)) (𝓝 0) (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hpow :
        Tendsto (fun q : ℝ => 1 - q ^ (m + 1)) (𝓝 0) (𝓝 (1 - 0)))
    have hquot : Tendsto (fun q : ℝ => q ^ (m + 1) / (1 - q ^ (m + 1)))
        (𝓝 0) (𝓝 0) := by
      simpa using hpow.div hden (by norm_num : (1 : ℝ) ≠ 0)
    have hconst : Tendsto (fun _ : ℝ => (2 : ℝ) ^ (m + 1)) (𝓝 0)
        (𝓝 ((2 : ℝ) ^ (m + 1))) := tendsto_const_nhds
    simpa using hconst.mul hquot
  have hdiff : Tendsto (fun q : ℝ =>
      actualMoment q m - actualMomentTerm q m 0) (𝓝[>] 0) (𝓝 0) := by
    have hhalf_nhds : ∀ᶠ q : ℝ in 𝓝 0, q < 1 / 2 :=
      Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)
    have hhalf : ∀ᶠ q : ℝ in 𝓝[>] 0, q < 1 / 2 :=
      hhalf_nhds.filter_mono inf_le_left
    apply squeeze_zero'
    · filter_upwards [self_mem_nhdsWithin, hhalf] with q hq0 hqhalf
      exact actualMoment_tail_nonneg hq0 (hqhalf.trans (by norm_num)) m
    · filter_upwards [self_mem_nhdsWithin, hhalf] with q hq0 hqhalf
      exact actualMoment_tail_le hq0 hqhalf.le m
    · exact hbound.mono_left inf_le_left
  have := hdiff.add (hzero.mono_left inf_le_left)
  convert this using 1 <;> ring_nf

/-- The form needed by the polynomial-part uniqueness theorem. -/
theorem actualMoment_inverse_tendsto_one (m : ℕ) :
    Tendsto (fun p : ℝ => actualMoment p⁻¹ m) atTop (𝓝 1) :=
  (actualMoment_tendsto_one m).comp tendsto_inv_atTop_nhdsGT_zero

#print axioms actualMomentTerm_le_geometric
#print axioms actualMoment_tail_le
#print axioms actualMoment_tendsto_one
#print axioms actualMoment_inverse_tendsto_one

end
end ErdosProblems.Erdos1049.PaperR20
