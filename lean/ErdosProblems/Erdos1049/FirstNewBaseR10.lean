import ErdosProblems.Erdos1049.RationalBaseContour
import ErdosProblems.Erdos1049.QProductBoundsR10

/-!
# The least new denominator and numerator

These are the actual infinite-contour parameter statements.
They do not assert irrationality of a Lambert value. The sharper upper
contour is proved by a convergent-series tail bound, not a decimal oracle.
-/
namespace ErdosProblems.Erdos1049.PaperR10
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- A telescoping integral-comparison bound for the actual trigamma series. -/
theorem trigammaSeries_le_inverse_sub_one {x : ℝ} (hx : 1 < x) :
    trigammaSeries x ≤ 1 / (x - 1) := by
  have hp (N : ℕ) :
      (∑ k ∈ Finset.range N, 1 / ((k : ℝ) + x) ^ 2) ≤
        1 / (x - 1) - 1 / ((N : ℝ) + x - 1) := by
    induction N with
    | zero => simp
    | succ N hN =>
      have hz : 0 < (N : ℝ) + x - 1 := by
        linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
      have hz' : 0 < (N : ℝ) + x := by
        linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
      have ht : 1 / ((N : ℝ) + x) ^ 2 ≤
          1 / ((N : ℝ) + x - 1) - 1 / ((N : ℝ) + x) := by
        calc
          _ ≤ 1 / (((N : ℝ) + x) * ((N : ℝ) + x - 1)) :=
            one_div_le_one_div_of_le (mul_pos hz' hz) (by nlinarith)
          _ = _ := by field_simp [hz.ne', hz'.ne']; ring
      have he : ((N + 1 : ℕ) : ℝ) + x - 1 = (N : ℝ) + x := by
        push_cast; ring
      rw [Finset.sum_range_succ, he]
      linarith
  unfold trigammaSeries
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro N
  have hz : 0 < (N : ℝ) + x - 1 := by
    linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
  exact (hp N).trans (sub_le_self _ (one_div_nonneg.mpr hz.le))

lemma trigammaSeries_split (K : ℕ) {x : ℝ} (hx : 0 < x) :
    (∑ k ∈ Finset.range K, 1 / ((k : ℝ) + x) ^ 2) +
      trigammaSeries ((K : ℝ) + x) = trigammaSeries x := by
  have h := (summable_trigammaTerm hx).sum_add_tsum_nat_add K
  simpa [trigammaSeries, Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

/-- A deliberately loose but sufficient common tail bound after sixteen terms. -/
lemma zudilinJTerm_upper_sixteen {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    zudilinJTerm u v ≤
      (∑ k ∈ Finset.range 16,
        (1 / ((k : ℝ) + u) ^ 2 - 1 / ((k : ℝ) + v) ^ 2)) + 1 / 15 := by
  have hsU := trigammaSeries_split 16 hu
  have hsV := trigammaSeries_split 16 hv
  have ht := trigammaSeries_le_inverse_sub_one (x := 16 + u) (by linarith)
  have ht' : trigammaSeries (16 + u) ≤ (1 : ℝ) / 15 := by
    apply ht.trans
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hv' := trigammaSeries_nonneg (16 + v)
  norm_num at hsU hsV
  have hsU' :
      (∑ k ∈ Finset.range 16, 1 / ((k : ℝ) + u) ^ 2) +
        trigammaSeries (16 + u) = trigammaSeries u := by
    simpa only [one_div] using hsU
  have hsV' :
      (∑ k ∈ Finset.range 16, 1 / ((k : ℝ) + v) ^ 2) +
        trigammaSeries (16 + v) = trigammaSeries v := by
    simpa only [one_div] using hsV
  unfold zudilinJTerm
  have htail :
      trigammaSeries (16 + u) - trigammaSeries (16 + v) ≤ (1 : ℝ) / 15 := by
    linarith
  calc
    trigammaSeries u - trigammaSeries v =
        ((∑ k ∈ Finset.range 16, 1 / ((k : ℝ) + u) ^ 2) +
          trigammaSeries (16 + u)) -
        ((∑ k ∈ Finset.range 16, 1 / ((k : ℝ) + v) ^ 2) +
          trigammaSeries (16 + v)) := by rw [hsU', hsV']
    _ = (∑ k ∈ Finset.range 16,
          (1 / ((k : ℝ) + u) ^ 2 - 1 / ((k : ℝ) + v) ^ 2)) +
          (trigammaSeries (16 + u) - trigammaSeries (16 + v)) := by
        rw [Finset.sum_sub_distrib]
        ring
    _ ≤ _ := add_le_add_right htail _

/-- The thirteen finite sums plus their proven tails give J < 79. -/
theorem zudilinJ_lt_79 : zudilinJ < 79 := by
  have h1 := zudilinJTerm_upper_sixteen (u := (1 / 14)) (v := (1 / 12))
    (by norm_num) (by norm_num)
  have c1 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (1 / 14)) ^ 2 - 1 / ((k : ℝ) + (1 / 12)) ^ 2)) <
      (5202337679 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h2 := zudilinJTerm_upper_sixteen (u := (1 / 7)) (v := (1 / 6))
    (by norm_num) (by norm_num)
  have c2 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (1 / 7)) ^ 2 - 1 / ((k : ℝ) + (1 / 6)) ^ 2)) <
      (1303886130 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h3 := zudilinJTerm_upper_sixteen (u := (3 / 14)) (v := (1 / 4))
    (by norm_num) (by norm_num)
  have c3 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (3 / 14)) ^ 2 - 1 / ((k : ℝ) + (1 / 4)) ^ 2)) <
      (582689311 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h4 := zudilinJTerm_upper_sixteen (u := (2 / 7)) (v := (1 / 3))
    (by norm_num) (by norm_num)
  have c4 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (2 / 7)) ^ 2 - 1 / ((k : ℝ) + (1 / 3)) ^ 2)) <
      (330583529 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h5 := zudilinJTerm_upper_sixteen (u := (5 / 14)) (v := (2 / 5))
    (by norm_num) (by norm_num)
  have c5 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (5 / 14)) ^ 2 - 1 / ((k : ℝ) + (2 / 5)) ^ 2)) <
      (163395903 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h6 := zudilinJTerm_upper_sixteen (u := (3 / 7)) (v := (7 / 15))
    (by norm_num) (by norm_num)
  have c6 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (3 / 7)) ^ 2 - 1 / ((k : ℝ) + (7 / 15)) ^ 2)) <
      (88704482 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h7 := zudilinJTerm_upper_sixteen (u := (1 / 2)) (v := (8 / 15))
    (by norm_num) (by norm_num)
  have c7 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (1 / 2)) ^ 2 - 1 / ((k : ℝ) + (8 / 15)) ^ 2)) <
      (51110981 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h8 := zudilinJTerm_upper_sixteen (u := (4 / 7)) (v := (3 / 5))
    (by norm_num) (by norm_num)
  have c8 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (4 / 7)) ^ 2 - 1 / ((k : ℝ) + (3 / 5)) ^ 2)) <
      (30517747 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h9 := zudilinJTerm_upper_sixteen (u := (9 / 14)) (v := (2 / 3))
    (by norm_num) (by norm_num)
  have c9 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (9 / 14)) ^ 2 - 1 / ((k : ℝ) + (2 / 3)) ^ 2)) <
      (18505298 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h10 := zudilinJTerm_upper_sixteen (u := (5 / 7)) (v := (11 / 15))
    (by norm_num) (by norm_num)
  have c10 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (5 / 7)) ^ 2 - 1 / ((k : ℝ) + (11 / 15)) ^ 2)) <
      (11153721 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h11 := zudilinJTerm_upper_sixteen (u := (11 / 14)) (v := (4 / 5))
    (by norm_num) (by norm_num)
  have c11 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (11 / 14)) ^ 2 - 1 / ((k : ℝ) + (4 / 5)) ^ 2)) <
      (6483918 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h12 := zudilinJTerm_upper_sixteen (u := (6 / 7)) (v := (13 / 15))
    (by norm_num) (by norm_num)
  have c12 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (6 / 7)) ^ 2 - 1 / ((k : ℝ) + (13 / 15)) ^ 2)) <
      (3430314 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  have h13 := zudilinJTerm_upper_sixteen (u := (13 / 14)) (v := (14 / 15))
    (by norm_num) (by norm_num)
  have c13 : (∑ k ∈ Finset.range 16,
      (1 / ((k : ℝ) + (13 / 14)) ^ 2 - 1 / ((k : ℝ) + (14 / 15)) ^ 2)) <
      (1388391 : ℝ) / 100000000 := by norm_num [Finset.sum_range_succ]
  unfold zudilinJ
  linarith only [h1, c1, h2, c2, h3, c3, h4, c4, h5, c5, h6, c6, h7, c7, h8, c8, h9, c9, h10, c10, h11, c11, h12, c12, h13, c13]

/-- This small upper bracket is strong enough to prove least-base assertions. -/
theorem zudilinContour_lt_eleven_twentysevenths :
    zudilinContour < (11 : ℝ) / 27 := by
  have hJ := zudilinJ_lt_79
  have hpi : Real.pi ^ 2 < 10 := by
    have h := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have hcoef : (3 : ℝ) / 10 < 3 / Real.pi ^ 2 :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) hpi
  have hp : (3 : ℝ) / 10 * 146 < 3 / Real.pi ^ 2 * (225 - zudilinJ) := by
    have h1 := mul_lt_mul_of_pos_left (show (146 : ℝ) < 225 - zudilinJ by linarith)
      (by positivity : (0 : ℝ) < 3 / Real.pi ^ 2)
    have h2 := mul_lt_mul_of_pos_right hcoef (by norm_num : (0 : ℝ) < 146)
    exact h2.trans h1
  unfold zudilinContour
  apply (div_lt_iff₀ zudilinC1_pos).mpr
  unfold zudilinC0 zudilinC1
  linarith

theorem bundschuhMargin_gt_199_500 :
    (199 : ℝ) / 500 < 1 / 2 - 1 / Real.pi ^ 2 := by
  have hpi : (500 : ℝ) / 51 < Real.pi ^ 2 := by
    have h := Real.pi_gt_d2
    nlinarith [Real.pi_pos]
  have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 500 / 51) hpi
  norm_num at h
  calc
    (199 : ℝ) / 500 = 1 / 2 - 51 / 500 := by norm_num
    _ < 1 / 2 - (Real.pi ^ 2)⁻¹ := sub_lt_sub_left h _
    _ = 1 / 2 - 1 / Real.pi ^ 2 := by simp only [one_div]

lemma not_contour_of_eleventh_power_le {a b : ℕ}
    (ha : 1 < a) (hb : 0 < b) (hp : a ^ 11 ≤ b ^ 27) :
    ¬ ZudilinContourRegion a b := by
  intro h
  have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha)
  have hr : Real.log b / Real.log a < (11 : ℝ) / 27 :=
    h.trans zudilinContour_lt_eleven_twentysevenths
  have hr' := (div_lt_iff₀ hlog).mp hr
  have hpR : (a : ℝ) ^ 11 ≤ (b : ℝ) ^ 27 := by exact_mod_cast hp
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hh := Real.log_le_log (pow_pos haR 11) hpR
  rw [Real.log_pow, Real.log_pow] at hh
  norm_num at hh
  linarith

lemma bvRegion_of_500_199_power {a b : ℕ}
    (ha : 1 < a) (hb : 0 < b) (hp : b ^ 500 < a ^ 199) :
    BundschuhVaananenHeightRegion a b := by
  have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha)
  have hpR : (b : ℝ) ^ 500 < (a : ℝ) ^ 199 := by exact_mod_cast hp
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hh := Real.log_lt_log (pow_pos hbR 500) hpR
  rw [Real.log_pow, Real.log_pow] at hh
  norm_num at hh
  have hr : Real.log b / Real.log a < (199 : ℝ) / 500 := by
    apply (div_lt_iff₀ hlog).mpr
    linarith
  exact hr.trans bundschuhMargin_gt_199_500

/-- Both regions are strict, so the old boundary belongs to their difference. -/
theorem strict_region_difference (t old new : ℝ) :
    (t < new ∧ ¬ t < old) ↔ old ≤ t ∧ t < new := by
  constructor <;> intro h
  · exact ⟨le_of_not_gt h.2, h.1⟩
  · exact ⟨h.2, not_lt_of_ge h.1⟩

/-- This definition records only the difference of the two sufficient regions. -/
def NewContourBase (a b : ℕ) : Prop :=
  1 ≤ b ∧ b < a ∧ Nat.Coprime a b ∧
    ZudilinContourRegion a b ∧ ¬ BundschuhVaananenHeightRegion a b

/-- A small-exponent certificate for the three large power comparisons below. -/
lemma pow_500_lt_pow_199_of {x y : ℕ}
    (hx : 0 < x) (hy : 0 < y)
    (h58 : x ^ 58 < y ^ 23) (h5 : x ^ 5 < y ^ 2) :
    x ^ 500 < y ^ 199 := by
  calc
    x ^ 500 = (x ^ 58) ^ 5 * (x ^ 5) ^ 42 := by
      rw [show 500 = 58 * 5 + 5 * 42 by norm_num, pow_add, pow_mul, pow_mul]
    _ < (y ^ 23) ^ 5 * (x ^ 5) ^ 42 :=
      Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left h58 (by norm_num)) (by positivity)
    _ < (y ^ 23) ^ 5 * (y ^ 2) ^ 42 :=
      Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left h5 (by norm_num)) (by positivity)
    _ = y ^ 199 := by
      rw [show 199 = 23 * 5 + 2 * 42 by norm_num, pow_add, pow_mul, pow_mul]

lemma contour_denominator_two_old {a : ℕ} (ha : 2 < a)
    (h : ZudilinContourRegion a 2) : BundschuhVaananenHeightRegion a 2 := by
  have ha6 : 6 ≤ a := by
    by_contra hn
    have hp : a ^ 11 ≤ 2 ^ 27 :=
      (Nat.pow_le_pow_left (by omega : a ≤ 5) 11).trans
        (by norm_num : 5 ^ 11 ≤ 2 ^ 27)
    exact not_contour_of_eleventh_power_le (by omega) (by norm_num) hp h
  apply bvRegion_of_500_199_power (by omega) (by norm_num)
  have hpow : 2 ^ 500 < 6 ^ 199 :=
    pow_500_lt_pow_199_of (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hpow.trans_le (Nat.pow_le_pow_left ha6 199)

lemma contour_denominator_three_old {a : ℕ} (ha : 3 < a)
    (hc : Nat.Coprime a 3) (h : ZudilinContourRegion a 3) :
    BundschuhVaananenHeightRegion a 3 := by
  have ha15 : 15 ≤ a := by
    by_contra hn
    have hp : a ^ 11 ≤ 3 ^ 27 :=
      (Nat.pow_le_pow_left (by omega : a ≤ 14) 11).trans
        (by norm_num : 14 ^ 11 ≤ 3 ^ 27)
    exact not_contour_of_eleventh_power_le (by omega) (by norm_num) hp h
  have hne : a ≠ 15 := by intro he; subst a; norm_num at hc
  have ha16 : 16 ≤ a := by omega
  apply bvRegion_of_500_199_power (by omega) (by norm_num)
  have hpow : 3 ^ 500 < 16 ^ 199 :=
    pow_500_lt_pow_199_of (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact hpow.trans_le (Nat.pow_le_pow_left ha16 199)

/-- Minimality over all positive coprime pairs, not merely a finite scan. -/
theorem newContourBase_minimal {a b : ℕ} (h : NewContourBase a b) :
    4 ≤ b ∧ 31 ≤ a := by
  rcases h with ⟨hb, hba, hc, hr, hold⟩
  have hb4 : 4 ≤ b := by
    by_contra hn
    have cases : b = 1 ∨ b = 2 ∨ b = 3 := by omega
    rcases cases with he | he | he
    · subst b
      apply hold
      have hp := bundschuhMargin_gt_199_500
      simpa [BundschuhVaananenHeightRegion] using
        (show (0 : ℝ) < 1 / 2 - 1 / Real.pi ^ 2 by linarith)
    · subst b
      exact hold (contour_denominator_two_old hba hr)
    · subst b
      exact hold (contour_denominator_three_old hba hc hr)
  refine ⟨hb4, ?_⟩
  by_contra hn
  have hp : a ^ 11 ≤ b ^ 27 := calc
    a ^ 11 ≤ 30 ^ 11 := Nat.pow_le_pow_left (by omega) 11
    _ ≤ 4 ^ 27 := by norm_num
    _ ≤ b ^ 27 := Nat.pow_le_pow_left hb4 27
  exact not_contour_of_eleventh_power_le (by omega) (by omega) hp hr

theorem thirtyoneFour_is_newContourBase : NewContourBase 31 4 := by
  refine ⟨by norm_num, by norm_num, by norm_num,
    thirtyoneFour_mem_zudilinContourRegion, ?_⟩
  exact thirtyoneFour_outside_bundschuhVaananenHeightRegion

/-- At the first denominator the new numerator is unique. -/
theorem newContourBase_denominator_four_iff (a : ℕ) :
    NewContourBase a 4 ↔ a = 31 := by
  constructor
  · intro h
    have hmin := (newContourBase_minimal h).2
    have hc := h.2.2.1
    have hn32 : a ≠ 32 := by intro he; subst a; norm_num at hc
    by_contra hne
    have ha33 : 33 ≤ a := by omega
    apply h.2.2.2.2
    apply bvRegion_of_500_199_power (by omega) (by norm_num)
    have hpow : 4 ^ 500 < 33 ^ 199 :=
      pow_500_lt_pow_199_of (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact hpow.trans_le (Nat.pow_le_pow_left ha33 199)
  · rintro rfl
    exact thirtyoneFour_is_newContourBase

end ErdosProblems.Erdos1049.PaperR10
