import ErdosProblems.Erdos1049.G02CyclotomicR16
import ErdosProblems.Erdos1049.ActualAGrowthR14
import ErdosProblems.Erdos1049.LambertSourceSummationR14
import ErdosProblems.Erdos1049.PaperLongCapR9
import Mathlib

/-!
# G02 literal source-rate assembly

Every endpoint below specialises the actual R11/R13 U,V and R9 remainder.
No totient, cyclotomic, degree, or remainder rate is a hypothesis of the
final source theorem. Proves exact quadratic rates of U, V, A and the remainder.
This is not a construction of a new common-width four-jet family.
-/
namespace ErdosProblems.Erdos1049.PaperR16
open Polynomial Finset Filter Asymptotics
open PaperR9 PaperR10 PaperR11 PaperR12 PaperR13 PaperR14
open scoped BigOperators Topology
set_option maxHeartbeats 3000000

noncomputable def sourceUEvalR16 (p : ℝ) (n : ℕ) : ℝ :=
  (sourceU n).eval₂ (Int.castRingHom ℝ) p
noncomputable def sourceVEvalR16 (p : ℝ) (n : ℕ) : ℝ :=
  (sourceV n).eval₂ (Int.castRingHom ℝ) p
noncomputable def sourceAEvalR16 (p : ℝ) (n : ℕ) : ℝ :=
  (sourceA n).eval₂ (Int.castRingHom ℝ) p
noncomputable def sourceRemainderR16 (p : ℝ) (n : ℕ) : ℝ :=
  polynomialRemainder sourceU sourceV PaperR7.paperLambert p n

lemma sourceM_rateR16 : QuadRateR16 (fun n => (sourceM n : ℝ)) 266 := by
  apply rate_of_eventual_linear_errorR16 _ 266 35 (by norm_num)
  exact Eventually.of_forall (fun n => by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have he : (sourceM n : ℝ)-266*sqScale n = 34*(n : ℝ)+1 := by
      simp only [sourceM, sqScale, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    rw [he, abs_of_nonneg (by positivity)]
    nlinarith)

lemma sourceK_rateR16 : QuadRateR16 (fun n => (sourceK n : ℝ)) sourceC1R16 := by
  apply rate_of_eventual_linear_errorR16 _ sourceC1R16 42 (by norm_num)
  exact Eventually.of_forall (fun n => by
    simpa only [sourceC1R16, sqScale] using sourceK_quadratic_residual n)

lemma actual_U_degree_identityR16 (n : ℕ) (hn : 1 ≤ n) :
    ((sourceU n).natDegree : ℝ) =
      (sourceK n : ℝ)-(sourceM n : ℝ)+complementDegreeR16 n := by
  have hk := (sourceK_gt_M n hn).le
  rw [actual_U_degree, Nat.cast_add, Nat.cast_sub hk]
  unfold complementDegreeR16
  rw [(sourceComplement_monic_degree n).2]

lemma actual_U_degree_posR16 (n : ℕ) (hn : 1 ≤ n) : 0 < (sourceU n).natDegree := by
  rw [actual_U_degree]
  have hk := sourceK_gt_M n hn
  omega

lemma actual_pairWidth_identityR16 (n : ℕ) (hn : 1 ≤ n) :
    pairWidth sourceU sourceV n = (sourceU n).natDegree := by
  unfold pairWidth
  rw [actual_V_quotient_degree n hn]
  exact max_eq_left (Nat.sub_le _ _)

theorem actual_U_degree_rateR16 :
    QuadRateR16 (fun n => ((sourceU n).natDegree : ℝ)) sourceDeltaR16 := by
  have h := (sourceK_rateR16.sub sourceM_rateR16).add actual_complement_degree_rateR16
  have hc : sourceC1R16-266+sourceGammaR16=sourceDeltaR16 := by
    unfold sourceDeltaR16 sourceC0R16
    ring
  rw [hc] at h
  apply h.congr_eventually
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (actual_U_degree_identityR16 n hn).symm

theorem actual_V_degree_rateR16 :
    QuadRateR16 (fun n => ((sourceV n).natDegree : ℝ)) sourceDeltaR16 := by
  have hconst : QuadRateR16 (fun _ : ℕ => (-1 : ℝ)) 0 :=
    bounded_rate_zeroR16 _ 1 (by norm_num) (Eventually.of_forall (fun _ => by norm_num))
  have h := actual_U_degree_rateR16.add hconst
  simp only [add_zero] at h
  apply h.congr_eventually
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [actual_V_quotient_degree n hn,
    Nat.cast_sub (show 1 ≤ (sourceU n).natDegree by have := actual_U_degree_posR16 n hn; omega)]
  norm_num
  ring

theorem actual_pairWidth_rateR16 :
    QuadRateR16 (fun n => (pairWidth sourceU sourceV n : ℝ)) sourceDeltaR16 := by
  apply actual_U_degree_rateR16.congr_eventually
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [actual_pairWidth_identityR16 n hn]

theorem actual_pairWidth_upperR16 :
    QuadUpper (fun n => (pairWidth sourceU sourceV n : ℝ)) sourceDeltaR16 :=
  actual_pairWidth_rateR16.upper

lemma actual_A_eventually_nonzeroR16 (p : ℝ) (hp : 1 < p) :
    ∀ᶠ n in atTop, sourceAEvalR16 p n ≠ 0 := by
  obtain ⟨L, U, hL, hU, hb⟩ := actual_A_eventual_two_sided p hp
  filter_upwards [hb] with n hn
  have hpos : 0 < |sourceAEvalR16 p n| :=
    (mul_pos hL (pow_pos (zero_lt_one.trans hp) _)).trans_le hn.1
  exact abs_pos.mp hpos

lemma actual_U_eval_normalisationR16 (p : ℝ) (hp : 1 < p) (n : ℕ) :
    sourceUEvalR16 p n = complementEvalR16 p n*sourceAEvalR16 p n/p^sourceM n := by
  have hp0 := (zero_lt_one.trans hp).ne'
  apply (eq_div_iff (pow_ne_zero _ hp0)).2
  have h := actual_real_A_normalisation p n
  dsimp [sourceUEvalR16, complementEvalR16, sourceAEvalR16]
  simpa only [mul_comm] using h.symm

lemma actual_U_eventually_nonzeroR16 (p : ℝ) (hp : 1 < p) :
    ∀ᶠ n in atTop, sourceUEvalR16 p n ≠ 0 := by
  filter_upwards [actual_A_eventually_nonzeroR16 p hp] with n hn
  rw [actual_U_eval_normalisationR16 p hp n]
  exact div_ne_zero (mul_ne_zero (actual_complement_posR16 p hp n).ne' hn)
    (pow_ne_zero _ (zero_lt_one.trans hp).ne')

theorem actual_U_quadLogRateR16 (p : ℝ) (hp : 1 < p) :
    QuadLogRate (sourceUEvalR16 p) (sourceDeltaR16*Real.log p) := by
  have hA : QuadLogRate (sourceAEvalR16 p) (sourceC1R16*Real.log p) :=
    actual_A_quadLogRate p hp
  have hC := actual_complement_quadLogRateR16 p hp
  have hm := quadLogRate_powerR16 sourceM 266 p (zero_lt_one.trans hp) sourceM_rateR16
  have hCn : ∀ᶠ n in atTop, complementEvalR16 p n ≠ 0 :=
    Eventually.of_forall (fun n => (actual_complement_posR16 p hp n).ne')
  have hAn := actual_A_eventually_nonzeroR16 p hp
  have hmn : ∀ᶠ n in atTop, p^sourceM n ≠ 0 :=
    Eventually.of_forall (fun n => pow_ne_zero _ (zero_lt_one.trans hp).ne')
  have h := quadLogRate_divR16 (quadLogRate_mulR16 hC hA hCn hAn) hm
    (by filter_upwards [hCn, hAn] with n hn hm; exact mul_ne_zero hn hm) hmn
  have hc : sourceGammaR16*Real.log p+sourceC1R16*Real.log p-266*Real.log p =
      sourceDeltaR16*Real.log p := by
    unfold sourceDeltaR16 sourceC0R16
    ring
  rw [hc] at h
  apply quadLogRate_congrR16 h
  exact Eventually.of_forall (fun n => (actual_U_eval_normalisationR16 p hp n).symm)

/-- Positivity strengthens the inherited nonvanishing statement, at every n. -/
theorem actual_remainder_posR16 (p : ℝ) (hp : 1 < p) (n : ℕ) :
    0 < sourceRemainderR16 p n := by
  rw [sourceRemainderR16, actual_cancelled_remainder_identity p hp n]
  have hp0 := zero_lt_one.trans hp
  exact div_pos (mul_pos (actual_complement_posR16 p hp n)
    (sourcePositiveH_pos (inv_pos.mpr hp0) ((inv_lt_one₀ hp0).2 hp) n))
    (pow_pos hp0 _)

/-- Exact rate of the unchanged R9 polynomial remainder, not only an upper bound. -/
theorem actual_remainder_quadLogRateR16 (p : ℝ) (hp : 1 < p) :
    QuadLogRate (sourceRemainderR16 p) (-sourceC0R16*Real.log p) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := inv_pos.mpr hp0
  have hq1 := (inv_lt_one₀ hp0).2 hp
  have hC := actual_complement_quadLogRateR16 p hp
  have hH := sourcePositiveH_quadLogRate_zero hq0 hq1
  have hCn : ∀ᶠ n in atTop, complementEvalR16 p n ≠ 0 :=
    Eventually.of_forall (fun n => (actual_complement_posR16 p hp n).ne')
  have hHn : ∀ᶠ n in atTop, sourcePositiveH p⁻¹ n ≠ 0 :=
    Eventually.of_forall (fun n => (sourcePositiveH_pos hq0 hq1 n).ne')
  have hm := quadLogRate_powerR16 sourceM 266 p hp0 sourceM_rateR16
  have hmn : ∀ᶠ n in atTop, p^sourceM n ≠ 0 :=
    Eventually.of_forall (fun n => pow_ne_zero _ hp0.ne')
  have h := quadLogRate_divR16 (quadLogRate_mulR16 hC hH hCn hHn) hm
    (by filter_upwards [hCn, hHn] with n hn hm; exact mul_ne_zero hn hm) hmn
  have hc : sourceGammaR16*Real.log p+0-266*Real.log p =
      -sourceC0R16*Real.log p := by
    unfold sourceC0R16
    ring
  rw [hc] at h
  apply quadLogRate_congrR16 h
  exact Eventually.of_forall (fun n =>
    (actual_cancelled_remainder_identity p hp n).symm)

lemma paperLambert_posR16 (p : ℝ) (hp : 1 < p) : 0 < PaperR7.paperLambert p := by
  have hs := paperLambert_summable p hp
  have ht : 0 < 1/(p^(0+1)-1) :=
    one_div_pos.mpr (power_sub_one_posR16 p hp 1 (by norm_num))
  have hb := hs.le_tsum 0 (fun k _ =>
    (one_div_pos.mpr (power_sub_one_posR16 p hp (k+1) (by omega))).le)
  exact ht.trans_le hb

/-- The V equality follows from strict separation of the U and remainder rates. -/
theorem actual_V_quadLogRate_and_nonzeroR16 (p : ℝ) (hp : 1 < p) :
    QuadLogRate (sourceVEvalR16 p) (sourceDeltaR16*Real.log p) ∧
      (∀ᶠ n in atTop, sourceVEvalR16 p n ≠ 0) := by
  have hl : 0 < Real.log p := Real.log_pos hp
  have hgap : -sourceC0R16*Real.log p < sourceDeltaR16*Real.log p := by
    have hc : 0 < sourceC1R16*Real.log p := by unfold sourceC1R16; positivity
    have he := source_rate_constantsR16.1
    nlinarith
  have hLn : ∀ᶠ n in atTop, sourceRemainderR16 p n ≠ 0 :=
    Eventually.of_forall (fun n => (actual_remainder_posR16 p hp n).ne')
  obtain ⟨hr, hn⟩ := quadLogRate_dominant_differenceR16
    (sourceUEvalR16 p) (sourceRemainderR16 p)
    (sourceDeltaR16*Real.log p) (-sourceC0R16*Real.log p) (PaperR7.paperLambert p)
    (paperLambert_posR16 p hp) hgap (actual_U_quadLogRateR16 p hp)
    (actual_remainder_quadLogRateR16 p hp) (actual_U_eventually_nonzeroR16 p hp) hLn
  have he (n : ℕ) : PaperR7.paperLambert p*sourceUEvalR16 p n-
      sourceRemainderR16 p n = sourceVEvalR16 p n := by
    dsimp [sourceUEvalR16, sourceVEvalR16, sourceRemainderR16, polynomialRemainder]
    ring
  constructor
  · exact quadLogRate_congrR16 hr (Eventually.of_forall he)
  · filter_upwards [hn] with n hn'
    simpa only [he] using hn'

theorem actual_V_quadLogRateR16 (p : ℝ) (hp : 1 < p) :
    QuadLogRate (sourceVEvalR16 p) (sourceDeltaR16*Real.log p) :=
  (actual_V_quadLogRate_and_nonzeroR16 p hp).1

theorem actual_U_exp_upperR16 (p : ℝ) (hp : 1 < p) :
    QuadExpUpper (sourceUEvalR16 p) (sourceDeltaR16*Real.log p) :=
  actual_U_eval_of_degree_rate sourceDeltaR16 p hp actual_pairWidth_upperR16

theorem actual_remainder_tendsto_zeroR16 (p : ℝ) (hp : 1 < p) :
    Tendsto (sourceRemainderR16 p) atTop (𝓝 0) := by
  apply (actual_remainder_quadLogRateR16 p hp).exp_upper.tendsto_zero
  have h := mul_pos sourceC0_posR16 (Real.log_pos hp)
  nlinarith

/-- Closed short-note consumer package. This asserts no irrationality conclusion. -/
theorem actual_shortCapHypothesesR16 :
    CapHypotheses sourceU sourceV PaperR7.paperLambert sourceC0R16 sourceDeltaR16 0 := by
  refine ⟨sourceC0_posR16, sourceDelta_posR16, le_rfl, actual_pairWidth_upperR16,
    actual_pairHeight_log_upper_zero, ?_, ?_⟩
  · intro p hp
    exact Eventually.of_forall (fun n => actual_cancelled_remainder_nonzero p hp n)
  · intro p hp
    exact actual_remainder_quadLogRateR16 p hp

/-- Closed long-paper consumer package, preserving the actual max-height convention. -/
theorem actual_longCapHypothesesR16 :
    LongCapHypotheses sourceU sourceV PaperR7.paperLambert sourceC0R16 sourceDeltaR16 0 := by
  refine ⟨sourceC0_posR16, sourceDelta_posR16, le_rfl, actual_pairWidth_upperR16,
    actual_maxPairHeight_log_upper_zero, ?_, ?_⟩
  · intro p hp
    exact Eventually.of_forall (fun n => actual_cancelled_remainder_nonzero p hp n)
  · intro p hp
    exact actual_remainder_quadLogRateR16 p hp

/-- Exact actual-width homogenisation. It does not assert integrality at arbitrary real a,b. -/
theorem actual_cleared_remainder_rateR16 (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    QuadLogRate
      (fun n => b^pairWidth sourceU sourceV n * sourceRemainderR16 (a/b) n)
      (sourceC1R16*Real.log b-sourceC0R16*Real.log a) := by
  have ha : 0 < a := hb.trans hab
  have hp : 1 < a/b := (lt_div_iff₀ hb).2 (by simpa using hab)
  have hpow := quadLogRate_powerR16 (pairWidth sourceU sourceV) sourceDeltaR16 b hb
    actual_pairWidth_rateR16
  have hrem := actual_remainder_quadLogRateR16 (a/b) hp
  have h := quadLogRate_mulR16 hpow hrem
    (Eventually.of_forall (fun n => pow_ne_zero _ hb.ne'))
    (Eventually.of_forall (fun n => (actual_remainder_posR16 (a/b) hp n).ne'))
  have he : sourceDeltaR16*Real.log b + -sourceC0R16*Real.log (a/b) =
      sourceC1R16*Real.log b-sourceC0R16*Real.log a := by
    rw [Real.log_div ha.ne' hb.ne']
    linear_combination Real.log b * source_rate_constantsR16.1
  rwa [he] at h

/-- The normalised limit notation used in the paper, with no new supplier premise. -/
theorem actual_source_normalised_limitsR16 (p : ℝ) (hp : 1 < p) :
    Tendsto (fun n => (pairWidth sourceU sourceV n : ℝ)/sqScale n)
      atTop (𝓝 sourceDeltaR16) ∧
    Tendsto (fun n => Real.log |sourceUEvalR16 p n|/sqScale n)
      atTop (𝓝 (sourceDeltaR16*Real.log p)) ∧
    Tendsto (fun n => Real.log |sourceVEvalR16 p n|/sqScale n)
      atTop (𝓝 (sourceDeltaR16*Real.log p)) ∧
    Tendsto (fun n => Real.log |sourceRemainderR16 p n|/sqScale n)
      atTop (𝓝 (-sourceC0R16*Real.log p)) := by
  exact ⟨normalized_tendsto_of_littleO _ _ actual_pairWidth_rateR16,
    normalized_tendsto_of_littleO _ _ (actual_U_quadLogRateR16 p hp),
    normalized_tendsto_of_littleO _ _ (actual_V_quadLogRateR16 p hp),
    normalized_tendsto_of_littleO _ _ (actual_remainder_quadLogRateR16 p hp)⟩

/-- Final source-only endpoint. The sole varying input is a real p>1. -/
theorem actual_source_quad_ratesR16 (p : ℝ) (hp : 1 < p) :
    QuadRateR16 (fun n => (pairWidth sourceU sourceV n : ℝ)) sourceDeltaR16 ∧
    QuadLogRate (pairHeight sourceU sourceV) 0 ∧
    QuadLogRate (maxPairHeight sourceU sourceV) 0 ∧
    QuadLogRate (complementEvalR16 p) (sourceGammaR16*Real.log p) ∧
    QuadLogRate (sourceAEvalR16 p) (sourceC1R16*Real.log p) ∧
    QuadLogRate (sourceUEvalR16 p) (sourceDeltaR16*Real.log p) ∧
    QuadLogRate (sourceVEvalR16 p) (sourceDeltaR16*Real.log p) ∧
    QuadLogRate (sourceRemainderR16 p) (-sourceC0R16*Real.log p) ∧
    (∀ n, 0 < sourceRemainderR16 p n) := by
  exact ⟨actual_pairWidth_rateR16,
    actual_pairHeight_quadLogRate_zero, actual_maxPairHeight_quadLogRate_zero,
    actual_complement_quadLogRateR16 p hp, actual_A_quadLogRate p hp,
    actual_U_quadLogRateR16 p hp, actual_V_quadLogRateR16 p hp,
    actual_remainder_quadLogRateR16 p hp, actual_remainder_posR16 p hp⟩

end ErdosProblems.Erdos1049.PaperR16
