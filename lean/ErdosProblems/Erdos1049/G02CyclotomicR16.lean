import ErdosProblems.Erdos1049.G02RateCalculusR16
import ErdosProblems.Erdos1049.ActualSourceRemainderR14
import Mathlib

/-!
# G02 fixed-base cyclotomic logarithms

The factors are the literal integer cyclotomic polynomials, including Φ₁.
The all-index O_p(n) estimate uses a uniform summable-log majorant, rather
than an incorrect O(log l) estimate near the moving unit circle.
Proves the quadratic log rate of the source complement at each real p > 1.
-/
namespace ErdosProblems.Erdos1049.PaperR16
open Polynomial Finset Filter Asymptotics
open PaperR10 PaperR11 PaperR12 PaperR14
open scoped BigOperators Topology
set_option maxHeartbeats 3000000

noncomputable def cyclotomicEvalR16 (p : ℝ) (l : ℕ) : ℝ :=
  (cyclotomic l ℤ).eval₂ (Int.castRingHom ℝ) p
noncomputable def complementEvalR16 (p : ℝ) (n : ℕ) : ℝ :=
  (sourceComplement n).eval₂ (Int.castRingHom ℝ) p
noncomputable def logTailTermR16 (q : ℝ) (k : ℕ) : ℝ :=
  -Real.log (1-q^(k+1))
noncomputable def logTailMajorantR16 (q : ℝ) : ℝ := q/(1-q)^2
noncomputable def weightedLogTailR16 (q : ℝ) (k : ℕ) : ℝ :=
  logTailTermR16 q k / ((k : ℝ)+1)
noncomputable def weightedLogSumR16 (q : ℝ) : ℝ := ∑' k, weightedLogTailR16 q k

lemma logTailTerm_boundsR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ logTailTermR16 q k ∧ logTailTermR16 q k ≤ q^(k+1)/(1-q) := by
  have hpow : q^(k+1) ≤ q := by
    rw [pow_succ]
    nlinarith [pow_le_one₀ hq0.le hq1.le (n := k)]
  have hpos : 0 < 1-q^(k+1) := by linarith
  have hlog : Real.log (1-q^(k+1)) ≤ 0 := by
    have h := Real.log_le_log hpos
      (show 1-q^(k+1) ≤ 1 by have := pow_nonneg hq0.le (k+1); linarith)
    simpa using h
  constructor
  · dsimp [logTailTermR16]; linarith
  · have h := abs_log_one_sub_le (pow_nonneg hq0.le (k+1)) hpow hq1
    simpa only [logTailTermR16, abs_of_nonpos hlog] using h

lemma hasSum_logTail_majorantR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => q^(k+1)/(1-q)) (logTailMajorantR16 q) := by
  have h := hasSum_qPochhammer_log_majorant (a := q) hq0.le hq1
  convert h using 1 <;> simp only [logTailMajorantR16, pow_succ, pow_two] <;> ring

lemma logTailTerm_summableR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (logTailTermR16 q) :=
  summable_nonneg_dominated (fun k => (logTailTerm_boundsR16 q hq0 hq1 k).1)
    (fun k => (logTailTerm_boundsR16 q hq0 hq1 k).2)
    (hasSum_logTail_majorantR16 q hq0 hq1).summable

lemma logTailTerm_tsum_boundR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∑' k, logTailTermR16 q k) ≤ logTailMajorantR16 q := by
  have h := (logTailTerm_summableR16 q hq0 hq1).tsum_le_tsum
    (fun k => (logTailTerm_boundsR16 q hq0 hq1 k).2)
    (hasSum_logTail_majorantR16 q hq0 hq1).summable
  simpa only [(hasSum_logTail_majorantR16 q hq0 hq1).tsum_eq] using h

lemma logTailTerm_tail_boundR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (K : ℕ) :
    (∑' k : ℕ, logTailTermR16 q (k+K)) ≤ q^(K+1)/(1-q)^2 := by
  have hs : Summable (fun k : ℕ => logTailTermR16 q (k+K)) :=
    (summable_nat_add_iff K).2 (logTailTerm_summableR16 q hq0 hq1)
  have hg : HasSum (fun k : ℕ => q^(k+K+1)/(1-q)) (q^(K+1)/(1-q)^2) := by
    have h := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (q^(K+1)/(1-q))
    convert h using 1
    · funext k
      rw [show k+K+1=(K+1)+k by omega, pow_add]
      ring
    · simp only [pow_two, div_eq_mul_inv, mul_inv_rev]
      ring
  have ht := hs.tsum_le_tsum (fun k => (logTailTerm_boundsR16 q hq0 hq1 (k+K)).2)
    hg.summable
  simpa only [hg.tsum_eq] using ht

lemma weightedLogTail_boundsR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ weightedLogTailR16 q k ∧ weightedLogTailR16 q k ≤ logTailTermR16 q k := by
  have hb := (logTailTerm_boundsR16 q hq0 hq1 k).1
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  dsimp [weightedLogTailR16]
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < (k : ℝ)+1)).2
    nlinarith

lemma weightedLogTail_summableR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (weightedLogTailR16 q) :=
  summable_nonneg_dominated (fun k => (weightedLogTail_boundsR16 q hq0 hq1 k).1)
    (fun k => (weightedLogTail_boundsR16 q hq0 hq1 k).2)
    (logTailTerm_summableR16 q hq0 hq1)

lemma weightedLogSum_boundR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ weightedLogSumR16 q ∧ weightedLogSumR16 q ≤ logTailMajorantR16 q := by
  constructor
  · exact tsum_nonneg (fun k => (weightedLogTail_boundsR16 q hq0 hq1 k).1)
  · exact ((weightedLogTail_summableR16 q hq0 hq1).tsum_le_tsum
      (fun k => (weightedLogTail_boundsR16 q hq0 hq1 k).2)
      (logTailTerm_summableR16 q hq0 hq1)).trans
        (logTailTerm_tsum_boundR16 q hq0 hq1)

lemma weightedLogTail_tail_boundR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (K : ℕ) :
    (∑' k : ℕ, weightedLogTailR16 q (k+K)) ≤
      q^(K+1)/(((K : ℝ)+1)*(1-q)^2) := by
  have hs : Summable (fun k : ℕ => weightedLogTailR16 q (k+K)) :=
    (summable_nat_add_iff K).2 (weightedLogTail_summableR16 q hq0 hq1)
  have hb : Summable (fun k : ℕ => logTailTermR16 q (k+K)) :=
    (summable_nat_add_iff K).2 (logTailTerm_summableR16 q hq0 hq1)
  have hden : 0 < (K : ℝ)+1 := by positivity
  have hp (k : ℕ) : weightedLogTailR16 q (k+K) ≤
      logTailTermR16 q (k+K)/((K : ℝ)+1) := by
    unfold weightedLogTailR16
    apply div_le_div_of_nonneg_left (logTailTerm_boundsR16 q hq0 hq1 (k+K)).1 hden
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  have ht := hs.tsum_le_tsum hp (hb.div_const ((K : ℝ)+1))
  rw [tsum_div_const] at ht
  have hu := div_le_div_of_nonneg_right (logTailTerm_tail_boundR16 q hq0 hq1 K) hden.le
  apply ht.trans
  convert hu using 1
  rw [div_div, mul_comm ((1 - q) ^ 2) ((K : ℝ) + 1)]

/-- Möbius inversion applied at the actual real evaluation, not a surrogate. -/
theorem cyclotomic_real_moebiusR16 (p : ℝ) (hp : 1 < p) (l : ℕ) (hl : 0 < l) :
    cyclotomicEvalR16 p l =
      ∏ x ∈ l.divisorsAntidiagonal, (p^x.2-1)^ArithmeticFunction.moebius x.1 := by
  symm
  apply (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero
    (f := cyclotomicEvalR16 p) (g := fun d => p^d-1)
    (fun d hd => real_cyclotomic_eval_nonzero p hp d hd)
    (fun d hd => real_power_denominator_nonzero p hp d hd)).mp
      (fun d hd => ?_) l hl
  have he := congrArg (Polynomial.eval₂ (Int.castRingHom ℝ) p)
    (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hd ℤ)
  simpa only [cyclotomicEvalR16, eval₂_finset_prod, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_one] using he

lemma power_sub_one_posR16 (p : ℝ) (hp : 1 < p) (d : ℕ) (hd : 0 < d) :
    0 < p^d-1 := by
  have ht : p ≤ p^d := by
    simpa only [pow_one] using pow_le_pow_right₀ hp.le (show 1 ≤ d by omega)
  linarith

lemma cyclotomic_real_posR16 (p : ℝ) (hp : 1 < p) (l : ℕ) (hl : 0 < l) :
    0 < cyclotomicEvalR16 p l := by
  rw [cyclotomic_real_moebiusR16 p hp l hl]
  apply prod_pos
  intro x hx
  have hd := (antidiagonal_nonzeroR16 hx).2
  exact zpow_pos (power_sub_one_posR16 p hp x.2 (by omega)) _

lemma log_power_sub_oneR16 (p : ℝ) (hp : 1 < p) (d : ℕ) (hd : 0 < d) :
    Real.log (p^d-1) = (d : ℝ)*Real.log p + Real.log (1-p⁻¹^d) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 : 0 < p⁻¹ := inv_pos.mpr hp0
  have hq1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).2 hp
  have hpow : p⁻¹^d ≤ p⁻¹ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [pow_succ]
    nlinarith [pow_le_one₀ hq0.le hq1.le (n := k)]
  have htail : 0 < 1-p⁻¹^d := by linarith
  have he : p^d-1 = p^d*(1-p⁻¹^d) := by
    rw [inv_pow]
    field_simp [pow_ne_zero d hp0.ne']
    <;> ring
  rw [he, Real.log_mul (pow_ne_zero _ hp0.ne') htail.ne', Real.log_pow]

/-- Exact logarithm formula, including l=1. -/
theorem cyclotomic_log_residual_identityR16 (p : ℝ) (hp : 1 < p)
    (l : ℕ) (hl : 0 < l) :
    Real.log (cyclotomicEvalR16 p l) - (l.totient : ℝ)*Real.log p =
      ∑ x ∈ l.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) *
        Real.log (1-p⁻¹^x.2) := by
  rw [cyclotomic_real_moebiusR16 p hp l hl,
    Real.log_prod (fun x hx => zpow_ne_zero _
      (real_power_denominator_nonzero p hp x.2
        (by have := (antidiagonal_nonzeroR16 hx).2; omega)))]
  simp_rw [Real.log_zpow]
  have he : (∑ x ∈ l.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ)*
      Real.log (p^x.2-1)) =
      (l.totient : ℝ)*Real.log p +
      ∑ x ∈ l.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ)*
        Real.log (1-p⁻¹^x.2) := by
    calc
      _ = ∑ x ∈ l.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius x.1 : ℝ)*(x.2 : ℝ)*Real.log p +
            (ArithmeticFunction.moebius x.1 : ℝ)*Real.log (1-p⁻¹^x.2)) := by
        apply sum_congr rfl
        intro x hx
        rw [log_power_sub_oneR16 p hp x.2
          (by have := (antidiagonal_nonzeroR16 hx).2; omega)]
        ring
      _ = _ := by
        rw [sum_add_distrib, ← Finset.sum_mul, ← totient_moebiusR16 l hl]
  rw [he]
  ring

lemma antidiagonal_logTail_sum_leR16 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (l : ℕ) :
    (∑ x ∈ l.divisorsAntidiagonal, logTailTermR16 q (x.2-1)) ≤
      logTailMajorantR16 q := by
  classical
  have hi : ∀ x ∈ l.divisorsAntidiagonal, ∀ y ∈ l.divisorsAntidiagonal,
      x.2-1=y.2-1 → x=y := by
    intro x hx y hy h
    have hx0 := (antidiagonal_nonzeroR16 hx).2
    have hy0 := (antidiagonal_nonzeroR16 hy).2
    have hd : x.2=y.2 := by omega
    have hxp := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hyp := (Nat.mem_divisorsAntidiagonal.mp hy).1
    have ha : x.1=y.1 := by
      rw [← hd] at hyp
      exact mul_right_cancel₀ hx0 (hxp.trans hyp.symm)
    exact Prod.ext ha hd
  have he : (∑ x ∈ l.divisorsAntidiagonal, logTailTermR16 q (x.2-1)) =
      ∑ k ∈ l.divisorsAntidiagonal.image (fun x => x.2-1), logTailTermR16 q k := by
    rw [Finset.sum_image]
    exact hi
  rw [he]
  exact ((logTailTerm_summableR16 q hq0 hq1).sum_le_tsum _
    (fun k _ => (logTailTerm_boundsR16 q hq0 hq1 k).1)).trans
      (logTailTerm_tsum_boundR16 q hq0 hq1)

/-- Uniform in l, for a fixed real p>1. -/
theorem cyclotomic_log_errorR16 (p : ℝ) (hp : 1 < p) (l : ℕ) (hl : 0 < l) :
    |Real.log (cyclotomicEvalR16 p l) - (l.totient : ℝ)*Real.log p| ≤
      logTailMajorantR16 p⁻¹ := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := inv_pos.mpr hp0
  have hq1 := (inv_lt_one₀ hp0).2 hp
  rw [cyclotomic_log_residual_identityR16 p hp l hl]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum (g := fun x => logTailTermR16 p⁻¹ (x.2-1)) ?_).trans
    (antidiagonal_logTail_sum_leR16 p⁻¹ hq0 hq1 l)
  intro x hx
  have hd : 1 ≤ x.2 := by
    have := (antidiagonal_nonzeroR16 hx).2
    omega
  have hb := logTailTerm_boundsR16 p⁻¹ hq0 hq1 (x.2-1)
  have he : |Real.log (1-p⁻¹^x.2)| = logTailTermR16 p⁻¹ (x.2-1) := by
    dsimp [logTailTermR16] at hb ⊢
    rw [Nat.sub_add_cancel hd] at hb ⊢
    rw [abs_of_nonpos (by linarith [hb.1])]
  rw [abs_mul, he]
  exact (mul_le_mul_of_nonneg_right (mu_abs_le_oneR16 x.1) hb.1).trans_eq (one_mul _)

lemma actual_complement_eval_productR16 (p : ℝ) (n : ℕ) :
    complementEvalR16 p n = ∏ l ∈ Icc 1 (15*n),
      if sourceWeight n l=0 then cyclotomicEvalR16 p l else 1 := by
  classical
  change (eval₂RingHom (Int.castRingHom ℝ) p) (sourceComplement n) = _
  simp only [sourceComplement, map_prod]
  apply prod_congr rfl
  intro l hl
  split_ifs <;> simp [cyclotomicEvalR16]

lemma actual_complement_posR16 (p : ℝ) (hp : 1 < p) (n : ℕ) :
    0 < complementEvalR16 p n := by
  rw [actual_complement_eval_productR16]
  apply prod_pos
  intro l hl
  split_ifs
  · exact cyclotomic_real_posR16 p hp l (by have := (mem_Icc.mp hl).1; omega)
  · norm_num

lemma actual_complement_log_productR16 (p : ℝ) (hp : 1 < p) (n : ℕ) :
    Real.log (complementEvalR16 p n) = ∑ l ∈ Icc 1 (15*n),
      if sourceWeight n l=0 then Real.log (cyclotomicEvalR16 p l) else 0 := by
  rw [actual_complement_eval_productR16,
    Real.log_prod (by
      intro l hl
      split_ifs
      · exact (cyclotomic_real_posR16 p hp l (by have := (mem_Icc.mp hl).1; omega)).ne'
      · norm_num)]
  apply sum_congr rfl
  intro l hl
  split_ifs <;> simp

/-- Literal complement estimate, for every n including 0, with explicit p-dependence. -/
theorem actual_complement_log_errorR16 (p : ℝ) (hp : 1 < p) (n : ℕ) :
    |Real.log (complementEvalR16 p n)-complementDegreeR16 n*Real.log p| ≤
      15*(n : ℝ)*logTailMajorantR16 p⁻¹ := by
  classical
  have hp0 := zero_lt_one.trans hp
  have hq0 : 0 < p⁻¹ := inv_pos.mpr hp0
  have hq1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).2 hp
  have hA : 0 ≤ logTailMajorantR16 p⁻¹ := by unfold logTailMajorantR16; positivity
  have hd : complementDegreeR16 n =
      ∑ l ∈ Icc 1 (15*n), if sourceWeight n l=0 then (l.totient : ℝ) else 0 := by
    unfold complementDegreeR16
    rw [(sourceComplement_monic_degree n).2]
    push_cast
    try rfl
  rw [actual_complement_log_productR16 p hp n, hd, Finset.sum_mul, ← sum_sub_distrib]
  calc
    _ ≤ ∑ l ∈ Icc 1 (15*n),
        |(if sourceWeight n l=0 then Real.log (cyclotomicEvalR16 p l) else 0) -
          (if sourceWeight n l=0 then (l.totient : ℝ) else 0)*Real.log p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l ∈ Icc 1 (15*n), logTailMajorantR16 p⁻¹ := by
      apply sum_le_sum
      intro l hl
      split_ifs
      · exact cyclotomic_log_errorR16 p hp l (by have := (mem_Icc.mp hl).1; omega)
      · simpa using hA
    _ = _ := by simp [Nat.card_Icc] <;> ring

/-- The missing fixed-base logarithmic rate for the unchanged source complement. -/
theorem actual_complement_quadLogRateR16 (p : ℝ) (hp : 1 < p) :
    PaperR9.QuadLogRate (complementEvalR16 p) (sourceGammaR16*Real.log p) := by
  have hA : 0 ≤ 15*logTailMajorantR16 p⁻¹ := by
    unfold logTailMajorantR16
    have hp0 := zero_lt_one.trans hp
    positivity
  have he : QuadRateR16 (fun n => Real.log (complementEvalR16 p n)-
      complementDegreeR16 n*Real.log p) 0 := by
    apply rate_of_eventual_linear_errorR16 _ 0 (15*logTailMajorantR16 p⁻¹) hA
    exact Eventually.of_forall (fun n => by
      have h := actual_complement_log_errorR16 p hp n
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      simp only [zero_mul, sub_zero]
      exact h.trans (by nlinarith))
  have hd := actual_complement_degree_rateR16.const_mul (Real.log p)
  have h := hd.add he
  simp only [add_zero] at h
  rw [mul_comm (Real.log p) sourceGammaR16] at h
  apply QuadRateR16.congr_eventually h
  exact Eventually.of_forall (fun n => by
    rw [abs_of_pos (actual_complement_posR16 p hp n)]
    ring)

end ErdosProblems.Erdos1049.PaperR16
