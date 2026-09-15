import ErdosProblems.Erdos1049.QProductBoundsR10
import ErdosProblems.Erdos1049.PaperAsymptoticsR9

/-!
# The actual positive 2004 source series in direction (14,12,14;27)

This module CONSTRUCTS the positive hypergeometric series,
proves its convergence, proves uniform two-sided bounds, and proves its exact
zero quadratic logarithmic rate. In particular none of those properties is
an added hypothesis.

The last denominator has length 13*n+1. Replacing it by 13*n would be the
historical off-by-one error identified in the supplied notes.

The identity with the cancelled integer polynomial linear form is not asserted
here: that algebraic/arithmetic source transport remains separately identified.
-/
namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped BigOperators Topology

lemma quotient_of_unit_interval_bounds {P A B : ℝ} (hP : 0 < P)
    (hA : P ≤ A ∧ A ≤ 1) (hB : P ≤ B ∧ B ≤ 1) :
    P ≤ A / B ∧ A / B ≤ P⁻¹ := by
  have hBpos : 0 < B := hP.trans_le hB.1
  constructor
  · apply (le_div_iff₀ hBpos).mpr
    calc
      P * B ≤ P * 1 := mul_le_mul_of_nonneg_left hB.2 hP.le
      _ = P := by ring
      _ ≤ A := hA.1
  · calc
      A / B ≤ 1 / B := div_le_div_of_nonneg_right hA.2 hBpos.le
      _ ≤ 1 / P := one_div_le_one_div_of_le hP hB.1
      _ = _ := one_div P

/-- The positive series printed in the current short paper, with every
Pochhammer length written as a natural number without truncated subtraction. -/
noncomputable def sourcePositiveHTerm (q : ℝ) (n t : ℕ) : ℝ :=
  q ^ ((14 * n + 1) * t) *
    (qPochhammerFinite (q ^ (t + 1)) q (12 * n) /
      qPochhammerFinite q q (12 * n)) *
    (qPochhammerFinite q q (13 * n) /
      qPochhammerFinite (q ^ (14 * n + 1 + t)) q (13 * n + 1))

noncomputable def sourcePositiveH (q : ℝ) (n : ℕ) : ℝ :=
  ∑' t : ℕ, sourcePositiveHTerm q n t

/-- A termwise bound valid even at n=0 and t=0. -/
theorem sourcePositiveHTerm_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n t : ℕ) :
    q ^ ((14 * n + 1) * t) * (qPochhammerInfinity q q) ^ 2 ≤
        sourcePositiveHTerm q n t ∧
    sourcePositiveHTerm q n t ≤
        (qPochhammerInfinity q q)⁻¹ ^ 2 * (q ^ (14 * n + 1)) ^ t := by
  let P := qPochhammerInfinity q q
  have hP : 0 < P := qPochhammerInfinity_pos q q
  have h1 := shifted_qPochhammer_bounds hq0 hq1 (t + 1) (12 * n) (by omega)
  have h2 := shifted_qPochhammer_bounds hq0 hq1 1 (12 * n) (by omega)
  have h3 := shifted_qPochhammer_bounds hq0 hq1 1 (13 * n) (by omega)
  have h4 := shifted_qPochhammer_bounds hq0 hq1 (14 * n + 1 + t) (13 * n + 1) (by omega)
  simp only [pow_one] at h2 h3
  have hr1 := quotient_of_unit_interval_bounds hP h1 h2
  have hr2 := quotient_of_unit_interval_bounds hP h3 h4
  have hpow : 0 ≤ q ^ ((14 * n + 1) * t) := pow_nonneg hq0.le _
  have hlo := mul_le_mul hr1.1 hr2.1 hP.le (hP.le.trans hr1.1)
  have hup := mul_le_mul hr1.2 hr2.2 (hP.le.trans hr2.1) (inv_nonneg.mpr hP.le)
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlo hpow
    simpa only [sourcePositiveHTerm, P, pow_two, mul_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_left hup hpow
    calc
      sourcePositiveHTerm q n t ≤
          q ^ ((14 * n + 1) * t) * (P⁻¹ * P⁻¹) := by
        simpa only [sourcePositiveHTerm, P, mul_assoc] using hh
      _ = P⁻¹ ^ 2 * (q ^ (14 * n + 1)) ^ t := by
        rw [pow_mul, pow_two]
        ring

theorem sourcePositiveHTerm_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n t : ℕ) : 0 ≤ sourcePositiveHTerm q n t :=
  (mul_nonneg (pow_nonneg hq0.le _) (sq_nonneg _)).trans
    (sourcePositiveHTerm_bounds hq0 hq1 n t).1

/-- Convergence is proved before any use of tsum comparison. -/
theorem summable_sourcePositiveHTerm {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℕ) : Summable (sourcePositiveHTerm q n) := by
  have hqn : q ^ (14 * n + 1) < 1 := by
    have h := qpow_antitone hq0.le hq1.le (by omega : 1 ≤ 14 * n + 1)
    have hqpow1 : q ^ 1 < 1 := by simpa only [pow_one] using hq1
    exact h.trans_lt hqpow1
  apply summable_nonneg_dominated (sourcePositiveHTerm_nonneg hq0 hq1 n)
    (fun t => (sourcePositiveHTerm_bounds hq0 hq1 n t).2)
  exact (summable_geometric_of_lt_one (pow_nonneg hq0.le _) hqn).mul_left _

/-- The exact n-dependent upper bound of the printed source argument. -/
theorem sourcePositiveH_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (qPochhammerInfinity q q) ^ 2 ≤ sourcePositiveH q n ∧
      sourcePositiveH q n ≤ (qPochhammerInfinity q q)⁻¹ ^ 2 /
        (1 - q ^ (14 * n + 1)) := by
  have hs := summable_sourcePositiveHTerm hq0 hq1 n
  have hqn : q ^ (14 * n + 1) < 1 := by
    have h := qpow_antitone hq0.le hq1.le (by omega : 1 ≤ 14 * n + 1)
    have hqpow1 : q ^ 1 < 1 := by simpa only [pow_one] using hq1
    exact h.trans_lt hqpow1
  constructor
  · have ht := (sourcePositiveHTerm_bounds hq0 hq1 n 0).1
    simp only [Nat.mul_zero, pow_zero, one_mul] at ht
    exact ht.trans (hs.le_tsum 0 (fun k _ => sourcePositiveHTerm_nonneg hq0 hq1 n k))
  · have hg := (hasSum_geometric_of_lt_one (pow_nonneg hq0.le _) hqn).mul_left
      ((qPochhammerInfinity q q)⁻¹ ^ 2)
    calc
      sourcePositiveH q n ≤ ∑' t : ℕ,
          (qPochhammerInfinity q q)⁻¹ ^ 2 * (q ^ (14 * n + 1)) ^ t :=
        Summable.tsum_le_tsum (fun t => (sourcePositiveHTerm_bounds hq0 hq1 n t).2)
          hs hg.summable
      _ = _ := by simpa only [div_eq_mul_inv] using hg.tsum_eq

/-- Uniform in n: the denominator in the upper bound can be replaced by 1-q. -/
theorem sourcePositiveH_uniform_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (qPochhammerInfinity q q) ^ 2 ≤ sourcePositiveH q n ∧
      sourcePositiveH q n ≤ (qPochhammerInfinity q q)⁻¹ ^ 2 / (1 - q) := by
  have hb := sourcePositiveH_bounds hq0 hq1 n
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hqn : q ^ (14 * n + 1) ≤ q := by
    simpa only [pow_one] using qpow_antitone hq0.le hq1.le (by omega : 1 ≤ 14 * n + 1)
  exact div_le_div_of_nonneg_left (sq_nonneg _) (sub_pos.mpr hq1) (by linarith)

theorem sourcePositiveH_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    0 < sourcePositiveH q n :=
  (sq_pos_of_pos (qPochhammerInfinity_pos q q)).trans_le
    (sourcePositiveH_bounds hq0 hq1 n).1

/-- Both logarithmic sides are uniform, so no exceptional zero indices remain. -/
theorem sourcePositiveH_log_bounded {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |Real.log (sourcePositiveH q n)| ≤ C := by
  let L := (qPochhammerInfinity q q) ^ 2
  let U := (qPochhammerInfinity q q)⁻¹ ^ 2 / (1 - q)
  have hL : 0 < L := sq_pos_of_pos (qPochhammerInfinity_pos q q)
  have hU : 0 < U := by
    dsimp [U]
    exact div_pos (sq_pos_of_pos (inv_pos.mpr (qPochhammerInfinity_pos q q)))
      (sub_pos.mpr hq1)
  refine ⟨|Real.log L| + |Real.log U|, by positivity, ?_⟩
  intro n
  have hb := sourcePositiveH_uniform_bounds hq0 hq1 n
  have hlo := Real.log_le_log hL hb.1
  have hup := Real.log_le_log (sourcePositiveH_pos hq0 hq1 n) hb.2
  apply abs_le.mpr
  constructor
  · have hh := neg_abs_le (Real.log L)
    have hh' := abs_nonneg (Real.log U)
    linarith
  · have hh := le_abs_self (Real.log U)
    have hh' := abs_nonneg (Real.log L)
    linarith

/-- A bounded logarithm has zero quadratic rate. The proof includes the limiting
step rather than encoding it as a source hypothesis. -/
theorem sourcePositiveH_quadLogRate_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    PaperR9.QuadLogRate (sourcePositiveH q) 0 := by
  obtain ⟨C, hC, hbound⟩ := sourcePositiveH_log_bounded hq0 hq1
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [PaperR9.eventually_linear_le_square C ε hC hε] with n hn
  have hCmul : C ≤ C * (2 * (n : ℝ) + 1) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have htotal := (hbound n).trans (hCmul.trans hn)
  simpa only [PaperR9.sqScale, zero_mul, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (n : ℝ)),
    abs_of_pos (sourcePositiveH_pos hq0 hq1 n)] using htotal

end ErdosProblems.Erdos1049.PaperR10
