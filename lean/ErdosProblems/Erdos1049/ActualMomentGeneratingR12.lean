import ErdosProblems.Erdos1049.QProductBoundsR10
import Mathlib

/-!
# The actual analytic moment generating identity

Proves summability, positivity, and the identity v_m^* = P^4 G_q(q^(m+1)).

Unlike a positive-measure consumer, this file starts with the literal finite
q-product summand in the 2016 normalised moment. It proves summability and
performs the finite/infinite product cancellation at w=q^(m+1). No moment
identity, atom identity, summability, or product nonvanishing is a premise.

The subsequent coefficient expansion of G, comparison of its coefficients,
and infinite Cauchy--Binet passage are separate obligations; this file does
not mislabel those consequences as established merely by the identity below.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open PaperR10
open scoped BigOperators

/-- Splitting an absolutely convergent logarithmic product at an arbitrary
finite index. The assumptions ensure this is the genuine infinite product. -/
theorem qPochhammerInfinity_split {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    qPochhammerInfinity a q =
      qPochhammerFinite a q n * qPochhammerInfinity (a * q ^ n) q := by
  have hs := summable_log_qPochhammer ha0 ha1 hq0 hq1
  unfold qPochhammerInfinity
  rw [← hs.sum_add_tsum_nat_add n, Real.exp_add,
    exp_sum_log_qPochhammer ha0 ha1 hq0 hq1.le]
  congr 1
  apply congrArg Real.exp
  apply tsum_congr
  intro k
  simp only [pow_add]
  congr 2 <;> ring

lemma positive_shift_power_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (s : ℕ) (hs : 1 ≤ s) : q ^ s < 1 := by
  have h : q ^ s ≤ q := by simpa using qpow_antitone hq0.le hq1.le hs
  exact h.trans_lt hq1

/-- A finite shifted product as an exact ratio of two nonzero products. -/
theorem qPochhammerFinite_shifted_ratio {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (s : ℕ) (hs : 1 ≤ s) (n : ℕ) :
    qPochhammerFinite (q ^ s) q n =
      qPochhammerInfinity (q ^ s) q / qPochhammerInfinity (q ^ (s + n)) q := by
  apply (eq_div_iff (qPochhammerInfinity_pos (q ^ (s + n)) q).ne').2
  simpa only [pow_add] using
    (qPochhammerInfinity_split (pow_nonneg hq0.le s)
      (positive_shift_power_lt_one hq0 hq1 s hs) hq0.le hq1 n).symm

/-- The literal t-th summand of the source's normalised moment v_m^*. -/
noncomputable def actualMomentTerm (q : ℝ) (m t : ℕ) : ℝ :=
  q ^ ((m + 1) * t) * (qPochhammerFinite q q m) ^ 3 *
    qPochhammerFinite (q ^ (t + 1)) q m /
      qPochhammerFinite (q ^ (m + t + 1)) q (m + 1)

noncomputable def actualMoment (q : ℝ) (m : ℕ) : ℝ :=
  ∑' t : ℕ, actualMomentTerm q m t

/-- Every source summand is strictly positive, even at m=0 or t=0. -/
theorem actualMomentTerm_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m t : ℕ) :
    0 < actualMomentTerm q m t := by
  unfold actualMomentTerm
  apply div_pos
  · apply mul_pos
    · exact mul_pos (pow_pos hq0 _) (pow_pos
        (qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le m) 3)
    · exact qPochhammerFinite_pos (pow_nonneg hq0.le _)
        (positive_shift_power_lt_one hq0 hq1 _ (by omega)) hq0.le hq1.le m
  · exact qPochhammerFinite_pos (pow_nonneg hq0.le _)
      (positive_shift_power_lt_one hq0 hq1 _ (by omega)) hq0.le hq1.le (m + 1)

/-- A single fixed positive product controls every denominator. -/
theorem actualMomentTerm_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m t : ℕ) :
    actualMomentTerm q m t ≤
      q ^ ((m + 1) * t) / qPochhammerInfinity q q := by
  have ha := qPochhammerFinite_nonneg_le_one hq0.le hq1.le hq0.le hq1.le m
  have hb := qPochhammerFinite_nonneg_le_one (pow_nonneg hq0.le (t + 1))
    (positive_shift_power_lt_one hq0 hq1 (t + 1) (by omega)).le hq0.le hq1.le m
  have hd := shifted_qPochhammer_bounds hq0 hq1 (m + t + 1) (m + 1) (by omega)
  have hP := qPochhammerInfinity_pos q q
  have hdpos : 0 < qPochhammerFinite (q ^ (m + t + 1)) q (m + 1) := hP.trans_le hd.1
  have ha3 : (qPochhammerFinite q q m) ^ 3 ≤ 1 := pow_le_one₀ ha.1 ha.2
  have hab : (qPochhammerFinite q q m) ^ 3 *
      qPochhammerFinite (q ^ (t + 1)) q m ≤ 1 := by
    calc
      _ ≤ 1 * qPochhammerFinite (q ^ (t + 1)) q m :=
        mul_le_mul_of_nonneg_right ha3 hb.1
      _ ≤ 1 := by simpa using hb.2
  unfold actualMomentTerm
  calc
    _ = q ^ ((m + 1) * t) * ((qPochhammerFinite q q m) ^ 3 *
          qPochhammerFinite (q ^ (t + 1)) q m) /
          qPochhammerFinite (q ^ (m + t + 1)) q (m + 1) := by ring
    _ ≤ q ^ ((m + 1) * t) / qPochhammerFinite (q ^ (m + t + 1)) q (m + 1) := by
      apply div_le_div_of_nonneg_right _ hdpos.le
      simpa using mul_le_mul_of_nonneg_left hab (pow_nonneg hq0.le _)
    _ ≤ q ^ ((m + 1) * t) / qPochhammerInfinity q q :=
      div_le_div_of_nonneg_left (pow_nonneg hq0.le _) hP hd.1

/-- Summability is proved before the totalised tsum is used as a moment. -/
theorem actualMomentTerm_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    Summable (actualMomentTerm q m) := by
  apply summable_nonneg_dominated (fun t => (actualMomentTerm_pos hq0 hq1 m t).le)
    (fun t => actualMomentTerm_le hq0 hq1 m t)
  have hg := (hasSum_geometric_of_lt_one (pow_nonneg hq0.le (m + 1))
    (positive_shift_power_lt_one hq0 hq1 (m + 1) (by omega))).summable
  simpa only [pow_mul] using hg.div_const (qPochhammerInfinity q q)

/-- Strict positivity of the literal analytic moment at every index. -/
theorem actualMoment_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    0 < actualMoment q m := by
  have hs := actualMomentTerm_summable hq0 hq1 m
  have hb := hs.sum_le_tsum ({0} : Finset ℕ)
    (fun t _ => (actualMomentTerm_pos hq0 hq1 m t).le)
  have h0 := actualMomentTerm_pos hq0 hq1 m 0
  exact h0.trans_le (by simpa [actualMoment] using hb)

/-- The term in the independent-variable generating function. -/
noncomputable def actualGeneratingTerm (q w : ℝ) (t : ℕ) : ℝ :=
  w ^ t / qPochhammerFinite q q t *
    qPochhammerInfinity (q ^ t * w ^ 2) q /
      (qPochhammerInfinity (q ^ t * w) q) ^ 2

noncomputable def actualGeneratingFunction (q w : ℝ) : ℝ :=
  (∑' t : ℕ, actualGeneratingTerm q w t) /
    (qPochhammerInfinity w q) ^ 3

/-- The four cancellations responsible for the source generating identity,
proved term by term rather than assumed under the name of a source bridge. -/
theorem actualMomentTerm_generating {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (m t : ℕ) :
    actualMomentTerm q m t =
      (qPochhammerInfinity q q) ^ 4 /
        (qPochhammerInfinity (q ^ (m + 1)) q) ^ 3 *
          actualGeneratingTerm q (q ^ (m + 1)) t := by
  have hm := qPochhammerFinite_shifted_ratio hq0 hq1 1 (by omega) m
  have ht := qPochhammerFinite_shifted_ratio hq0 hq1 1 (by omega) t
  have htm := qPochhammerFinite_shifted_ratio hq0 hq1 (t + 1) (by omega) m
  have hden := qPochhammerFinite_shifted_ratio hq0 hq1 (m + t + 1) (by omega) (m + 1)
  have hi1 : 1 + m = m + 1 := by omega
  have hi2 : 1 + t = t + 1 := by omega
  have hi3 : t + 1 + m = m + t + 1 := by omega
  have hi4 : m + t + 1 + (m + 1) = 2 * m + t + 2 := by omega
  simp only [pow_one, hi1] at hm
  simp only [pow_one, hi2] at ht
  rw [hi3] at htm
  rw [hi4] at hden
  have he1 : q ^ t * (q ^ (m + 1)) ^ 2 = q ^ (2 * m + t + 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1 <;> omega
  have he2 : q ^ t * q ^ (m + 1) = q ^ (m + t + 1) := by
    rw [← pow_add]
    congr 1 <;> omega
  unfold actualMomentTerm actualGeneratingTerm
  rw [hm, ht, htm, hden, he1, he2, ← pow_mul]
  field_simp [(qPochhammerInfinity_pos q q).ne',
    (qPochhammerInfinity_pos (q ^ (m + 1)) q).ne',
    (qPochhammerInfinity_pos (q ^ (t + 1)) q).ne',
    (qPochhammerInfinity_pos (q ^ (m + t + 1)) q).ne',
    (qPochhammerInfinity_pos (q ^ (2 * m + t + 2)) q).ne']
  <;> ring

/-- Convergence of the independent-variable sum at every source argument. -/
theorem actualGeneratingTerm_summable_at_source {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    Summable (actualGeneratingTerm q (q ^ (m + 1))) := by
  have hc : (qPochhammerInfinity q q) ^ 4 /
      (qPochhammerInfinity (q ^ (m + 1)) q) ^ 3 ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ (qPochhammerInfinity_pos q q).ne')
      (pow_ne_zero _ (qPochhammerInfinity_pos (q ^ (m + 1)) q).ne')
  have hs : Summable (fun t : ℕ =>
      (qPochhammerInfinity q q) ^ 4 /
        (qPochhammerInfinity (q ^ (m + 1)) q) ^ 3 *
          actualGeneratingTerm q (q ^ (m + 1)) t) := by
    have hfun : actualMomentTerm q m = fun t : ℕ =>
        (qPochhammerInfinity q q) ^ 4 /
          (qPochhammerInfinity (q ^ (m + 1)) q) ^ 3 *
            actualGeneratingTerm q (q ^ (m + 1)) t :=
      funext (actualMomentTerm_generating hq0 hq1 m)
    rw [← hfun]
    exact actualMomentTerm_summable hq0 hq1 m
  exact (summable_mul_left_iff hc).mp hs

/-- Actual analytic source identity v_m^*=P^4 G_q(q^(m+1)), for every m>=0.
This is not a hypothesis-bearing positive-measure wrapper. -/
theorem actual_moment_generating_identity {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    actualMoment q m = (qPochhammerInfinity q q) ^ 4 *
      actualGeneratingFunction q (q ^ (m + 1)) := by
  unfold actualMoment actualGeneratingFunction
  simp_rw [actualMomentTerm_generating hq0 hq1]
  rw [tsum_mul_left]
  ring

end ErdosProblems.Erdos1049.PaperR12
