import ErdosProblems.Erdos1049.ActualSourceRemainderR14
import ErdosProblems.Erdos1049.GaussianDegreeR12
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib

/-!
# Fixed-base growth of the actual alternating A polynomial

Proves two-sided fixed-base bounds and the quadratic log rate of A_n(p).

Gaussian reciprocity is proved from finite factorial identities. Every earlier
summand loses at least n powers against the last one. The resulting tail is
bounded by a constant times n*q^n, which tends to zero. Thus possible alternating
cancellation is controlled before logarithms or a quadratic rate are asserted.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset Filter Asymptotics
open PaperR10 PaperR11 PaperR12
open scoped BigOperators Topology

lemma triangularExponent_split (N k : ℕ) (hk : k ≤ N) :
    triangularExponent N = triangularExponent k + triangularExponent (N - k) + k * (N - k) := by
  have h0 := twice_choose_two_int N
  have h1 := twice_choose_two_int k
  have h2 := twice_choose_two_int (N - k)
  have he : ((N - k : ℕ) : ℤ) = (N : ℤ) - (k : ℤ) := Nat.cast_sub hk
  have hh : ((triangularExponent N : ℕ) : ℤ) =
      ((triangularExponent k + triangularExponent (N - k) + k * (N - k) : ℕ) : ℤ) := by
    simp only [triangularExponent, Nat.cast_add, Nat.cast_mul] at *
    rw [he] at h2 ⊢
    nlinarith
  exact_mod_cast hh

lemma gaussian_reciprocal_real (p : ℝ) (hp : 1 < p) (N k : ℕ) (hk : k ≤ N) :
    gaussBinom p N k = p ^ (k * (N - k)) * gaussBinom p⁻¹ N k := by
  have hp0 := (zero_lt_one.trans hp).ne'
  have hq0 : 0 < p⁻¹ := inv_pos.mpr (zero_lt_one.trans hp)
  have hq1 : p⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hp)).mpr hp
  have hpk := qPochhammer_large_base_nonzero hp k
  have hpn := qPochhammer_large_base_nonzero hp (N - k)
  have hqk := qPochhammer_q_nonzero hq0 hq1 k
  have hqn := qPochhammer_q_nonzero hq0 hq1 (N - k)
  have hgp : gaussBinom p N k = qPochhammer p p N /
      (qPochhammer p p k * qPochhammer p p (N - k)) := by
    apply (eq_div_iff (mul_ne_zero hpk hpn)).mpr
    simpa only [mul_assoc] using gaussBinom_mul_qPochhammer_qPochhammer p N k hk
  have hgq : gaussBinom p⁻¹ N k = qPochhammer p⁻¹ p⁻¹ N /
      (qPochhammer p⁻¹ p⁻¹ k * qPochhammer p⁻¹ p⁻¹ (N - k)) := by
    apply (eq_div_iff (mul_ne_zero hqk hqn)).mpr
    simpa only [mul_assoc] using gaussBinom_mul_qPochhammer_qPochhammer p⁻¹ N k hk
  rw [hgp, hgq, qPochhammer_reciprocal_div p hp0 N,
    qPochhammer_reciprocal_div p hp0 k,
    qPochhammer_reciprocal_div p hp0 (N - k)]
  have hs : (-1 : ℝ) ^ N = (-1 : ℝ) ^ k * (-1 : ℝ) ^ (N - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hs, triangularExponent_split N k hk, pow_add, pow_add]
  field_simp [hp0, hpk, hpn]
  <;> ring

lemma gaussian_small_base_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (N k : ℕ) (hk : k ≤ N) :
    qPochhammerInfinity q q ≤ gaussBinom q N k ∧
      gaussBinom q N k ≤ (qPochhammerInfinity q q)⁻¹ := by
  have hden := qPochhammer_q_nonzero hq0 hq1 k
  have he : gaussBinom q N k =
      qPochhammer q (q ^ (N - k + 1)) k / qPochhammer q q k := by
    exact (eq_div_iff hden).mpr (gaussBinom_mul_qPochhammer q hk)
  rw [he, ← qPochhammerFinite_eq, ← qPochhammerFinite_eq]
  have ha := shifted_qPochhammer_bounds hq0 hq1 (N - k + 1) k (by omega)
  have hb := shifted_qPochhammer_bounds hq0 hq1 1 k (by omega)
  simp only [pow_one] at hb
  exact quotient_of_unit_interval_bounds (qPochhammerInfinity_pos q q) ha hb

lemma actual_AS_abs_reciprocal (p : ℝ) (hp : 1 < p) (n s : ℕ) (hs : s ≤ 13 * n) :
    |(sourceASummand n s).eval₂ (Int.castRingHom ℝ) p| =
      p ^ sourceASummandDegree n s *
        (gaussBinom p⁻¹ (14 * n + s) (12 * n) *
          gaussBinom p⁻¹ (13 * n) (13 * n - s)) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := inv_pos.mpr hp0
  have hq1 := (inv_lt_one₀ hp0).mpr hp
  have hG1 : 0 < gaussBinom p⁻¹ (14 * n + s) (12 * n) :=
    (qPochhammerInfinity_pos _ _).trans_le
      (gaussian_small_base_bounds hq0 hq1 _ _ (by omega)).1
  have hG2 : 0 < gaussBinom p⁻¹ (13 * n) (13 * n - s) :=
    (qPochhammerInfinity_pos _ _).trans_le
      (gaussian_small_base_bounds hq0 hq1 _ _ (Nat.sub_le _ _)).1
  have hraw : (sourceASummand n s).eval₂ (Int.castRingHom ℝ) p =
      (-1 : ℝ) ^ s * p ^ sourceASummandDegree n s *
        (gaussBinom p⁻¹ (14 * n + s) (12 * n) *
          gaussBinom p⁻¹ (13 * n) (13 * n - s)) := by
    simp only [sourceASummand, sourceGaussianProduct, eval₂_mul, eval₂_C, eval₂_pow,
      eval₂_X, eval₂_neg, eval₂_one, map_pow, map_neg, map_one, eval₂_gaussBinom]
    rw [gaussian_reciprocal_real p hp _ _ (by omega),
      gaussian_reciprocal_real p hp _ _ (Nat.sub_le _ _)]
    have he1 : 14 * n + s - 12 * n = 2 * n + s := by omega
    have he2 : 13 * n - (13 * n - s) = s := by omega
    simp only [sourceASummandDegree, he1, he2, pow_add]
    ring
  rw [hraw, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (pow_pos hp0 _), abs_of_pos (mul_pos hG1 hG2)]

lemma actual_AS_fixed_base_bounds (p : ℝ) (hp : 1 < p) (n s : ℕ) (hs : s ≤ 13 * n) :
    p ^ sourceASummandDegree n s * (qPochhammerInfinity p⁻¹ p⁻¹) ^ 2 ≤
      |(sourceASummand n s).eval₂ (Int.castRingHom ℝ) p| ∧
    |(sourceASummand n s).eval₂ (Int.castRingHom ℝ) p| ≤
      p ^ sourceASummandDegree n s * ((qPochhammerInfinity p⁻¹ p⁻¹)⁻¹) ^ 2 := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := inv_pos.mpr hp0
  have hq1 := (inv_lt_one₀ hp0).mpr hp
  have hP := qPochhammerInfinity_pos p⁻¹ p⁻¹
  have hg1 := gaussian_small_base_bounds hq0 hq1 (14 * n + s) (12 * n) (by omega)
  have hg2 := gaussian_small_base_bounds hq0 hq1 (13 * n) (13 * n - s) (Nat.sub_le _ _)
  rw [actual_AS_abs_reciprocal p hp n s hs]
  constructor
  · exact mul_le_mul_of_nonneg_left
      (by simpa only [pow_two] using mul_le_mul hg1.1 hg2.1 hP.le (hP.le.trans hg1.1))
      (pow_nonneg hp0.le _)
  · exact mul_le_mul_of_nonneg_left
      (by simpa only [pow_two] using mul_le_mul hg1.2 hg2.2 (hP.le.trans hg2.1) (inv_nonneg.mpr hP.le))
      (pow_nonneg hp0.le _)

lemma actual_A_degree_gap (n s : ℕ) (hs : s < 13 * n) :
    sourceASummandDegree n s + n ≤ sourceK n := by
  have hstep := sourceASummandDegree_succ n s hs
  have htop : sourceASummandDegree n (s + 1) ≤ sourceASummandDegree n (13 * n) := by
    rcases lt_or_eq_of_le (show s + 1 ≤ 13 * n by omega) with h | h
    · exact (sourceASummandDegree_strict n h le_rfl).le
    · rw [h]
  rw [sourceASummandDegree_last] at htop
  omega

noncomputable def actualAEarlierSum (p : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ range (13 * n), (sourceASummand n s).eval₂ (Int.castRingHom ℝ) p

noncomputable def actualATailBound (q : ℝ) (n : ℕ) : ℝ :=
  13 * (n : ℝ) * ((qPochhammerInfinity q q)⁻¹) ^ 2 * q ^ n

lemma actual_A_earlier_bound (p : ℝ) (hp : 1 < p) (n : ℕ) :
    |actualAEarlierSum p n| ≤ p ^ sourceK n * actualATailBound p⁻¹ n := by
  have hp0 := zero_lt_one.trans hp
  unfold actualAEarlierSum
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ s ∈ range (13 * n),
        p ^ sourceK n * ((qPochhammerInfinity p⁻¹ p⁻¹)⁻¹) ^ 2 * (p⁻¹) ^ n := by
      apply sum_le_sum
      intro s hs
      have hs' := mem_range.mp hs
      have hterm := (actual_AS_fixed_base_bounds p hp n s hs'.le).2
      have hpow := pow_le_pow_right₀ hp.le (actual_A_degree_gap n s hs')
      have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg (inv_nonneg.mpr hp0.le) n)
      rw [pow_add] at hmul
      have he : (p ^ sourceASummandDegree n s * p ^ n) * (p⁻¹) ^ n =
          p ^ sourceASummandDegree n s := by simp [inv_pow, hp0.ne', mul_assoc]
      rw [he] at hmul
      exact hterm.trans (by
        have h := mul_le_mul_of_nonneg_right hmul (sq_nonneg ((qPochhammerInfinity p⁻¹ p⁻¹)⁻¹))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
    _ = _ := by simp [actualATailBound]; ring

lemma actual_A_last_split (p : ℝ) (n : ℕ) :
    (sourceA n).eval₂ (Int.castRingHom ℝ) p = actualAEarlierSum p n +
      (sourceASummand n (13 * n)).eval₂ (Int.castRingHom ℝ) p := by
  simp only [sourceA, eval₂_finset_sum, eval₂_add, sum_range_succ, actualAEarlierSum]

lemma actualATailBound_tendsto_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (actualATailBound q) atTop (𝓝 0) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.tendsto_atTop_zero
  have hm := h.const_mul (13 * ((qPochhammerInfinity q q)⁻¹) ^ 2)
  rw [mul_zero] at hm
  refine hm.congr (fun n => ?_)
  dsimp only [actualATailBound]
  ring

/-- Uniform eventual two-sided bounds, after controlling the alternating tail. -/
theorem actual_A_eventual_two_sided (p : ℝ) (hp : 1 < p) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ᶠ n : ℕ in atTop,
      L * p ^ sourceK n ≤ |(sourceA n).eval₂ (Int.castRingHom ℝ) p| ∧
      |(sourceA n).eval₂ (Int.castRingHom ℝ) p| ≤ U * p ^ sourceK n := by
  let P := qPochhammerInfinity p⁻¹ p⁻¹
  have hP : 0 < P := qPochhammerInfinity_pos _ _
  have hp0 := zero_lt_one.trans hp
  have hq0 := inv_pos.mpr hp0
  have hq1 := (inv_lt_one₀ hp0).mpr hp
  refine ⟨P ^ 2 / 2, (P⁻¹) ^ 2 + P ^ 2 / 2, by positivity, by positivity, ?_⟩
  have hsmall : ∀ᶠ n in atTop, actualATailBound p⁻¹ n < P ^ 2 / 2 :=
    (actualATailBound_tendsto_zero hq0 hq1).eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hsmall] with n hn
  have htop := actual_AS_fixed_base_bounds p hp n (13 * n) le_rfl
  rw [sourceASummandDegree_last] at htop
  have htail := actual_A_earlier_bound p hp n
  have hpow : 0 ≤ p ^ sourceK n := (pow_pos hp0 _).le
  have htail' : |actualAEarlierSum p n| ≤ p ^ sourceK n * (P ^ 2 / 2) :=
    htail.trans (mul_le_mul_of_nonneg_left hn.le hpow)
  have habs := abs_add_le (actualAEarlierSum p n)
    ((sourceASummand n (13 * n)).eval₂ (Int.castRingHom ℝ) p)
  rw [← actual_A_last_split] at habs
  have hrev := abs_sub ((sourceA n).eval₂ (Int.castRingHom ℝ) p) (actualAEarlierSum p n)
  have hdiff : (sourceA n).eval₂ (Int.castRingHom ℝ) p - actualAEarlierSum p n =
      (sourceASummand n (13 * n)).eval₂ (Int.castRingHom ℝ) p := by rw [actual_A_last_split]; ring
  rw [hdiff] at hrev
  change p ^ sourceK n * P ^ 2 ≤
      |(sourceASummand n (13 * n)).eval₂ (Int.castRingHom ℝ) p| ∧
    |(sourceASummand n (13 * n)).eval₂ (Int.castRingHom ℝ) p| ≤
      p ^ sourceK n * (P⁻¹) ^ 2 at htop
  constructor <;> nlinarith

lemma sourceK_quadratic_residual (n : ℕ) :
    |(sourceK n : ℝ) - (1091 / 2 : ℝ) * (n : ℝ) ^ 2| ≤ 42 * (2 * (n : ℝ) + 1) := by
  let A := 1091 * n ^ 2 + 81 * n + 2
  have hm := Nat.mod_lt A (by norm_num : 0 < 2)
  have he := Nat.mod_add_div A 2
  have hlow : 2 * sourceK n ≤ A := by dsimp [sourceK, A]; omega
  have hupp : A < 2 * sourceK n + 2 := by dsimp [sourceK, A] at *; omega
  have hlow' : (2 : ℝ) * sourceK n ≤ 1091 * (n : ℝ) ^ 2 + 81 * n + 2 := by exact_mod_cast hlow
  have hupp' : 1091 * (n : ℝ) ^ 2 + 81 * n + 2 < (2 : ℝ) * sourceK n + 2 := by exact_mod_cast hupp
  rw [abs_le]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- The actual A evaluation has the claimed quadratic rate, not merely its
polynomial degree. Nonvanishing is established before logarithmic transport. -/
theorem actual_A_quadLogRate (p : ℝ) (hp : 1 < p) :
    PaperR9.QuadLogRate (fun n => (sourceA n).eval₂ (Int.castRingHom ℝ) p)
      ((1091 / 2 : ℝ) * Real.log p) := by
  obtain ⟨L, U, hL, hU, hb⟩ := actual_A_eventual_two_sided p hp
  let C := |Real.log L| + |Real.log U|
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hp0 := zero_lt_one.trans hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp.le
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hb,
    PaperR9.eventually_linear_le_square (C + 42 * Real.log p) ε
      (by positivity) hε] with n hn hεn
  have hA : 0 < |(sourceA n).eval₂ (Int.castRingHom ℝ) p| :=
    (mul_pos hL (pow_pos hp0 _)).trans_le hn.1
  have hlo := Real.log_le_log (mul_pos hL (pow_pos hp0 _)) hn.1
  have hup := Real.log_le_log hA hn.2
  rw [Real.log_mul hL.ne' (pow_ne_zero _ hp0.ne'), Real.log_pow] at hlo
  rw [Real.log_mul hU.ne' (pow_ne_zero _ hp0.ne'), Real.log_pow] at hup
  have hres : |Real.log |(sourceA n).eval₂ (Int.castRingHom ℝ) p| -
      (sourceK n : ℝ) * Real.log p| ≤ C := by
    rw [abs_le]
    dsimp [C]
    constructor <;> linarith [le_abs_self (Real.log U), neg_le_abs (Real.log L),
      abs_nonneg (Real.log L), abs_nonneg (Real.log U)]
  have hk := mul_le_mul_of_nonneg_right (sourceK_quadratic_residual n) hlog
  have hsplit :
      Real.log |(sourceA n).eval₂ (Int.castRingHom ℝ) p| -
          ((1091 / 2 : ℝ) * Real.log p) * PaperR9.sqScale n =
      (Real.log |(sourceA n).eval₂ (Int.castRingHom ℝ) p| -
          (sourceK n : ℝ) * Real.log p) +
        ((sourceK n : ℝ) - (1091 / 2 : ℝ) * (n : ℝ) ^ 2) * Real.log p := by
    simp only [PaperR9.sqScale]
    ring
  simp only [Real.norm_eq_abs, abs_of_nonneg (PaperR9.sqScale_nonneg n)]
  rw [hsplit]
  apply (abs_add_le _ _).trans
  have hk' : |((sourceK n : ℝ) - (1091 / 2 : ℝ) * (n : ℝ) ^ 2) * Real.log p| ≤
      42 * (2 * (n : ℝ) + 1) * Real.log p := by
    simpa only [abs_mul, abs_of_nonneg hlog] using hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have htotal : C + 42 * (2 * (n : ℝ) + 1) * Real.log p ≤
      (C + 42 * Real.log p) * (2 * (n : ℝ) + 1) := by nlinarith
  exact (add_le_add hres hk').trans (htotal.trans hεn)

end ErdosProblems.Erdos1049.PaperR14
