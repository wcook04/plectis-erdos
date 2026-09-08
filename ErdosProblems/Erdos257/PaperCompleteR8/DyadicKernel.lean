import ErdosProblems.Erdos257.PaperCompleteR8.OrbitBound
import ErdosProblems.Erdos257.DyadicShellSynchronisation

/-!
# The finite estimate (S)

All three regimes refer to the actual modular atom, not abstract error terms.
The complete-orbit argument is in OrbitBound. The dyadic reciprocal-tail bound
is reused from the compiled WeightedSupportAveraging module. This file proves
no-wrap and transition bounds and then assembles the uniform finite estimate.
NOT COMPILED in this return.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems.Erdos257.DyadicShellSynchronisation

/-- An elementary substitute for convexity in the transition case. -/
theorem normalised_geom_prefix_le {B : ℝ} (hB : 1 ≤ B)
    (n d : ℕ) (hnd : n ≤ d) :
    (d : ℝ) * (∑ i ∈ Finset.range n, B ^ i) ≤
      (n : ℝ) * (∑ i ∈ Finset.range d, B ^ i) := by
  have hBn : 0 ≤ B ^ n := pow_nonneg (le_trans zero_le_one hB) n
  have hhead : (∑ i ∈ Finset.range n, B ^ i) ≤ (n : ℝ) * B ^ n := by
    calc
      _ ≤ ∑ _i ∈ Finset.range n, B ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_right₀ hB (Finset.mem_range.mp hi).le
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htail : ((d - n : ℕ) : ℝ) * B ^ n ≤
      ∑ i ∈ Finset.range (d - n), B ^ (n + i) := by
    calc
      _ = ∑ _i ∈ Finset.range (d - n), B ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _hi
        exact pow_le_pow_right₀ hB (Nat.le_add_right n i)
  have hsplit : (∑ i ∈ Finset.range d, B ^ i) =
      (∑ i ∈ Finset.range n, B ^ i) +
        ∑ i ∈ Finset.range (d - n), B ^ (n + i) := by
    -- Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean: sum_range_add.
    have hndeq : n + (d - n) = d := by omega
    simpa only [hndeq] using
      (Finset.sum_range_add (fun i => B ^ i) n (d - n))
  have hsub : ((d - n : ℕ) : ℝ) = (d : ℝ) - (n : ℝ) := Nat.cast_sub hnd
  have hhead' := mul_le_mul_of_nonneg_left hhead (Nat.cast_nonneg (d - n))
  have htail' := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg n)
  rw [hsub] at hhead' htail'
  rw [hsplit]
  nlinarith only [hhead', htail']

/-- (B^n-1)/(B^d-1) ≤ n/d for 0 ≤ n ≤ d. -/
theorem pow_sub_one_ratio_le {B : ℝ} (hB : 1 < B)
    (n d : ℕ) (hd : 0 < d) (hnd : n ≤ d) :
    (B ^ n - 1) / (B ^ d - 1) ≤ (n : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hgap : 0 < B - 1 := sub_pos.mpr hB
  have hden : 0 < B ^ d - 1 := kernel_den_pos hB hd
  have h := normalised_geom_prefix_le hB.le n d hnd
  -- Mathlib/Algebra/Field/GeomSum.lean: geom_sum_eq, opened at the pin.
  rw [geom_sum_eq hB.ne', geom_sum_eq hB.ne'] at h
  have hmul := mul_le_mul_of_nonneg_right h hgap.le
  have hscaled : (d : ℝ) * (B ^ n - 1) ≤ (n : ℝ) * (B ^ d - 1) := by
    convert hmul using 1 <;> field_simp [hgap.ne']
  exact (div_le_div_iff₀ hden hdR).2 (by nlinarith only [hscaled])

/-- Pointwise far no-wrap bound. -/
theorem kernelWeight_le_of_twice_lt {B : ℝ} (hB : 1 < B)
    (d N : ℕ) (hfar : 2 * N < d) :
    kernelWeight B d N ≤ 1 / ((d : ℝ) * (B - 1)) := by
  have hd : 0 < d := by omega
  have hNd : N < d := by omega
  have hB0 : 0 ≤ B := le_trans zero_le_one hB.le
  have hsq : (B ^ N) ^ 2 ≤ B ^ (d - 1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hB.le (by omega)
  -- Mathlib/Data/Real/Sqrt.lean: sqrt_le_sqrt and sqrt_sq.
  have hsqrt : B ^ N ≤ Real.sqrt (B ^ (d - 1)) := by
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (pow_nonneg hB0 N)] at h
    exact h
  have hgeom : (d : ℝ) * B ^ N ≤ ∑ i ∈ Finset.range d, B ^ i :=
    (mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg d)).trans
      (card_mul_sqrt_le_geom_sum hB0 d)
  rw [geom_sum_eq hB.ne'] at hgeom
  have hgap : 0 < B - 1 := sub_pos.mpr hB
  have hden : 0 < B ^ d - 1 := kernel_den_pos hB hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hprod : B ^ N * ((d : ℝ) * (B - 1)) ≤ B ^ d - 1 := by
    have h := (le_div_iff₀ hgap).mp hgeom
    nlinarith only [h]
  unfold kernelWeight
  rw [Nat.mod_eq_of_lt hNd]
  apply (div_le_div_iff₀ hden (mul_pos hdR hgap)).2
  simpa only [one_mul] using hprod

/-- The whole no-wrap regime of one progression average. -/
theorem progressionMean_kernel_le_of_far {B : ℝ} (hB : 1 < B)
    (L d T : ℕ) (hT : 0 < T) (hfar : 2 * (L * T) < d) :
    progressionMean L T (kernelWeight B d) ≤ 1 / ((d : ℝ) * (B - 1)) := by
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hterm : ∀ m ∈ Finset.range T,
      kernelWeight B d ((m + 1) * L) ≤ 1 / ((d : ℝ) * (B - 1)) := by
    intro m hm
    have hmT : m + 1 ≤ T := by have := Finset.mem_range.mp hm; omega
    have hmul : (m + 1) * L ≤ L * T := by
      simpa only [mul_comm] using Nat.mul_le_mul_right L hmT
    apply kernelWeight_le_of_twice_lt hB
    omega
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  unfold progressionMean
  apply (div_le_iff₀ hTreal).2
  simpa only [mul_comm] using hsum

/-- Exact no-wrap geometric sum, before the transition estimate. -/
theorem progressionMean_kernel_no_wrap_eq {B : ℝ} (hB : 1 < B)
    (L d T : ℕ) (hL : 0 < L) (hT : 0 < T) (hwrap : L * T < d) :
    progressionMean L T (kernelWeight B d) =
      (B ^ L / ((T : ℝ) * (B ^ L - 1))) *
        ((B ^ (L * T) - 1) / (B ^ d - 1)) := by
  have hd : 0 < d := by omega
  have hden := (kernel_den_pos hB hd).ne'
  have hCne : B ^ L ≠ 1 := (one_lt_pow₀ hB hL.ne').ne'
  have hCG : B ^ L - 1 ≠ 0 := sub_ne_zero.mpr hCne
  have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hterms : ∀ m ∈ Finset.range T,
      kernelWeight B d ((m + 1) * L) =
        B ^ L * (B ^ L) ^ m / (B ^ d - 1) := by
    intro m hm
    have hmT : m + 1 ≤ T := by have := Finset.mem_range.mp hm; omega
    have hlt : (m + 1) * L < d :=
      lt_of_le_of_lt (by simpa only [mul_comm] using Nat.mul_le_mul_right L hmT) hwrap
    unfold kernelWeight
    rw [Nat.mod_eq_of_lt hlt]
    rw [Nat.add_mul, one_mul, pow_add, mul_comm m L, pow_mul]
    ring
  unfold progressionMean
  rw [Finset.sum_congr rfl hterms, ← Finset.sum_div, ← Finset.mul_sum,
    geom_sum_eq hCne]
  rw [← pow_mul]
  field_simp [hden, hCG, hTr]
  <;> ring

/-- Bound for the (at most one) transitional dyadic length. -/
theorem progressionMean_kernel_le_transition {B : ℝ}
    (hB : 1 < B) (hB2 : B ≤ 2)
    (L d T : ℕ) (hL : 0 < L) (hT : 0 < T) (hwrap : L * T < d) :
    progressionMean L T (kernelWeight B d) ≤
      2 * (L : ℝ) / ((d : ℝ) * (B - 1)) := by
  have hd : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hgap : 0 < B - 1 := sub_pos.mpr hB
  have hden : 0 < B ^ L - 1 := kernel_den_pos hB hL
  have hpow : B ≤ B ^ L := by
    calc B = B ^ (1 : ℕ) := (pow_one B).symm
      _ ≤ B ^ L := pow_le_pow_right₀ hB.le hL
  have hratio : B ^ L / (B ^ L - 1) ≤ B / (B - 1) := by
    apply (div_le_div_iff₀ hden hgap).2
    nlinarith only [hpow]
  have hn : (B ^ (L * T) - 1) / (B ^ d - 1) ≤ ((L * T : ℕ) : ℝ) / d :=
    pow_sub_one_ratio_le hB (L * T) d hd hwrap.le
  rw [progressionMean_kernel_no_wrap_eq hB L d T hL hT hwrap]
  have hpref : 0 ≤ B ^ L / ((T : ℝ) * (B ^ L - 1)) := by positivity
  calc
    _ ≤ (B ^ L / ((T : ℝ) * (B ^ L - 1))) * (((L * T : ℕ) : ℝ) / d) :=
      mul_le_mul_of_nonneg_left hn hpref
    _ = ((L : ℝ) / d) * (B ^ L / (B ^ L - 1)) := by
      push_cast
      field_simp [hden.ne', hTR.ne', hdR.ne']
      <;> ring
    _ ≤ ((L : ℝ) / d) * (B / (B - 1)) :=
      mul_le_mul_of_nonneg_left hratio (div_nonneg hLR.le hdR.le)
    _ ≤ ((L : ℝ) / d) * (2 / (B - 1)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hB2 hgap.le) (div_nonneg hLR.le hdR.le)
    _ = _ := by field_simp <;> ring

/-- There cannot be two transitional dyadic lengths. -/
theorem dyadic_transition_unique (L d : ℕ) {i j : ℕ}
    (hi : L * 2 ^ i < d ∧ d ≤ 2 * (L * 2 ^ i))
    (hj : L * 2 ^ j < d ∧ d ≤ 2 * (L * 2 ^ j)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hpow : 2 * 2 ^ i ≤ (2 : ℕ) ^ j := by
      have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
        (show i + 1 ≤ j by omega)
      simpa only [pow_succ, mul_comm] using h
    have hmul := Nat.mul_le_mul_left L hpow
    nlinarith only [hi.2, hj.1, hmul]
  · have hpow : 2 * 2 ^ j ≤ (2 : ℕ) ^ i := by
      have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
        (show j + 1 ≤ i by omega)
      simpa only [pow_succ, mul_comm] using h
    have hmul := Nat.mul_le_mul_left L hpow
    nlinarith only [hj.2, hi.1, hmul]

/-- The actual finite estimate (S). The proof needs M>0, not M≥4L;
the latter is only needed when replacing the displayed factor by 2. -/
theorem dyadicMean_kernelWeight_le (B : ℝ) (hB : 1 < B) (hB2 : B ≤ 2)
    (L d R M : ℕ) (hL : 0 < L) (hd : 0 < d) (hM : 0 < M) :
    dyadicMean L R M (kernelWeight B d) ≤
      (1 + 4 * (L : ℝ) / M) / ((d : ℝ) * (B - 1)) := by
  classical
  let J := Finset.Ico R (R + M)
  let a : ℝ := 1 / ((d : ℝ) * (B - 1))
  let near : ℕ → ℝ := fun j =>
    if d ≤ L * 2 ^ j then (1 / 2 : ℝ) ^ j / (B - 1) else 0
  let trans : ℕ → ℝ := fun j =>
    if L * 2 ^ j < d ∧ d ≤ 2 * (L * 2 ^ j) then 2 * (L : ℝ) * a else 0
  have hgap : 0 < B - 1 := sub_pos.mpr hB
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hcard : J.card = M := by dsimp [J]; rw [Nat.card_Ico]; omega
  have hpoint : ∀ j ∈ J,
      progressionMean L (2 ^ j) (kernelWeight B d) ≤ a + near j + trans j := by
    intro j _hj
    have hT : 0 < (2 : ℕ) ^ j := by positivity
    by_cases hn : d ≤ L * 2 ^ j
    · have hnot : ¬(L * 2 ^ j < d ∧ d ≤ 2 * (L * 2 ^ j)) := by omega
      have h := progressionMean_kernel_le_mean_add_error B hB L d (2 ^ j) hL hd hT
      have hid : 1 / (((2 ^ j : ℕ) : ℝ) * (B - 1)) =
          (1 / 2 : ℝ) ^ j / (B - 1) := by
        push_cast
        rw [div_pow, one_pow]
        field_simp
        <;> ring
      rw [hid] at h
      simpa only [a, near, trans, if_pos hn, if_neg hnot, add_zero] using h
    · have hlt : L * 2 ^ j < d := Nat.lt_of_not_ge hn
      by_cases ht : d ≤ 2 * (L * 2 ^ j)
      · have h := progressionMean_kernel_le_transition hB hB2 L d (2 ^ j) hL hT hlt
        have heq : 2 * (L : ℝ) / ((d : ℝ) * (B - 1)) = 2 * (L : ℝ) * a := by
          dsimp [a]; ring
        rw [heq] at h
        have htt : L * 2 ^ j < d ∧ d ≤ 2 * (L * 2 ^ j) := ⟨hlt, ht⟩
        simp only [near, trans, if_neg hn, if_pos htt, add_zero]
        exact h.trans (le_add_of_nonneg_left ha)
      · have hfar : 2 * (L * 2 ^ j) < d := Nat.lt_of_not_ge ht
        have h := progressionMean_kernel_le_of_far hB L d (2 ^ j) hT hfar
        have hnot : ¬(L * 2 ^ j < d ∧ d ≤ 2 * (L * 2 ^ j)) := fun h => ht h.2
        simpa only [a, near, trans, if_neg hn, if_neg hnot, add_zero] using h
  have hnear : (∑ j ∈ J, near j) ≤ 2 * (L : ℝ) * a := by
    have h := sum_dyadic_observation_weights_le J L d hd
    have hdiv := div_le_div_of_nonneg_right h hgap.le
    have heq : (∑ j ∈ J, near j) =
        (∑ j ∈ J.filter (fun j => d ≤ L * 2 ^ j), (1 / 2 : ℝ) ^ j) / (B - 1) := by
      rw [Finset.sum_div, Finset.sum_filter]
    rw [heq]
    convert hdiv using 1 <;> dsimp [a] <;> field_simp <;> ring
  have htrans : (∑ j ∈ J, trans j) ≤ 2 * (L : ℝ) * a := by
    let K := J.filter (fun j => L * 2 ^ j < d ∧ d ≤ 2 * (L * 2 ^ j))
    have hKcard : K.card ≤ 1 := by
      -- Mathlib/Data/Finset/Card.lean: card_le_one.
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact dyadic_transition_unique L d (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2
    have hKreal : (K.card : ℝ) ≤ 1 := by exact_mod_cast hKcard
    have hsum : (∑ j ∈ J, trans j) = (K.card : ℝ) * (2 * (L : ℝ) * a) := by
      calc
        _ = ∑ _j ∈ K, 2 * (L : ℝ) * a := by
          dsimp [K]
          simp only [Finset.sum_filter, trans]
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have h := mul_le_mul_of_nonneg_right hKreal
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg L)) ha)
    simpa only [one_mul] using h
  have hbudget := finite_average_le_of_two_error_budgets
    J M hM hcard (L : ℝ) a
    (fun j => progressionMean L (2 ^ j) (kernelWeight B d)) near trans
    hpoint hnear htrans
  change (∑ j ∈ J, progressionMean L (2 ^ j) (kernelWeight B d)) / (M : ℝ) ≤ _
  convert hbudget using 1 <;> dsimp [a] <;> ring

/-- Mandate's exact range M≥4L, as a direct corollary. -/
theorem dyadicMean_kernelWeight_le_of_four_mul_le
    (B : ℝ) (hB : 1 < B) (hB2 : B ≤ 2)
    (L d R M : ℕ) (hL : 0 < L) (hd : 0 < d) (hscale : 4 * L ≤ M) :
    dyadicMean L R M (kernelWeight B d) ≤
      (1 + 4 * (L : ℝ) / M) / ((d : ℝ) * (B - 1)) := by
  exact dyadicMean_kernelWeight_le B hB hB2 L d R M hL hd (by omega)

end ErdosProblems.Erdos257.PaperCompleteR8
end
