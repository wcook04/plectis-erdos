import ErdosProblems.Erdos243.PaperCompleteR7.Arithmetic

/-!
# Real limits and the division-free hypotheses used by the corpus

Uncompiled candidates.  In particular, the real limit in the sparse-gcd
paper statement is not silently replaced by an assumed arithmetic bound.
The equivalence is proved here.  Little-o of the count relative to N is
expressed as convergence of count/N to zero (the denominator is eventually
positive).
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter

/-- Cast conversion used to align the printed absolute value with the
integer magnitude in the existing declarations. -/
theorem natAbs_cast_real (z : ℤ) : (Int.natAbs z : ℝ) = |(z : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- A real ratio tending to zero is exactly the division-free natural
form used in `ReciprocalTailRigidity`.  Positivity is only eventual. -/
theorem nat_ratio_tendsto_zero_iff
    (m d : ℕ → ℕ)
    (hd : ∃ N, ∀ n, N ≤ n → 0 < d n) :
    Tendsto (fun n ↦ (m n : ℝ) / (d n : ℝ)) atTop (nhds 0) ↔
      ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * m n < d n := by
  obtain ⟨Nd, hNd⟩ := hd
  constructor
  · intro hlim K
    have heps : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim _ heps
    refine ⟨max Nd N, fun n hn ↦ ?_⟩
    have hdn : (0 : ℝ) < d n := by
      exact_mod_cast hNd n ((Nat.le_max_left Nd N).trans hn)
    have hnonneg : (0 : ℝ) ≤ (m n : ℝ) / (d n : ℝ) := by positivity
    have hlt : (m n : ℝ) / (d n : ℝ) < 1 / ((K : ℝ) + 1) := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
        hN n ((Nat.le_max_right Nd N).trans hn)
    have hm : (m n : ℝ) * ((K : ℝ) + 1) < (d n : ℝ) := by
      have hmul := (div_lt_div_iff₀ hdn (by positivity : (0 : ℝ) < K + 1)).mp hlt
      simpa only [one_mul] using hmul
    have hk : (K : ℝ) * (m n : ℝ) < (d n : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (m n : ℝ) by positivity]
    exact_mod_cast hk
  · intro hsmall
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    have hKpos : (0 : ℝ) < K := (one_div_pos.mpr hε).trans hK
    have hrecip : (1 : ℝ) / K < ε := by
      apply (div_lt_iff₀ hKpos).mpr
      have hprod := (div_lt_iff₀ hε).mp hK
      nlinarith
    obtain ⟨N, hN⟩ := hsmall K
    refine ⟨max Nd N, fun n hn ↦ ?_⟩
    have hdn : (0 : ℝ) < d n := by
      exact_mod_cast hNd n ((Nat.le_max_left Nd N).trans hn)
    have hmul : (m n : ℝ) * (K : ℝ) < (d n : ℝ) := by
      have hk : K * m n < d n := hN n ((Nat.le_max_right Nd N).trans hn)
      exact_mod_cast (by simpa only [Nat.mul_comm] using hk : m n * K < d n)
    have hlt : (m n : ℝ) / (d n : ℝ) < 1 / (K : ℝ) := by
      apply (div_lt_div_iff₀ hdn hKpos).mpr
      simpa only [one_mul] using hmul
    have hnonneg : (0 : ℝ) ≤ (m n : ℝ) / (d n : ℝ) := by positivity
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
      hlt.trans hrecip

/-- Printed real normalised vanishing and the exact arithmetic interface. -/
theorem normalized_vanishing_iff
    (C : ℕ → ℕ) (E : ℕ → ℤ) (hCpos : ∀ n, 0 < C n) :
    Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0) ↔
      ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n := by
  have h := nat_ratio_tendsto_zero_iff (fun n ↦ Int.natAbs (E n)) C
    ⟨0, fun n _ ↦ hCpos n⟩
  simpa only [natAbs_cast_real] using h

/-- The corpus's recursive count is exactly the finite-set cardinality
printed in the long record.  This is not a replacement count. -/
theorem strictGrowthCount_eq_filter_card (G : ℕ → ℕ) (N : ℕ) :
    strictGrowthCount G N =
      ((Finset.range N).filter (fun j ↦ G j < G (j + 1))).card := by
  classical
  induction N with
  | zero => simp [strictGrowthCount]
  | succ N ih =>
      by_cases h : G N < G (N + 1)
      · rw [Finset.range_add_one, Finset.filter_insert, if_pos h,
          Finset.card_insert_of_notMem (by simp)]
        simp only [strictGrowthCount, h, if_pos, ih]
      · rw [Finset.range_add_one, Finset.filter_insert, if_neg h]
        simp [strictGrowthCount, h, ih]

/-- Long record `res:gcdsparse`: real little-o statement (ratio form) AND
arbitrarily late constant blocks, from the displayed real limit. -/
theorem sparse_gcd_changes
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hlim : Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N ↦
      (((Finset.range N).filter (fun j ↦
        Nat.gcd (C j) (D j) < Nat.gcd (C (j + 1)) (D (j + 1)))).card : ℝ) /
          (N : ℝ)) atTop (nhds 0) ∧
    (∀ B L : ℕ, ∃ n, B ≤ n ∧ ∀ j, j ≤ L →
      Nat.gcd (C (n + j)) (D (n + j)) = Nat.gcd (C n) (D n)) := by
  have hv := (normalized_vanishing_iff C E hCpos).mp hlim
  have hsub := tailGcd_strictGrowthCount_sublinear_of_normalizedVanishes
    a C D E hCpos hC hD hE hv
  constructor
  · have hz : Tendsto (fun N ↦
        (strictGrowthCount (fun n ↦ Nat.gcd (C n) (D n)) N : ℝ) / (N : ℝ))
        atTop (nhds 0) := by
      apply (nat_ratio_tendsto_zero_iff
        (strictGrowthCount (fun n ↦ Nat.gcd (C n) (D n)))
        (fun n ↦ n) ⟨1, fun n hn ↦ lt_of_lt_of_le Nat.zero_lt_one hn⟩).mpr
      intro K
      by_cases hK : 0 < K
      · exact hsub K hK
      · have hKzero : K = 0 := by omega
        subst K
        exact ⟨1, fun n hn ↦ by simpa using (show 0 < n by omega)⟩
    simpa only [strictGrowthCount_eq_filter_card] using hz
  · exact tailGcd_exists_arbitrarilyLate_constBlock_of_normalizedVanishes
      a C D E hCpos hC hD hE hv

end ErdosProblems.Erdos243.PaperCompleteR7
