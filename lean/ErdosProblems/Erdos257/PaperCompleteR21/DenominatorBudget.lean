import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Paper-form restatement of long Erdős #257 `prop:exponent-gap`
("Weighted denominator budget", `a257_front.tex:1463`).

For `n ≥ 2` and a skip set `Skip_n ⊆ {2,…,n−1}`, with `D_n` the reduced
denominator of `∑_{d ∈ Skip_n} 1/(2^d − 1)`,

`log₂ D_n ≤ ∑_{d ∈ Skip_n} log₂(2^d − 1) ≤ ∑_{d ∈ Skip_n} d ≤ n(n−1)/2 − 1`,

with the middle inequality strict when the skip set is nonempty and both sums
zero when it is empty.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

/-- The finite Mersenne sum associated with a skip set. -/
def skipSum (S : Finset ℕ) : ℚ := ∑ d ∈ S, 1 / ((2 : ℚ) ^ d - 1)

private theorem den_dvd_of_mul_int_eq {q : ℚ} {N z : ℤ} (hN : N ≠ 0)
    (h : q * (N : ℚ) = (z : ℚ)) : ((q.den : ℤ)) ∣ N := by
  have hNQ : ((N : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hN
  have hq : q = Rat.divInt z N := by
    rw [Rat.divInt_eq_div, eq_div_iff hNQ]
    exact h
  rw [hq]
  exact Rat.den_dvd z N

private theorem mersenne_int_pos {d : ℕ} (hd : 1 ≤ d) : (0 : ℤ) < 2 ^ d - 1 := by
  have h : (1 : ℤ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  omega

private theorem mersenne_rat_ne {d : ℕ} (hd : 1 ≤ d) : ((2 : ℚ) ^ d - 1) ≠ 0 := by
  have h : (1 : ℚ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  intro hc
  linarith

/-- `D_n` divides the product of its Mersenne denominators. -/
theorem skipSum_den_dvd_prod (S : Finset ℕ) (hS : ∀ d ∈ S, 1 ≤ d) :
    ((skipSum S).den : ℤ) ∣ ∏ d ∈ S, ((2 : ℤ) ^ d - 1) := by
  classical
  have hNne : (∏ d ∈ S, ((2 : ℤ) ^ d - 1)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro d hd
    exact ne_of_gt (mersenne_int_pos (hS d hd))
  refine den_dvd_of_mul_int_eq (z := ∑ d ∈ S, ∏ e ∈ S.erase d, ((2 : ℤ) ^ e - 1))
    hNne ?_
  push_cast
  rw [skipSum, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hfac : (∏ e ∈ S, ((2 : ℚ) ^ e - 1))
      = ((2 : ℚ) ^ d - 1) * ∏ e ∈ S.erase d, ((2 : ℚ) ^ e - 1) :=
    (Finset.mul_prod_erase S _ hd).symm
  rw [hfac, ← mul_assoc, one_div, inv_mul_cancel₀ (mersenne_rat_ne (hS d hd)),
    one_mul]

private theorem log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- `log₂(2^d − 1) < d` for every `d ≥ 1`. -/
theorem logb_mersenne_lt {d : ℕ} (hd : 1 ≤ d) :
    Real.logb 2 ((2 : ℝ) ^ d - 1) < (d : ℝ) := by
  have h1 : (1 : ℝ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
  have hpos : (0 : ℝ) < 2 ^ d - 1 := by linarith
  have hlt : ((2 : ℝ) ^ d - 1) < 2 ^ d := by linarith
  have hlog := Real.log_lt_log hpos hlt
  have hpow : Real.log ((2 : ℝ) ^ d) = (d : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  rw [← Real.log_div_log, div_lt_iff₀ log_two_pos]
  rw [hpow] at hlog
  linarith

/-- Long `prop:exponent-gap`, every clause. -/
theorem weighted_denominator_budget (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico 2 n) :
    Real.logb 2 (((skipSum S).den : ℕ) : ℝ)
        ≤ ∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1) ∧
      (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) ≤ ∑ d ∈ S, (d : ℝ) ∧
      (∑ d ∈ S, (d : ℝ)) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 - 1 ∧
      (S.Nonempty →
        (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) < ∑ d ∈ S, (d : ℝ)) ∧
      (S = ∅ → (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) = 0 ∧
        (∑ d ∈ S, (d : ℝ)) = 0) := by
  classical
  have hbounds : ∀ d ∈ S, 2 ≤ d ∧ d < n := by
    intro d hd
    have := Finset.mem_Ico.mp (hS hd)
    exact this
  have hS1 : ∀ d ∈ S, 1 ≤ d := fun d hd => le_trans (by omega) (hbounds d hd).1
  -- clause 1
  have hclause1 : Real.logb 2 (((skipSum S).den : ℕ) : ℝ)
      ≤ ∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1) := by
    have hdvd := skipSum_den_dvd_prod S hS1
    have hNpos : (0 : ℤ) < ∏ d ∈ S, ((2 : ℤ) ^ d - 1) :=
      Finset.prod_pos fun d hd => mersenne_int_pos (hS1 d hd)
    have hle : ((skipSum S).den : ℤ) ≤ ∏ d ∈ S, ((2 : ℤ) ^ d - 1) :=
      Int.le_of_dvd hNpos hdvd
    have hleR : (((skipSum S).den : ℕ) : ℝ) ≤ ∏ d ∈ S, ((2 : ℝ) ^ d - 1) := by
      have hcast : ((((skipSum S).den : ℤ)) : ℝ)
          ≤ ((∏ d ∈ S, ((2 : ℤ) ^ d - 1) : ℤ) : ℝ) := by exact_mod_cast hle
      push_cast at hcast
      exact hcast
    have hDpos : (0 : ℝ) < (((skipSum S).den : ℕ) : ℝ) := by
      exact_mod_cast (skipSum S).pos
    have hlog : Real.log (((skipSum S).den : ℕ) : ℝ)
        ≤ Real.log (∏ d ∈ S, ((2 : ℝ) ^ d - 1)) := Real.log_le_log hDpos hleR
    have hprod : Real.log (∏ d ∈ S, ((2 : ℝ) ^ d - 1))
        = ∑ d ∈ S, Real.log ((2 : ℝ) ^ d - 1) := by
      refine Real.log_prod ?_
      intro d hd
      have h1 : (1 : ℝ) < 2 ^ d := one_lt_pow₀ (by norm_num) (by
        have := hS1 d hd; omega)
      intro hc
      linarith
    have hsum : ∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)
        = (∑ d ∈ S, Real.log ((2 : ℝ) ^ d - 1)) / Real.log 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun d _ => (Real.log_div_log).symm
    rw [← Real.log_div_log, hsum, div_le_div_iff₀ log_two_pos log_two_pos]
    nlinarith [hlog, hprod, log_two_pos]
  -- clause 2 and 4
  have hpointwise : ∀ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1) < (d : ℝ) :=
    fun d hd => logb_mersenne_lt (hS1 d hd)
  have hclause2 : (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) ≤ ∑ d ∈ S, (d : ℝ) :=
    Finset.sum_le_sum fun d hd => (hpointwise d hd).le
  have hclause4 : S.Nonempty →
      (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) < ∑ d ∈ S, (d : ℝ) :=
    fun hne => Finset.sum_lt_sum_of_nonempty hne hpointwise
  -- clause 3
  have hclause3 : (∑ d ∈ S, (d : ℝ)) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 - 1 := by
    have hnat : ∑ d ∈ S, d ≤ ∑ d ∈ Finset.Ico 2 n, d :=
      Finset.sum_le_sum_of_subset hS
    have hcons : (∑ i ∈ Finset.Ico 0 2, i) + (∑ i ∈ Finset.Ico 2 n, i)
        = ∑ i ∈ Finset.Ico 0 n, i :=
      Finset.sum_Ico_consecutive (fun i : ℕ => i) (by omega) (by omega)
    have hrange : ∑ i ∈ Finset.range n, i = ∑ i ∈ Finset.Ico 0 n, i := by
      rw [Finset.range_eq_Ico]
    have hgauss := Finset.sum_range_id_mul_two n
    have h02 : (∑ i ∈ Finset.Ico 0 2, i) = 1 := by decide
    have hkey : 2 * (∑ d ∈ S, d) + 2 ≤ (∑ i ∈ Finset.range n, i) * 2 := by omega
    have hkey2 : 2 * (∑ d ∈ S, d) + 2 ≤ n * (n - 1) := by
      rw [← hgauss]; exact hkey
    have hcastn : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      have hle1 : (1 : ℕ) ≤ n := by omega
      push_cast [hle1]
      ring
    have hsumcast : (∑ d ∈ S, (d : ℝ)) = ((∑ d ∈ S, d : ℕ) : ℝ) := by push_cast; ring
    have hkeyR : 2 * ((∑ d ∈ S, d : ℕ) : ℝ) + 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
      have h : ((2 * (∑ d ∈ S, d) + 2 : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
        exact_mod_cast hkey2
      rw [hcastn] at h
      push_cast at h
      linarith
    rw [hsumcast]
    linarith
  refine ⟨hclause1, hclause2, hclause3, hclause4, ?_⟩
  intro hempty
  subst hempty
  simp

#print axioms skipSum_den_dvd_prod
#print axioms weighted_denominator_budget
end ErdosProblems.Erdos257.PaperCompleteR21
