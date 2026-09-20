import ErdosProblems.Erdos269.PaperR7BasicAssembly
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

/-! Literal real cutoffs for the paper's x≥1 statements. The finite prefix is
filtered by `(smooth3Val ... : ℝ) ≤ x`; it is not a surrogate integer-cutoff
hypothesis. Its equality to the existing integer carrier is proved below.
All Lean builds and audits are UNRUN. -/
namespace ErdosProblems.Erdos269.PaperR10

open scoped BigOperators

/-- A real cutoff and its natural floor select exactly the same integer powers. -/
theorem power_brackets_real_cutoff {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x) :
    ((p ^ Nat.log p ⌊x⌋₊ : ℕ) : ℝ) ≤ x ∧
      x < ((p ^ (Nat.log p ⌊x⌋₊ + 1) : ℕ) : ℝ) := by
  have hn : ⌊x⌋₊ ≠ 0 := by
    have h := (Nat.one_le_floor_iff x).mpr hx
    omega
  constructor
  · have hpow : ((p ^ Nat.log p ⌊x⌋₊ : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self p hn
    exact hpow.trans (Nat.floor_le (le_trans (by norm_num : (0 : ℝ) ≤ 1) hx))
  · exact Nat.lt_of_floor_lt
      (Nat.lt_pow_succ_log_self hp ⌊x⌋₊)

theorem real_log_floor_eq_nat_log_floor {p : ℕ} (hp : 1 < p)
    {x : ℝ} (hx : 1 ≤ x) :
    ⌊Real.logb p x⌋₊ = Nat.log p ⌊x⌋₊ := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hn : 0 ≤ Real.logb p x := (Real.logb_nonneg_iff hpR hx0).mpr hx
  have h := power_brackets_real_cutoff hp hx
  apply (Nat.floor_eq_iff hn).mpr
  constructor
  · apply (Real.le_logb_iff_rpow_le hpR hx0).mpr
    simpa only [Real.rpow_natCast, Nat.cast_pow] using h.1
  · have hh : Real.logb p x < ((Nat.log p ⌊x⌋₊ + 1 : ℕ) : ℝ) := by
      apply (Real.logb_lt_iff_lt_rpow hpR hx0).mpr
      simpa only [Real.rpow_natCast, Nat.cast_pow] using h.2
    simpa only [Nat.cast_add, Nat.cast_one] using hh

/-- Ordinary integer floor agrees with the natural floor in the paper domain. -/
theorem integer_log_floor_eq {p : ℕ} (hp : 1 < p) {x : ℝ} (hx : 1 ≤ x) :
    ⌊Real.logb p x⌋ = (Nat.log p ⌊x⌋₊ : ℤ) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hn : 0 ≤ Real.logb p x :=
    (Real.logb_nonneg_iff hpR (lt_of_lt_of_le (by norm_num) hx)).mpr hx
  rw [← Int.natCast_floor_eq_floor hn, real_log_floor_eq_nat_log_floor hp hx]

noncomputable def realPrefixExponents (p q r : ℕ) (x : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (⌊Real.logb p x⌋₊ + 1)).product
    ((Finset.range (⌊Real.logb q x⌋₊ + 1)).product
      (Finset.range (⌊Real.logb r x⌋₊ + 1)))).filter
        (fun e => (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ≤ x)

noncomputable def realPrefixLcm (p q r : ℕ) (x : ℝ) : ℕ :=
  (realPrefixExponents p q r x).lcm
    (fun e => smooth3Val p q r e.1 e.2.1 e.2.2)

noncomputable def realThreePrimeHeight (p q r : ℕ) (x : ℝ) : ℕ :=
  p ^ ⌊Real.logb p x⌋₊ * q ^ ⌊Real.logb q x⌋₊ * r ^ ⌊Real.logb r x⌋₊

theorem realPrefixExponents_eq {p q r : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 < r) {x : ℝ} (hx : 1 ≤ x) :
    realPrefixExponents p q r x = smoothPrefixExponents p q r ⌊x⌋₊ := by
  classical
  unfold realPrefixExponents smoothPrefixExponents
  rw [real_log_floor_eq_nat_log_floor hp hx,
    real_log_floor_eq_nat_log_floor hq hx, real_log_floor_eq_nat_log_floor hr hx]
  ext e
  simp only [Finset.mem_filter, Nat.le_floor_iff (le_trans (by norm_num : (0 : ℝ) ≤ 1) hx)]

theorem realThreePrimeHeight_eq {p q r : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 < r) {x : ℝ} (hx : 1 ≤ x) :
    realThreePrimeHeight p q r x = threePrimeHeight p q r ⌊x⌋₊ := by
  simp only [realThreePrimeHeight, threePrimeHeight,
    real_log_floor_eq_nat_log_floor hp hx, real_log_floor_eq_nat_log_floor hq hx,
    real_log_floor_eq_nat_log_floor hr hx]

/-- Short and long `res:lcm` with the full real domain, including x=1. -/
theorem running_lcm_real_cutoff {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x : ℝ} (hx : 1 ≤ x) :
    realPrefixLcm p q r x = realThreePrimeHeight p q r x := by
  have hn : ⌊x⌋₊ ≠ 0 := by have h := (Nat.one_le_floor_iff x).mpr hx; omega
  rw [realThreePrimeHeight_eq hp.one_lt hq.one_lt hr.one_lt hx]
  unfold realPrefixLcm
  rw [realPrefixExponents_eq hp.one_lt hq.one_lt hr.one_lt hx]
  exact smoothPrefixLcm_eq_threePrimeHeight hp hq hr hpq hpr hqr hn

/-- Short `res:cube`, without silently replacing the real cutoff by its floor. -/
theorem cubic_height_real_cutoff {p q r : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    {x : ℝ} (hx : 1 ≤ x) :
    x ^ 3 / ((p : ℝ) * q * r) < (realThreePrimeHeight p q r x : ℝ) ∧
      (realThreePrimeHeight p q r x : ℝ) ≤ x ^ 3 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans (by decide : 0 < 1) hp)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_trans (by decide : 0 < 1) hq)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_trans (by decide : 0 < 1) hr)
  have hP := power_brackets_real_cutoff hp hx
  have hQ := power_brackets_real_cutoff hq hx
  have hR := power_brackets_real_cutoff hr hx
  rw [realThreePrimeHeight_eq hp hq hr hx]
  constructor
  · apply (div_lt_iff₀ (mul_pos (mul_pos hp0 hq0) hr0)).mpr
    have hh : x * x * x <
        ((p ^ (Nat.log p ⌊x⌋₊ + 1) : ℕ) : ℝ) *
        ((q ^ (Nat.log q ⌊x⌋₊ + 1) : ℕ) : ℝ) *
        ((r ^ (Nat.log r ⌊x⌋₊ + 1) : ℕ) : ℝ) := by
      gcongr
      · exact hP.2
      · exact hQ.2
      · exact hR.2
    convert hh using 1 <;> simp only [threePrimeHeight, pow_succ, Nat.cast_mul] <;> ring
  · have hh :
        ((p ^ Nat.log p ⌊x⌋₊ : ℕ) : ℝ) *
        ((q ^ Nat.log q ⌊x⌋₊ : ℕ) : ℝ) *
        ((r ^ Nat.log r ⌊x⌋₊ : ℕ) : ℝ) ≤ x * x * x := by
      gcongr
      · exact hP.1
      · exact hQ.1
      · exact hR.1
    convert hh using 1 <;> (try simp only [threePrimeHeight, Nat.cast_mul]) <;> ring

end ErdosProblems.Erdos269.PaperR10
