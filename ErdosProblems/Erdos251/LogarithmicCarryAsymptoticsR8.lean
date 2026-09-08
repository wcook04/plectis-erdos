import ErdosProblems.Erdos251.LogarithmicCarryR8
import ErdosProblems.Erdos251.SparseScheduleDensityR8
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Cumulative n log n growth for the value-6 word

This proof source uses only the synthetic factorial spike
sets. It does NOT assume the prime number theorem. The baseline mean is
proved using Stirling's factorial bound, and the sparse modification error
is controlled by the proved zero density of the factorial sites.

Pinned source APIs:
* Analysis/SpecialFunctions/Stirling.lean: le_log_factorial_stirling.
* Data/Nat/Factorial/Basic.lean: factorial_le_pow, factorial_succ.
* Topology/MetricSpace/Pseudo/Defs.lean: Metric.tendsto_atTop.
* Topology/MetricSpace/Pseudo/Lemmas.lean: squeeze_zero'.
* Order/Filter/AtTopBot/Archimedean.lean: tendsto_natCast_atTop_atTop.
-/

noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperR8.LogCarry

open SparseSchedule

def factorialCentre (j : ℕ) : ℕ := (j + 5).factorial
def doubleFactorialCentre (j : ℕ) : ℕ := 2 * factorialCentre j

theorem factorialCentre_strictMono : StrictMono factorialCentre := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact Nat.factorial_lt_of_lt (by omega : 0 < j + 5) (by omega)

theorem factorialCentre_spacing (R : ℕ) :
    ∃ J, ∀ j, J ≤ j → R ≤ factorialCentre (j + 1) - factorialCentre j := by
  refine ⟨R, ?_⟩
  intro j hj
  have hp : 1 ≤ (j + 5).factorial := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hs : factorialCentre (j + 1) = (j + 6) * factorialCentre j := by
    change (j + 1 + 5).factorial = (j + 6) * (j + 5).factorial
    rw [show j + 1 + 5 = (j + 5) + 1 by omega, Nat.factorial_succ]
  have hmul := Nat.mul_le_mul_left (j + 5) hp
  simp only [Nat.mul_one] at hmul
  change j + 5 ≤ (j + 5) * factorialCentre j at hmul
  have heq : (j + 6) * factorialCentre j =
      (j + 5) * factorialCentre j + factorialCentre j := by ring
  rw [hs, heq, Nat.add_sub_cancel]
  exact hj.trans ((by omega : j ≤ j + 5).trans hmul)

theorem doubleFactorialCentre_strictMono : StrictMono doubleFactorialCentre := by
  intro i j hij
  have h := factorialCentre_strictMono hij
  unfold doubleFactorialCentre
  omega

theorem doubleFactorialCentre_spacing (R : ℕ) :
    ∃ J, ∀ j, J ≤ j → R ≤ doubleFactorialCentre (j + 1) - doubleFactorialCentre j := by
  obtain ⟨J, hJ⟩ := factorialCentre_spacing R
  refine ⟨J, ?_⟩
  intro j hj
  have h := hJ j hj
  unfold doubleFactorialCentre
  omega

theorem special_eq_ranges (n : ℕ) :
    Special n ↔ n ∈ Set.range factorialCentre ∨ n ∈ Set.range doubleFactorialCentre := by
  constructor
  · rintro (⟨k, hk, heq⟩ | ⟨k, hk, heq⟩)
    · left
      refine ⟨k - 5, ?_⟩
      unfold factorialCentre
      rw [Nat.sub_add_cancel hk]
      exact heq.symm
    · right
      refine ⟨k - 5, ?_⟩
      unfold doubleFactorialCentre factorialCentre
      rw [Nat.sub_add_cancel hk]
      exact heq.symm
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact Or.inl ⟨k + 5, by omega, hk.symm⟩
    · exact Or.inr ⟨k + 5, by omega, hk.symm⟩

def specialCount (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range n).filter Special).card

/-- Reciprocal-integer density budget for the actual synthetic spike set. -/
theorem specialCount_budget (R : ℕ) (hR : 0 < R) :
    ∃ N, ∀ n, N ≤ n → R * specialCount n ≤ n := by
  classical
  have h1 := upperBanachZero_of_eventual_spacing factorialCentre
    factorialCentre_strictMono factorialCentre_spacing
  have h2 := upperBanachZero_of_eventual_spacing doubleFactorialCentre
    doubleFactorialCentre_strictMono doubleFactorialCentre_spacing
  obtain ⟨N1, hN1⟩ := h1 (2 * R) (by omega)
  obtain ⟨N2, hN2⟩ := h2 (2 * R) (by omega)
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  let s1 := (Finset.range n).filter (fun k => k ∈ Set.range factorialCentre)
  let s2 := (Finset.range n).filter (fun k => k ∈ Set.range doubleFactorialCentre)
  have ha : (2 * R) * s1.card ≤ n := by
    simpa only [Nat.zero_add, Nat.Ico_zero_eq_range] using
      hN1 0 n ((le_max_left _ _).trans hn)
  have hb : (2 * R) * s2.card ≤ n := by
    simpa only [Nat.zero_add, Nat.Ico_zero_eq_range] using
      hN2 0 n ((le_max_right _ _).trans hn)
  have hsub : (Finset.range n).filter Special ⊆ s1 ∪ s2 := by
    intro k hk
    obtain ⟨hkr, hks⟩ := Finset.mem_filter.mp hk
    rcases (special_eq_ranges k).mp hks with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hkr, h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hkr, h⟩))
  have hc : specialCount n ≤ s1.card + s2.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hmul := Nat.mul_le_mul_left (2 * R) hc
  nlinarith

theorem specialCount_div_tendsto_zero :
    Tendsto (fun n : ℕ => (specialCount n : ℝ) / n) atTop (𝓝 0) := by
  -- Mathlib/Topology/MetricSpace/Pseudo/Defs.lean.
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R, hRε⟩ := exists_nat_gt (1 / ε)
  have hRr : (0 : ℝ) < R := lt_trans (by positivity : (0 : ℝ) < 1 / ε) hRε
  have hR : 0 < R := by exact_mod_cast hRr
  obtain ⟨N, hN⟩ := specialCount_budget R hR
  refine ⟨max 1 N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbound : (R : ℝ) * (specialCount n : ℝ) ≤ n := by
    exact_mod_cast hN n ((le_max_right _ _).trans hn)
  have hratio : (specialCount n : ℝ) / n ≤ 1 / (R : ℝ) := by
    apply (div_le_iff₀ hnr).mpr
    calc
      (specialCount n : ℝ) ≤ (n : ℝ) / R :=
        (le_div_iff₀ hRr).mpr (by nlinarith [hbound])
      _ = (1 / (R : ℝ)) * n := by ring
  have hcoeff : 1 / (R : ℝ) < ε := by
    apply (div_lt_iff₀ hRr).mpr
    have h := (div_lt_iff₀ hε).mp hRε
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hnr.le)]
  exact hratio.trans_lt hcoeff

/-- Logarithms of the finite factorial product, proved by induction. -/
theorem sum_log_successors (n : ℕ) :
    ∑ j ∈ range n, Real.log ((j : ℝ) + 1) = Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, Nat.factorial_succ]
      push_cast
      rw [Real.log_mul (by positivity) (by exact_mod_cast Nat.factorial_ne_zero n)]
      ring

def baselineSum (n : ℕ) : ℝ := ∑ j ∈ range n, (baseline j : ℝ)
def carryExcess (n : ℕ) : ℝ := ∑ j ∈ range n, ((carry j : ℝ) - baseline j)

theorem baselineSum_bounds (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ baselineSum n ∧
      baselineSum n ≤ Real.log (n.factorial : ℝ) + 6 * n := by
  have hlo : ∀ j ∈ range n, Real.log ((j : ℝ) + 1) ≤ (baseline j : ℝ) := by
    intro j hj
    linarith [(baseline_log_bounds j).1]
  have hhi : ∀ j ∈ range n, (baseline j : ℝ) ≤ Real.log ((j : ℝ) + 1) + 6 := by
    intro j hj
    exact (baseline_log_bounds j).2
  have h1 := Finset.sum_le_sum hlo
  have h2 := Finset.sum_le_sum hhi
  rw [sum_log_successors] at h1
  simp only [Finset.sum_add_distrib, sum_log_successors, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at h2
  exact ⟨h1, by simpa only [mul_comm] using h2⟩

/-- A coarse factorial bound is sufficient; no sharp Stirling error is used. -/
theorem log_factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - (1 + |Real.log (2 * Real.pi)|) * n ≤
      Real.log (n.factorial : ℝ) ∧
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnr
  -- Mathlib/Analysis/SpecialFunctions/Stirling.lean.
  have hs := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have hp := neg_abs_le (Real.log (2 * Real.pi))
  have hnabs := mul_le_mul_of_nonneg_left hnr (abs_nonneg (Real.log (2 * Real.pi)))
  have hnonneg := mul_nonneg (abs_nonneg (Real.log (2 * Real.pi))) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  constructor
  · nlinarith only [hs, hp, hnabs, hl, hnonneg]
  · have hfac : (n.factorial : ℝ) ≤ (n : ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial) hfac
    simpa only [Real.log_pow] using hlog

theorem log_nat_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The baseline average is asymptotic to n log n. -/
theorem baselineSum_asymptotic :
    Tendsto (fun n : ℕ => baselineSum n / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
  let C : ℝ := 1 + |Real.log (2 * Real.pi)|
  have hC : 0 ≤ C := by positivity
  have hlow : Tendsto (fun n : ℕ => 1 - C / Real.log n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := C)).div_atTop log_nat_tendsto_atTop
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  have hhigh : Tendsto (fun n : ℕ => 1 + 6 / Real.log n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (6 : ℝ))).div_atTop log_nat_tendsto_atTop
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have h1 := (log_factorial_bounds n (by omega)).1
    have h2 := (baselineSum_bounds n).1
    apply (le_div_iff₀ (mul_pos hnR hl)).mpr
    have heq : (1 - C / Real.log n) * ((n : ℝ) * Real.log n) =
        (n : ℝ) * Real.log n - C * n := by field_simp [hnR.ne', hl.ne'] <;> ring
    rw [heq]
    exact h1.trans h2
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have h1 := (log_factorial_bounds n (by omega)).2
    have h2 := (baselineSum_bounds n).2
    apply (div_le_iff₀ (mul_pos hnR hl)).mpr
    have heq : (1 + 6 / Real.log n) * ((n : ℝ) * Real.log n) =
        (n : ℝ) * Real.log n + 6 * n := by field_simp [hnR.ne', hl.ne'] <;> ring
    rw [heq]
    linarith

theorem carryExcess_bounds (n : ℕ) :
    0 ≤ carryExcess n ∧ carryExcess n ≤ (baseline n : ℝ) * specialCount n := by
  classical
  have hnonneg : ∀ j, 0 ≤ (carry j : ℝ) - baseline j := by
    intro j
    exact sub_nonneg.mpr (by exact_mod_cast (carry_bounds j).1)
  refine ⟨Finset.sum_nonneg (fun j _ => hnonneg j), ?_⟩
  have hterm : ∀ j ∈ range n,
      (carry j : ℝ) - baseline j ≤ if Special j then (baseline n : ℝ) else 0 := by
    intro j hj
    by_cases hs : Special j
    · rw [if_pos hs]
      have h1 : (carry j : ℝ) ≤ 2 * baseline j := by exact_mod_cast (carry_bounds j).2
      have h2 : (baseline j : ℝ) ≤ baseline n := by
        exact_mod_cast baseline_mono (Nat.le_of_lt (Finset.mem_range.mp hj))
      linarith
    · rw [if_neg hs, carry_of_ordinary hs]
      simp only [sub_self, le_refl]
  have h := Finset.sum_le_sum hterm
  have heq : (∑ j ∈ range n, if Special j then (baseline n : ℝ) else 0) =
      (baseline n : ℝ) * specialCount n := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, specialCount, mul_comm]
  exact h.trans_eq heq

theorem baseline_le_three_log_eventually :
    ∀ᶠ n : ℕ in atTop, (baseline n : ℝ) ≤ 3 * Real.log n := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ),
    log_nat_tendsto_atTop.eventually_ge_atTop 6] with n hn hlog
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have harg : (n : ℝ) + 1 ≤ 2 * n := by linarith
  have hlog' := Real.log_le_log (by positivity : 0 < (n : ℝ) + 1) harg
  rw [Real.log_mul (by norm_num) (by positivity : (n : ℝ) ≠ 0)] at hlog'
  have h2 : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hnR
  linarith [(baseline_log_bounds n).2]

/-- Sparse factorial changes do not affect the leading cumulative term. -/
theorem carryExcess_normalized_tendsto_zero :
    Tendsto (fun n : ℕ => carryExcess n / ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
  have h3 := specialCount_div_tendsto_zero.const_mul 3
  have h3' : Tendsto (fun n : ℕ => 3 * ((specialCount n : ℝ) / n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using h3
  apply squeeze_zero' ?_ ?_ h3'
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    exact div_nonneg (carryExcess_bounds n).1 (mul_nonneg (Nat.cast_nonneg _) hln)
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ), baseline_le_three_log_eventually] with n hn hb
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have he := (carryExcess_bounds n).2
    have hmul := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (specialCount n))
    apply (div_le_iff₀ (mul_pos hnR hl)).mpr
    have heq : (3 * ((specialCount n : ℝ) / n)) * ((n : ℝ) * Real.log n) =
        (3 * Real.log n) * specialCount n := by field_simp [hnR.ne', hl.ne'] <;> ring
    rw [heq]
    exact he.trans hmul

theorem endpoint_normalized_tendsto_zero :
    Tendsto (fun n : ℕ => (carry n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
  have h6 : Tendsto (fun n : ℕ => (6 : ℝ) / n) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (6 : ℝ))).div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' ?_ ?_ h6
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with n hn
    have hc : (0 : ℝ) ≤ (carry n : ℝ) := by
      exact_mod_cast (le_trans (by norm_num : (0 : ℤ) ≤ 6) ((baseline_ge_six n).trans (carry_bounds n).1))
    exact div_nonneg hc (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))))
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ), baseline_le_three_log_eventually] with n hn hb
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hc : (carry n : ℝ) ≤ 2 * baseline n := by exact_mod_cast (carry_bounds n).2
    apply (div_le_iff₀ (mul_pos hnR hl)).mpr
    have heq : ((6 : ℝ) / n) * ((n : ℝ) * Real.log n) = 6 * Real.log n := by field_simp [hnR.ne', hl.ne']
    rw [heq]
    linarith

/-- Complete cumulative prime-number-theorem-scale conclusion, for the
synthetic word only. The real prime number theorem is not a premise. -/
theorem position_PNT_scale :
    Tendsto (fun n : ℕ => (position n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
  have h9 : Tendsto (fun n : ℕ => (9 : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (9 : ℝ) / n) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (9 : ℝ))).div_atTop tendsto_natCast_atTop_atTop
    have hl : Tendsto (fun n : ℕ => (1 : ℝ) / Real.log n) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop log_nat_tendsto_atTop
    simpa only [zero_mul, mul_one_div, div_div] using hn.mul hl
  have hmean : Tendsto (fun n : ℕ =>
      baselineSum n / ((n : ℝ) * Real.log n) +
      carryExcess n / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
    simpa only [add_zero] using baselineSum_asymptotic.add carryExcess_normalized_tendsto_zero
  have hlim := (h9.add hmean).sub endpoint_normalized_tendsto_zero
  have heq : ∀ n : ℕ,
      (9 : ℝ) / ((n : ℝ) * Real.log n) +
        (baselineSum n / ((n : ℝ) * Real.log n) +
          carryExcess n / ((n : ℝ) * Real.log n)) -
        (carry n : ℝ) / ((n : ℝ) * Real.log n) =
      (position n : ℝ) / ((n : ℝ) * Real.log n) := by
    intro n
    have hp : (position n : ℝ) = 9 + (∑ j ∈ range n, (carry j : ℝ)) - carry n := by
      exact_mod_cast position_identity n
    have hs : baselineSum n + carryExcess n = ∑ j ∈ range n, (carry j : ℝ) := by
      unfold baselineSum carryExcess
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hp, ← hs]
    ring
  simpa only [heq, zero_add, sub_zero] using hlim

/-- The full existential construction is exhibited by `digit` and `position`.
Positive even coefficients are expressed in Z with explicit positivity;
this is not an additional hypothesis on the construction. -/
theorem logarithmic_recurring_values_countermodel :
    (∀ n, 1 ≤ n → 0 < digit n ∧ (2 : ℤ) ∣ digit n) ∧
    (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧ digit i = 2 ∧ digit j = 4) ∧
    (∀ B : ℤ, ∀ N : ℕ, ∃ n, N ≤ n ∧ B < digit n) ∧
    (∀ h : ℕ, 0 < h → ¬ ∃ N₀, ∀ n, N₀ ≤ n → digit (n + h) = digit n) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → (digit n : ℝ) ≤ C * Real.log (n : ℝ)) ∧
    HasSum (fun j : ℕ => (digit (j + 1) : ℝ) / 2 ^ (j + 1)) 6 ∧
    (∀ N, HasSum (fun j : ℕ => (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (carry N : ℝ)) ∧
    (∀ N h, ∃ z : ℤ,
      (∑' j : ℕ, (digit (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
      (∑' j : ℕ, (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z) ∧
    StrictMono position ∧ (∀ n, ∃ z : ℤ, position n = 2 * z + 1) ∧
    Tendsto (fun n : ℕ => (position n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
  refine ⟨?_, ?_, digit_cofinally_unbounded, digit_not_eventually_periodic,
    digit_eventual_log_bound, hasSum_six, hasSum_tail, all_tail_shifts_integral,
    position_strictMono, position_odd, position_PNT_scale⟩
  · intro n hn
    exact ⟨digit_positive n hn, digit_even n⟩
  · intro t ht N
    exact digit_recurring_multiples t N ht

/-- Existential form of the displayed paper statement. The cumulative
position is defined from the SAME coefficient witness, not supplied independently. -/
theorem exists_logarithmic_recurring_values_countermodel :
    ∃ a U : ℕ → ℤ,
      let P : ℕ → ℤ := fun n => 3 + ∑ j ∈ range n, a (j + 1);
      (∀ n, 1 ≤ n → 0 < a n ∧ (2 : ℤ) ∣ a n) ∧
      (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧ a i = 2 ∧ a j = 4) ∧
      (∀ B : ℤ, ∀ N : ℕ, ∃ n, N ≤ n ∧ B < a n) ∧
      (∀ h : ℕ, 0 < h → ¬ ∃ N₀, ∀ n, N₀ ≤ n → a (n + h) = a n) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → (a n : ℝ) ≤ C * Real.log (n : ℝ)) ∧
      HasSum (fun j : ℕ => (a (j + 1) : ℝ) / 2 ^ (j + 1)) 6 ∧
      (∀ N, HasSum (fun j : ℕ => (a (N + j + 1) : ℝ) / 2 ^ (j + 1)) (U N : ℝ)) ∧
      (∀ N h, ∃ z : ℤ,
        (∑' j : ℕ, (a (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
        (∑' j : ℕ, (a (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z) ∧
      StrictMono P ∧ (∀ n, ∃ z : ℤ, P n = 2 * z + 1) ∧
      Tendsto (fun n : ℕ => (P n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
  exact ⟨digit, carry, logarithmic_recurring_values_countermodel⟩

#print axioms exists_logarithmic_recurring_values_countermodel

#print axioms logarithmic_recurring_values_countermodel
end ErdosProblems.Erdos251.PaperR8.LogCarry
