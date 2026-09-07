import Erdos257PeriodNoncollapse.CertificateKernel
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# An unconditional end-to-end divisor-incidence zero-window bound

Uncompiled R7 candidate. This addresses the mathematical conclusion of the
long record's sublogarithmic coverage proposition by a stronger bound.
The predicate below states the actual consecutive-zero condition explicitly.
No rationality, recurrence, or asymptotic estimate is assumed.

It is not a claim about gaps between selected exponents: those and zero
windows of their divisor transform are different objects.
-/

noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR7
open Erdos257PeriodNoncollapse

/-- The h positions immediately after N all have zero divisor incidence. -/
def IncidenceZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ h → supportCoeff A (N + i) = 0

/-- Every a consecutive positions contain a multiple of a. -/
theorem next_multiple_in_window (a N : ℕ) (ha : 0 < a) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ a ∧ a ∣ N + i := by
  let r := N % a
  have hr : r < a := Nat.mod_lt N ha
  have hdecomp : r + a * (N / a) = N := by
    simpa [r] using Nat.mod_add_div N a
  refine ⟨a - r, by omega, Nat.sub_le _ _, ?_⟩
  refine ⟨N / a + 1, ?_⟩
  calc
    N + (a - r) = a * (N / a) + a := by omega
    _ = a * (N / a + 1) := by ring

/-- The strongest elementary form: a selected positive exponent a bounds
all incidence zero windows by a-1, independently of rationality. -/
theorem incidence_zero_window_lt_selected
    (A : Set ℕ) (a N h : ℕ) (ha : a ∈ A) (ha0 : 0 < a)
    (hzero : IncidenceZeroWindow A N h) : h < a := by
  by_contra hnot
  have hah : a ≤ h := Nat.le_of_not_gt hnot
  obtain ⟨i, hi, hia, hdiv⟩ := next_multiple_in_window a N ha0
  have hpos : 0 < supportCoeff A (N + i) :=
    supportCoeff_pos_of_mem_dvd A ha hdiv (by omega)
  have hz := hzero i hi (hia.trans hah)
  omega

/-- Exact epsilon-logarithmic conclusion of long result 136, with every
shift allowed and the explicit constant B=a. Rationality is unnecessary.
This does not assume, or prove, a superlogarithmic zero-window producer. -/
theorem incidence_zero_window_eps_logb
    (A : Set ℕ) (a : ℕ) (ha : a ∈ A) (ha0 : 0 < a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, ∀ (c N h : ℕ), 1 ≤ N →
      IncidenceZeroWindow A (c + N) h →
      (h : ℝ) ≤ ε * Real.logb 2 (N : ℝ) + B := by
  refine ⟨(a : ℝ), ?_⟩
  intro c N h hN hzero
  have hh : h < a := incidence_zero_window_lt_selected A a (c + N) h ha ha0 hzero
  have hhR : (h : ℝ) ≤ (a : ℝ) := by exact_mod_cast hh.le
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.logb 2 (N : ℝ) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg hNR) (Real.log_nonneg (by norm_num))
  exact hhR.trans (le_add_of_nonneg_left (mul_nonneg hε.le hlog))

/-- A uniform finite zero-window bound whenever the support has one positive
member. The finite set of small exponents need not be coprime. -/
theorem exists_uniform_incidence_zero_window_bound
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    ∃ B : ℕ, ∀ N h : ℕ, IncidenceZeroWindow A N h → h ≤ B := by
  obtain ⟨a, ha0, ha⟩ := hA
  refine ⟨a - 1, ?_⟩
  intro N h hz
  have := incidence_zero_window_lt_selected A a N h ha ha0 hz
  omega

end ErdosProblems.Erdos257.PaperCompleteR7
end
