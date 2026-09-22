import Mathlib

/-!
# The literal Lambert series and a quantitative logarithmic estimate

Candidate source. Every new Lean check is UNRUN.
The value at index zero is zero (division by zero in the ambient field), so
`lambert` is exactly the usual series indexed by positive integers. Statements
about its analytic value always carry the open-unit-disc hypothesis.
-/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace ErdosProblems.Erdos1049.PaperR16

/-- A literal summand, with the harmless zero-index convention. -/
def lambertTerm {K : Type*} [NormedField K] (z : K) (n : ℕ) : K :=
  z ^ n / (1 - z ^ n)

/-- The literal Lambert series; the analytic interpretation is used only in the disc. -/
def lambert {K : Type*} [NormedField K] (z : K) : K :=
  ∑' n : ℕ, lambertTerm z n

@[simp] theorem lambertTerm_zero {K : Type*} [NormedField K] (z : K) :
    lambertTerm z 0 = 0 := by simp [lambertTerm]

lemma unit_pow_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    r ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hn := pow_nonneg hr0 n
      nlinarith

lemma unit_pow_antitone {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {a b : ℕ} (hab : a ≤ b) : r ^ b ≤ r ^ a := by
  have hp : r ^ b = r ^ a * r ^ (b - a) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  have := unit_pow_le_one hr0 hr1 (b - a)
  have := pow_nonneg hr0 a
  nlinarith

lemma unit_pow_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {n : ℕ} (hn : 0 < n) : r ^ n < 1 := by
  have h := unit_pow_antitone hr0 hr1.le (show 1 ≤ n by omega)
  simpa using lt_of_le_of_lt h (by simpa using hr1)

/-- A geometric majorant, including the zero-index convention. -/
theorem norm_lambertTerm_le {K : Type*} [NormedField K]
    (z : K) (hz : ‖z‖ < 1) (n : ℕ) :
    ‖lambertTerm z n‖ ≤ ‖z‖ ^ n / (1 - ‖z‖) := by
  by_cases hn : n = 0
  · subst n
    simp only [lambertTerm_zero, norm_zero, pow_zero]
    exact div_nonneg (by norm_num) (sub_nonneg.mpr hz.le)
  have hpow : ‖z‖ ^ n ≤ ‖z‖ := by
    simpa using unit_pow_antitone (norm_nonneg z) hz.le
      (show 1 ≤ n by omega)
  have hden : 1 - ‖z‖ ≤ ‖(1 : K) - z ^ n‖ := by
    have h := norm_sub_norm_le (1 : K) (z ^ n)
    simp only [norm_one, norm_pow] at h
    linarith
  calc
    ‖lambertTerm z n‖ = ‖z‖ ^ n / ‖(1 : K) - z ^ n‖ := by
      simp [lambertTerm, norm_div, norm_pow]
    _ ≤ ‖z‖ ^ n / (1 - ‖z‖) := by
      apply (div_le_div_iff₀
        (lt_of_lt_of_le (sub_pos.mpr hz) hden) (sub_pos.mpr hz)).2
      exact mul_le_mul_of_nonneg_left hden (pow_nonneg (norm_nonneg z) n)

/-- Absolute convergence, rather than an arbitrary totalised `tsum`. -/
theorem lambert_norm_summable {K : Type*} [NormedField K]
    (z : K) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖lambertTerm z n‖) := by
  have hmajor :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz).div_const (1 - ‖z‖)
  refine Summable.of_norm_bounded hmajor ?_
  intro n
  simpa only [norm_norm] using norm_lambertTerm_le z hz n

theorem lambert_summable {K : Type*} [NormedField K] [CompleteSpace K]
    (z : K) (hz : ‖z‖ < 1) : Summable (lambertTerm z) :=
  (lambert_norm_summable z hz).of_norm

/-- Explicit identification with the positive-index source series. -/
theorem lambert_hasSum_positive {K : Type*} [NormedField K] [CompleteSpace K]
    (z : K) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / (1 - z ^ (n + 1))) (lambert z) := by
  have hi : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    dsimp only at h
    omega
  have ho : ∀ n ∉ Set.range (fun j : ℕ => j + 1), lambertTerm z n = 0 := by
    intro n hn
    cases n with
    | zero => simp
    | succ n => exact False.elim (hn ⟨n, rfl⟩)
  simpa only [Function.comp_apply, lambertTerm] using
    (hi.hasSum_iff ho).2 (lambert_summable z hz).hasSum

theorem lambert_eq_tsum_positive {K : Type*} [NormedField K] [CompleteSpace K]
    (z : K) (hz : ‖z‖ < 1) :
    lambert z = ∑' n : ℕ, z ^ (n + 1) / (1 - z ^ (n + 1)) :=
  (lambert_hasSum_positive z hz).tsum_eq.symm

@[simp] theorem lambert_ofReal (r : ℝ) :
    lambert (r : ℂ) = ((lambert (K := ℝ) r : ℝ) : ℂ) := by
  unfold lambert
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp [lambertTerm]

/-- The elementary finite geometric factor, not a new Mahler matrix. -/
def geometricBlock (n : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, r ^ j

lemma geometricBlock_identity (n : ℕ) (r : ℝ) :
    (1 - r) * geometricBlock n r = 1 - r ^ n := by
  induction n with
  | zero => simp [geometricBlock]
  | succ n ih =>
      simp only [geometricBlock, Finset.sum_range_succ, pow_succ] at *
      nlinarith

lemma geometricBlock_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    geometricBlock n r ≤ (n : ℝ) := by
  calc
    geometricBlock n r ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun j _ => unit_pow_le_one hr0 hr1 j)
    _ = n := by simp

lemma geometricBlock_lower {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) :
    (n : ℝ) * r ^ n ≤ geometricBlock n r := by
  calc
    (n : ℝ) * r ^ n = ∑ _j ∈ Finset.range n, r ^ n := by simp
    _ ≤ geometricBlock n r := by
      apply Finset.sum_le_sum
      intro j hj
      exact unit_pow_antitone hr0 hr1 (Finset.mem_range.mp hj).le

lemma geometricBlock_pos {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 0 < n) :
    0 < geometricBlock n r := by
  unfold geometricBlock
  apply Finset.sum_pos
  · intro j _
    exact pow_pos hr j
  · exact ⟨0, Finset.mem_range.mpr hn⟩

/-- A pointwise comparison whose total error has sum at most one. -/
lemma lambertTerm_log_bounds (r : ℝ) (hr : 0 < r ∧ r < 1) (n : ℕ) :
    r ^ n / (n : ℝ) ≤ (1 - r) * lambertTerm r n ∧
    (1 - r) * lambertTerm r n ≤ r ^ n / (n : ℝ) + (1 - r) * r ^ n := by
  by_cases hn : n = 0
  · subst n
    simp only [lambertTerm_zero, mul_zero, pow_zero, Nat.cast_zero, div_zero,
      zero_add, mul_one]
    constructor
    · exact le_rfl
    · linarith [hr.2]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hp : r ^ n < 1 := unit_pow_lt_one hr.1.le hr.2 (Nat.pos_of_ne_zero hn)
  have hd : 0 < 1 - r ^ n := sub_pos.mpr hp
  have hident := geometricBlock_identity n r
  have hupper := mul_le_mul_of_nonneg_left
    (geometricBlock_le hr.1.le hr.2.le n) (sub_nonneg.mpr hr.2.le)
  have hlower := mul_le_mul_of_nonneg_left
    (geometricBlock_lower hr.1.le hr.2.le n) (sub_nonneg.mpr hr.2.le)
  have hlo : 1 / (n : ℝ) ≤ (1 - r) / (1 - r ^ n) := by
    apply (div_le_div_iff₀ hnR hd).2
    nlinarith
  have hup : (1 - r) / (1 - r ^ n) ≤ 1 / (n : ℝ) + (1 - r) := by
    calc
      (1 - r) / (1 - r ^ n) ≤ (1 + (n : ℝ) * (1 - r)) / n := by
        apply (div_le_div_iff₀ hd hnR).2
        nlinarith
      _ = 1 / (n : ℝ) + (1 - r) := by
        field_simp [ne_of_gt hnR] <;> ring
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo (pow_nonneg hr.1.le n)
    convert h using 1 <;> dsimp [lambertTerm] <;> ring
  · have h := mul_le_mul_of_nonneg_left hup (pow_nonneg hr.1.le n)
    convert h using 1 <;> dsimp [lambertTerm] <;> ring

/-- Positive logarithmic mass on the real interval `(0,1)`. -/
def logMass (r : ℝ) : ℝ := -Real.log (1 - r)

lemma logMass_pos {r : ℝ} (hr : 0 < r ∧ r < 1) : 0 < logMass r := by
  unfold logMass
  exact neg_pos.mpr (Real.log_neg (by linarith) (by linarith))

lemma logarithmic_hasSum (r : ℝ) (hr : 0 < r ∧ r < 1) :
    HasSum (fun n : ℕ => r ^ n / (n : ℝ)) (logMass r) := by
  have htail := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |r| < 1 by simpa [abs_of_pos hr.1] using hr.2)
  have hi : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    dsimp only at h
    omega
  have ho : ∀ n ∉ Set.range (fun j : ℕ => j + 1), r ^ n / (n : ℝ) = 0 := by
    intro n hn
    cases n with
    | zero => simp
    | succ n => exact False.elim (hn ⟨n, rfl⟩)
  apply (hi.hasSum_iff ho).1
  change HasSum (fun n : ℕ => r ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) (logMass r)
  simpa [logMass, Function.comp_apply, Nat.cast_add, Nat.cast_one] using htail

/-- Quantitative analytic supplier: the error is between zero and one. -/
theorem lambert_log_error_bounds (r : ℝ) (hr : 0 < r ∧ r < 1) :
    0 ≤ (1 - r) * lambert r - logMass r ∧
    (1 - r) * lambert r - logMass r ≤ 1 := by
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hr.1] using hr.2
  have hs : HasSum (fun n : ℕ => (1 - r) * lambertTerm r n)
      ((1 - r) * lambert r) := (lambert_summable r hrnorm).hasSum.mul_left _
  have hl := logarithmic_hasSum r hr
  have hg : HasSum (fun n : ℕ => (1 - r) * r ^ n) (1 : ℝ) := by
    convert (hasSum_geometric_of_lt_one hr.1.le hr.2).mul_left (1 - r) using 1
    field_simp [show 1 - r ≠ 0 by linarith [hr.2]]
  have hlo := hasSum_le (fun n => (lambertTerm_log_bounds r hr n).1) hl hs
  have hup := hasSum_le (fun n => (lambertTerm_log_bounds r hr n).2) hs (hl.add hg)
  constructor <;> linarith

end ErdosProblems.Erdos1049.PaperR16
