import Mathlib.Tactic

/-!
# Erdős #1041: the paired high mode has negative critical trace

For a low Newton-face coefficient `A_m`, disk tangency forces the complementary
correction `-conj(A_m) z^(n-m)`.  Newton's identities give the critical-point
moment

`sum_c c^(n-m) = (m(n-m)/n) A_m`.

This module checks the exact trace consequence: the real sum of the paired
correction is `-(m(n-m)/n)|A_m|^2`, hence strictly negative.  It also checks
the finite lexicographic selector consumed by the analytic argument.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFacePairedTrace

/-- The disk-forced complementary correction associated to one low mode. -/
noncomputable def pairedCorrection (A : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  -(starRingEnd ℂ A) * z ^ k

/-- The critical-moment identity turns the complementary correction trace into
a negative real multiple of `|A|^2`. -/
theorem pairedCorrection_sum_eq_neg_normSq
    {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {A : ℂ} {k : ℕ} {α : ℝ}
    (hmoment : ∑ i ∈ s, c i ^ k = (α : ℂ) * A) :
    ∑ i ∈ s, pairedCorrection A k (c i) =
      ((-α * Complex.normSq A : ℝ) : ℂ) := by
  simp only [pairedCorrection]
  rw [← Finset.mul_sum, hmoment]
  rw [show -(starRingEnd ℂ A) * ((α : ℂ) * A) =
      (-(α : ℂ)) * ((starRingEnd ℂ A) * A) by ring]
  rw [mul_comm (starRingEnd ℂ A) A, Complex.mul_conj]
  norm_num

/-- In particular, a positive moment weight and a nonzero active coefficient
make the total real correction strictly negative. -/
theorem pairedCorrection_re_sum_neg
    {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {A : ℂ} {k : ℕ} {α : ℝ}
    (hα : 0 < α) (hA : A ≠ 0)
    (hmoment : ∑ i ∈ s, c i ^ k = (α : ℂ) * A) :
    (∑ i ∈ s, pairedCorrection A k (c i)).re < 0 := by
  rw [pairedCorrection_sum_eq_neg_normSq s c hmoment]
  norm_num
  exact mul_pos hα (Complex.normSq_pos.mpr hA)

/-- The Newton weight `m(n-m)/n` is positive in the low-mode range. -/
theorem pairedWeight_pos {n m : ℕ} (hm : 0 < m) (hmn : m < n) :
    0 < (m : ℝ) * (n - m : ℝ) / (n : ℝ) := by
  have hn : 0 < n := lt_trans hm hmn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmnR : (m : ℝ) < n := by exact_mod_cast hmn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (mul_pos hmR (sub_pos.mpr hmnR)) hnR

/-- A zero leading trace followed by a negative correction trace always has a
lexicographically negative entry: either the leading value is already negative,
or it vanishes and the paired correction is negative. -/
theorem exists_lexicographically_negative
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (leading correction : ι → ℝ)
    (hleading : ∑ i, leading i = 0)
    (hcorrection : ∑ i, correction i < 0) :
    ∃ i, leading i < 0 ∨ (leading i = 0 ∧ correction i < 0) := by
  classical
  by_cases hneg : ∃ i, leading i < 0
  · obtain ⟨i, hi⟩ := hneg
    exact ⟨i, Or.inl hi⟩
  · have hnonneg : ∀ i, 0 ≤ leading i := by
      intro i
      exact le_of_not_gt (fun hi => hneg ⟨i, hi⟩)
    have hzero : ∀ i, leading i = 0 := by
      intro i
      have hle : leading i ≤ ∑ j, leading j := by
        exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      rw [hleading] at hle
      exact le_antisymm hle (hnonneg i)
    have hkneg : ∃ i, correction i < 0 := by
      by_contra h
      push Not at h
      have hsum : 0 ≤ ∑ i, correction i :=
        Finset.sum_nonneg fun i _ => h i
      linarith
    obtain ⟨i, hi⟩ := hkneg
    exact ⟨i, Or.inr ⟨hzero i, hi⟩⟩

/-- The all-degree finite kernel: the exact Newton moment for the maximal tied
low mode forces a lexicographically negative critical saddle. -/
theorem paired_trace_lexicographic_selector
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (leading : ι → ℝ) (c : ι → ℂ)
    {A : ℂ} {k : ℕ} {α : ℝ}
    (hleading : ∑ i, leading i = 0)
    (hα : 0 < α) (hA : A ≠ 0)
    (hmoment : ∑ i, c i ^ k = (α : ℂ) * A) :
    ∃ i, leading i < 0 ∨
      (leading i = 0 ∧ (pairedCorrection A k (c i)).re < 0) := by
  apply exists_lexicographically_negative leading
    (fun i => (pairedCorrection A k (c i)).re) hleading
  simpa using pairedCorrection_re_sum_neg Finset.univ c hα hA
    (by simpa using hmoment)

end ErdosProblems.Erdos1041.TiedNewtonFacePairedTrace
