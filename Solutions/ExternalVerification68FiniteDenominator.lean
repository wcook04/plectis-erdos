import ErdosProblems.Erdos68.PaperCompleteFiniteSizeCertificate

namespace Erdos249257.ExternalVerification68FiniteDenominator

noncomputable def factorialGapSeries : ℝ :=
  ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0

theorem finite_denominator_exclusion (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hS : factorialGapSeries = (a : ℝ) / q) :
    (2 : ℕ) ^ 39990 ≤ q ∧ (10 : ℕ) ^ 12040 < q := by
  have h := ErdosProblems.Erdos68.PaperComplete.FiniteLead.SizeOnly.denominator_exclusion a q hq hS
  exact ⟨h.1, h.2.2⟩

end Erdos249257.ExternalVerification68FiniteDenominator
