import Mathlib

/-!
# Totient finite exclusion and certificate completeness

The finite denominator bound excludes a bounded rational family. The four
completeness interfaces identify actual shifted tails and finite certificates;
the pointwise supply remains equivalent to the open irrationality problem.
Positive shifts are required in those irrationality equivalences.

The trusted statements use only Mathlib and explicit arithmetic definitions.
-/

namespace Erdos249257.ExternalVerification249FiniteCertificates

/-- The actual scaled tail of the binary totient series. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

/-- The integer discrepancy in a finite shifted totient window. -/
def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) *
      2 ^ (L - 1 - j)

/-- A finite residue lies outside both error-boundary arcs. -/
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

theorem totientSeries_denominator_exclusion :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  sorry

theorem exists_certifiedKill_iff_tail_diff_notMem_int (h N : ℕ) :
    (∃ L, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

theorem tail_diff_mem_int_iff_scaled_series_mem_int (h N : ℕ) :
    (totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ↔
      ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        ∈ Set.range ((↑) : ℤ → ℝ)) := by
  sorry

theorem irrational_totient_series_iff_all_tail_diffs_nonintegral :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

theorem irrational_totient_series_iff_pointwise_certificates :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ, ∃ L, certifiedKill h N L := by
  sorry

end Erdos249257.ExternalVerification249FiniteCertificates
