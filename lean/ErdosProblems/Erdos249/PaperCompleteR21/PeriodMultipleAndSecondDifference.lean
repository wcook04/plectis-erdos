import Erdos249257.CertificateKernel

/-! Paper-form restatements of two long-paper certificate environments:

* `catalogue:cert:b2` — "It suffices to use multiples of a period": a
  certificate along ANY positive multiple of each prescribed period, at
  arbitrarily large basepoints, implies irrationality; with `m = 1` this is
  the quantified condition of `catalogue:cert:a10`, so the multiple condition
  is in fact equivalent to irrationality.
* `catalogue:cert:b9a` — "Soundness of a second-difference certificate": the
  rank-2 residue band of radius `2(N+2h+L+2)` forces
  `R_{N+2h} - 2R_{N+h} + R_N ∉ ℤ`, together with the measured `(h,N) = (1,8)`
  cell (rank-1 fires at depth 8, rank-2 at no depth `L ≤ 8` and at `L = 9`).

The existing `Erdos249257.TotientTailPeriodKiller` proofs carry the content;
here `D(h,N,L) = windowDiscrepancy h N L`, `C(h,N,L) = certifiedKill h N L`
and `R_N = totientTail N`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-- **It suffices to use multiples of a period.**
`(∀ h₀ > 0, ∀ N₀, ∃ m > 0, ∃ N ≥ N₀, ∃ L, C(m·h₀, N, L)) → S ∉ ℚ`. -/
theorem irrational_of_period_multiple_certificate_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totient_series_of_multiple_certificate_supply hsupply

/-- The `m = 1` instance: the quantified condition of the base theorem is the
special case of the multiple condition at multiplier one. -/
theorem period_multiple_certificate_at_one {h₀ N L : ℕ}
    (hcert : certifiedKill h₀ N L) : certifiedKill (1 * h₀) N L := by
  simpa using hcert

/-- The displayed implication makes the multiple-period condition equivalent
to irrationality: rationality makes every tail difference along a period ray
integral after a fixed starting index, and conversely completeness supplies a
certificate at multiplier one. -/
theorem period_multiple_certificate_supply_iff :
    (∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
        ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  constructor
  · exact irrational_totient_series_of_multiple_certificate_supply
  · intro hirr h₀ hh N₀
    obtain ⟨N, hN, L, hL⟩ :=
      irrational_totient_series_iff_certificate_supply.mp hirr h₀ hh N₀
    exact ⟨1, Nat.one_pos, N, hN, L, period_multiple_certificate_at_one hL⟩

/-- **Soundness of a second-difference certificate.**  If
`2(N+2h+L+2) < (D(h,N+h,L) - D(h,N,L)) mod 2^L < 2^L - 2(N+2h+L+2)`
then `R_{N+2h} - 2R_{N+h} + R_N ∉ ℤ`. -/
theorem second_difference_certificate_sound {h N L : ℕ}
    (hlow : 2 * ((N : ℤ) + 2 * h + L + 2) <
      (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L)
    (hhigh : (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L <
      2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)) :
    totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N ∉
      Set.range ((↑) : ℤ → ℝ) := by
  have hcert : certifiedRank2Kill h N L := ⟨hlow, hhigh⟩
  intro hmem
  obtain ⟨k, hk⟩ := hmem
  exact second_diff_notMem_int_of_certifiedRank2Kill hcert ⟨k, by rw [hk]; ring⟩

/-- The measured cell at `(h,N) = (1,8)`: the first-difference test holds at
depth `8`, the second-difference test fails at every depth `L ≤ 8` and holds
at `L = 9`. -/
theorem second_difference_cell_one_eight :
    certifiedKill 1 8 8 ∧
      (∀ L : ℕ, L ≤ 8 → ¬ certifiedRank2Kill 1 8 L) ∧
      certifiedRank2Kill 1 8 9 := by
  obtain ⟨hone, hfail, hnine⟩ :=
    totient_tail_rank_two_kill_sound_but_not_shallower_cell
  refine ⟨hone, ?_, hnine⟩
  intro L hL
  rcases Nat.eq_zero_or_pos L with rfl | hpos
  · decide
  · exact hfail L (Finset.mem_Icc.mpr ⟨hpos, hL⟩)

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_period_multiple_certificate_supply
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_at_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_supply_iff
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.second_difference_certificate_sound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.second_difference_cell_one_eight
