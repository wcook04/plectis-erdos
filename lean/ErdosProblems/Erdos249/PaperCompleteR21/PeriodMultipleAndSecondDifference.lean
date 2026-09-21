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

/-- **The converse direction.**  Rationality makes all such tail differences
integral after a fixed starting index: there are a period `h > 0` and an index
`N₀` with `R_{N+m·h} - R_N ∈ ℤ` for every `m` and every `N ≥ N₀`. -/
theorem rational_forces_period_multiple_integrality
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ m N : ℕ, N₀ ≤ N →
      totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  obtain ⟨h, hpos, N₀, hint⟩ := eventual_period_of_not_irrational hrat
  exact ⟨h, hpos, N₀, fun m N hN => tail_diff_mul_mem_int hint m N hN⟩

/-- **The rank-1 truncation error.**  `|2^L (R_{N+h} - R_N) - D(h,N,L)| ≤
N + h + L + 2`: the deep tails after depth `L` are nonnegative and at most
`(M+L+2)/2^L`. -/
theorem abs_tail_diff_scaled_sub_window_le (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + h) - totientTail N) -
        ((windowDiscrepancy h N L : ℤ) : ℝ)| ≤ (N : ℝ) + h + L + 2 := by
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hdec1 := totientTail_eq_partial_add_tail (N + h) L
  have hdec2 := totientTail_eq_partial_add_tail N L
  have hA := windowDiscrepancy_div_eq h N L
  have hT1n := tail_after_nonneg (N + h) L
  have hT2n := tail_after_nonneg N L
  have hT1u := tail_after_le (N + h) L
  have hT2u := tail_after_le N L
  set P1 := ∑ j ∈ Finset.range L, (Nat.totient (N + h + 1 + j) : ℝ) / 2 ^ (j + 1) with hP1
  set P2 := ∑ j ∈ Finset.range L, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1) with hP2
  set T1 := ∑' j : ℕ, (Nat.totient (N + h + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT1
  set T2 := ∑' j : ℕ, (Nat.totient (N + 1 + (j + L)) : ℝ) / 2 ^ ((j + L) + 1) with hT2
  have hDval : ((windowDiscrepancy h N L : ℤ) : ℝ) = (P1 - P2) * 2 ^ L :=
    (div_eq_iff h2L.ne').mp hA
  have hb1 : T1 * 2 ^ L ≤ (N : ℝ) + h + L + 2 := by
    have hmul := mul_le_mul_of_nonneg_right hT1u h2L.le
    rw [div_mul_cancel₀ _ h2L.ne'] at hmul
    push_cast at hmul
    linarith
  have hb2 : T2 * 2 ^ L ≤ (N : ℝ) + L + 2 := by
    have hmul := mul_le_mul_of_nonneg_right hT2u h2L.le
    rw [div_mul_cancel₀ _ h2L.ne'] at hmul
    linarith
  have hn1 : 0 ≤ T1 * 2 ^ L := mul_nonneg hT1n h2L.le
  have hn2 : 0 ≤ T2 * 2 ^ L := mul_nonneg hT2n h2L.le
  have hgoal : (2 : ℝ) ^ L * (totientTail (N + h) - totientTail N) -
      ((windowDiscrepancy h N L : ℤ) : ℝ) = T1 * 2 ^ L - T2 * 2 ^ L := by
    rw [hdec1, hdec2, hDval]
    ring
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  rw [hgoal, abs_le]
  constructor <;> linarith

/-- **The error behind the rank-2 radius.**  Subtracting the two tail
identities leaves an error of absolute value at most `2(N+2h+L+2)`:
`|2^L (R_{N+2h} - 2 R_{N+h} + R_N) - (D(h,N+h,L) - D(h,N,L))| ≤ 2(N+2h+L+2)`. -/
theorem second_difference_error_bound (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N) -
        ((windowDiscrepancy h (N + h) L - windowDiscrepancy h N L : ℤ) : ℝ)| ≤
      2 * ((N : ℝ) + 2 * h + L + 2) := by
  have h1 := abs_tail_diff_scaled_sub_window_le h (N + h) L
  have h2 := abs_tail_diff_scaled_sub_window_le h N L
  rw [abs_le] at h1 h2
  push_cast at h1 h2
  rw [show N + 2 * h = N + h + h from by omega]
  push_cast
  rw [abs_le]
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

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
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_period_multiple_integrality
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.abs_tail_diff_scaled_sub_window_le
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.second_difference_error_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.second_difference_certificate_sound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.second_difference_cell_one_eight
