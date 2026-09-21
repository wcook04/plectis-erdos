import Erdos249257.CertificateKernel
import Erdos249257.GapFareyBound

/-! Paper-form restatements of the two Farey-gap environments:

* `prop:C2-inv` — with `V` the totient residue at `(N,K) = (1,240)`, the
  inequality `(qV) mod 2^240 + 243q < 2^240` holds for every
  `1 ≤ q ≤ 79639646646701375323355774875831053` and fails first at
  `q = 79639646646701375323355774875831054`; the range is approximately
  `7.96 × 10^34`;
* `prop:C3-inv` — every reduced fraction with denominator at most
  `79639646646701375323355774875831053` differs from `S`.

`V` is written as the paper writes it, as the window totient residue
`(∑_{r=1}^{240} φ(1+r) 2^(240-r)) mod 2^240`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257

/-! ### `prop:C2-inv` — the exact range of the stated Farey-gap inequality -/

/-- **The exact range of the stated Farey-gap inequality.**  Every
`1 ≤ q ≤ 79639646646701375323355774875831053` satisfies
`(qV) mod 2^240 + 243q < 2^240`, and the first failure is at
`q = 79639646646701375323355774875831054`. -/
theorem farey_window_1_240_exact_range :
    (∀ q : ℕ, 1 ≤ q → q ≤ 79639646646701375323355774875831053 →
        (q * ((∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r))
              % 2 ^ 240)) % 2 ^ 240 + q * 243 < 2 ^ 240) ∧
      ¬ ((79639646646701375323355774875831054 *
              ((∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r))
                % 2 ^ 240)) % 2 ^ 240
            + 79639646646701375323355774875831054 * 243 < 2 ^ 240) := by
  obtain ⟨hpass, hfail⟩ := GapFareyBound.gap_check_window_1_240_first_failure
  rw [totient_carry_residue_window_1_240_eq]
  exact ⟨fun q h1 h2 => hpass q (by omega) (by omega), hfail⟩

/-- The range is approximately `7.96 × 10^34`. -/
theorem farey_window_1_240_range_magnitude :
    (796 : ℕ) * 10 ^ 32 ≤ 79639646646701375323355774875831053 ∧
      (79639646646701375323355774875831053 : ℕ) < 797 * 10 ^ 32 := by
  constructor <;> norm_num

/-! ### `prop:C3-inv` — the resulting denominator exclusion -/

/-- **The resulting denominator exclusion, reduced-fraction form.**  No
rational with reduced denominator at most `79639646646701375323355774875831053`
equals `S`. -/
theorem totient_series_ne_reduced_fraction_of_small_denominator (p : ℚ)
    (hden : p.den ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (p : ℝ) :=
  tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053
    p hden

/-- The same exclusion written for an explicit quotient `a/q` with
`a ∈ ℤ` and `q ≥ 1`. -/
theorem totient_series_ne_int_div_of_small_denominator (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hle : q ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ) :=
  tsum_totient_div_pow_two_ne_int_div_of_den_le_79639646646701375323355774875831053
    a q hq hle

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_exact_range
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_range_magnitude
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_reduced_fraction_of_small_denominator
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_int_div_of_small_denominator
