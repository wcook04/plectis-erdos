import ErdosProblems.Erdos243.PaperCompleteR11.CubicQuarticWindows

/-! The two exact modulo-seven phases in the paper, together with the
sharp one-seventh lower-density obstruction. -/
namespace ErdosProblems.Erdos243.PaperCompleteR20
open ErdosProblems.Erdos243.PaperCompleteR11

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def cubicTwelveProfile (c : ℤ) (n : ℕ) : ℤ :=
  2 * (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) + c

private theorem twelve_binomial_eq_profile (c : ℤ) (n : ℕ) :
    12 * risingBinomial n + c = cubicTwelveProfile c n := by
  unfold cubicTwelveProfile
  linear_combination 2 * six_mul_risingBinomial n

theorem plus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 0 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile 1 (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile 1 n} (1 / 7) := by
  have hcert : CubicQuarticNonresidue (3 : ZMod 7) := by
    unfold CubicQuarticNonresidue cubicLeftOne cubicLeftTwo cubicRightOne
    decide
  have hroot : (12 : ZMod 7) * ((3 : ZMod 7) ^ 3 - 3) + ((6 * 1 : ℤ) : ZMod 7) = 0 := by decide
  constructor
  · intro n hn hphase
    have hphase' : (n : ZMod 7) = 3 - 3 := by simpa using hphase
    simpa only [twelve_binomial_eq_profile] using
      integral_cubic_quartic_window_hit a u v 12 1 T n 7 hn hnum hden
        3 (by decide) hroot hcert hphase'
  · simpa only [twelve_binomial_eq_profile] using
      integral_cubic_quartic_prime_density a u v 12 1 T 7 (by decide) hnum hden
        3 (by decide) hroot hcert

theorem minus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 1 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile (-1) (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile (-1) n} (1 / 7) := by
  have hcert : CubicQuarticNonresidue (4 : ZMod 7) := by
    unfold CubicQuarticNonresidue cubicLeftOne cubicLeftTwo cubicRightOne
    decide
  have hroot : (12 : ZMod 7) * ((4 : ZMod 7) ^ 3 - 4) + ((6 * (-1) : ℤ) : ZMod 7) = 0 := by decide
  constructor
  · intro n hn hphase
    have hphase' : (n : ZMod 7) = 4 - 3 := by simpa using hphase
    simpa only [twelve_binomial_eq_profile] using
      integral_cubic_quartic_window_hit a u v 12 (-1) T n 7 hn hnum hden
        4 (by decide) hroot hcert hphase'
  · simpa only [twelve_binomial_eq_profile] using
      integral_cubic_quartic_prime_density a u v 12 (-1) T 7 (by decide) hnum hden
        4 (by decide) hroot hcert

#print axioms plus_one_forbidden_word
#print axioms minus_one_forbidden_word
end ErdosProblems.Erdos243.PaperCompleteR20
