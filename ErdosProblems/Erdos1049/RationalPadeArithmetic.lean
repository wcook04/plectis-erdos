import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős #1049: finite arithmetic for rational Padé homogenisation

This module isolates the polynomial denominator-exponent calculations in the
rational-base Padé packet.  Every exponent is doubled, so the statements live
over `ℤ` and contain no floor or parity bookkeeping.  They certify only the
finite homogenisation arithmetic; positivity of the Padé remainder and its
asymptotics remain separate analytic obligations.
-/

namespace ErdosProblems.Erdos1049

/-- Twice the proposed common denominator exponent
`Eₙ = (3n² - n) / 2`. -/
def rationalPadeDenExpTwice (n : ℤ) : ℤ :=
  3 * n * n - n

/-- Twice the denominator exponent of the `k`-th summand in the homogenised
little-`q` Legendre `P` polynomial. -/
def rationalPadePSummandDenExpTwice (n k : ℤ) : ℤ :=
  2 * (k * (n - k) + n * k) + k * (k - 1)

/-- The doubled `P`-summand exponent never exceeds the proposed common
exponent when `0 ≤ k ≤ n`.  The gap factors as
`(n-k)(3n-k-1)`. -/
theorem rationalPadePSummandDenExpTwice_le
    {n k : ℤ} (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k ≤ n) :
    rationalPadePSummandDenExpTwice n k ≤ rationalPadeDenExpTwice n := by
  by_cases hn0 : n = 0
  · have hk0 : k = 0 := by omega
    simp [rationalPadePSummandDenExpTwice, rationalPadeDenExpTwice, hn0, hk0]
  · have hn1 : 1 ≤ n := by omega
    have hleft : 0 ≤ n - k := sub_nonneg.mpr hkn
    have hright : 0 ≤ 3 * n - k - 1 := by nlinarith
    have hprod : 0 ≤ (n - k) * (3 * n - k - 1) :=
      mul_nonneg hleft hright
    unfold rationalPadePSummandDenExpTwice rationalPadeDenExpTwice
    nlinarith

/-- Twice the maximal denominator exponent in the `Q`-summand calculation,
after the change of variables `j = n - m - 1`. -/
def rationalPadeQMaxDenExpTwice (n m : ℤ) : ℤ :=
  let j := n - m - 1
  2 * (n * n - n) + j * j + 2 * j * m + j - m * m + 3 * m

/-- Exact doubled gap identity for the rational `Q`-summand maximum:
`2(Eₙ-Fmax) = 2(n + m(m-1))`. -/
theorem rationalPadeQMaxDenExpTwice_gap (n m : ℤ) :
    rationalPadeDenExpTwice n - rationalPadeQMaxDenExpTwice n m =
      2 * (n + m * (m - 1)) := by
  simp [rationalPadeDenExpTwice, rationalPadeQMaxDenExpTwice]
  ring

/-- In the nonvanishing `m ≥ 1` range, the doubled `Q` exponent is bounded
by the same common exponent. -/
theorem rationalPadeQMaxDenExpTwice_le
    {n m : ℤ} (hn : 0 ≤ n) (hm : 1 ≤ m) :
    rationalPadeQMaxDenExpTwice n m ≤ rationalPadeDenExpTwice n := by
  have hm0 : 0 ≤ m := by omega
  have hmm1 : 0 ≤ m - 1 := by omega
  have hprod : 0 ≤ m * (m - 1) := mul_nonneg hm0 hmm1
  have hgap := rationalPadeQMaxDenExpTwice_gap n m
  nlinarith

end ErdosProblems.Erdos1049
