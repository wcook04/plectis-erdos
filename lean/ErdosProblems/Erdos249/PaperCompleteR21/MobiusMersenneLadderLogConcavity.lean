import Erdos249257.SignedQMomentObstruction
import Erdos249257.CertificateKernel
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Paper-form restatements of the three Möbius–Mersenne ladder theorems at
the end of the long paper, for `Θ_r = ∑_{n≥0} μ(n+1)/(2^(n+1)-1)^r`:

* the values at exponents one and two: `Θ_1 = 1/2` and `Θ_2 = S - 1/2`;
* the two-summand Hankel gap
  `(1-3^{-(r+1)})^2 - (1-3^{-r})(1-3^{-(r+2)}) = 4/3^{r+2}`, and the strict
  log-concavity of `1 - 3^{-r}` for every integer `r ≥ 1`;
* strict log-concavity of the full ladder: `Θ_r Θ_{r+2} < Θ_{r+1}^2` for every
  integer `r ≥ 1`, equivalently a negative `2 × 2` Hankel determinant. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.SignedQMomentObstruction

/-! ### The values at exponents one and two -/

/-- **The values at exponents one and two.**  `Θ_1 = 1/2` and
`Θ_2 = S - 1/2`. -/
theorem mobiusMersenneTheta_one_and_two :
    mobiusMersenneTheta 1 = 1 / 2 ∧
      mobiusMersenneTheta 2
        = (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) - 1 / 2 := by
  refine ⟨mobiusMersenneTheta_one, ?_⟩
  rw [mobiusMersenneTheta_two_eq_totient_offset,
    ← tsum_totient_div_pow_two_eq_pnat_half_pow]

/-! ### The first two summands give a positive Hankel gap -/

/-- **The exact two-summand Hankel gap.**
`(1-3^{-(r+1)})^2 - (1-3^{-r})(1-3^{-(r+2)}) = 4/3^{r+2}`. -/
theorem twoAtom_hankel_gap (r : ℕ) :
    (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2
        - (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      = 4 / (3 : ℝ) ^ (r + 2) :=
  mobiusMersenneTwoAtom_hankelGap r

/-- **Consequently `1 - 3^{-r}` is strictly log-concave for every integer
`r ≥ 1`.** -/
theorem twoAtom_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      < (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2 :=
  mobiusMersenneTwoAtom_strict_logConcave r

/-! ### Strict log-concavity for all integer `r ≥ 1` -/

/-- **Strict log-concavity of the full ladder.**  For every integer `r ≥ 1`,
`Θ_r Θ_{r+2} < Θ_{r+1}^2`. -/
theorem theta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
      < mobiusMersenneTheta (r + 1) ^ 2 :=
  mobiusMersenneTheta_strict_logConcave r hr

/-- **Equivalently, the `2 × 2` Hankel determinant is negative.** -/
theorem theta_hankel_det_neg (r : ℕ) (hr : 1 ≤ r) :
    Matrix.det (Matrix.of
        ![![mobiusMersenneTheta r, mobiusMersenneTheta (r + 1)],
          ![mobiusMersenneTheta (r + 1), mobiusMersenneTheta (r + 2)]]) < 0 := by
  rw [Matrix.det_fin_two_of, ← pow_two]
  exact mobiusMersenneTheta_hankel_two_neg r hr

/-- The same statement written out as a difference. -/
theorem theta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
        - mobiusMersenneTheta (r + 1) ^ 2 < 0 :=
  mobiusMersenneTheta_hankel_two_neg r hr

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.mobiusMersenneTheta_one_and_two
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_hankel_gap
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_strict_logConcave
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.theta_strict_logConcave
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_det_neg
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_two_neg
