import Erdos249257.CertificateKernel

/-! The near-integer irrationality criterion of the long #249 manuscript
(`catalogue:cert:d2`): if every `q ≥ 1` admits integers `m, z` with
`0 < |mξ - z| < 1/q`, then `ξ` is irrational; and restricting the multiplier
to the powers of a fixed base is a sufficient special case. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257

/-- **The near-integer criterion** (`catalogue:cert:d2`, first display): both
the strict lower bound (which excludes exact integer hits) and the scaled
upper bound (which must be available for arbitrarily large `q`) are
hypotheses. -/
theorem irrational_of_near_integer_multiples {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ :=
  irrational_of_int_mul_near_int h

/-- **The base-power special case** (`catalogue:cert:d2`, second sentence):
restricting the multiplier to `m = b₀ⁿ` for a fixed integer base `b₀ ≥ 2` is
sufficient. -/
theorem irrational_of_near_integer_base_powers (b₀ : ℕ) (hb : 2 ≤ b₀) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ :=
  irrational_of_pow_mul_near_int b₀ h

#print axioms irrational_of_near_integer_multiples
#print axioms irrational_of_near_integer_base_powers
end ErdosProblems.Erdos249.PaperCompleteR21
