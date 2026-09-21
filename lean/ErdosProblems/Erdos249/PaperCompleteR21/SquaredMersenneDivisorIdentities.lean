import Erdos249257.GcdMomentCalculus

/-! Paper-form restatements of the squared-Mersenne divisor identities of the
long #249 manuscript: the divisor-sum identity, the gcd-moment identity, and
the pair-divisibility mass that produces the squared denominator.  The
coefficients are spelled by their standard names -- `σ`, `τ` and Pillai's `P`
-- rather than by the ladder's internal divisor sums. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open GcdMomentCalculus
open scoped BigOperators

/-- Pillai's gcd-sum function, transcribed from the manuscript's definition
`P(n) = ∑_{e ∣ n} φ(e)·(n/e) = (φ * Id)(n)`. -/
def pillaiGcdSum (n : ℕ) : ℕ := ∑ e ∈ n.divisors, Nat.totient e * (n / e)

private lemma sigma_one_cast (n : ℕ) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) = ∑ e ∈ n.divisors, (((n / e : ℕ) : ℝ)) := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum,
    Nat.sum_div_divisors n (fun d => (d : ℝ))]

private lemma sigma_zero_cast (n : ℕ) :
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) = ((n.divisors.card : ℕ) : ℝ) := by
  rw [ArithmeticFunction.sigma_zero_apply]

private lemma pillai_cast (n : ℕ) :
    ((pillaiGcdSum n : ℕ) : ℝ)
      = ∑ e ∈ n.divisors, (Nat.totient e : ℝ) * (((n / e : ℕ) : ℝ)) := by
  rw [pillaiGcdSum, Nat.cast_sum]
  exact Finset.sum_congr rfl fun e _ => by push_cast; ring

/-- **The divisor-sum identity** (`prop:zetaq`, `catalogue:mob:a4`):
`∑_{d≥1} 1/(2ᵈ-1)² = ∑_{n≥1} (σ(n) - τ(n))·(1/2)ⁿ`, with `σ` the
sum-of-divisors function and `τ` the number-of-divisors function. -/
theorem divisor_sum_identity :
    ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          (((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℝ)
            - ((ArithmeticFunction.sigma 0 (n : ℕ) : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  rw [tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series]
  refine tsum_congr fun n => ?_
  rw [sigma_one_cast, sigma_zero_cast]

/-- **The gcd-moment identity** (`prop:pillai`, `catalogue:mob:a5`):
`∑_{d≥1} φ(d)/(2ᵈ-1)² = ∑_{n≥1} (P(n) - n)·(1/2)ⁿ` with `P = φ * Id`
Pillai's gcd-sum function. -/
theorem gcd_moment_identity :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          (((pillaiGcdSum (n : ℕ) : ℕ) : ℝ) - ((n : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  rw [tsum_totient_div_mersenne_sq_eq_gcd_moment_series]
  refine tsum_congr fun n => ?_
  rw [pillai_cast]

/-- **The weight of pairs divisible by a fixed integer** (`catalogue:mob:a7`):
for independent fair-coin waiting times `X, Y` with `P(X = n) = P(Y = n) = 2⁻ⁿ`
on `n ≥ 1`, and every `d ≥ 1`,
`P(d ∣ X and d ∣ Y) = 1/(2ᵈ-1)²`. -/
theorem pair_divisibility_mass (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2 :=
  tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq d hd

private lemma tsum_pow_succ_of_lt_one' {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑' j : ℕ, x ^ (j + 1) = x / (1 - x) := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  rw [div_eq_mul_inv, ← tsum_geometric_of_norm_lt_one hnorm, ← tsum_mul_left]
  exact tsum_congr fun j => pow_succ' x j

/-- **The one-variable geometric sum** (`catalogue:mob:a7`, second sentence):
`∑_{k≥1} 2^{-dk} = 1/(2ᵈ-1)`; the squared denominator is the product of two
copies of it. -/
theorem tsum_geometric_multiples (d : ℕ) (hd : 0 < d) :
    ∑' k : ℕ, ((1 : ℝ) / 2) ^ (d * (k + 1)) = 1 / ((2 : ℝ) ^ d - 1) := by
  have hx0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ d := by positivity
  have hx1 : ((1 : ℝ) / 2) ^ d < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hd.ne'
  have hpos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have hpow : ((1 : ℝ) / 2) ^ d = 1 / (2 : ℝ) ^ d := by rw [div_pow, one_pow]
  have hden : (1 : ℝ) - ((1 : ℝ) / 2) ^ d = ((2 : ℝ) ^ d - 1) / (2 : ℝ) ^ d := by
    rw [hpow]
    field_simp
  calc ∑' k : ℕ, ((1 : ℝ) / 2) ^ (d * (k + 1))
      = ∑' k : ℕ, (((1 : ℝ) / 2) ^ d) ^ (k + 1) :=
        tsum_congr fun k => by rw [← pow_mul]
    _ = ((1 : ℝ) / 2) ^ d / (1 - ((1 : ℝ) / 2) ^ d) := tsum_pow_succ_of_lt_one' hx0 hx1
    _ = 1 / ((2 : ℝ) ^ d - 1) := by
        rw [hden, hpow, div_div_eq_mul_div, one_div_mul_cancel (ne_of_gt hpos)]

/-- **Replacing the weight `1` by `μ`** (`catalogue:mob:a4`, fourth
sentence): the value becomes `S - 1/2`, the constant of the Möbius-square
definition. -/
theorem moebius_weight_value :
    ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
        / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)) - 1 / 2 := by
  rw [MersenneLambertLadder.tsum_totient_half_pow_eq_half_add_moebius_sq]
  ring

#print axioms tsum_geometric_multiples
#print axioms moebius_weight_value
#print axioms divisor_sum_identity
#print axioms gcd_moment_identity
#print axioms pair_divisibility_mass
end ErdosProblems.Erdos249.PaperCompleteR21
