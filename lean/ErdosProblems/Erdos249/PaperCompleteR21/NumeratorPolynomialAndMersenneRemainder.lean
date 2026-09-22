import Erdos249257.DyadicPrefixCompression
import Erdos249257.GreedyAchievementSet
import Erdos249257.RepunitMobiusNumerator

/-! Paper-form restatements of the long paper's repunit numerator polynomial
and of the exact dyadic remainder bounds:

* *Positive coefficients of the numerator polynomial* — the explicit gcd-word
  form, its positivity below `r`, its vanishing above, and the divisor-sum
  value of one coefficient;
* the corollary evaluating the numerator at `X = 2`, with the integrality of
  each repunit quotient;
* *The geometric remainder bound* — the exact third-channel identity, the
  `4/3` pointwise majorant and the `4/21` tail bound. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open scoped BigOperators Polynomial
open Erdos249257
open Erdos249257.RepunitMobiusNumerator

/-! ### The numerator polynomial -/

private theorem sumGcdDivisorsScaled {g H : ℕ} (hH : 0 < H) (hgH : g ∣ H) :
    ∑ d ∈ g.divisors, ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ) =
      ((H / g : ℕ) : ℤ) * (Nat.totient g : ℤ) := by
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgH hH
  calc
    ∑ d ∈ g.divisors, ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ)
        = ∑ d ∈ g.divisors,
            ((H / g : ℕ) : ℤ) *
              (ArithmeticFunction.moebius d * ((g / d : ℕ) : ℤ)) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          have hdg : d ∣ g := Nat.dvd_of_mem_divisors hd
          rw [← Nat.div_mul_div hgH hdg, Nat.cast_mul]
          ring
    _ = ((H / g : ℕ) : ℤ) *
          ∑ d ∈ g.divisors,
            ArithmeticFunction.moebius d * ((g / d : ℕ) : ℤ) := by
          rw [Finset.mul_sum]
    _ = ((H / g : ℕ) : ℤ) * (Nat.totient g : ℤ) := by
          rw [MersenneLambertLadder.sum_divisors_moebius_mul_div g hgpos]

/-- The paper's numerator polynomial `∑_{d ∣ r} μ(d)(r/d) ∑_{j<r/d} X^{dj}`. -/
noncomputable def paperNumeratorPolynomial (r : ℕ) : Polynomial ℤ :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ)) *
      ∑ j ∈ Finset.range (r / d), (Polynomial.X : Polynomial ℤ) ^ (d * j)

private theorem spacedRepunit_eq_sum_pow (d q : ℕ) :
    spacedRepunit d q = ∑ j ∈ Finset.range q, (Polynomial.X : Polynomial ℤ) ^ (d * j) := by
  rw [spacedRepunit]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.X_pow_eq_monomial]

theorem paperNumeratorPolynomial_eq (r : ℕ) :
    paperNumeratorPolynomial r = mobiusNumeratorPolynomial r := by
  rw [paperNumeratorPolynomial, mobiusNumeratorPolynomial]
  refine Finset.sum_congr rfl ?_
  intro d _
  rw [spacedRepunit_eq_sum_pow]

/-- **Positive coefficients of the numerator polynomial** — the explicit
gcd-word expression `∑_{d ∣ r} μ(d)(r/d) ∑_{j<r/d} X^{dj} =
∑_{k<r} (r/gcd(r,k)) φ(gcd(r,k)) X^k` for squarefree `r`. -/
theorem paperNumerator_eq_gcdWordForm {r : ℕ} (hr : Squarefree r) :
    paperNumeratorPolynomial r =
      ∑ k ∈ Finset.range r,
        Polynomial.C (((r / Nat.gcd r k) * Nat.totient (Nat.gcd r k) : ℕ) : ℤ) *
          (Polynomial.X : Polynomial ℤ) ^ k := by
  ext m
  rw [paperNumeratorPolynomial_eq, mobiusNumeratorPolynomial_coeff hr,
    Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  by_cases hm : m < r
  · rw [if_pos hm, if_pos hm, gcdWordCoeff]
  · rw [if_neg hm, if_neg hm]

/-- Every coefficient below `r` is positive. -/
theorem paperNumerator_coeff_pos {r k : ℕ} (hr : Squarefree r) (hk : k < r) :
    0 < (paperNumeratorPolynomial r).coeff k := by
  rw [paperNumeratorPolynomial_eq]
  exact mobiusNumeratorPolynomial_coeff_pos hr hk

/-- Every coefficient at or above `r` is zero. -/
theorem paperNumerator_coeff_eq_zero {r k : ℕ} (hr : Squarefree r) (hk : r ≤ k) :
    (paperNumeratorPolynomial r).coeff k = 0 := by
  rw [paperNumeratorPolynomial_eq, mobiusNumeratorPolynomial_coeff hr,
    if_neg (by omega)]

/-- Extracting `X^k` on the left gives `∑_{d ∣ gcd(r,k)} μ(d) r/d`. -/
theorem paperNumerator_coeff_eq_gcd_divisor_sum {r k : ℕ} (hr : Squarefree r)
    (hk : k < r) :
    (paperNumeratorPolynomial r).coeff k =
      ∑ d ∈ (Nat.gcd r k).divisors,
        ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ) := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  rw [paperNumeratorPolynomial_eq, mobiusNumeratorPolynomial_coeff hr, if_pos hk,
    gcdWordCoeff, sumGcdDivisorsScaled hrpos (Nat.gcd_dvd_left r k)]
  push_cast
  ring

/-- Each quotient `(2^r-1)/(2^d-1)` is an integer because `d ∣ r`. -/
theorem mersenne_dvd_of_dvd {d r : ℕ} (hd : d ∣ r) :
    (2 ^ d - 1 : ℕ) ∣ (2 ^ r - 1 : ℕ) :=
  Nat.pow_sub_one_dvd_pow_sub_one 2 hd

/-- **Evaluation at `X = 2`** gives `∑_{d ∣ r} μ(d)(r/d)(2^r-1)/(2^d-1)`. -/
theorem paperNumerator_eval_two {r : ℕ} (_hr : Squarefree r) :
    (((paperNumeratorPolynomial r).eval 2 : ℤ) : ℚ) =
      ∑ d ∈ r.divisors,
        (ArithmeticFunction.moebius d : ℚ) * ((r / d : ℕ) : ℚ) *
          (((2 : ℚ) ^ r - 1) / ((2 : ℚ) ^ d - 1)) := by
  have heval : ∀ d ∈ r.divisors,
      ((Polynomial.C (ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ)) *
          ∑ j ∈ Finset.range (r / d), (Polynomial.X : Polynomial ℤ) ^ (d * j)).eval 2) =
        ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ) *
          ∑ j ∈ Finset.range (r / d), ((2 : ℤ) ^ d) ^ j := by
    intro d _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finset_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Polynomial.eval_pow, Polynomial.eval_X, pow_mul]
  rw [paperNumeratorPolynomial, Polynomial.eval_finset_sum,
    Finset.sum_congr rfl heval]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
  have hone : ((2 : ℚ) ^ d) ≠ 1 :=
    ne_of_gt (one_lt_pow₀ (by norm_num) hdpos.ne')
  have hgeom : ∑ j ∈ Finset.range (r / d), ((2 : ℚ) ^ d) ^ j =
      ((2 : ℚ) ^ r - 1) / ((2 : ℚ) ^ d - 1) := by
    rw [geom_sum_eq hone, ← pow_mul, Nat.mul_div_cancel' hdr]
  have hdivcast : (((r : ℤ) / (d : ℤ) : ℤ) : ℚ) = ((r / d : ℕ) : ℚ) := by
    norm_cast
  rw [hdivcast, hgeom]

/-- The squarefree assumption identifies the divisor sum with the
subset-of-primes form of the formal source. -/
theorem paperNumerator_eval_two_primeSubsetForm {r : ℕ} (hr : Squarefree r) :
    (paperNumeratorPolynomial r).eval 2 =
      ∑ s ∈ r.primeFactors.powerset,
        (-1 : ℤ) ^ s.card * ((r / s.prod id : ℕ) : ℤ) *
          ((((2 ^ r - 1) / (2 ^ s.prod id - 1) : ℕ)) : ℤ) := by
  rw [paperNumeratorPolynomial_eq, mobiusNumeratorPolynomial_eval_two hr]
  simp only [RadicalMobiusShadow.mobiusNumerator, RadicalMobiusShadow.mersenne]

/-! ### The geometric remainder bound -/

/-- `1 - 2^{-n} ≥ 3/4` for `n ≥ 2`. -/
theorem one_sub_half_pow_ge {n : ℕ} (hn : 2 ≤ n) :
    (3 : ℝ) / 4 ≤ 1 - ((1 : ℝ) / 2) ^ n := by
  have h : ((1 : ℝ) / 2) ^ n ≤ ((1 : ℝ) / 2) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h2 : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
  rw [h2] at h
  linarith

/-- **The geometric remainder bound**, pointwise: for `n ≥ 2`,
`1/(2^n-1) - 2^{-n} - 4^{-n} = 8^{-n}/(1-2^{-n}) ≤ (4/3)·8^{-n}`. -/
theorem mersenneRemainder_identity_and_bound {n : ℕ} (hn : 2 ≤ n) :
    1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n =
        ((1 : ℝ) / 8) ^ n / (1 - ((1 : ℝ) / 2) ^ n) ∧
      1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n ≤
        (4 / 3 : ℝ) * ((1 : ℝ) / 8) ^ n := by
  have hid := mersenneWeight_eq_two_channels_add_remainder (n := n) (by omega)
  rw [mersenneWeight] at hid
  have hfirst :
      1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n =
        mersenneWeightRemainder n := by linarith
  refine ⟨?_, ?_⟩
  · rw [hfirst, mersenneWeightRemainder]
  · rw [hfirst]
    exact mersenneWeightRemainder_le_four_thirds hn

/-- `∑_{n>m} 8^{-n} = (1/7)·8^{-m}`. -/
theorem tsum_eighth_pow_tail (m : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) = (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ m := by
  have hgeo : ∑' k : ℕ, ((1 : ℝ) / 8) ^ k = 8 / 7 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  calc
    ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1)
        = ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + 1) * ((1 : ℝ) / 8) ^ k := by
          refine tsum_congr ?_
          intro k
          rw [← pow_add, show m + 1 + k = m + k + 1 by omega]
    _ = ((1 : ℝ) / 8) ^ (m + 1) * ∑' k : ℕ, ((1 : ℝ) / 8) ^ k := tsum_mul_left
    _ = (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ m := by
          rw [hgeo, pow_succ]
          ring

/-- `(4/3)∑_{n>m} 8^{-n} = (4/21)·8^{-m}`, the middle equality of the paper's
summed bound. -/
theorem four_thirds_tsum_eighth_pow_tail (m : ℕ) :
    (4 / 3 : ℝ) * ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) =
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := by
  rw [tsum_eighth_pow_tail]
  ring

/-- **The geometric remainder bound**, summed: for an integer `m ≥ 1`,
`∑_{n>m}(1/(2^n-1) - 2^{-n} - 4^{-n}) ≤ (4/21)·8^{-m}`. -/
theorem mersenneRemainderTail_le {m : ℕ} (hm : 0 < m) :
    ∑' k : ℕ,
        (1 / ((2 : ℝ) ^ (m + k + 1) - 1) - ((1 : ℝ) / 2) ^ (m + k + 1) -
          ((1 : ℝ) / 4) ^ (m + k + 1)) ≤
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := by
  have hcongr : ∀ k : ℕ,
      1 / ((2 : ℝ) ^ (m + k + 1) - 1) - ((1 : ℝ) / 2) ^ (m + k + 1) -
          ((1 : ℝ) / 4) ^ (m + k + 1) = mersenneWeightRemainder (m + k + 1) := by
    intro k
    have hid := mersenneWeight_eq_two_channels_add_remainder (n := m + k + 1) (by omega)
    rw [mersenneWeight] at hid
    linarith
  have hkey :
      ∑' k : ℕ, mersenneWeightRemainder (m + k + 1) ≤
        (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := by
    have h := mersenneWeightRemainderTail_le_four_twentyone hm
    rw [mersenneWeightRemainderTail] at h
    exact h
  calc
    ∑' k : ℕ,
        (1 / ((2 : ℝ) ^ (m + k + 1) - 1) - ((1 : ℝ) / 2) ^ (m + k + 1) -
          ((1 : ℝ) / 4) ^ (m + k + 1))
        = ∑' k : ℕ, mersenneWeightRemainder (m + k + 1) := tsum_congr hcongr
    _ ≤ (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m := hkey

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperNumeratorPolynomial_eq
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eq_gcdWordForm
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_pos
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_zero
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_gcd_divisor_sum
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.mersenne_dvd_of_dvd
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two_primeSubsetForm
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.four_thirds_tsum_eighth_pow_tail
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.one_sub_half_pow_ge
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainder_identity_and_bound
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.tsum_eighth_pow_tail
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainderTail_le
