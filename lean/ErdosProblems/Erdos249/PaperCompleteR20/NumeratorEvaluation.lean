import Erdos249257.RepunitMobiusNumerator

/-! The manuscript's literal divisor-sum numerator evaluation.
The geometric evaluation proof is recovered from RepunitMobiusNumerator's
private lemma; the upstream checked module is kept unchanged. -/
namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257 Erdos249257.RepunitMobiusNumerator
open scoped BigOperators

private theorem eval_spacedRepunit_two {r d : ℕ}
    (hr : 0 < r) (hd : d ∣ r) :
    (spacedRepunit d (r / d)).eval 2 =
      (((RadicalMobiusShadow.mersenne r /
          RadicalMobiusShadow.mersenne d : ℕ) : ℤ)) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hr
  have htwo : 2 ≤ 2 ^ d := by
    have := Nat.one_lt_two_pow hdpos.ne'
    omega
  have hp : (2 ^ d) ^ (r / d) = 2 ^ r := by
    rw [← pow_mul, Nat.mul_div_cancel' hd]
  have hnat :
      ∑ j ∈ Finset.range (r / d), 2 ^ (d * j) =
        RadicalMobiusShadow.mersenne r /
          RadicalMobiusShadow.mersenne d := by
    simp_rw [pow_mul]
    rw [Nat.geomSum_eq htwo, hp]
    rfl
  rw [spacedRepunit, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial, one_mul]
  exact_mod_cast hnat

theorem numerator_eval_two_divisors {r : ℕ} (hr : 0 < r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      ∑ d ∈ r.divisors,
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) *
          (((RadicalMobiusShadow.mersenne r /
            RadicalMobiusShadow.mersenne d : ℕ) : ℤ)) := by
  rw [mobiusNumeratorPolynomial, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Polynomial.eval_C_mul, eval_spacedRepunit_two hr (Nat.dvd_of_mem_divisors hd)]

#print axioms numerator_eval_two_divisors
end ErdosProblems.Erdos249.PaperCompleteR20
