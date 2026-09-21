import ErdosProblems.Erdos249.PaperCompleteR20.NumeratorEvaluation

namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257
open RepunitMobiusNumerator RadicalMobiusShadow
open scoped BigOperators

/-- The subset calculation only needs distinct primes, not squarefreeness
of the ambient index. Recover the original argument on its radical. -/
private theorem moebius_subset (r : ℕ) {s : Finset ℕ}
    (hs : s ⊆ r.primeFactors) :
    ArithmeticFunction.moebius (s.prod id) = (-1 : ℤ) ^ s.card := by
  have hp : ∀ p ∈ s, p.Prime := fun p h => Nat.prime_of_mem_primeFactors (hs h)
  have hdiv : s.prod id ∣ squarefreeKernel r :=
    Finset.prod_dvd_prod_of_subset s r.primeFactors id hs
  have hsf := (squarefreeKernel_squarefree r).squarefree_of_dvd hdiv
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]
  congr 1
  rw [ArithmeticFunction.cardFactors_apply]
  calc
    (s.prod id).primeFactorsList.length = (s.prod id).primeFactors.card :=
      (List.toFinset_card_of_nodup hsf.nodup_primeFactorsList).symm
    _ = s.card := by
      simpa [Function.id_def] using congrArg Finset.card (Nat.primeFactors_prod hp)

/-- Extend the recovered numerator evaluation to every positive index;
non-squarefree divisor terms vanish, rather than being assumed absent. -/
theorem numerator_eval_two_all_positive {r : ℕ} (hr : 0 < r) :
    (mobiusNumeratorPolynomial r).eval 2 = mobiusNumerator r := by
  rw [numerator_eval_two_divisors hr]
  let f : ℕ → ℤ := fun d => ArithmeticFunction.moebius d * (r / d : ℕ) *
    ((mersenne r / mersenne d : ℕ) : ℤ)
  change (∑ d ∈ r.divisors, f d) = mobiusNumerator r
  have hf : (∑ d ∈ r.divisors, f d) = ∑ d ∈ r.divisors.filter Squarefree, f d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hns : ¬ Squarefree d := fun h => hnot (Finset.mem_filter.mpr ⟨hd, h⟩)
    simp [f, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
  rw [hf, Nat.sum_divisors_filter_squarefree hr.ne', Nat.factors_eq]
  unfold mobiusNumerator
  apply Finset.sum_congr rfl
  intro s hs
  rw [s.prod_val]
  dsimp only [f]
  have hm := moebius_subset r (Finset.mem_powerset.mp hs)
  simpa only [Function.id_def] using congrArg
    (fun z : ℤ => z * (r / s.prod id : ℕ) * ((mersenne r / mersenne (s.prod id) : ℕ) : ℤ)) hm

theorem radical_decomposition (H r : ℕ) (hH : 0 < H) (hr : 0 < r) :
    (H : ℚ) * numericMobiusShadow H =
      ((H / squarefreeKernel H : ℕ) : ℚ) * baseMobiusShadow (squarefreeKernel H) ∧
    (baseMobiusShadow r).den = mersenne r /
      ((mobiusNumeratorPolynomial r).eval 2).natAbs.gcd (mersenne r) := by
  exact ⟨scaledMobiusShadow_eq_radicalBase H hH,
    by rw [numerator_eval_two_all_positive hr, baseMobiusShadow_den r hr]⟩

#print axioms numerator_eval_two_all_positive
#print axioms radical_decomposition
end ErdosProblems.Erdos249.PaperCompleteR20
