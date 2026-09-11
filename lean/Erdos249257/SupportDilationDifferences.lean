import Erdos249257.BooleanMobiusCarry
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
# Support dilation differences

This file formalises T14's finite algebraic interface.  For
`f_A(n) = #{a ∈ A : a ∣ n}`, the forward dilation difference

`Δ_p f(n) = f(pn) - f(n)`

is the divisor-count coefficient of the pulled-back support
`p⁻¹A = {a | pa ∈ A}` whenever `n` is coprime to `p`.  Iterating along a
pairwise-coprime list gives the corresponding product pullback.  If every
element of `A` has at most `K` prime factors counted with multiplicity, any
pullback by more than `K` primes has zero divisor-count coefficient.

These are exact finite identities.  No correlation estimate, distribution
theorem, or conclusion about the universal Erdős #257 statement is asserted.
-/

open scoped ArithmeticFunction.Omega

namespace Erdos249257.SupportDilationDifferences

/-- Pull a support back through multiplication by `p`. -/
def supportPullback (p : ℕ) (A : Set ℕ) : Set ℕ :=
  {a | p * a ∈ A}

/-- Successive support pullback.  Its membership condition is multiplication
by the product of the listed dilation factors. -/
def iteratedSupportPullback : List ℕ → Set ℕ → Set ℕ
  | [], A => A
  | p :: ps, A => supportPullback p (iteratedSupportPullback ps A)

/-- Integer-valued packaging of the support divisor-count coefficient. -/
noncomputable def supportCoeffInt (A : Set ℕ) (n : ℕ) : ℤ :=
  supportCoeff A n

/-- The forward dilation difference `f(pn)-f(n)`. -/
def dilationDifference (p : ℕ) (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  f (p * n) - f n

/-- Compose dilation differences in list order. -/
def iteratedDilationDifference : List ℕ → (ℕ → ℤ) → ℕ → ℤ
  | [], f => f
  | p :: ps, f => dilationDifference p (iteratedDilationDifference ps f)

@[simp]
theorem mem_supportPullback {p a : ℕ} {A : Set ℕ} :
    a ∈ supportPullback p A ↔ p * a ∈ A := Iff.rfl

@[simp]
theorem mem_iteratedSupportPullback {ps : List ℕ} {a : ℕ} {A : Set ℕ} :
    a ∈ iteratedSupportPullback ps A ↔ ps.prod * a ∈ A := by
  induction ps generalizing a with
  | nil => simp [iteratedSupportPullback]
  | cons p ps ih =>
      change (p * a ∈ iteratedSupportPullback ps A) ↔
        (p :: ps).prod * a ∈ A
      rw [ih (a := p * a)]
      simp only [List.prod_cons]
      constructor <;> intro h
      · simpa [mul_assoc, mul_left_comm] using h
      · simpa [mul_assoc, mul_left_comm] using h

private theorem divisors_mul_prime_split {n p : ℕ}
    (hp : p.Prime) :
    (n * p).divisors =
      n.divisors ∪ n.divisors.image (fun d => d * p) := by
  rw [Nat.divisors_mul, hp.divisors]
  ext d
  simp only [Finset.mem_mul, Finset.mem_union, Nat.mem_divisors,
    Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor <;> aesop

private theorem divisors_disjoint_prime_multiples {n p : ℕ}
    (hp : p.Prime) (hnp : n.Coprime p) :
    Disjoint n.divisors (n.divisors.image fun d => d * p) := by
  rw [Finset.disjoint_left]
  intro d hdn hdp
  obtain ⟨e, hen, rfl⟩ := Finset.mem_image.mp hdp
  have hep_dvd_n : e * p ∣ n := Nat.dvd_of_mem_divisors hdn
  have hp_dvd_n : p ∣ n := (dvd_mul_left p e).trans hep_dvd_n
  exact (hp.coprime_iff_not_dvd.mp hnp.symm) hp_dvd_n

private theorem filtered_prime_multiple_card
    {n p : ℕ} (hp : p.Prime) (A : Set ℕ)
    [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ supportPullback p A)] :
    ((n.divisors.image fun d => d * p).filter fun d => d ∈ A).card =
      (n.divisors.filter fun d => d ∈ supportPullback p A).card := by
  classical
  have heq :
      (n.divisors.image fun d => d * p).filter (fun d => d ∈ A) =
        (n.divisors.filter fun d => d ∈ supportPullback p A).image
          (fun d => d * p) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_image, mem_supportPullback]
    constructor
    · rintro ⟨⟨e, hen, rfl⟩, hepA⟩
      exact ⟨e, ⟨hen, by simpa [Nat.mul_comm] using hepA⟩, rfl⟩
    · rintro ⟨e, ⟨hen, hpeA⟩, rfl⟩
      exact ⟨⟨e, hen, rfl⟩, by simpa [Nat.mul_comm] using hpeA⟩
  rw [heq, Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_right hp.pos hab

/-- The exact one-step divisor split behind T14. -/
theorem supportCoeff_mul_prime
    (A : Set ℕ) {n p : ℕ} (hp : p.Prime) (hnp : n.Coprime p) :
    supportCoeff A (p * n) =
      supportCoeff A n + supportCoeff (supportPullback p A) n := by
  classical
  rw [Nat.mul_comm p n, supportCoeff_eq_card_filter,
    supportCoeff_eq_card_filter, supportCoeff_eq_card_filter,
    divisors_mul_prime_split hp, Finset.filter_union]
  have hdisj : Disjoint
      (n.divisors.filter fun d => d ∈ A)
      ((n.divisors.image fun d => d * p).filter fun d => d ∈ A) :=
    (divisors_disjoint_prime_multiples hp hnp).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [Finset.card_union_of_disjoint hdisj,
    filtered_prime_multiple_card hp A]

/-- A single forward dilation difference is the coefficient of the pulled-back
support at every argument coprime to the prime dilation. -/
theorem dilationDifference_supportCoeffInt
    (A : Set ℕ) {n p : ℕ} (hp : p.Prime) (hnp : n.Coprime p) :
    dilationDifference p (supportCoeffInt A) n =
      supportCoeffInt (supportPullback p A) n := by
  change (supportCoeff A (p * n) : ℤ) - (supportCoeff A n : ℤ) =
    (supportCoeff (supportPullback p A) n : ℤ)
  rw [supportCoeff_mul_prime A hp hnp]
  push_cast
  ring

/-- Distinct primes are pairwise coprime, packaged in the list form consumed
by the iterated dilation theorem. -/
theorem pairwise_coprime_of_nodup_primes
    {ps : List ℕ} (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup) :
    ps.Pairwise Nat.Coprime := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hprimeTail : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hpNotMem : p ∉ ps := (List.nodup_cons.mp hnodup).1
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih hprimeTail (List.nodup_cons.mp hnodup).2⟩
      intro q hq
      exact (Nat.coprime_primes hp (hprimeTail q hq)).mpr fun hpq =>
        hpNotMem (hpq ▸ hq)

/-- T14's iterated identity.  Pairwise coprimality makes every intermediate
argument legal for the next one-step split. -/
theorem iteratedDilationDifference_supportCoeffInt
    (A : Set ℕ) {ps : List ℕ} {n : ℕ}
    (hprime : ∀ p ∈ ps, p.Prime) (hpair : ps.Pairwise Nat.Coprime)
    (hn : n.Coprime ps.prod) :
    iteratedDilationDifference ps (supportCoeffInt A) n =
      supportCoeffInt (iteratedSupportPullback ps A) n := by
  induction ps generalizing A n with
  | nil => simp [iteratedDilationDifference, iteratedSupportPullback]
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have hprimeTail : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hpairTail : ps.Pairwise Nat.Coprime := hpair.tail
      have hpTail : p.Coprime ps.prod :=
        Nat.coprime_list_prod_right_iff.mpr
          (List.pairwise_cons.mp hpair).1
      have hnTail : n.Coprime ps.prod :=
        Nat.Coprime.of_dvd_right (dvd_mul_left ps.prod p) (by simpa using hn)
      have hpnTail : (p * n).Coprime ps.prod := hpTail.mul_left hnTail
      have hnp : n.Coprime p :=
        Nat.Coprime.of_dvd_right (dvd_mul_right p ps.prod) (by simpa using hn)
      rw [iteratedDilationDifference, dilationDifference,
        ih (A := A) hprimeTail hpairTail hpnTail,
        ih (A := A) hprimeTail hpairTail hnTail]
      simpa [dilationDifference, iteratedSupportPullback] using
        (dilationDifference_supportCoeffInt
          (iteratedSupportPullback ps A) hp hnp)

/-- Interface distinct-prime form of the iterated identity. -/
theorem iteratedDilationDifference_supportCoeffInt_of_nodup_primes
    (A : Set ℕ) {ps : List ℕ} {n : ℕ}
    (hprime : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup)
    (hn : n.Coprime ps.prod) :
    iteratedDilationDifference ps (supportCoeffInt A) n =
      supportCoeffInt (iteratedSupportPullback ps A) n :=
  iteratedDilationDifference_supportCoeffInt A hprime
    (pairwise_coprime_of_nodup_primes hprime hnodup) hn

/-- A product of prime dilation factors has exactly one `Ω` contribution per
list entry, including repeated primes. -/
theorem cardFactors_list_prod_of_primes
    {ps : List ℕ} (hprime : ∀ p ∈ ps, p.Prime) :
    ArithmeticFunction.cardFactors ps.prod = ps.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hp : p.Prime := hprime p (by simp)
      have htail : ∀ q ∈ ps, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hprod0 : ps.prod ≠ 0 := by
        apply List.prod_ne_zero
        intro hzero
        exact (htail 0 hzero).ne_zero rfl
      rw [List.prod_cons, ArithmeticFunction.cardFactors_mul hp.ne_zero hprod0,
        ArithmeticFunction.cardFactors_apply_prime hp, ih htail,
        List.length_cons]
      omega

/-- More than `K` prime pullbacks annihilate every divisor coefficient of a
support whose elements have `Ω` at most `K`.  No pairwise-coprimality
hypothesis is needed for this support-side extinction statement. -/
theorem supportCoeff_iteratedSupportPullback_eq_zero_of_cardFactors_le
    (A : Set ℕ) {ps : List ℕ} {K n : ℕ}
    (hprime : ∀ p ∈ ps, p.Prime)
    (hbound : ∀ a ∈ A, ArithmeticFunction.cardFactors a ≤ K)
    (hlen : K < ps.length) :
    supportCoeff (iteratedSupportPullback ps A) n = 0 := by
  classical
  rw [supportCoeff_eq_card_filter, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro d hdn hdPull
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hdn
  have hprod0 : ps.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hprime 0 hzero).ne_zero rfl
  have hmemA : ps.prod * d ∈ A :=
    mem_iteratedSupportPullback.mp hdPull
  have hΩ := hbound (ps.prod * d) hmemA
  have hprodΩ := cardFactors_list_prod_of_primes hprime
  rw [ArithmeticFunction.cardFactors_mul hprod0 hdpos.ne', hprodΩ] at hΩ
  omega

/-- The finite bounded-`Ω` annihilation theorem: a pairwise-coprime
prime list longer than the support's `Ω` ceiling makes the actual iterated
dilation difference vanish at arguments coprime to its product. -/
theorem iteratedDilationDifference_eq_zero_of_cardFactors_le
    (A : Set ℕ) {ps : List ℕ} {K n : ℕ}
    (hprime : ∀ p ∈ ps, p.Prime) (hpair : ps.Pairwise Nat.Coprime)
    (hn : n.Coprime ps.prod)
    (hbound : ∀ a ∈ A, ArithmeticFunction.cardFactors a ≤ K)
    (hlen : K < ps.length) :
    iteratedDilationDifference ps (supportCoeffInt A) n = 0 := by
  rw [iteratedDilationDifference_supportCoeffInt A hprime hpair hn,
    supportCoeffInt,
    supportCoeff_iteratedSupportPullback_eq_zero_of_cardFactors_le
      A hprime hbound hlen]
  norm_num

/-! Kernel fixtures: one difference extracts multiples of `2`, while two
pairwise-coprime prime differences annihilate the support `{2,3}` because its
elements have `Ω = 1`. -/

def supportTwoThree : Set ℕ := Erdos249257.support23

theorem dilationDifference_supportTwoThree_fixture :
    dilationDifference 2 (supportCoeffInt supportTwoThree) 3 = 1 := by
  change (supportCoeff Erdos249257.support23 6 : ℤ) -
    supportCoeff Erdos249257.support23 3 = 1
  rw [Erdos249257.supportCoeff_support23_eq_residue
      (n := 6) (by norm_num),
    Erdos249257.supportCoeff_support23_eq_residue
      (n := 3) (by norm_num)]
  norm_num [Erdos249257.supportCoeff23Residue]

theorem iteratedDilationDifference_supportTwoThree_fixture :
    iteratedDilationDifference [2, 3]
      (supportCoeffInt supportTwoThree) 5 = 0 := by
  apply iteratedDilationDifference_eq_zero_of_cardFactors_le
    supportTwoThree (K := 1)
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl <;> norm_num
  · decide
  · norm_num
  · intro a ha
    simp [supportTwoThree] at ha
    rcases ha with rfl | rfl <;> norm_num
  · norm_num

#print axioms dilationDifference_supportCoeffInt
#print axioms pairwise_coprime_of_nodup_primes
#print axioms iteratedDilationDifference_supportCoeffInt
#print axioms iteratedDilationDifference_supportCoeffInt_of_nodup_primes
#print axioms cardFactors_list_prod_of_primes
#print axioms supportCoeff_iteratedSupportPullback_eq_zero_of_cardFactors_le
#print axioms iteratedDilationDifference_eq_zero_of_cardFactors_le
#print axioms dilationDifference_supportTwoThree_fixture
#print axioms iteratedDilationDifference_supportTwoThree_fixture

end Erdos249257.SupportDilationDifferences
