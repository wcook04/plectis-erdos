import ErdosProblems.Erdos257.WitnessBlockArithmetic
import ErdosProblems.Erdos257.WitnessBlockReciprocal
import ErdosProblems.Erdos257.PaperCompleteR7.PrimeWeightedDefinitions

/-!
# Canonical prime weights on the arithmetic clause layers

The exact prime-part identity keeps all primes of the witness. On cofactors
congruent to one modulo the union of the clause and witness primes, only the
clause-intersection product remains.
-/

noncomputable section
namespace ErdosProblems.Erdos257
open PaperCompleteR7

theorem primeSetPart_clause_layer (C P : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (k m : ℕ) (hm : m ≠ 0) :
    primeSetPart P (C.prod id ^ k * m) =
      (P ∩ C).prod id ^ k * primeSetPart P m :=
  restricted_prime_part_clause_layer C P hC k m hm

/-- The selected progression avoids every prime in either finite set. -/
theorem clause_progression_coprime (C P : Finset ℕ) (j : ℕ) :
    Nat.Coprime (1 + j * (C ∪ P).prod id) (C.prod id) := by
  have hc : Nat.Coprime (1 + j * (C ∪ P).prod id) ((C ∪ P).prod id) := by simp
  exact hc.of_dvd_right (Finset.prod_dvd_prod_of_subset C (C ∪ P) id Finset.subset_union_left)

/-- Progression points below the cofactor cutoff belong to the actual host. -/
theorem clause_progression_mem (C P : Finset ℕ) (k j : ℕ) (hk : 1 ≤ k)
    (hcut : 1 + j * (C ∪ P).prod id ≤ 2 ^ (C.prod id ^ k)) :
    C.prod id ^ k * (1 + j * (C ∪ P).prod id) ∈ witnessClauseSupport C := by
  exact ⟨k, hk, 1 + j * (C ∪ P).prod id, by omega, hcut,
    clause_progression_coprime C P j, rfl⟩

/-- Arbitrary primes outside the clause disappear on this progression,
without being discarded from the original witness definition. -/
theorem primeSetPart_clause_progression (C P : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (hP : ∀ p ∈ P, Nat.Prime p) (k j : ℕ) :
    primeSetPart P (C.prod id ^ k * (1 + j * (C ∪ P).prod id)) =
      (P ∩ C).prod id ^ k := by
  classical
  rw [primeSetPart_clause_layer C P hC k _ (by omega)]
  suffices primeSetPart P (1 + j * (C ∪ P).prod id) = 1 by rw [this, mul_one]
  apply Finset.prod_eq_one
  intro p hp
  have hU : ∀ q ∈ C ∪ P, Nat.Prime q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hC q hq
    · exact hP q hq
  have hcop : Nat.Coprime (1 + j * (C ∪ P).prod id) ((C ∪ P).prod id) := by simp
  rw [coprime_clause_factorization (C ∪ P) hU _ hcop (Finset.mem_union_right C hp), pow_zero]

/-- Literal evaluation of the canonical weighted summand on the progression
used for the lower estimate. -/
theorem primeWeightedTerm_clause_progression (b : ℕ) (C P : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (hP : ∀ p ∈ P, Nat.Prime p) (k j : ℕ) :
    primeWeightedTerm b P (C.prod id ^ k * (1 + j * (C ∪ P).prod id)) =
      (((P ∩ C).prod id ^ k : ℕ) : ℝ) /
        ((((C.prod id ^ k : ℕ) : ℝ) * ((1 + j * (C ∪ P).prod id : ℕ) : ℝ)) *
          ((b : ℝ) ^ ((P ∩ C).prod id ^ k) - 1)) := by
  simp only [primeWeightedTerm, primeSetPart_clause_progression C P hC hP, Nat.cast_mul]

/-- A witness missing the clause has only a fixed multiple of the ordinary
reciprocal weight on the progression, including when it has outside primes. -/
theorem primeWeightedTerm_clause_progression_of_disjoint (b : ℕ) (C P : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (hP : ∀ p ∈ P, Nat.Prime p)
    (hdis : Disjoint P C) (k j : ℕ) :
    primeWeightedTerm b P (C.prod id ^ k * (1 + j * (C ∪ P).prod id)) =
      (1 / ((b : ℝ) - 1)) *
        (1 / ((C.prod id ^ k * (1 + j * (C ∪ P).prod id) : ℕ) : ℝ)) := by
  rw [primeWeightedTerm_clause_progression b C P hC hP]
  simp only [Finset.disjoint_iff_inter_eq_empty.mp hdis, Finset.prod_empty,
    one_pow, Nat.cast_one, pow_one, Nat.cast_mul]
  ring

/-- A finite prime witness disjoint from the clause has divergent canonical
weighted mass on the actual constructed support. Outside primes in `P` are
allowed and cannot remove this obstruction. -/
theorem not_summable_primeWeightedTerm_witnessClauseSupport_of_disjoint
    (b : ℕ) (hb : 2 ≤ b) (C P : Finset ℕ) (hCn : C.Nonempty)
    (hC : ∀ p ∈ C, Nat.Prime p) (hP : ∀ p ∈ P, Nat.Prime p)
    (hdis : Disjoint P C) :
    ¬ Summable (Set.indicator (witnessClauseSupport C) (primeWeightedTerm b P)) := by
  intro hs
  let Q := (C ∪ P).prod id
  have hU : ∀ q ∈ C ∪ P, Nat.Prime q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hC q hq
    · exact hP q hq
  have hQ : 0 < Q := clause_product_pos (C ∪ P) hU
  have hDQ : C.prod id ∣ Q :=
    Finset.prod_dvd_prod_of_subset C (C ∪ P) id Finset.subset_union_left
  have hi := clauseProgressionPoint_injective C hCn hC Q hQ hDQ
  have hsub := hs.comp_injective hi
  have hscaled : Summable (fun x : clauseProgressionIndex (C.prod id) Q =>
      (1 / ((b : ℝ) - 1)) * (1 / (clauseProgressionPoint (C.prod id) Q x : ℝ))) := by
    apply hsub.congr
    intro x
    rw [Set.indicator_of_mem (clauseProgression_mem C Q hQ hDQ x)]
    exact primeWeightedTerm_clause_progression_of_disjoint b C P hC hP hdis (x.1 + 1) x.2.val
  have hc : (1 / ((b : ℝ) - 1)) ≠ 0 := by
    have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
    apply one_div_ne_zero
    linarith
  exact not_summable_clauseProgression_reciprocal (C.prod id) Q
    (clause_product_pos C hC) hQ ((summable_mul_left_iff hc).mp hscaled)

#print axioms primeSetPart_clause_progression
#print axioms primeWeightedTerm_clause_progression_of_disjoint
#print axioms not_summable_primeWeightedTerm_witnessClauseSupport_of_disjoint

end ErdosProblems.Erdos257
end
