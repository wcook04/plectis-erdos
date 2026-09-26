import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Arithmetic of the clause support

The support is the actual union of coprime layers used in the witness-rule
construction. Prime factors outside the clause are retained in the exact
restricted factorization identity.
-/

noncomputable section
namespace ErdosProblems.Erdos257

/-- The arithmetic support for one nonempty clause of primes. -/
def witnessClauseSupport (C : Finset ℕ) : Set ℕ :=
  {a | ∃ k : ℕ, 1 ≤ k ∧ ∃ m : ℕ,
    1 ≤ m ∧ m ≤ 2 ^ (C.prod id ^ k) ∧ Nat.Coprime m (C.prod id) ∧
      a = C.prod id ^ k * m}

theorem clause_product_pos (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) :
    0 < C.prod id := Finset.prod_pos fun p hp => (hC p hp).pos

/-- A product over a finite prime set is squarefree, including its valuations
at primes outside that set. -/
theorem clause_product_factorization (C : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (p : ℕ) :
    (C.prod id).factorization p = if p ∈ C then 1 else 0 := by
  classical
  change (∏ q ∈ C, q).factorization p = if p ∈ C then 1 else 0
  rw [Nat.factorization_prod_apply (fun q hq => (hC q hq).ne_zero)]
  calc
    (∑ q ∈ C, (id q).factorization p) = ∑ q ∈ C, if q = p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [(hC q hq).factorization, Finsupp.single_apply, eq_comm]
    _ = if p ∈ C then 1 else 0 := by simp

/-- All clause primes have zero valuation in an allowed cofactor. -/
theorem coprime_clause_factorization (C : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (m : ℕ)
    (hm : Nat.Coprime m (C.prod id)) {p : ℕ} (hp : p ∈ C) :
    m.factorization p = 0 := by
  have hpd : p ∣ C.prod id := Finset.dvd_prod_of_mem id hp
  have hpm : Nat.Coprime p m := (hm.of_dvd_right hpd).symm
  exact Nat.factorization_eq_zero_of_not_dvd ((hC p hp).coprime_iff_not_dvd.mp hpm)

/-- The clause contribution and the complete cofactor contribution are both
present, even when the witness contains primes outside the clause. -/
theorem clause_layer_factorization (C : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (k m p : ℕ) (hm : m ≠ 0) :
    (C.prod id ^ k * m).factorization p =
      k * (if p ∈ C then 1 else 0) + m.factorization p := by
  rw [Nat.factorization_mul (pow_ne_zero _ (clause_product_pos C hC).ne') hm,
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
    smul_eq_mul, clause_product_factorization C hC]

/-- Every clause prime reads off the unique layer index. -/
theorem clause_layer_factorization_of_mem (C : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (k m : ℕ) (hm : m ≠ 0)
    (hcop : Nat.Coprime m (C.prod id)) {p : ℕ} (hp : p ∈ C) :
    (C.prod id ^ k * m).factorization p = k := by
  rw [clause_layer_factorization C hC k m p hm,
    coprime_clause_factorization C hC m hcop hp]
  simp [hp]

/-- Distinct positive coprime layers are disjoint. -/
theorem clause_layer_index_unique (C : Finset ℕ) (hCn : C.Nonempty)
    (hC : ∀ p ∈ C, Nat.Prime p) (k l m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hmc : Nat.Coprime m (C.prod id)) (hnc : Nat.Coprime n (C.prod id))
    (heq : C.prod id ^ k * m = C.prod id ^ l * n) : k = l := by
  obtain ⟨p, hp⟩ := hCn
  have hv := congrArg (fun a : ℕ => a.factorization p) heq
  dsimp only at hv
  rw [clause_layer_factorization_of_mem C hC k m hm hmc hp,
    clause_layer_factorization_of_mem C hC l n hn hnc hp] at hv
  exact hv

/-- The cofactor is unique as well as the layer index. -/
theorem clause_layer_pair_unique (C : Finset ℕ) (hCn : C.Nonempty)
    (hC : ∀ p ∈ C, Nat.Prime p) (k l m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hmc : Nat.Coprime m (C.prod id)) (hnc : Nat.Coprime n (C.prod id))
    (heq : C.prod id ^ k * m = C.prod id ^ l * n) : k = l ∧ m = n := by
  have hkl := clause_layer_index_unique C hCn hC k l m n hm hn hmc hnc heq
  subst l
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (clause_product_pos C hC)) heq⟩

/-- Exact restricted prime-part factorization, for an arbitrary finite
witness set `P`. No restriction `P ⊆ C` is imposed. -/
theorem restricted_prime_part_clause_layer (C P : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (k m : ℕ) (hm : m ≠ 0) :
    (∏ p ∈ P, p ^ (C.prod id ^ k * m).factorization p) =
      (P ∩ C).prod id ^ k * ∏ p ∈ P, p ^ m.factorization p := by
  classical
  simp_rw [clause_layer_factorization C hC k m _ hm, pow_add]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_pow]
  have heq : (P.filter (fun p => p ∈ C)) = P ∩ C := by ext; simp
  rw [← heq, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hc : p ∈ C <;> simp [hc]

#print axioms clause_layer_pair_unique
#print axioms restricted_prime_part_clause_layer

end ErdosProblems.Erdos257
end
