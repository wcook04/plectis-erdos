import ErdosProblems.Erdos257.PaperCompleteR8.PrimeHarmonicBlocks
import ErdosProblems.Erdos257.PaperCompleteR8.DivisorCubeMoments

/-!
# Fresh prime rows with reciprocal mass between one and four thirds

This supplies the actual bounded-mass row selection in the short paper.
At each finite stage choose a new odd prime q >= 4^(j+1), then a finite
set of fresh odd primes whose product of (1+1/p) first crosses q.
Every factor is at most 4/3, so the overshoot is strictly below 4q/3.
The recursion excludes the entire earlier alphabet, including every q.

These are constructed arithmetic data, not cover or irrationality hypotheses.
BoundedMassCoverBudget proves summability of their indexed cover costs;
BoundedMassHostSeparation proves reciprocal divergence and exclusion of every
finite-prime weighted criterion for the same union of divisor rows.
-/
noncomputable section
open scoped Classical
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset

theorem one_add_primeMass_le_product (P : Finset ℕ) :
    1 + (∑ p ∈ P, (1 : ℝ) / p) ≤ ∏ p ∈ P, (1 + (1 : ℝ) / p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [sum_insert hp, prod_insert hp]
    have hx : 0 ≤ (1 : ℝ) / p := by positivity
    have hS : 0 ≤ ∑ r ∈ P, (1 : ℝ) / r := sum_nonneg (fun r _ => by positivity)
    have hcross := mul_nonneg hx hS
    have hm := mul_le_mul_of_nonneg_left ih (by positivity : 0 ≤ 1 + (1 : ℝ) / p)
    nlinarith

/-- A finite multiplicative threshold crossing has at most one factor's
overshoot. The lower threshold exceeds the empty product. -/
theorem exists_subset_product_window (S : Finset ℕ) (f : ℕ → ℝ) (R : ℝ)
    (hR : 1 < R) (hf : ∀ p ∈ S, 0 < f p ∧ f p ≤ 4 / 3)
    (hS : R ≤ ∏ p ∈ S, f p) :
    ∃ P ⊆ S, R ≤ ∏ p ∈ P, f p ∧ (∏ p ∈ P, f p) < (4 / 3) * R := by
  revert hf hS
  induction S using Finset.induction_on with
  | empty =>
    intro hf hS
    simp only [prod_empty] at hS
    linarith
  | @insert p S hp ih =>
    intro hf hS
    by_cases ht : R ≤ ∏ r ∈ S, f r
    · obtain ⟨P, hPS, hlo, hhi⟩ := ih (fun r hr => hf r (mem_insert_of_mem hr)) ht
      exact ⟨P, hPS.trans (subset_insert p S), hlo, hhi⟩
    · refine ⟨insert p S, subset_rfl, hS, ?_⟩
      rw [prod_insert hp]
      have hp' := hf p (mem_insert_self _ _)
      exact (mul_lt_mul_of_pos_left (lt_of_not_ge ht) hp'.1).trans_le
        (mul_le_mul_of_nonneg_right hp'.2 (by linarith))

/-- Product windows survive deletion of any finite set of integers. -/
theorem exists_odd_prime_product_block (B : Finset ℕ) (R : ℝ) (hR : 1 < R) :
    ∃ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p ∧ 2 < p ∧ p ∉ B) ∧
      R ≤ ∏ p ∈ P, (1 + (1 : ℝ) / p) ∧
      (∏ p ∈ P, (1 + (1 : ℝ) / p)) < (4 / 3) * R := by
  obtain ⟨S, hS, hmass, _⟩ := exists_odd_prime_harmonic_block B R (by linarith)
  have hprod : R ≤ ∏ p ∈ S, (1 + (1 : ℝ) / p) := by
    have h := one_add_primeMass_le_product S
    linarith
  have hfactor : ∀ p ∈ S, 0 < 1 + (1 : ℝ) / p ∧ 1 + (1 : ℝ) / p ≤ 4 / 3 := by
    intro p hp
    have hpN : 3 ≤ p := by have h := (hS p hp).2.1; omega
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hpN
    have hinv : (1 : ℝ) / p ≤ 1 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
    exact ⟨by positivity, by linarith⟩
  obtain ⟨P, hPS, hlo, hhi⟩ := exists_subset_product_window S
    (fun p => 1 + (1 : ℝ) / p) R hR hfactor hprod
  exact ⟨P, fun p hp => hS p (hPS hp), hlo, hhi⟩

/-- One row avoids precisely the finite alphabet already used. -/
structure BoundedMassPrimeRow (j : ℕ) (B : Finset ℕ) where
  q : ℕ
  q_prime : Nat.Prime q
  q_odd : 2 < q
  q_large : 4 ^ (j + 1) ≤ q
  q_fresh : q ∉ B
  primes : Finset ℕ
  primes_spec : ∀ p ∈ primes, Nat.Prime p ∧ 2 < p ∧ p ∉ insert q B
  product_lower : (q : ℝ) ≤ ∏ p ∈ primes, (1 + (1 : ℝ) / p)
  product_upper : (∏ p ∈ primes, (1 + (1 : ℝ) / p)) < (4 / 3) * q

theorem exists_boundedMassPrimeRow (j : ℕ) (B : Finset ℕ) :
    Nonempty (BoundedMassPrimeRow j B) := by
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes
    (max (4 ^ (j + 1)) (B.sup id + 3))
  have hlarge : 4 ^ (j + 1) ≤ q := (le_max_left _ _).trans hq
  have hsup : B.sup id + 3 ≤ q := (le_max_right _ _).trans hq
  have hodd : 2 < q := by omega
  have hfresh : q ∉ B := by
    intro hmem
    have hle : q ≤ B.sup id := Finset.le_sup (f := id) hmem
    omega
  have hqR : (1 : ℝ) < q := by exact_mod_cast hprime.one_lt
  obtain ⟨P, hP, hlo, hhi⟩ := exists_odd_prime_product_block (insert q B) q hqR
  exact ⟨⟨q, hprime, hodd, hlarge, hfresh, P, hP, hlo, hhi⟩⟩

def chosenBoundedMassPrimeRow (j : ℕ) (B : Finset ℕ) : BoundedMassPrimeRow j B :=
  Classical.choice (exists_boundedMassPrimeRow j B)

def boundedMassForbidden : ℕ → Finset ℕ
  | 0 => ∅
  | j + 1 => boundedMassForbidden j ∪
      insert (chosenBoundedMassPrimeRow j (boundedMassForbidden j)).q
        (chosenBoundedMassPrimeRow j (boundedMassForbidden j)).primes

def boundedMassPrimeRow (j : ℕ) : BoundedMassPrimeRow j (boundedMassForbidden j) :=
  chosenBoundedMassPrimeRow j (boundedMassForbidden j)

def boundedMassAlphabet (j : ℕ) : Finset ℕ :=
  insert (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes

theorem boundedMassForbidden_mono : Monotone boundedMassForbidden := by
  apply monotone_nat_of_le_succ
  intro j
  exact subset_union_left

theorem boundedMassAlphabet_fresh (j p : ℕ) (hp : p ∈ boundedMassAlphabet j) :
    p ∉ boundedMassForbidden j := by
  rcases mem_insert.mp hp with rfl | hp
  · exact (boundedMassPrimeRow j).q_fresh
  · exact fun h => ((boundedMassPrimeRow j).primes_spec p hp).2.2 (mem_insert_of_mem h)

theorem boundedMassAlphabets_disjoint : Pairwise (fun j k =>
    Disjoint (boundedMassAlphabet j) (boundedMassAlphabet k)) := by
  have hlt : ∀ j k, j < k → Disjoint (boundedMassAlphabet j) (boundedMassAlphabet k) := by
    intro j k hjk
    apply disjoint_left.mpr
    intro p hpj hpk
    have hnext : p ∈ boundedMassForbidden (j + 1) := mem_union_right _ hpj
    exact boundedMassAlphabet_fresh k p hpk
      (boundedMassForbidden_mono (Nat.succ_le_of_lt hjk) hnext)
  intro j k hjk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hlt j k h
  · exact (hlt k j h).symm

/-- The complete arithmetic supplier for the printed bounded-mass rows.
Disjointness covers the q multipliers as well as the divisor primes. -/
theorem exists_boundedMassPrimeRows :
    ∃ (q : ℕ → ℕ) (P : ℕ → Finset ℕ),
      Pairwise (fun j k => Disjoint (insert (q j) (P j)) (insert (q k) (P k))) ∧
      ∀ j, Nat.Prime (q j) ∧ 2 < q j ∧ 4 ^ (j + 1) ≤ q j ∧ q j ∉ P j ∧
        (∀ p ∈ P j, Nat.Prime p ∧ 2 < p) ∧
        (q j : ℝ) ≤ ∏ p ∈ P j, (1 + (1 : ℝ) / p) ∧
        (∏ p ∈ P j, (1 + (1 : ℝ) / p)) < (4 / 3) * q j := by
  refine ⟨fun j => (boundedMassPrimeRow j).q, fun j => (boundedMassPrimeRow j).primes,
    boundedMassAlphabets_disjoint, ?_⟩
  intro j
  let R := boundedMassPrimeRow j
  refine ⟨R.q_prime, R.q_odd, R.q_large, ?_, ?_, R.product_lower, R.product_upper⟩
  · intro h
    exact (R.primes_spec R.q h).2.2 (mem_insert_self _ _)
  · intro p hp
    exact ⟨(R.primes_spec p hp).1, (R.primes_spec p hp).2.1⟩

/-- The selected divisor rows have exactly the bounded reciprocal masses
printed in the short paper, without an asymptotic estimate. -/
theorem boundedMassPrimeRow_reciprocal_bounds (j : ℕ) :
    1 ≤ ∑ a ∈ divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes,
      (1 : ℝ) / a ∧
    (∑ a ∈ divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes,
      (1 : ℝ) / a) < 4 / 3 := by
  let R := boundedMassPrimeRow j
  have hP : ∀ p ∈ R.primes, Nat.Prime p := fun p hp => (R.primes_spec p hp).1
  have hq : (0 : ℝ) < R.q := by exact_mod_cast R.q_prime.pos
  rw [cube_reciprocal_sum R.q R.primes R.q_prime.pos hP, cubeProductCost]
  have hlo : 1 ≤ (∏ p ∈ R.primes, (1 + (1 : ℝ) / p)) / (R.q : ℝ) :=
    (le_div_iff₀ hq).mpr (by simpa using R.product_lower)
  have hhi : (∏ p ∈ R.primes, (1 + (1 : ℝ) / p)) / (R.q : ℝ) < 4 / 3 :=
    (div_lt_iff₀ hq).mpr R.product_upper
  constructor
  · convert hlo using 1 <;> ring
  · convert hhi using 1 <;> ring

#print axioms exists_boundedMassPrimeRows
#print axioms boundedMassPrimeRow_reciprocal_bounds

end ErdosProblems.Erdos257.PaperCompleteR8
end
