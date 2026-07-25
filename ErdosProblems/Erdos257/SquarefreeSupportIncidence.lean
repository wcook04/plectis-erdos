import Mathlib

/-!
# Erdős #257: the divisor incidence of the squarefree support

For a support `A ⊆ ℕ` the Lambert rearrangement carries the value
`∑_{a ∈ A} 1/(2^a − 1)` onto the power series whose coefficient at `n` is the
divisor incidence `sc_A(n) = #{d ∣ n : d ∈ A}`.  Certificate arguments for
Erdős #257 read that coefficient sequence, and several of them open by
requiring an even coefficient in the first block.

This file computes the incidence exactly for the squarefree support
`A = {d ≥ 2 : d squarefree}` and records the consequence: the coefficient is
`2^ω(n) − 1`, which is **odd for every `n ≥ 2`**.  A support whose incidence is
never even is out of reach of any argument that opens by selecting an even
first-block coefficient, for every choice of block position — the obstruction
is uniform in the block, not a failure to search far enough.

Nothing here bears on the irrationality of the squarefree-support value, which
is open, and nothing here bears on universal #257.  The statements are about
the coefficient sequence, not about the sum.
-/

namespace ErdosProblems.Erdos257

open Finset

/-- The squarefree divisors of `n` are exactly the products of sets of its
prime factors. -/
theorem squarefreeDivisors_eq_image {n : ℕ} (hn : n ≠ 0) :
    {d ∈ n.divisors | Squarefree d}
      = n.primeFactors.powerset.image (fun s => ∏ p ∈ s, p) := by
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_image, mem_powerset]
  constructor
  · rintro ⟨⟨hdvd, -⟩, hsq⟩
    exact ⟨d.primeFactors, Nat.primeFactors_mono hdvd hn,
      Nat.prod_primeFactors_of_squarefree hsq⟩
  · rintro ⟨s, hs, rfl⟩
    have hprime : ∀ p ∈ s, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hs hp)
    have hdvd : (∏ p ∈ s, p) ∣ n :=
      (Finset.prod_dvd_prod_of_subset _ _ _ hs).trans (Nat.prod_primeFactors_dvd n)
    refine ⟨⟨hdvd, hn⟩, ?_⟩
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun p hp => ?_)
    · intro p hp q hq hpq
      show IsRelPrime p q
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
    · exact (hprime p hp).squarefree

/-- **The squarefree divisor count.**  A nonzero `n` has exactly `2^ω(n)`
squarefree divisors, where `ω(n)` is the number of distinct prime factors. -/
theorem card_squarefreeDivisors {n : ℕ} (hn : n ≠ 0) :
    #{d ∈ n.divisors | Squarefree d} = 2 ^ n.primeFactors.card := by
  rw [squarefreeDivisors_eq_image hn, Finset.card_image_of_injOn, Finset.card_powerset]
  intro s hs t ht hst
  replace hst : (∏ p ∈ s, p) = ∏ p ∈ t, p := hst
  have hsp : ∀ p ∈ s, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp (mem_coe.mp hs) hp)
  have htp : ∀ p ∈ t, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp (mem_coe.mp ht) hp)
  rw [← Nat.primeFactors_prod hsp, ← Nat.primeFactors_prod htp, hst]

/-- The divisor incidence of the squarefree support `{d ≥ 2 : d squarefree}`:
the number of squarefree divisors of `n` other than `1`. -/
def squarefreeIncidence (n : ℕ) : ℕ := #{d ∈ n.divisors | 2 ≤ d ∧ Squarefree d}

/-- **Exact incidence of the squarefree support.**  For every `n ≥ 1`,
`sc_A(n) = 2^ω(n) − 1`. -/
theorem squarefreeIncidence_eq {n : ℕ} (hn : n ≠ 0) :
    squarefreeIncidence n = 2 ^ n.primeFactors.card - 1 := by
  have hone : {d ∈ n.divisors | Squarefree d} = insert 1 {d ∈ n.divisors | 2 ≤ d ∧ Squarefree d} := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, mem_insert]
    constructor
    · rintro ⟨⟨hdvd, h0⟩, hsq⟩
      rcases Nat.lt_or_ge d 2 with hlt | hge
      · interval_cases d
        · exact absurd (Nat.eq_zero_of_zero_dvd hdvd) h0
        · exact Or.inl rfl
      · exact Or.inr ⟨⟨hdvd, h0⟩, hge, hsq⟩
    · rintro (rfl | ⟨hd, -, hsq⟩)
      · exact ⟨⟨one_dvd n, hn⟩, squarefree_one⟩
      · exact ⟨hd, hsq⟩
  have hnotmem : (1 : ℕ) ∉ {d ∈ n.divisors | 2 ≤ d ∧ Squarefree d} := by
    simp only [mem_filter, not_and]
    intro _ h
    omega
  have hcard := card_squarefreeDivisors hn
  rw [hone, Finset.card_insert_of_notMem hnotmem] at hcard
  unfold squarefreeIncidence
  omega

/-- **The squarefree incidence is odd at every `n ≥ 2`.**

Consequently no block-certificate argument that opens by requiring an even
divisor-incidence coefficient can ever apply to the squarefree support, at any
block position: the failure is a parity obstruction uniform in `n`, not a
search that has not gone far enough. -/
theorem odd_squarefreeIncidence {n : ℕ} (hn : 2 ≤ n) :
    Odd (squarefreeIncidence n) := by
  have hn0 : n ≠ 0 := by omega
  have hpos : 0 < n.primeFactors.card := by
    rw [Finset.card_pos]
    exact (Nat.nonempty_primeFactors).mpr hn
  rw [squarefreeIncidence_eq hn0]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [hk, pow_succ]
  refine ⟨2 ^ k - 1, ?_⟩
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

/-- The shifted coefficient `2^ω(n)` never leaves the Erdős coefficient range
`1 ≤ c(n) ≤ n`.  This is what makes the parity obstruction sharp rather than
an artefact of a badly scaled coefficient: repairing the parity by adding one
keeps the sequence admissible. -/
theorem two_pow_card_primeFactors_le {n : ℕ} (hn : n ≠ 0) :
    2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card
      ≤ ∏ p ∈ n.primeFactors, p := by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

end ErdosProblems.Erdos257
