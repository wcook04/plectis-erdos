import Erdos249257.CertificateKernel

/-!
# Reduced-denominator unit-gap certificates for Erdős #249

The existing gap consumer in `CertificateKernel` excludes a denominator when
the dyadically cleared tail interval contains no integer.  A reduced rational
denominator has one further exact invariant: its cleared numerator is a unit
modulo the odd part of the denominator.  This module records the finite
arithmetic certificate which permits integers in the interval only when all
of them are nonunits.

This is a strict certificate-level strengthening, not a supply theorem.  For
an odd prime power the strengthening can rescue at most one lattice point;
`reducedDenominatorUnitGapCert_prime_pow_iff` is the formal obstruction.
-/

namespace Erdos249257

/-- The dyadic carry residue used by the landed totient gap consumer. -/
def primitiveCarry (N K : ℕ) : ℕ :=
  (∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K

/-- A reduced-denominator unit-gap certificate.

Writing `u * primitiveCarry N K = J * 2^K + W`, the positive tail can
only cross the integers `J+1, ..., J+L`, where
`L = (W + u*(N+K+2))/2^K`.  The certificate says that every such candidate
is a nonunit modulo the odd reduced denominator `u`. -/
def ReducedDenominatorUnitGapCert (u N K : ℕ) : Prop :=
  let M := 2 ^ K
  let V := primitiveCarry N K
  let J := (u * V) / M
  let W := (u * V) % M
  let L := (W + u * (N + K + 2)) / M
  ∀ t ∈ Finset.Icc 1 L, ¬ Nat.Coprime (J + t) u

/-- The exact candidate count associated to a unit-gap certificate. -/
def reducedDenominatorCandidateCount (u N K : ℕ) : ℕ :=
  let M := 2 ^ K
  let V := primitiveCarry N K
  let W := (u * V) % M
  (W + u * (N + K + 2)) / M

/-- The exact residual supply exposed by the reduced-denominator consumer.
It is deliberately a proposition, not an axiom or a claimed theorem. -/
def PrimitiveReducedDenominatorUnitGapSupply : Prop :=
  ∀ a u : ℕ, 0 < u → Odd u →
    ∃ N K : ℕ, a ≤ N ∧ 0 < K ∧ ReducedDenominatorUnitGapCert u N K

/-- At a prime-power reduced denominator, nonunits are exactly multiples of
the underlying prime.  Since two consecutive integers are coprime, the
unit-gap extension can admit at most one candidate lattice point. -/
theorem reducedDenominatorUnitGapCert_prime_pow_iff
    {p e N K : ℕ} (hp : Nat.Prime p) (he : 0 < e) :
    ReducedDenominatorUnitGapCert (p ^ e) N K ↔
      let M := 2 ^ K
      let V := primitiveCarry N K
      let J := (p ^ e * V) / M
      let W := (p ^ e * V) % M
      let L := (W + p ^ e * (N + K + 2)) / M
      L = 0 ∨ (L = 1 ∧ p ∣ J + 1) := by
  dsimp [ReducedDenominatorUnitGapCert]
  let M := 2 ^ K
  let V := primitiveCarry N K
  let J := (p ^ e * V) / M
  let W := (p ^ e * V) % M
  let L := (W + p ^ e * (N + K + 2)) / M
  change (∀ t ∈ Finset.Icc 1 L, ¬ Nat.Coprime (J + t) (p ^ e)) ↔
    L = 0 ∨ (L = 1 ∧ p ∣ J + 1)
  constructor
  · intro h
    have hL : L ≤ 1 := by
      by_contra hnot
      have h2 : 2 ≤ L := by omega
      have hn1 := h 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hn2 := h 2 (Finset.mem_Icc.mpr ⟨by omega, h2⟩)
      have hd1 : p ∣ J + 1 := by
        rw [Nat.coprime_pow_right_iff he, Nat.coprime_comm,
          hp.coprime_iff_not_dvd] at hn1
        exact Classical.not_not.mp hn1
      have hd2 : p ∣ J + 2 := by
        rw [Nat.coprime_pow_right_iff he, Nat.coprime_comm,
          hp.coprime_iff_not_dvd] at hn2
        exact Classical.not_not.mp hn2
      have hc : Nat.Coprime (J + 1) (J + 2) := by
        rw [show J + 2 = 1 + (J + 1) by omega]
        simp
      have hp1 : p = 1 := Nat.eq_one_of_dvd_coprimes hc hd1 hd2
      exact hp.ne_one hp1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hL with hL0 | hL1
    · exact Or.inl hL0
    · right
      refine ⟨hL1, ?_⟩
      have hn := h 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [Nat.coprime_pow_right_iff he, Nat.coprime_comm,
        hp.coprime_iff_not_dvd] at hn
      exact Classical.not_not.mp hn
  · rintro (hL0 | ⟨hL1, hd⟩) t ht
    · simp [hL0] at ht
    · have ht1 : t = 1 := by
        have := Finset.mem_Icc.mp ht
        omega
      subst t
      rw [Nat.coprime_pow_right_iff he, Nat.coprime_comm,
        hp.coprime_iff_not_dvd]
      exact not_not_intro hd

/-- Numerical form of the prime-power ceiling: a certified interval for an
odd prime power contains zero or one candidate, never two. -/
theorem reducedDenominatorCandidateCount_prime_pow_le_one
    {p e N K : ℕ} (hp : Nat.Prime p) (he : 0 < e)
    (hcert : ReducedDenominatorUnitGapCert (p ^ e) N K) :
    reducedDenominatorCandidateCount (p ^ e) N K ≤ 1 := by
  have hshape :=
    (reducedDenominatorUnitGapCert_prime_pow_iff hp he).mp hcert
  dsimp only at hshape
  change ((p ^ e * primitiveCarry N K) % 2 ^ K
      + p ^ e * (N + K + 2)) / 2 ^ K ≤ 1
  rcases hshape with hzero | ⟨hone, _⟩
  · omega
  · omega

/-- Every hypothetical all-denominator unit-gap supply must in particular
solve the depth-growing zero-or-one-candidate problem for every odd prime
power.  This is the formal residual/no-go boundary, not a supply result. -/
theorem primitiveReducedDenominatorUnitGapSupply_prime_power_projection
    (hsupply : PrimitiveReducedDenominatorUnitGapSupply)
    {p e a : ℕ} (hp : Nat.Prime p) (hpodd : Odd p) (he : 0 < e) :
    ∃ N K : ℕ, a ≤ N ∧ 0 < K ∧
      ReducedDenominatorUnitGapCert (p ^ e) N K ∧
      reducedDenominatorCandidateCount (p ^ e) N K ≤ 1 := by
  obtain ⟨N, K, haN, hK, hcert⟩ :=
    hsupply a (p ^ e) (pow_pos hp.pos e) hpodd.pow
  exact ⟨N, K, haN, hK, hcert,
    reducedDenominatorCandidateCount_prime_pow_le_one hp he hcert⟩

/-- The first strict strengthening over the ordinary empty-gap certificate:
at `(u,N,K)=(3,3,5)` the dyadic interval contains the single integer `3`,
which is forbidden because it is a nonunit modulo the reduced denominator. -/
private theorem primitiveCarry_three_window_3_5_eval : primitiveCarry 3 5 = 24 := by
  have hφ4 : Nat.totient 4 = 2 := by decide
  have hφ5 : Nat.totient 5 = 4 := by decide
  have hφ6 : Nat.totient 6 = 2 := by decide
  have hφ7 : Nat.totient 7 = 6 := by decide
  have hφ8 : Nat.totient 8 = 4 := by decide
  have hIcc : (Finset.Icc 1 5 : Finset ℕ) = {1, 2, 3, 4, 5} := by decide
  simp only [primitiveCarry, hIcc]
  norm_num [hφ4, hφ5, hφ6, hφ7, hφ8]

theorem reducedDenominatorUnitGapCert_three_window_3_5 :
    ReducedDenominatorUnitGapCert 3 3 5 := by
  norm_num [ReducedDenominatorUnitGapCert, primitiveCarry_three_window_3_5_eval]

/-- The same row is not an ordinary empty-gap certificate: its scaled
residue plus tail height is `38`, while the dyadic modulus is `32`. -/
theorem not_ordinary_gap_certificate_three_window_3_5 :
    ¬ ((3 * primitiveCarry 3 5) % 2 ^ 5 + 3 * (3 + 5 + 2) < 2 ^ 5) := by
  rw [primitiveCarry_three_window_3_5_eval]
  norm_num

/-- Exact arithmetic in the strict-strengthening regression row. -/
theorem primitiveCarry_three_window_3_5 : primitiveCarry 3 5 = 24 := by
  exact primitiveCarry_three_window_3_5_eval

end Erdos249257
