import Mathlib

/-!
# Primitive `2p + 3q` multiplicity at multiples of ten

The Stern--Brocot expansion of the cylinder

`1 / ((2^2 - 1) * (2^3 - 1)) = 1 / 21`

emits one reciprocal-Mersenne term at rank `2p + 3q` for every positive
coprime pair `(p,q)`.  Rank ten is the first place where Booleanisation loses
one unit.  The lemma below proves that this is the only negative source after
passing to divisor sums: every later multiple `10k` has at least two distinct
primitive witnesses.
-/

namespace Erdos249257

/-- A positive primitive solution of `2p + 3q = n`. -/
def IsPrimitive23Solution (n p q : ℕ) : Prop :=
  0 < p ∧ 0 < q ∧ Nat.Coprime p q ∧ 2 * p + 3 * q = n

/-- Rank ten has no primitive `2p + 3q` witness.  Positivity leaves only
`q = 1,2,3`; parity excludes the odd cases, while `q = 2` forces the
non-primitive pair `(2,2)`. -/
theorem no_primitive23_solution_ten :
    ¬ ∃ p q : ℕ, IsPrimitive23Solution 10 p q := by
  rintro ⟨p, q, hp, hq, hcop, heq⟩
  have hqle : q ≤ 3 := by omega
  have hq2 : q = 2 := by omega
  subst q
  have hp2 : p = 2 := by omega
  subst p
  norm_num at hcop

/-- Rank eleven already has two distinct primitive witnesses, `(4,1)` and
`(1,3)`. -/
theorem exists_two_primitive23_solutions_eleven :
    ∃ p₁ q₁ p₂ q₂ : ℕ,
      IsPrimitive23Solution 11 p₁ q₁ ∧
      IsPrimitive23Solution 11 p₂ q₂ ∧
      (p₁, q₁) ≠ (p₂, q₂) := by
  exact ⟨4, 1, 1, 3, by norm_num [IsPrimitive23Solution],
    by norm_num [IsPrimitive23Solution], by norm_num⟩

/-- Every rank `n ≥ 11` occurs in the primitive `2p + 3q` cone.

For odd `n = 2r+1`, use `(r-1,1)`.  For even `n = 2k`, use
`(k-3,2)` when `k` is even and `(k-6,4)` when `k` is odd.  In each
case the first coordinate is odd, so it is coprime to the displayed power
of two. -/
theorem exists_primitive23_solution_of_eleven_le
    (n : ℕ) (hn : 11 ≤ n) :
    ∃ p q : ℕ, IsPrimitive23Solution n p q := by
  by_cases hodd : Odd n
  · obtain ⟨r, hr⟩ := hodd
    refine ⟨r - 1, 1, ?_⟩
    exact ⟨by omega, by norm_num, Nat.coprime_one_right (r - 1), by omega⟩
  · obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hodd
    by_cases hkodd : Odd k
    · have hkmod : k % 2 = 1 := Nat.odd_iff.mp hkodd
      have hk7 : 7 ≤ k := by omega
      have hpOdd : Odd (k - 6) := by
        rw [Nat.odd_iff]
        omega
      have hcop : Nat.Coprime (k - 6) 4 := by
        simpa using hpOdd.coprime_two_right.pow_right 2
      refine ⟨k - 6, 4, ?_⟩
      exact ⟨by omega, by norm_num, hcop, by omega⟩
    · have hkeven : Even k := Nat.not_odd_iff_even.mp hkodd
      have hk6 : 6 ≤ k := by omega
      have hpOdd : Odd (k - 3) := by
        rw [Nat.even_iff] at hkeven
        rw [Nat.odd_iff]
        omega
      refine ⟨k - 3, 2, ?_⟩
      exact ⟨by omega, by norm_num, hpOdd.coprime_two_right, by omega⟩

/-- Every multiple `10k`, for `k ≥ 2`, has two distinct positive primitive
representations `2p + 3q = 10k`.

The witnesses are completely explicit.  For odd `k` use
`(5k-6,4)` and `(5k-12,8)`.  For even `k`, `(5k-3,2)` is the first
witness; the second is `(1,6)` at `k=2`, `(2k+3,2k-2)` when
`k % 5 ≠ 1`, and `(2k-3,2k+2)` when `k % 5 = 1`. -/
theorem exists_two_primitive23_solutions_mul_ten
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ p₁ q₁ p₂ q₂ : ℕ,
      IsPrimitive23Solution (10 * k) p₁ q₁ ∧
      IsPrimitive23Solution (10 * k) p₂ q₂ ∧
      (p₁, q₁) ≠ (p₂, q₂) := by
  by_cases hodd : Odd k
  · refine ⟨5 * k - 6, 4, 5 * k - 12, 8, ?_, ?_, ?_⟩
    · have hk3 : 3 ≤ k := by
        have hne : k ≠ 2 := by
          intro heq
          subst k
          norm_num at hodd
        omega
      have hpOdd : Odd (5 * k - 6) := by
        rw [Nat.odd_iff] at hodd ⊢
        omega
      have hcop : Nat.Coprime (5 * k - 6) 4 := by
        simpa using hpOdd.coprime_two_right.pow_right 2
      exact ⟨by omega, by norm_num, hcop, by omega⟩
    · have hk3 : 3 ≤ k := by
        have hne : k ≠ 2 := by
          intro heq
          subst k
          norm_num at hodd
        omega
      have hpOdd : Odd (5 * k - 12) := by
        rw [Nat.odd_iff] at hodd ⊢
        omega
      have hcop : Nat.Coprime (5 * k - 12) 8 := by
        simpa using hpOdd.coprime_two_right.pow_right 3
      exact ⟨by omega, by norm_num, hcop, by omega⟩
    · norm_num
  · have heven : Even k := (Nat.not_odd_iff_even.mp hodd)
    have hp₁Odd : Odd (5 * k - 3) := by
      rw [Nat.even_iff] at heven
      rw [Nat.odd_iff]
      omega
    have hfirst : IsPrimitive23Solution (10 * k) (5 * k - 3) 2 := by
      exact ⟨by omega, by norm_num, hp₁Odd.coprime_two_right, by omega⟩
    by_cases hk2 : k = 2
    · subst k
      refine ⟨7, 2, 1, 6, ?_, ?_, ?_⟩
      · norm_num [IsPrimitive23Solution]
      · norm_num [IsPrimitive23Solution]
      · norm_num
    · have hk3 : k ≠ 3 := by
        intro heq
        subst k
        norm_num at heven
      have hk4 : 4 ≤ k := by omega
      by_cases hkmod : k % 5 = 1
      · have hnotdvd : ¬ 5 ∣ 2 * k - 3 := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have hcopFive : Nat.Coprime 5 (2 * k - 3) :=
          (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hnotdvd
        have hcop : Nat.Coprime (2 * k - 3) (2 * k + 2) := by
          have hadd : 2 * k + 2 = 5 + (2 * k - 3) := by omega
          rw [hadd]
          simpa using ((Nat.coprime_add_mul_right_left 5 (2 * k - 3) 1).mpr
            hcopFive).symm
        refine ⟨5 * k - 3, 2, 2 * k - 3, 2 * k + 2,
          hfirst, ?_, ?_⟩
        · exact ⟨by omega, by omega, hcop, by omega⟩
        · intro hpair
          have hq : 2 = 2 * k + 2 := congrArg Prod.snd hpair
          omega
      · have hnotdvd : ¬ 5 ∣ 2 * k - 2 := by
          rw [Nat.dvd_iff_mod_eq_zero]
          omega
        have hcopFive : Nat.Coprime 5 (2 * k - 2) :=
          (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hnotdvd
        have hcop : Nat.Coprime (2 * k + 3) (2 * k - 2) := by
          have hadd : 2 * k + 3 = 5 + (2 * k - 2) := by omega
          rw [hadd]
          simpa using (Nat.coprime_add_mul_right_left 5 (2 * k - 2) 1).mpr
            hcopFive
        refine ⟨5 * k - 3, 2, 2 * k + 3, 2 * k - 2,
          hfirst, ?_, ?_⟩
        · exact ⟨by omega, by omega, hcop, by omega⟩
        · intro hpair
          have hq : 2 = 2 * k - 2 := congrArg Prod.snd hpair
          omega

#print axioms exists_two_primitive23_solutions_mul_ten
#print axioms exists_primitive23_solution_of_eleven_le
#print axioms no_primitive23_solution_ten
#print axioms exists_two_primitive23_solutions_eleven

end Erdos249257
