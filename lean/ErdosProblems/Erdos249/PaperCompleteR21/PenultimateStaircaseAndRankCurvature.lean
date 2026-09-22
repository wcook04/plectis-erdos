import Erdos249257.TotientActualLcmTopEdgeStaircase
import Erdos249257.TotientFixedRankLcmAsymptotic

/-! Paper-form restatements of the top-edge staircase and fixed-rank curvature
block of the long #249 manuscript: the penultimate term of a partial
divisibility pattern (`prop:TE-02-inv`), the equivalent test using two residue
bits (`prop:TE-03-inv`), and the factor in a second difference
(`prop:FR-02-inv`).  All short-window differences are written literally as
`δ_{2^a}(j) = φ(2H+j) - φ(H+j)` with `H = H(2^a) = lcm(1,…,2^a)`. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine
open Erdos249257.TotientFixedRankLcmAsymptotic

/-- The arithmetic LCM-ray letter is the literal short-window totient
difference. -/
private lemma staircase_letter_eq_totient_difference (t j : ℕ) :
    lcmRayArithmeticLetter t j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ) := by
  rw [lcmRayArithmeticLetter_eq_deltaTotient]
  unfold deltaTotient
  rw [show periodLcm t + j + periodLcm t = 2 * periodLcm t + j from by omega]

/-! ### `prop:TE-02-inv` -- the penultimate term of a partial divisibility
pattern -/

/-- **The penultimate term of a partial divisibility pattern**
(`prop:TE-02-inv`).  Let `a, J, K, m` with `a ≥ 8`, `H = H(2^a)` and
`B = 2H+J+K+2`.  Suppose `0 < m ≤ K`, `J+K+a+6 < 2·2^a`, `B < 2^m`,
`δ_{2^a}(J+K) ≤ 2^m - B`, and `2^(r+1) ∣ δ_{2^a}(J+K-m+r+1)` for every `r`
with `r+1 < m`.  Then `δ_{2^a}(J+K-1) = 2^(m-1)` and `2^m < 2B`, so the
modulus lies in the strict interval `B < 2^m < 2B`. -/
theorem penultimate_shortWindow_difference_eq_half {a J K m : ℕ} (ha : 8 ≤ a)
    (hmPos : 0 < m) (hmK : m ≤ K)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlast : (Nat.totient (2 * periodLcm (2 ^ a) + (J + K)) : ℤ)
          - (Nat.totient (periodLcm (2 ^ a) + (J + K)) : ℤ)
        ≤ (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ))
    (hprefix : ∀ r : ℕ, r + 1 < m →
        (2 : ℤ) ^ (r + 1) ∣
          ((Nat.totient (2 * periodLcm (2 ^ a) + (J + K - m + r + 1)) : ℤ)
            - (Nat.totient (periodLcm (2 ^ a) + (J + K - m + r + 1)) : ℤ))) :
    ((Nat.totient (2 * periodLcm (2 ^ a) + (J + K - 1)) : ℤ)
          - (Nat.totient (periodLcm (2 ^ a) + (J + K - 1)) : ℤ))
        = (2 : ℤ) ^ (m - 1)
      ∧ (2 : ℤ) ^ m < 2 * ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
      ∧ (4 : ℤ) ≤ ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
      ∧ 3 ≤ m := by
  have hHpos : 0 < periodLcm (2 ^ a) := periodLcm_pos (2 ^ a)
  have hB4 : (4 : ℤ) ≤ ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) := by
    have hnat : (4 : ℕ) ≤ 2 * periodLcm (2 ^ a) + J + K + 2 := by omega
    exact_mod_cast hnat
  have hm3 : 3 ≤ m := by
    by_contra hnot
    have hdvd : (2 : ℤ) ^ m ∣ (2 : ℤ) ^ 2 := pow_dvd_pow 2 (by omega)
    have hle : (2 : ℤ) ^ m ≤ (2 : ℤ) ^ 2 := Int.le_of_dvd (by norm_num) hdvd
    norm_num at hle
    linarith
  have hpunc : ActualLcmTerminalPuncturedDyadicStaircase a J K m := by
    refine ⟨hmPos, hmK, ?_, hroom, ?_⟩
    · intro r hr
      rw [staircase_letter_eq_totient_difference,
        show J + (K - m) + r + 1 = J + K - m + r + 1 from by omega]
      exact hprefix r hr
    · rw [staircase_letter_eq_totient_difference]
      exact hlast
  obtain ⟨h1, h2⟩ := puncturedDyadicStaircase_penultimate_eq_half ha hshort hpunc
  refine ⟨?_, h2, hB4, hm3⟩
  rw [staircase_letter_eq_totient_difference] at h1
  exact h1

/-- **The penultimate term of a partial divisibility pattern**
(`prop:TE-02-inv`), final clause: since the modulus must lie in the strict
interval `B < 2^m < 2B`, there is at most one possible power of two. -/
theorem dyadicScale_unique_in_open_interval {B : ℤ} {m₁ m₂ : ℕ}
    (h₁ : B < (2 : ℤ) ^ m₁) (h₁' : (2 : ℤ) ^ m₁ < 2 * B)
    (h₂ : B < (2 : ℤ) ^ m₂) (h₂' : (2 : ℤ) ^ m₂ < 2 * B) :
    m₁ = m₂ := by
  by_contra hne
  rcases Nat.lt_or_ge m₁ m₂ with hlt | hge
  · have hdvd : (2 : ℤ) ^ (m₁ + 1) ∣ (2 : ℤ) ^ m₂ := pow_dvd_pow 2 (by omega)
    have hle : (2 : ℤ) ^ (m₁ + 1) ≤ (2 : ℤ) ^ m₂ :=
      Int.le_of_dvd (by positivity) hdvd
    rw [pow_succ] at hle
    linarith
  · have hlt : m₂ < m₁ := by omega
    have hdvd : (2 : ℤ) ^ (m₂ + 1) ∣ (2 : ℤ) ^ m₁ := pow_dvd_pow 2 (by omega)
    have hle : (2 : ℤ) ^ (m₂ + 1) ≤ (2 : ℤ) ^ m₁ :=
      Int.le_of_dvd (by positivity) hdvd
    rw [pow_succ] at hle
    linarith

/-! ### `prop:TE-03-inv` -- an equivalent test using two residue bits -/

/-- **An equivalent test using two residue bits** (`prop:TE-03-inv`), the
bit-reading clause: the mixed dyadic guard is exactly the statement that the
depth-`(b+2)` residue lies in `[2^b, 3·2^b)`, that is, its two leading bits
are `01` or `10`. -/
theorem dyadicMixedGuard_iff_twoBitBand (A : ℤ) (b : ℕ) :
    DyadicMixedGuard A b ↔
      ((2 : ℤ) ^ b ≤ A % (2 : ℤ) ^ (b + 2)
        ∧ A % (2 : ℤ) ^ (b + 2) < 3 * (2 : ℤ) ^ b) := by
  show (((2 : ℤ) ^ b ≤ A % (2 : ℤ) ^ (b + 2)
          ∧ A % (2 : ℤ) ^ (b + 2) < 2 * (2 : ℤ) ^ b)
        ∨ (2 * (2 : ℤ) ^ b ≤ A % (2 : ℤ) ^ (b + 2)
          ∧ A % (2 : ℤ) ^ (b + 2) < 3 * (2 : ℤ) ^ b)) ↔ _
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by linarith⟩
    · exact ⟨by linarith, h2⟩
  · rintro ⟨h1, h2⟩
    by_cases h : A % (2 : ℤ) ^ (b + 2) < 2 * (2 : ℤ) ^ b
    · exact Or.inl ⟨h1, h⟩
    · push_neg at h
      exact Or.inr ⟨h, h2⟩

/-- **An equivalent test using two residue bits** (`prop:TE-03-inv`).
For every `h, N`, existence of a certificate at some depth is equivalent to
the explicit condition: there are `s, b` with `𝒞(h, N+s, b+1)`, or else
`N+s+h+b+4 < 2^b` together with
`2^b ≤ D(h, N+s, b+2) mod 2^(b+2) < 3·2^b`, that is, the two leading bits are
`01` or `10`.  Since `b` depends on the unknown first successful depth, the
equivalence is not an a priori bound on the search depth. -/
theorem exists_certifiedKill_iff_twoBitResidueTest (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      ∃ s b : ℕ,
        certifiedKill h (N + s) (b + 1) ∨
          (N + s + h + b + 4 < 2 ^ b
            ∧ (2 : ℤ) ^ b ≤ windowDiscrepancy h (N + s) (b + 2) % (2 : ℤ) ^ (b + 2)
            ∧ windowDiscrepancy h (N + s) (b + 2) % (2 : ℤ) ^ (b + 2)
                < 3 * (2 : ℤ) ^ b) := by
  rw [exists_certifiedKill_iff_guardCylinderWitness]
  unfold GuardCylinderWitness
  constructor
  · rintro ⟨s, b, hs | ⟨hsc, hg⟩⟩
    · exact ⟨s, b, Or.inl hs⟩
    · obtain ⟨g1, g2⟩ := (dyadicMixedGuard_iff_twoBitBand _ _).1 hg
      exact ⟨s, b, Or.inr ⟨by omega, g1, g2⟩⟩
  · rintro ⟨s, b, hs | ⟨hsc, g1, g2⟩⟩
    · exact ⟨s, b, Or.inl hs⟩
    · exact ⟨s, b, Or.inr ⟨by omega,
        (dyadicMixedGuard_iff_twoBitBand _ _).2 ⟨g1, g2⟩⟩⟩

/-! ### `prop:FR-02-inv` -- the factor in a second difference -/

/-- If every prime divisor of `j` divides `x`, then `j` is coprime to `x+1`. -/
private lemma curvature_gcd_succ_eq_one {j x : ℕ}
    (hx : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ x) :
    Nat.gcd j (x + 1) = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpj : p ∣ j := hpd.trans (Nat.gcd_dvd_left _ _)
  have hp1 : p ∣ x + 1 := hpd.trans (Nat.gcd_dvd_right _ _)
  have hpx : p ∣ x := hx p hp hpj
  have hone : p ∣ 1 := (Nat.dvd_add_right hpx).mp hp1
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

/-- **The factor in a second difference** (`prop:FR-02-inv`), the clean-window
structure the extra factor of two rests on.  With `A = H_a/j`: the square
bound gives `j ∣ H_a` and that every prime divisor of `j` divides `A`, hence
`gcd(j, qA+1) = 1` for `q = 1, 2, 3`; also `2j ≤ 2^a`, so `2j ∣ H_a` and
`A ≥ 2` is even; the three arguments `qA+1` are therefore odd and greater
than two, and all three totients are even. -/
theorem fixedRank_cleanWindow_structure {a j : ℕ} (ha : 4 ≤ a) (hj : 0 < j)
    (hsq : j * j ≤ 2 ^ a) :
    j ∣ periodLcm (2 ^ a)
      ∧ (∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm (2 ^ a) / j)
      ∧ 2 * j ≤ 2 ^ a
      ∧ 2 * j ∣ periodLcm (2 ^ a)
      ∧ 2 ≤ periodLcm (2 ^ a) / j
      ∧ Even (periodLcm (2 ^ a) / j)
      ∧ (∀ q : ℕ, 0 < q → q ≤ 3 →
          Nat.gcd j (q * (periodLcm (2 ^ a) / j) + 1) = 1
            ∧ Odd (q * (periodLcm (2 ^ a) / j) + 1)
            ∧ 2 < q * (periodLcm (2 ^ a) / j) + 1
            ∧ Even (Nat.totient (q * (periodLcm (2 ^ a) / j) + 1))) := by
  obtain ⟨hjdvd, hclean⟩ := clean_periodLcm_divisor_of_sq_le hj hsq
  have hHpos : 0 < periodLcm (2 ^ a) := periodLcm_pos (2 ^ a)
  have hpow16 : (16 : ℕ) ≤ 2 ^ a := by
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have htwoJLe : 2 * j ≤ 2 ^ a := by
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · omega
    · have hjj : 2 * j ≤ j * j := Nat.mul_le_mul hj2 (le_refl j)
      omega
  have htwoJdvd : 2 * j ∣ periodLcm (2 ^ a) := dvd_periodLcm (by omega) htwoJLe
  have h2jle : 2 * j ≤ periodLcm (2 ^ a) := Nat.le_of_dvd hHpos htwoJdvd
  have hAge2 : 2 ≤ periodLcm (2 ^ a) / j := (Nat.le_div_iff_mul_le hj).2 (by omega)
  have hAeven : Even (periodLcm (2 ^ a) / j) := by
    obtain ⟨k, hk⟩ := htwoJdvd
    have hk' : periodLcm (2 ^ a) = j * (2 * k) := by rw [hk]; ring
    have hdiv : periodLcm (2 ^ a) / j = 2 * k := by
      rw [hk', Nat.mul_div_cancel_left _ hj]
    exact ⟨k, by omega⟩
  refine ⟨hjdvd, hclean, htwoJLe, htwoJdvd, hAge2, hAeven, ?_⟩
  intro q hq _hq3
  have hgcd : Nat.gcd j (q * (periodLcm (2 ^ a) / j) + 1) = 1 :=
    curvature_gcd_succ_eq_one (fun p hp hpj => (hclean p hp hpj).mul_left q)
  have hmul : 1 * (periodLcm (2 ^ a) / j) ≤ q * (periodLcm (2 ^ a) / j) :=
    Nat.mul_le_mul hq (le_refl _)
  have hqA : 2 ≤ q * (periodLcm (2 ^ a) / j) := by omega
  have hodd : Odd (q * (periodLcm (2 ^ a) / j) + 1) := by
    obtain ⟨k, hk⟩ := hAeven
    refine ⟨q * k, ?_⟩
    rw [hk]; ring
  exact ⟨hgcd, hodd, by omega, Nat.totient_even (by omega)⟩

/-- **The factor in a second difference** (`prop:FR-02-inv`).
Let `a ≥ 4` and `j ≥ 1` with `j² ≤ 2^a`, and put `H_a = H(2^a)`.  Then
`2φ(j) ∣ φ(3H_a+j) - 2φ(2H_a+j) + φ(H_a+j)`, and the displayed difference
equals `φ(j)(φ(3A+1) - 2φ(2A+1) + φ(A+1))` for `A = H_a/j`.  The divisibility
is a lower bound, not an exact valuation at each LCM height. -/
theorem two_mul_totient_dvd_totient_second_difference {a j : ℕ} (ha : 4 ≤ a)
    (hj : 0 < j) (hsq : j * j ≤ 2 ^ a) :
    (2 * (Nat.totient j : ℤ)) ∣
          ((Nat.totient (3 * periodLcm (2 ^ a) + j) : ℤ)
            - 2 * (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
            + (Nat.totient (periodLcm (2 ^ a) + j) : ℤ))
      ∧ ((Nat.totient (3 * periodLcm (2 ^ a) + j) : ℤ)
            - 2 * (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
            + (Nat.totient (periodLcm (2 ^ a) + j) : ℤ))
          = (Nat.totient j : ℤ)
              * ((Nat.totient (3 * (periodLcm (2 ^ a) / j) + 1) : ℤ)
                  - 2 * (Nat.totient (2 * (periodLcm (2 ^ a) / j) + 1) : ℤ)
                  + (Nat.totient (periodLcm (2 ^ a) / j + 1) : ℤ)) := by
  obtain ⟨hjdvd, hclean⟩ := clean_periodLcm_divisor_of_sq_le hj hsq
  have hdef : fixedRankSecondDifference (periodLcm (2 ^ a)) j
      = (Nat.totient (3 * periodLcm (2 ^ a) + j) : ℤ)
        - 2 * (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
        + (Nat.totient (periodLcm (2 ^ a) + j) : ℤ) := rfl
  refine ⟨?_, ?_⟩
  · rw [← hdef]
    exact two_mul_totient_dvd_fixedRankSecondDifference ha hj hsq
  · rw [← hdef]
    exact fixedRankSecondDifference_periodLcm_eq_mul hjdvd hclean

#print axioms penultimate_shortWindow_difference_eq_half
#print axioms dyadicScale_unique_in_open_interval
#print axioms dyadicMixedGuard_iff_twoBitBand
#print axioms exists_certifiedKill_iff_twoBitResidueTest
#print axioms fixedRank_cleanWindow_structure
#print axioms two_mul_totient_dvd_totient_second_difference
end ErdosProblems.Erdos249.PaperCompleteR21
