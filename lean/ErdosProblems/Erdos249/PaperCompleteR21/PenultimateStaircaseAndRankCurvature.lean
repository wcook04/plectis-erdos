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
      ∧ (2 : ℤ) ^ m < 2 * ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) := by
  have hpunc : ActualLcmTerminalPuncturedDyadicStaircase a J K m := by
    refine ⟨hmPos, hmK, ?_, hroom, ?_⟩
    · intro r hr
      rw [staircase_letter_eq_totient_difference,
        show J + (K - m) + r + 1 = J + K - m + r + 1 from by omega]
      exact hprefix r hr
    · rw [staircase_letter_eq_totient_difference]
      exact hlast
  obtain ⟨h1, h2⟩ := puncturedDyadicStaircase_penultimate_eq_half ha hshort hpunc
  refine ⟨?_, h2⟩
  rw [staircase_letter_eq_totient_difference] at h1
  exact h1

/-! ### `prop:TE-03-inv` -- an equivalent test using two residue bits -/

/-- The mixed dyadic guard is exactly the statement that the two leading bits
of the depth-`(b+2)` residue are `01` or `10`. -/
private lemma dyadicMixedGuard_iff_twoBitBand (A : ℤ) (b : ℕ) :
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
#print axioms exists_certifiedKill_iff_twoBitResidueTest
#print axioms two_mul_totient_dvd_totient_second_difference
end ErdosProblems.Erdos249.PaperCompleteR21
