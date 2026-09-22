import Erdos249257.TotientActualLcmTopEdgeStaircase
import Erdos249257.DiagonalFreshLossBridge

/-! Paper-form restatements of two long-paper environments of Erdős #249:

* arbitrarily large prime-power LCM jumps: `H(t) < H(t+1)` cofinally, with the
  explicit positions `t = p - 1` for a prime `p` and `t = 2^a - 1` for
  `a ≥ 1`, and the excluded endpoint `H(0) = H(1) = 1`;
* the sufficient inequality `σ_{2^a} ≥ 0` cofinally implies `S ∉ ℚ`, with the
  paper's formula for `σ_t` written out in terms of `D`.

Here `H(t) = periodLcm t`, `D(h,N,L) = windowDiscrepancy h N L` and
`σ_t = canonicalAdjacentSuffixCentralSlack t`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine
open Erdos249257.DiagonalPincerDecomposition

/-! ### Arbitrarily large prime-power LCM jumps -/

/-- **Cofinal strict LCM jumps.**  For every `t₀` there is `t ≥ t₀` with
`H(t) < H(t+1)`. -/
theorem exists_periodLcm_strict_jump_ge_paper (t₀ : ℕ) :
    ∃ t, t₀ ≤ t ∧ periodLcm t < periodLcm (t + 1) :=
  exists_periodLcm_strict_jump_ge t₀

/-- **The prime positions.**  One may take `t = p - 1` for any prime `p > t₀`. -/
theorem periodLcm_strict_jump_at_prime_pred {t₀ p : ℕ} (hp : p.Prime)
    (hpt : t₀ < p) :
    t₀ ≤ p - 1 ∧ periodLcm (p - 1) < periodLcm (p - 1 + 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  refine ⟨by omega, ?_⟩
  apply (periodLcm_strict_jump_iff_succ_not_dvd (p - 1)).2
  have hpred : p - 1 + 1 = p := by omega
  rw [hpred, periodLcm_eq_lcmHeight]
  intro hpdvd
  have hpLe : p ≤ p - 1 :=
    (MersenneShadowCyclotomicNoncollapse.prime_dvd_lcmHeight_iff hp).1 hpdvd
  omega

/-- **The power-of-two positions.**  `t = 2^a - 1` is a strict LCM jump for
every `a ≥ 1`: `2^a` is the next required power of two. -/
theorem periodLcm_strict_jump_at_powerTwo_pred {a : ℕ} (ha : 1 ≤ a) :
    periodLcm (2 ^ a - 1) < periodLcm (2 ^ a - 1 + 1) := by
  have hpow : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by norm_num)
  have hsucc : 2 ^ a - 1 + 1 = 2 ^ a := by omega
  rw [hsucc]
  rcases Nat.lt_or_ge a 2 with h | h
  · have ha1 : a = 1 := by omega
    subst ha1
    decide
  · exact periodLcm_pow_two_strict_jump h

/-- **The excluded endpoint.**  `a = 0` is excluded because `H(0) = H(1) = 1`,
so `t = 2^0 - 1 = 0` is not a strict jump. -/
theorem periodLcm_zero_and_one_eq_one :
    periodLcm 0 = 1 ∧ periodLcm 1 = 1 ∧ ¬ periodLcm 0 < periodLcm (0 + 1) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### The residue margin at an LCM jump -/

/-- The paper's formula for `σ_t`: with `m = ⌊log₂ H_t⌋ + 10` and
`d = (D(H_t, H_t+1, m) - D(H_t, H_t, m)) mod 2^m`,
`σ_t = min(d - 2^{m-5}, 2^m - 2^{m-5} - d)`. -/
theorem canonicalAdjacentSuffixCentralSlack_paper_formula (t : ℕ) :
    canonicalAdjacentSuffixCentralSlack t =
      min ((windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                (Nat.log2 (periodLcm t) + 10)
              - windowDiscrepancy (periodLcm t) (periodLcm t)
                (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10)
          - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5))
        (2 ^ (Nat.log2 (periodLcm t) + 10)
            - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5)
          - (windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                 (Nat.log2 (periodLcm t) + 10)
               - windowDiscrepancy (periodLcm t) (periodLcm t)
                 (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10)) := by
  simp only [canonicalAdjacentSuffixCentralSlack, canonicalAdjacentSuffixDepth,
    diagonalAdjacentSuffixResidue, diagonalSuffixResidue_eq_windowDiscrepancy,
    Nat.add_zero, ← Int.sub_emod]

/-- **A sufficient inequality.**  If for every `a₀` there is `a ≥ max(2,a₀)`
with `σ_{2^a} ≥ 0`, then `S ∉ ℚ`.  Nonnegativity, not strict positivity, is
what is required. -/
theorem irrational_of_powerTwo_postJump_slack_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a, max 2 a₀ ≤ a ∧
      0 ≤ canonicalAdjacentSuffixCentralSlack (2 ^ a)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  irrational_totientSeries_of_canonicalAdjacentSuffixPowerTwoPostJumpSlackSupply
    hsupply

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_periodLcm_strict_jump_ge_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_strict_jump_at_prime_pred
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_strict_jump_at_powerTwo_pred
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_zero_and_one_eq_one
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.canonicalAdjacentSuffixCentralSlack_paper_formula
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_powerTwo_postJump_slack_supply
