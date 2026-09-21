import Erdos249257.MobiusSignSupportNoGo
import Erdos249257.HalfCarryReachability
import Erdos249257.DyadicPrefixCompression

/-!
Paper-form restatements of two asserted environments of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`:

* `prop:mobius-nogo` (line 7609) — the exact signed Lambert identity, the sign
  separation `∑_{d ∈ N} 1/(2^d−1) = 1/2 + ∑_{d ∈ P} 1/(2^d−1)`, the first
  positive tail term at `d = 6` with `μ(6) = 1` and value `1/63`, and the
  resulting strict overshoot `1/2 + 1/63 ≤ ∑_{d ∈ N} 1/(2^d−1)`;
* `prop:finite-boolSupport-and-onesided` (line 7629) — no finite positive-index
  Boolean support has value `1/2`, the odd reduced denominator of every finite
  Mersenne subset sum (each `2^n − 1` being odd) against the even denominator
  of `1/2`, and the finite-depth rational death certificate with its `3/4`
  instance at level `1`, lookahead `0`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open ArithmeticFunction Erdos249257 Erdos249257.MobiusSignSupportNoGo
open Erdos249257.HalfCarryReachability

/-! ## `prop:mobius-nogo` -/

private theorem mu_two : moebius 2 = -1 := moebius_apply_prime Nat.prime_two

private theorem mu_three : moebius 3 = -1 := moebius_apply_prime (by norm_num)

private theorem mu_five : moebius 5 = -1 := moebius_apply_prime (by norm_num)

private theorem mu_four : moebius 4 = 0 := by
  apply moebius_eq_zero_of_not_squarefree
  intro hsq
  have h := hsq 2 (by norm_num)
  simp [Nat.isUnit_iff] at h

private theorem mu_six : moebius 6 = 1 := by
  calc
    moebius 6 = moebius 2 * moebius 3 := by
      simpa using isMultiplicative_moebius.map_mul_of_coprime
        (by norm_num : Nat.Coprime 2 3)
    _ = 1 := by rw [mu_two, mu_three]; norm_num

/-- The positive-Möbius tail really starts at `d = 6`: every smaller index
contributes zero, and the `d = 6` term is exactly `1/63`. -/
theorem paper_first_positiveMobius_tail_term :
    (∀ d : ℕ+, (d : ℕ) < 6 → positiveMobiusTailTerm d = 0) ∧
      moebius 6 = 1 ∧
      positiveMobiusTailTerm (⟨6, by norm_num⟩ : ℕ+) = (1 : ℝ) / 63 := by
  refine ⟨?_, mu_six, ?_⟩
  · rintro ⟨n, hn⟩ hd
    simp only [PNat.mk_coe] at hd ⊢
    interval_cases n
    · simp [positiveMobiusTailTerm]
    · simp [positiveMobiusTailTerm, mu_two]
    · simp [positiveMobiusTailTerm, mu_three]
    · simp [positiveMobiusTailTerm, mu_four]
    · simp [positiveMobiusTailTerm, mu_five]
  · norm_num [positiveMobiusTailTerm, mu_six, mersenneWeight]

/-- Long `prop:mobius-nogo`, every asserted clause.

`N = {d : μ(d) = −1}` is `negativeMobiusTerm`, `P = {d ≥ 2 : μ(d) = 1}` is
`positiveMobiusTailTerm`, and `1/(2^d − 1)` is `mersenneWeight d`.  The four
conjuncts are: the exact signed Lambert identity `∑_{d ≥ 1} μ(d)/(2^d − 1) =
1/2`; the sign separation; the quantitative bound through the `d = 6` term
`1/63`; and the strict overshoot of `1/2`. -/
theorem paper_mobius_support_overshoots_half :
    (∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1)) = 1 / 2 ∧
      (∑' d : ℕ+, negativeMobiusTerm d)
        = 1 / 2 + ∑' d : ℕ+, positiveMobiusTailTerm d ∧
      (1 : ℝ) / 2 + 1 / 63 ≤ ∑' d : ℕ+, negativeMobiusTerm d ∧
      (1 : ℝ) / 2 < ∑' d : ℕ+, negativeMobiusTerm d :=
  ⟨MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half,
    tsum_negativeMobius_eq_half_add_positiveMobiusTail,
    half_add_one_div_sixty_three_le_tsum_negativeMobius,
    half_lt_tsum_negativeMobius⟩

/-! ## `prop:finite-boolSupport-and-onesided` -/

/-- The certificate is literally a decidable comparison of two rationals. -/
instance paper_certifiedGreedyMersenneDeath_decidable
    (x : ℚ) (level lookahead : ℕ) :
    Decidable (CertifiedGreedyMersenneDeath x level lookahead) := by
  unfold CertifiedGreedyMersenneDeath
  infer_instance

/-- Long `prop:finite-boolSupport-and-onesided`, every asserted clause.

1. No finite positive-index Boolean support has value exactly `1/2`.
2. The reduced denominator of any finite Mersenne subset sum is odd, and each
   `2^n − 1` (`n ≥ 1`) is odd.
3. `1/2` has denominator `2`, which is even.
4. `CertifiedGreedyMersenneDeath` — a comparison of two rationals, hence a
   decidable finite-depth test — proves `x ∉ 𝒜`.
5. The supplied source excludes `3/4` at level `1` with lookahead `0`.
6. Scope clause: any support representing `1/2`, if it exists, must be
   infinite — by denominator parity alone, independently of any search. -/
theorem paper_finite_support_and_onesided_certificate :
    (∀ A : Set ℕ, A.Finite → 0 ∉ A → erdosSupportSeries 2 A ≠ (1 : ℝ) / 2) ∧
      (∀ F : Finset ℕ, 0 ∉ F → Odd (finiteErdosSum F 2).den) ∧
      (∀ n : ℕ, 1 ≤ n → Odd (2 ^ n - 1)) ∧
      ((1 : ℚ) / 2).den = 2 ∧ Even ((1 : ℚ) / 2).den ∧
      (∀ (x : ℚ) (level lookahead : ℕ),
        CertifiedGreedyMersenneDeath x level lookahead →
          ((x : ℚ) : ℝ) ∉ mersenneAchievementSet) ∧
      CertifiedGreedyMersenneDeath (3 / 4 : ℚ) 1 0 ∧
      (3 / 4 : ℝ) ∉ mersenneAchievementSet ∧
      (∀ A : Set ℕ, 0 ∉ A → erdosSupportSeries 2 A = (1 : ℝ) / 2 → A.Infinite) := by
  refine ⟨fun A hfin h0 => finite_boolSupport_ne_half A hfin h0,
    fun F h0 => finiteErdosSum_den_odd F h0, ?_, by norm_num, by norm_num,
    fun _ _ _ hcert => certifiedGreedyMersenneDeath_not_mem hcert,
    three_fourths_certifiedGreedyMersenneDeath,
    three_fourths_not_mem_mersenneAchievementSet,
    fun A h0 hvalue hfin => finite_boolSupport_ne_half A hfin h0 hvalue⟩
  intro n hn
  have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have heven : Even (2 ^ n) := (Nat.even_pow (m := 2) (n := n)).mpr ⟨even_two, by omega⟩
  exact Nat.Even.sub_odd hone heven odd_one

#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_first_positiveMobius_tail_term
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_mobius_support_overshoots_half
#print axioms ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_support_and_onesided_certificate

end ErdosProblems.Erdos257.PaperCompleteR21
