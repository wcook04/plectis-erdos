import ErdosProblems.Erdos68.PaperCompleteSupportedBands
import ErdosProblems.Erdos68.PaperCompleteExisting

/-!
# Labelled displays and prose results omitted by the theorem-environment census

The label res:translator in the SHORT note is the composite example U_9;
res:translator in the LONG record is the different prime-pair theorem.
Coverage keys are (source, label), not the bare label.
STATUS: all newly assembled declarations below are uncompiled candidates.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators

/-- The literal composite translator displayed in the short note. -/
theorem composite_translator_nine :
    isolatedChannelUnit 9 =
      Finsupp.single 8 9 - Finsupp.single 9 1 -
        Finsupp.single 2 5040 + Finsupp.single 3 1680 := by
  classical
  have hattach : ∀ n : ℕ, 2 ≤ n →
      isolatedChannelUnit n = adjacentDifference n -
        ∑ d ∈ Finset.Ico 2 n,
          (if d ∣ n then (channelWeight n d : ℤ) • isolatedChannelUnit d else 0) := by
    intro n hn
    rw [isolatedChannelUnit_of_two_le hn]
    congr 1
    exact Finset.sum_attach (Finset.Ico 2 n)
      (fun d => if d ∣ n then (channelWeight n d : ℤ) • isolatedChannelUnit d else 0)
  have h3 : isolatedChannelUnit 3 = adjacentDifference 3 := by
    rw [hattach 3 (by norm_num)]
    norm_num
  have h9 := hattach 9 (by norm_num)
  rw [show Finset.Ico 2 9 = ({2, 3, 4, 5, 6, 7, 8} : Finset ℕ) from by decide] at h9
  rw [h9]
  norm_num [h3, channelWeight]
  ext n
  simp only [adjacentDifference, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  norm_num
  all_goals (split_ifs <;> ring)

/-- The full advertised observable profile of that same composite translator. -/
theorem composite_translator_nine_profile :
    factorialMoment (isolatedChannelUnit 9) = 0 ∧
    ∀ d : ℕ, 2 ≤ d → channelNumerator (isolatedChannelUnit 9) d =
      if d = 9 then ((9 : ℕ).factorial : ℤ) - 1 else 0 :=
  ⟨factorialMoment_isolatedChannelUnit (by decide),
    fun _ hd => channelNumerator_isolatedChannelUnit (by decide) hd⟩

/-- Short-note res:congruence in the equivalent integer-divisibility form. -/
theorem supported_channel_congruence (f : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ((d.factorial : ℤ) - 1) ∣ channelNumerator f d - factorialMoment f := by
  obtain ⟨k, hk⟩ := supported_integral_normal_form f hd
  exact ⟨k, by linarith⟩

/-- Exact min-form split appearing under the two moving-factor prose labels. -/
theorem moving_factor_min_split {p q : ℕ}
    (hq : q ∣ factorialBlockPrivateModulus p) :
    factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * min
          (complementaryProjectedResidue (factorialBlockTailNumerator p)
            (factorialBlockPrivateModulus p)) (factorialBlockPrivateModulus p / q) ↔
    (factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p) ∧
      factorialBlockBudget p * factorialBlockCollisionCore p * q < factorialBlockScale p) := by
  simpa only [factorialBlock_unitFactorPairFloor_eq_min hq] using
    factorialBlock_unitFactorPairFloor_scale_iff hq

/-- The corresponding cofinal consumer on the actual tailored blocks.
Membership is the supplied canonical large prefix-private prime predicate. -/
theorem moving_factor_pair_criterion
    (hcert : ∀ B : ℕ, ∃ m q : ℕ,
      4 ≤ m ∧ B < m / 2 + 1 ∧ q ∈ factorialGapLargePrefixPrivatePrimes m ∧
      factorialBlockBudget (m / 2 + 1) * factorialBlockEndpointLcm (m / 2 + 1) <
        factorialBlockScale (m / 2 + 1) * complementaryProjectedResidue
          (factorialBlockTailNumerator (m / 2 + 1))
          (factorialBlockPrivateModulus (m / 2 + 1)) ∧
      factorialBlockBudget (m / 2 + 1) * factorialBlockCollisionCore (m / 2 + 1) * q <
        factorialBlockScale (m / 2 + 1)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply irrational_factorialGapSeries_of_cofinal_largePrefixPrivate_unitFactorPairFloor
  intro B
  obtain ⟨m, q, hm, hB, hq, hglobal, hcore⟩ := hcert B
  have hqR :=
    (factorialGapLargePrefixPrivatePrimes_unit_factor_pair_tailoredBlock (by omega) hq).2.1
  exact ⟨m, q, hm, hB, hq,
    (factorialBlock_unitFactorPairFloor_scale_iff hqR).mpr ⟨hglobal, hcore⟩⟩

/-- The apparent extra largeness condition in the canonical set follows
from the literal prime/factor/prefix-private hypotheses. Wilson excludes q=m+1. -/
lemma prefix_private_mem_large {m q : ℕ} (hm : 2 ≤ m) (hq : q.Prime)
    (hgap : q ∣ m.factorial - 1)
    (hprivate : ∀ k : ℕ, 2 ≤ k → k < m → Nat.Coprime q (k.factorial - 1)) :
    q ∈ factorialGapLargePrefixPrivatePrimes m := by
  apply (mem_factorialGapLargePrefixPrivatePrimes_iff hm).mpr
  have hgt : m < q := prime_dvd_factorial_sub_one_gt hq hgap
  have hne : q ≠ m + 1 := by
    intro heq
    subst q
    exact prime_succ_not_dvd_factorial_sub_one hm hq hgap
  exact ⟨hq, hgap, by omega, hprivate⟩

/-- Literal prime/prefix-private form of the moving-factor cofinal consumer;
canonical set membership is derived, not left as a stronger extra hypothesis. -/
theorem moving_factor_pair_criterion_literal
    (hcert : ∀ B : ℕ, ∃ m q : ℕ,
      4 ≤ m ∧ B < m / 2 + 1 ∧ q.Prime ∧ q ∣ m.factorial - 1 ∧
      (∀ k : ℕ, 2 ≤ k → k < m → Nat.Coprime q (k.factorial - 1)) ∧
      factorialBlockBudget (m / 2 + 1) * factorialBlockEndpointLcm (m / 2 + 1) <
        factorialBlockScale (m / 2 + 1) * complementaryProjectedResidue
          (factorialBlockTailNumerator (m / 2 + 1))
          (factorialBlockPrivateModulus (m / 2 + 1)) ∧
      factorialBlockBudget (m / 2 + 1) * factorialBlockCollisionCore (m / 2 + 1) * q <
        factorialBlockScale (m / 2 + 1)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply moving_factor_pair_criterion
  intro B
  obtain ⟨m, q, hm, hB, hq, hgap, hprivate, hglobal, hcore⟩ := hcert B
  exact ⟨m, q, hm, hB, prefix_private_mem_large (by omega) hq hgap hprivate,
    hglobal, hcore⟩

/-- The statement actually located at long res:split-factor-normalized-collision
is fixed-owner absorption, not a displayed arbitrary-factor theorem. -/
theorem fixed_owner_absorption {p n : ℕ} (hn : 2 ≤ n)
    (hlt : factorialGapDenominator n < p) :
    factorialGapDenominator n ∣ (p - 1).factorial ∧
      factorialBlockPrivateQuotient p n = 1 :=
  ⟨factorialGapDenominator_dvd_factorialBlockBase_of_lt hn hlt,
    factorialBlockPrivateQuotient_eq_one_of_gap_lt hn hlt⟩

set_option maxRecDepth 40000 in
/-- The exact decimal comparison in the finite-evidence paragraph. The two
small power certificates avoid asking norm_num to construct the whole large
comparison at once. This does NOT prove that a rational denominator reaches
2^39990; that requires the missing interval/continued-fraction formalisation. -/
theorem finite_decimal_comparison : (10 : ℕ) ^ 12038 < 2 ^ 39990 := by
  have ha : (10 : ℕ) ^ 205 ≤ 2 ^ 681 := by decide
  have hb : (10 : ℕ) ^ 148 < 2 ^ 492 := by decide
  calc
    (10 : ℕ) ^ 12038 = (10 ^ 205) ^ 58 * 10 ^ 148 := by
      rw [← pow_mul, ← pow_add]
      all_goals norm_num
    _ ≤ (2 ^ 681) ^ 58 * 10 ^ 148 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ha 58)
    _ < (2 ^ 681) ^ 58 * 2 ^ 492 :=
      Nat.mul_lt_mul_of_pos_left hb (by positivity)
    _ = 2 ^ 39990 := by
      rw [← pow_mul, ← pow_add]
      all_goals norm_num

end ErdosProblems.Erdos68.PaperComplete
