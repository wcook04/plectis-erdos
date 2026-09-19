import ErdosProblems.Erdos68.PrimePoleCriterion
import ErdosProblems.Erdos68.PrimePoleDenominator

/-!
# End-to-end maximal prime-power survival

Long-record label res:prime-pole. The supplied numerator identity and rational
reduction theorem are not by themselves the displayed theorem. This file
supplies the literal prefix/common-denominator equality, derives the maximum
and attainment hypotheses from the actual LCM, proves its cofactor a unit,
and joins the two existing results. No new analytic premise is used.

STATUS: uncompiled proof candidate; see theorem_coverage.json.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators

lemma gap_pos {M n : ℕ} (hn : n ∈ Finset.Icc 2 M) :
    0 < n.factorial - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr (Finset.mem_Icc.mp hn).1)

lemma prefix_lcm_pos (M : ℕ) : 0 < factorialGapPrefixLCM M := by
  apply Nat.pos_of_ne_zero
  change (Finset.Icc 2 M).lcm (fun n => n.factorial - 1) ≠ 0
  exact Finset.lcm_ne_zero_iff.mpr (fun n hn => (gap_pos hn).ne')

/-- The denominator theorem applies to the actual prefix, not a surrogate ratio. -/
theorem factorialGapPrefix_eq_lcm_ratio (M : ℕ) :
    factorialGapPrefix M =
      (factorialGapPrefixLCMNumerator M : ℚ) / factorialGapPrefixLCM M := by
  classical
  have hL : (factorialGapPrefixLCM M : ℚ) ≠ 0 := by
    exact_mod_cast (prefix_lcm_pos M).ne'
  unfold factorialGapPrefix factorialGapPrefixLCMNumerator
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  have hd : 0 < n.factorial - 1 := gap_pos hn
  have hdQ : ((n.factorial - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdvd := factorialGap_dvd_prefixLCM hn
  have hc : ((n.factorial - 1 : ℕ) : ℚ) = (n.factorial : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n.factorial), Nat.cast_one]
  rw [Nat.cast_div hdvd hdQ, ← hc]
  field_simp

/-- The exponent chosen from the LCM is positive, bounds every gap and is attained. -/
theorem lcm_prime_maximum {M p : ℕ} (hp : p.Prime)
    (hpL : p ∣ factorialGapPrefixLCM M) :
    let e := (factorialGapPrefixLCM M).factorization p
    1 ≤ e ∧
    (∀ n ∈ Finset.Icc 2 M, ¬ p ^ (e + 1) ∣ n.factorial - 1) ∧
    (∃ n ∈ Finset.Icc 2 M, p ^ e ∣ n.factorial - 1) := by
  dsimp only
  let L := factorialGapPrefixLCM M
  let e := L.factorization p
  have hL : L ≠ 0 := (prefix_lcm_pos M).ne'
  have he : 1 ≤ e := (hp.dvd_iff_one_le_factorization hL).mp hpL
  have hmax : ∀ n ∈ Finset.Icc 2 M, ¬ p ^ (e + 1) ∣ n.factorial - 1 := by
    intro n hn hdiv
    have hge := (hp.pow_dvd_iff_le_factorization hL).mp
      (hdiv.trans (factorialGap_dvd_prefixLCM hn))
    change e + 1 ≤ e at hge
    omega
  refine ⟨he, hmax, ?_⟩
  by_contra hnone
  have hlt : ∀ n ∈ Finset.Icc 2 M, (n.factorial - 1).factorization p < e := by
    intro n hn
    apply lt_of_not_ge
    intro hge
    exact hnone ⟨n, hn, (hp.pow_dvd_iff_le_factorization (gap_pos hn).ne').mpr hge⟩
  have hbad := finset_lcm_factorization_lt_of_all_lt
    (show 0 < e by omega) (fun n hn => gap_pos hn) hlt
  change e < e at hbad
  exact (lt_irrefl e) hbad

/-- Removing the full p-part of the literal LCM leaves a p-adic unit. -/
theorem lcm_maximal_cofactor_not_dvd {M p : ℕ} (hp : p.Prime) :
    ¬ p ∣ factorialGapPrefixLCM M /
      p ^ (factorialGapPrefixLCM M).factorization p := by
  have hL : factorialGapPrefixLCM M ≠ 0 := (prefix_lcm_pos M).ne'
  have hpe : p ^ (factorialGapPrefixLCM M).factorization p ∣ factorialGapPrefixLCM M :=
    (hp.pow_dvd_iff_le_factorization hL).mpr le_rfl
  intro hdiv
  have hmul := Nat.mul_dvd_mul_left
    (p ^ (factorialGapPrefixLCM M).factorization p) hdiv
  rw [Nat.mul_div_cancel' hpe] at hmul
  have hsucc : p ^ ((factorialGapPrefixLCM M).factorization p + 1) ∣
      factorialGapPrefixLCM M := by
    rw [pow_succ]
    exact hmul
  have hbad := (hp.pow_dvd_iff_le_factorization hL).mp hsucc
  omega

lemma maximal_hits_eq_valuation_filter {M p e : ℕ} (hp : p.Prime) :
    factorialGapMaxHits p M e =
      (Finset.Icc 2 M).filter (fun n => (n.factorial - 1).factorization p = e) := by
  classical
  ext n
  simp only [factorialGapMaxHits, Finset.mem_filter]
  constructor
  · rintro ⟨hn, he, hnext⟩
    have hle := (hp.pow_dvd_iff_le_factorization (gap_pos hn).ne').mp he
    have hnot := (hp.pow_dvd_iff_le_factorization (k := e + 1) (gap_pos hn).ne')
    have hlt : (n.factorial - 1).factorization p < e + 1 := by
      exact lt_of_not_ge (fun h => hnext (hnot.mpr h))
    exact ⟨hn, by omega⟩
  · rintro ⟨hn, he⟩
    refine ⟨hn, ?_, ?_⟩
    · apply (hp.pow_dvd_iff_le_factorization (gap_pos hn).ne').mpr
      omega
    · intro h
      have := (hp.pow_dvd_iff_le_factorization (gap_pos hn).ne').mp h
      omega

/-- Long res:prime-pole, end-to-end, with the paper's literal valuation-hit set. -/
theorem maximal_prime_power_survival {M p : ℕ} (_hM : 2 ≤ M)
    (hp : p.Prime) (hpL : p ∣ factorialGapPrefixLCM M) :
    (factorialGapPrefix M).den.factorization p =
        (factorialGapPrefixLCM M).factorization p ↔
      (∑ n ∈ (Finset.Icc 2 M).filter
          (fun n => (n.factorial - 1).factorization p =
            (factorialGapPrefixLCM M).factorization p),
        (((n.factorial - 1) /
          p ^ (factorialGapPrefixLCM M).factorization p : ℕ) : ZMod p)⁻¹) ≠ 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨he, hmax, hattain⟩ := lcm_prime_maximum hp hpL
  have hnum := factorialGapPrefixLCMNumerator_mod_prime hp he hmax hattain
  have hunit : ((factorialGapPrefixLCM M /
      p ^ (factorialGapPrefixLCM M).factorization p : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact lcm_maximal_cofactor_not_dvd (M := M) hp
  rw [factorialGapPrefix_eq_lcm_ratio,
    natRatio_den_factorization_eq_iff hp (prefix_lcm_pos M) hpL]
  have hcriterion : (¬ p ∣ factorialGapPrefixLCMNumerator M) ↔
      factorialGapPrincipalResidue p M
        ((factorialGapPrefixLCM M).factorization p) ≠ 0 := by
    rw [← ZMod.natCast_eq_zero_iff (factorialGapPrefixLCMNumerator M) p, hnum]
    simp only [mul_eq_zero, hunit, false_or]
  simpa only [factorialGapPrincipalResidue, maximal_hits_eq_valuation_filter hp] using hcriterion

end ErdosProblems.Erdos68.PaperComplete
