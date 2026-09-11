import ErdosProblems.Erdos68.CompanionOrbitRationality
import ErdosProblems.Erdos68.FactorialZeroPlateau
import ErdosProblems.Erdos68.FactorialShiftFamilyOrbit
import ErdosProblems.Erdos68.ShrinkingTargetNormalForm
import ErdosProblems.Erdos68.PrimePoleCriterion
import ErdosProblems.Erdos68.PrimePoleDenominator
import ErdosProblems.Erdos68.PrimeZeroBranch
import ErdosProblems.Erdos68.ChannelIntegralCongruence
import ErdosProblems.Erdos68.PrimeUnitTranslator

/-!
# Paper-complete assemblies for Erdős 68

Packet: round 7, live source 48953f39dfcae869741242a8cb4815b29bce46b7.
These declarations group the exact displayed conclusions rather than citing
only one constituent lemma. All mathematical inputs are supplied library
results. The new assembly file has NOT been compiled in the return environment.
No parent irrationality theorem without its explicit cofinal premise is added.

`¬ Irrational x` is the library's rationality predicate. `facFloor x m` is
`floor (m! * x)`; `strictFacTopRat (factorialGapPrefix m) m` is the paper's Z_m.
-/

namespace ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators

/-- Short res:companion-orbit-rationality-boundary, including its cofinal form. -/
theorem companion_orbit_boundary :
    (¬ Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0) ∧
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        (facFloor companionConstant m + 2) % (m : ℤ) ≠ 0) :=
  ⟨not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two,
   irrational_factorialGapSeries_iff_cofinal_companion_floor_misses⟩

/-- Long res:companion-orbit. -/
theorem companion_orbit :
    ¬ Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0 :=
  not_irrational_factorialGapSeries_iff_eventually_companion_floor_neg_two

/-- Short res:carry-characterization and its result-label alias. -/
theorem carry_characterisation :
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) :=
  ⟨irrational_factorialGapSeries_iff_cofinal_nonunit_carries,
   irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses⟩

/-- The finite equivalences in long res:carry-equivalence, with BOTH endpoints. -/
theorem strict_successor_window {m : ℕ} (hm : 3 ≤ m) :
    (factorialGapStepCarry m = 1 ↔
      (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
    ((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m ↔
      1 + 1 / ((m.factorial : ℝ) - 1) <
          (m : ℝ) * factorialGapPredecessorGap m ∧
      (m : ℝ) * factorialGapPredecessorGap m ≤
          2 + 1 / ((m.factorial : ℝ) - 1)) := by
  refine ⟨factorialGapStepCarry_eq_one_iff_dvd_strictFacTopRat hm, ?_⟩
  simpa only [strictFacTop_ratCast] using
    dvd_strictFacTop_factorialGapPrefix_iff_predecessorGap_window hm

/-- The two rational-denominator conclusions in long res:carry-equivalence. -/
theorem nonunit_denominator_exclusion {m q : ℕ} {a : ℤ}
    (hm : 3 ≤ m) (hq : 0 < q)
    (hS : _root_.Erdos68.factorialGapSeries = (a : ℝ) / (q : ℝ))
    (hmiss : factorialGapStepCarry m ≠ 1) :
    (¬ q ∣ (m - 1).factorial) ∧ m ≤ q :=
  ⟨rational_denominator_not_dvd_pred_factorial_of_nonunit_carry hm hmiss hq hS,
   rational_denominator_ge_of_nonunit_carry hm hmiss hq hS⟩

/-- Whole long res:carry-equivalence, not only its finite-window lemma. -/
theorem strict_successor_characterisation :
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
      ((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m ↔
        1 + 1 / ((m.factorial : ℝ) - 1) <
            (m : ℝ) * factorialGapPredecessorGap m ∧
        (m : ℝ) * factorialGapPredecessorGap m ≤
            2 + 1 / ((m.factorial : ℝ) - 1))) ∧
    (¬ Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
    (∀ (m q : ℕ) (a : ℤ), 3 ≤ m → 0 < q →
      _root_.Erdos68.factorialGapSeries = (a : ℝ) / (q : ℝ) →
      factorialGapStepCarry m ≠ 1 →
      (¬ q ∣ (m - 1).factorial) ∧ m ≤ q) :=
  ⟨fun _ hm => strict_successor_window hm,
   not_irrational_factorialGapSeries_iff_eventually_unit_carries,
   irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses,
   fun _ _ _ hm hq hS hmiss => nonunit_denominator_exclusion hm hq hS hmiss⟩

/-- Whole long res:lower-escape, including the finite sufficient test and
its cofinal consumer. No escape events are asserted to exist. -/
theorem lower_interval_criterion :
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        factorialGapScaledTail m ≤
          (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1)) ∧
    (∀ m : ℕ, 3 ≤ m →
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m) →
      factorialGapScaledTail m ≤
        (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1)) ∧
    ((∀ B : ℕ, ∃ m : ℕ, 3 ≤ m ∧ B < m ∧
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m)) →
      Irrational _root_.Erdos68.factorialGapSeries) :=
  ⟨irrational_factorialGapSeries_iff_cofinal_lower_endpoint_escape,
   fun _ hm hout => lower_endpoint_escape_of_predecessorGap_outside_window hm hout,
   irrational_factorialGapSeries_of_cofinal_predecessorGap_outside_window⟩

/-- Long res:shift-family: rational and cofinal formulations for every t ≥ -1. -/
theorem uniform_family_boundary {t : ℤ} (ht : -1 ≤ t) :
    (¬ Irrational (shiftGapSeries t) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2) ∧
    (Irrational (shiftGapSeries t) ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2) :=
  ⟨not_irrational_shiftGapSeries_iff_eventually_ceil_residue_two ht,
   irrational_shiftGapSeries_iff_cofinal_ceil_residue_misses ht⟩

/-- The identifications and zero-shift conclusion also printed in that theorem. -/
theorem uniform_family_members :
    shiftGapSeries (-1) = _root_.Erdos68.factorialGapSeries ∧
    shiftGapSeries 0 = Real.exp 1 - 2 ∧
    (∀ m : ℕ, ⌈(0 : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant 0⌉ = 0) ∧
    (∀ m : ℕ, 3 ≤ m → ¬ (m : ℤ) ∣ (0 : ℤ) - 2) ∧
    Irrational (Real.exp 1) := by
  refine ⟨shiftGapSeries_neg_one_eq_factorialGapSeries,
    shiftGapSeries_zero_eq_exp_one_sub_two, ?_, ?_,
    irrational_exp_one_of_family_boundary⟩
  · intro m
    simp
  · intro m hm hdiv
    have hdiv' : (m : ℤ) ∣ (2 : ℤ) := by simpa using hdiv
    have hle : (m : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hdiv'
    omega

/-- Short res:global-complementary-criterion. The paper allows NATURAL p,
whereas the library's named final consumer asks for prime p. We use the
already proved natural-parameter block-exit theorem to remove that extra
hypothesis. This is not an assumption that p is prime in disguise. -/
theorem global_complementary_criterion_nat
    (hcert : ∀ B : ℕ, ∃ p : ℕ,
      3 ≤ p ∧ B < p ∧ 1 < factorialBlockPrivateModulus p ∧
      factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p)) :
    Irrational _root_.Erdos68.factorialGapSeries := by
  apply irrational_factorialGapSeries_of_cofinal_nonunit_carries
  intro B
  obtain ⟨p, hp, hBp, hR, hlarge⟩ := hcert B
  obtain ⟨m, hm, hmiss⟩ :=
    exists_nonunitCarry_in_primeBlock_of_global_complementaryTail hp hR hlarge
  exact ⟨m, hBp.trans_le (Finset.mem_Icc.mp hm).1, hmiss⟩

/-- Long res:global-residue, with precisely the displayed prime hypothesis. -/
theorem global_complementary_criterion_prime
    (hcert : ∀ B : ℕ, ∃ p : ℕ,
      p.Prime ∧ B < p ∧ 1 < factorialBlockPrivateModulus p ∧
      factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p)) :
    Irrational _root_.Erdos68.factorialGapSeries :=
  irrational_factorialGapSeries_of_cofinal_global_complementaryTail hcert

/-- Long res:wilson-cofinality. Nat parameters encode the displayed
nonnegative integer bound and positive least-hit indices. -/
theorem cofinal_first_prime_occurrences :
    ∀ B : ℕ, ∃ q m : ℕ, B < m ∧ q.Prime ∧ m < q ∧
      q ∣ m.factorial - 1 ∧
      ∀ k : ℕ, 2 ≤ k → k < m → Nat.Coprime q (k.factorial - 1) :=
  cofinal_prefixPrivate_factorialGap_hits

/-- Long res:product-lcm. The list presentation retains repetitions and
counts every unordered position-pair exactly once. It is stronger than the
positive-input version because no positivity assumptions are needed. -/
theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ _root_.Erdos68.listLCM xs * _root_.Erdos68.pairwiseGCDProduct xs :=
  _root_.Erdos68.list_prod_dvd_lcm_mul_pairwiseGCDProduct xs

/-- Long res:normalform, with the finite-family presentation used in its source. -/
theorem integral_normal_form {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (i : ι → ℕ) {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℤ, _root_.Erdos68.channelNumerator c i d =
      _root_.Erdos68.factorialMoment c i + ((d.factorial : ℤ) - 1) * k :=
  _root_.Erdos68.exists_channelCorrection c i hd

/-- The band identity in long res:bandbreakpoint. -/
theorem quotient_band {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (i : ι → ℕ) (d k : ℕ)
    (hlo : ∀ j, k * d ≤ i j) (hhi : ∀ j, i j < (k + 1) * d) :
    _root_.Erdos68.factorialMoment c i =
      (d.factorial ^ k : ℤ) * _root_.Erdos68.channelNumerator c i d :=
  _root_.Erdos68.factorialMoment_eq_factorial_pow_mul_channelNumerator_band
    c i d k hlo hhi

/-- First-band consequence in the same environment. -/
theorem first_band_cancellation {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (i : ι → ℕ) (d : ℕ)
    (hlo : ∀ j, d ≤ i j) (hhi : ∀ j, i j < 2 * d)
    (hzero : _root_.Erdos68.channelNumerator c i d = 0) :
    _root_.Erdos68.factorialMoment c i = 0 :=
  _root_.Erdos68.factorialMoment_eq_zero_of_channelNumerator_eq_zero_firstBand
    c i d hlo hhi hzero

/-- Last consequence in res:bandbreakpoint; the nonempty assumption is
DERIVED from the nonzero moment rather than imposed on the paper. -/
theorem breakpoint_escape {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (i : ι → ℕ) (d : ℕ)
    (hlo : ∀ j, d ≤ i j)
    (hzero : _root_.Erdos68.channelNumerator c i d = 0)
    (hne : _root_.Erdos68.factorialMoment c i ≠ 0) :
    ∃ j, 2 * d ≤ i j := by
  classical
  by_contra h
  have hhi : ∀ j, i j < 2 * d := by
    intro j
    exact lt_of_not_ge (fun hj => h ⟨j, hj⟩)
  exact hne (first_band_cancellation c i d hlo hhi hzero)

/-- Finite part of long res:channel-radius with its stated numerical constant. -/
theorem square_subsequence_radius {t M R : ℕ}
    (ht : 2 ^ 32 ≤ t) (hM : 0 < M)
    (hdiv : _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) :=
  _root_.Erdos68.square_subsequence_radius_three_halves_lower ht hM hdiv hsmall

/-- The sequence conclusions in res:channel-radius require only EVENTUAL
hypotheses, not hypotheses beginning at the numerical threshold. -/
theorem radius_no_eventual_upper (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T : ℕ, ∀ t : ℕ, T ≤ t → 2 * (R t + 1) ≤ 3 * t ^ 3 := by
  obtain ⟨T₀, hT₀⟩ := hH
  rintro ⟨T₁, hT₁⟩
  let t := max (max T₀ T₁) (2 ^ 32)
  have ht₀ : T₀ ≤ t := (Nat.le_max_left T₀ T₁).trans (Nat.le_max_left _ _)
  have ht₁ : T₁ ≤ t := (Nat.le_max_right T₀ T₁).trans (Nat.le_max_left _ _)
  obtain ⟨hpos, hdiv, hsmall⟩ := hT₀ t ht₀
  have hlower := square_subsequence_radius (Nat.le_max_right _ _) hpos hdiv hsmall
  exact (not_lt_of_ge (hT₁ t ht₁)) hlower

/-- Literal real-ratio formulation printed in the radius environment. -/
theorem radius_no_eventual_ratio_upper (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (((R t : ℕ) : ℝ) + 1) / (t : ℝ) ^ 3 ≤ (3 : ℝ) / 2 := by
  rintro ⟨T, hT⟩
  apply radius_no_eventual_upper M R hH
  refine ⟨max T 1, ?_⟩
  intro t ht
  have htT : T ≤ t := (Nat.le_max_left _ _).trans ht
  have htpos : (0 : ℝ) < t := by
    have : 1 ≤ t := (Nat.le_max_right _ _).trans ht
    exact_mod_cast (show 0 < t by omega)
  have h := (div_le_iff₀ (pow_pos htpos 3)).mp (hT t htT)
  have hc : (2 : ℝ) * ((R t : ℝ) + 1) ≤ 3 * (t : ℝ) ^ 3 := by nlinarith
  exact_mod_cast hc

/-- Literal R(t)=o(t^3) is excluded, not only the shifted radius R(t)+1. -/
theorem radius_not_littleO (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => (R t : ℝ)) =o[Filter.atTop]
      (fun t : ℕ => (t : ℝ) ^ 3) := by
  intro hlittle
  have hbound := hlittle.def (show (0 : ℝ) < 1 / 2 by norm_num)
  have hnat : ∀ᶠ t : ℕ in Filter.atTop, 2 * (R t + 1) ≤ 3 * t ^ 3 := by
    filter_upwards [hbound, Filter.eventually_ge_atTop (1 : ℕ)] with t ht ht1
    have hR : |(R t : ℝ)| = (R t : ℝ) := abs_of_nonneg (by positivity)
    have ht3 : |(t : ℝ) ^ 3| = (t : ℝ) ^ 3 := abs_of_nonneg (by positivity)
    simp only [Real.norm_eq_abs, hR, ht3] at ht
    have hone : (1 : ℝ) ≤ (t : ℝ) ^ 3 := by
      have ht1R : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      exact one_le_pow₀ ht1R
    have hh : (2 : ℝ) * ((R t : ℝ) + 1) ≤ 3 * (t : ℝ) ^ 3 := by nlinarith
    exact_mod_cast hh
  exact radius_no_eventual_upper M R hH (Filter.eventually_atTop.1 hnat)

/-- Corrector identities on the auxiliary support, including p=2.
See PaperCompleteSupportNoGo for the paper's n≥2 support incompatibility. -/
theorem prime_channel_corrector {p : ℕ} (hp : p.Prime) :
    _root_.Erdos68.factorialMoment (_root_.Erdos68.primeTranslatorCoeff p)
      (_root_.Erdos68.primeTranslatorIndex p) = 0 ∧
    _root_.Erdos68.channelNumerator (_root_.Erdos68.primeTranslatorCoeff p)
      (_root_.Erdos68.primeTranslatorIndex p) p = (p.factorial : ℤ) - 1 ∧
    (∀ d : ℕ, 2 ≤ d → d ≠ p →
      _root_.Erdos68.channelNumerator (_root_.Erdos68.primeTranslatorCoeff p)
        (_root_.Erdos68.primeTranslatorIndex p) d = 0) := by
  refine ⟨_root_.Erdos68.primeTranslator_moment_zero hp.pos,
    _root_.Erdos68.primeTranslator_channel_at_prime hp, ?_⟩
  intro d hd hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact _root_.Erdos68.primeTranslator_channel_zero_of_lt_p hp hd hlt
  · exact _root_.Erdos68.primeTranslator_channel_zero_of_p_lt hp.pos hgt

end ErdosProblems.Erdos68.PaperComplete
