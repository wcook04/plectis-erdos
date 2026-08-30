/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification.Statements

/-!
# Trusted statements for the external Comparator packet

The holes in this module are intentional trusted challenge statements.  This
module is not part of the project's default Lean build.  The external
Comparator job checks that `ExternalVerification.Solution` supplies these exact
declarations, uses only the configured axiom budget, and is accepted by Lean's
kernel.
-/

namespace Erdos249257.ExternalVerification

open scoped ENNReal
open Module MeasureTheory

theorem portfolioClaims (ι : Type*) [Fintype ι] : PortfolioClaims ι := by
  sorry

theorem irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses :
    Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ ¬(m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m :=
  (portfolioClaims Unit).problem68

theorem irrational_factorialGapSeries_iff_cofinal_nonunit_carries :
    Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧ factorialGapStepCarry m ≠ 1 :=
  (portfolioClaims Unit).problem68Carry

theorem no_cofinallyBoundedNegative_of_normalizedVanishes
    (a C D magnitude : ℕ → ℕ) (B : ℕ)
    (hB : 0 < B)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hRise : ∀ n, C (n + 1) ≤ C n + B)
    (hmagnitude : ∀ n, 0 < magnitude n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * magnitude n < C n)
    (hnegative : ∀ n, ∃ t e, n ≤ t ∧ 0 < e ∧ e ≤ B ∧
      D t + e = (a t - 1) * C t) : False :=
  (portfolioClaims Unit).problem243 a C D magnitude B hB ha hCpos hC hD hRise
    hmagnitude hvanish hnegative

theorem no_eventuallyPeriodicNegative_orbit
    (a D C e : ℕ → ℕ) (N h M : ℕ)
    (hh : 0 < h) (hM : 0 < M) (ha : ∀ n, 2 ≤ a n)
    (hepos : ∀ n, 0 < e (N + n))
    (helt : ∀ n, e (N + n) < a (N + n))
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hC : ∀ n, C (n + 1) = C n + e n)
    (hshape : ∀ n, D n + e n = (a n - 1) * C n)
    (hperiod : ∀ n, e (N + n + h) = e (N + n))
    (hphase : ∀ n, C (N + n + h) = C (N + n) + M) : False :=
  (portfolioClaims Unit).problem243Periodic a D C e N h M hh hM ha hepos helt
    hD hC hshape hperiod hphase

theorem no_boundedRise_of_tailAvoidance
    (u m : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (hm : ∀ n, N ≤ n → 1 < m n)
    (hpair : ∀ {i j : ℕ}, N ≤ i → N ≤ j → i ≠ j →
      Nat.Coprime (m i) (m j))
    (havoid : ∀ {i t : ℕ}, N ≤ i → i < t →
      Nat.Coprime (m i) (u t))
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False :=
  (portfolioClaims Unit).problem243BoundedRiseTailAvoidance
    u m N B hB hm hpair havoid hrise huTop

theorem finrank_totientKernelThroughLevelFamily_eq (e : ℕ) (he : 1 ≤ e) :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 :=
  (portfolioClaims Unit).problem249Finite e he

theorem not_finiteDimensional_span_fullTotientKernel :
    ¬ FiniteDimensional ℚ
      (Submodule.span ℚ (Set.range fullTotientKernelFamily)) :=
  (portfolioClaims Unit).problem249Infinite

theorem exists_totientDyadicSectionBasis :
    Nonempty
      (Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily))) :=
  (portfolioClaims Unit).problem249Basis

theorem finrank_allBaseTotientKernelThroughLevelFamily_eq_of_linearIndependent
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (hcanon : LinearIndependent ℚ (canonicalAllBaseTotientKernelFamily k e)) :
    finrank ℚ
      (Submodule.span ℚ
        (Set.range (allBaseTotientKernelThroughLevelFamily k e))) =
      k ^ e + 1 :=
  (portfolioClaims Unit).problem249AllBaseRank k e hk he hcanon

theorem tsum_pos_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1 :=
  (portfolioClaims Unit).problem249VisibleCoprimeMass

theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ)) :=
  (portfolioClaims Unit).problem249SquaredGcdMoment

theorem runHeight_defect_fib_sum_lower (e : List ℕ) :
    Nat.fib (e.length + 3) + Nat.fib (e.length + 1) * e.sum ≤
      runHeight (defectRunLengths e) :=
  (portfolioClaims Unit).problem249SternBrocotRunStability e

theorem cylinderMass_split (a b : ℕ+) :
    cylinderMass a b =
      1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + cylinderMass (a + b) b + cylinderMass a (a + b) :=
  (portfolioClaims Unit).problem249CylinderMassSplit a b

theorem lcm_factorIdeal_finiteRank_shiftAlgebra_not_sufficient
    (t : ℕ) (ht : 3 ≤ t) :
    ∃ c a : ℕ → ℤ,
      (∃ k, c k ≠ 0) ∧
      (∀ i, a i = dyadicCoboundary c i) ∧
      ∀ terms : List (ℕ × ℤ),
        ∃ d b : ℕ → ℤ,
          (∀ i, d i = shiftLinearCombination terms c i) ∧
          (∀ i, b i = shiftLinearCombination terms a i) ∧
          (∀ i, b i = dyadicCoboundary d i) ∧
          (∀ n L, dyadicClearedPrefix b n L =
            (2 : ℤ) ^ L * d n - d (n + L)) ∧
          (∀ i, (Nat.totient (periodLcm t) : ℤ) ∣ b i) ∧
          (∀ j, j ∣ periodLcm t → ∀ i, (Nat.totient j : ℤ) ∣ b i) ∧
          (∀ i, |d i| ≤ shiftLinearWeight terms *
            |(Nat.totient (periodLcm t) : ℤ)|) ∧
          ∀ i, |b i| ≤ shiftLinearWeight terms *
            (2 * |(Nat.totient (periodLcm t) : ℤ)|) :=
  (portfolioClaims Unit).problem249LcmFactorIdealShiftAlgebra t ht

theorem irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      PowerTwoActualLcmOrbitNonintegralitySupply :=
  (portfolioClaims Unit).problem249ActualLcmOrbit

theorem irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply
    (hsupply : PowerTwoActualLcmOrbitNonintegralitySupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  (portfolioClaims Unit).problem249ActualLcmOrbit_of_supply hsupply

theorem irrational_totientSeries_of_actualLcmOrbitSeparationSupply
    (hsupply : PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) :=
  (portfolioClaims Unit).problem249ActualLcmOrbitSeparation hsupply

theorem exists_primeGap0_gt (M : ℕ) : ∃ n, M < primeGap0 n :=
  (portfolioClaims Unit).problem251 M

theorem irrational_tsum_primeDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  (portfolioClaims Unit).problem251Equivalence hprime

theorem volume_mersenneAchievementSet : volume mersenneAchievementSet = 1 :=
  (portfolioClaims Unit).problem257Measure

theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) :=
  (portfolioClaims Unit).problem257FullSupport b hb

theorem irrational_erdosSupportSeries_pairwise_coprime
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a)) :
    Irrational (erdosSupportSeries b A) :=
  (portfolioClaims Unit).problem257PairwiseCoprime b A hb hA hpair hsum

theorem irrational_ratWeightSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (γ : ℕ → ℚ) (hb : 2 ≤ b) (hm : 0 < m)
    (hγ0 : ∀ n : ℕ, 0 ≤ γ n)
    (hper : ∀ n : ℕ, N₀ ≤ n → γ (n + m) = γ n)
    (hpos : ∃ a : ℕ, N₀ ≤ a ∧ 0 < a ∧ 0 < γ a) :
    Irrational (∑' a : ℕ, ((γ a : ℝ)) / ((b : ℝ) ^ a - 1)) :=
  (portfolioClaims Unit).problem257RatWeightEventuallyPeriodic
    b m N₀ γ hb hm hγ0 hper hpos

theorem irrational_erdosSupportSeries_of_orthogonalPetalBouquet
    {A : Set ℕ} (hB : OrthogonalPetalBouquet A)
    (hselection : SunflowerForcedSlotTailSelection A) :
    Irrational (erdosSupportSeries 2 A) :=
  (portfolioClaims Unit).problem257OrthogonalPetalSunflower hB hselection

theorem finite_period_noncollapse_rat_den_interface
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (hcop : Nat.Coprime b (finiteErdosSum F b).den) :
    orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id :=
  (portfolioClaims Unit).problem257FinitePeriod F b hF h0 hb hcop

theorem volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0) :=
  (portfolioClaims Unit).problem257Dichotomy J

theorem exists_shifted_odd_tail_nat_states_of_support_fraction
    (A : Set ℕ) (hA : ∃ a : ℕ, 0 < a ∧ a ∈ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) :=
  (portfolioClaims Unit).problem257ShiftedOddTailNatStates A hA p c v hv hvalue

theorem supportCoeff_mul_eq_add_defect
    (A : Set ℕ) {a x : ℕ} (ha : a ∈ A) (ha0 : 0 < a) (hx0 : 0 < x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x :=
  (portfolioClaims Unit).problem257CompositeDilationDefect A ha ha0 hx0

theorem seven_le_of_intBand_odd {p D q : ℤ}
    (hp : 0 < p) (hD : 0 < D) (hq : 0 < q)
    (hpodd : Odd p) (hDodd : Odd D) (hqodd : Odd q)
    (hband : IntBand p D q) :
    7 ≤ p :=
  (portfolioClaims Unit).problem257HalfTwoAdicBand hp hD hq hpodd hDodd hqodd hband

theorem kernel_235_minor_eq_neg_one_fifteen :
    threePrimeKernelQ 2 3 5 0 0 0 *
          threePrimeKernelQ 2 3 5 1 1 0 -
        threePrimeKernelQ 2 3 5 1 0 0 *
          threePrimeKernelQ 2 3 5 0 1 0 =
      -(1 / 15 : ℚ) :=
  (portfolioClaims Unit).problem269

theorem smoothPrefixLcm_eq_threePrimeHeight
    {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x :=
  (portfolioClaims Unit).problem269Lcm hp hq hr hpq hpr hqr hx

theorem finiteSmoothKernelSum_groupedByHeight
    (p q r hp hq hr : ℕ) :
    (∑ e ∈ smoothExponentBox hp hq hr,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) :=
  (portfolioClaims Unit).problem269HeightGrouping p q r hp hq hr

theorem exists_small_translation_separating_arguments
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (hc : Function.Injective c) {ε : ℝ} (hε : 0 < ε) :
    ∃ shift : ℂ, ‖shift‖ < ε ∧
      (∀ i, c i + shift ≠ 0) ∧
      ∀ i j, i ≠ j →
        ¬ SamePositiveRay (c i + shift) (c j + shift) :=
  (portfolioClaims ι).problem1041 c hc hε

theorem constant_perturbation_roots_in_unitDisk
    (f : Polynomial ℂ) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsplit : f.Splits) {ρ ε : ℝ} (hρ : 0 ≤ ρ)
    (hroots : ∀ b ∈ f.roots, ‖b‖ ≤ ρ) (hε : 0 < ε)
    (hmargin : ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ + ρ < 1)
    {shift : ℂ} (hshift : ‖shift‖ < ε) :
    ∀ a : ℂ, (f + Polynomial.C shift).eval a = 0 → ‖a‖ < 1 :=
  (portfolioClaims Unit).problem1041Roots f hf hdeg hsplit hρ hroots hε
    hmargin hshift

theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit :=
  (portfolioClaims Unit).problem1049 hN hK

theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1) :=
  (portfolioClaims Unit).problem1049Recurrence hr N

end Erdos249257.ExternalVerification
