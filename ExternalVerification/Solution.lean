/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ExternalVerification.Statements
import Erdos249257.GreedyAchievementSet
import Erdos249257.TotientMahlerDefect
import ErdosProblems.Erdos68.FactorialZeroPlateau
import ErdosProblems.Erdos243.ReciprocalTailRigidity
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import ErdosProblems.Erdos257.MersenneSubseriesRigidity
import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import ErdosProblems.Erdos1041.NewtonFlowRaySeparation
import ErdosProblems.Erdos1049.RationalBaseLambert

/-!
# Solutions for the external Comparator packet

These thin wrappers expose nineteen existing results through the Mathlib-only
statement vocabulary in `ExternalVerification.Statements`.  They add no new
mathematical claim: each proof is a definitional transport from the declaration
owned by the public claim registry.
-/

namespace Erdos249257.ExternalVerification

open scoped ENNReal
open Module MeasureTheory

theorem portfolioClaims (ι : Type*) [Fintype ι] : PortfolioClaims ι := by
  constructor
  · simpa [factorialGapSeries, factorialGapTail, factorialGapTailTerm,
      strictFacTopRat, factorialGapPrefix,
      Erdos68.factorialGapSeries, Erdos68.factorialGapTail,
      Erdos68.factorialGapTailTerm,
      ErdosProblems.Erdos68.strictFacTopRat,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_strictFacTopRat_misses
  · simpa [factorialGapSeries, factorialGapTail, factorialGapTailTerm,
      factorialGapStepCarry, factorialGapPredecessorGap, strictFacTop,
      factorialGapPrefix,
      Erdos68.factorialGapSeries, Erdos68.factorialGapTail,
      Erdos68.factorialGapTailTerm,
      ErdosProblems.Erdos68.factorialGapStepCarry,
      ErdosProblems.Erdos68.factorialGapPredecessorGap,
      ErdosProblems.Erdos68.strictFacTop,
      ErdosProblems.Erdos68.factorialGapPrefix] using
      ErdosProblems.Erdos68.irrational_factorialGapSeries_iff_cofinal_nonunit_carries
  · intro a C D magnitude B hB ha hCpos hC hD hRise hmagnitude hvanish hnegative
    exact ErdosProblems.Erdos243.no_cofinallyBoundedNegative_of_normalizedVanishes
      a C D magnitude B hB ha hCpos hC hD hRise hmagnitude hvanish hnegative
  · exact ErdosProblems.Erdos243.no_eventuallyPeriodicNegative_orbit
  · intro e he
    simpa [totientKernelThroughLevelFamily, totientKernelSeq,
      Erdos249257.totientKernelThroughLevelFamily,
      Erdos249257.totientKernelSeq] using
      Erdos249257.finrank_totientKernelThroughLevelFamily_eq e he
  · simpa [fullTotientKernelFamily, totientKernelSeq,
      Erdos249257.fullTotientKernelFamily,
      Erdos249257.totientKernelSeq] using
      Erdos249257.not_finiteDimensional_span_fullTotientKernel
  · refine ⟨?_⟩
    simpa [TotientOddCoreIndex, fullTotientKernelFamily, totientKernelSeq,
      Erdos249257.TotientOddCoreIndex,
      Erdos249257.fullTotientKernelFamily,
      Erdos249257.totientKernelSeq] using
      Erdos249257.totientDyadicSectionBasis
  · intro M
    simpa [primeGap0, prime0, ErdosProblems.Erdos251.primeGap0,
      ErdosProblems.Erdos251.prime0] using
      ErdosProblems.Erdos251.exists_primeGap0_gt M
  · intro hprime
    simpa [primeDyadicTerm, primeGapDyadicTerm, primeGap0, prime0,
      ErdosProblems.Erdos251.primeDyadicTerm,
      ErdosProblems.Erdos251.primeGapDyadicTerm,
      ErdosProblems.Erdos251.primeGap0,
      ErdosProblems.Erdos251.prime0] using
      ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap hprime
  · simpa [mersenneAchievementSet, positiveMersenneSupportValue, mersenneWeight,
      Erdos249257.mersenneAchievementSet,
      Erdos249257.positiveMersenneSupportValue,
      Erdos249257.mersenneWeight] using
      Erdos249257.volume_mersenneAchievementSet
  · intro b hb
    simpa using Erdos249257.irrational_erdosSum_full_support b hb
  · intro F b hF h0 hb hcop
    simpa [finiteErdosSum, Erdos249257.finiteErdosSum] using
      Erdos249257.finite_period_noncollapse_rat_den F b hF h0 hb
  · intro J
    simpa [supportedMersenneAchievementSet, supportedMersenneDigitValue,
      SupportedMersenneDigits, positiveMersenneDigitValue, mersenneDigitTerm,
      mersenneWeight,
      ErdosProblems.Erdos257.supportedMersenneAchievementSet,
      ErdosProblems.Erdos257.supportedMersenneDigitValue,
      ErdosProblems.Erdos257.SupportedMersenneDigits,
      Erdos249257.positiveMersenneDigitValue,
      Erdos249257.mersenneDigitTerm,
      Erdos249257.mersenneWeight] using
      ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy J
  · simpa [threePrimeKernelQ, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.threePrimeKernelQ,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.kernel_235_minor_eq_neg_one_fifteen
  · intro p q r x hp hq hr hpq hpr hqr hx
    simpa [smoothPrefixLcm, smoothPrefixExponents, threePrimeHeight, smooth3Val,
      ErdosProblems.Erdos269.smoothPrefixLcm,
      ErdosProblems.Erdos269.smoothPrefixExponents,
      ErdosProblems.Erdos269.threePrimeHeight,
      ErdosProblems.Erdos269.smooth3Val] using
      ErdosProblems.Erdos269.smoothPrefixLcm_eq_threePrimeHeight
        hp hq hr hpq hpr hqr hx
  · intro c hc ε hε
    simpa [SamePositiveRay, ErdosProblems.Erdos1041.SamePositiveRay] using
      ErdosProblems.Erdos1041.exists_small_translation_separating_arguments c hc hε
  · exact ErdosProblems.Erdos1041.constant_perturbation_roots_in_unitDisk
  · intro N K Q digit hN hK
    simpa [CoordinatewiseCorridor,
      ErdosProblems.Erdos1049.CoordinatewiseCorridor] using
      ErdosProblems.Erdos1049.threeHalves_no_coordinatewiseCorridor
        (N := N) (K := K) (Q := Q) (digit := digit) hN hK
  · intro r s B F coeff hr N
    simpa [rationalBaseClearedTailQ, rationalBasePrefixQ,
      ErdosProblems.Erdos1049.rationalBaseClearedTailQ,
      ErdosProblems.Erdos1049.rationalBasePrefixQ] using
      ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ
        (r := r) (s := s) (B := B) (F := F) (coeff := coeff) hr N

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
    (hB : 0 < B) (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
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

theorem finrank_totientKernelThroughLevelFamily_eq (e : ℕ) (he : 1 ≤ e) :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 := by
  simpa [totientKernelThroughLevelFamily, totientKernelSeq,
    Erdos249257.totientKernelThroughLevelFamily,
    Erdos249257.totientKernelSeq] using
    Erdos249257.finrank_totientKernelThroughLevelFamily_eq e he

theorem not_finiteDimensional_span_fullTotientKernel :
    ¬ FiniteDimensional ℚ
      (Submodule.span ℚ (Set.range fullTotientKernelFamily)) := by
  simpa [fullTotientKernelFamily, totientKernelSeq,
    Erdos249257.fullTotientKernelFamily,
    Erdos249257.totientKernelSeq] using
    Erdos249257.not_finiteDimensional_span_fullTotientKernel

theorem exists_totientDyadicSectionBasis :
    Nonempty
      (Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily))) :=
  (portfolioClaims Unit).problem249Basis

theorem volume_mersenneAchievementSet : volume mersenneAchievementSet = 1 := by
  simpa [mersenneAchievementSet, positiveMersenneSupportValue, mersenneWeight,
    Erdos249257.mersenneAchievementSet,
    Erdos249257.positiveMersenneSupportValue,
    Erdos249257.mersenneWeight] using
    Erdos249257.volume_mersenneAchievementSet

theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := by
  simpa using Erdos249257.irrational_erdosSum_full_support b hb

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

theorem exists_primeGap0_gt (M : ℕ) : ∃ n, M < primeGap0 n :=
  (portfolioClaims Unit).problem251 M

theorem irrational_tsum_primeDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  (portfolioClaims Unit).problem251Equivalence hprime

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
