import Erdos249257.TerminalOnlyScaledVanishing
import Erdos249257.DyadicPrefixCompression
import Erdos249257.BooleanMobiusCofinalExactRows
import Erdos249257.BooleanMobiusExactTransition
import Erdos249257.HalfCylinderFullShellSeamBridge
import Erdos249257.HalfCylinderFloorErrorReset
import Mathlib.NumberTheory.Real.Irrational

/-!
# Erdős #257: the rational-half counterexample frontier

This module records two distinct boundary results.  First, a
`HalfTerminalOnlyScaledVanishingSequence` would produce an infinite support
whose reciprocal-Mersenne subseries is exactly `1/2`, and would therefore
refute the universal irrationality assertion.  No such sequence is
constructed here; finite suffix-cylinder computations do not supply the
required cofinal hypothesis.

Second, no finite Boolean support using ranks at least two can sum to
`1/21`.  This does not construct a representation of `1/21` or prove its
membership in the achievement set.  Neither result settles Erdős #257.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCarryReachability
open Erdos257PeriodNoncollapse.HalfCylinderFiniteShadow
open Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy
open Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction
open Filter Set

/-- The universal irrationality assertion in Erdős #257. -/
def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

/-- Any terminal scaled-vanishing sequence supplies an infinite rational
counterexample of exact value `1/2`. -/
theorem exists_rational_half_counterexample_of_terminalScaledVanishing
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 :=
  exists_infinite_support_half_of_terminalScaledVanishing S

/-- The same conditional hypothesis negates the universal irrationality
claim. -/
theorem not_universal_of_terminalScaledVanishing
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  obtain ⟨A, hA, hhalf⟩ :=
    exists_rational_half_counterexample_of_terminalScaledVanishing S
  intro huniversal
  have hirr := huniversal A hA
  rw [hhalf] at hirr
  have hcast : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
  rw [hcast] at hirr
  exact (Rat.not_irrational (1 / 2 : ℚ)) hirr

/-! ## The strict-core midpoint attachment

The midpoint absorption argument is already subsumed by the cap-free
closed-set consumer.  What remains conditional is the cofinal strict-core
bound itself, not the exceptional midpoint state.
-/

/-- A cofinal `2^(R+1)` strict-core bound supplies an infinite rational
counterexample of exact value `1/2`.  This theorem consumes
`CofinalEvenHalfCutoffCoreBound`; it does not produce that open hypothesis. -/
theorem exists_rational_half_counterexample_of_cofinalEvenCoreBound
    (hcore : CofinalEvenHalfCutoffCoreBound) :
    ∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  obtain ⟨A, hA0, hhalf⟩ :=
    half_mem_mersenneAchievementSet_of_cofinalEvenCoreBound hcore
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hhalf.symm
  refine ⟨A, ?_, hseries⟩
  intro hfinite
  exact finite_boolSupport_ne_half A hfinite hA0 hseries

/-- Consequently the attachment's cofinal strict-core hypothesis negates
the universal irrationality assertion in Erdős #257. -/
theorem not_universal_of_cofinalEvenCoreBound
    (hcore : CofinalEvenHalfCutoffCoreBound) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  obtain ⟨A, hA, hhalf⟩ :=
    exists_rational_half_counterexample_of_cofinalEvenCoreBound hcore
  intro huniversal
  have hirr := huniversal A hA
  rw [hhalf] at hirr
  have hcast : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
  rw [hcast] at hirr
  exact (Rat.not_irrational (1 / 2 : ℚ)) hirr

/-! ## Quotient rows approaching one half from above

The existing exact-row consumer uses the truncated nonterminating binary
target `2^(n-1)-1`.  The adjacent integer target `2^(n-1)` is equally valid:
an exact Boolean quotient row at this target has real Mersenne value

`1/2 + localFractionMass(D,n)/2^n`.

Thus any cofinal supply of such rows converges to `1/2` from above.  The
producer remains the open all-depth row-existence statement; no finite audit
is promoted here.
-/

/-- A finite Boolean quotient row whose integral target is exactly
`2^(n-1)`.  This is the target used by the target-zero computation, distinct
from the `2^(n-1)-1` nonterminating-binary row. -/
def ExactAboveLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1)

/-- Target-zero quotient rows occur at arbitrarily large endpoints.  The
finite supports need not be compatible between endpoints. -/
def CofinalExactAboveLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactAboveLocalMersenneHalfRow n

/-! ## The fractional phase is the exact divisor-coefficient tail

The quotient-row fractional mass is not an independent error coordinate.
After casting to the reals it is exactly the scaled binary tail of the
finite support's divisor-count sequence.  This identifies the local quotient
phase with the already-bounded global carry tail. -/

/-- The fractional mass has the same affine endpoint recurrence as the
binary coefficient tail: doubling expels exactly the selected divisors of
the new endpoint. -/
theorem localFractionMass_succ
    {D : Finset ℕ} {M : ℕ} (hD : ∀ d ∈ D, 2 ≤ d) :
    localFractionMass D (M + 1) =
      2 * localFractionMass D M - endpointDivisorContribution D (M + 1) := by
  have hscaleM := scaled_localMersennePrefixValue
    (D := D) (M := M) hD
  have hscaleSucc := scaled_localMersennePrefixValue
    (D := D) (M := M + 1) hD
  have hquot := localPrefixQuotient_succ (D := D) (M := M) hD
  rw [hquot] at hscaleSucc
  have hpow : (2 : ℚ) ^ (M + 1) = 2 * (2 : ℚ) ^ M := by
    rw [pow_succ']
  rw [hpow] at hscaleSucc
  push_cast at hscaleSucc
  linarith

/-- Exact bridge between the local Mersenne fractional phase and the future
binary divisor-coefficient tail. -/
theorem localFractionMass_cast_eq_binaryCoeffTail
    {D : Finset ℕ} (hD : ∀ d ∈ D, 2 ≤ d) (M : ℕ) :
    ((localFractionMass D M : ℚ) : ℝ) =
      binaryCoeffTail (supportCoeff (↑D : Set ℕ)) M := by
  induction M with
  | zero =>
      have hscale := scaled_localMersennePrefixValue
        (D := D) (M := 0) hD
      have hquot0 : localPrefixQuotient D 0 = 0 := by
        unfold localPrefixQuotient localMersenneQuotient
        apply Finset.sum_eq_zero
        intro d hd
        have hden : 1 < 2 ^ d - 1 := by
          have hfour : 4 ≤ 2 ^ d := by
            simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (hD d hd)
          omega
        simp [Nat.div_eq_of_lt hden]
      rw [hquot0] at hscale
      norm_num at hscale
      rw [binaryCoeffTail_zero,
        ← erdosSupportSeries_two_eq_binaryCoeffSeries,
        ← positiveMersenneSupportValue_eq_erdosSupportSeries,
        positiveMersenneSupportValue_eq_cast_finiteErdosSum]
      exact_mod_cast hscale.symm
  | succ M ih =>
      rw [localFractionMass_succ hD]
      push_cast
      rw [binaryCoeffTail_succ _ (supportCoeff_le_self (↑D : Set ℕ)) M,
        ih, endpointDivisorContribution_eq_supportCoeff (by omega)]

/-- The fractional phase inherits the unconditional divisor-pair envelope
for binary support tails. -/
theorem localFractionMass_cast_le_two_sqrt_add_four
    {D : Finset ℕ} (hD : ∀ d ∈ D, 2 ≤ d) (M : ℕ) :
    ((localFractionMass D M : ℚ) : ℝ) ≤
      2 * Real.sqrt (M : ℝ) + 4 := by
  rw [localFractionMass_cast_eq_binaryCoeffTail hD M]
  exact binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    (↑D : Set ℕ) M

/-- Integer-square-root sharpening of the fractional phase envelope.  The
strict bound is convenient for an integral crossing residual: there are only
`2 * Nat.sqrt M + 3` possible nonnegative lattice states left to inspect. -/
theorem localFractionMass_cast_lt_two_natSqrt_add_three
    {D : Finset ℕ} (hD : ∀ d ∈ D, 2 ≤ d) {M : ℕ} (hM : 4 ≤ M) :
    ((localFractionMass D M : ℚ) : ℝ) <
      2 * (Nat.sqrt M : ℝ) + 3 := by
  rw [localFractionMass_cast_eq_binaryCoeffTail hD M]
  exact binaryCoeffTail_supportCoeff_lt_two_natSqrt_add_three
    (↑D : Set ℕ) M hM

/-- A phase crossing is already visible in a finite future coefficient
window up to one integral unit, once the omitted shifted tail is smaller
than the window's dyadic denominator. -/
theorem residual_sub_one_lt_finiteCoeffWindow_of_phase
    {D : Finset ℕ} {M R L : ℕ} (hD : ∀ d ∈ D, 2 ≤ d)
    (hphase : (R : ℚ) < localFractionMass D M)
    (htail : binaryCoeffTail (supportCoeff (↑D : Set ℕ)) (M + L) <
      (2 : ℝ) ^ L) :
    (R : ℝ) - 1 < finiteCoeffWindow (↑D : Set ℕ) M L := by
  have hphaseR :
      (R : ℝ) < binaryCoeffTail (supportCoeff (↑D : Set ℕ)) M := by
    rw [← localFractionMass_cast_eq_binaryCoeffTail hD M]
    exact_mod_cast hphase
  rw [binaryCoeffTail_eq_finiteCoeffWindow_add_shiftedTail] at hphaseR
  have hpow : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hsmall :
      binaryCoeffTail (supportCoeff (↑D : Set ℕ)) (M + L) /
          (2 : ℝ) ^ L < 1 := by
    exact (div_lt_one hpow).2 htail
  linarith

/-- Integer numerator form of the finite-window certificate.  A positive
integral phase residual below the complete tail forces the next `L`
divisor-coefficient rows to carry more than `(R-1) * 2^L`. -/
theorem residual_pred_mul_pow_lt_finiteCoeffWindowNumerator_of_phase
    {D : Finset ℕ} {M R L : ℕ} (hD : ∀ d ∈ D, 2 ≤ d) (hR : 1 ≤ R)
    (hphase : (R : ℚ) < localFractionMass D M)
    (htail : binaryCoeffTail (supportCoeff (↑D : Set ℕ)) (M + L) <
      (2 : ℝ) ^ L) :
    (R - 1) * 2 ^ L <
      finiteCoeffWindowNumerator (↑D : Set ℕ) M L := by
  have hwindow := residual_sub_one_lt_finiteCoeffWindow_of_phase
    hD hphase htail
  rw [finiteCoeffWindow_eq_numerator_div_pow] at hwindow
  have hpow : (0 : ℝ) < (2 : ℝ) ^ L := by positivity
  have hmul := (lt_div_iff₀ hpow).mp hwindow
  have hcast : ((R - 1 : ℕ) : ℝ) = (R : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ R)]
    norm_num
  rw [← hcast] at hmul
  exact_mod_cast hmul

/-- The universal square-root tail envelope supplies the finite-window
hypothesis from a completely integral choice of look-ahead length. -/
theorem residual_pred_mul_pow_lt_finiteCoeffWindowNumerator_of_phase_of_sqrt
    {D : Finset ℕ} {M R L : ℕ} (hD : ∀ d ∈ D, 2 ≤ d) (hR : 1 ≤ R)
    (hML : 4 ≤ M + L)
    (hlook : 2 * Nat.sqrt (M + L) + 3 ≤ 2 ^ L)
    (hphase : (R : ℚ) < localFractionMass D M) :
    (R - 1) * 2 ^ L <
      finiteCoeffWindowNumerator (↑D : Set ℕ) M L := by
  apply residual_pred_mul_pow_lt_finiteCoeffWindowNumerator_of_phase
    hD hR hphase
  have htail := binaryCoeffTail_supportCoeff_lt_two_natSqrt_add_three
    (↑D : Set ℕ) (M + L) hML
  have hlookR :
      2 * (Nat.sqrt (M + L) : ℝ) + 3 ≤ (2 : ℝ) ^ L := by
    exact_mod_cast hlook
  exact htail.trans_le hlookR

/-- A target-zero quotient row differs from one half only by its positive
fractional mass, hence by at most `(n+1)/2^n`. -/
theorem abs_exactAboveLocalMersenneRowValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1)) :
    |exactLocalMersenneRowValue D - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  have hscale := scaled_localMersennePrefixValue
    (D := D) (M := n) (fun d hd ↦ (hD d hd).1)
  have hFnonneg := localFractionMass_nonneg
    (D := D) (M := n) (fun d hd ↦ (hD d hd).1)
  have hFcard := localFractionMass_le_card
    (D := D) (M := n) (fun d hd ↦ (hD d hd).1)
  have hcard : D.card ≤ n + 1 := by
    have hsubset : D ⊆ Finset.range (n + 1) := by
      intro d hd
      exact Finset.mem_range.mpr (by have := (hD d hd).2; omega)
    exact (Finset.card_le_card hsubset).trans_eq (by simp)
  have hFupper : localFractionMass D n ≤ (n + 1 : ℕ) := by
    exact hFcard.trans (by exact_mod_cast hcard)
  push_cast at hFupper
  have hFupper' :
      localFractionMass D n ≤ ((n + 1 : ℕ) : ℚ) := by
    simpa using hFupper
  have hpow : (2 : ℚ) ^ n = 2 * (2 : ℚ) ^ (n - 1) := by
    calc
      (2 : ℚ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1 <;> omega
      _ = 2 * (2 : ℚ) ^ (n - 1) := by rw [pow_succ]; ring
  have hscale' :
      localMersennePrefixValue D * (2 : ℚ) ^ n =
        (localPrefixQuotient D n : ℚ) + localFractionMass D n := by
    simpa [mul_comm] using hscale
  have hquotCast :
      (localPrefixQuotient D n : ℚ) = (2 : ℚ) ^ (n - 1) := by
    exact_mod_cast hquot
  have hidQ :
      localMersennePrefixValue D - (1 : ℚ) / 2 =
        localFractionMass D n / (2 : ℚ) ^ n := by
    rw [eq_div_iff (by positivity : (2 : ℚ) ^ n ≠ 0)]
    rw [sub_mul, hscale', hquotCast, hpow]
    ring
  have habsQ :
      |localMersennePrefixValue D - (1 : ℚ) / 2| ≤
        ((n + 1 : ℕ) : ℚ) / (2 : ℚ) ^ n := by
    rw [hidQ, abs_div, abs_pow,
      abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2),
      abs_of_nonneg hFnonneg]
    exact div_le_div_of_nonneg_right hFupper' (by positivity)
  have habsR :
      (((|localMersennePrefixValue D - (1 : ℚ) / 2| : ℚ) : ℝ)) ≤
        ((((n + 1 : ℕ) : ℚ) / (2 : ℚ) ^ n : ℚ) : ℝ) := by
    exact_mod_cast habsQ
  simpa [exactLocalMersenneRowValue] using habsR

/-- A target-zero quotient prefix is still below one half whenever its
remaining integral slack pays for the cardinality bound on its fractional
mass.  This turns any quotient/real-greedy disagreement into a small-slack
event. -/
theorem localMersennePrefixValue_le_half_of_aboveResidual_card
    {D : Finset ℕ} {n R : ℕ} (hn : 1 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : localPrefixQuotient D n + R = 2 ^ (n - 1))
    (hcard : D.card ≤ R) :
    RationalHalfCutoffUndershoot D 1 := by
  have hscale :
      localMersennePrefixValue D * (2 : ℚ) ^ n =
        (localPrefixQuotient D n : ℚ) + localFractionMass D n := by
    simpa [mul_comm] using
      (scaled_localMersennePrefixValue (D := D) (M := n) hD)
  have hFcard := localFractionMass_le_card (D := D) (M := n) hD
  have hcardQ : ((D.card : ℕ) : ℚ) ≤ (R : ℚ) := by
    exact_mod_cast hcard
  have hFR : localFractionMass D n ≤ (R : ℚ) := hFcard.trans hcardQ
  have hrowQ :
      (localPrefixQuotient D n : ℚ) + (R : ℚ) =
        (2 : ℚ) ^ (n - 1) := by
    exact_mod_cast hrow
  have hpow : (2 : ℚ) ^ n = 2 * (2 : ℚ) ^ (n - 1) := by
    calc
      (2 : ℚ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1 <;> omega
      _ = 2 * (2 : ℚ) ^ (n - 1) := by rw [pow_succ]; ring
  unfold RationalHalfCutoffUndershoot
  rw [show localMersennePrefixValue D =
      ((localPrefixQuotient D n : ℚ) + localFractionMass D n) /
        (2 : ℚ) ^ n by
    rw [eq_div_iff (by positivity : (2 : ℚ) ^ n ≠ 0), hscale]]
  calc
    ((localPrefixQuotient D n : ℚ) + localFractionMass D n) /
        (2 : ℚ) ^ n ≤
      ((localPrefixQuotient D n : ℚ) + (R : ℚ)) /
        (2 : ℚ) ^ n := by
          exact div_le_div_of_nonneg_right
            (add_le_add_right hFR _) (by positivity)
    _ = 1 / (2 : ℚ) := by rw [hrowQ, hpow]; field_simp

/-- Exact crossing inequality: if a target-zero quotient prefix lies above
one half in the real Mersenne coordinate, then its remaining integral slack
is strictly smaller than the fractional phase. -/
theorem aboveResidual_lt_fractionMass_of_half_lt_localMersennePrefixValue
    {D : Finset ℕ} {n R : ℕ} (hn : 1 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : localPrefixQuotient D n + R = 2 ^ (n - 1))
    (hcross : (1 : ℚ) / 2 < localMersennePrefixValue D) :
    (R : ℚ) < localFractionMass D n := by
  have hscale :
      localMersennePrefixValue D * (2 : ℚ) ^ n =
        (localPrefixQuotient D n : ℚ) + localFractionMass D n := by
    simpa [mul_comm] using
      (scaled_localMersennePrefixValue (D := D) (M := n) hD)
  have hrowQ :
      (localPrefixQuotient D n : ℚ) + (R : ℚ) =
        (2 : ℚ) ^ (n - 1) := by
    exact_mod_cast hrow
  have hpow : (2 : ℚ) ^ n = 2 * (2 : ℚ) ^ (n - 1) := by
    calc
      (2 : ℚ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1 <;> omega
      _ = 2 * (2 : ℚ) ^ (n - 1) := by rw [pow_succ]; ring
  have hscaledCross :
      (2 : ℚ) ^ (n - 1) <
        localMersennePrefixValue D * (2 : ℚ) ^ n := by
    rw [hpow]
    nlinarith [show (0 : ℚ) < (2 : ℚ) ^ (n - 1) by positivity]
  rw [hscale, ← hrowQ] at hscaledCross
  linarith

/-- Exact phase criterion for a target-zero prefix.  Crossing the real half
target is equivalent—not merely implied—to the integral slack lying below
the quotient fractional phase. -/
theorem half_lt_localMersennePrefixValue_iff_residual_lt_fractionMass
    {D : Finset ℕ} {n R : ℕ} (hn : 1 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : localPrefixQuotient D n + R = 2 ^ (n - 1)) :
    (1 : ℚ) / 2 < localMersennePrefixValue D ↔
      (R : ℚ) < localFractionMass D n := by
  constructor
  · exact aboveResidual_lt_fractionMass_of_half_lt_localMersennePrefixValue
      hn hD hrow
  · intro hphase
    have hscale :
        localMersennePrefixValue D * (2 : ℚ) ^ n =
          (localPrefixQuotient D n : ℚ) + localFractionMass D n := by
      simpa [mul_comm] using
        (scaled_localMersennePrefixValue (D := D) (M := n) hD)
    have hrowQ :
        (localPrefixQuotient D n : ℚ) + (R : ℚ) =
          (2 : ℚ) ^ (n - 1) := by
      exact_mod_cast hrow
    have hpow : (2 : ℚ) ^ n = 2 * (2 : ℚ) ^ (n - 1) := by
      calc
        (2 : ℚ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1 <;> omega
        _ = 2 * (2 : ℚ) ^ (n - 1) := by rw [pow_succ]; ring
    have hnum :
        (2 : ℚ) ^ (n - 1) <
          (localPrefixQuotient D n : ℚ) + localFractionMass D n := by
      rw [← hrowQ]
      linarith
    rw [show localMersennePrefixValue D =
        ((localPrefixQuotient D n : ℚ) + localFractionMass D n) /
          (2 : ℚ) ^ n by
      rw [eq_div_iff (by positivity : (2 : ℚ) ^ n ≠ 0), hscale]]
    calc
      (1 : ℚ) / 2 = (2 : ℚ) ^ (n - 1) / (2 : ℚ) ^ n := by
        rw [hpow]
        field_simp
      _ < ((localPrefixQuotient D n : ℚ) + localFractionMass D n) /
          (2 : ℚ) ^ n :=
        (div_lt_div_iff_of_pos_right
          (show (0 : ℚ) < (2 : ℚ) ^ n by positivity)).2 hnum

/-- A positive-residual target-zero crossing has a finite, entirely integral
future-incidence certificate.  The look-ahead length only has to dominate the
universal square-root envelope for the shifted tail. -/
theorem aboveResidual_pred_mul_pow_lt_finiteCoeffWindowNumerator
    {D : Finset ℕ} {n R L : ℕ} (hn : 4 ≤ n) (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : localPrefixQuotient D n + R = 2 ^ (n - 1))
    (hlook : 2 * Nat.sqrt (n + L) + 3 ≤ 2 ^ L)
    (hcross : (1 : ℚ) / 2 < localMersennePrefixValue D) :
    (R - 1) * 2 ^ L <
      finiteCoeffWindowNumerator (↑D : Set ℕ) n L := by
  exact residual_pred_mul_pow_lt_finiteCoeffWindowNumerator_of_phase_of_sqrt
    hD hR (by omega) hlook
      ((half_lt_localMersennePrefixValue_iff_residual_lt_fractionMass
        (by omega : 1 ≤ n) hD hrow).mp hcross)

/-- Finite-window exclusion in consumer form.  If the weighted next `L`
divisor rows fit below `(R-1) * 2^L`, the target-zero prefix cannot cross the
real half target.  This is the exact local inequality left for a producer. -/
theorem localMersennePrefixValue_le_half_of_finiteCoeffWindowNumerator
    {D : Finset ℕ} {n R L : ℕ} (hn : 4 ≤ n) (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : localPrefixQuotient D n + R = 2 ^ (n - 1))
    (hlook : 2 * Nat.sqrt (n + L) + 3 ≤ 2 ^ L)
    (hwindow : finiteCoeffWindowNumerator (↑D : Set ℕ) n L ≤
      (R - 1) * 2 ^ L) :
    localMersennePrefixValue D ≤ (1 : ℚ) / 2 := by
  by_contra hnot
  have hcross : (1 : ℚ) / 2 < localMersennePrefixValue D :=
    lt_of_not_ge hnot
  have hforced := aboveResidual_pred_mul_pow_lt_finiteCoeffWindowNumerator
    hn hR hD hrow hlook hcross
  omega

/-- The first quotient/real crossing residual is universally square-root
small.  This is stronger than the cardinality window and uses no special
property of the support beyond ranks at least two. -/
theorem aboveResidual_cast_lt_two_sqrt_add_four
    {D : Finset ℕ} {n R : ℕ} (hn : 1 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : localPrefixQuotient D n + R = 2 ^ (n - 1))
    (hcross : (1 : ℚ) / 2 < localMersennePrefixValue D) :
    (R : ℝ) < 2 * Real.sqrt (n : ℝ) + 4 := by
  have hphase :=
    aboveResidual_lt_fractionMass_of_half_lt_localMersennePrefixValue
      hn hD hrow hcross
  have hphaseR :
      (R : ℝ) < ((localFractionMass D n : ℚ) : ℝ) := by
    exact_mod_cast hphase
  exact hphaseR.trans_le
    (localFractionMass_cast_le_two_sqrt_add_four hD n)

/-- Natural-number version of the sharpened crossing band.  It replaces a
real square-root comparison by the exact finite lattice window
`R < 2 * Nat.sqrt n + 3`. -/
theorem aboveResidual_lt_two_natSqrt_add_three
    {D : Finset ℕ} {n R : ℕ} (hn : 4 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : localPrefixQuotient D n + R = 2 ^ (n - 1))
    (hcross : (1 : ℚ) / 2 < localMersennePrefixValue D) :
    R < 2 * Nat.sqrt n + 3 := by
  have hphase :=
    aboveResidual_lt_fractionMass_of_half_lt_localMersennePrefixValue
      (by omega : 1 ≤ n) hD hrow hcross
  have hphaseR :
      (R : ℝ) < ((localFractionMass D n : ℚ) : ℝ) := by
    exact_mod_cast hphase
  have hbound : (R : ℝ) < 2 * (Nat.sqrt n : ℝ) + 3 :=
    hphaseR.trans (localFractionMass_cast_lt_two_natSqrt_add_three hD hn)
  exact_mod_cast hbound

/-- Contrapositive form: if a target-zero quotient prefix lies strictly
above one half, then its remaining integer slack is smaller than the support
cardinality. -/
theorem aboveResidual_lt_card_of_half_lt_localMersennePrefixValue
    {D : Finset ℕ} {n R : ℕ} (hn : 1 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : localPrefixQuotient D n + R = 2 ^ (n - 1))
    (hcross : (1 : ℚ) / 2 < localMersennePrefixValue D) :
    R < D.card := by
  by_contra hnot
  have hcard : D.card ≤ R := Nat.le_of_not_gt hnot
  have hbelow := localMersennePrefixValue_le_half_of_aboveResidual_card
    hn hD hrow hcard
  unfold RationalHalfCutoffUndershoot at hbelow
  norm_num [localMersennePrefixValue_eq_finiteErdosSum] at hbelow hcross
  linarith

/-- At an even target-zero row, a midpoint quotient take that crosses above
the real half target must leave residual strictly below the midpoint rank.
Thus the unresolved quotient-take/real-skip event is confined to a finite
integer window `R < d`, rather than an unrestricted fractional comparison. -/
theorem aboveMidpointResidual_lt_rank_of_real_crossing
    {D : Finset ℕ} {d R : ℕ} (hd : 2 ≤ d)
    (hD : ∀ a ∈ D, 2 ≤ a ∧ a < d)
    (hrow : localPrefixQuotient (insert d D) (2 * d) + R =
      2 ^ (2 * d - 1))
    (hcross : (1 : ℚ) / 2 <
      localMersennePrefixValue (insert d D)) :
    R < d := by
  classical
  have hsupp : ∀ a ∈ insert d D, 2 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haD
    · exact hd
    · exact (hD a haD).1
  have hsmall := aboveResidual_lt_card_of_half_lt_localMersennePrefixValue
    (n := 2 * d) (R := R) (by omega) hsupp hrow hcross
  have hsubset : insert d D ⊆ Finset.Icc 1 d := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haD
    · exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    · exact Finset.mem_Icc.mpr
        ⟨Nat.one_le_of_lt (hD a haD).1, (hD a haD).2.le⟩
  have hcard : (insert d D).card ≤ d := by
    calc
      (insert d D).card ≤ (Finset.Icc 1 d).card :=
        Finset.card_le_card hsubset
      _ = d := by simp
  exact hsmall.trans_le hcard

/-- Square-root sharpening of the midpoint crossing window.  Any unresolved
quotient-take/real-skip event at endpoint `2d` has residual below
`2√(2d)+4`, not merely below `d`. -/
theorem aboveMidpointResidual_cast_lt_two_sqrt_add_four_of_real_crossing
    {D : Finset ℕ} {d R : ℕ} (hd : 2 ≤ d)
    (hD : ∀ a ∈ D, 2 ≤ a ∧ a < d)
    (hrow : localPrefixQuotient (insert d D) (2 * d) + R =
      2 ^ (2 * d - 1))
    (hcross : (1 : ℚ) / 2 <
      localMersennePrefixValue (insert d D)) :
    (R : ℝ) < 2 * Real.sqrt ((2 * d : ℕ) : ℝ) + 4 := by
  classical
  have hsupp : ∀ a ∈ insert d D, 2 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haD
    · exact hd
    · exact (hD a haD).1
  exact aboveResidual_cast_lt_two_sqrt_add_four
    (n := 2 * d) (R := R) (by omega) hsupp hrow hcross

/-- Exact integral form of the midpoint crossing band. -/
theorem aboveMidpointResidual_lt_two_natSqrt_add_three_of_real_crossing
    {D : Finset ℕ} {d R : ℕ} (hd : 2 ≤ d)
    (hD : ∀ a ∈ D, 2 ≤ a ∧ a < d)
    (hrow : localPrefixQuotient (insert d D) (2 * d) + R =
      2 ^ (2 * d - 1))
    (hcross : (1 : ℚ) / 2 <
      localMersennePrefixValue (insert d D)) :
    R < 2 * Nat.sqrt (2 * d) + 3 := by
  classical
  have hsupp : ∀ a ∈ insert d D, 2 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haD
    · exact hd
    · exact (hD a haD).1
  exact aboveResidual_lt_two_natSqrt_add_three
    (n := 2 * d) (R := R) (by omega) hsupp hrow hcross

/-- At the midpoint seam, every positive-residual quotient-take/real-skip
mismatch forces the next logarithmic-size frozen divisor window to outweigh
`(R-1) * 2^L`.  Excluding this integral inequality at every rank excludes the
remaining mismatch mechanism; the theorem does not assert that exclusion. -/
theorem aboveMidpointResidual_pred_mul_pow_lt_finiteCoeffWindowNumerator
    {D : Finset ℕ} {d R L : ℕ} (hd : 2 ≤ d) (hR : 1 ≤ R)
    (hD : ∀ a ∈ D, 2 ≤ a ∧ a < d)
    (hrow : localPrefixQuotient (insert d D) (2 * d) + R =
      2 ^ (2 * d - 1))
    (hlook : 2 * Nat.sqrt (2 * d + L) + 3 ≤ 2 ^ L)
    (hcross : (1 : ℚ) / 2 <
      localMersennePrefixValue (insert d D)) :
    (R - 1) * 2 ^ L <
      finiteCoeffWindowNumerator (↑(insert d D) : Set ℕ) (2 * d) L := by
  classical
  have hsupp : ∀ a ∈ insert d D, 2 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haD
    · exact hd
    · exact (hD a haD).1
  exact aboveResidual_pred_mul_pow_lt_finiteCoeffWindowNumerator
    (n := 2 * d) (R := R) (L := L) (by omega) hR hsupp hrow hlook hcross

/-- Midpoint seam consumer for the finite-window route.  Together with a
separate exclusion of residual zero, this weighted incidence inequality is
enough to rule out quotient-take/real-skip disagreement. -/
theorem midpointPrefix_le_half_of_finiteCoeffWindowNumerator
    {D : Finset ℕ} {d R L : ℕ} (hd : 2 ≤ d) (hR : 1 ≤ R)
    (hD : ∀ a ∈ D, 2 ≤ a ∧ a < d)
    (hrow : localPrefixQuotient (insert d D) (2 * d) + R =
      2 ^ (2 * d - 1))
    (hlook : 2 * Nat.sqrt (2 * d + L) + 3 ≤ 2 ^ L)
    (hwindow :
      finiteCoeffWindowNumerator (↑(insert d D) : Set ℕ) (2 * d) L ≤
        (R - 1) * 2 ^ L) :
    localMersennePrefixValue (insert d D) ≤ (1 : ℚ) / 2 := by
  classical
  have hsupp : ∀ a ∈ insert d D, 2 ≤ a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | haD
    · exact hd
    · exact (hD a haD).1
  exact localMersennePrefixValue_le_half_of_finiteCoeffWindowNumerator
    (n := 2 * d) (R := R) (L := L) (by omega) hR hsupp hrow hlook hwindow

/-! ## The forced seam word at a first midpoint mismatch

For the actual real-greedy prefix below rank `d`, a target-zero midpoint take
with residual `R` fixes the preceding full-shell margin to `-(R+1)`.  Hence a
real skip at that rank is not an arbitrary bad prefix: the existing seam
classifier forces it to be the unique deterministic seam-greedy word, with
seam remainder exactly `R+1`. -/

/-- Exact first-shell accounting for a target-zero midpoint take against the
actual real-greedy prefix below `d`. -/
theorem greedyHalfFrozenMargin_fullShell_eq_neg_residual_succ_of_midpointRow
    {d R : ℕ} (hd : 2 ≤ d)
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1)) :
    greedyHalfFrozenMargin (d - 1) d = -((R + 1 : ℕ) : ℤ) := by
  classical
  let P := halfGreedyPrefixSupport (d - 1)
  have hbelow : ∀ a ∈ P, 2 ≤ a ∧ a < d :=
    halfGreedyPrefixSupport_pred_below d hd
  have hdnot : d ∉ P := by
    intro hmem
    exact (Nat.lt_irrefl d) (hbelow d hmem).2
  have hinsert :
      localPrefixQuotient (insert d P) (2 * d) =
        localMersenneQuotient (2 * d) d +
          localPrefixQuotient P (2 * d) := by
    unfold localPrefixQuotient
    rw [Finset.sum_insert hdnot]
  have hcoin : localMersenneQuotient (2 * d) d = 2 ^ d + 1 :=
    localMersenneQuotient_two_mul_self hd
  have hpow : 2 ^ d ≤ 2 ^ (2 * d - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hquot :
      localPrefixQuotient P (2 * d) + R + 1 = seamSubsetTarget d := by
    change localPrefixQuotient (insert d P) (2 * d) + R =
      2 ^ (2 * d - 1) at hrow
    rw [hinsert, hcoin] at hrow
    unfold seamSubsetTarget
    omega
  have hstem :
      stemTruncatedSum d P = localPrefixQuotient P (2 * d) := by
    rw [stemTruncatedSum_eq_sum_support hbelow]
    unfold localPrefixQuotient
    apply Finset.sum_congr rfl
    intro a ha
    exact (localMersenneQuotient_two_mul_eq_truncatedMersenneWeight d a).symm
  have hmargin :=
    greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target d hd
  change greedyHalfFrozenMargin (d - 1) d =
      (stemTruncatedSum d P : ℤ) - (seamSubsetTarget d : ℤ) at hmargin
  rw [hmargin, hstem]
  have hquotZ :
      (localPrefixQuotient P (2 * d) : ℤ) + (R : ℤ) + 1 =
        (seamSubsetTarget d : ℤ) := by
    exact_mod_cast hquot
  push_cast
  omega

/-- Converse first-shell accounting: every negative full-shell margin is an
exact target-zero midpoint quotient row, with a uniquely determined natural
residual.  This is the bridge needed to turn a negative ancestry-budget
event into the quotient/defect coordinates used below. -/
theorem exists_midpointRow_of_fullShell_neg
    {d : ℕ} (hd : 2 ≤ d)
    (hneg : greedyHalfFrozenMargin (d - 1) d < 0) :
    ∃ R : ℕ,
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1) := by
  classical
  let P := halfGreedyPrefixSupport (d - 1)
  have hbelow : ∀ a ∈ P, 2 ≤ a ∧ a < d :=
    halfGreedyPrefixSupport_pred_below d hd
  have hdnot : d ∉ P := by
    intro hmem
    exact (Nat.lt_irrefl d) (hbelow d hmem).2
  have hinsert :
      localPrefixQuotient (insert d P) (2 * d) =
        localMersenneQuotient (2 * d) d +
          localPrefixQuotient P (2 * d) := by
    unfold localPrefixQuotient
    rw [Finset.sum_insert hdnot]
  have hcoin : localMersenneQuotient (2 * d) d = 2 ^ d + 1 :=
    localMersenneQuotient_two_mul_self hd
  have hstem :
      stemTruncatedSum d P = localPrefixQuotient P (2 * d) := by
    rw [stemTruncatedSum_eq_sum_support hbelow]
    unfold localPrefixQuotient
    apply Finset.sum_congr rfl
    intro a ha
    exact (localMersenneQuotient_two_mul_eq_truncatedMersenneWeight d a).symm
  have hmargin :=
    greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target d hd
  change greedyHalfFrozenMargin (d - 1) d =
      (stemTruncatedSum d P : ℤ) - (seamSubsetTarget d : ℤ) at hmargin
  have hquot_lt : localPrefixQuotient P (2 * d) < seamSubsetTarget d := by
    rw [hstem] at hmargin
    omega
  refine ⟨seamSubsetTarget d - localPrefixQuotient P (2 * d) - 1, ?_⟩
  rw [hinsert, hcoin]
  have hpow : 2 ^ d ≤ 2 ^ (2 * d - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have htargetAdd : seamSubsetTarget d + 2 ^ d = 2 ^ (2 * d - 1) := by
    unfold seamSubsetTarget
    omega
  omega

/-- A quotient-take/real-skip midpoint event forces exact seam-word
alignment and identifies the deterministic seam remainder with `R+1`. -/
theorem midpointRealSkip_forces_seamAlignment_and_remainder
    {d R : ℕ} (hd : 3 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1)) :
    stemBits d (halfGreedyPrefixSupport (d - 1)) =
        integerGreedyBits (seamWeights d) (seamSubsetTarget d) ∧
      seamIntegerGreedyRemainder d = R + 1 := by
  have hmargin :=
    greedyHalfFrozenMargin_fullShell_eq_neg_residual_succ_of_midpointRow
      (d := d) (R := R) (by omega) hrow
  have hneg : greedyHalfFrozenMargin (d - 1) d < 0 := by
    rw [hmargin]
    omega
  obtain ⟨halign, _⟩ :=
    (skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos
      d hd hskip).1 hneg
  refine ⟨halign, ?_⟩
  have hseam :=
    greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment
      d hd halign
  rw [hmargin] at hseam
  exact_mod_cast (show
    (seamIntegerGreedyRemainder d : ℤ) = (R + 1 : ℕ) by omega)

/-- The floor-error coordinate gives a second, independent obstruction to a
midpoint mismatch.  Once the first shell has forced the deterministic seam
word, a real skip is impossible if its integer remainder exceeds the seam
support cardinality by at least two.  Hence the midpoint residual itself is
at most that cardinality. -/
theorem midpointRealSkip_forces_residual_le_seamSupportCard
    {d R : ℕ} (hd : 5 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1)) :
    R ≤ (seamWordSupport (seamGreedyWord d)).card := by
  obtain ⟨halignList, hrem⟩ :=
    midpointRealSkip_forces_seamAlignment_and_remainder
      (d := d) (R := R) (by omega) hskip hrow
  have halignWord : halfActualSeamWord d = seamGreedyWord d := by
    apply SeamRowWord.toList_injective
    rw [halfActualSeamWord_toList d (by omega), seamGreedyWord_toList]
    exact halignList
  by_contra hnot
  have hlarge :
      (seamWordSupport (seamGreedyWord d)).card + 2 ≤
        seamIntegerGreedyRemainder d := by
    rw [hrem]
    omega
  have htakeRat :=
    mersenneWeightRat_le_seamGreedyRemainder_of_card_add_two_le
      d hd hlarge
  rw [← halignWord,
    seamWordRationalRemainder_halfActualSeamWord d (by omega)] at htakeRat
  have htakeRat' :
      mersenneWeightRat (d - 1 + 1) ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1) := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using htakeRat
  have htakeReal :=
    (rational_greedy_take_iff_real (1 / 2 : ℚ) (d - 1)).1 htakeRat'
  apply hskip
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using htakeReal

/-- A midpoint quotient-take/real-skip event is therefore a row-small seam
event.  This is weaker than the support-cardinality conclusion above, but it
connects the mismatch frontier to the existing last-non-right-ancestor
analysis of small seam remainders. -/
theorem midpointRealSkip_forces_seamRemainder_lt_rank
    {d R : ℕ} (hd : 5 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1)) :
    seamIntegerGreedyRemainder d < d := by
  have hcard :=
    midpointRealSkip_forces_residual_le_seamSupportCard hd hskip hrow
  have hrem :=
    (midpointRealSkip_forces_seamAlignment_and_remainder
      (d := d) (R := R) (by omega) hskip hrow).2
  have hwidth := seamWordSupport_card_le_width (seamGreedyWord d)
  rw [hrem]
  omega

/-- The exact all-depth seam inequality selected by the forced-word
experiment.  It is a disposable producer: the theorem below records exactly
what it buys, without asserting that the producer has been proved. -/
def SeamRemainderCardGapFromEight : Prop :=
  ∀ d : ℕ, 8 ≤ d →
    (seamWordSupport (seamGreedyWord d)).card + 2 ≤
      seamIntegerGreedyRemainder d

/-- The seam support-cardinality gap excludes every mature
quotient-take/real-skip midpoint event. -/
theorem midpointRow_realTake_of_seamRemainderCardGapFromEight
    (hgap : SeamRemainderCardGapFromEight)
    {d R : ℕ} (hd : 8 ≤ d)
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1)) :
    mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
  by_contra hskip
  have hcard :=
    midpointRealSkip_forces_residual_le_seamSupportCard
      (d := d) (R := R) (by omega) hskip hrow
  have hrem :=
    (midpointRealSkip_forces_seamAlignment_and_remainder
      (d := d) (R := R) (by omega) hskip hrow).2
  have hlarge := hgap d hd
  rw [hrem] at hlarge
  omega

/-- Taking a rank which the actual half-greedy orbit skips necessarily
crosses one half.  This discharges the analytic crossing premise in the
second-shell certificate below directly from the actual orbit. -/
theorem insert_halfGreedyPrefixSupport_gt_half_of_realSkip
    {d : ℕ} (hd : 2 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1)) :
    (1 / 2 : ℚ) < localMersennePrefixValue
      (insert d (halfGreedyPrefixSupport (d - 1))) := by
  have hskipRat : ¬ mersenneWeightRat d ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1) := by
    intro htakeRat
    apply hskip
    have htakeReal :=
      (rational_greedy_take_iff_real (1 / 2 : ℚ) (d - 1)).1
        (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using htakeRat)
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using htakeReal
  have hrem :
      greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1) =
        (1 / 2 : ℚ) -
          localMersennePrefixValue (halfGreedyPrefixSupport (d - 1)) := by
    simpa [halfGreedyPrefixSupport] using
      (greedyMersenneRemainderRat_eq_sub_finiteErdosSum
        (1 / 2 : ℚ) (d - 1))
  have hbelow := halfGreedyPrefixSupport_pred_below d hd
  have hdnot : d ∉ halfGreedyPrefixSupport (d - 1) := by
    intro hmem
    exact (Nat.lt_irrefl d) (hbelow d hmem).2
  have hinsert :
      localMersennePrefixValue
          (insert d (halfGreedyPrefixSupport (d - 1))) =
        localMersennePrefixValue (halfGreedyPrefixSupport (d - 1)) +
          mersenneWeightRat d := by
    unfold localMersennePrefixValue
    rw [Finset.sum_insert hdnot]
    ring
  have hgap :
      greedyMersenneRemainderRat (1 / 2 : ℚ) (d - 1) <
        mersenneWeightRat d := lt_of_not_ge hskipRat
  rw [hrem] at hgap
  rw [hinsert]
  linarith

/-- Two-shell certificate for a first positive-residual midpoint mismatch.
The first shell forces the unique seam word and remainder `R+1`; the next
short window must then cross the displayed weighted incidence threshold. -/
theorem midpointRealSkip_forces_seamSecondShellCertificate
    {d R L : ℕ} (hd : 3 ≤ d) (hR : 1 ≤ R)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1))
    (hlook : 2 * Nat.sqrt (2 * d + L) + 3 ≤ 2 ^ L)
    (hcross : (1 : ℚ) / 2 < localMersennePrefixValue
      (insert d (halfGreedyPrefixSupport (d - 1)))) :
    stemBits d (halfGreedyPrefixSupport (d - 1)) =
        integerGreedyBits (seamWeights d) (seamSubsetTarget d) ∧
      seamIntegerGreedyRemainder d = R + 1 ∧
      (R - 1) * 2 ^ L <
        finiteCoeffWindowNumerator
          (↑(insert d (halfGreedyPrefixSupport (d - 1))) : Set ℕ)
          (2 * d) L := by
  obtain ⟨halign, hrem⟩ :=
    midpointRealSkip_forces_seamAlignment_and_remainder hd hskip hrow
  refine ⟨halign, hrem, ?_⟩
  exact aboveMidpointResidual_pred_mul_pow_lt_finiteCoeffWindowNumerator
    (D := halfGreedyPrefixSupport (d - 1)) (d := d) (R := R) (L := L)
      (by omega) hR (halfGreedyPrefixSupport_pred_below d (by omega))
      hrow hlook hcross

/-- Actual-orbit form of the two-shell certificate.  The real-skip
hypothesis already forces the hypothetical inserted prefix above one half,
so no separate phase premise remains. -/
theorem midpointRealSkip_forces_seamSecondShellCertificate_autoCross
    {d R L : ℕ} (hd : 3 ≤ d) (hR : 1 ≤ R)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hrow :
      localPrefixQuotient
          (insert d (halfGreedyPrefixSupport (d - 1))) (2 * d) + R =
        2 ^ (2 * d - 1))
    (hlook : 2 * Nat.sqrt (2 * d + L) + 3 ≤ 2 ^ L) :
    stemBits d (halfGreedyPrefixSupport (d - 1)) =
        integerGreedyBits (seamWeights d) (seamSubsetTarget d) ∧
      seamIntegerGreedyRemainder d = R + 1 ∧
      (R - 1) * 2 ^ L <
        finiteCoeffWindowNumerator
          (↑(insert d (halfGreedyPrefixSupport (d - 1))) : Set ℕ)
          (2 * d) L := by
  exact midpointRealSkip_forces_seamSecondShellCertificate
    hd hR hskip hrow hlook
      (insert_halfGreedyPrefixSupport_gt_half_of_realSkip (by omega) hskip)

/-- Cofinal target-zero quotient rows put `1/2` in the closed Mersenne
achievement set. -/
theorem half_mem_mersenneAchievementSet_of_cofinalExactAboveLocalRows
    (hcofinal : CofinalExactAboveLocalMersenneHalfRows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  unfold CofinalExactAboveLocalMersenneHalfRows at hcofinal
  have hsupply : ∀ N : ℕ, ∃ n : ℕ,
      max N 2 ≤ n ∧ ExactAboveLocalMersenneHalfRow n := fun N ↦
    hcofinal (max N 2)
  choose n hn hrow using hsupply
  simp only [ExactAboveLocalMersenneHalfRow] at hrow
  choose D hD hquot using hrow
  let y : ℕ → ℝ := fun N ↦ exactLocalMersenneRowValue (D N)
  have hn2 : ∀ N : ℕ, 2 ≤ n N := by
    intro N
    exact (le_max_right N 2).trans (hn N)
  have hntop : Tendsto n atTop atTop := by
    exact tendsto_atTop_mono
      (fun N ↦ (le_max_left N 2).trans (hn N)) tendsto_id
  have hbound : ∀ N : ℕ,
      |y N - (1 : ℝ) / 2| ≤
        ((n N + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n N) := by
    intro N
    exact abs_exactAboveLocalMersenneRowValue_sub_half_le
      (hn2 N) (hD N) (hquot N)
  have hy : Tendsto y atTop (nhds ((1 : ℝ) / 2)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have habs : Tendsto (fun N : ℕ ↦ |y N - (1 : ℝ) / 2|)
        atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun N ↦ abs_nonneg _
      · exact Filter.Eventually.of_forall hbound
      · exact tendsto_nat_succ_div_two_pow_zero.comp hntop
    simpa [Real.norm_eq_abs] using habs
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall fun N ↦
      exactLocalMersenneRowValue_mem_mersenneAchievementSet
        (fun d hd ↦ (hD N d hd).1))

/-- The cofinal target-zero producer supplies an infinite support of exact
rational value `1/2`. -/
theorem exists_rational_half_counterexample_of_cofinalExactAboveLocalRows
    (hcofinal : CofinalExactAboveLocalMersenneHalfRows) :
    ∃ A : Set ℕ, A.Infinite ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  obtain ⟨A, hA0, hhalf⟩ :=
    half_mem_mersenneAchievementSet_of_cofinalExactAboveLocalRows hcofinal
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hhalf.symm
  refine ⟨A, ?_, hseries⟩
  intro hfinite
  exact finite_boolSupport_ne_half A hfinite hA0 hseries

/-- Consequently the cofinal target-zero producer refutes the universal
irrationality statement. -/
theorem not_universal_of_cofinalExactAboveLocalRows
    (hcofinal : CofinalExactAboveLocalMersenneHalfRows) :
    ¬ UniversalMersenneSubseriesIrrationality := by
  obtain ⟨A, hA, hhalf⟩ :=
    exists_rational_half_counterexample_of_cofinalExactAboveLocalRows hcofinal
  intro huniversal
  have hirr := huniversal A hA
  rw [hhalf] at hirr
  have hcast : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
  rw [hcast] at hirr
  exact (Rat.not_irrational (1 / 2 : ℚ)) hirr

/-! ## The rational target `1/21` cannot terminate -/

/-- No finite Boolean support on the genuine reciprocal-Mersenne ranks can
sum to `1/21`.  The reduced-denominator order theorem forces the support lcm
to be six, hence every selected rank is one of `2`, `3`, or `6`; the eight
remaining finite possibilities are then exact arithmetic.

Consequently, if a representation of `1/21` is first reduced to Boolean
support using only ranks at least two, this theorem rules out finite support.
The existence of such a representation is not proved here. -/
theorem finiteErdosSum_ne_one_div_twenty_one
    (F : Finset ℕ) (hF : ∀ n ∈ F, 2 ≤ n) :
    finiteErdosSum F 2 ≠ (1 : ℚ) / 21 := by
  intro heq
  have h0 : 0 ∉ F := by
    intro hzero
    have := hF 0 hzero
    omega
  have hne : F.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at heq
    norm_num [finiteErdosSum] at heq
  have horder :=
    oddDoublingOrder_finiteErdosSum_den_eq_lcm F hne h0
  have hden : (finiteErdosSum F 2).den = 21 := by
    rw [heq]
    norm_num
  have horder' :
      oddDoublingOrder 21 (by decide : Odd 21) = F.lcm id := by
    simpa only [hden] using horder
  have horder21 : oddDoublingOrder 21 (by decide : Odd 21) = 6 :=
    two_three_dyadicPrefix_fixture.2.2.1
  rw [horder21] at horder'
  have hlcm : F.lcm id = 6 := horder'.symm
  have hlcm' : F.lcm (fun m : ℕ ↦ m) = 6 := by
    simpa only [id_eq] using hlcm
  have hranks : ∀ n ∈ F, n = 2 ∨ n = 3 ∨ n = 6 := by
    intro n hn
    have hndvd : n ∣ 6 := by
      rw [← hlcm']
      exact Finset.dvd_lcm (f := fun m : ℕ ↦ m) hn
    have hnle : n ≤ 6 := Nat.le_of_dvd (by omega) hndvd
    obtain ⟨k, hk⟩ := hndvd
    have hn2 := hF n hn
    interval_cases n <;> omega
  have hF_eq :
      F = ({2, 3, 6} : Finset ℕ).filter (fun n ↦ n ∈ F) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hn
      exact ⟨hranks n hn, hn⟩
    · exact fun hn ↦ hn.2
  by_cases h2 : 2 ∈ F <;>
    by_cases h3 : 3 ∈ F <;>
      by_cases h6 : 6 ∈ F <;> {
        rw [hF_eq] at heq
        simp only [finiteErdosSum, Finset.sum_filter] at heq
        norm_num [finiteErdosSum, h2, h3, h6] at heq
      }

#print axioms abs_exactAboveLocalMersenneRowValue_sub_half_le
#print axioms exists_rational_half_counterexample_of_cofinalEvenCoreBound
#print axioms not_universal_of_cofinalEvenCoreBound
#print axioms localMersennePrefixValue_le_half_of_aboveResidual_card
#print axioms aboveResidual_lt_card_of_half_lt_localMersennePrefixValue
#print axioms aboveMidpointResidual_lt_rank_of_real_crossing
#print axioms localFractionMass_cast_eq_binaryCoeffTail
#print axioms localFractionMass_cast_le_two_sqrt_add_four
#print axioms localFractionMass_cast_lt_two_natSqrt_add_three
#print axioms residual_sub_one_lt_finiteCoeffWindow_of_phase
#print axioms residual_pred_mul_pow_lt_finiteCoeffWindowNumerator_of_phase
#print axioms residual_pred_mul_pow_lt_finiteCoeffWindowNumerator_of_phase_of_sqrt
#print axioms aboveResidual_lt_fractionMass_of_half_lt_localMersennePrefixValue
#print axioms half_lt_localMersennePrefixValue_iff_residual_lt_fractionMass
#print axioms aboveResidual_pred_mul_pow_lt_finiteCoeffWindowNumerator
#print axioms localMersennePrefixValue_le_half_of_finiteCoeffWindowNumerator
#print axioms aboveResidual_cast_lt_two_sqrt_add_four
#print axioms aboveResidual_lt_two_natSqrt_add_three
#print axioms aboveMidpointResidual_cast_lt_two_sqrt_add_four_of_real_crossing
#print axioms aboveMidpointResidual_lt_two_natSqrt_add_three_of_real_crossing
#print axioms aboveMidpointResidual_pred_mul_pow_lt_finiteCoeffWindowNumerator
#print axioms midpointPrefix_le_half_of_finiteCoeffWindowNumerator
#print axioms greedyHalfFrozenMargin_fullShell_eq_neg_residual_succ_of_midpointRow
#print axioms exists_midpointRow_of_fullShell_neg
#print axioms midpointRealSkip_forces_seamAlignment_and_remainder
#print axioms midpointRealSkip_forces_residual_le_seamSupportCard
#print axioms midpointRealSkip_forces_seamRemainder_lt_rank
#print axioms midpointRow_realTake_of_seamRemainderCardGapFromEight
#print axioms insert_halfGreedyPrefixSupport_gt_half_of_realSkip
#print axioms midpointRealSkip_forces_seamSecondShellCertificate
#print axioms midpointRealSkip_forces_seamSecondShellCertificate_autoCross
#print axioms half_mem_mersenneAchievementSet_of_cofinalExactAboveLocalRows
#print axioms exists_rational_half_counterexample_of_cofinalExactAboveLocalRows
#print axioms not_universal_of_cofinalExactAboveLocalRows

end ErdosProblems.Erdos257
