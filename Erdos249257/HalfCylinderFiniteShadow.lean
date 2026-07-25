import Erdos249257.HalfCarryReachability
import Erdos249257.PrimitiveSupportBridge
import Erdos249257.DyadicPrefixCompression

/-!
# Finite shadows of the half-carry strip

This module records consequences that do not depend on the open global
cylinder induction.  Every admissible finite word satisfies an exact
half-residual formula and an explicit Archimedean upper bound.  A coefficient
word with the boundary-pair difference pattern has carry difference exactly
one throughout the prescribed pre-feedback interval.  Finally, the first-wrap
endpoint is reduced to one exact integer seam hole, together with an explicit
greedy witness showing that raw-block safety does not itself force seam escape.

Neither statement proves the linear escape estimate required for global
no-wrap.  The second theorem also shows why the coefficient equations alone
do not contradict the boundary pair before its first feedback row.
-/

namespace Erdos249257.HalfCylinderFiniteShadow

open Set
open HalfCarryReachability

/-- A finite word has no support beyond its declared depth. -/
theorem wordSupport_subset_Iic {N : ℕ} (a : HalfWord N) :
    wordSupport a ⊆ Set.Iic N := by
  intro n hn
  exact Nat.le_of_lt_succ hn.1

/-- Intersecting the support of a depth-`N` word with `Iic N` changes
nothing. -/
@[simp] theorem wordSupport_inter_Iic {N : ℕ} (a : HalfWord N) :
    wordSupport a ∩ Set.Iic N = wordSupport a :=
  Set.inter_eq_left.mpr (wordSupport_subset_Iic a)

/-- Admissibility at a positive depth excludes exponent one from the word
support. -/
theorem one_not_mem_wordSupport_of_admissible
    {N : ℕ} (a : HalfWord N)
    (ha : HalfStripAdmissible N a) :
    1 ∉ wordSupport a := by
  rintro ⟨h, htrue⟩
  have hfalse := ha.2.1 (show 1 < N + 1 by omega)
  have hidx : (⟨1, h⟩ : Fin (N + 1)) =
      ⟨1, show 1 < N + 1 by omega⟩ := Fin.ext (by rfl)
  rw [hidx, hfalse] at htrue
  contradiction

/-- **Exact finite-shadow identity.**  For an admissible word at positive
depth `N`, the discrepancy of its finite Mersenne support sum from `1/2` is
the terminal integer half carry minus the future-multiple coefficient tail,
scaled by `2^N`. -/
theorem halfStripAdmissible_residual_eq
    {N : ℕ} (hN : 1 ≤ N) (a : HalfWord N)
    (ha : HalfStripAdmissible N a) :
    (1 : ℝ) / 2 - erdosSupportSeries 2 (wordSupport a) =
      ((integerHalfCarry (wordSupport a) (N - 1) : ℤ) -
        binaryCoeffTail (supportCoeff (wordSupport a)) N) /
          (2 : ℝ) ^ N := by
  have hone := one_not_mem_wordSupport_of_admissible a ha
  have hres :=
    halfFinitePrefix_residual_eq_pow_mul_integerCarry_sub_finiteTail
      (wordSupport a) hone (N - 1)
  simpa [integerHalfCarry, Nat.sub_add_cancel hN] using hres

/-! ## Finite future-incidence producer -/

/-- The first `J` coefficient rows strictly inside the complete analytic
tail after row `n`. -/
noncomputable def finiteCoeffWindow
    (A : Set ℕ) (n J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J,
    (supportCoeff A (n + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

/-- Exact carry-coordinate form of normalized raw half slack.  The index
`n-1` is essential: its coefficient horizon ends at row `n`, while the
analytic tail begins at row `n+1`. -/
theorem one_sub_pow_mul_halfResidual_eq_tail_sub_centered
    (A : Set ℕ) (hone : 1 ∉ A) (n : ℕ) (hn : 1 ≤ n) :
    1 - (2 : ℝ) ^ n *
        ((1 : ℝ) / 2 - erdosSupportSeries 2 A) =
      binaryCoeffTail (supportCoeff A) n -
        (mobiusCenteredHalfCarry A (n - 1) : ℝ) := by
  have hindex : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hcarry := integerHalfCarry_eq_scaled_residual_add_tail
    A hone (n - 1)
  rw [hindex] at hcarry
  unfold mobiusCenteredHalfCarry
  push_cast
  linarith

/-- Every finite coefficient window is termwise below the complete analytic
tail.  This strict truncation is what makes the next theorem a sufficient
producer rather than an equivalent restatement of raw safety. -/
theorem finiteCoeffWindow_le_binaryCoeffTail
    (A : Set ℕ) (n J : ℕ) :
    finiteCoeffWindow A n J ≤
      binaryCoeffTail (supportCoeff A) n := by
  have hsum : Summable (fun j : ℕ ↦
      (supportCoeff A (n + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) :=
    summable_coeff_shift_tail 2 n (supportCoeff A)
      (by norm_num) (supportCoeff_le_self A)
  unfold finiteCoeffWindow binaryCoeffTail
  exact hsum.sum_le_tsum (Finset.range J) (fun j _ ↦ by positivity)

/-- Any named future coefficient contributes its own dyadically weighted
term to the complete tail.  This one-row projection is the reusable bridge
for arithmetic sieves that locate a divisor incidence at a nonconstant
offset, where choosing a whole `finiteCoeffWindow` would obscure the exact
source row. -/
theorem coeff_term_le_binaryCoeffTail
    (A : Set ℕ) (n j : ℕ) :
    (supportCoeff A (n + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) ≤
      binaryCoeffTail (supportCoeff A) n := by
  have hsum : Summable (fun k : ℕ ↦
      (supportCoeff A (n + k + 1) : ℝ) / (2 : ℝ) ^ (k + 1)) :=
    summable_coeff_shift_tail 2 n (supportCoeff A)
      (by norm_num) (supportCoeff_le_self A)
  unfold binaryCoeffTail
  have hsingle := hsum.sum_le_tsum ({j} : Finset ℕ) (fun k _ ↦ by positivity)
  simpa using hsingle

/-- A finite future-divisor incidence inequality forces the normalized
residual below one.  The remaining unbounded problem is precisely to produce
`hwindow` on every actual greedy prefix. -/
theorem scaledHalfResidual_le_one_of_finiteCoeffWindow
    (A : Set ℕ) (hone : 1 ∉ A) (n J : ℕ) (hn : 1 ≤ n)
    (hwindow :
      (mobiusCenteredHalfCarry A (n - 1) : ℝ) ≤
        finiteCoeffWindow A n J) :
    (2 : ℝ) ^ n *
        ((1 : ℝ) / 2 - erdosSupportSeries 2 A) ≤ 1 := by
  have htail :
      (mobiusCenteredHalfCarry A (n - 1) : ℝ) ≤
        binaryCoeffTail (supportCoeff A) n :=
    hwindow.trans (finiteCoeffWindow_le_binaryCoeffTail A n J)
  have hid := one_sub_pow_mul_halfResidual_eq_tail_sub_centered
    A hone n hn
  linarith

/-- The same finite-incidence implication in explicitly nonnegative-slack
form. -/
theorem rawHalfSlack_nonneg_of_finiteCoeffWindow
    (A : Set ℕ) (hone : 1 ∉ A) (n J : ℕ) (hn : 1 ≤ n)
    (hwindow :
      (mobiusCenteredHalfCarry A (n - 1) : ℝ) ≤
        finiteCoeffWindow A n J) :
    0 ≤ 1 - (2 : ℝ) ^ n *
        ((1 : ℝ) / 2 - erdosSupportSeries 2 A) := by
  exact sub_nonneg.mpr
    (scaledHalfResidual_le_one_of_finiteCoeffWindow
      A hone n J hn hwindow)

/-! ## Exact future-skip capacity factorization -/

/-- Integer numerator of the frozen coefficient window.  The recurrence
uses the binary weights `2^(J-i)` without division. -/
noncomputable def finiteCoeffWindowNumerator
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * finiteCoeffWindowNumerator A n J +
        supportCoeff A (n + J + 1)

/-- Binary capacity carried by skipped support bits in the next `J` rows.
The earliest skip receives the largest binary weight. -/
noncomputable def futureSkipCapacity
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * futureSkipCapacity A n J +
        (by
          classical
          exact if n + J + 1 ∈ A then 0 else 1)

/-- The recursive numerator is exactly `2^J` times the existing real-valued
finite coefficient window. -/
theorem finiteCoeffWindow_eq_numerator_div_pow
    (A : Set ℕ) (n J : ℕ) :
    finiteCoeffWindow A n J =
      (finiteCoeffWindowNumerator A n J : ℝ) / (2 : ℝ) ^ J := by
  induction J with
  | zero => simp [finiteCoeffWindow, finiteCoeffWindowNumerator]
  | succ J ih =>
      calc
        finiteCoeffWindow A n (J + 1) =
            finiteCoeffWindow A n J +
              (supportCoeff A (n + J + 1) : ℝ) / (2 : ℝ) ^ (J + 1) := by
          simp [finiteCoeffWindow, Finset.sum_range_succ]
        _ = (finiteCoeffWindowNumerator A n J : ℝ) / (2 : ℝ) ^ J +
              (supportCoeff A (n + J + 1) : ℝ) / (2 : ℝ) ^ (J + 1) := by
          rw [ih]
        _ = (finiteCoeffWindowNumerator A n (J + 1) : ℝ) /
              (2 : ℝ) ^ (J + 1) := by
          simp only [finiteCoeffWindowNumerator, Nat.cast_add, Nat.cast_mul,
            Nat.cast_ofNat, pow_succ]
          ring

/-- Exact decomposition of the complete coefficient tail into its first
`J` rows and the shifted complete tail that remains. -/
theorem binaryCoeffTail_eq_finiteCoeffWindow_add_shiftedTail
    (A : Set ℕ) (n J : ℕ) :
    binaryCoeffTail (supportCoeff A) n =
      finiteCoeffWindow A n J +
        binaryCoeffTail (supportCoeff A) (n + J) / (2 : ℝ) ^ J := by
  induction J with
  | zero => simp [finiteCoeffWindow]
  | succ J ih =>
      have htail := binaryCoeffTail_succ
        (supportCoeff A) (supportCoeff_le_self A) (n + J)
      calc
        binaryCoeffTail (supportCoeff A) n =
            finiteCoeffWindow A n J +
              binaryCoeffTail (supportCoeff A) (n + J) / (2 : ℝ) ^ J := ih
        _ = finiteCoeffWindow A n (J + 1) +
              binaryCoeffTail (supportCoeff A) (n + (J + 1)) /
                (2 : ℝ) ^ (J + 1) := by
          rw [show n + (J + 1) = n + J + 1 by omega, htail]
          simp only [finiteCoeffWindow, Finset.sum_range_succ, pow_succ]
          ring

/-- **Exact future-skip factorization.**  Freeze the support at depth `n`
and inspect any window `J <= n`.  The weighted frozen incidence surplus is
exactly the binary capacity of actual future skips minus the actual centered
carry at the end of the window. -/
theorem futureSkipCapacity_factorization
    (A : Set ℕ) (n J : ℕ) (hn : 1 ≤ n) (hJ : J ≤ n) :
    (finiteCoeffWindowNumerator (primitivePrefix A n) n J : ℤ) -
        (2 : ℤ) ^ J * mobiusCenteredHalfCarry A (n - 1) =
      (futureSkipCapacity A n J : ℤ) -
        mobiusCenteredHalfCarry A (n - 1 + J) := by
  classical
  induction J with
  | zero => simp [finiteCoeffWindowNumerator, futureSkipCapacity]
  | succ J ih =>
      have ih' := ih (by omega)
      have hshell := supportCoeff_primitiveResidual_first_shell
        A n (n + J + 1) (by omega) (by omega)
      have hsplit := supportCoeff_eq_primitivePrefix_add_residual
        A n (n + J + 1)
      rw [hshell] at hsplit
      have hcarry := mobiusCenteredHalfCarry_succ A (n - 1 + J)
      have hrow : n - 1 + J + 2 = n + J + 1 := by omega
      rw [hrow] at hcarry
      have hnext : n - 1 + (J + 1) = n - 1 + J + 1 := by omega
      calc
        (finiteCoeffWindowNumerator (primitivePrefix A n) n (J + 1) : ℤ) -
              (2 : ℤ) ^ (J + 1) * mobiusCenteredHalfCarry A (n - 1) =
            2 * ((finiteCoeffWindowNumerator (primitivePrefix A n) n J : ℤ) -
              (2 : ℤ) ^ J * mobiusCenteredHalfCarry A (n - 1)) +
              (supportCoeff (primitivePrefix A n) (n + J + 1) : ℤ) := by
          simp only [finiteCoeffWindowNumerator, Nat.cast_add, Nat.cast_mul,
            Nat.cast_ofNat, pow_succ]
          ring
        _ = 2 * ((futureSkipCapacity A n J : ℤ) -
              mobiusCenteredHalfCarry A (n - 1 + J)) +
              (supportCoeff (primitivePrefix A n) (n + J + 1) : ℤ) := by
          rw [ih']
        _ = (futureSkipCapacity A n (J + 1) : ℤ) -
              mobiusCenteredHalfCarry A (n - 1 + (J + 1)) := by
          rw [hnext, hcarry, hsplit]
          by_cases hmem : n + J + 1 ∈ A
          · simp [futureSkipCapacity, primitiveBit, hmem]
            ring
          · simp [futureSkipCapacity, primitiveBit, hmem]
            ring

/-- Integer form of the exact producer: the frozen coefficient numerator
covers the initial centered carry iff the future skip word covers the actual
terminal centered carry. -/
theorem finiteCoeffWindowNumerator_covers_iff_terminal_le_skipCapacity
    (A : Set ℕ) (n J : ℕ) (hn : 1 ≤ n) (hJ : J ≤ n) :
    (2 : ℤ) ^ J * mobiusCenteredHalfCarry A (n - 1) ≤
        (finiteCoeffWindowNumerator (primitivePrefix A n) n J : ℤ) ↔
      mobiusCenteredHalfCarry A (n - 1 + J) ≤
        (futureSkipCapacity A n J : ℤ) := by
  have hid := futureSkipCapacity_factorization A n J hn hJ
  constructor
  · intro h
    have hnonneg : 0 ≤
        (finiteCoeffWindowNumerator (primitivePrefix A n) n J : ℤ) -
          (2 : ℤ) ^ J * mobiusCenteredHalfCarry A (n - 1) :=
      sub_nonneg.mpr h
    rw [hid] at hnonneg
    exact sub_nonneg.mp hnonneg
  · intro h
    have hnonneg : 0 ≤
        (futureSkipCapacity A n J : ℤ) -
          mobiusCenteredHalfCarry A (n - 1 + J) :=
      sub_nonneg.mpr h
    rw [← hid] at hnonneg
    exact sub_nonneg.mp hnonneg

/-- Real-valued form consumed by `scaledHalfResidual_le_one_of_finiteCoeffWindow`.
The finite-incidence hypothesis is not merely sufficient on the first shell:
it is exactly terminal-carry coverage by the actual future skip word. -/
theorem finiteCoeffWindow_covers_iff_terminal_le_skipCapacity
    (A : Set ℕ) (n J : ℕ) (hn : 1 ≤ n) (hJ : J ≤ n) :
    (mobiusCenteredHalfCarry A (n - 1) : ℝ) ≤
        finiteCoeffWindow (primitivePrefix A n) n J ↔
      mobiusCenteredHalfCarry A (n - 1 + J) ≤
        (futureSkipCapacity A n J : ℤ) := by
  rw [finiteCoeffWindow_eq_numerator_div_pow]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  constructor
  · intro h
    have hscaled : (2 : ℝ) ^ J *
          (mobiusCenteredHalfCarry A (n - 1) : ℝ) ≤
        (finiteCoeffWindowNumerator (primitivePrefix A n) n J : ℝ) :=
      by simpa [mul_comm] using (le_div_iff₀ hpow).mp h
    have hscaledZ : (2 : ℤ) ^ J *
          mobiusCenteredHalfCarry A (n - 1) ≤
        (finiteCoeffWindowNumerator (primitivePrefix A n) n J : ℤ) := by
      exact_mod_cast hscaled
    exact (finiteCoeffWindowNumerator_covers_iff_terminal_le_skipCapacity
      A n J hn hJ).mp hscaledZ
  · intro h
    have hscaledZ :=
      (finiteCoeffWindowNumerator_covers_iff_terminal_le_skipCapacity
        A n J hn hJ).mpr h
    have hscaled : (2 : ℝ) ^ J *
          (mobiusCenteredHalfCarry A (n - 1) : ℝ) ≤
        (finiteCoeffWindowNumerator (primitivePrefix A n) n J : ℝ) := by
      exact_mod_cast hscaledZ
    exact (le_div_iff₀ hpow).mpr (by simpa [mul_comm] using hscaled)

/-- A support prefix has reduced tail-gap coordinates `(E,D)` at row `n`
when its centered carry minus its complete coefficient tail is exactly
`E/D`. -/
def ReducedTailGapCoordinates
    (P : Set ℕ) (n : ℕ) (E : ℤ) (D : ℕ) : Prop :=
  0 < D ∧
    (mobiusCenteredHalfCarry P (n - 1) : ℝ) -
        binaryCoeffTail (supportCoeff P) n = (E : ℝ) / (D : ℝ)

/-- The landed half-greedy excess and denominator are literally reduced
tail-gap coordinates for the finite greedy prefix. -/
theorem halfGreedyPrefix_reducedTailGapCoordinates (k : ℕ) :
    ReducedTailGapCoordinates
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1)
      (halfGreedyNextDyadicExcessNumerator k)
      (halfGreedyPrefixDenominator k) := by
  constructor
  · exact Rat.den_pos (halfGreedyPrefixRat k)
  · have hgap := halfGreedyPrefixSupportTailGap_eq_excess_div_denominator k
    simpa [ReducedTailGapCoordinates, halfGreedyPrefixSupportTailGap,
      halfGreedyPrefixIntegerCarry, halfGreedyPrefixCoeffTail,
      mobiusCenteredHalfCarry, integerHalfCarry] using hgap

/-- **Reduced-state skip-capacity identity.**  If the prefix of an actual
support `A` through `n` has reduced coordinates `(E,D)`, then the future-skip
margin is the negative reduced excess, amplified by `2^J`, minus the exact
coefficient tail omitted beyond the finite window.

This is the proof socket

`S_J - e_J = -2^J E/D - R_(n,J)`.
-/
theorem futureSkipCapacityMargin_eq_reducedTailTax
    (A P : Set ℕ) (n J : ℕ) (E : ℤ) (D : ℕ)
    (hn : 1 ≤ n) (hJ : J ≤ n)
    (hprefix : primitivePrefix A n = P)
    (hred : ReducedTailGapCoordinates P n E D) :
    (futureSkipCapacity A n J : ℝ) -
        (mobiusCenteredHalfCarry A (n - 1 + J) : ℝ) =
      -(2 : ℝ) ^ J * ((E : ℝ) / (D : ℝ)) -
        binaryCoeffTail (supportCoeff P) (n + J) := by
  have hcentered :
      mobiusCenteredHalfCarry A (n - 1) =
        mobiusCenteredHalfCarry P (n - 1) := by
    rw [← hprefix]
    unfold primitivePrefix mobiusCenteredHalfCarry
    rw [integerHalfCarry_inter_Iic_eq_of_succ_le A n (n - 1) (by omega)]
  have hcenteredR :
      (mobiusCenteredHalfCarry A (n - 1) : ℝ) =
        (mobiusCenteredHalfCarry P (n - 1) : ℝ) := by
    exact_mod_cast hcentered
  have hidZ := futureSkipCapacity_factorization A n J hn hJ
  have hidR := congrArg (fun z : ℤ ↦ (z : ℝ)) hidZ
  push_cast at hidR
  rw [hprefix] at hidR
  rw [hcenteredR] at hidR
  have hnum := finiteCoeffWindow_eq_numerator_div_pow P n J
  have hpow : (2 : ℝ) ^ J ≠ 0 := by positivity
  have hnumMul :
      finiteCoeffWindow P n J * (2 : ℝ) ^ J =
        (finiteCoeffWindowNumerator P n J : ℝ) :=
    (eq_div_iff hpow).mp hnum
  have htail := binaryCoeffTail_eq_finiteCoeffWindow_add_shiftedTail P n J
  have hgap := hred.2
  calc
    (futureSkipCapacity A n J : ℝ) -
          (mobiusCenteredHalfCarry A (n - 1 + J) : ℝ) =
        (finiteCoeffWindowNumerator P n J : ℝ) -
          (2 : ℝ) ^ J *
            (mobiusCenteredHalfCarry P (n - 1) : ℝ) := by
      exact hidR.symm
    _ = (2 : ℝ) ^ J *
          (finiteCoeffWindow P n J -
            (mobiusCenteredHalfCarry P (n - 1) : ℝ)) := by
      rw [← hnumMul]
      ring
    _ = (2 : ℝ) ^ J *
          (-((E : ℝ) / (D : ℝ)) -
            binaryCoeffTail (supportCoeff P) (n + J) / (2 : ℝ) ^ J) := by
      congr 1
      linarith [htail, hgap]
    _ = -(2 : ℝ) ^ J * ((E : ℝ) / (D : ℝ)) -
          binaryCoeffTail (supportCoeff P) (n + J) := by
      field_simp [hpow]

/-- Coverage by the future skip word is exactly the reduced tail-tax
inequality. -/
theorem futureSkipCoverage_iff_reducedTailTax
    (A P : Set ℕ) (n J : ℕ) (E : ℤ) (D : ℕ)
    (hn : 1 ≤ n) (hJ : J ≤ n)
    (hprefix : primitivePrefix A n = P)
    (hred : ReducedTailGapCoordinates P n E D) :
    mobiusCenteredHalfCarry A (n - 1 + J) ≤
        (futureSkipCapacity A n J : ℤ) ↔
      binaryCoeffTail (supportCoeff P) (n + J) ≤
        -(2 : ℝ) ^ J * ((E : ℝ) / (D : ℝ)) := by
  have hid := futureSkipCapacityMargin_eq_reducedTailTax
    A P n J E D hn hJ hprefix hred
  constructor
  · intro h
    have hR :
        (mobiusCenteredHalfCarry A (n - 1 + J) : ℝ) ≤
          (futureSkipCapacity A n J : ℝ) := by
      exact_mod_cast h
    linarith
  · intro h
    have hR :
        (mobiusCenteredHalfCarry A (n - 1 + J) : ℝ) ≤
          (futureSkipCapacity A n J : ℝ) := by
      linarith
    exact_mod_cast hR

/-- One-step permanence: once future skip capacity covers the actual
centered carry, the next first-shell row remains covered. -/
theorem futureSkipCoverage_succ
    (A : Set ℕ) (n t : ℕ) (hn : 1 ≤ n) (ht : t + 1 ≤ n)
    (hcover : mobiusCenteredHalfCarry A (n - 1 + t) ≤
      (futureSkipCapacity A n t : ℤ)) :
    mobiusCenteredHalfCarry A (n - 1 + (t + 1)) ≤
      (futureSkipCapacity A n (t + 1) : ℤ) := by
  classical
  have hshell := supportCoeff_primitiveResidual_first_shell
    A n (n + t + 1) (by omega) (by omega)
  have hsplit := supportCoeff_eq_primitivePrefix_add_residual
    A n (n + t + 1)
  rw [hshell] at hsplit
  have hcarry := mobiusCenteredHalfCarry_succ A (n - 1 + t)
  have hrow : n - 1 + t + 2 = n + t + 1 := by omega
  rw [hrow] at hcarry
  have hnext : n - 1 + (t + 1) = n - 1 + t + 1 := by omega
  rw [hnext, hcarry, hsplit]
  by_cases hmem : n + t + 1 ∈ A
  · simp [futureSkipCapacity, primitiveBit, hmem]
    omega
  · simp [futureSkipCapacity, primitiveBit, hmem]
    omega

/-- **First-shell persistence.**  Coverage at any intermediate time remains
true at every later time that stays inside the first dyadic shell. -/
theorem futureSkipCoverage_persistent
    (A : Set ℕ) (n t u : ℕ) (hn : 1 ≤ n) (htu : t + u ≤ n)
    (hcover : mobiusCenteredHalfCarry A (n - 1 + t) ≤
      (futureSkipCapacity A n t : ℤ)) :
    mobiusCenteredHalfCarry A (n - 1 + (t + u)) ≤
      (futureSkipCapacity A n (t + u) : ℤ) := by
  induction u with
  | zero => simpa using hcover
  | succ u ih =>
      have ih' := ih (by omega)
      have hstep := futureSkipCoverage_succ A n (t + u) hn (by omega) ih'
      simpa [Nat.add_assoc] using hstep

/-- Every omitted row contributes its own binary weight to the total skip
capacity.  In particular, the earliest skip is the strongest single-row
certificate. -/
theorem futureSkipWeight_le_capacity_of_not_mem
    (A : Set ℕ) (n J i : ℕ) (hi : i < J)
    (hskip : n + i + 1 ∉ A) :
    2 ^ (J - (i + 1)) ≤ futureSkipCapacity A n J := by
  classical
  induction J generalizing i with
  | zero => omega
  | succ J ih =>
      by_cases hiJ : i = J
      · subst i
        simp [futureSkipCapacity, hskip]
      · have hi' : i < J := by omega
        have hprev := ih i hi' hskip
        have hexp : J + 1 - (i + 1) = (J - (i + 1)) + 1 := by omega
        rw [hexp, pow_succ]
        by_cases hlast : n + J + 1 ∈ A
        · simp [futureSkipCapacity, hlast]
          simpa [mul_comm] using Nat.mul_le_mul_right 2 hprev
        · simp [futureSkipCapacity, hlast]
          have hdouble := Nat.mul_le_mul_right 2 hprev
          omega

/-- One sufficiently early actual skip is therefore enough to establish the
finite incidence producer.  The governed receipt tests precisely this
stronger one-skip condition with `i` chosen as the first future skip. -/
theorem finiteCoeffWindow_covers_of_one_future_skip
    (A : Set ℕ) (n J i : ℕ) (hn : 1 ≤ n) (hJ : J ≤ n)
    (hi : i < J) (hskip : n + i + 1 ∉ A)
    (hterminal : mobiusCenteredHalfCarry A (n - 1 + J) ≤
      (2 ^ (J - (i + 1)) : ℕ)) :
    (mobiusCenteredHalfCarry A (n - 1) : ℝ) ≤
      finiteCoeffWindow (primitivePrefix A n) n J := by
  apply (finiteCoeffWindow_covers_iff_terminal_le_skipCapacity
    A n J hn hJ).mpr
  have hweight := futureSkipWeight_le_capacity_of_not_mem
    A n J i hi hskip
  have hweightZ : (2 ^ (J - (i + 1)) : ℕ) ≤
      (futureSkipCapacity A n J : ℤ) := by
    exact_mod_cast hweight
  exact hterminal.trans hweightZ

/-- The exact skip-capacity condition feeds the already-landed residual
consumer for the frozen prefix. -/
theorem scaledPrefixHalfResidual_le_one_of_terminal_le_skipCapacity
    (A : Set ℕ) (hone : 1 ∉ A) (n J : ℕ)
    (hn : 1 ≤ n) (hJ : J ≤ n)
    (hterminal : mobiusCenteredHalfCarry A (n - 1 + J) ≤
      (futureSkipCapacity A n J : ℤ)) :
    (2 : ℝ) ^ n *
        ((1 : ℝ) / 2 - erdosSupportSeries 2 (primitivePrefix A n)) ≤ 1 := by
  have hwindow :=
    (finiteCoeffWindow_covers_iff_terminal_le_skipCapacity
      A n J hn hJ).mpr hterminal
  have hcentered :
      mobiusCenteredHalfCarry (primitivePrefix A n) (n - 1) =
        mobiusCenteredHalfCarry A (n - 1) := by
    unfold primitivePrefix mobiusCenteredHalfCarry
    rw [integerHalfCarry_inter_Iic_eq_of_succ_le A n (n - 1) (by omega)]
  apply scaledHalfResidual_le_one_of_finiteCoeffWindow
    (primitivePrefix A n) (by simp [primitivePrefix, hone]) n J hn
  rwa [hcentered]

/-- **Finite-shadow upper bound.**  An admissible finite word is within
`(4√N+8)/2^N` of `1/2`.  This is an unconditional finite theorem; it does
not assert that such words exist at every depth. -/
theorem halfStripAdmissible_abs_residual_le
    {N : ℕ} (hN : 1 ≤ N) (a : HalfWord N)
    (ha : HalfStripAdmissible N a) :
    |(1 : ℝ) / 2 - erdosSupportSeries 2 (wordSupport a)| ≤
      (4 * Real.sqrt (N : ℝ) + 8) / (2 : ℝ) ^ N := by
  rw [halfStripAdmissible_residual_eq hN a ha, abs_div,
    abs_of_pos (show (0 : ℝ) < (2 : ℝ) ^ N by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hcarry := ha.2.2 N hN le_rfl
  have hcarryNonneg :
      (0 : ℝ) ≤ (integerHalfCarry (wordSupport a) (N - 1) : ℤ) := by
    exact_mod_cast (show (0 : ℤ) ≤
      integerHalfCarry (wordSupport a) (N - 1) by omega)
  have hcarryUpper :
      ((integerHalfCarry (wordSupport a) (N - 1) : ℤ) : ℝ) ≤
        2 * Real.sqrt (N : ℝ) + 4 := by
    have hboundR :
        ((integerHalfCarry (wordSupport a) (N - 1) : ℤ) : ℝ) ≤
          (halfStripBound N : ℕ) := by
      exact_mod_cast hcarry.2
    have hsqrt : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    unfold halfStripBound at hboundR
    push_cast at hboundR
    linarith
  have htailNonneg :
      (0 : ℝ) ≤ binaryCoeffTail (supportCoeff (wordSupport a)) N :=
    binaryCoeffTail_nonneg _ _
  have htailUpper :
      binaryCoeffTail (supportCoeff (wordSupport a)) N ≤
        2 * Real.sqrt (N : ℝ) + 4 :=
    binaryCoeffTail_supportCoeff_le_two_sqrt_add_four (wordSupport a) N
  calc
    |((integerHalfCarry (wordSupport a) (N - 1) : ℤ) : ℝ) -
          binaryCoeffTail (supportCoeff (wordSupport a)) N| ≤
        |((integerHalfCarry (wordSupport a) (N - 1) : ℤ) : ℝ)| +
          |binaryCoeffTail (supportCoeff (wordSupport a)) N| :=
      abs_sub _ _
    _ = ((integerHalfCarry (wordSupport a) (N - 1) : ℤ) : ℝ) +
          binaryCoeffTail (supportCoeff (wordSupport a)) N := by
      rw [abs_of_nonneg hcarryNonneg, abs_of_nonneg htailNonneg]
    _ ≤ (2 * Real.sqrt (N : ℝ) + 4) +
          (2 * Real.sqrt (N : ℝ) + 4) :=
      add_le_add hcarryUpper htailUpper
    _ = 4 * Real.sqrt (N : ℝ) + 8 := by ring

/-- **Pre-feedback gauge symmetry.**  Suppose two support-coefficient words
agree up to the carry immediately before row `s`, the left word has one
additional coefficient at row `s`, and the right word has one additional
coefficient at every later row through `n`.  Their integer half carries then
differ by exactly one at every row from `s` through `n`.

This isolates the named pre-feedback no-go: the recurrence and Boolean-sized
coefficient difference pattern are jointly consistent on the whole window,
so a contradiction must use information not represented by those local
equations. -/
theorem preFeedbackGaugeSymmetry
    (left right : Set ℕ) (s n : ℕ) (hs : 2 ≤ s) (hsn : s ≤ n)
    (hbase : integerHalfCarry right (s - 2) =
      integerHalfCarry left (s - 2))
    (hseam : supportCoeff right s + 1 = supportCoeff left s)
    (htail : ∀ m : ℕ, s < m → m ≤ n →
      supportCoeff right m = supportCoeff left m + 1) :
    integerHalfCarry right (n - 1) =
      integerHalfCarry left (n - 1) + 1 := by
  have hclaim : ∀ m : ℕ, s ≤ m → m ≤ n →
      integerHalfCarry right (m - 1) =
        integerHalfCarry left (m - 1) + 1 := by
    intro m hsm
    induction m, hsm using Nat.le_induction with
    | base =>
        intro _
        rw [show s - 1 = (s - 2) + 1 by omega,
          integerHalfCarry_succ, integerHalfCarry_succ]
        have hscoeff : s - 2 + 2 = s := by omega
        rw [hscoeff]
        omega
    | succ m hsm' ih =>
        intro hmn
        have ih' := ih (by omega)
        rw [show m + 1 - 1 = (m - 1) + 1 by omega,
          integerHalfCarry_succ, integerHalfCarry_succ]
        have hmcoeff : m - 1 + 2 = m + 1 := by omega
        rw [hmcoeff]
        have hcoeff := htail (m + 1) (by omega) hmn
        push_cast at hcoeff
        omega
  exact hclaim n hsn le_rfl

/-! ## Exact first-feedback arithmetic -/

/-- Inserting one previously absent divisor adds exactly one to the Boolean
divisor coefficient at that row. -/
theorem supportCoeff_insert_divisor
    (A : Set ℕ) {d n : ℕ} (hd : d ∈ n.divisors) (hdA : d ∉ A) :
    supportCoeff (insert d A) n = supportCoeff A n + 1 := by
  classical
  rw [supportCoeff_eq_card_filter, supportCoeff_eq_card_filter]
  have hfilter :
      n.divisors.filter (fun e => e ∈ insert d A) =
        insert d (n.divisors.filter fun e => e ∈ A) := by
    ext e
    by_cases hed : e = d
    · subst e
      simp [hd]
    · simp [hed]
  rw [hfilter]
  simp [hdA]

/-- Adding the current row itself to a support increases its divisor-count
coefficient by exactly one. -/
theorem supportCoeff_insert_self
    (A : Set ℕ) {n : ℕ} (hn : 0 < n) (hnA : n ∉ A) :
    supportCoeff (insert n A) n = supportCoeff A n + 1 := by
  have hdiv : n ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨dvd_rfl, Nat.ne_of_gt hn⟩
  exact supportCoeff_insert_divisor A hdiv hnA

/-- **Exact row-`2s` feedback theorem.**  Assume the two boundary parents
have carries `δ` and `δ+1`, while their first feedback coefficients are
`c+1` and `c`.  The zero/one children then have carries
`H-1,H-2,H+2,H+1`, respectively, where `H=2δ-c`.

The hypotheses isolate the set-level divisor-realisation question from the
now-closed feedback algebra. -/
theorem firstFeedbackChildCarries
    (left right : Set ℕ) (s c : ℕ) (δ : ℤ) (hs : 1 ≤ s)
    (hleftParent : integerHalfCarry left (2 * s - 2) = δ)
    (hrightParent : integerHalfCarry right (2 * s - 2) = δ + 1)
    (hleftCoeff : supportCoeff left (2 * s) = c + 1)
    (hrightCoeff : supportCoeff right (2 * s) = c)
    (hleftFresh : 2 * s ∉ left) (hrightFresh : 2 * s ∉ right) :
    integerHalfCarry left (2 * s - 1) = 2 * δ - c - 1 ∧
    integerHalfCarry (insert (2 * s) left) (2 * s - 1) =
      2 * δ - c - 2 ∧
    integerHalfCarry right (2 * s - 1) = 2 * δ - c + 2 ∧
    integerHalfCarry (insert (2 * s) right) (2 * s - 1) =
      2 * δ - c + 1 := by
  have hrow : 2 * s - 1 = (2 * s - 2) + 1 := by omega
  have hcoeffRow : 2 * s - 2 + 2 = 2 * s := by omega
  have hleftInsertParent := integerHalfCarry_insert_future_eq left
    (show 2 * s - 2 + 2 ≤ 2 * s by omega)
  have hrightInsertParent := integerHalfCarry_insert_future_eq right
    (show 2 * s - 2 + 2 ≤ 2 * s by omega)
  have hleftInsertCoeff := supportCoeff_insert_self left
    (show 0 < 2 * s by omega) hleftFresh
  have hrightInsertCoeff := supportCoeff_insert_self right
    (show 0 < 2 * s by omega) hrightFresh
  constructor
  · rw [hrow, integerHalfCarry_succ, hcoeffRow, hleftParent, hleftCoeff]
    push_cast
    omega
  constructor
  · rw [hrow, integerHalfCarry_succ, hcoeffRow, hleftInsertParent,
      hleftInsertCoeff, hleftParent, hleftCoeff]
    push_cast
    omega
  constructor
  · rw [hrow, integerHalfCarry_succ, hcoeffRow, hrightParent, hrightCoeff]
    omega
  · rw [hrow, integerHalfCarry_succ, hcoeffRow, hrightInsertParent,
      hrightInsertCoeff, hrightParent, hrightCoeff]
    push_cast
    omega

/-- The complete pre-feedback-to-first-feedback composition.  The gauge
hypotheses determine the right parent carry from the left one; only the
row-`2s` coefficient reversal and the absence of an already-selected current
bit remain as explicit Boolean-divisor inputs. -/
theorem firstFeedbackChildCarries_of_preFeedbackGauge
    (left right : Set ℕ) (s c : ℕ) (δ : ℤ) (hs : 2 ≤ s)
    (hbase : integerHalfCarry right (s - 2) =
      integerHalfCarry left (s - 2))
    (hseam : supportCoeff right s + 1 = supportCoeff left s)
    (htail : ∀ m : ℕ, s < m → m ≤ 2 * s - 1 →
      supportCoeff right m = supportCoeff left m + 1)
    (hdelta : integerHalfCarry left (2 * s - 2) = δ)
    (hleftCoeff : supportCoeff left (2 * s) = c + 1)
    (hrightCoeff : supportCoeff right (2 * s) = c)
    (hleftFresh : 2 * s ∉ left) (hrightFresh : 2 * s ∉ right) :
    integerHalfCarry left (2 * s - 1) = 2 * δ - c - 1 ∧
    integerHalfCarry (insert (2 * s) left) (2 * s - 1) =
      2 * δ - c - 2 ∧
    integerHalfCarry right (2 * s - 1) = 2 * δ - c + 2 ∧
    integerHalfCarry (insert (2 * s) right) (2 * s - 1) =
      2 * δ - c + 1 := by
  have hright := preFeedbackGaugeSymmetry left right s (2 * s - 1)
    hs (by omega) hbase hseam htail
  have hrightParent : integerHalfCarry right (2 * s - 2) = δ + 1 := by
    rw [show 2 * s - 1 - 1 = 2 * s - 2 by omega] at hright
    omega
  exact firstFeedbackChildCarries left right s c δ (by omega)
    hdelta hrightParent hleftCoeff hrightCoeff hleftFresh hrightFresh

/-! ## Exact endpoint and seam reduction -/

/-- Endpoint-bearing fixed-coefficient transition. -/
def FixedCoeffNumeratorReachable (c T k q : ℤ) : Prop :=
  ∃ h : ℤ,
    (k = 2 * h - c ∧ q = 2 * (T - h)) ∨
      (k = 2 * h - c - 1 ∧ q = 2 * (T - h) + 1)

/-- Under one common proper-divisor coefficient, the child numerator and
carry add to the common endpoint `2T-c`. -/
theorem fixedCoeffCylinder_endpoint
    {T h c k q b : ℤ}
    (hk : k = 2 * h - c - b)
    (hq : q = 2 * (T - h) + b) :
    q = (2 * T - c) - k := by
  omega

/-- Complete scalar recurrence: every fixed-coefficient target has exactly
the affine numerator with next endpoint `2T-c`. -/
theorem fixedCoeffNumeratorReachable_iff_endpoint
    (c T k q : ℤ) :
    FixedCoeffNumeratorReachable c T k q ↔ q = (2 * T - c) - k := by
  constructor
  · rintro ⟨h, (⟨hk, hq⟩ | ⟨hk, hq⟩)⟩ <;> omega
  · intro hq
    obtain ⟨h, hh, -⟩ := fixedCoeffChild_existsUnique c k
    rcases hh with hk | hk
    · exact ⟨h, Or.inl ⟨hk, by omega⟩⟩
    · exact ⟨h, Or.inr ⟨hk, by omega⟩⟩

/-- At a first half-divisor wrap, write the old endpoint as a fixed prefix,
the half-bit boundary, and boundary carry `δ`.  The next raw endpoint is the
extended prefix boundary plus the seam hole `2δ-c`. -/
theorem firstWrap_rawEndpoint_decomposition
    {P Q T δ c : ℤ}
    (hT : T = P * (2 * Q) + Q + δ) :
    2 * T - c = (2 * P + 1) * (2 * Q) + (2 * δ - c) := by
  rw [hT]
  ring

/-- For an actual Boolean stem `P`, the scalar `c` is literally its divisor
coefficient at row `2s`, and the seam hole is one more than the row-`2s`
carry of the left boundary word `P ∪ {s}` with the new row left off. -/
theorem actualFirstWrap_hole_eq_leftZeroCarry_add_one
    (P : Set ℕ) {s : ℕ} (hs : 1 ≤ s) (hsP : s ∉ P) (δ : ℤ)
    (hδ : integerHalfCarry (insert s P) (2 * s - 2) = δ) :
    2 * δ - (supportCoeff P (2 * s) : ℤ) =
      integerHalfCarry (insert s P) (2 * s - 1) + 1 := by
  have hsdvd : s ∈ (2 * s).divisors := by
    apply Nat.mem_divisors.mpr
    refine ⟨⟨2, by omega⟩, by omega⟩
  have hcoeff := supportCoeff_insert_divisor P hsdvd hsP
  rw [show 2 * s - 1 = (2 * s - 2) + 1 by omega,
    integerHalfCarry_succ, show 2 * s - 2 + 2 = 2 * s by omega,
    hδ, hcoeff]
  push_cast
  omega

/-- Consequently an in-strip seam hole is exactly a left zero-child carry in
the shifted strip `[0,B-1]`. -/
theorem hole_in_strip_iff_shiftedCarry_in_strip
    {B H K : ℤ} (hHK : H = K + 1) :
    (1 ≤ H ∧ H ≤ B) ↔ (0 ≤ K ∧ K < B) := by
  omega

/-- An integer hole misses an integer strip exactly when it is below the
strip or above it. -/
theorem hole_avoids_integerStrip_iff
    {B H : ℤ} :
    (∀ k : ℤ, 1 ≤ k → k ≤ B → k ≠ H) ↔ H < 1 ∨ B < H := by
  constructor
  · intro h
    by_cases hlow : H < 1
    · exact Or.inl hlow
    · right
      by_contra hhigh
      exact h H (by omega) (by omega) rfl
  · rintro (hlow | hhigh) k hk1 hkB <;> omega

/-- The landed one-hole theorem makes seam escape exactly equivalent to
full scalar reachability of the integer strip. -/
theorem evenSeam_fullIntegerStrip_iff_escape
    {B δ c : ℤ} :
    (∀ k : ℤ, 1 ≤ k → k ≤ B → EvenSeamReachable δ c k) ↔
      2 * δ - c < 1 ∨ B < 2 * δ - c := by
  rw [← hole_avoids_integerStrip_iff (B := B) (H := 2 * δ - c)]
  constructor
  · intro h k hk1 hkB
    exact (evenSeamReachable_iff δ c k).mp (h k hk1 hkB)
  · intro h k hk1 hkB
    exact (evenSeamReachable_iff δ c k).mpr (h k hk1 hkB)

/-- The exact first greedy post-take state is the `{2,3}` fragment with
residual `1/42`. -/
theorem greedyHalf_rankThree_prefix_fixture :
    greedyMersennePrefixRat (1 / 2 : ℚ) 3 = ({2, 3} : Finset ℕ) ∧
      (1 / 2 : ℚ) - finiteErdosSum ({2, 3} : Finset ℕ) 2 = 1 / 42 := by
  constructor
  · classical
    ext k
    simp only [greedyMersennePrefixRat, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨a, ⟨ha, htake⟩, rfl⟩
      interval_cases a
      · norm_num [greedyMersenneRemainderRat, mersenneWeightRat] at htake
      · simp
      · simp
    · rintro (rfl | rfl)
      · refine ⟨1, ⟨by norm_num, ?_⟩, by norm_num⟩
        norm_num [greedyMersenneRemainderRat, mersenneWeightRat]
      · refine ⟨2, ⟨by norm_num, ?_⟩, by norm_num⟩
        norm_num [greedyMersenneRemainderRat, mersenneWeightRat]
  · rw [two_three_dyadicPrefix_fixture.1]
    norm_num

/-- Exact non-equivalence witness.  The greedy state after taking rank `3`
is dyadically safe at the last predecessor before rank `6`, but its scalar
half-cylinder seam has the in-strip hole `H=3`. -/
theorem rankThree_rawSafe_but_seamNotEscaped :
    BlockDyadicSafeAt 1 21 5 ∧
      halfStripBound 6 = 8 ∧
      ¬ ((2 : ℤ) * 2 - 1 < 1 ∨ (8 : ℤ) < (2 : ℤ) * 2 - 1) ∧
      ¬ EvenSeamReachable 2 1 3 := by
  refine ⟨by norm_num [BlockDyadicSafeAt], ?_, by norm_num,
    depth14_evenSeam_three_not_reachable⟩
  have hsqrt : Nat.sqrt 6 = 2 := by
    symm
    exact Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩
  simp [halfStripBound, hsqrt]

#print axioms halfStripAdmissible_residual_eq
#print axioms one_sub_pow_mul_halfResidual_eq_tail_sub_centered
#print axioms finiteCoeffWindow_le_binaryCoeffTail
#print axioms coeff_term_le_binaryCoeffTail
#print axioms scaledHalfResidual_le_one_of_finiteCoeffWindow
#print axioms rawHalfSlack_nonneg_of_finiteCoeffWindow
#print axioms futureSkipCapacity_factorization
#print axioms finiteCoeffWindow_covers_iff_terminal_le_skipCapacity
#print axioms finiteCoeffWindow_covers_of_one_future_skip
#print axioms binaryCoeffTail_eq_finiteCoeffWindow_add_shiftedTail
#print axioms halfGreedyPrefix_reducedTailGapCoordinates
#print axioms futureSkipCapacityMargin_eq_reducedTailTax
#print axioms futureSkipCoverage_iff_reducedTailTax
#print axioms futureSkipCoverage_persistent
#print axioms scaledPrefixHalfResidual_le_one_of_terminal_le_skipCapacity
#print axioms halfStripAdmissible_abs_residual_le
#print axioms preFeedbackGaugeSymmetry
#print axioms supportCoeff_insert_divisor
#print axioms supportCoeff_insert_self
#print axioms firstFeedbackChildCarries
#print axioms firstFeedbackChildCarries_of_preFeedbackGauge
#print axioms fixedCoeffCylinder_endpoint
#print axioms fixedCoeffNumeratorReachable_iff_endpoint
#print axioms firstWrap_rawEndpoint_decomposition
#print axioms actualFirstWrap_hole_eq_leftZeroCarry_add_one
#print axioms evenSeam_fullIntegerStrip_iff_escape
#print axioms greedyHalf_rankThree_prefix_fixture
#print axioms rankThree_rawSafe_but_seamNotEscaped

end Erdos249257.HalfCylinderFiniteShadow

/-! ## Actual half-greedy skip-capacity specialization -/

namespace Erdos249257

open Set Filter
open HalfCarryReachability
open HalfCylinderFiniteShadow

/-- The exact-rational finite greedy prefix is the cutoff of the real greedy
support.  This bridge is independent of any skip assumption. -/
theorem primitivePrefix_greedyMersenneSupport_eq_prefixRat
    (x : ℚ) (n : ℕ) :
    primitivePrefix (greedyMersenneSupport (x : ℝ)) n =
      (↑(greedyMersennePrefixRat x n) : Set ℕ) := by
  classical
  ext a
  constructor
  · rintro ⟨ha, han⟩
    have ha0 : a ≠ 0 := by
      intro hzero
      subst a
      exact (zero_not_mem_greedyMersenneSupport (x : ℝ)) ha
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha0
    change j + 1 ∈ greedyMersennePrefixRat x n
    unfold greedyMersennePrefixRat
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · change j + 1 ≤ n at han
      exact Finset.mem_range.mpr han
    · exact (rational_greedy_take_iff_real x j).mpr
        ((succ_mem_greedyMersenneSupport_iff (x : ℝ) j).mp ha)
  · intro ha
    change a ∈ greedyMersennePrefixRat x n at ha
    unfold greedyMersennePrefixRat at ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    rcases Finset.mem_filter.mp hj with ⟨hjrange, htake⟩
    refine ⟨?_, ?_⟩
    · exact (succ_mem_greedyMersenneSupport_iff (x : ℝ) j).mpr
        ((rational_greedy_take_iff_real x j).mp htake)
    · exact Finset.mem_range.mp hjrange

/-- If the next real greedy decision skips rank `k + 1`, extending the
cutoff from `k` to `k + 1` does not change the primitive prefix. -/
theorem primitivePrefix_greedyMersenneSupport_succ_eq_of_skip
    (x : ℝ) (k : ℕ)
    (hskip : ¬ mersenneWeight (k + 1) ≤ greedyMersenneRemainder x k) :
    primitivePrefix (greedyMersenneSupport x) (k + 1) =
      primitivePrefix (greedyMersenneSupport x) k := by
  have hnot : k + 1 ∉ greedyMersenneSupport x := by
    simpa only [succ_mem_greedyMersenneSupport_iff] using hskip
  ext a
  simp only [primitivePrefix, Set.mem_inter_iff, Set.mem_Iic]
  constructor
  · rintro ⟨ha, hak1⟩
    refine ⟨ha, ?_⟩
    by_contra hnotle
    have hae : a = k + 1 := by omega
    exact hnot (hae ▸ ha)
  · rintro ⟨ha, hak⟩
    exact ⟨ha, by omega⟩

/-- At an actual skipped half-greedy rank, the full real support through
`k + 1` is exactly the landed finite rational support through `k`. -/
theorem primitivePrefix_greedyHalf_eq_halfGreedyPrefixSupport_of_skip
    (k : ℕ)
    (hskip : ¬ mersenneWeight (k + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) k) :
    primitivePrefix (greedyMersenneSupport (1 / 2 : ℝ)) (k + 1) =
      (↑(halfGreedyPrefixSupport k) : Set ℕ) := by
  rw [primitivePrefix_greedyMersenneSupport_succ_eq_of_skip
    (1 / 2 : ℝ) k hskip]
  simpa [halfGreedyPrefixSupport] using
    primitivePrefix_greedyMersenneSupport_eq_prefixRat (1 / 2 : ℚ) k

/-- The generic reduced skip-capacity margin, instantiated at an actual
skipped half-greedy rank. -/
theorem greedyHalf_futureSkipCapacityMargin_eq_reducedTailTax
    (k J : ℕ)
    (hskip : ¬ mersenneWeight (k + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) k)
    (hJ : J ≤ k + 1) :
    (futureSkipCapacity (greedyMersenneSupport (1 / 2 : ℝ))
          (k + 1) J : ℝ) -
        (mobiusCenteredHalfCarry
          (greedyMersenneSupport (1 / 2 : ℝ)) (k + J) : ℝ) =
      -(2 : ℝ) ^ J *
          ((halfGreedyNextDyadicExcessNumerator k : ℝ) /
            (halfGreedyPrefixDenominator k : ℝ)) -
        binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ))
          (k + 1 + J) := by
  have h := futureSkipCapacityMargin_eq_reducedTailTax
    (greedyMersenneSupport (1 / 2 : ℝ))
    (↑(halfGreedyPrefixSupport k) : Set ℕ)
    (k + 1) J
    (halfGreedyNextDyadicExcessNumerator k)
    (halfGreedyPrefixDenominator k)
    (by omega) hJ
    (primitivePrefix_greedyHalf_eq_halfGreedyPrefixSupport_of_skip k hskip)
    (halfGreedyPrefix_reducedTailGapCoordinates k)
  simpa using h

/-- Actual future-skip coverage is exactly the specialized reduced tail-tax
inequality at every governed horizon `J ≤ k + 1`. -/
theorem greedyHalf_futureSkipCoverage_iff_reducedTailTax
    (k J : ℕ)
    (hskip : ¬ mersenneWeight (k + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) k)
    (hJ : J ≤ k + 1) :
    mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) (k + J) ≤
          (futureSkipCapacity (greedyMersenneSupport (1 / 2 : ℝ))
            (k + 1) J : ℤ) ↔
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ))
          (k + 1 + J) ≤
        -(2 : ℝ) ^ J *
          ((halfGreedyNextDyadicExcessNumerator k : ℝ) /
            (halfGreedyPrefixDenominator k : ℝ)) := by
  have h := futureSkipCoverage_iff_reducedTailTax
    (greedyMersenneSupport (1 / 2 : ℝ))
    (↑(halfGreedyPrefixSupport k) : Set ℕ)
    (k + 1) J
    (halfGreedyNextDyadicExcessNumerator k)
    (halfGreedyPrefixDenominator k)
    (by omega) hJ
    (primitivePrefix_greedyHalf_eq_halfGreedyPrefixSupport_of_skip k hskip)
    (halfGreedyPrefix_reducedTailGapCoordinates k)
  simpa using h

/-! ## Frozen-prefix first-passage form of the actual producer -/

/-- Signed frozen-prefix margin. Its nonnegativity says that the first `J`
future divisor-incidence rows cover the centered carry at depth `k`. -/
noncomputable def greedyHalfFrozenMargin (k J : ℕ) : ℤ :=
  (finiteCoeffWindowNumerator
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℤ) -
    (2 : ℤ) ^ J *
      mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k

@[simp] theorem greedyHalfFrozenMargin_zero (k : ℕ) :
    greedyHalfFrozenMargin k 0 =
      -mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k := by
  simp [greedyHalfFrozenMargin, finiteCoeffWindowNumerator]

/-- Exact integer recurrence. The forcing term is a divisor count in the
frozen finite prefix, with no real tail or future greedy decision. -/
theorem greedyHalfFrozenMargin_succ (k J : ℕ) :
    greedyHalfFrozenMargin k (J + 1) =
      2 * greedyHalfFrozenMargin k J +
        (supportCoeff
          (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + J + 2) : ℤ) := by
  simp only [greedyHalfFrozenMargin, finiteCoeffWindowNumerator,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  ring

/-- Normalized margin is exactly the finite coefficient window minus the
initial centered carry. -/
theorem greedyHalfFrozenMargin_cast_eq_pow_mul_window_sub_carry
    (k J : ℕ) :
    (greedyHalfFrozenMargin k J : ℝ) =
      (2 : ℝ) ^ J *
        (finiteCoeffWindow
            (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J -
          (mobiusCenteredHalfCarry
            (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ)) := by
  have hwindow := finiteCoeffWindow_eq_numerator_div_pow
    (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J
  have hpow : (2 : ℝ) ^ J ≠ 0 := by positivity
  have hnum :
      finiteCoeffWindow
          (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J *
          (2 : ℝ) ^ J =
        (finiteCoeffWindowNumerator
          (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℝ) :=
    (eq_div_iff hpow).mp hwindow
  unfold greedyHalfFrozenMargin
  push_cast
  rw [← hnum]
  ring

/-- The signed recurrence crosses zero exactly when the finite frozen window
covers the initial centered carry. -/
theorem greedyHalfFrozenMargin_nonneg_iff_window_covers (k J : ℕ) :
    0 ≤ greedyHalfFrozenMargin k J ↔
      (mobiusCenteredHalfCarry
          (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) ≤
        finiteCoeffWindow
          (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J := by
  have hid := greedyHalfFrozenMargin_cast_eq_pow_mul_window_sub_carry k J
  have hpow : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  constructor
  · intro h
    have hR : (0 : ℝ) ≤ (greedyHalfFrozenMargin k J : ℝ) := by
      exact_mod_cast h
    rw [hid] at hR
    nlinarith
  · intro h
    have hR : (0 : ℝ) ≤ (greedyHalfFrozenMargin k J : ℝ) := by
      rw [hid]
      exact mul_nonneg hpow.le (sub_nonneg.mpr h)
    exact_mod_cast hR

/-- Once the signed recurrence crosses zero, every later recurrence state
stays nonnegative. -/
theorem greedyHalfFrozenMargin_nonneg_succ
    (k J : ℕ) (h : 0 ≤ greedyHalfFrozenMargin k J) :
    0 ≤ greedyHalfFrozenMargin k (J + 1) := by
  rw [greedyHalfFrozenMargin_succ]
  positivity

/-- On an actual skipped rank and inside the first shell, the frozen margin
is literally actual future-skip capacity minus the actual terminal carry. -/
theorem greedyHalfFrozenMargin_eq_actual_skip_margin
    (k J : ℕ)
    (hskip : ¬ mersenneWeight (k + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) k)
    (hJ : J ≤ k + 1) :
    greedyHalfFrozenMargin k J =
      (futureSkipCapacity (greedyMersenneSupport (1 / 2 : ℝ))
          (k + 1) J : ℤ) -
        mobiusCenteredHalfCarry
          (greedyMersenneSupport (1 / 2 : ℝ)) (k + J) := by
  let G := greedyMersenneSupport (1 / 2 : ℝ)
  let P : Set ℕ := ↑(halfGreedyPrefixSupport k)
  have hprefix : primitivePrefix G (k + 1) = P := by
    simpa [G, P] using
      primitivePrefix_greedyHalf_eq_halfGreedyPrefixSupport_of_skip k hskip
  have hcarry : mobiusCenteredHalfCarry P k =
      mobiusCenteredHalfCarry G k := by
    rw [← hprefix]
    unfold primitivePrefix mobiusCenteredHalfCarry
    rw [integerHalfCarry_inter_Iic_eq_of_succ_le G (k + 1) k (by omega)]
  have hfac := futureSkipCapacity_factorization
    G (k + 1) J (by omega) hJ
  rw [hprefix] at hfac
  have hk : k + 1 - 1 = k := by omega
  rw [hk, ← hcarry] at hfac
  simpa [greedyHalfFrozenMargin, G, P] using hfac

/-- The landed reduced tail-tax inequality is exactly nonnegativity of the
finite integer recurrence. -/
theorem greedyHalfFrozenMargin_nonneg_iff_reducedTailTax
    (k J : ℕ)
    (hskip : ¬ mersenneWeight (k + 1) ≤
      greedyMersenneRemainder (1 / 2 : ℝ) k)
    (hJ : J ≤ k + 1) :
    0 ≤ greedyHalfFrozenMargin k J ↔
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ))
          (k + 1 + J) ≤
        -(2 : ℝ) ^ J *
          ((halfGreedyNextDyadicExcessNumerator k : ℝ) /
            (halfGreedyPrefixDenominator k : ℝ)) := by
  rw [greedyHalfFrozenMargin_eq_actual_skip_margin k J hskip hJ,
    sub_nonneg]
  exact greedyHalf_futureSkipCoverage_iff_reducedTailTax k J hskip hJ

/-- Finite coefficient windows converge to the complete normalized
coefficient tail. -/
theorem tendsto_finiteCoeffWindow_atTop
    (P : Set ℕ) (n : ℕ) :
    Tendsto (fun J : ℕ ↦ finiteCoeffWindow P n J) atTop
      (nhds (binaryCoeffTail (supportCoeff P) n)) := by
  have hbase := binaryCoeffTail_div_pow_tendsto_zero
    (supportCoeff P) (supportCoeff_le_self P)
  have hshift := hbase.comp (tendsto_add_atTop_nat n)
  have hscaled := hshift.const_mul ((2 : ℝ) ^ n)
  have hrem :
      Tendsto (fun J : ℕ ↦
        binaryCoeffTail (supportCoeff P) (n + J) / (2 : ℝ) ^ J)
        atTop (nhds 0) := by
    convert hscaled using 1
    · funext J
      simp only [Function.comp_apply]
      rw [show J + n = n + J by omega, pow_add]
      field_simp
    · simp
  have hlimit :=
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ binaryCoeffTail (supportCoeff P) n) atTop
      (nhds (binaryCoeffTail (supportCoeff P) n))).sub hrem
  convert hlimit using 1
  · funext J
    have hsplit := binaryCoeffTail_eq_finiteCoeffWindow_add_shiftedTail
      P n J
    linarith
  · simp

/-- Negative dyadic excess forces an eventual zero crossing of the frozen
integer recurrence. This horizon is not yet bounded by the first shell. -/
theorem exists_greedyHalfFrozenMargin_nonneg_of_excess_neg
    (k : ℕ) (hE : halfGreedyNextDyadicExcessNumerator k < 0) :
    ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J := by
  let P : Set ℕ := ↑(halfGreedyPrefixSupport k)
  let C : ℤ := mobiusCenteredHalfCarry P k
  have hred := halfGreedyPrefix_reducedTailGapCoordinates k
  have hD : (0 : ℝ) < (halfGreedyPrefixDenominator k : ℝ) := by
    exact_mod_cast hred.1
  have hER : (halfGreedyNextDyadicExcessNumerator k : ℝ) < 0 := by
    exact_mod_cast hE
  have hbelow : (C : ℝ) < binaryCoeffTail (supportCoeff P) (k + 1) := by
    have hratio :
        (halfGreedyNextDyadicExcessNumerator k : ℝ) /
          (halfGreedyPrefixDenominator k : ℝ) < 0 :=
      div_neg_of_neg_of_pos hER hD
    have hred' := hred
    simp only [ReducedTailGapCoordinates] at hred'
    have hgap := hred'.2
    have hk : k + 1 - 1 = k := by omega
    rw [hk] at hgap
    change (C : ℝ) < binaryCoeffTail (supportCoeff P) (k + 1)
    dsimp [C, P]
    linarith
  have hlim := tendsto_finiteCoeffWindow_atTop P (k + 1)
  obtain ⟨J, hJ⟩ := ((tendsto_order.1 hlim).1 (C : ℝ) hbelow).exists
  refine ⟨J, ?_⟩
  exact (greedyHalfFrozenMargin_nonneg_iff_window_covers k J).2
    (by simpa [P, C] using hJ.le)

/-- At positive depth, eventual first passage is equivalent to strict
dyadic safety. Oddness excludes the zero-excess boundary. -/
theorem exists_greedyHalfFrozenMargin_nonneg_iff_excess_neg
    (k : ℕ) (hk : 0 < k) :
    (∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J) ↔
      halfGreedyNextDyadicExcessNumerator k < 0 := by
  constructor
  · rintro ⟨J, hJ⟩
    let P : Set ℕ := ↑(halfGreedyPrefixSupport k)
    have hwindow :=
      (greedyHalfFrozenMargin_nonneg_iff_window_covers k J).1 hJ
    have htail := hwindow.trans
      (finiteCoeffWindow_le_binaryCoeffTail P (k + 1) J)
    have hred := halfGreedyPrefix_reducedTailGapCoordinates k
    have hratio :
        (halfGreedyNextDyadicExcessNumerator k : ℝ) /
            (halfGreedyPrefixDenominator k : ℝ) ≤ 0 := by
      have hred' := hred
      simp only [ReducedTailGapCoordinates] at hred'
      have hgap := hred'.2
      have hk' : k + 1 - 1 = k := by omega
      rw [hk'] at hgap
      linarith
    have hD : (0 : ℝ) < (halfGreedyPrefixDenominator k : ℝ) := by
      exact_mod_cast hred.1
    have hER : (halfGreedyNextDyadicExcessNumerator k : ℝ) ≤ 0 := by
      have := (div_le_iff₀ hD).mp hratio
      simpa using this
    have hE : halfGreedyNextDyadicExcessNumerator k ≤ 0 := by
      exact_mod_cast hER
    have hne : halfGreedyNextDyadicExcessNumerator k ≠ 0 := by
      intro heq
      have hodd := halfGreedyNextDyadicExcessNumerator_odd hk
      simp [heq] at hodd
    omega
  · intro hE
    exact exists_greedyHalfFrozenMargin_nonneg_of_excess_neg k hE

/-- Exact remaining governed producer after all reductions: the first
nonnegative state of the frozen recurrence must occur by `k + 1`. -/
def HalfGreedyGovernedFrozenMarginProducer : Prop :=
  ∀ k : ℕ,
    ¬ mersenneWeight (k + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) k →
      ∃ J : ℕ, J ≤ k + 1 ∧ 0 ≤ greedyHalfFrozenMargin k J

/-- The governed first-passage producer closes exact half-membership. -/
theorem half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer
    (hproducer : HalfGreedyGovernedFrozenMarginProducer) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_of_skipped_dyadicCap
  intro k hskip
  rcases hproducer k hskip with ⟨J, hJ, hmargin⟩
  apply (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos k).2
  let P : Set ℕ := ↑(halfGreedyPrefixSupport k)
  have hwindow :=
    (greedyHalfFrozenMargin_nonneg_iff_window_covers k J).1 hmargin
  have htail := hwindow.trans
    (finiteCoeffWindow_le_binaryCoeffTail P (k + 1) J)
  have hred := halfGreedyPrefix_reducedTailGapCoordinates k
  have hratio :
      (halfGreedyNextDyadicExcessNumerator k : ℝ) /
          (halfGreedyPrefixDenominator k : ℝ) ≤ 0 := by
    have hred' := hred
    simp only [ReducedTailGapCoordinates] at hred'
    have hgap := hred'.2
    have hk' : k + 1 - 1 = k := by omega
    rw [hk'] at hgap
    linarith
  have hD : (0 : ℝ) < (halfGreedyPrefixDenominator k : ℝ) := by
    exact_mod_cast hred.1
  have hER : (halfGreedyNextDyadicExcessNumerator k : ℝ) ≤ 0 := by
    have := (div_le_iff₀ hD).mp hratio
    simpa using this
  exact_mod_cast hER

end Erdos249257

#print axioms Erdos249257.primitivePrefix_greedyMersenneSupport_eq_prefixRat
#print axioms Erdos249257.primitivePrefix_greedyMersenneSupport_succ_eq_of_skip
#print axioms Erdos249257.primitivePrefix_greedyHalf_eq_halfGreedyPrefixSupport_of_skip
#print axioms Erdos249257.greedyHalf_futureSkipCapacityMargin_eq_reducedTailTax
#print axioms Erdos249257.greedyHalf_futureSkipCoverage_iff_reducedTailTax
#print axioms Erdos249257.greedyHalfFrozenMargin_succ
#print axioms Erdos249257.greedyHalfFrozenMargin_nonneg_iff_reducedTailTax
#print axioms Erdos249257.exists_greedyHalfFrozenMargin_nonneg_iff_excess_neg
#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer
