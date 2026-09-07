import Erdos257PeriodNoncollapse.BooleanMobiusGlobalRepair
import Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction

/-!
# Cofinal exact Boolean--Möbius rows

This module isolates a weaker consumer than a coherent global repair
trajectory.  It needs only exact finite quotient rows at arbitrarily large
endpoints.  The supports at different endpoints need not agree at any
coordinate.

For an exact row `D` at endpoint `n`, the quotient identity

`localPrefixQuotient D n = 2^(n-1) - 1`

and the fractional-part estimate from `BooleanMobiusGlobalRepair` give

`|localMersennePrefixValue D - 1/2| <= (n+1)/2^n`.

Thus any cofinal supply of exact rows produces achievement-set points tending
to `1/2`.  Closedness then gives exact membership.  This separates the
finite Boolean producer from every coherence or frozen-diagonal requirement.
-/

namespace Erdos257PeriodNoncollapse

open Filter Set
open HalfCylinderIntegerGreedy
open BooleanMobiusGreedyReduction

/-! ## Producer socket -/

/-- An exact finite Boolean quotient row at endpoint `n`. -/
def ExactLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1

/-- Exact Boolean quotient rows occur at arbitrarily large endpoints.  No
compatibility is imposed between the witnesses at different endpoints. -/
def CofinalExactLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactLocalMersenneHalfRow n

/-! ## Lower-half quotient-greedy producer -/

/-- The exact deterministic frontier exposed by splitting every quotient row
at its half cutoff.  Only ranks `2,…,⌊M/2⌋` occur in the inequality; the
remaining ranks are a complete descending binary word. -/
def CofinalHalfCutoffGreedyWindows : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, max N 2 ≤ M ∧
    integerGreedyRemainder (localMersenneWeights M (M / 2))
        (2 ^ (M - 1) - 1) <
      2 ^ (M - M / 2)

/-- Cofinal safety of the strict core immediately before the terminal
`2^R+1` coin on even endpoints.  Compared with the full half-cutoff
inequality, this asks only for a coarse `2^(R+1)+1` bound and exclusion of
the single lattice state `2^R`. -/
def CofinalEvenHalfCutoffCoreSafety : Prop :=
  ∀ N : ℕ, ∃ R : ℕ, max N 2 ≤ R ∧
    evenHalfCutoffCoreRemainder R < 2 * 2 ^ R + 1 ∧
      evenHalfCutoffCoreRemainder R ≠ 2 ^ R

/-- The strictly weaker approximate-row frontier.  The exceptional state
`2^R` is harmless for convergence: only the coarse subexponential bound is
needed when exact finite completion is replaced by closed-set approximation. -/
def CofinalEvenHalfCutoffCoreBound : Prop :=
  ∀ N : ℕ, ∃ R : ℕ, max N 3 ≤ R ∧
    evenHalfCutoffCoreRemainder R < 2 * 2 ^ R + 1

/-- The scale-invariant approximate-row frontier.  No fixed exponential
cap is mathematically distinguished: all that closed-set approximation
needs is a cofinal sequence on which the core defect is `o(4^R)`. -/
noncomputable def evenHalfCutoffCoreNormalizedRemainder (R : ℕ) : ℝ :=
  (evenHalfCutoffCoreRemainder R : ℝ) / (4 : ℝ) ^ R

def EvenHalfCutoffCoreRemainderSubquadraticAlong
    (rows : ℕ → ℕ) : Prop :=
  Tendsto rows atTop atTop ∧
    Tendsto
      (fun j ↦ evenHalfCutoffCoreNormalizedRemainder (rows j))
      atTop (nhds 0)

/-- The single forbidden-state criterion on cofinally many even rows is
exactly enough to supply the canonical half-cutoff windows. -/
theorem cofinalHalfCutoffGreedyWindows_of_evenCoreSafety
    (hcore : CofinalEvenHalfCutoffCoreSafety) :
    CofinalHalfCutoffGreedyWindows := by
  intro N
  obtain ⟨R, hNR, hbound, hne⟩ := hcore N
  have hR : 2 ≤ R := (le_max_right N 2).trans hNR
  refine ⟨2 * R, ?_, ?_⟩
  · have hN : N ≤ R := (le_max_left N 2).trans hNR
    omega
  · have hsafety :
        integerGreedyRemainder
            (localMersenneWeights (2 * R) R)
            (2 ^ (2 * R - 1) - 1) < 2 ^ R :=
      (integerGreedyRemainder_even_halfCutoff_lt_iff_core_ne hR).2
        ⟨hbound, hne⟩
    simpa [show (2 * R) / 2 = R by omega,
      show 2 * R - R = R by omega] using hsafety

/-- One successful lower-half window produces an exact local row at the
same endpoint. -/
theorem exactLocalMersenneHalfRow_of_halfCutoffGreedyWindow
    {M : ℕ} (hM : 2 ≤ M)
    (hwindow :
      integerGreedyRemainder (localMersenneWeights M (M / 2))
          (2 ^ (M - 1) - 1) <
        2 ^ (M - M / 2)) :
    ExactLocalMersenneHalfRow M :=
  exists_exactFullMersenneHalfRowSupport_of_halfCutoffWindow hM hwindow

/-- Cofinal lower-half window bounds are already the complete finite
producer required by the closedness argument. -/
theorem cofinalExactLocalMersenneHalfRows_of_halfCutoffGreedyWindows
    (hwindow : CofinalHalfCutoffGreedyWindows) :
    CofinalExactLocalMersenneHalfRows := by
  intro N
  obtain ⟨M, hNM, hM⟩ := hwindow N
  exact ⟨M, (le_max_left N 2).trans hNM,
    exactLocalMersenneHalfRow_of_halfCutoffGreedyWindow
      ((le_max_right N 2).trans hNM) hM⟩

/-! ## Finite row values -/

/-- The real Mersenne value carried by a finite exact-row support. -/
noncomputable def exactLocalMersenneRowValue (D : Finset ℕ) : ℝ :=
  ((localMersennePrefixValue D : ℚ) : ℝ)

theorem exactLocalMersenneRowValue_mem_mersenneAchievementSet
    {D : Finset ℕ} (hD : ∀ d ∈ D, 2 ≤ d) :
    exactLocalMersenneRowValue D ∈ mersenneAchievementSet := by
  refine ⟨(↑D : Set ℕ), ?_, ?_⟩
  · intro hzero
    have := hD 0 hzero
    omega
  · rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [exactLocalMersenneRowValue,
      localMersennePrefixValue_eq_finiteErdosSum]

theorem abs_exactLocalMersenneRowValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    |exactLocalMersenneRowValue D - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  exact abs_localMersennePrefixValue_sub_half_le hn hD hquot

/-! ## Approximate quotient rows -/

/-- A quotient row with natural defect `r` approximates one half with error
at most `(n+1+r)/2^n`.  Exact rows are the special case `r=0`; this form is
what lets a subexponential core remainder bypass exact binary completion. -/
theorem abs_exactLocalMersenneRowValue_sub_half_le_of_defect
    {D : Finset ℕ} {n r : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot :
      localPrefixQuotient D n + r = 2 ^ (n - 1) - 1) :
    |exactLocalMersenneRowValue D - (1 : ℝ) / 2| ≤
      ((n + 1 + r : ℕ) : ℝ) / (2 : ℝ) ^ n := by
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
  have hpow : (2 : ℚ) ^ n = 2 * (2 : ℚ) ^ (n - 1) := by
    calc
      (2 : ℚ) ^ n = 2 ^ ((n - 1) + 1) := by congr 1 <;> omega
      _ = 2 * (2 : ℚ) ^ (n - 1) := by rw [pow_succ]; ring
  have hscale' :
      localMersennePrefixValue D * (2 : ℚ) ^ n =
        (localPrefixQuotient D n : ℚ) + localFractionMass D n := by
    simpa [mul_comm] using hscale
  have hone : 1 ≤ 2 ^ (n - 1) :=
    Nat.one_le_pow _ _ (by norm_num)
  have hcastTarget : ((2 ^ (n - 1) - 1 : ℕ) : ℚ) =
      (2 : ℚ) ^ (n - 1) - 1 := by
    rw [Nat.cast_sub hone]
    norm_num
  have hquotCast := congrArg (fun x : ℕ ↦ (x : ℚ)) hquot
  simp only [Nat.cast_add] at hquotCast
  rw [hcastTarget] at hquotCast
  have hidQ :
      localMersennePrefixValue D - (1 : ℚ) / 2 =
        (localFractionMass D n - 1 - r) / (2 : ℚ) ^ n := by
    rw [eq_div_iff (by positivity : (2 : ℚ) ^ n ≠ 0)]
    rw [sub_mul, hscale', hpow]
    push_cast
    linarith
  have habsQ :
      |localMersennePrefixValue D - (1 : ℚ) / 2| ≤
        ((n + 1 + r : ℕ) : ℚ) / (2 : ℚ) ^ n := by
    rw [hidQ, abs_div, abs_pow,
      abs_of_nonneg (by norm_num : (0 : ℚ) ≤ 2)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (abs_le).2
    have hrnonneg : (0 : ℚ) ≤ r := by positivity
    constructor <;> push_cast <;> linarith
  have habsR :
      (((|localMersennePrefixValue D - (1 : ℚ) / 2| : ℚ) : ℝ)) ≤
        ((((n + 1 + r : ℕ) : ℚ) / (2 : ℚ) ^ n : ℚ) : ℝ) := by
    exact_mod_cast habsQ
  simpa [exactLocalMersenneRowValue] using habsR

/-! ## Coarse even-core consumer -/

/-- **Approximate even-core endgame.**  Exact binary completion is not
necessary.  If the strict-core remainder is below `2^(R+1)+1` at cofinally
many even endpoints, the decoded core rows already approach one half at
rate at most `4/2^R`; closedness supplies exact membership.

In particular, the isolated exceptional state `A=2^R` from the exact-row
route disappears completely from the remaining proposition. -/
theorem half_mem_mersenneAchievementSet_of_cofinalEvenCoreBound
    (hcore : CofinalEvenHalfCutoffCoreBound) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  choose R hR hbound using hcore
  let D : ℕ → Finset ℕ := fun N ↦ evenHalfCutoffCoreSupport (R N)
  let y : ℕ → ℝ := fun N ↦ exactLocalMersenneRowValue (D N)
  have hRthree : ∀ N, 3 ≤ R N := by
    intro N
    exact (le_max_right N 3).trans (hR N)
  have hRtop : Tendsto R atTop atTop := by
    exact tendsto_atTop_mono
      (fun N ↦ (le_max_left N 3).trans (hR N)) tendsto_id
  have hD : ∀ N d, d ∈ D N → 2 ≤ d ∧ d ≤ 2 * R N := by
    intro N d hd
    have hb := evenHalfCutoffCoreSupport_mem_bounds hd
    exact ⟨hb.1, by omega⟩
  have hrowDefect : ∀ N,
      localPrefixQuotient (D N) (2 * R N) +
          evenHalfCutoffCoreRemainder (R N) =
        2 ^ (2 * R N - 1) - 1 := by
    intro N
    simpa [D] using
      localPrefixQuotient_evenHalfCutoffCoreSupport_add_remainder
        (show 2 ≤ R N by
          have := hRthree N
          omega)
  have herror : ∀ N,
      |y N - (1 : ℝ) / 2| ≤
        (4 : ℝ) / (2 : ℝ) ^ (R N) := by
    intro N
    have hraw :=
      abs_exactLocalMersenneRowValue_sub_half_le_of_defect
        (n := 2 * R N)
        (r := evenHalfCutoffCoreRemainder (R N))
        (show 2 ≤ 2 * R N by
          have := hRthree N
          omega)
        (hD N) (hrowDefect N)
    have hlinear : 2 * R N + 1 < 2 ^ (R N + 1) := by
      have h := two_mul_add_four_lt_two_pow_succ (hRthree N)
      omega
    have hrem :
        evenHalfCutoffCoreRemainder (R N) ≤ 2 * 2 ^ (R N) := by
      have := hbound N
      omega
    have hnum :
        2 * R N + 1 + evenHalfCutoffCoreRemainder (R N) ≤
          2 ^ (R N + 2) := by
      have hpow :
          2 ^ (R N + 2) = 2 ^ (R N + 1) + 2 ^ (R N + 1) := by
        rw [show R N + 2 = (R N + 1) + 1 by omega, pow_succ]
        ring
      have hrem' : 2 * 2 ^ (R N) = 2 ^ (R N + 1) := by
        rw [pow_succ']
      rw [hpow, ← hrem']
      omega
    calc
      |y N - (1 : ℝ) / 2| ≤
          (((2 * R N + 1 +
            evenHalfCutoffCoreRemainder (R N) : ℕ) : ℝ) /
              (2 : ℝ) ^ (2 * R N)) := hraw
      _ ≤ (((2 ^ (R N + 2) : ℕ) : ℝ) /
              (2 : ℝ) ^ (2 * R N)) := by
            exact div_le_div_of_nonneg_right
              (by exact_mod_cast hnum) (by positivity)
      _ = (4 : ℝ) / (2 : ℝ) ^ (R N) := by
            rw [show 2 * R N = R N + R N by omega]
            norm_num [pow_add]
            field_simp
  have hgeomBase :
      Tendsto (fun r : ℕ ↦ (4 : ℝ) / (2 : ℝ) ^ r)
        atTop (nhds 0) := by
    have hOne : Tendsto (fun r : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ r)
        atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : (1 : ℝ) < 2))
    convert hOne.const_mul 4 using 1
    · funext r
      ring
    · norm_num
  have hgeom :
      Tendsto (fun N : ℕ ↦ (4 : ℝ) / (2 : ℝ) ^ (R N))
        atTop (nhds 0) :=
    hgeomBase.comp hRtop
  have hy : Tendsto y atTop (nhds ((1 : ℝ) / 2)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have habs : Tendsto (fun N : ℕ ↦ |y N - (1 : ℝ) / 2|)
        atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun N ↦ abs_nonneg _
      · exact Filter.Eventually.of_forall herror
      · exact hgeom
    simpa [Real.norm_eq_abs] using habs
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall fun N ↦
      exactLocalMersenneRowValue_mem_mersenneAchievementSet
        (fun d hd ↦ (hD N d hd).1))

/-- **Cap-free approximate-row endgame.**  A cofinal `o(4^R)` strict-core
defect already supplies finite achievement-set points converging to one
half.  The earlier `2^(R+1)+1` condition is merely one convenient producer
of this intrinsic hypothesis, not a structural threshold. -/
theorem half_mem_mersenneAchievementSet_of_evenCoreSubquadraticAlong
    (rows : ℕ → ℕ)
    (hrows : EvenHalfCutoffCoreRemainderSubquadraticAlong rows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  rcases hrows with ⟨hcofinal, hnormalized⟩
  let D : ℕ → Finset ℕ :=
    fun N ↦ evenHalfCutoffCoreSupport (rows N)
  let y : ℕ → ℝ := fun N ↦ exactLocalMersenneRowValue (D N)
  have hD : ∀ N d, d ∈ D N → 2 ≤ d ∧ d ≤ 2 * rows N := by
    intro N d hd
    have hb := evenHalfCutoffCoreSupport_mem_bounds hd
    exact ⟨hb.1, by omega⟩
  have hlarge : ∀ᶠ N : ℕ in atTop, 3 ≤ rows N :=
    hcofinal (eventually_ge_atTop 3)
  have hlinearBase :
      Tendsto (fun R : ℕ ↦ (2 : ℝ) / (2 : ℝ) ^ R)
        atTop (nhds 0) := by
    have hOne :
        Tendsto (fun R : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ R)
          atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : (1 : ℝ) < 2))
    convert hOne.const_mul 2 using 1
    · funext R
      ring
    · norm_num
  have hlinear :
      Tendsto (fun N : ℕ ↦ (2 : ℝ) / (2 : ℝ) ^ (rows N))
        atTop (nhds 0) :=
    hlinearBase.comp hcofinal
  have hupper :
      Tendsto
        (fun N : ℕ ↦
          (2 : ℝ) / (2 : ℝ) ^ (rows N) +
            evenHalfCutoffCoreNormalizedRemainder (rows N))
        atTop (nhds 0) := by
    simpa using hlinear.add hnormalized
  have herror : Tendsto
      (fun N : ℕ ↦ |y N - (1 : ℝ) / 2|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun N ↦ abs_nonneg _
    · filter_upwards [hlarge] with N hR
      have hrowDefect :
          localPrefixQuotient (D N) (2 * rows N) +
              evenHalfCutoffCoreRemainder (rows N) =
            2 ^ (2 * rows N - 1) - 1 := by
        simpa [D] using
          localPrefixQuotient_evenHalfCutoffCoreSupport_add_remainder
            (show 2 ≤ rows N by omega)
      have hraw :=
        abs_exactLocalMersenneRowValue_sub_half_le_of_defect
          (n := 2 * rows N)
          (r := evenHalfCutoffCoreRemainder (rows N))
          (show 2 ≤ 2 * rows N by omega)
          (hD N) hrowDefect
      have hlinNat : 2 * rows N + 1 ≤ 2 ^ (rows N + 1) := by
        have h := two_mul_add_four_lt_two_pow_succ hR
        omega
      have hnum :
          ((2 * rows N + 1 +
              evenHalfCutoffCoreRemainder (rows N) : ℕ) : ℝ) ≤
            ((2 ^ (rows N + 1) : ℕ) : ℝ) +
              (evenHalfCutoffCoreRemainder (rows N) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hlinNat _
      calc
        |y N - (1 : ℝ) / 2| ≤
            (((2 * rows N + 1 +
              evenHalfCutoffCoreRemainder (rows N) : ℕ) : ℝ) /
                (2 : ℝ) ^ (2 * rows N)) := hraw
        _ ≤ ((((2 ^ (rows N + 1) : ℕ) : ℝ) +
              (evenHalfCutoffCoreRemainder (rows N) : ℝ)) /
                (2 : ℝ) ^ (2 * rows N)) := by
              exact div_le_div_of_nonneg_right hnum (by positivity)
        _ = (2 : ℝ) / (2 : ℝ) ^ (rows N) +
              evenHalfCutoffCoreNormalizedRemainder (rows N) := by
              rw [show 2 * rows N = rows N + rows N by omega]
              norm_num [pow_add, pow_succ,
                evenHalfCutoffCoreNormalizedRemainder]
              rw [show (4 : ℝ) ^ rows N =
                (2 : ℝ) ^ (rows N * 2) by
                  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
                  congr 1
                  omega]
              field_simp
              ring
    · exact hupper
  have hy : Tendsto y atTop (nhds ((1 : ℝ) / 2)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using herror
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall fun N ↦
      exactLocalMersenneRowValue_mem_mersenneAchievementSet
        (fun d hd ↦ (hD N d hd).1))

/-! ## Cofinal closed-set consumer -/

/-- **Cofinal exact-row consumer.**  Arbitrarily large exact finite quotient
rows force `1/2` into the closed Mersenne achievement set.  The selected rows
may be mutually incompatible; only their endpoint lengths tend to infinity. -/
theorem half_mem_mersenneAchievementSet_of_cofinalExactLocalRows
    (hcofinal : CofinalExactLocalMersenneHalfRows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  unfold CofinalExactLocalMersenneHalfRows at hcofinal
  have hsupply : ∀ N : ℕ, ∃ n : ℕ,
      max N 2 ≤ n ∧ ExactLocalMersenneHalfRow n := fun N ↦
    hcofinal (max N 2)
  choose n hn hrow using hsupply
  simp only [ExactLocalMersenneHalfRow] at hrow
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
    exact abs_exactLocalMersenneRowValue_sub_half_le
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

/-- **Lower-half greedy endgame.**  A cofinal supply of the explicit
half-cutoff window inequality puts `1/2` in the Mersenne achievement set. -/
theorem half_mem_mersenneAchievementSet_of_cofinalHalfCutoffGreedyWindows
    (hwindow : CofinalHalfCutoffGreedyWindows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_cofinalExactLocalRows
    (cofinalExactLocalMersenneHalfRows_of_halfCutoffGreedyWindows hwindow)

/-- **Even-core forbidden-state endgame.**  A cofinal supply of the coarse
core bound together with avoidance of the one exact state `2^R` proves the
half-value instance of Erdős #257. -/
theorem half_mem_mersenneAchievementSet_of_cofinalEvenCoreSafety
    (hcore : CofinalEvenHalfCutoffCoreSafety) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_cofinalHalfCutoffGreedyWindows
    (cofinalHalfCutoffGreedyWindows_of_evenCoreSafety hcore)

#print axioms exactLocalMersenneHalfRow_of_halfCutoffGreedyWindow
#print axioms cofinalExactLocalMersenneHalfRows_of_halfCutoffGreedyWindows
#print axioms half_mem_mersenneAchievementSet_of_cofinalHalfCutoffGreedyWindows
#print axioms cofinalHalfCutoffGreedyWindows_of_evenCoreSafety
#print axioms half_mem_mersenneAchievementSet_of_cofinalEvenCoreSafety
#print axioms abs_exactLocalMersenneRowValue_sub_half_le_of_defect
#print axioms half_mem_mersenneAchievementSet_of_cofinalEvenCoreBound
#print axioms half_mem_mersenneAchievementSet_of_evenCoreSubquadraticAlong

end Erdos257PeriodNoncollapse
