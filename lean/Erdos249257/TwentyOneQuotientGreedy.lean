import Erdos249257.TwentyOneQuotientCompactness
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.BooleanMobiusExactTransition
import Erdos249257.HalfCutLocator
import Erdos249257.HalfGreedyFatalGap

/-!
# The canonical quotient-greedy construction at `1/21`

The compactness criterion in `TwentyOneQuotientCompactness` asks for one
finite quotient row at every even depth.  This file makes that row
deterministic: run the ordinary descending integer-greedy algorithm on the
quotient weights for ranks `2,…,R`.

The decoded support is automatically admissible, and its quotient defect is
exactly the algorithm's terminal remainder.  Thus the prescribed rational
point belongs to the Mersenne achievement set as soon as one proves the
single scalar inequality

`integerGreedyRemainder (localMersenneWeights (2 * R) R)
  (twentyOneQuotientTarget (2 * R)) < 2 ^ R`.
-/

namespace Erdos249257

open Filter Set
open BooleanMobiusGreedyReduction
open HalfCylinderIntegerGreedy

/-- The deterministic finite support obtained from the quotient-greedy word
at even depth `2R`. -/
def twentyOneEvenQuotientGreedySupport (R : ℕ) : Finset ℕ :=
  lowerSupportFromBits 2
    (integerGreedyBits
      (localMersenneWeights (2 * R) R)
      (twentyOneQuotientTarget (2 * R)))

/-- The terminal scalar state of the same quotient-greedy row. -/
def twentyOneEvenQuotientGreedyRemainder (R : ℕ) : ℕ :=
  integerGreedyRemainder
    (localMersenneWeights (2 * R) R)
    (twentyOneQuotientTarget (2 * R))

/-- Remainder just before the terminal rank `R` is processed. -/
def twentyOneEvenQuotientCoreRemainder (R : ℕ) : ℕ :=
  integerGreedyRemainder
    (localMersenneWeights (2 * R) (R - 1))
    (twentyOneQuotientTarget (2 * R))

/-- The positive Mersenne gap contains more than half of its second
geometric channel. -/
theorem half_quarter_pow_lt_mersenneGap
    {d : ℕ} (hd : 0 < d) :
    (1 / 2 : ℝ) * ((1 : ℝ) / 4) ^ d < mersenneGap d := by
  have hweight := mersenneWeight_eq_two_channels_add_remainder hd
  have hrem := mersenneWeightRemainder_nonneg (n := d) hd
  have hcorr := mersenneCorrectionTail_lt_doubleDepth (m := d) hd
  have hcorrPow :
      ((1 : ℝ) / 2) ^ (2 * d + 1) =
        (1 / 2 : ℝ) * ((1 : ℝ) / 4) ^ d := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [hcorrPow] at hcorr
  rw [mersenneGap_eq_weightCorrection_sub_correctionTail]
  nlinarith

/-- At every genuinely earlier rank, scaling its positive Mersenne gap to
the even endpoint leaves more than one full integer unit. -/
theorem one_lt_four_pow_mul_mersenneGap_of_lt
    {R d : ℕ} (hd : 0 < d) (hdR : d < R) :
    (1 : ℝ) < (4 : ℝ) ^ R * mersenneGap d := by
  have hgap := half_quarter_pow_lt_mersenneGap hd
  have hmul := mul_lt_mul_of_pos_left hgap
    (show 0 < (4 : ℝ) ^ R by positivity)
  have hcancel :
      (4 : ℝ) ^ d * ((1 : ℝ) / 4) ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  have hsplit :
      (4 : ℝ) ^ R = (4 : ℝ) ^ (R - d) * (4 : ℝ) ^ d := by
    rw [← pow_add]
    congr 1
    omega
  have hscaled :
      (4 : ℝ) ^ R * ((1 / 2 : ℝ) * ((1 : ℝ) / 4) ^ d) =
        (1 / 2 : ℝ) * (4 : ℝ) ^ (R - d) := by
    rw [hsplit]
    calc
      (4 : ℝ) ^ (R - d) * (4 : ℝ) ^ d *
            ((1 / 2 : ℝ) * ((1 : ℝ) / 4) ^ d)
          = (1 / 2 : ℝ) * (4 : ℝ) ^ (R - d) *
              ((4 : ℝ) ^ d * ((1 : ℝ) / 4) ^ d) := by ring
      _ = (1 / 2 : ℝ) * (4 : ℝ) ^ (R - d) := by rw [hcancel]; ring
  have hpow :
      (4 : ℝ) ^ 1 ≤ (4 : ℝ) ^ (R - d) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [hscaled] at hmul
  norm_num at hpow
  linarith

/-- **The denominator-21 quotient word has one more unit of separation than
the generic binary-window estimate.**  At a nonterminal rank, that extra
unit comes from the scaled positive Mersenne gap; at the terminal rank it is
the exact `2^R+1` coin. -/
theorem localMersenneQuotient_two_mul_strong_dominanceGap
    {R d : ℕ} (hd : 2 ≤ d) (hdR : d ≤ R) :
    2 ^ R + 1 +
        (localMersenneWeightsFrom (2 * R) R (d + 1)).sum ≤
      localMersenneQuotient (2 * R) d := by
  by_cases heq : d = R
  · subst d
    rw [localMersenneWeightsFrom_eq_nil (by omega),
      List.sum_nil, localMersenneQuotient_two_mul_self (by omega)]
    omega
  · have hdlt : d < R := by omega
    have htail :
        (((localMersenneWeightsFrom (2 * R) R (d + 1)).sum : ℕ) : ℝ) +
            (2 : ℝ) ^ (2 * R) * mersenneTail R ≤
          (2 : ℝ) ^ (2 * R) * mersenneTail d := by
      simpa [show d + 1 - 1 = d by omega] using
        localMersenneWeightsFrom_cast_sum_add_tail_le
          (2 * R) R (d + 1) (by omega) (by omega)
    have hcorr := mersenneCorrectionTail_pos R
    have hfirst :
        ((1 : ℝ) / 2) ^ R < mersenneTail R := by
      unfold mersenneCorrectionTail at hcorr
      linarith
    have hscale := two_pow_mul_half_pow
      (M := 2 * R) (R := R) (by omega)
    have hscaledTail :
        (2 : ℝ) ^ R <
          (2 : ℝ) ^ (2 * R) * mersenneTail R := by
      have hscale' :
          (2 : ℝ) ^ R =
            (2 : ℝ) ^ (2 * R) * ((1 : ℝ) / 2) ^ R := by
        simpa [show 2 * R - R = R by omega] using hscale.symm
      rw [hscale']
      exact mul_lt_mul_of_pos_left hfirst (by positivity)
    have hpowFour :
        (2 : ℝ) ^ (2 * R) = (4 : ℝ) ^ R := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    have hscaledGap :
        (1 : ℝ) <
          (2 : ℝ) ^ (2 * R) * mersenneGap d := by
      rw [hpowFour]
      exact one_lt_four_pow_mul_mersenneGap_of_lt (by omega) hdlt
    have hhead := scaled_lt_localMersenneQuotient_cast_add_one
      (M := 2 * R) (d := d) (by omega)
    have hreal :
        (((2 ^ R + 1 +
            (localMersenneWeightsFrom (2 * R) R (d + 1)).sum : ℕ) : ℕ) : ℝ) <
          (((localMersenneQuotient (2 * R) d + 1 : ℕ) : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      calc
        (2 : ℝ) ^ R + 1 +
              (((localMersenneWeightsFrom (2 * R) R (d + 1)).sum : ℕ) : ℝ)
            < (2 : ℝ) ^ (2 * R) * mersenneTail R +
                (2 : ℝ) ^ (2 * R) * mersenneGap d +
                (((localMersenneWeightsFrom (2 * R) R (d + 1)).sum : ℕ) : ℝ) := by
                  linarith
        _ ≤ (2 : ℝ) ^ (2 * R) * mersenneTail d +
              (2 : ℝ) ^ (2 * R) * mersenneGap d := by
                linarith
        _ = (2 : ℝ) ^ (2 * R) * mersenneWeight d := by
              unfold mersenneGap
              ring
        _ < (localMersenneQuotient (2 * R) d : ℝ) + 1 :=
          by simpa using hhead
    have hnat :
        2 ^ R + 1 +
            (localMersenneWeightsFrom (2 * R) R (d + 1)).sum <
          localMersenneQuotient (2 * R) d + 1 := by
      exact_mod_cast hreal
    omega

/-- Recursive form of the strong denominator-21 separation estimate. -/
theorem localMersenneWeightsFrom_two_mul_strong_gapDominates
    {R d : ℕ} (hd : 2 ≤ d) :
    GapDominates (2 ^ R + 1)
      (localMersenneWeightsFrom (2 * R) R d) := by
  by_cases hdR : d ≤ R
  · rw [localMersenneWeightsFrom_eq_cons hdR, GapDominates]
    exact
      ⟨localMersenneQuotient_two_mul_strong_dominanceGap hd hdR,
        localMersenneWeightsFrom_two_mul_strong_gapDominates (by omega)⟩
  · rw [localMersenneWeightsFrom_eq_nil (by omega)]
    trivial
termination_by R + 1 - d
decreasing_by omega

/-- The full lower denominator-21 quotient word separates distinct Boolean
rows by at least `2^R+1`, including the formerly saturated boundary. -/
theorem localMersenneWeights_two_mul_strong_gapDominates (R : ℕ) :
    GapDominates (2 ^ R + 1)
      (localMersenneWeights (2 * R) R) := by
  exact localMersenneWeightsFrom_two_mul_strong_gapDominates (by omega)

/-- **Strict closed rows are canonical.**  The quantitative
superincreasing gap of the lower quotient word leaves no freedom below the
binary boundary: any Boolean word whose defect is strictly smaller than
`2^R` is exactly the deterministic quotient-greedy word, with the same
terminal remainder. -/
theorem twentyOneStrictClosedRow_forces_quotientGreedy
    {R s : ℕ} {bits : List Bool}
    (hlen :
      bits.length = (localMersenneWeights (2 * R) R).length)
    (hrow :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits + s =
        twentyOneQuotientTarget (2 * R))
    (hstrict : s < 2 ^ R) :
    bits =
        integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) ∧
      s = twentyOneEvenQuotientGreedyRemainder R := by
  have hunique :=
    lower_word_eq_greedy_and_remainder_eq
      (M := 2 * R) (R := R)
      (C := twentyOneQuotientTarget (2 * R)) (A := s)
      (weights := localMersenneWeights (2 * R) R) (bits := bits)
      (by rw [lowerBinaryWindow_odd]; positivity)
      (localMersenneWeights_gapDominates (by omega))
      hlen hrow
      (by simpa only [lowerBinaryWindow_odd] using hstrict)
  simpa [twentyOneEvenQuotientGreedyRemainder] using hunique

/-- **Every closed row is canonical, including exact saturation.**  The
extra unit in the denominator-21 separation estimate upgrades the closed
inequality `s ≤ 2^R` to a strict gap inequality. -/
theorem twentyOneClosedRow_forces_quotientGreedy
    {R s : ℕ} {bits : List Bool}
    (hlen :
      bits.length = (localMersenneWeights (2 * R) R).length)
    (hrow :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits + s =
        twentyOneQuotientTarget (2 * R))
    (hclosed : s ≤ 2 ^ R) :
    bits =
        integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) ∧
      s = twentyOneEvenQuotientGreedyRemainder R := by
  have hadm :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits ≤
        twentyOneQuotientTarget (2 * R) := by
    omega
  have hdefect :
      twentyOneQuotientTarget (2 * R) -
          weightedBoolSum (localMersenneWeights (2 * R) R) bits = s := by
    omega
  have heq :=
    eq_integerGreedyBits_of_remainder_lt_gap
      (gap := 2 ^ R + 1)
      (C := twentyOneQuotientTarget (2 * R))
      (weights := localMersenneWeights (2 * R) R)
      (bits := bits)
      (by positivity)
      (localMersenneWeights_two_mul_strong_gapDominates R)
      hlen hadm (by omega)
  subst bits
  exact ⟨rfl, by
    simpa [twentyOneEvenQuotientGreedyRemainder,
      integerGreedyRemainder] using hdefect.symm⟩

/-- Compatibility form of the former closed-row boundary dichotomy.  The
strong gap proves the right disjunct unconditionally, so exact saturation is
no longer a distinct Boolean row. -/
theorem twentyOneClosedRow_boundary_or_quotientGreedy
    {R s : ℕ} {bits : List Bool}
    (hlen :
      bits.length = (localMersenneWeights (2 * R) R).length)
    (hrow :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits + s =
        twentyOneQuotientTarget (2 * R))
    (hclosed : s ≤ 2 ^ R) :
    s = 2 ^ R ∨
      (bits =
          integerGreedyBits
            (localMersenneWeights (2 * R) R)
            (twentyOneQuotientTarget (2 * R)) ∧
        s = twentyOneEvenQuotientGreedyRemainder R) := by
  exact Or.inr (twentyOneClosedRow_forces_quotientGreedy hlen hrow hclosed)

/-- Exact one-state transition at the final rank.  The last quotient coin is
`2^R + 1`. -/
theorem twentyOneEvenQuotientGreedyRemainder_eq_coreStep
    {R : ℕ} (hR : 2 ≤ R) :
    twentyOneEvenQuotientGreedyRemainder R =
      if 2 ^ R + 1 ≤ twentyOneEvenQuotientCoreRemainder R then
        twentyOneEvenQuotientCoreRemainder R - (2 ^ R + 1)
      else
        twentyOneEvenQuotientCoreRemainder R := by
  unfold twentyOneEvenQuotientGreedyRemainder
  rw [localMersenneWeights_even_halfCutoff_split hR,
    integerGreedyRemainder_append]
  change integerGreedyRemainder [2 ^ R + 1]
      (twentyOneEvenQuotientCoreRemainder R) = _
  rw [integerGreedyRemainder_cons]
  simp only [integerGreedyRemainder_nil]

/-- The desired final window has an exact two-interval description in terms
of the strict-core state. -/
theorem twentyOneEvenQuotientGreedyRemainder_lt_iff
    {R : ℕ} (hR : 2 ≤ R) :
    twentyOneEvenQuotientGreedyRemainder R < 2 ^ R ↔
      twentyOneEvenQuotientCoreRemainder R < 2 ^ R ∨
        (2 ^ R + 1 ≤ twentyOneEvenQuotientCoreRemainder R ∧
          twentyOneEvenQuotientCoreRemainder R < 2 * 2 ^ R + 1) := by
  rw [twentyOneEvenQuotientGreedyRemainder_eq_coreStep hR]
  by_cases htake :
      2 ^ R + 1 ≤ twentyOneEvenQuotientCoreRemainder R
  · rw [if_pos htake]
    omega
  · rw [if_neg htake]
    omega

/-- Under the natural coarse core bound, failure is the single exact state
`2^R`; no interval estimate remains. -/
theorem twentyOneEvenQuotientGreedyRemainder_lt_iff_core_ne
    {R : ℕ} (hR : 2 ≤ R) :
    twentyOneEvenQuotientGreedyRemainder R < 2 ^ R ↔
      twentyOneEvenQuotientCoreRemainder R < 2 * 2 ^ R + 1 ∧
        twentyOneEvenQuotientCoreRemainder R ≠ 2 ^ R := by
  rw [twentyOneEvenQuotientGreedyRemainder_lt_iff hR]
  omega

/-! ## Constant-width terminal fringe

One step farther back, the last strict-core coin has the exact value
`2^(R+1)+4`.  Consequently the factor-two core ceiling can fail, subject
to a coarse preterminal bound, at only six explicitly named integers. -/

/-- Remainder immediately before the last strict-core rank `R-1`. -/
def twentyOneEvenQuotientPreterminalRemainder (R : ℕ) : ℕ :=
  integerGreedyRemainder
    (localMersenneWeights (2 * R) (R - 2))
    (twentyOneQuotientTarget (2 * R))

/-- The last strict-core quotient coin differs from its binary skeleton by
exactly four. -/
theorem localMersenneQuotient_two_mul_pred
    {R : ℕ} (hR : 4 ≤ R) :
    localMersenneQuotient (2 * R) (R - 1) = 2 ^ (R + 1) + 4 := by
  let P := 2 ^ (R - 1)
  let q := P - 1
  let Q := 2 ^ (R + 1) + 4
  have hP : 8 ≤ P := by
    dsimp [P]
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (show 3 ≤ R - 1 by omega))
  have hqadd : q + 1 = P := by
    dsimp [q]
    omega
  have hB : 2 ^ (R + 1) = 4 * P := by
    dsimp [P]
    rw [show R + 1 = (R - 1) + 2 by omega, pow_add]
    norm_num
    ring
  have hpow : 2 ^ (2 * R) = 4 * P * P := by
    dsimp [P]
    rw [show 2 * R = (R - 1) + (R - 1) + 2 by omega,
      pow_add, pow_add]
    norm_num
    ring
  have hdecomp : 2 ^ (2 * R) = Q * q + 4 := by
    rw [hpow]
    symm
    calc
      Q * q + 4 = 4 * P * q + 4 * (q + 1) := by
        dsimp [Q]
        rw [hB]
        ring
      _ = 4 * P * q + 4 * P := by rw [hqadd]
      _ = 4 * P * (q + 1) := by ring
      _ = 4 * P * P := by rw [hqadd]
  have hfour : 4 < q := by
    dsimp [q]
    omega
  unfold localMersenneQuotient
  change 2 ^ (2 * R) / q = Q
  apply Nat.div_eq_of_lt_le
  · rw [hdecomp]
    exact Nat.le_add_right _ _
  · rw [hdecomp]
    calc
      Q * q + 4 < Q * q + q := Nat.add_lt_add_left hfour _
      _ = (Q + 1) * q := by ring

/-- The preceding quotient coin has only a constant additive excess over
its binary skeleton.  This deliberately uses a coarse constant: after
normalization by `4^R`, every fixed excess is negligible. -/
theorem localMersenneQuotient_two_mul_pred_pred_le
    {R : ℕ} (hR : 4 ≤ R) :
    localMersenneQuotient (2 * R) (R - 2) ≤
      2 ^ (R + 2) + 21 := by
  by_cases hR4 : R = 4
  · subst R
    norm_num [localMersenneQuotient]
  · have hR5 : 5 ≤ R := by omega
    let P := 2 ^ (R - 2)
    have hP : 8 ≤ P := by
      dsimp [P]
      simpa using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2)
          (show 3 ≤ R - 2 by omega))
    have hden : 0 < P - 1 := by omega
    have hlarge : 21 ≤ 5 * P := by omega
    have hB : 2 ^ (R + 2) = 16 * P := by
      dsimp [P]
      rw [show R + 2 = (R - 2) + 4 by omega, pow_add]
      norm_num
      ring
    have hpow : 2 ^ (2 * R) = 16 * P * P := by
      dsimp [P]
      rw [show 2 * R = (R - 2) + (R - 2) + 4 by omega,
        pow_add, pow_add]
      norm_num
      ring
    unfold localMersenneQuotient
    change 2 ^ (2 * R) / (P - 1) ≤ 2 ^ (R + 2) + 21
    apply (Nat.div_le_iff_le_mul hden).2
    have hmul :
        16 * P * P ≤ (16 * P + 21) * (P - 1) := by
      let q := P - 1
      have hPq : P = q + 1 := by
        dsimp [q]
        omega
      rw [hPq]
      simp only [Nat.add_sub_cancel]
      nlinarith
    rw [hpow, hB]
    omega

/-- Exact final transition inside the strict core. -/
theorem twentyOneEvenQuotientCoreRemainder_eq_preterminalStep
    {R : ℕ} (hR : 4 ≤ R) :
    twentyOneEvenQuotientCoreRemainder R =
      if 2 ^ (R + 1) + 4 ≤
          twentyOneEvenQuotientPreterminalRemainder R then
        twentyOneEvenQuotientPreterminalRemainder R -
          (2 ^ (R + 1) + 4)
      else
        twentyOneEvenQuotientPreterminalRemainder R := by
  have htail :
      localMersenneWeightsFrom (2 * R) (R - 1) (R - 1) =
        [localMersenneQuotient (2 * R) (R - 1)] := by
    rw [localMersenneWeightsFrom_eq_cons (by omega),
      localMersenneWeightsFrom_eq_nil (by omega)]
  have hsplit :
      localMersenneWeights (2 * R) (R - 1) =
        localMersenneWeights (2 * R) (R - 2) ++
          [localMersenneQuotient (2 * R) (R - 1)] := by
    unfold localMersenneWeights
    rw [localMersenneWeightsFrom_split
        (M := 2 * R) (S := R - 1) (R := R - 2) (d := 2)
        (by omega) (by omega),
      show R - 2 + 1 = R - 1 by omega,
      htail]
  unfold twentyOneEvenQuotientCoreRemainder
  rw [hsplit, integerGreedyRemainder_append]
  change integerGreedyRemainder
      [localMersenneQuotient (2 * R) (R - 1)]
      (twentyOneEvenQuotientPreterminalRemainder R) = _
  rw [integerGreedyRemainder_cons,
    localMersenneQuotient_two_mul_pred hR]
  simp only [integerGreedyRemainder_nil]

/-- The core ceiling is exactly two safe intervals in the preterminal
state.  The missing lower fringe has width three. -/
theorem twentyOneEvenQuotientCoreRemainder_lt_iff_preterminal
    {R : ℕ} (hR : 4 ≤ R) :
    twentyOneEvenQuotientCoreRemainder R < 2 ^ (R + 1) + 1 ↔
      twentyOneEvenQuotientPreterminalRemainder R < 2 ^ (R + 1) + 1 ∨
        (2 ^ (R + 1) + 4 ≤
            twentyOneEvenQuotientPreterminalRemainder R ∧
          twentyOneEvenQuotientPreterminalRemainder R <
            2 * 2 ^ (R + 1) + 5) := by
  rw [twentyOneEvenQuotientCoreRemainder_eq_preterminalStep hR]
  by_cases htake :
      2 ^ (R + 1) + 4 ≤ twentyOneEvenQuotientPreterminalRemainder R
  · rw [if_pos htake]
    omega
  · rw [if_neg htake]
    omega

/-- Under the natural twice-last-coin prebound, only six integer states can
violate the sufficient core ceiling. -/
theorem twentyOneEvenQuotientCoreRemainder_lt_of_preterminal_fringe_avoidance
    {R : ℕ} (hR : 4 ≤ R)
    (hpre :
      twentyOneEvenQuotientPreterminalRemainder R <
        2 * 2 ^ (R + 1) + 8)
    (h₁ : twentyOneEvenQuotientPreterminalRemainder R ≠ 2 ^ (R + 1) + 1)
    (h₂ : twentyOneEvenQuotientPreterminalRemainder R ≠ 2 ^ (R + 1) + 2)
    (h₃ : twentyOneEvenQuotientPreterminalRemainder R ≠ 2 ^ (R + 1) + 3)
    (h₅ :
      twentyOneEvenQuotientPreterminalRemainder R ≠
        2 * 2 ^ (R + 1) + 5)
    (h₆ :
      twentyOneEvenQuotientPreterminalRemainder R ≠
        2 * 2 ^ (R + 1) + 6)
    (h₇ :
      twentyOneEvenQuotientPreterminalRemainder R ≠
        2 * 2 ^ (R + 1) + 7) :
    twentyOneEvenQuotientCoreRemainder R < 2 ^ (R + 1) + 1 := by
  rw [twentyOneEvenQuotientCoreRemainder_lt_iff_preterminal hR]
  omega

/-! ## Full-row binary completion

The half-cutoff endpoint above deliberately discards the quotient coins at
ranks `R+1,…,2R`.  Those coins are the exact binary word
`2^(R-1),…,1`.  Retaining them removes the isolated forbidden state
`core = 2^R`: that state is completed with defect exactly one, which is
already negligible after division by `4^R`.
-/

/-- The deterministic quotient-greedy support using every rank through the
binary endpoint `2R`. -/
def twentyOneEvenFullQuotientGreedySupport (R : ℕ) : Finset ℕ :=
  lowerSupportFromBits 2
    (integerGreedyBits
      (localMersenneWeights (2 * R) (2 * R))
      (twentyOneQuotientTarget (2 * R)))

/-- The terminal defect after the complete quotient word through `2R`. -/
def twentyOneEvenFullQuotientGreedyRemainder (R : ℕ) : ℕ :=
  integerGreedyRemainder
    (localMersenneWeights (2 * R) (2 * R))
    (twentyOneQuotientTarget (2 * R))

/-- Weak form of exact binary completion.  A capacity at most the total
binary window leaves remainder at most one; strict inequality gives the
existing zero-remainder theorem. -/
theorem integerGreedyRemainder_upperMersenneWindow_le_one
    {M d C : ℕ} (hd2 : 2 ≤ d) (hhalf : M / 2 < d)
    (hdM : d ≤ M + 1) (hC : C ≤ 2 ^ (M + 1 - d)) :
    integerGreedyRemainder (localMersenneWeightsFrom M M d) C ≤ 1 := by
  by_cases hend : d = M + 1
  · subst d
    rw [localMersenneWeightsFrom_eq_nil (by omega)]
    simp only [integerGreedyRemainder_nil, Nat.sub_self, pow_zero] at hC ⊢
    omega
  · have hdle : d ≤ M := by omega
    have hcoin :=
      localMersenneQuotient_eq_two_pow_sub_of_half_lt hd2 hhalf hdle
    rw [localMersenneWeightsFrom_eq_cons hdle,
      integerGreedyRemainder_cons, hcoin]
    have hpow :
        2 ^ (M + 1 - d) = 2 * 2 ^ (M - d) := by
      rw [show M + 1 - d = (M - d) + 1 by omega, pow_succ]
      ring
    by_cases htake : 2 ^ (M - d) ≤ C
    · rw [if_pos htake]
      apply integerGreedyRemainder_upperMersenneWindow_le_one
          (d := d + 1)
      · omega
      · omega
      · omega
      · rw [show M + 1 - (d + 1) = M - d by omega]
        rw [hpow] at hC
        omega
    · rw [if_neg htake]
      apply integerGreedyRemainder_upperMersenneWindow_le_one
          (d := d + 1)
      · omega
      · omega
      · omega
      · rw [show M + 1 - (d + 1) = M - d by omega]
        omega
termination_by M + 1 - d
decreasing_by
  all_goals
    have hstep : M + 1 - (d + 1) = M - d := by omega
    rw [hstep]
    omega

/-- Additive-slack form of binary completion.  If the incoming carry exceeds
the complete upper binary capacity by at most `K`, its terminal defect is at
most `K+1`.  The old closed-window lemma is the case `K=0`. -/
theorem integerGreedyRemainder_upperMersenneWindow_le_add
    {M d C K : ℕ} (hd2 : 2 ≤ d) (hhalf : M / 2 < d)
    (hdM : d ≤ M + 1) (hC : C ≤ 2 ^ (M + 1 - d) + K) :
    integerGreedyRemainder (localMersenneWeightsFrom M M d) C ≤ K + 1 := by
  by_cases hend : d = M + 1
  · subst d
    rw [localMersenneWeightsFrom_eq_nil (by omega)]
    simp only [integerGreedyRemainder_nil, Nat.sub_self, pow_zero] at hC ⊢
    omega
  · have hdle : d ≤ M := by omega
    have hcoin :=
      localMersenneQuotient_eq_two_pow_sub_of_half_lt hd2 hhalf hdle
    rw [localMersenneWeightsFrom_eq_cons hdle,
      integerGreedyRemainder_cons, hcoin]
    have hpow :
        2 ^ (M + 1 - d) = 2 * 2 ^ (M - d) := by
      rw [show M + 1 - d = (M - d) + 1 by omega, pow_succ]
      ring
    by_cases htake : 2 ^ (M - d) ≤ C
    · rw [if_pos htake]
      apply integerGreedyRemainder_upperMersenneWindow_le_add
          (d := d + 1) (K := K)
      · omega
      · omega
      · omega
      · rw [show M + 1 - (d + 1) = M - d by omega]
        rw [hpow] at hC
        omega
    · rw [if_neg htake]
      apply integerGreedyRemainder_upperMersenneWindow_le_add
          (d := d + 1) (K := K)
      · omega
      · omega
      · omega
      · rw [show M + 1 - (d + 1) = M - d by omega]
        omega
termination_by M + 1 - d
decreasing_by
  all_goals
    have hstep : M + 1 - (d + 1) = M - d := by omega
    rw [hstep]
    omega

/-! ## Two-step quotient pulses

Passing from even depth `M` to `M+2` multiplies every old quotient by four.
The entire rounding correction is the two-bit divisor pulse

`2 * 1_{d ∣ M+1} + 1_{d ∣ M+2}`.

Thus a frozen finite prefix has only one small, explicitly arithmetic
perturbation when an exact row is lifted by two depths. -/

/-- The correction to fourfold scaling of one Mersenne quotient. -/
def localMersenneTwoStepPulse (M d : ℕ) : ℕ :=
  2 * (if d ∣ M + 1 then 1 else 0) +
    (if d ∣ M + 2 then 1 else 0)

theorem localMersenneTwoStepPulse_le_three (M d : ℕ) :
    localMersenneTwoStepPulse M d ≤ 3 := by
  unfold localMersenneTwoStepPulse
  split_ifs <;> omega

/-- Exact fourfold scaling with its two endpoint-divisor bits exposed. -/
theorem localMersenneQuotient_add_two
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient (M + 2) d =
      4 * localMersenneQuotient M d +
        localMersenneTwoStepPulse M d := by
  rw [show M + 2 = (M + 1) + 1 by omega,
    localMersenneQuotient_endpoint_succ hd,
    localMersenneQuotient_endpoint_succ hd]
  unfold localMersenneTwoStepPulse
  split_ifs <;> omega

/-- The aggregate two-bit pulse of a frozen finite support. -/
def localPrefixTwoStepPulse (D : Finset ℕ) (M : ℕ) : ℕ :=
  2 * endpointDivisorContribution D (M + 1) +
    endpointDivisorContribution D (M + 2)

/-- Each selected lower rank contributes at most the two-bit word `11`.
This cardinality bound is the coarse estimate which makes carry
nonnegativity automatic once the scalar state dominates the support size. -/
theorem localPrefixTwoStepPulse_le_three_mul_card
    (D : Finset ℕ) (M : ℕ) :
    localPrefixTwoStepPulse D M ≤ 3 * D.card := by
  unfold localPrefixTwoStepPulse endpointDivisorContribution
  have h₁ := Finset.card_filter_le D (fun d ↦ d ∣ M + 1)
  have h₂ := Finset.card_filter_le D (fun d ↦ d ∣ M + 2)
  omega

/-- Endpoint divisor pulses have a genuine finite memory horizon.  If the
support is bounded by `R`, then a divisor contributing at either endpoint
`2R+1` or `2R+2` is already at most `⌊(2R+2)/3⌋`: the complementary factor
cannot be one or two.  Thus the newest third of the support cannot influence
the next two-step pulse. -/
theorem endpointDivisorContribution_horizon_stable
    (D : Finset ℕ) {R n : ℕ}
    (hD : ∀ d ∈ D, d ≤ R)
    (hnlo : 2 * R + 1 ≤ n) (hnhi : n ≤ 2 * R + 2) :
    endpointDivisorContribution D n =
      endpointDivisorContribution
        (D.filter fun d ↦ d ≤ (2 * R + 2) / 3) n := by
  classical
  have hcut :
      ∀ d ∈ D, d ∣ n → d ≤ (2 * R + 2) / 3 := by
    intro d hdD hdvd
    obtain ⟨q, rfl⟩ := hdvd
    have hq : 3 ≤ q := by
      by_contra hnot
      have hqle : q ≤ 2 := by omega
      have hprod : d * q ≤ R * 2 :=
        Nat.mul_le_mul (hD d hdD) hqle
      omega
    have hthree : d * 3 ≤ d * q :=
      Nat.mul_le_mul_left d hq
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 3)).2
    omega
  unfold endpointDivisorContribution
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hdD, hdvd⟩
    exact ⟨⟨hdD, hcut d hdD hdvd⟩, hdvd⟩
  · rintro ⟨⟨hdD, _hdcut⟩, hdvd⟩
    exact ⟨hdD, hdvd⟩

/-- The aggregate two-step pulse therefore depends only on the oldest
two-thirds of a bounded support.  This is the exact horizon-stability fact
behind the observed one-dimensional quotient replay. -/
theorem localPrefixTwoStepPulse_horizon_stable
    (D : Finset ℕ) (R : ℕ)
    (hD : ∀ d ∈ D, d ≤ R) :
    localPrefixTwoStepPulse D (2 * R) =
      localPrefixTwoStepPulse
        (D.filter fun d ↦ d ≤ (2 * R + 2) / 3) (2 * R) := by
  unfold localPrefixTwoStepPulse
  rw [
    endpointDivisorContribution_horizon_stable D hD
      (show 2 * R + 1 ≤ 2 * R + 1 by omega)
      (show 2 * R + 1 ≤ 2 * R + 2 by omega),
    endpointDivisorContribution_horizon_stable D hD
      (show 2 * R + 1 ≤ 2 * R + 2 by omega)
      (show 2 * R + 2 ≤ 2 * R + 2 by omega)]

/-- A frozen quotient prefix changes by exactly its aggregate divisor pulse. -/
theorem localPrefixQuotient_add_two
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 2) =
      4 * localPrefixQuotient D M +
        localPrefixTwoStepPulse D M := by
  rw [show M + 2 = (M + 1) + 1 by omega,
    localPrefixQuotient_succ hD, localPrefixQuotient_succ hD]
  unfold localPrefixTwoStepPulse
  rw [show M + 1 + 1 = M + 2 by omega]
  omega

/-- The target's corresponding two-step pulse is determined only by the
current residue modulo `21`. -/
def twentyOneTargetTwoStepPulse (M : ℕ) : ℕ :=
  4 * (2 ^ M % 21) / 21

theorem twentyOneTargetTwoStepPulse_le_three (M : ℕ) :
    twentyOneTargetTwoStepPulse M ≤ 3 := by
  unfold twentyOneTargetTwoStepPulse
  have hmod : 2 ^ M % 21 < 21 := Nat.mod_lt _ (by omega)
  have hlt : 4 * (2 ^ M % 21) / 21 < 4 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    omega
  omega

/-- Exact fourfold scaling of the denominator-`21` quotient target. -/
theorem twentyOneQuotientTarget_add_two (M : ℕ) :
    twentyOneQuotientTarget (M + 2) =
      4 * twentyOneQuotientTarget M +
        twentyOneTargetTwoStepPulse M := by
  have hpow : 2 ^ (M + 2) = 4 * 2 ^ M := by
    simp [pow_add, Nat.mul_comm]
  have hdecomp := Nat.mod_add_div (2 ^ M) 21
  have hscaled :
      4 * 2 ^ M =
        4 * (2 ^ M % 21) + 21 * (4 * (2 ^ M / 21)) := by
    omega
  unfold twentyOneQuotientTarget twentyOneTargetTwoStepPulse
  rw [hpow, hscaled,
    Nat.add_mul_div_left (4 * (2 ^ M % 21)) (4 * (2 ^ M / 21))
      (by omega)]
  omega

/-- A rationally safe finite prefix is quotient-admissible at every binary
depth.  This is the denominator-`21` analogue of the one-sided rational
greedy comparison: the positive source fractions prevent an integral
overshoot. -/
theorem localPrefixQuotient_le_twentyOneTarget_of_prefix_le
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hsafe : localMersennePrefixValue D ≤ (1 / 21 : ℚ)) :
    localPrefixQuotient D M ≤ twentyOneQuotientTarget M := by
  have hscale :=
    scaled_localMersennePrefixValue (D := D) (M := M) hD
  have htarget := scaled_one_div_twenty_one_eq_target_add_fraction M
  have hpowNonneg : (0 : ℚ) ≤ (2 : ℚ) ^ M := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsafe hpowNonneg
  rw [hscale, htarget] at hscaled
  have hF0 := localFractionMass_nonneg (D := D) (M := M) hD
  have hrho1 := twentyOneTargetFraction_lt_one M
  have hcast :
      (localPrefixQuotient D M : ℚ) <
        (twentyOneQuotientTarget M + 1 : ℕ) := by
    push_cast
    linarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast hcast)

/-- Quotient-greedy cannot skip a rank which the rational greedy rule could
still take.  Thus any disagreement between the two decisions is necessarily
a quotient-only take, never a false skip. -/
theorem localMersenneQuotient_le_twentyOneRemainder_of_rational_take
    {D : Finset ℕ} {M d : ℕ}
    (hD : ∀ e ∈ D, 2 ≤ e)
    (hd : 2 ≤ d)
    (hnot : d ∉ D)
    (htake :
      localMersennePrefixValue D + mersenneWeightRat d ≤ (1 / 21 : ℚ)) :
    localMersenneQuotient M d ≤
      twentyOneQuotientTarget M - localPrefixQuotient D M := by
  have hDinsert : ∀ e ∈ insert d D, 2 ≤ e := by
    intro e he
    simp only [Finset.mem_insert] at he
    rcases he with rfl | he
    · exact hd
    · exact hD e he
  have hpref :
      localMersennePrefixValue (insert d D) =
        localMersennePrefixValue D + mersenneWeightRat d := by
    unfold localMersennePrefixValue
    rw [Finset.sum_insert hnot]
    ring
  have hquot :
      localPrefixQuotient (insert d D) M =
        localPrefixQuotient D M + localMersenneQuotient M d := by
    unfold localPrefixQuotient
    rw [Finset.sum_insert hnot]
    omega
  have hadm :=
    localPrefixQuotient_le_twentyOneTarget_of_prefix_le
      (D := insert d D) (M := M) hDinsert (by
        rw [hpref]
        exact htake)
  rw [hquot] at hadm
  omega

/-! ## Exact comparison with rational greedy

The quotient algorithm has a one-sided rounding error: relative to the
exact rational greedy word it can take too early, but it cannot skip too
early.  A completed quotient word which is still rationally admissible
therefore has no room for a first disagreement. -/

/-- Exact rational descending-greedy decisions on the consecutive ranks
`d, ..., d + n - 1`, starting from residual capacity `x`. -/
def rationalMersenneGreedyBitsFrom : ℕ → ℕ → ℚ → List Bool
  | _, 0, _ => []
  | d, n + 1, x =>
      if mersenneWeightRat d ≤ x then
        true ::
          rationalMersenneGreedyBitsFrom (d + 1) n
            (x - mersenneWeightRat d)
      else
        false :: rationalMersenneGreedyBitsFrom (d + 1) n x

@[simp] theorem rationalMersenneGreedyBitsFrom_length
    (d n : ℕ) (x : ℚ) :
    (rationalMersenneGreedyBitsFrom d n x).length = n := by
  induction n generalizing d x with
  | zero => simp [rationalMersenneGreedyBitsFrom]
  | succ n ih =>
      simp only [rationalMersenneGreedyBitsFrom]
      split <;> simp [ih]

/-- Greedy execution on a concatenated integer word exposes the first
word verbatim before continuing from its terminal remainder. -/
theorem integerGreedyBits_append
    (xs ys : List ℕ) (C : ℕ) :
    integerGreedyBits (xs ++ ys) C =
      integerGreedyBits xs C ++
        integerGreedyBits ys (integerGreedyRemainder xs C) := by
  induction xs generalizing C with
  | nil => simp [integerGreedyBits]
  | cons w ws ih =>
      simp only [List.cons_append, integerGreedyBits,
        integerGreedyRemainder_cons]
      by_cases htake : w ≤ C <;> simp [htake, ih]

/-- Decoding one appended Boolean decision changes a lower support only at
the new terminal rank.  This is the finite-set counterpart of sequential
integer-greedy execution. -/
theorem lowerSupportFromBits_append_singleton
    (d : ℕ) (bits : List Bool) (b : Bool) :
    lowerSupportFromBits d (bits ++ [b]) =
      if b then
        insert (d + bits.length) (lowerSupportFromBits d bits)
      else
        lowerSupportFromBits d bits := by
  induction bits generalizing d with
  | nil =>
      cases b <;> simp [lowerSupportFromBits]
  | cons a bits ih =>
      have hterminal :
          d + 1 + bits.length = d + (bits.length + 1) := by
        omega
      cases a <;> cases b <;>
        simp [lowerSupportFromBits, ih, hterminal, Finset.insert_comm]

/-- The first `n` exact-rational greedy decisions do not depend on how far
the finite observation horizon is extended. -/
theorem rationalMersenneGreedyBitsFrom_take
    (d n m : ℕ) (x : ℚ) :
    (rationalMersenneGreedyBitsFrom d (n + m) x).take n =
      rationalMersenneGreedyBitsFrom d n x := by
  induction n generalizing d x with
  | zero => simp [rationalMersenneGreedyBitsFrom]
  | succ n ih =>
      simp only [Nat.succ_add, rationalMersenneGreedyBitsFrom]
      by_cases htake : mersenneWeightRat d ≤ x <;>
        simp [htake, ih]

/-- Starting from the genuine rational residual before rank `d`, the
finite rational word decodes exactly to the real greedy support on the
observed interval. -/
theorem mem_lowerSupportFromBits_rationalMersenneGreedyBitsFrom_iff
    {x : ℚ} {d n e : ℕ} (hd : 1 ≤ d) :
    e ∈ lowerSupportFromBits d
          (rationalMersenneGreedyBitsFrom d n
            (greedyMersenneRemainderRat x (d - 1))) ↔
      d ≤ e ∧ e < d + n ∧
        e ∈ greedyMersenneSupport (x : ℝ) := by
  induction n generalizing d e with
  | zero =>
      simp [rationalMersenneGreedyBitsFrom, lowerSupportFromBits]
      omega
  | succ n ih =>
      have hdstep : d - 1 + 1 = d := by omega
      have hbit :
          d ∈ greedyMersenneSupport (x : ℝ) ↔
            mersenneWeightRat d ≤
              greedyMersenneRemainderRat x (d - 1) := by
        calc
          d ∈ greedyMersenneSupport (x : ℝ) ↔
              mersenneWeight d ≤
                greedyMersenneRemainder (x : ℝ) (d - 1) := by
            simpa only [hdstep] using
              (succ_mem_greedyMersenneSupport_iff (x : ℝ) (d - 1))
          _ ↔ mersenneWeightRat d ≤
                greedyMersenneRemainderRat x (d - 1) := by
            simpa only [hdstep] using
              (rational_greedy_take_iff_real x (d - 1)).symm
      by_cases htake :
          mersenneWeightRat d ≤
            greedyMersenneRemainderRat x (d - 1)
      · have hrem :
            greedyMersenneRemainderRat x d =
              greedyMersenneRemainderRat x (d - 1) -
                mersenneWeightRat d := by
          have hrec :=
            greedyMersenneRemainderRat_succ x (d - 1)
          rw [hdstep, if_pos htake] at hrec
          exact hrec
        have ihtail :=
          ih (d := d + 1) (e := e) (by omega)
        simp only [show d + 1 - 1 = d by omega] at ihtail
        rw [rationalMersenneGreedyBitsFrom, if_pos htake,
          lowerSupportFromBits, Finset.mem_insert]
        rw [← hrem, ihtail]
        constructor
        · rintro (rfl | ⟨hde, hed, heA⟩)
          · exact ⟨le_rfl, by omega, hbit.2 htake⟩
          · exact ⟨by omega, by omega, heA⟩
        · rintro ⟨hde, hed, heA⟩
          by_cases heq : e = d
          · exact Or.inl heq
          · exact Or.inr ⟨by omega, by omega, heA⟩
      · have hrem :
            greedyMersenneRemainderRat x d =
              greedyMersenneRemainderRat x (d - 1) := by
          have hrec :=
            greedyMersenneRemainderRat_succ x (d - 1)
          rw [hdstep, if_neg htake] at hrec
          exact hrec
        have ihtail :=
          ih (d := d + 1) (e := e) (by omega)
        simp only [show d + 1 - 1 = d by omega] at ihtail
        rw [rationalMersenneGreedyBitsFrom, if_neg htake,
          lowerSupportFromBits, ← hrem, ihtail]
        constructor
        · rintro ⟨hde, hed, heA⟩
          exact ⟨by omega, by omega, heA⟩
        · rintro ⟨hde, hed, heA⟩
          have hne : e ≠ d := by
            intro heq
            subst e
            exact htake (hbit.1 heA)
          exact ⟨by omega, by omega, heA⟩

/-- The rational prefix is exactly the bounded part of the real greedy
support.  This packages the cast agreement of every individual decision into
the finite-support formulation used by the quotient recurrence. -/
theorem mem_greedyMersennePrefixRat_iff_real_support
    {x : ℚ} {n d : ℕ} :
    d ∈ greedyMersennePrefixRat x n ↔
      1 ≤ d ∧ d ≤ n ∧ d ∈ greedyMersenneSupport (x : ℝ) := by
  classical
  constructor
  · intro hd
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hklt, htake⟩ := Finset.mem_filter.mp hk
    have hkR : k + 1 ∈ greedyMersenneSupport (x : ℝ) := by
      apply (succ_mem_greedyMersenneSupport_iff (x : ℝ) k).2
      exact (rational_greedy_take_iff_real x k).1 htake
    exact ⟨by omega, by
      have := Finset.mem_range.mp hklt
      omega, hkR⟩
  · rintro ⟨hd1, hdn, hreal⟩
    refine Finset.mem_image.mpr ⟨d - 1, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    apply (rational_greedy_take_iff_real x (d - 1)).2
    apply (succ_mem_greedyMersenneSupport_iff (x : ℝ) (d - 1)).1
    simpa only [Nat.sub_add_cancel hd1] using hreal

/-- For the target `1/21`, the rational word may start at rank two because
rank one is forced to be absent.  Decoding through rank `R` is therefore
exactly the rational prefix. -/
theorem lowerSupportFromBits_rationalTwentyOne_eq_greedyMersennePrefixRat
    (R : ℕ) :
    lowerSupportFromBits 2
        (rationalMersenneGreedyBitsFrom 2 (R - 1) (1 / 21 : ℚ)) =
      greedyMersennePrefixRat (1 / 21 : ℚ) R := by
  classical
  ext d
  rw [mem_greedyMersennePrefixRat_iff_real_support]
  have hresidual :
      greedyMersenneRemainderRat (1 / 21 : ℚ) (2 - 1) =
        (1 / 21 : ℚ) := by
    norm_num [greedyMersenneRemainderRat, mersenneWeightRat]
  have hdecode :=
    mem_lowerSupportFromBits_rationalMersenneGreedyBitsFrom_iff
      (x := (1 / 21 : ℚ)) (d := 2) (n := R - 1) (e := d) (by omega)
  rw [hresidual] at hdecode
  rw [hdecode]
  constructor
  · rintro ⟨hd2, hdR, hmem⟩
    exact ⟨by omega, by omega, hmem⟩
  · rintro ⟨hd1, hdR, hmem⟩
    have hd2 : 2 ≤ d := by
      by_contra hdnot
      have hdEq : d = 1 := by omega
      subst d
      have htake :=
        (succ_mem_greedyMersenneSupport_iff (1 / 21 : ℝ) 0).1
          (by simpa using hmem)
      norm_num [greedyMersenneRemainder, mersenneWeight] at htake
    exact ⟨hd2, by omega, hmem⟩

/-- Positivity of the Mersenne weights makes finite prefix value monotone
under support inclusion. -/
theorem localMersennePrefixValue_mono_of_subset
    {A B : Finset ℕ} (hAB : A ⊆ B)
    (hB : ∀ d ∈ B, 1 ≤ d) :
    localMersennePrefixValue A ≤ localMersennePrefixValue B := by
  unfold localMersennePrefixValue
  apply Finset.sum_le_sum_of_subset_of_nonneg hAB
  intro d hd _hdA
  exact (mersenneWeightRat_pos (hB d hd)).le

/-- **No first divergence.**  Start quotient greedy at the exact quotient
defect left by an already agreed prefix `P`.  If its completed support is
still below `1/21`, then every remaining quotient decision agrees with the
exact rational greedy decision from the corresponding rational residual. -/
theorem localQuotientGreedyBits_eq_rationalGreedyBitsFrom_of_safe
    {P : Finset ℕ} {M R d : ℕ}
    (hd2 : 2 ≤ d)
    (hP : ∀ e ∈ P, 2 ≤ e ∧ e < d)
    (hPadm :
      localPrefixQuotient P M ≤ twentyOneQuotientTarget M)
    (hsafe :
      localMersennePrefixValue
          (P ∪
            lowerSupportFromBits d
              (integerGreedyBits
                (localMersenneWeightsFrom M R d)
                (twentyOneQuotientDefect P M))) ≤
        (1 / 21 : ℚ)) :
    integerGreedyBits
        (localMersenneWeightsFrom M R d)
        (twentyOneQuotientDefect P M) =
      rationalMersenneGreedyBitsFrom d (R + 1 - d)
        ((1 / 21 : ℚ) - localMersennePrefixValue P) := by
  classical
  induction hmeasure : R + 1 - d using Nat.strong_induction_on
      generalizing d P with
  | h n ih =>
      by_cases hdR : d ≤ R
      · have hnpos : 0 < n := by omega
        have hnstep : n = (R + 1 - (d + 1)) + 1 := by omega
        have hweights :
            localMersenneWeightsFrom M R d =
              localMersenneQuotient M d ::
                localMersenneWeightsFrom M R (d + 1) :=
          localMersenneWeightsFrom_eq_cons hdR
        have hdnot : d ∉ P := by
          intro hdP
          exact (Nat.lt_irrefl d) (hP d hdP).2
        by_cases htakeQ :
            localMersenneQuotient M d ≤ twentyOneQuotientDefect P M
        · have hbits :
              integerGreedyBits
                  (localMersenneWeightsFrom M R d)
                  (twentyOneQuotientDefect P M) =
                true ::
                  integerGreedyBits
                    (localMersenneWeightsFrom M R (d + 1))
                    (twentyOneQuotientDefect P M -
                      localMersenneQuotient M d) := by
            rw [hweights]
            simp [integerGreedyBits, htakeQ]
          have hsafe' :
              localMersennePrefixValue
                  (P ∪ insert d
                    (lowerSupportFromBits (d + 1)
                      (integerGreedyBits
                        (localMersenneWeightsFrom M R (d + 1))
                        (twentyOneQuotientDefect P M -
                          localMersenneQuotient M d)))) ≤
                (1 / 21 : ℚ) := by
            simpa [hbits, lowerSupportFromBits] using hsafe
          have hsubset :
              insert d P ⊆
                P ∪ insert d
                  (lowerSupportFromBits (d + 1)
                    (integerGreedyBits
                      (localMersenneWeightsFrom M R (d + 1))
                      (twentyOneQuotientDefect P M -
                        localMersenneQuotient M d))) := by
            intro e he
            simp only [Finset.mem_insert, Finset.mem_union] at he ⊢
            rcases he with rfl | he
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl he
          have hallRanks :
              ∀ e ∈
                  P ∪ insert d
                    (lowerSupportFromBits (d + 1)
                      (integerGreedyBits
                        (localMersenneWeightsFrom M R (d + 1))
                        (twentyOneQuotientDefect P M -
                          localMersenneQuotient M d))),
                1 ≤ e := by
            intro e he
            simp only [Finset.mem_union, Finset.mem_insert] at he
            rcases he with heP | rfl | heTail
            · have he2 := (hP e heP).1
              omega
            · omega
            · have hebound := (lowerSupportFromBits_mem_bounds heTail).1
              omega
          have hinsertSafe :
              localMersennePrefixValue (insert d P) ≤
                (1 / 21 : ℚ) :=
            (localMersennePrefixValue_mono_of_subset hsubset hallRanks).trans
              hsafe'
          have hinsertValue :
              localMersennePrefixValue (insert d P) =
                localMersennePrefixValue P + mersenneWeightRat d := by
            unfold localMersennePrefixValue
            rw [Finset.sum_insert hdnot]
            ring
          have htakeRat :
              mersenneWeightRat d ≤
                (1 / 21 : ℚ) - localMersennePrefixValue P := by
            rw [hinsertValue] at hinsertSafe
            linarith
          have hquotInsert :
              localPrefixQuotient (insert d P) M =
                localPrefixQuotient P M +
                  localMersenneQuotient M d := by
            unfold localPrefixQuotient
            rw [Finset.sum_insert hdnot]
            omega
          have hPadmInsert :
              localPrefixQuotient (insert d P) M ≤
                twentyOneQuotientTarget M := by
            rw [hquotInsert]
            unfold twentyOneQuotientDefect at htakeQ
            omega
          have hdefectInsert :
              twentyOneQuotientDefect (insert d P) M =
                twentyOneQuotientDefect P M -
                  localMersenneQuotient M d := by
            unfold twentyOneQuotientDefect
            rw [hquotInsert]
            omega
          have hPInsert :
              ∀ e ∈ insert d P, 2 ≤ e ∧ e < d + 1 := by
            intro e he
            simp only [Finset.mem_insert] at he
            rcases he with rfl | he
            · exact ⟨hd2, by omega⟩
            · exact ⟨(hP e he).1, (hP e he).2.trans_le (Nat.le_succ d)⟩
          have hsafeTail :
              localMersennePrefixValue
                  (insert d P ∪
                    lowerSupportFromBits (d + 1)
                      (integerGreedyBits
                        (localMersenneWeightsFrom M R (d + 1))
                        (twentyOneQuotientDefect (insert d P) M))) ≤
                (1 / 21 : ℚ) := by
            rw [hdefectInsert]
            simpa [Finset.insert_union] using hsafe'
          have hrec :=
            ih (R + 1 - (d + 1)) (by omega)
              (d := d + 1) (P := insert d P)
              (by omega) hPInsert hPadmInsert hsafeTail (by omega)
          have hresidual :
              (1 / 21 : ℚ) -
                  localMersennePrefixValue (insert d P) =
                ((1 / 21 : ℚ) - localMersennePrefixValue P) -
                  mersenneWeightRat d := by
            rw [hinsertValue]
            ring
          rw [hdefectInsert, hresidual] at hrec
          rw [hbits, hnstep, rationalMersenneGreedyBitsFrom,
            if_pos htakeRat, hrec]
        · have hskipRat :
              ¬ mersenneWeightRat d ≤
                (1 / 21 : ℚ) - localMersennePrefixValue P := by
            intro htakeRat
            have htake :
                localMersennePrefixValue P + mersenneWeightRat d ≤
                  (1 / 21 : ℚ) := by
              linarith
            exact htakeQ
              (localMersenneQuotient_le_twentyOneRemainder_of_rational_take
                (fun e he => (hP e he).1) hd2 hdnot htake)
          have hbits :
              integerGreedyBits
                  (localMersenneWeightsFrom M R d)
                  (twentyOneQuotientDefect P M) =
                false ::
                  integerGreedyBits
                    (localMersenneWeightsFrom M R (d + 1))
                    (twentyOneQuotientDefect P M) := by
            rw [hweights]
            simp [integerGreedyBits, htakeQ]
          have hsafeTail :
              localMersennePrefixValue
                  (P ∪
                    lowerSupportFromBits (d + 1)
                      (integerGreedyBits
                        (localMersenneWeightsFrom M R (d + 1))
                        (twentyOneQuotientDefect P M))) ≤
                (1 / 21 : ℚ) := by
            simpa [hbits, lowerSupportFromBits] using hsafe
          have hP' :
              ∀ e ∈ P, 2 ≤ e ∧ e < d + 1 := by
            intro e he
            exact ⟨(hP e he).1, (hP e he).2.trans_le (Nat.le_succ d)⟩
          have hrec :=
            ih (R + 1 - (d + 1)) (by omega)
              (d := d + 1) (P := P)
              (by omega) hP' hPadm hsafeTail (by omega)
          rw [hbits, hnstep, rationalMersenneGreedyBitsFrom,
            if_neg hskipRat, hrec]
      · have hnil := localMersenneWeightsFrom_eq_nil (M := M) (by omega : R < d)
        have hnzero : n = 0 := by omega
        rw [hnil, hnzero]
        rfl

/-- A rationally safe complete quotient row is literally the exact rational
greedy Boolean word through the same horizon.  Thus an under-target full row
is not a second approximation scheme: it is the genuine `1/21` orbit. -/
theorem twentyOneEvenFullQuotientGreedyBits_eq_rational_of_safe
    {R : ℕ}
    (hsafe :
      localMersennePrefixValue
          (twentyOneEvenFullQuotientGreedySupport R) ≤
        (1 / 21 : ℚ)) :
    integerGreedyBits
        (localMersenneWeights (2 * R) (2 * R))
        (twentyOneQuotientTarget (2 * R)) =
      rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ) := by
  have hcompare :=
    localQuotientGreedyBits_eq_rationalGreedyBitsFrom_of_safe
      (P := ∅) (M := 2 * R) (R := 2 * R) (d := 2)
      (by omega)
      (by simp)
      (by simp [localPrefixQuotient])
      (by
        simpa [twentyOneEvenFullQuotientGreedySupport,
          twentyOneQuotientDefect, localPrefixQuotient] using hsafe)
  simpa [localMersenneWeights, twentyOneQuotientDefect,
    localPrefixQuotient, localMersennePrefixValue, finiteErdosSum] using
      hcompare

/-- Any finite disagreement with the exact rational greedy word certifies
strict overshoot of the completed quotient row.  The witness is purely
Boolean: no rational summation or defect estimate is needed to recognize
the crossing. -/
theorem one_div_twenty_one_lt_fullGreedyPrefix_of_bits_ne_rational
    {R : ℕ}
    (hne :
      integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R)) ≠
        rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)) :
    (1 / 21 : ℚ) <
      localMersennePrefixValue
        (twentyOneEvenFullQuotientGreedySupport R) := by
  by_contra hnot
  exact hne
    (twentyOneEvenFullQuotientGreedyBits_eq_rational_of_safe
      (le_of_not_gt hnot))

/-- A quotient-admissible row which reaches or overshoots the rational
target has defect no larger than its support.  This reverses the familiar
`card ≤ defect` safety certificate and is the key one-sided compactness
estimate: overshooting rows already have only linear quotient error. -/
theorem twentyOneQuotientDefect_le_card_of_target_le_prefix
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hadm : localPrefixQuotient D M ≤ twentyOneQuotientTarget M)
    (hover : (1 / 21 : ℚ) ≤ localMersennePrefixValue D) :
    twentyOneQuotientDefect D M ≤ D.card := by
  have hid :=
    scaled_localMersennePrefixValue_sub_one_div_twenty_one hD hadm
  have hnonneg :
      0 ≤ (2 : ℚ) ^ M *
        (localMersennePrefixValue D - (1 / 21 : ℚ)) := by
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hover)
  rw [hid] at hnonneg
  have hFcard := localFractionMass_le_card (D := D) (M := M) hD
  have hrho0 := twentyOneTargetFraction_nonneg M
  have hcast :
      (twentyOneQuotientDefect D M : ℚ) ≤ (D.card : ℚ) := by
    linarith
  exact_mod_cast hcast

/-- The exact sign classifier for any denominator-`21` quotient row.
Overshoot is neither a real-analytic mystery nor a quotient-remainder
estimate: it is precisely the comparison between source fractional mass
and quotient defect plus the periodic target fraction. -/
theorem one_div_twenty_one_le_localMersennePrefixValue_iff_fraction_balance
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hadm : localPrefixQuotient D M ≤ twentyOneQuotientTarget M) :
    (1 / 21 : ℚ) ≤ localMersennePrefixValue D ↔
      (twentyOneQuotientDefect D M : ℚ) +
          twentyOneTargetFraction M ≤
        localFractionMass D M := by
  have hid :=
    scaled_localMersennePrefixValue_sub_one_div_twenty_one hD hadm
  have hpowPos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
  constructor
  · intro hover
    have hnonneg :
        0 ≤ (2 : ℚ) ^ M *
          (localMersennePrefixValue D - (1 / 21 : ℚ)) :=
      mul_nonneg hpowPos.le (sub_nonneg.mpr hover)
    rw [hid] at hnonneg
    linarith
  · intro hbalance
    have hnonneg :
        0 ≤ (2 : ℚ) ^ M *
          (localMersennePrefixValue D - (1 / 21 : ℚ)) := by
      rw [hid]
      linarith
    exact sub_nonneg.mp
      (nonneg_of_mul_nonneg_right hnonneg hpowPos)

/-- The multiplicative order of `2` modulo `21` divides six. -/
theorem two_pow_six_mul_mod_twentyOne (k : ℕ) :
    2 ^ (6 * k) % 21 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show 6 * (k + 1) = 6 * k + 6 by omega, pow_add, Nat.mul_mod, ih]
      norm_num

/-- On the cofinal even rows with rank divisible by three, the periodic
target fraction is the literal rational `1/21`. -/
theorem twentyOneTargetFraction_two_mul_eq_one_div_twenty_one_of_three_dvd
    {R : ℕ} (hR : 3 ∣ R) :
    twentyOneTargetFraction (2 * R) = (1 / 21 : ℚ) := by
  obtain ⟨k, rfl⟩ := hR
  unfold twentyOneTargetFraction
  rw [show 2 * (3 * k) = 6 * k by omega, two_pow_six_mul_mod_twentyOne]
  norm_num

/-- Cardinality dominated by the exact quotient defect is a sufficient
finite certificate that the underlying rational prefix is still below the
prescribed point. -/
theorem localMersennePrefixValue_le_one_div_twenty_one_of_card_le_state
    {D : Finset ℕ} {M s : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow :
      localPrefixQuotient D M + s = twentyOneQuotientTarget M)
    (hcard : D.card ≤ s) :
    localMersennePrefixValue D ≤ (1 / 21 : ℚ) := by
  have hadm :
      localPrefixQuotient D M ≤ twentyOneQuotientTarget M := by omega
  have hid :=
    scaled_localMersennePrefixValue_sub_one_div_twenty_one hD hadm
  have hdefect : twentyOneQuotientDefect D M = s := by
    unfold twentyOneQuotientDefect
    omega
  rw [hdefect] at hid
  have hFcard := localFractionMass_le_card (D := D) (M := M) hD
  have hcardQ : (D.card : ℚ) ≤ s := by exact_mod_cast hcard
  have hrho0 := twentyOneTargetFraction_nonneg M
  have hnonpos :
      (2 : ℚ) ^ M *
          (localMersennePrefixValue D - (1 / 21 : ℚ)) ≤ 0 := by
    rw [hid]
    linarith
  have hpowPos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hnonpos hpowPos)

/-- Rational safety therefore supplies the exact pulse inequality required
by the sharp lower-state transition. -/
theorem localPrefixTwoStepPulse_le_carry_of_prefix_le
    {D : Finset ℕ} {R s : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow :
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R))
    (hsafe : localMersennePrefixValue D ≤ (1 / 21 : ℚ)) :
    localPrefixTwoStepPulse D (2 * R) ≤
      4 * s + twentyOneTargetTwoStepPulse (2 * R) := by
  have hadm :=
    localPrefixQuotient_le_twentyOneTarget_of_prefix_le
      (D := D) (M := 2 * (R + 1)) hD hsafe
  rw [show 2 * (R + 1) = 2 * R + 2 by omega,
    twentyOneQuotientTarget_add_two,
    localPrefixQuotient_add_two hD] at hadm
  omega

/-! ## The exact upper-row hole

At depth `2(R+1)`, the upper word beginning at rank `R+1` consists of the
boundary coin `2^(R+1)+1`, followed by the complete binary word
`2^R,…,1`.  Consequently it represents every value below `2^(R+2)` except
the single missing value `2^(R+1)`. -/

theorem integerGreedyRemainder_upperBoundaryWindow_eq_zero
    {R C : ℕ} (hR : 1 ≤ R)
    (hC : C < 2 ^ (R + 2)) (hne : C ≠ 2 ^ (R + 1)) :
    integerGreedyRemainder
        (localMersenneWeightsFrom
          (2 * (R + 1)) (2 * (R + 1)) (R + 1)) C = 0 := by
  rw [localMersenneWeightsFrom_eq_cons (by omega),
    integerGreedyRemainder_cons,
    localMersenneQuotient_two_mul_self (by omega)]
  by_cases htake : 2 ^ (R + 1) + 1 ≤ C
  · rw [if_pos htake]
    apply integerGreedyRemainder_upperMersenneWindow_eq_zero
        (M := 2 * (R + 1)) (d := R + 2)
    · omega
    · omega
    · omega
    · simpa only [show
          2 * (R + 1) + 1 - (R + 2) = R + 1 by omega] using
        (show C - (2 ^ (R + 1) + 1) < 2 ^ (R + 1) by
          rw [show 2 ^ (R + 2) = 2 * 2 ^ (R + 1) by
            rw [pow_succ]; ring] at hC
          omega)
  · rw [if_neg htake]
    apply integerGreedyRemainder_upperMersenneWindow_eq_zero
        (M := 2 * (R + 1)) (d := R + 2)
    · omega
    · omega
    · omega
    · simpa only [show
          2 * (R + 1) + 1 - (R + 2) = R + 1 by omega] using
        (show C < 2 ^ (R + 1) by omega)

/-- Closed-window form: the unique missing value is not a genuine
obstruction for compactness, since it leaves terminal defect exactly one. -/
theorem integerGreedyRemainder_upperBoundaryWindow_le_one
    {R C : ℕ} (hR : 1 ≤ R)
    (hC : C ≤ 2 ^ (R + 2)) :
    integerGreedyRemainder
        (localMersenneWeightsFrom
          (2 * (R + 1)) (2 * (R + 1)) (R + 1)) C ≤ 1 := by
  rw [localMersenneWeightsFrom_eq_cons (by omega),
    integerGreedyRemainder_cons,
    localMersenneQuotient_two_mul_self (by omega)]
  by_cases htake : 2 ^ (R + 1) + 1 ≤ C
  · rw [if_pos htake]
    apply integerGreedyRemainder_upperMersenneWindow_le_one
        (M := 2 * (R + 1)) (d := R + 2)
    · omega
    · omega
    · omega
    · simpa only [show
          2 * (R + 1) + 1 - (R + 2) = R + 1 by omega] using
        (show C - (2 ^ (R + 1) + 1) ≤ 2 ^ (R + 1) by
          rw [show 2 ^ (R + 2) = 2 * 2 ^ (R + 1) by
            rw [pow_succ]; ring] at hC
          omega)
  · rw [if_neg htake]
    apply integerGreedyRemainder_upperMersenneWindow_le_one
        (M := 2 * (R + 1)) (d := R + 2)
    · omega
    · omega
    · omega
    · simpa only [show
          2 * (R + 1) + 1 - (R + 2) = R + 1 by omega] using
        (show C ≤ 2 ^ (R + 1) by omega)

/-- The deterministic support decoding of the upper boundary word. -/
def upperBoundaryCompletionSupport (R C : ℕ) : Finset ℕ :=
  lowerSupportFromBits (R + 1)
    (integerGreedyBits
      (localMersenneWeightsFrom
        (2 * (R + 1)) (2 * (R + 1)) (R + 1)) C)

theorem upperBoundaryCompletionSupport_mem_bounds
    {R C d : ℕ} (hd : d ∈ upperBoundaryCompletionSupport R C) :
    R + 1 ≤ d ∧ d ≤ 2 * (R + 1) := by
  unfold upperBoundaryCompletionSupport at hd
  have hbounds := lowerSupportFromBits_mem_bounds hd
  have hlen := integerGreedyBits_length
    (localMersenneWeightsFrom
      (2 * (R + 1)) (2 * (R + 1)) (R + 1)) C
  rw [localMersenneWeightsFrom_length] at hlen
  omega

/-- Away from the unique hole, decoding the upper word gives an exact
quotient representation of its carry. -/
theorem localPrefixQuotient_upperBoundaryCompletionSupport
    {R C : ℕ} (hR : 1 ≤ R)
    (hC : C < 2 ^ (R + 2)) (hne : C ≠ 2 ^ (R + 1)) :
    localPrefixQuotient (upperBoundaryCompletionSupport R C)
        (2 * (R + 1)) = C := by
  let weights :=
    localMersenneWeightsFrom
      (2 * (R + 1)) (2 * (R + 1)) (R + 1)
  let bits := integerGreedyBits weights C
  have hlen : bits.length = 2 * (R + 1) + 1 - (R + 1) := by
    rw [integerGreedyBits_length]
    exact localMersenneWeightsFrom_length _ _ _
  have hdecode :=
    localPrefixQuotient_lowerSupportFromBits
      (M := 2 * (R + 1)) (R := 2 * (R + 1))
      (d := R + 1) (bits := bits) hlen
  have hadm := integerGreedyBits_admissible weights C
  have hzero :=
    integerGreedyRemainder_upperBoundaryWindow_eq_zero hR hC hne
  change localPrefixQuotient (lowerSupportFromBits (R + 1) bits)
      (2 * (R + 1)) = C
  rw [hdecode]
  have hadm' :
      weightedBoolSum
          (localMersenneWeightsFrom
            (2 * (R + 1)) (2 * (R + 1)) (R + 1)) bits ≤ C := by
    simpa [weights, bits] using hadm
  have hzero' :
      C - weightedBoolSum
          (localMersenneWeightsFrom
            (2 * (R + 1)) (2 * (R + 1)) (R + 1)) bits = 0 := by
    simpa [weights, bits, integerGreedyRemainder] using hzero
  omega

/-- The decoded upper support always misses a carry in the closed window by
at most one. -/
theorem localPrefixQuotient_upperBoundaryCompletionSupport_add_defect
    {R C : ℕ} (hR : 1 ≤ R)
    (hC : C ≤ 2 ^ (R + 2)) :
    ∃ e : ℕ,
      e ≤ 1 ∧
      localPrefixQuotient (upperBoundaryCompletionSupport R C)
          (2 * (R + 1)) + e = C := by
  let weights :=
    localMersenneWeightsFrom
      (2 * (R + 1)) (2 * (R + 1)) (R + 1)
  let bits := integerGreedyBits weights C
  let e := integerGreedyRemainder weights C
  have hlen : bits.length = 2 * (R + 1) + 1 - (R + 1) := by
    rw [integerGreedyBits_length]
    exact localMersenneWeightsFrom_length _ _ _
  have hdecode :=
    localPrefixQuotient_lowerSupportFromBits
      (M := 2 * (R + 1)) (R := 2 * (R + 1))
      (d := R + 1) (bits := bits) hlen
  have hadm := integerGreedyBits_admissible weights C
  have he :=
    integerGreedyRemainder_upperBoundaryWindow_le_one hR hC
  refine ⟨e, by simpa [e, weights] using he, ?_⟩
  change localPrefixQuotient (lowerSupportFromBits (R + 1) bits)
      (2 * (R + 1)) + e = C
  rw [hdecode]
  have hadm' :
      weightedBoolSum
          (localMersenneWeightsFrom
            (2 * (R + 1)) (2 * (R + 1)) (R + 1)) bits ≤ C := by
    simpa [weights, bits] using hadm
  have hpartition :
      weightedBoolSum
          (localMersenneWeightsFrom
            (2 * (R + 1)) (2 * (R + 1)) (R + 1)) bits + e = C := by
    dsimp [e]
    unfold integerGreedyRemainder
    simpa [weights, bits] using
      (Nat.add_sub_of_le hadm)
  exact hpartition

/-- Any lower prefix whose remaining carry lies in the upper representable
window extends to an exact denominator-`21` quotient row. -/
theorem exists_twentyOneExactRow_of_upperBoundaryCarry
    {D : Finset ℕ} {R : ℕ} (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ R)
    (hadm :
      localPrefixQuotient D (2 * (R + 1)) ≤
        twentyOneQuotientTarget (2 * (R + 1)))
    (hcarry :
      twentyOneQuotientTarget (2 * (R + 1)) -
          localPrefixQuotient D (2 * (R + 1)) <
        2 ^ (R + 2))
    (hnotHole :
      twentyOneQuotientTarget (2 * (R + 1)) -
          localPrefixQuotient D (2 * (R + 1)) ≠
        2 ^ (R + 1)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * (R + 1)) ∧
      localPrefixQuotient E (2 * (R + 1)) =
        twentyOneQuotientTarget (2 * (R + 1)) := by
  let C :=
    twentyOneQuotientTarget (2 * (R + 1)) -
      localPrefixQuotient D (2 * (R + 1))
  let U := upperBoundaryCompletionSupport R C
  have hU :
      localPrefixQuotient U (2 * (R + 1)) = C := by
    exact localPrefixQuotient_upperBoundaryCompletionSupport
      hR (by simpa [C] using hcarry) (by simpa [C] using hnotHole)
  have hdisj : Disjoint D U := by
    rw [Finset.disjoint_left]
    intro d hdD hdU
    have hdlo := (upperBoundaryCompletionSupport_mem_bounds hdU).1
    have hdhi := (hD d hdD).2
    omega
  refine ⟨D ∪ U, Finset.subset_union_left, ?_, ?_⟩
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hdD | hdU
    · exact ⟨(hD d hdD).1, (hD d hdD).2.trans (by omega)⟩
    · have hbounds := upperBoundaryCompletionSupport_mem_bounds hdU
      exact ⟨by omega, hbounds.2⟩
  · have hunion :
        localPrefixQuotient (D ∪ U) (2 * (R + 1)) =
          localPrefixQuotient D (2 * (R + 1)) +
            localPrefixQuotient U (2 * (R + 1)) := by
      unfold localPrefixQuotient
      rw [Finset.sum_union hdisj]
    rw [hunion, hU]
    dsimp [C]
    omega

/-- Closed-window continuation.  Even when the carry hits the single
upper-word hole, the extended row exists with quotient defect at most one. -/
theorem exists_twentyOneRow_defect_le_one_of_upperBoundaryCarry
    {D : Finset ℕ} {R : ℕ} (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ R)
    (hadm :
      localPrefixQuotient D (2 * (R + 1)) ≤
        twentyOneQuotientTarget (2 * (R + 1)))
    (hcarry :
      twentyOneQuotientTarget (2 * (R + 1)) -
          localPrefixQuotient D (2 * (R + 1)) ≤
        2 ^ (R + 2)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * (R + 1)) ∧
      localPrefixQuotient E (2 * (R + 1)) ≤
        twentyOneQuotientTarget (2 * (R + 1)) ∧
      twentyOneQuotientDefect E (2 * (R + 1)) ≤ 1 := by
  let C :=
    twentyOneQuotientTarget (2 * (R + 1)) -
      localPrefixQuotient D (2 * (R + 1))
  let U := upperBoundaryCompletionSupport R C
  obtain ⟨e, he, hUraw⟩ :=
    localPrefixQuotient_upperBoundaryCompletionSupport_add_defect
      (R := R) (C := C) hR (by simpa [C] using hcarry)
  have hU :
      localPrefixQuotient U (2 * (R + 1)) + e = C := by
    simpa [U] using hUraw
  have hdisj : Disjoint D U := by
    rw [Finset.disjoint_left]
    intro d hdD hdU
    have hdlo := (upperBoundaryCompletionSupport_mem_bounds hdU).1
    have hdhi := (hD d hdD).2
    omega
  refine ⟨D ∪ U, Finset.subset_union_left, ?_, ?_, ?_⟩
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hdD | hdU
    · exact ⟨(hD d hdD).1, (hD d hdD).2.trans (by omega)⟩
    · have hbounds := upperBoundaryCompletionSupport_mem_bounds hdU
      exact ⟨by omega, hbounds.2⟩
  · have hunion :
        localPrefixQuotient (D ∪ U) (2 * (R + 1)) =
          localPrefixQuotient D (2 * (R + 1)) +
            localPrefixQuotient U (2 * (R + 1)) := by
      unfold localPrefixQuotient
      rw [Finset.sum_union hdisj]
    rw [hunion]
    have hpartition :
        localPrefixQuotient D (2 * (R + 1)) + C =
          twentyOneQuotientTarget (2 * (R + 1)) := by
      dsimp [C]
      omega
    omega
  · unfold twentyOneQuotientDefect
    have hunion :
        localPrefixQuotient (D ∪ U) (2 * (R + 1)) =
          localPrefixQuotient D (2 * (R + 1)) +
            localPrefixQuotient U (2 * (R + 1)) := by
      unfold localPrefixQuotient
      rw [Finset.sum_union hdisj]
    rw [hunion]
    have hpartition :
        localPrefixQuotient D (2 * (R + 1)) + C =
          twentyOneQuotientTarget (2 * (R + 1)) := by
      dsimp [C]
      omega
    omega

/-! ## Scalar row-extension recurrence

Suppose a row at depth `2R` decomposes into a frozen lower prefix with
quotient `L` and a binary upper value `b`, so `L+b=T_{2R}`.  At the next
even depth the residual carry is exactly

`4b + targetPulse - prefixPulse`.

The upper bound is automatic from `b<2^R`; only nonnegativity and avoidance
of the single upper-word hole remain. -/

theorem twentyOneUpperExtensionCarry_eq
    {D : Finset ℕ} {R b : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow :
      localPrefixQuotient D (2 * R) + b =
        twentyOneQuotientTarget (2 * R))
    (hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * b + twentyOneTargetTwoStepPulse (2 * R)) :
    twentyOneQuotientTarget (2 * (R + 1)) -
        localPrefixQuotient D (2 * (R + 1)) =
      4 * b + twentyOneTargetTwoStepPulse (2 * R) -
        localPrefixTwoStepPulse D (2 * R) := by
  rw [show 2 * (R + 1) = 2 * R + 2 by omega,
    twentyOneQuotientTarget_add_two,
    localPrefixQuotient_add_two hD]
  omega

theorem twentyOneUpperExtensionCarry_lt
    {D : Finset ℕ} {R b : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow :
      localPrefixQuotient D (2 * R) + b =
        twentyOneQuotientTarget (2 * R))
    (hb : b < 2 ^ R)
    (hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * b + twentyOneTargetTwoStepPulse (2 * R)) :
    twentyOneQuotientTarget (2 * (R + 1)) -
        localPrefixQuotient D (2 * (R + 1)) <
      2 ^ (R + 2) := by
  rw [twentyOneUpperExtensionCarry_eq hD hrow hpulse]
  have htarget := twentyOneTargetTwoStepPulse_le_three (2 * R)
  have hpow : 2 ^ (R + 2) = 4 * 2 ^ R := by
    rw [pow_add]
    norm_num
    omega
  omega

/-- Error-tolerant form of the scalar recurrence.  The old upper binary value
and its terminal defect enter only through their sum. -/
theorem twentyOneUpperExtensionCarry_eq_of_defect
    {D : Finset ℕ} {R b e : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow :
      localPrefixQuotient D (2 * R) + b + e =
        twentyOneQuotientTarget (2 * R))
    (hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * (b + e) + twentyOneTargetTwoStepPulse (2 * R)) :
    twentyOneQuotientTarget (2 * (R + 1)) -
        localPrefixQuotient D (2 * (R + 1)) =
      4 * (b + e) + twentyOneTargetTwoStepPulse (2 * R) -
        localPrefixTwoStepPulse D (2 * R) := by
  rw [show 2 * (R + 1) = 2 * R + 2 by omega,
    twentyOneQuotientTarget_add_two,
    localPrefixQuotient_add_two hD]
  omega

/-- **Closed two-step row extension.**  A lower state with old accounting
`L+b+e=T` extends to a full next row of defect at most one whenever its
explicit two-bit divisor pulse leaves the scaled carry inside the complete
upper capacity.  There is no exceptional-state premise. -/
theorem exists_twentyOneRow_defect_le_one_of_twoStepState
    {D : Finset ℕ} {R b e : ℕ} (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ R)
    (hrow :
      localPrefixQuotient D (2 * R) + b + e =
        twentyOneQuotientTarget (2 * R))
    (hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * (b + e) + twentyOneTargetTwoStepPulse (2 * R))
    (hcapacity :
      4 * (b + e) + twentyOneTargetTwoStepPulse (2 * R) -
          localPrefixTwoStepPulse D (2 * R) ≤
        2 ^ (R + 2)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * (R + 1)) ∧
      localPrefixQuotient E (2 * (R + 1)) ≤
        twentyOneQuotientTarget (2 * (R + 1)) ∧
      twentyOneQuotientDefect E (2 * (R + 1)) ≤ 1 := by
  have hDtwo : ∀ d ∈ D, 2 ≤ d := fun d hd ↦ (hD d hd).1
  have hcarryEq :=
    twentyOneUpperExtensionCarry_eq_of_defect hDtwo hrow hpulse
  have hadm :
      localPrefixQuotient D (2 * (R + 1)) ≤
        twentyOneQuotientTarget (2 * (R + 1)) := by
    rw [show 2 * (R + 1) = 2 * R + 2 by omega,
      twentyOneQuotientTarget_add_two,
      localPrefixQuotient_add_two hDtwo]
    omega
  apply exists_twentyOneRow_defect_le_one_of_upperBoundaryCarry
    hR hD hadm
  rw [hcarryEq]
  exact hcapacity

/-- **Closed scalar extension.**  The raw pulse inequalities needed by
`exists_twentyOneRow_defect_le_one_of_twoStepState` follow from three
state-space facts:

* the scalar state dominates the number of frozen ranks;
* it lies in the closed binary window; and
* if it saturates the window, the endpoint divisor pulse absorbs the target
  pulse.

Thus the only remaining boundary case is the explicitly named saturated
state; every strict interior state continues automatically. -/
theorem exists_twentyOneRow_defect_le_one_of_closedState
    {D : Finset ℕ} {R b e : ℕ} (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ R)
    (hrow :
      localPrefixQuotient D (2 * R) + b + e =
        twentyOneQuotientTarget (2 * R))
    (hcard : D.card ≤ b + e)
    (hclosed : b + e ≤ 2 ^ R)
    (hsaturated :
      b + e = 2 ^ R →
        twentyOneTargetTwoStepPulse (2 * R) ≤
          localPrefixTwoStepPulse D (2 * R)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * (R + 1)) ∧
      localPrefixQuotient E (2 * (R + 1)) ≤
        twentyOneQuotientTarget (2 * (R + 1)) ∧
      twentyOneQuotientDefect E (2 * (R + 1)) ≤ 1 := by
  have hpulseBound :=
    localPrefixTwoStepPulse_le_three_mul_card D (2 * R)
  have hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * (b + e) + twentyOneTargetTwoStepPulse (2 * R) := by
    omega
  have htarget := twentyOneTargetTwoStepPulse_le_three (2 * R)
  have hpow : 2 ^ (R + 2) = 4 * 2 ^ R := by
    rw [pow_add]
    norm_num
    omega
  have hcapacity :
      4 * (b + e) + twentyOneTargetTwoStepPulse (2 * R) -
          localPrefixTwoStepPulse D (2 * R) ≤
        2 ^ (R + 2) := by
    by_cases hsat : b + e = 2 ^ R
    · have hreset := hsaturated hsat
      rw [hpow, hsat]
      omega
    · have hinterior : b + e < 2 ^ R := by omega
      rw [hpow]
      omega
  exact exists_twentyOneRow_defect_le_one_of_twoStepState
    hR hD hrow hpulse hcapacity

/-! ## The actual lower-state transition

The preceding theorem completes a whole finite row.  To iterate the lower
half itself, only the new boundary rank `R+1` may be added.  The following
definitions expose that single Boolean decision and its remaining scalar
state. -/

/-- Add the new lower boundary rank exactly when its quotient coin fits. -/
def twentyOneBoundaryLowerSupport
    (D : Finset ℕ) (R C : ℕ) : Finset ℕ :=
  if 2 ^ (R + 1) + 1 ≤ C then insert (R + 1) D else D

/-- The scalar carry left after the new lower boundary decision. -/
def twentyOneBoundaryScalarState (R C : ℕ) : ℕ :=
  if 2 ^ (R + 1) + 1 ≤ C then C - (2 ^ (R + 1) + 1) else C

/-- Signed distance from a scalar lower state to the closed binary capacity.
The signed coordinate avoids truncated-subtraction artifacts while deriving
the exact perturbed-doubling law. -/
def twentyOneSignedClosedMargin (R s : ℕ) : ℤ :=
  (2 : ℤ) ^ R - (s : ℤ)

/-- On a taken boundary coin, the closed-capacity margin doubles in scale
and follows the exact affine law `m ↦ 4m + pulse + 1 - targetPulse`. -/
theorem twentyOneSignedClosedMargin_boundary_of_take
    {D : Finset ℕ} {R s : ℕ}
    (htake :
      2 ^ (R + 1) + 1 ≤
        4 * s + twentyOneTargetTwoStepPulse (2 * R) -
          localPrefixTwoStepPulse D (2 * R)) :
    twentyOneSignedClosedMargin (R + 1)
        (twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R))) =
      4 * twentyOneSignedClosedMargin R s +
        (localPrefixTwoStepPulse D (2 * R) : ℤ) + 1 -
          (twentyOneTargetTwoStepPulse (2 * R) : ℤ) := by
  have hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * s + twentyOneTargetTwoStepPulse (2 * R) := by
    by_contra hnot
    have hle :
        4 * s + twentyOneTargetTwoStepPulse (2 * R) ≤
          localPrefixTwoStepPulse D (2 * R) :=
      Nat.le_of_not_ge hnot
    have hzero :
        4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R) = 0 :=
      Nat.sub_eq_zero_of_le hle
    rw [hzero] at htake
    have hpositive : 0 < 2 ^ (R + 1) + 1 := by positivity
    omega
  unfold twentyOneSignedClosedMargin twentyOneBoundaryScalarState
  rw [if_pos htake, Nat.cast_sub htake, Nat.cast_sub hpulse, pow_succ]
  push_cast
  ring

/-- On a skipped boundary coin, the same affine update crosses the binary
cut once.  Saturation is therefore exactly the zero state of this signed
perturbed-doubling recurrence. -/
theorem twentyOneSignedClosedMargin_boundary_of_skip
    {D : Finset ℕ} {R s : ℕ}
    (hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * s + twentyOneTargetTwoStepPulse (2 * R))
    (hskip :
      ¬ 2 ^ (R + 1) + 1 ≤
        4 * s + twentyOneTargetTwoStepPulse (2 * R) -
          localPrefixTwoStepPulse D (2 * R)) :
    twentyOneSignedClosedMargin (R + 1)
        (twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R))) =
      4 * twentyOneSignedClosedMargin R s -
          (2 : ℤ) ^ (R + 1) +
        (localPrefixTwoStepPulse D (2 * R) : ℤ) -
          (twentyOneTargetTwoStepPulse (2 * R) : ℤ) := by
  unfold twentyOneSignedClosedMargin twentyOneBoundaryScalarState
  rw [if_neg hskip, Nat.cast_sub hpulse, pow_succ]
  push_cast
  ring

theorem twentyOneBoundaryLowerSupport_subset
    (D : Finset ℕ) (R C : ℕ) :
    D ⊆ twentyOneBoundaryLowerSupport D R C := by
  unfold twentyOneBoundaryLowerSupport
  split_ifs
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.rfl

theorem twentyOneBoundaryLowerSupport_mem_bounds
    {D : Finset ℕ} {R C d : ℕ}
    (hR : 1 ≤ R)
    (hD : ∀ e ∈ D, 2 ≤ e ∧ e ≤ R)
    (hd : d ∈ twentyOneBoundaryLowerSupport D R C) :
    2 ≤ d ∧ d ≤ R + 1 := by
  by_cases htake : 2 ^ (R + 1) + 1 ≤ C
  · have hd' : d = R + 1 ∨ d ∈ D := by
      simpa [twentyOneBoundaryLowerSupport, htake] using hd
    rcases hd' with rfl | hdD
    · omega
    · exact ⟨(hD d hdD).1, (hD d hdD).2.trans (Nat.le_succ R)⟩
  · have hdD : d ∈ D := by
      simpa [twentyOneBoundaryLowerSupport, htake] using hd
    exact ⟨(hD d hdD).1, (hD d hdD).2.trans (Nat.le_succ R)⟩

/-- The new boundary bit and its scalar remainder exactly partition any
admissible carry. -/
theorem localPrefixQuotient_boundaryLowerSupport_add_scalar
    {D : Finset ℕ} {R C : ℕ} (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ R) :
    localPrefixQuotient (twentyOneBoundaryLowerSupport D R C)
          (2 * (R + 1)) +
        twentyOneBoundaryScalarState R C =
      localPrefixQuotient D (2 * (R + 1)) + C := by
  have hnot : R + 1 ∉ D := by
    intro hmem
    have := (hD (R + 1) hmem).2
    omega
  unfold twentyOneBoundaryLowerSupport twentyOneBoundaryScalarState
  by_cases htake : 2 ^ (R + 1) + 1 ≤ C
  · rw [if_pos htake, if_pos htake]
    have hins :
        localPrefixQuotient (insert (R + 1) D) (2 * (R + 1)) =
          localMersenneQuotient (2 * (R + 1)) (R + 1) +
            localPrefixQuotient D (2 * (R + 1)) := by
      unfold localPrefixQuotient
      rw [Finset.sum_insert hnot]
    rw [hins, localMersenneQuotient_two_mul_self (by omega)]
    omega
  · rw [if_neg htake, if_neg htake]

/-- Closed binary capacity is preserved by the one new lower-boundary bit.
The extra unit is genuine: the boundary coin is `2^(R+1)+1`, so an incoming
carry one unit above the complete binary capacity still lands exactly on the
closed boundary after that coin is taken. -/
theorem twentyOneBoundaryScalarState_le
    {R C : ℕ}
    (hC : C ≤ 2 ^ (R + 2) + 1) :
    twentyOneBoundaryScalarState R C ≤ 2 ^ (R + 1) := by
  have hpow : 2 ^ (R + 2) = 2 * 2 ^ (R + 1) := by
    rw [pow_succ]
    omega
  unfold twentyOneBoundaryScalarState
  by_cases htake : 2 ^ (R + 1) + 1 ≤ C
  · rw [if_pos htake]
    rw [hpow] at hC
    omega
  · rw [if_neg htake]
    omega

/-- Exact classification of the two ways the boundary decision can land on
the closed binary endpoint.  The ordinary value `2^(R+1)` comes from
skipping the new coin, while the exceptional value `2^(R+2)+1` comes from
taking the coin and retaining exactly one full binary block. -/
theorem twentyOneBoundaryScalarState_eq_boundary_iff
    {R C : ℕ}
    (hC : C ≤ 2 ^ (R + 2) + 1) :
    twentyOneBoundaryScalarState R C = 2 ^ (R + 1) ↔
      C = 2 ^ (R + 1) ∨ C = 2 ^ (R + 2) + 1 := by
  have hpow : 2 ^ (R + 2) = 2 * 2 ^ (R + 1) := by
    rw [pow_succ]
    omega
  unfold twentyOneBoundaryScalarState
  by_cases htake : 2 ^ (R + 1) + 1 ≤ C
  · rw [if_pos htake]
    constructor
    · intro h
      right
      omega
    · rintro (h | h)
      · omega
      · rw [h, hpow]
        omega
  · rw [if_neg htake]
    constructor
    · exact fun h ↦ Or.inl h
    · rintro (h | h)
      · exact h
      · rw [hpow] at hC h
        omega

/-- If the old lower state is strict, the exceptional take-branch endpoint
is too large.  Hence a newly saturated state can be born only from the
single exact mid-carry value `2^(R+1)` in the skip branch. -/
theorem twentyOneBoundaryScalarState_eq_boundary_iff_of_strict
    {D : Finset ℕ} {R s : ℕ}
    (hstrict : s < 2 ^ R) :
    twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R)) =
        2 ^ (R + 1) ↔
      4 * s + twentyOneTargetTwoStepPulse (2 * R) -
          localPrefixTwoStepPulse D (2 * R) =
        2 ^ (R + 1) := by
  have htarget := twentyOneTargetTwoStepPulse_le_three (2 * R)
  have hpow : 2 ^ (R + 2) = 4 * 2 ^ R := by
    rw [pow_add]
    norm_num
    omega
  rw [twentyOneBoundaryScalarState_eq_boundary_iff]
  · omega
  · rw [hpow]
    omega

/-- The exact safety test for propagating the cardinality-dominates-pulse
invariant through the new boundary decision.  In the take branch this is the
only genuinely new gap: the carry must clear the boundary coin by at least
the enlarged support cardinality. -/
theorem card_boundaryLowerSupport_le_scalar
    {D : Finset ℕ} {R C : ℕ}
    (hD : ∀ d ∈ D, d ≤ R)
    (hsafe :
      if 2 ^ (R + 1) + 1 ≤ C then
        D.card + 1 ≤ C - (2 ^ (R + 1) + 1)
      else D.card ≤ C) :
    (twentyOneBoundaryLowerSupport D R C).card ≤
      twentyOneBoundaryScalarState R C := by
  have hnot : R + 1 ∉ D := by
    intro hmem
    have := hD (R + 1) hmem
    omega
  unfold twentyOneBoundaryLowerSupport twentyOneBoundaryScalarState
  by_cases htake : 2 ^ (R + 1) + 1 ≤ C
  · rw [if_pos htake] at hsafe
    rw [if_pos htake, if_pos htake, Finset.card_insert_of_notMem hnot]
    omega
  · rw [if_neg htake] at hsafe
    rw [if_neg htake, if_neg htake]
    exact hsafe

/-- **Lossless recursive step.**  A closed lower state propagates to rank
`R+1` provided only:

* the saturated state absorbs all but at most one unit of the target pulse,
  with the boundary coin's extra unit absorbing the last one; and
* a taken new boundary coin clears the explicit cardinality-sized gap.

All quotient accounting, support bounds, pulse nonnegativity, and binary
capacity are discharged here. -/
theorem exists_twentyOneClosedLowerState_succ
    {D : Finset ℕ} {R s : ℕ} (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ R)
    (hrow :
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R))
    (hcard : D.card ≤ s)
    (hclosed : s ≤ 2 ^ R)
    (hsaturated :
      s = 2 ^ R →
        twentyOneTargetTwoStepPulse (2 * R) ≤
          localPrefixTwoStepPulse D (2 * R) + 1)
    (hsafe :
      let C :=
        4 * s + twentyOneTargetTwoStepPulse (2 * R) -
          localPrefixTwoStepPulse D (2 * R)
      if 2 ^ (R + 1) + 1 ≤ C then
        D.card + 1 ≤ C - (2 ^ (R + 1) + 1)
      else D.card ≤ C) :
    ∃ E : Finset ℕ, ∃ t : ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ R + 1) ∧
      localPrefixQuotient E (2 * (R + 1)) + t =
        twentyOneQuotientTarget (2 * (R + 1)) ∧
      E.card ≤ t ∧
      t ≤ 2 ^ (R + 1) := by
  let C :=
    4 * s + twentyOneTargetTwoStepPulse (2 * R) -
      localPrefixTwoStepPulse D (2 * R)
  let E := twentyOneBoundaryLowerSupport D R C
  let t := twentyOneBoundaryScalarState R C
  have hpulseBound :=
    localPrefixTwoStepPulse_le_three_mul_card D (2 * R)
  have hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * s + twentyOneTargetTwoStepPulse (2 * R) := by
    omega
  have hcarryEq :=
    twentyOneUpperExtensionCarry_eq (D := D) (R := R) (b := s)
      (fun d hd ↦ (hD d hd).1) hrow hpulse
  have hadm :
      localPrefixQuotient D (2 * (R + 1)) ≤
        twentyOneQuotientTarget (2 * (R + 1)) := by
    rw [show 2 * (R + 1) = 2 * R + 2 by omega,
      twentyOneQuotientTarget_add_two,
      localPrefixQuotient_add_two (fun d hd ↦ (hD d hd).1)]
    omega
  have haccount :
      localPrefixQuotient D (2 * (R + 1)) + C =
        twentyOneQuotientTarget (2 * (R + 1)) := by
    dsimp [C]
    omega
  have htarget := twentyOneTargetTwoStepPulse_le_three (2 * R)
  have hpow : 2 ^ (R + 2) = 4 * 2 ^ R := by
    rw [pow_add]
    norm_num
    omega
  have hcapacity : C ≤ 2 ^ (R + 2) + 1 := by
    dsimp [C]
    by_cases hsat : s = 2 ^ R
    · have hreset := hsaturated hsat
      rw [hpow, hsat]
      omega
    · have hinterior : s < 2 ^ R := by omega
      rw [hpow]
      omega
  refine ⟨E, t, twentyOneBoundaryLowerSupport_subset D R C, ?_, ?_, ?_, ?_⟩
  · intro d hd
    exact twentyOneBoundaryLowerSupport_mem_bounds hR hD hd
  · dsimp [E, t]
    rw [localPrefixQuotient_boundaryLowerSupport_add_scalar hR hD]
    exact haccount
  · dsimp [E, t]
    apply card_boundaryLowerSupport_le_scalar
    · exact fun d hd ↦ (hD d hd).2
    · simpa [C] using hsafe
  · dsimp [t]
    exact twentyOneBoundaryScalarState_le hcapacity

/-- **Sharp closed-state transition.**  Cardinality domination is only one
coarse way to prove pulse nonnegativity.  Once the exact pulse inequality is
given directly, the lower state propagates with no take-gap hypothesis at
all.  The sole capacity exception is the explicitly visible saturated
socket, sharpened by the boundary coin's extra unit. -/
theorem exists_twentyOneClosedLowerState_succ_of_pulse
    {D : Finset ℕ} {R s : ℕ} (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ R)
    (hrow :
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R))
    (hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * s + twentyOneTargetTwoStepPulse (2 * R))
    (hclosed : s ≤ 2 ^ R)
    (hsaturated :
      s = 2 ^ R →
        twentyOneTargetTwoStepPulse (2 * R) ≤
          localPrefixTwoStepPulse D (2 * R) + 1) :
    ∃ E : Finset ℕ, ∃ t : ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ R + 1) ∧
      localPrefixQuotient E (2 * (R + 1)) + t =
        twentyOneQuotientTarget (2 * (R + 1)) ∧
      t ≤ 2 ^ (R + 1) := by
  let C :=
    4 * s + twentyOneTargetTwoStepPulse (2 * R) -
      localPrefixTwoStepPulse D (2 * R)
  let E := twentyOneBoundaryLowerSupport D R C
  let t := twentyOneBoundaryScalarState R C
  have hcarryEq :=
    twentyOneUpperExtensionCarry_eq (D := D) (R := R) (b := s)
      (fun d hd ↦ (hD d hd).1) hrow hpulse
  have hadm :
      localPrefixQuotient D (2 * (R + 1)) ≤
        twentyOneQuotientTarget (2 * (R + 1)) := by
    rw [show 2 * (R + 1) = 2 * R + 2 by omega,
      twentyOneQuotientTarget_add_two,
      localPrefixQuotient_add_two (fun d hd ↦ (hD d hd).1)]
    omega
  have haccount :
      localPrefixQuotient D (2 * (R + 1)) + C =
        twentyOneQuotientTarget (2 * (R + 1)) := by
    dsimp [C]
    omega
  have htarget := twentyOneTargetTwoStepPulse_le_three (2 * R)
  have hpow : 2 ^ (R + 2) = 4 * 2 ^ R := by
    rw [pow_add]
    norm_num
    omega
  have hcapacity : C ≤ 2 ^ (R + 2) + 1 := by
    dsimp [C]
    by_cases hsat : s = 2 ^ R
    · have hreset := hsaturated hsat
      rw [hpow, hsat]
      omega
    · have hinterior : s < 2 ^ R := by omega
      rw [hpow]
      omega
  refine ⟨E, t, twentyOneBoundaryLowerSupport_subset D R C, ?_, ?_, ?_⟩
  · intro d hd
    exact twentyOneBoundaryLowerSupport_mem_bounds hR hD hd
  · dsimp [E, t]
    rw [localPrefixQuotient_boundaryLowerSupport_add_scalar hR hD]
    exact haccount
  · dsimp [t]
    exact twentyOneBoundaryScalarState_le hcapacity

/-- The scalar carry always dominates the old support cardinality under the
closed-state invariant.  Hence the no-take branch of `hsafe` above is
automatic. -/
theorem card_le_twentyOneUpperExtensionCarry
    {D : Finset ℕ} {R s : ℕ}
    (hcard : D.card ≤ s) :
    D.card ≤
      4 * s + twentyOneTargetTwoStepPulse (2 * R) -
        localPrefixTwoStepPulse D (2 * R) := by
  have hpulse :=
    localPrefixTwoStepPulse_le_three_mul_card D (2 * R)
  omega

/-- Equivalent recurrence with the automatic no-take branch
removed.  The sole interior obstruction is now the explicit *take gap*. -/
theorem exists_twentyOneClosedLowerState_succ_of_takeGap
    {D : Finset ℕ} {R s : ℕ} (hR : 1 ≤ R)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ R)
    (hrow :
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R))
    (hcard : D.card ≤ s)
    (hclosed : s ≤ 2 ^ R)
    (hsaturated :
      s = 2 ^ R →
        twentyOneTargetTwoStepPulse (2 * R) ≤
          localPrefixTwoStepPulse D (2 * R) + 1)
    (htakeGap :
      let C :=
        4 * s + twentyOneTargetTwoStepPulse (2 * R) -
          localPrefixTwoStepPulse D (2 * R)
      2 ^ (R + 1) + 1 ≤ C →
        D.card + 1 ≤ C - (2 ^ (R + 1) + 1)) :
    ∃ E : Finset ℕ, ∃ t : ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ R + 1) ∧
      localPrefixQuotient E (2 * (R + 1)) + t =
        twentyOneQuotientTarget (2 * (R + 1)) ∧
      E.card ≤ t ∧
      t ≤ 2 ^ (R + 1) := by
  apply exists_twentyOneClosedLowerState_succ
    hR hD hrow hcard hclosed hsaturated
  let C :=
    4 * s + twentyOneTargetTwoStepPulse (2 * R) -
      localPrefixTwoStepPulse D (2 * R)
  have hcardC : D.card ≤ C := by
    exact card_le_twentyOneUpperExtensionCarry hcard
  by_cases htake : 2 ^ (R + 1) + 1 ≤ C
  · rw [if_pos htake]
    exact htakeGap htake
  · rw [if_neg htake]
    exact hcardC

/-- At even depths the denominator-`21` target pulse has only the two values
`0` and `3`. -/
theorem twentyOneTargetTwoStepPulse_even_cases (R : ℕ) :
    twentyOneTargetTwoStepPulse (2 * R) = 0 ∨
      twentyOneTargetTwoStepPulse (2 * R) = 3 := by
  have hres :
      2 ^ (2 * R) % 21 = 1 ∨
        2 ^ (2 * R) % 21 = 4 ∨
          2 ^ (2 * R) % 21 = 16 := by
    induction R with
    | zero => simp
    | succ R ih =>
        have hstep :
            2 ^ (2 * (R + 1)) % 21 =
              (4 * (2 ^ (2 * R) % 21)) % 21 := by
          rw [show 2 * (R + 1) = 2 * R + 2 by omega, pow_add,
            Nat.mul_mod]
          norm_num
          rw [Nat.mul_comm]
        rw [hstep]
        rcases ih with h | h | h <;> simp [h]
  unfold twentyOneTargetTwoStepPulse
  rcases hres with h | h | h <;> simp [h]

/-- The even denominator-`21` pulse is three-periodic in the half-depth. -/
theorem twentyOneTargetTwoStepPulse_even_add_three (R : ℕ) :
    twentyOneTargetTwoStepPulse (2 * (R + 3)) =
      twentyOneTargetTwoStepPulse (2 * R) := by
  unfold twentyOneTargetTwoStepPulse
  rw [show 2 * (R + 3) = 2 * R + 6 by omega, pow_add, Nat.mul_mod]
  norm_num

/-- Exact location of the nonzero even pulse.  It occurs only in the last
half-depth residue class modulo three. -/
theorem twentyOneTargetTwoStepPulse_even_eq_three_iff (R : ℕ) :
    twentyOneTargetTwoStepPulse (2 * R) = 3 ↔ R % 3 = 2 := by
  induction R using Nat.strong_induction_on with
  | h R ih =>
      by_cases hsmall : R < 3
      · interval_cases R <;> norm_num [twentyOneTargetTwoStepPulse]
      · obtain ⟨K, rfl⟩ : ∃ K : ℕ, R = K + 3 := by
          exact ⟨R - 3, by omega⟩
        rw [twentyOneTargetTwoStepPulse_even_add_three]
        have hK := ih K (by omega)
        simpa [Nat.add_mod] using hK

/-- Therefore the saturated transition is automatic unless the target pulse is
the unique nonzero value, in which case exactly three endpoint-divisor bits
are sufficient. -/
theorem twentyOneSaturatedPulse_iff
    (D : Finset ℕ) (R : ℕ) :
    twentyOneTargetTwoStepPulse (2 * R) ≤
        localPrefixTwoStepPulse D (2 * R) ↔
      twentyOneTargetTwoStepPulse (2 * R) = 0 ∨
        3 ≤ localPrefixTwoStepPulse D (2 * R) := by
  rcases twentyOneTargetTwoStepPulse_even_cases R with h | h
  · simp [h]
  · simp [h]

/-- Exact saturated case for the lower-state transition.  The boundary
coin contributes one unit beyond its binary skeleton, so at the unique
nonzero target pulse only two endpoint-divisor units, rather than three,
are required to preserve the closed state. -/
theorem twentyOneClosedTransitionSaturatedPulse_iff
    (D : Finset ℕ) (R : ℕ) :
    twentyOneTargetTwoStepPulse (2 * R) ≤
        localPrefixTwoStepPulse D (2 * R) + 1 ↔
      twentyOneTargetTwoStepPulse (2 * R) = 0 ∨
        2 ≤ localPrefixTwoStepPulse D (2 * R) := by
  rcases twentyOneTargetTwoStepPulse_even_cases R with h | h
  · simp [h]
  · simp [h]

/-- **Exact entrance classifier for the supercapacity regime.**  If the old
lower state is exactly saturated, the next boundary state can cross above
its binary capacity only in the unique nonzero target-pulse residue class,
and then only when the frozen support contributes at most one endpoint
divisor.

Thus the permanent-escape branch cannot enter through a broad interval: its
first possible excess is the constant-width fringe produced by
`targetPulse = 3` and `supportPulse ≤ 1`. -/
theorem twentyOneSaturatedBoundary_crosses_iff_sparsePulse
    {D : Finset ℕ} {R s : ℕ}
    (hsaturated : s = 2 ^ R) :
    2 ^ (R + 1) <
        twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R)) ↔
      twentyOneTargetTwoStepPulse (2 * R) = 3 ∧
        localPrefixTwoStepPulse D (2 * R) ≤ 1 := by
  subst s
  have hpowSucc : 2 ^ (R + 1) = 2 * 2 ^ R := by
    rw [pow_succ]
    omega
  rcases twentyOneTargetTwoStepPulse_even_cases R with hzero | hthree
  · unfold twentyOneBoundaryScalarState
    rw [hzero]
    simp only [add_zero]
    by_cases htake :
        2 ^ (R + 1) + 1 ≤
          4 * 2 ^ R - localPrefixTwoStepPulse D (2 * R)
    · rw [if_pos htake, hpowSucc]
      omega
    · rw [if_neg htake, hpowSucc]
      omega
  · unfold twentyOneBoundaryScalarState
    rw [hthree]
    by_cases htake :
        2 ^ (R + 1) + 1 ≤
          4 * 2 ^ R + 3 - localPrefixTwoStepPulse D (2 * R)
    · rw [if_pos htake, hpowSucc]
      omega
    · rw [if_neg htake, hpowSucc]
      omega

/-- **A saturated escape forces an older support hole.**  Write the unique
crossing residue as `R = 3a+2`.  The second endpoint in the crossing pulse is

`2R+2 = 6(a+1)`.

Both `a+1` and `2(a+1)` divide that endpoint.  Since a crossing has total
two-step support pulse at most one, at least one of those two ancestor ranks
is absent.  This is the one-third-scale obstruction attached to the actual
entrance into supercapacity, rather than to a later saturated transition. -/
theorem twentyOneSaturatedBoundary_crossing_forces_ancestor_hole
    {D : Finset ℕ} {R s : ℕ}
    (hsaturated : s = 2 ^ R)
    (hcross :
      2 ^ (R + 1) <
        twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R))) :
    ∃ a : ℕ,
      R = 3 * a + 2 ∧
        (a + 1 ∉ D ∨ 2 * (a + 1) ∉ D) := by
  classical
  have hdata :=
    (twentyOneSaturatedBoundary_crosses_iff_sparsePulse
      (D := D) hsaturated).1 hcross
  have hRmod : R % 3 = 2 :=
    (twentyOneTargetTwoStepPulse_even_eq_three_iff R).1 hdata.1
  let a := R / 3
  have hRa : R = 3 * a + 2 := by
    have hdecomp := Nat.mod_add_div R 3
    dsimp [a]
    omega
  refine ⟨a, hRa, ?_⟩
  by_contra hnoHole
  have hd₁ : a + 1 ∈ D := by
    by_contra hnot
    exact hnoHole (Or.inl hnot)
  have hd₂ : 2 * (a + 1) ∈ D := by
    by_contra hnot
    exact hnoHole (Or.inr hnot)
  have hdvd₁ : a + 1 ∣ 2 * R + 2 := by
    refine ⟨6, ?_⟩
    rw [hRa]
    ring
  have hdvd₂ : 2 * (a + 1) ∣ 2 * R + 2 := by
    refine ⟨3, ?_⟩
    rw [hRa]
    ring
  let F : Finset ℕ := {a + 1, 2 * (a + 1)}
  have hFcard : F.card = 2 := by
    dsimp [F]
    exact Finset.card_pair (by omega)
  have hFsub :
      F ⊆ D.filter (fun d ↦ d ∣ 2 * R + 2) := by
    intro d hd
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hd₁, hdvd₁⟩
    · exact Finset.mem_filter.mpr ⟨hd₂, hdvd₂⟩
  have hendpoint :
      2 ≤ endpointDivisorContribution D (2 * R + 2) := by
    unfold endpointDivisorContribution
    calc
      2 = F.card := hFcard.symm
      _ ≤ (D.filter (fun d ↦ d ∣ 2 * R + 2)).card :=
        Finset.card_le_card hFsub
  unfold localPrefixTwoStepPulse at hdata
  omega

/-- **Two-pulse normal form of the only bad saturated transition.**  Start
from a strict lower state and suppose the next boundary decision lands
exactly on the closed endpoint.  If that endpoint would fail the following
saturated transition, then:

* the pulse which created the endpoint was zero;
* the incoming carry was the exact skip value `2^(R+1)`;
* the boundary bit was not inserted; and
* the following divisor pulse has size at most one.

Thus a bad saturation is not a one-row equality.  It is a rigid sparse
two-pulse pattern in consecutive endpoint pairs. -/
theorem twentyOneBadSaturatedTransition_forces_sparse_twoPulse
    {D : Finset ℕ} {R s : ℕ}
    (hstrict : s < 2 ^ R)
    (hsaturated :
      twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R)) =
        2 ^ (R + 1))
    (hbad :
      ¬ twentyOneTargetTwoStepPulse (2 * (R + 1)) ≤
        localPrefixTwoStepPulse
            (twentyOneBoundaryLowerSupport D R
              (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse D (2 * R)))
            (2 * (R + 1)) +
          1) :
    twentyOneTargetTwoStepPulse (2 * R) = 0 ∧
      4 * s + twentyOneTargetTwoStepPulse (2 * R) -
          localPrefixTwoStepPulse D (2 * R) =
        2 ^ (R + 1) ∧
      twentyOneBoundaryLowerSupport D R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R)) =
        D ∧
      localPrefixTwoStepPulse D (2 * (R + 1)) ≤ 1 := by
  let C :=
    4 * s + twentyOneTargetTwoStepPulse (2 * R) -
      localPrefixTwoStepPulse D (2 * R)
  let E := twentyOneBoundaryLowerSupport D R C
  have hC : C = 2 ^ (R + 1) := by
    exact
      (twentyOneBoundaryScalarState_eq_boundary_iff_of_strict
        (D := D) (R := R) hstrict).1 (by simpa [C] using hsaturated)
  have hnext : twentyOneTargetTwoStepPulse (2 * (R + 1)) = 3 := by
    rcases twentyOneTargetTwoStepPulse_even_cases (R + 1) with hzero | hthree
    · exfalso
      apply hbad
      simp [hzero]
    · exact hthree
  have hnextPulse : localPrefixTwoStepPulse E (2 * (R + 1)) ≤ 1 := by
    have htarget :=
      twentyOneTargetTwoStepPulse_le_three (2 * (R + 1))
    have hbad' :
        ¬ twentyOneTargetTwoStepPulse (2 * (R + 1)) ≤
          localPrefixTwoStepPulse E (2 * (R + 1)) + 1 := by
      simpa [E, C] using hbad
    omega
  have hnextMod : (R + 1) % 3 = 2 :=
    (twentyOneTargetTwoStepPulse_even_eq_three_iff (R + 1)).1 hnext
  have hRmod : R % 3 = 1 := by
    have hRdecomp := Nat.mod_add_div R 3
    have hnextDecomp := Nat.mod_add_div (R + 1) 3
    have hRlt := Nat.mod_lt R (by omega : 0 < 3)
    omega
  have hcurrent : twentyOneTargetTwoStepPulse (2 * R) = 0 := by
    rcases twentyOneTargetTwoStepPulse_even_cases R with hzero | hthree
    · exact hzero
    · have := (twentyOneTargetTwoStepPulse_even_eq_three_iff R).1 hthree
      omega
  have hskip : ¬ 2 ^ (R + 1) + 1 ≤ C := by
    rw [hC]
    omega
  have hE : E = D := by
    simp [E, twentyOneBoundaryLowerSupport, hskip]
  refine ⟨hcurrent, by simpa [C] using hC, by simpa [E, C] using hE, ?_⟩
  simpa [hE] using hnextPulse

/-- **Margin normal form of a failed saturation.**  A failed saturated transition
can occur only in half-depth residue class `1 mod 3`.  Its incoming divisor
pulse must be a multiple of four and must exactly complement four times the
old capacity margin to `2^(R+1)`, while the following pulse has size at most
one.  This is the arithmetic zero-reachability obstruction exposed by the
signed margin recurrence. -/
theorem twentyOneBadSaturatedTransition_forces_margin_residue
    {D : Finset ℕ} {R s : ℕ} (hR : 1 ≤ R)
    (hstrict : s < 2 ^ R)
    (hsaturated :
      twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R)) =
        2 ^ (R + 1))
    (hbad :
      ¬ twentyOneTargetTwoStepPulse (2 * (R + 1)) ≤
        localPrefixTwoStepPulse
            (twentyOneBoundaryLowerSupport D R
              (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse D (2 * R)))
            (2 * (R + 1)) +
          1) :
    R % 3 = 1 ∧
      4 * (2 ^ R - s) + localPrefixTwoStepPulse D (2 * R) =
        2 ^ (R + 1) ∧
      4 ∣ localPrefixTwoStepPulse D (2 * R) ∧
      localPrefixTwoStepPulse D (2 * (R + 1)) ≤ 1 := by
  have hdata :=
    twentyOneBadSaturatedTransition_forces_sparse_twoPulse
      hstrict hsaturated hbad
  rcases hdata with ⟨htarget, hcarry, hsupport, hnextPulse⟩
  have hnext : twentyOneTargetTwoStepPulse (2 * (R + 1)) = 3 := by
    rcases twentyOneTargetTwoStepPulse_even_cases (R + 1) with hzero | hthree
    · exfalso
      apply hbad
      simp [hzero]
    · exact hthree
  have hnextMod : (R + 1) % 3 = 2 :=
    (twentyOneTargetTwoStepPulse_even_eq_three_iff (R + 1)).1 hnext
  have hRmod : R % 3 = 1 := by
    have hRdecomp := Nat.mod_add_div R 3
    have hnextDecomp := Nat.mod_add_div (R + 1) 3
    have hRlt := Nat.mod_lt R (by omega : 0 < 3)
    omega
  have hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤ 4 * s := by
    rw [htarget] at hcarry
    have hpowPos : 0 < 2 ^ (R + 1) := by positivity
    omega
  have hpow : 2 ^ (R + 1) = 2 * 2 ^ R := by
    rw [pow_succ]
    ring
  have hmargin :
      4 * (2 ^ R - s) + localPrefixTwoStepPulse D (2 * R) =
        2 ^ (R + 1) := by
    rw [htarget] at hcarry
    omega
  have hpowDvd : 4 ∣ 2 ^ (R + 1) := by
    simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using
      (pow_dvd_pow (2 : ℕ) (show 2 ≤ R + 1 by omega))
  rcases hpowDvd with ⟨k, hk⟩
  have hpulseDvd : 4 ∣ localPrefixTwoStepPulse D (2 * R) := by
    refine ⟨k - (2 ^ R - s), ?_⟩
    omega
  refine ⟨hRmod, hmargin, hpulseDvd, ?_⟩
  simpa [hsupport] using hnextPulse

/-- Equivalent state-coordinate form of the same obstruction.  At a bad
saturation the strict predecessor is not merely "near half capacity": it is
exactly half capacity plus one quarter of the incoming divisor pulse.  The
pulse quotient is a natural number because bad saturation already forces
four-divisibility. -/
theorem twentyOneBadSaturatedTransition_forces_half_state
    {D : Finset ℕ} {R s : ℕ} (hR : 1 ≤ R)
    (hstrict : s < 2 ^ R)
    (hsaturated :
      twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R)) =
        2 ^ (R + 1))
    (hbad :
      ¬ twentyOneTargetTwoStepPulse (2 * (R + 1)) ≤
        localPrefixTwoStepPulse
            (twentyOneBoundaryLowerSupport D R
              (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse D (2 * R)))
            (2 * (R + 1)) +
          1) :
    ∃ k : ℕ,
      localPrefixTwoStepPulse D (2 * R) = 4 * k ∧
      s = 2 ^ (R - 1) + k ∧
      localPrefixTwoStepPulse D (2 * (R + 1)) ≤ 1 := by
  obtain ⟨_hRmod, hmargin, hpulseDvd, hnextPulse⟩ :=
    twentyOneBadSaturatedTransition_forces_margin_residue
      hR hstrict hsaturated hbad
  rcases hpulseDvd with ⟨k, hk⟩
  have hpowR : 2 ^ R = 2 * 2 ^ (R - 1) := by
    calc
      2 ^ R = 2 ^ ((R - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (R - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (R - 1) := by ring
  have hpowSucc : 2 ^ (R + 1) = 4 * 2 ^ (R - 1) := by
    calc
      2 ^ (R + 1) = 2 ^ ((R - 1) + 2) := by congr 1 <;> omega
      _ = 2 ^ (R - 1) * 2 ^ 2 := by rw [pow_add]
      _ = 4 * 2 ^ (R - 1) := by norm_num; ring
  refine ⟨k, hk, ?_, hnextPulse⟩
  rw [hk, hpowR, hpowSucc] at hmargin
  omega

/-- **A bad saturation has a strictly older support hole.**  Write the
forced residue class as `R = 3a+1`.  The second endpoint in the following
pulse is then

`2R+4 = 6(a+1)`.

Both `a+1` and `2(a+1)` are distinct divisors of that endpoint.  Since a
bad socket has total following pulse at most one, they cannot both belong
to the old support.  Thus the zero-reachability obstruction descends to an
explicit missing digit at one-third or two-thirds scale. -/
theorem twentyOneBadSaturatedTransition_forces_ancestor_hole
    {D : Finset ℕ} {R s : ℕ} (hR : 4 ≤ R)
    (hstrict : s < 2 ^ R)
    (hsaturated :
      twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse D (2 * R)) =
        2 ^ (R + 1))
    (hbad :
      ¬ twentyOneTargetTwoStepPulse (2 * (R + 1)) ≤
        localPrefixTwoStepPulse
            (twentyOneBoundaryLowerSupport D R
              (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse D (2 * R)))
            (2 * (R + 1)) +
          1) :
    ∃ a : ℕ,
      R = 3 * a + 1 ∧
        (a + 1 ∉ D ∨ 2 * (a + 1) ∉ D) := by
  classical
  obtain ⟨hRmod, _hmargin, _hpulseDvd, hnextPulse⟩ :=
    twentyOneBadSaturatedTransition_forces_margin_residue
      (by omega : 1 ≤ R) hstrict hsaturated hbad
  let a := R / 3
  have hRa : R = 3 * a + 1 := by
    have hdecomp := Nat.mod_add_div R 3
    dsimp [a]
    omega
  refine ⟨a, hRa, ?_⟩
  by_contra hnoHole
  have hd₁ : a + 1 ∈ D := by
    by_contra hnot
    exact hnoHole (Or.inl hnot)
  have hd₂ : 2 * (a + 1) ∈ D := by
    by_contra hnot
    exact hnoHole (Or.inr hnot)
  have hdvd₁ : a + 1 ∣ 2 * (R + 1) + 2 := by
    refine ⟨6, ?_⟩
    rw [hRa]
    ring
  have hdvd₂ : 2 * (a + 1) ∣ 2 * (R + 1) + 2 := by
    refine ⟨3, ?_⟩
    rw [hRa]
    ring
  let F : Finset ℕ := {a + 1, 2 * (a + 1)}
  have hFcard : F.card = 2 := by
    dsimp [F]
    exact Finset.card_pair (by omega)
  have hFsub :
      F ⊆ D.filter (fun d ↦ d ∣ 2 * (R + 1) + 2) := by
    intro d hd
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hd₁, hdvd₁⟩
    · exact Finset.mem_filter.mpr ⟨hd₂, hdvd₂⟩
  have hendpoint :
      2 ≤ endpointDivisorContribution D (2 * (R + 1) + 2) := by
    unfold endpointDivisorContribution
    calc
      2 = F.card := hFcard.symm
      _ ≤ (D.filter (fun d ↦ d ∣ 2 * (R + 1) + 2)).card :=
        Finset.card_le_card hFsub
  unfold localPrefixTwoStepPulse at hnextPulse
  omega

/-! ## Closed-state compactness endpoint -/

/-- One closed lower state at every even depth.  Equality at the binary
boundary is allowed; the compactness error still decays like `2⁻ᴿ`. -/
def TwentyOneClosedLowerStateSupply : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    ∃ D : Finset ℕ, ∃ s : ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ R) ∧
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R) ∧
      s ≤ 2 ^ R

/-- **Closed-state endpoint.**  The sharp recurrence may land exactly on
the binary boundary.  That does not obstruct the limiting construction:
closed-window states alone already put `1/21` in the Mersenne achievement
set. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    (hsupply : TwentyOneClosedLowerStateSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  classical
  choose D s hD hrow hclosed using fun R =>
    hsupply (R + 2) (by omega)
  let y : ℕ → ℝ := fun R =>
    ((localMersennePrefixValue (D R) : ℚ) : ℝ)
  have hshift : Tendsto (fun R : ℕ => R + 2) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat 2
  have hadm : ∀ R : ℕ,
      localPrefixQuotient (D R) (2 * (R + 2)) ≤
        twentyOneQuotientTarget (2 * (R + 2)) := by
    intro R
    have := hrow R
    omega
  have hdefect : ∀ R : ℕ,
      twentyOneQuotientDefect (D R) (2 * (R + 2)) = s R := by
    intro R
    unfold twentyOneQuotientDefect
    have := hrow R
    omega
  have hdist :
      Tendsto (fun R : ℕ => dist (y R) (1 / 21 : ℝ))
        atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => dist_nonneg)
      (Filter.Eventually.of_forall fun R => ?_)
      (tendsto_twentyOne_evenQuotientWindow_error.comp hshift)
    rw [Real.dist_eq]
    calc
      |y R - (1 / 21 : ℝ)| ≤
          ((twentyOneQuotientDefect (D R) (2 * (R + 2)) +
              (D R).card + 1 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * (R + 2)) := by
        exact abs_localMersennePrefixValue_sub_one_div_twenty_one_le
          (fun d hd => (hD R d hd).1) (hadm R)
      _ ≤
          (((2 ^ (R + 2) + (2 * (R + 2) + 1) : ℕ) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * (R + 2)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hcardBound : (D R).card ≤ R + 1 := by
          have hsubset : D R ⊆ Finset.Icc 2 (R + 2) := by
            intro d hd
            simp only [Finset.mem_Icc]
            exact hD R d hd
          calc
            (D R).card ≤ (Finset.Icc 2 (R + 2)).card :=
              Finset.card_le_card hsubset
            _ = R + 1 := by simp
        have hs := hclosed R
        rw [hdefect R]
        exact_mod_cast (by omega :
          s R + (D R).card + 1 ≤
            2 ^ (R + 2) + (2 * (R + 2) + 1))
  have hy : Tendsto y atTop (nhds (1 / 21 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hyMem : ∀ R : ℕ, y R ∈ mersenneAchievementSet := by
    intro R
    let A : Set ℕ := ↑(D R)
    have hA0 : 0 ∉ A := by
      intro hzero
      have := (hD R 0 (by simpa [A] using hzero)).1
      omega
    refine ⟨A, hA0, ?_⟩
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [y, localMersennePrefixValue_eq_finiteErdosSum]
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

/-- The complete row is the half-cutoff computation followed by its pure
binary suffix. -/
theorem twentyOneEvenFullQuotientGreedyRemainder_eq_upperCompletion
    {R : ℕ} (hR : 1 ≤ R) :
    twentyOneEvenFullQuotientGreedyRemainder R =
      integerGreedyRemainder
        (localMersenneWeightsFrom (2 * R) (2 * R) (R + 1))
        (twentyOneEvenQuotientGreedyRemainder R) := by
  unfold twentyOneEvenFullQuotientGreedyRemainder
  unfold twentyOneEvenQuotientGreedyRemainder
  unfold localMersenneWeights
  rw [localMersenneWeightsFrom_split
      (M := 2 * R) (S := 2 * R) (R := R) (d := 2)
      (by omega) (by omega),
    integerGreedyRemainder_append]

/-- The coarse strict-core bound already puts the half-cutoff remainder
inside the *closed* binary window.  No avoidance of `core = 2^R` is needed. -/
theorem twentyOneEvenQuotientGreedyRemainder_le_of_coreBound
    {R : ℕ} (hR : 2 ≤ R)
    (hcore :
      twentyOneEvenQuotientCoreRemainder R < 2 * 2 ^ R + 1) :
    twentyOneEvenQuotientGreedyRemainder R ≤ 2 ^ R := by
  rw [twentyOneEvenQuotientGreedyRemainder_eq_coreStep hR]
  by_cases htake :
      2 ^ R + 1 ≤ twentyOneEvenQuotientCoreRemainder R
  · rw [if_pos htake]
    omega
  · rw [if_neg htake]
    omega

/-- Exact closed-window classifier.  Allowing the endpoint replaces the old
two-part strict obstruction by one weak upper bound on the preterminal
core. -/
theorem twentyOneEvenQuotientGreedyRemainder_le_iff_core_le
    {R : ℕ} (hR : 2 ≤ R) :
    twentyOneEvenQuotientGreedyRemainder R ≤ 2 ^ R ↔
      twentyOneEvenQuotientCoreRemainder R ≤ 2 * 2 ^ R + 1 := by
  rw [twentyOneEvenQuotientGreedyRemainder_eq_coreStep hR]
  by_cases htake :
      2 ^ R + 1 ≤ twentyOneEvenQuotientCoreRemainder R
  · rw [if_pos htake]
    omega
  · rw [if_neg htake]
    omega

/-- **Exceptional-state absorption.**  Once the full upper word is retained,
the coarse core bound leaves quotient defect at most one.  In particular the
old exceptional state `core = 2^R` is harmless. -/
theorem twentyOneEvenFullQuotientGreedyRemainder_le_one_of_coreBound
    {R : ℕ} (hR : 2 ≤ R)
    (hcore :
      twentyOneEvenQuotientCoreRemainder R < 2 * 2 ^ R + 1) :
    twentyOneEvenFullQuotientGreedyRemainder R ≤ 1 := by
  rw [twentyOneEvenFullQuotientGreedyRemainder_eq_upperCompletion (by omega)]
  apply integerGreedyRemainder_upperMersenneWindow_le_one
      (M := 2 * R) (d := R + 1)
  · omega
  · omega
  · omega
  · simpa only [show 2 * R + 1 - (R + 1) = R by omega] using
      twentyOneEvenQuotientGreedyRemainder_le_of_coreBound hR hcore

/-- The genuinely coarse terminal condition.  It retains the twice-last-coin
ceiling but deliberately imposes no avoidance of the six constant-width
fringe states. -/
def TwentyOneEvenQuotientPreterminalCoarseBound : Prop :=
  ∀ R : ℕ, 4 ≤ R →
    twentyOneEvenQuotientPreterminalRemainder R <
      2 * 2 ^ (R + 1) + 8

/-- The canonical greedy statement, with no numerical fringe chosen by
hand: after ranks `2,…,R-2`, the remainder lies below the next quotient
coin.  Exact computation supports the stronger closed binary-window bound,
but this next-coin form is all compactness needs. -/
def TwentyOneEvenQuotientPreterminalNextCoinBound : Prop :=
  ∀ R : ℕ, 4 ≤ R →
    twentyOneEvenQuotientPreterminalRemainder R <
      localMersenneQuotient (2 * R) (R - 2)

/-- The next-coin hypothesis leaves the half-row remainder below twice the
binary window.  The constant quotient excess is absorbed directly into this
bound. -/
theorem twentyOneEvenQuotientGreedyRemainder_le_double_of_preterminalNextCoin
    {R : ℕ} (hR : 4 ≤ R)
    (hnext :
      twentyOneEvenQuotientPreterminalRemainder R <
        localMersenneQuotient (2 * R) (R - 2)) :
    twentyOneEvenQuotientGreedyRemainder R ≤ 2 ^ (R + 1) := by
  have hcoin :=
    localMersenneQuotient_two_mul_pred_pred_le hR
  have hB : 2 ^ (R + 2) = 2 * 2 ^ (R + 1) := by
    rw [pow_succ]
    omega
  have hpre :
      twentyOneEvenQuotientPreterminalRemainder R <
        2 * 2 ^ (R + 1) + 21 :=
    hnext.trans_le (by simpa [hB] using hcoin)
  have hcore :
      twentyOneEvenQuotientCoreRemainder R < 2 ^ (R + 1) + 17 := by
    rw [twentyOneEvenQuotientCoreRemainder_eq_preterminalStep hR]
    by_cases htake :
        2 ^ (R + 1) + 4 ≤
          twentyOneEvenQuotientPreterminalRemainder R
    · rw [if_pos htake]
      omega
    · rw [if_neg htake]
      omega
  rw [twentyOneEvenQuotientGreedyRemainder_eq_coreStep (by omega)]
  have hpow : 2 ^ (R + 1) = 2 * 2 ^ R := by
    rw [pow_succ]
    omega
  have hsixteen : 16 ≤ 2 ^ R := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (show 4 ≤ R by omega))
  by_cases htake :
      2 ^ R + 1 ≤ twentyOneEvenQuotientCoreRemainder R
  · rw [if_pos htake]
    rw [hpow] at hcore ⊢
    omega
  · rw [if_neg htake]
    rw [hpow]
    omega

/-- The coarse preterminal ceiling leaves the strict-core state below its
last coin.  The old six exceptional preterminal values merely become the
three top strict-core values. -/
theorem twentyOneEvenQuotientCoreRemainder_lt_add_four_of_preterminalBound
    {R : ℕ} (hR : 4 ≤ R)
    (hpre :
      twentyOneEvenQuotientPreterminalRemainder R <
        2 * 2 ^ (R + 1) + 8) :
    twentyOneEvenQuotientCoreRemainder R < 2 ^ (R + 1) + 4 := by
  rw [twentyOneEvenQuotientCoreRemainder_eq_preterminalStep hR]
  by_cases htake :
      2 ^ (R + 1) + 4 ≤ twentyOneEvenQuotientPreterminalRemainder R
  · rw [if_pos htake]
    omega
  · rw [if_neg htake]
    omega

/-- After the terminal lower rank, the same coarse bound exceeds the closed
binary window by at most two. -/
theorem twentyOneEvenQuotientGreedyRemainder_le_add_two_of_preterminalBound
    {R : ℕ} (hR : 4 ≤ R)
    (hpre :
      twentyOneEvenQuotientPreterminalRemainder R <
        2 * 2 ^ (R + 1) + 8) :
    twentyOneEvenQuotientGreedyRemainder R ≤ 2 ^ R + 2 := by
  have hcore :=
    twentyOneEvenQuotientCoreRemainder_lt_add_four_of_preterminalBound
      hR hpre
  rw [twentyOneEvenQuotientGreedyRemainder_eq_coreStep (by omega)]
  by_cases htake :
      2 ^ R + 1 ≤ twentyOneEvenQuotientCoreRemainder R
  · rw [if_pos htake]
    have hpow : 2 ^ (R + 1) = 2 * 2 ^ R := by
      rw [pow_succ]
      omega
    rw [hpow] at hcore
    omega
  · rw [if_neg htake]
    omega

/-- **Terminal-fringe absorption.**  All six preterminal fringe states are
accepted.  The full binary suffix converts the coarse preterminal ceiling
to terminal defect at most three. -/
theorem twentyOneEvenFullQuotientGreedyRemainder_le_three_of_preterminalBound
    {R : ℕ} (hR : 4 ≤ R)
    (hpre :
      twentyOneEvenQuotientPreterminalRemainder R <
        2 * 2 ^ (R + 1) + 8) :
    twentyOneEvenFullQuotientGreedyRemainder R ≤ 3 := by
  rw [twentyOneEvenFullQuotientGreedyRemainder_eq_upperCompletion (by omega)]
  apply integerGreedyRemainder_upperMersenneWindow_le_add
      (M := 2 * R) (d := R + 1) (K := 2)
  · omega
  · omega
  · omega
  · simpa only [show 2 * R + 1 - (R + 1) = R by omega] using
      twentyOneEvenQuotientGreedyRemainder_le_add_two_of_preterminalBound
        hR hpre

/-- Every rank selected by the full quotient word lies in `2,…,2R`. -/
theorem twentyOneEvenFullQuotientGreedySupport_mem_bounds
    {R d : ℕ} (hd : d ∈ twentyOneEvenFullQuotientGreedySupport R) :
    2 ≤ d ∧ d ≤ 2 * R := by
  unfold twentyOneEvenFullQuotientGreedySupport at hd
  have hbounds := lowerSupportFromBits_mem_bounds hd
  have hlen := integerGreedyBits_length
    (localMersenneWeights (2 * R) (2 * R))
    (twentyOneQuotientTarget (2 * R))
  simp only [localMersenneWeights_length] at hlen
  omega

/-- The decoded full quotient and its terminal defect exactly partition the
denominator-`21` target. -/
theorem localPrefixQuotient_twentyOneEvenFullGreedySupport_add_remainder
    {R : ℕ} (hR : 1 ≤ R) :
    localPrefixQuotient
          (twentyOneEvenFullQuotientGreedySupport R) (2 * R) +
        twentyOneEvenFullQuotientGreedyRemainder R =
      twentyOneQuotientTarget (2 * R) := by
  let weights := localMersenneWeights (2 * R) (2 * R)
  let C := twentyOneQuotientTarget (2 * R)
  let bits := integerGreedyBits weights C
  have hlen : bits.length = 2 * R - 1 := by
    simpa [bits, weights] using integerGreedyBits_length weights C
  have hlen' : bits.length = 2 * R + 1 - 2 := by omega
  have hdecode :=
    localPrefixQuotient_lowerSupportFromBits
      (M := 2 * R) (R := 2 * R) (d := 2) (bits := bits) hlen'
  have hadm := integerGreedyBits_admissible weights C
  have hadm' : weightedBoolSum weights bits ≤ C := by
    simpa [bits] using hadm
  have hpartition :
      weightedBoolSum weights bits + integerGreedyRemainder weights C = C := by
    unfold integerGreedyRemainder
    change weightedBoolSum weights bits +
        (C - weightedBoolSum weights bits) = C
    omega
  change localPrefixQuotient (lowerSupportFromBits 2 bits) (2 * R) +
      integerGreedyRemainder weights C = C
  rw [hdecode]
  exact hpartition

theorem localPrefixQuotient_twentyOneEvenFullGreedySupport_le
    {R : ℕ} (hR : 1 ≤ R) :
    localPrefixQuotient
        (twentyOneEvenFullQuotientGreedySupport R) (2 * R) ≤
      twentyOneQuotientTarget (2 * R) := by
  have hpartition :=
    localPrefixQuotient_twentyOneEvenFullGreedySupport_add_remainder hR
  omega

/-- The abstract quotient defect of the full row is its concrete terminal
greedy remainder. -/
theorem twentyOneQuotientDefect_fullGreedySupport
    {R : ℕ} (hR : 1 ≤ R) :
    twentyOneQuotientDefect
        (twentyOneEvenFullQuotientGreedySupport R) (2 * R) =
      twentyOneEvenFullQuotientGreedyRemainder R := by
  unfold twentyOneQuotientDefect
  have hpartition :=
    localPrefixQuotient_twentyOneEvenFullGreedySupport_add_remainder hR
  omega

/-- Residue-class form of the full-row sign obstruction.  Along
`R ≡ 0 (mod 3)`, overshoot is exactly the concrete inequality
`defect + 1/21 ≤ fractional mass`. -/
theorem one_div_twenty_one_le_fullGreedyPrefix_iff_fraction_balance
    {R : ℕ} (hR : 1 ≤ R) (hRthree : 3 ∣ R) :
    (1 / 21 : ℚ) ≤
        localMersennePrefixValue
          (twentyOneEvenFullQuotientGreedySupport R) ↔
      (twentyOneEvenFullQuotientGreedyRemainder R : ℚ) +
          (1 / 21 : ℚ) ≤
        localFractionMass
          (twentyOneEvenFullQuotientGreedySupport R) (2 * R) := by
  rw [one_div_twenty_one_le_localMersennePrefixValue_iff_fraction_balance
      (fun d hd =>
        (twentyOneEvenFullQuotientGreedySupport_mem_bounds hd).1)
      (localPrefixQuotient_twentyOneEvenFullGreedySupport_le hR),
    twentyOneQuotientDefect_fullGreedySupport hR,
    twentyOneTargetFraction_two_mul_eq_one_div_twenty_one_of_three_dvd
      hRthree]

/-- A convenient elementary envelope for the linear error supplied by an
overshooting full row. -/
theorem two_mul_sub_two_le_two_pow (R : ℕ) :
    2 * R - 2 ≤ 2 ^ R := by
  induction R with
  | zero => simp
  | succ R ih =>
      cases R with
      | zero => norm_num
      | succ R =>
          rw [pow_succ]
          have htwo : 2 ≤ 2 ^ (R + 1) := by
            simpa using
              (Nat.pow_le_pow_right (by norm_num : 0 < 2)
                (show 1 ≤ R + 1 by omega))
          omega

/-- One-sided full-row criterion.  No bound on the deterministic quotient
remainder is assumed: it is enough that an unbounded sequence of admissible
full greedy rows reaches the rational target from above. -/
def TwentyOneCofinalEvenFullQuotientOvershoot : Prop :=
  ∃ R : ℕ → ℕ,
    Tendsto R atTop atTop ∧
      (∀ k : ℕ, 2 ≤ R k) ∧
      ∀ k : ℕ, (1 / 21 : ℚ) ≤
        localMersennePrefixValue
          (twentyOneEvenFullQuotientGreedySupport (R k))

/-- Boolean form of the cofinal full-row criterion.  A row qualifies exactly
when quotient rounding has forced a decision different from exact rational
greedy by the same horizon. -/
def TwentyOneCofinalEvenFullQuotientRationalDivergence : Prop :=
  ∃ R : ℕ → ℕ,
    Tendsto R atTop atTop ∧
      (∀ k : ℕ, 2 ≤ R k) ∧
      ∀ k : ℕ,
        integerGreedyBits
            (localMersenneWeights (2 * R k) (2 * R k))
            (twentyOneQuotientTarget (2 * R k)) ≠
          rationalMersenneGreedyBitsFrom 2 (2 * R k - 1) (1 / 21 : ℚ)

/-- **One-sided full-row endpoint.**  Cofinal overshoot of the deterministic
full quotient rows already proves membership.  The scaled error identity
forces quotient defect at most support cardinality, hence only linear
numerator growth against the exponential binary normalization. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalFullOvershoot
    (hover : TwentyOneCofinalEvenFullQuotientOvershoot) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  classical
  rcases hover with ⟨R, hR, hRtwo, hover⟩
  let D : ℕ → Finset ℕ :=
    fun k => twentyOneEvenFullQuotientGreedySupport (R k)
  let y : ℕ → ℝ :=
    fun k => ((localMersennePrefixValue (D k) : ℚ) : ℝ)
  have hdist :
      Tendsto (fun k : ℕ => dist (y k) (1 / 21 : ℝ))
        atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => dist_nonneg)
      (Filter.Eventually.of_forall fun k => ?_)
      (tendsto_twentyOne_evenQuotientWindow_error.comp hR)
    rw [Real.dist_eq]
    calc
      |y k - (1 / 21 : ℝ)| ≤
          ((twentyOneQuotientDefect (D k) (2 * R k) +
              (D k).card + 1 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * R k) := by
        exact abs_localMersennePrefixValue_sub_one_div_twenty_one_le
          (fun d hd =>
            (twentyOneEvenFullQuotientGreedySupport_mem_bounds
              (R := R k) (d := d) (by simpa [D] using hd)).1)
          (by
            simpa [D] using
              localPrefixQuotient_twentyOneEvenFullGreedySupport_le
                (R := R k) (by
                  have hRk := hRtwo k
                  omega))
      _ ≤
          (((2 ^ (R k) + (2 * R k + 1) : ℕ) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * R k) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hcard : (D k).card ≤ 2 * R k - 1 := by
          have hsubset : D k ⊆ Finset.Icc 2 (2 * R k) := by
            intro d hd
            simp only [Finset.mem_Icc]
            exact
              twentyOneEvenFullQuotientGreedySupport_mem_bounds
                (R := R k) (d := d) (by simpa [D] using hd)
          calc
            (D k).card ≤ (Finset.Icc 2 (2 * R k)).card :=
              Finset.card_le_card hsubset
            _ = 2 * R k - 1 := by simp
        have hadm :
            localPrefixQuotient (D k) (2 * R k) ≤
              twentyOneQuotientTarget (2 * R k) := by
          simpa [D] using
            localPrefixQuotient_twentyOneEvenFullGreedySupport_le
              (R := R k) (by
                have hRk := hRtwo k
                omega)
        have hdefect :
            twentyOneQuotientDefect (D k) (2 * R k) ≤ (D k).card := by
          exact twentyOneQuotientDefect_le_card_of_target_le_prefix
            (fun d hd =>
              (twentyOneEvenFullQuotientGreedySupport_mem_bounds
                (R := R k) (d := d) (by simpa [D] using hd)).1)
            hadm (by simpa [D] using hover k)
        have hlinear := two_mul_sub_two_le_two_pow (R k)
        exact_mod_cast (by omega :
          twentyOneQuotientDefect (D k) (2 * R k) +
              (D k).card + 1 ≤
            2 ^ (R k) + (2 * R k + 1))
  have hy : Tendsto y atTop (nhds (1 / 21 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hyMem : ∀ k : ℕ, y k ∈ mersenneAchievementSet := by
    intro k
    let A : Set ℕ := ↑(D k)
    have hA0 : 0 ∉ A := by
      intro hzero
      have hbound :=
        twentyOneEvenFullQuotientGreedySupport_mem_bounds
          (R := R k) (d := 0) (by simpa [A, D] using hzero)
      omega
    refine ⟨A, hA0, ?_⟩
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [y, D, localMersennePrefixValue_eq_finiteErdosSum]
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

/-- **Boolean divergence endpoint.**  Cofinal finite disagreement between
quotient greedy and exact rational greedy proves the prescribed point. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalFullDivergence
    (hdiv : TwentyOneCofinalEvenFullQuotientRationalDivergence) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalFullOvershoot
  rcases hdiv with ⟨R, hR, hRtwo, hdiv⟩
  exact ⟨R, hR, hRtwo, fun k =>
    (one_div_twenty_one_lt_fullGreedyPrefix_of_bits_ne_rational
      (hdiv k)).le⟩

/-- The only possible surviving branch after the Boolean divergence
endpoint: beyond one finite row, every complete quotient-greedy word agrees
bit-for-bit with the exact rational greedy word through the same horizon. -/
def TwentyOneEventuallyEvenFullQuotientRationalAlignment : Prop :=
  ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    integerGreedyBits
        (localMersenneWeights (2 * R) (2 * R))
        (twentyOneQuotientTarget (2 * R)) =
      rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)

/-- Full quotient/rational alignment already identifies the canonical
lower-half quotient support with the actual real greedy support.  This is
the bridge which lets a local lower-state obstruction consume the cofinite
support information in the fatal branch. -/
theorem twentyOneEvenQuotientGreedySupport_mem_iff_of_fullAlignment
    {R d : ℕ} (hR : 2 ≤ R) (hd2 : 2 ≤ d) (hdR : d ≤ R)
    (halign :
      integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R)) =
        rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)) :
    d ∈ twentyOneEvenQuotientGreedySupport R ↔
      d ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
  have hsplit :
      localMersenneWeights (2 * R) (2 * R) =
        localMersenneWeights (2 * R) R ++
          localMersenneWeightsFrom (2 * R) (2 * R) (R + 1) := by
    unfold localMersenneWeights
    exact localMersenneWeightsFrom_split (by omega) (by omega)
  have hprefixQ :
      (integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R))).take (R - 1) =
        integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) := by
    rw [hsplit, integerGreedyBits_append]
    have hlen :
        (integerGreedyBits
            (localMersenneWeights (2 * R) R)
            (twentyOneQuotientTarget (2 * R))).length = R - 1 := by
      rw [integerGreedyBits_length, localMersenneWeights_length]
    rw [← hlen]
    exact List.take_left
  have hcount : 2 * R - 1 = (R - 1) + R := by omega
  have hprefixRat :
      (rationalMersenneGreedyBitsFrom 2 (2 * R - 1)
          (1 / 21 : ℚ)).take (R - 1) =
        rationalMersenneGreedyBitsFrom 2 (R - 1) (1 / 21 : ℚ) := by
    rw [hcount]
    exact rationalMersenneGreedyBitsFrom_take 2 (R - 1) R (1 / 21 : ℚ)
  have hwords :
      integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) =
        rationalMersenneGreedyBitsFrom 2 (R - 1) (1 / 21 : ℚ) := by
    rw [← hprefixQ, halign, hprefixRat]
  have hresidual :
      greedyMersenneRemainderRat (1 / 21 : ℚ) (2 - 1) =
        (1 / 21 : ℚ) := by
    norm_num [greedyMersenneRemainderRat, mersenneWeightRat]
  unfold twentyOneEvenQuotientGreedySupport
  rw [hwords, ← hresidual]
  rw [mem_lowerSupportFromBits_rationalMersenneGreedyBitsFrom_iff
    (x := (1 / 21 : ℚ)) (d := 2) (n := R - 1) (e := d) (by omega)]
  norm_num
  constructor
  · exact fun h ↦ h.2.2
  · exact fun hd ↦ ⟨hd2, by omega, hd⟩

/-- **Unconditional terminal dichotomy.**  If the prescribed point is not
already in the achievement set, quotient rounding can disagree with exact
rational greedy only at finitely many full even horizons.

Indeed, failure of eventual alignment supplies a disagreeing row beyond
every cutoff.  Choosing one such row beyond `k + 2` gives a cofinal sequence,
and the Boolean divergence endpoint then proves membership. -/
theorem twentyOneEventuallyEvenFullQuotientRationalAlignment_of_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    TwentyOneEventuallyEvenFullQuotientRationalAlignment := by
  classical
  by_contra hfail
  unfold TwentyOneEventuallyEvenFullQuotientRationalAlignment at hfail
  push Not at hfail
  choose R hRge hRdiv using fun k => hfail (k + 2)
  apply hnot
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalFullDivergence
  refine ⟨R, ?_, ?_, hRdiv⟩
  · apply tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards with k
    simpa only [id_eq] using (show k ≤ R k by
      have := hRge k
      omega)
  · intro k
    have := hRge k
    omega

/-- Every future argument may therefore split on a mathematically exact
alternative: either `1/21` is represented, or all sufficiently deep full
quotient rows are genuine rational-greedy prefixes. -/
theorem one_div_twenty_one_mem_or_eventuallyFullQuotientRationalAlignment :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ∨
      TwentyOneEventuallyEvenFullQuotientRationalAlignment := by
  by_cases hmem : (1 / 21 : ℝ) ∈ mersenneAchievementSet
  · exact Or.inl hmem
  · exact Or.inr
      (twentyOneEventuallyEvenFullQuotientRationalAlignment_of_not_mem hmem)

/-- The single branch left after combining the exact greedy survival
criterion, absorbing fatality, quotient/rational alignment, and the
correction-boundary doubling-block split.

The definition records the fatal witness together with the eventual alignment
and doubling-block conditions used below. -/
def TwentyOneFatalAlignedBranch : Prop :=
  ∃ n R₀ : ℕ,
    GreedyMersenneFatalAt (1 / 21 : ℝ) n ∧
      (greedyMersenneSkippedSupport (1 / 21 : ℝ)).Finite ∧
      (∀ k : ℕ,
        n + k + 1 ∈ greedyMersenneSupport (1 / 21 : ℝ)) ∧
      (∀ R : ℕ, R₀ ≤ R →
        integerGreedyBits
            (localMersenneWeights (2 * R) (2 * R))
            (twentyOneQuotientTarget (2 * R)) =
          rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)) ∧
      TwentyOneGreedyEventuallyHitsDoublingBlocks

/-- **The fatal branch cannot sustain a late failed saturated transition.**  Full
quotient/rational alignment identifies the canonical lower word with the
actual greedy support.  Cofinite selection then fills both ancestor digits
forced by a sufficiently late scale `R = 3a+1`, contradicting the
one-third-scale hole theorem. -/
theorem twentyOneFatalAlignedBranch_eventually_saturated_socket
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R s : ℕ, K ≤ R →
      s < 2 ^ R →
      twentyOneBoundaryScalarState R
          (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse
              (twentyOneEvenQuotientGreedySupport R) (2 * R)) =
        2 ^ (R + 1) →
      twentyOneTargetTwoStepPulse (2 * (R + 1)) ≤
        localPrefixTwoStepPulse
            (twentyOneBoundaryLowerSupport
              (twentyOneEvenQuotientGreedySupport R) R
              (4 * s + twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)))
            (2 * (R + 1)) +
          1 := by
  obtain
      ⟨n, R₀, _hfatal, _hfinite, hselected, halign, _hhits⟩ :=
    hbranch
  refine ⟨max R₀ (3 * n + 4), ?_⟩
  intro R s hKR hstrict hsaturated
  have hR₀ : R₀ ≤ R := (le_max_left _ _).trans hKR
  have hR4 : 4 ≤ R := by
    have hlarge : 3 * n + 4 ≤ R :=
      (le_max_right R₀ (3 * n + 4)).trans hKR
    omega
  by_contra hbad
  obtain ⟨a, hRa, hhole⟩ :=
    twentyOneBadSaturatedTransition_forces_ancestor_hole
      (D := twentyOneEvenQuotientGreedySupport R)
      hR4 hstrict hsaturated hbad
  have hna : n ≤ a := by
    have hlarge : 3 * n + 4 ≤ R :=
      (le_max_right R₀ (3 * n + 4)).trans hKR
    omega
  have hRtwo : 2 ≤ R := by omega
  have halignR := halign R hR₀
  have hactual₁ :
      a + 1 ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
    convert hselected (a - n) using 1 <;> omega
  have hactual₂ :
      2 * (a + 1) ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
    convert hselected (2 * a + 1 - n) using 1 <;> omega
  have hD₁ :
      a + 1 ∈ twentyOneEvenQuotientGreedySupport R := by
    apply
      (twentyOneEvenQuotientGreedySupport_mem_iff_of_fullAlignment
        hRtwo (by omega) (by rw [hRa]; omega) halignR).2
    exact hactual₁
  have hD₂ :
      2 * (a + 1) ∈ twentyOneEvenQuotientGreedySupport R := by
    apply
      (twentyOneEvenQuotientGreedySupport_mem_iff_of_fullAlignment
        hRtwo (by omega) (by rw [hRa]; omega) halignR).2
    exact hactual₂
  exact hhole.elim (fun h ↦ h hD₁) (fun h ↦ h hD₂)

/-- Non-membership has no diffuse asymptotic branch: it forces one absorbing
fatal state, cofinite exact-greedy selection, eventual quotient/rational
alignment, and eventual occupation of every doubling block. -/
theorem twentyOneFatalAlignedBranch_of_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    TwentyOneFatalAlignedBranch := by
  have hnotSurvive :
      ¬ ∀ n : ℕ,
        greedyMersenneRemainder (1 / 21 : ℝ) n ≤ mersenneTail n := by
    intro hsurvive
    exact hnot
      ((mem_mersenneAchievementSet_iff_greedy_survival
        (1 / 21 : ℝ)).2 ⟨by norm_num, hsurvive⟩)
  push Not at hnotSurvive
  obtain ⟨n, hn⟩ := hnotSurvive
  have hfatal : GreedyMersenneFatalAt (1 / 21 : ℝ) n := hn
  obtain ⟨R₀, halign⟩ :=
    twentyOneEventuallyEvenFullQuotientRationalAlignment_of_not_mem hnot
  have hhits : TwentyOneGreedyEventuallyHitsDoublingBlocks :=
    (one_div_twenty_one_mem_or_eventually_hits_doublingBlocks).resolve_left
      hnot
  exact ⟨n, R₀, hfatal,
    finite_greedyMersenneSkippedSupport_of_fatalAt hfatal,
    fun k => mem_greedyMersenneSupport_of_fatalAt_add_succ hfatal k,
    halign, hhits⟩

/-- **Exact membership dichotomy.**  Membership of `1/21` is equivalent
to excluding one explicit fatal/cofinite/aligned branch; every other
asymptotic behavior already lands in the achievement set. -/
theorem one_div_twenty_one_mem_or_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ∨
      TwentyOneFatalAlignedBranch := by
  by_cases hmem : (1 / 21 : ℝ) ∈ mersenneAchievementSet
  · exact Or.inl hmem
  · exact Or.inr (twentyOneFatalAlignedBranch_of_not_mem hmem)

/-- The displayed branch is not merely necessary: its fatal witness makes it
exactly equivalent to non-membership. -/
theorem twentyOneFatalAlignedBranch_iff_not_mem :
    TwentyOneFatalAlignedBranch ↔
      (1 / 21 : ℝ) ∉ mersenneAchievementSet := by
  constructor
  · rintro ⟨n, _R₀, hfatal, _hfinite, _hselected, _halign, _hhits⟩ hmem
    have hsurvive :=
      (mem_mersenneAchievementSet_iff_greedy_survival
        (1 / 21 : ℝ)).1 hmem
    exact (not_le_of_gt hfatal) (hsurvive.2 n)
  · exact twentyOneFatalAlignedBranch_of_not_mem

/-- Consequently the prescribed point is represented exactly when the
fatal/cofinite/aligned branch is impossible. -/
theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch := by
  rw [twentyOneFatalAlignedBranch_iff_not_mem]
  tauto

/-! ## The fatal branch as an Erdős--Borwein approximation -/

open scoped Classical in
/-- The actual denominator-`21` skips visible through level `M`. -/
noncomputable def twentyOneSkippedPrefix (M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter
    (fun m => m ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ))

/-- `M` is the final exponent skipped by the actual denominator-`21`
greedy orbit. -/
def IsLastTwentyOneGreedySkip (M : ℕ) : Prop :=
  M ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ) ∧
    ∀ m, M < m →
      m ∉ greedyMersenneSkippedSupport (1 / 21 : ℝ)

/-- Rank one is unconditionally omitted by the denominator-`21` orbit.
This supplies the nonempty finite set needed to choose a final skip. -/
theorem one_mem_greedyMersenneSkippedSupport_twentyOne :
    1 ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ) := by
  rw [show (1 : ℕ) = 0 + 1 by omega,
    succ_mem_greedyMersenneSkippedSupport_iff]
  norm_num [greedyMersenneRemainder, mersenneWeight]

/-- A final skip makes the bounded prefix equal to the complete skipped
support. -/
theorem coe_twentyOneSkippedPrefix_eq_skippedSupport
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    (↑(twentyOneSkippedPrefix M) : Set ℕ) =
      greedyMersenneSkippedSupport (1 / 21 : ℝ) := by
  classical
  ext m
  simp only [twentyOneSkippedPrefix, Finset.mem_coe, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · exact fun hm => hm.2
  · intro hm
    refine ⟨?_, hm⟩
    by_contra hnot
    exact hlast.2 m (by omega) hm

/-- Exponent zero never enters a denominator-`21` skipped prefix. -/
theorem zero_not_mem_twentyOneSkippedPrefix (M : ℕ) :
    0 ∉ twentyOneSkippedPrefix M := by
  simp [twentyOneSkippedPrefix,
    zero_not_mem_greedyMersenneSkippedSupport]

/-- The final actual skip is visible in its bounded skipped prefix. -/
theorem lastTwentyOneSkip_mem_skippedPrefix
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    M ∈ twentyOneSkippedPrefix M := by
  classical
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), hlast.1⟩

/-- The exact reduced denominator of the final skipped-prefix sum has
binary order equal to the skipped-exponent LCM. -/
theorem lastTwentyOneSkip_oddDoublingOrder_eq_lcm
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    oddDoublingOrder
          (finiteErdosSum (twentyOneSkippedPrefix M) 2).den
          (finiteErdosSum_den_odd (twentyOneSkippedPrefix M)
            (zero_not_mem_twentyOneSkippedPrefix M)) =
      (twentyOneSkippedPrefix M).lcm id := by
  exact oddDoublingOrder_finiteErdosSum_den_eq_lcm
    (twentyOneSkippedPrefix M)
    ⟨M, lastTwentyOneSkip_mem_skippedPrefix hlast⟩
    (zero_not_mem_twentyOneSkippedPrefix M)

/-- In particular, the final skipped exponent survives as a lower bound on
the exact binary order of the reduced finite-shift denominator. -/
theorem lastTwentyOneSkip_le_oddDoublingOrder
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    M ≤
      oddDoublingOrder
        (finiteErdosSum (twentyOneSkippedPrefix M) 2).den
        (finiteErdosSum_den_odd (twentyOneSkippedPrefix M)
          (zero_not_mem_twentyOneSkippedPrefix M)) := by
  rw [lastTwentyOneSkip_oddDoublingOrder_eq_lcm hlast]
  apply Nat.le_of_dvd
  · exact Nat.pos_of_ne_zero
      (lcm_ne_zero_of_zero_not_mem (twentyOneSkippedPrefix M)
        (zero_not_mem_twentyOneSkippedPrefix M))
  · exact Finset.dvd_lcm (f := id)
      (lastTwentyOneSkip_mem_skippedPrefix hlast)

/-- After a final skip, every remaining Mersenne weight is selected. -/
theorem twentyOneGreedySupportSuffix_eq_tail_of_lastSkip
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    positiveMersenneSupportSuffix
        (greedyMersenneSupport (1 / 21 : ℝ)) M =
      mersenneTail M := by
  unfold positiveMersenneSupportSuffix mersenneTail
  apply tsum_congr
  intro k
  have hnotSkip :
      M + k + 1 ∉ greedyMersenneSkippedSupport (1 / 21 : ℝ) :=
    hlast.2 (M + k + 1) (by omega)
  have hselected :
      M + k + 1 ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
    by_contra hnotSelected
    exact hnotSkip ⟨by omega, hnotSelected⟩
  rw [Set.indicator_of_mem hselected]

/-- The selected value is its finite prefix plus the complete tail after a
final denominator-`21` skip. -/
theorem twentyOneGreedySupportValue_eq_prefix_add_tail_of_lastSkip
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    positiveMersenneSupportValue
        (greedyMersenneSupport (1 / 21 : ℝ)) =
      (∑ k ∈ Finset.range M,
          Set.indicator (greedyMersenneSupport (1 / 21 : ℝ))
            mersenneWeight (k + 1)) +
        mersenneTail M := by
  rw [positiveMersenneSupportValue_eq_prefix_add_suffix]
  rw [twentyOneGreedySupportSuffix_eq_tail_of_lastSkip hlast]

/-- Exact displacement identity: the finite rational shift above the
Erdős--Borwein constant is the fatal residual excess over the remaining
tail. -/
theorem lastTwentyOneSkip_shiftDelta_eq_remainder_sub_tail
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    (1 / 21 : ℝ) +
          positiveMersenneSupportValue
            (↑(twentyOneSkippedPrefix M) : Set ℕ) -
        erdosBorweinMersenneConstant =
      greedyMersenneRemainder (1 / 21 : ℝ) M - mersenneTail M := by
  have hpartition :=
    erdosBorweinMersenneConstant_eq_greedy_add_skipped (1 / 21 : ℝ)
  have hcoe := coe_twentyOneSkippedPrefix_eq_skippedSupport hlast
  have hselected :=
    twentyOneGreedySupportValue_eq_prefix_add_tail_of_lastSkip hlast
  have hprefix :=
    greedyMersenne_prefix_add_remainder (1 / 21 : ℝ) M
  rw [← hcoe, hselected] at hpartition
  linarith

/-- A final omitted rank leaves the post-decision residual below its
omitted Mersenne weight. -/
theorem lastTwentyOneSkip_remainder_lt_weight
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    greedyMersenneRemainder (1 / 21 : ℝ) M < mersenneWeight M := by
  rcases M with _ | m
  · exact False.elim
      (zero_not_mem_greedyMersenneSkippedSupport (1 / 21 : ℝ) hlast.1)
  · have hskip :
        ¬ mersenneWeight (m + 1) ≤
          greedyMersenneRemainder (1 / 21 : ℝ) m :=
      (succ_mem_greedyMersenneSkippedSupport_iff
        (1 / 21 : ℝ) m).1 hlast.1
    rw [greedyMersenneRemainder_succ, if_neg hskip]
    exact lt_of_not_ge hskip

/-- Selecting the complete suffix makes the remaining tail no larger than
the level-`M` residual. -/
theorem lastTwentyOneSkip_tail_le_remainder
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    mersenneTail M ≤
      greedyMersenneRemainder (1 / 21 : ℝ) M := by
  have hstep : ∀ k : ℕ,
      greedyMersenneRemainder (1 / 21 : ℝ) (M + k) =
        greedyMersenneRemainder (1 / 21 : ℝ) M -
          ∑ i ∈ Finset.range k, mersenneWeight (M + i + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hnotSkip :
            M + k + 1 ∉
              greedyMersenneSkippedSupport (1 / 21 : ℝ) :=
          hlast.2 (M + k + 1) (by omega)
        have htake :
            mersenneWeight (M + k + 1) ≤
              greedyMersenneRemainder (1 / 21 : ℝ) (M + k) := by
          by_contra hnot
          exact hnotSkip
            ((succ_mem_greedyMersenneSkippedSupport_iff
              (1 / 21 : ℝ) (M + k)).2 hnot)
        rw [show M + (k + 1) = (M + k) + 1 by ring,
          greedyMersenneRemainder_succ, if_pos htake, ih,
          Finset.sum_range_succ]
        ring
  have hpartial : ∀ k : ℕ,
      ∑ i ∈ Finset.range k, mersenneWeight (M + i + 1) ≤
        greedyMersenneRemainder (1 / 21 : ℝ) M := by
    intro k
    have hnonneg := greedyMersenneRemainder_nonneg
      (x := (1 / 21 : ℝ)) (by norm_num) (M + k)
    have h := hstep k
    linarith
  unfold mersenneTail
  exact le_of_tendsto'
    (summable_mersenneTail M).tendsto_sum_tsum_nat hpartial

/-- Irrationality excludes equality between the Erdős--Borwein constant and
the rational finite shift determined by a final denominator-`21` skip. -/
theorem lastTwentyOneSkip_shiftDelta_ne_zero
    {M : ℕ} (_hlast : IsLastTwentyOneGreedySkip M) :
    (1 / 21 : ℝ) +
          positiveMersenneSupportValue
            (↑(twentyOneSkippedPrefix M) : Set ℕ) -
        erdosBorweinMersenneConstant ≠ 0 := by
  intro hzero
  apply (irrational_erdosBorweinMersenneConstant.ne_rat
    ((1 : ℚ) / 21 + finiteErdosSum (twentyOneSkippedPrefix M) 2))
  have hshift :=
    positiveMersenneSupportValue_eq_cast_finiteErdosSum
      (twentyOneSkippedPrefix M)
  calc
    erdosBorweinMersenneConstant =
        (1 / 21 : ℝ) +
          positiveMersenneSupportValue
            (↑(twentyOneSkippedPrefix M) : Set ℕ) := by
              linarith
    _ = (((1 : ℚ) / 21 +
          finiteErdosSum (twentyOneSkippedPrefix M) 2 : ℚ) : ℝ) := by
            rw [hshift]
            push_cast
            norm_num

/-- A final denominator-`21` skip gives an exact one-sided approximation to
the Erdős--Borwein constant, with error strictly smaller than the
superincreasing gap at the final omitted exponent. -/
theorem lastTwentyOneSkip_erdosBorwein_fatalInterval
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    0 <
        (1 / 21 : ℝ) +
            positiveMersenneSupportValue
              (↑(twentyOneSkippedPrefix M) : Set ℕ) -
          erdosBorweinMersenneConstant ∧
      (1 / 21 : ℝ) +
            positiveMersenneSupportValue
              (↑(twentyOneSkippedPrefix M) : Set ℕ) -
          erdosBorweinMersenneConstant <
        mersenneGap M := by
  have hdelta :=
    lastTwentyOneSkip_shiftDelta_eq_remainder_sub_tail hlast
  have hnonneg := lastTwentyOneSkip_tail_le_remainder hlast
  have hne := lastTwentyOneSkip_shiftDelta_ne_zero hlast
  have hrem := lastTwentyOneSkip_remainder_lt_weight hlast
  constructor
  · exact lt_of_le_of_ne (by linarith) (Ne.symm hne)
  · unfold mersenneGap
    linarith

/-- A rational lying between the first three geometric tail channels and
the current Mersenne weight has a sharply localized dyadic excess.  If
`x = p/q` and `Δ = pT-q`, then `p/3 < Δ < p`.

The third channel is decisive for the strict lower bound: the first two
channels alone approach `p/3` from the wrong side. -/
theorem rat_thirdChannelWindow_dyadicExcess
    (x : ℚ) {T : ℕ} (hT : 2 ≤ T)
    (hlower :
      1 / (T : ℚ) +
          1 / (3 * (T : ℚ) ^ 2) +
          1 / (7 * (T : ℚ) ^ 3) < x)
    (hupper : x < 1 / ((T : ℚ) - 1)) :
    x.num.natAbs <
        3 * (x.num.natAbs * T - x.den) ∧
      x.num.natAbs * T - x.den < x.num.natAbs := by
  let p := x.num.natAbs
  let q := x.den
  change p < 3 * (p * T - q) ∧ p * T - q < p
  have hbasePos :
      (0 : ℚ) <
        1 / (T : ℚ) +
          1 / (3 * (T : ℚ) ^ 2) +
          1 / (7 * (T : ℚ) ^ 3) := by
    positivity
  have hxpos : 0 < x := hbasePos.trans hlower
  have hnumPos : 0 < x.num := Rat.num_pos.mpr hxpos
  have hpcastInt : (p : ℤ) = x.num := by
    simpa only [p, Int.natAbs_of_nonneg hnumPos.le]
  have hpcastRat : (p : ℚ) = (x.num : ℚ) := by
    exact_mod_cast hpcastInt
  have hqpos : 0 < q := by
    simpa only [q] using Rat.den_pos x
  have hqposRat : (0 : ℚ) < q := by exact_mod_cast hqpos
  have hTposRat : (0 : ℚ) < T := by exact_mod_cast (by omega : 0 < T)
  have hTsubPos : (0 : ℚ) < (T : ℚ) - 1 := by
    have hTcast : (2 : ℚ) ≤ T := by exact_mod_cast hT
    linarith
  have hthirdDenPos : (0 : ℚ) < (T : ℚ) - 1 / 3 := by
    have hTcast : (2 : ℚ) ≤ T := by exact_mod_cast hT
    linarith
  have hxform : x = (p : ℚ) / (q : ℚ) := by
    rw [hpcastRat]
    simpa only [q] using (Rat.num_div_den x).symm
  have hthreeChannel :
      1 / ((T : ℚ) - 1 / 3) <
        1 / (T : ℚ) +
          1 / (3 * (T : ℚ) ^ 2) +
          1 / (7 * (T : ℚ) ^ 3) := by
    have hTcast : (2 : ℚ) ≤ T := by exact_mod_cast hT
    apply (div_lt_iff₀ hthirdDenPos).2
    field_simp [ne_of_gt hTposRat]
    nlinarith
  have hlowerSimple :
      1 / ((T : ℚ) - 1 / 3) < (p : ℚ) / (q : ℚ) := by
    rw [← hxform]
    exact hthreeChannel.trans hlower
  have hlowerCrossRat :
      (q : ℚ) < (p : ℚ) * ((T : ℚ) - 1 / 3) := by
    have hcross :=
      (div_lt_div_iff₀ hthirdDenPos hqposRat).mp hlowerSimple
    simpa only [one_mul] using hcross
  have hlowerCross :
      p + 3 * q < 3 * (p * T) := by
    have hlowerCrossRat' :
        (p : ℚ) + 3 * (q : ℚ) <
          3 * ((p : ℚ) * (T : ℚ)) := by
      nlinarith [hlowerCrossRat]
    exact_mod_cast hlowerCrossRat'
  have hupperCrossRat :
      (p : ℚ) * ((T : ℚ) - 1) < q := by
    rw [hxform] at hupper
    have hcross :=
      (div_lt_div_iff₀ hqposRat hTsubPos).mp hupper
    simpa only [one_mul] using hcross
  have hupperCross : p * (T - 1) < q := by
    have hupperCrossRat' :
        ((p * (T - 1) : ℕ) : ℚ) < (q : ℚ) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ T)]
      norm_num
      exact hupperCrossRat
    exact_mod_cast hupperCrossRat'
  have hqpt : q < p * T := by
    have hfirstChannel :
        (1 : ℚ) / T < (p : ℚ) / q := by
      rw [← hxform]
      exact (by
        have hnonneg :
            (0 : ℚ) ≤
              1 / (3 * (T : ℚ) ^ 2) +
                1 / (7 * (T : ℚ) ^ 3) := by positivity
        linarith)
    have hcross :=
      (div_lt_div_iff₀ hTposRat hqposRat).mp hfirstChannel
    have hcrossRat' : (q : ℚ) < ((p * T : ℕ) : ℚ) := by
      rw [Nat.cast_mul]
      simpa only [one_mul] using hcross
    exact_mod_cast hcrossRat'
  have hdelta : p * T - q + q = p * T :=
    Nat.sub_add_cancel hqpt.le
  have hupperFactor : p * (T - 1) + p = p * T := by
    calc
      p * (T - 1) + p = p * ((T - 1) + 1) := by ring
      _ = p * T := by rw [Nat.sub_add_cancel (by omega : 1 ≤ T)]
  constructor
  · omega
  · omega

/-- At a final denominator-`21` skip, the reduced residual immediately
before the skip lies in the three-channel dyadic window.  Thus its exact
excess `Δ = p * 2^M - q` satisfies `p / 3 < Δ < p`. -/
theorem lastTwentyOneSkip_dyadicExcess_window
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    let x := greedyMersenneRemainderRat (1 / 21 : ℚ) (M - 1)
    x.num.natAbs <
        3 * (x.num.natAbs * 2 ^ M - x.den) ∧
      x.num.natAbs * 2 ^ M - x.den < x.num.natAbs := by
  rcases M with _ | m
  · exact False.elim
      (zero_not_mem_greedyMersenneSkippedSupport (1 / 21 : ℝ) hlast.1)
  · dsimp only [Nat.succ_sub_one]
    let x := greedyMersenneRemainderRat (1 / 21 : ℚ) m
    have hskipNot :
        ¬ mersenneWeight (m + 1) ≤
          greedyMersenneRemainder (1 / 21 : ℝ) m :=
      (succ_mem_greedyMersenneSkippedSupport_iff
        (1 / 21 : ℝ) m).1 hlast.1
    have hskipReal :
        greedyMersenneRemainder (1 / 21 : ℝ) m <
          mersenneWeight (m + 1) :=
      lt_of_not_ge hskipNot
    have hremSucc :
        greedyMersenneRemainder (1 / 21 : ℝ) (m + 1) =
          greedyMersenneRemainder (1 / 21 : ℝ) m := by
      rw [greedyMersenneRemainder_succ, if_neg hskipNot]
    have hlowerReal :
        HalfGreedyFatalGap.mersenneTailLB3 (m + 1) <
          greedyMersenneRemainder (1 / 21 : ℝ) m := by
      calc
        HalfGreedyFatalGap.mersenneTailLB3 (m + 1) <
            mersenneTail (m + 1) :=
          HalfGreedyFatalGap.mersenneTailLB3_lt_mersenneTail (m + 1)
        _ ≤ greedyMersenneRemainder (1 / 21 : ℝ) (m + 1) :=
          lastTwentyOneSkip_tail_le_remainder hlast
        _ = greedyMersenneRemainder (1 / 21 : ℝ) m := hremSucc
    have hlowerRat :
        1 / ((2 ^ (m + 1) : ℕ) : ℚ) +
              1 / (3 * (((2 ^ (m + 1) : ℕ) : ℚ)) ^ 2) +
              1 / (7 * (((2 ^ (m + 1) : ℕ) : ℚ)) ^ 3) <
            x := by
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa [x, HalfGreedyFatalGap.mersenneTailLB3, div_pow] using
        hlowerReal
    have hupperRat :
        x < 1 / (((2 ^ (m + 1) : ℕ) : ℚ) - 1) := by
      have hskipRat : x < mersenneWeightRat (m + 1) := by
        apply (Rat.cast_lt (K := ℝ)).mp
        simpa [x] using hskipReal
      simpa [mersenneWeightRat, natCast_pow_sub_one] using hskipRat
    simpa only [x] using
      rat_thirdChannelWindow_dyadicExcess x
        (T := 2 ^ (m + 1)) (by
          exact one_lt_pow₀ (by omega : 1 < (2 : ℕ))
            (by omega : m + 1 ≠ 0))
        hlowerRat hupperRat

/-- Every reduced rational residual on the `1/21` greedy orbit has odd
denominator.  The target denominator and every selected Mersenne
denominator are odd, and reduction can only divide their lcm. -/
theorem greedyTwentyOneRemainderRat_den_odd (n : ℕ) :
    Odd (greedyMersenneRemainderRat (1 / 21 : ℚ) n).den := by
  let P := greedyMersennePrefixRat (1 / 21 : ℚ) n
  have hP0 : 0 ∉ P := by
    simpa only [P] using
      zero_not_mem_greedyMersennePrefixRat (1 / 21 : ℚ) n
  have hprefixOdd : Odd (finiteErdosSum P 2).den :=
    finiteErdosSum_den_odd P hP0
  have hremEq :
      greedyMersenneRemainderRat (1 / 21 : ℚ) n =
        (1 / 21 : ℚ) - finiteErdosSum P 2 := by
    simpa only [P] using
      greedyMersenneRemainderRat_eq_sub_finiteErdosSum
        (1 / 21 : ℚ) n
  have htargetDen : (1 / 21 : ℚ).den = 21 := by norm_num
  have hremDvd :
      (greedyMersenneRemainderRat (1 / 21 : ℚ) n).den ∣
        Nat.lcm 21 (finiteErdosSum P 2).den := by
    rw [hremEq]
    simpa only [htargetDen] using
      Rat.sub_den_dvd_lcm (1 / 21 : ℚ) (finiteErdosSum P 2)
  have hproductOdd : Odd (21 * (finiteErdosSum P 2).den) :=
    (by exact ⟨10, by omega⟩ : Odd 21).mul hprefixOdd
  have hlcmOdd : Odd (Nat.lcm 21 (finiteErdosSum P 2).den) :=
    hproductOdd.of_dvd_nat
      (Nat.lcm_dvd_mul 21 (finiteErdosSum P 2).den)
  exact hlcmOdd.of_dvd_nat hremDvd

/-- Subtracting the reciprocal of an odd denominator flips the parity of
the reduced numerator, provided the subtraction stays positive.  The
point is that both stages of rational cancellation are odd: the common
factor of the two odd denominators is odd, and so is the residual
normalizing factor.  Thus cancellation cannot alter the parity flip in
`p * (Q / gcd(q,Q)) - q / gcd(q,Q)`. -/
theorem rat_sub_inv_oddDen_num_parity_flip
    (x : ℚ) {Q : ℕ} (hQpos : 0 < Q)
    (hxdenOdd : Odd x.den) (hQOdd : Odd Q)
    (htake : (1 : ℚ) / Q < x) :
    let y := x - (1 : ℚ) / Q
    (Odd x.num.natAbs → Even y.num.natAbs) ∧
      (Even x.num.natAbs → Odd y.num.natAbs) := by
  dsimp only
  let p := x.num.natAbs
  let q := x.den
  let d := Nat.gcd q Q
  let q₁ := q / d
  let Q₁ := Q / d
  let A := p * Q₁ - q₁
  let e := Nat.gcd A d
  let y := x - (1 : ℚ) / Q
  have hnormal :
      y.num.natAbs = A / e ∧
        y.den = (d / e) * q₁ * Q₁ := by
    simpa only [p, q, d, q₁, Q₁, A, e, y] using
      rat_sub_inv_nat_twoStage_normalForm x hQpos htake
  have hdq : d ∣ q := Nat.gcd_dvd_left q Q
  have hdQ : d ∣ Q := Nat.gcd_dvd_right q Q
  have hoddDiv :
      ∀ {a b : ℕ}, Odd a → b ∣ a → Odd (a / b) := by
    intro a b ha hba
    rw [← Nat.not_even_iff_odd]
    intro hquotEven
    apply (Nat.not_even_iff_odd.mpr ha)
    rw [← Nat.mul_div_cancel' hba]
    exact hquotEven.mul_left b
  have hdOdd : Odd d := hxdenOdd.of_dvd_nat hdq
  have hq₁Odd : Odd q₁ := hoddDiv hxdenOdd hdq
  have hQ₁Odd : Odd Q₁ := hoddDiv hQOdd hdQ
  have hed : e ∣ d := Nat.gcd_dvd_right A d
  have heA : e ∣ A := Nat.gcd_dvd_left A d
  have heOdd : Odd e := hdOdd.of_dvd_nat hed
  have hfactor : e * (A / e) = A := Nat.mul_div_cancel' heA
  have hypos : 0 < y := by
    dsimp only [y]
    exact sub_pos.mpr htake
  have hynumPos : 0 < y.num.natAbs := by
    have hnumPos : 0 < y.num := Rat.num_pos.mpr hypos
    exact Int.natAbs_pos.mpr (ne_of_gt hnumPos)
  have hAdivPos : 0 < A / e := by
    rw [← hnormal.1]
    exact hynumPos
  have hepos : 0 < e := heOdd.pos
  have hApos : 0 < A := by
    have heA_le : e ≤ A := (Nat.div_pos_iff.mp hAdivPos).2
    omega
  have hq₁le : q₁ ≤ p * Q₁ := by
    simpa only [A] using (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hApos))
  constructor
  · intro hpOdd
    have hAOddSub : Even A := by
      simpa only [A] using Nat.Odd.sub_odd (hpOdd.mul hQ₁Odd) hq₁Odd
    have htwoFactor : 2 ∣ e * (A / e) := by
      rw [hfactor]
      exact even_iff_two_dvd.mp hAOddSub
    have hquotEven : Even (A / e) :=
      even_iff_two_dvd.mpr
        (heOdd.coprime_two_left.dvd_of_dvd_mul_left htwoFactor)
    rw [hnormal.1]
    exact hquotEven
  · intro hpEven
    have hAOdd : Odd A := by
      simpa only [A] using
        Nat.Even.sub_odd hq₁le (hpEven.mul_right Q₁) hq₁Odd
    have hquotOdd : Odd (A / e) := by
      rw [← Nat.not_even_iff_odd]
      intro hquotEven
      apply (Nat.not_even_iff_odd.mpr hAOdd)
      rw [← hfactor]
      exact hquotEven.mul_left e
    rw [hnormal.1]
    exact hquotOdd

/-- The three-channel window excludes every small reduced numerator at a
hypothetical final skip.  Numerator `2` would be the already-forbidden
Mersenne exceptional coordinate; numerator `3` would force an even
denominator, contradicting the odd-denominator orbit invariant. -/
theorem lastTwentyOneSkip_remainder_num_ge_four
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    4 ≤
      (greedyMersenneRemainderRat
        (1 / 21 : ℚ) (M - 1)).num.natAbs := by
  rcases M with _ | m
  · exact False.elim
      (zero_not_mem_greedyMersenneSkippedSupport (1 / 21 : ℝ) hlast.1)
  · let x := greedyMersenneRemainderRat (1 / 21 : ℚ) m
    let p := x.num.natAbs
    let q := x.den
    let T := 2 ^ (m + 1)
    let delta := p * T - q
    have hwindow :
        p < 3 * delta ∧ delta < p := by
      simpa only [Nat.succ_sub_one, x, p, q, T, delta] using
        lastTwentyOneSkip_dyadicExcess_window hlast
    have hdeltaPos : 0 < delta := by omega
    have hqpt : q < p * T := by
      exact (Nat.sub_pos_iff_lt).mp
        (by simpa only [delta] using hdeltaPos)
    have hdeltaEq : delta + q = p * T := by
      simpa only [delta, Nat.add_comm] using Nat.sub_add_cancel hqpt.le
    have hqOdd : Odd q := by
      simpa only [q, x] using greedyTwentyOneRemainderRat_den_odd m
    have hTeven : Even T := by
      rw [even_iff_two_dvd]
      simpa only [T] using dvd_pow_self 2 (by omega : m + 1 ≠ 0)
    by_contra hnot
    have hpNot : ¬ 4 ≤ p := by
      simpa only [Nat.succ_sub_one, x, p] using hnot
    have hpLe : p ≤ 3 := by omega
    interval_cases hpCase : p
    · omega
    · omega
    · have hdeltaOne : delta = 1 := by omega
      have hqException : q = 2 ^ (m + 2) - 1 := by
        dsimp only [T] at hdeltaEq
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
        omega
      exact
        (greedyTwentyOneResidual_not_mersenneException m)
          ⟨by simpa only [x, p] using hpCase,
            by simpa only [x, q] using hqException⟩
    · have hdeltaTwo : delta = 2 := by omega
      have hqEven : Even q := by
        obtain ⟨k, hk⟩ := hTeven
        refine ⟨3 * k - 1, ?_⟩
        omega
      exact (Nat.not_even_iff_odd.mpr hqOdd) hqEven

/-- Parity-sensitive cancellation in a reduced dyadic excess window.
Suppose `delta + q = p*T`, with `T` even, `q` and `delta` odd, and
`p/3 < delta < p`.  If `p` is odd, the predecessor gcd divides the
even error `p-delta`, so its odd part is smaller than one third of `p`.
If `p` is even, the successor gcd divides twice the distance from
`delta` to `p/2`; coprimality excludes zero distance, so it is smaller
than one half of `p`. -/
theorem dyadicExcess_adjacent_gcd_parity
    {p q T delta : ℕ}
    (hTpos : 0 < T) (hqOdd : Odd q) (hdeltaOdd : Odd delta)
    (hcop : p.Coprime q)
    (hbalance : delta + q = p * T)
    (hlower : p < 3 * delta) (hupper : delta < p)
    (hp4 : 4 ≤ p) :
    (Odd p → 3 * Nat.gcd q (T - 1) < p) ∧
      (Even p → 2 * Nat.gcd q (2 * T - 1) < p) := by
  let D := T - 1
  have hDsucc : D + 1 = T := by
    simpa only [D] using Nat.sub_add_cancel hTpos
  have hsplit : p * T = p * D + p := by
    rw [← hDsucc]
    ring
  have hdeltaPos : 0 < delta := by omega
  constructor
  · intro hpOdd
    let epsilon := p - delta
    let g := Nat.gcd q D
    have hepsilonPos : 0 < epsilon := by
      simpa only [epsilon] using Nat.sub_pos_of_lt hupper
    have hepsilonAdd : epsilon + p * D = q := by
      dsimp only [epsilon]
      omega
    have hgq : g ∣ q := Nat.gcd_dvd_left q D
    have hgD : g ∣ D := Nat.gcd_dvd_right q D
    have hgpD : g ∣ p * D := dvd_mul_of_dvd_right hgD p
    have hgepsilon : g ∣ epsilon := by
      have hdvd : g ∣ q - p * D := Nat.dvd_sub hgq hgpD
      have heq : q - p * D = epsilon := by omega
      rwa [heq] at hdvd
    have hgOdd : Odd g := hqOdd.of_dvd_nat hgq
    have hepsilonEven : Even epsilon := by
      simpa only [epsilon] using Nat.Odd.sub_odd hpOdd hdeltaOdd
    obtain ⟨k, hk⟩ := hepsilonEven
    have hgTwoK : g ∣ 2 * k := by
      simpa only [hk, two_mul] using hgepsilon
    have hgk : g ∣ k :=
      hgOdd.coprime_two_right.dvd_of_dvd_mul_left hgTwoK
    have hkPos : 0 < k := by omega
    have hgLe : g ≤ k := Nat.le_of_dvd hkPos hgk
    have hthreeEpsilon : 3 * epsilon < 2 * p := by
      dsimp only [epsilon]
      omega
    have hthreeK : 3 * k < p := by omega
    simpa only [g, D] using (show 3 * g < p by omega)
  · intro hpEven
    obtain ⟨k, hk⟩ := hpEven
    let Q := 2 * T - 1
    let g := Nat.gcd q Q
    have hQsucc : Q + 1 = 2 * T := by
      simpa only [Q] using Nat.sub_add_cancel (by omega : 0 < 2 * T)
    have hQform : Q = 2 * D + 1 := by
      rw [← hDsucc] at hQsucc
      omega
    have hgq : g ∣ q := Nat.gcd_dvd_left q Q
    have hgQ : g ∣ Q := Nat.gcd_dvd_right q Q
    have hgOdd : Odd g := hqOdd.of_dvd_nat hgq
    have hgtwoq : g ∣ 2 * q := dvd_mul_of_dvd_right hgq 2
    have hgpQ : g ∣ p * Q := dvd_mul_of_dvd_right hgQ p
    have hQbalance : p * Q + p = 2 * q + 2 * delta := by
      calc
        p * Q + p = p * (Q + 1) := by ring
        _ = p * (2 * T) := by rw [hQsucc]
        _ = 2 * (p * T) := by ring
        _ = 2 * (delta + q) := by rw [hbalance]
        _ = 2 * q + 2 * delta := by ring
    have hdeltaNe : delta ≠ k := by
      intro heq
      have hkDvdP : k ∣ p := by
        refine ⟨2, ?_⟩
        omega
      have hqEq : q = k * Q := by
        apply Nat.add_right_cancel (m := k)
        calc
          q + k = delta + q := by rw [heq]; omega
          _ = p * T := hbalance
          _ = (k + k) * T := by rw [hk]
          _ = k * (2 * T) := by ring
          _ = k * (Q + 1) := by rw [hQsucc]
          _ = k * Q + k := by ring
      have hkDvdQ : k ∣ q := ⟨Q, hqEq⟩
      have hkOne : k = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hkDvdP hkDvdQ
      omega
    rcases lt_or_gt_of_ne hdeltaNe with hdeltaLt | hkLt
    · let e := k - delta
      have hePos : 0 < e := by
        simpa only [e] using Nat.sub_pos_of_lt hdeltaLt
      have hdiff : 2 * q - p * Q = 2 * e := by
        dsimp only [e]
        omega
      have hgeTwo : g ∣ 2 * e := by
        have hdvd : g ∣ 2 * q - p * Q :=
          Nat.dvd_sub hgtwoq hgpQ
        rwa [hdiff] at hdvd
      have hge : g ∣ e :=
        hgOdd.coprime_two_right.dvd_of_dvd_mul_left hgeTwo
      have hgLe : g ≤ e := Nat.le_of_dvd hePos hge
      have heLt : e < k := by
        dsimp only [e]
        omega
      simpa only [g, Q, hk] using (show 2 * g < p by omega)
    · let e := delta - k
      have hePos : 0 < e := by
        simpa only [e] using Nat.sub_pos_of_lt hkLt
      have hdiff : p * Q - 2 * q = 2 * e := by
        dsimp only [e]
        omega
      have hgeTwo : g ∣ 2 * e := by
        have hdvd : g ∣ p * Q - 2 * q :=
          Nat.dvd_sub hgpQ hgtwoq
        rwa [hdiff] at hdvd
      have hge : g ∣ e :=
        hgOdd.coprime_two_right.dvd_of_dvd_mul_left hgeTwo
      have hgLe : g ≤ e := Nat.le_of_dvd hePos hge
      have heLt : e < k := by
        dsimp only [e]
        omega
      simpa only [g, Q, hk] using (show 2 * g < p by omega)

/-- At a hypothetical final denominator-`21` skip, parity decides which
adjacent Mersenne denominator has a quantitatively small common factor
with the reduced residual denominator.  Odd numerator gives a one-third
predecessor bound; even numerator gives a one-half successor bound. -/
theorem lastTwentyOneSkip_adjacent_gcd_parity
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    let x := greedyMersenneRemainderRat (1 / 21 : ℚ) (M - 1)
    (Odd x.num.natAbs →
        3 * Nat.gcd x.den (2 ^ M - 1) < x.num.natAbs) ∧
      (Even x.num.natAbs →
        2 * Nat.gcd x.den (2 ^ (M + 1) - 1) < x.num.natAbs) := by
  rcases M with _ | m
  · exact False.elim
      (zero_not_mem_greedyMersenneSkippedSupport (1 / 21 : ℝ) hlast.1)
  · dsimp only [Nat.succ_sub_one]
    let x := greedyMersenneRemainderRat (1 / 21 : ℚ) m
    let p := x.num.natAbs
    let q := x.den
    let T := 2 ^ (m + 1)
    let delta := p * T - q
    have hwindow :
        p < 3 * delta ∧ delta < p := by
      simpa only [Nat.succ_sub_one, x, p, q, T, delta] using
        lastTwentyOneSkip_dyadicExcess_window hlast
    have hdeltaPos : 0 < delta := by omega
    have hqpt : q < p * T := by
      exact (Nat.sub_pos_iff_lt).mp
        (by simpa only [delta] using hdeltaPos)
    have hbalance : delta + q = p * T := by
      simpa only [delta, Nat.add_comm] using Nat.sub_add_cancel hqpt.le
    have hqOdd : Odd q := by
      simpa only [q, x] using greedyTwentyOneRemainderRat_den_odd m
    have hTeven : Even T := by
      rw [even_iff_two_dvd]
      simpa only [T] using dvd_pow_self 2 (by omega : m + 1 ≠ 0)
    have hdeltaOdd : Odd delta := by
      rw [← Nat.not_even_iff_odd]
      intro hdeltaEven
      have hsumOdd : Odd (delta + q) := hdeltaEven.add_odd hqOdd
      rw [hbalance] at hsumOdd
      exact
        (Nat.not_even_iff_odd.mpr hsumOdd)
          (hTeven.mul_left p)
    have hcop : p.Coprime q := by
      simpa only [p, q, x] using x.reduced
    have hp4 : 4 ≤ p := by
      simpa only [Nat.succ_sub_one, x, p] using
        lastTwentyOneSkip_remainder_num_ge_four hlast
    have hgeneric :=
      dyadicExcess_adjacent_gcd_parity
        (p := p) (q := q) (T := T) (delta := delta)
        (by positivity) hqOdd hdeltaOdd hcop
        hbalance hwindow.1 hwindow.2 hp4
    have hpowNext : 2 ^ ((m + 1) + 1) = 2 * T := by
      rw [pow_succ]
      dsimp only [T]
      ring
    simpa only [Nat.succ_eq_add_one, x, p, q, T, hpowNext] using hgeneric

/-- A hypothetical final denominator-`21` skip is automatically a
dyadically unsafe skip.  The existing primitive-normalization theorem then
forces an exponential product across the reduced numerators immediately
before and after its forced successor take. -/
theorem lastTwentyOneSkip_unsafe_numeratorProduct_gt
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M) :
    2 ^ M - 1 <
      (greedyMersenneRemainderRat
          (1 / 21 : ℚ) (M - 1)).num.natAbs *
        (greedyMersenneRemainderRat
          (1 / 21 : ℚ) (M + 1)).num.natAbs := by
  rcases M with _ | m
  · exact False.elim
      (zero_not_mem_greedyMersenneSkippedSupport (1 / 21 : ℝ) hlast.1)
  · have hskipNot :
        ¬ mersenneWeight (m + 1) ≤
          greedyMersenneRemainder (1 / 21 : ℝ) m :=
      (succ_mem_greedyMersenneSkippedSupport_iff
        (1 / 21 : ℝ) m).1 hlast.1
    have hskipReal :
        greedyMersenneRemainder (1 / 21 : ℝ) m <
          mersenneWeight (m + 1) :=
      lt_of_not_ge hskipNot
    have hremSucc :
        greedyMersenneRemainder (1 / 21 : ℝ) (m + 1) =
          greedyMersenneRemainder (1 / 21 : ℝ) m := by
      rw [greedyMersenneRemainder_succ, if_neg hskipNot]
    have hcapTail :
        (1 / 2 : ℝ) ^ (m + 1) < mersenneTail (m + 1) := by
      exact
        (halfDyadicCap_le_halfTwoChannelCap (m + 1)).trans_lt
          (halfTwoChannelCap_lt_mersenneTail (m + 1))
    have hdyadicReal :
        (1 / 2 : ℝ) ^ (m + 1) <
          greedyMersenneRemainder (1 / 21 : ℝ) m := by
      calc
        (1 / 2 : ℝ) ^ (m + 1) < mersenneTail (m + 1) := hcapTail
        _ ≤ greedyMersenneRemainder (1 / 21 : ℝ) (m + 1) :=
          lastTwentyOneSkip_tail_le_remainder hlast
        _ = greedyMersenneRemainder (1 / 21 : ℝ) m := hremSucc
    have hdyadicRat :
        1 / (2 : ℚ) ^ (m + 1) <
          greedyMersenneRemainderRat (1 / 21 : ℚ) m := by
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa [div_pow] using hdyadicReal
    have hskipRat :
        greedyMersenneRemainderRat (1 / 21 : ℚ) m <
          mersenneWeightRat (m + 1) := by
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa using hskipReal
    simpa only [Nat.succ_sub_one, Nat.succ_add] using
      greedyTwentyOne_unsafeSkip_numeratorProduct_gt
        m hdyadicRat hskipRat

/-- If the reduced numerator before a hypothetical final skip is even,
the parity-sensitive successor-gcd bound removes at least twice as much
possible cancellation from the forced next take.  The basic numerator
product obstruction therefore gains a full factor of two. -/
theorem lastTwentyOneSkip_even_double_numeratorProduct_gt
    {M : ℕ} (hlast : IsLastTwentyOneGreedySkip M)
    (heven :
      Even
        (greedyMersenneRemainderRat
          (1 / 21 : ℚ) (M - 1)).num.natAbs) :
    2 * (2 ^ M - 1) <
      (greedyMersenneRemainderRat
          (1 / 21 : ℚ) (M - 1)).num.natAbs *
        (greedyMersenneRemainderRat
          (1 / 21 : ℚ) (M + 1)).num.natAbs := by
  rcases M with _ | m
  · exact False.elim
      (zero_not_mem_greedyMersenneSkippedSupport (1 / 21 : ℝ) hlast.1)
  · let x := greedyMersenneRemainderRat (1 / 21 : ℚ) m
    let Q := 2 ^ (m + 2) - 1
    let d := Nat.gcd x.den Q
    let q₁ := x.den / d
    let Q₁ := Q / d
    let A := x.num.natAbs * Q₁ - q₁
    let e := Nat.gcd A d
    let y := greedyMersenneRemainderRat (1 / 21 : ℚ) (m + 2)
    have hskipNot :
        ¬ mersenneWeight (m + 1) ≤
          greedyMersenneRemainder (1 / 21 : ℝ) m :=
      (succ_mem_greedyMersenneSkippedSupport_iff
        (1 / 21 : ℝ) m).1 hlast.1
    have hskipReal :
        greedyMersenneRemainder (1 / 21 : ℝ) m <
          mersenneWeight (m + 1) :=
      lt_of_not_ge hskipNot
    have hremSucc :
        greedyMersenneRemainder (1 / 21 : ℝ) (m + 1) =
          greedyMersenneRemainder (1 / 21 : ℝ) m := by
      rw [greedyMersenneRemainder_succ, if_neg hskipNot]
    have hcapTail :
        (1 / 2 : ℝ) ^ (m + 1) < mersenneTail (m + 1) := by
      exact
        (halfDyadicCap_le_halfTwoChannelCap (m + 1)).trans_lt
          (halfTwoChannelCap_lt_mersenneTail (m + 1))
    have hdyadicReal :
        (1 / 2 : ℝ) ^ (m + 1) <
          greedyMersenneRemainder (1 / 21 : ℝ) m := by
      calc
        (1 / 2 : ℝ) ^ (m + 1) < mersenneTail (m + 1) := hcapTail
        _ ≤ greedyMersenneRemainder (1 / 21 : ℝ) (m + 1) :=
          lastTwentyOneSkip_tail_le_remainder hlast
        _ = greedyMersenneRemainder (1 / 21 : ℝ) m := hremSucc
    have hdyadicRat :
        1 / (2 : ℚ) ^ (m + 1) < x := by
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa [x, div_pow] using hdyadicReal
    have hskipRat : x < mersenneWeightRat (m + 1) := by
      apply (Rat.cast_lt (K := ℝ)).mp
      simpa [x] using hskipReal
    have htwo :=
      greedyTwentyOne_unsafeSkip_nextResidual_twoStage
        m hdyadicRat hskipRat
    have hprod : 2 ^ (m + 1) - 1 < e * y.num.natAbs := by
      simpa only [x, Q, d, q₁, Q₁, A, e, y] using htwo.2.2
    have hdBound : 2 * d < x.num.natAbs := by
      have hparity :=
        (lastTwentyOneSkip_adjacent_gcd_parity hlast).2 heven
      simpa only [Nat.succ_sub_one, Nat.succ_eq_add_one, x, Q, d] using
        hparity
    have hdpos : 0 < d := by
      have hxden : 0 < x.den := Rat.den_pos x
      have hQpos : 0 < Q := by
        dsimp only [Q]
        exact pow_sub_one_pos_of_ne_zero 2 (m + 2) (by omega) (by omega)
      simpa only [d] using Nat.gcd_pos_of_pos_left Q hxden
    have hed : e ∣ d := Nat.gcd_dvd_right A d
    have heLeD : e ≤ d := Nat.le_of_dvd hdpos hed
    have htwoELe : 2 * e ≤ x.num.natAbs := by omega
    have hscaled :
        2 * (2 ^ (m + 1) - 1) <
          x.num.natAbs * y.num.natAbs := by
      calc
        2 * (2 ^ (m + 1) - 1) <
            2 * (e * y.num.natAbs) :=
          Nat.mul_lt_mul_of_pos_left hprod (by omega)
        _ = (2 * e) * y.num.natAbs := by ring
        _ ≤ x.num.natAbs * y.num.natAbs :=
          Nat.mul_le_mul_right y.num.natAbs htwoELe
    simpa only [Nat.succ_sub_one, Nat.succ_add, x, y] using hscaled

/-- Nonmembership supplies a final actual skip, not merely an arbitrary
finite fatal witness. -/
theorem exists_lastTwentyOneGreedySkip_of_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ∃ M : ℕ, IsLastTwentyOneGreedySkip M := by
  classical
  obtain ⟨_n, _R₀, _hfatal, hfinite, _hselected, _halign, _hhits⟩ :=
    twentyOneFatalAlignedBranch_of_not_mem hnot
  let F : Finset ℕ := hfinite.toFinset
  have h1F : 1 ∈ F := by
    simpa [F] using one_mem_greedyMersenneSkippedSupport_twentyOne
  have hFne : F.Nonempty := ⟨1, h1F⟩
  let M : ℕ := F.max' hFne
  have hMmemF : M ∈ F := Finset.max'_mem F hFne
  have hMskip :
      M ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ) := by
    simpa [F] using hMmemF
  refine ⟨M, hMskip, fun m hMm hmSkip => ?_⟩
  have hmF : m ∈ F := by
    simpa [F] using hmSkip
  exact (not_lt_of_ge (Finset.le_max' F m hmF)) hMm

/-- **Erdős--Borwein fatal-interval reduction.**  If the prescribed
rational point is not represented, one finite exact Mersenne shift
approximates the full Erdős--Borwein constant from above inside the sharp
gap at its greatest exponent. -/
theorem twentyOne_not_mem_forces_erdosBorwein_fatalInterval
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ∃ M : ℕ,
      IsLastTwentyOneGreedySkip M ∧
        0 <
          (1 / 21 : ℝ) +
              positiveMersenneSupportValue
                (↑(twentyOneSkippedPrefix M) : Set ℕ) -
            erdosBorweinMersenneConstant ∧
        (1 / 21 : ℝ) +
              positiveMersenneSupportValue
                (↑(twentyOneSkippedPrefix M) : Set ℕ) -
            erdosBorweinMersenneConstant <
          mersenneGap M := by
  obtain ⟨M, hlast⟩ := exists_lastTwentyOneGreedySkip_of_not_mem hnot
  exact
    ⟨M, hlast,
      (lastTwentyOneSkip_erdosBorwein_fatalInterval hlast).1,
      (lastTwentyOneSkip_erdosBorwein_fatalInterval hlast).2⟩

/-- Exact rational form of the fatal interval.  This is the form used by
any height-aware irrationality-measure or primitive-denominator argument:
the approximant is literally `1/21` plus a finite Mersenne sum, and its
greatest denominator exponent is the final actual skip. -/
theorem twentyOne_not_mem_forces_rational_erdosBorwein_fatalInterval
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ∃ M : ℕ,
      IsLastTwentyOneGreedySkip M ∧
        0 <
          (1 / 21 : ℝ) +
              ((finiteErdosSum (twentyOneSkippedPrefix M) 2 : ℚ) : ℝ) -
            erdosBorweinMersenneConstant ∧
        (1 / 21 : ℝ) +
              ((finiteErdosSum (twentyOneSkippedPrefix M) 2 : ℚ) : ℝ) -
            erdosBorweinMersenneConstant <
          mersenneGap M := by
  obtain ⟨M, hlast, hpos, hlt⟩ :=
    twentyOne_not_mem_forces_erdosBorwein_fatalInterval hnot
  have hshift :=
    positiveMersenneSupportValue_eq_cast_finiteErdosSum
      (twentyOneSkippedPrefix M)
  rw [hshift] at hpos hlt
  exact ⟨M, hlast, hpos, hlt⟩

/-- Non-membership eliminates the sole exceptional word in the actual
left-boundary correction theorem.  Past the fatal rank, both `K+1` and
`K+2` are selected; the exceptional word would select the former and skip
the latter.  Hence every sufficiently late left boundary has forcing depth
strictly larger than `K`.

This removes one of the two orientation-specific correction obstructions:
only the right-boundary long-selected-run case can survive. -/
theorem twentyOneEventualLeftCorrectionBoundaryAmplification_of_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ∃ K₀ : ℕ, ∀ K v q : ℕ, K₀ ≤ K → 3 ≤ K → Odd q →
      supportDyadicPrefixNumerator
          (greedyMersenneSupport (1 / 21 : ℝ)) (2 * K) =
        2 ^ v * q →
      K < 2 * K - v - 1 := by
  obtain ⟨n, _R₀, _hfatal, _hfinite, hselected, _halign, _hhits⟩ :=
    twentyOneFatalAlignedBranch_of_not_mem hnot
  refine ⟨n + 1, ?_⟩
  intro K v q hK₀ hK hq hprefix
  have hfirst :
      K + 1 ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
    convert hselected (K - n) using 1 <;> omega
  have hhit :
      ∃ m : ℕ, K < m ∧ m ≤ 2 * K ∧
        m ∈ greedyMersenneSupport (1 / 21 : ℝ) :=
    ⟨K + 1, by omega, by omega, hfirst⟩
  rcases
      correctionBoundary_left_valuation_lt_or_singleton_doublingBlock
        (greedyMersenneSupport (1 / 21 : ℝ)) K v q (by omega)
        hq hprefix hhit with
    hv | ⟨_hv, _hfirst, hrest⟩
  · exact ((crossedBoundary_forceDepth_gt_iff (by omega)).2 hv)
  · have hsecond :
        K + 2 ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
      convert hselected (K + 1 - n) using 1 <;> omega
    exact ((hrest (K + 2) (by omega) (by omega)) hsecond).elim

/-- The surviving right-boundary behavior has an exact, fixed ancestor.
Once the fatal branch starts selecting every exponent, adding one more
membership bit sends `P + 1` to `2 * (P + 1)`.  Thus the entire later
dyadic numerator is obtained by shifting the single numerator at the fatal
rank.

This is a negative result for the correction route: the right-boundary
long-selected-run alternative does not hide fresh depth growth.  Its
power-of-two factor grows only by appending the already-forced terminal
ones, so any contradiction must come from a different coordinate such as
the denominator-`21` defect. -/
theorem twentyOneFatalAlignedBranch_supportDyadicPrefix_factorization
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ n : ℕ, ∀ t : ℕ,
      supportDyadicPrefixNumerator
          (greedyMersenneSupport (1 / 21 : ℝ)) (n + t) + 1 =
        2 ^ t *
          (supportDyadicPrefixNumerator
            (greedyMersenneSupport (1 / 21 : ℝ)) n + 1) := by
  obtain ⟨n, _R₀, _hfatal, _hfinite, hselected, _halign, _hhits⟩ :=
    hbranch
  refine ⟨n, ?_⟩
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
      have hbit :
          supportMembershipBit
              (greedyMersenneSupport (1 / 21 : ℝ)) (n + t + 1) = 1 :=
        (supportMembershipBit_eq_one_iff
          (greedyMersenneSupport (1 / 21 : ℝ)) (n + t + 1)).2
            (hselected t)
      rw [show n + (t + 1) = (n + t) + 1 by omega]
      unfold supportDyadicPrefixNumerator at ih ⊢
      rw [binaryCoeffPrefixNumerator, hbit]
      calc
        2 *
              binaryCoeffPrefixNumerator
                (supportMembershipBit
                  (greedyMersenneSupport (1 / 21 : ℝ))) (n + t) +
              1 + 1 =
            2 *
              (binaryCoeffPrefixNumerator
                (supportMembershipBit
                  (greedyMersenneSupport (1 / 21 : ℝ))) (n + t) + 1) := by
            ring
        _ =
            2 *
              (2 ^ t *
                (binaryCoeffPrefixNumerator
                  (supportMembershipBit
                    (greedyMersenneSupport (1 / 21 : ℝ))) n + 1)) := by
            rw [ih]
        _ =
            2 ^ (t + 1) *
              (binaryCoeffPrefixNumerator
                (supportMembershipBit
                  (greedyMersenneSupport (1 / 21 : ℝ))) n + 1) := by
            rw [pow_succ]
            ring

/-- In particular, every sufficiently late right boundary carries all of
the power of two forced by the cofinite selected suffix. -/
theorem twentyOneFatalAlignedBranch_rightBoundary_power_dvd
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ n : ℕ, ∀ K : ℕ, n ≤ 2 * K →
      2 ^ (2 * K - n) ∣
        supportDyadicPrefixNumerator
          (greedyMersenneSupport (1 / 21 : ℝ)) (2 * K) + 1 := by
  obtain ⟨n, hfactor⟩ :=
    twentyOneFatalAlignedBranch_supportDyadicPrefix_factorization hbranch
  refine ⟨n, ?_⟩
  intro K hnK
  have h := hfactor (2 * K - n)
  rw [show n + (2 * K - n) = 2 * K by omega] at h
  exact ⟨
    supportDyadicPrefixNumerator
        (greedyMersenneSupport (1 / 21 : ℝ)) n + 1,
    h⟩

/-- The full-row condition: only the coarse strict-core ceiling remains.
The former exact-state exclusion has disappeared. -/
def TwentyOneEvenFullQuotientCoreBound : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    twentyOneEvenQuotientCoreRemainder R < 2 * 2 ^ R + 1

/-- The two finite rows below the preterminal range are exact, so the coarse
condition gives a uniform defect-three full row at every required depth. -/
theorem twentyOneEvenFullQuotientGreedyRemainder_le_three_of_coarseBound
    (hpre : TwentyOneEvenQuotientPreterminalCoarseBound) :
    ∀ R : ℕ, 2 ≤ R →
      twentyOneEvenFullQuotientGreedyRemainder R ≤ 3 := by
  intro R hR
  by_cases hR4 : 4 ≤ R
  · exact
      twentyOneEvenFullQuotientGreedyRemainder_le_three_of_preterminalBound
        hR4 (hpre R hR4)
  · obtain rfl | rfl : R = 2 ∨ R = 3 := by omega
    · have hweights : localMersenneWeights 4 4 = [5, 2, 1] := by
        rw [localMersenneWeights,
          localMersenneWeightsFrom_eq_cons (by omega : 2 ≤ 4),
          localMersenneWeightsFrom_eq_cons (by omega : 3 ≤ 4),
          localMersenneWeightsFrom_eq_cons (by omega : 4 ≤ 4),
          localMersenneWeightsFrom_eq_nil (by omega : 4 < 5)]
        norm_num [localMersenneQuotient]
      unfold twentyOneEvenFullQuotientGreedyRemainder
      rw [hweights]
      norm_num [twentyOneQuotientTarget, integerGreedyRemainder,
        integerGreedyBits, weightedBoolSum]
    · have hweights : localMersenneWeights 6 6 = [21, 9, 4, 2, 1] := by
        rw [localMersenneWeights,
          localMersenneWeightsFrom_eq_cons (by omega : 2 ≤ 6),
          localMersenneWeightsFrom_eq_cons (by omega : 3 ≤ 6),
          localMersenneWeightsFrom_eq_cons (by omega : 4 ≤ 6),
          localMersenneWeightsFrom_eq_cons (by omega : 5 ≤ 6),
          localMersenneWeightsFrom_eq_cons (by omega : 6 ≤ 6),
          localMersenneWeightsFrom_eq_nil (by omega : 6 < 7)]
        norm_num [localMersenneQuotient]
      unfold twentyOneEvenFullQuotientGreedyRemainder
      rw [hweights]
      norm_num [twentyOneQuotientTarget, integerGreedyRemainder,
        integerGreedyBits, weightedBoolSum]

/-- **Bounded full-row endpoint.**  A uniform defect bound of three already
puts `1/21` in the achievement set.  The constant is deliberately the one
needed by the terminal-fringe absorption below; after normalization by
`4^R`, it is as harmless as defect one. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_fullGreedyRemainder_le_three
    (hfull : ∀ R : ℕ, 2 ≤ R →
      twentyOneEvenFullQuotientGreedyRemainder R ≤ 3) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  classical
  let D : ℕ → Finset ℕ :=
    fun R => twentyOneEvenFullQuotientGreedySupport (R + 2)
  let y : ℕ → ℝ :=
    fun R => ((localMersennePrefixValue (D R) : ℚ) : ℝ)
  have hshift : Tendsto (fun R : ℕ => R + 2) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat 2
  have hdist :
      Tendsto (fun R : ℕ => dist (y R) (1 / 21 : ℝ))
        atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => dist_nonneg)
      (Filter.Eventually.of_forall fun R => ?_)
      (tendsto_twentyOne_evenQuotientWindow_error.comp hshift)
    rw [Real.dist_eq]
    calc
      |y R - (1 / 21 : ℝ)| ≤
          ((twentyOneQuotientDefect (D R) (2 * (R + 2)) +
              (D R).card + 1 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * (R + 2)) := by
        exact abs_localMersennePrefixValue_sub_one_div_twenty_one_le
          (fun d hd =>
            (twentyOneEvenFullQuotientGreedySupport_mem_bounds
              (R := R + 2) (d := d) (by simpa [D] using hd)).1)
          (by
            simpa [D] using
              localPrefixQuotient_twentyOneEvenFullGreedySupport_le
                (R := R + 2) (by omega))
      _ ≤
          (((2 ^ (R + 2) + (2 * (R + 2) + 1) : ℕ) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * (R + 2)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hcard : (D R).card ≤ 2 * (R + 2) - 1 := by
          have hsubset : D R ⊆ Finset.Icc 2 (2 * (R + 2)) := by
            intro d hd
            simp only [Finset.mem_Icc]
            exact
              twentyOneEvenFullQuotientGreedySupport_mem_bounds
                (R := R + 2) (d := d) (by simpa [D] using hd)
          calc
            (D R).card ≤ (Finset.Icc 2 (2 * (R + 2))).card :=
              Finset.card_le_card hsubset
            _ = 2 * (R + 2) - 1 := by simp
        have hdefect :
            twentyOneQuotientDefect (D R) (2 * (R + 2)) ≤ 3 := by
          rw [show D R =
              twentyOneEvenFullQuotientGreedySupport (R + 2) by rfl,
            twentyOneQuotientDefect_fullGreedySupport (by omega)]
          exact hfull (R + 2) (by omega)
        have hpow : 4 ≤ 2 ^ (R + 2) := by
          simpa using
            (Nat.pow_le_pow_right (by norm_num : 0 < 2)
              (show 2 ≤ R + 2 by omega))
        exact_mod_cast (by omega :
          twentyOneQuotientDefect (D R) (2 * (R + 2)) +
              (D R).card + 1 ≤
            2 ^ (R + 2) + (2 * (R + 2) + 1))
  have hy : Tendsto y atTop (nhds (1 / 21 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hyMem : ∀ R : ℕ, y R ∈ mersenneAchievementSet := by
    intro R
    let A : Set ℕ := ↑(D R)
    have hA0 : 0 ∉ A := by
      intro hzero
      have hbound :=
        twentyOneEvenFullQuotientGreedySupport_mem_bounds
          (R := R + 2) (d := 0) (by simpa [A, D] using hzero)
      omega
    refine ⟨A, hA0, ?_⟩
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [y, D, localMersennePrefixValue_eq_finiteErdosSum]
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

/-- **Full-row quotient endpoint.**  A coarse factor-two core ceiling is
enough to put `1/21` in the achievement set.  The complete binary suffix
absorbs the old exceptional state with defect at most one, and the finite
full rows converge without any coherence assumption. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_fullQuotientCoreBound
    (hcore : TwentyOneEvenFullQuotientCoreBound) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply
    one_div_twenty_one_mem_mersenneAchievementSet_of_fullGreedyRemainder_le_three
  intro R hR
  exact
    (twentyOneEvenFullQuotientGreedyRemainder_le_one_of_coreBound
      hR (hcore R hR)).trans (by omega)

/-- **Six-state-free quotient endpoint.**  The preterminal twice-last-coin
ceiling alone proves membership.  No equality exclusion survives: the full
binary suffix absorbs every constant-width fringe state with defect at most
three. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_preterminalCoarseBound
    (hpre : TwentyOneEvenQuotientPreterminalCoarseBound) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  one_div_twenty_one_mem_mersenneAchievementSet_of_fullGreedyRemainder_le_three
    (twentyOneEvenFullQuotientGreedyRemainder_le_three_of_coarseBound hpre)

/-- Every decoded greedy rank lies in the prescribed lower window. -/
theorem twentyOneEvenQuotientGreedySupport_mem_bounds
    {R d : ℕ} (hd : d ∈ twentyOneEvenQuotientGreedySupport R) :
    2 ≤ d ∧ d ≤ R := by
  unfold twentyOneEvenQuotientGreedySupport at hd
  have hbounds := lowerSupportFromBits_mem_bounds hd
  have hlen := integerGreedyBits_length
    (localMersenneWeights (2 * R) R)
    (twentyOneQuotientTarget (2 * R))
  simp only [localMersenneWeights_length] at hlen
  omega

/-- The decoded quotient and the deterministic remainder exactly partition
the denominator-`21` target. -/
theorem localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder
    {R : ℕ} (hR : 2 ≤ R) :
    localPrefixQuotient (twentyOneEvenQuotientGreedySupport R) (2 * R) +
        twentyOneEvenQuotientGreedyRemainder R =
      twentyOneQuotientTarget (2 * R) := by
  let weights := localMersenneWeights (2 * R) R
  let C := twentyOneQuotientTarget (2 * R)
  let bits := integerGreedyBits weights C
  have hlen : bits.length = R - 1 := by
    simpa [bits, weights] using integerGreedyBits_length weights C
  have hlen' : bits.length = R + 1 - 2 := by omega
  have hdecode :=
    localPrefixQuotient_lowerSupportFromBits
      (M := 2 * R) (R := R) (d := 2) (bits := bits) hlen'
  have hadm := integerGreedyBits_admissible weights C
  have hadm' : weightedBoolSum weights bits ≤ C := by
    simpa [bits] using hadm
  have hpartition :
      weightedBoolSum weights bits + integerGreedyRemainder weights C = C := by
    unfold integerGreedyRemainder
    change weightedBoolSum weights bits +
        (C - weightedBoolSum weights bits) = C
    omega
  change localPrefixQuotient (lowerSupportFromBits 2 bits) (2 * R) +
      integerGreedyRemainder weights C = C
  rw [hdecode]
  exact hpartition

/-- Full alignment at horizon `R+1` already fixes the quotient-greedy word
through rank `R` to the exact rational prefix.  This is the prefix identity
needed before exposing the final boundary decision. -/
theorem twentyOneSuccessorQuotientPrefixSupport_eq_greedyMersennePrefixRat
    {R : ℕ} (hR : 2 ≤ R)
    (halignSucc :
      integerGreedyBits
          (localMersenneWeights (2 * (R + 1)) (2 * (R + 1)))
          (twentyOneQuotientTarget (2 * (R + 1))) =
        rationalMersenneGreedyBitsFrom 2
          (2 * (R + 1) - 1) (1 / 21 : ℚ)) :
    lowerSupportFromBits 2
        (integerGreedyBits
          (localMersenneWeights (2 * (R + 1)) R)
          (twentyOneQuotientTarget (2 * (R + 1)))) =
      greedyMersennePrefixRat (1 / 21 : ℚ) R := by
  have hsplit :
      localMersenneWeights (2 * (R + 1)) (2 * (R + 1)) =
        localMersenneWeights (2 * (R + 1)) R ++
          localMersenneWeightsFrom
            (2 * (R + 1)) (2 * (R + 1)) (R + 1) := by
    unfold localMersenneWeights
    exact localMersenneWeightsFrom_split (by omega) (by omega)
  have hprefixQ :
      (integerGreedyBits
          (localMersenneWeights (2 * (R + 1)) (2 * (R + 1)))
          (twentyOneQuotientTarget (2 * (R + 1)))).take (R - 1) =
        integerGreedyBits
          (localMersenneWeights (2 * (R + 1)) R)
          (twentyOneQuotientTarget (2 * (R + 1))) := by
    rw [hsplit, integerGreedyBits_append]
    have hlen :
        (integerGreedyBits
            (localMersenneWeights (2 * (R + 1)) R)
            (twentyOneQuotientTarget (2 * (R + 1)))).length =
          R - 1 := by
      rw [integerGreedyBits_length, localMersenneWeights_length]
    rw [← hlen]
    exact List.take_left
  have hcount : 2 * (R + 1) - 1 = (R - 1) + (R + 2) := by
    omega
  have hprefixRat :
      (rationalMersenneGreedyBitsFrom 2
          (2 * (R + 1) - 1) (1 / 21 : ℚ)).take (R - 1) =
        rationalMersenneGreedyBitsFrom 2 (R - 1) (1 / 21 : ℚ) := by
    rw [hcount]
    exact
      rationalMersenneGreedyBitsFrom_take
        2 (R - 1) (R + 2) (1 / 21 : ℚ)
  rw [← lowerSupportFromBits_rationalTwentyOne_eq_greedyMersennePrefixRat R]
  congr 1
  rw [← hprefixQ, halignSucc, hprefixRat]

/-- Once a full quotient row aligns with exact rational greedy, its lower
support is not merely pointwise compatible: it is the exact greedy
prefix through rank `R`. -/
theorem twentyOneEvenQuotientGreedySupport_eq_greedyMersennePrefixRat_of_fullAlignment
    {R : ℕ} (hR : 2 ≤ R)
    (halign :
      integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R)) =
        rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)) :
    twentyOneEvenQuotientGreedySupport R =
      greedyMersennePrefixRat (1 / 21 : ℚ) R := by
  classical
  ext d
  rw [mem_greedyMersennePrefixRat_iff_real_support]
  constructor
  · intro hd
    have hbounds := twentyOneEvenQuotientGreedySupport_mem_bounds hd
    have hactual :=
      (twentyOneEvenQuotientGreedySupport_mem_iff_of_fullAlignment
        hR hbounds.1 hbounds.2 halign).1 hd
    refine ⟨by omega, hbounds.2, ?_⟩
    norm_num at hactual ⊢
    exact hactual
  · rintro ⟨hd1, hdR, hactual⟩
    have hactualR :
        d ∈ greedyMersenneSupport (1 / 21 : ℝ) := by
      norm_num at hactual ⊢
      exact hactual
    have hd2 : 2 ≤ d := by
      by_contra hdnot
      have hdEq : d = 1 := by omega
      subst d
      have htake :=
        (succ_mem_greedyMersenneSupport_iff (1 / 21 : ℝ) 0).1
          (by simpa using hactualR)
      norm_num [greedyMersenneRemainder, mersenneWeight] at htake
    exact
      (twentyOneEvenQuotientGreedySupport_mem_iff_of_fullAlignment
        hR hd2 hdR halign).2 hactualR

/-- Aligned quotient supports inherit the exact rational greedy
undershoot.  The proof uses the nonnegative residual in the exact
rational telescoping identity, so it does not assume membership of the
infinite target. -/
theorem localMersennePrefixValue_twentyOneEvenQuotientGreedySupport_le_of_fullAlignment
    {R : ℕ} (hR : 2 ≤ R)
    (halign :
      integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R)) =
        rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)) :
    localMersennePrefixValue
        (twentyOneEvenQuotientGreedySupport R) ≤ (1 / 21 : ℚ) := by
  rw [
    twentyOneEvenQuotientGreedySupport_eq_greedyMersennePrefixRat_of_fullAlignment
      hR halign,
    localMersennePrefixValue_eq_finiteErdosSum]
  have hrem :=
    greedyMersenneRemainderRat_eq_sub_finiteErdosSum
      (1 / 21 : ℚ) R
  have hrem0 :=
    greedyMersenneRemainderRat_nonneg_of_nonneg
      (x := (1 / 21 : ℚ)) (by norm_num) R
  linarith

/-- Full alignment therefore supplies the exact nonnegative carry
inequality for the canonical lower state. -/
theorem localPrefixTwoStepPulse_twentyOneEvenQuotientGreedySupport_le_carry_of_fullAlignment
    {R : ℕ} (hR : 2 ≤ R)
    (halign :
      integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R)) =
        rationalMersenneGreedyBitsFrom 2 (2 * R - 1) (1 / 21 : ℚ)) :
    localPrefixTwoStepPulse
        (twentyOneEvenQuotientGreedySupport R) (2 * R) ≤
      4 * twentyOneEvenQuotientGreedyRemainder R +
        twentyOneTargetTwoStepPulse (2 * R) := by
  apply localPrefixTwoStepPulse_le_carry_of_prefix_le
  · intro d hd
    exact
      (twentyOneEvenQuotientGreedySupport_mem_bounds
        (R := R) (d := d) hd).1
  · exact
      localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder hR
  · exact
      localMersennePrefixValue_twentyOneEvenQuotientGreedySupport_le_of_fullAlignment
        hR halign

/-- The fatal aligned branch has no eventual carry-sign obstruction.
Beyond one cutoff, the canonical lower quotient state always supplies a
genuine natural carry; only its upper closed-capacity bound can still fail. -/
theorem twentyOneFatalAlignedBranch_eventually_canonical_carry_nonneg
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      localPrefixTwoStepPulse
          (twentyOneEvenQuotientGreedySupport R) (2 * R) ≤
        4 * twentyOneEvenQuotientGreedyRemainder R +
          twentyOneTargetTwoStepPulse (2 * R) := by
  obtain
      ⟨_n, R₀, _hfatal, _hfinite, _hselected, halign, _hhits⟩ :=
    hbranch
  refine ⟨max R₀ 2, ?_⟩
  intro R hKR
  apply
    localPrefixTwoStepPulse_twentyOneEvenQuotientGreedySupport_le_carry_of_fullAlignment
      (by
        have := (le_max_right R₀ 2).trans hKR
        omega)
  exact halign R ((le_max_left R₀ 2).trans hKR)

/-- Consecutive full quotient/rational alignment turns the canonical lower
support into the exact one-bit boundary recurrence.  In particular, the
apparently horizon-dependent quotient-greedy rows are a genuine
one-dimensional state machine on the surviving branch. -/
theorem twentyOneEvenQuotientGreedySupport_succ_eq_boundary_of_fullAlignment
    {R : ℕ} (hR : 2 ≤ R)
    (halign :
      integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R)) =
        rationalMersenneGreedyBitsFrom 2
          (2 * R - 1) (1 / 21 : ℚ))
    (halignSucc :
      integerGreedyBits
          (localMersenneWeights (2 * (R + 1)) (2 * (R + 1)))
          (twentyOneQuotientTarget (2 * (R + 1))) =
        rationalMersenneGreedyBitsFrom 2
          (2 * (R + 1) - 1) (1 / 21 : ℚ)) :
    twentyOneEvenQuotientGreedySupport (R + 1) =
      twentyOneBoundaryLowerSupport
        (twentyOneEvenQuotientGreedySupport R) R
        (4 * twentyOneEvenQuotientGreedyRemainder R +
          twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse
              (twentyOneEvenQuotientGreedySupport R) (2 * R)) := by
  let D := twentyOneEvenQuotientGreedySupport R
  let s := twentyOneEvenQuotientGreedyRemainder R
  let M := 2 * (R + 1)
  let T := twentyOneQuotientTarget M
  let xs := localMersenneWeights M R
  let bits := integerGreedyBits xs T
  let C :=
    4 * s + twentyOneTargetTwoStepPulse (2 * R) -
      localPrefixTwoStepPulse D (2 * R)
  have hDprefix :
      D = greedyMersennePrefixRat (1 / 21 : ℚ) R := by
    dsimp [D]
    exact
      twentyOneEvenQuotientGreedySupport_eq_greedyMersennePrefixRat_of_fullAlignment
        hR halign
  have hbitsSupport :
      lowerSupportFromBits 2 bits =
        greedyMersennePrefixRat (1 / 21 : ℚ) R := by
    dsimp [bits, xs, T, M]
    exact
      twentyOneSuccessorQuotientPrefixSupport_eq_greedyMersennePrefixRat
        hR halignSucc
  have hsupport : lowerSupportFromBits 2 bits = D := by
    rw [hbitsSupport, hDprefix]
  have hlen : bits.length = R - 1 := by
    dsimp [bits, xs]
    rw [integerGreedyBits_length, localMersenneWeights_length]
  have hlen' : bits.length = R + 1 - 2 := by omega
  have hdecode :
      localPrefixQuotient (lowerSupportFromBits 2 bits) M =
        weightedBoolSum xs bits := by
    dsimp [xs]
    exact
      localPrefixQuotient_lowerSupportFromBits
        (M := M) (R := R) (d := 2) (bits := bits) hlen'
  have hrow :
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R) := by
    dsimp [D, s]
    exact
      localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder hR
  have hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * s + twentyOneTargetTwoStepPulse (2 * R) := by
    dsimp [D, s]
    exact
      localPrefixTwoStepPulse_twentyOneEvenQuotientGreedySupport_le_carry_of_fullAlignment
        hR halign
  have hcarry :
      T - localPrefixQuotient D M = C := by
    dsimp [T, M, C]
    exact
      twentyOneUpperExtensionCarry_eq
        (D := D) (R := R) (b := s)
        (fun d hd ↦
          (twentyOneEvenQuotientGreedySupport_mem_bounds
            (R := R) (d := d) (by simpa [D] using hd)).1)
        hrow hpulse
  have hrem : integerGreedyRemainder xs T = C := by
    unfold integerGreedyRemainder
    rw [← hdecode, hsupport]
    exact hcarry
  have hweights :
      localMersenneWeights M (R + 1) =
        xs ++ [2 ^ (R + 1) + 1] := by
    dsimp [xs]
    calc
      localMersenneWeights M (R + 1) =
          localMersenneWeights M R ++
            localMersenneWeightsFrom M (R + 1) (R + 1) := by
        unfold localMersenneWeights
        exact localMersenneWeightsFrom_split (by omega) (by omega)
      _ = localMersenneWeights M R ++
            [localMersenneQuotient M (R + 1)] := by
        rw [localMersenneWeightsFrom_eq_cons (by omega),
          localMersenneWeightsFrom_eq_nil (by omega)]
      _ = localMersenneWeights M R ++ [2 ^ (R + 1) + 1] := by
        rw [show M = 2 * (R + 1) by rfl,
          localMersenneQuotient_two_mul_self (by omega)]
  unfold twentyOneEvenQuotientGreedySupport
  change
    lowerSupportFromBits 2
        (integerGreedyBits
          (localMersenneWeights M (R + 1)) T) =
      twentyOneBoundaryLowerSupport D R C
  rw [hweights, integerGreedyBits_append, hrem]
  have hsupport' :
      lowerSupportFromBits 2 (integerGreedyBits xs T) = D := by
    simpa [bits] using hsupport
  have hlen'' : (integerGreedyBits xs T).length = R - 1 := by
    simpa [bits] using hlen
  have hindex :
      2 + (integerGreedyBits xs T).length = R + 1 := by
    rw [hlen'']
    omega
  by_cases htake : 2 ^ (R + 1) + 1 ≤ C
  · have htail :
        integerGreedyBits [2 ^ (R + 1) + 1] C = [true] := by
      simp [integerGreedyBits, htake]
    rw [htail, lowerSupportFromBits_append_singleton]
    rw [hsupport']
    simp [twentyOneBoundaryLowerSupport, htake, hindex]
  · have htail :
        integerGreedyBits [2 ^ (R + 1) + 1] C = [false] := by
      simp [integerGreedyBits, htake]
    rw [htail, lowerSupportFromBits_append_singleton]
    rw [hsupport']
    simp [twentyOneBoundaryLowerSupport, htake]

/-- Consecutive full alignment also identifies the canonical scalar
remainder with the one-dimensional boundary update.  Together with the
preceding support theorem, this removes all horizon dependence from the
surviving denominator-`21` dynamics. -/
theorem twentyOneEvenQuotientGreedyRemainder_succ_eq_boundary_of_fullAlignment
    {R : ℕ} (hR : 2 ≤ R)
    (halign :
      integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R)) =
        rationalMersenneGreedyBitsFrom 2
          (2 * R - 1) (1 / 21 : ℚ))
    (halignSucc :
      integerGreedyBits
          (localMersenneWeights (2 * (R + 1)) (2 * (R + 1)))
          (twentyOneQuotientTarget (2 * (R + 1))) =
        rationalMersenneGreedyBitsFrom 2
          (2 * (R + 1) - 1) (1 / 21 : ℚ)) :
    twentyOneEvenQuotientGreedyRemainder (R + 1) =
      twentyOneBoundaryScalarState R
        (4 * twentyOneEvenQuotientGreedyRemainder R +
          twentyOneTargetTwoStepPulse (2 * R) -
            localPrefixTwoStepPulse
              (twentyOneEvenQuotientGreedySupport R) (2 * R)) := by
  let D := twentyOneEvenQuotientGreedySupport R
  let s := twentyOneEvenQuotientGreedyRemainder R
  let C :=
    4 * s + twentyOneTargetTwoStepPulse (2 * R) -
      localPrefixTwoStepPulse D (2 * R)
  have hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ R := by
    intro d hd
    exact
      twentyOneEvenQuotientGreedySupport_mem_bounds
        (R := R) (d := d) (by simpa [D] using hd)
  have hrow :
      localPrefixQuotient D (2 * R) + s =
        twentyOneQuotientTarget (2 * R) := by
    dsimp [D, s]
    exact
      localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder hR
  have hpulse :
      localPrefixTwoStepPulse D (2 * R) ≤
        4 * s + twentyOneTargetTwoStepPulse (2 * R) := by
    dsimp [D, s]
    exact
      localPrefixTwoStepPulse_twentyOneEvenQuotientGreedySupport_le_carry_of_fullAlignment
        hR halign
  have hnext :
      localPrefixQuotient D (2 * (R + 1)) + C =
        twentyOneQuotientTarget (2 * (R + 1)) := by
    dsimp [C]
    rw [show 2 * (R + 1) = 2 * R + 2 by omega,
      twentyOneQuotientTarget_add_two,
      localPrefixQuotient_add_two (fun d hd ↦ (hD d hd).1)]
    omega
  have hboundary :=
    localPrefixQuotient_boundaryLowerSupport_add_scalar
      (D := D) (R := R) (C := C) (by omega) hD
  have hcanonical :=
    localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder
      (R := R + 1) (by omega)
  have hsupport :=
    twentyOneEvenQuotientGreedySupport_succ_eq_boundary_of_fullAlignment
      hR halign halignSucc
  change
    twentyOneEvenQuotientGreedyRemainder (R + 1) =
      twentyOneBoundaryScalarState R C
  change
    twentyOneEvenQuotientGreedySupport (R + 1) =
      twentyOneBoundaryLowerSupport D R C at hsupport
  rw [hsupport] at hcanonical
  omega

/-- Consecutive exact alignment binds the abstract saturated-escape
classifier to the canonical denominator-`21` row.  Hence any aligned first
crossing above capacity has a concrete missing greedy ancestor at one-third
or two-thirds scale. -/
theorem
    twentyOneAlignedSaturatedCrossing_forces_canonical_ancestor_hole
    {R : ℕ} (hR : 2 ≤ R)
    (halign :
      integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R)) =
        rationalMersenneGreedyBitsFrom 2
          (2 * R - 1) (1 / 21 : ℚ))
    (halignSucc :
      integerGreedyBits
          (localMersenneWeights (2 * (R + 1)) (2 * (R + 1)))
          (twentyOneQuotientTarget (2 * (R + 1))) =
        rationalMersenneGreedyBitsFrom 2
          (2 * (R + 1) - 1) (1 / 21 : ℚ))
    (hsaturated :
      twentyOneEvenQuotientGreedyRemainder R = 2 ^ R)
    (hcross :
      2 ^ (R + 1) <
        twentyOneEvenQuotientGreedyRemainder (R + 1)) :
    ∃ a : ℕ,
      R = 3 * a + 2 ∧
        (a + 1 ∉ twentyOneEvenQuotientGreedySupport R ∨
          2 * (a + 1) ∉ twentyOneEvenQuotientGreedySupport R) := by
  have hstep :=
    twentyOneEvenQuotientGreedyRemainder_succ_eq_boundary_of_fullAlignment
      hR halign halignSucc
  apply
    twentyOneSaturatedBoundary_crossing_forces_ancestor_hole
      (D := twentyOneEvenQuotientGreedySupport R)
      (s := twentyOneEvenQuotientGreedyRemainder R)
      hsaturated
  rw [← hstep]
  exact hcross

/-- An aligned supercapacity entrance produces a genuine omitted exponent in
the real denominator-`21` greedy orbit, not merely a hole in the auxiliary
quotient word.  Moreover that exponent is at the same scale as the entrance:

`d ≤ R ≤ 3d`.

The universal skip estimate therefore makes the Boolean--Möbius defect at
that ancestor only square-root sized.  This is the quantitative descent
bridge between the quotient escape and the Lambert carry orbit. -/
theorem
    twentyOneAlignedSaturatedCrossing_forces_scaled_greedy_skip
    {R : ℕ} (hR : 5 ≤ R)
    (halign :
      integerGreedyBits
          (localMersenneWeights (2 * R) (2 * R))
          (twentyOneQuotientTarget (2 * R)) =
        rationalMersenneGreedyBitsFrom 2
          (2 * R - 1) (1 / 21 : ℚ))
    (halignSucc :
      integerGreedyBits
          (localMersenneWeights (2 * (R + 1)) (2 * (R + 1)))
          (twentyOneQuotientTarget (2 * (R + 1))) =
        rationalMersenneGreedyBitsFrom 2
          (2 * (R + 1) - 1) (1 / 21 : ℚ))
    (hsaturated :
      twentyOneEvenQuotientGreedyRemainder R = 2 ^ R)
    (hcross :
      2 ^ (R + 1) <
        twentyOneEvenQuotientGreedyRemainder (R + 1)) :
    ∃ d : ℕ,
      d ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ) ∧
        d ≤ R ∧ R ≤ 3 * d ∧
          (twentyOneGreedyDefect d : ℝ) <
            2 * Real.sqrt (d : ℝ) + 6 := by
  obtain ⟨a, hRa, haHole | htwoAHole⟩ :=
    twentyOneAlignedSaturatedCrossing_forces_canonical_ancestor_hole
      (by omega : 2 ≤ R) halign halignSucc hsaturated hcross
  · have ha2 : 2 ≤ a + 1 := by omega
    have haR : a + 1 ≤ R := by omega
    have hnot :
        a + 1 ∉ greedyMersenneSupport (1 / 21 : ℝ) := by
      intro haMem
      exact haHole
        ((twentyOneEvenQuotientGreedySupport_mem_iff_of_fullAlignment
          (R := R) (d := a + 1) (by omega) ha2 haR halign).2 haMem)
    have hskip :
        a + 1 ∈ greedyMersenneSkippedSupport (1 / 21 : ℝ) := by
      exact ⟨by omega, hnot⟩
    exact
      ⟨a + 1, hskip, haR, by omega,
        twentyOneGreedyDefect_lt_two_sqrt_add_six_of_skip hskip⟩
  · have htwoA2 : 2 ≤ 2 * (a + 1) := by omega
    have htwoAR : 2 * (a + 1) ≤ R := by omega
    have hnot :
        2 * (a + 1) ∉ greedyMersenneSupport (1 / 21 : ℝ) := by
      intro htwoAMem
      exact htwoAHole
        ((twentyOneEvenQuotientGreedySupport_mem_iff_of_fullAlignment
          (R := R) (d := 2 * (a + 1)) (by omega) htwoA2 htwoAR halign).2
            htwoAMem)
    have hskip :
        2 * (a + 1) ∈
          greedyMersenneSkippedSupport (1 / 21 : ℝ) := by
      exact ⟨by omega, hnot⟩
    exact
      ⟨2 * (a + 1), hskip, htwoAR, by omega,
        twentyOneGreedyDefect_lt_two_sqrt_add_six_of_skip hskip⟩

/-- On the fatal branch the horizon-indexed canonical rows eventually become
one exact non-autonomous state machine: the support appends precisely its
boundary decision and the scalar follows the matching boundary remainder.
The only remaining way this branch can survive is therefore an eventual
escape above the closed binary capacity, not loss of alignment or carry
sign. -/
theorem twentyOneFatalAlignedBranch_eventually_canonical_transition
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      twentyOneEvenQuotientGreedySupport (R + 1) =
          twentyOneBoundaryLowerSupport
            (twentyOneEvenQuotientGreedySupport R) R
            (4 * twentyOneEvenQuotientGreedyRemainder R +
              twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)) ∧
        twentyOneEvenQuotientGreedyRemainder (R + 1) =
          twentyOneBoundaryScalarState R
            (4 * twentyOneEvenQuotientGreedyRemainder R +
              twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)) := by
  obtain
      ⟨_n, R₀, _hfatal, _hfinite, _hselected, halign, _hhits⟩ :=
    hbranch
  refine ⟨max R₀ 2, ?_⟩
  intro R hKR
  have hR : 2 ≤ R := (le_max_right R₀ 2).trans hKR
  have hR₀ : R₀ ≤ R := (le_max_left R₀ 2).trans hKR
  have halignR := halign R hR₀
  have halignSucc := halign (R + 1) (by omega)
  exact
    ⟨twentyOneEvenQuotientGreedySupport_succ_eq_boundary_of_fullAlignment
        hR halignR halignSucc,
      twentyOneEvenQuotientGreedyRemainder_succ_eq_boundary_of_fullAlignment
        hR halignR halignSucc⟩

/-- The quotient row is admissible simply because greedy never overspends. -/
theorem localPrefixQuotient_twentyOneEvenQuotientGreedySupport_le
    {R : ℕ} (hR : 2 ≤ R) :
    localPrefixQuotient (twentyOneEvenQuotientGreedySupport R) (2 * R) ≤
      twentyOneQuotientTarget (2 * R) := by
  have hpartition :=
    localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder hR
  omega

/-- The abstract quotient defect is exactly the concrete greedy remainder. -/
theorem twentyOneQuotientDefect_greedySupport
    {R : ℕ} (hR : 2 ≤ R) :
    twentyOneQuotientDefect
        (twentyOneEvenQuotientGreedySupport R) (2 * R) =
      twentyOneEvenQuotientGreedyRemainder R := by
  unfold twentyOneQuotientDefect
  have hpartition :=
    localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder hR
  omega

/-- The sole arithmetic condition remaining after canonicalization. -/
def TwentyOneEvenQuotientGreedyWindow : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    twentyOneEvenQuotientGreedyRemainder R < 2 ^ R

/-- Equivalent strict-core arithmetic package: a coarse two-window bound and
avoidance of one exact integer state. -/
def TwentyOneEvenQuotientCoreControl : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    twentyOneEvenQuotientCoreRemainder R < 2 * 2 ^ R + 1 ∧
      twentyOneEvenQuotientCoreRemainder R ≠ 2 ^ R

/-- The genuinely sufficient closed-core condition.  Compared with strict
core control, it has no exceptional equality and admits the two additional
top states exposed by the exact classifier above. -/
def TwentyOneEvenQuotientClosedCoreControl : Prop :=
  ∀ R : ℕ, 2 ≤ R →
    twentyOneEvenQuotientCoreRemainder R ≤ 2 * 2 ^ R + 1

/-- Strict-core control is exactly what the canonical greedy window needs. -/
theorem twentyOneEvenQuotientGreedyWindow_of_coreControl
    (hcore : TwentyOneEvenQuotientCoreControl) :
    TwentyOneEvenQuotientGreedyWindow := by
  intro R hR
  rw [twentyOneEvenQuotientGreedyRemainder_lt_iff_core_ne hR]
  exact hcore R hR

/-- The canonical greedy window supplies every finite row required by the
compactness theorem. -/
theorem twentyOneEvenQuotientWindowSupply_of_greedyWindow
    (hwindow : TwentyOneEvenQuotientGreedyWindow) :
    TwentyOneEvenQuotientWindowSupply := by
  intro R hR
  refine ⟨twentyOneEvenQuotientGreedySupport R, ?_, ?_, ?_⟩
  · intro d hd
    exact twentyOneEvenQuotientGreedySupport_mem_bounds hd
  · exact localPrefixQuotient_twentyOneEvenQuotientGreedySupport_le hR
  · rw [twentyOneQuotientDefect_greedySupport hR]
    exact hwindow R hR

/-- **One-scalar-state endpoint.**  The terminal quotient-greedy remainder
bound at every even depth proves that `1/21` is a Boolean Mersenne subseries
sum. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_greedyWindow
    (hwindow : TwentyOneEvenQuotientGreedyWindow) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  one_div_twenty_one_mem_mersenneAchievementSet_of_evenQuotientWindow
    (twentyOneEvenQuotientWindowSupply_of_greedyWindow hwindow)

/-- **Closed-core endpoint.**  The prescribed point follows from the single
weak preterminal inequality; neither strictness nor avoidance of an exact
integer state remains. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_closedCoreControl
    (hcore : TwentyOneEvenQuotientClosedCoreControl) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  apply one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
  intro R hR
  refine
    ⟨twentyOneEvenQuotientGreedySupport R,
      twentyOneEvenQuotientGreedyRemainder R, ?_, ?_, ?_⟩
  · intro d hd
    exact twentyOneEvenQuotientGreedySupport_mem_bounds hd
  · exact
      localPrefixQuotient_twentyOneEvenQuotientGreedySupport_add_remainder hR
  · rw [twentyOneEvenQuotientGreedyRemainder_le_iff_core_le hR]
    exact hcore R hR

/-- Final endpoint phrased solely through strict-core arithmetic. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_coreControl
    (hcore : TwentyOneEvenQuotientCoreControl) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  one_div_twenty_one_mem_mersenneAchievementSet_of_greedyWindow
    (twentyOneEvenQuotientGreedyWindow_of_coreControl hcore)

/-- Closedness only needs good quotient rows along one unbounded sequence;
the all-depth window is stronger than the endpoint requires. -/
def TwentyOneCofinalEvenQuotientGreedyWindow : Prop :=
  ∃ R : ℕ → ℕ,
    Tendsto R atTop atTop ∧
      ∀ k : ℕ, 2 ≤ R k ∧
        twentyOneEvenQuotientGreedyRemainder (R k) < 2 ^ (R k)

/-- Minimal asymptotic form of the quotient route.  No fixed cap is built
into the statement: the normalized deterministic defect (with only a
linear support-cardinality allowance) must tend to zero along one unbounded
sequence of rows. -/
def TwentyOneCofinalEvenQuotientGreedyDecay : Prop :=
  ∃ R : ℕ → ℕ,
    Tendsto R atTop atTop ∧
      (∀ k : ℕ, 2 ≤ R k) ∧
      Tendsto
        (fun k : ℕ =>
          ((twentyOneEvenQuotientGreedyRemainder (R k) +
              (2 * R k + 1) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * R k))
        atTop (nhds 0)

/-- The same cofinal condition in the exact strict-core form. -/
def TwentyOneCofinalEvenQuotientCoreControl : Prop :=
  ∃ R : ℕ → ℕ,
    Tendsto R atTop atTop ∧
      ∀ k : ℕ, 2 ≤ R k ∧
        twentyOneEvenQuotientCoreRemainder (R k) <
            2 * 2 ^ (R k) + 1 ∧
          twentyOneEvenQuotientCoreRemainder (R k) ≠ 2 ^ (R k)

/-- Cofinal strict-core control gives cofinal good greedy rows. -/
theorem twentyOneCofinalEvenQuotientGreedyWindow_of_coreControl
    (hcore : TwentyOneCofinalEvenQuotientCoreControl) :
    TwentyOneCofinalEvenQuotientGreedyWindow := by
  rcases hcore with ⟨R, hR, hcore⟩
  refine ⟨R, hR, ?_⟩
  intro k
  refine ⟨(hcore k).1, ?_⟩
  rw [twentyOneEvenQuotientGreedyRemainder_lt_iff_core_ne (hcore k).1]
  exact (hcore k).2

/-- **Minimal cofinal quotient endpoint.**  Normalized deterministic defect
decay on one unbounded sequence puts `1/21` in the achievement set. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay
    (hcofinal : TwentyOneCofinalEvenQuotientGreedyDecay) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  classical
  rcases hcofinal with ⟨R, hR, hRtwo, hdecay⟩
  let D : ℕ → Finset ℕ :=
    fun k => twentyOneEvenQuotientGreedySupport (R k)
  let y : ℕ → ℝ :=
    fun k => ((localMersennePrefixValue (D k) : ℚ) : ℝ)
  have hdist :
      Tendsto (fun k : ℕ => dist (y k) (1 / 21 : ℝ))
        atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ => dist_nonneg)
      (Filter.Eventually.of_forall fun k => ?_)
      hdecay
    rw [Real.dist_eq]
    calc
      |y k - (1 / 21 : ℝ)| ≤
          ((twentyOneQuotientDefect (D k) (2 * R k) +
              (D k).card + 1 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * R k) := by
        exact abs_localMersennePrefixValue_sub_one_div_twenty_one_le
          (fun d hd =>
            (twentyOneEvenQuotientGreedySupport_mem_bounds
              (R := R k) (d := d) hd).1)
          (localPrefixQuotient_twentyOneEvenQuotientGreedySupport_le
            (hRtwo k))
      _ ≤
          (((twentyOneEvenQuotientGreedyRemainder (R k) +
              (2 * R k + 1) : ℕ) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * R k) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hcard : (D k).card ≤ R k + 1 := by
          have hsubset : D k ⊆ Finset.Icc 2 (R k) := by
            intro d hd
            simp only [Finset.mem_Icc]
            exact twentyOneEvenQuotientGreedySupport_mem_bounds hd
          calc
            (D k).card ≤ (Finset.Icc 2 (R k)).card :=
              Finset.card_le_card hsubset
            _ ≤ R k + 1 := by
              simp
              omega
        have hdefect :
            twentyOneQuotientDefect (D k) (2 * R k) =
              twentyOneEvenQuotientGreedyRemainder (R k) := by
          exact twentyOneQuotientDefect_greedySupport (hRtwo k)
        have hRk : 2 ≤ R k := hRtwo k
        have hnat :
            twentyOneQuotientDefect (D k) (2 * R k) +
                (D k).card + 1 ≤
              twentyOneEvenQuotientGreedyRemainder (R k) +
                (2 * R k + 1) := by
          rw [hdefect]
          omega
        exact_mod_cast hnat
  have hy : Tendsto y atTop (nhds (1 / 21 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hyMem : ∀ k : ℕ, y k ∈ mersenneAchievementSet := by
    intro k
    let A : Set ℕ := ↑(D k)
    have hA0 : 0 ∉ A := by
      intro hzero
      have hbound :=
        twentyOneEvenQuotientGreedySupport_mem_bounds
          (R := R k) (d := 0) (by simpa [A] using hzero)
      omega
    refine ⟨A, hA0, ?_⟩
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [y, D, localMersennePrefixValue_eq_finiteErdosSum]
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

/-- The square-root window implies the cap-free normalized decay condition. -/
theorem twentyOneCofinalEvenQuotientGreedyDecay_of_window
    (hwindow : TwentyOneCofinalEvenQuotientGreedyWindow) :
    TwentyOneCofinalEvenQuotientGreedyDecay := by
  rcases hwindow with ⟨R, hR, hrow⟩
  refine ⟨R, hR, (fun k => (hrow k).1), ?_⟩
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => by positivity)
    (Filter.Eventually.of_forall fun k => ?_)
    (tendsto_twentyOne_evenQuotientWindow_error.comp hR)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hrem :
      twentyOneEvenQuotientGreedyRemainder (R k) ≤ 2 ^ (R k) :=
    (hrow k).2.le
  exact_mod_cast (by omega :
    twentyOneEvenQuotientGreedyRemainder (R k) +
        (2 * R k + 1) ≤
      2 ^ (R k) + (2 * R k + 1))

/-- Closed canonical rows along any unbounded sequence already give the
cap-free decay required by compactness.  Strictness is irrelevant at this
stage: the quotient normalization is quadratic in the binary scale. -/
theorem twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows
    {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop)
    (hrow : ∀ k : ℕ,
      2 ≤ R k ∧
        twentyOneEvenQuotientGreedyRemainder (R k) ≤ 2 ^ (R k)) :
    TwentyOneCofinalEvenQuotientGreedyDecay := by
  refine ⟨R, hR, (fun k => (hrow k).1), ?_⟩
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => by positivity)
    (Filter.Eventually.of_forall fun k => ?_)
    (tendsto_twentyOne_evenQuotientWindow_error.comp hR)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hclosed := (hrow k).2
  exact_mod_cast
    Nat.add_le_add_right hclosed (2 * R k + 1)

/-- The canonical next-coin inequality implies the cap-free decay
condition.  The half-row remainder may be twice the old binary window; that
still decays geometrically after the quotient normalization by `4^R`. -/
theorem twentyOneCofinalEvenQuotientGreedyDecay_of_preterminalNextCoin
    (hnext : TwentyOneEvenQuotientPreterminalNextCoinBound) :
    TwentyOneCofinalEvenQuotientGreedyDecay := by
  let rows : ℕ → ℕ := fun k => k + 4
  have hrows : Tendsto rows atTop atTop := by
    simpa [rows, Nat.add_comm] using tendsto_add_atTop_nat 4
  refine ⟨rows, hrows, (fun k => by simp [rows]), ?_⟩
  have hbase :=
    tendsto_twentyOne_evenQuotientWindow_error.comp hrows
  have hupp :
      Tendsto
        (fun k : ℕ =>
          (((2 * (2 ^ rows k + (2 * rows k + 1)) : ℕ) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * rows k))
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat,
      mul_div_assoc, mul_zero] using hbase.const_mul 2
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun _ => by positivity)
    (Filter.Eventually.of_forall fun k => ?_)
    hupp
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hrem :=
    twentyOneEvenQuotientGreedyRemainder_le_double_of_preterminalNextCoin
      (R := rows k) (by simp [rows]) (hnext (rows k) (by simp [rows]))
  have hpow : 2 ^ (rows k + 1) = 2 * 2 ^ rows k := by
    rw [pow_succ]
    omega
  rw [hpow] at hrem
  exact_mod_cast (by omega :
    twentyOneEvenQuotientGreedyRemainder (rows k) +
        (2 * rows k + 1) ≤
      2 * (2 ^ rows k + (2 * rows k + 1)))

/-- **Cofinal quotient endpoint.**  Arbitrarily deep square-root-window
rows already put `1/21` in the achievement set; omitted depths are
irrelevant. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyWindow
    (hcofinal : TwentyOneCofinalEvenQuotientGreedyWindow) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay
    (twentyOneCofinalEvenQuotientGreedyDecay_of_window hcofinal)

/-- **Exact permanent-escape form of the fatal branch.**  If the prescribed
point is not represented, the canonical quotient remainder is eventually
strictly above its closed binary capacity at every depth.  Any unbounded
sequence of closed returns would already converge to `1/21` by compactness.

Combined with `twentyOneFatalAlignedBranch_eventually_canonical_transition`,
this leaves one explicit dynamical regime: an exact aligned recurrence which
eventually stays in `2^R < s_R`. -/
theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R := by
  classical
  by_contra hfail
  push Not at hfail
  choose R hRge hRclosed using fun k => hfail (k + 2)
  have hRtop : Tendsto R atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards with k
    simpa only [id_eq] using (show k ≤ R k by
      have := hRge k
      omega)
  have hclosed :
      ∀ k : ℕ, 2 ≤ R k ∧
        twentyOneEvenQuotientGreedyRemainder (R k) ≤ 2 ^ (R k) := by
    intro k
    exact ⟨by
      have := hRge k
      omega, hRclosed k⟩
  have hmem :
      (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
    apply one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay
    exact
      twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows hRtop hclosed
  exact (twentyOneFatalAlignedBranch_iff_not_mem.mp hbranch) hmem

/-- **Affine normal form of the only remaining fatal regime.**  Once the
canonical remainder has escaped strictly above `2^R`, its exponential
margin dominates the entire linear divisor pulse.  Consequently the new
boundary coin always fits: the support appends `R+1`, and the scalar follows
one literal affine recurrence with no residual Boolean branch. -/
theorem twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      twentyOneEvenQuotientGreedySupport (R + 1) =
          insert (R + 1) (twentyOneEvenQuotientGreedySupport R) ∧
        twentyOneEvenQuotientGreedyRemainder (R + 1) =
          (4 * twentyOneEvenQuotientGreedyRemainder R +
              twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)) -
            (2 ^ (R + 1) + 1) := by
  classical
  obtain ⟨Ktransition, htransition⟩ :=
    twentyOneFatalAlignedBranch_eventually_canonical_transition hbranch
  obtain ⟨Kescape, hescape⟩ :=
    twentyOneFatalAlignedBranch_eventually_strict_supercapacity hbranch
  refine ⟨max (max Ktransition Kescape) 4, ?_⟩
  intro R hKR
  have hRtransition : Ktransition ≤ R :=
    (le_max_left Ktransition Kescape).trans
      ((le_max_left (max Ktransition Kescape) 4).trans hKR)
  have hRescape : Kescape ≤ R :=
    (le_max_right Ktransition Kescape).trans
      ((le_max_left (max Ktransition Kescape) 4).trans hKR)
  have hRfour : 4 ≤ R :=
    (le_max_right (max Ktransition Kescape) 4).trans hKR
  let D := twentyOneEvenQuotientGreedySupport R
  let s := twentyOneEvenQuotientGreedyRemainder R
  let p := localPrefixTwoStepPulse D (2 * R)
  let t := twentyOneTargetTwoStepPulse (2 * R)
  have hDcard : D.card ≤ R + 1 := by
    have hsubset : D ⊆ Finset.Icc 2 R := by
      intro d hd
      simp only [Finset.mem_Icc]
      exact twentyOneEvenQuotientGreedySupport_mem_bounds
        (R := R) (d := d) (by simpa [D] using hd)
    calc
      D.card ≤ (Finset.Icc 2 R).card := Finset.card_le_card hsubset
      _ ≤ R + 1 := by
        simp
        omega
  have hpulse : p ≤ 3 * (R + 1) := by
    have :=
      localPrefixTwoStepPulse_le_three_mul_card D (2 * R)
    dsimp [p]
    omega
  have hs : 2 ^ R + 1 ≤ s := by
    have := hescape R hRescape
    dsimp [s]
    omega
  have hlinear := two_mul_sub_two_le_two_pow R
  have hlinear' : R + 2 ≤ 2 ^ R := by omega
  have hpowsucc : 2 ^ (R + 1) = 2 * 2 ^ R := by
    rw [pow_succ]
    omega
  have hthree : 3 * R ≤ 2 ^ (R + 1) := by
    rw [hpowsucc]
    omega
  have hbudget :
      p + (2 ^ (R + 1) + 1) ≤ 4 * s + t := by
    omega
  have htake :
      2 ^ (R + 1) + 1 ≤ 4 * s + t - p :=
    Nat.le_sub_of_add_le (by omega)
  have hstep := htransition R hRtransition
  dsimp [D, s, p, t] at htake ⊢
  simpa [twentyOneBoundaryLowerSupport,
      twentyOneBoundaryScalarState, htake] using hstep

/-- Cofinal strict-core control is therefore sufficient for the prescribed
rational point. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalCoreControl
    (hcore : TwentyOneCofinalEvenQuotientCoreControl) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyWindow
    (twentyOneCofinalEvenQuotientGreedyWindow_of_coreControl hcore)

/-- **Canonical next-coin endpoint.**  It is enough to prove the ordinary
greedy invariant that every preterminal state lies below the next quotient
coin.  No fixed fringe width, exact equality exclusion, or full-row defect
cap remains in the hypothesis. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_preterminalNextCoin
    (hnext : TwentyOneEvenQuotientPreterminalNextCoinBound) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet :=
  one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay
    (twentyOneCofinalEvenQuotientGreedyDecay_of_preterminalNextCoin hnext)

#print axioms localMersenneWeights_two_mul_strong_gapDominates
#print axioms twentyOneClosedRow_forces_quotientGreedy
#print axioms twentyOneQuotientDefect_greedySupport
#print axioms twentyOneEvenQuotientGreedyRemainder_lt_iff_core_ne
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalCoreControl
#print axioms
  twentyOneEvenFullQuotientGreedyRemainder_le_one_of_coreBound
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_fullQuotientCoreBound
#print axioms
  twentyOneEvenFullQuotientGreedyRemainder_le_three_of_preterminalBound
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_preterminalCoarseBound
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_preterminalNextCoin
#print axioms localPrefixTwoStepPulse_le_three_mul_card
#print axioms endpointDivisorContribution_horizon_stable
#print axioms localPrefixTwoStepPulse_horizon_stable
#print axioms exists_twentyOneRow_defect_le_one_of_closedState
#print axioms exists_twentyOneClosedLowerState_succ
#print axioms exists_twentyOneClosedLowerState_succ_of_pulse
#print axioms twentyOneBoundaryScalarState_eq_boundary_iff
#print axioms twentyOneBoundaryScalarState_eq_boundary_iff_of_strict
#print axioms twentyOneSignedClosedMargin_boundary_of_take
#print axioms twentyOneSignedClosedMargin_boundary_of_skip
#print axioms twentyOneTargetTwoStepPulse_even_add_three
#print axioms twentyOneTargetTwoStepPulse_even_eq_three_iff
#print axioms twentyOneSaturatedPulse_iff
#print axioms twentyOneClosedTransitionSaturatedPulse_iff
#print axioms twentyOneSaturatedBoundary_crosses_iff_sparsePulse
#print axioms
  twentyOneSaturatedBoundary_crossing_forces_ancestor_hole
#print axioms
  twentyOneAlignedSaturatedCrossing_forces_scaled_greedy_skip
#print axioms twentyOneBadSaturatedTransition_forces_sparse_twoPulse
#print axioms twentyOneBadSaturatedTransition_forces_margin_residue
#print axioms twentyOneBadSaturatedTransition_forces_half_state
#print axioms twentyOneBadSaturatedTransition_forces_ancestor_hole
#print axioms one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
#print axioms localPrefixQuotient_le_twentyOneTarget_of_prefix_le
#print axioms localMersenneQuotient_le_twentyOneRemainder_of_rational_take
#print axioms
  localQuotientGreedyBits_eq_rationalGreedyBitsFrom_of_safe
#print axioms
  twentyOneEvenFullQuotientGreedyBits_eq_rational_of_safe
#print axioms
  mem_lowerSupportFromBits_rationalMersenneGreedyBitsFrom_iff
#print axioms
  one_div_twenty_one_lt_fullGreedyPrefix_of_bits_ne_rational
#print axioms twentyOneQuotientDefect_le_card_of_target_le_prefix
#print axioms
  one_div_twenty_one_le_localMersennePrefixValue_iff_fraction_balance
#print axioms two_pow_six_mul_mod_twentyOne
#print axioms
  twentyOneTargetFraction_two_mul_eq_one_div_twenty_one_of_three_dvd
#print axioms
  one_div_twenty_one_le_fullGreedyPrefix_iff_fraction_balance
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalFullOvershoot
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalFullDivergence
#print axioms
  twentyOneEventuallyEvenFullQuotientRationalAlignment_of_not_mem
#print axioms
  twentyOneEvenQuotientGreedySupport_mem_iff_of_fullAlignment
#print axioms mem_greedyMersennePrefixRat_iff_real_support
#print axioms
  twentyOneEvenQuotientGreedySupport_eq_greedyMersennePrefixRat_of_fullAlignment
#print axioms
  localMersennePrefixValue_twentyOneEvenQuotientGreedySupport_le_of_fullAlignment
#print axioms
  localPrefixTwoStepPulse_twentyOneEvenQuotientGreedySupport_le_carry_of_fullAlignment
#print axioms
  twentyOneFatalAlignedBranch_eventually_canonical_carry_nonneg
#print axioms lowerSupportFromBits_append_singleton
#print axioms
  twentyOneEvenQuotientGreedySupport_succ_eq_boundary_of_fullAlignment
#print axioms
  twentyOneEvenQuotientGreedyRemainder_succ_eq_boundary_of_fullAlignment
#print axioms
  twentyOneAlignedSaturatedCrossing_forces_canonical_ancestor_hole
#print axioms
  twentyOneFatalAlignedBranch_eventually_canonical_transition
#print axioms
  twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows
#print axioms
  twentyOneFatalAlignedBranch_eventually_strict_supercapacity
#print axioms
  twentyOneFatalAlignedBranch_eventually_affine_supercapacity
#print axioms
  one_div_twenty_one_mem_or_eventuallyFullQuotientRationalAlignment
#print axioms twentyOneFatalAlignedBranch_eventually_saturated_socket
#print axioms twentyOneFatalAlignedBranch_of_not_mem
#print axioms one_div_twenty_one_mem_or_fatalAlignedBranch
#print axioms twentyOneFatalAlignedBranch_iff_not_mem
#print axioms one_div_twenty_one_mem_iff_not_fatalAlignedBranch
#print axioms lastTwentyOneSkip_shiftDelta_eq_remainder_sub_tail
#print axioms lastTwentyOneSkip_erdosBorwein_fatalInterval
#print axioms twentyOne_not_mem_forces_erdosBorwein_fatalInterval
#print axioms
  twentyOne_not_mem_forces_rational_erdosBorwein_fatalInterval
#print axioms
  twentyOneEventualLeftCorrectionBoundaryAmplification_of_not_mem
#print axioms
  twentyOneFatalAlignedBranch_supportDyadicPrefix_factorization
#print axioms twentyOneFatalAlignedBranch_rightBoundary_power_dvd
#print axioms localMersennePrefixValue_le_one_div_twenty_one_of_card_le_state
#print axioms twentyOneEvenQuotientGreedyRemainder_le_iff_core_le
#print axioms one_div_twenty_one_mem_mersenneAchievementSet_of_closedCoreControl

end Erdos249257
