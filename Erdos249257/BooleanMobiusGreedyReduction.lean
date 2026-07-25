import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.HalfCylinderIntegerGreedy

/-!
# Boolean Möbius lower-word greedy reduction

This module isolates the finite integer reduction behind the Boolean Möbius
repair.  Its endpoint is deliberately conditional: a lower word which leaves
less than the complete binary upper window must be the unique descending
integer-greedy word.  The arithmetic behavior of that greedy word remains a
separate obligation.
-/

namespace Erdos249257.BooleanMobiusGreedyReduction

open HalfCylinderIntegerGreedy

/-! ## The parity-uniform binary window -/

/-- Number of binary suffix values available after a truncation at depth
`M`, when ranks through `R` have already been fixed. -/
def lowerBinaryWindow (M R : ℕ) : ℕ :=
  2 ^ (M - R)

theorem lowerBinaryWindow_even (R : ℕ) (hR : 1 ≤ R) :
    lowerBinaryWindow (2 * R - 1) R = 2 ^ (R - 1) := by
  unfold lowerBinaryWindow
  congr 1
  omega

theorem lowerBinaryWindow_odd (R : ℕ) :
    lowerBinaryWindow (2 * R) R = 2 ^ R := by
  unfold lowerBinaryWindow
  congr 1
  omega

/-! ## The concrete local Mersenne word -/

/-- The local Boolean target at binary depth `M`.  In the half construction
`k = 1`, so this is the integer immediately below `2^(M-1)`. -/
def localMersenneTarget (M k : ℕ) : ℕ :=
  2 ^ (M - k) - 1

/-- Descending local quotient weights with ranks `d,d+1,…,R`. -/
def localMersenneWeightsFrom (M R : ℕ) : ℕ → List ℕ
  | d =>
      if h : d ≤ R then
        localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1)
      else
        []
termination_by d => R + 1 - d
decreasing_by omega

/-- The complete lower quotient word on ranks `2,…,R`. -/
def localMersenneWeights (M R : ℕ) : List ℕ :=
  localMersenneWeightsFrom M R 2

theorem localMersenneWeightsFrom_eq_nil
    {M R d : ℕ} (h : R < d) :
    localMersenneWeightsFrom M R d = [] := by
  rw [localMersenneWeightsFrom]
  simp [Nat.not_le.mpr h]

theorem localMersenneWeightsFrom_eq_cons
    {M R d : ℕ} (h : d ≤ R) :
    localMersenneWeightsFrom M R d =
      localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1) := by
  rw [localMersenneWeightsFrom]
  simp [h]

theorem localMersenneWeightsFrom_length (M R d : ℕ) :
    (localMersenneWeightsFrom M R d).length = R + 1 - d := by
  by_cases hdR : d ≤ R
  · rw [localMersenneWeightsFrom_eq_cons hdR, List.length_cons,
      localMersenneWeightsFrom_length M R (d + 1)]
    omega
  · rw [localMersenneWeightsFrom_eq_nil (by omega)]
    simp
    omega
termination_by R + 1 - d
decreasing_by omega

@[simp] theorem localMersenneWeights_length (M R : ℕ) :
    (localMersenneWeights M R).length = R - 1 := by
  unfold localMersenneWeights
  rw [localMersenneWeightsFrom_length]
  omega

/-- The quotient is at most its unfloored real Mersenne weight. -/
theorem localMersenneQuotient_cast_le_scaled
    {M d : ℕ} (hd : 1 ≤ d) :
    ((localMersenneQuotient M d : ℕ) : ℝ) ≤
      (2 : ℝ) ^ M * mersenneWeight d := by
  have hpowNat : 1 < 2 ^ d := one_lt_pow₀ (by omega) (by omega)
  have hdenNat : 0 < 2 ^ d - 1 := Nat.sub_pos_of_lt hpowNat
  have hdenReal : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
    have hpowReal : (1 : ℝ) < (2 : ℝ) ^ d :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hdenCast :
      (((2 ^ d - 1 : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ d - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hmulNat :
      (2 ^ M / (2 ^ d - 1)) * (2 ^ d - 1) ≤ 2 ^ M := by
    simpa [Nat.mul_comm] using Nat.mul_div_le (2 ^ M) (2 ^ d - 1)
  have hmulReal :
      (((2 ^ M / (2 ^ d - 1) : ℕ) : ℕ) : ℝ) *
          (((2 ^ d - 1 : ℕ) : ℕ) : ℝ) ≤
        (((2 ^ M : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hmulNat
  unfold localMersenneQuotient
  change (((2 ^ M / (2 ^ d - 1) : ℕ) : ℕ) : ℝ) ≤
    (2 : ℝ) ^ M * (1 / ((2 : ℝ) ^ d - 1))
  rw [show (2 : ℝ) ^ M * (1 / ((2 : ℝ) ^ d - 1)) =
      (2 : ℝ) ^ M / ((2 : ℝ) ^ d - 1) by ring]
  rw [le_div_iff₀ hdenReal]
  simpa only [hdenCast, Nat.cast_pow, Nat.cast_ofNat] using hmulReal

/-- The unfloored real Mersenne weight is strictly below the successor of
its integral quotient. -/
theorem scaled_lt_localMersenneQuotient_cast_add_one
    {M d : ℕ} (hd : 1 ≤ d) :
    (2 : ℝ) ^ M * mersenneWeight d <
      (((localMersenneQuotient M d + 1 : ℕ) : ℕ) : ℝ) := by
  have hpowNat : 1 < 2 ^ d := one_lt_pow₀ (by omega) (by omega)
  have hdenNat : 0 < 2 ^ d - 1 := Nat.sub_pos_of_lt hpowNat
  have hdenReal : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
    have hpowReal : (1 : ℝ) < (2 : ℝ) ^ d :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hdenCast :
      (((2 ^ d - 1 : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ d - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hquot :
      2 ^ M < (2 ^ M / (2 ^ d - 1) + 1) * (2 ^ d - 1) :=
    (Nat.div_lt_iff_lt_mul hdenNat).1
      (Nat.lt_succ_self (2 ^ M / (2 ^ d - 1)))
  have hquotReal :
      (((2 ^ M : ℕ) : ℕ) : ℝ) <
        (((2 ^ M / (2 ^ d - 1) + 1 : ℕ) : ℕ) : ℝ) *
          (((2 ^ d - 1 : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hquot
  unfold localMersenneQuotient
  change (2 : ℝ) ^ M * (1 / ((2 : ℝ) ^ d - 1)) <
    (((2 ^ M / (2 ^ d - 1) + 1 : ℕ) : ℕ) : ℝ)
  rw [show (2 : ℝ) ^ M * (1 / ((2 : ℝ) ^ d - 1)) =
      (2 : ℝ) ^ M / ((2 : ℝ) ^ d - 1) by ring]
  rw [div_lt_iff₀ hdenReal]
  simpa only [hdenCast, Nat.cast_pow, Nat.cast_ofNat] using hquotReal

/-- The finite quotient tail, together with the omitted infinite Mersenne
tail after rank `R`, is bounded by the corresponding full tail. -/
theorem localMersenneWeightsFrom_cast_sum_add_tail_le
    (M R d : ℕ) (hd : 1 ≤ d) (hdR : d ≤ R + 1) :
    (((localMersenneWeightsFrom M R d).sum : ℕ) : ℝ) +
        (2 : ℝ) ^ M * mersenneTail R ≤
      (2 : ℝ) ^ M * mersenneTail (d - 1) := by
  by_cases heq : d = R + 1
  · subst d
    rw [localMersenneWeightsFrom_eq_nil (by omega)]
    simp
  · have hdle : d ≤ R := by omega
    have hnext :
        (((localMersenneWeightsFrom M R (d + 1)).sum : ℕ) : ℝ) +
            (2 : ℝ) ^ M * mersenneTail R ≤
          (2 : ℝ) ^ M * mersenneTail d := by
      simpa [show d + 1 - 1 = d by omega] using
        localMersenneWeightsFrom_cast_sum_add_tail_le
          M R (d + 1) (by omega) (by omega)
    have hhead := localMersenneQuotient_cast_le_scaled
      (M := M) (d := d) hd
    have htailRec :
        mersenneTail (d - 1) = mersenneWeight d + mersenneTail d := by
      simpa [show d - 1 + 1 = d by omega] using
        mersenneTail_eq_weight_add (d - 1)
    rw [localMersenneWeightsFrom_eq_cons hdle, List.sum_cons, Nat.cast_add]
    calc
      ((localMersenneQuotient M d : ℕ) : ℝ) +
            (((localMersenneWeightsFrom M R (d + 1)).sum : ℕ) : ℝ) +
            (2 : ℝ) ^ M * mersenneTail R
          ≤ (2 : ℝ) ^ M * mersenneWeight d +
              ((((localMersenneWeightsFrom M R (d + 1)).sum : ℕ) : ℝ) +
                (2 : ℝ) ^ M * mersenneTail R) := by
              linarith
      _ ≤ (2 : ℝ) ^ M * mersenneWeight d +
            (2 : ℝ) ^ M * mersenneTail d := by
              linarith
      _ = (2 : ℝ) ^ M * mersenneTail (d - 1) := by
            rw [htailRec]
            ring
termination_by R + 1 - d
decreasing_by omega

/-- Cancelling `R` binary factors exposes the exact first omitted harmonic.
This is the parity-uniform identity behind the gap `2^(M-R)`. -/
theorem two_pow_mul_half_pow
    {M R : ℕ} (hRM : R ≤ M) :
    (2 : ℝ) ^ M * ((1 : ℝ) / 2) ^ R =
      (2 : ℝ) ^ (M - R) := by
  induction R generalizing M with
  | zero => simp
  | succ R ih =>
      have hpred : R ≤ M - 1 := by omega
      have hMpow : (2 : ℝ) ^ M = (2 : ℝ) ^ (M - 1) * 2 := by
        calc
          (2 : ℝ) ^ M = 2 ^ ((M - 1) + 1) := by
            congr 1
            omega
          _ = (2 : ℝ) ^ (M - 1) * 2 := by rw [pow_succ]
      have hRpow : ((1 : ℝ) / 2) ^ (R + 1) =
          ((1 : ℝ) / 2) ^ R * ((1 : ℝ) / 2) := by
        rw [pow_succ]
      calc
        (2 : ℝ) ^ M * ((1 : ℝ) / 2) ^ (R + 1) =
            ((2 : ℝ) ^ (M - 1) * 2) *
              (((1 : ℝ) / 2) ^ R * ((1 : ℝ) / 2)) := by
                rw [hMpow, hRpow]
        _ = (2 : ℝ) ^ (M - 1) * ((1 : ℝ) / 2) ^ R := by ring
        _ = (2 : ℝ) ^ ((M - 1) - R) := ih hpred
        _ = (2 : ℝ) ^ (M - (R + 1)) := by
              congr 1
              omega

/-- Concrete first-harmonic plus higher-tail bound.  The omitted first
binary harmonic after rank `R` is exactly `2^(M-R)`; the strictly positive
Mersenne correction beyond it absorbs all quotient-floor losses. -/
theorem localMersenneQuotient_dominanceGap
    {M R d : ℕ} (hRM : R ≤ M) (hd : 1 ≤ d) (hdR : d ≤ R) :
    lowerBinaryWindow M R +
        (localMersenneWeightsFrom M R (d + 1)).sum ≤
      localMersenneQuotient M d := by
  have htail :
      (((localMersenneWeightsFrom M R (d + 1)).sum : ℕ) : ℝ) +
          (2 : ℝ) ^ M * mersenneTail R ≤
        (2 : ℝ) ^ M * mersenneTail d := by
    simpa [show d + 1 - 1 = d by omega] using
      localMersenneWeightsFrom_cast_sum_add_tail_le
        M R (d + 1) (by omega) (by omega)
  have hcorr := mersenneCorrectionTail_pos R
  have hfirst :
      ((1 : ℝ) / 2) ^ R < mersenneTail R := by
    unfold mersenneCorrectionTail at hcorr
    linarith
  have hscale := two_pow_mul_half_pow hRM
  have hwindowCast :
      ((lowerBinaryWindow M R : ℕ) : ℝ) =
        (2 : ℝ) ^ (M - R) := by
    simp [lowerBinaryWindow]
  have hscaledFirst :
      ((lowerBinaryWindow M R : ℕ) : ℝ) <
        (2 : ℝ) ^ M * mersenneTail R := by
    rw [hwindowCast, ← hscale]
    exact mul_lt_mul_of_pos_left hfirst (by positivity)
  have hsuper := mersenneTail_lt_weight (n := d) (by omega)
  have hhead := scaled_lt_localMersenneQuotient_cast_add_one
    (M := M) (d := d) hd
  have hreal :
      ((lowerBinaryWindow M R : ℕ) : ℝ) +
          (((localMersenneWeightsFrom M R (d + 1)).sum : ℕ) : ℝ) <
        (((localMersenneQuotient M d + 1 : ℕ) : ℕ) : ℝ) := by
    calc
      ((lowerBinaryWindow M R : ℕ) : ℝ) +
            (((localMersenneWeightsFrom M R (d + 1)).sum : ℕ) : ℝ)
          < (2 : ℝ) ^ M * mersenneTail R +
              (((localMersenneWeightsFrom M R (d + 1)).sum : ℕ) : ℝ) := by
                linarith
      _ ≤ (2 : ℝ) ^ M * mersenneTail d := by linarith
      _ < (2 : ℝ) ^ M * mersenneWeight d :=
        mul_lt_mul_of_pos_left hsuper (by positivity)
      _ < (((localMersenneQuotient M d + 1 : ℕ) : ℕ) : ℝ) := hhead
  have hnat :
      lowerBinaryWindow M R +
          (localMersenneWeightsFrom M R (d + 1)).sum <
        localMersenneQuotient M d + 1 := by
    exact_mod_cast hreal
  omega

theorem localMersenneWeightsFrom_gapDominates
    {M R d : ℕ} (hRM : R ≤ M) (hd : 1 ≤ d) :
    GapDominates (lowerBinaryWindow M R)
      (localMersenneWeightsFrom M R d) := by
  by_cases hdR : d ≤ R
  · rw [localMersenneWeightsFrom_eq_cons hdR, GapDominates]
    exact ⟨localMersenneQuotient_dominanceGap hRM hd hdR,
      localMersenneWeightsFrom_gapDominates hRM (by omega)⟩
  · have hnil : localMersenneWeightsFrom M R d = [] :=
      localMersenneWeightsFrom_eq_nil (by omega)
    rw [hnil]
    trivial
termination_by R + 1 - d
decreasing_by omega

theorem localMersenneWeights_gapDominates
    {M R : ℕ} (hRM : R ≤ M) :
    GapDominates (lowerBinaryWindow M R) (localMersenneWeights M R) := by
  exact localMersenneWeightsFrom_gapDominates hRM (by omega)

/-- Even endpoints `M = 2R-1` have separation window `2^(R-1)`. -/
theorem localMersenneWeights_gapDominates_even
    (R : ℕ) (hR : 1 ≤ R) :
    GapDominates (2 ^ (R - 1)) (localMersenneWeights (2 * R - 1) R) := by
  have h := localMersenneWeights_gapDominates
    (M := 2 * R - 1) (R := R) (by omega)
  rw [lowerBinaryWindow_even R hR] at h
  exact h

/-- Odd endpoints `M = 2R` have separation window `2^R`. -/
theorem localMersenneWeights_gapDominates_odd (R : ℕ) :
    GapDominates (2 ^ R) (localMersenneWeights (2 * R) R) := by
  have h := localMersenneWeights_gapDominates
    (M := 2 * R) (R := R) (by omega)
  rw [lowerBinaryWindow_odd R] at h
  exact h

/-- At endpoint `n`, the gap is exactly the capacity of the already-written
strict upper suffix through `n-1`. -/
theorem lowerBinaryWindow_endpoint (n : ℕ) :
    lowerBinaryWindow (n - 1) (n / 2) =
      2 ^ (upperHalfRepairLength n - 1) := by
  unfold lowerBinaryWindow upperHalfRepairLength
  congr 1
  omega

/-- Endpoint form consumed by the Boolean--Möbius repair process. -/
theorem localMersenneEndpointWeights_gapDominates
    {n : ℕ} (hn : 2 ≤ n) :
    GapDominates (2 ^ (upperHalfRepairLength n - 1))
      (localMersenneWeights (n - 1) (n / 2)) := by
  have h := localMersenneWeights_gapDominates
    (M := n - 1) (R := n / 2) (by omega)
  rw [lowerBinaryWindow_endpoint n] at h
  exact h

/-! ## A gap-dominating word has only one lower-window representative -/

/-- Every admissible non-greedy word misses the capacity by at least the
full separation gap.  This is the precise form needed before specializing
the gap to `lowerBinaryWindow M R`. -/
theorem gap_le_remainder_of_ne_integerGreedyBits
    {gap C : ℕ} {weights : List ℕ} {bits : List Bool} (hgap : 0 < gap)
    (hdom : GapDominates gap weights)
    (hlen : bits.length = weights.length)
    (hadm : weightedBoolSum weights bits ≤ C)
    (hne : bits ≠ integerGreedyBits weights C) :
    gap ≤ C - weightedBoolSum weights bits := by
  have hgreedyLen := integerGreedyBits_length weights C
  have hgreedyAdm := integerGreedyBits_admissible weights C
  have hmax := integerGreedyBits_maximal hgap hdom hlen hadm
  rcases weightedBoolSum_separated hgap hdom hlen hgreedyLen hne with
    hbelow | habove
  · omega
  · omega

/-- A Boolean word whose defect is smaller than the separation gap is the
descending integer-greedy word. -/
theorem eq_integerGreedyBits_of_remainder_lt_gap
    {gap C : ℕ} {weights : List ℕ} {bits : List Bool} (hgap : 0 < gap)
    (hdom : GapDominates gap weights)
    (hlen : bits.length = weights.length)
    (hadm : weightedBoolSum weights bits ≤ C)
    (hwindow : C - weightedBoolSum weights bits < gap) :
    bits = integerGreedyBits weights C := by
  by_contra hne
  have hlarge := gap_le_remainder_of_ne_integerGreedyBits
    hgap hdom hlen hadm hne
  omega

/-- Exact unique-window hinge.  Under gap dominance, a given admissible word
has a defect inside the binary upper window iff it is the integer-greedy word
and the deterministic greedy remainder lies in that window. -/
theorem remainder_lt_gap_iff_eq_integerGreedyBits
    {gap C : ℕ} {weights : List ℕ} {bits : List Bool} (hgap : 0 < gap)
    (hdom : GapDominates gap weights)
    (hlen : bits.length = weights.length)
    (hadm : weightedBoolSum weights bits ≤ C) :
    C - weightedBoolSum weights bits < gap ↔
      bits = integerGreedyBits weights C ∧
        integerGreedyRemainder weights C < gap := by
  constructor
  · intro hwindow
    have heq := eq_integerGreedyBits_of_remainder_lt_gap
      hgap hdom hlen hadm hwindow
    subst bits
    exact ⟨rfl, hwindow⟩
  · rintro ⟨rfl, hwindow⟩
    exact hwindow

/-- Consumer form for the Boolean Möbius repair.  If the chosen lower word
and its binary suffix `A` exactly fill `C`, and `A` lies in the parity-uniform
upper window, then the lower word is forced to be integer greedy and `A` is
literally the integer-greedy remainder. -/
theorem lower_word_eq_greedy_and_remainder_eq
    {M R C A : ℕ} {weights : List ℕ} {bits : List Bool}
    (hwindowPos : 0 < lowerBinaryWindow M R)
    (hdom : GapDominates (lowerBinaryWindow M R) weights)
    (hlen : bits.length = weights.length)
    (hfill : weightedBoolSum weights bits + A = C)
    (hA : A < lowerBinaryWindow M R) :
    bits = integerGreedyBits weights C ∧
      A = integerGreedyRemainder weights C := by
  have hadm : weightedBoolSum weights bits ≤ C := by omega
  have hdefect : C - weightedBoolSum weights bits = A := by omega
  have heq := eq_integerGreedyBits_of_remainder_lt_gap
    hwindowPos hdom hlen hadm (by omega)
  subst bits
  exact ⟨rfl, by simpa [integerGreedyRemainder] using hdefect.symm⟩

/-! ## Specialization to the Boolean--Möbius endpoint target -/

/-- The locally defined suffix is the target defect of the selected quotient
sum.  This identity is valid with truncated natural subtraction as written. -/
theorem localBinarySuffix_eq_localMersenneTarget_sub
    (D : Finset ℕ) (k M : ℕ) :
    localBinarySuffix D k M =
      localMersenneTarget M k - localPrefixQuotient D M := by
  unfold localBinarySuffix localMersenneTarget
  omega

/-- If the frozen quotient sum is admissible, its suffix exactly fills the
local target. -/
theorem localPrefixQuotient_add_localBinarySuffix
    {D : Finset ℕ} {k M : ℕ}
    (hadm : localPrefixQuotient D M ≤ localMersenneTarget M k) :
    localPrefixQuotient D M + localBinarySuffix D k M =
      localMersenneTarget M k := by
  rw [localBinarySuffix_eq_localMersenneTarget_sub]
  omega

/-- Concrete quotient-word reduction at the general local target
`2^(M-k)-1`.  No abstract dominance premise remains. -/
theorem localMersenneTarget_lower_word_eq_greedy_and_remainder_eq
    {M R k A : ℕ} {bits : List Bool}
    (hRM : R ≤ M)
    (hlen : bits.length = (localMersenneWeights M R).length)
    (hfill :
      weightedBoolSum (localMersenneWeights M R) bits + A =
        localMersenneTarget M k)
    (hA : A < lowerBinaryWindow M R) :
    bits = integerGreedyBits (localMersenneWeights M R)
        (localMersenneTarget M k) ∧
      A = integerGreedyRemainder (localMersenneWeights M R)
        (localMersenneTarget M k) := by
  exact lower_word_eq_greedy_and_remainder_eq
    (Nat.two_pow_pos _) (localMersenneWeights_gapDominates hRM)
    hlen hfill hA

/-- Exact `k=1` endpoint used by the half construction.  A lower quotient
word whose defect lies inside the strict upper-half binary window is forced
to be the deterministic integer-greedy word. -/
theorem localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq
    {M R A : ℕ} {bits : List Bool}
    (hRM : R ≤ M)
    (hlen : bits.length = (localMersenneWeights M R).length)
    (hfill :
      weightedBoolSum (localMersenneWeights M R) bits + A =
        2 ^ (M - 1) - 1)
    (hA : A < lowerBinaryWindow M R) :
    bits = integerGreedyBits (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) ∧
      A = integerGreedyRemainder (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) := by
  simpa [localMersenneTarget] using
    (localMersenneTarget_lower_word_eq_greedy_and_remainder_eq
      (M := M) (R := R) (k := 1) (A := A) (bits := bits)
      hRM hlen hfill hA)

/-- Fully specialized endpoint form: `M=n-1`, `R=⌊n/2⌋`, `k=1`.
The target is `2^(n-2)-1` and the separating window is the strict upper
suffix capacity `2^(upperHalfRepairLength n-1)`. -/
theorem localMersenneEndpoint_lower_word_eq_greedy_and_remainder_eq
    {n A : ℕ} {bits : List Bool}
    (hn : 2 ≤ n)
    (hlen : bits.length =
      (localMersenneWeights (n - 1) (n / 2)).length)
    (hfill :
      weightedBoolSum (localMersenneWeights (n - 1) (n / 2)) bits + A =
        2 ^ (n - 2) - 1)
    (hA : A < 2 ^ (upperHalfRepairLength n - 1)) :
    bits = integerGreedyBits
        (localMersenneWeights (n - 1) (n / 2)) (2 ^ (n - 2) - 1) ∧
      A = integerGreedyRemainder
        (localMersenneWeights (n - 1) (n / 2)) (2 ^ (n - 2) - 1) := by
  have hfill' :
      weightedBoolSum (localMersenneWeights (n - 1) (n / 2)) bits + A =
        2 ^ ((n - 1) - 1) - 1 := by
    simpa [show (n - 1) - 1 = n - 2 by omega] using hfill
  have hA' : A < lowerBinaryWindow (n - 1) (n / 2) := by
    rw [lowerBinaryWindow_endpoint]
    exact hA
  simpa [show (n - 1) - 1 = n - 2 by omega] using
    (localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq
      (M := n - 1) (R := n / 2) (A := A) (bits := bits)
      (by omega) hlen hfill' hA')

/-- Source-level suffix form.  Once a Boolean list is identified with the
frozen support's quotient sum, admissibility and the binary-window bound
force both the greedy word and its exact remainder. -/
theorem localBinarySuffix_forces_greedy_lower_word
    {D : Finset ℕ} {M R k : ℕ} {bits : List Bool}
    (hRM : R ≤ M)
    (hlen : bits.length = (localMersenneWeights M R).length)
    (hsum : weightedBoolSum (localMersenneWeights M R) bits =
      localPrefixQuotient D M)
    (hadm : localPrefixQuotient D M ≤ localMersenneTarget M k)
    (hwindow : localBinarySuffix D k M < lowerBinaryWindow M R) :
    bits = integerGreedyBits (localMersenneWeights M R)
        (localMersenneTarget M k) ∧
      localBinarySuffix D k M =
        integerGreedyRemainder (localMersenneWeights M R)
          (localMersenneTarget M k) := by
  apply localMersenneTarget_lower_word_eq_greedy_and_remainder_eq
    hRM hlen
  · rw [hsum]
    exact localPrefixQuotient_add_localBinarySuffix hadm
  · exact hwindow

/-- The preceding source-level theorem at the exact half target `k=1`. -/
theorem localBinarySuffix_one_forces_greedy_lower_word
    {D : Finset ℕ} {M R : ℕ} {bits : List Bool}
    (hRM : R ≤ M)
    (hlen : bits.length = (localMersenneWeights M R).length)
    (hsum : weightedBoolSum (localMersenneWeights M R) bits =
      localPrefixQuotient D M)
    (hadm : localPrefixQuotient D M ≤ 2 ^ (M - 1) - 1)
    (hwindow : localBinarySuffix D 1 M < lowerBinaryWindow M R) :
    bits = integerGreedyBits (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) ∧
      localBinarySuffix D 1 M =
        integerGreedyRemainder (localMersenneWeights M R)
          (2 ^ (M - 1) - 1) := by
  simpa [localMersenneTarget] using
    (localBinarySuffix_forces_greedy_lower_word
      (D := D) (M := M) (R := R) (k := 1) (bits := bits)
      hRM hlen hsum hadm hwindow)

/-- Conversely, every non-greedy admissible lower word leaves at least one
complete upper window.  Thus it can never be the lower half of a filled
Boolean predecessor whose suffix is a binary word of width `M - R`. -/
theorem lowerBinaryWindow_le_defect_of_ne_greedy
    {M R C : ℕ} {weights : List ℕ} {bits : List Bool}
    (hwindowPos : 0 < lowerBinaryWindow M R)
    (hdom : GapDominates (lowerBinaryWindow M R) weights)
    (hlen : bits.length = weights.length)
    (hadm : weightedBoolSum weights bits ≤ C)
    (hne : bits ≠ integerGreedyBits weights C) :
    lowerBinaryWindow M R ≤ C - weightedBoolSum weights bits := by
  exact gap_le_remainder_of_ne_integerGreedyBits
    hwindowPos hdom hlen hadm hne

/-! ## The remaining greedy arithmetic is exposed, not assumed away -/

/-- A load on the next Möbius endpoint is safe when its binary repair value
`2*A+1-load` is nonnegative. -/
def RepairLoadSafe (load A : ℕ) : Prop :=
  load ≤ 2 * A + 1

/-- Once the lower-window uniqueness theorem is available, proving the load
cap for the deterministic greedy word is enough for every filled predecessor
in that window.  This theorem intentionally retains that greedy cap as a
hypothesis: it is the genuine arithmetic hinge. -/
theorem repairLoadSafe_of_greedy
    {M R C A : ℕ} {weights : List ℕ} {bits : List Bool}
    (endpointLoad : List Bool → ℕ)
    (hwindowPos : 0 < lowerBinaryWindow M R)
    (hdom : GapDominates (lowerBinaryWindow M R) weights)
    (hlen : bits.length = weights.length)
    (hfill : weightedBoolSum weights bits + A = C)
    (hA : A < lowerBinaryWindow M R)
    (hgreedy : RepairLoadSafe
      (endpointLoad (integerGreedyBits weights C))
      (integerGreedyRemainder weights C)) :
    RepairLoadSafe (endpointLoad bits) A := by
  obtain ⟨rfl, rfl⟩ := lower_word_eq_greedy_and_remainder_eq
    hwindowPos hdom hlen hfill hA
  exact hgreedy

/-- Exact iff form of the remaining hinge, assuming the greedy remainder is
itself in the upper window. -/
theorem all_filled_lower_words_repairLoadSafe_iff_greedy
    {M R C : ℕ} {weights : List ℕ}
    (endpointLoad : List Bool → ℕ)
    (hwindowPos : 0 < lowerBinaryWindow M R)
    (hdom : GapDominates (lowerBinaryWindow M R) weights)
    (hgreedyWindow :
      integerGreedyRemainder weights C < lowerBinaryWindow M R) :
    (∀ (bits : List Bool) (A : ℕ),
        bits.length = weights.length →
        weightedBoolSum weights bits + A = C →
        A < lowerBinaryWindow M R →
        RepairLoadSafe (endpointLoad bits) A) ↔
      RepairLoadSafe (endpointLoad (integerGreedyBits weights C))
        (integerGreedyRemainder weights C) := by
  constructor
  · intro hall
    apply hall (integerGreedyBits weights C)
      (integerGreedyRemainder weights C)
    · exact integerGreedyBits_length weights C
    · have hadm := integerGreedyBits_admissible weights C
      simp only [integerGreedyRemainder]
      omega
    · exact hgreedyWindow
  · intro hgreedy bits A hlen hfill hA
    exact repairLoadSafe_of_greedy endpointLoad hwindowPos hdom
      hlen hfill hA hgreedy

end Erdos249257.BooleanMobiusGreedyReduction
