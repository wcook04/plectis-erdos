import Erdos249257.HalfCylinderMiddleCarryLowerBound
import Erdos249257.HalfUpperResetCriticalBand
import Erdos249257.HalfCylinderPullbackCardPropagation
import Erdos249257.BooleanMobiusExactTransition

/-!
# All-scale ancestry of a unit seam remainder

The fatal-borrow reduction leaves one degenerate midpoint branch in which
the deterministic seam remainder is exactly one.  This module records the
arithmetic law forced by that state.  After an upper reset and `k` right
steps, the reset charge and the genuine divisor-incidence pulses fill the
dyadic cylinder to within exactly one unit.  Consequently every terminal
base-four suffix packet is congruent to `-1` at its own scale.

This is unconditional finite arithmetic.  It does not assert that the unit
state is impossible; it replaces that question by a nested family of exact
divisibility certificates which retains the selected-support ancestry.
-/

namespace Erdos249257

open HalfCylinderIntegerGreedy
open HalfUpperResetCriticalBand
open HalfCylinderPullbackCardPropagation
open HalfCylinderFiniteShadow
open HalfCarryReachability

noncomputable section

/-- A unit endpoint fills the upper-reset/right-run cylinder to within
exactly one unit. -/
theorem seamUpperThenRightRun_unit_exactCharge
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hunit : seamIntegerGreedyRemainder (d + k + 1) = 1) :
    4 ^ k *
          (4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse) +
        affineRightRunCharge
          (fun j ↦
            (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k + 1 =
      2 ^ (d + k + 1) := by
  have hcylinder := seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  omega

/-- With the natural late-run bound `k ≤ d`, the unit endpoint says that
one plus the whole right-run pulse packet is a multiple of `4^k`. -/
theorem four_pow_dvd_one_add_rightRunCharge_of_unit
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hunit : seamIntegerGreedyRemainder (d + k + 1) = 1) :
    4 ^ k ∣
      1 + affineRightRunCharge
        (fun j ↦
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k := by
  let E := 4 * (seamAdjacentCut d hd5).overshoot +
    (seamAdjacentCut d hd5).abovePulse
  let C := affineRightRunCharge
    (fun j ↦ (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k
  have htotal := seamUpperThenRightRun_unit_exactCharge
    hd5 hcarry hrun hunit
  change 4 ^ k * E + C + 1 = 2 ^ (d + k + 1) at htotal
  have hfactor :
      4 ^ k * 2 ^ (d - k + 1) = 2 ^ (d + k + 1) := by
    rw [show 4 ^ k = 2 ^ (2 * k) by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
    congr 1
    omega
  have hpow : 4 ^ k ∣ 2 ^ (d + k + 1) := by
    rw [← hfactor]
    exact dvd_mul_right (4 ^ k) (2 ^ (d - k + 1))
  have hsum : 4 ^ k ∣ 4 ^ k * E + (C + 1) := by
    have heq : 4 ^ k * E + (C + 1) = 2 ^ (d + k + 1) := by
      omega
    rw [heq]
    exact hpow
  have hsum' : 4 ^ k ∣ (1 + C) + 4 ^ k * E := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsum
  exact (Nat.dvd_add_iff_left (dvd_mul_right (4 ^ k) E)).mpr hsum'

/-- Every terminal suffix of a unit-endpoint right run carries the same
exact `-1` residue.  This is the all-scale selected-ancestry law: the last
`r` genuine pulse digits, by themselves, cancel one modulo `4^r`. -/
theorem four_pow_dvd_one_add_rightRunCharge_suffix_of_unit
    {d k r : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d) (hr : r ≤ k)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hunit : seamIntegerGreedyRemainder (d + k + 1) = 1) :
    4 ^ r ∣
      1 + affineRightRunCharge
        (fun q ↦
          (seamAdjacentCut (d + (k - r + q) + 1) (by omega)).belowPulse) r := by
  let pulse : ℕ → ℕ := fun j ↦
    (seamAdjacentCut (d + j + 1) (by omega)).belowPulse
  have hfull : 4 ^ k ∣ 1 + affineRightRunCharge pulse k := by
    simpa [pulse] using
      four_pow_dvd_one_add_rightRunCharge_of_unit
        hd5 hk hcarry hrun hunit
  obtain ⟨G, hG⟩ := hfull
  have hsuffix := four_pow_dvd_remainder_add_affineRightRunCharge_suffix
    1 G pulse k r hr
  apply hsuffix
  simpa [Nat.add_comm] using hG

/-- Before the two-thirds crossing, a unit endpoint pins the frozen reset
support's binary multiplicity window to the inverse-of-three residue.  In
division-free form, `3 F = 1 (mod 4^k)`, where `F` is the numerator of the
`2k` support-coefficient window beginning at binary row `2(d+1)`.

This is the quotient/defect form of the unit-state obstruction: it contains
no rational remainder denominator. -/
theorem four_pow_dvd_three_mul_resetMultiplicityWindow_add_fourPow_sub_one_of_unit
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hshort : 2 * (d + k) < 3 * d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hunit : seamIntegerGreedyRemainder (d + k + 1) = 1) :
    4 ^ k ∣
      3 * finiteCoeffWindowNumerator
          (↑(seamWordSupport (seamAdjacentCut d hd5).above) : Set ℕ)
          (2 * (d + 1)) (2 * k) + 4 ^ k - 1 := by
  let A := seamWordSupport (seamAdjacentCut d hd5).above
  let pulse : ℕ → ℕ := fun j ↦
    (seamAdjacentCut (d + j + 1) (by omega)).belowPulse
  have hpulse : ∀ j : ℕ, j < k →
      pulse j = ∑ e ∈ A, rowPulse (d + 1 + j) e := by
    intro j hj
    have hlate : 2 * (d + j + 1) < 3 * d := by omega
    have h := seamUpperThenRightRun_belowPulse_eq_resetSupportSum
      hd5 hcarry hrun (q := j) (by omega) hlate
    simpa [A, pulse, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hpulseCharge :
      affineRightRunCharge pulse k =
        affineRightRunCharge
          (fun j ↦ ∑ e ∈ A, rowPulse (d + 1 + j) e) k := by
    have hprefix : ∀ m : ℕ, m ≤ k →
        affineRightRunCharge pulse m =
          affineRightRunCharge
            (fun j ↦ ∑ e ∈ A, rowPulse (d + 1 + j) e) m := by
      intro m hm
      induction m with
      | zero => simp [affineRightRunCharge]
      | succ m ih =>
          simp only [affineRightRunCharge, ih (by omega)]
          rw [hpulse m (by omega)]
    exact hprefix k (le_refl k)
  have hdiv : 4 ^ k ∣ 1 + affineRightRunCharge pulse k := by
    simpa [pulse] using
      four_pow_dvd_one_add_rightRunCharge_of_unit
        hd5 hk hcarry hrun hunit
  let F := finiteCoeffWindowNumerator (↑A : Set ℕ) (2 * (d + 1)) (2 * k)
  have hbridge :
      3 * affineRightRunCharge pulse k =
        3 * F + 4 * (4 ^ k - 1) := by
    rw [hpulseCharge]
    simpa [A, F] using
      (three_mul_affineRightRunCharge_eq_multiplicityWindow_add_geometric
        (d + 1) A k)
  have hdivThree : 4 ^ k ∣ 3 * (1 + affineRightRunCharge pulse k) :=
    dvd_mul_of_dvd_right hdiv 3
  have hpowPos : 0 < 4 ^ k := pow_pos (by norm_num) k
  have hsum :
      4 ^ k ∣ (3 * F + 4 ^ k - 1) + 3 * 4 ^ k := by
    have heq :
        (3 * F + 4 ^ k - 1) + 3 * 4 ^ k =
          3 * (1 + affineRightRunCharge pulse k) := by
      omega
    rw [heq]
    exact hdivThree
  have hmultiple : 4 ^ k ∣ 3 * 4 ^ k := by
    exact dvd_mul_left (4 ^ k) 3
  have htarget : 4 ^ k ∣ 3 * F + 4 ^ k - 1 :=
    (Nat.dvd_add_iff_left hmultiple).mpr hsum
  simpa [A, F]

/-- The same obstruction after the finite multiplicity window is telescoped:
the endpoint centered Möbius carry must lie in the single residue class
`-4/3` modulo `4^k`.  This is the sparse quotient/defect lattice which a
future Archimedean carry bound can exclude. -/
theorem int_four_pow_dvd_three_mul_resetCarryEnd_add_four_of_unit
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hshort : 2 * (d + k) < 3 * d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hunit : seamIntegerGreedyRemainder (d + k + 1) = 1) :
    ((4 ^ k : ℕ) : ℤ) ∣
      3 * mobiusCenteredHalfCarry
          (↑(seamWordSupport (seamAdjacentCut d hd5).above) : Set ℕ)
          (2 * (d + k) + 1) + 4 := by
  let A := seamWordSupport (seamAdjacentCut d hd5).above
  let F := finiteCoeffWindowNumerator (↑A : Set ℕ) (2 * (d + 1)) (2 * k)
  have hnat :=
    four_pow_dvd_three_mul_resetMultiplicityWindow_add_fourPow_sub_one_of_unit
      hd5 hk hshort hcarry hrun hunit
  change 4 ^ k ∣ 3 * F + 4 ^ k - 1 at hnat
  obtain ⟨q, hq⟩ := hnat
  have hqAdd : 3 * F + 4 ^ k = 4 ^ k * q + 1 := by
    have hpowPos : 0 < 4 ^ k := pow_pos (by norm_num) k
    omega
  have hqAddInt :
      3 * (F : ℤ) + (4 ^ k : ℕ) =
        ((4 ^ k : ℕ) : ℤ) * q + 1 := by
    exact_mod_cast hqAdd
  have hcenter :=
    finiteCoeffWindowNumerator_sub_baseline_eq_centeredCarry
      (↑A : Set ℕ) (2 * (d + 1)) (2 * k) (by omega)
  have hpow : (2 : ℤ) ^ (2 * k) = (4 : ℤ) ^ k := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [hpow] at hcenter
  have hstartIndex : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
  have hendIndex : 2 * (d + 1) + 2 * k - 1 = 2 * (d + k) + 1 := by omega
  rw [hstartIndex, hendIndex] at hcenter
  change
    (F : ℤ) - ((4 : ℤ) ^ k - 1) =
      (4 : ℤ) ^ k *
          mobiusCenteredHalfCarry (↑A : Set ℕ) (2 * d + 1) -
        mobiusCenteredHalfCarry (↑A : Set ℕ) (2 * (d + k) + 1)
    at hcenter
  refine ⟨4 + 3 * mobiusCenteredHalfCarry (↑A : Set ℕ) (2 * d + 1) - q, ?_⟩
  change
    3 * mobiusCenteredHalfCarry (↑A : Set ℕ) (2 * (d + k) + 1) + 4 =
      ((4 ^ k : ℕ) : ℤ) *
        (4 + 3 * mobiusCenteredHalfCarry (↑A : Set ℕ) (2 * d + 1) - q)
  have hcastPow : (((4 ^ k : ℕ) : ℤ)) = (4 : ℤ) ^ k := by
    norm_cast
  rw [hcastPow] at hqAddInt ⊢
  ring_nf at hcenter hqAddInt ⊢
  linarith

/-! ## Ordered boundary transport from a unit pulse -/

/-- A unit boundary pulse is ordered information, not merely a small scalar:
the odd divisor multiplicity vanishes and the following even multiplicity is
exactly one. -/
theorem pairedSupportCoeff_eq_zero_one_of_wordPulse_eq_one
    {s : ℕ} (b : SeamRowWord s)
    (hpulse : wordPulse s b.toNatWord = 1) :
    supportCoeff (↑(seamWordSupport b) : Set ℕ) (2 * s + 1) = 0 ∧
      supportCoeff (↑(seamWordSupport b) : Set ℕ) (2 * s + 2) = 1 := by
  have hpair := wordPulse_eq_pairedSupportCoeff b
  omega

/-- The ordered coefficient pair `(0, 1)` has an exact two-step quotient
signature: it sends a quotient `Q` to `4Q + 1`.  This is the quotient/defect
coordinate in which a fatal unit-pulse row should next be propagated. -/
theorem localPrefixQuotient_add_two_eq_four_mul_add_one_of_wordPulse_eq_one
    {s : ℕ} (b : SeamRowWord s)
    (hpulse : wordPulse s b.toNatWord = 1) :
    localPrefixQuotient (seamWordSupport b) (2 * s + 2) =
      4 * localPrefixQuotient (seamWordSupport b) (2 * s) + 1 := by
  have hD : ∀ d ∈ seamWordSupport b, 2 ≤ d := by
    intro d hd
    exact (seamWordSupport_below hd).1
  obtain ⟨hodd, heven⟩ :=
    pairedSupportCoeff_eq_zero_one_of_wordPulse_eq_one b hpulse
  have hsuccOdd := localPrefixQuotient_succ
    (D := seamWordSupport b) (M := 2 * s) hD
  have hsuccEven := localPrefixQuotient_succ
    (D := seamWordSupport b) (M := 2 * s + 1) hD
  rw [endpointDivisorContribution_eq_supportCoeff (by omega), hodd] at hsuccOdd
  rw [endpointDivisorContribution_eq_supportCoeff (by omega), heven] at hsuccEven
  have hevenIndex : 2 * s + 1 + 1 = 2 * s + 2 := by omega
  rw [hevenIndex] at hsuccEven
  omega

/-- Inserting the terminal rank does not disturb the unit pulse, so the same
two-step quotient signature holds for the support used by the fatal midpoint
row itself. -/
theorem localPrefixQuotient_insert_terminal_add_two_eq_four_mul_add_one_of_wordPulse_eq_one
    {s : ℕ} (hs5 : 5 ≤ s) (b : SeamRowWord s)
    (hpulse : wordPulse s b.toNatWord = 1) :
    localPrefixQuotient (insert s (seamWordSupport b)) (2 * s + 2) =
      4 * localPrefixQuotient (insert s (seamWordSupport b)) (2 * s) + 1 := by
  have hD : ∀ d ∈ insert s (seamWordSupport b), 2 ≤ d := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · omega
    · exact (seamWordSupport_below hd).1
  have hpair := pairedSupportCoeff_insert_terminal_eq_wordPulse hs5 b
  rw [hpulse] at hpair
  have hcoe :
      (↑(insert s (seamWordSupport b)) : Set ℕ) =
        insert s (↑(seamWordSupport b) : Set ℕ) := by
    ext d
    simp
  have hodd : supportCoeff
      (↑(insert s (seamWordSupport b)) : Set ℕ) (2 * s + 1) = 0 := by
    rw [hcoe]
    omega
  have heven : supportCoeff
      (↑(insert s (seamWordSupport b)) : Set ℕ) (2 * s + 2) = 1 := by
    rw [hcoe]
    omega
  have hsuccOdd := localPrefixQuotient_succ
    (D := insert s (seamWordSupport b)) (M := 2 * s) hD
  have hsuccEven := localPrefixQuotient_succ
    (D := insert s (seamWordSupport b)) (M := 2 * s + 1) hD
  rw [endpointDivisorContribution_eq_supportCoeff (by omega), hodd] at hsuccOdd
  rw [endpointDivisorContribution_eq_supportCoeff (by omega), heven] at hsuccEven
  have hevenIndex : 2 * s + 1 + 1 = 2 * s + 2 := by omega
  rw [hevenIndex] at hsuccEven
  omega

/-- Therefore an exact fatal midpoint quotient followed by a unit pulse lands
two rows later at `2^(2s+1)+1`, namely two units above the half-endpoint
target at that scale. -/
theorem localPrefixQuotient_insert_terminal_add_two_eq_pow_add_one_of_midpoint_unit
    {s : ℕ} (hs5 : 5 ≤ s) (b : SeamRowWord s)
    (hpulse : wordPulse s b.toNatWord = 1)
    (hmid : localPrefixQuotient (insert s (seamWordSupport b)) (2 * s) =
      2 ^ (2 * s - 1)) :
    localPrefixQuotient (insert s (seamWordSupport b)) (2 * s + 2) =
      2 ^ (2 * s + 1) + 1 := by
  rw [localPrefixQuotient_insert_terminal_add_two_eq_four_mul_add_one_of_wordPulse_eq_one
    hs5 b hpulse, hmid]
  have hindex : 2 * s + 1 = (2 * s - 1) + 2 := by omega
  rw [hindex, pow_add]
  norm_num
  ring

#print axioms seamUpperThenRightRun_unit_exactCharge
#print axioms four_pow_dvd_one_add_rightRunCharge_of_unit
#print axioms four_pow_dvd_one_add_rightRunCharge_suffix_of_unit
#print axioms four_pow_dvd_three_mul_resetMultiplicityWindow_add_fourPow_sub_one_of_unit
#print axioms int_four_pow_dvd_three_mul_resetCarryEnd_add_four_of_unit
#print axioms pairedSupportCoeff_eq_zero_one_of_wordPulse_eq_one
#print axioms localPrefixQuotient_add_two_eq_four_mul_add_one_of_wordPulse_eq_one
#print axioms localPrefixQuotient_insert_terminal_add_two_eq_four_mul_add_one_of_wordPulse_eq_one
#print axioms localPrefixQuotient_insert_terminal_add_two_eq_pow_add_one_of_midpoint_unit

end

end Erdos249257
