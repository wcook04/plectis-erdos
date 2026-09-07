import Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand
import Erdos257PeriodNoncollapse.HalfCylinderResetSqrtEscape
import Erdos257PeriodNoncollapse.HalfResetSqrtEscapeScaleProducers
import Erdos257PeriodNoncollapse.HalfCylinderFiniteShadow
import Mathlib.Tactic

/-!
# Support-cardinality propagation through half cylinders

The exact half-seam pullbacks produce base-four cylinders

`R + C = 4^k * Q`.

The useful invariant is not monotonicity of the raw coordinate `Q` (which is
false), but domination of the endpoint support cardinality by `Q`.  Every
actual pulse is at most twice the current support cardinality.  Hence, once
`Q` is at least the endpoint cardinality plus two, every affine cylinder
digit is at most `3 * Q`.  The geometric series then absorbs the whole
charge and forces `Q ≤ R`.

This file proves that propagation principle and specializes it to an actual
upper-reset/right-run block.  It isolates the remaining producer as a scalar
critical-gap/cardinality comparison; no congruence or finite-search
hypothesis is inserted.
-/

namespace Erdos257PeriodNoncollapse.HalfCylinderPullbackCardPropagation

open Finset
open HalfCylinderIntegerGreedy
open HalfUpperResetCriticalBand
open HalfCylinderFiniteShadow
open HalfCarryReachability

/-- A selected rank contributes its own nonnegative row pulse to the whole
word pulse.  This generic form is useful for the upper adjacent-cut word,
which is identified with the next greedy word only after a carry. -/
theorem rowPulse_le_wordPulse_of_mem
    {s d : ℕ} (b : SeamRowWord s) (hd : d ∈ seamWordSupport b) :
    rowPulse s d ≤ wordPulse s b.toNatWord := by
  classical
  rw [wordPulse_eq_sum_seamWordSupport]
  exact Finset.single_le_sum (fun e _ ↦ Nat.zero_le (rowPulse s e)) hd

/-- Every mature carry has a genuinely positive upper pulse.  The reason is
structural rather than quantitative: the carry identifies the next greedy
word with the false-extension of the upper word, rank `2` is forced in that
next word, and rank `2` contributes exactly one unit across every seam row. -/
theorem seamAdjacentCut_abovePulse_pos_of_successorCarries
    {s : ℕ} (hs12 : 12 ≤ s)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    0 < (seamAdjacentCut s (by omega)).abovePulse := by
  have hword := seamGreedyWord_succ_eq_upperBranch s (by omega) hcarry
  have h2next :=
    (two_three_six_mem_seamGreedySupport (s + 1) (by omega)).1
  rw [hword, seamWordSupport_extend_false (by omega)] at h2next
  have hp := rowPulse_le_wordPulse_of_mem
    (s := s) (d := 2) (seamAdjacentCut s (by omega)).above h2next
  have h2even : 2 ∣ 2 * s + 2 := by omega
  have h2odd : ¬ 2 ∣ 2 * s + 1 := by omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, h2even, h2odd]
  change 0 < wordPulse s
      (seamAdjacentCut s (by omega)).above.toNatWord
  rw [hp2] at hp
  omega

/-- The half-cylinder lower bound at a carry is in fact the sharp
three-halves source bound.  Separation gives `gap ≤ R + O`; positivity of
the compulsory rank-two upper pulse upgrades the carry inequality from
`4O ≤ gap` to `4O < gap`.  Since `gap = 4 * 2^(s-1)`, the remainder lies
strictly above `3 * 2^(s-1)`. -/
theorem seamSuccessorCarries_remainder_gt_threeHalf
    {s : ℕ} (hs12 : 12 ≤ s)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    3 * 2 ^ (s - 1) < seamIntegerGreedyRemainder s := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s (by omega)
  have hbelowAbove : F.oldSum K.below < F.oldSum K.above :=
    lt_of_le_of_lt K.below_admissible K.above_strict
  have hsep := F.separated hbelowAbove
  have hbelow := K.old_below_add_remainder
  have habove := K.capacity_add_overshoot
  change F.oldSum K.below + K.remainder = seamSubsetTarget s at hbelow
  change seamSubsetTarget s + K.overshoot = F.oldSum K.above at habove
  have hgapRO : F.gap ≤ K.remainder + K.overshoot := by
    omega
  have hpulse : 0 < K.abovePulse := by
    exact seamAdjacentCut_abovePulse_pos_of_successorCarries hs12 hcarry
  have hfourO : 4 * K.overshoot < F.gap := by
    change 4 * K.overshoot + K.abovePulse ≤ F.gap at hcarry
    omega
  change 2 ^ (s + 1) ≤
      (seamAdjacentCut s (by omega)).remainder +
        (seamAdjacentCut s (by omega)).overshoot at hgapRO
  change 4 * (seamAdjacentCut s (by omega)).overshoot <
      2 ^ (s + 1) at hfourO
  rw [seamAdjacentCut_remainder (by omega)] at hgapRO
  have hpow : (2 : ℕ) ^ (s + 1) = 4 * 2 ^ (s - 1) := by
    rw [show s + 1 = (s - 1) + 2 by omega, pow_add]
    norm_num
    ring
  rw [hpow] at hgapRO hfourO
  omega

/-! ## Pulse registers are binary multiplicity windows -/

/-- The total pulse of an arbitrary fixed support is exactly the paired
odd/even divisor-multiplicity coefficient in the two newly exposed binary
rows.  This is the finite-support form of
`wordPulse_eq_pairedSupportCoeff`, with no seam-word hypothesis. -/
theorem sum_rowPulse_eq_pairedSupportCoeff
    (b : ℕ) (A : Finset ℕ) :
    (∑ e ∈ A, rowPulse b e) =
      supportCoeff (↑A : Set ℕ) (2 * b + 2) +
        2 * supportCoeff (↑A : Set ℕ) (2 * b + 1) := by
  classical
  rw [supportCoeff_finset_eq_indicatorSum,
    supportCoeff_finset_eq_indicatorSum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  unfold rowPulse
  simp [Nat.mem_divisors]

/-- Two binary coefficient-window steps are exactly one base-four
fixed-support pulse step.  Thus the pulse register used by the half-cylinder
pullback is not merely analogous to the multiplicity tail: it is literally
its division-free finite numerator on the paired interval
`(2b, 2b + 2k]`. -/
theorem fixedSupportPulseCharge_eq_finiteCoeffWindowNumerator
    (b : ℕ) (A : Finset ℕ) (k : ℕ) :
    fixedSupportPulseCharge b A k =
      finiteCoeffWindowNumerator (↑A : Set ℕ) (2 * b) (2 * k) := by
  induction k with
  | zero =>
      simp [fixedSupportPulseCharge, finiteCoeffWindowNumerator]
  | succ k ih =>
      have hoddCoeff :
          supportCoeff (↑A : Set ℕ) (2 * b + 2 * k + 1) =
            supportCoeff (↑A : Set ℕ) (2 * (b + k) + 1) := by
        congr 1
        omega
      have hevenCoeff :
          supportCoeff (↑A : Set ℕ) (2 * b + (2 * k + 1) + 1) =
            supportCoeff (↑A : Set ℕ) (2 * (b + k) + 2) := by
        congr 1
        omega
      rw [fixedSupportPulseCharge,
        show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        finiteCoeffWindowNumerator, finiteCoeffWindowNumerator, ih,
        sum_rowPulse_eq_pairedSupportCoeff, hoddCoeff, hevenCoeff]
      omega

/-- The centered finite multiplicity window is a pure boundary term in the
signed Möbius carry.  This is the division-free finite form of the `X(P)`
lattice coordinate: all interior excess incidences telescope. -/
theorem finiteCoeffWindowNumerator_sub_baseline_eq_centeredCarry
    (A : Set ℕ) (n J : ℕ) (hn : 1 ≤ n) :
    (finiteCoeffWindowNumerator A n J : ℤ) - ((2 : ℤ) ^ J - 1) =
      (2 : ℤ) ^ J * mobiusCenteredHalfCarry A (n - 1) -
        mobiusCenteredHalfCarry A (n + J - 1) := by
  induction J with
  | zero => simp [finiteCoeffWindowNumerator]
  | succ J ih =>
      have hrec := mobiusCenteredHalfCarry_succ A (n + J - 1)
      rw [show n + J - 1 + 1 = n + J by omega,
        show n + J - 1 + 2 = n + J + 1 by omega] at hrec
      rw [show n + (J + 1) - 1 = n + J by omega]
      calc
        (finiteCoeffWindowNumerator A n (J + 1) : ℤ) -
              ((2 : ℤ) ^ (J + 1) - 1) =
            2 * ((finiteCoeffWindowNumerator A n J : ℤ) -
              ((2 : ℤ) ^ J - 1)) +
                (supportCoeff A (n + J + 1) : ℤ) - 1 := by
          simp only [finiteCoeffWindowNumerator, Nat.cast_add, Nat.cast_mul,
            Nat.cast_ofNat, pow_succ]
          ring
        _ = 2 * ((2 : ℤ) ^ J * mobiusCenteredHalfCarry A (n - 1) -
              mobiusCenteredHalfCarry A (n + J - 1)) +
                (supportCoeff A (n + J + 1) : ℤ) - 1 := by
          rw [ih]
        _ = (2 : ℤ) ^ (J + 1) * mobiusCenteredHalfCarry A (n - 1) -
              mobiusCenteredHalfCarry A (n + J) := by
          rw [hrec, pow_succ]
          ring

/-- Base-four form of the same telescoping law.  The frozen pulse packet
minus its layer-one baseline is exactly the difference of two centered
Möbius carries at the binary endpoints. -/
theorem fixedSupportPulseCharge_sub_geometric_eq_centeredCarry
    (b : ℕ) (A : Finset ℕ) (k : ℕ) (hb : 1 ≤ b) :
    (fixedSupportPulseCharge b A k : ℤ) - ((4 : ℤ) ^ k - 1) =
      (4 : ℤ) ^ k *
          mobiusCenteredHalfCarry (↑A : Set ℕ) (2 * b - 1) -
        mobiusCenteredHalfCarry (↑A : Set ℕ) (2 * b + 2 * k - 1) := by
  have h := finiteCoeffWindowNumerator_sub_baseline_eq_centeredCarry
    (↑A : Set ℕ) (2 * b) (2 * k) (by omega)
  have hpow : (2 : ℤ) ^ (2 * k) = (4 : ℤ) ^ k := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [← fixedSupportPulseCharge_eq_finiteCoeffWindowNumerator,
    hpow] at h
  simpa only [show 2 * b + 2 * k - 1 = 2 * b + 2 * k - 1 by rfl]
    using h

/-- The affine `+4` digit used by an actual right-run cylinder contributes
only the exact geometric baseline.  After clearing the denominator `3`, the
remaining register is the fixed-support multiplicity window. -/
theorem three_mul_affineRightRunCharge_eq_fixedSupport_add_geometric
    (b : ℕ) (A : Finset ℕ) (k : ℕ) :
    3 * affineRightRunCharge
          (fun q ↦ ∑ e ∈ A, rowPulse (b + q) e) k =
      3 * fixedSupportPulseCharge b A k + 4 * (4 ^ k - 1) := by
  induction k with
  | zero =>
      simp [affineRightRunCharge, fixedSupportPulseCharge]
  | succ k ih =>
      have hpowpos : 0 < 4 ^ k := pow_pos (by norm_num) k
      simp only [affineRightRunCharge, fixedSupportPulseCharge, pow_succ]
      omega

/-- Division-free multiplicity-coordinate form of the complete affine
right-run register.  This is the exact bridge to the excess-multiplicity
window `X(P)`: the only discrepancy is the explicit all-ones baseline
`4(4^k-1)/3`. -/
theorem three_mul_affineRightRunCharge_eq_multiplicityWindow_add_geometric
    (b : ℕ) (A : Finset ℕ) (k : ℕ) :
    3 * affineRightRunCharge
          (fun q ↦ ∑ e ∈ A, rowPulse (b + q) e) k =
      3 * finiteCoeffWindowNumerator (↑A : Set ℕ) (2 * b) (2 * k) +
        4 * (4 ^ k - 1) := by
  rw [three_mul_affineRightRunCharge_eq_fixedSupport_add_geometric,
    fixedSupportPulseCharge_eq_finiteCoeffWindowNumerator]

/-- A base-four affine charge whose digits are bounded by `3Q` is at most
`Q(4^k-1)`.  This is the exact geometric absorption estimate used by the
pullback-card invariant. -/
theorem affineRightRunCharge_le_coordinate_geometric
    (pulse : ℕ → ℕ) (Q k : ℕ)
    (hdigit : ∀ j : ℕ, j < k → pulse j + 4 ≤ 3 * Q) :
    affineRightRunCharge pulse k ≤ Q * (4 ^ k - 1) := by
  revert hdigit
  induction k with
  | zero =>
      intro _hdigit
      simp [affineRightRunCharge]
  | succ k ih =>
      intro hdigit
      have hprev := ih (fun j hj ↦ hdigit j (by omega))
      have hlast := hdigit k (by omega)
      have hpow : 4 ^ k = (4 ^ k - 1) + 1 := by
        have : 0 < 4 ^ k := pow_pos (by norm_num) k
        omega
      have hpowSucc : 4 ^ (k + 1) - 1 = 4 * (4 ^ k - 1) + 3 := by
        rw [pow_succ]
        omega
      calc
        affineRightRunCharge pulse (k + 1) =
            4 * affineRightRunCharge pulse k + (pulse k + 4) := by
          simp [affineRightRunCharge, Nat.add_assoc]
        _ ≤ 4 * (Q * (4 ^ k - 1)) + 3 * Q :=
          Nat.add_le_add (Nat.mul_le_mul_left 4 hprev) hlast
        _ = Q * (4 ^ (k + 1) - 1) := by
          rw [hpowSucc]
          ring

/-- Algebraic exact-cylinder amplification from a division-free `2Q` charge
budget. -/
theorem exactCylinder_amplification_of_twoBudget
    {R C Q k : ℕ}
    (hexact : R + C = 4 ^ k * Q)
    (hcharge : 3 * C + 2 * Q ≤ 2 * Q * 4 ^ k) :
    4 ^ k * Q + 2 * Q ≤ 3 * R := by
  have hscaled : 3 * R + 3 * C = 3 * (4 ^ k * Q) := by
    omega
  ring_nf at hcharge hscaled ⊢
  omega

/-- Exact-cylinder amplification under the actual `2Q` digit budget.  The
ordinary absorption lemma only keeps `Q ≤ R`; this strengthened form keeps
the base-four scale and is therefore suitable for recursive reset packets.
The charge estimate itself is the existing
`three_mul_affineRightRunCharge_add_two_mul_le`; this theorem is its exact
cylinder consumer. -/
theorem scaled_coordinate_add_two_coordinate_le_three_remainder
    {R Q k : ℕ} (pulse : ℕ → ℕ)
    (hexact : R + affineRightRunCharge pulse k = 4 ^ k * Q)
    (hdigit : ∀ j : ℕ, j < k → pulse j + 4 ≤ 2 * Q) :
    4 ^ k * Q + 2 * Q ≤ 3 * R := by
  have hcharge :=
    three_mul_affineRightRunCharge_add_two_mul_le pulse Q k hdigit
  exact exactCylinder_amplification_of_twoBudget hexact hcharge

/-- Geometric charge absorption in an exact base-four cylinder forces the
initial coordinate below the terminal remainder. -/
theorem coordinate_le_remainder_of_exactCylinder
    {R C Q k : ℕ}
    (hexact : R + C = 4 ^ k * Q)
    (hcharge : C ≤ Q * (4 ^ k - 1)) :
    Q ≤ R := by
  have hpow : 4 ^ k = (4 ^ k - 1) + 1 := by
    have : 0 < 4 ^ k := pow_pos (by norm_num) k
    omega
  have hexact' : R + C = Q * (4 ^ k - 1) + Q := by
    calc
      R + C = 4 ^ k * Q := hexact
      _ = ((4 ^ k - 1) + 1) * Q := by rw [← hpow]
      _ = Q * (4 ^ k - 1) + Q := by ring
  omega

/-- The fixed-support charge in a backward pullback obeys the same geometric
bound.  Its digits have no affine `+4`, so the support-cardinality estimate
is even stronger than in a forward right run. -/
theorem fixedSupportPulseCharge_le_coordinate_geometric
    {b : ℕ} {A : Finset ℕ} (hA : ∀ e ∈ A, 2 ≤ e)
    (Q k : ℕ) (hcard : A.card ≤ Q) :
    fixedSupportPulseCharge b A k ≤ Q * (4 ^ k - 1) := by
  induction k with
  | zero => simp [fixedSupportPulseCharge]
  | succ k ih =>
      have hdigit :
          (∑ e ∈ A, rowPulse (b + k) e) ≤ 3 * Q := by
        have htwo :
            (∑ e ∈ A, rowPulse (b + k) e) ≤ 2 * A.card := by
          calc
            (∑ e ∈ A, rowPulse (b + k) e) ≤
                ∑ _e ∈ A, 2 := by
              apply Finset.sum_le_sum
              intro e he
              exact rowPulse_le_two (b + k) e (hA e he)
            _ = 2 * A.card := by simp [Nat.mul_comm]
        omega
      have hpow : 4 ^ k = (4 ^ k - 1) + 1 := by
        have : 0 < 4 ^ k := pow_pos (by norm_num) k
        omega
      have hpowSucc : 4 ^ (k + 1) - 1 = 4 * (4 ^ k - 1) + 3 := by
        rw [pow_succ]
        omega
      calc
        fixedSupportPulseCharge b A (k + 1) =
            4 * fixedSupportPulseCharge b A k +
              ∑ e ∈ A, rowPulse (b + k) e := by
          simp [fixedSupportPulseCharge]
        _ ≤ 4 * (Q * (4 ^ k - 1)) + 3 * Q :=
          Nat.add_le_add (Nat.mul_le_mul_left 4 ih) hdigit
        _ = Q * (4 ^ (k + 1) - 1) := by
          rw [hpowSucc]
          ring

/-- The fixed-support block also obeys the sharper `2Q` digit budget.  This
is the backward-packet analogue of the existing affine right-run estimate. -/
theorem three_mul_fixedSupportPulseCharge_add_two_mul_le
    {b : ℕ} {A : Finset ℕ} (hA : ∀ e ∈ A, 2 ≤ e)
    (Q k : ℕ) (hcard : A.card ≤ Q) :
    3 * fixedSupportPulseCharge b A k + 2 * Q ≤
      2 * Q * 4 ^ k := by
  induction k with
  | zero => simp [fixedSupportPulseCharge]
  | succ k ih =>
      have hdigit :
          (∑ e ∈ A, rowPulse (b + k) e) ≤ 2 * Q := by
        calc
          (∑ e ∈ A, rowPulse (b + k) e) ≤
              ∑ _e ∈ A, 2 := by
            apply Finset.sum_le_sum
            intro e he
            exact rowPulse_le_two (b + k) e (hA e he)
          _ = 2 * A.card := by simp [Nat.mul_comm]
          _ ≤ 2 * Q := Nat.mul_le_mul_left 2 hcard
      simp only [fixedSupportPulseCharge, pow_succ]
      ring_nf at ih hdigit ⊢
      omega

/-- Quantitative backward-packet consumer.  A nonnegative pullback
coordinate whose fixed support fits its `2Q` digit budget is amplified by the
entire base-four block at the critical gap. -/
theorem fixedSupport_exactCylinder_amplification
    {b k G Q : ℕ} {A : Finset ℕ}
    (hA : ∀ e ∈ A, 2 ≤ e) (hcard : A.card ≤ Q)
    (hexact : G + fixedSupportPulseCharge b A k = 4 ^ k * Q) :
    4 ^ k * Q + 2 * Q ≤ 3 * G := by
  apply exactCylinder_amplification_of_twoBudget hexact
  exact three_mul_fixedSupportPulseCharge_add_two_mul_le hA Q k hcard

/-- The two quantitative stage bounds compose without discarding either
base-four scale. -/
theorem twoStage_amplification
    {Q G R b k : ℕ}
    (hbackAmp : 4 ^ b * Q + 2 * Q ≤ 3 * G)
    (hforwardAmp : 4 ^ k * G + 2 * G ≤ 3 * R) :
    4 ^ (b + k) * Q + 2 * 4 ^ k * Q + 6 * G ≤ 9 * R := by
  have hbackScaled := Nat.mul_le_mul_left (4 ^ k) hbackAmp
  have hforwardScaled := Nat.mul_le_mul_left 3 hforwardAmp
  rw [pow_add]
  ring_nf at hbackScaled hforwardScaled ⊢
  omega

/-- Two exact `2Q`-budget cylinders compose without discarding their scale.
This is the abstract parent/child packet inequality: the first cylinder
amplifies `Q` to `G`, and the second amplifies `G` to `R`. -/
theorem twoCylinder_amplification
    {Q G R Cback Cforward b k : ℕ}
    (hback : G + Cback = 4 ^ b * Q)
    (hbackBudget : 3 * Cback + 2 * Q ≤ 2 * Q * 4 ^ b)
    (hforward : R + Cforward = 4 ^ k * G)
    (hforwardBudget : 3 * Cforward + 2 * G ≤ 2 * G * 4 ^ k) :
    4 ^ (b + k) * Q + 2 * 4 ^ k * Q + 6 * G ≤ 9 * R := by
  apply twoStage_amplification
  · exact exactCylinder_amplification_of_twoBudget hback hbackBudget
  · exact exactCylinder_amplification_of_twoBudget hforward hforwardBudget

/-- A signed backward-pullback identity becomes an ordinary natural-number
cylinder as soon as its coordinate is known nonnegative.  A cardinality
bound on the transported fixed support then forces the coordinate below the
critical gap. -/
theorem coordinate_le_criticalGap_of_fixedSupportPullback
    {b k G : ℕ} {A : Finset ℕ} {Q : ℤ}
    (hA : ∀ e ∈ A, 2 ≤ e)
    (hQ : 0 ≤ Q)
    (hcard : A.card ≤ Q.toNat)
    (hexact :
      (G : ℤ) + (fixedSupportPulseCharge b A k : ℤ) =
        ((4 ^ k : ℕ) : ℤ) * Q) :
    Q.toNat ≤ G := by
  have hQcast : ((Q.toNat : ℕ) : ℤ) = Q := by
    exact Int.toNat_of_nonneg hQ
  have hexactNat :
      G + fixedSupportPulseCharge b A k = 4 ^ k * Q.toNat := by
    have hexact' := hexact
    rw [← hQcast] at hexact'
    exact_mod_cast hexact'
  have hcharge :
      fixedSupportPulseCharge b A k ≤ Q.toNat * (4 ^ k - 1) :=
    fixedSupportPulseCharge_le_coordinate_geometric hA Q.toNat k hcard
  exact coordinate_le_remainder_of_exactCylinder hexactNat hcharge

/-- Quantitative signed-pullback form.  Once the earlier coordinate is
nonnegative, the exact integer identity can be naturalized without loss and
the backward block retains its full base-four amplification. -/
theorem scaled_pullbackCoordinate_add_two_le_three_criticalGap
    {b k G : ℕ} {A : Finset ℕ} {Q : ℤ}
    (hA : ∀ e ∈ A, 2 ≤ e)
    (hQ : 0 ≤ Q)
    (hcard : A.card ≤ Q.toNat)
    (hexact :
      (G : ℤ) + (fixedSupportPulseCharge b A k : ℤ) =
        ((4 ^ k : ℕ) : ℤ) * Q) :
    4 ^ k * Q.toNat + 2 * Q.toNat ≤ 3 * G := by
  have hQcast : ((Q.toNat : ℕ) : ℤ) = Q :=
    Int.toNat_of_nonneg hQ
  have hexactNat :
      G + fixedSupportPulseCharge b A k = 4 ^ k * Q.toNat := by
    have hexact' := hexact
    rw [← hQcast] at hexact'
    exact_mod_cast hexact'
  exact fixedSupport_exactCylinder_amplification hA hcard hexactNat

/-- The audited pullback-card inequality is stable under a backward
fixed-support block.  If the pullback coordinate dominates a chosen endpoint
cardinality by two, and the transported support has at most one extra rank,
then the forward critical gap has the same cardinality margin. -/
theorem criticalGap_ge_card_add_two_of_fixedSupportPullback
    {b k G card : ℕ} {A : Finset ℕ} {Q : ℤ}
    (hA : ∀ e ∈ A, 2 ≤ e)
    (hcardA : A.card ≤ card + 1)
    (hQcard : ((card + 2 : ℕ) : ℤ) ≤ Q)
    (hexact :
      (G : ℤ) + (fixedSupportPulseCharge b A k : ℤ) =
        ((4 ^ k : ℕ) : ℤ) * Q) :
    card + 2 ≤ G := by
  have hQ : 0 ≤ Q := by
    have : (0 : ℤ) ≤ ((card + 2 : ℕ) : ℤ) := by positivity
    exact this.trans hQcard
  have hcardQNat : card + 2 ≤ Q.toNat := by
    have hQcard' := hQcard
    rw [← Int.toNat_of_nonneg hQ] at hQcard'
    exact_mod_cast hQcard'
  have hAQ : A.card ≤ Q.toNat := by omega
  have hQG := coordinate_le_criticalGap_of_fixedSupportPullback
    hA hQ hAQ hexact
  exact hcardQNat.trans hQG

/-- An actual upper-reset/right-run block retains the full base-four scale
of its critical coordinate.  Endpoint-card domination gives the sharp `2Q`
digit budget, so the terminal remainder is at least
`(4^k * Q + 2Q) / 3`, not merely `Q`.

This is the forward half of the recursive parent/child packet inequality. -/
theorem seamUpperThenRightRun_scaledCriticalGap_add_two_le_three_remainder
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hgap :
      (seamWordSupport (seamGreedyWord (d + k + 1))).card + 2 ≤
        2 ^ (d - k + 1) - seamUpperResetCharge d hd5) :
    4 ^ k * (2 ^ (d - k + 1) - seamUpperResetCharge d hd5) +
          2 * (2 ^ (d - k + 1) - seamUpperResetCharge d hd5) ≤
      3 * seamIntegerGreedyRemainder (d + k + 1) := by
  let Aend := seamWordSupport (seamGreedyWord (d + k + 1))
  let Q := 2 ^ (d - k + 1) - seamUpperResetCharge d hd5
  let pulse : ℕ → ℕ := fun j ↦
    (seamAdjacentCut (d + j + 1) (by omega)).belowPulse
  have hpulse : ∀ j : ℕ, j < k → pulse j + 4 ≤ 2 * Q := by
    intro j hj
    have hsupportJ := seamUpperThenRightRun_support
      hd5 hcarry hrun j (by omega)
    have hsupportK := seamUpperThenRightRun_support
      hd5 hcarry hrun k (by omega)
    have hsubset :
        seamWordSupport (seamGreedyWord (d + j + 1)) ⊆ Aend := by
      rw [hsupportJ]
      change _ ⊆ seamWordSupport (seamGreedyWord (d + k + 1))
      rw [hsupportK]
      intro e he
      rcases Finset.mem_union.mp he with hbase | hinterval
      · exact Finset.mem_union_left _ hbase
      · have hbounds := Finset.mem_Ico.mp hinterval
        exact Finset.mem_union_right _
          (Finset.mem_Ico.mpr ⟨hbounds.1, by omega⟩)
    have hcard :
        (seamWordSupport (seamGreedyWord (d + j + 1))).card ≤ Aend.card :=
      Finset.card_le_card hsubset
    have hpulseCard :=
      wordPulse_le_two_mul_supportCard
        (seamGreedyWord (d + j + 1))
    have hpulseBound : pulse j ≤ 2 * Aend.card := by
      change wordPulse (d + j + 1)
          (seamGreedyWord (d + j + 1)).toNatWord ≤ 2 * Aend.card
      exact hpulseCard.trans (Nat.mul_le_mul_left 2 hcard)
    change Aend.card + 2 ≤ Q at hgap
    omega
  have hexact :
      seamIntegerGreedyRemainder (d + k + 1) +
          affineRightRunCharge pulse k = 4 ^ k * Q := by
    simpa [pulse, Q] using
      seamUpperThenRightRun_remainder_add_charge_eq_scaledCriticalGap
        hd5 hk hcarry hrun
  exact scaled_coordinate_add_two_coordinate_le_three_remainder
    pulse hexact hpulse

/-! ## The terminal-middle packet transfer

An upper/right block does not end when its terminal remainder alone crosses a
threshold.  The entire affine pulse packet has to cross with it.  The middle
reset at the terminal row gives an exact, lossless way to move that packet to
the next landing: the terminal pulse cancels between the middle recurrence and
the next affine-charge digit.

This is the symmetric return step needed by the endpoint-packet programme. -/

/-- On a middle branch, adjoining the terminal pulse to an affine packet
transports the whole packet to the next landing without loss. -/
theorem terminalMiddle_affinePacket_step
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hncarry :
      ¬ (seamAdjacentCut (d + k + 1) (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut (d + k + 1) (by omega)).remainder +
            (seamPerturbedFamily (d + k + 1) (by omega)).gap -
            (seamAdjacentCut (d + k + 1) (by omega)).belowPulse <
          (seamAdjacentCut (d + k + 1) (by omega)).terminalWeight) :
    seamIntegerGreedyRemainder (d + k + 2) +
          affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) (k + 1) =
        4 * (seamIntegerGreedyRemainder (d + k + 1) +
          affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k) +
          2 ^ (d + k + 2) + 4 := by
  have hmiddleRec := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    (s := d + k + 1) (by omega) hncarry hmiddle
  have hmiddleRec' :
      seamIntegerGreedyRemainder (d + k + 2) +
          (seamAdjacentCut (d + k + 1) (by omega)).belowPulse =
        4 * seamIntegerGreedyRemainder (d + k + 1) +
          2 ^ (d + k + 2) := by
    simpa only [show d + k + 1 + 1 = d + k + 2 by omega] using hmiddleRec
  simp only [affineRightRunCharge]
  omega

/-- The half-cylinder endpoint packet inequality is exactly the next middle
landing packet inequality at the returned scale.  This is an equivalence,
not a one-sided estimate, so subsequent descent arguments lose no margin. -/
theorem terminalMiddle_endpointPacket_lt_half_iff_nextLandingPacket_lt
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hncarry :
      ¬ (seamAdjacentCut (d + k + 1) (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut (d + k + 1) (by omega)).remainder +
            (seamPerturbedFamily (d + k + 1) (by omega)).gap -
            (seamAdjacentCut (d + k + 1) (by omega)).belowPulse <
          (seamAdjacentCut (d + k + 1) (by omega)).terminalWeight) :
    seamIntegerGreedyRemainder (d + k + 1) +
          affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k <
        2 ^ (d + k) ↔
      seamIntegerGreedyRemainder (d + k + 2) +
          affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) (k + 1) <
        2 ^ (d + k + 3) + 4 := by
  have hstep := terminalMiddle_affinePacket_step
    (d := d) (k := k) hd5 hncarry hmiddle
  have hpow2 : 2 ^ (d + k + 2) = 4 * 2 ^ (d + k) := by
    rw [show d + k + 2 = (d + k) + 2 by omega, pow_add]
    norm_num [Nat.mul_comm]
  have hpow3 : 2 ^ (d + k + 3) = 8 * 2 ^ (d + k) := by
    rw [show d + k + 3 = (d + k) + 3 by omega, pow_add]
    norm_num [Nat.mul_comm]
  rw [hstep, hpow2, hpow3]
  omega

/-- Exact signed packet cylinder after any source row and a finite right run.
For a middle reset the initial deviation is positive-facing, so the terminal
packet equals the row dyadic term plus the base-four dilate of that deviation.
The generic statement also records the negative-facing upper case. -/
theorem rightRun_signedPacket_exact
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) :
    (seamIntegerGreedyRemainder (d + k + 1) : ℤ) -
          ((2 ^ (d + k + 1) : ℕ) : ℤ) +
          (affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k : ℤ) =
        ((4 ^ k : ℕ) : ℤ) * seamResetDeviation d := by
  let X : ℕ → ℤ := fun q ↦
    (seamIntegerGreedyRemainder (d + q + 1) : ℤ) -
      ((2 ^ (d + q + 1) : ℕ) : ℤ)
  let pulse : ℕ → ℕ := fun q ↦
    (seamAdjacentCut (d + q + 1) (by omega)).belowPulse
  have hrec : ∀ q : ℕ, q < k →
      X (q + 1) = 4 * X q - (pulse q : ℤ) - 4 := by
    intro q hq
    have hstep := hrun q hq
    have hstepZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hstep
    have hpow :
        (2 : ℤ) ^ (d + q + 2) =
          2 * (2 : ℤ) ^ (d + q + 1) := by
      rw [show d + q + 2 = (d + q + 1) + 1 by omega, pow_succ]
      ring
    dsimp [X, pulse]
    rw [show d + (q + 1) + 1 = d + q + 2 by omega]
    push_cast at hstepZ
    rw [hpow] at hstepZ
    omega
  have hiter := affineRightExcess_exactIterate X pulse k hrec
  have hbase : X 0 = seamResetDeviation d := by
    simp [X, seamResetDeviation]
  rw [hbase] at hiter
  simpa [X, pulse, Nat.add_assoc] using hiter

/-- Symmetric middle-reset endpoint form.  The lower return-time inequality
for a middle deviation is exactly the statement that the terminal affine
packet lies above the three-halves boundary.  Together with the upper
half-boundary theorem, this puts both alternating reset types in one packet
coordinate. -/
theorem rightRun_scaledDeviation_gt_iff_endpointPacket_gt_threeHalf
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1)) :
    (((2 ^ (d + k) : ℕ) : ℤ) <
        ((4 ^ k : ℕ) : ℤ) * seamResetDeviation d) ↔
      (((3 * 2 ^ (d + k) : ℕ) : ℤ) <
        (seamIntegerGreedyRemainder (d + k + 1) : ℤ) +
          (affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k : ℤ)) := by
  have hexact := rightRun_signedPacket_exact
    hd5 hrun
  have hdouble :
      (2 : ℤ) ^ (d + k + 1) =
        2 * (2 : ℤ) ^ (d + k) := by
    rw [show d + k + 1 = (d + k) + 1 by omega, pow_succ]
    ring
  push_cast at hexact ⊢
  rw [hdouble] at hexact
  omega

/-- If a right run ends at an actual carry, its terminal affine packet is
automatically above the three-halves boundary.  No estimate of the accumulated
right-run charge is required: the terminal remainder alone clears the
boundary by the compulsory positive upper pulse theorem. -/
theorem rightRun_endpointPacket_gt_threeHalf_of_terminalCarry
    {d k : ℕ} (hd12 : 12 ≤ d)
    (hterminal :
      (seamAdjacentCut (d + k + 1) (by omega)).successorCarries) :
    3 * 2 ^ (d + k) <
      seamIntegerGreedyRemainder (d + k + 1) +
        affineRightRunCharge
          (fun q ↦
            (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k := by
  have hremainder := seamSuccessorCarries_remainder_gt_threeHalf
    (s := d + k + 1) (by omega) hterminal
  rw [show d + k + 1 - 1 = d + k by omega] at hremainder
  omega

/-- The symmetric middle-reset return inequality is unconditional once the
observed right run terminates in a carry.  Combining the exact signed packet
cylinder with the terminal three-halves bound yields
`2^(d+k) < 4^k * dev_d`, which is the lower half of the exact reset law. -/
theorem rightRun_scaledDeviation_gt_of_terminalCarry
    {d k : ℕ} (hd12 : 12 ≤ d)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hterminal :
      (seamAdjacentCut (d + k + 1) (by omega)).successorCarries) :
    ((2 ^ (d + k) : ℕ) : ℤ) <
      ((4 ^ k : ℕ) : ℤ) * seamResetDeviation d := by
  apply (rightRun_scaledDeviation_gt_iff_endpointPacket_gt_threeHalf
    (by omega) hrun).2
  exact_mod_cast rightRun_endpointPacket_gt_threeHalf_of_terminalCarry
    hd12 hterminal

/-- A small middle landing cannot return to an upper carry until almost the
full shell. -/
theorem rightRun_length_ge_of_middle_small_of_terminalCarry
    {s M b k : ℕ} (hs12 : 12 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s (by omega)).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s (by omega)).belowPulse <
          (seamAdjacentCut s (by omega)).terminalWeight)
    (hsmall : seamIntegerGreedyRemainder s < M)
    (hM : M ≤ 2 ^ b)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (s + q + 2) +
          2 ^ (s + q + 2) +
          (seamAdjacentCut (s + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (s + q + 1))
    (hterminal :
      (seamAdjacentCut (s + k + 1) (by omega)).successorCarries) :
    s - b - 1 ≤ k := by
  have hdev := middleResetDeviation_eq (s := s) (by omega) hncarry hmiddle
  have hrem := seamAdjacentCut_remainder (s := s) (by omega)
  have hdevlt : seamResetDeviation s < (((2 ^ (b + 2) : ℕ) : ℤ)) := by
    rw [hdev, hrem]
    have hsmallZ : ((seamIntegerGreedyRemainder s : ℕ) : ℤ) < (M : ℤ) := by
      exact_mod_cast hsmall
    have hMZ : (M : ℤ) ≤ ((2 ^ b : ℕ) : ℤ) := by
      exact_mod_cast hM
    have hpulseZ : (0 : ℤ) ≤
        ((seamAdjacentCut s (by omega)).belowPulse : ℤ) := by positivity
    have hpow : (((2 ^ (b + 2) : ℕ) : ℤ)) = 4 * ((2 ^ b : ℕ) : ℤ) := by
      push_cast
      rw [pow_add]
      norm_num
      ring
    rw [hpow]
    omega
  have hscale := rightRun_scaledDeviation_gt_of_terminalCarry
    hs12 hrun hterminal
  have hfourpos : (0 : ℤ) < ((4 ^ k : ℕ) : ℤ) := by positivity
  have hmul :
      ((4 ^ k : ℕ) : ℤ) * seamResetDeviation s <
        ((4 ^ k : ℕ) : ℤ) * ((2 ^ (b + 2) : ℕ) : ℤ) :=
    mul_lt_mul_of_pos_left hdevlt hfourpos
  have hpow : (4 ^ k : ℕ) * 2 ^ (b + 2) = 2 ^ (2 * k + b + 2) := by
    rw [show (4 : ℕ) ^ k = 2 ^ (2 * k) by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]]
    rw [show 2 * k + b + 2 = 2 * k + (b + 2) by omega, pow_add, pow_add]
    ring
  have hpowersZ :
      ((2 ^ (s + k) : ℕ) : ℤ) < ((2 ^ (2 * k + b + 2) : ℕ) : ℤ) := by
    rw [← hpow]
    push_cast
    exact lt_trans hscale hmul
  have hpowers : 2 ^ (s + k) < 2 ^ (2 * k + b + 2) := by
    exact_mod_cast hpowersZ
  have hexp : s + k < 2 * k + b + 2 := by
    by_contra hnot
    have hle : 2 * k + b + 2 ≤ s + k := by omega
    have hpwle : 2 ^ (2 * k + b + 2) ≤ 2 ^ (s + k) :=
      Nat.pow_le_pow_right (by norm_num) hle
    omega
  omega

/-- For an upper/right block which terminates in a reset, the critical-index
identity is therefore equivalent to the returned middle-landing packet
bound.  This is the proof-facing form of the symmetric middle-reset return
inequality. -/
theorem seamUpperThenRightRun_criticalIndex_eq_iff_nextMiddleLandingPacket_lt
    {d k j : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ q : ℕ, q < k →
      seamIntegerGreedyRemainder (d + q + 2) +
          2 ^ (d + q + 2) +
          (seamAdjacentCut (d + q + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + q + 1))
    (hreset : SeamGreedyUpperOrMiddleAt (d + k + 1) (by omega))
    (hcritical :
      CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j) :
    j = k ↔
      seamIntegerGreedyRemainder (d + k + 2) +
          affineRightRunCharge
            (fun q ↦
              (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) (k + 1) <
        2 ^ (d + k + 3) + 4 := by
  have hterminal := seamUpperThenRightRun_terminal_isMiddle
    hd5 hcarry hrun hreset
  calc
    j = k ↔
        seamIntegerGreedyRemainder (d + k + 1) +
            affineRightRunCharge
              (fun q ↦
                (seamAdjacentCut (d + q + 1) (by omega)).belowPulse) k <
          2 ^ (d + k) :=
      seamUpperThenRightRun_criticalIndex_eq_iff_endpointPacket_lt_half
        hd5 hcarry hrun hcritical
    _ ↔ _ := terminalMiddle_endpointPacket_lt_half_iff_nextLandingPacket_lt
      hd5 hterminal.1 hterminal.2

/-- In particular, the quantitative forward amplifier propagates the
endpoint support-cardinality margin to the terminal remainder. -/
theorem seamUpperThenRightRun_remainder_ge_supportCard_add_two
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hgap :
      (seamWordSupport (seamGreedyWord (d + k + 1))).card + 2 ≤
        2 ^ (d - k + 1) - seamUpperResetCharge d hd5) :
    (seamWordSupport (seamGreedyWord (d + k + 1))).card + 2 ≤
      seamIntegerGreedyRemainder (d + k + 1) := by
  let Q := 2 ^ (d - k + 1) - seamUpperResetCharge d hd5
  have hamp :=
    seamUpperThenRightRun_scaledCriticalGap_add_two_le_three_remainder
      hd5 hk hcarry hrun hgap
  change 4 ^ k * Q + 2 * Q ≤
    3 * seamIntegerGreedyRemainder (d + k + 1) at hamp
  have hpow : 1 ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hQscaled : Q ≤ 4 ^ k * Q := by
    calc
      Q = 1 * Q := by simp
      _ ≤ 4 ^ k * Q := Nat.mul_le_mul_right Q hpow
  have hthreeQ : 3 * Q ≤
      4 ^ k * Q + 2 * Q := by omega
  have hthreeQR : 3 * Q ≤
      3 * seamIntegerGreedyRemainder (d + k + 1) :=
    hthreeQ.trans hamp
  have hQR : Q ≤ seamIntegerGreedyRemainder (d + k + 1) :=
    Nat.le_of_mul_le_mul_left hthreeQR (by norm_num)
  change (seamWordSupport
    (seamGreedyWord (d + k + 1))).card + 2 ≤ Q at hgap
  exact hgap.trans hQR

/-- For a late upper reset, domination of the endpoint support by the exact
earlier pullback coordinate gives a quantitative backward amplification to
the forward critical gap.

The proof uses the source-current largest-false decomposition: the reset
upper word has support `insert d u`, while every later right step only adds
new ranks.  Thus the fixed support transported by the backward identity is a
subset of the endpoint support, exactly the cardinality input required by
`scaled_pullbackCoordinate_add_two_le_three_criticalGap`. -/
theorem lateUpperReset_scaledPullback_add_two_le_three_criticalGap
    {s d k : ℕ} (hs5 : 5 ≤ s) (hk : k ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hfactor : s + k ≤ 2 * d + 1)
    (hcarry : (seamAdjacentCut s hs5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (s + j + 2) +
          2 ^ (s + j + 2) +
          (seamAdjacentCut (s + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (s + j + 1))
    (hpullbackCard :
      (((seamWordSupport
          (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) ≤
        seamEarlierCriticalPullbackCoordinate s d k) :
    4 ^ (s - d) *
          (seamEarlierCriticalPullbackCoordinate s d k).toNat +
        2 * (seamEarlierCriticalPullbackCoordinate s d k).toNat ≤
      3 * (2 ^ (s - k + 1) - seamUpperResetCharge s hs5) := by
  classical
  obtain ⟨u, hu, _hbase, hsupp, hpull⟩ :=
    exists_backwardCriticalDistance_pullback_of_lateLargestFalse
      hs5 hd hlate hk hfactor
  have hA : ∀ e ∈ insert d u, 2 ≤ e := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · exact hd.1
    · exact (hu e heu).1
  have habove :=
    seamAdjacentCut_above_eq_largestSkipUpperWord_of_support
      hs5 hd.1 hu hd.2.1 hsupp hlate
  have hupperBounds : ∀ e ∈ insert d u, 2 ≤ e ∧ e < s := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · exact ⟨hd.1, hd.2.1⟩
    · exact ⟨(hu e heu).1, (hu e heu).2.trans hd.2.1⟩
  have hupperSupport :
      seamWordSupport (largestSkipUpperWord s d u) = insert d u := by
    unfold largestSkipUpperWord
    exact seamWordSupport_seamRowWordOfFinset hupperBounds
  have hendpointSupport :=
    seamUpperThenRightRun_support hs5 hcarry hrun k (by omega)
  have hsubset :
      insert d u ⊆
        seamWordSupport (seamGreedyWord (s + k + 1)) := by
    rw [hendpointSupport, habove, hupperSupport]
    exact Finset.subset_union_left
  have hcardA :
      (insert d u).card ≤
        (seamWordSupport (seamGreedyWord (s + k + 1))).card + 1 := by
    have := Finset.card_le_card hsubset
    omega
  have hcylinder :=
    seamUpperThenRightRun_exactCylinder hs5 hcarry hrun
  have hfactorPow :
      4 ^ k * 2 ^ (s - k + 1) = 2 ^ (s + k + 1) := by
    rw [show 4 ^ k = 2 ^ (2 * k) by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
    congr 1
    omega
  have hweighted :
      4 ^ k * seamUpperResetCharge s hs5 ≤ 2 ^ (s + k + 1) := by
    change seamIntegerGreedyRemainder (s + k + 1) +
        4 ^ k * seamUpperResetCharge s hs5 +
          affineRightRunCharge
            (fun j ↦
              (seamAdjacentCut (s + j + 1) (by omega)).belowPulse) k =
        2 ^ (s + k + 1) at hcylinder
    omega
  have hchargeLe :
      seamUpperResetCharge s hs5 ≤ 2 ^ (s - k + 1) := by
    have hweighted' :
        4 ^ k * seamUpperResetCharge s hs5 ≤
          4 ^ k * 2 ^ (s - k + 1) := by
      rwa [hfactorPow]
    exact Nat.le_of_mul_le_mul_left hweighted'
      (pow_pos (by norm_num) k)
  have hpullNat :
      ((2 ^ (s - k + 1) - seamUpperResetCharge s hs5 : ℕ) : ℤ) +
          (fixedSupportPulseCharge
            (d + 1) (insert d u) (s - d) : ℤ) =
        ((4 ^ (s - d) : ℕ) : ℤ) *
          seamEarlierCriticalPullbackCoordinate s d k := by
    calc
      ((2 ^ (s - k + 1) - seamUpperResetCharge s hs5 : ℕ) : ℤ) +
            (fixedSupportPulseCharge
              (d + 1) (insert d u) (s - d) : ℤ) =
          ((2 ^ (s - k + 1) : ℕ) : ℤ) -
              (seamUpperResetCharge s hs5 : ℤ) +
            (fixedSupportPulseCharge
              (d + 1) (insert d u) (s - d) : ℤ) := by
        rw [Nat.cast_sub hchargeLe]
      _ = ((4 ^ (s - d) : ℕ) : ℤ) *
            seamEarlierCriticalPullbackCoordinate s d k := hpull
  have hQ : 0 ≤ seamEarlierCriticalPullbackCoordinate s d k := by
    have hzero :
        (0 : ℤ) ≤
          (((seamWordSupport
            (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) := by
      positivity
    exact hzero.trans hpullbackCard
  have hcardQNat :
      (seamWordSupport (seamGreedyWord (s + k + 1))).card + 2 ≤
        (seamEarlierCriticalPullbackCoordinate s d k).toNat := by
    have hpullbackCard' := hpullbackCard
    rw [← Int.toNat_of_nonneg hQ] at hpullbackCard'
    exact_mod_cast hpullbackCard'
  have hAQ :
      (insert d u).card ≤
        (seamEarlierCriticalPullbackCoordinate s d k).toNat := by
    omega
  exact scaled_pullbackCoordinate_add_two_le_three_criticalGap
    hA hQ hAQ hpullNat

/-- The quantitative backward amplifier in particular propagates the
endpoint-card margin to the critical gap. -/
theorem lateUpperReset_criticalGap_ge_endpointCard_add_two_of_pullbackCoordinate
    {s d k : ℕ} (hs5 : 5 ≤ s) (hk : k ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hfactor : s + k ≤ 2 * d + 1)
    (hcarry : (seamAdjacentCut s hs5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (s + j + 2) +
          2 ^ (s + j + 2) +
          (seamAdjacentCut (s + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (s + j + 1))
    (hpullbackCard :
      (((seamWordSupport
          (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) ≤
        seamEarlierCriticalPullbackCoordinate s d k) :
    (seamWordSupport (seamGreedyWord (s + k + 1))).card + 2 ≤
      2 ^ (s - k + 1) - seamUpperResetCharge s hs5 := by
  let Q := seamEarlierCriticalPullbackCoordinate s d k
  let G := 2 ^ (s - k + 1) - seamUpperResetCharge s hs5
  have hamp :=
    lateUpperReset_scaledPullback_add_two_le_three_criticalGap
      hs5 hk hd hlate hfactor hcarry hrun hpullbackCard
  change 4 ^ (s - d) * Q.toNat + 2 * Q.toNat ≤ 3 * G at hamp
  have hpow : 1 ≤ 4 ^ (s - d) := one_le_pow₀ (by norm_num)
  have hQscaled : Q.toNat ≤ 4 ^ (s - d) * Q.toNat := by
    calc
      Q.toNat = 1 * Q.toNat := by simp
      _ ≤ 4 ^ (s - d) * Q.toNat :=
        Nat.mul_le_mul_right Q.toNat hpow
  have hthreeQ : 3 * Q.toNat ≤
      4 ^ (s - d) * Q.toNat + 2 * Q.toNat := by omega
  have hthreeQG : 3 * Q.toNat ≤ 3 * G := hthreeQ.trans hamp
  have hQG : Q.toNat ≤ G :=
    Nat.le_of_mul_le_mul_left hthreeQG (by norm_num)
  have hQ : 0 ≤ Q := by
    have hzero :
        (0 : ℤ) ≤
          (((seamWordSupport
            (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) := by
      positivity
    exact hzero.trans hpullbackCard
  have hcardQNat :
      (seamWordSupport (seamGreedyWord (s + k + 1))).card + 2 ≤
        Q.toNat := by
    have hpullbackCard' := hpullbackCard
    change (((seamWordSupport
      (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) ≤ Q at hpullbackCard'
    rw [← Int.toNat_of_nonneg hQ] at hpullbackCard'
    exact_mod_cast hpullbackCard'
  exact hcardQNat.trans hQG

/-- Full quantitative parent/child packet inequality for an actual late
upper reset.  The pullback coordinate is amplified through the fixed-support
ancestry block and then through the observed right run, with neither
base-four factor collapsed to a mere order comparison. -/
theorem lateUpperReset_twoBlock_amplification_of_pullbackCoordinate
    {s d k : ℕ} (hs5 : 5 ≤ s) (hk : k ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hfactor : s + k ≤ 2 * d + 1)
    (hcarry : (seamAdjacentCut s hs5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (s + j + 2) +
          2 ^ (s + j + 2) +
          (seamAdjacentCut (s + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (s + j + 1))
    (hpullbackCard :
      (((seamWordSupport
          (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) ≤
        seamEarlierCriticalPullbackCoordinate s d k) :
    4 ^ ((s - d) + k) *
          (seamEarlierCriticalPullbackCoordinate s d k).toNat +
        2 * 4 ^ k *
          (seamEarlierCriticalPullbackCoordinate s d k).toNat +
        6 * (2 ^ (s - k + 1) - seamUpperResetCharge s hs5) ≤
      9 * seamIntegerGreedyRemainder (s + k + 1) := by
  let Q := (seamEarlierCriticalPullbackCoordinate s d k).toNat
  let G := 2 ^ (s - k + 1) - seamUpperResetCharge s hs5
  have hback :=
    lateUpperReset_scaledPullback_add_two_le_three_criticalGap
      hs5 hk hd hlate hfactor hcarry hrun hpullbackCard
  have hgap :=
    lateUpperReset_criticalGap_ge_endpointCard_add_two_of_pullbackCoordinate
      hs5 hk hd hlate hfactor hcarry hrun hpullbackCard
  have hforward :=
    seamUpperThenRightRun_scaledCriticalGap_add_two_le_three_remainder
      hs5 hk hcarry hrun hgap
  change 4 ^ (s - d) * Q + 2 * Q ≤ 3 * G at hback
  change 4 ^ k * G + 2 * G ≤
    3 * seamIntegerGreedyRemainder (s + k + 1) at hforward
  exact twoStage_amplification hback hforward

/-- Full two-block propagation.  A pullback-coordinate/cardinality margin at
a late upper reset survives both the backward fixed-support block and the
forward actual right run, yielding the seam remainder/cardinality gap at the
observed endpoint. -/
theorem lateUpperReset_endpointRemainder_ge_card_add_two_of_pullbackCoordinate
    {s d k : ℕ} (hs5 : 5 ≤ s) (hk : k ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hfactor : s + k ≤ 2 * d + 1)
    (hcarry : (seamAdjacentCut s hs5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (s + j + 2) +
          2 ^ (s + j + 2) +
          (seamAdjacentCut (s + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (s + j + 1))
    (hpullbackCard :
      (((seamWordSupport
          (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) ≤
        seamEarlierCriticalPullbackCoordinate s d k) :
    (seamWordSupport (seamGreedyWord (s + k + 1))).card + 2 ≤
      seamIntegerGreedyRemainder (s + k + 1) := by
  apply seamUpperThenRightRun_remainder_ge_supportCard_add_two
    hs5 hk hcarry hrun
  exact lateUpperReset_criticalGap_ge_endpointCard_add_two_of_pullbackCoordinate
    hs5 hk hd hlate hfactor hcarry hrun hpullbackCard

/-- The pulled-back coordinate is exactly the preceding middle coordinate
minus the exposed dyadic staircase.  This rewrites the remaining producer
in the variables of the actual middle ancestor, retaining its exact paired
pulse rather than replacing it by a coarse row-width bound. -/
theorem lateUpperReset_pullbackCoordinate_eq_previousMiddleCoordinate
    {s d k : ℕ} (hs13 : 13 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    seamEarlierCriticalPullbackCoordinate s d k =
      4 * (seamIntegerGreedyRemainder d : ℤ) -
          ((seamAdjacentCut d (by omega)).belowPulse : ℤ) - 4 +
        ((2 ^ ((2 * d + 1) - (s + k)) : ℕ) : ℤ) -
          ((2 ^ ((2 * d + 2) - s) : ℕ) : ℤ) := by
  have hmiddle := lateUpperReset_previousProducer_isMiddle
    (s := s) (d := d) hs13 hd hlate hcarry
  have hlanding := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    (s := d) (by omega) hmiddle.1 hmiddle.2
  have hlandingZ :
      (seamIntegerGreedyRemainder (d + 1) : ℤ) +
          ((seamAdjacentCut d (by omega)).belowPulse : ℤ) =
        4 * (seamIntegerGreedyRemainder d : ℤ) +
          ((2 ^ (d + 1) : ℕ) : ℤ) := by
    exact_mod_cast hlanding
  unfold seamEarlierCriticalPullbackCoordinate
  omega

/-- A natural-number form of the exact residual producer.  It says that the
previous middle coordinate clears the exposed dyadic staircase by the
endpoint support cardinality.  This is equivalent to the pullback-card
margin after the exact middle recurrence, but is shaped for induction across
alternating reset blocks. -/
def LateUpperPreviousMiddleStaircaseEscape : Prop :=
  ∀ (s d k : ℕ) (hs13 : 13 ≤ s) (hd5 : 5 ≤ d),
    IsLargestFalseRank (seamGreedyWord s) d →
    2 * s < 3 * d → s + k ≤ 2 * d + 1 →
    (seamAdjacentCut s (by omega)).successorCarries →
      2 ^ ((2 * d + 2) - s) +
            (seamAdjacentCut d (by omega)).belowPulse + 4 +
            (seamWordSupport (seamGreedyWord (s + k + 1))).card + 2 ≤
        4 * seamIntegerGreedyRemainder d +
          2 ^ ((2 * d + 1) - (s + k))

/-- A stronger but support-free form of the remaining pullback producer.
At row `s+k+1` there are at most `s+k-1` selectable ranks, so domination
of the endpoint row itself by the pullback coordinate automatically supplies
the endpoint-cardinality margin. -/
def LateUpperPullbackRankEscape : Prop :=
  ∀ (s d k : ℕ) (hs13 : 13 ≤ s) (hd5 : 5 ≤ d),
    IsLargestFalseRank (seamGreedyWord s) d →
    2 * s < 3 * d → s + k ≤ 2 * d + 1 →
    (seamAdjacentCut s (by omega)).successorCarries →
      (((s + k + 1 : ℕ) : ℤ)) ≤
        seamEarlierCriticalPullbackCoordinate s d k

/-- The row-rank producer is sufficient for the exact support-cardinality
premise.  This reduction uses only the structural width of a seam word; it
does not assume anything about which ranks are selected. -/
theorem pullbackCard_of_lateUpperPullbackRankEscape
    (hrank : LateUpperPullbackRankEscape)
    {s d k : ℕ} (hs13 : 13 ≤ s) (hd5 : 5 ≤ d)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hfactor : s + k ≤ 2 * d + 1)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    (((seamWordSupport
        (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) ≤
      seamEarlierCriticalPullbackCoordinate s d k := by
  have hcard := seamWordSupport_card_le_width
    (seamGreedyWord (s + k + 1))
  have hcardRank :
      (seamWordSupport (seamGreedyWord (s + k + 1))).card + 2 ≤
        s + k + 1 := by
    omega
  have hcardRankZ :
      (((seamWordSupport
          (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) ≤
        (((s + k + 1 : ℕ) : ℤ)) := by
    exact_mod_cast hcardRank
  exact hcardRankZ.trans
    (hrank s d k hs13 hd5 hd hlate hfactor hcarry)

/-- The middle-staircase producer is exactly strong enough to supply the
pullback-coordinate/cardinality premise used by the two-block propagation
theorem. -/
theorem pullbackCard_of_lateUpperPreviousMiddleStaircaseEscape
    (hescape : LateUpperPreviousMiddleStaircaseEscape)
    {s d k : ℕ} (hs13 : 13 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hfactor : s + k ≤ 2 * d + 1)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries) :
    (((seamWordSupport
        (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ) ≤
      seamEarlierCriticalPullbackCoordinate s d k := by
  have hmiddleCoordinate :=
    lateUpperReset_pullbackCoordinate_eq_previousMiddleCoordinate
      hs13 hd hlate hcarry (k := k)
  rw [hmiddleCoordinate]
  have hNat := hescape s d k hs13 (by omega) hd hlate hfactor hcarry
  have hNatZ :
      (((2 ^ ((2 * d + 2) - s) +
            (seamAdjacentCut d (by omega)).belowPulse + 4 +
            (seamWordSupport
              (seamGreedyWord (s + k + 1))).card + 2 : ℕ) : ℤ)) ≤
        (((4 * seamIntegerGreedyRemainder d +
            2 ^ ((2 * d + 1) - (s + k)) : ℕ) : ℤ)) := by
    exact_mod_cast hNat
  push_cast at hNatZ
  omega

/-- Consequently the single middle-staircase producer discharges the full
support-cardinality gap at every late upper/right endpoint in its exact
factor range. -/
theorem lateUpperReset_endpointRemainder_ge_card_add_two_of_middleStaircaseEscape
    (hescape : LateUpperPreviousMiddleStaircaseEscape)
    {s d k : ℕ} (hs13 : 13 ≤ s) (hk : k ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hfactor : s + k ≤ 2 * d + 1)
    (hcarry : (seamAdjacentCut s (by omega)).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (s + j + 2) +
          2 ^ (s + j + 2) +
          (seamAdjacentCut (s + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (s + j + 1)) :
    (seamWordSupport (seamGreedyWord (s + k + 1))).card + 2 ≤
      seamIntegerGreedyRemainder (s + k + 1) := by
  apply lateUpperReset_endpointRemainder_ge_card_add_two_of_pullbackCoordinate
    (by omega) hk hd hlate hfactor hcarry hrun
  exact pullbackCard_of_lateUpperPreviousMiddleStaircaseEscape
    hescape hs13 hd hlate hfactor hcarry

#print axioms affineRightRunCharge_le_coordinate_geometric
#print axioms exactCylinder_amplification_of_twoBudget
#print axioms scaled_coordinate_add_two_coordinate_le_three_remainder
#print axioms coordinate_le_remainder_of_exactCylinder
#print axioms fixedSupportPulseCharge_le_coordinate_geometric
#print axioms three_mul_fixedSupportPulseCharge_add_two_mul_le
#print axioms fixedSupport_exactCylinder_amplification
#print axioms twoStage_amplification
#print axioms twoCylinder_amplification
#print axioms terminalMiddle_affinePacket_step
#print axioms terminalMiddle_endpointPacket_lt_half_iff_nextLandingPacket_lt
#print axioms rightRun_signedPacket_exact
#print axioms rightRun_scaledDeviation_gt_iff_endpointPacket_gt_threeHalf
#print axioms seamAdjacentCut_abovePulse_pos_of_successorCarries
#print axioms seamSuccessorCarries_remainder_gt_threeHalf
#print axioms sum_rowPulse_eq_pairedSupportCoeff
#print axioms fixedSupportPulseCharge_eq_finiteCoeffWindowNumerator
#print axioms finiteCoeffWindowNumerator_sub_baseline_eq_centeredCarry
#print axioms fixedSupportPulseCharge_sub_geometric_eq_centeredCarry
#print axioms three_mul_affineRightRunCharge_eq_fixedSupport_add_geometric
#print axioms three_mul_affineRightRunCharge_eq_multiplicityWindow_add_geometric
#print axioms rightRun_endpointPacket_gt_threeHalf_of_terminalCarry
#print axioms rightRun_scaledDeviation_gt_of_terminalCarry
#print axioms rightRun_length_ge_of_middle_small_of_terminalCarry
#print axioms seamUpperThenRightRun_criticalIndex_eq_iff_nextMiddleLandingPacket_lt
#print axioms coordinate_le_criticalGap_of_fixedSupportPullback
#print axioms scaled_pullbackCoordinate_add_two_le_three_criticalGap
#print axioms criticalGap_ge_card_add_two_of_fixedSupportPullback
#print axioms seamUpperThenRightRun_scaledCriticalGap_add_two_le_three_remainder
#print axioms seamUpperThenRightRun_remainder_ge_supportCard_add_two
#print axioms lateUpperReset_scaledPullback_add_two_le_three_criticalGap
#print axioms lateUpperReset_criticalGap_ge_endpointCard_add_two_of_pullbackCoordinate
#print axioms lateUpperReset_twoBlock_amplification_of_pullbackCoordinate
#print axioms lateUpperReset_endpointRemainder_ge_card_add_two_of_pullbackCoordinate
#print axioms lateUpperReset_pullbackCoordinate_eq_previousMiddleCoordinate
#print axioms pullbackCard_of_lateUpperPullbackRankEscape
#print axioms pullbackCard_of_lateUpperPreviousMiddleStaircaseEscape
#print axioms lateUpperReset_endpointRemainder_ge_card_add_two_of_middleStaircaseEscape

end Erdos257PeriodNoncollapse.HalfCylinderPullbackCardPropagation
