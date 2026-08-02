import Erdos249257.ActualForeignResidueProjection
import Erdos249257.LambertDiagonalEnclosure
import Erdos249257.TotientShiftedMobiusPulse
import Mathlib.Tactic

/-!
# The shifted Möbius tail is the actual foreign-residue kernel

This module compares two independently defined descriptions of the same
totient-tail contribution.  The first is the shifted Möbius pulse obtained by
an absolutely summable Lambert regrouping.  The second is the residue kernel
used in the finite diagonal decomposition.  The equality
`positiveForeignResidueKernel_eq_shiftedMobiusPulseTerm` identifies them
term by term.

Consequently the literal totient tail is the sum of the positive residue
kernels, that kernel family is summable, and diagonal tail differences are
sums of the corresponding channel increments.  The later theorems split those
sums at a finite cutoff and discharge the analytic tail-limit hypothesis in
the projected-enclosure argument.

These are coordinate and convergence statements.  They do not show that any
channel is nonzero or dominant, prevent cancellation between channels, or
produce the finite separation hypothesis consumed by the miss theorems.  In
particular the bridge supplies no cofinal certificate family, carry escape,
eventual nonintegrality, contradiction, irrationality theorem, or solution of
Erdős 249.
-/

namespace Erdos249257.TotientShiftedMobiusForeignBridge

open ActualForeignResidueProjection
open Filter
open FullTargetPrimeAdjunctionNoGo
open LambertDiagonalEnclosure
open SquaredMersenneDiagonalEnclosure
open TotientShiftedMobiusPulse
open TotientTailPeriodKiller
open scoped BigOperators

/-- The residue kernel postulated by the finite projection lane is exactly
the shifted Möbius pulse obtained from the convergent Lambert regrouping. -/
theorem positiveForeignResidueKernel_eq_shiftedMobiusPulseTerm
    (d : ℕ+) (N : ℕ) :
    positiveForeignResidueKernel d N = shiftedMobiusPulseTerm N d := by
  have hdR : ((d : ℕ) : ℝ) ≠ 0 := by positivity
  have hM : (2 : ℝ) ^ (d : ℕ) - 1 ≠ 0 := by
    have hpow : (1 : ℝ) < (2 : ℝ) ^ (d : ℕ) :=
      one_lt_pow₀ (by norm_num) d.ne_zero
    linarith
  unfold positiveForeignResidueKernel foreignResidueKernel
    shiftedMobiusPulseTerm
  rw [show residueOffset (d : ℕ) N = forwardMultipleShift N d by rfl,
    add_forwardMultipleShift_eq N d.pos]
  push_cast
  field_simp [hdR, hM]

/-- **Global analytic kernel identity for the actual residue coordinates.**
The literal tail `R_N` is the sum of the positive residue channels used by
the finite foreign-projection decomposition. -/
theorem totientTail_eq_tsum_positiveForeignResidueKernel (N : ℕ) :
    totientTail N =
      ∑' d : ℕ+, positiveForeignResidueKernel d N := by
  rw [totientTail_eq_tsum_shiftedMobiusPulse]
  exact tsum_congr fun d =>
    (positiveForeignResidueKernel_eq_shiftedMobiusPulseTerm d N).symm

/-- Absolute convergence of the actual residue kernel.  Only finitely many
channels lie at or below `N`; above `N` the exact stable-range formula is
dominated by a pair of geometric series. -/
theorem summable_positiveForeignResidueKernel (N : ℕ) :
    Summable (fun d : ℕ+ => positiveForeignResidueKernel d N) := by
  have hhalf0 : Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hquarter0 : Summable (fun n : ℕ => ((1 : ℝ) / 4) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hhalf : Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff 1).mpr hhalf0
  have hquarter :
      Summable (fun n : ℕ => ((1 : ℝ) / 4) ^ (n + 1)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff 1).mpr hquarter0
  have hgeo : Summable (fun n : ℕ =>
      (2 : ℝ) ^ N *
        (2 * ((1 : ℝ) / 2) ^ (n + 1) +
          4 * ((1 : ℝ) / 4) ^ (n + 1))) :=
    ((hhalf.mul_left 2).add (hquarter.mul_left 4)).mul_left
      ((2 : ℝ) ^ N)
  have hnat :
      Summable (fun n : ℕ => foreignResidueKernel (n + 1) N) := by
    refine Summable.of_norm_bounded_eventually_nat hgeo ?_
    filter_upwards [eventually_gt_atTop N] with n hn
    have hd : 0 < n + 1 := by omega
    have hN : N < n + 1 := by omega
    have hmu :
        |((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast MersenneLambertLadder.abs_moebius_le_one (n + 1)
    rw [foreignResidueKernel_of_lt hd hN, Real.norm_eq_abs, abs_mul,
      abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (2 : ℝ) ^ N by positivity),
      abs_of_nonneg (stableResidueFactor_nonneg (n + 1))]
    calc
      |((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ)| *
            (2 : ℝ) ^ N * stableResidueFactor (n + 1) ≤
          1 * (2 : ℝ) ^ N * stableResidueFactor (n + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmu (by positivity))
          (stableResidueFactor_nonneg (n + 1))
      _ ≤ (2 : ℝ) ^ N *
          (2 / (2 : ℝ) ^ (n + 1) + 4 / (4 : ℝ) ^ (n + 1)) := by
        simpa using mul_le_mul_of_nonneg_left
          (stableResidueFactor_le_geometric hd)
          (show (0 : ℝ) ≤ (2 : ℝ) ^ N by positivity)
      _ = (2 : ℝ) ^ N *
          (2 * ((1 : ℝ) / 2) ^ (n + 1) +
            4 * ((1 : ℝ) / 4) ^ (n + 1)) := by
        rw [div_pow, div_pow]
        ring
  change Summable (fun d : ℕ+ => foreignResidueKernel (d : ℕ) N)
  exact (summable_pnat_iff_summable_succ
    (f := fun d : ℕ => foreignResidueKernel d N)).mpr hnat

/-- Each diagonal residue increment is literally the difference of the two
shifted Möbius pulses at `H` and `2H`. -/
theorem positiveResidueIncrement_eq_shiftedMobiusPulse_sub
    (d : ℕ+) (H : ℕ) :
    positiveResidueIncrement d H =
      shiftedMobiusPulseTerm (2 * H) d - shiftedMobiusPulseTerm H d := by
  unfold positiveResidueIncrement
  rw [positiveForeignResidueKernel_eq_shiftedMobiusPulseTerm,
    positiveForeignResidueKernel_eq_shiftedMobiusPulseTerm]

/-- The diagonal increment family is absolutely summable, so subtraction of
the two literal tails may be interchanged with the residue-channel sum. -/
theorem summable_positiveResidueIncrement (H : ℕ) :
    Summable (fun d : ℕ+ => positiveResidueIncrement d H) := by
  simpa [positiveResidueIncrement] using
    (summable_positiveForeignResidueKernel (2 * H)).sub
      (summable_positiveForeignResidueKernel H)

/-- The actual diagonal is the unconditional sum of all residue increments.
This is the global bridge required before splitting divisor and foreign
channels at a finite cutoff. -/
theorem scaleDiagonalTailDifference_eq_tsum_positiveResidueIncrement
    (H : ℕ) :
    scaleDiagonalTailDifference H =
      ∑' d : ℕ+, positiveResidueIncrement d H := by
  unfold scaleDiagonalTailDifference
  rw [totientTail_eq_tsum_positiveForeignResidueKernel,
    totientTail_eq_tsum_positiveForeignResidueKernel]
  simpa [positiveResidueIncrement] using
    ((summable_positiveForeignResidueKernel (2 * H)).tsum_sub
      (summable_positiveForeignResidueKernel H)).symm

/-- Splitting the absolutely summable residue family at `D` identifies the
literal diagonal with the finite residue state plus the exact shifted tail. -/
theorem scaleDiagonalTailDifference_eq_finiteResidue_add_tail
    (H D : ℕ) :
    scaleDiagonalTailDifference H =
      finiteResidueDiagonal H D +
        ∑' k : ℕ, residueIncrement (D + 1 + k) H := by
  let f : ℕ → ℝ := fun n ↦ residueIncrement (n + 1) H
  have hnat : Summable f := by
    rw [show f = fun n : ℕ ↦ residueIncrement (n + 1) H by rfl,
      ← summable_pnat_iff_summable_succ
        (f := fun d : ℕ ↦ residueIncrement d H)]
    exact (summable_positiveResidueIncrement H).congr fun d ↦
      positiveResidueIncrement_coe d H
  have hglobalNat :
      scaleDiagonalTailDifference H = ∑' n : ℕ, f n := by
    rw [scaleDiagonalTailDifference_eq_tsum_positiveResidueIncrement]
    calc
      (∑' d : ℕ+, positiveResidueIncrement d H) =
          ∑' d : ℕ+, residueIncrement (d : ℕ) H := by
        exact tsum_congr fun d ↦ positiveResidueIncrement_coe d H
      _ = ∑' n : ℕ, residueIncrement (n + 1) H :=
        tsum_pnat_eq_tsum_succ
          (f := fun d : ℕ ↦ residueIncrement d H)
      _ = ∑' n : ℕ, f n := by rfl
  have hprefix :
      (∑ n ∈ Finset.range D, f n) = finiteResidueDiagonal H D := by
    unfold finiteResidueDiagonal f
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  have hsplit := hnat.sum_add_tsum_nat_add D
  calc
    scaleDiagonalTailDifference H = ∑' n : ℕ, f n := hglobalNat
    _ = (∑ n ∈ Finset.range D, f n) +
        ∑' n : ℕ, f (n + D) := hsplit.symm
    _ = finiteResidueDiagonal H D +
        ∑' k : ℕ, residueIncrement (D + 1 + k) H := by
      rw [hprefix]
      congr 1
      apply tsum_congr
      intro k
      simp [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Absolute convergence of the first-order Möbius--Mersenne series, exposed
here because the renormalized residue coordinate spends its exact tail. -/
theorem summable_moebius_div_mersenne :
    Summable (fun d : ℕ+ =>
      ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1)) := by
  have hgeo : Summable (fun d : ℕ+ =>
      2 * ((1 : ℝ) / 2) ^ (d : ℕ)) := by
    have h : Summable (fun n : ℕ => 2 * ((1 : ℝ) / 2) ^ n) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 2
    exact h.subtype _
  refine Summable.of_norm_bounded hgeo fun d => ?_
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (d : ℕ) - 1 := by
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) d.ne_zero)
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (d : ℕ) := by positivity
  have hd2 : (2 : ℝ) ≤ (2 : ℝ) ^ (d : ℕ) := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ (d : ℕ) := pow_le_pow_right₀ (by norm_num) d.pos
  have hmu :
      |((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast MersenneLambertLadder.abs_moebius_le_one (d : ℕ)
  have hgeq :
      2 * ((1 : ℝ) / 2) ^ (d : ℕ) = 2 / (2 : ℝ) ^ (d : ℕ) := by
    rw [div_pow, one_pow]
    ring
  rw [Real.norm_eq_abs, abs_div, abs_of_pos h1, hgeq,
    div_le_div_iff₀ h1 h2]
  nlinarith [mul_le_mul_of_nonneg_right hmu h2.le]

/-- The rational first-order correction is exactly the shifted infinite tail
of the absolutely convergent Möbius--Mersenne series. -/
theorem firstLambertTailCorrectionRat_cast_eq_tsum (D : ℕ) :
    (firstLambertTailCorrectionRat D : ℝ) =
      ∑' k : ℕ,
        ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
          ((2 : ℝ) ^ (D + 1 + k) - 1) := by
  let f : ℕ → ℝ := fun n =>
    ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) /
      ((2 : ℝ) ^ (n + 1) - 1)
  have hsum : Summable f := by
    dsimp [f]
    rw [← summable_pnat_iff_summable_succ
      (f := fun n : ℕ =>
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) /
          ((2 : ℝ) ^ n - 1))]
    exact summable_moebius_div_mersenne
  have hsplit := hsum.sum_add_tsum_nat_add D
  have htotal : (∑' n : ℕ, f n) = 1 / 2 := by
    calc
      (∑' n : ℕ, f n) =
          ∑' d : ℕ+,
            ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
              ((2 : ℝ) ^ (d : ℕ) - 1) := by
        simpa [f] using
          (tsum_pnat_eq_tsum_succ
            (f := fun n : ℕ =>
              ((ArithmeticFunction.moebius n : ℤ) : ℝ) /
                ((2 : ℝ) ^ n - 1))).symm
      _ = 1 / 2 :=
        MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half
  calc
    (firstLambertTailCorrectionRat D : ℝ) =
        1 / 2 - ∑ k ∈ Finset.range D, f k := by
      unfold firstLambertTailCorrectionRat
      push_cast
      rfl
    _ = ∑' n : ℕ, f (n + D) := by
      rw [← htotal, ← hsplit]
      ring
    _ = ∑' k : ℕ,
        ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
          ((2 : ℝ) ^ (D + 1 + k) - 1) := by
      apply tsum_congr
      intro k
      simp [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Above the full diagonal scale, every omitted residue channel is stable.
Its exact tail is the diagonal coefficient times the first-order correction
plus the canonical squared-Mersenne tail. -/
theorem residueIncrement_tail_eq_lambert_tails
    {H D : ℕ} (hcutoff : 2 * H ≤ D) :
    (∑' k : ℕ, residueIncrement (D + 1 + k) H) =
      (diagonalCoefficient H : ℝ) *
        ((firstLambertTailCorrectionRat D : ℝ) + mobiusSquareTail D) := by
  let f₁ : ℕ → ℝ := fun k =>
    ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
      ((2 : ℝ) ^ (D + 1 + k) - 1)
  let f₂ : ℕ → ℝ := fun k =>
    ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
      (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)
  have hbase₁ : Summable (fun n : ℕ =>
      ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) /
        ((2 : ℝ) ^ (n + 1) - 1)) := by
    rw [← summable_pnat_iff_summable_succ
      (f := fun n : ℕ =>
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) /
          ((2 : ℝ) ^ n - 1))]
    exact summable_moebius_div_mersenne
  have hbase₂ : Summable (fun n : ℕ =>
      ((ArithmeticFunction.moebius (n + 1) : ℤ) : ℝ) /
        (((2 : ℝ) ^ (n + 1) - 1) ^ 2)) := by
    rw [← summable_pnat_iff_summable_succ
      (f := fun n : ℕ =>
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) /
          (((2 : ℝ) ^ n - 1) ^ 2))]
    exact MersenneLambertLadder.summable_moebius_div_mersenne_sq
  have hsum₁ : Summable f₁ := by
    have hshift := (summable_nat_add_iff D).mpr hbase₁
    simpa [f₁, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hsum₂ : Summable f₂ := by
    have hshift := (summable_nat_add_iff D).mpr hbase₂
    simpa [f₂, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift
  have hfirst : (∑' k : ℕ, f₁ k) =
      (firstLambertTailCorrectionRat D : ℝ) := by
    exact (firstLambertTailCorrectionRat_cast_eq_tsum D).symm
  have hsquare : (∑' k : ℕ, f₂ k) = mobiusSquareTail D := by
    unfold mobiusSquareTail
    rfl
  calc
    (∑' k : ℕ, residueIncrement (D + 1 + k) H) =
        ∑' k : ℕ, (diagonalCoefficient H : ℝ) * (f₁ k + f₂ k) := by
      apply tsum_congr
      intro k
      rw [residueIncrement_of_twice_lt (by omega) (by omega)]
      unfold stableResidueFactor f₁ f₂
      ring
    _ = (diagonalCoefficient H : ℝ) *
        ∑' k : ℕ, (f₁ k + f₂ k) := by rw [tsum_mul_left]
    _ = (diagonalCoefficient H : ℝ) *
        ((∑' k : ℕ, f₁ k) + ∑' k : ℕ, f₂ k) := by
      rw [hsum₁.tsum_add hsum₂]
    _ = (diagonalCoefficient H : ℝ) *
        ((firstLambertTailCorrectionRat D : ℝ) + mobiusSquareTail D) := by
      rw [hfirst, hsquare]

/-- **The renormalized residue socket is discharged.**  Once the cutoff is
past `2H`, the finite residue presentation and the canonical rational
squared-Mersenne centre are the same coordinate. -/
theorem renormalizedResidueAgreement_of_twice_le
    {H D : ℕ} (hH : 0 < H) (hcutoff : 2 * H ≤ D) :
    RenormalizedResidueAgreement H D := by
  have hfinite :
      scaleExplicitShadow H + projectedForeignDefect H D =
        finiteResidueDiagonal H D := by
    rw [finiteResidueDiagonal_eq_projectedForeign_add_divisor,
      projectedDivisorChannels_eq_scaleExplicitShadow hH (by omega)]
    ring
  have hglobal :=
    scaleDiagonalTailDifference_eq_finiteResidue_add_tail H D
  have htail := residueIncrement_tail_eq_lambert_tails hcutoff
  have hlambert :=
    scaleDiagonalTailDifference_sub_lambertProjectedDiagonal H D
  unfold RenormalizedResidueAgreement renormalizedResidueProjection
  calc
    scaleExplicitShadow H + projectedForeignDefect H D +
          (diagonalCoefficient H : ℝ) *
            (firstLambertTailCorrectionRat D : ℝ) =
        finiteResidueDiagonal H D +
          (diagonalCoefficient H : ℝ) *
            (firstLambertTailCorrectionRat D : ℝ) := by rw [hfinite]
    _ = (finiteResidueDiagonal H D +
          ∑' k : ℕ, residueIncrement (D + 1 + k) H) -
        (diagonalCoefficient H : ℝ) * mobiusSquareTail D := by
      rw [htail]
      ring
    _ = scaleDiagonalTailDifference H -
        (diagonalCoefficient H : ℝ) * mobiusSquareTail D := by rw [← hglobal]
    _ = lambertProjectedDiagonal H D := by linarith

/-- Endpoint-facing form: after the exact coordinate agreement above, the
only remaining hypothesis is finite rational separation from every integer. -/
theorem scaleFullTarget_miss_of_renormalized_residue_separation_of_twice_le
    {H D : ℕ} (hH : 0 < H) (hcutoff : 2 * H ≤ D)
    (hsep : ∀ z : ℤ, lambertSquareComplementBound H D <
      |renormalizedResidueProjection H D - (z : ℝ)|) :
    ¬ScaleFullTargetHit H :=
  scaleFullTarget_miss_of_renormalized_residue_separation
    (renormalizedResidueAgreement_of_twice_le hH hcutoff) hsep

/-- **The foreign tail-limit socket is discharged.**  Once `D` contains
`H`, every divisor channel lies in the finite prefix.  The remaining actual
foreign defect is therefore exactly the absolutely summable residue tail
above `D`, whose interval partial sums converge to its `tsum`. -/
theorem foreignResidueTailLimit_of_le
    {H D : ℕ} (hH : 0 < H) (hHD : H ≤ D) :
    ForeignResidueTailLimit H D := by
  let f : ℕ → ℝ := fun n ↦ residueIncrement (n + 1) H
  let tail : ℕ → ℝ := fun n ↦ residueIncrement (D + 1 + n) H
  have hnat : Summable f := by
    rw [show f = fun n : ℕ ↦ residueIncrement (n + 1) H by rfl,
      ← summable_pnat_iff_summable_succ
        (f := fun d : ℕ ↦ residueIncrement d H)]
    exact (summable_positiveResidueIncrement H).congr fun d ↦
      positiveResidueIncrement_coe d H
  have htail : Summable tail := by
    have hshift := (summable_nat_add_iff D).mpr hnat
    simpa [f, tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using hshift
  have hpartial :
      Tendsto (fun n ↦ ∑ i ∈ Finset.range n, tail i) atTop
        (nhds (∑' i : ℕ, tail i)) :=
    htail.hasSum.tendsto_sum_nat
  have hpartialSub :
      Tendsto (fun L ↦ ∑ i ∈ Finset.range (L - D), tail i) atTop
        (nhds (∑' i : ℕ, tail i)) :=
    hpartial.comp (tendsto_sub_atTop_nat D)
  have hwindow :
      (fun L ↦ foreignTailWindow H D L) =
        (fun L ↦ ∑ i ∈ Finset.range (L - D), tail i) := by
    funext L
    unfold foreignTailWindow tail
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hglobalNat :
      scaleDiagonalTailDifference H = ∑' n : ℕ, f n := by
    rw [scaleDiagonalTailDifference_eq_tsum_positiveResidueIncrement]
    calc
      (∑' d : ℕ+, positiveResidueIncrement d H) =
          ∑' d : ℕ+, residueIncrement (d : ℕ) H := by
        apply tsum_congr
        intro d
        exact positiveResidueIncrement_coe d H
      _ = ∑' n : ℕ, residueIncrement (n + 1) H :=
        tsum_pnat_eq_tsum_succ
          (f := fun d : ℕ ↦ residueIncrement d H)
      _ = ∑' n : ℕ, f n := by rfl
  have hprefix :
      (∑ n ∈ Finset.range D, f n) = finiteResidueDiagonal H D := by
    unfold finiteResidueDiagonal f
    rw [← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    simp [Nat.add_comm]
  have hsplit := hnat.sum_add_tsum_nat_add D
  have hglobalSplit :
      scaleDiagonalTailDifference H =
        finiteResidueDiagonal H D + ∑' n : ℕ, tail n := by
    calc
      scaleDiagonalTailDifference H = ∑' n : ℕ, f n := hglobalNat
      _ = (∑ n ∈ Finset.range D, f n) +
          ∑' n : ℕ, f (n + D) := hsplit.symm
      _ = finiteResidueDiagonal H D + ∑' n : ℕ, tail n := by
        rw [hprefix]
        congr 1
        apply tsum_congr
        intro n
        simp [f, tail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have htailValue :
      (∑' n : ℕ, tail n) =
        scaleForeignDefect H - projectedForeignDefect H D := by
    unfold scaleForeignDefect
    rw [hglobalSplit,
      finiteResidueDiagonal_eq_projectedForeign_add_divisor,
      projectedDivisorChannels_eq_scaleExplicitShadow hH hHD]
    ring
  unfold ForeignResidueTailLimit
  rw [hwindow, ← htailValue]
  exact hpartialSub

/-! ## Unconditional projected enclosure -/

/-- The shifted Möbius identity removes the former tail-limit hypothesis
from the finite foreign-residue projection.  Once the cutoff contains the
full diagonal scale, the projected defect is controlled by its explicit
geometric complement budget. -/
theorem controlledForeignProjection_of_twice_le
    {H D : ℕ} (hH : 0 < H) (hcutoff : 2 * H ≤ D) :
    ControlledForeignProjection H D := by
  apply controlledForeignProjection_of_tail_limit hcutoff
  exact foreignResidueTailLimit_of_le hH (by omega)

/-- Exact separation of the finite residue state now rules out a full-target
hit without an analytic socket: the required tail limit is supplied by the
shifted Möbius expansion above. -/
theorem scaleFullTarget_miss_of_projected_separation_of_twice_le
    {H D : ℕ} (hH : 0 < H) (hcutoff : 2 * H ≤ D)
    (hseparation : ProjectedFullTargetSeparation H D) :
    ¬ScaleFullTargetHit H := by
  exact scaleFullTarget_miss_of_projected_separation
    (controlledForeignProjection_of_twice_le hH hcutoff) hseparation

/-- Expanded exact-rational certificate form of the unconditional projected
enclosure. -/
theorem scaleFullTarget_miss_of_projected_separation_of_twice_le_of_forall_int
    {H D : ℕ} (hH : 0 < H) (hcutoff : 2 * H ≤ D)
    (hseparation : ∀ z : ℤ, foreignComplementBound H D <
      |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|) :
    ¬ScaleFullTargetHit H := by
  apply scaleFullTarget_miss_of_projected_separation_of_twice_le hH hcutoff
  exact hseparation

#print axioms controlledForeignProjection_of_twice_le
#print axioms scaleFullTarget_miss_of_projected_separation_of_twice_le
#print axioms scaleFullTarget_miss_of_projected_separation_of_twice_le_of_forall_int
#print axioms firstLambertTailCorrectionRat_cast_eq_tsum
#print axioms residueIncrement_tail_eq_lambert_tails
#print axioms renormalizedResidueAgreement_of_twice_le
#print axioms scaleFullTarget_miss_of_renormalized_residue_separation_of_twice_le

end Erdos249257.TotientShiftedMobiusForeignBridge
