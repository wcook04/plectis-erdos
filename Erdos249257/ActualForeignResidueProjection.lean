import Erdos249257.FullTargetPrimeAdjunctionNoGo
import Erdos249257.RepunitMobiusNumerator
import Erdos249257.SquaredMersenneDiagonalEnclosure
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Actual foreign-residue projection

Unimported producer owner for the finite Möbius-residue projection derived in
`docs/formal_math/erdos249_actual_foreign_residue_projection_receipt_2026_07_11.md`.

The definitions below identify the concrete finite state and its closed
complement budget.  The landed theorem is the proof consumer: once the kernel
identity and complement estimate are supplied, an exact rational separation
from the integer lattice rules out a full-target hit.  The analytic kernel
identity and complement estimate remain the next focused Lean validation lane;
there is no endpoint-defined curvature or new abstract holonomy interface here.
-/

namespace Erdos249257.ActualForeignResidueProjection

open scoped ArithmeticFunction.Moebius BigOperators
open FullTargetPrimeAdjunctionNoGo
open SquaredMersenneDiagonalEnclosure

/-- The least positive shift sending `N` to a multiple of `d`. -/
def residueOffset (d N : ℕ) : ℕ := d - N % d

/-- Above the vertex index, the residue offset is the literal gap to `d`. -/
theorem residueOffset_eq_sub_of_lt {d N : ℕ} (hN : N < d) :
    residueOffset d N = d - N := by
  rw [residueOffset, Nat.mod_eq_of_lt hN]

/-- The exact Möbius residue channel whose sum is the local totient tail. -/
noncomputable def foreignResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - residueOffset d N) *
      (((N + residueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))

/-- The analytic residue state is indexed by positive channels.  Keeping this
wrapper separate from the finite natural-indexed kernel excludes the
totalized `d = 0` denominator from every future `tsum` theorem. -/
noncomputable def positiveForeignResidueKernel (d : ℕ+) (N : ℕ) : ℝ :=
  foreignResidueKernel (d : ℕ) N

/-- The diagonal increment on the positive analytic channel space. -/
noncomputable def positiveResidueIncrement (d : ℕ+) (H : ℕ) : ℝ :=
  positiveForeignResidueKernel d (2 * H) - positiveForeignResidueKernel d H

/-- The common stable factor carried by every channel above the vertex. -/
noncomputable def stableResidueFactor (d : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ d - 1) + 1 / (((2 : ℝ) ^ d - 1) ^ 2)

/-- Once `N < d`, the residue kernel has no remaining dependence on
`N mod d`: it is `mu(d) * 2^N` times a fixed Mersenne factor. -/
theorem foreignResidueKernel_of_lt {d N : ℕ} (hd : 0 < d) (hN : N < d) :
    foreignResidueKernel d N =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (2 : ℝ) ^ N * stableResidueFactor d := by
  have hNle : N ≤ d := hN.le
  have hsub : d - (d - N) = N := Nat.sub_sub_self hNle
  have hadd : N + (d - N) = d := Nat.add_sub_of_le hNle
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpowNat : 1 < 2 ^ d := Nat.one_lt_two_pow hd.ne'
  have hpowR : (1 : ℝ) < (2 : ℝ) ^ d := by exact_mod_cast hpowNat
  have hM : (2 : ℝ) ^ d - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpowR)
  rw [foreignResidueKernel, residueOffset_eq_sub_of_lt hN, hsub, hadd]
  unfold stableResidueFactor
  field_simp [hdR, hM]

/-- Contribution of channel `d` to the diagonal `R_(2H) - R_H`. -/
noncomputable def residueIncrement (d H : ℕ) : ℝ :=
  foreignResidueKernel d (2 * H) - foreignResidueKernel d H

/-- Positive-channel increments agree definitionally with the finite kernel
on the coerced natural index. -/
theorem positiveResidueIncrement_coe (d : ℕ+) (H : ℕ) :
    positiveResidueIncrement d H = residueIncrement (d : ℕ) H := rfl

/-- A divisor channel is exactly one summand of the finite explicit shadow.
This is the finite-side bridge behind the decomposition into divisor and
foreign channels; the global divisor-sum identity remains a separate
Möbius-expansion obligation. -/
theorem residueIncrement_of_dvd {d H : ℕ} (hd : 0 < d) (hdvd : d ∣ H) :
    residueIncrement d H =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (H : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  have h2dvd : d ∣ 2 * H := dvd_mul_of_dvd_right hdvd 2
  have hmod : H % d = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have h2mod : (2 * H) % d = 0 := Nat.mod_eq_zero_of_dvd h2dvd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpowNat : 1 < 2 ^ d := Nat.one_lt_two_pow hd.ne'
  have hpowR : (1 : ℝ) < (2 : ℝ) ^ d := by exact_mod_cast hpowNat
  have hM : (2 : ℝ) ^ d - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpowR)
  unfold residueIncrement foreignResidueKernel residueOffset
  rw [hmod, h2mod]
  simp only [Nat.sub_zero, Nat.sub_self, pow_zero]
  push_cast
  field_simp [hdR, hM]
  ring

/-- In the stable range `2H < d`, the diagonal channel is the explicit
coefficient `C_H` times one fixed Mersenne factor. -/
theorem residueIncrement_of_twice_lt {d H : ℕ} (hd : 0 < d)
    (hstable : 2 * H < d) :
    residueIncrement d H =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (diagonalCoefficient H : ℝ) * stableResidueFactor d := by
  have hH : H < d := by omega
  rw [residueIncrement, foreignResidueKernel_of_lt hd hstable,
    foreignResidueKernel_of_lt hd hH]
  unfold diagonalCoefficient
  have hpow : (1 : ℕ) ≤ 2 ^ H := Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.cast_mul, Nat.cast_sub hpow]
  push_cast
  rw [show 2 * H = H + H by omega, pow_add]
  ring

/-- The stable Mersenne factor is nonnegative. -/
theorem stableResidueFactor_nonneg (d : ℕ) : 0 ≤ stableResidueFactor d := by
  unfold stableResidueFactor
  have hden : (0 : ℝ) ≤ (2 : ℝ) ^ d - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  positivity

/-- Pointwise geometric domination used by the closed complement budget. -/
theorem stableResidueFactor_le_geometric {d : ℕ} (hd : 0 < d) :
    stableResidueFactor d ≤
      2 / (2 : ℝ) ^ d + 4 / (4 : ℝ) ^ d := by
  have hM : (0 : ℝ) < (2 : ℝ) ^ d - 1 := by
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) hd.ne')
  have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ d := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hlinear : (2 : ℝ) ^ d ≤ 2 * ((2 : ℝ) ^ d - 1) := by
    linarith
  have hfirst :
      1 / ((2 : ℝ) ^ d - 1) ≤ 2 / (2 : ℝ) ^ d := by
    rw [div_le_div_iff₀ hM hpow]
    linarith
  have hsq :
      ((2 : ℝ) ^ d) ^ 2 ≤ (2 * ((2 : ℝ) ^ d - 1)) ^ 2 := by
    exact (sq_le_sq₀ hpow.le (mul_nonneg (by norm_num) hM.le)).2 hlinear
  have hfour : (0 : ℝ) < (4 : ℝ) ^ d := by positivity
  have hsecond :
      1 / (((2 : ℝ) ^ d - 1) ^ 2) ≤ 4 / (4 : ℝ) ^ d := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hM) hfour]
    rw [show (4 : ℝ) ^ d = ((2 : ℝ) ^ d) ^ 2 by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_two]]
    nlinarith
  unfold stableResidueFactor
  linarith

/-- Every omitted stable channel is dominated by the geometric summand whose
tail is `foreignComplementBound`. -/
theorem abs_residueIncrement_le_geometric {d H : ℕ}
    (hstable : 2 * H < d) :
    |residueIncrement d H| ≤
      (diagonalCoefficient H : ℝ) *
        (2 / (2 : ℝ) ^ d + 4 / (4 : ℝ) ^ d) := by
  have hd : 0 < d := by omega
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast MersenneLambertLadder.abs_moebius_le_one d
  rw [residueIncrement_of_twice_lt hd hstable, abs_mul, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ diagonalCoefficient H by positivity),
    abs_of_nonneg (stableResidueFactor_nonneg d)]
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| *
          (diagonalCoefficient H : ℝ) * stableResidueFactor d ≤
        1 * (diagonalCoefficient H : ℝ) * stableResidueFactor d := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmu (by positivity))
        (stableResidueFactor_nonneg d)
    _ ≤ (diagonalCoefficient H : ℝ) *
        (2 / (2 : ℝ) ^ d + 4 / (4 : ℝ) ^ d) := by
      simpa using mul_le_mul_of_nonneg_left
        (stableResidueFactor_le_geometric hd)
        (show (0 : ℝ) ≤ diagonalCoefficient H by positivity)

/-- A finite window of omitted channels above cutoff `D`.  This is the finite
precursor of the analytic complement `G_H - P_(H,D)`. -/
noncomputable def foreignTailWindow (H D L : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (D + 1) L, residueIncrement d H

/-- Finite tail windows obey the same geometric majorant as the intended
infinite complement.  Passing this estimate to the `tsum` limit is now a
separate summability step. -/
theorem abs_foreignTailWindow_le_geometric_sum
    {H D L : ℕ} (hcutoff : 2 * H ≤ D) :
    |foreignTailWindow H D L| ≤
      (diagonalCoefficient H : ℝ) *
        ∑ d ∈ Finset.Icc (D + 1) L,
          (2 / (2 : ℝ) ^ d + 4 / (4 : ℝ) ^ d) := by
  unfold foreignTailWindow
  calc
    |∑ d ∈ Finset.Icc (D + 1) L, residueIncrement d H| ≤
        ∑ d ∈ Finset.Icc (D + 1) L, |residueIncrement d H| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc (D + 1) L,
        (diagonalCoefficient H : ℝ) *
          (2 / (2 : ℝ) ^ d + 4 / (4 : ℝ) ^ d) := by
      apply Finset.sum_le_sum
      intro d hdMem
      have hdLower : D + 1 ≤ d := (Finset.mem_Icc.mp hdMem).1
      apply abs_residueIncrement_le_geometric
      omega
    _ = (diagonalCoefficient H : ℝ) *
        ∑ d ∈ Finset.Icc (D + 1) L,
          (2 / (2 : ℝ) ^ d + 4 / (4 : ℝ) ^ d) := by
      rw [Finset.mul_sum]

/-- The finite geometric majorant of every window past `D` is already inside
the closed complement budget.  This is the finite, validation-friendly part
of the eventual `tsum` estimate. -/
theorem geometric_window_le_closed_complement (D L : ℕ) :
    ∑ d ∈ Finset.Icc (D + 1) L,
        (2 / (2 : ℝ) ^ d + 4 / (4 : ℝ) ^ d) ≤
      2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D) := by
  have hIcc : Finset.Icc (D + 1) L = Finset.Ico (D + 1) (L + 1) := by
    ext d
    simp
  rw [hIcc]
  have htwo := geom_sum_Ico_le_of_lt_one
    (x := (1 / 2 : ℝ)) (m := D + 1) (n := L + 1) (by norm_num) (by norm_num)
  have hfour := geom_sum_Ico_le_of_lt_one
    (x := (1 / 4 : ℝ)) (m := D + 1) (n := L + 1) (by norm_num) (by norm_num)
  have htwo' : ∑ d ∈ Finset.Ico (D + 1) (L + 1), (1 / 2 : ℝ) ^ d ≤
      1 / (2 : ℝ) ^ D := by
    calc
      ∑ d ∈ Finset.Ico (D + 1) (L + 1), (1 / 2 : ℝ) ^ d ≤
          (1 / 2 : ℝ) ^ (D + 1) / (1 - (1 / 2 : ℝ)) := htwo
      _ = 1 / (2 : ℝ) ^ D := by
        rw [div_pow]
        field_simp
        ring
  have hfour' : ∑ d ∈ Finset.Ico (D + 1) (L + 1), (1 / 4 : ℝ) ^ d ≤
      1 / (3 * (4 : ℝ) ^ D) := by
    calc
      ∑ d ∈ Finset.Ico (D + 1) (L + 1), (1 / 4 : ℝ) ^ d ≤
          (1 / 4 : ℝ) ^ (D + 1) / (1 - (1 / 4 : ℝ)) := hfour
      _ = 1 / (3 * (4 : ℝ) ^ D) := by
        rw [div_pow]
        field_simp
        ring
  calc
    ∑ d ∈ Finset.Ico (D + 1) (L + 1),
        (2 / (2 : ℝ) ^ d + 4 / (4 : ℝ) ^ d) =
      ∑ d ∈ Finset.Ico (D + 1) (L + 1),
        (2 * (1 / 2 : ℝ) ^ d + 4 * (1 / 4 : ℝ) ^ d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [div_pow, div_pow]
      ring
    _ = 2 * (∑ d ∈ Finset.Ico (D + 1) (L + 1), (1 / 2 : ℝ) ^ d) +
        4 * (∑ d ∈ Finset.Ico (D + 1) (L + 1), (1 / 4 : ℝ) ^ d) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (1 / (2 : ℝ) ^ D) + 4 * (1 / (3 * (4 : ℝ) ^ D)) := by
      gcongr
    _ = 2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D) := by ring

/-- Closed geometric budget for every omitted channel when `2H ≤ D`. -/
noncomputable def foreignComplementBound (H D : ℕ) : ℝ :=
  (diagonalCoefficient H : ℝ) *
    (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D))

/-- The finite foreign tail is bounded by the closed complement budget.  The
only remaining analytic obligation is to identify the actual complement with
the limit of these windows. -/
theorem abs_foreignTailWindow_le_foreignComplementBound
    {H D L : ℕ} (hcutoff : 2 * H ≤ D) :
    |foreignTailWindow H D L| ≤ foreignComplementBound H D := by
  rw [foreignComplementBound]
  calc
    |foreignTailWindow H D L| ≤
        (diagonalCoefficient H : ℝ) *
          ∑ d ∈ Finset.Icc (D + 1) L,
            (2 / (2 : ℝ) ^ d + 4 / (4 : ℝ) ^ d) :=
      abs_foreignTailWindow_le_geometric_sum hcutoff
    _ ≤ (diagonalCoefficient H : ℝ) *
        (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D)) := by
      gcongr
      exact geometric_window_le_closed_complement D L

/-- The actual foreign channels up to cutoff `D`; divisor channels are the
explicit shadow and are deliberately excluded. -/
noncomputable def projectedForeignDefect (H D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ H then 0 else residueIncrement d H

/-- The complementary finite state consisting of precisely the divisor
channels.  Its explicit Möbius form is supplied below. -/
noncomputable def projectedDivisorChannels (H D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ H then residueIncrement d H else 0

/-- The unprojected finite residue state before splitting at the divisor
boundary. -/
noncomputable def finiteResidueDiagonal (H D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, residueIncrement d H

/-- The finite residue state splits exactly into the retained foreign
projection and the complementary divisor state. -/
theorem finiteResidueDiagonal_eq_projectedForeign_add_divisor (H D : ℕ) :
    finiteResidueDiagonal H D =
      projectedForeignDefect H D + projectedDivisorChannels H D := by
  unfold finiteResidueDiagonal projectedForeignDefect projectedDivisorChannels
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdiv : d ∣ H <;> simp [hdiv]

/-- The finite divisor complement is the literal truncated Möbius shadow.
Consequently, the only missing comparison with `scaleExplicitShadow` is the
global divisor expansion supplied by the radical-shadow owner. -/
theorem projectedDivisorChannels_eq_truncated_mobius (H D : ℕ) :
    projectedDivisorChannels H D =
      ∑ d ∈ Finset.Icc 1 D,
        if d ∣ H then
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (H : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1))
        else 0 := by
  unfold projectedDivisorChannels
  apply Finset.sum_congr rfl
  intro d hdMem
  by_cases hdiv : d ∣ H
  · rw [if_pos hdiv, if_pos hdiv,
      residueIncrement_of_dvd (Finset.mem_Icc.mp hdMem).1 hdiv]
  · simp [hdiv]

/-- The real explicit shadow is exactly the sum of all divisor residue
increments.  This is the finite producer required before the analytic channel
sum can be split into divisor and foreign parts. -/
theorem scaleExplicitShadow_eq_sum_divisors_residueIncrement
    {H : ℕ} (hH : 0 < H) :
    scaleExplicitShadow H =
      ∑ d ∈ H.divisors, residueIncrement d H := by
  have hrat :=
    (RepunitMobiusNumerator.sum_divisors_moebius_ratio_eq_scaledMobiusShadow
      H hH).symm
  have hreal := congrArg (fun q : ℚ ↦ (q : ℝ)) hrat
  push_cast at hreal
  rw [scaleExplicitShadow, scaleExplicitShadowRat]
  push_cast
  calc
    (H : ℝ) *
        (RadicalMobiusShadow.numericMobiusShadow H : ℝ) =
      ∑ d ∈ H.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (H : ℝ) /
          ((d : ℝ) *
            (RadicalMobiusShadow.mersenne d : ℝ)) := hreal
    _ = ∑ d ∈ H.divisors, residueIncrement d H := by
      apply Finset.sum_congr rfl
      intro d hdmem
      have hdvd : d ∣ H := Nat.dvd_of_mem_divisors hdmem
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hH
      have hpow : (1 : ℕ) ≤ 2 ^ d :=
        Nat.one_le_pow _ _ (by norm_num)
      have hMcast :
          (RadicalMobiusShadow.mersenne d : ℝ) =
            (2 : ℝ) ^ d - 1 := by
        unfold RadicalMobiusShadow.mersenne
        rw [Nat.cast_sub hpow]
        push_cast
        rfl
      rw [residueIncrement_of_dvd hdpos hdvd, hMcast]

/-- Once the cutoff contains `H`, it contains every divisor channel.  Their
sum is exactly the explicit radical Möbius shadow. -/
theorem projectedDivisorChannels_eq_scaleExplicitShadow
    {H D : ℕ} (hH : 0 < H) (hHD : H ≤ D) :
    projectedDivisorChannels H D = scaleExplicitShadow H := by
  have hset :
      {d ∈ Finset.Icc 1 D | d ∣ H} = H.divisors := by
    ext d
    constructor
    · intro hd
      exact Nat.mem_divisors.mpr
        ⟨(Finset.mem_filter.mp hd).2, hH.ne'⟩
    · intro hd
      have hdvd : d ∣ H := Nat.dvd_of_mem_divisors hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hH
      have hdleH : d ≤ H := Nat.le_of_dvd hH hdvd
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hdpos, hdleH.trans hHD⟩, hdvd⟩
  calc
    projectedDivisorChannels H D =
        ∑ d ∈ {d ∈ Finset.Icc 1 D | d ∣ H},
          residueIncrement d H := by
      unfold projectedDivisorChannels
      rw [Finset.sum_filter]
    _ = ∑ d ∈ H.divisors, residueIncrement d H := by rw [hset]
    _ = scaleExplicitShadow H :=
      (scaleExplicitShadow_eq_sum_divisors_residueIncrement hH).symm

/-- The projection is controlled when its difference from the actual foreign
defect lies inside the explicit geometric budget. -/
def ControlledForeignProjection (H D : ℕ) : Prop :=
  |scaleForeignDefect H - projectedForeignDefect H D| ≤
    foreignComplementBound H D

/-- Exact finite separation of the projected diagonal from every integer. -/
def ProjectedFullTargetSeparation (H D : ℕ) : Prop :=
  ∀ z : ℤ, foreignComplementBound H D <
    |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|

/-- **Complement noncancellation consumer.**  A controlled projection whose
finite rational state is farther from every integer than the whole omitted
complement can move it forces a genuine full-target miss. -/
theorem scaleFullTarget_miss_of_projected_separation
    {H D : ℕ} (hcontrol : ControlledForeignProjection H D)
    (hseparation : ProjectedFullTargetSeparation H D) :
    ¬ScaleFullTargetHit H := by
  rw [scaleFullTargetHit_iff_integral]
  rintro ⟨z, hz⟩
  have hcontrol' := hcontrol
  unfold ControlledForeignProjection at hcontrol'
  rw [scaleForeignDefect, ← hz] at hcontrol'
  have hneg :
      scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ) =
        -((z : ℝ) - scaleExplicitShadow H - projectedForeignDefect H D) := by
    ring
  have hle :
      |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)| ≤
        foreignComplementBound H D := by
    rw [hneg, abs_neg]
    exact hcontrol'
  exact (not_lt_of_ge hle) (hseparation z)

/-- Expanded hypothesis form for downstream certificate generators. -/
theorem scaleFullTarget_miss_of_abs_sub_le_of_forall_int
    {H D : ℕ}
    (hcontrol : |scaleForeignDefect H - projectedForeignDefect H D| ≤
      foreignComplementBound H D)
    (hseparation : ∀ z : ℤ, foreignComplementBound H D <
      |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|) :
    ¬ScaleFullTargetHit H :=
  scaleFullTarget_miss_of_projected_separation hcontrol hseparation

/-! ## First-order Lambert renormalisation -/

/-- Exact rational correction which spends the first-order Möbius-Lambert
tail instead of bounding it absolutely. -/
def firstLambertTailCorrectionRat (D : ℕ) : ℚ :=
  1 / 2 - ∑ k ∈ Finset.range D,
    (ArithmeticFunction.moebius (k + 1) : ℚ) /
      ((2 : ℚ) ^ (k + 1) - 1)

/-- The corrected residue presentation of the projected diagonal. -/
noncomputable def renormalizedResidueProjection (H D : ℕ) : ℝ :=
  scaleExplicitShadow H + projectedForeignDefect H D +
    (diagonalCoefficient H : ℝ) * (firstLambertTailCorrectionRat D : ℝ)

/-- Agreement of the corrected residue presentation with the canonical
squared-Mersenne centre.  The exact checker proves this finite identity for
fixtures; the remaining general Lean proof is the global divisor/kernel bridge
owned by this residue lane.  This proposition is coordinate-only: the direct
squared-Mersenne full-target consumer does not require it. -/
def RenormalizedResidueAgreement (H D : ℕ) : Prop :=
  renormalizedResidueProjection H D = lambertProjectedDiagonal H D

/-- Once the finite residue/kernel bridge supplies agreement, the canonical
sharp square-tail enclosure immediately turns corrected residue separation
into an actual full-target miss. -/
theorem scaleFullTarget_miss_of_renormalized_residue_separation
    {H D : ℕ} (hagrees : RenormalizedResidueAgreement H D)
    (hsep : ∀ z : ℤ, lambertSquareComplementBound H D <
      |renormalizedResidueProjection H D - (z : ℝ)|) :
    ¬ScaleFullTargetHit H := by
  apply scaleFullTarget_miss_of_lambert_projected_separation
  intro z
  rw [← hagrees]
  exact hsep z

#print axioms scaleFullTarget_miss_of_renormalized_residue_separation

end Erdos249257.ActualForeignResidueProjection
