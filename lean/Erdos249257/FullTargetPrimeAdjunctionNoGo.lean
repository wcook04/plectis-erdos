import Erdos249257.DiagonalPincerDecomposition
import Erdos249257.PrimePowerJumpDynamics
import Mathlib.Tactic

/-!
# Full-target prime-adjunction no-go

This file closes the proposed two-prime full-target diamond as an obstruction
route.  At an arbitrary positive scale `H`, the actual diagonal tail difference
has an affine multiplicative transport along every ray `H \mapsto kH`.  Hence an
integral diagonal at `H` remains integral at every multiple, and the four-hit
prime-adjunction square is equivalent to its bottom hit.

The same calculation transports the actual foreign defect.  Its inhomogeneous
term is the endpoint coboundary `Q * E_H - E_(kH)`, so the complete state has
zero diamond curvature.  A future positive holonomy route therefore needs an
independently defined projection of the actual foreign state together with a
theorem controlling the discarded complement; explicit-shadow fibres alone
cannot supply it.
-/

namespace Erdos249257.FullTargetPrimeAdjunctionNoGo

open scoped BigOperators
open TotientTailPeriodKiller
open RadicalMobiusShadow
open DiagonalPincerDecomposition

/-- The #249 constant, named locally for the generic-scale transport. -/
noncomputable def totientSeries : ℝ :=
  ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n

/-- The coefficient of the #249 constant in `R_(2H) - R_H`. -/
def diagonalCoefficient (H : ℕ) : ℕ := 2 ^ H * (2 ^ H - 1)

/-- The actual diagonal tail difference at an arbitrary scale. -/
noncomputable def scaleDiagonalTailDifference (H : ℕ) : ℝ :=
  totientTail (2 * H) - totientTail H

/-- The integral prefix correction in the generic diagonal formula. -/
def diagonalPrefixCorrection (H : ℕ) : ℤ :=
  (totientPrefix H : ℤ) - (totientPrefix (2 * H) : ℤ)

/-- Exact generic-scale diagonal formula `D_H = C_H S + Z_H`. -/
theorem scaleDiagonalTailDifference_eq (H : ℕ) :
    scaleDiagonalTailDifference H =
      (diagonalCoefficient H : ℝ) * totientSeries +
        (diagonalPrefixCorrection H : ℝ) := by
  have hH := two_pow_mul_totient_series_eq H
  have h2H := two_pow_mul_totient_series_eq (2 * H)
  change (2 : ℝ) ^ H * totientSeries =
    (totientPrefix H : ℝ) + totientTail H at hH
  change (2 : ℝ) ^ (2 * H) * totientSeries =
    (totientPrefix (2 * H) : ℝ) + totientTail (2 * H) at h2H
  unfold scaleDiagonalTailDifference diagonalCoefficient
    diagonalPrefixCorrection
  push_cast
  rw [show 2 * H = H + H by omega] at h2H ⊢
  rw [pow_add] at h2H
  have hpow : (1 : ℕ) ≤ 2 ^ H := Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.cast_sub hpow]
  push_cast
  nlinarith

/-- The exact natural multiplier carrying the coefficient at `H` to `kH`. -/
def diagonalScaleQuotient (H k : ℕ) : ℕ :=
  2 ^ ((k - 1) * H) * ∑ i ∈ Finset.range k, (2 ^ H) ^ i

theorem diagonalCoefficient_pos {H : ℕ} (hH : 0 < H) :
    0 < diagonalCoefficient H := by
  unfold diagonalCoefficient
  have : 1 < 2 ^ H := Nat.one_lt_two_pow hH.ne'
  exact Nat.mul_pos (pow_pos (by norm_num) _) (Nat.sub_pos_of_lt this)

/-- `C_(kH) = Q_k(H) C_H`, with the quotient displayed as a geometric sum. -/
theorem diagonalCoefficient_mul (H k : ℕ) (hk : 0 < k) :
    diagonalCoefficient (k * H) =
      diagonalScaleQuotient H k * diagonalCoefficient H := by
  have hgeom := geom_sum_mul_of_one_le (x := 2 ^ H)
    (Nat.one_le_pow _ _ (by norm_num)) k
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk.ne'
  have hexp : (k - 1) * H + H = k * H := by
    calc
      (k - 1) * H + H = ((k - 1) + 1) * H := by ring
      _ = k * H := by rw [Nat.sub_add_cancel hk1]
  have hpow : 2 ^ ((k - 1) * H) * 2 ^ H = 2 ^ (k * H) := by
    rw [← pow_add, hexp]
  unfold diagonalCoefficient diagonalScaleQuotient
  calc
    2 ^ (k * H) * (2 ^ (k * H) - 1) =
        2 ^ (k * H) * ((2 ^ H) ^ k - 1) := by
          rw [Nat.mul_comm k H, pow_mul]
    _ = 2 ^ (k * H) *
        ((∑ i ∈ Finset.range k, (2 ^ H) ^ i) * (2 ^ H - 1)) := by
          rw [← hgeom]
    _ = (2 ^ ((k - 1) * H) *
          ∑ i ∈ Finset.range k, (2 ^ H) ^ i) *
        (2 ^ H * (2 ^ H - 1)) := by
          rw [← hpow]
          ring

/-- The integer correction in affine diagonal transport. -/
def diagonalTransportCorrection (H k : ℕ) : ℤ :=
  diagonalPrefixCorrection (k * H) -
    (diagonalScaleQuotient H k : ℤ) * diagonalPrefixCorrection H

/-- Exact affine transport of the actual diagonal along every positive
multiplicative scale ray. -/
theorem scaleDiagonalTailDifference_mul (H k : ℕ) (hk : 0 < k) :
    scaleDiagonalTailDifference (k * H) =
      (diagonalScaleQuotient H k : ℝ) * scaleDiagonalTailDifference H +
        (diagonalTransportCorrection H k : ℝ) := by
  rw [scaleDiagonalTailDifference_eq, scaleDiagonalTailDifference_eq,
    diagonalCoefficient_mul H k hk]
  unfold diagonalTransportCorrection
  push_cast
  ring

/-- The exact rational explicit shadow at an arbitrary scale. -/
def scaleExplicitShadowRat (H : ℕ) : ℚ :=
  (H : ℚ) * numericMobiusShadow H

noncomputable def scaleExplicitShadow (H : ℕ) : ℝ :=
  (scaleExplicitShadowRat H : ℝ)

/-- The actual part of the generic diagonal left after removing the explicit
finite Möbius shadow. -/
noncomputable def scaleForeignDefect (H : ℕ) : ℝ :=
  scaleDiagonalTailDifference H - scaleExplicitShadow H

/-- The full reduced-rational pincer target at a generic scale. -/
def ScaleFullTargetHit (H : ℕ) : Prop :=
  ∃ z : ℤ, ((scaleExplicitShadowRat H).den : ℝ) * scaleForeignDefect H =
    (-(scaleExplicitShadowRat H).num : ℝ) +
      ((scaleExplicitShadowRat H).den : ℝ) * (z : ℝ)

/-- The generic full-target pincer is exactly integrality of the actual
diagonal; its lattice witness is not an independent state variable. -/
theorem scaleFullTargetHit_iff_integral (H : ℕ) :
    ScaleFullTargetHit H ↔
      IsIntegralValue (scaleDiagonalTailDifference H) := by
  have hden : (0 : ℝ) < (scaleExplicitShadowRat H).den := by
    exact_mod_cast (scaleExplicitShadowRat H).den_pos
  have hden0 : ((scaleExplicitShadowRat H).den : ℝ) ≠ 0 := hden.ne'
  have hshadow : scaleExplicitShadow H =
      ((scaleExplicitShadowRat H).num : ℝ) /
        ((scaleExplicitShadowRat H).den : ℝ) := by
    rw [scaleExplicitShadow, Rat.cast_def]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [scaleForeignDefect, hshadow] at hz
    field_simp [hden0] at hz
    have hmul : ((scaleExplicitShadowRat H).den : ℝ) *
        (scaleDiagonalTailDifference H - (z : ℝ)) = 0 := by
      linarith
    have hzero : scaleDiagonalTailDifference H - (z : ℝ) = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hden0
    linarith
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [scaleForeignDefect, hshadow]
    have hz' : scaleDiagonalTailDifference H = (z : ℝ) := hz.symm
    rw [hz']
    field_simp
    ring

/-- A producer-independent enclosure consumer for the actual diagonal.
Any centre separated from every integer by more than a proved error radius
forces a miss of the full reduced target. -/
theorem scaleFullTarget_miss_of_enclosure
    {H : ℕ} {q ε : ℝ}
    (hbound : |scaleDiagonalTailDifference H - q| ≤ ε)
    (hsep : ∀ z : ℤ, ε < |q - (z : ℝ)|) :
    ¬ScaleFullTargetHit H := by
  rw [scaleFullTargetHit_iff_integral]
  rintro ⟨z, hz⟩
  have hle : |q - (z : ℝ)| ≤ ε := by
    rw [hz, abs_sub_comm]
    exact hbound
  exact (not_lt_of_ge hle) (hsep z)

/-- Full-target hits propagate upward along divisibility rays. -/
theorem scaleFullTargetHit_mul {H k : ℕ} (hk : 0 < k)
    (hHit : ScaleFullTargetHit H) : ScaleFullTargetHit (k * H) := by
  rw [scaleFullTargetHit_iff_integral] at hHit ⊢
  obtain ⟨z, hz⟩ := hHit
  refine ⟨(diagonalScaleQuotient H k : ℤ) * z +
    diagonalTransportCorrection H k, ?_⟩
  rw [scaleDiagonalTailDifference_mul H k hk, ← hz]
  push_cast
  ring

/-- The four-hit prime-adjunction condition contains exactly the information
of the bottom hit.  No primality or freshness assumption is needed. -/
theorem fullTarget_primeAdjunction_diamond_iff_root
    (H p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (ScaleFullTargetHit H ∧ ScaleFullTargetHit (p * H) ∧
      ScaleFullTargetHit (q * H) ∧ ScaleFullTargetHit (p * q * H)) ↔
      ScaleFullTargetHit H := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, scaleFullTargetHit_mul hp h,
      scaleFullTargetHit_mul hq h, ?_⟩
    simpa [Nat.mul_assoc] using scaleFullTargetHit_mul (Nat.mul_pos hp hq) h

/-- The inhomogeneous foreign correction is an endpoint coboundary. -/
noncomputable def foreignTransportCorrection (H k : ℕ) : ℝ :=
  (diagonalScaleQuotient H k : ℝ) * scaleExplicitShadow H -
    scaleExplicitShadow (k * H)

/-- First theorem that transports the actual foreign defect rather than only
the explicit polynomial shadow. -/
theorem scaleForeignDefect_mul (H k : ℕ) (hk : 0 < k) :
    scaleForeignDefect (k * H) =
      (diagonalScaleQuotient H k : ℝ) * scaleForeignDefect H +
        foreignTransportCorrection H k +
          (diagonalTransportCorrection H k : ℝ) := by
  rw [scaleForeignDefect, scaleForeignDefect,
    scaleDiagonalTailDifference_mul H k hk]
  unfold foreignTransportCorrection
  ring

/-- Scale quotients compose, which is the algebra behind zero curvature. -/
theorem diagonalScaleQuotient_comp
    (H k l : ℕ) (hH : 0 < H) (hk : 0 < k) (hl : 0 < l) :
    diagonalScaleQuotient (k * H) l * diagonalScaleQuotient H k =
      diagonalScaleQuotient H (l * k) := by
  have h1 := diagonalCoefficient_mul H k hk
  have h2 := diagonalCoefficient_mul (k * H) l hl
  have h3 := diagonalCoefficient_mul H (l * k) (Nat.mul_pos hl hk)
  have heq :
      (diagonalScaleQuotient (k * H) l * diagonalScaleQuotient H k) *
          diagonalCoefficient H =
        diagonalScaleQuotient H (l * k) * diagonalCoefficient H := by
    calc
      _ = diagonalScaleQuotient (k * H) l * diagonalCoefficient (k * H) := by
        rw [h1, mul_assoc]
      _ = diagonalCoefficient (l * (k * H)) := h2.symm
      _ = diagonalCoefficient ((l * k) * H) := by rw [Nat.mul_assoc]
      _ = _ := h3
  exact Nat.eq_of_mul_eq_mul_right (diagonalCoefficient_pos hH) heq

/-- The complete foreign correction has exactly zero `(p,q)` diamond
curvature. -/
theorem foreignTransportCorrection_primeAdjunction_flat
    (H p q : ℕ) (hH : 0 < H) (hp : 0 < p) (hq : 0 < q) :
    (diagonalScaleQuotient (p * H) q : ℝ) *
          foreignTransportCorrection H p +
        foreignTransportCorrection (p * H) q =
      (diagonalScaleQuotient (q * H) p : ℝ) *
          foreignTransportCorrection H q +
        foreignTransportCorrection (q * H) p := by
  have hpq := diagonalScaleQuotient_comp H p q hH hp hq
  have hqp := diagonalScaleQuotient_comp H q p hH hq hp
  have hpqR :
      (diagonalScaleQuotient (p * H) q : ℝ) *
          diagonalScaleQuotient H p =
        diagonalScaleQuotient H (q * p) := by exact_mod_cast hpq
  have hqpR :
      (diagonalScaleQuotient (q * H) p : ℝ) *
          diagonalScaleQuotient H q =
        diagonalScaleQuotient H (p * q) := by exact_mod_cast hqp
  calc
    _ = ((diagonalScaleQuotient (p * H) q : ℝ) *
          diagonalScaleQuotient H p) * scaleExplicitShadow H -
        scaleExplicitShadow ((q * p) * H) := by
        unfold foreignTransportCorrection
        rw [← Nat.mul_assoc]
        ring
    _ = (diagonalScaleQuotient H (q * p) : ℝ) *
          scaleExplicitShadow H - scaleExplicitShadow ((q * p) * H) := by
        rw [hpqR]
    _ = (diagonalScaleQuotient H (p * q) : ℝ) *
          scaleExplicitShadow H - scaleExplicitShadow ((p * q) * H) := by
        rw [Nat.mul_comm p q]
    _ = ((diagonalScaleQuotient (q * H) p : ℝ) *
          diagonalScaleQuotient H q) * scaleExplicitShadow H -
        scaleExplicitShadow ((p * q) * H) := by
        rw [hqpR]
    _ = _ := by
        unfold foreignTransportCorrection
        rw [← Nat.mul_assoc]
        ring

#print axioms scaleDiagonalTailDifference_eq
#print axioms diagonalCoefficient_mul
#print axioms scaleDiagonalTailDifference_mul
#print axioms scaleFullTargetHit_iff_integral
#print axioms scaleFullTarget_miss_of_enclosure
#print axioms scaleFullTargetHit_mul
#print axioms fullTarget_primeAdjunction_diamond_iff_root
#print axioms scaleForeignDefect_mul
#print axioms foreignTransportCorrection_primeAdjunction_flat

end Erdos249257.FullTargetPrimeAdjunctionNoGo
