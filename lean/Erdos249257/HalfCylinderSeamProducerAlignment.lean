import Erdos249257.HalfCylinderProducerCarrySocket
import Erdos249257.HalfCylinderFiniteShadow

/-!
# Seam-to-producer carry alignment

The first-wrap seam hole is one more than the left zero-child carry at row
`2s`. Two further coefficient rows turn that carry into the producer-aligned
carry. The correction is the explicit paired incidence pulse.
-/

namespace Erdos249257

open Set
open HalfCarryReachability
open HalfCylinderFiniteShadow

/-- If `insert s P` is the left boundary support at the first feedback row,
its producer-aligned carry is four times the shifted seam hole, minus the
explicit odd/even paired incidence pulse at rows `2s+1` and `2s+2`.

The seam hole is `2δ - supportCoeff P (2s)`, as in
`actualFirstWrap_hole_eq_leftZeroCarry_add_one`. -/
theorem producerCarry_insert_eq_four_mul_shiftedHole_sub_pulse
    (P : Set ℕ) (s : ℕ) (hs : 1 ≤ s) (hsP : s ∉ P) (δ : ℤ)
    (hδ : integerHalfCarry (insert s P) (2 * s - 2) = δ) :
    producerCarry (insert s P) s =
      4 * (2 * δ - (supportCoeff P (2 * s) : ℤ) - 1) -
        (2 * (supportCoeff (insert s P) (2 * s + 1) : ℤ) +
          (supportCoeff (insert s P) (2 * s + 2) : ℤ)) := by
  let A : Set ℕ := insert s P
  let H : ℤ := 2 * δ - (supportCoeff P (2 * s) : ℤ)
  have hhole := actualFirstWrap_hole_eq_leftZeroCarry_add_one
    P hs hsP δ hδ
  have hparent : integerHalfCarry A (2 * s - 1) = H - 1 := by
    dsimp [A, H]
    omega
  have hstep : integerHalfCarry A (2 * s) =
      2 * integerHalfCarry A (2 * s - 1) -
        (supportCoeff A (2 * s + 1) : ℤ) := by
    have hi1 : 2 * s = (2 * s - 1) + 1 := by omega
    have hi2 : 2 * s - 1 + 2 = 2 * s + 1 := by omega
    have hcoeffIndex :
        (supportCoeff A (2 * s - 1 + 2) : ℤ) =
          (supportCoeff A (2 * s + 1) : ℤ) :=
      congrArg (fun n : ℕ ↦ (supportCoeff A n : ℤ)) hi2
    calc
      integerHalfCarry A (2 * s) =
          integerHalfCarry A ((2 * s - 1) + 1) :=
        congrArg (integerHalfCarry A) hi1
      _ = 2 * integerHalfCarry A (2 * s - 1) -
          (supportCoeff A (2 * s - 1 + 2) : ℤ) :=
        integerHalfCarry_succ A (2 * s - 1)
      _ = 2 * integerHalfCarry A (2 * s - 1) -
          (supportCoeff A (2 * s + 1) : ℤ) := by rw [hcoeffIndex]
  calc
    producerCarry (insert s P) s =
        integerHalfCarry A (2 * s + 1) := by rfl
    _ = 2 * integerHalfCarry A (2 * s) -
          (supportCoeff A (2 * s + 2) : ℤ) := by
      simpa using integerHalfCarry_succ A (2 * s)
    _ = 2 * (2 * integerHalfCarry A (2 * s - 1) -
          (supportCoeff A (2 * s + 1) : ℤ)) -
          (supportCoeff A (2 * s + 2) : ℤ) := by
      rw [hstep]
    _ = 4 * (2 * δ - (supportCoeff P (2 * s) : ℤ) - 1) -
          (2 * (supportCoeff (insert s P) (2 * s + 1) : ℤ) +
            (supportCoeff (insert s P) (2 * s + 2) : ℤ)) := by
      rw [hparent]
      dsimp [A, H]
      ring

#print axioms producerCarry_insert_eq_four_mul_shiftedHole_sub_pulse

end Erdos249257
