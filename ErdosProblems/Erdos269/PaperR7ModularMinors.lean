import ErdosProblems.Erdos269.KernelCarryRank
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Round 7: actual uniform minors modulo every admissible denominator

Reduction is the inverse of the NATURAL height in `ZMod B`. There is no
putative ring homomorphism from `ℚ` to `ZMod B`. We first compute with units
in an arbitrary commutative ring, then identify the result with that inverse.
The row/column indices are chosen before either the modulus or layer.

Validation: authored, not compiled. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems.Shared

section Units
variable {R : Type*} [CommRing R]

private def heightUnit235 (u₂ u₃ u₅ : Rˣ) (x : ℕ) : Rˣ :=
  u₂ ^ Nat.log 2 x * u₃ ^ Nat.log 3 x * u₅ ^ Nat.log 5 x

private def rowUnit235 (u₂ u₃ u₅ : Rˣ) (i k : ℕ) : Rˣ :=
  u₂ ^ i * u₃ ^ Nat.log 3 (2 ^ i * 5 ^ k) *
    u₅ ^ Nat.log 5 (2 ^ i) * u₅ ^ k

private def colUnit235 (u₂ u₃ u₅ : Rˣ) (j k : ℕ) : Rˣ :=
  u₂ ^ Nat.log 2 (3 ^ j * 5 ^ k) * u₃ ^ j * u₅ ^ Nat.log 5 (3 ^ j)

private theorem heightUnit235_val (u₂ u₃ u₅ : Rˣ)
    (h₂ : (u₂ : R) = 2) (h₃ : (u₃ : R) = 3) (h₅ : (u₅ : R) = 5) (x : ℕ) :
    (heightUnit235 u₂ u₃ u₅ x : R) = (threePrimeHeight 2 3 5 x : R) := by
  simp [heightUnit235, threePrimeHeight, h₂, h₃, h₅]

private theorem rowUnit235_val (u₂ u₃ u₅ : Rˣ)
    (h₂ : (u₂ : R) = 2) (h₃ : (u₃ : R) = 3) (h₅ : (u₅ : R) = 5) (i k : ℕ) :
    (rowUnit235 u₂ u₃ u₅ i k : R) = (rowFactor 2 3 5 i k : R) := by
  simp [rowUnit235, rowFactor, h₂, h₃, h₅]

private theorem colUnit235_val (u₂ u₃ u₅ : Rˣ)
    (h₂ : (u₂ : R) = 2) (h₃ : (u₃ : R) = 3) (h₅ : (u₅ : R) = 5) (j k : ℕ) :
    (colUnit235 u₂ u₃ u₅ j k : R) = (colFactor 2 3 5 j k : R) := by
  simp [colUnit235, colFactor, h₂, h₃, h₅]

private theorem heightUnit235_factorisation (u₂ u₃ u₅ : Rˣ)
    (h₂ : (u₂ : R) = 2) (h₃ : (u₃ : R) = 3) (h₅ : (u₅ : R) = 5) (i j k : ℕ) :
    heightUnit235 u₂ u₃ u₅ (smooth3Val 2 3 5 i j k) =
      rowUnit235 u₂ u₃ u₅ i k * colUnit235 u₂ u₃ u₅ j k *
        u₅ ^ logCarry 5 (2 ^ i) (3 ^ j) := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, h₅,
    heightUnit235_val u₂ u₃ u₅ h₂ h₃ h₅,
    rowUnit235_val u₂ u₃ u₅ h₂ h₃ h₅,
    colUnit235_val u₂ u₃ u₅ h₂ h₃ h₅]
  have hN := threePrimeHeight_factorisation
    (by norm_num : 1 < (2 : ℕ)) (by norm_num : 1 < (3 : ℕ))
    (by norm_num : 1 < (5 : ℕ)) i j k
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    congrArg (fun x : ℕ => (x : R)) hN

private theorem product_units_isUnit {ι : Type*} [Fintype ι] (u : ι → Rˣ) :
    IsUnit (∏ i, (u i : R)) := by
  classical
  exact ⟨∏ i, u i, by simp⟩

private theorem inverse_five_sub_one_isUnit (u₂ u₅ : Rˣ)
    (h₂ : (u₂ : R) = 2) (h₅ : (u₅ : R) = 5) :
    IsUnit ((↑(u₅⁻¹) : R) - 1) := by
  have hmul : (5 : R) * (↑(u₅⁻¹) : R) = 1 := by rw [← h₅]; simp
  have heq : (↑(u₅⁻¹) : R) - 1 = -((2 : R) ^ 2) * (↑(u₅⁻¹) : R) := by
    calc
      (↑(u₅⁻¹) : R) - 1 = (↑(u₅⁻¹) : R) - 5 * (↑(u₅⁻¹) : R) := by rw [hmul]
      _ = -((2 : R) ^ 2) * (↑(u₅⁻¹) : R) := by ring
  rw [heq]
  have hu₂ : IsUnit (2 : R) := by rw [← h₂]; exact u₂.isUnit
  exact (hu₂.pow 2).neg.mul (u₅⁻¹).isUnit

/-- The selected staircase is invertible in every ring in which 2, 3, 5 are units. -/
private theorem selected_unit_minor (u₂ u₃ u₅ : Rˣ)
    (h₂ : (u₂ : R) = 2) (h₃ : (u₃ : R) = 3) (h₅ : (u₅ : R) = 5)
    (n : ℕ) (I J : Fin (n + 1) → ℕ)
    (hcarry : ∀ i j, logCarry 5 (2 ^ I i) (3 ^ J j) =
      if (j : ℕ) ≤ (i : ℕ) then 1 else 0) (k : ℕ) :
    IsUnit (Matrix.det fun i j : Fin (n + 1) =>
      (↑((heightUnit235 u₂ u₃ u₅ (smooth3Val 2 3 5 (I i) (J j) k))⁻¹) : R)) := by
  let A : Fin (n + 1) → Rˣ := fun i => (rowUnit235 u₂ u₃ u₅ (I i) k)⁻¹
  let B : Fin (n + 1) → Rˣ := fun j => (colUnit235 u₂ u₃ u₅ (J j) k)⁻¹
  have hmat : (fun i j : Fin (n + 1) =>
        (↑((heightUnit235 u₂ u₃ u₅ (smooth3Val 2 3 5 (I i) (J j) k))⁻¹) : R)) =
      Matrix.diagonal (fun i => (A i : R)) *
        carryStaircase (↑(u₅⁻¹) : R) n * Matrix.diagonal (fun j => (B j : R)) := by
    funext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul,
      heightUnit235_factorisation u₂ u₃ u₅ h₂ h₃ h₅, hcarry i j]
    by_cases hji : (j : ℕ) ≤ (i : ℕ)
    · simp [carryStaircase, hji, A, B, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
    · simp [carryStaircase, hji, A, B, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, det_carryStaircase]
  exact ((product_units_isUnit A).mul
    ((u₅⁻¹).isUnit.mul ((inverse_five_sub_one_isUnit u₂ u₅ h₂ h₅).pow n))).mul
      (product_units_isUnit B)

end Units

/-- The literal reduction: invert the natural running-LCM height modulo B. -/
noncomputable def kernelMod235 (B i j k : ℕ) : ZMod B :=
  (threePrimeHeight 2 3 5 (smooth3Val 2 3 5 i j k) : ZMod B)⁻¹

private theorem inverse_unit_value_zmod {B : ℕ} (u : (ZMod B)ˣ) :
    (↑(u⁻¹) : ZMod B) = (u : ZMod B)⁻¹ := by
  have h := ZMod.mul_inv_of_unit (u : ZMod B) u.isUnit
  calc
    (↑(u⁻¹) : ZMod B) = (↑(u⁻¹) : ZMod B) * 1 := by simp
    _ = (↑(u⁻¹) : ZMod B) * ((u : ZMod B) * (u : ZMod B)⁻¹) := by rw [h]
    _ = ((↑(u⁻¹) : ZMod B) * (u : ZMod B)) * (u : ZMod B)⁻¹ := by ring
    _ = (u : ZMod B)⁻¹ := by simp

private theorem admissible_prime_units {B : ℕ} (hB : Nat.Coprime B 30) :
    IsUnit (2 : ZMod B) ∧ IsUnit (3 : ZMod B) ∧ IsUnit (5 : ZMod B) := by
  have h30 : Nat.Coprime (2 * 3 * 5) B := by simpa using hB.symm
  rcases Nat.coprime_mul_iff_left.mp h30 with ⟨h23, h5⟩
  rcases Nat.coprime_mul_iff_left.mp h23 with ⟨h2, h3⟩
  exact ⟨(ZMod.isUnit_iff_coprime _ _).mpr h2,
    (ZMod.isUnit_iff_coprime _ _).mpr h3, (ZMod.isUnit_iff_coprime _ _).mpr h5⟩

/-- Whole short-note `res:admissible-modular-minors`, including the rational
nonvanishing required by the phrase "the maps in Theorem 1". Choices precede B and k. -/
theorem admissible_modular_minors (n : ℕ) :
    ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧
      (∀ k : ℕ,
        (Matrix.det fun i j : Fin n => threePrimeKernelQ 2 3 5 (I i) (J j) k) ≠ 0) ∧
      (∀ B : ℕ, 2 ≤ B → Nat.Coprime B 30 → ∀ k : ℕ,
        IsUnit (Matrix.det fun i j : Fin n => kernelMod235 B (I i) (J j) k) ∧
        IsUnit (Matrix.of fun i j : Fin n => kernelMod235 B (I i) (J j) k)) := by
  have hα := noIntegerOrbit_logb_of_prime
    (by decide : Nat.Prime 2) (by decide : Nat.Prime 5) (by decide : (2 : ℕ) ≠ 5)
  have hβ := noIntegerOrbit_logb_of_prime
    (by decide : Nat.Prime 3) (by decide : Nat.Prime 5) (by decide : (3 : ℕ) ≠ 5)
  obtain ⟨I, J, _, _, hI, hJ, hstair⟩ := exists_staircase_indices hα hβ n
  have hcarry : ∀ i j : Fin n,
      logCarry 5 (2 ^ I i) (3 ^ J j) = if (j : ℕ) ≤ (i : ℕ) then 1 else 0 := by
    intro i j
    have h := logCarry_pow_eq_floor_fract (b := 5) (by norm_num)
      (by norm_num : 0 < (2 : ℕ)) (by norm_num : 0 < (3 : ℕ)) (I i) (J j)
    rw [hstair i j] at h
    split_ifs at h ⊢ <;> omega
  refine ⟨I, J, hI, hJ, ?_, ?_⟩
  · intro k
    cases n with
    | zero => simp [Matrix.det_fin_zero]
    | succ n =>
      let u₂ : ℚˣ := Units.mk0 2 (by norm_num)
      let u₃ : ℚˣ := Units.mk0 3 (by norm_num)
      let u₅ : ℚˣ := Units.mk0 5 (by norm_num)
      have hunit := selected_unit_minor u₂ u₃ u₅ rfl rfl rfl n I J hcarry k
      have hinv (u : ℚˣ) : (↑(u⁻¹) : ℚ) = (u : ℚ)⁻¹ := by
        apply mul_left_cancel₀ u.ne_zero
        simp
      have hentry : ∀ i j : Fin (n + 1),
          (↑((heightUnit235 u₂ u₃ u₅ (smooth3Val 2 3 5 (I i) (J j) k))⁻¹) : ℚ) =
          threePrimeKernelQ 2 3 5 (I i) (J j) k := by
        intro i j
        rw [hinv, heightUnit235_val u₂ u₃ u₅ rfl rfl rfl]
        rfl
      have hdet : IsUnit (Matrix.det fun i j : Fin (n + 1) =>
          threePrimeKernelQ 2 3 5 (I i) (J j) k) := by
        simpa only [hentry] using hunit
      exact isUnit_iff_ne_zero.mp hdet
  · intro B _ hB k
    have hdet : IsUnit (Matrix.det fun i j : Fin n => kernelMod235 B (I i) (J j) k) := by
      cases n with
      | zero => simp [Matrix.det_fin_zero]
      | succ n =>
        obtain ⟨⟨u₂, h₂⟩, ⟨u₃, h₃⟩, ⟨u₅, h₅⟩⟩ := admissible_prime_units hB
        have hunit := selected_unit_minor u₂ u₃ u₅ h₂ h₃ h₅ n I J hcarry k
        have hentry : ∀ i j : Fin (n + 1),
            (↑((heightUnit235 u₂ u₃ u₅ (smooth3Val 2 3 5 (I i) (J j) k))⁻¹) : ZMod B) =
            kernelMod235 B (I i) (J j) k := by
          intro i j
          rw [inverse_unit_value_zmod, heightUnit235_val u₂ u₃ u₅ h₂ h₃ h₅]
          rfl
        simpa only [hentry] using hunit
    exact ⟨hdet, (Matrix.isUnit_iff_isUnit_det _).mpr hdet⟩

end ErdosProblems.Erdos269.PaperR7
