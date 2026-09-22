import ErdosProblems.Erdos1049.SourceFiniteTransformR12
import ErdosProblems.Erdos1049.SourceHomogeneousR12
import Mathlib

/-!
# Root-window cancellation for the actual Omega carry pattern



The two independent variables are important. The second Gaussian's lower
argument may exceed its upper argument in a residue block. Replacing the
integer exponent w-a+1 by truncated natural subtraction is incorrect.
This file proves the finite local identity with the integer exponent,
including these zero terms. It does not assume a local vanishing conclusion.
The remaining passage from source summands to residue blocks is separately
recorded, and is not smuggled in as an axiom here.
-/
namespace ErdosProblems.Erdos1049.PaperR13
open Finset
open scoped BigOperators

section CommRing
variable {R : Type*} [CommRing R]

/-- Finite interchange with two genuinely independent variables. -/
theorem two_variable_qPochhammer_transform (q z y : R) (a v : ℕ) :
    (∑ h ∈ range (v + 1),
      qBinomialTerm q z v h * qPochhammer q (y * q ^ h) a) =
    ∑ j ∈ range (a + 1),
      qBinomialTerm q y a j * qPochhammer q (z * q ^ j) v := by
  simp_rw [qPochhammer_eq_sum, mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro h hh
  have hex : (q ^ h) ^ j = (q ^ j) ^ h := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [qBinomialTerm, mul_pow, hex]
  ring

/-- A block of consecutive powers containing ell has an actual zero factor. -/
theorem qPochhammer_root_window (q : R) {ell b v : ℕ}
    (hq : q ^ ell = 1) (hb : b ≤ ell) (hv : ell < b + v) :
    qPochhammer q (q ^ b) v = 0 := by
  apply qPochhammer_eq_zero_of_exists q (q ^ b) (i := ell - b)
  · omega
  · rw [← pow_add, Nat.add_sub_of_le hb, hq]

/-- The residue-window hypotheses force every transformed term to vanish.
No assertion of primitiveness, Gaussian cancellation or source identity is
needed at this finite stage. -/
theorem two_variable_root_window_sum_zero (q y : R) {ell a r v : ℕ}
    (hq : q ^ ell = 1) (har : r + a < ell) (hrv : ell ≤ r + v) :
    (∑ h ∈ range (v + 1),
      qBinomialTerm q (q ^ (r + 1)) v h * qPochhammer q (y * q ^ h) a) = 0 := by
  rw [two_variable_qPochhammer_transform]
  apply sum_eq_zero
  intro j hj
  have hj' : j ≤ a := by have := mem_range.mp hj; omega
  have hz : qPochhammer q (q ^ (r + 1) * q ^ j) v = 0 := by
    rw [← pow_add]
    exact qPochhammer_root_window q hq (by omega) (by omega)
  rw [hz, mul_zero]

end CommRing

section Field
variable {K : Type*} [Field K]

/-- The Gaussian factorial identity at every upper argument, including the
zero range. The right-hand starting exponent is an integer, not Nat.sub. -/
theorem gaussian_mul_qPochhammer_integer_start (q : K) (hq : q ≠ 0)
    (w a h : ℕ) :
    gaussBinom q (w + h) a * qPochhammer q q a =
      qPochhammer q (q ^ ((w : ℤ) - a + 1) * q ^ h) a := by
  by_cases ha : a ≤ w + h
  · have he : ((w : ℤ) - a + 1) + (h : ℤ) =
        ((w + h - a + 1 : ℕ) : ℤ) := by omega
    have hp : q ^ ((w : ℤ) - a + 1) * q ^ h = q ^ (w + h - a + 1) := by
      rw [← zpow_natCast q h, ← zpow_add₀ hq, he, zpow_natCast]
    rw [hp]
    exact gaussBinom_mul_qPochhammer q ha
  · have halt : w + h < a := by omega
    rw [gaussBinom_eq_zero_of_lt q halt, zero_mul]
    symm
    apply qPochhammer_eq_zero_of_exists q _ (i := a - (w + h) - 1)
    · omega
    · have he : ((w : ℤ) - a + 1) + (h : ℤ) +
          ((a - (w + h) - 1 : ℕ) : ℤ) = 0 := by omega
      rw [← zpow_natCast q h, ← zpow_natCast q (a - (w + h) - 1),
        ← zpow_add₀ hq, ← zpow_add₀ hq, he, zpow_zero]

/-- All factors of (q;q)_a are nonzero below the primitive-root order. -/
theorem qPochhammer_nonzero_below_order (q : K) {ell : ℕ}
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1) :
    ∀ a : ℕ, a < ell → qPochhammer q q a ≠ 0 := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
      intro ha
      rw [qPochhammer_succ]
      apply mul_ne_zero (ih (by omega))
      rw [← pow_succ']
      exact sub_ne_zero.mpr (hprimitive (a + 1) (by omega) ha).symm

/-- Literal local Gaussian sum used in the second Omega carry case. -/
def rootLocalGaussianSum (q : K) (w a r v : ℕ) : K :=
  ∑ h ∈ range (v + 1),
    (-1 : K) ^ h * q ^ (h.choose 2 + (r + 1) * h) *
      gaussBinom q v h * gaussBinom q (w + h) a

/-- Division-free local identity; meaningful even when (q;q)_a vanishes. -/
theorem rootLocalGaussianSum_cleared (q : K) (hq : q ≠ 0) (w a r v : ℕ) :
    rootLocalGaussianSum q w a r v * qPochhammer q q a =
      ∑ j ∈ range (a + 1),
        qBinomialTerm q (q ^ ((w : ℤ) - a + 1)) a j *
          qPochhammer q (q ^ (r + 1) * q ^ j) v := by
  rw [← two_variable_qPochhammer_transform]
  unfold rootLocalGaussianSum
  rw [sum_mul]
  apply sum_congr rfl
  intro h hh
  have he : (-1 : K) ^ h * q ^ (h.choose 2 + (r + 1) * h) *
        gaussBinom q v h * gaussBinom q (w + h) a * qPochhammer q q a =
      qBinomialTerm q (q ^ (r + 1)) v h *
        (gaussBinom q (w + h) a * qPochhammer q q a) := by
    simp only [qBinomialTerm, pow_add, pow_mul]
    ring
  rw [he, gaussian_mul_qPochhammer_integer_start q hq]

/-- Local cancellation derived from its displayed factors, not postulated. -/
theorem rootLocalGaussianSum_eq_zero (q : K) (hq : q ≠ 0) {ell w a r v : ℕ}
    (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (har : r + a < ell) (hrv : ell ≤ r + v) :
    rootLocalGaussianSum q w a r v = 0 := by
  have hp : qPochhammer q q a ≠ 0 :=
    qPochhammer_nonzero_below_order q hprimitive a (by omega)
  apply (mul_eq_zero.mp (show rootLocalGaussianSum q w a r v *
      qPochhammer q q a = 0 from ?_)).resolve_right hp
  rw [rootLocalGaussianSum_cleared q hq]
  apply sum_eq_zero
  intro j hj
  have hj' : j ≤ a := by have := mem_range.mp hj; omega
  have hz : qPochhammer q (q ^ (r + 1) * q ^ j) v = 0 := by
    rw [← pow_add]
    exact qPochhammer_root_window q hroot (by omega) (by omega)
  rw [hz, mul_zero]

/-- The commonly used residue relation a+r=v implies the root-window bound. -/
theorem rootLocalGaussianSum_eq_zero_of_residues (q : K) (hq : q ≠ 0)
    {ell w a r v : ℕ} (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hv : v < ell) (harv : a + r = v) (hrv : ell ≤ r + v) :
    rootLocalGaussianSum q w a r v = 0 :=
  rootLocalGaussianSum_eq_zero q hq hroot hprimitive (by omega) hrv

end Field
end ErdosProblems.Erdos1049.PaperR13
