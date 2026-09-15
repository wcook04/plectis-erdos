import ErdosProblems.Erdos1049.SourceHomogeneousR12
import Mathlib

/-!
# The actual B monomial cancellation



The late j-channel is treated by a homogeneous finite identity in Z[X].
No endpoint divisibility, Laurent membership, source package, or initial-order
assertion is assumed. This removes X^M from the actual integral numerator D*B.
The additional cyclotomic Omega cancellation is a different theorem and is
not asserted in this file.
-/
namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open PaperR11
open scoped BigOperators

noncomputable def sourceShiftedASum (n j : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1), sourceShiftedASummand n s j

lemma X_power_dvd_signed_summand (m e : ℕ) (c : ℤ) (p : ℤ[X]) (he : m ≤ e) :
    (X : ℤ[X]) ^ m ∣ C c * X ^ e * p := by
  obtain ⟨v, hv⟩ := X_power_dvd_of_le m e he
  refine ⟨C c * v * p, ?_⟩
  rw [hv]
  ring

lemma sourceShiftedASummand_early_dvd (n s j : ℕ) (hj : j ≤ n) :
    (X : ℤ[X]) ^ sourceM n ∣ sourceShiftedASummand n s j := by
  have hmul := Nat.mul_le_mul_right (2 * n + s) hj
  have hexp : j * (2 * n + s) ≤ sourceAExponent n s := by
    unfold sourceAExponent
    nlinarith [Nat.zero_le (s.choose 2)]
  unfold sourceShiftedASummand
  apply X_power_dvd_signed_summand
  omega

/-- The exponent used to homogenise all the negative-shift channels. -/
def sourceHomogeneousBase (n j u : ℕ) : ℕ :=
  sourceM n + 2 * n ^ 2 - (2 * n * j + 13 * n * u)

def sourceHomogeneousOrder (n u : ℕ) : ℕ :=
  13 * n * u + (u + 1) * (2 * n + 1) + (u + 1).choose 2

lemma sourceHomogeneousBase_add (n j u : ℕ) (hj : j ≤ 14 * n) (hu : u < 13 * n) :
    sourceHomogeneousBase n j u + (2 * n * j + 13 * n * u) = sourceM n + 2 * n ^ 2 := by
  unfold sourceHomogeneousBase
  apply Nat.sub_add_cancel
  have hjmul := Nat.mul_le_mul_left (2 * n) hj
  have humul := Nat.mul_le_mul_left (13 * n) hu.le
  unfold sourceM
  nlinarith

/-- Exact exponent matching: every natural subtraction is accompanied by its
bound, and no negative exponent is silently truncated. -/
lemma source_shift_homogeneous_exponent (n s j u : ℕ)
    (hs : s ≤ 13 * n) (hj : j ≤ 14 * n) (hu : u < 13 * n) (hju : j = n + u + 1) :
    sourceM n + sourceAExponent n s - j * (2 * n + s) =
      sourceHomogeneousBase n j u + s.choose 2 + u * (13 * n - s) := by
  have hb := sourceHomogeneousBase_add n j u hj hu
  have hsub : 13 * n - s + s = 13 * n := by omega
  have hsubmul : u * (13 * n - s) + u * s = 13 * n * u := by
    calc
      _ = u * (13 * n - s + s) := by ring
      _ = _ := by rw [hsub]; ring
  have hprod : j * (2 * n + s) = (n + u + 1) * (2 * n + s) := by rw [hju]
  have hexact : sourceHomogeneousBase n j u + s.choose 2 + u * (13 * n - s) +
      j * (2 * n + s) = sourceM n + sourceAExponent n s := by
    unfold sourceAExponent
    nlinarith
  omega

/-- The homogeneous transform is identified with the actual shifted residue
sum; Gaussian symmetry is proved from the original recurrence. -/
theorem sourceShiftedASum_homogeneous (n j u : ℕ) (hj : j ≤ 14 * n)
    (hu : u < 13 * n) (hju : j = n + u + 1) :
    sourceShiftedASum n j = (X : ℤ[X]) ^ sourceHomogeneousBase n j u *
      homogeneousSourceInner X (X ^ u) (12 * n + 1) (2 * n) (13 * n + 1) := by
  unfold sourceShiftedASum homogeneousSourceInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ 13 * n := by have hh := Finset.mem_range.mp hs; omega
  have he := source_shift_homogeneous_exponent n s j u hs' hj hu hju
  have hg : gaussBinom (X : ℤ[X]) (13 * n) (13 * n - s) =
      gaussBinom X (13 * n) s := (gaussian_polynomial_symmetry (13 * n) s hs').symm
  have hi1 : 13 * n + 1 - 1 = 13 * n := by omega
  have hi2 : 12 * n + 1 - 1 = 12 * n := by omega
  have hi3 : 12 * n + 1 + 2 * n + s - 1 = 14 * n + s := by omega
  have hsign : (C ((-1 : ℤ) ^ s) : ℤ[X]) = (-1 : ℤ[X]) ^ s := by simp
  unfold sourceShiftedASummand sourceGaussianProduct
  rw [he, hg, hi1, hi2, hi3, hsign]
  simp only [pow_add, pow_mul]
  ring

/-- The first potentially surviving transformed index is u+1. Its power
provides a common divisor even when every index vanishes. -/
theorem homogeneous_source_inner_dvd (n u : ℕ) (hu : u < 13 * n) :
    (X : ℤ[X]) ^ sourceHomogeneousOrder n u ∣
      homogeneousSourceInner X (X ^ u) (12 * n + 1) (2 * n) (13 * n + 1) := by
  apply X_power_dvd_cancel_constant_one
    (qPochhammer (X : ℤ[X]) X (12 * n)) _ (sourceHomogeneousOrder n u)
  · exact qPochhammer_X_constantCoeff (12 * n)
  · have ht := homogeneous_source_transform_polynomial u
      (a := 12 * n + 1) (d := 2 * n) (v := 13 * n + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at ht
    rw [ht]
    apply Finset.dvd_sum
    intro h hh
    by_cases hhu : h ≤ u
    · rw [homogeneousPochhammer_zero u h (13 * n) hu hhu, mul_zero]
      exact dvd_zero _
    · have huh : u < h := by omega
      rw [homogeneousPochhammer_factor u h (13 * n) huh]
      have hc := Nat.choose_le_choose 2 (show u + 1 ≤ h by omega)
      have hm := Nat.mul_le_mul_right (2 * n + 1) (show u + 1 ≤ h by omega)
      have he : sourceHomogeneousOrder n u ≤
          (h * (2 * n + 1) + h.choose 2) + u * (13 * n) := by
        unfold sourceHomogeneousOrder
        nlinarith
      have hid : (-1 : ℤ[X]) ^ h * X ^ (h * (2 * n + 1) + h.choose 2) *
          gaussBinom X (12 * n) h *
            (X ^ (u * (13 * n)) * ∏ i ∈ Finset.range (13 * n),
              (1 - X ^ (h + i - u))) =
          X ^ ((h * (2 * n + 1) + h.choose 2) + u * (13 * n)) *
            ((-1 : ℤ[X]) ^ h * gaussBinom X (12 * n) h *
              ∏ i ∈ Finset.range (13 * n), (1 - X ^ (h + i - u))) := by
        rw [pow_add]
        ring
      rw [hid]
      exact dvd_mul_of_dvd_left (X_power_dvd_of_le _ _ he) _

lemma sourceHomogeneousBase_order (n j u : ℕ) (hj : j ≤ 14 * n)
    (hu : u < 13 * n) (hju : j = n + u + 1) :
    sourceHomogeneousBase n j u + sourceHomogeneousOrder n u =
      sourceM n + (u + 1) + (u + 1).choose 2 := by
  have hb := sourceHomogeneousBase_add n j u hj hu
  have hjmul : 2 * n * j = 2 * n * (n + u + 1) := by rw [hju]
  unfold sourceHomogeneousOrder
  nlinarith

/-- All actual j-channels, with the early and negative-shift regimes both
covered. n=0 is vacuous; no separate numerical base cases are needed. -/
theorem actual_shifted_A_sum_monomial_dvd (n j : ℕ) (hj : j ≤ 14 * n) :
    (X : ℤ[X]) ^ sourceM n ∣ sourceShiftedASum n j := by
  by_cases hearly : j ≤ n
  · unfold sourceShiftedASum
    exact Finset.dvd_sum (fun s _ => sourceShiftedASummand_early_dvd n s j hearly)
  · let u := j - n - 1
    have hu : u < 13 * n := by dsimp [u]; omega
    have hju : j = n + u + 1 := by dsimp [u]; omega
    obtain ⟨v, hv⟩ := homogeneous_source_inner_dvd n u hu
    rw [sourceShiftedASum_homogeneous n j u hj hu hju, hv, ← mul_assoc, ← pow_add]
    have he : sourceM n ≤ sourceHomogeneousBase n j u + sourceHomogeneousOrder n u := by
      rw [sourceHomogeneousBase_order n j u hj hu hju]
      omega
    exact dvd_mul_of_dvd_left (X_power_dvd_of_le _ _ he) v

/-- A finite reordering exposes the cancellations before multiplication by the
common denominator quotient, rather than claiming each late residue works. -/
lemma sourceClearedB_reordered (n : ℕ) :
    sourceClearedB n =
      (∑ s ∈ Finset.range (13 * n + 1), ∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l) +
      ∑ j ∈ Finset.Icc 1 (14 * n), sourceShiftedASum n j * sourceDQuotient n j := by
  unfold sourceClearedB
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [sourceShiftedASum, Finset.sum_mul]

/-- The universal monomial divisibility of the actual D-cleared B. -/
theorem actual_B_monomial_divisibility (n : ℕ) :
    (X : ℤ[X]) ^ sourceM n ∣ sourceClearedB n := by
  rw [sourceClearedB_reordered]
  apply dvd_add
  · apply Finset.dvd_sum
    intro s hs
    apply Finset.dvd_sum
    intro l hl
    refine ⟨sourceNormalisedASummand n s * sourceDQuotient n l, ?_⟩
    rw [sourceASummand_factor, mul_assoc]
  · apply Finset.dvd_sum
    intro j hj
    exact dvd_mul_of_dvd_left
      (actual_shifted_A_sum_monomial_dvd n j (Finset.mem_Icc.mp hj).2) _

/-- Canonical polynomial quotient, not an unspecified chosen witness. -/
noncomputable def sourceBWithoutMonomial (n : ℕ) : ℤ[X] :=
  sourceClearedB n /ₘ ((X : ℤ[X]) ^ sourceM n)

theorem actual_B_monomial_factor (n : ℕ) :
    sourceClearedB n = (X : ℤ[X]) ^ sourceM n * sourceBWithoutMonomial n := by
  have hrem := (modByMonic_eq_zero_iff_dvd (monic_X_pow (sourceM n))).2
    (actual_B_monomial_divisibility n)
  have h := modByMonic_add_div (sourceClearedB n) ((X : ℤ[X]) ^ sourceM n)
  simpa only [hrem, zero_add, sourceBWithoutMonomial] using h.symm

/-- Full X^M clearing of the literal rational B. The Omega factor is not
included: that later cyclotomic cancellation remains a distinct supplier. -/
theorem actual_B_monomial_clearing_rational (n : ℕ) :
    algebraMap ℤ[X] (RatFunc ℤ) (sourceD n) * sourceBRational n =
      (algebraMap ℤ[X] (RatFunc ℤ) X) ^ sourceM n *
        algebraMap ℤ[X] (RatFunc ℤ) (sourceBWithoutMonomial n) := by
  rw [← actual_B_first_clearing_rational, actual_B_monomial_factor, map_mul, map_pow]

end ErdosProblems.Erdos1049.PaperR12
