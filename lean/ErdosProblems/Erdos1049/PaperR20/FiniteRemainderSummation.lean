import ErdosProblems.Erdos1049.PaperR16.LambertBasic
import ErdosProblems.Erdos1049.ActualMomentGeneratingR12
import Mathlib

/-!
# Summing a finite rational-kernel remainder certificate

The theorems here consume a literal, pointwise finite certificate.  They do
not assert that the certificate exists: later polynomial computations supply
its coefficients in the finite range where they have been checked.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Finset
open scoped BigOperators

noncomputable section

/-- The first `s` positive-index terms of the real Lambert series. -/
def finiteLambertPrefix (q : ℝ) (s : ℕ) : ℝ :=
  ∑ n ∈ range s, q ^ (n + 1) / (1 - q ^ (n + 1))

/-- Removing the first `r-1` positive Lambert terms leaves the tail starting
at exponent `r`. -/
theorem tsum_lambert_tail {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℕ) (hr : 1 ≤ r) :
    (∑' t : ℕ, q ^ (t + r) / (1 - q ^ (t + r))) =
      PaperR16.lambert q - finiteLambertPrefix q (r - 1) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hs := PaperR16.lambert_hasSum_positive q hnorm
  have hsplit := hs.summable.sum_add_tsum_nat_add (r - 1)
  have hshift :
      (fun t : ℕ => q ^ (t + (r - 1) + 1) / (1 - q ^ (t + (r - 1) + 1))) =
        (fun t : ℕ => q ^ (t + r) / (1 - q ^ (t + r))) := by
    funext t
    have ht : t + (r - 1) + 1 = t + r := by omega
    rw [ht]
  rw [hshift] at hsplit
  rw [hs.tsum_eq] at hsplit
  change finiteLambertPrefix q (r - 1) +
      (∑' t : ℕ, q ^ (t + r) / (1 - q ^ (t + r))) =
        PaperR16.lambert q at hsplit
  linarith

/-- The tail identity packaged as a `HasSum`, for finite linear combinations. -/
theorem hasSum_lambert_tail {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℕ) (hr : 1 ≤ r) :
    HasSum (fun t : ℕ => q ^ (t + r) / (1 - q ^ (t + r)))
      (PaperR16.lambert q - finiteLambertPrefix q (r - 1)) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hs := (PaperR16.lambert_hasSum_positive q hnorm).summable
  have htail : Summable
      (fun t : ℕ => q ^ (t + r) / (1 - q ^ (t + r))) := by
    have h := (summable_nat_add_iff (r - 1)).2 hs
    convert h using 1
    funext t
    have ht : t + (r - 1) + 1 = t + r := by omega
    rw [ht]
  rw [← tsum_lambert_tail hq0 hq1 r hr]
  exact htail.hasSum

/-- The literal finite rational kernel occurring in a certificate for the
`m`-th actual moment summand. -/
def finiteRationalKernel (q : ℝ) (m : ℕ)
    (A : Fin m → ℝ) (C : Fin (m + 1) → ℝ) (t : ℕ) : ℝ :=
  (∑ j, A j * q ^ ((j.val + 1) * t)) +
    ∑ k, C k * q ^ (m + 1 + k.val + t) /
      (1 - q ^ (m + 1 + k.val + t))

/-- A finite rational kernel sums to one Lambert coefficient, finitely many
geometric poles, and explicit finite Lambert prefixes. -/
theorem finiteRationalKernel_hasSum {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (m : ℕ) (A : Fin m → ℝ) (C : Fin (m + 1) → ℝ) :
    HasSum (finiteRationalKernel q m A C)
      ((∑ k, C k) * PaperR16.lambert q +
        ∑ j, A j / (1 - q ^ (j.val + 1)) -
        ∑ k, C k * finiteLambertPrefix q (m + k.val)) := by
  have hgeo (j : Fin m) :
      HasSum (fun t : ℕ => A j * q ^ ((j.val + 1) * t))
        (A j / (1 - q ^ (j.val + 1))) := by
    have hpow0 : 0 ≤ q ^ (j.val + 1) := pow_nonneg hq0.le _
    have hpow1 : q ^ (j.val + 1) < 1 :=
      PaperR12.positive_shift_power_lt_one hq0 hq1 _ (by omega)
    simpa only [pow_mul, div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hpow0 hpow1).mul_left (A j)
  have htail (k : Fin (m + 1)) :
      HasSum
        (fun t : ℕ => C k * q ^ (m + 1 + k.val + t) /
          (1 - q ^ (m + 1 + k.val + t)))
        (C k * (PaperR16.lambert q - finiteLambertPrefix q (m + k.val))) := by
    have hs := (hasSum_lambert_tail hq0 hq1 (m + 1 + k.val) (by omega)).mul_left (C k)
    have hprefix : m + 1 + k.val - 1 = m + k.val := by omega
    simpa [hprefix, Nat.add_comm, mul_div_assoc] using hs
  have hA := hasSum_sum (s := Finset.univ) (fun j _ => hgeo j)
  have hC := hasSum_sum (s := Finset.univ) (fun k _ => htail k)
  have h := hA.add hC
  convert h using 1
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Summation of an externally supplied literal certificate for
`PaperR12.actualMomentTerm`.  The pointwise identity is the finite certificate
input; this theorem performs only its analytic summation. -/
theorem actualMoment_eq_of_finiteRationalKernel_certificate {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ)
    (A : Fin m → ℝ) (C : Fin (m + 1) → ℝ)
    (hcertificate : ∀ t : ℕ,
      PaperR12.actualMomentTerm q m t = finiteRationalKernel q m A C t) :
    PaperR12.actualMoment q m =
      (∑ k, C k) * PaperR16.lambert q +
        ∑ j, A j / (1 - q ^ (j.val + 1)) -
        ∑ k, C k * finiteLambertPrefix q (m + k.val) := by
  have hs := finiteRationalKernel_hasSum hq0 hq1 m A C
  have hm : HasSum (PaperR12.actualMomentTerm q m)
      ((∑ k, C k) * PaperR16.lambert q +
        ∑ j, A j / (1 - q ^ (j.val + 1)) -
        ∑ k, C k * finiteLambertPrefix q (m + k.val)) :=
    hs.congr_fun hcertificate
  exact hm.tsum_eq

end

#print axioms actualMoment_eq_of_finiteRationalKernel_certificate

end ErdosProblems.Erdos1049.PaperR20
