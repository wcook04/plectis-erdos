import Mathlib

/-!
# Finite correction from kernel zeros

This file isolates the finite algebra behind the polynomial correction in the
Erdős 1049 coefficient-moment identity.  Once a rational kernel has a finite
partial-fraction expansion and vanishes at the first `m` powers of its base,
the long residue prefixes differ from the short source prefixes by two
explicit quotient evaluations.  The proof uses only finite reindexing and a
geometric sum; no analytic or Padé theorem is assumed.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Finset
open scoped BigOperators

/-- Reverse the final block of a range sum.  This is the index change
`n = k + r` to `n + 1 = m + k - s` used by the kernel-zero argument. -/
private theorem sum_range_tail_reflect {F : Type*} [AddCommGroup F]
    (m k : ℕ) (f : ℕ → F) :
    (∑ n ∈ range (m + k), f n) - ∑ n ∈ range k, f n =
      ∑ s ∈ range m, f (m + k - 1 - s) := by
  rw [Nat.add_comm m k, Finset.sum_range_add]
  simp only [add_sub_cancel_left]
  rw [← Finset.sum_range_reflect (fun r => f (k + r)) m]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  have hslt : s < m := Finset.mem_range.mp hs
  omega

/-- **Kernel-zero correction lemma.**

`Q j` is the coefficient of `X^(j+1)` in the polynomial quotient and `C k`
is the `k`th simple-pole residue.  The hypothesis is exactly what remains
after evaluating the partial-fraction identity at the numerator zeros
`X = p^(s+1)` and cancelling its constant term against the sum of residues.

The conclusion converts the full residue prefixes and the quotient values at
`p` into the short source prefixes and the quotient values at `p^(m+1)`.
For the Erdős 1049 kernel, the latter quotient sum is the finite triangular
correction obtained from the generating function for `S_(m,l)`. -/
theorem kernelZero_correction_identity {F : Type*} [Field F]
    (m : ℕ) (p : F) (Q C : ℕ → F)
    (hden : ∀ j ∈ range m, p ^ (j + 1) ≠ 1)
    (hzero : ∀ s ∈ range m,
      (∑ j ∈ range m, Q j * p ^ ((s + 1) * (j + 1))) +
          ∑ k ∈ range (m + 1), C k / (p ^ (m + k - s) - 1) = 0) :
    (∑ k ∈ range (m + 1),
        ∑ n ∈ range (m + k), C k / (p ^ (n + 1) - 1)) -
        ∑ j ∈ range m, Q j * p ^ (j + 1) / (p ^ (j + 1) - 1) =
      (∑ k ∈ range (m + 1),
        ∑ n ∈ range k, C k / (p ^ (n + 1) - 1)) -
        ∑ j ∈ range m,
          Q j * p ^ ((m + 1) * (j + 1)) / (p ^ (j + 1) - 1) := by
  have hblocks :
      (∑ k ∈ range (m + 1),
          ∑ n ∈ range (m + k), C k / (p ^ (n + 1) - 1)) -
          ∑ k ∈ range (m + 1),
            ∑ n ∈ range k, C k / (p ^ (n + 1) - 1) =
        ∑ s ∈ range m,
          ∑ k ∈ range (m + 1), C k / (p ^ (m + k - s) - 1) := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ k ∈ range (m + 1),
          ∑ s ∈ range m,
            C k / (p ^ ((m + k - 1 - s) + 1) - 1) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [sum_range_tail_reflect]
      _ = ∑ k ∈ range (m + 1),
          ∑ s ∈ range m, C k / (p ^ (m + k - s) - 1) := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro s hs
        have hslt : s < m := Finset.mem_range.mp hs
        rw [show (m + k - 1 - s) + 1 = m + k - s by omega]
      _ = _ := by rw [Finset.sum_comm]
  have hzerosum :
      (∑ s ∈ range m,
          ∑ k ∈ range (m + 1), C k / (p ^ (m + k - s) - 1)) =
        -∑ j ∈ range m, Q j *
          (∑ s ∈ range m, p ^ ((s + 1) * (j + 1))) := by
    calc
      _ = ∑ s ∈ range m,
          -(∑ j ∈ range m, Q j * p ^ ((s + 1) * (j + 1))) := by
        apply Finset.sum_congr rfl
        intro s hs
        linear_combination hzero s hs
      _ = -∑ s ∈ range m,
          ∑ j ∈ range m, Q j * p ^ ((s + 1) * (j + 1)) := by
        rw [Finset.sum_neg_distrib]
      _ = -∑ j ∈ range m,
          ∑ s ∈ range m, Q j * p ^ ((s + 1) * (j + 1)) := by
        rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
  have hgeom (j : ℕ) (hj : j ∈ range m) :
      (∑ s ∈ range m, p ^ ((s + 1) * (j + 1))) =
        p ^ ((m + 1) * (j + 1)) / (p ^ (j + 1) - 1) -
          p ^ (j + 1) / (p ^ (j + 1) - 1) := by
    let x : F := p ^ (j + 1)
    have hx1 : x ≠ 1 := hden j hj
    have hpow (s : ℕ) : p ^ ((s + 1) * (j + 1)) = x ^ (s + 1) := by
      change p ^ ((s + 1) * (j + 1)) = (p ^ (j + 1)) ^ (s + 1)
      rw [← pow_mul]
      rw [Nat.mul_comm]
    calc
      _ = ∑ s ∈ range m, x ^ (s + 1) := by simp_rw [hpow]
      _ = x * ∑ s ∈ range m, x ^ s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [pow_succ]
        ring
      _ = x * ((x ^ m - 1) / (x - 1)) := by rw [geom_sum_eq hx1]
      _ = x ^ (m + 1) / (x - 1) - x / (x - 1) := by
        rw [pow_succ]
        field_simp [sub_ne_zero.mpr hx1]
      _ = _ := by
        have hp : x ^ (m + 1) = p ^ ((m + 1) * (j + 1)) := by
          calc
            x ^ (m + 1) = (p ^ (j + 1)) ^ (m + 1) := rfl
            _ = p ^ ((j + 1) * (m + 1)) := (pow_mul p (j + 1) (m + 1)).symm
            _ = p ^ ((m + 1) * (j + 1)) := by rw [Nat.mul_comm]
        rw [hp]
  have hsumgeom :
      (∑ j ∈ range m, Q j *
          (∑ s ∈ range m, p ^ ((s + 1) * (j + 1)))) =
        ∑ j ∈ range m, Q j *
          (p ^ ((m + 1) * (j + 1)) / (p ^ (j + 1) - 1) -
            p ^ (j + 1) / (p ^ (j + 1) - 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hgeom j hj]
  calc
    (∑ k ∈ range (m + 1),
        ∑ n ∈ range (m + k), C k / (p ^ (n + 1) - 1)) -
        ∑ j ∈ range m, Q j * p ^ (j + 1) / (p ^ (j + 1) - 1) =
      (∑ k ∈ range (m + 1),
        ∑ n ∈ range k, C k / (p ^ (n + 1) - 1)) +
        ((∑ k ∈ range (m + 1),
          ∑ n ∈ range (m + k), C k / (p ^ (n + 1) - 1)) -
          ∑ k ∈ range (m + 1),
            ∑ n ∈ range k, C k / (p ^ (n + 1) - 1)) -
        ∑ j ∈ range m, Q j * p ^ (j + 1) / (p ^ (j + 1) - 1) := by
      ring
    _ = (∑ k ∈ range (m + 1),
        ∑ n ∈ range k, C k / (p ^ (n + 1) - 1)) -
        (∑ j ∈ range m, Q j *
          (∑ s ∈ range m, p ^ ((s + 1) * (j + 1)))) -
        ∑ j ∈ range m, Q j * p ^ (j + 1) / (p ^ (j + 1) - 1) := by
      rw [hblocks, hzerosum]
      ring
    _ = _ := by
      rw [hsumgeom]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring

#print axioms kernelZero_correction_identity

end ErdosProblems.Erdos1049.PaperR20
