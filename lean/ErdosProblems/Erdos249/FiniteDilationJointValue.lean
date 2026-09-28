import ErdosProblems.Erdos249.FiniteDilationPulseCore
import ErdosProblems.Erdos249.FiniteDilationSeriesTransport
import ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

/-!
# Joint irrationality for a finite family of commensurate bases

This private module composes the finite-dilation CRT pulse, finite-series
transport, and the public integer-radix pulse consumer.  The statement is a
finite-combination theorem; the countable rational-independence corollary
requires only the usual reduction of a relation to finite support.
-/

namespace ErdosProblems.Erdos249.FiniteDilationJointValue

open ErdosProblems.Erdos249.FiniteDilationPulseCore
open ErdosProblems.Erdos249.FiniteDilationSeriesTransport
open ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables

/-- A nonzero observable at the least surviving dilation and a prime-accessible
residue makes the finite linear combination of base-power series irrational. -/
theorem irrational_finset_dilated_totient_values
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (m B δ r H : ℕ)
    (hm : 0 < m) (hB : 2 ≤ B)
    (hδD : δ ∈ D) (hδ : 0 < δ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hH : ∀ d ∈ D, d ≤ H)
    (hrlt : r < m) (hr : Nat.Coprime (r + 1) m)
    (hzero : ∀ d ∈ D, g d 0 = 0)
    (hgr : g δ r ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ d ∈ D, ∀ s < m, |(g d s : ℝ)| ≤ C) :
    Irrational (∑ d ∈ D, ∑' n : ℕ,
      (g d (Nat.totient n % m) : ℝ) / ((B : ℝ) ^ d) ^ n) := by
  let a := mixedCoefficient D g m
  have hpulse : ∀ L : ℕ, ∃ N : ℕ, L + 1 < N ∧ a N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (N - j) = 0 ∧ a (N + j) = 0 :=
    mixedCoefficient_has_pulses D g m δ r H hm hδD hδ hpos hmin hH
      hrlt hr hzero hgr
  have hbound : ∀ N : ℕ, |(a N : ℝ)| ≤ ∑ _d ∈ D, C :=
    mixedCoefficient_bounded D g m hm C hC hg
  have hradix : Irrational (radixValue B a) :=
    irrational_radixValue_of_pulses B hB a (∑ _d ∈ D, C) hbound hpulse
  have hseries : radixValue B a =
      ∑ d ∈ D, ∑' n : ℕ,
        (g d (Nat.totient n % m) : ℝ) / ((B : ℝ) ^ d) ^ n := by
    simpa only [radixValue, a, mixedCoefficient] using
      integer_mixed_radixValue_eq_finset_values D g m B hm hB hpos C hC hg
  rw [← hseries]
  exact hradix

/-- At a dyadic modulus every even residue is accessible from a prime centre.
This is the nonconstant branch needed for the full joint observable
classification after rational observables are centred and cleared. -/
theorem irrational_finset_dyadic_observable_values
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (k B δ r H : ℕ)
    (hk : 0 < k) (hB : 2 ≤ B)
    (hδD : δ ∈ D) (hδ : 0 < δ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hH : ∀ d ∈ D, d ≤ H)
    (hrlt : r < 2 ^ k) (hre : Even r)
    (hzero : ∀ d ∈ D, g d 0 = 0)
    (hgr : g δ r ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ d ∈ D, ∀ s < 2 ^ k, |(g d s : ℝ)| ≤ C) :
    Irrational (∑ d ∈ D, ∑' n : ℕ,
      (g d (Nat.totient n % (2 ^ k)) : ℝ) / ((B : ℝ) ^ d) ^ n) := by
  have hodd : Odd (r + 1) := by
    obtain ⟨t, ht⟩ := hre
    refine ⟨t, ?_⟩
    omega
  have hcop : Nat.Coprime (r + 1) (2 ^ k) :=
    (Nat.coprime_pow_right_iff hk (r + 1) 2).mpr
      (Nat.coprime_two_right.mpr hodd)
  exact irrational_finset_dilated_totient_values D g (2 ^ k) B δ r H
    (pow_pos (by decide) _) hB hδD hδ hpos hmin hH hrlt hcop
    hzero hgr C hC hg

/-- Positive-index version of the dyadic nonconstant branch. -/
theorem irrational_finset_dyadic_positive_values
    (D : Finset ℕ) (g : ℕ → ℕ → ℤ) (k B δ r H : ℕ)
    (hk : 0 < k) (hB : 2 ≤ B)
    (hδD : δ ∈ D) (hδ : 0 < δ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hH : ∀ d ∈ D, d ≤ H)
    (hrlt : r < 2 ^ k) (hre : Even r)
    (hzero : ∀ d ∈ D, g d 0 = 0)
    (hgr : g δ r ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ d ∈ D, ∀ s < 2 ^ k, |(g d s : ℝ)| ≤ C) :
    Irrational (∑ d ∈ D, ∑' n : ℕ,
      (g d (Nat.totient (n + 1) % (2 ^ k)) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) := by
  have hI := irrational_finset_dyadic_observable_values
    D g k B δ r H hk hB hδD hδ hpos hmin hH hrlt hre
    hzero hgr C hC hg
  have hseries :
      (∑ d ∈ D, ∑' n : ℕ,
        (g d (Nat.totient n % (2 ^ k)) : ℝ) / ((B : ℝ) ^ d) ^ n) =
      (∑ d ∈ D, ∑' n : ℕ,
        (g d (Nat.totient (n + 1) % (2 ^ k)) : ℝ) /
          ((B : ℝ) ^ d) ^ (n + 1)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := hpos d hd
    have hBd : 2 ≤ B ^ d := by
      calc
        2 ≤ B := hB
        _ = B ^ 1 := by simp
        _ ≤ B ^ d := pow_le_pow_right₀ (by omega : 1 ≤ B) hd1
    simpa only [Nat.cast_pow] using
      (tsum_totient_observable_eq_positive (g d) (2 ^ k) (B ^ d)
        (pow_pos (by decide) _) hBd (hzero d hd) C
        (fun s hs => hg d hd s hs))
  rw [← hseries]
  exact hI

/-- Every finite nonzero integer combination of least-residue totient series
at distinct positive powers of one base is irrational.  The least active
dilation is supplied explicitly by `δ`; any finite nonzero relation has one. -/
theorem irrational_finset_least_residue_values
    (D : Finset ℕ) (c : ℕ → ℤ) (m B δ H : ℕ)
    (hm : 3 ≤ m) (hB : 2 ≤ B)
    (hδD : δ ∈ D) (hδ : 0 < δ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hH : ∀ d ∈ D, d ≤ H)
    (hcδ : c δ ≠ 0) :
    Irrational (∑ d ∈ D, ∑' n : ℕ,
      ((c d * (Nat.totient n % m : ℤ) : ℤ) : ℝ) /
        ((B : ℝ) ^ d) ^ n) := by
  let g : ℕ → ℕ → ℤ := fun d s => c d * s
  let C : ℝ := ∑ d ∈ D, |(c d : ℝ)| * (m : ℝ)
  have hC : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hg : ∀ d ∈ D, ∀ s < m, |(g d s : ℝ)| ≤ C := by
    intro d hd s hs
    have hsingle : |(c d : ℝ)| * (m : ℝ) ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum (s := D) (a := d)
        (f := fun e : ℕ => |(c e : ℝ)| * (m : ℝ))
        (by intro e he; exact mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) hd
    have hsreal : (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs.le
    calc
      |(g d s : ℝ)| = |(c d : ℝ)| * (s : ℝ) := by simp [g, abs_mul]
      _ ≤ |(c d : ℝ)| * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hsreal (abs_nonneg _)
      _ ≤ C := hsingle
  have hr : Nat.Coprime ((m - 2) + 1) m := by
    have hcop : Nat.Coprime (m - 1) m :=
      (Nat.coprime_self_sub_left (by omega : 1 ≤ m)).mpr
        (Nat.coprime_one_left m)
    convert hcop using 1
    omega
  have hgr : g δ (m - 2) ≠ 0 := by
    change c δ * (m - 2 : ℕ) ≠ 0
    exact mul_ne_zero hcδ (by exact_mod_cast (by omega : m - 2 ≠ 0))
  simpa only [g] using
    (irrational_finset_dilated_totient_values D g m B δ (m - 2) H
      (by omega) hB hδD hδ hpos hmin hH (by omega) hr
      (by intro d hd; simp [g]) hgr C hC hg)

/-- The positive-index formulation of the finite joint least-residue theorem.
This is the series appearing in the ordinary countable independence claim. -/
theorem irrational_finset_least_residue_positive_values
    (D : Finset ℕ) (c : ℕ → ℤ) (m B δ H : ℕ)
    (hm : 3 ≤ m) (hB : 2 ≤ B)
    (hδD : δ ∈ D) (hδ : 0 < δ)
    (hpos : ∀ d ∈ D, 0 < d)
    (hmin : ∀ d ∈ D, δ ≤ d)
    (hH : ∀ d ∈ D, d ≤ H)
    (hcδ : c δ ≠ 0) :
    Irrational (∑ d ∈ D, ∑' n : ℕ,
      ((c d * (Nat.totient (n + 1) % m : ℤ) : ℤ) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) := by
  have hI := irrational_finset_least_residue_values
    D c m B δ H hm hB hδD hδ hpos hmin hH hcδ
  have hseries :
      (∑ d ∈ D, ∑' n : ℕ,
        ((c d * (Nat.totient n % m : ℤ) : ℤ) : ℝ) /
          ((B : ℝ) ^ d) ^ n) =
      (∑ d ∈ D, ∑' n : ℕ,
        ((c d * (Nat.totient (n + 1) % m : ℤ) : ℤ) : ℝ) /
          ((B : ℝ) ^ d) ^ (n + 1)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := hpos d hd
    have hBd : 2 ≤ B ^ d := by
      calc
        2 ≤ B := hB
        _ = B ^ 1 := by simp
        _ ≤ B ^ d := pow_le_pow_right₀ (by omega : 1 ≤ B) hd1
    let gd : ℕ → ℤ := fun s => c d * s
    have hgd : ∀ s < m,
        |(gd s : ℝ)| ≤ |(c d : ℝ)| * (m : ℝ) := by
      intro s hs
      have hsreal : (s : ℝ) ≤ (m : ℝ) := by exact_mod_cast hs.le
      calc
        |(gd s : ℝ)| = |(c d : ℝ)| * (s : ℝ) := by simp [gd, abs_mul]
        _ ≤ |(c d : ℝ)| * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hsreal (abs_nonneg _)
    simpa only [gd, Nat.cast_pow] using
      (tsum_totient_observable_eq_positive gd m (B ^ d)
        (by omega) hBd (by simp [gd])
        (|(c d : ℝ)| * (m : ℝ)) hgd)
  rw [← hseries]
  exact hI

#print axioms irrational_finset_dilated_totient_values
#print axioms irrational_finset_dyadic_observable_values
#print axioms irrational_finset_dyadic_positive_values
#print axioms irrational_finset_least_residue_values
#print axioms irrational_finset_least_residue_positive_values

end ErdosProblems.Erdos249.FiniteDilationJointValue
