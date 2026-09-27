-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import ErdosProblems.ArgumentGraph.Derived.Erdos243

/-!
# Erdős #243: what the transport-square factoring adds

`transport_square_unconditional` (`long243:res:transportsquare`) assumes `v n > 0` for
`n ≥ T` and passes it to `primitive_zero_density_multiplier_irreducibility` only for claims
it does not use, so `transport_square_unconditional.factored` leaves it out. The theorem
below shows that the hypotheses the factoring keeps imply it: from a zero term on, `v`
vanishes (`v (n + 1) = a n * v n`), coprimality then gives `u n = 1`, and
`m * C(n + 2, 3) + c` exceeds `1` for large `n`, so the exceptional set contains a tail,
which zero lower density forbids. The factored theorem is the same result, on the same
premise region, with a shorter statement.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11

theorem le_choose_add_two_three (n : ℕ) (hn : 1 ≤ n) : n ≤ (n + 2).choose 3 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have h : (n + 2 + 1).choose 3 = (n + 2).choose 2 + (n + 2).choose 3 :=
      Nat.choose_succ_succ' (n + 2) 2
    have hpos : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
    have e1 : n + 1 + 2 = n + 2 + 1 := by omega
    rw [e1]
    omega

/-- A set containing every `n ≥ K` does not have zero lower density. -/
theorem not_zeroLowerDensity_of_tail (E : Set ℕ) (K : ℕ) (htail : ∀ n, K ≤ n → n ∈ E) :
    ¬ ZeroLowerDensity E := by
  intro hzero
  obtain ⟨X, hX, hlt⟩ := hzero (1 / 2) (by norm_num) (2 * K)
  have hcount := disjoint_periodic_count E K 1 1 le_rfl
    (fun k => ⟨0, by norm_num, htail _ (by omega)⟩) (X - K)
  have hXeq : K + 1 * (X - K) = X := by omega
  rw [hXeq] at hcount
  have hc : ((X - K : ℕ) : ℝ) ≤ (exceptionCount E X : ℝ) := by exact_mod_cast hcount
  have hsub : ((X - K : ℕ) : ℝ) = (X : ℝ) - K := by rw [Nat.cast_sub (by omega)]
  have h2 : (2 * K : ℝ) ≤ X := by exact_mod_cast hX
  linarith

/-- The hypotheses `transport_square_unconditional.factored` keeps imply the positivity
hypothesis it leaves out. -/
theorem transport_square_positivity_of_rest
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c}) :
    ∀ n, T ≤ n → 0 < v n := by
  intro k hk
  by_contra hv
  have hvk : v k = 0 := by omega
  have hvan : ∀ n, k ≤ n → v n = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hvk
    | succ n hn ih => rw [hden n (by omega), ih, mul_zero]
  have hu1 : ∀ n, k ≤ n → u n = 1 := by
    intro n hn
    have h := hcop n (by omega)
    rw [hvan n hn] at h
    exact Nat.coprime_zero_right _ |>.mp h
  have hgrow : ∀ n, c.natAbs + 2 ≤ n → (m : ℤ) * risingBinomial n + c ≠ 1 := by
    intro n hn heq
    have h1 : (n : ℤ) ≤ ((n + 2).choose 3 : ℤ) := by
      exact_mod_cast le_choose_add_two_three n (by omega)
    have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hn' : (c.natAbs : ℤ) + 2 ≤ n := by exact_mod_cast hn
    have habs : -(c.natAbs : ℤ) ≤ c := by
      rcases Int.natAbs_eq c with h | h <;> omega
    have hC0 : (0 : ℤ) ≤ ((n + 2).choose 3 : ℤ) := by positivity
    have hmb : (n : ℤ) ≤ (m : ℤ) * ((n + 2).choose 3 : ℤ) := by nlinarith
    unfold risingBinomial at heq
    linarith
  apply not_zeroLowerDensity_of_tail _ (max k (c.natAbs + 2)) _ hzero
  intro n hn
  show (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c
  rw [hu1 n (le_of_max_le_left hn)]
  push_cast
  exact fun h => hgrow n (le_of_max_le_right hn) h.symm

end ErdosProblems.Erdos243.PaperCompleteR21

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.not_zeroLowerDensity_of_tail
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.transport_square_positivity_of_rest
