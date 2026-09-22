import ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser
import ErdosProblems.Erdos243.PaperCompleteR11.CoprimeCores
import Mathlib.Data.Fintype.BigOperators

/-!
# Orbit-supplied gcd and product budgets

Every gcd bound and every old-divisor
statement is derived from the exact two-coordinate orbit. In particular,
no pairwise-coprimality assumption is made on the original multipliers.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open PaperCompleteR7 Filter
open scoped BigOperators Topology

/-- Positive integer powers are monotone in the exponent. -/
theorem nat_pow_mono_exponent (a : ℕ) (ha : 1 ≤ a) {n m : ℕ}
    (hnm : n ≤ m) : a ^ n ≤ a ^ m :=
  Nat.pow_le_pow_right (by omega) hnm

/-- The exact denominator of a whole block, including its initial factor. -/
theorem denominator_block_product (a D : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = a n * D n) (J B : ℕ) :
    D (J + B) = D J * ∏ i : Fin B, a (J + i) := by
  rw [Fin.prod_univ_eq_prod_range (fun i ↦ a (J + i)) B]
  induction B with
  | zero => simp
  | succ B ih =>
      rw [show J + (B + 1) = (J + B) + 1 by omega, hD, ih,
        Finset.prod_range_succ]
      ring

/-- Block products are not bounded by multiplying unrelated pointwise
majorants: they divide, and are bounded by, the actual denominator. -/
theorem multiplier_block_product_le_denominator (a D : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = a n * D n) (hDpos : ∀ n, 0 < D n)
    (J B : ℕ) : (∏ i : Fin B, a (J + i)) ≤ D (J + B) := by
  rw [denominator_block_product a D hD J B]
  exact Nat.le_mul_of_pos_left _ (hDpos J)

/-- The overlap of two distinct multipliers divides a positive, genuinely
constructed later numerator. -/
theorem multiplier_gcd_dvd_next_numerator (a U D : ℕ → ℕ)
    (hU : ∀ n, U (n + 1) + D n = a n * U n)
    (hD : ∀ n, D (n + 1) = a n * D n) {i j : ℕ} (hij : i < j) :
    Nat.gcd (a i) (a j) ∣ U (j + 1) := by
  have hd : Nat.gcd (a i) (a j) ∣ D j :=
    (Nat.gcd_dvd_left _ _).trans (base_dvd_denState_later a D hD hij)
  have hp : Nat.gcd (a i) (a j) ∣ a j * U j :=
    dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
  rw [← hU j] at hp
  exact (Nat.dvd_add_iff_left hd).mpr hp

/-- A single terminal record bounds every pairwise gcd in a growing block. -/
theorem multiplier_gcd_le_terminal_record (a U D : ℕ → ℕ)
    (hU : ∀ n, U (n + 1) + D n = a n * U n)
    (hD : ∀ n, D (n + 1) = a n * D n) (hUpos : ∀ n, 0 < U n)
    {i j M : ℕ} (hij : i ≠ j) (hi : i < M) (hj : j < M) :
    Nat.gcd (a i) (a j) ≤ runningMax U M := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (Nat.le_of_dvd (hUpos (j + 1))
      (multiplier_gcd_dvd_next_numerator a U D hU hD hlt)).trans
        (le_runningMax U (by omega))
  · rw [Nat.gcd_comm]
    exact (Nat.le_of_dvd (hUpos (i + 1))
      (multiplier_gcd_dvd_next_numerator a U D hU hD hgt)).trans
        (le_runningMax U (by omega))

/-- Every selected multiplier has become old at the terminal block index. -/
theorem multiplier_block_old (a D : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = a n * D n) (J B : ℕ)
    (i : Fin B) (n : ℕ) (hn : J + B ≤ n) : a (J + i) ∣ D n :=
  base_dvd_denState_later a D hD (by have := i.isLt; omega)

/-- A natural-base double exponential is bounded by a shifted binary tower. -/
theorem natural_base_power_le_binaryTower (A n : ℕ) :
    A ^ (2 ^ n) ≤ binaryTower (n + A) := by
  have hA : A ≤ binaryTower A := by
    have h₁ := index_succ_le_two_pow A
    have h₂ := index_succ_le_two_pow (2 ^ A)
    unfold binaryTower
    omega
  calc
    A ^ (2 ^ n) ≤ binaryTower A ^ (2 ^ n) := Nat.pow_le_pow_left hA _
    _ = binaryTower (n + A) := by
      simp only [binaryTower, ← pow_mul, pow_add]
      congr 1
      ring

/-- A uniform multiplier majorant gives the denominator the same double
exponential order. The multiplicative initial denominator is retained. -/
theorem denominator_double_exponential_envelope
    (a D : ℕ → ℕ) (A : ℕ)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (ha : ∀ n, a n ≤ A ^ (2 ^ n)) :
    ∃ L : ℕ, ∀ n, D n ≤ binaryTower (n + L) := by
  let Q := max A (D 0)
  have hbound : ∀ n, D n ≤ Q ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, pow_one] using (le_max_right A (D 0))
    | succ n ih =>
        rw [hD, doublePower_succ]
        have haQ : a n ≤ Q ^ (2 ^ n) :=
          (ha n).trans (Nat.pow_le_pow_left (le_max_left A (D 0)) _)
        have hh := Nat.mul_le_mul haQ ih
        simpa only [pow_two] using hh
  exact ⟨Q, fun n ↦ (hbound n).trans (natural_base_power_le_binaryTower Q n)⟩

/-- The canonical multiplier envelope is global; its finite prefix is not
silently discarded before a denominator product is formed. -/
theorem canonical_global_multiplier_envelope
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n, a n ≤ A ^ (2 ^ n) := by
  obtain ⟨N, A, haN, hA, hb⟩ := quadratic_double_exponential_bounds a ha hapos hgrowth
  have hApos : 1 ≤ A := by omega
  refine ⟨A, hApos, fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hlow : a (N + k) ≤ A ^ (2 ^ k) := by have := (hb k).2; omega
    exact hlow.trans (nat_pow_mono_exponent A hApos (two_pow_mono (by omega)))
  · have hprefix : a n ≤ a N := ha.monotone (by omega)
    have hpow : A ≤ A ^ (2 ^ n) := by
      have h := nat_pow_mono_exponent A hApos
        (Nat.one_le_pow n 2 (by norm_num))
      simpa only [pow_one] using h
    exact hprefix.trans ((by omega : a N ≤ A).trans hpow)

/-- No denominator-growth hypothesis is added to the canonical endpoint. -/
theorem canonical_denominator_binaryTower_bound
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (q : ℕ)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    ∃ L : ℕ, ∀ n, canonicalDenominator a q n ≤ binaryTower (n + L) := by
  obtain ⟨A, hA, haA⟩ := canonical_global_multiplier_envelope a ha hapos hgrowth
  apply denominator_double_exponential_envelope a (canonicalDenominator a q) A
  · intro n
    simp only [canonicalDenominator, prefixProduct_succ]
    ring
  · exact haA

/-- The real geometric envelope is converted to an exact natural exponent
budget, including the finite prefix. -/
theorem runningMax_binary_exponent_of_real_envelope
    (U : ℕ → ℕ) (K : ℝ)
    (hK : ∀ n, (runningMax U n : ℝ) ≤ K * (2 : ℝ) ^ n) :
    ∃ L : ℕ, ∀ n, runningMax U n ≤ 2 ^ (L + n) := by
  obtain ⟨L, hL⟩ := exists_nat_gt K
  have hLpow : L ≤ 2 ^ L := by have := index_succ_le_two_pow L; omega
  refine ⟨L, fun n ↦ ?_⟩
  have hLreal : K ≤ (2 : ℝ) ^ L := by
    have hh : (L : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hLpow
    exact hL.le.trans hh
  have h := (hK n).trans
    (mul_le_mul_of_nonneg_right hLreal (by positivity : (0 : ℝ) ≤ 2 ^ n))
  rw [← pow_add] at h
  exact_mod_cast h

/-- This integer envelope is supplied by the canonical reciprocal series. -/
theorem canonical_runningMax_binary_exponent
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    ∃ L : ℕ, ∀ n, runningMax (canonicalNaturalNumerator a p q) n ≤ 2 ^ (L + n) := by
  obtain ⟨K, hKpos, hC, hH⟩ :=
    canonical_runningMax_subexponential_envelope a ha hapos p q hq hs hgrowth 2 (by norm_num)
  exact runningMax_binary_exponent_of_real_envelope _ K hH

end ErdosProblems.Erdos243.PaperCompleteR11
