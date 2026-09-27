import ErdosProblems.Erdos257.CoverIndependentPeriodicMean
import Mathlib

/-! # Exact finite-period counts for dyadic logarithmic events

For the separating divisor frames, the event for a prime in row k is
2^(k+2)*p divides n but 2^(k+3)*p does not. Counting it by subtraction
avoids probabilistic independence assumptions or limiting density suppliers.
-/
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset

/-- Exact event count before choosing a common period. -/
theorem card_dyadic_divisibility_event (d X : ℕ) (hd : 0 < d) :
    ((Icc 1 X).filter (fun n => d ∣ n ∧ ¬ 2 * d ∣ n)).card =
      X / d - X / (2 * d) := by
  have hsub : (Icc 1 X).filter (fun n => 2 * d ∣ n) ⊆
      (Icc 1 X).filter (fun n => d ∣ n) := by
    intro n hn
    obtain ⟨hnX, hn⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnX, (dvd_mul_left d 2).trans hn⟩
  have heq : (Icc 1 X).filter (fun n => d ∣ n ∧ ¬ 2 * d ∣ n) =
      (Icc 1 X).filter (fun n => d ∣ n) \
        (Icc 1 X).filter (fun n => 2 * d ∣ n) := by
    ext n
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [heq, card_sdiff_of_subset hsub, card_Icc_one_filter_dvd hd,
    card_Icc_one_filter_dvd (by omega)]

/-- At a complete period, exactly half the multiples survive. -/
theorem card_dyadic_divisibility_event_period (d X : ℕ)
    (hd : 0 < d) (hperiod : 2 * d ∣ X) :
    ((Icc 1 X).filter (fun n => d ∣ n ∧ ¬ 2 * d ∣ n)).card =
      X / (2 * d) := by
  rw [card_dyadic_divisibility_event d X hd]
  obtain ⟨m, rfl⟩ := hperiod
  have hfirst : (2 * d * m) / d = 2 * m := by
    rw [show 2 * d * m = (2 * m) * d by ring]
    exact Nat.mul_div_cancel _ hd
  have hsecond : (2 * d * m) / (2 * d) = m := by
    rw [mul_comm (2 * d) m]
    exact Nat.mul_div_cancel _ (by omega)
  rw [hfirst, hsecond]
  omega

/-- The real-valued mean is an exact reciprocal, not merely an asymptotic density. -/
theorem mean_dyadic_divisibility_event (d X : ℕ) (hd : 0 < d)
    (hX : 0 < X) (hperiod : 2 * d ∣ X) :
    (∑ n ∈ Icc 1 X, if d ∣ n ∧ ¬ 2 * d ∣ n then (1 : ℝ) else 0) /
        (X : ℝ) = 1 / (2 * (d : ℝ)) := by
  classical
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  rw [card_dyadic_divisibility_event_period d X hd hperiod]
  have hden : (2 * d : ℕ) ≠ 0 := by omega
  rw [Nat.cast_div hperiod (by exact_mod_cast hden)]
  push_cast
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  field_simp

/-- Exact finite harmonic contribution of a prime block at a common period.
The identity holds for arbitrary positive distinct integers as well. -/
theorem mean_prime_block_dyadic_events (P : Finset ℕ) (r X : ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hX : 0 < X)
    (hperiod : ∀ p ∈ P, 2 * (2 ^ r * p) ∣ X) :
    (∑ n ∈ Icc 1 X, ∑ p ∈ P,
      if 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n then (1 : ℝ) else 0) /
        (X : ℝ) =
      (∑ p ∈ P, (1 : ℝ) / p) / (2 * (2 : ℝ) ^ r) := by
  classical
  rw [sum_comm, sum_div, sum_div]
  apply sum_congr rfl
  intro p hp
  rw [mean_dyadic_divisibility_event _ X
    (Nat.mul_pos (Nat.pow_pos (by decide)) (hP p hp)) hX (hperiod p hp)]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ErdosProblems.Erdos257.PaperCompleteR8
