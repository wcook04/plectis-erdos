import Erdos249257.LcmConeFlatness

/-! Exact interfaces for the complete LCM-grid statements of the long paper.
Existing tail-period and certificate proofs carry the mathematical content. -/
namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257.TotientTailPeriodKiller

theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ) := by
  simpa only [Nat.add_mul] using rational_totient_series_forces_lcm_cone_flatness hrat

theorem lcm_grid_fractional_parts
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      Int.fract (totientTail ((q + m) * periodLcm t)) =
        Int.fract (totientTail (q * periodLcm t)) := by
  obtain ⟨t₁, ht⟩ := lcm_grid_flatness hrat
  refine ⟨t₁, fun t htt q m hq => ?_⟩
  obtain ⟨k, hk⟩ := ht t htt q m hq
  have heq : totientTail ((q + m) * periodLcm t) =
      totientTail (q * periodLcm t) + (k : ℝ) := by linarith
  rw [heq, Int.fract_add_intCast]

theorem certificate_denominator_exclusion (r : ℚ) (h N L : ℕ)
    (hcert : certifiedKill h N L) (hden : r.den ∣ 2 ^ N * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ) := by
  intro hS
  exact tail_diff_notMem_int_of_certifiedKill hcert (tail_diff_int_of_den_dvd r hS h N hden)

theorem certificate_shift_positive (h N L : ℕ) (hcert : certifiedKill h N L) : 0 < h := by
  by_contra hn
  have hz : h = 0 := by omega
  have hh := hcert.1
  simp [windowDiscrepancy, hz] at hh
  omega

theorem lcm_grid_supply_iff :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
        certifiedKill (m * periodLcm t) (q * periodLcm t) L := by
  constructor
  · intro hirr t₀
    obtain ⟨t, ht, L, hL⟩ := irrational_totient_series_iff_lcm_diagonal_certificate_supply.mp hirr t₀
    exact ⟨t, ht, 1, 1, L, by omega, by simpa using hL⟩
  · exact irrational_totient_series_of_lcm_cone_certificate_supply

theorem lcm_grid_multiplier_positive (t q m L : ℕ)
    (hc : certifiedKill (m * periodLcm t) (q * periodLcm t) L) : 0 < m := by
  have hp := certificate_shift_positive _ _ _ hc
  by_contra hn
  have hm : m = 0 := by omega
  simp [hm] at hp

theorem short_lcm_window_nondivisor (t j : ℕ) (ht : 1 ≤ t) (hj : 1 ≤ j)
    (hlt : j < 2 * t) (hnd : ¬ j ∣ periodLcm t) :
    ∃ p a : ℕ, Nat.Prime p ∧ 1 ≤ a ∧ j = p ^ a ∧ t < j := by
  obtain ⟨p, a, hp, heq, hgt⟩ := eq_prime_pow_of_not_dvd_periodLcm hj hlt hnd
  refine ⟨p, a, hp, ?_, heq, hgt⟩
  by_contra ha
  have hz : a = 0 := by omega
  simp [hz] at heq
  omega

theorem clean_lcm_ray_factorisation (t j q : ℕ) (hdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (periodLcm t / j)) :
    q * periodLcm t + j = j * (q * (periodLcm t / j) + 1) ∧
    Nat.Coprime j (q * (periodLcm t / j) + 1) ∧
    Nat.totient (q * periodLcm t + j) = Nat.totient j * Nat.totient (q * (periodLcm t / j) + 1) := by
  refine ⟨?_, coprime_ray_cofactor q hclean, totient_periodLcm_ray_split q hdvd hclean⟩
  have h := Nat.mul_div_cancel' hdvd
  nlinarith

theorem unclean_lcm_ray_counterexample :
    2 ∣ periodLcm 2 ∧ Nat.totient (periodLcm 2 + 2) = 2 ∧
    Nat.totient 2 * Nat.totient (periodLcm 2 / 2 + 1) = 1 ∧
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ 2 → p ∣ (periodLcm 2 / 2)) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro h
  have := h 2 Nat.prime_two (dvd_refl 2)
  norm_num [periodLcm] at this


end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_fractional_parts
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.certificate_denominator_exclusion
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.certificate_shift_positive
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_supply_iff
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_multiplier_positive
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.short_lcm_window_nondivisor
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.clean_lcm_ray_factorisation
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.unclean_lcm_ray_counterexample
#print axioms Erdos249257.TotientTailPeriodKiller.dvd_periodLcm
