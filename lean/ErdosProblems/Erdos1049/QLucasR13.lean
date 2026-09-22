import ErdosProblems.Erdos1049.RootUnityLocalCancellationR13
import Mathlib

/-!
# q-Lucas for the project's actual Pascal-recursive Gaussian


The theorem is derived from Pascal's recursion and vanishing of the
intermediate entries in the first root block. It is not an axiom or a
statement about a different library Gaussian.
-/
namespace ErdosProblems.Erdos1049.PaperR13

lemma quotient_remainder_successor_no_carry {ell n : ℕ} (hell : 0 < ell)
    (h : n % ell + 1 < ell) :
    (n + 1) / ell = n / ell ∧ (n + 1) % ell = n % ell + 1 := by
  have hmod : (n + 1) % ell = n % ell + 1 := by
    rw [Nat.add_mod]
    have he : 1 % ell = 1 := Nat.mod_eq_of_lt (by omega)
    rw [he, Nat.mod_eq_of_lt h]
  exact ⟨Nat.succ_div_of_mod_ne_zero (by rw [hmod]; omega), hmod⟩

lemma quotient_remainder_successor_carry {ell n : ℕ} (hell : 0 < ell)
    (h : n % ell + 1 = ell) :
    (n + 1) / ell = n / ell + 1 ∧ (n + 1) % ell = 0 := by
  have hmod : (n + 1) % ell = 0 := by
    calc
      (n + 1) % ell = (n % ell + 1) % ell := by simp [Nat.add_mod]
      _ = 0 := by rw [h]; simp
  exact ⟨Nat.succ_div_of_mod_eq_zero hmod, hmod⟩

section Field
variable {K : Type*} [Field K]

lemma root_power_reduce (q : K) {ell : ℕ} (hroot : q ^ ell = 1) (n : ℕ) :
    q ^ n = q ^ (n % ell) := by
  calc
    q ^ n = q ^ (n % ell + ell * (n / ell)) := by rw [Nat.mod_add_div]
    _ = q ^ (n % ell) := by rw [pow_add, pow_mul, hroot, one_pow, mul_one]

lemma root_power_difference (q : K) (hq : q ≠ 0) {ell n k : ℕ}
    (hroot : q ^ ell = 1) (hk : k ≤ n) (hrem : k % ell ≤ n % ell) :
    q ^ (n - k) = q ^ (n % ell - k % ell) := by
  apply mul_right_cancel₀ (pow_ne_zero (k % ell) hq)
  calc
    q ^ (n - k) * q ^ (k % ell) = q ^ (n - k) * q ^ k := by
      rw [root_power_reduce q hroot k]
    _ = q ^ n := by rw [← pow_add, Nat.sub_add_cancel hk]
    _ = q ^ (n % ell) := root_power_reduce q hroot n
    _ = q ^ (n % ell - k % ell) * q ^ (k % ell) := by
      rw [← pow_add, Nat.sub_add_cancel hrem]

/-- The only primitive-root input needed by the Pascal induction. -/
theorem gaussian_first_root_block_zero (q : K) {ell k : ℕ}
    (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1)
    (hk0 : 0 < k) (hk : k < ell) : gaussBinom q ell k = 0 := by
  have hp := qPochhammer_nonzero_below_order q hprimitive k hk
  have h := gaussBinom_mul_qPochhammer q hk.le
  have hz : qPochhammer q (q ^ (ell - k + 1)) k = 0 :=
    qPochhammer_root_window q hroot (by omega) (by omega)
  rw [hz] at h
  exact (mul_eq_zero.mp h).resolve_right hp

lemma lucas_expression_zero_of_lt (q : K) {ell n k : ℕ}
    (hnk : n < k) :
    ((n / ell).choose (k / ell) : K) * gaussBinom q (n % ell) (k % ell) = 0 := by
  have hd : n / ell ≤ k / ell := Nat.div_le_div_right hnk.le
  rcases lt_or_eq_of_le hd with hlt | heq
  · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]
  · have hn := Nat.mod_add_div n ell
    have hk := Nat.mod_add_div k ell
    rw [heq] at hn
    have hrem : n % ell < k % ell := by omega
    rw [gaussBinom_eq_zero_of_lt q hrem, mul_zero]

set_option maxHeartbeats 1000000 in
/-- All-index q-Lucas for the literal Gaussian definition used in A and B. -/
theorem gaussian_qLucas (q : K) (hq : q ≠ 0) {ell : ℕ} (hell : 0 < ell)
    (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1) :
    ∀ n k : ℕ, gaussBinom q n k =
      ((n / ell).choose (k / ell) : K) * gaussBinom q (n % ell) (k % ell) := by
  intro n
  induction n with
  | zero =>
      intro k
      rcases k with _ | k
      · simp
      · rw [gaussBinom_zero_succ]
        exact (lucas_expression_zero_of_lt q (ell := ell) (by omega)).symm
  | succ n ih =>
      intro k
      rcases k with _ | k
      · simp
      · by_cases hk : k ≤ n
        · rw [gaussBinom_succ_of_le q hk, ih (k + 1), ih k]
          have hnlt := Nat.mod_lt n hell
          have hklt := Nat.mod_lt k hell
          by_cases hnc : n % ell + 1 = ell
          · obtain ⟨hnd, hnm⟩ := quotient_remainder_successor_carry hell hnc
            have hnrem : n % ell = ell - 1 := by omega
            by_cases hkc : k % ell + 1 = ell
            · obtain ⟨hkd, hkm⟩ := quotient_remainder_successor_carry hell hkc
              have hkrem : k % ell = ell - 1 := by omega
              have hpow := root_power_difference q hq hroot hk
                (show k % ell ≤ n % ell by omega)
              rw [hnrem, hkrem, Nat.sub_self, pow_zero] at hpow
              rw [hnd, hnm, hkd, hkm, hpow, hnrem, hkrem]
              simp [gaussBinom_self, Nat.choose_succ_succ, Nat.cast_add, add_comm]
            · obtain ⟨hkd, hkm⟩ := quotient_remainder_successor_no_carry hell (by omega : k % ell + 1 < ell)
              have hrem : k % ell ≤ n % ell := by omega
              have hpow := root_power_difference q hq hroot hk hrem
              have hz : gaussBinom q (n % ell) (k % ell + 1) +
                  q ^ (n % ell - k % ell) * gaussBinom q (n % ell) (k % ell) = 0 := by
                rw [← gaussBinom_succ_of_le q hrem, hnc]
                exact gaussian_first_root_block_zero q hroot hprimitive (by omega) (by omega)
              rw [hnd, hnm, hkd, hkm, hpow, gaussBinom_zero_succ, mul_zero]
              calc
                _ = ((n / ell).choose (k / ell) : K) *
                    (gaussBinom q (n % ell) (k % ell + 1) +
                      q ^ (n % ell - k % ell) * gaussBinom q (n % ell) (k % ell)) := by ring
                _ = 0 := by rw [hz, mul_zero]
          · obtain ⟨hnd, hnm⟩ := quotient_remainder_successor_no_carry hell (by omega : n % ell + 1 < ell)
            by_cases hkc : k % ell + 1 = ell
            · obtain ⟨hkd, hkm⟩ := quotient_remainder_successor_carry hell hkc
              have hz : gaussBinom q (n % ell) (k % ell) = 0 :=
                gaussBinom_eq_zero_of_lt q (by omega)
              rw [hnd, hnm, hkd, hkm, hz]
              simp
            · obtain ⟨hkd, hkm⟩ := quotient_remainder_successor_no_carry hell (by omega : k % ell + 1 < ell)
              rw [hnd, hnm, hkd, hkm]
              by_cases hrem : k % ell ≤ n % ell
              · rw [root_power_difference q hq hroot hk hrem,
                  gaussBinom_succ_of_le q hrem]
                ring
              · have hlt : n % ell < k % ell := by omega
                rw [gaussBinom_eq_zero_of_lt q hlt,
                  gaussBinom_eq_zero_of_lt q (by omega : n % ell < k % ell + 1),
                  gaussBinom_eq_zero_of_lt q (by omega : n % ell + 1 < k % ell + 1)]
                ring
        · have hlt : n + 1 < k + 1 := by omega
          rw [gaussBinom_eq_zero_of_lt q hlt]
          exact (lucas_expression_zero_of_lt q hlt).symm

/-- This wrapper explicitly refers to evaluations of the actual integer
polynomials, rather than an unconnected Gaussian family. -/
theorem actual_gaussian_eval_qLucas (q : K) (hq : q ≠ 0) {ell : ℕ}
    (hell : 0 < ell) (hroot : q ^ ell = 1)
    (hprimitive : ∀ j : ℕ, 0 < j → j < ell → q ^ j ≠ 1) (n k : ℕ) :
    (gaussBinom (Polynomial.X : Polynomial ℤ) n k).eval₂ (Int.castRingHom K) q =
      ((n / ell).choose (k / ell) : K) * gaussBinom q (n % ell) (k % ell) := by
  rw [eval₂_gaussBinom]
  exact gaussian_qLucas q hq hell hroot hprimitive n k

end Field
end ErdosProblems.Erdos1049.PaperR13
