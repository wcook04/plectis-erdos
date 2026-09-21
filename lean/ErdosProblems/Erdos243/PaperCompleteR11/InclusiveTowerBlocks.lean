import ErdosProblems.Erdos243.PaperCompleteR11.OrbitBlockArithmetic

/-!
# Explicit square-sized blocks for the inclusive boundary

These bounds apply simultaneously
throughout a block whose width grows with the selection parameter. They
replace the previously missing uniform `ceil(log B)` estimates with exact
natural arithmetic on the cofinal choices `k = 2^t`, `B = k^2`.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators

/-- The exponential dominates the precise linear exponent used below. -/
theorem four_mul_add_one_le_two_pow {t : ℕ} (ht : 5 ≤ t) :
    4 * t + 1 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      rw [pow_succ]
      omega

/-- Exact domination of the fourth power; no floating-point evaluation is
used for the growing parameter. -/
theorem twice_fourth_power_le_two_pow_two_pow {t : ℕ} (ht : 5 ≤ t) :
    2 * (2 ^ t) ^ 4 ≤ 2 ^ (2 ^ t) := by
  calc
    2 * (2 ^ t) ^ 4 = 2 ^ (4 * t + 1) := by
      rw [← pow_mul, show t * 4 = 4 * t by omega, pow_succ]
      ring
    _ ≤ 2 ^ (2 ^ t) := two_pow_mono (four_mul_add_one_le_two_pow ht)

/-- The entire gcd-loss exponent fits below the first multiplier's double
exponential exponent, even though the block itself grows quadratically. -/
theorem square_block_exponent_budget (K N t : ℕ) (ht : 5 ≤ t)
    (hKN : K + N ≤ 2 ^ t) :
    (K + (N + 2 ^ t + (2 ^ t) ^ 2)) * (2 ^ t) ^ 2 ≤ 2 ^ (2 ^ t) := by
  let k := 2 ^ t
  have hk : 2 ≤ k := by
    have hh := index_succ_le_two_pow t
    dsimp [k]
    omega
  have hlin : 2 * k ≤ k ^ 2 := by
    have hh := Nat.mul_le_mul_left k hk
    nlinarith
  have hsum : K + (N + k + k ^ 2) ≤ 2 * k ^ 2 := by
    dsimp [k] at *
    omega
  calc
    (K + (N + k + k ^ 2)) * k ^ 2 ≤ (2 * k ^ 2) * k ^ 2 :=
      Nat.mul_le_mul_right _ hsum
    _ = 2 * k ^ 4 := by ring
    _ ≤ 2 ^ k := twice_fourth_power_le_two_pow_two_pow ht

/-- The exact size premise of `coprime_core_record_fence` is supplied by
one common running-maximum envelope and one common multiplier lower bound. -/
theorem square_block_core_size (U : ℕ → ℕ) (K N t : ℕ)
    (ht : 5 ≤ t) (hKN : K + N ≤ 2 ^ t)
    (hH : runningMax U (N + 2 ^ t + (2 ^ t) ^ 2) ≤
      2 ^ (K + (N + 2 ^ t + (2 ^ t) ^ 2)))
    (A : Fin ((2 ^ t) ^ 2) → ℕ)
    (hA : ∀ i, 2 * binaryTower (2 ^ t) ≤ A i) :
    ∀ i, max ((2 ^ t) ^ 2) (runningMax U (N + 2 ^ t + (2 ^ t) ^ 2)) *
      (runningMax U (N + 2 ^ t + (2 ^ t) ^ 2)) ^ ((2 ^ t) ^ 2 - 1) < A i := by
  let B := (2 ^ t) ^ 2
  let M := N + 2 ^ t + B
  let H := runningMax U M
  let V := 2 ^ (K + M)
  have hB : 1 ≤ B := by
    dsimp [B]
    exact Nat.one_le_pow 2 (2 ^ t) (pow_pos (by norm_num) t)
  have hBV : B ≤ V := by
    have hindex := index_succ_le_two_pow M
    have hmono := two_pow_mono (show M ≤ K + M by omega)
    dsimp [M, V] at *
    omega
  have hHV : H ≤ V := hH
  have hexp := square_block_exponent_budget K N t ht hKN
  intro i
  calc
    max B H * H ^ (B - 1) ≤ V * V ^ (B - 1) :=
      Nat.mul_le_mul (max_le hBV hHV) (Nat.pow_le_pow_left hHV _)
    _ = V ^ B := by
      calc
        _ = V ^ (B - 1 + 1) := by rw [pow_succ]; ring
        _ = V ^ B := by rw [Nat.sub_add_cancel hB]
    _ = 2 ^ ((K + M) * B) := by dsimp [V]; rw [pow_mul]
    _ ≤ binaryTower (2 ^ t) := two_pow_mono hexp
    _ < 2 * binaryTower (2 ^ t) := by have := binaryTower_pos (2 ^ t); omega
    _ ≤ A i := hA i

/-- Any fixed integer scale and the complete CRT interval cost only an
additive tower-index constant. This avoids an unjustified equality under
log-log rescaling. -/
theorem scaled_crt_height_binaryTower (g P B h : ℕ)
    (hP : P ≤ binaryTower h) (hB : B ≤ binaryTower h) :
    g * (2 * P + B) ≤ binaryTower (h + g + 2) := by
  let S := binaryTower (h + g)
  have hS : 2 ≤ S := by
    have hh := binaryTower_mono (show 0 ≤ h + g by omega)
    norm_num [binaryTower] at hh
    exact hh
  have hPS : P ≤ S := hP.trans (binaryTower_mono (by omega))
  have hBS : B ≤ S := hB.trans (binaryTower_mono (by omega))
  have hgS : g ≤ S := by
    have hh := index_succ_le_two_pow g
    have hh' := index_succ_le_two_pow (2 ^ g)
    have ht := binaryTower_mono (show g ≤ h + g by omega)
    dsimp [S, binaryTower] at *
    omega
  have hfirst : g * (2 * P + B) ≤ 3 * S ^ 2 := by
    have hh := Nat.mul_le_mul hgS (show 2 * P + B ≤ 3 * S by omega)
    nlinarith
  have hsq : 3 ≤ S ^ 2 := by nlinarith
  calc
    g * (2 * P + B) ≤ 3 * S ^ 2 := hfirst
    _ ≤ S ^ 4 := by
      have hh := Nat.mul_le_mul_right (S ^ 2) hsq
      nlinarith
    _ = binaryTower (h + g + 2) := by
      rw [show h + g + 2 = (h + g + 1) + 1 by omega,
        binaryTower_succ, binaryTower_succ]
      dsimp [S]
      ring

/-- Exact logarithmic budget for the whole scaled CRT interval. -/
theorem scaled_crt_height_logLog (g P B h : ℕ)
    (hP : P ≤ binaryTower h) (hB : B ≤ binaryTower h) :
    recordLogLog (g * (2 * P + B) : ℕ) ≤ (h + g + 2 : ℕ) := by
  apply recordLogLog_le_of_le_binaryTower (by omega)
  exact_mod_cast scaled_crt_height_binaryTower g P B h hP hB

end ErdosProblems.Erdos243.PaperCompleteR11
