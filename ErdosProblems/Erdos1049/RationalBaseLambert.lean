import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #1049: rational-base Lambert arithmetic

The published Bundschuh--Väänänen theorem supplies irrationality for a
height-restricted family of rational bases, including `7/2`. This initial
problem-owned module formalizes the elementary obstruction which is independent
of that analytic theorem: a literal coordinatewise transfer of the integer-base
Erdős corridor would force an impossible power-versus-linear inequality at
`3/2`.

It does not assert irrationality at `3/2`, nor the unrestricted rational-base
conjecture.
-/

namespace ErdosProblems.Erdos1049

/-- The finite arithmetic core of a coordinatewise rational-base corridor.
`digit` abstracts the final divisor coefficient that is individually cleared. -/
def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)

/-- Clearing the `K`-th coordinate and making the positive remainder smaller
than one forces the numerator base to satisfy a power-versus-linear bound. -/
theorem coordinatewiseCorridor_implies_pow_lt_linear
    {a b N K Q digit : ℕ}
    (h : CoordinatewiseCorridor a b N K Q digit) :
    b ^ (N + K + 1) < a * (N + K) := by
  rcases h with ⟨ha, hQ, hdigit, hdigit_le, hdiv, htail⟩
  have hpow_pos : 0 < a ^ K := pow_pos ha K
  have hpow_le : a ^ K ≤ Q * digit :=
    Nat.le_of_dvd (Nat.mul_pos hQ hdigit) hdiv
  have hpow_linear : a ^ K ≤ Q * (N + K) :=
    hpow_le.trans (Nat.mul_le_mul_left Q hdigit_le)
  have hcombined :
      Q * b ^ (N + K + 1) < Q * (a * (N + K)) := by
    calc
      Q * b ^ (N + K + 1) < a ^ (K + 1) := htail
      _ = a ^ K * a := by rw [pow_succ]
      _ ≤ (Q * (N + K)) * a := Nat.mul_le_mul_right a hpow_linear
      _ = Q * (a * (N + K)) := by ring
  exact (Nat.mul_lt_mul_left hQ).mp hcombined

/-- Exponential growth already dominates the required linear corridor for all
`x ≥ 2`. -/
theorem three_mul_lt_two_pow_succ {x : ℕ} (hx : 2 ≤ x) :
    3 * x < 2 ^ (x + 1) := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
      have hpow : 3 < 2 ^ (x + 1) := by
        have : 2 ^ 2 ≤ 2 ^ (x + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      rw [pow_succ]
      omega

/-- The literal coordinatewise Erdős corridor cannot occur at base `3/2` once
both the shift and cleared window are nonempty. -/
theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit := by
  intro hcorr
  have hlt := coordinatewiseCorridor_implies_pow_lt_linear hcorr
  have hge := three_mul_lt_two_pow_succ (x := N + K) (by omega)
  omega

end ErdosProblems.Erdos1049
