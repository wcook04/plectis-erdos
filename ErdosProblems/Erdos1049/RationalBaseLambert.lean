import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

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

/-! ## Rational-base cleared-tail dynamics -/

/-- The first `N` terms of a rational-base divisor-series coordinate.  The
coefficient sequence is kept abstract so the recurrence is reusable beyond
the divisor function. -/
def rationalBasePrefixQ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.range N,
    coeff (m + 1) * s ^ (m + 1) / r ^ (m + 1)

@[simp] theorem rationalBasePrefixQ_succ
    (r s : ℚ) (coeff : ℕ → ℚ) (N : ℕ) :
    rationalBasePrefixQ r s coeff (N + 1) =
      rationalBasePrefixQ r s coeff N +
        coeff (N + 1) * s ^ (N + 1) / r ^ (N + 1) := by
  rw [rationalBasePrefixQ, rationalBasePrefixQ, Finset.sum_range_succ]

/-- Denominator-cleared tail state for a putative rational value `F`. -/
def rationalBaseClearedTailQ
    (r s B F : ℚ) (coeff : ℕ → ℚ) (N : ℕ) : ℚ :=
  B * r ^ N * (F - rationalBasePrefixQ r s coeff N)

/-- Exact rational-base recurrence.  The forcing term contains `s^(N+1)`;
this is the denominator-base tax absent from the integer-base case `s = 1`. -/
theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1) := by
  rw [rationalBaseClearedTailQ, rationalBaseClearedTailQ,
    rationalBasePrefixQ_succ, pow_succ]
  field_simp [hr]
  ring

/-- Natural-valued magnitude of the forcing term in the cleared recurrence. -/
def rationalBaseForcingNat
    (s B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) : ℕ :=
  B * coeff (N + 1) * s ^ (N + 1)

/-- At every genuine noninteger denominator base `s ≥ 2`, positive
coefficients force at least exponential `2^(N+1)` growth. -/
theorem twoPow_le_rationalBaseForcingNat
    {s B : ℕ} {coeff : ℕ → ℕ} {N : ℕ}
    (hs : 2 ≤ s) (hB : 1 ≤ B) (hc : 1 ≤ coeff (N + 1)) :
    2 ^ (N + 1) ≤ rationalBaseForcingNat s B coeff N := by
  have hcoeff : 1 ≤ B * coeff (N + 1) := Nat.mul_pos hB hc
  calc
    2 ^ (N + 1) ≤ s ^ (N + 1) := Nat.pow_le_pow_left hs _
    _ = 1 * s ^ (N + 1) := by simp
    _ ≤ (B * coeff (N + 1)) * s ^ (N + 1) :=
      Nat.mul_le_mul_right _ hcoeff
    _ = rationalBaseForcingNat s B coeff N := by
      simp [rationalBaseForcingNat, mul_assoc]

/-- In the integer-base case the denominator-base tax collapses exactly. -/
@[simp] theorem rationalBaseForcingNat_one
    (B : ℕ) (coeff : ℕ → ℕ) (N : ℕ) :
    rationalBaseForcingNat 1 B coeff N = B * coeff (N + 1) := by
  simp [rationalBaseForcingNat]

end ErdosProblems.Erdos1049
