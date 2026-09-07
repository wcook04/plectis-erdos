import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

/-!
# Erdős #1049: rational-base Lambert arithmetic

The published Bundschuh--Väänänen theorem supplies irrationality for a
height-restricted family of rational bases, including `7/2`.  This module
formalizes the complete elementary Archimedean height inequality needed at
`7/2`.  It also formalizes an obstruction independent of that analytic theorem:
a literal coordinatewise transfer of the integer-base Erdős corridor would
force an impossible power-versus-linear inequality at `3/2`.

It does not assert irrationality at `3/2`, nor the unrestricted rational-base
conjecture.
-/

namespace ErdosProblems.Erdos1049

/-! ## Exact arithmetic certificate for the published `7/2` lane -/

/-- The integer-power comparison used to bound
`log 2 / log 7 < 7 / 18`.  The logarithmic monotonicity step is deliberately
kept outside this arithmetic declaration. -/
theorem sevenHalves_power_certificate : 2 ^ 18 < 7 ^ 7 := by
  norm_num

/-- The exact rational boundary used after the elementary strict estimate
`1 / π² < 1 / 9`.  Supplying `3 < π` and the published analytic theorem is
a separate source-backed layer. -/
theorem sevenHalves_rational_margin :
    (7 : ℚ) / 18 = 1 / 2 - 1 / 9 := by
  norm_num

/-- The height region in the Bundschuh--Väänänen theorem, written in the
form needed for a positive reduced rational base `a / b`.  This definition
records only the elementary parameter inequality; it does not internalize
the external analytic irrationality theorem. -/
def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2

/-- The exact power certificate implies the logarithmic estimate used at
base `7 / 2`. -/
theorem sevenHalves_log_ratio_lt_seven_eighteenths :
    Real.log 2 / Real.log 7 < (7 : ℝ) / 18 := by
  have hpows : (2 : ℝ) ^ 18 < (7 : ℝ) ^ 7 := by
    exact_mod_cast sevenHalves_power_certificate
  have hlogs :
      Real.log ((2 : ℝ) ^ 18) < Real.log ((7 : ℝ) ^ 7) :=
    Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) hpows
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs
  have hlog7 : 0 < Real.log (7 : ℝ) := Real.log_pos (by norm_num)
  apply (div_lt_iff₀ hlog7).2
  nlinarith

/-- The elementary `pi > 3` bound puts `7 / 18` strictly inside the
Bundschuh--Väänänen height margin. -/
theorem sevenEighteenths_lt_bundschuhVaananenMargin :
    (7 : ℝ) / 18 < 1 / 2 - 1 / Real.pi ^ 2 := by
  have hpiSq : (9 : ℝ) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hinv : 1 / Real.pi ^ 2 < (1 : ℝ) / 9 :=
    one_div_lt_one_div_of_lt (by norm_num) hpiSq
  norm_num at hinv ⊢
  linarith

/-- Fully kernel-checked parameter verification for the first nonintegral
base covered by the published height theorem.  Combining this declaration
with that external theorem gives irrationality of the Lambert value at
`7 / 2`; no analytic theorem is introduced as an axiom here. -/
theorem sevenHalves_mem_bundschuhVaananenHeightRegion :
    BundschuhVaananenHeightRegion 7 2 := by
  exact sevenHalves_log_ratio_lt_seven_eighteenths.trans
    sevenEighteenths_lt_bundschuhVaananenMargin

/-- The source-facing Archimedean height inequality for `q = 7 / 2`.
This is exactly the elementary parameter condition consumed by the external
Bundschuh--Väänänen theorem; applying that analytic theorem remains a separate,
source-backed step. -/
theorem sevenHalves_archimedean_height_condition :
    Real.log 7 / Real.log ((7 : ℝ) / 2) <
      ((1 : ℝ) / 2 + 1 / Real.pi ^ 2)⁻¹ := by
  have hlog7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have hmargin :
      Real.log 2 / Real.log 7 <
        (1 : ℝ) / 2 - 1 / Real.pi ^ 2 := by
    simpa [BundschuhVaananenHeightRegion] using
      sevenHalves_mem_bundschuhVaananenHeightRegion
  have hratio :
      Real.log 2 <
        ((1 : ℝ) / 2 - 1 / Real.pi ^ 2) * Real.log 7 :=
    (div_lt_iff₀ hlog7).mp hmargin
  have hcore :
      ((1 : ℝ) / 2 + 1 / Real.pi ^ 2) * Real.log 7 <
        Real.log 7 - Real.log 2 := by
    linarith
  have hc : 0 < (1 : ℝ) / 2 + 1 / Real.pi ^ 2 := by
    have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    positivity
  have hdiv :
      Real.log 7 <
        (Real.log 7 - Real.log 2) /
          ((1 : ℝ) / 2 + 1 / Real.pi ^ 2) := by
    apply (lt_div_iff₀ hc).2
    simpa [mul_comm] using hcore
  have hlog72 : 0 < Real.log ((7 : ℝ) / 2) :=
    Real.log_pos (by norm_num)
  apply (div_lt_iff₀ hlog72).2
  rw [Real.log_div (by norm_num : (7 : ℝ) ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 0)]
  simpa [div_eq_mul_inv, mul_comm] using hdiv

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
