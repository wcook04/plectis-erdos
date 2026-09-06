/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the parity-perturbed rational control in Erdős #249

Erdős Problem 249 asks whether `S = ∑_{n≥1} φ(n)/2^n` is irrational.  The
declarations below construct an explicit coefficient sequence `c` and record
what it satisfies.  The sequence obeys the growth bound `c n ≤ n`, agrees with
Euler's totient at every odd argument, stays within `2` of the totient at every
argument, and has binary series exactly `5/4`.  The same sequence carries a
tempered integral binary orbit whose canonical dyadic carry sections through
levels `1, …, e` span a rational space of dimension at least `2^e - 1` for
every `e`.

The construction is a centred base-four expansion with digit set
`{-2, -1, 0, 1}` applied to `5/4 - S` and deposited at the even arguments.

These statements bound method.  Every hypothesis of the carry anti-compression
theorem, and its conclusion, holds for a sequence whose series is the rational
number `5/4`.  Nothing here bears on whether `S` itself is irrational, and
Erdős Problem 249 remains open.
-/

namespace Erdos249257.ExternalVerification249ParityPerturbedRationalControl

open Module Filter

/-- The binary coefficient series `∑_{n≥1} c(n)/2^n`. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

/-- The exact integer carry recurrence together with the subexponential
boundary `u(N) = o(2^N)`. -/
def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)

/-- A dyadic section of an integer carry orbit, viewed over `ℚ`. -/
def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)

/-- Every carry section through levels `1, …, e`. -/
abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))

/-- The canonical family of carry sections through levels `1, …, e`. -/
def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val

/-- The digit extracted from `x`: `⌊4x + 2/3⌋`. -/
noncomputable def digit (x : ℝ) : ℤ := ⌊4 * x + 2 / 3⌋

/-- One centred base-four step: `x ↦ 4x - ⌊4x + 2/3⌋`. -/
noncomputable def step (x : ℝ) : ℝ := 4 * x - (digit x : ℝ)

/-- Iterated remainders. -/
noncomputable def rem (x : ℝ) : ℕ → ℝ
  | 0 => x
  | m + 1 => step (rem x m)

/-- The `m`-th digit, carrying weight `4^{-(m+1)}`. -/
noncomputable def dig (x : ℝ) (m : ℕ) : ℤ := digit (rem x m)

/-- The binary totient series. -/
noncomputable abbrev S : ℝ := binaryCoeffSeries Nat.totient

/-- `ξ = 5/4 - S`, the quantity expanded in centred base four. -/
noncomputable def xi : ℝ := 5 / 4 - S

/-- The perturbation: the `m`-th centred digit at the even argument `2m`, zero
at odd arguments and at `0`. -/
noncomputable def delta (n : ℕ) : ℤ :=
  if n % 2 = 0 ∧ 2 ≤ n then dig xi (n / 2 - 1) else 0

/-- The control coefficient sequence `c = φ + δ`. -/
noncomputable def control (n : ℕ) : ℕ := ((Nat.totient n : ℤ) + delta n).toNat

/-- A coefficient sequence bounded by `n`, equal to `φ` at every odd argument,
within `2` of `φ` everywhere, with rational binary series. -/
theorem parity_perturbed_rational_control :
    (∀ n, control n ≤ n) ∧ (∀ n, n % 2 = 1 → control n = Nat.totient n) ∧
      (∀ n, |(control n : ℤ) - Nat.totient n| ≤ 2) ∧
      binaryCoeffSeries control = 5 / 4 := by
  sorry

/-- The control series is exactly `5/4`. -/
theorem control_series : binaryCoeffSeries control = 5 / 4 := by
  sorry

/-- The control series is rational. -/
theorem not_irrational_control : ¬ Irrational (binaryCoeffSeries control) := by
  sorry

/-- The control carries a tempered integral binary orbit whose dyadic carry
sections through every level `e` span a rational space of dimension at least
`2^e - 1`. -/
theorem control_temperedOrbit_carryRank_unbounded :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit control v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  sorry

/-- Carry anti-compression for any coefficient sequence agreeing with `φ` at
every odd argument. -/
theorem finrank_canonicalCarryKernel_ge_of_oddAgree {c : ℕ → ℕ}
    (hodd : ∀ n, n % 2 = 1 → c n = Nat.totient n)
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit c v u) (e : ℕ) :
    2 ^ e - 1 ≤
      finrank ℚ
        (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  sorry

end Erdos249257.ExternalVerification249ParityPerturbedRationalControl
