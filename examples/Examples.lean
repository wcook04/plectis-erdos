-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Erdos249257

/-!
# Minimal downstream consumer

This module is not part of the `Erdos249257` library. It imports the package
root exactly as an external project would (`import Erdos249257`) and derives a
small corollary through the advertised public interface, so the release is
demonstrably usable from outside, not merely internally buildable. CI builds
it with `lake build Examples`.

The same proof-trust rules apply here as in the library: no `sorry`, no
`admit`, no new axioms (`scripts/check_release.py` scans this directory too).
-/

open Erdos249257

/-- Downstream instance of the headline theorem: the base-3 series
`∑ 1/(3ⁿ − 1)` is irrational, obtained by specialising
`irrational_erdosSum_full_support` exactly as a consumer project would. -/
theorem downstream_base_three_irrational :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((3 : ℝ) ^ (k + 1) - 1)) := by
  have h := irrational_erdosSum_full_support 3 (by norm_num)
  have hcast : ((3 : ℕ) : ℝ) = (3 : ℝ) := by norm_num
  rwa [hcast] at h

/-- The release's own base-2 headline, reached through the public root
import: the Erdős–Borwein constant is irrational. -/
example : Irrational (∑' k : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) - 1)) :=
  irrational_erdosBorwein_series

/-- Downstream use of a conditional interface. The rational-gap lower bound
is supplied by the library, while the analytic shell estimate remains an
explicit hypothesis. In particular, this does not prove the universal
Erdős #257 statement for arbitrary infinite supports. -/
theorem downstream_conditional_rational_shell_bound
    (whole pfx : ℚ) (K X : ℕ)
    (hpositive : pfx < whole) (hX : 1 ≤ X)
    (hupper : (whole : ℝ) - (pfx : ℝ) ≤
      (K : ℝ) / (2 : ℝ) ^ X + 2 / (2 : ℝ) ^ (2 * X)) :
    (2 : ℝ) ^ X ≤
      ((whole.den * pfx.den : ℕ) : ℝ) * (K + 1) :=
  prefixDenominator_shell_power_bound_of_rational_difference
    whole pfx K X hpositive hX hupper

/-- The external import also exposes the exact finite correction for a
composite support multiplier.  This is a local divisor identity: it does not
bound arbitrary defects or prove the open #257 irrationality statement. -/
theorem downstream_composite_dilation_defect
    (A : Set ℕ) {a x : ℕ} (ha : a ∈ A) (ha0 : 0 < a) (hx0 : 0 < x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        CompositeDilationDefect.compositeDilationDefect A a x :=
  CompositeDilationDefect.supportCoeff_mul_eq_add_defect A ha ha0 hx0
