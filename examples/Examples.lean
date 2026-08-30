-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0
import Erdos249257
import ErdosProblems

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

/-! The centered-state recovery family is also a reusable consumer of the
problem-centric library.  Keep the signed recovery theorem as the one
downstream example: its centered-zero and Sylvester declarations are
mechanism evidence inside the same family, not separate endpoint claims. -/

/-- Downstream reuse of the exact #243 centered-state recovery mechanism.

The consumer keeps every load-bearing hypothesis visible: exact natural
`C/D` dynamics, `a > 1`, positive `C`, strict centering, a uniform lower
bound on the signed centered error, and division-free normalized vanishing.
It derives eventual zero centered defect, but does not assert that an
unrestricted reciprocal-tail orbit satisfies those hypotheses or solve
Erdős #243. -/
theorem downstream_bounded_negative_part_recovery
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (B : ℕ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n,
      E n = ErdosProblems.Erdos243.centeredState
        (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∀ n, Int.natAbs (E n) < C n)
    (hbound : ∀ n, -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 :=
  ErdosProblems.Erdos243.boundedNegativePart_eventually_zero
    a C D E B ha hCpos hC hD hE hcentered hbound hvanish

/-! The Boolean–Möbius transport is a second, genuinely reusable view of
#257 rationality: it removes the support from the downstream certificate while
retaining the exact rational numerator, denominator, and positivity boundary.
It is a normal-form constraint, not a contradiction or a solution of #257. -/

/-- Downstream reuse of the exact Boolean–Möbius rational-support equivalence.

The quotient-only certificate is useful to consumers that need to reason about
the carry orbit rather than reconstructing a support set.  The support-side
existence remains in the iff, and `q > 0` stays explicit. -/
theorem downstream_boolean_mobius_carry_normal_form
    (p : ℤ) (q : ℕ) (hq : 0 < q) :
    (∃ A : Set ℕ, 0 ∉ A ∧ (∃ a : ℕ, 0 < a ∧ a ∈ A) ∧
        erdosSupportSeries 2 A = (p : ℝ) / (q : ℝ)) ↔
      ∃ U : ℕ → ℤ, BooleanMobiusCarryCertificate p q U :=
  exists_normalized_support_fraction_iff_exists_booleanMobiusCarry p q hq
