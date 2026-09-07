/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #1049 prime-support and two-selector package

This package exposes nine source-independent consumers from the q-Apéry and
two-selector developments.  The first four statements carry no arithmetic
support hypothesis at all: the sharp `1/q` gap at a rational target follows
from nonvanishing of the integral linear form, its two-row version follows
from a nonzero exterior determinant, and the determinant-height tradeoff
follows from two small remainders.  The prime and prime-power statements are
the q-Apéry-facing specialisations of those gaps, and the unimodular height
statement is the specialisation of the tradeoff to a bounded change of basis.
They prove exact arithmetic gaps and analytic tradeoffs; they do not produce
the required q-Apéry prime support or prove irrationality of the Lambert value
at `3 / 2`.
-/

namespace Erdos249257.ExternalVerification1049PrimeSupportSelectors

open Filter

/-- At a rational target `a / q` with `q` positive, two integral coefficient
rows with nonzero exterior determinant `A₁ B₂ - A₂ B₁` cannot both have
remainder below `1 / q`.  Nonvanishing of the determinant is the only
hypothesis on the rows: no primality, no denominator support, and no
coprimality between `a` and `q`. -/
theorem twoSelector_rationalGap
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hdet : A₁ * B₂ - A₂ * B₁ ≠ 0) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  sorry

/-- At a rational target `a / q` with `q` positive, a nonzero integral linear
form `B (a/q) - A` has absolute value at least `1 / q`.  Nonvanishing of the
form is the only hypothesis: no primality, no denominator support, and no
coprimality between `a` and `q`. -/
theorem integerLinearForm_rationalGap
    (a q A B : ℤ) (hq : 0 < q)
    (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry

/-- Along integral row pairs with nonzero exterior determinant, both real
linear forms cannot tend to zero at a rational target. -/
theorem rationalTwoSelector_notBothTendstoZero
    (a q : ℤ) (hq : 0 < q)
    (A₁ B₁ A₂ B₂ : ℕ → ℤ)
    (hdet : ∀ n, A₁ n * B₂ n - A₂ n * B₁ n ≠ 0) :
    ¬(Tendsto
        (fun n ↦ (B₁ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ n : ℝ))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ (B₂ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ n : ℝ))
        atTop (nhds 0)) := by
  sorry

/-- Two real remainders at most `ε` at a common target bound the exterior
determinant by `ε (|B₁| + |B₂|)`.  The bound uses no change of basis, no
unimodularity, and no coefficient-height hypothesis. -/
theorem twoSelector_detHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ F ε : ℝ)
    (h₁ : |B₁ * F - A₁| ≤ ε) (h₂ : |B₂ * F - A₂| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤ ε * (|B₁| + |B₂|) := by
  sorry

/-- A real two-row recombination with determinant of absolute value one and
coefficient height at most `H` cannot make both remainders smaller than the
preserved determinant budget.  This is the bounded-change-of-basis
specialisation of the determinant-height tradeoff, and integer-unimodular
changes of basis are a further special case. -/
theorem twoSelector_unimodularHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ u v w z F H ε : ℝ)
    (hunimod : |u * z - v * w| = 1)
    (hε : 0 ≤ ε)
    (hu : |u| ≤ H) (hv : |v| ≤ H) (hw : |w| ≤ H) (hz : |z| ≤ H)
    (h₁ : |(u * B₁ + v * B₂) * F - (u * A₁ + v * A₂)| ≤ ε)
    (h₂ : |(w * B₁ + z * B₂) * F - (w * A₁ + z * A₂)| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤
      2 * H * ε * (|B₁| + |B₂|) := by
  sorry

/-- A common prime in two denominator coordinates, with only one prime power
in their exterior determinant, forces a full `1/q` gap in at least one row at
a rational target whose denominator is prime to that prime.  This is the
q-Apéry-facing specialisation of `twoSelector_rationalGap`: the hypothesis
that `ell ^ 2` does not divide the determinant already gives a nonzero
determinant, and the prime data records the arithmetic interface the q-Apéry
rows are expected to supply. -/
theorem primeSupportedTwoSelector_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hellq : ¬ (ell : ℤ) ∣ q)
    (hellB₁ : (ell : ℤ) ∣ B₁)
    (hellB₂ : (ell : ℤ) ∣ B₂)
    (hdet : ¬ (ell : ℤ) ^ 2 ∣ A₁ * B₂ - A₂ * B₁) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  sorry

/-- A prime dividing the denominator coordinate, but neither the numerator
coordinate nor the rational denominator, forces the sharp rational `1/q` gap
in a single integral linear form.  This is the q-Apéry-facing specialisation
of `integerLinearForm_rationalGap`: the prime data certifies that the form is
nonzero. -/
theorem primeSupportedOneRow_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ) (hq : 0 < q)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry

/-- Prime-power support in the denominator coordinate yields the same sharp
single-row `1/q` gap once the exponent is nonzero.  The conclusion needs only
one prime copy, and this interface retains the stronger source data exactly so
that a q-Apéry tail exponent can be passed through unchanged. -/
theorem primePowerSupportedOneRow_rationalGap
    {ell r : ℕ} (hell : ell.Prime) (hr : r ≠ 0)
    (a q A B : ℤ) (hq : 0 < q)
    (hellPowB : (ell : ℤ) ^ r ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry

/-- When every denominator coordinate is zero modulo `N`, `N < 2^k` already
forces a nontrivial binary selector collision in both coordinates. -/
theorem zeroDenominatorCoordinates_binaryCollision
    {N k : ℕ} [NeZero N]
    (w : Fin k → ZMod N × ZMod N)
    (hzero : ∀ i, (w i).2 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry

end Erdos249257.ExternalVerification1049PrimeSupportSelectors
