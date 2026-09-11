import Mathlib

/-!
# Regular-rate extraction: exact formal target

Status: verified locally by the focused Newton-classification build on 2026-09-09.

This file deliberately does **not** manufacture a theorem body for the analytic
extraction theorem.  It pins the exact proposition that the ordinary proof in
`MATHEMATICS.md` proves and that Type A can formalise against Mathlib v4.29.1.
No placeholder proof command is used.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace Erdos243V6

/-- The rising factorial `n (n+1) ... (n+d-1)` in `ℚ`. -/
def risingQ (n d : ℕ) : ℚ :=
  ∏ k ∈ Finset.range d, ((n + k : ℕ) : ℚ)

/-- Exact asymptotic hypothesis.  Positivity is required only on the stated
`n ≥ 1` domain; all values of the ratio expression at `n = 0` are eventually
irrelevant to `atTop`.  The comparison scale is `n^{-lam}` via `Real.rpow`. -/
def RegularRateHypothesis (C : ℕ → ℕ) (lam : ℝ) : Prop :=
  (∀ n, 1 ≤ n → 0 < C n) ∧ 1 < lam ∧
    (fun n : ℕ ↦ (C (n + 1) : ℝ) / (C n : ℝ) - (1 + lam / (n : ℝ)))
      =o[atTop]
    (fun n : ℕ ↦ Real.rpow (n : ℝ) (-lam))

/-- Exact conclusion required by the packet. -/
def RegularRateConclusion (C : ℕ → ℕ) (lam : ℝ) : Prop :=
  ∃ d : ℕ, 2 ≤ d ∧ lam = d ∧
    ∃ A B : ℚ, 0 < A ∧
      ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℚ) = A * risingQ n d + B

/-- The unproved-in-Lean target declaration.  The mathematical proof is supplied
in `MATHEMATICS.md`; this definition prevents status drift from a paper theorem
to a purported kernel theorem. -/
def RegularRateExtractionStatement : Prop :=
  ∀ (C : ℕ → ℕ) (lam : ℝ),
    RegularRateHypothesis C lam → RegularRateConclusion C lam

#check RegularRateExtractionStatement

end Erdos243V6
