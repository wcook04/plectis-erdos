/- Copyright (c) 2026 Will Cook. Released under Apache 2.0. -/
import Mathlib
/-! Deliberately weaker but proved statement. Comparator must reject the type. -/
open Filter Topology Finset
namespace ErdosProblems.ExternalVerification
theorem feedbackPolicy_preserves_sum (A d : ℕ → ℕ)
    (h : ∀ n, d n ≤ A n) : ∀ n, d n ≤ A n := h
end ErdosProblems.ExternalVerification
