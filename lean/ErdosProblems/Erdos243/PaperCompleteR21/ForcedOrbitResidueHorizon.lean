import ErdosProblems.Erdos243.FiniteHorizonResidue

/-!
# Erdős 243: the factorial residue reduction for forced orbits

Paper-form restatement of `long243:res:residue` of the long note
`paper/reasoning-parts/erdos243/core.tex`: for all `h` and all integers
`a ≡ b (mod (h+1)!)`, the forced orbit from `a` survives `h` updates exactly
when the orbit from `b` does.

`ForcedSurvives h 0 a` is the tree's survival predicate: exact division of
the forced numerator `(i+1) a² - (i+2) a + (i+3)` by `i + 2` at each of the
first `h` indices, starting at index `0`.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

/-- **Factorial residue reduction (`long243:res:residue`).**
For all `h` and all integers `a ≡ b [ZMOD (h+1)!]`, the forced orbit from `a`
survives `h` forced updates exactly when the orbit from `b` does. -/
theorem forcedOrbit_survives_iff_of_factorial_modEq
    (h : ℕ) (a b : ℤ)
    (hab : a ≡ b [ZMOD ((h + 1).factorial : ℤ)]) :
    ForcedSurvives h 0 a ↔ ForcedSurvives h 0 b :=
  forcedSurvives_iff_of_modEq_factorial hab

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.forcedOrbit_survives_iff_of_factorial_modEq
#print axioms ErdosProblems.Erdos243.forcedSurvives_iff_of_modEq_factorial

end ErdosProblems.Erdos243.PaperCompleteR21
