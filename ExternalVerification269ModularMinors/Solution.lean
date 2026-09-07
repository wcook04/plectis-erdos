/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos269.PaperR7ModularMinors

namespace Erdos249257.ExternalVerification269ModularMinors

/-- The `{2,3,5}`-smooth value of an exponent vector. -/
abbrev smoothVal235 (i j k : ℕ) : ℕ := ErdosProblems.Erdos269.smooth3Val 2 3 5 i j k

/-- The running-LCM height at `{2,3,5}`. -/
abbrev height235 (x : ℕ) : ℕ := ErdosProblems.Erdos269.threePrimeHeight 2 3 5 x

/-- The exact rational kernel. -/
abbrev kernelQ235 (i j k : ℕ) : ℚ :=
  ErdosProblems.Erdos269.threePrimeKernelQ 2 3 5 i j k

/-- The literal reduction: invert the natural height in `ZMod B`. -/
noncomputable abbrev kernelMod235 := ErdosProblems.Erdos269.PaperR7.kernelMod235

/-- One choice of indices giving nonzero rational minors and unit minors modulo
every admissible denominator, at every layer. -/
theorem admissible_modular_minors (n : ℕ) :
    ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧
      (∀ k : ℕ,
        (Matrix.det fun i j : Fin n => kernelQ235 (I i) (J j) k) ≠ 0) ∧
      (∀ B : ℕ, 2 ≤ B → Nat.Coprime B 30 → ∀ k : ℕ,
        IsUnit (Matrix.det fun i j : Fin n => kernelMod235 B (I i) (J j) k) ∧
        IsUnit (Matrix.of fun i j : Fin n => kernelMod235 B (I i) (J j) k)) :=
  ErdosProblems.Erdos269.PaperR7.admissible_modular_minors n

end Erdos249257.ExternalVerification269ModularMinors
