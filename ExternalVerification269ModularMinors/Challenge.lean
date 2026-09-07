/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #269 admissible modular minors

For `(p,q,r) = (2,3,5)` write `H(x)` for the product of the largest pure `2`-,
`3`- and `5`-powers not exceeding `x`, and attach to the exponent vector
`(i,j,k)` the kernel value `H(2^i 3^j 5^k)⁻¹`.

The compared theorem produces, for every order `n`, one pair of injective index
maps `I, J` that works simultaneously for three things: the rational minor is
nonzero at every layer `k`, the same minor reduced modulo `B` is a unit for
every `B ≥ 2` coprime to `30` and every layer, and the reduced matrix itself is
invertible. The index maps are chosen before the modulus and before the layer,
which is the content of the phrase "the maps in Theorem 1" on the page.

Reduction is taken as the inverse of the natural height in `ZMod B`. There is no
ring map from the rationals to `ZMod B` and none is used.

This is a rank and invertibility statement about the kernel. It supplies no
irrationality argument and does not settle Erdős Problem 269, which remains open.
-/

namespace Erdos249257.ExternalVerification269ModularMinors

/-- The `{2,3,5}`-smooth value of an exponent vector. -/
def smoothVal235 (i j k : ℕ) : ℕ := 2 ^ i * 3 ^ j * 5 ^ k

/-- The running-LCM height at `{2,3,5}`. -/
def height235 (x : ℕ) : ℕ :=
  2 ^ Nat.log 2 x * 3 ^ Nat.log 3 x * 5 ^ Nat.log 5 x

/-- The exact rational kernel. -/
def kernelQ235 (i j k : ℕ) : ℚ := ((height235 (smoothVal235 i j k) : ℕ) : ℚ)⁻¹

/-- The literal reduction: invert the natural height in `ZMod B`. -/
def kernelMod235 (B i j k : ℕ) : ZMod B :=
  ((height235 (smoothVal235 i j k) : ℕ) : ZMod B)⁻¹

/-- One choice of indices giving nonzero rational minors and unit minors modulo
every admissible denominator, at every layer. -/
theorem admissible_modular_minors (n : ℕ) :
    ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧
      (∀ k : ℕ,
        (Matrix.det fun i j : Fin n => kernelQ235 (I i) (J j) k) ≠ 0) ∧
      (∀ B : ℕ, 2 ≤ B → Nat.Coprime B 30 → ∀ k : ℕ,
        IsUnit (Matrix.det fun i j : Fin n => kernelMod235 B (I i) (J j) k) ∧
        IsUnit (Matrix.of fun i j : Fin n => kernelMod235 B (I i) (J j) k)) := sorry

end Erdos249257.ExternalVerification269ModularMinors
