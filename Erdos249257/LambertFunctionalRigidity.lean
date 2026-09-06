import Erdos249257.MersenneLambertLadder

/-!
# Functional rigidity of Lambert Booleanisation

The coefficient of `r^n` in the formal Lambert series attached to an
arithmetic weight `c` is `(c * zeta) n`.  Convolution by `zeta` is injective,
because convolution by the Möbius function is its inverse.  Hence a Boolean
weight can agree with a source Lambert series at every coefficient only when
the source weight was already Boolean.

This separates a genuine Lambert-series normalisation from an equality that
holds only at the single point `r = 1 / 2`.
-/

namespace Erdos249257
namespace LambertFunctionalRigidity

open scoped ArithmeticFunction.Moebius

abbrev zetaZ : ArithmeticFunction ℤ :=
  (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)

/-- An integer arithmetic function is Boolean on every positive index. -/
def IsBooleanWeight (b : ArithmeticFunction ℤ) : Prop :=
  ∀ n : ℕ, 0 < n → b n = 0 ∨ b n = 1

/-- **Formal Lambert rigidity.**  Convolution by `zeta`, equivalently passage
from source weights to formal Lambert coefficients, is injective. -/
theorem mul_zeta_injective :
    Function.Injective (fun c : ArithmeticFunction ℤ => c * zetaZ) := by
  intro c b hcoeff
  change c * zetaZ = b * zetaZ at hcoeff
  calc
    c = 1 * c := by rw [one_mul]
    _ = (ArithmeticFunction.moebius * zetaZ) * c := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = ArithmeticFunction.moebius * (c * zetaZ) := by
      ac_rfl
    _ = ArithmeticFunction.moebius * (b * zetaZ) := by rw [hcoeff]
    _ = (ArithmeticFunction.moebius * zetaZ) * b := by
      ac_rfl
    _ = 1 * b := by rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = b := by rw [one_mul]

/-- The signed Möbius Lambert identity cannot be preserved coefficientwise
by any Boolean arithmetic weight. -/
theorem no_boolean_formal_lambert_moebius :
    ¬ ∃ b : ArithmeticFunction ℤ,
      IsBooleanWeight b ∧
        ArithmeticFunction.moebius * zetaZ = b * zetaZ := by
  rintro ⟨b, hbool, hcoeff⟩
  have hrigid : ArithmeticFunction.moebius = b :=
    mul_zeta_injective hcoeff
  have htwo := congrArg (fun f : ArithmeticFunction ℤ => f 2) hrigid
  change ArithmeticFunction.moebius 2 = b 2 at htwo
  rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two] at htwo
  rcases hbool 2 (by omega) with hzero | hone <;> omega

/-- The totient Lambert identity cannot be preserved coefficientwise by any
Boolean arithmetic weight: its source coefficient at `3` is `2`. -/
theorem no_boolean_formal_lambert_totient :
    ¬ ∃ b : ArithmeticFunction ℤ,
      IsBooleanWeight b ∧
        MersenneLambertLadder.totientZ * zetaZ = b * zetaZ := by
  rintro ⟨b, hbool, hcoeff⟩
  have hrigid : MersenneLambertLadder.totientZ = b :=
    mul_zeta_injective hcoeff
  have hthree := congrArg (fun f : ArithmeticFunction ℤ => f 3) hrigid
  change MersenneLambertLadder.totientZ 3 = b 3 at hthree
  have hvalue : MersenneLambertLadder.totientZ 3 = 2 := by
    rw [MersenneLambertLadder.totientZ_apply,
      Nat.totient_prime (by decide : Nat.Prime 3)]
    norm_num
  rw [hvalue] at hthree
  rcases hbool 3 (by omega) with hzero | hone <;> omega

/-- The primitive-conductor Lambert identity cannot be preserved
coefficientwise by any Boolean arithmetic weight: its source coefficient at
`5` is `5 - 2 = 3`. -/
theorem no_boolean_formal_lambert_primWeight :
    ¬ ∃ b : ArithmeticFunction ℤ,
      IsBooleanWeight b ∧
        MersenneLambertLadder.primWeight * zetaZ = b * zetaZ := by
  rintro ⟨b, hbool, hcoeff⟩
  have hrigid : MersenneLambertLadder.primWeight = b :=
    mul_zeta_injective hcoeff
  have hfive := congrArg (fun f : ArithmeticFunction ℤ => f 5) hrigid
  change MersenneLambertLadder.primWeight 5 = b 5 at hfive
  have hp : Nat.Prime 5 := by decide
  rw [MersenneLambertLadder.primWeight_apply_prime hp] at hfive
  norm_num at hfive
  rcases hbool 5 (by omega) with hzero | hone <;> omega

#print axioms mul_zeta_injective
#print axioms no_boolean_formal_lambert_moebius
#print axioms no_boolean_formal_lambert_totient
#print axioms no_boolean_formal_lambert_primWeight

end LambertFunctionalRigidity
end Erdos249257
