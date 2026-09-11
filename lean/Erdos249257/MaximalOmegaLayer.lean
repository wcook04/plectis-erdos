import Erdos249257.SupportSunflowerDichotomy
import Mathlib.Tactic

/-!
# Mixed prime-power support layers

This file extends the exact one-prime-power layer already proved in
`SupportSunflowerDichotomy` to the first genuinely mixed case.  The result is
finite coefficient algebra only: it supplies no transport from rationality
through multiplicative decimation and asserts no bounded-`Ω` endpoint.
-/

namespace Erdos249257.MaximalOmegaLayer

open Erdos249257.SupportDilationDifferences
open Erdos249257.SupportSunflowerDichotomy

/-- The signed coefficient layer between exact `p`-adic levels `e-1` and `e`.-/
def primePowerLayer (p e : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g (p ^ e * n) - g (p ^ (e - 1) * n)

/-- The two-signature mixed layer.  Further list-level iteration can use this
as its checked algebraic step without committing to a factorization API. -/
def mixedPrimePowerLayerTwo
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  primePowerLayer q f (primePowerLayer p e g) n

/-- Prime-power layer operators commute as integer finite differences. -/
theorem primePowerLayer_comm
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) :
    primePowerLayer q f (primePowerLayer p e g) n =
      primePowerLayer p e (primePowerLayer q f g) n := by
  simp only [primePowerLayer]
  ring_nf

/-- Two distinct exact prime-power layers extract the iterated exact-valuation
pullback.  This is the mixed repeated-prime algebra missing from the
distinct-prime dilation owner. -/
theorem mixedPrimePowerLayerTwo_supportCoeffInt
    (A : Set ℕ) {p e q f n : ℕ}
    (hp : p.Prime) (he : 0 < e) (hq : q.Prime) (hf : 0 < f)
    (hpq : p ≠ q) (hn : n.Coprime (p * q)) :
    mixedPrimePowerLayerTwo p e q f (supportCoeffInt A) n =
      supportCoeffInt
        (exactPrimePowerPullback q f (exactPrimePowerPullback p e A)) n := by
  have hnp : n.Coprime p :=
    Nat.Coprime.of_dvd_right (dvd_mul_right p q) hn
  have hnq : n.Coprime q :=
    Nat.Coprime.of_dvd_right (dvd_mul_left q p) hn
  have hqp : q.Coprime p :=
    (Nat.coprime_primes hq hp).mpr hpq.symm
  have hqfp : (q ^ f).Coprime p := hqp.pow_left f
  have hqpredp : (q ^ (f - 1)).Coprime p := hqp.pow_left (f - 1)
  have hqfnp : (q ^ f * n).Coprime p := hqfp.mul_left hnp
  have hqprednp : (q ^ (f - 1) * n).Coprime p :=
    hqpredp.mul_left hnp
  unfold mixedPrimePowerLayerTwo primePowerLayer
  rw [supportCoeffInt_prime_power_layer A hp he hqfnp,
    supportCoeffInt_prime_power_layer A hp he hqprednp,
    supportCoeffInt_prime_power_layer
      (exactPrimePowerPullback p e A) hq hf hnq]

/-- Regression for the mixed `2^2`/`3` signature: the singleton support
`{12}` contributes exactly one at residual argument `1`. -/
theorem mixedPrimePowerLayerTwo_twelve_fixture :
    mixedPrimePowerLayerTwo 2 2 3 1
      (supportCoeffInt ({12} : Set ℕ)) 1 = 1 := by
  rw [mixedPrimePowerLayerTwo_supportCoeffInt ({12} : Set ℕ)
    (p := 2) (e := 2) (q := 3) (f := 1) (n := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  norm_num [supportCoeffInt, exactPrimePowerPullback,
    supportCoeff_eq_card_filter]
  decide

#print axioms primePowerLayer_comm
#print axioms mixedPrimePowerLayerTwo_supportCoeffInt
#print axioms mixedPrimePowerLayerTwo_twelve_fixture

end Erdos249257.MaximalOmegaLayer
