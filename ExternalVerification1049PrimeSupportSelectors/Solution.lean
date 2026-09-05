/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1049.QAperyTailDenominator

namespace Erdos249257.ExternalVerification1049PrimeSupportSelectors

open Filter

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
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| :=
  ErdosProblems.Erdos1049.rational_twoSelector_gap_of_prime_tail_support
    hell a q A₁ B₁ A₂ B₂ hq hellq hellB₁ hellB₂ hdet

theorem rationalTwoSelector_notBothTendstoZero
    (a q : ℤ) (hq : 0 < q)
    (A₁ B₁ A₂ B₂ : ℕ → ℤ)
    (hdet : ∀ n, A₁ n * B₂ n - A₂ n * B₁ n ≠ 0) :
    ¬(Tendsto
        (fun n ↦ (B₁ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ n : ℝ))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ (B₂ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ n : ℝ))
        atTop (nhds 0)) :=
  ErdosProblems.Erdos1049.rational_twoSelector_not_both_tendsto_zero
    a q hq A₁ B₁ A₂ B₂ hdet

theorem primeSupportedOneRow_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ) (hq : 0 < q)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| :=
  ErdosProblems.Erdos1049.rational_integerLinearForm_gap_of_prime_support
    hell a q A B hq hellB hellA hellq

theorem primePowerSupportedOneRow_rationalGap
    {ell r : ℕ} (hell : ell.Prime) (hr : r ≠ 0)
    (a q A B : ℤ) (hq : 0 < q)
    (hellPowB : (ell : ℤ) ^ r ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| :=
  ErdosProblems.Erdos1049.rational_integerLinearForm_gap_of_prime_power_support
    hell hr a q A B hq hellPowB hellA hellq

theorem twoSelector_unimodularHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ u v w z F H ε : ℝ)
    (hunimod : |u * z - v * w| = 1)
    (hε : 0 ≤ ε)
    (hu : |u| ≤ H) (hv : |v| ≤ H) (hw : |w| ≤ H) (hz : |z| ≤ H)
    (h₁ : |(u * B₁ + v * B₂) * F - (u * A₁ + v * A₂)| ≤ ε)
    (h₂ : |(w * B₁ + z * B₂) * F - (w * A₁ + z * A₂)| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤
      2 * H * ε * (|B₁| + |B₂|) :=
  ErdosProblems.Erdos1049.twoSelector_unimodular_height_decay_tradeoff
    A₁ B₁ A₂ B₂ u v w z F H ε hunimod hε hu hv hw hz h₁ h₂

theorem zeroDenominatorCoordinates_binaryCollision
    {N k : ℕ} [NeZero N]
    (w : Fin k → ZMod N × ZMod N)
    (hzero : ∀ i, (w i).2 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 :=
  ErdosProblems.Erdos1049.zmod_binary_collision_of_zero_denominator_coordinates
    w hzero hcard

end Erdos249257.ExternalVerification1049PrimeSupportSelectors
