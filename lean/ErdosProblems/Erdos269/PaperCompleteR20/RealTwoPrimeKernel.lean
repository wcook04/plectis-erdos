import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Two-generator separation for arbitrary real bases

The long paper allows real generators greater than one. Integer floors and
integer powers retain that literal domain, including nonintegral bases.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

noncomputable section

def realTwoPrimeHeight (p q t : ℝ) : ℝ :=
  p ^ ⌊Real.logb p t⌋ * q ^ ⌊Real.logb q t⌋

def realTwoPrimeKernel (p q : ℝ) (i j : ℕ) : ℝ :=
  (realTwoPrimeHeight p q (p ^ i * q ^ j))⁻¹

theorem floor_logb_two_powers_left {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (i j : ℕ) :
    ⌊Real.logb p (p ^ i * q ^ j)⌋ = (i : ℤ) + ⌊Real.logb p (q ^ j)⌋ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  rw [Real.logb_mul (pow_ne_zero i hp0) (pow_ne_zero j hq0),
    Real.logb_pow p p i, Real.logb_self_eq_one hp, mul_one,
    Int.floor_natCast_add]

theorem floor_logb_two_powers_right {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (i j : ℕ) :
    ⌊Real.logb q (p ^ i * q ^ j)⌋ = ⌊Real.logb q (p ^ i)⌋ + (j : ℤ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  rw [Real.logb_mul (pow_ne_zero i hp0) (pow_ne_zero j hq0),
    Real.logb_pow q q j, Real.logb_self_eq_one hq, mul_one,
    Int.floor_add_natCast]

/-- The literal outer-product identity for every real pair of bases above one. -/
theorem realTwoPrimeKernel_eq_outer_product {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (i j : ℕ) :
    realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  unfold realTwoPrimeKernel realTwoPrimeHeight
  rw [floor_logb_two_powers_left hp hq, floor_logb_two_powers_right hp hq,
    zpow_add₀ hp0, zpow_add₀ hq0]
  simp only [zpow_natCast, mul_inv_rev]
  ring

/-- All two-by-two minors vanish, with no integrality assumption on the bases. -/
theorem realTwoPrimeKernel_minor_two_eq_zero {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (i i' j j' : ℕ) :
    realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
      realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0 := by
  simp only [realTwoPrimeKernel_eq_outer_product hp hq]
  ring

/-- Both clauses of the long paper's real-generator rank proposition. -/
theorem real_two_prime_separation {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    (∀ i j : ℕ, realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹) ∧
    (∀ i i' j j' : ℕ,
      realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
        realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0) :=
  ⟨realTwoPrimeKernel_eq_outer_product hp hq,
    realTwoPrimeKernel_minor_two_eq_zero hp hq⟩

#print axioms real_two_prime_separation

end

end ErdosProblems.Erdos269.PaperCompleteR20
