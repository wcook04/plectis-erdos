import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Erdős #1041: all-branch fibre product kernel

The companion note proves the resultant identity and complete Lagrange moment
system.  This module checks the half-plane contraction consumer and an exact
countermodel to extracting a marked-pair arithmetic bound from product plus
zero-sum data alone.
-/

namespace ErdosProblems.Erdos1041.TiedNewtonFaceFibreProduct

open scoped BigOperators

noncomputable section

def factorSq (r : ℝ) (u : ℂ) : ℝ :=
  r^2 / Complex.normSq ((r : ℂ)-u)

theorem normSq_real_sub_ge {r : ℝ} (hr : 0 ≤ r) {u : ℂ} (hu : u.re ≤ 0) :
    r^2 ≤ Complex.normSq ((r : ℂ)-u) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
    Complex.sub_im, Complex.ofReal_im, zero_sub]
  nlinarith [sq_nonneg u.im]

theorem normSq_real_sub_pos {r : ℝ} (hr : 0 < r) {u : ℂ} (hu : u.re ≤ 0) :
    0 < Complex.normSq ((r : ℂ)-u) := by
  have h := normSq_real_sub_ge (le_of_lt hr) hu
  nlinarith

theorem factorSq_nonneg (r : ℝ) (u : ℂ) : 0 ≤ factorSq r u := by
  dsimp [factorSq]
  exact div_nonneg (sq_nonneg r) (Complex.normSq_nonneg _)

theorem factorSq_le_one {r : ℝ} (hr : 0 < r) {u : ℂ} (hu : u.re ≤ 0) :
    factorSq r u ≤ 1 := by
  dsimp [factorSq]
  exact (div_le_one (normSq_real_sub_pos hr hu)).mpr
    (normSq_real_sub_ge (le_of_lt hr) hu)

theorem prod_factorSq_le_one {r : ℝ} (hr : 0 < r) {m : ℕ}
    (u : Fin m → ℂ) (hu : ∀ k, (u k).re ≤ 0) :
    ∏ k, factorSq r (u k) ≤ 1 := by
  apply Finset.prod_le_one
  · intro k _
    exact factorSq_nonneg r (u k)
  · intro k _
    exact factorSq_le_one hr (hu k)

/-- Any independently established resultant identity in squared norms feeds
directly into the half-plane product contraction. -/
theorem speedProductSq_le_one_of_identity {r speedProductSq : ℝ}
    (hr : 0 < r) {m : ℕ} (u : Fin m → ℂ)
    (hu : ∀ k, (u k).re ≤ 0)
    (hid : speedProductSq = ∏ k, factorSq r (u k)) :
    speedProductSq ≤ 1 := by
  rw [hid]
  exact prod_factorSq_le_one hr u hu

/-- Product contraction plus the first velocity-moment cancellation does not
control the arithmetic sum of a marked pair. -/
theorem zeroSum_product_countermodel :
    (2 : ℝ) + 2 + (-4) + (1/10) + (-1/10) = 0 ∧
    |(2 : ℝ)| * |(2 : ℝ)| * |(-4 : ℝ)| * |(1/10 : ℝ)| * |(-1/10 : ℝ)|
      = 4/25 ∧
    |(2 : ℝ)| + |(2 : ℝ)| > 2 := by
  norm_num

end

end ErdosProblems.Erdos1041.TiedNewtonFaceFibreProduct
