import Mathlib.Tactic

/-!
# Erdős #1041: the first-nonzero-mode model

The near-Fekete homogeneous model on an `n`-th-root ray is

`t^m * p - t^n`,

where `p = Re (A * omega^(m*j))`.  A nonpositive phase coefficient makes the
whole ray strictly safe away from the origin.  The companion arithmetic lemma
checks that the phase-orbit lower bound `d * floor(q/2)` is at least two when
`n=d*q >= 4` and `q>=2`.

The geometric fact that a closed half-plane contains at least `floor(q/2)`
equally spaced `q`-th roots is proved in the accompanying analytic note.  This
module checks the two load-bearing consumers without importing complex
analysis or trigonometric counting machinery.
-/

namespace ErdosProblems.Erdos1041.FormACutFirstNonzeroMode

/-- The real value of the two-homogeneous model on one root ray. -/
def modelRay (n m : ℕ) (p t : ℝ) : ℝ := t ^ m * p - t ^ n

/-- A nonpositive phase coefficient keeps the model ray in the closed
sublevel, including at the origin. -/
theorem modelRay_nonpos {n m : ℕ} {p t : ℝ}
    (ht : 0 ≤ t) (hp : p ≤ 0) : modelRay n m p t ≤ 0 := by
  unfold modelRay
  have hleft : t ^ m * p ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht m) hp
  have hright : 0 ≤ t ^ n := pow_nonneg ht n
  linarith

/-- Away from the origin the baseline term `-t^n` makes the model ray
strictly safe, even when the phase coefficient itself vanishes. -/
theorem modelRay_strict {n m : ℕ} {p t : ℝ}
    (ht : 0 < t) (hp : p ≤ 0) : modelRay n m p t < 0 := by
  unfold modelRay
  have hleft : t ^ m * p ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (le_of_lt ht) m) hp
  have hright : 0 < t ^ n := pow_pos ht n
  linarith

/-- Two distinct nonpositive phase coefficients give two strict model spokes. -/
theorem two_modelRays_strict {ι : Type*} {n m : ℕ} {p : ι → ℝ} {i j : ι}
    (hij : i ≠ j) (hi : p i ≤ 0) (hj : p j ≤ 0) :
    i ≠ j ∧
      (∀ t : ℝ, 0 < t → modelRay n m (p i) t < 0) ∧
      (∀ t : ℝ, 0 < t → modelRay n m (p j) t < 0) := by
  refine ⟨hij, ?_, ?_⟩
  · intro t ht
    exact modelRay_strict ht hi
  · intro t ht
    exact modelRay_strict ht hj

/-- The arithmetic behind the sharp degree threshold.  If the mode orbit has
`q` distinct phases, each repeated `d` times, then its closed-half-plane supply
is `d * floor(q/2)`.  Under `n=d*q >= 4` this supply is at least two. -/
theorem two_le_mode_halfplane_supply {n d q : ℕ}
    (hn : 4 ≤ n) (hd : 1 ≤ d) (hq : 2 ≤ q) (hfactor : n = d * q) :
    2 ≤ d * (q / 2) := by
  by_cases hq4 : 4 ≤ q
  · have hhalf : 2 ≤ q / 2 := by omega
    calc
      2 ≤ q / 2 := hhalf
      _ = 1 * (q / 2) := by simp
      _ ≤ d * (q / 2) := Nat.mul_le_mul_right (q / 2) hd
  · have hq_cases : q = 2 ∨ q = 3 := by omega
    rcases hq_cases with rfl | rfl
    · simp at hfactor ⊢
      omega
    · simp at hfactor ⊢
      omega

end ErdosProblems.Erdos1041.FormACutFirstNonzeroMode
