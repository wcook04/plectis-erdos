import Mathlib.Tactic

/-!
# Erdős #269: bounded-radix tail escape

Consider an affine orbit
`x (n + 1) = P n * x n - c n` with integral `c n` and radices
`2 ≤ P n ≤ B`.  If the orbit is eventually always within `1/(B+1)` of an
integer, the corresponding errors grow by at least a factor of two at every
step; hence one of the states is itself integral.  Otherwise the orbit is at
least `1/(B+1)` from every integer at arbitrarily late indices.

The threshold is attained: at constant radix `B` and digit sequence
alternating `0, B - 1`, the rational orbit alternating `1/(B+1)` and
`B/(B+1)` is never integral and stays exactly `1/(B+1)` from the integers.
That example is rational, so it says nothing about optimality for irrational
orbits.  The first public statement fixed `B = 30`, the bound needed by the
dyadic height ratios of #269; `boundedRadix_zero_or_cofinal_far` keeps that
interface as a specialisation of the parameterised theorem.

The integral state in the first alternative need not be zero.  The theorem
also makes no assertion that the separated indices are eventually all
indices, have positive density, or have unbounded distance from the integers.
-/

namespace ErdosProblems.Erdos269

/-- A real number lies strictly within `δ` of an integer. -/
def NearInteger (x δ : ℝ) : Prop :=
  ∃ z : ℤ, |x - (z : ℝ)| < δ

/-- A real number is at least `δ` from every integer. -/
def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|

/-- Two consecutive `1/(B+1)`-near-integer witnesses in an affine step of
integer radix at most `B` must obey the same affine integer recurrence. -/
theorem affine_nearInteger_alignment_of_le
    {B P : ℕ} {x y : ℝ} {c m n : ℤ}
    (hP : P ≤ B)
    (hrec : y = (P : ℝ) * x - (c : ℝ))
    (hx : |x - (m : ℝ)| < 1 / ((B : ℝ) + 1))
    (hy : |y - (n : ℝ)| < 1 / ((B : ℝ) + 1)) :
    n = (P : ℤ) * m - c := by
  let k : ℤ := (P : ℤ) * m - c - n
  have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  have hk_cast :
      (k : ℝ) = (y - (n : ℝ)) - (P : ℝ) * (x - (m : ℝ)) := by
    dsimp [k]
    rw [hrec]
    push_cast
    ring
  have hmul :
      |(P : ℝ) * (x - (m : ℝ))| ≤
        (P : ℝ) * (1 / ((B : ℝ) + 1)) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg P)]
    exact mul_le_mul_of_nonneg_left (le_of_lt hx) (Nat.cast_nonneg P)
  have hk_lt : |(k : ℝ)| < 1 := by
    rw [hk_cast]
    calc
      |(y - (n : ℝ)) - (P : ℝ) * (x - (m : ℝ))| ≤
          |y - (n : ℝ)| + |(P : ℝ) * (x - (m : ℝ))| :=
        abs_sub _ _
      _ < 1 / ((B : ℝ) + 1) + (P : ℝ) * (1 / ((B : ℝ) + 1)) :=
        add_lt_add_of_lt_of_le hy hmul
      _ ≤ 1 := by
        have hP' : (P : ℝ) ≤ B := by exact_mod_cast hP
        rw [show 1 / ((B : ℝ) + 1) + (P : ℝ) * (1 / ((B : ℝ) + 1)) =
            ((P : ℝ) + 1) / ((B : ℝ) + 1) by ring]
        rw [div_le_iff₀ hB1]
        linarith
  have hk_zero : k = 0 := by
    have hlo : (-1 : ℝ) < (k : ℝ) := (abs_lt.mp hk_lt).1
    have hhi : (k : ℝ) < 1 := (abs_lt.mp hk_lt).2
    have hlo' : (-1 : ℤ) < k := by exact_mod_cast hlo
    have hhi' : k < (1 : ℤ) := by exact_mod_cast hhi
    omega
  dsimp [k] at hk_zero
  omega

/-- The `1/31` threshold is `1/(B+1)` at `B = 30`. -/
theorem one_div_thirtyOne_eq : (1 : ℝ) / 31 = 1 / (((30 : ℕ) : ℝ) + 1) := by
  norm_num

/-- Two consecutive `1/31`-near-integer witnesses in an affine step of
integer radix at most `30` must obey the same affine integer recurrence. -/
theorem affine_nearInteger_alignment
    {P : ℕ} {x y : ℝ} {c m n : ℤ}
    (hP : P ≤ 30)
    (hrec : y = (P : ℝ) * x - (c : ℝ))
    (hx : |x - (m : ℝ)| < (1 : ℝ) / 31)
    (hy : |y - (n : ℝ)| < (1 : ℝ) / 31) :
    n = (P : ℤ) * m - c := by
  rw [one_div_thirtyOne_eq] at hx hy
  exact affine_nearInteger_alignment_of_le hP hrec hx hy

/-- Once the integer witnesses align, the signed errors multiply exactly by
the radix. -/
theorem affine_nearInteger_error_mul
    {P : ℕ} {x y : ℝ} {c m n : ℤ}
    (hrec : y = (P : ℝ) * x - (c : ℝ))
    (halign : n = (P : ℤ) * m - c) :
    y - (n : ℝ) = (P : ℝ) * (x - (m : ℝ)) := by
  rw [hrec, halign]
  push_cast
  ring

/-- A real affine orbit with integral digits and radices in `[2,B]` either
has an integral state or returns cofinally often to distance at least
`1/(B+1)` from every integer. -/
theorem boundedRadix_zero_or_cofinal_far_of_le
    (B : ℕ) (P : ℕ → ℕ) (c : ℕ → ℤ) (x : ℕ → ℝ)
    (hPlo : ∀ a, 2 ≤ P a)
    (hPhi : ∀ a, P a ≤ B)
    (hrec :
      ∀ a, x (a + 1) =
        (P a : ℝ) * x a - (c a : ℝ)) :
    (∃ a : ℕ, ∃ z : ℤ, x a = (z : ℝ)) ∨
      ∀ a₀, ∃ a, a₀ ≤ a ∧
        FarFromIntegers (x a) (1 / ((B : ℝ) + 1)) := by
  classical
  by_cases hescape :
      ∀ a₀, ∃ a, a₀ ≤ a ∧
        FarFromIntegers (x a) (1 / ((B : ℝ) + 1))
  · exact Or.inr hescape
  · left
    push Not at hescape
    rcases hescape with ⟨a₀, hclose⟩
    have hnear : ∀ k : ℕ,
        NearInteger (x (a₀ + k)) (1 / ((B : ℝ) + 1)) := by
      intro k
      have hnfar := hclose (a₀ + k) (Nat.le_add_right a₀ k)
      unfold FarFromIntegers at hnfar
      simp only [not_forall] at hnfar
      rcases hnfar with ⟨z, hz⟩
      exact ⟨z, lt_of_not_ge hz⟩
    let m : ℕ → ℤ := fun k => Classical.choose (hnear k)
    have hm (k : ℕ) :
        |x (a₀ + k) - (m k : ℝ)| < 1 / ((B : ℝ) + 1) :=
      Classical.choose_spec (hnear k)
    have herr (k : ℕ) :
        x (a₀ + (k + 1)) - (m (k + 1) : ℝ) =
          (P (a₀ + k) : ℝ) *
            (x (a₀ + k) - (m k : ℝ)) := by
      have hindex : a₀ + (k + 1) = (a₀ + k) + 1 := by omega
      have halign : m (k + 1) =
          (P (a₀ + k) : ℤ) * m k - c (a₀ + k) := by
        apply affine_nearInteger_alignment_of_le (hPhi (a₀ + k))
          (hrec (a₀ + k))
        · exact hm k
        · rw [← hindex]
          exact hm (k + 1)
      rw [hindex]
      exact affine_nearInteger_error_mul (hrec (a₀ + k)) halign
    have hgrow (k : ℕ) :
        (2 : ℝ) ^ k * |x a₀ - (m 0 : ℝ)| ≤
          |x (a₀ + k) - (m k : ℝ)| := by
      induction k with
      | zero => simp
      | succ k ih =>
          have htwoP : (2 : ℝ) ≤ P (a₀ + k) := by
            exact_mod_cast hPlo (a₀ + k)
          calc
            (2 : ℝ) ^ (k + 1) * |x a₀ - (m 0 : ℝ)| =
                2 * ((2 : ℝ) ^ k * |x a₀ - (m 0 : ℝ)|) := by
                  rw [pow_succ]
                  ring
            _ ≤ 2 * |x (a₀ + k) - (m k : ℝ)| :=
              mul_le_mul_of_nonneg_left ih (by norm_num)
            _ ≤ (P (a₀ + k) : ℝ) *
                |x (a₀ + k) - (m k : ℝ)| :=
              mul_le_mul_of_nonneg_right htwoP (abs_nonneg _)
            _ = |x (a₀ + (k + 1)) - (m (k + 1) : ℝ)| := by
              have habsP :
                  |(P (a₀ + k) : ℝ)| = (P (a₀ + k) : ℝ) :=
                abs_of_nonneg (Nat.cast_nonneg (P (a₀ + k)))
              calc
                (P (a₀ + k) : ℝ) *
                    |x (a₀ + k) - (m k : ℝ)| =
                    |(P (a₀ + k) : ℝ)| *
                      |x (a₀ + k) - (m k : ℝ)| := by
                        rw [habsP]
                _ = |(P (a₀ + k) : ℝ) *
                    (x (a₀ + k) - (m k : ℝ))| := (abs_mul _ _).symm
                _ = |x (a₀ + (k + 1)) - (m (k + 1) : ℝ)| := by
                  rw [herr k]
    have hzero : x a₀ - (m 0 : ℝ) = 0 := by
      by_contra hne
      have habs : 0 < |x a₀ - (m 0 : ℝ)| := abs_pos.mpr hne
      obtain ⟨k, hk⟩ :=
        pow_unbounded_of_one_lt
          ((1 / ((B : ℝ) + 1)) / |x a₀ - (m 0 : ℝ)|)
          (by norm_num : (1 : ℝ) < 2)
      have hlarge :
          1 / ((B : ℝ) + 1) <
            (2 : ℝ) ^ k * |x a₀ - (m 0 : ℝ)| := by
        exact (div_lt_iff₀ habs).mp hk
      have := hgrow k
      have := hm k
      nlinarith
    exact ⟨a₀, m 0, by linarith⟩

/-- A real affine orbit with integral digits and radices in `[2,30]` either
has an integral state or returns cofinally often to distance at least `1/31`
from every integer. -/
theorem boundedRadix_zero_or_cofinal_far
    (P : ℕ → ℕ) (c : ℕ → ℤ) (x : ℕ → ℝ)
    (hPlo : ∀ a, 2 ≤ P a)
    (hPhi : ∀ a, P a ≤ 30)
    (hrec :
      ∀ a, x (a + 1) =
        (P a : ℝ) * x a - (c a : ℝ)) :
    (∃ a : ℕ, ∃ z : ℤ, x a = (z : ℝ)) ∨
      ∀ a₀, ∃ a, a₀ ≤ a ∧
        FarFromIntegers (x a) ((1 : ℝ) / 31) := by
  rw [one_div_thirtyOne_eq]
  exact boundedRadix_zero_or_cofinal_far_of_le 30 P c x hPlo hPhi hrec

/-- The threshold `1/(B+1)` of `boundedRadix_zero_or_cofinal_far_of_le`
cannot be raised for the general statement.  At constant radix `B` with
digits alternating `0` and `B - 1`, the orbit alternating `1/(B+1)` and
`1 - 1/(B+1)` has no integral state and stays exactly `1/(B+1)` from the
integers.  The orbit is rational; this says nothing about the best
threshold for irrational orbits. -/
theorem boundedRadix_threshold_attained (B : ℕ) (hB : 2 ≤ B) :
    ∃ c : ℕ → ℤ, ∃ x : ℕ → ℝ,
      (∀ a, x (a + 1) = (B : ℝ) * x a - (c a : ℝ)) ∧
      (∀ a, ∃ z : ℤ, |x a - (z : ℝ)| = 1 / ((B : ℝ) + 1)) ∧
      ∀ a, FarFromIntegers (x a) (1 / ((B : ℝ) + 1)) := by
  set δ : ℝ := 1 / ((B : ℝ) + 1) with hδdef
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by positivity
  have hkey : (B : ℝ) * δ = 1 - δ := by
    rw [hδdef]
    field_simp
    ring
  have hδpos : 0 < δ := by positivity
  have hδhalf : 2 * δ ≤ 1 := by
    rw [hδdef, mul_one_div, div_le_iff₀ hB1]
    linarith
  refine ⟨fun a => if a % 2 = 0 then 0 else (B : ℤ) - 1,
    fun a => if a % 2 = 0 then δ else 1 - δ, ?_, ?_, ?_⟩
  · intro a
    dsimp only
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha
    · rw [if_pos ha, if_neg (by omega : ¬ (a + 1) % 2 = 0), if_pos ha]
      push_cast
      linear_combination -hkey
    · rw [if_neg (by omega : ¬ a % 2 = 0), if_pos (by omega : (a + 1) % 2 = 0),
        if_neg (by omega : ¬ a % 2 = 0)]
      push_cast
      linear_combination hkey
  · intro a
    dsimp only
    by_cases ha : a % 2 = 0
    · refine ⟨0, ?_⟩
      rw [if_pos ha, Int.cast_zero, sub_zero]
      exact abs_of_pos hδpos
    · refine ⟨1, ?_⟩
      rw [if_neg ha, Int.cast_one, show 1 - δ - 1 = -δ by ring, abs_neg]
      exact abs_of_pos hδpos
  · intro a z
    dsimp only
    have hz : (z : ℝ) ≤ 0 ∨ 1 ≤ (z : ℝ) := by
      rcases le_or_gt z 0 with hz | hz
      · exact Or.inl (by exact_mod_cast hz)
      · exact Or.inr (by exact_mod_cast hz)
    by_cases ha : a % 2 = 0
    · rw [if_pos ha]
      rcases hz with hz | hz
      · exact le_abs.mpr (Or.inl (by linarith))
      · exact le_abs.mpr (Or.inr (by linarith))
    · rw [if_neg ha]
      rcases hz with hz | hz
      · exact le_abs.mpr (Or.inl (by linarith))
      · exact le_abs.mpr (Or.inr (by linarith))

/-- Exact cancellation of a nontrivially scaled affine tail forces the source
real number to be rational. -/
theorem rational_of_scaledTail_integer
    {S τ : ℝ} {X A B z : ℤ}
    (hB : B ≠ 0)
    (hX : X ≠ 0)
    (htail : τ = (X : ℝ) * S - (A : ℝ))
    (hint : (B : ℝ) * τ = (z : ℝ)) :
    ∃ q : ℚ, S = q := by
  have hBX : B * X ≠ 0 := mul_ne_zero hB hX
  have hidentity :
      ((B * X : ℤ) : ℝ) * S = ((z + B * A : ℤ) : ℝ) := by
    push_cast
    rw [htail] at hint
    nlinarith
  let q : ℚ := ((z + B * A : ℤ) : ℚ) / ((B * X : ℤ) : ℚ)
  refine ⟨q, ?_⟩
  have hden : (((B * X : ℤ) : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast hBX
  rw [show (q : ℝ) =
      (((z + B * A : ℤ) : ℚ) : ℝ) /
        (((B * X : ℤ) : ℚ) : ℝ) by
      simp [q]]
  apply (eq_div_iff hden).2
  simpa [mul_comm] using hidentity

end ErdosProblems.Erdos269
