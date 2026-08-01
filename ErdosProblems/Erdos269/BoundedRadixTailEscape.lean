import Mathlib.Tactic

/-!
# Erdős #269: bounded-radix tail escape

Generic real affine-tail rigidity for the bounded one-block radix word.
-/

namespace ErdosProblems.Erdos269

/-- A real number lies strictly within `δ` of an integer. -/
def NearInteger (x δ : ℝ) : Prop :=
  ∃ z : ℤ, |x - (z : ℝ)| < δ

/-- A real number is at least `δ` from every integer. -/
def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|

/-- Two consecutive `1/31`-near-integer witnesses in an affine step of
integer radix at most `30` must obey the same affine integer recurrence. -/
theorem affine_nearInteger_alignment
    {P : ℕ} {x y : ℝ} {c m n : ℤ}
    (hP : P ≤ 30)
    (hrec : y = (P : ℝ) * x - (c : ℝ))
    (hx : |x - (m : ℝ)| < (1 : ℝ) / 31)
    (hy : |y - (n : ℝ)| < (1 : ℝ) / 31) :
    n = (P : ℤ) * m - c := by
  let k : ℤ := (P : ℤ) * m - c - n
  have hk_cast :
      (k : ℝ) = (y - (n : ℝ)) - (P : ℝ) * (x - (m : ℝ)) := by
    dsimp [k]
    rw [hrec]
    push_cast
    ring
  have hmul :
      |(P : ℝ) * (x - (m : ℝ))| ≤
        (P : ℝ) * ((1 : ℝ) / 31) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg P)]
    exact mul_le_mul_of_nonneg_left (le_of_lt hx) (Nat.cast_nonneg P)
  have hk_lt : |(k : ℝ)| < 1 := by
    rw [hk_cast]
    calc
      |(y - (n : ℝ)) - (P : ℝ) * (x - (m : ℝ))| ≤
          |y - (n : ℝ)| + |(P : ℝ) * (x - (m : ℝ))| :=
        abs_sub _ _
      _ < (1 : ℝ) / 31 + (P : ℝ) * ((1 : ℝ) / 31) :=
        add_lt_add_of_lt_of_le hy hmul
      _ ≤ 1 := by
        have hP' : (P : ℝ) ≤ 30 := by exact_mod_cast hP
        have hadd : (P : ℝ) + 1 ≤ 30 + 1 := by linarith
        calc
          (1 : ℝ) / 31 + (P : ℝ) * ((1 : ℝ) / 31) =
              ((P : ℝ) + 1) / 31 := by ring
          _ ≤ (30 + 1 : ℝ) / 31 :=
            div_le_div_of_nonneg_right hadd (by norm_num)
          _ = 1 := by norm_num
  have hk_zero : k = 0 := by
    have hlo : (-1 : ℝ) < (k : ℝ) := (abs_lt.mp hk_lt).1
    have hhi : (k : ℝ) < 1 := (abs_lt.mp hk_lt).2
    have hlo' : (-1 : ℤ) < k := by exact_mod_cast hlo
    have hhi' : k < (1 : ℤ) := by exact_mod_cast hhi
    omega
  dsimp [k] at hk_zero
  omega

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

/-- A real affine orbit with integral digits and radices in `[2,30]` either
hits an integer or returns cofinally often to distance at least `1/31` from
every integer. -/
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
  classical
  by_cases hescape :
      ∀ a₀, ∃ a, a₀ ≤ a ∧
        FarFromIntegers (x a) ((1 : ℝ) / 31)
  · exact Or.inr hescape
  · left
    push Not at hescape
    rcases hescape with ⟨a₀, hclose⟩
    have hnear : ∀ k : ℕ,
        NearInteger (x (a₀ + k)) ((1 : ℝ) / 31) := by
      intro k
      have hnfar := hclose (a₀ + k) (Nat.le_add_right a₀ k)
      unfold FarFromIntegers at hnfar
      simp only [not_forall] at hnfar
      rcases hnfar with ⟨z, hz⟩
      exact ⟨z, lt_of_not_ge hz⟩
    let m : ℕ → ℤ := fun k => Classical.choose (hnear k)
    have hm (k : ℕ) :
        |x (a₀ + k) - (m k : ℝ)| < (1 : ℝ) / 31 :=
      Classical.choose_spec (hnear k)
    have herr (k : ℕ) :
        x (a₀ + (k + 1)) - (m (k + 1) : ℝ) =
          (P (a₀ + k) : ℝ) *
            (x (a₀ + k) - (m k : ℝ)) := by
      have hindex : a₀ + (k + 1) = (a₀ + k) + 1 := by omega
      have halign : m (k + 1) =
          (P (a₀ + k) : ℤ) * m k - c (a₀ + k) := by
        apply affine_nearInteger_alignment (hPhi (a₀ + k))
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
          (((1 : ℝ) / 31) / |x a₀ - (m 0 : ℝ)|)
          (by norm_num : (1 : ℝ) < 2)
      have hlarge :
          (1 : ℝ) / 31 <
            (2 : ℝ) ^ k * |x a₀ - (m 0 : ℝ)| := by
        exact (div_lt_iff₀ habs).mp hk
      have := hgrow k
      have := hm k
      nlinarith
    exact ⟨a₀, m 0, by linarith⟩

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
