import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring

/-!
# Erdős #243: reciprocal-tail rigidity

This module owns the exact centered integer dynamics behind the rational case.
It proves the algebraic defect identity and the well-founded stabilization step:
if the centered errors are eventually nonnegative, the natural tail state is
nonincreasing and the errors eventually vanish.

It does not settle the unrestricted problem, whose live obstruction is an
integer centered state that may be negative infinitely often.
-/

namespace ErdosProblems.Erdos243

/-- The Sylvester successor `a² - a + 1`, expressed in a ring. -/
def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

/-- Product-cleared denominator update `Dₙ₊₁ = aₙ Dₙ`. -/
def nextDenState (a D : ℤ) : ℤ :=
  a * D

/-- Product-cleared reciprocal-tail update `Cₙ₊₁ = aₙ Cₙ - Dₙ`. -/
def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D

/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. -/
def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

/-- The next denominator defect from the Sylvester step. -/
def sylvesterDefect (a aNext : ℤ) : ℤ :=
  aNext - sylvesterNext a

/-- The tail update is exactly `Cₙ₊₁ = Cₙ - Eₙ`. -/
theorem nextTailState_eq_sub_centered (a D C : ℤ) :
    nextTailState a D C = C - centeredState a D C := by
  simp [nextTailState, centeredState]
  ring

/-! The entire integer-state system is equivariant under a common scale.  This
removes a large family of duplicate constant-negative-state searches. -/

@[simp] theorem nextDenState_scale (s a D : ℤ) :
    nextDenState a (s * D) = s * nextDenState a D := by
  simp [nextDenState]
  ring

@[simp] theorem nextTailState_scale (s a D C : ℤ) :
    nextTailState a (s * D) (s * C) = s * nextTailState a D C := by
  simp [nextTailState]
  ring

@[simp] theorem centeredState_scale (s a D C : ℤ) :
    centeredState a (s * D) (s * C) = s * centeredState a D C := by
  simp [centeredState]
  ring

/-- Exact defect equation:
`Δₙ Cₙ₊₁ = aₙ² Eₙ - Eₙ₊₁`. -/
theorem sylvesterDefect_mul_nextTailState
    (a aNext D C : ℤ) :
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C) := by
  simp [sylvesterDefect, sylvesterNext, nextTailState, nextDenState,
    centeredState]
  ring

/-- If two consecutive centered errors vanish and the next tail state is
nonzero, the defect identity forces the original denominator sequence to take
the exact Sylvester step. -/
theorem sylvesterNext_eq_of_centered_zero
    (a aNext D C : ℤ)
    (hCnext : nextTailState a D C ≠ 0)
    (hE : centeredState a D C = 0)
    (hEnext :
      centeredState aNext (nextDenState a D) (nextTailState a D C) = 0) :
    aNext = sylvesterNext a := by
  have hdefect := sylvesterDefect_mul_nextTailState a aNext D C
  rw [hE, hEnext] at hdefect
  simp only [mul_zero, sub_zero] at hdefect
  have hzero : sylvesterDefect a aNext = 0 :=
    (mul_eq_zero.mp hdefect).resolve_right hCnext
  rw [sylvesterDefect] at hzero
  exact sub_eq_zero.mp hzero

/-- Along an exact product-cleared tail orbit, eventual vanishing of the
centered state and eventual nonvanishing of the next tail force the exact
Sylvester recurrence from some index onward. -/
theorem sylvesterNext_eventually_of_centered_zero
    (a D C : ℕ → ℤ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, C (n + 1) = nextTailState (a n) (D n) (C n))
    (hE : ∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0)
    (hCne : ∃ N, ∀ n, N ≤ n → C (n + 1) ≠ 0) :
    ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := by
  obtain ⟨NE, hE⟩ := hE
  obtain ⟨NC, hCne⟩ := hCne
  refine ⟨max NE NC, fun n hn ↦ ?_⟩
  have hnE : NE ≤ n := (Nat.le_max_left NE NC).trans hn
  have hnC : NC ≤ n := (Nat.le_max_right NE NC).trans hn
  apply sylvesterNext_eq_of_centered_zero (a n) (a (n + 1)) (D n) (C n)
  · rw [← hC n]
    exact hCne n hnC
  · exact hE n hnE
  · rw [← hD n, ← hC n]
    exact hE (n + 1) (hnE.trans (Nat.le_succ n))

/-- Every nonincreasing sequence of naturals is eventually constant. -/
theorem antitone_nat_eventually_constant
    (C : ℕ → ℕ) (hstep : ∀ n, C (n + 1) ≤ C n) :
    ∃ N, ∀ n, N ≤ n → C n = C N := by
  classical
  let P : ℕ → Prop := fun m => ∃ n, C n = m
  have hP : ∃ m, P m := ⟨C 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.find_spec hP
  have hanti : Antitone C := antitone_nat_of_succ_le hstep
  refine ⟨N, fun n hn => ?_⟩
  have hle : C n ≤ C N := hanti hn
  have hmin : C N ≤ C n := by
    rw [hN]
    exact Nat.find_min' hP ⟨n, rfl⟩
  exact Nat.le_antisymm hle hmin

/-- The positive-integer stabilization step used by every one-sided #243
criterion. If `Cₙ₊₁ + Eₙ = Cₙ`, then the nonnegative errors vanish
eventually. -/
theorem centeredState_eventually_zero
    (C E : ℕ → ℕ) (hrec : ∀ n, C (n + 1) + E n = C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  have hstep : ∀ n, C (n + 1) ≤ C n := fun n => by
    have := hrec n
    omega
  obtain ⟨N, hconst⟩ := antitone_nat_eventually_constant C hstep
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : N ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hsame : C (n + 1) = C n :=
    (hconst (n + 1) hn1).trans (hconst n hn).symm
  have := hrec n
  omega

end ErdosProblems.Erdos243
