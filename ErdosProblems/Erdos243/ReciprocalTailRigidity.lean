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
