import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# Erdős #243: exact finite-horizon residue transport

For the normalized constant-negative obstruction, the forced update at index
`n` has numerator

`(n + 1) a² - (n + 2) a + (n + 3)`

and denominator `n + 2`. This module proves the finite-state fact used by the
exact search: survival through `h` updates depends only on the initial state
modulo `(h + 1)!`. The result is finite-horizon only; it neither constructs
an infinite negative-state orbit nor rules one out.
-/

namespace ErdosProblems.Erdos243

/-- Numerator of the forced normalized constant-negative update. -/
def forcedNumerator (n : ℕ) (a : ℤ) : ℤ :=
  (n + 1 : ℤ) * a ^ 2 - (n + 2 : ℤ) * a + (n + 3 : ℤ)

/-- The forced numerator is polynomially compatible with congruence. -/
theorem forcedNumerator_modEq
    {n : ℕ} {a b modulus : ℤ}
    (h : a ≡ b [ZMOD modulus]) :
    forcedNumerator n a ≡ forcedNumerator n b [ZMOD modulus] := by
  have hsq : a ^ 2 ≡ b ^ 2 [ZMOD modulus] := h.pow 2
  have hquad :
      (n + 1 : ℤ) * a ^ 2 ≡ (n + 1 : ℤ) * b ^ 2 [ZMOD modulus] :=
    hsq.mul_left _
  have hlinear :
      (n + 2 : ℤ) * a ≡ (n + 2 : ℤ) * b [ZMOD modulus] :=
    h.mul_left _
  simpa [forcedNumerator] using
    (hquad.sub hlinear).add_right (n + 3 : ℤ)

/-- Exact division cancels the same nonzero factor from values and modulus. -/
theorem quotient_modEq_of_modEq_mul
    {d m a b : ℤ} (hd : d ≠ 0)
    (ha : d ∣ a) (hb : d ∣ b)
    (h : a ≡ b [ZMOD d * m]) :
    a / d ≡ b / d [ZMOD m] := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  simpa [Int.mul_ediv_cancel_left _ hd] using h.mul_left_cancel' hd

/-- Modulus sufficient for `remaining` forced updates starting at `index`.
It is represented recursively so each exact division removes the visible first
factor. -/
def horizonModulus : ℕ → ℕ → ℕ
  | 0, _ => 1
  | remaining + 1, index =>
      (index + 2) * horizonModulus remaining (index + 1)

/-- The recursive modulus is the corresponding ascending factorial. -/
theorem horizonModulus_eq_ascFactorial (remaining index : ℕ) :
    horizonModulus remaining index = (index + 2).ascFactorial remaining := by
  induction remaining generalizing index with
  | zero => simp [horizonModulus]
  | succ remaining ih =>
      rw [horizonModulus, ih]
      simpa [Nat.ascFactorial_succ] using
        Nat.succ_ascFactorial (index + 2) remaining

/-- At the initial index, the finite-horizon modulus is exactly `(h + 1)!`. -/
theorem horizonModulus_zero_eq_factorial (h : ℕ) :
    horizonModulus h 0 = (h + 1).factorial := by
  rw [horizonModulus_eq_ascFactorial]
  simpa [Nat.add_comm] using Nat.ascFactorial_eq_div 1 h

/-- Exact survival predicate for the first `remaining` forced divisions. -/
def ForcedSurvives : ℕ → ℕ → ℤ → Prop
  | 0, _, _ => True
  | remaining + 1, index, a =>
      let d : ℤ := index + 2
      d ∣ forcedNumerator index a ∧
        ForcedSurvives remaining (index + 1)
          (forcedNumerator index a / d)

/-- One successful update transports congruence from a modulus `d*m` to the
shrunk modulus `m`. -/
theorem forcedQuotient_modEq
    {index : ℕ} {m a b : ℤ}
    (h : a ≡ b [ZMOD (index + 2 : ℤ) * m])
    (ha : (index + 2 : ℤ) ∣ forcedNumerator index a)
    (hb : (index + 2 : ℤ) ∣ forcedNumerator index b) :
    forcedNumerator index a / (index + 2 : ℤ) ≡
      forcedNumerator index b / (index + 2 : ℤ) [ZMOD m] := by
  apply quotient_modEq_of_modEq_mul (by omega) ha hb
  exact forcedNumerator_modEq h

/-- Survival for a fixed finite horizon depends only on the state modulo the
recursive horizon modulus. -/
theorem forcedSurvives_iff_of_modEq :
    ∀ {remaining index : ℕ} {a b : ℤ},
      a ≡ b [ZMOD (horizonModulus remaining index : ℤ)] →
      (ForcedSurvives remaining index a ↔
        ForcedSurvives remaining index b)
  | 0, index, a, b, _ => by simp [ForcedSurvives]
  | remaining + 1, index, a, b, hab => by
      have hab' :
          a ≡ b [ZMOD (index + 2 : ℤ) *
            (horizonModulus remaining (index + 1) : ℤ)] := by
        simpa [horizonModulus, Nat.cast_mul] using hab
      have hnum :
          forcedNumerator index a ≡ forcedNumerator index b
            [ZMOD (index + 2 : ℤ) *
              (horizonModulus remaining (index + 1) : ℤ)] :=
        forcedNumerator_modEq hab'
      have hnumD :
          forcedNumerator index a ≡ forcedNumerator index b
            [ZMOD (index + 2 : ℤ)] :=
        hnum.of_mul_right _
      constructor
      · rintro ⟨hdiva, hsurva⟩
        have hdivb : (index + 2 : ℤ) ∣ forcedNumerator index b := by
          apply Int.modEq_zero_iff_dvd.mp
          exact hnumD.symm.trans (Int.modEq_zero_iff_dvd.mpr hdiva)
        refine ⟨hdivb, ?_⟩
        exact (forcedSurvives_iff_of_modEq
          (forcedQuotient_modEq hab' hdiva hdivb)).mp hsurva
      · rintro ⟨hdivb, hsurvb⟩
        have hdiva : (index + 2 : ℤ) ∣ forcedNumerator index a := by
          apply Int.modEq_zero_iff_dvd.mp
          exact hnumD.trans (Int.modEq_zero_iff_dvd.mpr hdivb)
        refine ⟨hdiva, ?_⟩
        exact (forcedSurvives_iff_of_modEq
          (forcedQuotient_modEq hab' hdiva hdivb)).mpr hsurvb

/-- Exact factorial-residue theorem used by the finite search. -/
theorem forcedSurvives_iff_of_modEq_factorial
    {h : ℕ} {a b : ℤ}
    (hab : a ≡ b [ZMOD ((h + 1).factorial : ℤ)]) :
    ForcedSurvives h 0 a ↔ ForcedSurvives h 0 b := by
  apply forcedSurvives_iff_of_modEq
  simpa [horizonModulus_zero_eq_factorial] using hab

end ErdosProblems.Erdos243
