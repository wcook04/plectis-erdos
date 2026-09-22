import ErdosProblems.Erdos243.PaperCompleteR11.RecordDivisibility

/-!
# Finite inclusive-boundary transfer

These are the exact finite inequalities used at the final step of the
inclusive log--log corollary.  They do not claim the still-missing limsup,
totient, or asymptotic selection argument.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open PaperCompleteR9

/-- For the additive state equation `U_{n+1}=U_n-V_n`, the increment above the
previous running maximum is bounded by the negative part of the error.  This
remains true across arbitrary drawdowns. -/
theorem record_increment_le_negative_part
    (U : ℕ → ℕ) (V : ℕ → ℤ)
    (hstep : ∀ n, (U (n + 1) : ℤ) = (U n : ℤ) - V n) (n : ℕ) :
    ((U (n + 1) - runningMax U n : ℕ) : ℤ) ≤ max (-V n) 0 := by
  by_cases hrecord : runningMax U n < U (n + 1)
  · have hsource : U n ≤ runningMax U n := le_runningMax U (le_rfl : n ≤ n)
    have hgap : ((U (n + 1) - runningMax U n : ℕ) : ℤ) =
        (U (n + 1) : ℤ) - runningMax U n := by
      omega
    rw [hgap]
    have hdiff : (U (n + 1) : ℤ) - U n = -V n := by
      have hs := hstep n
      omega
    calc
      (U (n + 1) : ℤ) - runningMax U n ≤ (U (n + 1) : ℤ) - U n := by
        exact sub_le_sub_left (by exact_mod_cast hsource) _
      _ = -V n := hdiff
      _ ≤ max (-V n) 0 := le_max_left _ _
  · have hzero : U (n + 1) - runningMax U n = 0 :=
      Nat.sub_eq_zero_of_le (by omega)
    rw [hzero]
    simp

/-- At a strict record the negative error is strictly positive, and the
source-to-endpoint rise is exactly `-V_n`. -/
theorem strict_record_negative_error
    (U : ℕ → ℕ) (V : ℕ → ℤ)
    (hstep : ∀ n, (U (n + 1) : ℤ) = (U n : ℤ) - V n)
    {n : ℕ} (hr : IsStrictRecord U n) :
    0 < -V n ∧ ((U (n + 1) - U n : ℕ) : ℤ) = -V n := by
  have hrise : U n < U (n + 1) := hr n le_rfl
  have hriseZ : (U n : ℤ) < U (n + 1) := by exact_mod_cast hrise
  have hs := hstep n
  constructor <;> omega

/-- Hence on a strict record the record increment itself is bounded by the
exact negative error, the finite inequality used to transfer the record
boundary theorem to the inclusive error condition. -/
theorem strict_record_increment_le_negative_error
    (U : ℕ → ℕ) (V : ℕ → ℤ)
    (hstep : ∀ n, (U (n + 1) : ℤ) = (U n : ℤ) - V n)
    {n : ℕ} (hr : IsStrictRecord U n) :
    ((U (n + 1) - runningMax U n : ℕ) : ℤ) ≤ -V n := by
  have hneg := (strict_record_negative_error U V hstep hr).1
  have hbound := record_increment_le_negative_part U V hstep n
  rw [max_eq_left (le_of_lt hneg)] at hbound
  exact hbound

end ErdosProblems.Erdos243.PaperCompleteR11
