import ErdosProblems.Erdos243.ReciprocalTailRigidity
import ErdosProblems.Erdos243.PaperCompleteR21.SlowGrowthProductIncrements

/-!
# Erdős 243: the slow negative part (`long243:res:slownegative`)

The paper's theorem reads: let `(a, C, D)` be an exact orbit of natural numbers
with `a_n > 1`, `C_n > 0`, `D_0 ≥ 1`, under vanishing relative error; suppose
that for some `δ ∈ (0,1)` and all large `n` with `E_n < 0` one has
`-E_n ≤ (1-δ) ℓ(C_n)`.  Then `E_n = 0` for all large `n`, and
`a_{n+1} = a_n² - a_n + 1` for all large `n`.

The written proof has exactly two inputs.

* The upper half.  `C_{n+1} = C_n - E_n` and `C_n ≤ H_n = max_{j ≤ n} C_j`
  give `H_{n+1} - H_n ≤ (-E_n)_+ ≤ (1-δ) ℓ(C_n) ≤ (1-δ) ℓ(H_n)`, so
  `Θ = limsup (H_{n+1} - H_n)/ℓ(H_n) ≤ 1 - δ < 1`.  This half is
  `recordTheta_le_of_slow_negative`
  (`PaperCompleteR21/SlowGrowthProductIncrements.lean`), which is stated for an
  arbitrary exact orbit and is imported here.
* The lower half.  If the error is not eventually zero then `Θ ≥ 1`.  The
  paper takes this from the proof of `long243:res:recorddichotomy`, asserting
  that the argument there uses only `a_n > 1`, `C_n > 0`, `D_0 ≥ 1` and
  vanishing relative error.  In the tree that half exists only in the
  *canonical* coordinates of a rational reciprocal sum
  (`PaperCompleteR11.canonical_recordTheta_gt_one`, which additionally assumes
  `StrictMono a`, `HasSum (1/aₙ) = p/q` and `a_{n+1}/a_n² → 1`).  It is not
  available for an arbitrary exact orbit, and proving it there is the whole of
  the record dichotomy.

This file therefore carries the theorem with that second input as one explicit,
named hypothesis `hdichotomy`, and proves everything else.  The statement is
consequently weaker than the paper's; discharging `hdichotomy` for a general
exact orbit is the single remaining step.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open ErdosProblems.Erdos243
open ErdosProblems.Erdos243.PaperCompleteR11

/-- The paper's growing bound on the negative part, extended from the indices
where `E n < 0` to the whole tail.  Where `E n ≥ 0` the left side is
nonpositive and the right side is nonnegative, because `ℓ ≥ 1`. -/
theorem slowNegative_bound_all_of_negative_part
    (C : ℕ → ℕ) (E : ℕ → ℤ) (c : ℝ) (hc0 : 0 ≤ c) (N : ℕ)
    (hslow : ∀ n, N ≤ n → E n < 0 →
      -((E n : ℤ) : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ)) :
    ∀ n, N ≤ n → -((E n : ℤ) : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ) := by
  intro n hn
  rcases lt_or_ge (E n) 0 with h | h
  · exact hslow n hn h
  · have hEn : (0 : ℝ) ≤ ((E n : ℤ) : ℝ) := by exact_mod_cast h
    have hl : (1 : ℝ) ≤ recordLogLog ((C n : ℕ) : ℝ) := one_le_recordLogLog _
    have : (0 : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ) := by nlinarith
    linarith

/-- **Slow negative part** (`long243:res:slownegative`), with the record-limsup
lower bound of `long243:res:recorddichotomy` carried as the explicit hypothesis
`hdichotomy`.

Both conclusions of the paper are stated: the centred error vanishes on a tail,
and the original denominators satisfy the Sylvester recurrence
`a_{n+1} = a_n² - a_n + 1` on a tail. -/
theorem slowNegative_eventually_zero_and_sylvesterNext
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (δ : ℝ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hDstep : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hslow : ∃ N, ∀ n, N ≤ n → E n < 0 →
      -((E n : ℤ) : ℝ) ≤ (1 - δ) * recordLogLog ((C n : ℕ) : ℝ))
    (hdichotomy : (¬ ∃ N, ∀ n, N ≤ n → E n = 0) → (1 : EReal) ≤ recordTheta C) :
    (∃ N, ∀ n, N ≤ n → E n = 0) ∧
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  have hE' : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ) := by
    intro n
    rw [hE n, centeredState]
  have hzero : ∃ N, ∀ n, N ≤ n → E n = 0 := by
    by_contra hnot
    obtain ⟨N, hN⟩ := hslow
    have hall := slowNegative_bound_all_of_negative_part C E (1 - δ) (by linarith) N hN
    have hle : recordTheta C ≤ (((1 - δ : ℝ)) : EReal) :=
      recordTheta_le_of_slow_negative a C D E hC hE' (1 - δ) (by linarith) N hall
    have hlow : (1 : EReal) ≤ recordTheta C := hdichotomy hnot
    have hchain : (1 : EReal) ≤ (((1 - δ : ℝ)) : EReal) := le_trans hlow hle
    have hlt : (((1 - δ : ℝ)) : EReal) < (1 : EReal) := by
      rw [← EReal.coe_one]
      exact_mod_cast (by linarith : (1 - δ : ℝ) < 1)
    exact absurd hchain (not_le.mpr hlt)
  refine ⟨hzero, ?_⟩
  apply sylvesterNext_eventually_of_centered_zero
    (fun n ↦ (a n : ℤ)) (fun n ↦ (D n : ℤ)) (fun n ↦ (C n : ℤ))
  · intro n
    exact natDen_eq_nextDenState a D hDstep n
  · intro n
    exact natTail_eq_nextTailState a C D hC n
  · obtain ⟨N, hN⟩ := hzero
    refine ⟨N, fun n hn ↦ ?_⟩
    have hn0 := hN n hn
    rw [hE n] at hn0
    exact hn0
  · exact ⟨0, fun n _hn ↦ by exact_mod_cast (Nat.ne_of_gt (hCpos (n + 1)))⟩

#print axioms
  ErdosProblems.Erdos243.PaperCompleteR21.slowNegative_eventually_zero_and_sylvesterNext

end ErdosProblems.Erdos243.PaperCompleteR21
