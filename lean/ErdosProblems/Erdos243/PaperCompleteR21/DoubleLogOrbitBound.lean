import ErdosProblems.Erdos243.PaperCompleteR21.ExactOrbitRecordDichotomy
import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup

/-!
# Erdős #243: the double-logarithmic implication for an exact orbit

Paper restatement of the displayed implication in the section "Further consequences"
(`sec:secondaryrate`) of the short #243 paper: under the hypotheses of Theorem 1.2
(`res:bounded`) other than (5),
`limsup_n (-E_n)_+ / log₂ log₂ max(4, C_n) ≤ 1  ⟹  E_n = 0 eventually`.

The paper says that its two steps are Lean theorems and that only their combination was
missing.  This file supplies that combination:

* `exactOrbit_recordTheta_gt_one` (strict record bound): if `E_n` is not eventually zero,
  then `1 < limsup_n (H_{n+1} - H_n) / log₂ log₂ max(4, H_n)` with `H_n = max_{j ≤ n} C_j`;
* `recordTheta_le_negativeError_limsup` (comparison with the negative part): that limit
  superior is at most the one in the display;
* `D₀ ≥ 1`, which follows from (6): if `D₀ = 0` then every `D_n = 0`, so
  `|E_n| = (a_n - 1) C_n ≥ C_n`, contradicting (6) with `K = 1`.

The limit superior is taken in the extended reals `EReal`, so an unbounded quotient has
limit superior `+∞` rather than a junk real value.  Hypothesis (4) follows from (6) with
`K = 1` and is not used separately.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open ErdosProblems.Erdos243
open ErdosProblems.Erdos243.PaperCompleteR11

/-- `sec:secondaryrate` (the displayed double-logarithmic implication; the companion's
`long243:res:loglogboundary` for an exact orbit).  Let `a, C, D : ℕ → ℕ` and `E : ℕ → ℤ`
satisfy the hypotheses of Theorem 1.2 (`res:bounded`) other than (5):

1. `a_n > 1` and `C_n > 0` for every `n`;
2. `C_{n+1} + D_n = a_n C_n` and `D_{n+1} = a_n D_n`;
3. `E_n = D_n - (a_n - 1) C_n` for every `n`;
4. `|E_n| < C_n` for all large `n`;
6. for every integer `K ≥ 1` there is an `N` with `K |E_n| < C_n` for all `n ≥ N`.

Then
`limsup_{n→∞} (-E_n)_+ / log₂ log₂ max(4, C_n) ≤ 1  ⟹  E_n = 0 eventually`. -/
theorem exactOrbit_double_logarithmic_bound
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (h1 : ∀ n, 1 < a n ∧ 0 < C n)
    (h2 : ∀ n, C (n + 1) + D n = a n * C n ∧ D (n + 1) = a n * D n)
    (h3 : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ))
    (_h4 : ∃ N, ∀ n, N ≤ n → |E n| < (C n : ℤ))
    (h6 : ∀ K : ℤ, 1 ≤ K → ∃ N, ∀ n, N ≤ n → K * |E n| < (C n : ℤ)) :
    limsup (fun n => ((((max (-E n) 0 : ℤ) : ℝ) /
        Real.logb 2 (Real.logb 2 (max 4 (C n : ℝ))) : ℝ) : EReal)) atTop ≤ 1 →
      ∃ N, ∀ n, N ≤ n → E n = 0 := by
  -- (4) is the case `K = 1` of (6); the combination does not use it separately.
  intro hlim
  by_contra hnot
  have hC : ∀ n, C (n + 1) + D n = a n * C n := fun n => (h2 n).1
  have hD : ∀ n, D (n + 1) = a n * D n := fun n => (h2 n).2
  have hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ) := by
    intro n
    rw [h3 n, centeredState]
  -- (6) in the natural-number form used by the record bound (`K = 0` is (1))
  have hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n := by
    intro K
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · exact ⟨0, fun n _ => by simpa using (h1 n).2⟩
    · obtain ⟨N, hN⟩ := h6 (K : ℤ) (by exact_mod_cast hK)
      refine ⟨N, fun n hn => ?_⟩
      have h := hN n hn
      rw [Int.abs_eq_natAbs] at h
      exact_mod_cast h
  -- `D₀ ≥ 1`, a consequence of (6)
  have hD0 : 1 ≤ D 0 := by
    by_contra h0
    have hDz : ∀ n, D n = 0 := by
      intro n
      induction n with
      | zero => omega
      | succ n ih => rw [hD n, ih, mul_zero]
    obtain ⟨N, hN⟩ := h6 1 le_rfl
    have hlt := hN N le_rfl
    rw [h3 N, hDz N, Nat.cast_zero, one_mul] at hlt
    have ha : (2 : ℤ) ≤ (a N : ℤ) := by exact_mod_cast (h1 N).1
    have hc : (0 : ℤ) < (C N : ℤ) := by exact_mod_cast (h1 N).2
    have habs := neg_le_abs ((0 : ℤ) - ((a N : ℤ) - 1) * (C N : ℤ))
    nlinarith
  have hstep : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n :=
    natTail_eq_sub_centeredState a C D E hC hE
  -- the two Lean steps
  have hgt : (1 : EReal) < recordTheta C :=
    exactOrbit_recordTheta_gt_one a C D E (fun n => (h1 n).1) (fun n => (h1 n).2) hD0 hC hD hE
      hvanish hnot
  have hle := recordTheta_le_negativeError_limsup C E hstep
  -- the comparison quotient is the displayed one
  have hid : (fun n => ((negativeErrorLogLogCharge C E n : ℝ) : EReal)) =
      fun n => ((((max (-E n) 0 : ℤ) : ℝ) /
        Real.logb 2 (Real.logb 2 (max 4 (C n : ℝ))) : ℝ) : EReal) := by
    funext n
    simp only [negativeErrorLogLogCharge, recordLogLog, Real.logb]
  rw [hid] at hle
  exact absurd (hgt.trans_le hle) (not_lt.mpr hlim)

end ErdosProblems.Erdos243.PaperCompleteR21

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_double_logarithmic_bound
