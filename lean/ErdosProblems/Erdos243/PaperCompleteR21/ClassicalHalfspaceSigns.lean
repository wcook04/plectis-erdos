import ErdosProblems.Erdos243.GlobalLcmHeight
import ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect
import Mathlib.Tactic.NormNum.GCD

/-!
# Erdős 243: comparison of the two signs (`long243:res:classicalhalfspace`)

This file states and proves every clause of the proposition "comparison of the
two signs" (`paper/reasoning-parts/erdos243/core.tex`, line 2427), in the
zero-based indexing of the tree.  The paper's data are

`P_n = ∏_{j < n} a_j`,  `D_n = q P_n`,  `x_n = ∑_{k ≥ n} 1/a_k`,
`C_n = D_n x_n`,  `E_n = D_n - (a_n - 1) C_n`,
`L_n = lcm(q, a_0, …, a_{n-1})`,  `M_n = D_n / L_n`,
`G_n = gcd(C_n, D_n)`,  `ẽ_n = E_n / G_n`,

which are `prefixProduct`, `canonicalDenominator`, `realTail`,
`canonicalNaturalNumerator`, `centeredState`, `cumulativeDigitLcm`,
`cumulativeOverlapDebt` and `Nat.gcd` in the tree.  That `M_n` really is
`D_n / L_n` is `cumulativeOverlapDebt_mul_lcm_eq_productScale` together with
`digitProductScale_eq_canonicalDenominator` below.

The clauses:

* `M_n ∣ G_n` — `overlapDebt_dvd_gcd`.  The paper's reason is that both
  `C_n = D_n x_n` and `L_n x_n` are integers; here `L_n x_n` is produced
  explicitly as `lcmClearedNumerator`, whose integrality is `q ∣ L_n` and
  `a_j ∣ L_n` for `j < n`.
* `G_n/M_n` is a positive integer and `E_n/M_n = (G_n/M_n) ẽ_n` is an integer
  with the same sign as `E_n` — `canonicalError_div_overlapDebt`.
* the identity `long243:eq:shiftedsign`, valid whenever `a_{n+1} C_n C_{n+1} ≠ 0`
  — `growthDefect_eq_neg_relativeError_add_shiftedCorrection` abstractly and
  `canonical_growthDefect_identity` on the canonical orbit.
* `0 < Λ_n < 3/a_n` for all large `n` under the standing hypotheses —
  `canonicalCorrection_pos_and_lt_three_div`.
* the Erdős–Straus quantity `Z_n^ES` — `erdosStrausQuantity`; its least common
  multiple includes `a_n` and not `q`
  (`erdosStraus_lcm_includes_digit_not_denominator`), and it is neither `Q_n`
  nor `L_n γ_{n+1}/a_{n+1}` (`erdosStrausQuantity_ne_productDefect_ne_lcmShift`,
  an explicit witness).
* `Z_n^ES` has the sign of `Λ_{n+1} - E_{n+1}/C_{n+1}`, is positive when
  `E_{n+1} ≤ 0`, and for `E_{n+1} > 0` is negative exactly when
  `E_{n+1}/C_{n+1} > Λ_{n+1}` — `erdosStrausQuantity_sign`.
* on a Sylvester tail `E_n = 0` and `Λ_n = (a_n - 1)/a_{n+1} > 0` —
  `sylvesterTail_shiftedCorrection`.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open ErdosProblems.Erdos243
open ErdosProblems.Erdos243.PaperCompleteR7
open scoped BigOperators

/-! ## 1. The cumulative least common multiple and the clearing factor -/

/-- The clearing denominator divides every cumulative least common multiple. -/
theorem dvd_cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    q ∣ cumulativeDigitLcm q a n := by
  induction n with
  | zero => exact dvd_rfl
  | succ n ih => exact ih.trans (Nat.dvd_lcm_left _ _)

/-- Every earlier digit divides the cumulative least common multiple. -/
theorem digit_dvd_cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    ∀ n, j < n → a j ∣ cumulativeDigitLcm q a n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
      intro h
      by_cases hjn : j < n
      · exact (ih hjn).trans (Nat.dvd_lcm_left _ _)
      · have hje : j = n := by omega
        subst hje
        exact Nat.dvd_lcm_right _ _

/-- The cumulative product scale is the canonical product-cleared denominator
`D_n = q P_n`. -/
theorem digitProductScale_eq_canonicalDenominator (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    digitProductScale q a n = canonicalDenominator a q n := by
  induction n with
  | zero => simp [digitProductScale, canonicalDenominator, prefixProduct]
  | succ n ih =>
      have h : digitProductScale q a (n + 1) = a n * digitProductScale q a n := rfl
      rw [h, ih]
      show a n * (q * prefixProduct a n) = q * prefixProduct a (n + 1)
      rw [prefixProduct_succ]
      ring

/-- `M_n L_n = D_n`: the overlap debt of the tree is exactly the paper's
clearing factor `M_n = D_n / L_n`. -/
theorem overlapDebt_mul_cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    cumulativeOverlapDebt q a n * cumulativeDigitLcm q a n =
      canonicalDenominator a q n := by
  rw [cumulativeOverlapDebt_mul_lcm_eq_productScale,
    digitProductScale_eq_canonicalDenominator]

theorem canonicalDenominator_pos (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (q : ℕ) (hq : 0 < q) (n : ℕ) : 0 < canonicalDenominator a q n :=
  Nat.mul_pos hq (prefixProduct_pos a hpos n)

theorem overlapDebt_pos (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (q : ℕ) (hq : 0 < q) (n : ℕ) : 0 < cumulativeOverlapDebt q a n := by
  rcases Nat.eq_zero_or_pos (cumulativeOverlapDebt q a n) with h0 | h0
  · exfalso
    have h := overlapDebt_mul_cumulativeDigitLcm q a n
    rw [h0, zero_mul] at h
    have := canonicalDenominator_pos a hpos q hq n
    omega
  · exact h0

theorem cumulativeDigitLcm_pos (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (q : ℕ) (hq : 0 < q) (n : ℕ) : 0 < cumulativeDigitLcm q a n := by
  rcases Nat.eq_zero_or_pos (cumulativeDigitLcm q a n) with h0 | h0
  · exfalso
    have h := overlapDebt_mul_cumulativeDigitLcm q a n
    rw [h0, mul_zero] at h
    have := canonicalDenominator_pos a hpos q hq n
    omega
  · exact h0

/-! ## 2. `M_n ∣ G_n`, and the integrality and sign of `E_n / M_n` -/

/-- The LCM-cleared numerator `U_n = L_n x_n`.  It is an integer because
`q ∣ L_n` and `a_j ∣ L_n` for every `j < n`. -/
def lcmClearedNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * ((cumulativeDigitLcm q a n / q : ℕ) : ℤ) -
    ∑ j ∈ Finset.range n, ((cumulativeDigitLcm q a n / a j : ℕ) : ℤ)

/-- `C_n = M_n U_n`: the product-cleared numerator is the clearing factor times
the LCM-cleared numerator. -/
theorem overlapDebt_mul_lcmClearedNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    ((cumulativeOverlapDebt q a n : ℕ) : ℤ) * lcmClearedNumerator a p q n =
      clearedIntegerNumerator a p q n := by
  have hi : cumulativeOverlapDebt q a n * (cumulativeDigitLcm q a n / q) =
      prefixProduct a n := by
    apply Nat.eq_of_mul_eq_mul_left hq
    calc q * (cumulativeOverlapDebt q a n * (cumulativeDigitLcm q a n / q))
        = cumulativeOverlapDebt q a n * (q * (cumulativeDigitLcm q a n / q)) := by
          ring
      _ = cumulativeOverlapDebt q a n * cumulativeDigitLcm q a n := by
          rw [Nat.mul_div_cancel' (dvd_cumulativeDigitLcm q a n)]
      _ = canonicalDenominator a q n := overlapDebt_mul_cumulativeDigitLcm q a n
      _ = q * prefixProduct a n := rfl
  have hii : ∀ j, j < n →
      cumulativeOverlapDebt q a n * (cumulativeDigitLcm q a n / a j) =
        q * (prefixProduct a n / a j) := by
    intro j hj
    apply Nat.eq_of_mul_eq_mul_left (hpos j)
    have hdL : a j ∣ cumulativeDigitLcm q a n :=
      digit_dvd_cumulativeDigitLcm q a j n hj
    have hdP : a j ∣ prefixProduct a n :=
      Finset.dvd_prod_of_mem a (Finset.mem_range.mpr hj)
    calc a j * (cumulativeOverlapDebt q a n * (cumulativeDigitLcm q a n / a j))
        = cumulativeOverlapDebt q a n * (a j * (cumulativeDigitLcm q a n / a j)) := by
          ring
      _ = cumulativeOverlapDebt q a n * cumulativeDigitLcm q a n := by
          rw [Nat.mul_div_cancel' hdL]
      _ = canonicalDenominator a q n := overlapDebt_mul_cumulativeDigitLcm q a n
      _ = q * prefixProduct a n := rfl
      _ = q * (a j * (prefixProduct a n / a j)) := by
          rw [Nat.mul_div_cancel' hdP]
      _ = a j * (q * (prefixProduct a n / a j)) := by ring
  have hiZ : ((cumulativeOverlapDebt q a n : ℕ) : ℤ) *
      ((cumulativeDigitLcm q a n / q : ℕ) : ℤ) = ((prefixProduct a n : ℕ) : ℤ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hi
  unfold lcmClearedNumerator clearedIntegerNumerator
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · calc ((cumulativeOverlapDebt q a n : ℕ) : ℤ) *
        (p * ((cumulativeDigitLcm q a n / q : ℕ) : ℤ))
        = p * (((cumulativeOverlapDebt q a n : ℕ) : ℤ) *
            ((cumulativeDigitLcm q a n / q : ℕ) : ℤ)) := by ring
      _ = p * ((prefixProduct a n : ℕ) : ℤ) := by rw [hiZ]
  · apply Finset.sum_congr rfl
    intro j hj
    have h := hii j (Finset.mem_range.mp hj)
    exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) h

theorem overlapDebt_dvd_canonicalNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    cumulativeOverlapDebt q a n ∣ canonicalNaturalNumerator a p q n := by
  have hdvd : ((cumulativeOverlapDebt q a n : ℕ) : ℤ) ∣
      clearedIntegerNumerator a p q n :=
    ⟨lcmClearedNumerator a p q n,
      (overlapDebt_mul_lcmClearedNumerator a hpos p q hq n).symm⟩
  rw [← Int.natCast_dvd_natCast]
  show ((cumulativeOverlapDebt q a n : ℕ) : ℤ) ∣
    (((clearedIntegerNumerator a p q n).toNat : ℕ) : ℤ)
  by_cases h : 0 ≤ clearedIntegerNumerator a p q n
  · rw [Int.toNat_of_nonneg h]; exact hdvd
  · rw [Int.toNat_eq_zero.mpr (le_of_lt (not_le.mp h))]
    simp

theorem overlapDebt_dvd_canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) :
    cumulativeOverlapDebt q a n ∣ canonicalDenominator a q n :=
  ⟨cumulativeDigitLcm q a n, (overlapDebt_mul_cumulativeDigitLcm q a n).symm⟩

/-- **First clause of `long243:res:classicalhalfspace`.**
The clearing factor `M_n = D_n/L_n` is a positive integer dividing
`G_n = gcd(C_n, D_n)`. -/
theorem overlapDebt_dvd_gcd
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    0 < cumulativeOverlapDebt q a n ∧
      cumulativeOverlapDebt q a n *  cumulativeDigitLcm q a n =
        canonicalDenominator a q n ∧
      cumulativeOverlapDebt q a n ∣
        Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) :=
  ⟨overlapDebt_pos a hpos q hq n, overlapDebt_mul_cumulativeDigitLcm q a n,
    Nat.dvd_gcd (overlapDebt_dvd_canonicalNumerator a hpos p q hq n)
      (overlapDebt_dvd_canonicalDenominator a q n)⟩

/-- The canonical centred error `E_n = D_n - (a_n - 1) C_n`. -/
def canonicalError (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℤ :=
  centeredState (a n : ℤ) ((canonicalDenominator a q n : ℕ) : ℤ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℤ)

/-- **Second clause of `long243:res:classicalhalfspace`.**
`G_n/M_n` is a positive integer, `E_n/M_n = (G_n/M_n) ẽ_n` with
`ẽ_n = E_n/G_n`, and `E_n/M_n` has the same sign as `E_n`. -/
theorem canonicalError_div_overlapDebt
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    0 < Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) /
        cumulativeOverlapDebt q a n ∧
      ((cumulativeOverlapDebt q a n : ℕ) : ℤ) ∣ canonicalError a p q n ∧
      ((Nat.gcd (canonicalNaturalNumerator a p q n)
          (canonicalDenominator a q n) : ℕ) : ℤ) ∣ canonicalError a p q n ∧
      canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) =
        ((Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) /
            cumulativeOverlapDebt q a n : ℕ) : ℤ) *
          (canonicalError a p q n /
            ((Nat.gcd (canonicalNaturalNumerator a p q n)
              (canonicalDenominator a q n) : ℕ) : ℤ)) ∧
      (0 < canonicalError a p q n ↔
        0 < canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ)) ∧
      (canonicalError a p q n < 0 ↔
        canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) < 0) ∧
      (canonicalError a p q n = 0 ↔
        canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) = 0) := by
  have hMpos : 0 < cumulativeOverlapDebt q a n := overlapDebt_pos a hpos q hq n
  have hDpos : 0 < canonicalDenominator a q n := canonicalDenominator_pos a hpos q hq n
  have hGpos : 0 < Nat.gcd (canonicalNaturalNumerator a p q n)
      (canonicalDenominator a q n) := Nat.gcd_pos_of_pos_right _ hDpos
  have hMG : cumulativeOverlapDebt q a n ∣
      Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) :=
    (overlapDebt_dvd_gcd a hpos p q hq n).2.2
  have hquot : 0 < Nat.gcd (canonicalNaturalNumerator a p q n)
      (canonicalDenominator a q n) / cumulativeOverlapDebt q a n :=
    Nat.div_pos (Nat.le_of_dvd hGpos hMG) hMpos
  have hGE : ((Nat.gcd (canonicalNaturalNumerator a p q n)
      (canonicalDenominator a q n) : ℕ) : ℤ) ∣ canonicalError a p q n := by
    unfold canonicalError centeredState
    exact dvd_sub
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _))
      (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) _)
  have hME : ((cumulativeOverlapDebt q a n : ℕ) : ℤ) ∣ canonicalError a p q n :=
    (Int.natCast_dvd_natCast.mpr hMG).trans hGE
  have hMposZ : (0 : ℤ) < ((cumulativeOverlapDebt q a n : ℕ) : ℤ) := by
    exact_mod_cast hMpos
  have hGposZ : (0 : ℤ) < ((Nat.gcd (canonicalNaturalNumerator a p q n)
      (canonicalDenominator a q n) : ℕ) : ℤ) := by exact_mod_cast hGpos
  obtain ⟨m, hm⟩ := id hMG
  obtain ⟨e, he⟩ := id hGE
  have hmq : Nat.gcd (canonicalNaturalNumerator a p q n)
      (canonicalDenominator a q n) / cumulativeOverlapDebt q a n = m := by
    rw [hm, Nat.mul_div_cancel_left _ hMpos]
  have hprod : canonicalError a p q n =
      ((cumulativeOverlapDebt q a n : ℕ) : ℤ) * ((m : ℕ) : ℤ) * e := by
    rw [he, hm]; push_cast; ring
  have hEM : canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) =
      ((m : ℕ) : ℤ) * e := by
    rw [hprod, mul_assoc, Int.mul_ediv_cancel_left _ (ne_of_gt hMposZ)]
  have heq : canonicalError a p q n /
      ((Nat.gcd (canonicalNaturalNumerator a p q n)
        (canonicalDenominator a q n) : ℕ) : ℤ) = e := by
    rw [he, Int.mul_ediv_cancel_left _ (ne_of_gt hGposZ)]
  have hfactor : canonicalError a p q n =
      canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) *
        ((cumulativeOverlapDebt q a n : ℕ) : ℤ) := (Int.ediv_mul_cancel hME).symm
  refine ⟨hquot, hME, hGE, ?_, ?_, ?_, ?_⟩
  · rw [hEM, hmq, heq]
  · constructor
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith [hfactor, hMposZ, hc]
    · intro h
      rw [hfactor]
      exact mul_pos h hMposZ
  · constructor
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith [hfactor, hMposZ, hc]
    · intro h
      rw [hfactor]
      exact mul_neg_of_neg_of_pos h hMposZ
  · constructor
    · intro h
      rw [hEM] at *
      rw [hprod] at h
      have : ((cumulativeOverlapDebt q a n : ℕ) : ℤ) * (((m : ℕ) : ℤ) * e) = 0 := by
        rw [← h]; ring
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 (ne_of_gt hMposZ)
      · exact h1
    · intro h
      rw [hfactor, h, zero_mul]

/-! ## 3. The shifted-sign identity and its correction term -/

/-- The correction term `Λ_n` of `long243:eq:shiftedsign`. -/
def shiftedCorrectionTerm (a aNext C CNext E ENext : ℝ) : ℝ :=
  (1 - E / C) * (a - 1 + ENext / CNext) / aNext

/-- **The identity `long243:eq:shiftedsign`.**
For the exact recurrences `D_{n+1} = a_n D_n`, `C_{n+1} = a_n C_n - D_n` and
the centred error `E_n = D_n - (a_n - 1) C_n`, whenever `a_{n+1} C_n C_{n+1} ≠ 0`,

`a_n²/a_{n+1} - 1 = -E_n/C_n + Λ_n`. -/
theorem growthDefect_eq_neg_relativeError_add_shiftedCorrection
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (hne : aNext * C * CNext ≠ 0) :
    a ^ 2 / aNext - 1 =
      -(E / C) + shiftedCorrectionTerm a aNext C CNext E ENext := by
  have haNext : aNext ≠ 0 := by
    intro h; apply hne; rw [h]; ring
  have hC0 : C ≠ 0 := by
    intro h; apply hne; rw [h]; ring
  have hCNext : CNext ≠ 0 := by
    intro h; apply hne; rw [h]; ring
  subst hD
  subst hE
  subst hENext
  simp only [shiftedCorrectionTerm]
  rw [hC] at hCNext ⊢
  field_simp
  ring

/-- **The Sylvester-tail clause of `long243:res:classicalhalfspace`.**
If `E_n = 0` and `a_{n+1} = a_n² - a_n + 1`, then `E_{n+1} = 0` and
`Λ_n = (a_n - 1)/a_{n+1} > 0`. -/
theorem sylvesterTail_shiftedCorrection
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (ha : 1 < a)
    (hsyl : aNext = a ^ 2 - a + 1)
    (hzero : E = 0) :
    ENext = 0 ∧
      shiftedCorrectionTerm a aNext C CNext E ENext = (a - 1) / aNext ∧
      0 < shiftedCorrectionTerm a aNext C CNext E ENext := by
  have hDval : D = (a - 1) * C := by
    rw [hE] at hzero; linarith
  have hCNext : CNext = C := by rw [hC, hDval]; ring
  have hENextZero : ENext = 0 := by
    rw [hENext, hD, hDval, hCNext, hsyl]; ring
  have haNextPos : 0 < aNext := by
    rw [hsyl]; nlinarith
  have hLam : shiftedCorrectionTerm a aNext C CNext E ENext
      = (a - 1) / aNext := by
    simp only [shiftedCorrectionTerm, hzero, hENextZero, zero_div, sub_zero,
      add_zero, one_mul]
  refine ⟨hENextZero, hLam, ?_⟩
  rw [hLam]
  exact div_pos (by linarith) haNextPos

/-- The eventual bound `0 < Λ_n < 3/a_n`, in the abstract form in which it is
used: `a_n ≥ 2`, `a_{n+1} ≥ a_n²/2`, and both relative errors at most `1/4`. -/
theorem shiftedCorrectionTerm_pos_and_lt_three_div
    {A ANext C CNext E ENext : ℝ}
    (hA : 2 ≤ A) (hANext : A ^ 2 / 2 ≤ ANext)
    (hθ : |E / C| ≤ 1 / 4) (hθNext : |ENext / CNext| ≤ 1 / 4) :
    0 < shiftedCorrectionTerm A ANext C CNext E ENext ∧
      shiftedCorrectionTerm A ANext C CNext E ENext < 3 / A := by
  obtain ⟨h1, h2⟩ := abs_le.mp hθ
  obtain ⟨h3, h4⟩ := abs_le.mp hθNext
  have hApos : (0 : ℝ) < A := by linarith
  have hsq : (0 : ℝ) < A ^ 2 := by positivity
  have hANextpos : (0 : ℝ) < ANext := by nlinarith
  have hfac1 : (3 : ℝ) / 4 ≤ 1 - E / C := by linarith
  have hfac1' : 1 - E / C ≤ 5 / 4 := by linarith
  have hfac2 : (3 : ℝ) / 4 ≤ A - 1 + ENext / CNext := by linarith
  have hfac2' : A - 1 + ENext / CNext ≤ A - 3 / 4 := by linarith
  constructor
  · exact div_pos (by nlinarith) hANextpos
  · rw [shiftedCorrectionTerm, div_lt_div_iff₀ hANextpos hApos]
    have hprod : (1 - E / C) * (A - 1 + ENext / CNext) ≤ 5 / 4 * (A - 3 / 4) :=
      mul_le_mul hfac1' hfac2' (by linarith) (by norm_num)
    have hstep : (1 - E / C) * (A - 1 + ENext / CNext) * A ≤
        5 / 4 * (A - 3 / 4) * A :=
      mul_le_mul_of_nonneg_right hprod hApos.le
    nlinarith [hstep, hANext, hApos, hA]

/-! ## 4. The canonical orbit -/

/-- `Λ_n` on the canonical orbit. -/
def canonicalCorrection (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℝ :=
  shiftedCorrectionTerm (a n : ℝ) (a (n + 1) : ℝ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)
    ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)
    ((canonicalError a p q n : ℤ) : ℝ) ((canonicalError a p q (n + 1) : ℤ) : ℝ)

/-- **The identity `long243:eq:shiftedsign` on the canonical orbit.** -/
theorem canonical_growthDefect_identity
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 =
      -(((canonicalError a p q n : ℤ) : ℝ) /
          ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)) +
        canonicalCorrection a p q n := by
  obtain ⟨hcpos, hdpos, hc, hd, hrep⟩ := canonical_integer_tail a hpos p q hq hs
  have hCn : (0 : ℝ) < ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) := by
    exact_mod_cast hcpos n
  have hCn1 : (0 : ℝ) < ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcpos (n + 1)
  have han1 : (0 : ℝ) < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
  have hDstep : ((canonicalDenominator a q (n + 1) : ℕ) : ℝ) =
      (a n : ℝ) * ((canonicalDenominator a q n : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (hd n)
  have hCstep : ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) =
      (a n : ℝ) * ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) -
        ((canonicalDenominator a q n : ℕ) : ℝ) := by
    have h : ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) +
        ((canonicalDenominator a q n : ℕ) : ℝ) =
        (a n : ℝ) * ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (hc n)
    linarith
  have hEn : ((canonicalError a p q n : ℤ) : ℝ) =
      ((canonicalDenominator a q n : ℕ) : ℝ) -
        ((a n : ℝ) - 1) * ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) := by
    unfold canonicalError centeredState
    push_cast
    ring
  have hEn1 : ((canonicalError a p q (n + 1) : ℤ) : ℝ) =
      ((canonicalDenominator a q (n + 1) : ℕ) : ℝ) -
        ((a (n + 1) : ℝ) - 1) *
          ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) := by
    unfold canonicalError centeredState
    push_cast
    ring
  have hne : (a (n + 1) : ℝ) * ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) *
      ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) ≠ 0 := by
    positivity
  exact growthDefect_eq_neg_relativeError_add_shiftedCorrection
    hDstep hCstep hEn hEn1 hne

/-- **The eventual bound `0 < Λ_n < 3/a_n` under the standing hypotheses.** -/
theorem canonicalCorrection_pos_and_lt_three_div
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ n, N ≤ n →
      0 < canonicalCorrection a p q n ∧
        canonicalCorrection a p q n < 3 / (a n : ℝ) := by
  obtain ⟨hcpos, hdpos, hc, hd, hrep, hv, _⟩ :=
    canonical_integer_tail_normalized a ha hpos p q hq hs hgrowth
  obtain ⟨N1, hN1⟩ := hv 4
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hgrowth (1 / 2) (by norm_num)
  have hquarter : ∀ n, N1 ≤ n →
      |((canonicalError a p q n : ℤ) : ℝ) /
        ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)| ≤ 1 / 4 := by
    intro n hn
    have hCpos : (0 : ℝ) < ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) := by
      exact_mod_cast hcpos n
    have hnat := hN1 n hn
    have hz : (4 : ℤ) * |canonicalError a p q n| <
        ((canonicalNaturalNumerator a p q n : ℕ) : ℤ) := by
      have h' : ((4 * (canonicalError a p q n).natAbs : ℕ) : ℤ) <
          ((canonicalNaturalNumerator a p q n : ℕ) : ℤ) := by exact_mod_cast hnat
      push_cast [Int.natCast_natAbs] at h'
      exact h'
    have hr : (4 : ℝ) * |((canonicalError a p q n : ℤ) : ℝ)| <
        ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) := by exact_mod_cast hz
    rw [abs_div, abs_of_pos hCpos, div_le_iff₀ hCpos]
    linarith
  have hhalf : ∀ n, N2 ≤ n → (a n : ℝ) ^ 2 / 2 ≤ (a (n + 1) : ℝ) := by
    intro n hn
    have hsq : (0 : ℝ) < (a n : ℝ) ^ 2 := by
      have : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hpos n
      positivity
    have habs : |(a (n + 1) : ℝ) / (a n : ℝ) ^ 2 - 1| < 1 / 2 := by
      simpa only [Real.dist_eq] using hN2 n hn
    have hgt : (1 : ℝ) / 2 < (a (n + 1) : ℝ) / (a n : ℝ) ^ 2 := by
      have := (abs_lt.mp habs).1
      linarith
    have := (lt_div_iff₀ hsq).mp hgt
    linarith
  obtain ⟨N3, hN3⟩ : ∃ N, ∀ n, N ≤ n → 2 ≤ a n := by
    refine ⟨1, fun n hn ↦ ?_⟩
    have h0 := hpos 0
    have hh := ha (show 0 < n by omega)
    omega
  refine ⟨max (max N1 N2) N3, fun n hn ↦ ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left N1 N2) (le_max_left _ _)) hn
  have hn1' : N1 ≤ n + 1 := le_trans hn1 (Nat.le_succ n)
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right N1 N2) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_max_right _ _) hn
  have hA : (2 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast hN3 n hn3
  exact shiftedCorrectionTerm_pos_and_lt_three_div hA (hhalf n hn2)
    (hquarter n hn1) (hquarter (n + 1) hn1')

/-! ## 5. The Erdős–Straus quantity -/

/-- The Erdős–Straus quantity
`Z_n^ES = ([a_0,…,a_n]/a_{n+1})(a_{n+1}²/a_{n+2} - 1)`.  The least common
multiple is the `q = 1` cumulative one: it includes `a_n` and not the clearing
denominator. -/
def erdosStrausQuantity (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (cumulativeDigitLcm 1 a (n + 1) : ℝ) / (a (n + 1) : ℝ) *
    ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ) - 1)

/-- The least common multiple in `Z_n^ES` includes `a_n`, and is the `q = 1`
cumulative one, so it does not include the clearing denominator. -/
theorem erdosStraus_lcm_includes_digit_not_denominator (a : ℕ → ℕ) (n : ℕ) :
    cumulativeDigitLcm 1 a (n + 1) = Nat.lcm (cumulativeDigitLcm 1 a n) (a n) ∧
      a n ∣ cumulativeDigitLcm 1 a (n + 1) ∧
      cumulativeDigitLcm 1 a 0 = 1 :=
  ⟨rfl, Nat.dvd_lcm_right _ _, rfl⟩

/-- A positive integer sequence witnessing the distinctness remark. -/
def witnessDigits : ℕ → ℕ := fun j ↦ j + 2

theorem witnessDigits_pos (j : ℕ) : 0 < witnessDigits j := by
  unfold witnessDigits; omega

/-- `Z_n^ES` is not the product quantity `Q_n = (P_n/a_n) γ_n`, and it is not
`L_n γ_{n+1}/a_{n+1}` for the convention `L_n = lcm(q, a_0, …, a_{n-1})`.
The witness is `a_j = j + 2`, `q = 7`, `n = 1`, where the three values are
`33/10`, `5/6` and `77/10`. -/
theorem erdosStrausQuantity_ne_productDefect_ne_lcmShift :
    ∃ (a : ℕ → ℕ) (q n : ℕ), 0 < q ∧ (∀ m, 0 < a m) ∧
      erdosStrausQuantity a n ≠ productDefect a n ∧
      erdosStrausQuantity a n ≠
        (cumulativeDigitLcm q a n : ℝ) *
          ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ) - 1) / (a (n + 1) : ℝ) := by
  have hlcm1 : cumulativeDigitLcm 1 witnessDigits 2 = 6 := by
    show Nat.lcm (Nat.lcm 1 (witnessDigits 0)) (witnessDigits 1) = 6
    unfold witnessDigits
    norm_num
  have hlcm7 : cumulativeDigitLcm 7 witnessDigits 1 = 14 := by
    show Nat.lcm 7 (witnessDigits 0) = 14
    unfold witnessDigits
    norm_num
  have hprefix : prefixProduct witnessDigits 1 = 2 := by
    unfold prefixProduct witnessDigits
    norm_num
  refine ⟨witnessDigits, 7, 1, by norm_num, witnessDigits_pos, ?_, ?_⟩
  · rw [erdosStrausQuantity, productDefect, hlcm1, hprefix]
    unfold witnessDigits
    norm_num
  · rw [erdosStrausQuantity, hlcm1, hlcm7]
    unfold witnessDigits
    norm_num

/-- **The sign clauses of `long243:res:classicalhalfspace`.**
`Z_n^ES` is a positive multiple of the next growth defect, so it has the sign of
`Λ_{n+1} - E_{n+1}/C_{n+1}`; for all sufficiently large `n` it is positive when
`E_{n+1} ≤ 0`, and for `E_{n+1} > 0` it is negative exactly when
`E_{n+1}/C_{n+1} > Λ_{n+1}`. -/
theorem erdosStrausQuantity_sign
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ n, N ≤ n →
      (0 < erdosStrausQuantity a n ↔
        ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
            ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) <
          canonicalCorrection a p q (n + 1)) ∧
      (erdosStrausQuantity a n < 0 ↔
        canonicalCorrection a p q (n + 1) <
          ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
            ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)) ∧
      (canonicalError a p q (n + 1) ≤ 0 → 0 < erdosStrausQuantity a n) ∧
      (0 < canonicalError a p q (n + 1) →
        (erdosStrausQuantity a n < 0 ↔
          canonicalCorrection a p q (n + 1) <
            ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
              ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ))) := by
  obtain ⟨hcpos, hdpos, hc, hd, hrep⟩ := canonical_integer_tail a hpos p q hq hs
  obtain ⟨N, hN⟩ := canonicalCorrection_pos_and_lt_three_div a ha hpos p q hq hs hgrowth
  refine ⟨N, fun n hn ↦ ?_⟩
  have hLampos : 0 < canonicalCorrection a p q (n + 1) :=
    (hN (n + 1) (le_trans hn (Nat.le_succ n))).1
  have hKpos : (0 : ℝ) < (cumulativeDigitLcm 1 a (n + 1) : ℝ) /
      (a (n + 1) : ℝ) := by
    have h1 : (0 : ℝ) < (cumulativeDigitLcm 1 a (n + 1) : ℝ) := by
      exact_mod_cast cumulativeDigitLcm_pos a hpos 1 (by norm_num) (n + 1)
    have h2 : (0 : ℝ) < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
    exact div_pos h1 h2
  have hident := canonical_growthDefect_identity a hpos p q hq hs (n + 1)
  have hZ : erdosStrausQuantity a n =
      ((cumulativeDigitLcm 1 a (n + 1) : ℝ) / (a (n + 1) : ℝ)) *
        (canonicalCorrection a p q (n + 1) -
          ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
            ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)) := by
    rw [erdosStrausQuantity, hident]
    ring
  have hCpos : (0 : ℝ) < ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcpos (n + 1)
  have hposIff : 0 < erdosStrausQuantity a n ↔
      ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
          ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) <
        canonicalCorrection a p q (n + 1) := by
    rw [hZ]
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      nlinarith [hKpos, h, hcon]
    · intro h
      exact mul_pos hKpos (by linarith)
  have hnegIff : erdosStrausQuantity a n < 0 ↔
      canonicalCorrection a p q (n + 1) <
        ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
          ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) := by
    rw [hZ]
    constructor
    · intro h
      by_contra hcon
      push_neg at hcon
      nlinarith [hKpos, h, hcon]
    · intro h
      exact mul_neg_of_pos_of_neg hKpos (by linarith)
  refine ⟨hposIff, hnegIff, ?_, fun _ ↦ hnegIff⟩
  intro hE
  rw [hposIff]
  have hEle : ((canonicalError a p q (n + 1) : ℤ) : ℝ) ≤ 0 := by
    exact_mod_cast hE
  have : ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
      ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hEle hCpos.le
  linarith

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_dvd_gcd
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.canonicalError_div_overlapDebt
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.growthDefect_eq_neg_relativeError_add_shiftedCorrection
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.canonical_growthDefect_identity
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.sylvesterTail_shiftedCorrection
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.shiftedCorrectionTerm_pos_and_lt_three_div
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.canonicalCorrection_pos_and_lt_three_div
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.erdosStraus_lcm_includes_digit_not_denominator
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_ne_productDefect_ne_lcmShift
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_sign

end ErdosProblems.Erdos243.PaperCompleteR21
