import Erdos249257.FirstHarmonicPivot

/-! The first clause of the long #249 paper's `prop:dickman`
("A one-sided bound for the unassigned terms").

`prop:dickman` asserts four things: (a) an unassigned `n = N + t` has
`P(n) ≤ y_X` with `y_X = 4√X + 2t/√X`; (b) the resulting count is at most
`Ψ(2X+t-1, y_X) - Ψ(X+t-1, y_X)`; (c) that difference is `(1 - log 2 + o(1))X`;
(d) hence `< (8/25)X` eventually.  Clauses (b)–(d) need the smooth-number
counting function `Ψ` and Dickman's `ρ`, neither of which exists in Mathlib or
in this tree, plus the paper's cited fixed-`u` asymptotic.

Clause (a) is elementary and is proved here against the tree's own assignment
predicate.  The paper's assigned set `𝒜` is
`Erdos249257.TotientTailPeriodKiller.pivotSupplierBases X L s`, its offset `t`
is `pivotOffset L s = L - s + 1`, its `n = N + t` is `pivotArgument N L s`, and
its `P(n)`, `m = n/P(n)` are `pivotPrime`, `pivotCofactor`. -/

namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-- The paper's smoothness cut `y_X = 4√X + 2t/√X`. -/
noncomputable def dickmanCut (X t : ℕ) : ℝ :=
  4 * Real.sqrt X + 2 * (t : ℝ) / Real.sqrt X

private theorem natSqrt_le_sqrt (X : ℕ) : ((Nat.sqrt X : ℕ) : ℝ) ≤ Real.sqrt X := by
  have hsq_le : Nat.sqrt X * Nat.sqrt X ≤ X := by
    first
      | exact Nat.sqrt_le' X
      | exact Nat.sqrt_le X
      | exact Nat.le_sqrt.mp le_rfl
  have h2 : ((Nat.sqrt X : ℕ) : ℝ) * ((Nat.sqrt X : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hsq_le
  have h1 : ((Nat.sqrt X : ℕ) : ℝ) ^ 2 ≤ (X : ℝ) := by nlinarith [h2]
  have h3 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (by positivity)] at h3

private theorem sqrt_lt_natSqrt_succ (X : ℕ) :
    Real.sqrt X < ((Nat.sqrt X : ℕ) : ℝ) + 1 := by
  have hsq_lt : X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := by
    first
      | exact Nat.lt_succ_sqrt' X
      | exact Nat.lt_succ_sqrt X
      | exact Nat.sqrt_lt.mp (Nat.lt_succ_self _)
  have h2 : (X : ℝ) < (((Nat.sqrt X : ℕ) : ℝ) + 1) * (((Nat.sqrt X : ℕ) : ℝ) + 1) := by
    exact_mod_cast hsq_lt
  have h1 : (X : ℝ) < (((Nat.sqrt X : ℕ) : ℝ) + 1) ^ 2 := by nlinarith [h2]
  have h3 : Real.sqrt X < Real.sqrt ((((Nat.sqrt X : ℕ) : ℝ) + 1) ^ 2) :=
    Real.sqrt_lt_sqrt (by positivity) h1
  rwa [Real.sqrt_sq (by positivity)] at h3

/-- The tree's canonical selector really is the largest prime factor, with no
hypothesis relating the cofactor to the prime. -/
theorem pivotPrime_eq_max_primeFactor {N L s : ℕ} (hn : 1 < pivotArgument N L s) :
    pivotPrime N L s
      = (pivotArgument N L s).primeFactors.max' (Nat.nonempty_primeFactors.mpr hn) := by
  have hPmem : (pivotArgument N L s).primeFactors.max' (Nat.nonempty_primeFactors.mpr hn)
      ∈ (pivotArgument N L s).primeFactors := Finset.max'_mem _ _
  have hPprime : ((pivotArgument N L s).primeFactors.max'
      (Nat.nonempty_primeFactors.mpr hn)).Prime := Nat.prime_of_mem_primeFactors hPmem
  have hmem : (pivotArgument N L s).primeFactors.max' (Nat.nonempty_primeFactors.mpr hn)
      ∈ (pivotArgument N L s).primeFactors.toList := Finset.mem_toList.mpr hPmem
  have hnil := List.ne_nil_of_mem hmem
  have hmax : ((pivotArgument N L s).primeFactors.toList).max hnil
      = (pivotArgument N L s).primeFactors.max' (Nat.nonempty_primeFactors.mpr hn) := by
    apply (List.max_eq_iff hnil).2
    refine ⟨hmem, ?_⟩
    intro q hq
    exact Finset.le_max' _ q (Finset.mem_toList.mp hq)
  rw [pivotPrime]
  rw [List.foldl_max_eq_max hnil, hmax, Nat.max_eq_right hPprime.one_le]

/-- **`prop:dickman`, clause (a).**  If `N ∈ [X, 2X)` is unassigned and the
shifted argument `n = N + t` exceeds `1`, then `P(n) ≤ y_X = 4√X + 2t/√X`. -/
theorem largest_prime_factor_le_dickmanCut {X L s N : ℕ}
    (hX : 0 < X) (hN : N < 2 * X)
    (hn : 1 < pivotArgument N L s)
    (hnot : ¬ pivotSupplier X L s N) :
    (((pivotArgument N L s).primeFactors.max'
        (Nat.nonempty_primeFactors.mpr hn) : ℕ) : ℝ)
      ≤ dickmanCut X (pivotOffset L s) := by
  have hP := pivotPrime_eq_max_primeFactor hn
  set P := (pivotArgument N L s).primeFactors.max' (Nat.nonempty_primeFactors.mpr hn) with hPdef
  have hPmem : P ∈ (pivotArgument N L s).primeFactors := Finset.max'_mem _ _
  have hPprime : P.Prime := Nat.prime_of_mem_primeFactors hPmem
  have hPdvd : P ∣ pivotArgument N L s := Nat.dvd_of_mem_primeFactors hPmem
  have hmdef : pivotCofactor N L s = pivotArgument N L s / P := by rw [pivotCofactor, hP]
  have hmul : pivotCofactor N L s * P = pivotArgument N L s := by
    rw [hmdef]; exact Nat.div_mul_cancel hPdvd
  have hmpos : 0 < pivotCofactor N L s := by
    rcases Nat.eq_zero_or_pos (pivotCofactor N L s) with h0 | h0
    · rw [h0, zero_mul] at hmul; omega
    · exact h0
  have hsupp_iff : pivotSupplier X L s N ↔
      (pivotPrime N L s).Prime ∧
      pivotCofactor N L s * pivotPrime N L s = pivotArgument N L s ∧
      0 < pivotCofactor N L s ∧
      pivotCofactor N L s ≤ Nat.sqrt X / 2 ∧
      2 * Nat.sqrt X < pivotPrime N L s := Iff.rfl
  rw [hsupp_iff] at hnot
  push_neg at hnot
  have hPP : (pivotPrime N L s).Prime := by rw [hP]; exact hPprime
  have hmulP : pivotCofactor N L s * pivotPrime N L s = pivotArgument N L s := by
    rw [hP]; exact hmul
  have hsxpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by exact_mod_cast hX)
  have hsx : ((Nat.sqrt X : ℕ) : ℝ) ≤ Real.sqrt X := natSqrt_le_sqrt X
  have hnn : (0 : ℝ) ≤ 2 * ((pivotOffset L s : ℕ) : ℝ) / Real.sqrt X := by positivity
  by_cases hle : pivotCofactor N L s ≤ Nat.sqrt X / 2
  · have hlt := hnot hPP hmulP hmpos hle
    rw [hP] at hlt
    have hle2 : P ≤ 2 * Nat.sqrt X := by omega
    have hPR : (P : ℝ) ≤ 2 * ((Nat.sqrt X : ℕ) : ℝ) := by exact_mod_cast hle2
    rw [dickmanCut]
    linarith
  · have h2m : Nat.sqrt X + 1 ≤ 2 * pivotCofactor N L s := by omega
    have h1 : ((Nat.sqrt X : ℕ) : ℝ) + 1 ≤ 2 * ((pivotCofactor N L s : ℕ) : ℝ) := by
      exact_mod_cast h2m
    have h2 := sqrt_lt_natSqrt_succ X
    have h2mR : Real.sqrt X < 2 * ((pivotCofactor N L s : ℕ) : ℝ) := by linarith
    have hnltN : pivotArgument N L s < 2 * X + pivotOffset L s := by
      rw [pivotArgument]; omega
    have hnlt : (pivotArgument N L s : ℝ) < 2 * (X : ℝ) + ((pivotOffset L s : ℕ) : ℝ) := by
      exact_mod_cast hnltN
    have hmulR : ((pivotCofactor N L s : ℕ) : ℝ) * (P : ℝ) = (pivotArgument N L s : ℝ) := by
      exact_mod_cast hmul
    have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hPprime.pos
    have hstep : (P : ℝ) * Real.sqrt X < 2 * (2 * (X : ℝ) + ((pivotOffset L s : ℕ) : ℝ)) := by
      have ha : (P : ℝ) * Real.sqrt X < (P : ℝ) * (2 * ((pivotCofactor N L s : ℕ) : ℝ)) :=
        mul_lt_mul_of_pos_left h2mR hPpos
      have hb : (P : ℝ) * (2 * ((pivotCofactor N L s : ℕ) : ℝ))
          = 2 * (pivotArgument N L s : ℝ) := by rw [← hmulR]; ring
      linarith
    have hsqrtsq : Real.sqrt X * Real.sqrt X = (X : ℝ) := Real.mul_self_sqrt (by positivity)
    have hgoal : (P : ℝ)
        ≤ (4 * (X : ℝ) + 2 * ((pivotOffset L s : ℕ) : ℝ)) / Real.sqrt X := by
      rw [le_div_iff₀ hsxpos]
      linarith
    have h4 : 4 * Real.sqrt X = 4 * (X : ℝ) / Real.sqrt X := by
      rw [eq_div_iff hsxpos.ne']
      nlinarith [hsqrtsq]
    rw [dickmanCut, h4, ← add_div]
    exact hgoal

/-- The `y_X`-smoothness form of clause (a): every prime factor of an
unassigned `n = N + t` is at most `y_X`. -/
theorem primeFactors_le_dickmanCut {X L s N : ℕ}
    (hX : 0 < X) (hN : N < 2 * X)
    (hn : 1 < pivotArgument N L s)
    (hnot : ¬ pivotSupplier X L s N) :
    ∀ q ∈ (pivotArgument N L s).primeFactors, (q : ℝ) ≤ dickmanCut X (pivotOffset L s) := by
  intro q hq
  have hle : q ≤ (pivotArgument N L s).primeFactors.max'
      (Nat.nonempty_primeFactors.mpr hn) := Finset.le_max' _ q hq
  have hmax := largest_prime_factor_le_dickmanCut hX hN hn hnot
  have hq' : (q : ℝ) ≤ (((pivotArgument N L s).primeFactors.max'
      (Nat.nonempty_primeFactors.mpr hn) : ℕ) : ℝ) := by exact_mod_cast hle
  linarith

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.pivotPrime_eq_max_primeFactor
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.largest_prime_factor_le_dickmanCut
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.primeFactors_le_dickmanCut
