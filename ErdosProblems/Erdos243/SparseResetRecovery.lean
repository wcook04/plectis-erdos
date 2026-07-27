import ErdosProblems.Erdos243.ReciprocalTailRigidity
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős #243: the finite negative-mass endpoint

This module isolates the shortest checked consumer for the current frontier.
If the normalized negative part of the centered defect is summable, then the
natural tail state is eventually bounded.  Division-free normalized defect
vanishing then makes the integral defect eventually zero, so the original
denominators eventually follow the Sylvester recurrence.

The unrestricted problem is not claimed: a surviving counterexample must have
divergent normalized negative mass.
-/

namespace ErdosProblems.Erdos243

/-- A uniformly bounded positive tail and division-free normalized vanishing
force the integral centered state to vanish eventually. -/
theorem eventually_zero_of_bounded_tail_normalizedVanishes
    (C : ℕ → ℕ) (E : ℕ → ℤ) (M : ℕ)
    (hbound : ∀ n, C n ≤ M)
    (hvanish :
      ∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  obtain ⟨N, hN⟩ := hvanish (M + 1)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hsmall := hN n hn
  have habs : Int.natAbs (E n) = 0 := by
    by_contra hne
    have : 0 < Int.natAbs (E n) := Nat.pos_of_ne_zero hne
    have := hbound n
    nlinarith
  exact Int.natAbs_eq_zero.mp habs

/-- The normalized negative mass of an integral tail step. -/
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n

/-- The exact update `Cₙ₊₁ = Cₙ - Eₙ` is bounded above by multiplication by
`1 + negativeRelativeMass`. -/
theorem tail_growth_le_one_add_negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hstep :
      ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) :
    ∀ n,
      (C (n + 1) : ℝ) ≤
        C n * (1 + negativeRelativeMass C E n) := by
  intro n
  have hCne : (C n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hCpos n))
  by_cases he : E n ≤ 0
  · have hmin : min (E n) 0 = E n := min_eq_left he
    have habscast :
        (Int.natAbs (E n) : ℤ) = -E n :=
      Int.ofNat_natAbs_of_nonpos he
    have hstepR :
        (C (n + 1) : ℝ) =
          (C n : ℝ) - (E n : ℝ) := by
      exact_mod_cast hstep n
    rw [negativeRelativeMass, hmin]
    have habsR :
        (Int.natAbs (E n) : ℝ) = -(E n : ℝ) := by
      calc
        (Int.natAbs (E n) : ℝ) =
            (((Int.natAbs (E n) : ℕ) : ℤ) : ℝ) := by norm_num
        _ = ((-E n : ℤ) : ℝ) := by rw [habscast]
        _ = -(E n : ℝ) := by norm_num
    rw [habsR, hstepR]
    apply le_of_eq
    field_simp [hCne]
    ring
  · have hepos : 0 ≤ E n := by omega
    have hmin : min (E n) 0 = 0 := min_eq_right hepos
    have hstepR :
        (C (n + 1) : ℝ) =
          (C n : ℝ) - (E n : ℝ) := by
      exact_mod_cast hstep n
    rw [negativeRelativeMass, hmin]
    simp only [Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, mul_one]
    rw [hstepR]
    exact sub_le_self _ (by exact_mod_cast hepos)

/-- Summable nonnegative relative growth makes the integral tail eventually
bounded; division-free normalized vanishing then forces eventual zero. -/
theorem eventually_zero_of_summable_relativeGrowth
    (C : ℕ → ℕ) (E : ℕ → ℤ) (δ : ℕ → ℝ)
    (hδ : ∀ n, 0 ≤ δ n)
    (hsum : Summable δ)
    (hgrowth :
      ∀ n, (C (n + 1) : ℝ) ≤ C n * (1 + δ n))
    (hvanish :
      ∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  have hCprod : ∀ N,
      (C N : ℝ) ≤
        C 0 * (∏ i ∈ Finset.range N, (1 + δ i)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        calc
          (C (N + 1) : ℝ) ≤ C N * (1 + δ N) := hgrowth N
          _ ≤ (C 0 *
                (∏ i ∈ Finset.range N, (1 + δ i))) *
              (1 + δ N) :=
                mul_le_mul_of_nonneg_right ih (by linarith [hδ N])
          _ = C 0 *
              (∏ i ∈ Finset.range (N + 1), (1 + δ i)) := by
                rw [Finset.prod_range_succ]
                ring
  have hmulti : Multipliable (fun n ↦ 1 + δ n) :=
    Real.multipliable_one_add_of_summable hsum
  obtain ⟨R, hRpos, s, hs⟩ :=
    hmulti.eventually_bounded_finset_prod
  obtain ⟨N₀, hsRange⟩ := Finset.exists_nat_subset_range s
  obtain ⟨M, hM⟩ :=
    exists_nat_gt ((C 0 : ℝ) * R)
  have hMpos : 0 < M := by
    have hnonneg : 0 ≤ (C 0 : ℝ) * R :=
      mul_nonneg (by positivity) hRpos.le
    exact_mod_cast hnonneg.trans_lt hM
  obtain ⟨N₁, hN₁⟩ := hvanish M
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  have hn₀ : N₀ ≤ n := (Nat.le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (Nat.le_max_right _ _).trans hn
  have hprod :
      (∏ i ∈ Finset.range n, (1 + δ i)) ≤ R := by
    apply hs
    exact hsRange.trans (Finset.range_mono hn₀)
  have hCnReal : (C n : ℝ) < M := by
    calc
      (C n : ℝ) ≤
          C 0 * (∏ i ∈ Finset.range n, (1 + δ i)) :=
            hCprod n
      _ ≤ C 0 * R :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
      _ < M := hM
  have hCn : C n < M := by exact_mod_cast hCnReal
  have herr := hN₁ n hn₁
  have habs : Int.natAbs (E n) = 0 := by
    by_contra hne
    have habspos : 0 < Int.natAbs (E n) :=
      Nat.pos_of_ne_zero hne
    nlinarith
  exact Int.natAbs_eq_zero.mp habs

/-- Finite normalized negative mass forces the integral centered state to
vanish eventually. -/
theorem eventually_zero_of_summable_negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hstep :
      ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n)
    (hvanish :
      ∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (E n) < C n)
    (hsum : Summable (negativeRelativeMass C E)) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  apply eventually_zero_of_summable_relativeGrowth
    C E (negativeRelativeMass C E)
  · intro n
    exact div_nonneg (by positivity) (by positivity)
  · exact hsum
  · exact tail_growth_le_one_add_negativeRelativeMass C E hCpos hstep
  · exact hvanish

/-- Paper-facing endpoint: finite normalized negative mass forces the exact
reciprocal-tail orbit to follow the Sylvester recurrence eventually. -/
theorem sylvesterNext_eventually_of_summable_negativeRelativeMass
    (a D : ℕ → ℤ) (C : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC :
      ∀ n, (C (n + 1) : ℤ) =
        nextTailState (a n) (D n) (C n))
    (hCpos : ∀ n, 0 < C n)
    (hstep :
      ∀ n, (C (n + 1) : ℤ) =
        (C n : ℤ) - centeredState (a n) (D n) (C n))
    (hvanish :
      ∀ K, ∃ N, ∀ n, N ≤ n →
        K * Int.natAbs (centeredState (a n) (D n) (C n)) < C n)
    (hsum :
      Summable
        (negativeRelativeMass C
          (fun n ↦ centeredState (a n) (D n) (C n)))) :
    ∃ N, ∀ n, N ≤ n →
      a (n + 1) = sylvesterNext (a n) := by
  have hzero :
      ∃ N, ∀ n, N ≤ n →
        centeredState (a n) (D n) (C n) = 0 :=
    eventually_zero_of_summable_negativeRelativeMass
      C (fun n ↦ centeredState (a n) (D n) (C n))
      hCpos hstep hvanish hsum
  apply sylvesterNext_eventually_of_centered_zero
    a D (fun n ↦ (C n : ℤ)) hD
  · intro n
    exact hC n
  · exact hzero
  · refine ⟨0, fun n _hn ↦ ?_⟩
    exact_mod_cast (Nat.ne_of_gt (hCpos (n + 1)))

end ErdosProblems.Erdos243
