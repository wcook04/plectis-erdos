import ErdosProblems.Erdos257.FourNinthsCofinalRepairConsumer
import Erdos257PeriodNoncollapse.AllBaseReciprocalSupportIrrationality

/-!
# Finite repair deadlines and return transport

The September 2026 return batch proves a converse to the cofinal repair
consumer in ordinary mathematics. Combining that converse with the existing
support-uniform square-root tail bound gives more: every surviving orbit
repairs within a square-root sized window. This is an exact equivalence at
4/9, not a proof that the repair producer holds.

The analytic returns also use close returns outside reciprocal summability.
Their radix transport must therefore accept close returns directly, without
silently retaining the older reciprocal-summability hypothesis.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse Filter

noncomputable section

/-- A natural sequence in the square-root strip cannot strictly increase
through a window of length `2 * sqrt K + 12`. No recurrence is assumed. -/
theorem exists_repair_in_sqrt_window
    (Q : ℕ → ℕ)
    (hQ : ∀ N, (Q N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) + 4)
    (K : ℕ) :
    ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧ Q (N + 1) ≤ Q N := by
  by_contra hnone
  push Not at hnone
  let s := Nat.sqrt K
  let T := 2 * s + 12
  have hinc : ∀ j < T, Q (K + j) < Q (K + j + 1) := by
    intro j hj
    exact hnone (K + j) (by omega) (by dsimp [T, s] at hj ⊢; omega)
  have hgrow : ∀ j, j ≤ T → Q K + j ≤ Q (K + j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro hj
        have := ih (by omega)
        have := hinc j (by omega)
        simpa [Nat.add_assoc] using (show Q K + (j + 1) ≤ Q (K + j + 1) by omega)
  have hlow : (T : ℝ) ≤ (Q (K + T) : ℝ) := by
    exact_mod_cast (show T ≤ Q (K + T) by have := hgrow T le_rfl; omega)
  have hk : K < (s + 1) * (s + 1) := by
    exact Nat.lt_succ_sqrt K
  have hs : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hkR : (K : ℝ) < ((s : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' K
  have htR : (T : ℝ) = 2 * (s : ℝ) + 12 := by simp [T]
  have hroot : Real.sqrt ((K + T : ℕ) : ℝ) < (s : ℝ) + 4 := by
    apply (Real.sqrt_lt' (by positivity)).2
    push_cast
    nlinarith
  have hupper := hQ (K + T)
  linarith

/-- Under actual membership the floor defect lies in the support-uniform
square-root strip at every rank, including selected ranks. -/
theorem fourNinthsGreedyDefect_le_sqrt_of_mem
    (hmem : (4 / 9 : ℝ) ∈ mersenneAchievementSet) (N : ℕ) :
    (fourNinthsGreedyDefect N : ℝ) ≤ 2 * Real.sqrt (N : ℝ) + 4 := by
  rcases hmem with ⟨A, hA0, hvalue⟩
  have hsupport : greedyMersenneSupport (4 / 9 : ℝ) = A := by
    rw [hvalue]
    exact greedySupport_supportValue_eq A hA0
  have hseries : binaryCoeffSeries (supportCoeff A) = (4 / 9 : ℝ) := by
    rw [← erdosSupportSeries_two_eq_binaryCoeffSeries,
      ← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  have hsplit := binaryCoeffSeries_eq_prefix_add_tail
    (supportCoeff A) (supportCoeff_le_self A) N
  have hnum := binaryCoeffPrefixNumerator_div_pow (supportCoeff A) N
  have hp : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have htailEq : (2 : ℝ) ^ N * (4 / 9 : ℝ) -
      (binaryCoeffPrefixNumerator (supportCoeff A) N : ℝ) =
      binaryCoeffTail (supportCoeff A) N := by
    rw [hseries, ← hnum] at hsplit
    field_simp at hsplit
    nlinarith
  have hfloor : (fourNinthsBinaryFloor N : ℝ) ≤ (2 : ℝ) ^ N * (4 / 9 : ℝ) := by
    have h : 9 * fourNinthsBinaryFloor N ≤ 4 * 2 ^ N := by
      have hd := Nat.div_mul_le_self (4 * 2 ^ N) 9
      simpa [fourNinthsBinaryFloor, Nat.mul_comm] using hd
    have hR : (9 : ℝ) * (fourNinthsBinaryFloor N : ℝ) ≤ 4 * (2 : ℝ) ^ N := by
      exact_mod_cast h
    linarith
  have hcast : (fourNinthsGreedyDefect N : ℝ) =
      (fourNinthsBinaryFloor N : ℝ) -
      (binaryCoeffPrefixNumerator (supportCoeff A) N : ℝ) := by
    have h := fourNinthsGreedyDefect_cast_eq N
    rw [hsupport] at h
    exact_mod_cast h
  have ht := binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A N
  linarith

/-- A stronger necessary condition than cofinality: there is a repair in
every explicit square-root window. -/
theorem fourNinths_repair_sqrt_window_of_mem
    (hmem : (4 / 9 : ℝ) ∈ mersenneAchievementSet) (K : ℕ) :
    ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
      FourNinthsOneStepRepairSucc N := by
  obtain ⟨N, hKN, hN, hrep⟩ := exists_repair_in_sqrt_window
    fourNinthsGreedyDefect (fourNinthsGreedyDefect_le_sqrt_of_mem hmem) K
  refine ⟨N, hKN, hN, ?_⟩
  unfold FourNinthsOneStepRepairSucc
  exact_mod_cast hrep

/-- The old sufficient producer is also necessary. The equivalence is
target-specific and does not promote 4/9 membership to universal #257. -/
theorem four_ninths_mem_iff_repairCofinal :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔ FourNinthsOneStepRepairCofinal := by
  constructor
  · intro h K
    obtain ⟨N, hKN, _, hr⟩ := fourNinths_repair_sqrt_window_of_mem h K
    exact ⟨N, hKN, hr⟩
  · exact four_ninths_mem_mersenneAchievementSet_of_repairCofinal

/-- A finite-window formulation exactly equivalent to 4/9 membership. -/
theorem four_ninths_mem_iff_repair_sqrt_windows :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ N, K ≤ N ∧ N < K + 2 * Nat.sqrt K + 12 ∧
        FourNinthsOneStepRepairSucc N := by
  constructor
  · exact fourNinths_repair_sqrt_window_of_mem
  · intro h
    apply four_ninths_mem_mersenneAchievementSet_of_repairCofinal
    intro K
    obtain ⟨N, hKN, _, hr⟩ := h K
    exact ⟨N, hKN, hr⟩

/-- One certified window of strict increases excludes the target. -/
theorem four_ninths_not_mem_of_strict_sqrt_window
    (K : ℕ)
    (h : ∀ N, K ≤ N → N < K + 2 * Nat.sqrt K + 12 →
      fourNinthsGreedyDefect N < fourNinthsGreedyDefect (N + 1)) :
    (4 / 9 : ℝ) ∉ mersenneAchievementSet := by
  intro hm
  obtain ⟨N, hKN, hN, hr⟩ := fourNinths_repair_sqrt_window_of_mem hm K
  have hrN : fourNinthsGreedyDefect (N + 1) ≤ fourNinthsGreedyDefect N := by
    unfold FourNinthsOneStepRepairSucc at hr
    exact_mod_cast hr
  exact (not_le_of_gt (h N hKN hN)) hrN

/-- The all-base lattice endgame accepts the close-return property itself.
The weighted and fractional returns need no reciprocal-summability premise. -/
theorem irrational_erdosSupportSeries_of_radix_closeReturn
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
      (∑' d : ℕ, shiftedRadixSupportAtom b A N d) <
        (∑' d : ℕ, shiftedRadixSupportAtom b A 0 d) + ε) :
    Irrational (erdosSupportSeries b A) := by
  by_contra hrat
  have hvalue : HasRationalValue (erdosSupportSeries b A) :=
    (hasRationalValue_iff_not_irrational _).2 hrat
  obtain ⟨p, v, hv, hratValue⟩ := hvalue
  let T : ℕ → ℝ := fun N =>
    ∑' d : ℕ, shiftedRadixSupportAtom b A N d
  let u : ℕ → ℤ := Nat.rec p
    (fun N z => (b : ℤ) * z - ((v * supportCoeff A (N + 1) : ℕ) : ℤ))
  have hu0 : u 0 = p := rfl
  have huSucc : ∀ N : ℕ,
      u (N + 1) =
        (b : ℤ) * u N - ((v * supportCoeff A (N + 1) : ℕ) : ℤ) := by
    intro N
    rfl
  have hT0 : T 0 = erdosSupportSeries b A := by
    exact tsum_shiftedRadixSupportAtom_zero b A
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have huCast : ∀ N : ℕ, ((u N).cast : ℝ) = (v : ℝ) * T N := by
    intro N
    induction N with
    | zero =>
        rw [hu0, hT0, hratValue]
        field_simp
    | succ N ih =>
        rw [huSucc]
        push_cast
        rw [ih]
        have hstep := tsum_shiftedRadixSupportAtom_step b A N hb
        change (b : ℝ) * ((v : ℝ) * T N) -
            (v : ℝ) * supportCoeff A (N + 1) = (v : ℝ) * T (N + 1)
        change (b : ℝ) * T N - T (N + 1) =
            supportCoeff A (N + 1) at hstep
        nlinarith
  obtain ⟨N, hN, hnear⟩ :=
    hclose (1 / (v : ℝ)) (by positivity)
  have hstrict :=
    shiftedRadixSupportAtom_zero_strictMinimum b A hb hA N hN
  have hstrictT : T 0 < T N := by
    simpa [T] using hstrict
  have hnearT : T N < T 0 + 1 / (v : ℝ) := by
    simpa [T] using hnear
  have hgapPos : (0 : ℝ) < ((u N - u 0 : ℤ) : ℝ) := by
    push_cast
    rw [huCast N, huCast 0]
    nlinarith [mul_pos hvR (sub_pos.mpr hstrictT)]
  have hgapLt : ((u N - u 0 : ℤ) : ℝ) < 1 := by
    push_cast
    rw [huCast N, huCast 0]
    have htailGap : T N - T 0 < 1 / (v : ℝ) := by
      exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hnearT)
    have hmul := mul_lt_mul_of_pos_left htailGap hvR
    have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
    rw [show (v : ℝ) * (1 / (v : ℝ)) = 1 by field_simp] at hmul
    nlinarith
  have hgapPosInt : 0 < u N - u 0 := by exact_mod_cast hgapPos
  have hgapLtInt : u N - u 0 < 1 := by exact_mod_cast hgapLt
  omega


#print axioms exists_repair_in_sqrt_window
#print axioms four_ninths_mem_iff_repair_sqrt_windows
#print axioms four_ninths_not_mem_of_strict_sqrt_window
#print axioms irrational_erdosSupportSeries_of_radix_closeReturn

end
end ErdosProblems.Erdos257
