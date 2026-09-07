import ErdosProblems.Erdos243.PaperCompleteR7.Arithmetic

/-!
# Counterexamples to literal long-record assertions

Uncompiled Lean candidates.  Exact arithmetic is also replayed by the
independent Python checker, which is NOT described as kernel verification.

The phase-free cubic witness is an INFINITE positive primitive orbit.
All its multipliers exceed one and its four agreements are at the actual
indices 1,2,3,4.  It is not merely a finite word with missing extension data.
The valid phase-specific modulo-seven theorems are unaffected.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7.Counterexamples

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private def GoodPair (s : ℕ × ℕ) : Prop :=
  0 < s.1 ∧ 0 < s.2 ∧ Nat.Coprime s.1 s.2

/-- A total extension operation with positive next numerator. -/
private def extendPair (s : ℕ × ℕ) : ℕ × ℕ :=
  ((s.2 + 1) * (s.1 - 1) + 1, (s.2 + 1) * s.2)

private theorem succ_coprime (v : ℕ) : Nat.Coprime (v + 1) v := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  have hdv : Nat.gcd (v + 1) v ∣ v := Nat.gcd_dvd_right (v + 1) v
  have hds : Nat.gcd (v + 1) v ∣ v + 1 := Nat.gcd_dvd_left (v + 1) v
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right hdv).mpr hds)

private theorem extendPair_step (s : ℕ × ℕ) (hs : GoodPair s) :
    (extendPair s).1 + s.2 = (s.2 + 1) * s.1 ∧
    (extendPair s).2 = (s.2 + 1) * s.2 := by
  have hu : s.1 - 1 + 1 = s.1 := Nat.sub_add_cancel hs.1
  constructor
  · dsimp [extendPair]
    nlinarith
  · rfl

private theorem extendPair_good (s : ℕ × ℕ) (hs : GoodPair s) :
    GoodPair (extendPair s) := by
  have hstep := (extendPair_step s hs).1
  have hid := rawNext_gcd_exact_overlap hs.2.2 hstep
  have hg : Nat.gcd (s.2 + 1) s.2 = 1 := (succ_coprime s.2).gcd_eq_one
  dsimp only at hid
  rw [hg] at hid
  refine ⟨by dsimp [extendPair]; omega, ?_, ?_⟩
  · dsimp [extendPair]
    exact Nat.mul_pos (by omega) hs.2.1
  · apply Nat.coprime_iff_gcd_eq_one.mpr
    simpa only [Nat.div_one, Nat.gcd_one_right, Nat.mul_one] using hid

private def continuation : ℕ → ℕ × ℕ
  | 0 => (241, 4107290841814252701946720110)
  | n + 1 => extendPair (continuation n)

private theorem continuation_good (n : ℕ) : GoodPair (continuation n) := by
  induction n with
  | zero => exact ⟨by norm_num [continuation], by norm_num [continuation], by norm_num [continuation, Nat.Coprime]⟩
  | succ n ih => exact extendPair_good (continuation n) ih

/-- Explicit first four transitions, followed by the primitive extension. -/
def cubicCounterPair : ℕ → ℕ × ℕ
  | 0 => (12289, 24565)
  | 1 => (13, 49130)
  | 2 => (49, 185858790)
  | 3 => (121, 704969638962810)
  | n + 4 => continuation n

def cubicCounterMultiplier : ℕ → ℕ
  | 0 => 2
  | 1 => 3783
  | 2 => 3793039
  | 3 => 5826195363331
  | n + 4 => (continuation n).2 + 1

private theorem cubicCounter_good (n : ℕ) : GoodPair (cubicCounterPair n) := by
  rcases n with _ | n
  · exact ⟨by norm_num [continuation, cubicCounterPair], by norm_num [continuation, cubicCounterPair], by norm_num [continuation, cubicCounterPair, Nat.Coprime]⟩
  rcases n with _ | n
  · exact ⟨by norm_num [continuation, cubicCounterPair], by norm_num [continuation, cubicCounterPair], by norm_num [continuation, cubicCounterPair, Nat.Coprime]⟩
  rcases n with _ | n
  · exact ⟨by norm_num [continuation, cubicCounterPair], by norm_num [continuation, cubicCounterPair], by norm_num [continuation, cubicCounterPair, Nat.Coprime]⟩
  rcases n with _ | n
  · exact ⟨by norm_num [continuation, cubicCounterPair], by norm_num [continuation, cubicCounterPair], by norm_num [continuation, cubicCounterPair, Nat.Coprime]⟩
  exact continuation_good n

private theorem cubicCounter_multiplier_gt_one (n : ℕ) :
    1 < cubicCounterMultiplier n := by
  rcases n with _ | n
  · decide
  rcases n with _ | n
  · decide
  rcases n with _ | n
  · decide
  rcases n with _ | n
  · decide
  change 1 < (continuation n).2 + 1
  have hp := (continuation_good n).2.1
  omega

private theorem cubicCounter_step (n : ℕ) :
    (cubicCounterPair (n + 1)).1 + (cubicCounterPair n).2 =
      cubicCounterMultiplier n * (cubicCounterPair n).1 ∧
    (cubicCounterPair (n + 1)).2 =
      cubicCounterMultiplier n * (cubicCounterPair n).2 := by
  rcases n with _ | n
  · decide
  rcases n with _ | n
  · decide
  rcases n with _ | n
  · decide
  rcases n with _ | n
  · decide
  exact extendPair_step (continuation n) (continuation_good n)

/-- An infinite primitive positive orbit, with all a_n > 1, agreeing with
2n(n+1)(n+2)+1 at n=1,2,3,4.  This is an exact counterexample to the first
clause of long-record `res:modseven` as printed. -/
theorem infinite_primitive_four_cubic_agreements :
    ∃ a u v : ℕ → ℕ,
      (∀ n, 1 < a n) ∧
      (∀ n, 0 < u n) ∧ (∀ n, 0 < v n) ∧
      (∀ n, Nat.Coprime (u n) (v n)) ∧
      (∀ n, u (n + 1) + v n = a n * u n) ∧
      (∀ n, v (n + 1) = a n * v n) ∧
      (∀ i : Fin 4, u (1 + i.val) =
        2 * (1 + i.val) * (2 + i.val) * (3 + i.val) + 1) := by
  refine ⟨cubicCounterMultiplier,
    (fun n ↦ (cubicCounterPair n).1),
    (fun n ↦ (cubicCounterPair n).2),
    cubicCounter_multiplier_gt_one,
    (fun n ↦ (cubicCounter_good n).1),
    (fun n ↦ (cubicCounter_good n).2.1),
    (fun n ↦ (cubicCounter_good n).2.2),
    (fun n ↦ (cubicCounter_step n).1),
    (fun n ↦ (cubicCounter_step n).2), ?_⟩
  intro i
  fin_cases i <;> decide

/-- The exact universally quantified claim defeated by the witness.
No density bound is refuted by this theorem. -/
def PhaseFreeCubicExclusion : Prop :=
  ∀ a u v : ℕ → ℕ,
    (∀ n, 1 < a n) →
    (∀ n, 0 < u n) → (∀ n, 0 < v n) →
    (∀ n, Nat.Coprime (u n) (v n)) →
    (∀ n, u (n + 1) + v n = a n * u n) →
    (∀ n, v (n + 1) = a n * v n) →
    ∀ N : ℕ, ¬ ∀ i : Fin 4,
      u (N + i.val) = 2 * (N + i.val) * (N + i.val + 1) * (N + i.val + 2) + 1

theorem not_phase_free_cubic_exclusion : ¬ PhaseFreeCubicExclusion := by
  intro h
  obtain ⟨a, u, v, ha, hu, hv, hcop, hs, hd, hw⟩ :=
    infinite_primitive_four_cubic_agreements
  apply h a u v ha hu hv hcop hs hd 1
  intro i
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hw i

/-- Long record `res:classicalhalfspace`: the equality case gives gamma=0,
not the negative sign of -E.  All constants are exact rationals. -/
theorem shifted_sign_equality_counterexample :
    nextTailState 2 5 4 = 3 ∧
    nextDenState 2 5 = 10 ∧
    centeredState 2 5 4 = 1 ∧
    centeredState 4 10 3 = 1 ∧
    (1 : ℚ) / 4 = (1 - (1 : ℚ) / 4) * (2 - 1 + (1 : ℚ) / 3) / 4 ∧
    (2 : ℚ) ^ 2 / 4 - 1 = 0 ∧
    ¬ ((2 : ℚ) ^ 2 / 4 - 1 < 0) := by
  norm_num [nextTailState, nextDenState, centeredState]

/-- A precise local form of the erroneous sign implication.  The data are
integer exact states; only the quotients are taken in the rationals. -/
def ShiftedSignEqualityRule : Prop :=
  ∀ a aNext D C : ℤ,
    0 < a → 0 < aNext → 0 < C → 0 < nextTailState a D C →
    let E := centeredState a D C
    let Enext := centeredState aNext (nextDenState a D) (nextTailState a D C)
    let theta : ℚ := (E : ℚ) / (C : ℚ)
    let lambda : ℚ :=
      (1 - theta) * ((a : ℚ) - 1 + (Enext : ℚ) / (nextTailState a D C : ℚ)) /
        (aNext : ℚ)
    0 < E → lambda ≤ theta → (a : ℚ) ^ 2 / (aNext : ℚ) - 1 < 0

theorem not_shifted_sign_equality_rule : ¬ ShiftedSignEqualityRule := by
  intro h
  have hf := h 2 4 5 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [nextTailState])
  norm_num [centeredState, nextDenState, nextTailState] at hf

/-- Finite real-window obstruction used in the long record.
`WindowCounterexample.not_real_window_rule` extends it to an infinite
pairwise-coprime family with the required reciprocal-sum bound. -/
theorem real_window_rounding_obstruction :
    (1 : ℚ) / (1 - (2 : ℚ) / 5) < 9 / 5 ∧
    (∀ z : ℤ, (21 : ℚ) / 10 ≤ (z : ℚ) → (z : ℚ) < 39 / 10 → z = 3) ∧
    (3 : ℤ) ∣ 3 := by
  refine ⟨by norm_num, ?_, dvd_rfl⟩
  intro z hlo hhi
  have hl : (2 : ℚ) < z := by linarith
  have hh : (z : ℚ) < 4 := by linarith
  have hlz : (2 : ℤ) < z := by exact_mod_cast hl
  have hhz : z < (4 : ℤ) := by exact_mod_cast hh
  omega

end ErdosProblems.Erdos243.PaperCompleteR7.Counterexamples
