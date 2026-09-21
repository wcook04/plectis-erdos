import ErdosProblems.Erdos243.CumulativeLcmTransfer

/-! A genuine LCM-adapted, positive-coefficient orbit with unit actual record
jumps and unbounded height. Its lack of centring is essential. -/
namespace ErdosProblems.Erdos243.PaperCompleteR9

open scoped BigOperators

def driftDigit (n : ℕ) : ℕ := 2 ^ (n + 2)
def driftHeight (n : ℕ) : ℕ := n + 2
def driftCoefficient (n : ℕ) : ℤ := (n : ℤ) + 1

def driftError (n : ℕ) : ℤ :=
  driftCoefficient n * (cumulativeDigitLcm 2 driftDigit n : ℤ) -
    ((driftDigit n : ℤ) - 1) * (driftHeight n : ℤ)

theorem drift_power_divides (n : ℕ) : 2 ^ (n + 1) ∣ 2 ^ (n + 2) := by
  refine ⟨2, ?_⟩
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]

theorem drift_lcm (n : ℕ) : cumulativeDigitLcm 2 driftDigit n = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cumulativeDigitLcm, ih]
    change Nat.lcm (2 ^ (n + 1)) (2 ^ (n + 2)) = 2 ^ (n + 2)
    exact Nat.dvd_antisymm
      (Nat.lcm_dvd (drift_power_divides n) (dvd_refl _)) (Nat.dvd_lcm_right _ _)

theorem drift_overlap (n : ℕ) : lcmOverlap 2 driftDigit n = 2 ^ (n + 1) := by
  unfold lcmOverlap
  rw [drift_lcm]
  change Nat.gcd (2 ^ (n + 1)) (2 ^ (n + 2)) = 2 ^ (n + 1)
  exact Nat.dvd_antisymm (Nat.gcd_dvd_left _ _)
    (Nat.dvd_gcd (dvd_refl _) (drift_power_divides n))

theorem drift_exact_step (n : ℕ) :
    (lcmOverlap 2 driftDigit n : ℤ) * (driftHeight (n + 1) : ℤ) =
      (driftHeight n : ℤ) - driftError n := by
  simp only [driftError, drift_lcm, drift_overlap, driftDigit, driftHeight,
    driftCoefficient, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  simp only [pow_succ]
  ring

theorem drift_positive (n : ℕ) :
    0 < driftDigit n ∧ 0 < driftHeight n ∧ 0 < driftCoefficient n := by
  simp only [driftDigit, driftHeight, driftCoefficient]
  exact ⟨by positivity, by omega, by positivity⟩

theorem drift_unit_record_jump (n : ℕ) :
    driftHeight (n + 1) = driftHeight n + 1 ∧
    ∀ j, j ≤ n → driftHeight j < driftHeight (n + 1) := by
  constructor
  · change n + 1 + 2 = n + 2 + 1
    omega
  · intro j hj
    change j + 2 < n + 1 + 2
    omega

theorem drift_unbounded : ∀ H : ℕ, ∃ n, H < driftHeight n := by
  intro H
  exact ⟨H, by simp [driftHeight]⟩

theorem drift_error_closed_form (n : ℕ) :
    driftError n = (n : ℤ) + 2 - (2 : ℤ) ^ (n + 1) * ((n : ℤ) + 3) := by
  simp only [driftError, drift_lcm, driftDigit, driftHeight, driftCoefficient,
    Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  simp only [pow_succ]
  ring

/-- An exact telescoping finite prefix, not a floating-point experiment. -/
theorem drift_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n : ℚ) + 1) / (2 : ℚ) ^ (n + 2)) =
      1 - ((N : ℚ) + 2) / (2 : ℚ) ^ (N + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    simp only [pow_succ]
    field_simp
    ring

end ErdosProblems.Erdos243.PaperCompleteR9
