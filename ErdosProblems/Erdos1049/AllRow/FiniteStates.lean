import ErdosProblems.Erdos1049.AllRow.Filtered

/-!
# An exact finite-state version of the filtered row identity

Every transition sum is over `Finset.range K`. The depth and initial state are
arbitrary. The source application chooses `K` large enough for the requested
depth, after making a certified finite polynomial approximation. This avoids
an unjustified endomorphism of an algebraic direct sum.

Verified locally by the focused all-row audit on 2026-09-09.
-/

noncomputable section

namespace ErdosProblems.Erdos1049.AllRow

open scoped BigOperators

/-- A finite ratio with constant term one in the state variable. -/
def finiteRatio (a : ℕ → S) (K n : ℕ) : S :=
  1 + ∑ s ∈ Finset.range K,
    a (s + 1) * PowerSeries.X ^ ((n + 1) * (s + 1))

/-- Product of the finite ratios, with an arbitrary initial unit. -/
def finiteUnit (a : ℕ → S) (K : ℕ) (C : S) : ℕ → S
  | 0 => C
  | n + 1 => finiteUnit a K C n * finiteRatio a K n

/-- The state `t` attached to the finite product. -/
def finiteTail (a : ℕ → S) (K : ℕ) (C : S) (n t : ℕ) : S :=
  PowerSeries.X ^ ((n + 1) * t) * finiteUnit a K C n

/-- The finite source transition; coefficients do not depend on `n`. -/
def transition (a : ℕ → S) (K : ℕ) (f : ℕ → S) : ℕ → S
  | 0 => ∑ s ∈ Finset.range K, a (s + 1) * f s
  | t + 1 =>
      (PowerSeries.X ^ (t + 1) - 1) * f t +
        PowerSeries.X ^ (t + 1) *
          ∑ s ∈ Finset.range K, a (s + 1) * f (t + s + 1)

/-- Finite-depth state expansion. Unlike an infinite matrix power, this is an
ordinary structural recursion with a finite sum at every call. -/
def state (a : ℕ → S) (K : ℕ) (C : S) : ℕ → ℕ → ℕ → S
  | 0, n => finiteTail a K C n
  | j + 1, n => transition a K (state a K C j n)

@[simp] theorem constantCoeff_finiteRatio (a : ℕ → S) (K n : ℕ) :
    PowerSeries.constantCoeff (finiteRatio a K n) = 1 := by
  simp [finiteRatio, constantCoeff_q_pow,
    Nat.mul_ne_zero, Nat.succ_ne_zero]

@[simp] theorem constantCoeff_finiteUnit (a : ℕ → S) (K : ℕ) (C : S)
    (hC : PowerSeries.constantCoeff C = 1) (n : ℕ) :
    PowerSeries.constantCoeff (finiteUnit a K C n) = 1 := by
  induction n with
  | zero => exact hC
  | succ n ih =>
      rw [finiteUnit, map_mul, ih, constantCoeff_finiteRatio, one_mul]

/-- The exact consecutive-index identity before taking a difference. -/
theorem finiteTail_succ (a : ℕ → S) (K : ℕ) (C : S) (n t : ℕ) :
    finiteTail a K C (n + 1) t =
      PowerSeries.X ^ t * finiteTail a K C n t * finiteRatio a K n := by
  rw [finiteTail, finiteUnit, finiteTail]
  rw [show (n + 1 + 1) * t = t + (n + 1) * t by ring, pow_add]
  ring

theorem finiteTail_state_succ (a : ℕ → S) (K : ℕ) (C : S) (n t : ℕ) :
    finiteTail a K C n (t + 1) =
      PowerSeries.X ^ (n + 1) * finiteTail a K C n t := by
  rw [finiteTail, finiteTail,
    show (n + 1) * (t + 1) = (n + 1) + (n + 1) * t by ring, pow_add]
  ring

private theorem finiteTail_mul_ratio_sub_one
    (a : ℕ → S) (K : ℕ) (C : S) (n t : ℕ) :
    finiteTail a K C n t * (finiteRatio a K n - 1) =
      PowerSeries.X ^ (n + 1) *
        ∑ s ∈ Finset.range K, a (s + 1) * finiteTail a K C n (t + s) := by
  simp only [finiteRatio, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [finiteTail]
  have he : (n + 1) * t + (n + 1) * (s + 1) =
      (n + 1) + (n + 1) * (t + s) := by ring
  calc
    (PowerSeries.X ^ ((n + 1) * t) * finiteUnit a K C n) *
        (a (s + 1) * PowerSeries.X ^ ((n + 1) * (s + 1))) =
      PowerSeries.X ^ ((n + 1) * t + (n + 1) * (s + 1)) *
        (a (s + 1) * finiteUnit a K C n) := by rw [pow_add]; ring
    _ = PowerSeries.X ^ (n + 1) *
        (a (s + 1) *
          (PowerSeries.X ^ ((n + 1) * (t + s)) * finiteUnit a K C n)) := by
      rw [he, pow_add]
      ring

/-- The one-step transition identity, exactly and not just modulo a power. -/
theorem finiteTail_difference (a : ℕ → S) (K : ℕ) (C : S) (n t : ℕ) :
    finiteTail a K C (n + 1) t - finiteTail a K C n t =
      PowerSeries.X ^ (n + 1) * state a K C 1 n t := by
  rw [finiteTail_succ]
  have hsplit :
      PowerSeries.X ^ t * finiteTail a K C n t * finiteRatio a K n -
          finiteTail a K C n t =
        (PowerSeries.X ^ t - 1) * finiteTail a K C n t +
          PowerSeries.X ^ t *
            (finiteTail a K C n t * (finiteRatio a K n - 1)) := by ring
  rw [hsplit, finiteTail_mul_ratio_sub_one]
  cases t with
  | zero => simp [state, transition]
  | succ t =>
      rw [finiteTail_state_succ]
      change _ = PowerSeries.X ^ (n + 1) *
        ((PowerSeries.X ^ (t + 1) - 1) * finiteTail a K C n t +
          PowerSeries.X ^ (t + 1) *
            ∑ s ∈ Finset.range K, a (s + 1) * finiteTail a K C n (t + s + 1))
      have hsum :
          (∑ s ∈ Finset.range K,
            a (s + 1) * finiteTail a K C n (t + 1 + s)) =
          ∑ s ∈ Finset.range K,
            a (s + 1) * finiteTail a K C n (t + s + 1) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [show t + 1 + s = t + s + 1 by omega]
      rw [hsum]
      ring

private theorem transition_sub (a : ℕ → S) (K : ℕ) (f g : ℕ → S) (t : ℕ) :
    transition a K (fun u => f u - g u) t =
      transition a K f t - transition a K g t := by
  cases t <;>
    simp only [transition, mul_sub, Finset.sum_sub_distrib] <;> ring

private theorem transition_mul (a : ℕ → S) (K : ℕ) (c : S)
    (f : ℕ → S) (t : ℕ) :
    transition a K (fun u => c * f u) t = c * transition a K f t := by
  cases t <;>
    simp [transition, Finset.mul_sum, mul_add, mul_assoc, mul_left_comm, mul_comm]

/-- Every finite-depth state expansion inherits the same index difference. -/
theorem state_difference (a : ℕ → S) (K : ℕ) (C : S) :
    ∀ j n t, state a K C j (n + 1) t - state a K C j n t =
      PowerSeries.X ^ (n + 1) * state a K C (j + 1) n t := by
  intro j
  induction j with
  | zero => exact finiteTail_difference a K C
  | succ j ih =>
      intro n t
      change transition a K (state a K C j (n + 1)) t -
          transition a K (state a K C j n) t =
        PowerSeries.X ^ (n + 1) * transition a K (state a K C (j + 1) n) t
      rw [← transition_sub]
      have hf :
          (fun u => state a K C j (n + 1) u - state a K C j n u) =
          (fun u => PowerSeries.X ^ (n + 1) * state a K C (j + 1) n u) := by
        funext u
        exact ih n u
      rw [hf, transition_mul]

/-- Reuse the canonical source backward-shift operator at every depth. -/
theorem finite_row_factorisation (a : ℕ → S) (K : ℕ) (C : S) :
    ∀ j l t,
      zudilinBackwardShiftApply j (j + l) (fun n => finiteTail a K C n t) =
        PowerSeries.X ^ rowExponent j l * state a K C j l t := by
  intro j
  induction j with
  | zero => intro l t; simp [state]
  | succ j ih =>
      intro l t
      rw [zudilinBackwardShiftApply_succ j (j + 1 + l)
        (fun n => finiteTail a K C n t) (by omega)]
      rw [show j + 1 + l = j + (l + 1) by omega,
        show j + (l + 1) - 1 = j + l by omega,
        ih (l + 1) t, ih l t, rowExponent_column]
      calc
        PowerSeries.X ^ (rowExponent j l + j) * state a K C j (l + 1) t -
            PowerSeries.X ^ j *
              (PowerSeries.X ^ rowExponent j l * state a K C j l t) =
          PowerSeries.X ^ (rowExponent j l + j) *
            (state a K C j (l + 1) t - state a K C j l t) := by
          rw [pow_add]
          ring
        _ = PowerSeries.X ^ (rowExponent j l + j) *
            (PowerSeries.X ^ (l + 1) * state a K C (j + 1) l t) := by
          rw [state_difference]
        _ = PowerSeries.X ^ rowExponent (j + 1) l *
            state a K C (j + 1) l t := by
          rw [← mul_assoc, ← pow_add, rowExponent_succ]
          congr 2 <;> omega

/-- The finite transition has exactly the already-canonical associated grade.
The only size condition is `j ≤ K`; states themselves are unbounded. -/
theorem constantCoeff_state (a : ℕ → S) (K : ℕ) (C : S)
    (hC : PowerSeries.constantCoeff C = 1) :
    ∀ j, j ≤ K → ∀ n t,
      PowerSeries.constantCoeff (state a K C j n t) =
        hankelAssociatedCoeff (fun s => PowerSeries.constantCoeff (a s)) j t := by
  intro j
  induction j with
  | zero =>
      intro hj n t
      cases t with
      | zero => simp [state, finiteTail, constantCoeff_finiteUnit a K C hC,
          hankelAssociatedCoeff]
      | succ t => simp [state, finiteTail, constantCoeff_finiteUnit a K C hC,
          hankelAssociatedCoeff, constantCoeff_q_pow,
          Nat.mul_ne_zero, Nat.succ_ne_zero]
  | succ j ih =>
      intro hj n t
      have hj' : j ≤ K := by omega
      cases t with
      | zero =>
          change PowerSeries.constantCoeff
              (∑ s ∈ Finset.range K, a (s + 1) * state a K C j n s) = _
          simp only [map_sum, map_mul, ih hj', hankelAssociatedCoeff]
          symm
          apply Finset.sum_subset (Finset.range_subset_range.mpr hj)
          intro s _ hs
          have hjs : j < s := by
            simp only [Finset.mem_range, not_lt] at hs
            omega
          rw [associated_above _ j s hjs, mul_zero]
      | succ t =>
          change PowerSeries.constantCoeff
              ((PowerSeries.X ^ (t + 1) - 1) * state a K C j n t +
                PowerSeries.X ^ (t + 1) *
                  ∑ s ∈ Finset.range K,
                    a (s + 1) * state a K C j n (t + s + 1)) = _
          simp only [map_add, map_mul, map_sub,
            constantCoeff_q_pow, Nat.succ_ne_zero, if_false,
            map_one, zero_sub, neg_one_mul, zero_mul, add_zero,
            ih hj', hankelAssociatedCoeff]

/-- Full finite-model row initial monomial, including every lower coefficient. -/
theorem finite_row_initial (a : ℕ → S) (K : ℕ) (C : S)
    (hC : PowerSeries.constantCoeff C = 1) (j l t : ℕ) (hj : j ≤ K) :
    (∀ d, d < rowExponent j l →
      PowerSeries.coeff d
        (zudilinBackwardShiftApply j (j + l) (fun n => finiteTail a K C n t)) = 0) ∧
    PowerSeries.coeff (rowExponent j l)
      (zudilinBackwardShiftApply j (j + l) (fun n => finiteTail a K C n t)) =
        hankelAssociatedCoeff (fun s => PowerSeries.constantCoeff (a s)) j t := by
  constructor
  · intro d hd
    rw [finite_row_factorisation, PowerSeries.coeff_X_pow_mul']
    simp [Nat.not_le.mpr hd]
  · rw [finite_row_factorisation, PowerSeries.coeff_X_pow_mul']
    simp only [le_refl, if_true, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff]
    exact constantCoeff_state a K C hC j hj l t

end ErdosProblems.Erdos1049.AllRow
