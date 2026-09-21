import ErdosProblems.Erdos243.PaperCompleteR11.RecordDivisibility
import ErdosProblems.Erdos243.UncentredRecordCharge

/-!
# Finite mixed and raw record charging

Charges are zero off strict records. The fresh branch
uses the actual jump; the overlap branch uses the new record height.
The coefficient is an arbitrary integer and no centring is assumed.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open PaperCompleteR9 LcmRecordCrossing LcmRecordExcess
open scoped BigOperators

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def mixedCharge (U rho : ℕ → ℕ) (B : ℕ) (f : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  if IsStrictRecord U n then
    ((if rho n = 1 then U (n + 1) - U n - B
      else U (n + 1) - runningMax U n : ℕ) : ℝ) * f (U n)
  else 0

noncomputable def rawCharge (U rho : ℕ → ℕ) (B : ℕ) (f : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  if IsStrictRecord U n then
    ((rho n * U (n + 1) - U n - B : ℕ) : ℝ) * f (U n)
  else 0

theorem mixedCharge_nonneg (U rho : ℕ → ℕ) (B : ℕ) (f : ℕ → ℝ)
    (hf : ∀ u, 0 ≤ f u) (n : ℕ) : 0 ≤ mixedCharge U rho B f n := by
  classical
  have hh := hf (U n)
  unfold mixedCharge
  split_ifs <;> positivity

theorem rawCharge_nonneg (U rho : ℕ → ℕ) (B : ℕ) (f : ℕ → ℝ)
    (hf : ∀ u, 0 ≤ f u) (n : ℕ) : 0 ≤ rawCharge U rho B f n := by
  classical
  have hh := hf (U n)
  unfold rawCharge
  split_ifs <;> positivity

/-- At overlap records above the baseline, raw error pays the record gain.
Fresh records have identical mixed and raw charge. -/
theorem mixedCharge_le_rawCharge
    (U rho : ℕ → ℕ) (B : ℕ) (f : ℕ → ℝ)
    (hf : ∀ u, 0 ≤ f u) (n : ℕ) (hrho : 1 ≤ rho n)
    (hlarge : IsStrictRecord U n → B ≤ U (n + 1)) :
    mixedCharge U rho B f n ≤ rawCharge U rho B f n := by
  classical
  by_cases hr : IsStrictRecord U n
  · simp only [mixedCharge, rawCharge, if_pos hr]
    by_cases hone : rho n = 1
    · simp [hone]
    · rw [if_neg hone]
      have hR : U n ≤ runningMax U n := le_runningMax U le_rfl
      have hnew : runningMax U n < U (n + 1) := runningMax_lt U hr
      have hB := hlarge hr
      have htwo : 2 ≤ rho n := by omega
      have hmul := Nat.mul_le_mul_right (U (n + 1)) htwo
      have hcount : U (n + 1) - runningMax U n ≤
          rho n * U (n + 1) - U n - B := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (hf _)
  · simp [mixedCharge, rawCharge, hr]

/-- Identification with the paper's integer positive part, rather than
assuming that the source-to-endpoint jump is the raw error. -/
theorem rawCharge_eq_error
    (U rho : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ) (f : ℕ → ℝ) (n : ℕ)
    (hstep : (rho n : ℤ) * U (n + 1) = (U n : ℤ) - V n) :
    rawCharge U rho B f n =
      if IsStrictRecord U n then ((max (-V n - (B : ℤ)) 0 : ℤ) : ℝ) * f (U n)
      else 0 := by
  classical
  have hs : ((rho n * U (n + 1) : ℕ) : ℤ) = (U n : ℤ) - V n := by
    exact_mod_cast hstep
  have heq : ((rho n * U (n + 1) - U n - B : ℕ) : ℤ) =
      max (-V n - (B : ℤ)) 0 := by omega
  have heqR : ((rho n * U (n + 1) - U n - B : ℕ) : ℝ) =
      ((max (-V n - (B : ℤ)) 0 : ℤ) : ℝ) := by exact_mod_cast heq
  simp only [rawCharge, heqR]

/-- Spaced first-crossed walls cost no more than the record increment.
This estimate does not charge a repeated crossing after a drawdown. -/
theorem progression_card_le_record_increment
    (s : Finset ℕ) (x P R y : ℕ) (hP : 0 < P)
    (hlo : ∀ k ∈ s, R < x + k * P)
    (hhi : ∀ k ∈ s, x + k * P ≤ y) : s.card ≤ y - R := by
  by_cases hs : s.Nonempty
  · obtain ⟨k, hk⟩ := hs
    have hRy : R < y := (hlo k hk).trans_le (hhi k hk)
    have hspacing := crossed_progression_spacing s ⟨k, hk⟩ x P R (y - R)
      hlo (by intro j hj; have hh := hhi j hj; omega)
    have hmul : s.card - 1 ≤ (s.card - 1) * P := by
      simpa using Nat.mul_le_mul_left (s.card - 1) hP
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- The complete finite first-crossing partition for a mixed charge. Old
covering is required only at fresh steps and only after its supply time T. -/
theorem finite_mixed_record_bound
    (s : Finset ℕ) (U rho : ℕ → ℕ) (a b L : ℕ → ℤ)
    (T x P B N : ℕ) (hP : B < P)
    (hprefix : runningMax U T < x)
    (hN : ∀ k ∈ s, ∃ j ≤ N, x + k * P ≤ U j)
    (hstep : ∀ n, (rho n : ℤ) * U (n + 1) = a n * U n - b n * L n)
    (hcover : ∀ n, T ≤ n → rho n = 1 → ∀ k : ℕ, ∀ z : ℤ,
      ((x + k * P : ℕ) : ℤ) - B ≤ z → z < ((x + k * P : ℕ) : ℤ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L n ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u) :
    ∑ k ∈ s, f (x + k * P) ≤
      ∑ n ∈ Finset.range N, mixedCharge U rho B f n := by
  classical
  have hzero : ∀ k ∈ s, U 0 < x + k * P := by
    intro k hk
    have hh := le_runningMax U (Nat.zero_le T)
    omega
  rw [sum_firstCrossing_partition s U (fun k ↦ x + k * P) N
    (fun k ↦ f (x + k * P)) hzero hN]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hnT : T ≤ n
  · by_cases hr : IsStrictRecord U n
    · simp only [mixedCharge, if_pos hr]
      let crossed := s.filter (fun k ↦ FirstCrossing U (x + k * P) n)
      have hlow : ∀ k ∈ crossed, U n < x + k * P := by
        intro k hk
        exact (Finset.mem_filter.mp hk).2.1 n le_rfl
      have hhigh : ∀ k ∈ crossed, x + k * P ≤ U (n + 1) := by
        intro k hk
        exact (Finset.mem_filter.mp hk).2.2
      have hRlow : ∀ k ∈ crossed, runningMax U n < x + k * P := by
        intro k hk
        exact runningMax_lt U (Finset.mem_filter.mp hk).2.1
      by_cases hone : rho n = 1
      · rw [if_pos hone]
        have hstepn : (U (n + 1) : ℤ) = a n * U n - b n * L n := by
          simpa only [hone, Nat.cast_one, one_mul] using hstep n
        have hsplit : U (n + 1) - U n + U n = U (n + 1) :=
          Nat.sub_add_cancel (le_of_lt (hr n le_rfl))
        have hsplitZ : ((U (n + 1) - U n : ℕ) : ℤ) + U n = U (n + 1) := by
          exact_mod_cast hsplit
        have hfeedback : ((U (n + 1) - U n : ℕ) : ℤ) =
            (a n - 1) * U n - b n * L n := by nlinarith [hstepn]
        have hlocal := crossed_progression_weighted_charge crossed x P (U n)
          (U (n + 1) - U n) B (a n) (b n * L n) hP hlow
          (by intro k hk; have hh := hhigh k hk; omega) hfeedback
          (by
            intro k hk z hzlo hzhi
            obtain ⟨m, hm, hmL, hmz⟩ := hcover n hnT hone k z hzlo hzhi
            exact ⟨m, hm, dvd_mul_of_dvd_right hmL (b n), hmz⟩)
          f hf (hpos (U n))
        simpa only [crossed, Finset.sum_filter] using hlocal
      · rw [if_neg hone]
        have hc := progression_card_le_record_increment crossed x P
          (runningMax U n) (U (n + 1)) (by omega) hRlow hhigh
        have hlocal : ∑ k ∈ crossed, f (x + k * P) ≤
            ((U (n + 1) - runningMax U n : ℕ) : ℝ) * f (U n) := by
          calc
            ∑ k ∈ crossed, f (x + k * P) ≤ ∑ _k ∈ crossed, f (U n) :=
              Finset.sum_le_sum (fun k hk ↦ hf (le_of_lt (hlow k hk)))
            _ = (crossed.card : ℝ) * f (U n) := by simp
            _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hpos _)
        simpa only [crossed, Finset.sum_filter] using hlocal
    · simp only [mixedCharge, if_neg hr]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro k hk
      exact if_neg (fun h ↦ hr h.is_record)
  · have hsmall : ∀ k, ¬ FirstCrossing U (x + k * P) n := by
      intro k hk
      have hh := le_runningMax U (show n + 1 ≤ T by omega)
      have hc := hk.2
      omega
    simp only [if_neg (hsmall _), Finset.sum_const_zero]
    exact mixedCharge_nonneg U rho B f hpos n

end ErdosProblems.Erdos243.PaperCompleteR11
