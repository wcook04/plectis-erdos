import ErdosProblems.Erdos243.PaperCompleteR9Packets

/-!
# Record fences without primitivity


Unlike a source-jump fence, the result below charges the *record increment*.
It allows arbitrarily deep intervening drawdowns and does not assume that
numerator and denominator are coprime. It is a finite ingredient of the
inclusive log-log argument, not a declaration of that analytic endpoint.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators

/-- The running maximum is an attained value, including at index zero. -/
theorem runningMax_attained (U : ℕ → ℕ) (n : ℕ) :
    ∃ j, j ≤ n ∧ U j = runningMax U n := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      obtain ⟨j, hj, heq⟩ := ih
      by_cases h : U (n + 1) ≤ runningMax U n
      · refine ⟨j, by omega, ?_⟩
        simpa only [runningMax, max_eq_left h] using heq
      · refine ⟨n + 1, le_rfl, ?_⟩
        simp only [runningMax, max_eq_right (by omega : runningMax U n ≤ U (n + 1))]

/-- A common divisor of an exact state survives every subsequent step.
The coefficient may be any integer; no positivity is needed. -/
theorem common_divisor_persists
    (C D a b : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) = a n * C n - b n * D n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (m : ℤ) {s t : ℕ} (hst : s ≤ t)
    (hmC : m ∣ C s) (hmD : m ∣ D s) :
    m ∣ C t ∧ m ∣ D t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  induction k with
  | zero => simpa using And.intro hmC hmD
  | succ k ih =>
      have ih' := ih (by omega : s ≤ s + k)
      constructor
      · rw [show s + (k + 1) = (s + k) + 1 by omega, hC]
        exact dvd_sub (dvd_mul_of_dvd_right ih'.1 _) (dvd_mul_of_dvd_right ih'.2 _)
      · rw [show s + (k + 1) = (s + k) + 1 by omega, hD]
        exact dvd_mul_of_dvd_right ih'.2 _

/-- A divisor of both the old denominator and the current multiplier divides
 the following numerator. For unit coefficients this gives the pairwise-gcd
 estimate used in the coprime-core construction. -/
theorem multiplier_common_divisor_next
    (a C D C' m : ℤ) (hstep : C' = a * C - D)
    (hma : m ∣ a) (hmD : m ∣ D) : m ∣ C' := by
  rw [hstep]
  exact dvd_sub (dvd_mul_of_dvd_left hma C) hmD

/-- An old divisor found at an *attained previous record* divides the new
record gap, even if the source of the new record is far below that record. -/
theorem old_divisor_dvd_record_gap
    (U : ℕ → ℕ) (D a b : ℕ → ℤ)
    (hC : ∀ n, (U (n + 1) : ℤ) = a n * U n - b n * D n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (m : ℤ) {j n : ℕ} (hjn : j ≤ n)
    (hrecord : U j = runningMax U n)
    (hmU : m ∣ (U j : ℤ)) (hmD : m ∣ D j) :
    m ∣ (U (n + 1) : ℤ) - runningMax U n := by
  have hfuture := common_divisor_persists
    (fun k ↦ (U k : ℤ)) D a b hC hD m
    (show j ≤ n + 1 by omega) hmU hmD
  rw [← hrecord]
  exact dvd_sub hfuture.1 hmU

/-- No first crossing of a covered record block has record increment at
most its width. The cover need only hold after the moduli became old. -/
theorem first_crossing_record_gap_gt
    (U : ℕ → ℕ) (D a b : ℕ → ℤ) (T x B n : ℕ)
    (hC : ∀ k, (U (k + 1) : ℤ) = a k * U k - b k * D k)
    (hD : ∀ k, D (k + 1) = a k * D k)
    (hprefix : runningMax U T < x)
    (hfirst : LcmRecordCrossing.FirstCrossing U (x + B) n)
    (hcover : ∀ j, T ≤ j → ∀ z : ℕ, x ≤ z → z < x + B →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ (z : ℤ) ∧ m ∣ D j) :
    B < U (n + 1) - runningMax U n := by
  by_contra hnot
  have hgap : U (n + 1) - runningMax U n ≤ B := by omega
  have hRlt : runningMax U n < x + B := runningMax_lt U hfirst.1
  have hreach : x + B ≤ U (n + 1) := hfirst.2
  have hRnew : runningMax U n < U (n + 1) := hRlt.trans_le hreach
  have hgap_eq : U (n + 1) - runningMax U n + runningMax U n = U (n + 1) :=
    Nat.sub_add_cancel hRnew.le
  have hRx : x ≤ runningMax U n := by omega
  obtain ⟨j, hjn, hj⟩ := runningMax_attained U n
  have hTj : T ≤ j := by
    by_contra hbad
    have hu := le_runningMax U (show j ≤ T by omega)
    omega
  obtain ⟨m, hm, hmU, hmD⟩ := hcover j hTj (U j) (by omega) (by omega)
  have hdiv := old_divisor_dvd_record_gap U D a b hC hD m hjn hj hmU hmD
  have hpos : 0 < (U (n + 1) : ℤ) - runningMax U n := by
    apply sub_pos.mpr
    exact_mod_cast hRnew
  have hle := Int.le_of_dvd hpos hdiv
  have hgapZ : (U (n + 1) : ℤ) - runningMax U n ≤ (B : ℤ) := by omega
  omega

/-- The finite record fence assembled with an actual first crossing.
The hypothesis caps record increments, not all source-to-endpoint rises. -/
theorem bounded_by_record_cover
    (U : ℕ → ℕ) (D a b : ℕ → ℤ) (T x B : ℕ)
    (hC : ∀ k, (U (k + 1) : ℤ) = a k * U k - b k * D k)
    (hD : ∀ k, D (k + 1) = a k * D k)
    (hprefix : runningMax U T < x)
    (hcover : ∀ j, T ≤ j → ∀ z : ℕ, x ≤ z → z < x + B →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ (z : ℤ) ∧ m ∣ D j)
    (hcap : ∀ n, T ≤ n → runningMax U n < x + B →
      runningMax U n < U (n + 1) →
      U (n + 1) - runningMax U n ≤ B) :
    ∀ k, U k < x + B := by
  intro k
  by_contra hk
  have hzero : U 0 < x + B := by
    have h0 := le_runningMax U (Nat.zero_le T)
    omega
  obtain ⟨n, hn, _⟩ := LcmRecordCrossing.exists_unique_firstCrossing U
    (x + B) k hzero ⟨k, le_rfl, by omega⟩
  have hTn : T ≤ n := by
    by_contra hbad
    have hsmall := le_runningMax U (show n + 1 ≤ T by omega)
    have hhigh := hn.2.2
    omega
  have hRlt : runningMax U n < x + B := runningMax_lt U hn.2.1
  have hRnew : runningMax U n < U (n + 1) := hRlt.trans_le hn.2.2
  have hupper := hcap n hTn hRlt hRnew
  have hlower := first_crossing_record_gap_gt U D a b T x B n
    hC hD hprefix hn.2 hcover
  omega

/-- Fixed integer scaling commutes with the attained running maximum. -/
theorem runningMax_mul (U : ℕ → ℕ) (g n : ℕ) :
    runningMax (fun k ↦ g * U k) n = g * runningMax U n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [runningMax, ih]
      by_cases h : runningMax U n ≤ U (n + 1)
      · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_left g h)]
      · have h' : U (n + 1) ≤ runningMax U n := by omega
        rw [max_eq_left h', max_eq_left (Nat.mul_le_mul_left g h')]

/-- Record increments scale exactly; this is independent of an asymptotic
normaliser and must precede the analytic log-log rescaling argument. -/
theorem record_increment_mul (U : ℕ → ℕ) (g n : ℕ) :
    g * U (n + 1) - runningMax (fun k ↦ g * U k) n =
      g * (U (n + 1) - runningMax U n) := by
  rw [runningMax_mul, Nat.mul_sub_left_distrib]

end ErdosProblems.Erdos243.PaperCompleteR11
