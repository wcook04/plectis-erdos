import ErdosProblems.Erdos243.PaperCompleteR11.PrimitiveRecordBoundary

/-!
# Exact record-preserving quotient tails


The growth record below packages already derived orbit properties, not
any assertion about record gaps. Quotients are constructed from a genuine
common divisor. A global attained record is used as the starting index,
so the original running maximum is preserved exactly, including its prefix.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- Exact arithmetic and growth data used by both block arguments. -/
structure RecordGrowthOrbit : Type where
  a : ℕ → ℕ
  U : ℕ → ℕ
  D : ℕ → ℕ
  increasing : ∀ ⦃m n : ℕ⦄, m < n → a m < a n
  a_pos : ∀ n, 0 < a n
  U_pos : ∀ n, 0 < U n
  D_pos : ∀ n, 0 < D n
  U_step : ∀ n, U (n + 1) + D n = a n * U n
  D_step : ∀ n, D (n + 1) = a n * D n
  lower : ∃ N : ℕ, ∀ k, 2 * binaryTower k ≤ a (N + k)
  record_bound : ∃ K : ℕ, ∀ n, runningMax U n ≤ 2 ^ (K + n)
  den_bound : ∃ L : ℕ, ∀ n, D n ≤ binaryTower (n + L)
  unbounded : ∀ H : ℕ, ∃ n, H ≤ U n

/-- Monotonicity in the index, as distinct from monotonicity of the orbit. -/
theorem runningMax_mono_index (U : ℕ → ℕ) : Monotone (runningMax U) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_max_left _ _

/-- Every index has a later index which attains a global record. -/
theorem exists_late_attained_record (U : ℕ → ℕ)
    (hunbounded : ∀ H : ℕ, ∃ n, H ≤ U n) (S : ℕ) :
    ∃ s, S ≤ s ∧ U s = runningMax U s := by
  obtain ⟨n, hn⟩ := hunbounded (runningMax U S + 1)
  obtain ⟨s, hsn, hs⟩ := runningMax_attained U n
  have hUs : runningMax U S < U s := by
    have hh := le_runningMax U (le_refl n)
    omega
  have hSs : S ≤ s := by
    by_contra hnot
    have hh := le_runningMax U (show s ≤ S by omega)
    omega
  refine ⟨s, hSs, le_antisymm (le_runningMax U (le_refl s)) ?_⟩
  exact (runningMax_mono_index U hsn).trans_eq hs.symm

/-- Starting at an attained global record does not reset the past maximum. -/
theorem runningMax_shift_at_record (U : ℕ → ℕ) (s : ℕ)
    (hs : U s = runningMax U s) (n : ℕ) :
    runningMax (fun j ↦ U (s + j)) n = runningMax U (s + n) := by
  induction n with
  | zero => simpa only [runningMax, Nat.add_zero] using hs
  | succ n ih =>
      rw [runningMax, ih]
      congr 1

/-- A quotient tail's running maximum is bounded by the actual global
maximum, without requiring the quotient itself to be monotone. -/
theorem runningMax_shift_div_le (U : ℕ → ℕ) (s g n : ℕ) :
    runningMax (fun j ↦ U (s + j) / g) n ≤ runningMax U (s + n) := by
  obtain ⟨j, hj, heq⟩ := runningMax_attained (fun j ↦ U (s + j) / g) n
  rw [← heq]
  exact (Nat.div_le_self _ _).trans (le_runningMax U (by omega))

/-- Common divisors persist in natural coordinates on the entire tail. -/
theorem RecordGrowthOrbit.common_divisor_tail (O : RecordGrowthOrbit)
    (s g : ℕ) (hUg : g ∣ O.U s) (hDg : g ∣ O.D s) :
    ∀ n, g ∣ O.U (s + n) ∧ g ∣ O.D (s + n) := by
  intro n
  induction n with
  | zero => simpa only [Nat.add_zero] using And.intro hUg hDg
  | succ n ih =>
      have hu := O.U_step (s + n)
      have hd := O.D_step (s + n)
      constructor
      · have hsum : g ∣ O.U (s + n + 1) + O.D (s + n) := by
          rw [hu]
          exact dvd_mul_of_dvd_right ih.1 _
        simpa only [Nat.add_assoc] using (Nat.dvd_add_iff_left ih.2).mpr hsum
      · rw [show s + (n + 1) = (s + n) + 1 by omega, hd]
        exact dvd_mul_of_dvd_right ih.2 _

/-- The exact quotient orbit, with every positivity and growth property
proved from the original orbit. -/
def RecordGrowthOrbit.quotientAt (O : RecordGrowthOrbit) (s g : ℕ)
    (hg : 0 < g) (hUg : g ∣ O.U s) (hDg : g ∣ O.D s) : RecordGrowthOrbit := by
  have hdiv := O.common_divisor_tail s g hUg hDg
  refine {
    a := fun n ↦ O.a (s + n)
    U := fun n ↦ O.U (s + n) / g
    D := fun n ↦ O.D (s + n) / g
    increasing := fun i j hij ↦ O.increasing (by omega)
    a_pos := fun n ↦ O.a_pos _
    U_pos := fun n ↦ Nat.div_pos (Nat.le_of_dvd (O.U_pos _) (hdiv n).1) hg
    D_pos := fun n ↦ Nat.div_pos (Nat.le_of_dvd (O.D_pos _) (hdiv n).2) hg
    U_step := ?_
    D_step := ?_
    lower := ?_
    record_bound := ?_
    den_bound := ?_
    unbounded := ?_ }
  · intro n
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [Nat.mul_add, Nat.mul_div_cancel' (hdiv (n + 1)).1,
      Nat.mul_div_cancel' (hdiv n).2]
    calc
      O.U (s + (n + 1)) + O.D (s + n) = O.a (s + n) * O.U (s + n) := by
        simpa only [Nat.add_assoc] using O.U_step (s + n)
      _ = g * (O.a (s + n) * (O.U (s + n) / g)) := by
        rw [mul_left_comm, Nat.mul_div_cancel' (hdiv n).1]
  · intro n
    rw [show s + (n + 1) = (s + n) + 1 by omega, O.D_step]
    exact Nat.mul_div_assoc _ (hdiv n).2
  · obtain ⟨N, hN⟩ := O.lower
    refine ⟨N, fun k ↦ ?_⟩
    have hshift : O.a (N + k) ≤ O.a (s + (N + k)) := by
      by_cases hs : s = 0
      · simpa [hs]
      · exact Nat.le_of_lt (O.increasing (by omega))
    exact (hN k).trans hshift
  · obtain ⟨K, hK⟩ := O.record_bound
    refine ⟨K + s, fun n ↦ ?_⟩
    simpa only [Nat.add_assoc] using (runningMax_shift_div_le O.U s g n).trans (hK (s + n))
  · obtain ⟨L, hL⟩ := O.den_bound
    refine ⟨s + L, fun n ↦ ?_⟩
    have hh := (Nat.div_le_self (O.D (s + n)) g).trans (hL (s + n))
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh
  · intro H
    obtain ⟨j, hj⟩ := O.unbounded (max (g * H) (runningMax O.U s + 1))
    have hjbig : runningMax O.U s < O.U j := by
      have hh := (le_max_right (g * H) (runningMax O.U s + 1)).trans hj
      omega
    have hsj : s ≤ j := by
      by_contra hnot
      have hh := le_runningMax O.U (show j ≤ s by omega)
      omega
    let n := j - s
    have hsn : s + n = j := Nat.add_sub_of_le hsj
    refine ⟨n, ?_⟩
    have hid : g * (O.U (s + n) / g) = O.U j := by
      rw [Nat.mul_div_cancel' (hdiv n).1, hsn]
    have hgh : g * H ≤ g * (O.U (s + n) / g) := by
      rw [hid]
      exact (le_max_left _ _).trans hj
    by_contra hnot
    have hlt := Nat.mul_lt_mul_of_pos_left (show O.U (s + n) / g < H by omega) hg
    omega

/-- Exact equality of the global record with the scaled quotient record. -/
theorem RecordGrowthOrbit.quotient_record_exact (O : RecordGrowthOrbit)
    (s g : ℕ) (hg : 0 < g) (hUg : g ∣ O.U s) (hDg : g ∣ O.D s)
    (hs : O.U s = runningMax O.U s) (n : ℕ) :
    runningMax O.U (s + n) =
      g * runningMax (O.quotientAt s g hg hUg hDg).U n := by
  rw [← runningMax_shift_at_record O.U s hs n, ← runningMax_mul]
  congr 1
  funext j
  exact (Nat.mul_div_cancel' (O.common_divisor_tail s g hUg hDg j).1).symm

/-- An eventual global record cap passes to the quotient with coefficient
c/g and with the *scaled* normaliser. No asymptotic scaling identity is assumed. -/
theorem RecordGrowthOrbit.quotient_record_cap (O : RecordGrowthOrbit)
    (s g : ℕ) (hg : 0 < g) (hUg : g ∣ O.U s) (hDg : g ∣ O.D s)
    (hs : O.U s = runningMax O.U s) (c : ℝ) (T : ℕ)
    (hcap : ∀ n, T ≤ n → runningMax O.U n < O.U (n + 1) →
      ((O.U (n + 1) - runningMax O.U n : ℕ) : ℝ) ≤ c * recordLogLog (runningMax O.U n)) :
    let V := O.quotientAt s g hg hUg hDg
    ∀ n : ℕ, T ≤ n → runningMax V.U n < V.U (n + 1) →
      ((V.U (n + 1) - runningMax V.U n : ℕ) : ℝ) ≤
        (c / g) * recordLogLog (g * runningMax V.U n : ℕ) := by
  dsimp only
  let V := O.quotientAt s g hg hUg hDg
  intro n hn hnew
  have hmax := O.quotient_record_exact s g hg hUg hDg hs n
  have hnext : O.U (s + n + 1) = g * V.U (n + 1) := by
    simpa only [V, RecordGrowthOrbit.quotientAt, Nat.add_assoc] using
      (Nat.mul_div_cancel' (O.common_divisor_tail s g hUg hDg (n + 1)).1).symm
  have hnew' : runningMax O.U (s + n) < O.U (s + n + 1) := by
    rw [hmax, hnext]
    exact Nat.mul_lt_mul_of_pos_left hnew hg
  have hh := hcap (s + n) (by omega) hnew'
  rw [hmax, hnext, ← Nat.mul_sub_left_distrib, Nat.cast_mul] at hh
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  calc
    ((V.U (n + 1) - runningMax V.U n : ℕ) : ℝ) ≤
        (c * recordLogLog (g * runningMax V.U n : ℕ)) / g :=
      (le_div_iff₀ hgR).2 (by nlinarith)
    _ = (c / g) * recordLogLog (g * runningMax V.U n : ℕ) := by ring

end ErdosProblems.Erdos243.PaperCompleteR11
