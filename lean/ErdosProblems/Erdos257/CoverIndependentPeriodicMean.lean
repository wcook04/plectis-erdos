import Mathlib

/-!
# Cover-independent periodic means

Lemma A.1 of the 2026-09-06 Type B revision return: a nonnegative divisor
majorant of `g` controls every Cesàro average of `g`, hence every periodic
mean. This is not an irrationality theorem. It bounds cover cost.

The coprime-cover obstruction (Type B Theorem B.1) uses this averaging plus
the elementary density `1 - ∏(1 - 1/a)`; that density identity is recorded
as an ordinary proof in `VariableExponentCoverSeparation.md`.
-/

namespace ErdosProblems.Erdos257

open Finset

/-- Multiples of `d` in `{1, …, X}` number exactly `X / d`. -/
theorem card_Icc_one_filter_dvd {d X : ℕ} (hd : 0 < d) :
    ((Icc 1 X).filter (fun n => d ∣ n)).card = X / d := by
  have hsrc : (Icc 1 (X / d)).card = X / d := by
    simpa using Nat.card_Icc 1 (X / d)
  refine hsrc ▸ (card_bij (fun k _ => k * d) ?_ ?_ ?_).symm
  · intro k hk
    have hkIcc := mem_Icc.mp hk
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_left d k⟩
    · exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_le_iff.mp hkIcc.1) hd)
    · exact (Nat.le_div_iff_mul_le hd).mp hkIcc.2
  · intro a ha b hb h
    exact Nat.eq_of_mul_eq_mul_left hd (by simpa [mul_comm] using h)
  · intro n hn
    have hn' := mem_filter.mp hn
    have hnIcc := mem_Icc.mp hn'.1
    obtain ⟨k, hk⟩ := hn'.2
    have hkpos : 0 < k := by
      have hnpos : 0 < n := Nat.succ_le_iff.mp hnIcc.1
      rw [hk] at hnpos
      exact Nat.pos_of_mul_pos_left hnpos
    refine ⟨k, mem_Icc.mpr ⟨Nat.succ_le_of_lt hkpos, ?_⟩, by rw [hk, mul_comm]⟩
    exact (Nat.le_div_iff_mul_le hd).mpr (by
      rw [mul_comm, ← hk]
      exact hnIcc.2)

/-- Cost of a finitely supported nonnegative divisor majorant. -/
noncomputable def divisorMajorantCost (D : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, c d / d

/-- Cover-independent Cesàro bound: if `0 ≤ g n ≤ ∑_{d∣n} c_d` then the
average of `g` on `{1, …, X}` is at most the majorant cost. -/
theorem cesaro_le_divisorMajorantCost
    (g : ℕ → ℝ) (D : Finset ℕ) (c : ℕ → ℝ) (X : ℕ)
    (hX : 0 < X)
    (hD : ∀ d ∈ D, 0 < d)
    (hc : ∀ d ∈ D, 0 ≤ c d)
    (hg0 : ∀ n, 0 ≤ g n)
    (hmaj : ∀ n, 0 < n → g n ≤ ∑ d ∈ D.filter (fun d => d ∣ n), c d) :
    (∑ n ∈ Icc 1 X, g n) / X ≤ divisorMajorantCost D c := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hsum :
      ∑ n ∈ Icc 1 X, g n ≤ ∑ d ∈ D, c d * (X / d : ℕ) := by
    calc
      ∑ n ∈ Icc 1 X, g n
          ≤ ∑ n ∈ Icc 1 X, ∑ d ∈ D.filter (fun d => d ∣ n), c d := by
            apply sum_le_sum
            intro n hn
            have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
            exact hmaj n (Nat.succ_le_iff.mp hn1)
      _ = ∑ n ∈ Icc 1 X, ∑ d ∈ D, (if d ∣ n then c d else 0) := by
            apply sum_congr rfl
            intro n hn
            simp [sum_filter]
      _ = ∑ d ∈ D, ∑ n ∈ Icc 1 X, (if d ∣ n then c d else 0) := by
            rw [sum_comm]
      _ = ∑ d ∈ D, c d * ((Icc 1 X).filter (fun n => d ∣ n)).card := by
            apply sum_congr rfl
            intro d hd
            have hconst :
                ∑ n ∈ Icc 1 X, (if d ∣ n then c d else 0) =
                  c d * ((Icc 1 X).filter (fun n => d ∣ n)).card := by
              rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
            simpa using hconst
      _ = ∑ d ∈ D, c d * (X / d : ℕ) := by
            apply sum_congr rfl
            intro d hd
            rw [card_Icc_one_filter_dvd (hD d hd)]
  have hdiv :
      (∑ d ∈ D, c d * (X / d : ℕ)) / X ≤ divisorMajorantCost D c := by
    unfold divisorMajorantCost
    rw [sum_div]
    apply sum_le_sum
    intro d hd
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    calc
      c d * ((X / d : ℕ) : ℝ) / X
          ≤ c d * ((X : ℝ) / d) / X := by
            gcongr
            · exact hc d hd
            · exact Nat.cast_div_le
      _ = c d / d := by
            field_simp [hXne]
  exact (div_le_div_of_nonneg_right hsum hXpos.le).trans hdiv

/-- Trivial coprime cover: putting mass `1` on each modulus costs the
reciprocal sum. Type B Theorem B.1 compares every cover against a stronger
periodic-density lower bound recorded ordinarily. -/
theorem divisorMajorantCost_one (E : Finset ℕ) :
    divisorMajorantCost E (fun _ => (1 : ℝ)) = ∑ a ∈ E, (1 : ℝ) / a := by
  simp [divisorMajorantCost]

#print axioms card_Icc_one_filter_dvd
#print axioms cesaro_le_divisorMajorantCost

end ErdosProblems.Erdos257
