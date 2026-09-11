import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
# Rational denominator survival

This module owns the domain-neutral elimination step from displayed rational
data to a divisibility statement about the reduced denominator.  Downstream
domains remain responsible for proving their divisor and coprimality
certificates.
-/

namespace Erdos249257.RationalDenominatorSurvival

/-- A divisor of a displayed denominator survives rational reduction when it
is coprime to the displayed numerator. -/
theorem divisor_dvd_divInt_den
    {a : ℤ} {D m : ℕ} (hD : 0 < D) (hmD : m ∣ D)
    (hcop : Nat.Coprime m a.natAbs) :
    m ∣ (Rat.divInt a (D : ℤ)).den := by
  let q : ℚ := Rat.divInt a (D : ℤ)
  have hq : q = Rat.divInt a (D : ℤ) := rfl
  obtain ⟨c, hac, hDc⟩ :=
    Rat.num_den_mk (Int.natCast_ne_zero.mpr hD.ne') hq
  have hc_dvd : c.natAbs ∣ a.natAbs := by
    rw [hac, Int.natAbs_mul]
    exact dvd_mul_right _ _
  have hcop_c : Nat.Coprime m c.natAbs := hcop.of_dvd_right hc_dvd
  have hD_abs : D = c.natAbs * q.den := by
    have h := congrArg Int.natAbs hDc
    simpa [Int.natAbs_mul] using h
  have hmprod : m ∣ c.natAbs * q.den := by
    simpa [← hD_abs] using hmD
  exact (hcop_c.dvd_mul_left).mp hmprod

/-- Scaling can cancel the part `gcd C h`, but no further part of `C` when
`C` was coprime to the unscaled numerator. -/
theorem survivingDivisor_dvd_scaled_divInt_den
    {a : ℤ} {D C h : ℕ} (hD : 0 < D) (hCD : C ∣ D)
    (hcop : Nat.Coprime C a.natAbs) :
    C / Nat.gcd C h ∣
      (Rat.divInt ((h : ℤ) * a) (D : ℤ)).den := by
  let g := Nat.gcd C h
  have hCpos : 0 < C := Nat.pos_of_dvd_of_pos hCD hD
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left h hCpos
  have hgC : g ∣ C := Nat.gcd_dvd_left C h
  have hgh : g ∣ h := Nat.gcd_dvd_right C h
  have hgD : g ∣ D := hgC.trans hCD
  have hDdivpos : 0 < D / g :=
    Nat.div_pos (Nat.le_of_dvd hD hgD) hgpos
  have hCDdiv : C / g ∣ D / g := by
    rw [Nat.dvd_div_iff_mul_dvd hgD, Nat.mul_div_cancel' hgC]
    exact hCD
  have hCghg : Nat.Coprime (C / g) (h / g) := by
    simpa [g] using Nat.coprime_div_gcd_div_gcd
      (Nat.gcd_pos_of_pos_left h hCpos)
  have hCgC : C / g ∣ C := Nat.div_dvd_of_dvd hgC
  have hCga : Nat.Coprime (C / g) a.natAbs := hcop.of_dvd_left hCgC
  have hCgnum :
      Nat.Coprime (C / g) (((h / g : ℕ) : ℤ) * a).natAbs := by
    simpa [Int.natAbs_mul] using hCghg.mul_right hCga
  have hhEq : (h : ℤ) = (g : ℤ) * ((h / g : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgh).symm
  have hDEq : (D : ℤ) = (g : ℤ) * ((D / g : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgD).symm
  have hrat :
      Rat.divInt ((h : ℤ) * a) (D : ℤ) =
        Rat.divInt (((h / g : ℕ) : ℤ) * a) ((D / g : ℕ) : ℤ) := by
    apply (Rat.divInt_eq_divInt_iff
      (Int.natCast_ne_zero.mpr hD.ne')
      (Int.natCast_ne_zero.mpr hDdivpos.ne')).2
    rw [hhEq, hDEq]
    ring
  rw [hrat]
  simpa [g] using divisor_dvd_divInt_den hDdivpos hCDdiv hCgnum

/-! Small executable regressions for the cancellation boundary. -/

example : 2 ∣ 6 ∧ ¬2 ∣ (Rat.divInt 2 6).den := by
  norm_num [Rat.divInt]

example : 6 / Nat.gcd 6 0 ∣ (Rat.divInt ((0 : ℤ) * 1) 12).den := by
  exact survivingDivisor_dvd_scaled_divInt_den
    (a := 1) (D := 12) (C := 6) (h := 0) (by norm_num) (by norm_num)
      (by norm_num)

example : (Rat.divInt 4 12).den = 3 := by
  norm_num [Rat.divInt]

example : (Rat.divInt (-15) 12).den = 4 := by
  norm_num [Rat.divInt]

example : 24 / Nat.gcd 24 6 = 4 ∧ (Rat.divInt 6 72).den = 12 := by
  norm_num [Rat.divInt]

example {C : ℕ} (h : Nat.Coprime C 0) : C = 1 := by
  simpa using h

example {a : ℤ} {D C h : ℕ} (hD : 0 < D) (hCD : C ∣ D)
    (hCa : Nat.Coprime C a.natAbs) (hCh : Nat.Coprime C h) :
    C ∣ (Rat.divInt ((h : ℤ) * a) (D : ℤ)).den := by
  simpa [hCh.gcd_eq_one] using
    survivingDivisor_dvd_scaled_divInt_den (h := h) hD hCD hCa

end Erdos249257.RationalDenominatorSurvival
