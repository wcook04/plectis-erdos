import Mathlib

/-!
# Arbitrary-base isolated-pulse lattice obstruction

This is the algebraic core for the integer-radix extension of the
fixed-binary-base totient-residue theorem. It accepts a bounded tail orbit and
a fixed rational lattice as explicit hypotheses. The companion analytic
interface constructs that orbit from a bounded series.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7.ArbitraryBasePulse

private theorem iterate_zero_window
    (B : ℕ) (u : ℕ → ℤ) (T : ℕ → ℝ)
    (hrec : ∀ n, (B : ℝ) * T n = (u (n + 1) : ℝ) + T (n + 1)) :
    ∀ L N : ℕ,
      (∀ i, N < i → i ≤ N + L → u i = 0) →
      (B : ℝ) ^ L * T N = T (N + L) := by
  intro L
  induction L with
  | zero =>
      intro N _
      simp
  | succ L ih =>
      intro N hzero
      have hz : u (N + 1) = 0 := hzero (N + 1) (by omega) (by omega)
      have hrec' : (B : ℝ) * T N = T (N + 1) := by simpa [hz] using hrec N
      have hrest : ∀ i, N + 1 < i → i ≤ N + 1 + L → u i = 0 := by
        intro i hi hlo
        exact hzero i (by omega) (by omega)
      calc
        (B : ℝ) ^ (L + 1) * T N = (B : ℝ) ^ L * ((B : ℝ) * T N) := by
          rw [pow_succ]; ring
        _ = (B : ℝ) ^ L * T (N + 1) := by rw [hrec']
        _ = T (N + 1 + L) := ih (N + 1) hrest
        _ = T (N + (L + 1)) := by congr 1; omega

/-- A bounded integer sequence with arbitrarily long two-sided isolated pulses
cannot generate a bounded tail orbit lying in a fixed rational lattice for any
integer radix at least two. -/
theorem no_bounded_lattice_tail_of_pulses
    (B q : ℕ) (hB : 2 ≤ B) (hq : 0 < q)
    (u : ℕ → ℤ) (T : ℕ → ℝ) (C : ℝ)
    (hCu : ∀ n, |(u n : ℝ)| ≤ C)
    (hCT : ∀ n, |T n| ≤ C)
    (hrec : ∀ n, (B : ℝ) * T n = (u (n + 1) : ℝ) + T (n + 1))
    (hlattice : ∀ n, ∃ z : ℤ, (q : ℝ) * T n = (z : ℝ))
    (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ u p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → u (p - j) = 0 ∧ u (p + j) = 0) : False := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hCT 0)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (1 : ℝ) < B := by exact_mod_cast (show 1 < B by omega)
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt ((q : ℝ) * C) hBR
  obtain ⟨p, hp, hne, hzero⟩ := hpulse L
  have hpow : (0 : ℝ) < (B : ℝ) ^ L := pow_pos (by positivity) _
  have hbound : (q : ℝ) * C / (B : ℝ) ^ L < 1 := by
    exact (div_lt_iff₀ hpow).2 (by simpa using hL)
  have hright : ∀ i, p < i → i ≤ p + L → u i = 0 := by
    intro i hi hlo
    have hj : 0 < i - p := by omega
    have hjL : i - p ≤ L := by omega
    have hidx : p + (i - p) = i := by omega
    rw [← hidx]
    exact (hzero (i - p) hj hjL).2
  have hright_eq := iterate_zero_window B u T hrec L p hright
  have hTp : (q : ℝ) * |T p| < 1 := by
    have hupper : (B : ℝ) ^ L * |T p| ≤ C := by
      calc
        (B : ℝ) ^ L * |T p| = |(B : ℝ) ^ L * T p| := by
          rw [abs_mul, abs_of_pos hpow]
        _ = |T (p + L)| := by rw [hright_eq]
        _ ≤ C := hCT (p + L)
    have hdiv : |T p| ≤ C / (B : ℝ) ^ L :=
      (le_div_iff₀ hpow).2 (by simpa [mul_comm] using hupper)
    calc
      (q : ℝ) * |T p| ≤ (q : ℝ) * (C / (B : ℝ) ^ L) := by gcongr
      _ = (q : ℝ) * C / (B : ℝ) ^ L := by ring
      _ < 1 := hbound
  obtain ⟨z, hz⟩ := hlattice p
  have hzabs : |(z : ℝ)| < 1 := by
    rw [← hz, abs_mul, abs_of_pos hqR]
    exact hTp
  have hz0 : z = 0 := by
    have hzabs' : |z| < (1 : ℤ) := by exact_mod_cast hzabs
    have hzabs0 : |z| = 0 := by
      have hzn : (0 : ℤ) ≤ |z| := abs_nonneg z
      omega
    exact abs_eq_zero.mp hzabs0
  have hTp0 : T p = 0 := by
    rw [hz0, Int.cast_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left hqR.ne'
  let N := p - L - 1
  have hN : N + L + 1 = p := by dsimp [N]; omega
  have hleft : ∀ i, N < i → i ≤ N + L → u i = 0 := by
    intro i hi hlo
    have hj : 0 < p - i := by dsimp [N] at *; omega
    have hjL : p - i ≤ L := by dsimp [N] at *; omega
    have hidx : p - (p - i) = i := by omega
    rw [← hidx]
    exact (hzero (p - i) hj hjL).1
  have hleft_eq := iterate_zero_window B u T hrec L N hleft
  have hrecp : (B : ℝ) * T (p - 1) = (u p : ℝ) := by
    have hstep := hrec (p - 1)
    have hidx : p - 1 + 1 = p := by omega
    rw [hidx, hTp0] at hstep
    simpa using hstep
  have hleftp : (B : ℝ) ^ (L + 1) * T N = (u p : ℝ) := by
    have hidx : N + L = p - 1 := by omega
    rw [pow_succ]
    calc
      ((B : ℝ) ^ L * B) * T N = B * ((B : ℝ) ^ L * T N) := by ring
      _ = B * T (N + L) := by rw [hleft_eq]
      _ = B * T (p - 1) := by rw [hidx]
      _ = (u p : ℝ) := hrecp
  have hpow' : (0 : ℝ) < (B : ℝ) ^ (L + 1) := pow_pos (by positivity) _
  have hpow_le : (B : ℝ) ^ L ≤ (B : ℝ) ^ (L + 1) := by
    exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ B by omega)) (by omega)
  have hTN : (q : ℝ) * |T N| < 1 := by
    have hu : |(u p : ℝ)| ≤ C := hCu p
    have hupper : (B : ℝ) ^ (L + 1) * |T N| ≤ C := by
      calc
        (B : ℝ) ^ (L + 1) * |T N| = |(B : ℝ) ^ (L + 1) * T N| := by
          rw [abs_mul, abs_of_pos hpow']
        _ = |(u p : ℝ)| := by rw [hleftp]
        _ ≤ C := hu
    have hdiv : |T N| ≤ C / (B : ℝ) ^ (L + 1) :=
      (le_div_iff₀ hpow').2 (by simpa [mul_comm] using hupper)
    have hsmaller : C / (B : ℝ) ^ (L + 1) ≤ C / (B : ℝ) ^ L := by
      apply div_le_div_of_nonneg_left hC hpow hpow_le
    calc
      (q : ℝ) * |T N| ≤ (q : ℝ) * (C / (B : ℝ) ^ (L + 1)) := by gcongr
      _ ≤ (q : ℝ) * (C / (B : ℝ) ^ L) := by gcongr
      _ = (q : ℝ) * C / (B : ℝ) ^ L := by ring
      _ < 1 := hbound
  obtain ⟨w, hw⟩ := hlattice N
  have hwabs : |(w : ℝ)| < 1 := by
    rw [← hw, abs_mul, abs_of_pos hqR]
    exact hTN
  have hw0 : w = 0 := by
    have hwabs' : |w| < (1 : ℤ) := by exact_mod_cast hwabs
    have hwabs0 : |w| = 0 := by
      have hwn : (0 : ℤ) ≤ |w| := abs_nonneg w
      omega
    exact abs_eq_zero.mp hwabs0
  have hTN0 : T N = 0 := by
    rw [hw0, Int.cast_zero] at hw
    exact (mul_eq_zero.mp hw).resolve_left hqR.ne'
  rw [hTN0, mul_zero] at hleftp
  exact hne (by exact_mod_cast hleftp.symm)

end ErdosProblems.Erdos249.PaperCompleteR7.ArbitraryBasePulse

#print axioms ErdosProblems.Erdos249.PaperCompleteR7.ArbitraryBasePulse.no_bounded_lattice_tail_of_pulses
