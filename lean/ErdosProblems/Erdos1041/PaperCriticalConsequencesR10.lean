import ErdosProblems.Erdos1041.PaperCriticalValueMeanR10
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-! Sharpness, distributional control and existence of a small critical value.
These are numerical/analytic consequences only, not path-length conclusions.
All Lean builds and axiom audits are UNRUN. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace ErdosProblems.Erdos1041
open Polynomial Real PaperAnalyticTargets

def radialEqualityPolynomial (n : ℕ) (h lam : ℂ) : ℂ[X] := (X - C h) ^ n - C lam

theorem radialEqualityPolynomial_monic_degree (n : ℕ) (hn : 0 < n) (h lam : ℂ) :
    (radialEqualityPolynomial n h lam).IsMonicOfDegree n := by
  have H : ((X - C h : ℂ[X]) ^ n).IsMonicOfDegree n := by
    simpa only [one_mul] using (isMonicOfDegree_X_sub_one h).pow n
  exact H.sub (by simpa only [natDegree_C] using hn)

theorem radialEqualityPolynomial_roots (n : ℕ) (hn : 0 < n) (h lam : ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hlam : ‖lam‖ = R ^ n) :
    RootsInClosedDisc (radialEqualityPolynomial n h lam) h R := by
  intro z hz
  have hzpow : (z - h) ^ n = lam := by
    simpa only [radialEqualityPolynomial, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero] using hz
  have he : ‖z - h‖ ^ n = R ^ n := by
    simpa only [norm_pow, hlam] using congrArg norm hzpow
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) hR
    (show (0 : ℝ) < n by exact_mod_cast hn)).mp
  simpa only [Real.rpow_natCast, he] using (le_refl (R ^ n))

theorem radialEqualityPolynomial_critical (n : ℕ) (h lam : ℂ) :
    CriticalEnumeration (radialEqualityPolynomial n h lam) (fun _ : Fin (n - 1) => h) := by
  unfold CriticalEnumeration radialEqualityPolynomial
  simp only [derivative_sub, derivative_X_sub_C_pow, derivative_C, sub_zero,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exact sharpness for every positive exponent, including R=0. -/
theorem radialEqualityPolynomial_moment (n : ℕ) (hn : 0 < n) (h lam : ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hlam : ‖lam‖ = R ^ n) (t : ℝ) :
    (∑ _j : Fin (n - 1), ‖(radialEqualityPolynomial n h lam).eval h‖ ^ t) =
      ((n - 1 : ℕ) : ℝ) * R ^ ((n : ℝ) * t) := by
  simp only [radialEqualityPolynomial, eval_sub, eval_pow, eval_X, eval_C,
    sub_self, zero_pow (Nat.ne_of_gt hn), zero_sub, norm_neg, hlam,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Real.rpow_natCast R n, ← Real.rpow_mul hR]

/-- The two constants in the short-paper theorem are attained simultaneously. -/
theorem paper_critical_mean_sharpness (n : ℕ) (hn : 2 ≤ n) (h lam : ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hlam : ‖lam‖ = R ^ n) :
    let p := radialEqualityPolynomial n h lam
    p.Monic ∧ p.natDegree = n ∧ RootsInClosedDisc p h R ∧
    CriticalEnumeration p (fun _ : Fin (n - 1) => h) ∧
    (∑ _j : Fin (n - 1), ‖p.eval h‖ ^ (2 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖p.eval h‖ ^ (1 / (n : ℝ))) = ((n : ℝ) - 1) * R := by
  dsimp only
  have hn0 : 0 < n := by omega
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  refine ⟨(radialEqualityPolynomial_monic_degree n hn0 h lam).monic,
    (radialEqualityPolynomial_monic_degree n hn0 h lam).natDegree_eq,
    radialEqualityPolynomial_roots n hn0 h lam R hR hlam,
    radialEqualityPolynomial_critical n h lam, ?_, ?_⟩
  · have H := radialEqualityPolynomial_moment n hn0 h lam R hR hlam (2 / ((n : ℝ) - 1))
    have he : (n : ℝ) * (2 / ((n : ℝ) - 1)) = 2 * (n : ℝ) / ((n : ℝ) - 1) := by ring
    simpa only [hcast, he] using H
  · have H := radialEqualityPolynomial_moment n hn0 h lam R hR hlam (1 / (n : ℝ))
    have he : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
    simpa only [hcast, he, Real.rpow_one] using H

/-- Finite Markov bound, including repeated values as separate indices. -/
theorem finite_power_tail_bound {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (p t B : ℝ) (hp : 0 < p) (ht : 0 < t)
    (H : ∑ i, x i ^ p ≤ B) :
    ((Finset.univ.filter (fun i => t ≤ x i)).card : ℝ) ≤ B / t ^ p := by
  classical
  let A := Finset.univ.filter (fun i => t ≤ x i)
  have htP : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have H1 : (A.card : ℝ) * t ^ p ≤ ∑ i ∈ A, x i ^ p := by
    calc
      _ = ∑ _i ∈ A, t ^ p := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi =>
        Real.rpow_le_rpow ht.le (Finset.mem_filter.mp hi).2 hp.le)
  have H2 : (∑ i ∈ A, x i ^ p) ≤ ∑ i, x i ^ p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun i _ _ => Real.rpow_nonneg (hx i) p)
  exact (le_div_iff₀ htP).mpr (H1.trans (H2.trans H))

/-- Normalised critical radii have every moment up to 2n/(n-1).
The long-paper exponent n/(n-1) is a strict subset of this range. -/
theorem critical_normalised_radius_moment {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.Monic) (hdeg : f.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 < R)
    (hroots : RootsInClosedDisc f h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration f c) (p : ℝ) (hp : 0 < p)
    (hpmax : p ≤ 2 * (n : ℝ) / ((n : ℝ) - 1)) :
    (∑ j, (‖f.eval (c j)‖ ^ (1 / (n : ℝ)) / R) ^ p) ≤ (n : ℝ) - 1 := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have ht : p / (n : ℝ) ≤ 2 / ((n : ℝ) - 1) := by
    apply (div_le_iff₀ hnpos).mpr
    calc
      p ≤ 2 * (n : ℝ) / ((n : ℝ) - 1) := hpmax
      _ = (2 / ((n : ℝ) - 1)) * (n : ℝ) := by ring
  have H := critical_disc_moment hn f hf hdeg h R hR.le hroots c hc
    (p / (n : ℝ)) (div_pos hp hnpos) ht
  have hexp : (n : ℝ) * (p / (n : ℝ)) = p := by field_simp
  rw [hexp] at H
  have he (j : Fin (n - 1)) :
      (‖f.eval (c j)‖ ^ (1 / (n : ℝ)) / R) ^ p =
        ‖f.eval (c j)‖ ^ (p / (n : ℝ)) / R ^ p := by
    rw [Real.div_rpow (Real.rpow_nonneg (norm_nonneg _) _) hR.le,
      ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    ring
  simp only [he, ← Finset.sum_div]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hR p)).mpr H

/-- Exactly the concentration estimate displayed in the long paper. -/
theorem paper_critical_radius_tail {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.Monic) (hdeg : f.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 < R)
    (hroots : RootsInClosedDisc f h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration f c) (t : ℝ) (ht : 0 < t) :
    ((Finset.univ.filter (fun j => t * R ≤ ‖f.eval (c j)‖ ^ (1 / (n : ℝ)))).card : ℝ) ≤
      ((n : ℝ) - 1) / t ^ ((n : ℝ) / ((n : ℝ) - 1)) := by
  classical
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  let p := (n : ℝ) / ((n : ℝ) - 1)
  have hp : 0 < p := div_pos hnpos hmpos
  have hmax : p ≤ 2 * (n : ℝ) / ((n : ℝ) - 1) := by
    apply (div_le_div_iff_of_pos_right hmpos).mpr
    linarith
  have H := critical_normalised_radius_moment hn f hf hdeg h R hR hroots c hc p hp hmax
  have Htail := finite_power_tail_bound
    (fun j => ‖f.eval (c j)‖ ^ (1 / (n : ℝ)) / R)
    (fun j => div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hR.le)
    p t ((n : ℝ) - 1) hp ht H
  simpa only [le_div_iff₀ hR, p] using Htail

/-- The budget supplies a small critical value but no connecting path. -/
theorem exists_critical_value_le_radius_power {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.Monic) (hdeg : f.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc f h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration f c) : ∃ j, ‖f.eval (c j)‖ ≤ R ^ n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ht : (0 : ℝ) < 1 / (n : ℝ) := div_pos (by norm_num) hnpos
  have he : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
  have hRpow : (R ^ n) ^ (1 / (n : ℝ)) = R := by
    rw [← Real.rpow_natCast R n, ← Real.rpow_mul hR, he, Real.rpow_one]
  by_contra! hnot
  have hterm (j : Fin (n - 1)) : R < ‖f.eval (c j)‖ ^ (1 / (n : ℝ)) := by
    rw [← hRpow]
    exact Real.rpow_lt_rpow (pow_nonneg hR n) (hnot j) ht
  have Hlt := Finset.sum_lt_sum (s := Finset.univ)
    (fun j _ => (hterm j).le)
    ⟨⟨0, by omega⟩, Finset.mem_univ _, hterm _⟩
  have H := (paper_critical_value_mean n f c h R hn hf hdeg hR hroots hc).2
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcast] at Hlt
  exact (not_lt_of_ge H) Hlt

end ErdosProblems.Erdos1041
end
