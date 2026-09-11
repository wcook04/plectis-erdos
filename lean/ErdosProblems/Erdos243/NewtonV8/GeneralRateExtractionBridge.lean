import ErdosProblems.Erdos243.NewtonV6.RegularRateExtractionSpec
import ErdosProblems.Erdos243.NewtonV8.RisingQuotients
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# General-rate finite-difference bridge

Status: verified locally by the focused Newton-classification build on
2026-09-09. No declaration assumes the desired
`RegularRateConclusion`.

The retained general-`lambda` extraction theorem has two genuinely separate
formal layers.  This module supplies the first consumer layer: once the sharp
growth estimate `C n = O(n^lambda)` has been obtained from the ratio hypothesis,
the little-o error has zero additive residual, every rising quotient above
`lambda` tends to zero, and integrality makes the corresponding finite
difference eventually vanish.  Polynomial extraction and the final
`A * risingQ n d + B` classification remain separate consumers.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace Erdos243V8

/-- The error appearing literally in `RegularRateHypothesis`. -/
def regularRateError (C : ℕ → ℕ) (lam : ℝ) (n : ℕ) : ℝ :=
  (C (n + 1) : ℝ) / (C n : ℝ) - (1 + lam / (n : ℝ))

/-- Multiplying the relative error by the height gives the additive residual.
The exclusions are exactly the two denominators in the displayed identity. -/
theorem rateResidual_eq_mul_regularRateError (C : ℕ → ℕ) (lam : ℝ) (n : ℕ)
    (hC : C n ≠ 0) (hn : n ≠ 0) :
    rateResidual (fun m => (C m : ℝ)) lam n =
      (C n : ℝ) * regularRateError C lam n := by
  have hCr : (C n : ℝ) ≠ 0 := by exact_mod_cast hC
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [rateResidual, regularRateError]
  field_simp [hCr, hnr]
  ring

/-- The rising denominator dominates the corresponding ordinary power. -/
theorem pow_le_rising (j n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ j ≤ rising j n := by
  induction j generalizing n with
  | zero => simp [rising]
  | succ j ih =>
      rw [rising, pow_succ]
      have hstep : (n : ℝ) ^ j ≤ ((n + 1 : ℕ) : ℝ) ^ j := by
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.le_succ n) j
      have hih := ih (n + 1) (by omega)
      have hn0 : (0 : ℝ) ≤ n := by positivity
      calc
        (n : ℝ) ^ j * (n : ℝ) = (n : ℝ) * (n : ℝ) ^ j := by ring
        _ ≤ (n : ℝ) * rising j (n + 1) :=
          mul_le_mul_of_nonneg_left (hstep.trans hih) hn0

/-- Above its real exponent, the reciprocal rising denominator is little-o of
`n^{-lambda}`.  This is the exact decay needed to consume a sharp
`O(n^lambda)` height bound. -/
theorem inv_rising_isLittleO_rpow_neg (lam : ℝ) (j : ℕ) (hj : lam < j) :
    (fun n : ℕ => (rising j n)⁻¹) =o[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) (-lam)) := by
  rw [isLittleO_iff]
  intro c hc
  have hpow : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (lam - (j : ℝ)))
      atTop (𝓝 0) := by
    have hneg : lam - (j : ℝ) = -((j : ℝ) - lam) := by ring
    rw [hneg]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hj)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hpow c hc
  filter_upwards [eventually_atTop.2 ⟨N, hN⟩,
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hsmall hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hrpos : 0 < rising j n :=
    lt_of_lt_of_le zero_lt_one (rising_one_le j n hn)
  have hden := pow_le_rising j n hn
  have hratio : (rising j n)⁻¹ / Real.rpow (n : ℝ) (-lam) =
      Real.rpow (n : ℝ) (lam - (j : ℝ)) *
        ((n : ℝ) ^ j / rising j n) := by
    have hneg : Real.rpow (n : ℝ) (-lam) =
        (Real.rpow (n : ℝ) lam)⁻¹ :=
      Real.rpow_neg (le_of_lt hnpos) lam
    calc
      (rising j n)⁻¹ / Real.rpow (n : ℝ) (-lam) =
          Real.rpow (n : ℝ) lam / rising j n := by
        rw [hneg, div_inv_eq_mul]
        simp only [div_eq_mul_inv, mul_comm]
      _ = (Real.rpow (n : ℝ) lam / Real.rpow (n : ℝ) (j : ℝ)) *
          ((n : ℝ) ^ j / rising j n) := by
        have hjpow : Real.rpow (n : ℝ) (j : ℝ) = (n : ℝ) ^ j :=
          Real.rpow_natCast (n : ℝ) j
        rw [hjpow]
        field_simp [ne_of_gt hnpos, ne_of_gt hrpos]
      _ = Real.rpow (n : ℝ) (lam - (j : ℝ)) *
          ((n : ℝ) ^ j / rising j n) := by
        exact congrArg
          (fun x : ℝ => x * ((n : ℝ) ^ j / rising j n))
          (Real.rpow_sub hnpos lam (j : ℝ)).symm
  have hfactor : 0 ≤ (n : ℝ) ^ j / rising j n ∧
      (n : ℝ) ^ j / rising j n ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one hrpos).2 hden
  have hscale_nonneg : 0 ≤ Real.rpow (n : ℝ) (lam - (j : ℝ)) :=
    Real.rpow_nonneg (le_of_lt hnpos) _
  have hquot : ‖(rising j n)⁻¹ / Real.rpow (n : ℝ) (-lam)‖ ≤
      Real.rpow (n : ℝ) (lam - (j : ℝ)) := by
    rw [hratio, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hscale_nonneg hfactor.1)]
    exact mul_le_of_le_one_right hscale_nonneg hfactor.2
  have hsmall' : Real.rpow (n : ℝ) (lam - (j : ℝ)) < c := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hscale_nonneg] using hsmall
  have hscale_pos : 0 < Real.rpow (n : ℝ) (-lam) := Real.rpow_pos_of_pos hnpos _
  have hdecomp : (rising j n)⁻¹ =
      ((rising j n)⁻¹ / Real.rpow (n : ℝ) (-lam)) *
        Real.rpow (n : ℝ) (-lam) := by
    field_simp [ne_of_gt hscale_pos]
  rw [hdecomp, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (hquot.trans (le_of_lt hsmall')) (norm_nonneg _)

/-- The exact little-o hypothesis turns into a zero additive residual once the
sharp height bound has been supplied. -/
theorem residual_tendsto_zero_of_regularRate_growth
    (C : ℕ → ℕ) (lam : ℝ)
    (hreg : Erdos243V6.RegularRateHypothesis C lam)
    (hgrowth : (fun n : ℕ => (C n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) lam)) :
    Tendsto (rateResidual (fun n => (C n : ℝ)) lam) atTop (𝓝 0) := by
  obtain ⟨hpos, _hlam, herr⟩ := hreg
  change regularRateError C lam =o[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) (-lam)) at herr
  have hmul := hgrowth.mul_isLittleO herr
  have hrhs : (fun n : ℕ => Real.rpow (n : ℝ) lam *
      Real.rpow (n : ℝ) (-lam)) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    calc
      Real.rpow (n : ℝ) lam * Real.rpow (n : ℝ) (-lam) =
          Real.rpow (n : ℝ) (lam + -lam) :=
        (Real.rpow_add hnpos lam (-lam)).symm
      _ = 1 := by simp
  have hlhs : (fun n : ℕ => (C n : ℝ) * regularRateError C lam n) =ᶠ[atTop]
      rateResidual (fun n => (C n : ℝ)) lam := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    symm
    apply rateResidual_eq_mul_regularRateError
    · exact Nat.ne_of_gt (hpos n hn)
    · omega
  have hsmall : rateResidual (fun n => (C n : ℝ)) lam =o[atTop]
      (fun _ => (1 : ℝ)) := hmul.congr' hlhs hrhs
  exact (isLittleO_one_iff ℝ).mp hsmall

/-- A sharp height bound also makes every rising quotient of order strictly
larger than `lambda` tend to zero. -/
theorem risingQuotient_tendsto_zero_of_regularRate_growth
    (C : ℕ → ℕ) (lam : ℝ) (j : ℕ) (hj : lam < j)
    (hgrowth : (fun n : ℕ => (C n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) lam)) :
    Tendsto (risingQuotient (fun n => (C n : ℝ)) j) atTop (𝓝 0) := by
  have hinv := inv_rising_isLittleO_rpow_neg lam j hj
  have hmul := hgrowth.mul_isLittleO hinv
  have hrhs : (fun n : ℕ => Real.rpow (n : ℝ) lam *
      Real.rpow (n : ℝ) (-lam)) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    calc
      Real.rpow (n : ℝ) lam * Real.rpow (n : ℝ) (-lam) =
          Real.rpow (n : ℝ) (lam + -lam) :=
        (Real.rpow_add hnpos lam (-lam)).symm
      _ = 1 := by simp
  have hlhs : (fun n : ℕ => (C n : ℝ) * (rising j n)⁻¹) =
      risingQuotient (fun n => (C n : ℝ)) j := by
    funext n
    simp [risingQuotient, div_eq_mul_inv]
  have hsmall : risingQuotient (fun n => (C n : ℝ)) j =o[atTop]
      (fun _ => (1 : ℝ)) := hmul.congr' (Eventually.of_forall (congrFun hlhs)) hrhs
  exact (isLittleO_one_iff ℝ).mp hsmall

/-- General integral finite-difference consumer.  Unlike the cubic consumer,
the falling coefficient need not vanish: the quotient itself tends to zero
when `j > lambda`. -/
theorem general_rate_difference_eventually_zero_of_growth
    (C : ℕ → ℕ) (lam : ℝ) (j : ℕ) (hj : lam < j)
    (hreg : Erdos243V6.RegularRateHypothesis C lam)
    (hgrowth : (fun n : ℕ => (C n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.rpow (n : ℝ) lam)) :
    ∃ N, ∀ n, N ≤ n → fd j (fun m => (C m : ℤ)) n = 0 := by
  let CZ : ℕ → ℤ := fun n => (C n : ℤ)
  let CR : ℕ → ℝ := fun n => (C n : ℝ)
  have hres := residual_tendsto_zero_of_regularRate_growth C lam hreg hgrowth
  have happ := forward_difference_approximation CR
    (risingQuotient CR) (rateResidual CR lam)
    (fun k n => rising k (n + 1)) lam
    (by intro n; simp [risingQuotient, rising, CR])
    (by
      intro k
      exact eventually_atTop.2 ⟨1, fun n hn =>
        rising_quotient_difference CR lam k n hn⟩)
    (by
      intro k
      exact Eventually.of_forall fun n => rising_one_le k (n + 1) (by omega))
    hres j
  have hq := risingQuotient_tendsto_zero_of_regularRate_growth C lam j hj hgrowth
  have hcoeff : Tendsto (fun n =>
      (∏ k ∈ Finset.range j, (lam - (k : ℝ))) * risingQuotient CR j n)
      atTop (𝓝 0) := by
    simpa [CR] using (tendsto_const_nhds.mul hq)
  have hfdR : Tendsto (fun n => fd j CR n) atTop (𝓝 0) := by
    have := happ.add hcoeff
    simpa only [sub_add_cancel, add_zero] using this
  have hfdZ : Tendsto (fun n => (fd (R := ℤ) j CZ n : ℝ)) atTop (𝓝 0) := by
    have heq : (fun n => (fd (R := ℤ) j CZ n : ℝ)) =
        (fun n => fd (R := ℝ) j CR n) := by
      funext n
      simpa only [CZ, CR] using (fd_cast_int CZ j n).symm
    rw [heq]
    exact hfdR
  exact integer_zero_of_tendsto_zero (fd (R := ℤ) j CZ) hfdZ

end Erdos243V8
end
