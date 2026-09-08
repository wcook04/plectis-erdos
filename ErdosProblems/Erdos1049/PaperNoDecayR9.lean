import ErdosProblems.Erdos1049.PaperLongCapR9

/-!
A failure of homogenised decay below the square boundary, without assuming
that the normalised degrees converge. Decay would itself give a global upper
degree rate smaller than sigma, contradicting the checked polynomial cap.
This does not assert full-sequence divergence or irrationality of the value.
-/
namespace ErdosProblems.Erdos1049.PaperR9
open Filter
open scoped Topology

/-- A unit bound on the cleared remainder forces an upper rate for actual degrees. -/
theorem degree_upper_of_cleared_eventually_unit
    (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h b x : ℝ)
    (H : CapHypotheses U V F σ δ h) (hb : 1 < b) (hx : 1 < x)
    (hunit : ∀ᶠ n in atTop,
      |b ^ pairWidth U V n * polynomialRemainder U V F x n| ≤ 1) :
    QuadUpper (fun n => (pairWidth U V n : ℝ))
      (σ * Real.log x / Real.log b) := by
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hidentity := cleared_log_identity (pairWidth U V)
    (polynomialRemainder U V F x) b (zero_lt_one.trans hb) (H.nonzero x hx)
  intro ε hε
  have he : 0 < ε * Real.log b := mul_pos hε hlb
  filter_upwards [hunit, hidentity,
    littleO_bound _ (H.remainder_rate x hx) (ε * Real.log b) he] with n hu hi hr
  have hcleared : Real.log |b ^ pairWidth U V n *
      polynomialRemainder U V F x n| ≤ 0 := Real.log_nonpos (abs_nonneg _) hu
  rw [hi] at hcleared
  have hlo := (abs_le.mp hr).1
  have hcancel : σ * Real.log x / Real.log b * Real.log b = σ * Real.log x :=
    div_mul_cancel₀ _ hlb.ne'
  have hmul : (pairWidth U V n : ℝ) * Real.log b ≤
      ((σ * Real.log x / Real.log b + ε) * sqScale n) * Real.log b := by
    calc
      (pairWidth U V n : ℝ) * Real.log b ≤
          σ * Real.log x * sqScale n + (ε * Real.log b) * sqScale n := by
            linarith
      _ = (σ * Real.log x / Real.log b * Real.log b) * sqScale n +
          (ε * Real.log b) * sqScale n := by rw [hcancel]
      _ = ((σ * Real.log x / Real.log b + ε) * sqScale n) * Real.log b := by ring
  nlinarith

/-- No eventual unit bound is possible below the square boundary. -/
theorem cleared_below_square_not_eventually_unit
    (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h b x : ℝ)
    (H : CapHypotheses U V F σ δ h) (hb : 1 < b)
    (hx : 1 < x) (hxb : x < b) :
    ¬ (∀ᶠ n in atTop,
      |b ^ pairWidth U V n * polynomialRemainder U V F x n| ≤ 1) := by
  intro hunit
  let c := σ * Real.log x / Real.log b
  have hlb : 0 < Real.log b := Real.log_pos hb
  have hcpos : 0 < c := div_pos (mul_pos H.sigma_pos (Real.log_pos hx)) hlb
  have hclt : c < σ := by
    apply (div_lt_iff₀ hlb).mpr
    exact mul_lt_mul_of_pos_left
      (Real.log_lt_log (zero_lt_one.trans hx) hxb) H.sigma_pos
  have HC : CapHypotheses U V F σ c h :=
    ⟨H.sigma_pos, hcpos, H.height_nonneg,
      degree_upper_of_cleared_eventually_unit U V F σ δ h b x H hb hx hunit,
      H.height_upper, H.nonzero, H.remainder_rate⟩
  exact (not_lt_of_ge (sigma_le_delta U V F σ c h HC)) hclt

/-- The actual homogenised forms cannot tend to zero when `b < a < b²`.
The hypothesis concerns a polynomial family at every base greater than one;
this is not a statement about arbitrary approximations at a single base. -/
theorem cleared_below_square_not_tendsto_zero
    (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : LongCapHypotheses U V F σ δ h)
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) (hsquare : a < b * b) :
    ¬ Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
      polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0) := by
  have hb1 : 1 < b := by nlinarith
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb1
  have hbpos : (0 : ℝ) < b := zero_lt_one.trans hbR
  have hx : (1 : ℝ) < (a : ℝ) / b :=
    (one_lt_div hbpos).mpr (by exact_mod_cast hab)
  have hxb : (a : ℝ) / b < b :=
    (div_lt_iff₀ hbpos).mpr (by exact_mod_cast hsquare)
  intro hzero
  apply cleared_below_square_not_eventually_unit U V F σ δ h b ((a : ℝ) / b)
    (H.toShort U V F σ δ h) hbR hx hxb
  filter_upwards [(Metric.tendsto_nhds.mp hzero) 1 (by norm_num)] with n hn
  simpa only [Real.dist_eq, sub_zero] using hn.le

#print axioms cleared_below_square_not_tendsto_zero
end ErdosProblems.Erdos1049.PaperR9
