import ErdosProblems.Erdos1049.PaperAsymptoticsR9
import ErdosProblems.Erdos1049.PaperHomogenisationR7

/-!
The complete short-note cap, as an uncompiled proof-source candidate.

This is not an additional source-supply axiom: the hypotheses are the displayed
polynomial degree, l1 height, nonvanishing and logarithmic-rate hypotheses.
`QuadUpper` makes the paper's upper o(n^2) inequalities precise. The result is
proved for any real target function, hence also for the actual paperLambert.
No condition uniform in x beyond common constants is required: each fixed x
has its own eventual estimates, exactly as in the paper.

The long-record max-coefficient-height and limsup conclusions are separate.
-/
namespace ErdosProblems.Erdos1049.PaperR9
open Filter Asymptotics
open scoped Topology

noncomputable def pairWidth (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ :=
  max (U n).natDegree (V n).natDegree

noncomputable def pairHeight (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℝ :=
  max (PaperR7.coeffL1 (U n)) (PaperR7.coeffL1 (V n))

noncomputable def polynomialRemainder (U V : ℕ → Polynomial ℤ)
    (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x -
    (V n).eval₂ (Int.castRingHom ℝ) x

/-- Bundles only the hypotheses of res:archimedean-cap, not its conclusion. -/
structure CapHypotheses (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) : Prop where
  sigma_pos : 0 < σ
  delta_pos : 0 < δ
  height_nonneg : 0 ≤ h
  degree_upper : QuadUpper (fun n => (pairWidth U V n : ℝ)) δ
  height_upper : QuadUpper (fun n => Real.log (pairHeight U V n)) h
  nonzero : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, polynomialRemainder U V F x n ≠ 0
  remainder_rate : ∀ x : ℝ, 1 < x →
    QuadLogRate (polynomialRemainder U V F x) (-σ * Real.log x)

lemma coeffL1_nonneg (P : Polynomial ℤ) : 0 ≤ PaperR7.coeffL1 P := by
  unfold PaperR7.coeffL1
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-- The evaluation estimate uses the actual degree and l1 norm. -/
theorem polynomial_eval_exp_upper (U V : ℕ → Polynomial ℤ)
    (δ h x : ℝ) (hx : 1 < x)
    (hdeg : QuadUpper (fun n => (pairWidth U V n : ℝ)) δ)
    (hheight : QuadUpper (fun n => Real.log (pairHeight U V n)) h) :
    QuadExpUpper (fun n => (U n).eval₂ (Int.castRingHom ℝ) x)
      (h + δ * Real.log x) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hu := hheight.add (hdeg.const_mul hlog.le)
  intro ε hε
  filter_upwards [hu ε hε] with n hn
  have hwidth : (U n).natDegree ≤ pairWidth U V n := le_max_left _ _
  have heval := PaperR7.abs_eval_real_le_coeffL1_mul_pow
    (U n) (pairWidth U V n) x hx.le hwidth
  have hpow : 0 ≤ x ^ pairWidth U V n :=
    pow_nonneg (zero_lt_one.trans hx).le _
  have hH : PaperR7.coeffL1 (U n) ≤ Real.exp (Real.log (pairHeight U V n)) :=
    (le_max_left _ _).trans (Real.le_exp_log _)
  have hp : x ^ pairWidth U V n =
      Real.exp ((pairWidth U V n : ℝ) * Real.log x) := by
    rw [← Real.log_pow]
    exact (Real.exp_log (pow_pos (zero_lt_one.trans hx) _)).symm
  calc
    |(U n).eval₂ (Int.castRingHom ℝ) x| ≤
        PaperR7.coeffL1 (U n) * x ^ pairWidth U V n := heval
    _ ≤ Real.exp (Real.log (pairHeight U V n)) * x ^ pairWidth U V n :=
      mul_le_mul_of_nonneg_right hH hpow
    _ = Real.exp (Real.log (pairHeight U V n) +
        Real.log x * (pairWidth U V n : ℝ)) := by
      rw [hp, ← Real.exp_add, mul_comm (pairWidth U V n : ℝ)]
    _ ≤ Real.exp ((h + δ * Real.log x + ε) * sqScale n) := by
      apply Real.exp_le_exp.mpr
      simpa only [mul_comm (Real.log x) δ] using hn

/-- The omitted analytic step of the paper cap is now composed with its integer core. -/
theorem sigma_le_delta (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : CapHypotheses U V F σ δ h) : σ ≤ δ := by
  by_contra hn
  have hgap : 0 < σ - δ := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨p, hp⟩ := exists_nat_gt (max 1 (Real.exp (h / (σ - δ))))
  have hp1 : (1 : ℝ) < p := (le_max_left _ _).trans_lt hp
  have hpexp : Real.exp (h / (σ - δ)) < (p : ℝ) :=
    (le_max_right _ _).trans_lt hp
  have hpLog : h / (σ - δ) < Real.log p := by
    have ht := Real.log_lt_log (Real.exp_pos (h / (σ - δ))) hpexp
    simpa only [Real.log_exp] using ht
  have hstrict : h + δ * Real.log p < σ * Real.log p := by
    have ht := (div_lt_iff₀ hgap).mp hpLog
    nlinarith
  let A : ℕ → ℤ := fun n => (U n).eval (p : ℤ)
  let B : ℕ → ℤ := fun n => (V n).eval (p : ℤ)
  -- API: Algebra/Polynomial/Eval/Defs.lean, `eval₂_at_natCast`.
  have hcastU : ∀ n,
      (A n : ℝ) = (U n).eval₂ (Int.castRingHom ℝ) (p : ℝ) := by
    intro n
    exact (Polynomial.eval₂_at_natCast (p := U n) (Int.castRingHom ℝ) p).symm
  have hcastV : ∀ n,
      (B n : ℝ) = (V n).eval₂ (Int.castRingHom ℝ) (p : ℝ) := by
    intro n
    exact (Polynomial.eval₂_at_natCast (p := V n) (Int.castRingHom ℝ) p).symm
  have hrem : (fun n => (A n : ℝ) * F p - B n) =
      polynomialRemainder U V F p := by
    funext n
    rw [hcastU, hcastV]
    rfl
  have hA : QuadExpUpper (fun n => (A n : ℝ)) (h + δ * Real.log p) := by
    have hu := polynomial_eval_exp_upper U V δ h p hp1 H.degree_upper H.height_upper
    simpa only [hcastU] using hu
  have hL : QuadLogRate (fun n => (A n : ℝ) * F p - B n) (- (σ * Real.log p)) := by
    rw [hrem]
    simpa only [neg_mul] using H.remainder_rate p hp1
  have hne : ∀ᶠ n in atTop, (A n : ℝ) * F p - B n ≠ 0 := by
    filter_upwards [H.nonzero p hp1] with n hn
    simpa only [hcastU n, hcastV n, polynomialRemainder] using hn
  have hα : 0 ≤ h + δ * Real.log p :=
    add_nonneg H.height_nonneg (mul_nonneg H.delta_pos.le (Real.log_pos hp1).le)
  have hc := rate_le_height_rate A B (F p) (h + δ * Real.log p)
    (σ * Real.log p) hα hne hA hL
  exact (not_lt_of_ge hc) hstrict

lemma width_power_exp_upper (d : ℕ → ℕ) (b δ : ℝ) (hb : 1 ≤ b)
    (hd : QuadUpper (fun n => (d n : ℝ)) δ) :
    QuadExpUpper (fun n => b ^ d n) (δ * Real.log b) := by
  apply expUpper_of_logUpper
  have hlog : 0 ≤ Real.log b := Real.log_nonneg hb
  have h := hd.const_mul hlog
  have heq : (fun n => Real.log |b ^ d n|) =
      (fun n => Real.log b * (d n : ℝ)) := by
    funext n
    rw [abs_of_nonneg (pow_nonneg (zero_le_one.trans hb) _), Real.log_pow, mul_comm]
  rw [heq]
  simpa only [mul_comm (Real.log b) δ] using h

/-- Actual-degree homogeneous remainders, no substituted common width. -/
theorem cleared_forms_tendsto_zero (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : CapHypotheses U V F σ δ h)
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a)
    (hregion : Real.log b / Real.log a < σ / (σ + δ)) :
    Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
      polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := zero_lt_one.trans_le hbR
  have habR : (b : ℝ) < a := by exact_mod_cast hab
  have haR : (1 : ℝ) < a := hbR.trans_lt habR
  have hx : (1 : ℝ) < (a : ℝ) / b := (one_lt_div hbpos).mpr habR
  have hbalance : δ * Real.log b - σ * Real.log ((a : ℝ) / b) < 0 :=
    (PaperR7.logarithmic_region_iff_negative_balance a b σ δ haR hbpos
      H.sigma_pos H.delta_pos).mp hregion
  have hd := width_power_exp_upper (pairWidth U V) b δ hbR H.degree_upper
  have he := (H.remainder_rate ((a : ℝ) / b) hx).exp_upper
  have hu := hd.mul he
  apply hu.tendsto_zero
  simpa only [sub_eq_add_neg, neg_mul] using hbalance

/-- Full short-paper conclusion, with its two different clauses preserved. -/
theorem short_note_archimedean_cap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : CapHypotheses U V F σ δ h) :
    σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    ∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
      Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0) := by
  refine ⟨(PaperR7.half_cap_iff σ δ H.sigma_pos H.delta_pos).mpr
    (sigma_le_delta U V F σ δ h H), ?_⟩
  intro a b hb hab hregion
  exact cleared_forms_tendsto_zero U V F σ δ h H a b hb hab hregion

/-- Bridge from the literal upper little-o notation to QuadUpper. -/
theorem quadUpper_of_littleO_upper (f r : ℕ → ℝ) (a : ℝ)
    (hr : r =o[atTop] sqScale)
    (hf : ∀ᶠ n in atTop, f n ≤ a * sqScale n + r n) : QuadUpper f a := by
  intro ε hε
  filter_upwards [hf, littleO_bound r hr ε hε] with n hn he
  have hr' := (le_abs_self (r n)).trans he
  nlinarith

end ErdosProblems.Erdos1049.PaperR9
