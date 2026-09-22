import ErdosProblems.Erdos1049.PositiveSeriesR16
import ErdosProblems.Erdos1049.ActualMomentGeneratingR12

/-!
# Analytic q-binomial ratios and the positive Euler factor

New candidate; elaboration and axiom audit UNRUN. This module closes the
recurrence-to-analytic-identity implication. Coefficient bounds and product
nonvanishing are obtained from the existing QProductBoundsR10 module.
-/
namespace ErdosProblems.Erdos1049.PaperR16
open PaperR10 PaperR12 Filter
open scoped BigOperators Topology

@[simp] lemma qPochhammerInfinity_zero (q : ℝ) :
    qPochhammerInfinity 0 q = 1 := by
  simp [qPochhammerInfinity]

lemma qPochhammerInfinity_le_one {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    qPochhammerInfinity a q ≤ 1 := by
  simpa using qPochhammerInfinity_le_finite ha0 ha1 hq0 hq1 0

lemma qPochhammerInfinity_antitone_arg {a b q : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    qPochhammerInfinity b q ≤ qPochhammerInfinity a q := by
  have hb0 := ha0.trans hab
  apply le_of_tendsto_of_tendsto
    (tendsto_qPochhammerFinite hb0 hb1 hq0 hq1)
    (tendsto_qPochhammerFinite ha0 (hab.trans_lt hb1) hq0 hq1)
  apply Filter.Eventually.of_forall
  intro n
  unfold qPochhammerFinite
  apply Finset.prod_le_prod
  · intro k hk
    have hu : b * q ^ k ≤ b := by
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1.le) hb0
    linarith
  · intro k hk
    have h := mul_le_mul_of_nonneg_right hab (pow_nonneg hq0 k)
    linarith

lemma shifted_qPochhammerInfinity_lower {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) {t : ℕ} (ht : 1 ≤ t) :
    qPochhammerInfinity q q ≤ qPochhammerInfinity (q ^ t) q := by
  apply qPochhammerInfinity_antitone_arg (pow_nonneg hq0.le t) _ hq1 hq0.le hq1
  simpa using qpow_antitone hq0.le hq1.le ht

lemma qBinomialRatioCoeff_recurrence {a q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    qBinomialRatioCoeff a q (n + 1) * (1 - q ^ (n + 1)) =
      qBinomialRatioCoeff a q n * (1 - a * q ^ n) := by
  have hpow : q ^ (n + 1) ≤ q := by
    simpa using qpow_antitone hq0 hq1.le (by omega : 1 ≤ n + 1)
  have hd : 1 - q ^ (n + 1) ≠ 0 := by linarith
  rw [qBinomialRatioCoeff, div_mul_cancel₀ _ hd]

lemma qBinomialRatio_hasSum {a q w : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Summable (fun n : ℕ => qBinomialRatioCoeff a q n * w ^ n) :=
  summable_coeffEval_of_bounded
    (qBinomialRatioCoeff_nonneg ha0 ha1 hq0 hq1)
    (qBinomialRatioCoeff_upper ha0 ha1 hq0 hq1) hw0 hw1

lemma qBinomialRatio_functional {a q w : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    (1 - w) * coeffEval (qBinomialRatioCoeff a q) w =
      (1 - a * w) * coeffEval (qBinomialRatioCoeff a q) (q * w) := by
  have hqw0 : 0 ≤ q * w := mul_nonneg hq0 hw0
  have hqw1 : q * w < 1 := by
    have h : q * w ≤ w := by
      simpa using mul_le_mul_of_nonneg_right hq1.le hw0
    exact h.trans_lt hw1
  have h := coeffEval_functional_equation
    (qBinomialRatio_hasSum ha0 ha1 hq0 hq1 hw0 hw1)
    (qBinomialRatio_hasSum ha0 ha1 hq0 hq1 hqw0 hqw1)
    (u := 1) (v := -a)
    (fun n => by simpa only [neg_mul, sub_eq_add_neg] using
      qBinomialRatioCoeff_recurrence (a := a) hq0 hq1 n)
  simpa only [one_mul, neg_mul, ← sub_eq_add_neg] using h

lemma qBinomialRatio_finite_identity {a q w : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) (n : ℕ) :
    coeffEval (qBinomialRatioCoeff a q) w * qPochhammerFinite w q n =
      qPochhammerFinite (a * w) q n *
        coeffEval (qBinomialRatioCoeff a q) (q ^ n * w) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hz0 : 0 ≤ q ^ n * w := mul_nonneg (pow_nonneg hq0 n) hw0
      have hz1 : q ^ n * w < 1 := by
        have h : q ^ n * w ≤ w := by
          simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1.le) hw0
        exact h.trans_lt hw1
      have hf := qBinomialRatio_functional ha0 ha1 hq0 hq1 hz0 hz1
      have he : q * (q ^ n * w) = q ^ (n + 1) * w := by rw [pow_succ]; ring
      rw [he] at hf
      rw [qPochhammerFinite_succ, qPochhammerFinite_succ]
      calc
        _ = (coeffEval (qBinomialRatioCoeff a q) w * qPochhammerFinite w q n) *
            (1 - q ^ n * w) := by ring
        _ = (qPochhammerFinite (a * w) q n *
            coeffEval (qBinomialRatioCoeff a q) (q ^ n * w)) *
            (1 - q ^ n * w) := by rw [ih]
        _ = qPochhammerFinite (a * w) q n *
            ((1 - q ^ n * w) * coeffEval (qBinomialRatioCoeff a q) (q ^ n * w)) := by ring
        _ = qPochhammerFinite (a * w) q n *
            ((1 - a * (q ^ n * w)) *
              coeffEval (qBinomialRatioCoeff a q) (q ^ (n + 1) * w)) := by rw [hf]
        _ = _ := by ring

/-- The analytic q-binomial identity, proved from the existing coefficient
recurrence and an explicit product limit. No identity is assumed. -/
theorem qBinomialRatio_eval {a q w : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    coeffEval (qBinomialRatioCoeff a q) w =
      qPochhammerInfinity (a * w) q / qPochhammerInfinity w q := by
  have haw0 : 0 ≤ a * w := mul_nonneg ha0 hw0
  have haw1 : a * w < 1 := by
    have h : a * w ≤ w := by
      simpa using mul_le_mul_of_nonneg_right ha1 hw0
    exact h.trans_lt hw1
  have hn : Tendsto (fun n : ℕ => n + 1) atTop atTop := (tendsto_add_atTop_iff_nat 1).2 tendsto_id
  have hp := (tendsto_qPochhammerFinite hw0 hw1 hq0 hq1).comp hn
  have hpa := (tendsto_qPochhammerFinite haw0 haw1 hq0 hq1).comp hn
  have he := coeffEval_tendsto_geometric
    (qBinomialRatioCoeff_nonneg ha0 ha1 hq0 hq1)
    (qBinomialRatioCoeff_upper ha0 ha1 hq0 hq1)
    (by rfl : qBinomialRatioCoeff a q 0 = 1) hq0 hq1 hw0 hw1.le
  have hl := hp.const_mul (coeffEval (qBinomialRatioCoeff a q) w)
  have hr := hpa.mul he
  have hid : coeffEval (qBinomialRatioCoeff a q) w * qPochhammerInfinity w q =
      qPochhammerInfinity (a * w) q := by
    apply tendsto_nhds_unique hl
    simpa only [mul_one] using hr.congr' (Filter.Eventually.of_forall (fun n =>
      (qBinomialRatio_finite_identity ha0 ha1 hq0 hq1 hw0 hw1 (n + 1)).symm))
  exact (eq_div_iff (qPochhammerInfinity_pos w q).ne').2 hid

/-- Reciprocal q-product coefficients; the a=0 case is not a separate
unproved Euler/q-binomial identity. -/
noncomputable def inverseQCoeff (q : ℝ) : ℕ → ℝ := qBinomialRatioCoeff 0 q

lemma inverseQCoeff_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    inverseQCoeff q n = (qPochhammerFinite q q n)⁻¹ := by
  rw [inverseQCoeff, qBinomialRatioCoeff_eq_ratio hq0 hq1]
  simp [qPochhammerFinite]

lemma inverseQCoeff_bounds {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    1 ≤ inverseQCoeff q n ∧ inverseQCoeff q n ≤ (qPochhammerInfinity q q)⁻¹ := by
  constructor
  · simpa [inverseQCoeff] using
      qBinomialRatioCoeff_lower (a := 0) (by norm_num) (by norm_num) hq0 hq1 n
  · exact qBinomialRatioCoeff_upper (by norm_num) (by norm_num) hq0 hq1 n

theorem inverseQCoeff_eval {q w : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    coeffEval (inverseQCoeff q) w = (qPochhammerInfinity w q)⁻¹ := by
  simpa [inverseQCoeff] using
    qBinomialRatio_eval (a := 0) (by norm_num) (by norm_num) hq0 hq1 hw0 hw1

/-- A natural-number exponent with no truncated subtraction ambiguity. -/
def eulerOrder (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, i

@[simp] lemma eulerOrder_zero : eulerOrder 0 = 0 := by simp [eulerOrder]
lemma eulerOrder_succ (n : ℕ) : eulerOrder (n + 1) = eulerOrder n + n := by
  simp [eulerOrder, Finset.sum_range_succ]

lemma le_eulerOrder_succ (n : ℕ) : n ≤ eulerOrder (n + 1) := by
  rw [eulerOrder_succ]
  omega

noncomputable def eulerCoeff (q : ℝ) (n : ℕ) : ℝ :=
  q ^ eulerOrder n / qPochhammerFinite q q n

@[simp] lemma eulerCoeff_zero (q : ℝ) : eulerCoeff q 0 = 1 := by
  simp [eulerCoeff]

lemma eulerCoeff_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    0 ≤ eulerCoeff q n :=
  div_nonneg (pow_nonneg hq0 _) (qPochhammerFinite_pos hq0 hq1 hq0 hq1.le n).le

lemma eulerCoeff_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    eulerCoeff q n ≤ (qPochhammerInfinity q q)⁻¹ := by
  unfold eulerCoeff
  have hd := qPochhammerFinite_pos hq0 hq1 hq0 hq1.le n
  calc
    _ ≤ 1 / qPochhammerFinite q q n :=
      div_le_div_of_nonneg_right (pow_le_one₀ hq0 hq1.le) hd.le
    _ ≤ 1 / qPochhammerInfinity q q :=
      one_div_le_one_div_of_le (qPochhammerInfinity_pos q q)
        (qPochhammerInfinity_le_finite hq0 hq1 hq0 hq1 n)
    _ = _ := one_div _

lemma eulerCoeff_succ_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    eulerCoeff q (n + 1) ≤ (qPochhammerInfinity q q)⁻¹ * q ^ n := by
  unfold eulerCoeff
  have hd := qPochhammerFinite_pos hq0 hq1 hq0 hq1.le (n + 1)
  calc
    _ ≤ q ^ n / qPochhammerFinite q q (n + 1) :=
      div_le_div_of_nonneg_right
        (qpow_antitone hq0 hq1.le (le_eulerOrder_succ n)) hd.le
    _ ≤ q ^ n / qPochhammerInfinity q q :=
      div_le_div_of_nonneg_left (pow_nonneg hq0 n) (qPochhammerInfinity_pos q q)
        (qPochhammerInfinity_le_finite hq0 hq1 hq0 hq1 (n + 1))
    _ = _ := by ring

/-- Euler's positive product is summable at one, which is stronger than
convergence only inside the open unit interval. -/
theorem eulerCoeff_summable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (eulerCoeff q) := by
  apply (summable_nat_add_iff 1).1
  apply summable_nonneg_dominated
    (fun n => eulerCoeff_nonneg hq0 hq1 (n + 1))
    (fun n => eulerCoeff_succ_le hq0 hq1 n)
  exact (hasSum_geometric_of_lt_one hq0 hq1).summable.mul_left _

lemma eulerCoeff_weighted_summable {q w : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Summable (fun n : ℕ => eulerCoeff q n * w ^ n) := by
  apply summable_nonneg_dominated
    (fun n => mul_nonneg (eulerCoeff_nonneg hq0 hq1 n) (pow_nonneg hw0 n))
    (fun n => by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (pow_le_one₀ hw0 hw1 : w ^ n ≤ 1)
          (eulerCoeff_nonneg hq0 hq1 n))
    (eulerCoeff_summable hq0 hq1)

lemma eulerCoeff_recurrence {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    eulerCoeff q (n + 1) * (1 - q ^ (n + 1)) = eulerCoeff q n * q ^ n := by
  have hp := (qPochhammerFinite_pos hq0 hq1 hq0 hq1.le n).ne'
  have hqpow : q ^ (n + 1) ≤ q := by
    simpa using qpow_antitone hq0 hq1.le (by omega : 1 ≤ n + 1)
  have hd : 1 - q ^ (n + 1) ≠ 0 := by linarith
  unfold eulerCoeff
  rw [eulerOrder_succ, pow_add, qPochhammerFinite_succ]
  have he : q * q ^ n = q ^ (n + 1) := by rw [pow_succ]; ring
  rw [he]
  field_simp [hp, hd]
  <;> ring

lemma eulerEval_functional {q w : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    coeffEval (eulerCoeff q) w = (1 + w) * coeffEval (eulerCoeff q) (q * w) := by
  have hqw0 := mul_nonneg hq0 hw0
  have hqw1 : q * w ≤ 1 := by
    calc
      q * w ≤ 1 * w := mul_le_mul_of_nonneg_right hq1.le hw0
      _ ≤ 1 := by simpa using hw1
  have h := coeffEval_functional_equation
    (eulerCoeff_weighted_summable hq0 hq1 hw0 hw1)
    (eulerCoeff_weighted_summable hq0 hq1 hqw0 hqw1)
    (u := 0) (v := 1)
    (fun n => by simpa using eulerCoeff_recurrence hq0 hq1 n)
  simpa using h

/-- The mass of the Euler coefficient sequence. Its finite-product limit
identifies it with (-1;q)_infinity in ordinary product notation. -/
noncomputable def eulerMass (q : ℝ) : ℝ := ∑' n : ℕ, eulerCoeff q n

lemma one_le_eulerMass {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 ≤ eulerMass q := by
  have h := (eulerCoeff_summable hq0 hq1).sum_le_tsum ({0} : Finset ℕ)
    (fun n _ => eulerCoeff_nonneg hq0 hq1 n)
  simpa [eulerMass] using h

lemma eulerScale_summable {q a : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Summable (coeffScale (eulerCoeff q) a) :=
  eulerCoeff_weighted_summable hq0 hq1 ha0 ha1

lemma eulerScale_mass_le {q a : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∑' n, coeffScale (eulerCoeff q) a n) ≤ eulerMass q := by
  apply Summable.tsum_le_tsum _ (eulerScale_summable hq0 hq1 ha0 ha1)
    (eulerCoeff_summable hq0 hq1)
  intro n
  simpa [coeffScale] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ ha0 ha1) (eulerCoeff_nonneg hq0 hq1 n)


/-- Even/odd splitting of the genuine positive product. -/
lemma qPochhammerInfinity_even_odd {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    qPochhammerInfinity a q =
      qPochhammerInfinity a (q ^ 2) * qPochhammerInfinity (a * q) (q ^ 2) := by
  have hq20 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq21 : q ^ 2 < 1 := by nlinarith
  have haq0 := mul_nonneg ha0 hq0
  have haq1 : a * q < 1 := by
    have h : a * q ≤ a := by simpa using mul_le_mul_of_nonneg_left hq1.le ha0
    exact h.trans_lt ha1
  have he := (summable_log_qPochhammer ha0 ha1 hq20 hq21).hasSum
  have ho := (summable_log_qPochhammer haq0 haq1 hq20 hq21).hasSum
  have he' : HasSum (fun n : ℕ => Real.log (1 - a * q ^ (2 * n)))
      (∑' n : ℕ, Real.log (1 - a * (q ^ 2) ^ n)) := by
    simpa only [pow_mul] using he
  have ho' : HasSum (fun n : ℕ => Real.log (1 - a * q ^ (2 * n + 1)))
      (∑' n : ℕ, Real.log (1 - (a * q) * (q ^ 2) ^ n)) := by
    refine ho.congr_fun (fun n => ?_)
    congr 1
    simp only [pow_mul, pow_add, pow_one]
    ring
  have h := (HasSum.even_add_odd (f := fun n : ℕ => Real.log (1 - a * q ^ n)) he' ho').tsum_eq
  unfold qPochhammerInfinity
  rw [h, Real.exp_add]

lemma eulerEval_finite_identity {q w : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) (n : ℕ) :
    coeffEval (eulerCoeff q) w * qPochhammerFinite w q n =
      coeffEval (eulerCoeff q) (q ^ n * w) *
        qPochhammerFinite (w ^ 2) (q ^ 2) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hz0 := mul_nonneg (pow_nonneg hq0 n) hw0
      have hz1 : q ^ n * w ≤ 1 := by
        calc
          q ^ n * w ≤ 1 * w :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1.le) hw0
          _ ≤ 1 := by simpa using hw1.le
      have hf := eulerEval_functional hq0 hq1 hz0 hz1
      have he : q * (q ^ n * w) = q ^ (n + 1) * w := by rw [pow_succ]; ring
      rw [he] at hf
      have hsquare : (q ^ n * w) ^ 2 = w ^ 2 * (q ^ 2) ^ n := by
        simp only [mul_pow, ← pow_mul]
        simp [Nat.mul_comm, mul_comm]
      rw [qPochhammerFinite_succ, qPochhammerFinite_succ]
      calc
        _ = (coeffEval (eulerCoeff q) w * qPochhammerFinite w q n) *
            (1 - q ^ n * w) := by ring
        _ = (coeffEval (eulerCoeff q) (q ^ n * w) *
            qPochhammerFinite (w ^ 2) (q ^ 2) n) * (1 - q ^ n * w) := by rw [ih]
        _ = coeffEval (eulerCoeff q) (q ^ (n + 1) * w) *
            (qPochhammerFinite (w ^ 2) (q ^ 2) n * (1 - (q ^ n * w) ^ 2)) := by
              rw [hf]
              ring
        _ = _ := by rw [hsquare]

/-- The positive Euler coefficient supplier, identified with its product
using only positive-argument q-products already in the canonical library. -/
theorem eulerEval_pochhammer_identity {q w : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    coeffEval (eulerCoeff q) w * qPochhammerInfinity w q =
      qPochhammerInfinity (w ^ 2) (q ^ 2) := by
  have hq21 : q ^ 2 < 1 := by nlinarith
  have hw21 : w ^ 2 < 1 := by nlinarith
  have hn : Tendsto (fun n : ℕ => n + 1) atTop atTop := (tendsto_add_atTop_iff_nat 1).2 tendsto_id
  have hp := (tendsto_qPochhammerFinite hw0 hw1 hq0 hq1).comp hn
  have hp2 := (tendsto_qPochhammerFinite (sq_nonneg w) hw21 (sq_nonneg q) hq21).comp hn
  have he := coeffEval_tendsto_geometric
    (eulerCoeff_nonneg hq0 hq1) (eulerCoeff_le hq0 hq1)
    (eulerCoeff_zero q) hq0 hq1 hw0 hw1.le
  have hl := hp.const_mul (coeffEval (eulerCoeff q) w)
  apply tendsto_nhds_unique hl
  simpa only [one_mul] using (he.mul hp2).congr' (Filter.Eventually.of_forall
    (fun n => (eulerEval_finite_identity hq0 hq1 hw0 hw1 (n + 1)).symm))

/-- The numerator splitting in the paper, with the Euler factors supplied
by convergent nonnegative coefficient series, not formal square roots. -/
theorem pairedEulerRatio_identity {a b q w : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (hab : b ^ 2 = q * a ^ 2) :
    coeffEval (qBinomialRatioCoeff a q) w *
      coeffEval (qBinomialRatioCoeff b q) w *
      coeffEval (eulerCoeff q) (a * w) *
      coeffEval (eulerCoeff q) (b * w) =
      qPochhammerInfinity (a ^ 2 * w ^ 2) q /
        (qPochhammerInfinity w q) ^ 2 := by
  have haw0 := mul_nonneg ha0 hw0
  have hbw0 := mul_nonneg hb0 hw0
  have haw1 : a * w < 1 := by
    have h : a * w ≤ w := by simpa using mul_le_mul_of_nonneg_right ha1 hw0
    exact h.trans_lt hw1
  have hbw1 : b * w < 1 := by
    have h : b * w ≤ w := by simpa using mul_le_mul_of_nonneg_right hb1 hw0
    exact h.trans_lt hw1
  have hA0 : 0 ≤ a ^ 2 * w ^ 2 := mul_nonneg (sq_nonneg a) (sq_nonneg w)
  have hA1 : a ^ 2 * w ^ 2 < 1 := by
    have h : (a * w) ^ 2 < 1 := by nlinarith
    simpa [mul_pow] using h
  have hea := eulerEval_pochhammer_identity hq0 hq1 haw0 haw1
  have heb := eulerEval_pochhammer_identity hq0 hq1 hbw0 hbw1
  have hes := qPochhammerInfinity_even_odd hA0 hA1 hq0 hq1
  have hsq : (b * w) ^ 2 = (a ^ 2 * w ^ 2) * q := by rw [mul_pow, hab]; ring
  rw [hsq] at heb
  rw [mul_pow] at hea
  rw [qBinomialRatio_eval ha0 ha1 hq0 hq1 hw0 hw1,
    qBinomialRatio_eval hb0 hb1 hq0 hq1 hw0 hw1]
  apply (eq_div_iff (pow_ne_zero 2 (qPochhammerInfinity_pos w q).ne')).2
  field_simp [(qPochhammerInfinity_pos w q).ne']
  calc
    _ = (coeffEval (eulerCoeff q) (a * w) * qPochhammerInfinity (a * w) q) *
        (coeffEval (eulerCoeff q) (b * w) * qPochhammerInfinity (b * w) q) := by ring
    _ = _ := by rw [hea, heb, ← hes]

noncomputable def qPlusFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, (1 + a * q ^ j)

lemma eulerEval_plus_finite {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    coeffEval (eulerCoeff q) a =
      qPlusFinite a q n * coeffEval (eulerCoeff q) (q ^ n * a) := by
  induction n with
  | zero => simp [qPlusFinite]
  | succ n ih =>
      have hz0 := mul_nonneg (pow_nonneg hq0 n) ha0
      have hz1 : q ^ n * a ≤ 1 := by
        calc
          q ^ n * a ≤ 1 * a :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1.le) ha0
          _ ≤ 1 := by simpa using ha1
      have hf := eulerEval_functional hq0 hq1 hz0 hz1
      have harg : q * (q ^ n * a) = q ^ (n + 1) * a := by rw [pow_succ]; ring
      rw [harg] at hf
      calc
        _ = qPlusFinite a q n * coeffEval (eulerCoeff q) (q ^ n * a) := ih
        _ = qPlusFinite a q n *
            ((1 + q ^ n * a) * coeffEval (eulerCoeff q) (q ^ (n + 1) * a)) := by rw [hf]
        _ = _ := by
          simp only [qPlusFinite, Finset.prod_range_succ]
          ring

/-- A cofinal finite-product sequence tends to the Euler mass. This fixes
exactly which positive number is denoted by (-1;q)_infinity. -/
theorem tendsto_qPlusFinite_succ {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => qPlusFinite a q (n + 1)) atTop
      (𝓝 (coeffEval (eulerCoeff q) a)) := by
  have he := coeffEval_tendsto_geometric
    (eulerCoeff_nonneg hq0 hq1) (eulerCoeff_le hq0 hq1)
    (eulerCoeff_zero q) hq0 hq1 ha0 ha1
  have hquot := (tendsto_const_nhds.div he (by norm_num : (1 : ℝ) ≠ 0) :
    Tendsto (fun n : ℕ => coeffEval (eulerCoeff q) a /
      coeffEval (eulerCoeff q) (q ^ (n + 1) * a)) atTop
      (𝓝 (coeffEval (eulerCoeff q) a / 1)))
  have heq (n : ℕ) : qPlusFinite a q (n + 1) =
      coeffEval (eulerCoeff q) a /
        coeffEval (eulerCoeff q) (q ^ (n + 1) * a) := by
    have hz0 := mul_nonneg (pow_nonneg hq0 (n + 1)) ha0
    have hz1 : q ^ (n + 1) * a < 1 := by
      have hp : q ^ (n + 1) ≤ q := by
        simpa using qpow_antitone hq0 hq1.le (by omega : 1 ≤ n + 1)
      have h : q ^ (n + 1) * a ≤ q ^ (n + 1) := by
        simpa using mul_le_mul_of_nonneg_left ha1 (pow_nonneg hq0 (n + 1))
      exact (h.trans hp).trans_lt hq1
    have hp : 0 < coeffEval (eulerCoeff q) (q ^ (n + 1) * a) :=
      lt_of_lt_of_le (by norm_num) (coeffEval_bounds
        (eulerCoeff_nonneg hq0 hq1) (eulerCoeff_le hq0 hq1)
        (eulerCoeff_zero q) hz0 hz1).1
    exact (eq_div_iff hp.ne').2 (eulerEval_plus_finite ha0 ha1 hq0 hq1 (n + 1)).symm
  simpa only [div_one] using hquot.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm))

end ErdosProblems.Erdos1049.PaperR16
