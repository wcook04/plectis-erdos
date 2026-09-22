import ErdosProblems.Erdos1049.SourceBClearingR12
import ErdosProblems.Erdos1049.ActualMomentGeneratingR12
import ErdosProblems.Erdos1049.PaperLinearFormsR7
import Mathlib

/-!
# Absolutely convergent Lambert-window summation for the literal source B

Proves A_n F - B_n equals the absolutely convergent pole series.

The finite correction terms are exactly those of `sourceBReal`, not a newly
chosen constant term. All geometric and Lambert sums below have a summability
proof before `tsum` is used. The terminal theorem identifies A*F-B with the
actual partial-fraction series. The separate residue/interpolation calculation
must still identify that series with the positive hypergeometric H.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset
open PaperR10 PaperR11 PaperR12
open scoped BigOperators

noncomputable def lambertQTerm (q : ℝ) (t : ℕ) : ℝ :=
  q ^ (t + 1) / (1 - q ^ (t + 1))
noncomputable def lambertQ (q : ℝ) : ℝ := ∑' t : ℕ, lambertQTerm q t

noncomputable def lambertWindowTerm (q : ℝ) (a c t : ℕ) : ℝ :=
  q ^ ((a + 1) * (c + 1 + t)) / (1 - q ^ (c + 1 + t))
noncomputable def lambertWindow (q : ℝ) (a c : ℕ) : ℝ :=
  ∑' t : ℕ, lambertWindowTerm q a c t

lemma lambertWindowTerm_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (a c t : ℕ) : 0 ≤ lambertWindowTerm q a c t := by
  have hpow := positive_shift_power_lt_one hq0 hq1 (c + 1 + t) (by omega)
  exact div_nonneg (pow_nonneg hq0.le _) (sub_pos.mpr hpow).le

lemma lambertWindowTerm_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (a c t : ℕ) :
    lambertWindowTerm q a c t ≤ (1 - q)⁻¹ * q ^ (c + 1) * q ^ t := by
  have hbase : q ^ (c + 1 + t) ≤ q := by
    simpa using qpow_antitone hq0.le hq1.le (by omega : 1 ≤ c + 1 + t)
  have hexp : c + 1 + t ≤ (a + 1) * (c + 1 + t) := by nlinarith
  have hnum := qpow_antitone hq0.le hq1.le hexp
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hden' : 1 - q ≤ 1 - q ^ (c + 1 + t) := by linarith
  unfold lambertWindowTerm
  calc
    _ ≤ q ^ (c + 1 + t) / (1 - q ^ (c + 1 + t)) :=
      div_le_div_of_nonneg_right hnum (hden.le.trans hden')
    _ ≤ q ^ (c + 1 + t) / (1 - q) :=
      div_le_div_of_nonneg_left (pow_nonneg hq0.le _) hden hden'
    _ = _ := by rw [pow_add]; ring

/-- Absolute convergence for every source window, including a=c=0. -/
theorem lambertWindowTerm_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (a c : ℕ) : Summable (lambertWindowTerm q a c) := by
  apply summable_nonneg_dominated (lambertWindowTerm_nonneg hq0 hq1 a c)
    (lambertWindowTerm_le hq0 hq1 a c)
  exact (summable_geometric_of_lt_one hq0.le hq1).mul_left _

theorem lambertQTerm_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (lambertQTerm q) := by
  have he : lambertQTerm q = lambertWindowTerm q 0 0 := by
    funext t
    simp only [lambertWindowTerm, lambertQTerm, zero_add, one_mul, Nat.add_comm]
  rw [he]
  exact lambertWindowTerm_summable hq0 hq1 0 0

lemma lambertWindow_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (c : ℕ) :
    lambertWindow q 0 c = lambertQ q - ∑ t ∈ range c, lambertQTerm q t := by
  have h := (lambertQTerm_summable hq0 hq1).sum_add_tsum_nat_add c
  have he : (fun t : ℕ => lambertQTerm q (t + c)) = lambertWindowTerm q 0 c := by
    funext t
    have hx : t + c + 1 = c + 1 + t := by omega
    simp only [lambertQTerm, lambertWindowTerm, zero_add, one_mul, hx]
  rw [he] at h
  change (∑ t ∈ range c, lambertQTerm q t) + lambertWindow q 0 c = lambertQ q at h
  linarith

lemma lambertWindowTerm_succ {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (a c t : ℕ) :
    lambertWindowTerm q (a + 1) c t = lambertWindowTerm q a c t -
      q ^ ((a + 1) * (c + 1 + t)) := by
  have hden := (sub_pos.mpr
    (positive_shift_power_lt_one hq0 hq1 (c + 1 + t) (by omega))).ne'
  have hexp : (a + 1 + 1) * (c + 1 + t) =
      (a + 1) * (c + 1 + t) + (c + 1 + t) := by ring
  unfold lambertWindowTerm
  rw [hexp, pow_add]
  field_simp [hden]
  <;> ring

lemma lambertWindow_succ {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a c : ℕ) :
    lambertWindow q (a + 1) c = lambertWindow q a c -
      q ^ ((a + 1) * (c + 1)) / (1 - q ^ (a + 1)) := by
  have hpow := positive_shift_power_lt_one hq0 hq1 (a + 1) (by omega)
  have hg := (hasSum_geometric_of_lt_one (pow_nonneg hq0.le (a + 1)) hpow).mul_left
    (q ^ ((a + 1) * (c + 1)))
  have he : (fun t : ℕ => q ^ ((a + 1) * (c + 1 + t))) =
      (fun t : ℕ => q ^ ((a + 1) * (c + 1)) * (q ^ (a + 1)) ^ t) := by
    funext t
    rw [Nat.mul_add, pow_add, pow_mul, pow_mul]
  have hg' : HasSum (fun t : ℕ => q ^ ((a + 1) * (c + 1 + t)))
      (q ^ ((a + 1) * (c + 1)) * (1 - q ^ (a + 1))⁻¹) := by
    rw [he]
    exact hg
  unfold lambertWindow
  simp_rw [lambertWindowTerm_succ hq0 hq1]
  rw [(lambertWindowTerm_summable hq0 hq1 a c).tsum_sub hg'.summable, hg'.tsum_eq]
  ring

/-- The complete Lambert/geometric summation identity with its finite windows.
Natural c is the number of omitted initial Lambert terms; a is the number of
finite geometric corrections. There are no hidden negative-index sums. -/
theorem lambertWindow_identity {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (a c : ℕ) :
    lambertWindow q a c = lambertQ q -
      (∑ t ∈ range c, lambertQTerm q t) -
      ∑ j ∈ range a, q ^ ((j + 1) * (c + 1)) / (1 - q ^ (j + 1)) := by
  induction a with
  | zero => simpa using lambertWindow_zero hq0 hq1 c
  | succ a ih =>
      rw [lambertWindow_succ hq0 hq1, ih, sum_range_succ]
      ring

lemma inverse_base_pole_identity {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (j : ℕ) (hj : 1 ≤ j) :
    ((q⁻¹) ^ j - 1)⁻¹ = q ^ j / (1 - q ^ j) := by
  have hqj := pow_ne_zero j hq0.ne'
  have hden := (sub_pos.mpr (positive_shift_power_lt_one hq0 hq1 j hj)).ne'
  rw [inv_pow]
  field_simp [hqj, hden]
  <;> ring

/-- The paper's literal F(x) is the convergent q-Lambert sum at q=1/x. -/
theorem paperLambert_inverse_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    PaperR7.paperLambert q⁻¹ = lambertQ q := by
  unfold PaperR7.paperLambert lambertQ
  apply tsum_congr
  intro t
  simpa only [one_div, lambertQTerm] using inverse_base_pole_identity hq0 hq1 (t + 1) (by omega)

theorem paperLambert_summable (x : ℝ) (hx : 1 < x) :
    Summable (fun t : ℕ => 1 / (x ^ (t + 1) - 1)) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hq0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hq1 : x⁻¹ < 1 := (inv_lt_one₀ hx0).mpr hx
  have he : (fun t : ℕ => 1 / (x ^ (t + 1) - 1)) = lambertQTerm x⁻¹ := by
    funext t
    simpa only [inv_inv, one_div, lambertQTerm] using
      inverse_base_pole_identity hq0 hq1 (t + 1) (by omega)
  rw [he]
  exact lambertQTerm_summable hq0 hq1

lemma sum_range_shift_one {K : Type*} [AddCommMonoid K] (f : ℕ → K) (m : ℕ) :
    (∑ i ∈ range m, f (i + 1)) = ∑ j ∈ Icc 1 m, f j := by
  classical
  apply sum_bij (fun i _ => i + 1)
  · intro i hi
    exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hi; omega⟩
  · intro i hi j hj hij
    omega
  · intro j hj
    obtain ⟨hj0, hjm⟩ := mem_Icc.mp hj
    refine ⟨j - 1, mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rfl

lemma literal_source_B_window {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    sourceBReal n q⁻¹ =
      ∑ s ∈ range (13 * n + 1),
        (sourceASummand n s).eval₂ (Int.castRingHom ℝ) q⁻¹ *
          (lambertQ q - lambertWindow q (14 * n) (2 * n + s)) := by
  unfold sourceBReal sourceBValue
  simp only [coe_eval₂RingHom, eval₂_X]
  apply sum_congr rfl
  intro s hs
  congr 1
  rw [lambertWindow_identity hq0 hq1]
  have hf : (∑ l ∈ Icc 1 (2 * n + s), ((q⁻¹) ^ l - 1)⁻¹) =
      ∑ t ∈ range (2 * n + s), lambertQTerm q t := by
    rw [← sum_range_shift_one]
    apply sum_congr rfl
    intro t ht
    exact inverse_base_pole_identity hq0 hq1 (t + 1) (by omega)
  have hg : (∑ j ∈ Icc 1 (14 * n),
      (q⁻¹) ^ (-((j * (2 * n + s) : ℕ) : ℤ)) * ((q⁻¹) ^ j - 1)⁻¹) =
      ∑ j ∈ range (14 * n), q ^ ((j + 1) * (2 * n + s + 1)) / (1 - q ^ (j + 1)) := by
    rw [← sum_range_shift_one]
    apply sum_congr rfl
    intro j hj
    rw [inverse_base_pole_identity hq0 hq1 (j + 1) (by omega)]
    simp only [zpow_neg, zpow_natCast, inv_pow, inv_inv]
    have hexp : (j + 1) * (2 * n + s + 1) = (j + 1) * (2 * n + s) + (j + 1) := by ring
    rw [hexp, pow_add]
    ring
  rw [hf, hg]
  ring

lemma summable_finset_family {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (h : ∀ i ∈ s, Summable (f i)) : Summable (fun t => ∑ i ∈ s, f i t) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
      intro h
      simp only [sum_insert hi]
      exact (h i (mem_insert_self i s)).add
        (ih (fun j hj => h j (mem_insert_of_mem hj)))

lemma tsum_finset_family {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (h : ∀ i ∈ s, Summable (f i)) :
    (∑' t : ℕ, ∑ i ∈ s, f i t) = ∑ i ∈ s, ∑' t : ℕ, f i t := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
      intro h
      have hs := fun j hj => h j (mem_insert_of_mem hj)
      simp only [sum_insert hi]
      rw [(h i (mem_insert_self i s)).tsum_add (summable_finset_family s f hs), ih hs]

/-- Literal residues multiplied by their shifted pole tails. This definition
retains the exact A_s already used to define the source polynomials. -/
noncomputable def sourcePoleSeriesTerm (q : ℝ) (n t : ℕ) : ℝ :=
  ∑ s ∈ range (13 * n + 1),
    (sourceASummand n s).eval₂ (Int.castRingHom ℝ) q⁻¹ *
      lambertWindowTerm q (14 * n) (2 * n + s) t

noncomputable def sourcePoleSeries (q : ℝ) (n : ℕ) : ℝ :=
  ∑' t : ℕ, sourcePoleSeriesTerm q n t

theorem sourcePoleSeriesTerm_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    Summable (sourcePoleSeriesTerm q n) := by
  apply summable_finset_family
  intro s hs
  exact (lambertWindowTerm_summable hq0 hq1 (14 * n) (2 * n + s)).mul_left _

/-- Analytic summation of the actual source partial fractions. The remaining
algebraic task is precisely to identify these terms with the zero-extended
positive H terms; no identity with H is assumed in this theorem. -/
theorem actual_A_Lambert_sub_B_eq_pole_series {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (sourceA n).eval₂ (Int.castRingHom ℝ) q⁻¹ * PaperR7.paperLambert q⁻¹ -
      sourceBReal n q⁻¹ = sourcePoleSeries q n := by
  rw [paperLambert_inverse_eq hq0 hq1, literal_source_B_window hq0 hq1]
  unfold sourcePoleSeries sourcePoleSeriesTerm
  rw [tsum_finset_family _ _ (fun s _ =>
    (lambertWindowTerm_summable hq0 hq1 (14 * n) (2 * n + s)).mul_left _)]
  simp only [tsum_mul_left]
  change _ = ∑ s ∈ range (13 * n + 1),
    (sourceASummand n s).eval₂ (Int.castRingHom ℝ) q⁻¹ *
      lambertWindow q (14 * n) (2 * n + s)
  have hA : (sourceA n).eval₂ (Int.castRingHom ℝ) q⁻¹ =
      ∑ s ∈ range (13 * n + 1), (sourceASummand n s).eval₂ (Int.castRingHom ℝ) q⁻¹ := by
    exact map_sum (eval₂RingHom (Int.castRingHom ℝ) q⁻¹) _ _
  rw [hA, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro s hs
  ring

end ErdosProblems.Erdos1049.PaperR14
