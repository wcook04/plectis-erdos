import ErdosProblems.Erdos1049.PaperShortCapR9
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.Ring.Int

/-!
The LONG-record cap: maximum coefficient height, actual degrees and logarithmic
limits. UNCOMPILED proof source. This module is deliberately separate from the
short-note l1-height statement.

Pinned APIs: Order/LiminfLimsup.lean (`limsup_eq`, `csInf_le`),
Algebra/Order/Ring/Int.lean (`Nat.cast_natAbs`), and the metric/filter APIs cited
in PaperAsymptoticsR9. Finite support maxima are over naturals, including the
zero polynomial without an artificial positive-height premise.
-/
namespace ErdosProblems.Erdos1049.PaperR9
open Filter Asymptotics
open scoped Topology

noncomputable def maxCoeffNat (P : Polynomial ℤ) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natAbs)

noncomputable def maxPairHeight (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℝ :=
  (max (maxCoeffNat (U n)) (maxCoeffNat (V n)) : ℕ)

lemma abs_coeff_le_maxCoeffNat (P : Polynomial ℤ) (i : ℕ) :
    |(P.coeff i : ℝ)| ≤ (maxCoeffNat P : ℝ) := by
  by_cases hi : i ∈ P.support
  · have hh : (P.coeff i).natAbs ≤ maxCoeffNat P :=
      Finset.le_sup (f := fun j => (P.coeff j).natAbs) hi
    have hc : ((P.coeff i).natAbs : ℝ) ≤ (maxCoeffNat P : ℝ) := by
      exact_mod_cast hh
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
  · have hz : P.coeff i = 0 := by
      by_contra h
      exact hi (Polynomial.mem_support_iff.mpr h)
    simp only [hz, Int.cast_zero, abs_zero]
    exact Nat.cast_nonneg _

lemma coeffL1_le_width_mul_max (P : Polynomial ℤ) (W : ℕ)
    (hW : P.natDegree ≤ W) :
    PaperR7.coeffL1 P ≤ ((W : ℝ) + 1) * (maxCoeffNat P : ℝ) := by
  rw [PaperR7.coeffL1_eq_sum_range P W hW]
  calc
    (∑ i ∈ Finset.range (W + 1), |(P.coeff i : ℝ)|) ≤
        ∑ _i ∈ Finset.range (W + 1), (maxCoeffNat P : ℝ) :=
      Finset.sum_le_sum (fun i _ => abs_coeff_le_maxCoeffNat P i)
    _ = ((W : ℝ) + 1) * (maxCoeffNat P : ℝ) := by simp

lemma pairHeight_le_width_mul_max (U V : ℕ → Polynomial ℤ) (n : ℕ) :
    pairHeight U V n ≤ ((pairWidth U V n : ℝ) + 1) * maxPairHeight U V n := by
  apply max_le
  · have hm : (maxCoeffNat (U n) : ℝ) ≤ maxPairHeight U V n := by
      unfold maxPairHeight
      exact_mod_cast (le_max_left (maxCoeffNat (U n)) (maxCoeffNat (V n)))
    exact (coeffL1_le_width_mul_max (U n) (pairWidth U V n) (le_max_left _ _)).trans
      (mul_le_mul_of_nonneg_left hm (by positivity))
  · have hm : (maxCoeffNat (V n) : ℝ) ≤ maxPairHeight U V n := by
      unfold maxPairHeight
      exact_mod_cast (le_max_right (maxCoeffNat (U n)) (maxCoeffNat (V n)))
    exact (coeffL1_le_width_mul_max (V n) (pairWidth U V n) (le_max_right _ _)).trans
      (mul_le_mul_of_nonneg_left hm (by positivity))

lemma log_pairHeight_le (U V : ℕ → Polynomial ℤ) (n : ℕ) :
    Real.log (pairHeight U V n) ≤
      Real.log ((pairWidth U V n : ℝ) + 1) + Real.log (maxPairHeight U V n) := by
  have hw : 0 < (pairWidth U V n : ℝ) + 1 := by positivity
  have hH : 0 ≤ Real.log (maxPairHeight U V n) := Real.log_natCast_nonneg _
  have hW : 0 ≤ Real.log ((pairWidth U V n : ℝ) + 1) :=
    Real.log_nonneg (by
      have hh : (0 : ℝ) ≤ pairWidth U V n := Nat.cast_nonneg _
      linarith)
  by_cases hz : pairHeight U V n = 0
  · rw [hz, Real.log_zero]
    exact add_nonneg hW hH
  · have hnonneg : 0 ≤ pairHeight U V n :=
      (coeffL1_nonneg (U n)).trans (le_max_left _ _)
    have hp : 0 < pairHeight U V n := lt_of_le_of_ne hnonneg (Ne.symm hz)
    have he : pairHeight U V n ≤ ((pairWidth U V n : ℝ) + 1) *
        Real.exp (Real.log (maxPairHeight U V n)) :=
      (pairHeight_le_width_mul_max U V n).trans
        (mul_le_mul_of_nonneg_left (Real.le_exp_log _) hw.le)
    have hl := Real.log_le_log hp he
    rw [Real.log_mul hw.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    exact hl

/-- The extra factor (degree+1) costs o(n²), not an extra fixed height rate. -/
lemma log_width_plus_one_rate (d : ℕ → ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hd : QuadUpper (fun n => (d n : ℝ)) δ) :
    QuadUpper (fun n => Real.log ((d n : ℝ) + 1)) 0 := by
  intro ε hε
  let C : ℝ := Real.log (δ + 2) + 2
  have hlog : 0 ≤ Real.log (δ + 2) := Real.log_nonneg (by linarith)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  filter_upwards [hd 1 (by norm_num), eventually_ge_atTop (1 : ℕ),
      eventually_linear_le_square C ε hC hε] with n hn hn1 hlin
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hsq1 : (1 : ℝ) ≤ sqScale n := by dsimp [sqScale]; nlinarith
  have hdeg : (d n : ℝ) + 1 ≤ (δ + 2) * (n : ℝ) ^ 2 := by
    dsimp [sqScale] at *
    nlinarith
  have hlogdeg := Real.log_le_log (show 0 < (d n : ℝ) + 1 by positivity) hdeg
  rw [Real.log_mul (by linarith : δ + 2 ≠ 0)
    (pow_ne_zero 2 hnpos.ne'), Real.log_pow] at hlogdeg
  norm_num at hlogdeg
  have hln := Real.log_le_self hnpos.le
  have hlc : Real.log (δ + 2) ≤ Real.log (δ + 2) * (n : ℝ) := by
    nlinarith
  have hmid : Real.log ((d n : ℝ) + 1) ≤ C * (2 * (n : ℝ) + 1) := by
    dsimp [C]
    nlinarith
  simpa only [zero_add] using hmid.trans hlin

structure LongCapHypotheses (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) : Prop where
  sigma_pos : 0 < σ
  delta_pos : 0 < δ
  height_nonneg : 0 ≤ h
  degree_upper : QuadUpper (fun n => (pairWidth U V n : ℝ)) δ
  height_upper : QuadUpper (fun n => Real.log (maxPairHeight U V n)) h
  nonzero : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, polynomialRemainder U V F x n ≠ 0
  remainder_rate : ∀ x : ℝ, 1 < x →
    QuadLogRate (polynomialRemainder U V F x) (-σ * Real.log x)

/-- Exact max-height to l1-height transfer, using the degree hypothesis. -/
theorem LongCapHypotheses.toShort (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : LongCapHypotheses U V F σ δ h) :
    CapHypotheses U V F σ δ h := by
  refine ⟨H.sigma_pos, H.delta_pos, H.height_nonneg, H.degree_upper,
    ?_, H.nonzero, H.remainder_rate⟩
  have hW := log_width_plus_one_rate (pairWidth U V) δ H.delta_pos H.degree_upper
  have hsum := hW.add H.height_upper
  intro ε hε
  filter_upwards [hsum ε hε] with n hn
  simpa only [zero_add] using (log_pairHeight_le U V n).trans hn

lemma sqScale_pos_of_one_le {n : ℕ} (hn : 1 ≤ n) : 0 < sqScale n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact sq_pos_of_pos hnR

/-- Explicit correspondence with the paper's normalised little-o notation. -/
lemma normalized_tendsto_of_littleO (f : ℕ → ℝ) (a : ℝ)
    (hf : (fun n => f n - a * sqScale n) =o[atTop] sqScale) :
    Tendsto (fun n => f n / sqScale n) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((littleO_bound _ hf (ε / 2) (half_pos hε)).and (eventually_ge_atTop (1 : ℕ)))
  refine ⟨N, ?_⟩
  intro n hn
  have hs := sqScale_pos_of_one_le (hN n hn).2
  have hid : f n / sqScale n - a = (f n - a * sqScale n) / sqScale n := by
    field_simp [hs.ne']
  rw [Real.dist_eq, hid, abs_div, abs_of_pos hs]
  have hb : |f n - a * sqScale n| / sqScale n ≤ ε / 2 :=
    (div_le_iff₀ hs).mpr (hN n hn).1
  exact hb.trans_lt (by linarith)

lemma littleO_of_normalized_tendsto (f : ℕ → ℝ) (a : ℝ)
    (hf : Tendsto (fun n => f n / sqScale n) atTop (𝓝 a)) :
    (fun n => f n - a * sqScale n) =o[atTop] sqScale := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have he := (Metric.tendsto_nhds.mp hf) ε hε
  filter_upwards [he, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hs := sqScale_pos_of_one_le hn1
  have hid : f n - a * sqScale n = (f n / sqScale n - a) * sqScale n := by
    field_simp [hs.ne']
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hs, hid, abs_mul, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_right (by simpa only [Real.dist_eq] using hn.le) hs.le

lemma quadUpper_of_normalized_tendsto (f : ℕ → ℝ) (a : ℝ)
    (hf : Tendsto (fun n => f n / sqScale n) atTop (𝓝 a)) : QuadUpper f a := by
  exact quadUpper_of_littleO_upper f (fun n => f n - a * sqScale n) a
    (littleO_of_normalized_tendsto f a hf) (Eventually.of_forall (fun n => le_of_eq (by ring)))

lemma cleared_log_identity (d : ℕ → ℕ) (L : ℕ → ℝ) (b : ℝ) (hb : 0 < b)
    (hne : ∀ᶠ n in atTop, L n ≠ 0) :
    ∀ᶠ n in atTop, Real.log |b ^ d n * L n| =
      (d n : ℝ) * Real.log b + Real.log |L n| := by
  filter_upwards [hne] with n hn
  rw [abs_mul, abs_of_pos (pow_pos hb _),
    Real.log_mul (pow_ne_zero _ hb.ne') (abs_pos.mpr hn).ne', Real.log_pow]

/-- A real limsup bound, with its lower-boundedness obligation proved rather
than relying on the arbitrary totalisation of sInf on an unbounded set. -/
lemma limsup_normalized_le (f : ℕ → ℝ) (a : ℝ) (hf : QuadUpper f a)
    (hl : ∃ c : ℝ, ∀ᶠ n in atTop, c ≤ f n / sqScale n) :
    Filter.limsup (fun n => f n / sqScale n) atTop ≤ a := by
  obtain ⟨c, hc⟩ := hl
  have hbelow : BddBelow {z : ℝ | ∀ᶠ n in atTop, f n / sqScale n ≤ z} := by
    refine ⟨c, ?_⟩
    intro z hz
    obtain ⟨n, hn, hm⟩ := (hc.and hz).exists
    exact hn.trans hm
  have hbound : ∀ ε : ℝ, 0 < ε →
      Filter.limsup (fun n => f n / sqScale n) atTop ≤ a + ε := by
    intro ε hε
    rw [Filter.limsup_eq]
    apply csInf_le hbelow
    filter_upwards [hf ε hε, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    exact (div_le_iff₀ (sqScale_pos_of_one_le hn1)).mpr hn
  by_contra hh
  have hpos : 0 < (Filter.limsup (fun n => f n / sqScale n) atTop - a) / 2 := by
    linarith
  have hh' := hbound _ hpos
  linarith

/-- The full normalised limsup clause for the long note. -/
theorem long_cap_limsup (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : LongCapHypotheses U V F σ δ h)
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) :
    Filter.limsup (fun n =>
      Real.log |(b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop ≤
      δ * Real.log b - σ * Real.log ((a : ℝ) / b) := by
  let L := polynomialRemainder U V F ((a : ℝ) / b)
  let ρ : ℝ := -σ * Real.log ((a : ℝ) / b)
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := zero_lt_one.trans_le hbR
  have hx : (1 : ℝ) < (a : ℝ) / b :=
    (one_lt_div hbpos).mpr (by exact_mod_cast hab)
  have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hbR
  have hr : QuadLogRate L ρ := H.remainder_rate _ hx
  have hi := cleared_log_identity (pairWidth U V) L b hbpos (H.nonzero _ hx)
  have hu := (H.degree_upper.const_mul hlog).add hr.upper
  have hu' : QuadUpper (fun n => Real.log |(b : ℝ) ^ pairWidth U V n * L n|)
      (δ * Real.log b + ρ) := by
    intro ε hε
    filter_upwards [hu ε hε, hi] with n hn hid
    rw [hid]
    simpa only [mul_comm (Real.log (b : ℝ))] using hn
  have hlo : ∃ c : ℝ, ∀ᶠ n in atTop,
      c ≤ Real.log |(b : ℝ) ^ pairWidth U V n * L n| / sqScale n := by
    refine ⟨ρ - 1, ?_⟩
    filter_upwards [littleO_bound _ hr 1 (by norm_num), hi,
      eventually_ge_atTop (1 : ℕ)] with n hn hid hn1
    rw [hid]
    apply (le_div_iff₀ (sqScale_pos_of_one_le hn1)).mpr
    have hh := (abs_le.mp hn).1
    have hd : 0 ≤ (pairWidth U V n : ℝ) * Real.log (b : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) hlog
    nlinarith
  have hh := limsup_normalized_le _ _ hu' hlo
  simpa only [L, ρ, sub_eq_add_neg, neg_mul] using hh

/-- The actual limiting degree cannot be smaller than sigma. -/
theorem actual_degree_ge_sigma (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h d : ℝ) (H : LongCapHypotheses U V F σ δ h)
    (hd : Tendsto (fun n => (pairWidth U V n : ℝ) / sqScale n) atTop (𝓝 d)) :
    σ ≤ d := by
  have hd0 : 0 ≤ d := by
    by_contra hh
    have hdp : 0 < -d / 2 := by linarith
    obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.mp hd) (-d / 2) hdp).exists
    have hnonneg : 0 ≤ (pairWidth U V n : ℝ) / sqScale n :=
      div_nonneg (Nat.cast_nonneg _) (sqScale_nonneg n)
    rw [Real.dist_eq] at hn
    have hh' := (abs_lt.mp hn).2
    linarith
  have hdu := quadUpper_of_normalized_tendsto _ d hd
  by_contra hh
  let δ' : ℝ := (σ + d) / 2
  have hd' : 0 < δ' := by dsimp [δ']; linarith [H.sigma_pos]
  have hdd' : d ≤ δ' := by dsimp [δ']; linarith
  let H' : LongCapHypotheses U V F σ δ' h :=
    ⟨H.sigma_pos, hd', H.height_nonneg, hdu.mono hdd', H.height_upper,
      H.nonzero, H.remainder_rate⟩
  have hc := sigma_le_delta U V F σ δ' h (LongCapHypotheses.toShort U V F σ δ' h H')
  dsimp [δ'] at hc
  linarith

/-- The actual-degree normalised logarithmic limit is an identity plus two limits. -/
theorem actual_degree_log_limit (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h d : ℝ) (H : LongCapHypotheses U V F σ δ h)
    (hd : Tendsto (fun n => (pairWidth U V n : ℝ) / sqScale n) atTop (𝓝 d))
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) :
    Tendsto (fun n => Real.log |(b : ℝ) ^ pairWidth U V n *
      polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop
      (𝓝 (d * Real.log b - σ * Real.log ((a : ℝ) / b))) := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := zero_lt_one.trans_le hbR
  have hx : (1 : ℝ) < (a : ℝ) / b :=
    (one_lt_div hbpos).mpr (by exact_mod_cast hab)
  have hL := normalized_tendsto_of_littleO _ _ (H.remainder_rate _ hx)
  have hsum := (hd.mul (tendsto_const_nhds (x := Real.log (b : ℝ)))).add hL
  have hid := cleared_log_identity (pairWidth U V)
    (polynomialRemainder U V F ((a : ℝ) / b)) b hbpos (H.nonzero _ hx)
  apply Filter.Tendsto.congr' _ (show Tendsto
    (fun n => (pairWidth U V n : ℝ) / sqScale n * Real.log b +
      Real.log |polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n)
      atTop (𝓝 (d * Real.log b - σ * Real.log ((a : ℝ) / b))) from
        by simpa only [sub_eq_add_neg, neg_mul] using hsum)
  filter_upwards [hid] with n hn
  rw [hn, add_div]
  ring

lemma abs_tendsto_atTop_of_positive_log_rate (f : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hne : ∀ᶠ n in atTop, f n ≠ 0) (hf : QuadLogRate f c) :
    Tendsto (fun n => |f n|) atTop atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hf.exp_lower hne (c / 2) (half_pos hc))
  apply Filter.tendsto_atTop_atTop.2
  intro b
  by_cases hb : b ≤ 0
  · exact ⟨0, fun n _ => hb.trans (abs_nonneg _)⟩
  · have hbpos : 0 < b := lt_of_not_ge hb
    obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (2 * Real.log b / c))
    refine ⟨max N M, ?_⟩
    intro n hn
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hnM : M ≤ n := (le_max_right _ _).trans hn
    have hnR : (M : ℝ) ≤ n := by exact_mod_cast hnM
    have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans (hM.le.trans hnR)
    have hnc : 2 * Real.log b / c < (n : ℝ) :=
      (le_max_right _ _).trans_lt (hM.trans_le hnR)
    have hm := (div_lt_iff₀ hc).mp hnc
    have hs : (n : ℝ) ≤ sqScale n := by dsimp [sqScale]; nlinarith
    have hcs := mul_le_mul_of_nonneg_left hs hc.le
    have he : Real.log b ≤ (c - c / 2) * sqScale n := by nlinarith
    calc
      b = Real.exp (Real.log b) := (Real.exp_log hbpos).symm
      _ ≤ Real.exp ((c - c / 2) * sqScale n) := Real.exp_le_exp.mpr he
      _ ≤ |f n| := hN n hnN

/-- Both sides of the exact-degree cutoff. Boundary equality is not classified. -/
theorem actual_degree_decay_or_divergence (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h d : ℝ) (H : LongCapHypotheses U V F σ δ h)
    (hd : Tendsto (fun n => (pairWidth U V n : ℝ) / sqScale n) atTop (𝓝 d))
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) :
    let f := fun n => (b : ℝ) ^ pairWidth U V n *
      polynomialRemainder U V F ((a : ℝ) / b) n
    let c := d * Real.log b - σ * Real.log ((a : ℝ) / b)
    (c < 0 → Tendsto f atTop (𝓝 0)) ∧
    (0 < c → Tendsto (fun n => |f n|) atTop atTop) := by
  dsimp only
  let f := fun n => (b : ℝ) ^ pairWidth U V n *
    polynomialRemainder U V F ((a : ℝ) / b) n
  let c := d * Real.log b - σ * Real.log ((a : ℝ) / b)
  have hlim := actual_degree_log_limit U V F σ δ h d H hd a b hb hab
  have hr : QuadLogRate f c := littleO_of_normalized_tendsto _ _ hlim
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := zero_lt_one.trans_le hbR
  have hx : (1 : ℝ) < (a : ℝ) / b :=
    (one_lt_div hbpos).mpr (by exact_mod_cast hab)
  have hne : ∀ᶠ n in atTop, f n ≠ 0 := by
    filter_upwards [H.nonzero _ hx] with n hn
    exact mul_ne_zero (pow_ne_zero _ hbpos.ne') hn
  exact ⟨fun hc => hr.exp_upper.tendsto_zero hc,
    fun hc => abs_tendsto_atTop_of_positive_log_rate f c hc hne hr⟩


lemma logarithmic_balance_factorisation (a b σ d : ℝ)
    (ha : 1 < a) (hb : 0 < b) (hden : σ + d ≠ 0) :
    d * Real.log b - σ * Real.log (a / b) =
      ((σ + d) * Real.log a) * (Real.log b / Real.log a - σ / (σ + d)) := by
  have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
  have hlog : Real.log a ≠ 0 := (Real.log_pos ha).ne'
  rw [Real.log_div ha0 hb.ne']
  field_simp [hlog, hden]
  ring

/-- The paper's strict logarithmic threshold, on BOTH sides, for the actual degree. -/
theorem actual_degree_threshold (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h d : ℝ) (H : LongCapHypotheses U V F σ δ h)
    (hd : Tendsto (fun n => (pairWidth U V n : ℝ) / sqScale n) atTop (𝓝 d))
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) :
    (Real.log b / Real.log a < σ / (σ + d) →
      Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)) ∧
    (σ / (σ + d) < Real.log b / Real.log a →
      Tendsto (fun n => |(b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n|) atTop atTop) := by
  have hσd := actual_degree_ge_sigma U V F σ δ h d H hd
  have hdpos : 0 < d := H.sigma_pos.trans_le hσd
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := zero_lt_one.trans_le hbR
  have haR : (1 : ℝ) < a := hbR.trans_lt (by exact_mod_cast hab)
  have hsd : 0 < σ + d := add_pos H.sigma_pos hdpos
  have hp : 0 < (σ + d) * Real.log (a : ℝ) := mul_pos hsd (Real.log_pos haR)
  have hf := logarithmic_balance_factorisation a b σ d haR hbpos hsd.ne'
  have hboth := actual_degree_decay_or_divergence U V F σ δ h d H hd a b hb hab
  constructor
  · intro hr
    apply hboth.1
    rw [hf]
    exact mul_neg_of_pos_of_neg hp (sub_neg.mpr hr)
  · intro hr
    apply hboth.2
    rw [hf]
    exact mul_pos hp (sub_pos.mpr hr)

/-- At 3/2 the exact-degree forms actually diverge in absolute value. -/
theorem actual_degree_three_halves_diverges
    (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h d : ℝ) (H : LongCapHypotheses U V F σ δ h)
    (hd : Tendsto (fun n => (pairWidth U V n : ℝ) / sqScale n) atTop (𝓝 d)) :
    Tendsto (fun n => |(2 : ℝ) ^ pairWidth U V n *
      polynomialRemainder U V F ((3 : ℝ) / 2) n|) atTop atTop := by
  have hσd := actual_degree_ge_sigma U V F σ δ h d H hd
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hld : Real.log ((3 : ℝ) / 2) < Real.log 2 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hg := mul_le_mul_of_nonneg_right hσd hl2.le
  have hpos : 0 < d * Real.log 2 - σ * Real.log ((3 : ℝ) / 2) := by
    nlinarith [H.sigma_pos]
  exact (actual_degree_decay_or_divergence U V F σ δ h d H hd 3 2
    (by norm_num) (by norm_num)).2 hpos

/-- Full long-record aggregate. The maximum-height, limsup, exact-degree limit,
strict-threshold and 3/2 divergence clauses are not silently dropped. -/
theorem long_record_archcap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : LongCapHypotheses U V F σ δ h) :
    σ ≤ δ ∧ σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    (∀ a b : ℕ, 1 ≤ b → b < a →
      Filter.limsup (fun n => Real.log |(b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop ≤
        δ * Real.log b - σ * Real.log ((a : ℝ) / b)) ∧
    (∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
        Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
          polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)) ∧
    (∀ d : ℝ,
      Tendsto (fun n => (pairWidth U V n : ℝ) / sqScale n) atTop (𝓝 d) →
        σ ≤ d ∧
        (∀ a b : ℕ, 1 ≤ b → b < a →
          Tendsto (fun n => Real.log |(b : ℝ) ^ pairWidth U V n *
            polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop
            (𝓝 (d * Real.log b - σ * Real.log ((a : ℝ) / b)))) ∧
        (∀ a b : ℕ, 1 ≤ b → b < a →
          (Real.log b / Real.log a < σ / (σ + d) →
            Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
              polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)) ∧
          (σ / (σ + d) < Real.log b / Real.log a →
            Tendsto (fun n => |(b : ℝ) ^ pairWidth U V n *
              polynomialRemainder U V F ((a : ℝ) / b) n|) atTop atTop)) ∧
        Tendsto (fun n => |(2 : ℝ) ^ pairWidth U V n *
          polynomialRemainder U V F ((3 : ℝ) / 2) n|) atTop atTop) := by
  have HS := LongCapHypotheses.toShort U V F σ δ h H
  have hshort := short_note_archimedean_cap U V F σ δ h HS
  refine ⟨sigma_le_delta U V F σ δ h HS, hshort.1,
    (fun a b hb hab => long_cap_limsup U V F σ δ h H a b hb hab), hshort.2, ?_⟩
  intro d hd
  exact ⟨actual_degree_ge_sigma U V F σ δ h d H hd,
    (fun a b hb hab => actual_degree_log_limit U V F σ δ h d H hd a b hb hab),
    (fun a b hb hab => actual_degree_threshold U V F σ δ h d H hd a b hb hab),
    actual_degree_three_halves_diverges U V F σ δ h d H hd⟩

end ErdosProblems.Erdos1049.PaperR9
