import ErdosProblems.Erdos1049.PaperR16.RadialGauge

/-!
# Primitive-root radial limits from the literal series

Candidate source; new Lean checks UNRUN. A finite explicit phase bound replaces
an appeal to an unspecified compactness constant. The case of order one is
included: every remainder summand is then zero.
-/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace ErdosProblems.Erdos1049.PaperR16

/-- A finite, root-dependent constant. The zero phase contributes zero. -/
def phaseBound (d : ℕ) (ζ : ℂ) : ℝ :=
  ∑ a ∈ Finset.range d, 2 / ‖1 - ζ ^ a‖

lemma phaseBound_nonneg (d : ℕ) (ζ : ℂ) : 0 ≤ phaseBound d ζ := by
  unfold phaseBound
  exact Finset.sum_nonneg (fun _ _ => div_nonneg (by norm_num) (norm_nonneg _))

lemma root_pow_mod (ζ : ℂ) (d n : ℕ) (hζ : ζ ^ d = 1) :
    ζ ^ n = ζ ^ (n % d) := by
  calc
    ζ ^ n = ζ ^ (n % d + d * (n / d)) := by rw [Nat.mod_add_div]
    _ = ζ ^ (n % d) := by rw [pow_add, pow_mul, hζ, one_pow, mul_one]

/-- `|1-u| ≤ 2 |1-xu|` for a unit phase and `0≤x≤1`. -/
lemma phase_inverse_bound (u : ℂ) (hu : ‖u‖ = 1) (hne : u ≠ 1)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 / ‖1 - (x : ℂ) * u‖ ≤ 2 / ‖1 - u‖ := by
  have ha : 0 < ‖1 - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hxu : ‖(x : ℂ) * u‖ = x := by
    simp [norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have hrev : 1 - x ≤ ‖1 - (x : ℂ) * u‖ := by
    simpa only [norm_one, hxu] using norm_sub_norm_le (1 : ℂ) ((x : ℂ) * u)
  have hdist : ‖(x : ℂ) * u - u‖ = 1 - x := by
    have he : (x : ℂ) * u - u = ((x - 1 : ℝ) : ℂ) * u := by push_cast; ring
    rw [he, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hx1)]
    ring
  have htri : ‖1 - u‖ ≤ ‖1 - (x : ℂ) * u‖ + (1 - x) := by
    calc
      ‖1 - u‖ = ‖(1 - (x : ℂ) * u) + ((x : ℂ) * u - u)‖ := by
        congr 1
        ring
      _ ≤ ‖1 - (x : ℂ) * u‖ + ‖(x : ℂ) * u - u‖ := norm_add_le _ _
      _ = ‖1 - (x : ℂ) * u‖ + (1 - x) := by rw [hdist]
  have hd : 0 < ‖1 - (x : ℂ) * u‖ := by linarith
  apply (div_le_div_iff₀ hd ha).2
  nlinarith

def radialRemainderTerm (d : ℕ) (ζ : ℂ) (r : ℝ) (n : ℕ) : ℂ :=
  if d ∣ n then 0 else lambertTerm ((r : ℂ) * ζ) n

lemma norm_radialRemainderTerm_le (d : ℕ) (hd : 0 < d)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (r : ℝ) (hr : 0 < r ∧ r < 1) (n : ℕ) :
    ‖radialRemainderTerm d ζ r n‖ ≤ phaseBound d ζ * r ^ n := by
  by_cases hdiv : d ∣ n
  · simp only [radialRemainderTerm, if_pos hdiv, norm_zero]
    exact mul_nonneg (phaseBound_nonneg d ζ) (pow_nonneg hr.1.le n)
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (Nat.ne_of_gt hd)
  have hphase : ζ ^ n ≠ 1 := fun he => hdiv ((hζ.pow_eq_one_iff_dvd n).1 he)
  have hphase_norm : ‖ζ ^ n‖ = 1 := by simp [norm_pow, hnorm]
  have hi := phase_inverse_bound (ζ ^ n) hphase_norm hphase (r ^ n)
    (pow_nonneg hr.1.le n) (unit_pow_le_one hr.1.le hr.2.le n)
  have hc : 2 / ‖1 - ζ ^ n‖ ≤ phaseBound d ζ := by
    rw [root_pow_mod ζ d n hζ.pow_eq_one]
    unfold phaseBound
    exact Finset.single_le_sum
      (f := fun a => 2 / ‖1 - ζ ^ a‖)
      (fun a _ => div_nonneg (by norm_num) (norm_nonneg _))
      (Finset.mem_range.mpr (Nat.mod_lt n hd))
  have ht : ‖lambertTerm ((r : ℂ) * ζ) n‖ =
      r ^ n / ‖1 - ((r ^ n : ℝ) : ℂ) * ζ ^ n‖ := by
    simp [lambertTerm, mul_pow, norm_div, norm_mul, norm_pow, hnorm,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
  simp only [radialRemainderTerm, if_neg hdiv]
  rw [ht, div_eq_mul_inv]
  rw [one_div] at hi
  calc
    r ^ n * ‖1 - ((r ^ n : ℝ) : ℂ) * ζ ^ n‖⁻¹ ≤ r ^ n * phaseBound d ζ :=
      mul_le_mul_of_nonneg_left (hi.trans hc) (pow_nonneg hr.1.le n)
    _ = phaseBound d ζ * r ^ n := mul_comm _ _

/-- Exact splitting into multiples of the root order, with a summable remainder. -/
theorem lambert_root_remainder_bound (d : ℕ) (hd : 0 < d)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) (r : ℝ) (hr : 0 < r ∧ r < 1) :
    ‖lambert ((r : ℂ) * ζ) - lambert ((r ^ d : ℝ) : ℂ)‖ ≤
      phaseBound d ζ / (1 - r) := by
  let M : ℕ → ℂ := fun n => if d ∣ n then lambertTerm ((r : ℂ) * ζ) n else 0
  let R : ℕ → ℂ := radialRemainderTerm d ζ r
  have hmajor : Summable (fun n : ℕ => phaseBound d ζ * r ^ n) :=
    (summable_geometric_of_lt_one hr.1.le hr.2).mul_left _
  have hRnorm : Summable (fun n : ℕ => ‖R n‖) := by
    refine Summable.of_norm_bounded hmajor ?_
    intro n
    simpa only [norm_norm] using norm_radialRemainderTerm_le d hd ζ hζ r hr n
  have hR : Summable R := hRnorm.of_norm
  have hrpow := unit_power_mem hr hd
  have hpownorm : ‖((r ^ d : ℝ) : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1, abs_of_pos hrpow.1]
      using hrpow.2
  have harg : ((r : ℂ) * ζ) ^ d = ((r ^ d : ℝ) : ℂ) := by
    simp [mul_pow, hζ.pow_eq_one]
  have hinj : Function.Injective (fun n : ℕ => d * n) := by
    intro a b hab
    exact mul_left_cancel₀ (Nat.ne_of_gt hd) hab
  have hoff : ∀ n ∉ Set.range (fun j : ℕ => d * j), M n = 0 := by
    intro n hn
    dsimp [M]
    split_ifs with hdiv
    · obtain ⟨j, hj⟩ := hdiv
      exact False.elim (hn ⟨j, hj.symm⟩)
    · rfl
  have hM : HasSum M (lambert ((r ^ d : ℝ) : ℂ)) := by
    apply (hinj.hasSum_iff hoff).1
    apply (lambert_summable ((r ^ d : ℝ) : ℂ) hpownorm).hasSum.congr_fun
    intro n
    simp [Function.comp_apply, M, lambertTerm, pow_mul, harg]
  have hsplit : lambert ((r : ℂ) * ζ) =
      lambert ((r ^ d : ℝ) : ℂ) + ∑' n : ℕ, R n := by
    have hs : HasSum (lambertTerm ((r : ℂ) * ζ))
        (lambert ((r ^ d : ℝ) : ℂ) + ∑' n : ℕ, R n) := by
      apply (hM.add hR.hasSum).congr_fun
      intro n
      by_cases hn : d ∣ n <;> simp [M, R, radialRemainderTerm, hn]
    exact hs.tsum_eq
  rw [hsplit, add_sub_cancel_left]
  calc
    ‖∑' n : ℕ, R n‖ ≤ ∑' n : ℕ, ‖R n‖ := norm_tsum_le_tsum_norm hRnorm
    _ ≤ ∑' n : ℕ, phaseBound d ζ * r ^ n :=
      hRnorm.tsum_le_tsum
        (fun n => norm_radialRemainderTerm_le d hd ζ hζ r hr n) hmajor
    _ = phaseBound d ζ / (1 - r) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr.1.le hr.2, div_eq_mul_inv]

/-- The actual primitive-root radial limit. -/
theorem lambert_primitive_radial (d : ℕ) (hd : 0 < d)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ d) :
    Tendsto (fun r : ℝ => (radialGauge r : ℂ) * lambert ((r : ℂ) * ζ))
      radial (𝓝 ((d : ℂ)⁻¹)) := by
  have hE := radialGauge_mul_remainder_tendsto_zero
    (fun r : ℝ => lambert ((r : ℂ) * ζ) - lambert ((r ^ d : ℝ) : ℂ))
    (phaseBound d ζ) (by
      filter_upwards [radial_eventually_unit] with r hr
      exact lambert_root_remainder_bound d hd ζ hζ r hr)
  have hfactor : Tendsto
      (fun r : ℝ => ((radialGauge r / radialGauge (r ^ d) : ℝ) : ℂ))
      radial (𝓝 ((d : ℂ)⁻¹)) := by
    have h := (Complex.continuous_ofReal.tendsto ((d : ℝ)⁻¹)).comp
      (radialGauge_div_pow_tendsto d hd)
    simpa only [Function.comp_apply, Complex.ofReal_inv, Complex.ofReal_natCast] using h
  have hbase := lambert_complex_radial_at_one.comp (power_tendsto_radial d hd)
  have he : (fun r : ℝ => (radialGauge r : ℂ) * lambert ((r : ℂ) * ζ)) =ᶠ[radial]
      (fun r : ℝ => ((radialGauge r / radialGauge (r ^ d) : ℝ) : ℂ) *
        ((radialGauge (r ^ d) : ℂ) * lambert ((r ^ d : ℝ) : ℂ)) +
        (radialGauge r : ℂ) *
          (lambert ((r : ℂ) * ζ) - lambert ((r ^ d : ℝ) : ℂ))) := by
    filter_upwards [radial_eventually_unit] with r hr
    have hn : (radialGauge (r ^ d) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (radialGauge_pos (unit_power_mem hr hd)))
    push_cast
    field_simp [hn] <;> ring
  apply (tendsto_congr' he).2
  simpa only [Function.comp_apply, mul_one, add_zero] using (hfactor.mul hbase).add hE

/-- Composition with `z ↦ z^m`, with the indispensable factor `1/m`. -/
theorem lambert_primitive_power_radial (m d : ℕ) (hm : 0 < m) (hd : 0 < d)
    (ζ : ℂ) (hζ : IsPrimitiveRoot (ζ ^ m) d) :
    Tendsto (fun r : ℝ => (radialGauge r : ℂ) * lambert (((r : ℂ) * ζ) ^ m))
      radial (𝓝 ((m : ℂ)⁻¹ * (d : ℂ)⁻¹)) := by
  have hfactor : Tendsto
      (fun r : ℝ => ((radialGauge r / radialGauge (r ^ m) : ℝ) : ℂ))
      radial (𝓝 ((m : ℂ)⁻¹)) := by
    have h := (Complex.continuous_ofReal.tendsto ((m : ℝ)⁻¹)).comp
      (radialGauge_div_pow_tendsto m hm)
    simpa only [Function.comp_apply, Complex.ofReal_inv, Complex.ofReal_natCast] using h
  have hbase := (lambert_primitive_radial d hd (ζ ^ m) hζ).comp
    (power_tendsto_radial m hm)
  have he :
      (fun r : ℝ => (radialGauge r : ℂ) * lambert (((r : ℂ) * ζ) ^ m)) =ᶠ[radial]
      (fun r : ℝ => ((radialGauge r / radialGauge (r ^ m) : ℝ) : ℂ) *
        ((radialGauge (r ^ m) : ℂ) * lambert (((r ^ m : ℝ) : ℂ) * ζ ^ m))) := by
    filter_upwards [radial_eventually_unit] with r hr
    have hn : (radialGauge (r ^ m) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (radialGauge_pos (unit_power_mem hr hm)))
    simp only [mul_pow, ← Complex.ofReal_pow, Complex.ofReal_div]
    field_simp [hn] <;> ring
  exact (tendsto_congr' he).2 (hfactor.mul hbase)

end ErdosProblems.Erdos1049.PaperR16
