import Mathlib

/-!
# Erdős 1041, `res:one-root-gamma-false`: the plane encircling bound

This is the geometric input `hperim : PlanePerimeterBound` of
`Lobe.one_root_gamma_false` (`LobeAndArity.lean`): if a bounded set `A ⊆ ℂ`
contains the closed disc `closedBall x ρ`, then the one-dimensional Hausdorff
measure of `frontier A` is at least `2πρ`.  `plane_perimeter_bound` states the
body of the `def` `Lobe.PlanePerimeterBound` with its quantifiers as binders;
this file imports only Mathlib, and `LobeUnconditional.lean` packages it as a
term of that `def`.

The proof has two steps.

* **The circle has `μH[1]` at least `2πρ`.**  Cut the circle
  `θ ↦ x + ρ e^{iθ}` into `N` half-open arcs of angle `2π/N`.  Each closed arc
  is connected and its endpoints are `2ρ sin(π/N)` apart, so the `1`-Lipschitz
  map `z ↦ dist a z` from one endpoint `a` sends it onto a set containing an
  interval of that length; `μH[1]` on `ℝ` is Lebesgue measure.  Dropping the
  other endpoint costs nothing (`μH[1]` has no atoms).  The half-open arcs are
  disjoint and Borel (Lusin–Souslin), so `μH[1](circle) ≥ 2Nρ sin(π/N)`, which
  is at least `2πρ - π³ρ/(2N²)` because `sin t > t - t³/4` on `(0, 1]`.  Let
  `N → ∞`.
* **A `1`-Lipschitz map carries part of the frontier onto the circle.**  The
  radial retraction `z ↦ x + ρ (z - x)/‖z - x‖` is `1`-Lipschitz on
  `{z : ρ ≤ ‖z - x‖}`: with `a = z - x`, `b = w - x` and `λ = ρ²/(‖a‖‖b‖) ≤ 1`,
  `‖a - b‖² - ‖ρa/‖a‖ - ρb/‖b‖‖² = (‖a‖ - ‖b‖)² + 2(1 - λ)(‖a‖‖b‖ - ⟪a, b⟫) ≥ 0`.
  Every point `s` of the circle is the image of a point of `frontier A` on the
  outward ray through `s`: that ray is connected, starts at `s ∈ A` and leaves
  the bounded set `closure A`, so it meets `frontier A`, at distance at least
  `ρ` from `x`.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21.Lobe

open MeasureTheory Metric Set
open scoped Real ENNReal

/-! ### Length of a connected set and of a circular arc -/

/-- A preconnected set containing `a` and `b` has one-dimensional Hausdorff measure at least
`dist a b`: the `1`-Lipschitz map `z ↦ dist a z` sends it onto a set containing
`[0, dist a b]`, and `μH[1]` on `ℝ` is Lebesgue measure. -/
theorem ofReal_dist_le_hausdorffMeasure {K : Set ℂ} (hK : IsPreconnected K) {a b : ℂ}
    (ha : a ∈ K) (hb : b ∈ K) :
    ENNReal.ofReal (dist a b) ≤ Measure.hausdorffMeasure 1 K := by
  have hf : LipschitzWith 1 (dist a) := LipschitzWith.dist_right a
  have hsub : Icc 0 (dist a b) ⊆ dist a '' K :=
    (hK.image _ hf.continuous.continuousOn).Icc_subset ⟨a, ha, dist_self a⟩ ⟨b, hb, rfl⟩
  calc ENNReal.ofReal (dist a b) = Measure.hausdorffMeasure 1 (Icc 0 (dist a b)) := by
        rw [hausdorffMeasure_real, Real.volume_Icc, sub_zero]
    _ ≤ Measure.hausdorffMeasure 1 (dist a '' K) := measure_mono hsub
    _ ≤ Measure.hausdorffMeasure 1 K := by
        simpa using hf.hausdorffMeasure_image_le (d := 1) zero_le_one K

/-- The chord of the circle `θ ↦ x + ρ e^{iθ}` between the parameters `a` and `b`. -/
theorem dist_circleMap_circleMap (x : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (a b : ℝ) :
    dist (circleMap x ρ a) (circleMap x ρ b) = ρ * ‖2 * Real.sin ((b - a) / 2)‖ := by
  have hexp : Complex.exp (b * Complex.I)
      = Complex.exp (a * Complex.I) * Complex.exp (Complex.I * ((b - a : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hdiff : circleMap x ρ b - circleMap x ρ a
      = (ρ : ℂ) * Complex.exp (a * Complex.I)
        * (Complex.exp (Complex.I * ((b - a : ℝ) : ℂ)) - 1) := by
    simp only [circleMap]
    rw [hexp]
    ring
  rw [dist_comm, dist_eq_norm, hdiff, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Complex.norm_of_nonneg hρ, mul_one]

/-- A half-open arc of the circle of angle `b - a ∈ [0, 2π]` has `μH[1]` at least its chord
`2ρ sin((b - a)/2)`. -/
theorem chord_le_hausdorffMeasure_arc (x : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {a b : ℝ} (hab : a ≤ b)
    (hba : b - a ≤ 2 * π) :
    ENNReal.ofReal (ρ * (2 * Real.sin ((b - a) / 2)))
      ≤ Measure.hausdorffMeasure 1 (circleMap x ρ '' Ico a b) := by
  haveI := Measure.noAtoms_hausdorff ℂ one_pos
  have hsin : 0 ≤ Real.sin ((b - a) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hconn : IsPreconnected (circleMap x ρ '' Icc a b) :=
    isPreconnected_Icc.image _ (continuous_circleMap x ρ).continuousOn
  have h1 := ofReal_dist_le_hausdorffMeasure hconn
    (mem_image_of_mem _ (left_mem_Icc.2 hab)) (mem_image_of_mem _ (right_mem_Icc.2 hab))
  rw [dist_circleMap_circleMap x hρ, Real.norm_of_nonneg (mul_nonneg zero_le_two hsin)] at h1
  have hsplit : circleMap x ρ '' Icc a b ⊆ circleMap x ρ '' Ico a b ∪ {circleMap x ρ b} := by
    rintro _ ⟨θ, hθ, rfl⟩
    rcases eq_or_lt_of_le hθ.2 with h | h
    · right
      rw [h]
      exact mem_singleton _
    · left
      exact mem_image_of_mem _ ⟨hθ.1, h⟩
  calc ENNReal.ofReal (ρ * (2 * Real.sin ((b - a) / 2)))
      ≤ Measure.hausdorffMeasure 1 (circleMap x ρ '' Icc a b) := h1
    _ ≤ Measure.hausdorffMeasure 1 (circleMap x ρ '' Ico a b ∪ {circleMap x ρ b}) :=
        measure_mono hsplit
    _ ≤ Measure.hausdorffMeasure 1 (circleMap x ρ '' Ico a b)
          + Measure.hausdorffMeasure 1 {circleMap x ρ b} := measure_union_le _ _
    _ = Measure.hausdorffMeasure 1 (circleMap x ρ '' Ico a b) := by
        rw [measure_singleton, add_zero]

/-- The `k`-th of the `N` half-open arcs of angle `2π/N` of the circle `sphere x ρ`. -/
def circleArc (x : ℂ) (ρ : ℝ) (N k : ℕ) : Set ℂ :=
  circleMap x ρ '' Ico ((k : ℝ) * (2 * π / N)) (((k : ℝ) + 1) * (2 * π / N))

/-- Cutting the circle into `N` equal half-open arcs: `μH[1] (sphere x ρ) ≥ 2Nρ sin(π/N)`. -/
theorem chords_le_hausdorffMeasure_sphere (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) :
    ENNReal.ofReal (N * (ρ * (2 * Real.sin (π / N))))
      ≤ Measure.hausdorffMeasure 1 (sphere x ρ) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hδpos : 0 < 2 * π / N := by positivity
  have hNδ : (N : ℝ) * (2 * π / N) = 2 * π := by field_simp
  have hinj : InjOn (circleMap x ρ) (Ico 0 (2 * π)) :=
    injOn_circleMap_of_abs_sub_le' hρ.ne' (by linarith)
  have hIsub : ∀ k ∈ Finset.range N,
      Ico ((k : ℝ) * (2 * π / N)) (((k : ℝ) + 1) * (2 * π / N)) ⊆ Ico 0 (2 * π) := by
    intro k hk θ hθ
    have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hk
    refine ⟨le_trans (by positivity) hθ.1, ?_⟩
    calc θ < ((k : ℝ) + 1) * (2 * π / N) := hθ.2
      _ ≤ N * (2 * π / N) := mul_le_mul_of_nonneg_right hkN hδpos.le
      _ = 2 * π := hNδ
  have hdisj : ((Finset.range N : Finset ℕ) : Set ℕ).PairwiseDisjoint (circleArc x ρ N) := by
    intro j hj k hk hjk
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨θ, hθ, rfl⟩ ⟨θ', hθ', hEq⟩
    have hθθ' : θ' = θ := hinj (hIsub k hk hθ') (hIsub j hj hθ) hEq
    rw [hθθ'] at hθ'
    rcases lt_or_gt_of_ne hjk with h | h
    · have h' : (j : ℝ) + 1 ≤ k := by exact_mod_cast Nat.lt_iff_add_one_le.1 h
      have := mul_le_mul_of_nonneg_right h' hδpos.le
      linarith [hθ.2, hθ'.1]
    · have h' : (k : ℝ) + 1 ≤ j := by exact_mod_cast Nat.lt_iff_add_one_le.1 h
      have := mul_le_mul_of_nonneg_right h' hδpos.le
      linarith [hθ.1, hθ'.2]
  have hmeas : ∀ k ∈ Finset.range N, MeasurableSet (circleArc x ρ N k) := fun k hk =>
    measurableSet_Ico.image_of_continuousOn_injOn (continuous_circleMap x ρ).continuousOn
      (hinj.mono (hIsub k hk))
  have hsub : (⋃ k ∈ Finset.range N, circleArc x ρ N k) ⊆ sphere x ρ := by
    refine iUnion₂_subset fun k _ => ?_
    rintro _ ⟨θ, -, rfl⟩
    exact circleMap_mem_sphere x hρ.le θ
  have harc : ∀ k ∈ Finset.range N,
      ENNReal.ofReal (ρ * (2 * Real.sin (π / N)))
        ≤ Measure.hausdorffMeasure 1 (circleArc x ρ N k) := by
    intro k _
    have hlen : ((k : ℝ) + 1) * (2 * π / N) - k * (2 * π / N) = 2 * π / N := by ring
    have h := chord_le_hausdorffMeasure_arc x hρ.le
      (a := (k : ℝ) * (2 * π / N)) (b := ((k : ℝ) + 1) * (2 * π / N))
      (mul_le_mul_of_nonneg_right (by linarith) hδpos.le)
      (by rw [hlen]; exact div_le_self (by positivity) (Nat.one_le_cast.2 hN))
    rw [hlen, show 2 * π / (N : ℝ) / 2 = π / N by ring] at h
    exact h
  calc ENNReal.ofReal (N * (ρ * (2 * Real.sin (π / N))))
      = ∑ k ∈ Finset.range N, ENNReal.ofReal (ρ * (2 * Real.sin (π / N))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
    _ ≤ ∑ k ∈ Finset.range N, Measure.hausdorffMeasure 1 (circleArc x ρ N k) :=
        Finset.sum_le_sum harc
    _ = Measure.hausdorffMeasure 1 (⋃ k ∈ Finset.range N, circleArc x ρ N k) :=
        (measure_biUnion_finset hdisj hmeas).symm
    _ ≤ Measure.hausdorffMeasure 1 (sphere x ρ) := measure_mono hsub

/-- **The circumference bound**: `μH[1] (sphere x ρ) ≥ 2πρ`. -/
theorem two_pi_mul_le_hausdorffMeasure_sphere (x : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (2 * π * ρ) ≤ Measure.hausdorffMeasure 1 (sphere x ρ) := by
  rcases eq_or_lt_of_le hρ with rfl | hρ
  · simp
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 4 (π ^ 3 * ρ / ε))
  have hN4 : (4 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNε : π ^ 3 * ρ / ε < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hchord := chords_le_hausdorffMeasure_sphere x hρ (N := N) (by exact_mod_cast hNpos)
  have hx0 : 0 < π / N := by positivity
  have hx1 : π / N ≤ 1 := by
    rw [div_le_one₀ hNpos]
    linarith [Real.pi_le_four]
  have hsin := Real.sin_gt_sub_cube hx0 hx1
  have hsin0 : 0 ≤ Real.sin (π / N) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0.le (div_le_self Real.pi_pos.le (by linarith))
  have hcube : (N : ℝ) * (ρ * (2 * (π / N - (π / N) ^ 3 / 4)))
      = 2 * π * ρ - π ^ 3 * ρ / (2 * N ^ 2) := by
    field_simp
    ring
  have htail : π ^ 3 * ρ / (2 * N ^ 2) ≤ ε := by
    have h1 : π ^ 3 * ρ < N * ε := (div_lt_iff₀ hεpos).1 hNε
    have h2 : (N : ℝ) ≤ 2 * N ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hεpos.le]
  have hreal : 2 * π * ρ ≤ N * (ρ * (2 * Real.sin (π / N))) + ε := by
    have : (N : ℝ) * (ρ * (2 * (π / N - (π / N) ^ 3 / 4)))
        ≤ N * (ρ * (2 * Real.sin (π / N))) := by
      apply mul_le_mul_of_nonneg_left _ hNpos.le
      apply mul_le_mul_of_nonneg_left _ hρ.le
      linarith
    linarith
  have hnn : 0 ≤ (N : ℝ) * (ρ * (2 * Real.sin (π / N))) :=
    mul_nonneg hNpos.le (mul_nonneg hρ.le (mul_nonneg zero_le_two hsin0))
  calc ENNReal.ofReal (2 * π * ρ)
      ≤ ENNReal.ofReal (N * (ρ * (2 * Real.sin (π / N))) + ε) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (N * (ρ * (2 * Real.sin (π / N)))) + ε := by
        rw [ENNReal.ofReal_add hnn hεpos.le, ENNReal.ofReal_coe_nnreal]
    _ ≤ Measure.hausdorffMeasure 1 (sphere x ρ) + ε := by gcongr

/-! ### The radial retraction -/

/-- In a real inner product space the radial retraction onto the sphere of radius `ρ` is
`1`-Lipschitz on the complement of the open ball of radius `ρ`. -/
theorem norm_smul_sub_smul_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ρ : ℝ} (hρ : 0 < ρ) {u v : F} (hu : ρ ≤ ‖u‖) (hv : ρ ≤ ‖v‖) :
    ‖(ρ / ‖u‖) • u - (ρ / ‖v‖) • v‖ ≤ ‖u - v‖ := by
  have ha : 0 < ‖u‖ := lt_of_lt_of_le hρ hu
  have hb : 0 < ‖v‖ := lt_of_lt_of_le hρ hv
  have hc : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have hα0 : 0 ≤ ρ / ‖u‖ := (div_pos hρ ha).le
  have hβ0 : 0 ≤ ρ / ‖v‖ := (div_pos hρ hb).le
  have hα1 : ρ / ‖u‖ ≤ 1 := (div_le_one₀ ha).2 hu
  have hβ1 : ρ / ‖v‖ ≤ 1 := (div_le_one₀ hb).2 hv
  have hαu : ρ / ‖u‖ * ‖u‖ = ρ := div_mul_cancel₀ ρ ha.ne'
  have hβv : ρ / ‖v‖ * ‖v‖ = ρ := div_mul_cancel₀ ρ hb.ne'
  have hαβ1 : ρ / ‖u‖ * (ρ / ‖v‖) ≤ 1 := mul_le_one₀ hα1 hβ0 hβ1
  have hαβP : ρ / ‖u‖ * (ρ / ‖v‖) * (‖u‖ * ‖v‖) = ρ ^ 2 := by
    rw [show ρ / ‖u‖ * (ρ / ‖v‖) * (‖u‖ * ‖v‖) = (ρ / ‖u‖ * ‖u‖) * (ρ / ‖v‖ * ‖v‖) by ring,
      hαu, hβv, sq]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, norm_sub_sq_real,
    norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, Real.norm_of_nonneg hα0,
    Real.norm_of_nonneg hβ0, hαu, hβv]
  nlinarith [sq_nonneg (‖u‖ - ‖v‖), mul_nonneg (sub_nonneg.2 hαβ1) (sub_nonneg.2 hc)]

/-- The radial retraction `z ↦ x + ρ (z - x)/‖z - x‖` onto the circle `sphere x ρ`. -/
def radialRetraction (x : ℂ) (ρ : ℝ) (z : ℂ) : ℂ :=
  x + (ρ / ‖z - x‖) • (z - x)

theorem lipschitzOnWith_radialRetraction (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzOnWith 1 (radialRetraction x ρ) {z | ρ ≤ ‖z - x‖} := by
  refine LipschitzOnWith.mk_one fun z hz w hw => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have hRR : radialRetraction x ρ z - radialRetraction x ρ w
      = (ρ / ‖z - x‖) • (z - x) - (ρ / ‖w - x‖) • (w - x) := by
    simp only [radialRetraction]
    abel
  rw [hRR, show z - w = (z - x) - (w - x) by abel]
  exact norm_smul_sub_smul_le hρ hz hw

/-! ### The frontier covers the circle -/

/-- A preconnected set that meets `A` and leaves `closure A` meets `frontier A`. -/
theorem inter_frontier_nonempty_of_isPreconnected {L A : Set ℂ} (hL : IsPreconnected L)
    {s q : ℂ} (hs : s ∈ L) (hq : q ∈ L) (hsA : s ∈ A) (hqA : q ∉ closure A) :
    (L ∩ frontier A).Nonempty := by
  by_contra hcon
  have hfr : ∀ z ∈ L, z ∉ closure A \ interior A := fun z hz hzf => hcon ⟨z, hz, hzf⟩
  have hs_int : s ∈ interior A := by
    by_contra hsi
    exact hfr s hs ⟨subset_closure hsA, hsi⟩
  have hcover : L ⊆ interior A ∪ (closure A)ᶜ := by
    intro z hz
    by_cases hzi : z ∈ interior A
    · exact Or.inl hzi
    · exact Or.inr fun hzc => hfr z hz ⟨hzc, hzi⟩
  obtain ⟨z, -, hz1, hz2⟩ := hL _ _ isOpen_interior isClosed_closure.isOpen_compl hcover
    ⟨s, hs, hs_int⟩ ⟨q, hq, hqA⟩
  exact hz2 (interior_subset_closure hz1)

/-- Every point of the circle `sphere x ρ` is the radial retraction of a point of `frontier A`
at distance at least `ρ` from `x`. -/
theorem sphere_subset_image_radialRetraction {A : Set ℂ} {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hA : Bornology.IsBounded A) (hball : closedBall x ρ ⊆ A) :
    sphere x ρ ⊆ radialRetraction x ρ '' (frontier A ∩ {z | ρ ≤ ‖z - x‖}) := by
  intro s hs
  obtain ⟨r, hr⟩ := hA.subset_closedBall x
  have hsx : ‖s - x‖ = ρ := by rw [← dist_eq_norm]; exact hs
  have hsA : s ∈ A := hball (sphere_subset_closedBall hs)
  -- the outward ray `t ↦ x + t (s - x)`, `t ≥ 1`
  set γ : ℝ → ℂ := fun t => x + (t : ℂ) * (s - x) with hγ
  have hγc : Continuous γ :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖γ t - x‖ = t * ρ := by
    intro t ht
    simp only [hγ, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg ht, hsx]
  have hL : IsPreconnected (γ '' Ici 1) := isPreconnected_Ici.image _ hγc.continuousOn
  have hs_mem : s ∈ γ '' Ici 1 := ⟨1, self_mem_Ici, by simp [hγ]⟩
  set T : ℝ := (|r| + 1) / ρ + 1 with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ (|r| + 1) / ρ := by positivity
    linarith
  have hq_out : γ T ∉ closure A := by
    intro hq
    have hcl : closure A ⊆ closedBall x r := closure_minimal hr isClosed_closedBall
    have h1 := hcl hq
    rw [mem_closedBall, dist_eq_norm, hnorm T (by linarith)] at h1
    have h2 : T * ρ = |r| + 1 + ρ := by
      rw [hT]
      field_simp
    have h3 : r ≤ |r| := le_abs_self r
    linarith
  obtain ⟨p, ⟨t, ht, rfl⟩, hpfr⟩ :=
    inter_frontier_nonempty_of_isPreconnected hL hs_mem ⟨T, hT1, rfl⟩ hsA hq_out
  have ht1 : (1 : ℝ) ≤ t := ht
  have hpx : ‖γ t - x‖ = t * ρ := hnorm t (by linarith)
  refine ⟨γ t, ⟨hpfr, ?_⟩, ?_⟩
  · show ρ ≤ ‖γ t - x‖
    rw [hpx]
    nlinarith
  · have htρ : t * ρ ≠ 0 := by positivity
    -- the real scalar action on `ℂ` is multiplication by the real cast, definitionally
    have hval : radialRetraction x ρ (γ t)
        = x + ((ρ / ‖γ t - x‖ : ℝ) : ℂ) * (γ t - x) := rfl
    have hγt : γ t - x = (t : ℂ) * (s - x) := by
      simp only [hγ, add_sub_cancel_left]
    have hr : ρ / (t * ρ) * t = 1 := by
      rw [div_mul_eq_mul_div, div_eq_one_iff_eq htρ, mul_comm]
    have hcoef : ((ρ / (t * ρ) : ℝ) : ℂ) * (t : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hr, Complex.ofReal_one]
    rw [hval, hpx, hγt]
    calc x + ((ρ / (t * ρ) : ℝ) : ℂ) * ((t : ℂ) * (s - x))
        = x + (((ρ / (t * ρ) : ℝ) : ℂ) * (t : ℂ)) * (s - x) := by ring
      _ = s := by rw [hcoef]; ring

/-! ### The plane encircling bound -/

/-- **The plane encircling bound.**  If a bounded set `A ⊆ ℂ` contains the closed disc of
radius `ρ ≥ 0` about `x`, then `μH[1] (frontier A) ≥ 2πρ`. -/
theorem plane_perimeter_bound (A : Set ℂ) (x : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hA : Bornology.IsBounded A) (hball : Metric.closedBall x ρ ⊆ A) :
    ENNReal.ofReal (2 * Real.pi * ρ)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (frontier A) := by
  rcases eq_or_lt_of_le hρ with rfl | hρ
  · simp
  calc ENNReal.ofReal (2 * Real.pi * ρ)
      ≤ Measure.hausdorffMeasure 1 (sphere x ρ) :=
        two_pi_mul_le_hausdorffMeasure_sphere x hρ.le
    _ ≤ Measure.hausdorffMeasure 1
          (radialRetraction x ρ '' (frontier A ∩ {z | ρ ≤ ‖z - x‖})) :=
        measure_mono (sphere_subset_image_radialRetraction hρ hA hball)
    _ ≤ Measure.hausdorffMeasure 1 (frontier A ∩ {z | ρ ≤ ‖z - x‖}) := by
        simpa using ((lipschitzOnWith_radialRetraction x hρ).mono
          inter_subset_right).hausdorffMeasure_image_le (d := 1) zero_le_one
    _ ≤ Measure.hausdorffMeasure 1 (frontier A) := measure_mono inter_subset_left

end ErdosProblems.Erdos1041.PaperCompleteR21.Lobe
