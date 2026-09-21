import Mathlib

/-!
# Erdős #1041: circle-slice packing and the dual-arity root-count floor

Paper-form restatements of the two environments of
`paper/reasoning-parts/erdos1041/core.tex` labelled `res:circle-slice-packing`
(line 378) and `res:dual-arity-floor` (line 401).

The paper works in the Poincaré disc: the roots of a sublevel component are
pulled back by a Riemann map to points `b_j ∈ 𝔻`, written in geodesic polar
coordinates `(d_j, θ_j)` about the centre `0`, and `d` is the hyperbolic
distance normalised by `d(0,s) = 2 artanh s`.

Mathlib (v4.29.1) has no disc model of the hyperbolic plane, hence no
hyperbolic law of cosines.  That classical theorem is the *only* external
input used below, and it enters as one explicit named hypothesis:

  `hlaw : ∀ d₁ θ₁ d₂ θ₂, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
            = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂)`

for a map `pt : ℝ → ℝ → P` into a pseudometric space, `pt d θ` being the point
at hyperbolic distance `d` from the centre with argument `θ`.  This is verbatim
the identity the paper's proof invokes ("By the hyperbolic law of cosines the
point of the hyperbolic circle of radius `r` at angle `θ` lies in `B_j` exactly
when ...").  Everything else — the angular measure of the slices, their
disjointness, the total-measure bound, and the finite-sum assembly of the
root-count floor — is proved here with no further assumption.

The angular-measure step is the real work and is done without any circle
measure: the `k` open arcs are lifted to `ℝ` together with `N` of their
`2π`-translates, the resulting `kN` open intervals are shown pairwise disjoint
and contained in one interval of length `2T + 2πN + 2π`, and `N → ∞` gives the
sharp constant `π`.

* `sliceHalfAngle D d r` — the paper's `w(d,r)`, with `clamp` written
  `max (-1) (min 1 ·)`.
* `circle_slice_packing` — `res:circle-slice-packing`.
* `lam`, `delta` — the paper's `λ(d) = -log tanh(d/2)` and
  `δ(a) = -log(1 - e^{-1/a})`.
* `dual_arity_floor`, `dual_arity_floor_sup` — `res:dual-arity-floor`, the
  second with `U` given as the paper's supremum.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Real Set MeasureTheory

/-- The paper's `w(d,r) = arccos (clamp ((cosh d cosh r - cosh (D/2))/(sinh d sinh r)))`,
the half-width of the arc cut from the hyperbolic circle of radius `r` about the
centre by the open hyperbolic ball of radius `D/2` about a point at distance `d`
from the centre.  `clamp` truncates to `[-1,1]`. -/
def sliceHalfAngle (D d r : ℝ) : ℝ :=
  arccos (max (-1) (min 1 ((cosh d * cosh r - cosh (D / 2)) / (sinh d * sinh r))))

theorem sliceHalfAngle_nonneg (D d r : ℝ) : 0 ≤ sliceHalfAngle D d r :=
  arccos_nonneg _

theorem sliceHalfAngle_le_pi (D d r : ℝ) : sliceHalfAngle D d r ≤ π :=
  arccos_le_pi _

/-- An angle strictly inside the slice satisfies the strict law-of-cosines
inequality that defines the open ball. -/
private theorem cosh_expr_lt_of_abs_lt {D d r φ : ℝ} (hd : 0 < d) (hr : 0 < r)
    (hφ : |φ| < sliceHalfAngle D d r) :
    cosh d * cosh r - sinh d * sinh r * cos φ < cosh (D / 2) := by
  have hprod : 0 < sinh d * sinh r :=
    mul_pos (sinh_pos_iff.mpr hd) (sinh_pos_iff.mpr hr)
  set X : ℝ := (cosh d * cosh r - cosh (D / 2)) / (sinh d * sinh r) with hXdef
  set c : ℝ := max (-1) (min 1 X) with hcdef
  have hw : sliceHalfAngle D d r = arccos c := by rw [hcdef, hXdef]; rfl
  have hc1 : c ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have hc2 : (-1 : ℝ) ≤ c := le_max_left _ _
  rw [hw] at hφ
  have habs : |φ| ∈ Icc 0 π := ⟨abs_nonneg φ, le_trans hφ.le (arccos_le_pi c)⟩
  have harc : arccos c ∈ Icc 0 π := ⟨arccos_nonneg c, arccos_le_pi c⟩
  have hcos : cos (arccos c) < cos |φ| := strictAntiOn_cos habs harc hφ
  rw [cos_arccos hc2 hc1, cos_abs] at hcos
  have hXle : X ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have hc' : c = 1 := by
      rw [hcdef, min_eq_left hcon.le, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [hc', arccos_one] at hφ
    exact absurd hφ (not_lt.mpr (abs_nonneg φ))
  have hXc : X ≤ c := by
    rw [hcdef, min_eq_right hXle]
    exact le_max_right _ _
  have hXlt : X < cos φ := lt_of_le_of_lt hXc hcos
  rw [hXdef, div_lt_iff₀ hprod] at hXlt
  linarith

/-- The law of cosines turns the slice condition into membership of the open
hyperbolic ball of radius `D/2`. -/
private theorem dist_lt_half {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {D d r θ₀ θ₁ φ : ℝ} (hD : 0 < D) (hd : 0 < d) (hr : 0 < r)
    (hφ : |φ| < sliceHalfAngle D d r) (hcos : cos φ = cos (θ₀ - θ₁)) :
    dist (pt r θ₀) (pt d θ₁) < D / 2 := by
  have hkey := cosh_expr_lt_of_abs_lt hd hr hφ
  rw [hcos] at hkey
  have hlt : cosh (dist (pt r θ₀) (pt d θ₁)) < cosh (D / 2) := by
    rw [hlaw r θ₀ d θ₁]
    linarith
  have habs := cosh_lt_cosh.mp hlt
  rwa [abs_of_nonneg dist_nonneg,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ D / 2)] at habs

/-- **`res:circle-slice-packing`.**  If the `k` points at geodesic polar
coordinates `(d_j, θ_j)` are pairwise at hyperbolic distance at least `D`, then
for every radius `r > 0` the slice half-angles `w(d_j, r)` sum to at most `π`. -/
theorem circle_slice_packing {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {r : ℝ} (hr : 0 < r) :
    ∑ j, sliceHalfAngle D (d j) r ≤ π := by
  classical
  have hpi : (0 : ℝ) < π := pi_pos
  obtain ⟨w, hwdef⟩ : ∃ w : Fin k → ℝ, ∀ j, w j = sliceHalfAngle D (d j) r :=
    ⟨fun j => sliceHalfAngle D (d j) r, fun _ => rfl⟩
  have hgoal : ∑ j, sliceHalfAngle D (d j) r = ∑ j, w j :=
    Finset.sum_congr rfl fun j _ => (hwdef j).symm
  rw [hgoal]
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j; rw [hwdef]; exact sliceHalfAngle_nonneg _ _ _
  have hwpi : ∀ j, w j ≤ π := by
    intro j; rw [hwdef]; exact sliceHalfAngle_le_pi _ _ _
  -- membership of the open ball, in the `2π`-shifted form
  have hmem : ∀ (j : Fin k) (y : ℝ) (m : ℤ), |y - (m : ℝ) * (2 * π) - θ j| < w j →
      dist (pt r y) (pt (d j) (θ j)) < D / 2 := by
    intro j y m hlt
    rw [hwdef] at hlt
    refine dist_lt_half pt hlaw hD (hd j) hr hlt ?_
    have hrw : y - (m : ℝ) * (2 * π) - θ j = (y - θ j) - (m : ℝ) * (2 * π) := by ring
    rw [hrw, cos_sub_int_mul_two_pi]
  -- disjointness: a test angle cannot lie in two slices
  have hdisj : ∀ i j : Fin k, i ≠ j → ∀ (y : ℝ) (m n : ℤ),
      |y - (m : ℝ) * (2 * π) - θ i| < w i → |y - (n : ℝ) * (2 * π) - θ j| < w j → False := by
    intro i j hij y m n hi hj
    have h1 := hmem i y m hi
    have h2 := hmem j y n hj
    have h3 := hsep i j hij
    have htri : dist (pt (d i) (θ i)) (pt (d j) (θ j))
        ≤ dist (pt (d i) (θ i)) (pt r y) + dist (pt r y) (pt (d j) (θ j)) :=
      dist_triangle _ _ _
    rw [dist_comm (pt (d i) (θ i)) (pt r y)] at htri
    linarith
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact hpi.le
  -- a uniform bound for the angles
  have hT0 : (0 : ℝ) ≤ ∑ j, |θ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hTle : ∀ j, |θ j| ≤ ∑ j, |θ j| := fun j =>
    Finset.single_le_sum (f := fun j => |θ j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
  -- the `N`-fold interval packing estimate
  have key : ∀ N : ℕ, 0 < N →
      2 * (N : ℝ) * (∑ j, w j) ≤ 2 * (∑ j, |θ j|) + 2 * π * (N : ℝ) + 2 * π := by
    intro N hN
    obtain ⟨I, hIdef⟩ : ∃ I : Fin k × Fin N → Set ℝ, ∀ q : Fin k × Fin N,
        I q = Ioo (θ q.1 + (q.2.val : ℝ) * (2 * π) - w q.1)
                  (θ q.1 + (q.2.val : ℝ) * (2 * π) + w q.1) := ⟨_, fun _ => rfl⟩
    have hImeas : ∀ q : Fin k × Fin N, MeasurableSet (I q) := by
      intro q; rw [hIdef]; exact measurableSet_Ioo
    have hIvol : ∀ q : Fin k × Fin N, volume (I q) = ENNReal.ofReal (2 * w q.1) := by
      intro q
      rw [hIdef, Real.volume_Ioo]
      congr 1
      ring
    have hIsub : ∀ q : Fin k × Fin N,
        I q ⊆ Icc (-(∑ j, |θ j|) - π) ((∑ j, |θ j|) + 2 * π * (N : ℝ) + π) := by
      intro q y hy
      rw [hIdef, mem_Ioo] at hy
      have habs := hTle q.1
      rw [abs_le] at habs
      have h4 := hw0 q.1
      have h5 := hwpi q.1
      have h6 : (0 : ℝ) ≤ (q.2.val : ℝ) * (2 * π) := by positivity
      have hq2 : ((q.2.val : ℕ) : ℝ) ≤ (N : ℝ) - 1 := by
        have hlt : (q.2.val : ℕ) + 1 ≤ N := q.2.isLt
        have hc := (Nat.cast_le (α := ℝ)).mpr hlt
        push_cast at hc
        linarith
      have h7 : (q.2.val : ℝ) * (2 * π) ≤ ((N : ℝ) - 1) * (2 * π) :=
        mul_le_mul_of_nonneg_right hq2 (by positivity)
      constructor
      · linarith [hy.1, habs.1]
      · linarith [hy.2, habs.2]
    have hpd : ((Finset.univ : Finset (Fin k × Fin N)) : Set (Fin k × Fin N)).PairwiseDisjoint I := by
      intro q₁ _ q₂ _ hne
      obtain ⟨i, m⟩ := q₁
      obtain ⟨j, n⟩ := q₂
      have hgoal2 : Disjoint (I (i, m)) (I (j, n)) := by
        rw [Set.disjoint_left]
        intro y hy₁ hy₂
        rw [hIdef, mem_Ioo] at hy₁
        rw [hIdef, mem_Ioo] at hy₂
        simp only at hy₁ hy₂
        by_cases hfst : i = j
        · have hsnd : m ≠ n := by
            intro h
            exact hne (by rw [hfst, h])
          subst hfst
          have hW := hwpi i
          have hlt1 : (m.val : ℝ) * (2 * π) < (n.val : ℝ) * (2 * π) + 2 * π := by
            linarith [hy₁.1, hy₂.2]
          have hlt2 : (n.val : ℝ) * (2 * π) < (m.val : ℝ) * (2 * π) + 2 * π := by
            linarith [hy₂.1, hy₁.2]
          have hu : (m.val : ℝ) < (n.val : ℝ) + 1 := by nlinarith [hlt1, hpi]
          have hv : (n.val : ℝ) < (m.val : ℝ) + 1 := by nlinarith [hlt2, hpi]
          have hmn : m.val = n.val := by
            have c1 : m.val < n.val + 1 := by exact_mod_cast hu
            have c2 : n.val < m.val + 1 := by exact_mod_cast hv
            omega
          exact hsnd (Fin.val_injective hmn)
        · refine hdisj i j hfst y (m.val : ℤ) (n.val : ℤ) ?_ ?_
          · rw [abs_lt]
            push_cast
            constructor <;> linarith [hy₁.1, hy₁.2]
          · rw [abs_lt]
            push_cast
            constructor <;> linarith [hy₂.1, hy₂.2]
      exact hgoal2
    have hunion : volume (⋃ q ∈ (Finset.univ : Finset (Fin k × Fin N)), I q)
        = ∑ q ∈ (Finset.univ : Finset (Fin k × Fin N)), volume (I q) :=
      measure_biUnion_finset hpd fun q _ => hImeas q
    have hsubset : (⋃ q ∈ (Finset.univ : Finset (Fin k × Fin N)), I q)
        ⊆ Icc (-(∑ j, |θ j|) - π) ((∑ j, |θ j|) + 2 * π * (N : ℝ) + π) := by
      intro y hy
      simp only [Set.mem_iUnion, exists_prop] at hy
      obtain ⟨q, _, hyq⟩ := hy
      exact hIsub q hyq
    have hbound : ∑ q ∈ (Finset.univ : Finset (Fin k × Fin N)), volume (I q)
        ≤ volume (Icc (-(∑ j, |θ j|) - π) ((∑ j, |θ j|) + 2 * π * (N : ℝ) + π)) := by
      rw [← hunion]
      exact measure_mono hsubset
    rw [Real.volume_Icc] at hbound
    simp only [hIvol] at hbound
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun q (_ : q ∈ (Finset.univ : Finset (Fin k × Fin N))) => by
        have := hw0 q.1; linarith)] at hbound
    have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hBA : (0 : ℝ) ≤ (∑ j, |θ j|) + 2 * π * (N : ℝ) + π - (-(∑ j, |θ j|) - π) := by
      nlinarith [hT0, hpi, hNR]
    rw [ENNReal.ofReal_le_ofReal_iff hBA] at hbound
    have hsumeq : ∑ q ∈ (Finset.univ : Finset (Fin k × Fin N)), 2 * w q.1
        = 2 * (N : ℝ) * ∑ j, w j := by
      rw [Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsumeq] at hbound
    linarith
  -- let `N → ∞`
  by_contra hcon
  push_neg at hcon
  obtain ⟨N, hN⟩ := exists_nat_gt (((∑ j, |θ j|) + π) / ((∑ j, w j) - π))
  have hgap : 0 < (∑ j, w j) - π := by linarith
  have hNpos : 0 < N := by
    by_contra hz
    push_neg at hz
    interval_cases N
    · simp only [Nat.cast_zero] at hN
      have : (0 : ℝ) ≤ ((∑ j, |θ j|) + π) / ((∑ j, w j) - π) := by positivity
      linarith
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hkey := key N hNpos
  have hmul : (∑ j, |θ j|) + π < (N : ℝ) * ((∑ j, w j) - π) :=
    (div_lt_iff₀ hgap).mp hN
  nlinarith [hkey, hmul, hNR]

/-- The paper's `λ(d) = -log tanh(d/2)`. -/
def lam (d : ℝ) : ℝ := -log (tanh (d / 2))

/-- The paper's `δ(a) = -log(1 - e^{-1/a})`. -/
def delta (a : ℝ) : ℝ := -log (1 - exp (-(1 / a)))

private theorem tanh_strictMono : StrictMono tanh := by
  intro x y hxy
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh,
    div_lt_div_iff₀ (cosh_pos x) (cosh_pos y)]
  have h : 0 < sinh (y - x) := sinh_pos_iff.mpr (by linarith)
  rw [sinh_sub] at h
  linarith

private theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < tanh x := by
  have h := tanh_strictMono hx
  rwa [tanh_zero] at h

private theorem lam_lt_lam {d₁ d₂ : ℝ} (h₁ : 0 < d₁) (h : d₁ < d₂) : lam d₂ < lam d₁ := by
  have ht1 : 0 < tanh (d₁ / 2) := tanh_pos_of_pos (by linarith)
  have ht : tanh (d₁ / 2) < tanh (d₂ / 2) := tanh_strictMono (by linarith)
  have hlog : log (tanh (d₁ / 2)) < log (tanh (d₂ / 2)) := log_lt_log ht1 ht
  unfold lam
  linarith

/-- `λ` is strictly decreasing on the positive axis, so the paper's radius bound
`λ(d_j) ≤ δ(a)/2 = λ(d_low(a))` is the statement `d_j ≥ d_low(a)`. -/
theorem le_of_lam_le {d₁ d₂ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h : lam d₂ ≤ lam d₁) :
    d₁ ≤ d₂ := by
  by_contra hcon
  push_neg at hcon
  exact absurd h (not_le.mpr (lam_lt_lam h₂ hcon))

/-- **`res:dual-arity-floor`.**  With the separation `(eq:lc-separation)` and the
two consequences `(eq:lc-radius-and-budget)` of the standing failure hypothesis —
the radius bound `λ(d_j) ≤ δ(a)/2` and the budget `∑_j λ(d_j) ≥ x` — any
nonnegative weights `σ_i` at radii `r_i > 0` whose deficit `U` is positive force
`k ≥ (x - πΣ)/U`.  `U` is here any upper bound for the paper's supremand on
`[d_low(a), ∞)`; `dual_arity_floor_sup` is the form with `U` the supremum. -/
theorem dual_arity_floor {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {p : ℕ} (r σ : Fin p → ℝ) (hr : ∀ i, 0 < r i) (hσ : ∀ i, 0 ≤ σ i)
    {a x dlow U : ℝ} (hdlow : 0 < dlow) (hdlowval : lam dlow = delta a / 2)
    (hrad : ∀ j, lam (d j) ≤ delta a / 2)
    (hbudget : x ≤ ∑ j, lam (d j))
    (hU : ∀ s : ℝ, dlow ≤ s → lam s - ∑ i, σ i * sliceHalfAngle D s (r i) ≤ U)
    (hUpos : 0 < U) :
    (x - π * ∑ i, σ i) / U ≤ (k : ℝ) := by
  classical
  have hdj : ∀ j, dlow ≤ d j := fun j =>
    le_of_lam_le hdlow (hd j) (by rw [hdlowval]; exact hrad j)
  have hsum1 : ∑ j, (lam (d j) - ∑ i, σ i * sliceHalfAngle D (d j) (r i)) ≤ (k : ℝ) * U := by
    calc ∑ j, (lam (d j) - ∑ i, σ i * sliceHalfAngle D (d j) (r i))
        ≤ ∑ _j : Fin k, U := Finset.sum_le_sum fun j _ => hU (d j) (hdj j)
      _ = (k : ℝ) * U := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpack : ∀ i, ∑ j, sliceHalfAngle D (d j) (r i) ≤ π := fun i =>
    circle_slice_packing pt hlaw d θ hd hD hsep (hr i)
  have hsum2 : ∑ j, ∑ i, σ i * sliceHalfAngle D (d j) (r i) ≤ π * ∑ i, σ i := by
    rw [Finset.sum_comm]
    calc ∑ i, ∑ j, σ i * sliceHalfAngle D (d j) (r i)
        = ∑ i, σ i * ∑ j, sliceHalfAngle D (d j) (r i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ i, σ i * π :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpack i) (hσ i)
      _ = π * ∑ i, σ i := by rw [← Finset.sum_mul]; ring
  have hsplit : ∑ j, (lam (d j) - ∑ i, σ i * sliceHalfAngle D (d j) (r i))
      = (∑ j, lam (d j)) - ∑ j, ∑ i, σ i * sliceHalfAngle D (d j) (r i) := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit] at hsum1
  rw [div_le_iff₀ hUpos]
  linarith

/-- `res:dual-arity-floor` with `U` given exactly as the paper's supremum. -/
theorem dual_arity_floor_sup {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {p : ℕ} (r σ : Fin p → ℝ) (hr : ∀ i, 0 < r i) (hσ : ∀ i, 0 ≤ σ i)
    {a x dlow U : ℝ} (hdlow : 0 < dlow) (hdlowval : lam dlow = delta a / 2)
    (hrad : ∀ j, lam (d j) ≤ delta a / 2)
    (hbudget : x ≤ ∑ j, lam (d j))
    (hU : IsLUB {y : ℝ | ∃ s : ℝ, dlow ≤ s ∧
      y = lam s - ∑ i, σ i * sliceHalfAngle D s (r i)} U)
    (hUpos : 0 < U) :
    (x - π * ∑ i, σ i) / U ≤ (k : ℝ) :=
  dual_arity_floor pt hlaw d θ hd hD hsep r σ hr hσ hdlow hdlowval hrad hbudget
    (fun s hs => hU.1 ⟨s, hs, rfl⟩) hUpos

#print axioms sliceHalfAngle_nonneg
#print axioms sliceHalfAngle_le_pi
#print axioms circle_slice_packing
#print axioms le_of_lam_le
#print axioms dual_arity_floor
#print axioms dual_arity_floor_sup

end ErdosProblems.Erdos1041.PaperCompleteR21

end
