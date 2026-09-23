import ErdosProblems.Erdos1041.PaperCompleteR21.LobeAndArity

/-!
# Erdős 1041: `res:arity-not-capacity`

The short-note proposition `res:arity-not-capacity`
(`paper/1041/erdos-1041-lemniscate-newton-flow.tex`, line 880): for
`g(z) = z^3 - (3/400)z - 3/32`, all roots lie in the open unit disc and
`μ = 187/2000 ≤ 1/2`; the first merger joins two root components, so `k₀ = 2`,
but the component at level `2μ` containing that pair has normalised capacity `1`.

Here `K_t = {|g| ≤ t}` and `μ` is the least critical-value modulus.  `k₀` is the
number of roots, counted with multiplicity, in the component of `K_μ`
containing the critical point `c_*` with `|g(c_*)| = μ`
(`res:constant-factor-arity` in the long record).  The component at level `2μ`
is the component `C` of `{|g| < 2μ}` containing `c_*`, and its normalised
capacity is the capacity of `closure C` divided by `(2μ)^{1/3}`
(`res:constant-factor-capacity`).

`Arity.arity_not_capacity` states the whole proposition.  Everything except the
value of one capacity is proved outright:

* the root-disc and least-critical-value clauses (from `LobeAndArity.lean`);
* `c_* = -1/20` is the only critical point at level `μ`;
* the roots of `g`, with multiplicity, in the component of `K_μ` containing
  `c_*` are exactly two distinct roots `a` and `b`, so `k₀ = 2`, and `a` and `b`
  lie in different components of `{|g| < μ}`: the merger at level `μ` joins
  two root components;
* the component `C` of `{|g| < 2μ}` containing `c_*` contains `a` and `b`, is
  the whole set `{|g| < 2μ}`, and its closure is the whole filled lemniscate
  `{|g| ≤ 2μ}` (`Arity.closure_doubleLevelComponent`).

Capacity is measured by the transfinite diameter `transfiniteDiameter`; for a
compact plane set this equals the logarithmic capacity (the Fekete–Szegő
theorem).  Its value on a filled lemniscate is the one named input,
`LemniscateTransfiniteDiameter`: for monic `p` of degree `n ≥ 1` and `t > 0`,
the set `{|p| ≤ t}` has transfinite diameter `t^{1/n}`.  That is a classical
theorem about every monic polynomial and mentions no feature of `g`.  Mathlib
defines neither logarithmic capacity nor transfinite diameter, so it enters as
an explicit hypothesis.

Reference: T. Ransford, *Potential Theory in the Complex Plane*, Cambridge
University Press, 1995: Theorem 5.2.5 (capacity of a polynomial preimage) and
the Fekete–Szegő theorem (p. 153).

## Proof

On the line `Re z = 1/20` one has `|g| ≥ 47/500 > μ`, and on the real half-line
`z ≤ 1/10` one has `|g| ≥ μ`.  Hence `{|g| < μ}` lies in three disjoint open
pieces: left of the line and above the real axis, left of it and below, and
right of it.  By the maximum modulus principle applied to `1/g`, every
component of a strict sublevel set `{|g| < t}` contains a zero.  The components
of `{|g| < μ}` through `-1/20 ± i/5` and `1/2` therefore give roots `a`, `b`,
`r`, one in each piece, and these are all three roots.  The vertical segment
`Re z = -1/20`, `|Im z| ≤ 1/5` lies in `K_μ`, so `a` and `b` lie in the
component of `K_μ` through `c_* = -1/20`, while the line `Re z = 1/20` keeps
`r` out of it.  At level `2μ` the real segment `[-1/20, 1/2]` has
`|g| ≤ 47/500 < 2μ`, so all three roots lie in one component of `{|g| < 2μ}`;
since every component contains a root, that set is connected.  The open mapping
theorem gives its closure `{|g| ≤ 2μ}`.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Set Filter Topology

/-! ## Transfinite diameter and the named input -/

/-- The transfinite diameter of a plane set `E` (Fekete): the infimum over
`N ≥ 2` of the `N`-th diameters
`δ_N(E) = sup_{z_1, …, z_N ∈ E} (∏_{i<j} |z_i - z_j|)^{2/(N(N-1))}`.
For compact nonempty `E` each supremum is taken over a bounded nonempty family
and every `δ_N(E)` is nonnegative, so these are the classical quantities; the
sequence `δ_N(E)` is decreasing, so the infimum is its limit, and by the
Fekete–Szegő theorem that limit is the logarithmic capacity of `E`. -/
def transfiniteDiameter (E : Set ℂ) : ℝ :=
  ⨅ N : {N : ℕ // 2 ≤ N}, ⨆ z : Fin N.1 → E,
    (∏ q ∈ Finset.univ.filter (fun q : Fin N.1 × Fin N.1 => q.1 < q.2),
        ‖(z q.1 : ℂ) - z q.2‖) ^ ((2 : ℝ) / ((N.1 : ℝ) * ((N.1 : ℝ) - 1)))

/-- **Named input: the transfinite diameter of a filled lemniscate.**  For a
monic complex polynomial `p` of degree `n ≥ 1` and a level `t > 0`, the filled
lemniscate `{|p| ≤ t}` has transfinite diameter `t^{1/n}`.  This is the
capacity of a polynomial preimage, `cap(p⁻¹(E)) = cap(E)^{1/n}` for monic `p`
(Ransford, *Potential Theory in the Complex Plane*, Theorem 5.2.5), applied to
the closed disc of radius `t`, whose capacity is `t`, together with the
Fekete–Szegő theorem that the transfinite diameter of a compact plane set is
its logarithmic capacity (same book, p. 153).  It is a statement about every
monic polynomial.  Mathlib has neither notion, so the theorems below take it
as a hypothesis. -/
def LemniscateTransfiniteDiameter : Prop :=
  ∀ (p : ℂ[X]) (t : ℝ), p.Monic → 1 ≤ p.natDegree → 0 < t →
    transfiniteDiameter {z | ‖p.eval z‖ ≤ t} = t ^ ((1 : ℝ) / p.natDegree)

/-! ## Sublevel sets of a nonconstant complex polynomial -/

/-- The strict sublevel sets of a nonconstant complex polynomial are bounded. -/
theorem isBounded_polynomial_sublevel_lt (P : ℂ[X]) (hP : 0 < P.degree) (t : ℝ) :
    Bornology.IsBounded {z : ℂ | ‖P.eval z‖ < t} := by
  have h : Tendsto (fun z : ℂ => ‖P.eval z‖) (Bornology.cobounded ℂ) atTop :=
    P.tendsto_norm_atTop hP (z := fun z : ℂ => z) tendsto_norm_cobounded_atTop
  have h2 : {z : ℂ | t ≤ ‖P.eval z‖} ∈ Bornology.cobounded ℂ := h.eventually_ge_atTop t
  have h3 : Bornology.IsBounded {z : ℂ | t ≤ ‖P.eval z‖}ᶜ :=
    Bornology.isBounded_compl_iff.mpr (Bornology.isCobounded_def.mpr h2)
  convert h3 using 1
  ext z
  simp [not_le]

/-- A point of an open set lying in the closure of one of its components lies
in that component. -/
theorem mem_connectedComponentIn_of_mem_closure {Ω : Set ℂ} (hΩ : IsOpen Ω) {p z : ℂ}
    (hz : z ∈ closure (connectedComponentIn Ω p)) (hzΩ : z ∈ Ω) :
    z ∈ connectedComponentIn Ω p := by
  obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.mp hz (connectedComponentIn Ω z)
    hΩ.connectedComponentIn (mem_connectedComponentIn hzΩ)
  rw [connectedComponentIn_eq hyU, ← connectedComponentIn_eq hyV]
  exact mem_connectedComponentIn hzΩ

/-- **Every component of a strict sublevel set contains a zero.**  If `P` is a
nonconstant complex polynomial and `|P(p)| < t`, the component of `{|P| < t}`
containing `p` contains a zero of `P`.  The frontier of that bounded component
lies outside `{|P| < t}`.  If the component had no zero, `1/P` would be
holomorphic on its closure with modulus at most `1/t` on the frontier, and the
maximum modulus principle would give `|P(p)| ≥ t`. -/
theorem exists_zero_mem_connectedComponentIn_sublevel (P : ℂ[X]) (hP : 0 < P.degree)
    {t : ℝ} {p : ℂ} (hp : ‖P.eval p‖ < t) :
    ∃ z ∈ connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p, P.eval z = 0 := by
  have hΩopen : IsOpen {w : ℂ | ‖P.eval w‖ < t} :=
    isOpen_lt P.continuous.norm continuous_const
  have hUopen : IsOpen (connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p) :=
    hΩopen.connectedComponentIn
  have hpU : p ∈ connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p :=
    mem_connectedComponentIn hp
  have hUbdd : Bornology.IsBounded (connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p) :=
    (isBounded_polynomial_sublevel_lt P hP t).subset (connectedComponentIn_subset _ p)
  have ht : 0 < t := lt_of_le_of_lt (norm_nonneg _) hp
  have hfront : ∀ z ∈ frontier (connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p),
      t ≤ ‖P.eval z‖ := by
    intro z hz
    by_contra hlt
    have hzU := mem_connectedComponentIn_of_mem_closure hΩopen (frontier_subset_closure hz)
      (not_le.mp hlt)
    rw [hUopen.frontier_eq] at hz
    exact hz.2 hzU
  by_contra hnone
  have hno : ∀ z ∈ connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p, P.eval z ≠ 0 :=
    fun z hz h0 => hnone ⟨z, hz, h0⟩
  have hne : ∀ z ∈ closure (connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p),
      P.eval z ≠ 0 := by
    intro z hz h0
    by_cases hzU : z ∈ connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p
    · exact hno z hzU h0
    · have hzf : z ∈ frontier (connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p) := by
        rw [hUopen.frontier_eq]
        exact ⟨hz, hzU⟩
      have h1 := hfront z hzf
      rw [h0, norm_zero] at h1
      linarith
  have hd : DiffContOnCl ℂ (fun z => (P.eval z)⁻¹)
      (connectedComponentIn {w : ℂ | ‖P.eval w‖ < t} p) :=
    DifferentiableOn.diffContOnCl fun z hz =>
      (P.differentiableAt.inv (hne z hz)).differentiableWithinAt
  have hbound : ‖(P.eval p)⁻¹‖ ≤ t⁻¹ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hUbdd hd
      (fun z hz => by rw [norm_inv]; exact inv_anti₀ ht (hfront z hz)) (subset_closure hpU)
  rw [norm_inv] at hbound
  have hpos : 0 < ‖P.eval p‖ := norm_pos_iff.mpr (hno p hpU)
  have h2 := (inv_le_inv₀ hpos ht).mp hbound
  linarith

/-- **Closure of a strict sublevel set.**  For a nonconstant complex polynomial
and `t > 0`, the closure of `{|P| < t}` is `{|P| ≤ t}`: at a point `z₀` with
`|P(z₀)| = t`, the open mapping theorem gives points near `z₀` at which `P`
takes the value `(1 - δ) P(z₀)`, of modulus less than `t`. -/
theorem closure_polynomial_sublevel_lt (P : ℂ[X]) (hP : 0 < P.degree) {t : ℝ}
    (ht : 0 < t) :
    closure {z : ℂ | ‖P.eval z‖ < t} = {z : ℂ | ‖P.eval z‖ ≤ t} := by
  apply Subset.antisymm
  · exact closure_minimal
      (fun z (hz : ‖P.eval z‖ < t) => show ‖P.eval z‖ ≤ t from le_of_lt hz)
      (isClosed_le P.continuous.norm continuous_const)
  · intro z₀ hz₀
    rcases lt_or_eq_of_le (show ‖P.eval z₀‖ ≤ t from hz₀) with hlt | heq
    · exact subset_closure hlt
    · have han : AnalyticAt ℂ (fun z => P.eval z) z₀ :=
        Differentiable.analyticAt (fun z => P.differentiableAt) z₀
      rcases han.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
      · exfalso
        have hmem : {z : ℂ | P.eval z = (C (P.eval z₀)).eval z} ∈ 𝓝 z₀ := by
          filter_upwards [hconst] with z hz
          simpa using hz
        have hPC : P = C (P.eval z₀) :=
          Polynomial.eq_of_infinite_eval_eq P _ (infinite_of_mem_nhds z₀ hmem)
        have hdeg : P.degree ≤ 0 := by
          rw [hPC]
          exact degree_C_le
        exact absurd hP (not_lt.mpr hdeg)
      · rw [mem_closure_iff_nhds]
        intro V hV
        have himg : (fun z => P.eval z) '' V ∈ 𝓝 (P.eval z₀) := hopen (image_mem_map hV)
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himg
        have htne : t ≠ 0 := ht.ne'
        set δ : ℝ := min (1 / 2) (ε / (2 * t)) with hδ
        have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
        have hδle : δ ≤ 1 / 2 := min_le_left _ _
        have hδε : δ ≤ ε / (2 * t) := min_le_right _ _
        have hmem : ((1 - δ : ℝ) : ℂ) * P.eval z₀ ∈ Metric.ball (P.eval z₀) ε := by
          rw [Metric.mem_ball, dist_eq_norm]
          have hrw : ((1 - δ : ℝ) : ℂ) * P.eval z₀ - P.eval z₀ =
              -((δ : ℂ) * P.eval z₀) := by
            push_cast
            ring
          rw [hrw, norm_neg, norm_mul, heq, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hδpos]
          have h1 : δ * t ≤ ε / (2 * t) * t := mul_le_mul_of_nonneg_right hδε ht.le
          have h2 : ε / (2 * t) * t = ε / 2 := by
            rw [div_mul_eq_mul_div, mul_div_mul_right _ _ htne]
          linarith
        obtain ⟨z, hzV, hz⟩ := hball hmem
        refine ⟨z, hzV, ?_⟩
        show ‖P.eval z‖ < t
        have hz' : P.eval z = ((1 - δ : ℝ) : ℂ) * P.eval z₀ := hz
        rw [hz', norm_mul, heq, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        nlinarith [mul_pos hδpos ht]

/-- A component of `F` lies in one of two disjoint open sets covering `F`
when it meets that set. -/
theorem connectedComponentIn_subset_of_cover {F u v : Set ℂ} {p : ℂ} (hpF : p ∈ F)
    (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v) (hcover : F ⊆ u ∪ v)
    (hpu : p ∈ u) : connectedComponentIn F p ⊆ u :=
  isPreconnected_connectedComponentIn.subset_left_of_subset_union hu hv huv
    ((connectedComponentIn_subset F p).trans hcover) ⟨p, mem_connectedComponentIn hpF, hpu⟩

/-! ## `res:arity-not-capacity` -/

namespace Arity

theorem G_degree_pos : 0 < G.degree :=
  natDegree_pos_iff_degree_pos.mp (by rw [G_monic_and_degree.2]; norm_num)

/-- The real part of `g(z)`. -/
theorem G_re (z : ℂ) :
    (G.eval z).re = z.re ^ 3 - 3 * z.re * z.im ^ 2 - 3 / 400 * z.re - 3 / 32 := by
  rw [eval_G]
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

/-- The imaginary part of `g(z)`. -/
theorem G_im (z : ℂ) :
    (G.eval z).im = 3 * z.re ^ 2 * z.im - z.im ^ 3 - 3 / 400 * z.im := by
  rw [eval_G]
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem G_norm_sq (z : ℂ) :
    ‖G.eval z‖ ^ 2 = (G.eval z).re ^ 2 + (G.eval z).im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **The barrier.**  On the line `Re z = 1/20`,
`g(z) = -47/500 - (3/20) y^2 - i y^3` with `y = Im z`, so `|g| ≥ 47/500 > μ`. -/
theorem barrier {z : ℂ} (h : z.re = 1 / 20) : 47 / 500 ≤ ‖G.eval z‖ := by
  have hre : (G.eval z).re = -47 / 500 - 3 / 20 * z.im ^ 2 := by
    rw [G_re, h]
    ring
  have h1 := Complex.abs_re_le_norm (G.eval z)
  have h2 := neg_le_abs (G.eval z).re
  nlinarith [sq_nonneg z.im]

/-- On the real axis up to `1/10`,
`g(x) = -187/2000 - (x + 1/20)^2 (1/10 - x) ≤ -μ`, so `|g| ≥ μ`. -/
theorem real_axis_ge {z : ℂ} (him : z.im = 0) (hre : z.re ≤ 1 / 10) :
    187 / 2000 ≤ ‖G.eval z‖ := by
  have hr : (G.eval z).re = -187 / 2000 - (z.re + 1 / 20) ^ 2 * (1 / 10 - z.re) := by
    rw [G_re, him]
    ring
  have h1 := Complex.abs_re_le_norm (G.eval z)
  have h2 := neg_le_abs (G.eval z).re
  have h3 : 0 ≤ (z.re + 1 / 20) ^ 2 * (1 / 10 - z.re) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  linarith

/-- On the vertical line through `c_* = -1/20`,
`g(-1/20 + iy) = -187/2000 + (3/20) y^2 - i y^3`, so `|g| ≤ μ` for `y^2 ≤ 1/25`. -/
theorem vertical_le {z : ℂ} (hre : z.re = -1 / 20) (him : z.im ^ 2 ≤ 1 / 25) :
    ‖G.eval z‖ ≤ 187 / 2000 := by
  have hr : (G.eval z).re = -187 / 2000 + 3 / 20 * z.im ^ 2 := by
    rw [G_re, hre]
    ring
  have hi : (G.eval z).im = -z.im ^ 3 := by
    rw [G_im, hre]
    ring
  have hsq : ‖G.eval z‖ ^ 2 ≤ (187 / 2000) ^ 2 := by
    rw [G_norm_sq, hr, hi]
    have hs0 : 0 ≤ z.im ^ 2 := sq_nonneg _
    have h1 : 0 ≤ z.im ^ 2 * (1 / 25 - z.im ^ 2) := mul_nonneg hs0 (by linarith)
    have h2 : 0 ≤ (z.im ^ 2) ^ 2 * (1 / 25 - z.im ^ 2) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  nlinarith [norm_nonneg (G.eval z)]

/-- At the ends `-1/20 ± i/5` of the vertical segment, `|g| < μ`. -/
theorem vertical_end_lt {z : ℂ} (hre : z.re = -1 / 20) (him : z.im ^ 2 = 1 / 25) :
    ‖G.eval z‖ < 187 / 2000 := by
  have hr : (G.eval z).re = -187 / 2000 + 3 / 20 * z.im ^ 2 := by
    rw [G_re, hre]
    ring
  have hi : (G.eval z).im = -z.im ^ 3 := by
    rw [G_im, hre]
    ring
  have hsq : ‖G.eval z‖ ^ 2 < (187 / 2000) ^ 2 := by
    rw [G_norm_sq, hr, hi]
    have h6 : (-z.im ^ 3) ^ 2 = (z.im ^ 2) ^ 3 := by ring
    rw [h6, him]
    norm_num
  nlinarith [norm_nonneg (G.eval z)]

/-- `g(1/2) = 11/400`, so `|g(1/2)| < μ`. -/
theorem half_lt : ‖G.eval (1 / 2 : ℂ)‖ < 187 / 2000 := by
  have h : G.eval (1 / 2 : ℂ) = ((11 / 400 : ℝ) : ℂ) := by
    rw [eval_G]
    push_cast
    norm_num
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- On the real segment `[-1/20, 1/2]`, `-47/500 ≤ g ≤ 253/8000`, so
`|g| < 2μ`. -/
theorem real_segment_lt {z : ℂ} (him : z.im = 0) (h1 : -1 / 20 ≤ z.re)
    (h2 : z.re ≤ 1 / 2) : ‖G.eval z‖ < 2 * (187 / 2000) := by
  have hr : (G.eval z).re = z.re ^ 3 - 3 / 400 * z.re - 3 / 32 := by
    rw [G_re, him]
    ring
  have hi : (G.eval z).im = 0 := by
    rw [G_im, him]
    ring
  have hlow : -47 / 500 ≤ (G.eval z).re := by
    rw [hr]
    nlinarith [mul_nonneg (sq_nonneg (z.re - 1 / 20)) (by linarith : (0 : ℝ) ≤ z.re + 1 / 10)]
  have hup : (G.eval z).re ≤ 253 / 8000 := by
    rw [hr]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 2 - z.re)
      (by positivity : (0 : ℝ) ≤ (z.re + 1 / 4) ^ 2 + 3 / 16)]
  have hsq : ‖G.eval z‖ ^ 2 < (2 * (187 / 2000)) ^ 2 := by
    rw [G_norm_sq, hi]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 187 / 1000 - (G.eval z).re)
      (by linarith : (0 : ℝ) < (G.eval z).re + 187 / 1000)]
  nlinarith [norm_nonneg (G.eval z)]

/-- `{|g| < μ}` lies in three disjoint open pieces: left of the line
`Re z = 1/20` and above the real axis, left of it and below, and right of it. -/
theorem sublevel_mu_trichotomy {z : ℂ} (hz : ‖G.eval z‖ < 187 / 2000) :
    (z.re < 1 / 20 ∧ 0 < z.im) ∨ (z.re < 1 / 20 ∧ z.im < 0) ∨ 1 / 20 < z.re := by
  rcases lt_trichotomy z.re (1 / 20) with h | h | h
  · rcases lt_trichotomy z.im 0 with h' | h' | h'
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    · exfalso
      have := real_axis_ge h' (by linarith)
      linarith
    · exact Or.inl ⟨h, h'⟩
  · exfalso
    have := barrier h
    linarith
  · exact Or.inr (Or.inr h)

/-- The vertical line `Re z = -1/20` through `c_*`, parametrised by height. -/
def vline (y : ℝ) : ℂ := ((-1 / 20 : ℝ) : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem vline_re (y : ℝ) : (vline y).re = -1 / 20 := by simp [vline]

@[simp] theorem vline_im (y : ℝ) : (vline y).im = y := by simp [vline]

theorem continuous_vline : Continuous vline := by
  unfold vline
  fun_prop

theorem vline_zero : vline 0 = -(1 / 20) := by
  unfold vline
  push_cast
  ring

/-- `K_μ` is the closed sublevel set at the least critical level `μ = 187/2000`;
`c_* = -1/20` lies in it. -/
theorem cstar_mem_sublevel_mu : (-(1 / 20) : ℂ) ∈ {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} :=
  le_of_eq norm_value_minus

/-- The line `Re z = 1/20` keeps the component of `K_μ` through `c_*` in the
half-plane `Re z < 1/20`. -/
theorem firstMergeComponent_subset :
    connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)) ⊆
      {z : ℂ | z.re < 1 / 20} :=
  connectedComponentIn_subset_of_cover cstar_mem_sublevel_mu
    (isOpen_lt Complex.continuous_re continuous_const)
    (isOpen_lt continuous_const Complex.continuous_re)
    (Set.disjoint_left.mpr fun z (h1 : z.re < 1 / 20) (h2 : 1 / 20 < z.re) => lt_asymm h1 h2)
    (fun z hz => by
      rcases lt_trichotomy z.re (1 / 20) with h | h | h
      · exact Or.inl h
      · exfalso
        have h1 := barrier h
        have h2 : ‖G.eval z‖ ≤ 187 / 2000 := hz
        linarith
      · exact Or.inr h)
    (by show (-(1 / 20 : ℂ)).re < 1 / 20; norm_num)

/-- A component of `{|g| < μ}` through a point of the upper-left piece stays in
that piece. -/
theorem component_subset_upperLeft {p : ℂ} (hp : ‖G.eval p‖ < 187 / 2000)
    (hpu : p.re < 1 / 20 ∧ 0 < p.im) :
    connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} p ⊆
      {z : ℂ | z.re < 1 / 20 ∧ 0 < z.im} :=
  connectedComponentIn_subset_of_cover (v := {z : ℂ | z.re < 1 / 20 ∧ z.im < 0} ∪
      {z : ℂ | 1 / 20 < z.re}) hp
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))
    (((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im continuous_const)).union
      (isOpen_lt continuous_const Complex.continuous_re))
    (Set.disjoint_left.mpr fun z h1 h2 => by
      rcases h2 with h2 | h2
      · exact lt_asymm h1.2 h2.2
      · exact lt_asymm h1.1 h2)
    (fun z hz => by
      rcases sublevel_mu_trichotomy hz with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    hpu

/-- A component of `{|g| < μ}` through a point of the lower-left piece stays in
that piece. -/
theorem component_subset_lowerLeft {p : ℂ} (hp : ‖G.eval p‖ < 187 / 2000)
    (hpu : p.re < 1 / 20 ∧ p.im < 0) :
    connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} p ⊆
      {z : ℂ | z.re < 1 / 20 ∧ z.im < 0} :=
  connectedComponentIn_subset_of_cover (v := {z : ℂ | z.re < 1 / 20 ∧ 0 < z.im} ∪
      {z : ℂ | 1 / 20 < z.re}) hp
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im continuous_const))
    (((isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)).union
      (isOpen_lt continuous_const Complex.continuous_re))
    (Set.disjoint_left.mpr fun z h1 h2 => by
      rcases h2 with h2 | h2
      · exact lt_asymm h1.2 h2.2
      · exact lt_asymm h1.1 h2)
    (fun z hz => by
      rcases sublevel_mu_trichotomy hz with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h))
    hpu

/-- A component of `{|g| < μ}` through a point right of the line `Re z = 1/20`
stays right of it. -/
theorem component_subset_right {p : ℂ} (hp : ‖G.eval p‖ < 187 / 2000)
    (hpu : 1 / 20 < p.re) :
    connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} p ⊆ {z : ℂ | 1 / 20 < z.re} :=
  connectedComponentIn_subset_of_cover (v := {z : ℂ | z.re < 1 / 20}) hp
    (isOpen_lt continuous_const Complex.continuous_re)
    (isOpen_lt Complex.continuous_re continuous_const)
    (Set.disjoint_left.mpr fun z (h1 : 1 / 20 < z.re) (h2 : z.re < 1 / 20) => lt_asymm h1 h2)
    (fun z hz => by
      rcases sublevel_mu_trichotomy hz with h | h | h
      · exact Or.inr h.1
      · exact Or.inr h.1
      · exact Or.inl h)
    hpu

/-- The component of `{|g| < μ}` through `vline y₀` lies in the component of
`K_μ` through `c_*`, whenever the vertical segment from `c_*` to `vline y₀`
has `y^2 ≤ 1/25`. -/
theorem vline_component_subset_firstMerge {y₀ : ℝ} (hy₀ : y₀ ^ 2 = 1 / 25) :
    connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} (vline y₀) ⊆
      connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)) := by
  have hlt : ‖G.eval (vline y₀)‖ < 187 / 2000 :=
    vertical_end_lt (vline_re y₀) (by rw [vline_im]; exact hy₀)
  have hS : IsPreconnected (vline '' uIcc 0 y₀) :=
    isPreconnected_uIcc.image _ continuous_vline.continuousOn
  have hpS : vline y₀ ∈ vline '' uIcc 0 y₀ := ⟨y₀, right_mem_uIcc, rfl⟩
  have hpU : vline y₀ ∈
      connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} (vline y₀) :=
    mem_connectedComponentIn hlt
  have hunion := IsPreconnected.union (vline y₀) hpS hpU hS isPreconnected_connectedComponentIn
  have hc : (-(1 / 20) : ℂ) ∈ vline '' uIcc 0 y₀ ∪
      connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} (vline y₀) :=
    Or.inl ⟨0, left_mem_uIcc, vline_zero⟩
  have hsub : vline '' uIcc 0 y₀ ∪
      connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} (vline y₀) ⊆
      {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} := by
    rintro z (⟨y, hy, rfl⟩ | hz)
    · refine vertical_le (vline_re y) ?_
      rw [vline_im]
      rcases Set.mem_uIcc.mp hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · nlinarith
      · nlinarith
    · have h := connectedComponentIn_subset _ _ hz
      have h' : ‖G.eval z‖ < 187 / 2000 := h
      exact le_of_lt h'
  exact subset_union_right.trans (hunion.subset_connectedComponentIn hc hsub)

open scoped Classical in
/-- **The three roots.**  `g` has a root `a` in the component of `{|g| < μ}`
through `-1/20 + i/5` (upper left), a root `b` in the one through `-1/20 - i/5`
(lower left) and a root `r` in the one through `1/2` (right of `Re z = 1/20`),
and these are all the roots of `g`, each simple. -/
theorem three_roots : ∃ a b r : ℂ,
    G.roots = {a, b, r} ∧
    a ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} (vline (1 / 5)) ∧
    (a.re < 1 / 20 ∧ 0 < a.im) ∧
    b ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} (vline (-(1 / 5))) ∧
    (b.re < 1 / 20 ∧ b.im < 0) ∧
    r ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} (1 / 2) ∧
    1 / 20 < r.re := by
  have hup : ‖G.eval (vline (1 / 5))‖ < 187 / 2000 :=
    vertical_end_lt (vline_re _) (by rw [vline_im]; norm_num)
  have hdown : ‖G.eval (vline (-(1 / 5)))‖ < 187 / 2000 :=
    vertical_end_lt (vline_re _) (by rw [vline_im]; norm_num)
  obtain ⟨a, haU, ha0⟩ := exists_zero_mem_connectedComponentIn_sublevel G G_degree_pos hup
  obtain ⟨b, hbU, hb0⟩ := exists_zero_mem_connectedComponentIn_sublevel G G_degree_pos hdown
  obtain ⟨r, hrU, hr0⟩ := exists_zero_mem_connectedComponentIn_sublevel G G_degree_pos half_lt
  have ha : a.re < 1 / 20 ∧ 0 < a.im :=
    component_subset_upperLeft hup (by simp; norm_num) haU
  have hb : b.re < 1 / 20 ∧ b.im < 0 :=
    component_subset_lowerLeft hdown (by simp; norm_num) hbU
  have hr : 1 / 20 < r.re :=
    component_subset_right half_lt (by norm_num) hrU
  have hab : a ≠ b := fun h => by rw [h] at ha; exact lt_asymm ha.2 hb.2
  have har : a ≠ r := fun h => by rw [h] at ha; exact lt_asymm ha.1 hr
  have hbr : b ≠ r := fun h => by rw [h] at hb; exact lt_asymm hb.1 hr
  have hG0 : G ≠ 0 := G_monic_and_degree.1.ne_zero
  have hnodup : ({a, b, r} : Multiset ℂ).Nodup := by
    simp [hab, har, hbr]
  have hle : ({a, b, r} : Multiset ℂ) ≤ G.roots := by
    rw [Multiset.le_iff_subset hnodup]
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rw [mem_roots hG0, IsRoot.def]
    rcases hx with rfl | rfl | rfl
    · exact ha0
    · exact hb0
    · exact hr0
  have hcard : Multiset.card G.roots = 3 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, G_monic_and_degree.2]
  have hroots : ({a, b, r} : Multiset ℂ) = G.roots :=
    Multiset.eq_of_le_of_card_le hle (by rw [hcard]; simp)
  exact ⟨a, b, r, hroots.symm, haU, ha, hbU, hb, hrU, hr⟩

/-- The real segment `[-1/20, 1/2]` joins `c_*` to `1/2` inside `{|g| < 2μ}`. -/
theorem real_segment_subset :
    (fun x : ℝ => (x : ℂ)) '' Icc (-1 / 20) (1 / 2) ⊆
      {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} := by
  rintro _ ⟨x, hx, rfl⟩
  exact real_segment_lt (by simp) (by simpa using hx.1) (by simpa using hx.2)

open scoped Classical in
/-- **The merger clause of `res:arity-not-capacity`, with no hypotheses.**  The
roots of `g`, with multiplicity, in the component of `K_μ` containing
`c_* = -1/20` are exactly two distinct roots `a` and `b`, so `k₀ = 2`; `a` and
`b` lie in different components of `{|g| < μ}`, so the merger at level `μ`
joins two root components; and both lie in the component of `{|g| < 2μ}`
containing `c_*`, which is the whole of `{|g| < 2μ}`. -/
theorem arity_first_merger :
    (∃ a b : ℂ, a ≠ b ∧
      G.roots.filter
          (· ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)))
        = {a, b} ∧
      b ∉ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} a ∧
      a ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) ∧
      b ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20))) ∧
    Multiset.card (G.roots.filter
        (· ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)))) = 2 ∧
    connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) =
      {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} := by
  obtain ⟨a, b, r, hroots, haU, ha, hbU, hb, hrU, hr⟩ := three_roots
  -- the component of `K_μ` through `c_*`
  have haK : a ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)) :=
    vline_component_subset_firstMerge (by norm_num) haU
  have hbK : b ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)) :=
    vline_component_subset_firstMerge (by norm_num) hbU
  have hrK : r ∉ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)) :=
    fun h => lt_asymm (firstMergeComponent_subset h) hr
  have hfilter : G.roots.filter
      (· ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20))) =
        {a, b} := by
    rw [hroots, Multiset.insert_eq_cons, Multiset.insert_eq_cons,
      Multiset.filter_cons_of_pos _ haK, Multiset.filter_cons_of_pos _ hbK,
      Multiset.filter_singleton, if_neg hrK]
    rfl
  -- two root components below the merger level
  have hsep : b ∉ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} a := by
    rw [← connectedComponentIn_eq haU]
    intro h
    have := component_subset_upperLeft
      (vertical_end_lt (vline_re _) (by rw [vline_im]; norm_num))
      (by simp; norm_num) h
    exact lt_asymm this.2 hb.2
  -- the component at level `2μ`
  have hKC : connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)) ⊆
      connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn cstar_mem_sublevel_mu)
      (fun z hz => by
        have h0 := connectedComponentIn_subset _ _ hz
        have h1 : ‖G.eval z‖ ≤ 187 / 2000 := h0
        show ‖G.eval z‖ < 2 * (187 / 2000)
        linarith)
  have hR : IsPreconnected ((fun x : ℝ => (x : ℂ)) '' Icc (-1 / 20) (1 / 2)) :=
    isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have hcR : (-(1 / 20) : ℂ) ∈ (fun x : ℝ => (x : ℂ)) '' Icc (-1 / 20) (1 / 2) :=
    ⟨-1 / 20, ⟨le_rfl, by norm_num⟩, by push_cast; ring⟩
  have hhalfR : (1 / 2 : ℂ) ∈ (fun x : ℝ => (x : ℂ)) '' Icc (-1 / 20) (1 / 2) :=
    ⟨1 / 2, ⟨by norm_num, le_rfl⟩, by push_cast; ring⟩
  have hRU : IsPreconnected ((fun x : ℝ => (x : ℂ)) '' Icc (-1 / 20) (1 / 2) ∪
      connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} (1 / 2)) :=
    IsPreconnected.union (1 / 2 : ℂ) hhalfR (mem_connectedComponentIn half_lt) hR
      isPreconnected_connectedComponentIn
  have hRUC : (fun x : ℝ => (x : ℂ)) '' Icc (-1 / 20) (1 / 2) ∪
      connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} (1 / 2) ⊆
      connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) :=
    hRU.subset_connectedComponentIn (Or.inl hcR)
      (union_subset real_segment_subset (fun z hz => by
        have h0 := connectedComponentIn_subset _ _ hz
        have h1 : ‖G.eval z‖ < 187 / 2000 := h0
        show ‖G.eval z‖ < 2 * (187 / 2000)
        linarith))
  have haC := hKC haK
  have hbC := hKC hbK
  have hrC := hRUC (Or.inr hrU)
  have hG0 : G ≠ 0 := G_monic_and_degree.1.ne_zero
  have hCeq : connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) =
      {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} := by
    apply Subset.antisymm (connectedComponentIn_subset _ _)
    intro z hz
    obtain ⟨ρ, hρV, hρ0⟩ := exists_zero_mem_connectedComponentIn_sublevel G G_degree_pos hz
    have hρroots : ρ ∈ G.roots := (mem_roots hG0).mpr hρ0
    rw [hroots] at hρroots
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hρroots
    have hρC : ρ ∈
        connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) := by
      rcases hρroots with rfl | rfl | rfl
      · exact haC
      · exact hbC
      · exact hrC
    rw [connectedComponentIn_eq hρC, ← connectedComponentIn_eq hρV]
    exact mem_connectedComponentIn hz
  refine ⟨⟨a, b, fun h => ?_, hfilter, hsep, haC, hbC⟩, ?_, hCeq⟩
  · rw [h] at ha
    exact lt_asymm ha.2 hb.2
  · rw [hfilter]
    rfl

/-- **The component at level `2μ` is the whole filled lemniscate.**  The
closure of the component of `{|g| < 2μ}` containing `c_*` is `{|g| ≤ 2μ}`. -/
theorem closure_doubleLevelComponent :
    closure (connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20))) =
      {z : ℂ | ‖G.eval z‖ ≤ 2 * (187 / 2000)} := by
  rw [arity_first_merger.2.2]
  exact closure_polynomial_sublevel_lt G G_degree_pos (by norm_num)

open scoped Classical in
/-- **`res:arity-not-capacity`**, modulo the named input
`LemniscateTransfiniteDiameter`.  For `g(z) = z^3 - (3/400)z - 3/32`: `g` is a
monic cubic with every root in the open unit disc; `μ = 187/2000` is its least
critical-value modulus and `μ ≤ 1/2`; `c_* = -1/20` is its only critical point
at level `μ`; the roots of `g`, with multiplicity, in the component of
`K_μ = {|g| ≤ μ}` containing `c_*` are exactly two distinct roots `a` and `b`,
which lie in different components of `{|g| < μ}` (the first merger joins two
root components) and in the component `C` of `{|g| < 2μ}` containing `c_*`;
so `k₀ = 2`; and `C` has normalised capacity
`transfiniteDiameter (closure C) / (2μ)^{1/3} = 1`. -/
theorem arity_not_capacity (hLTD : LemniscateTransfiniteDiameter) :
    G.Monic ∧ G.natDegree = 3 ∧
      PaperAnalyticTargets.RootsInOpenUnitDisc G ∧
      PaperAnalyticTargets.CriticalMinimum G (187 / 2000 : ℝ) ∧
      (187 / 2000 : ℝ) ≤ 1 / 2 ∧
      (∀ c : ℂ, G.derivative.eval c = 0 ∧ ‖G.eval c‖ = 187 / 2000 ↔ c = -(1 / 20)) ∧
      (∃ a b : ℂ, a ≠ b ∧
        G.roots.filter
            (· ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)))
          = {a, b} ∧
        b ∉ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} a ∧
        a ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) ∧
        b ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20))) ∧
      Multiset.card (G.roots.filter
          (· ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20))))
        = 2 ∧
      transfiniteDiameter
          (closure (connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20))))
        / (2 * (187 / 2000 : ℝ)) ^ ((1 : ℝ) / 3) = 1 := by
  obtain ⟨hmerge, hk₀, -⟩ := arity_first_merger
  refine ⟨G_monic_and_degree.1, G_monic_and_degree.2, fun _ => arity_roots_in_open_disc,
    arity_criticalMinimum, arity_mu_le_half, ?_, hmerge, hk₀, ?_⟩
  · intro c
    constructor
    · rintro ⟨hc, hnorm⟩
      rcases (all_critical_points c).mp hc with rfl | rfl
      · rw [norm_value_plus] at hnorm
        norm_num at hnorm
      · rfl
    · rintro rfl
      exact ⟨(all_critical_points _).mpr (Or.inr rfl), norm_value_minus⟩
  · rw [closure_doubleLevelComponent,
      hLTD G (2 * (187 / 2000)) G_monic_and_degree.1 (by rw [G_monic_and_degree.2]; norm_num)
        (by norm_num), G_monic_and_degree.2]
    push_cast
    exact div_self (Real.rpow_pos_of_pos (by norm_num) _).ne'

end Arity

#print axioms isBounded_polynomial_sublevel_lt
#print axioms exists_zero_mem_connectedComponentIn_sublevel
#print axioms closure_polynomial_sublevel_lt
#print axioms Arity.three_roots
#print axioms Arity.arity_first_merger
#print axioms Arity.closure_doubleLevelComponent
#print axioms Arity.arity_not_capacity

end ErdosProblems.Erdos1041.PaperCompleteR21
