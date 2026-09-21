import ErdosProblems.Erdos1041.SharpCollinearChebyshev
import ErdosProblems.Erdos1041.PaperCurveAssembly

/-!
# Erdős 1041: the sharp Chebyshev bound for collinear roots, with sharpness

Paper-form restatement of

* `res:sharp-collinear-root-diameter`
  (`paper/1041/erdos-1041-lemniscate-newton-flow.tex`, line 1155),
* `thm:sharp-collinear-diameter`
  (`paper/reasoning-parts/erdos1041/core.tex`, line 1715),
* `cor:collinear-erdos-1041`
  (`paper/reasoning-parts/erdos1041/core.tex`, line 1769).

A monic complex polynomial of degree `n` whose zero occurrences are collinear is
written here in its factored form `∏ k, (X - C (base + dir * y k))` with
`‖dir‖ = 1` and `y : Fin n → ℝ`: that is exactly "monic of degree `n` with all
zero occurrences on one line", the line being `base + dir * ℝ`.  The diameter
`D` of the zero occurrences is carried as the hypothesis that `D` is the
greatest pairwise distance between zero occurrences.

The existing tree modules `SharpCollinearAlternation` and
`SharpCollinearChebyshev` supply the alternation/Chebyshev kernel: for a monic
real `p` of degree `m + 2` vanishing at `±1` and alternating in sign at `m + 1`
ordered interior points, one of those points has `|p| ≤ comparisonBound (m+2)`.
This file supplies everything the paper's proof needs around that kernel:

* the rigid normalisation (translation, rotation, scaling by `R = D/2`) and the
  transport identity `‖f (base + dir * s)‖ = R ^ n * |q ((s - mid)/R)|`;
* the existence of a maximiser of `|q|` in each root gap, and the fact that it
  is interior;
* the sign alternation of those gap maxima, proved directly from the product
  form of `q`;
* the upgrade from the kernel's pointwise conclusion to a bound on the WHOLE
  selected segment, which is where "`c i` is the gap maximum" is used;
* the repeated-zero (constant path) case;
* the sharpness clauses: the scaled Chebyshev configuration, its extreme zeros
  at distance `D`, a point of every adjacent gap at which the bound is attained
  with equality, and hence that no smaller constant works in any degree.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Finset Set
open ErdosProblems.Erdos1041.SharpCollinearChebyshev

/-! ### The constant `C_n = 1 / (2^(n-1) cos^n (π/(2n)))` -/

/-- The tree's `comparisonBound` is the paper's `C_n`. -/
theorem comparisonBound_eq_inv {n : ℕ} (hn : 2 ≤ n) :
    comparisonBound n = (2 ^ (n - 1) * endpointScale n ^ n)⁻¹ := by
  have hr : 0 < endpointScale n := endpointScale_pos hn
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n :=
    mul_pos (by positivity) (pow_pos (inv_pos.mpr hr) n)
  show |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
      = (2 ^ (n - 1) * endpointScale n ^ n)⁻¹
  rw [abs_of_pos hpos, inv_pow, mul_inv]

/-- `comparisonBound n` written exactly as the paper's `C_n`. -/
theorem comparisonBound_eq {n : ℕ} (hn : 2 ≤ n) :
    comparisonBound n = 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) := by
  rw [comparisonBound_eq_inv hn, one_div]
  rfl

theorem comparisonBound_pos {n : ℕ} (hn : 2 ≤ n) : 0 < comparisonBound n := by
  have hr : 0 < endpointScale n := endpointScale_pos hn
  rw [comparisonBound_eq_inv hn]
  have : (0 : ℝ) < 2 ^ (n - 1) * endpointScale n ^ n :=
    mul_pos (by positivity) (pow_pos hr n)
  exact inv_pos.mpr this

theorem comparisonBound_le_one {n : ℕ} (hn : 2 ≤ n) : comparisonBound n ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hr : 0 < endpointScale (k + 2) := endpointScale_pos hn
  set t : ℝ := Real.sqrt 2 with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg 2
  have ht2 : t ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht1 : (1 : ℝ) ≤ t := by nlinarith
  -- `cos (π / (2 (k+2))) ≥ cos (π/4) = √2 / 2`
  have hangle : Real.pi / (2 * ((k : ℝ) + 2)) ≤ Real.pi / 4 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hpi := Real.pi_pos
    have key : Real.pi / 4 - Real.pi / (2 * ((k : ℝ) + 2))
        = Real.pi * (2 * ((k : ℝ) + 2) - 4) / (4 * (2 * ((k : ℝ) + 2))) := by
      field_simp
    have hnn : (0 : ℝ) ≤ Real.pi * (2 * ((k : ℝ) + 2) - 4) / (4 * (2 * ((k : ℝ) + 2))) :=
      div_nonneg (by nlinarith) (by linarith)
    rw [← key] at hnn
    linarith
  have hcos : t / 2 ≤ endpointScale (k + 2) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / (2 * ((k : ℝ) + 2)))
      (y := Real.pi / 4) (by positivity) (by linarith [Real.pi_pos]) hangle
    rw [Real.cos_pi_div_four] at h
    have hcast : ((k : ℝ) + 2) = ((k + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at h
    exact h
  -- `2^(k+1) * (t/2)^(k+2) = t^k ≥ 1`
  have hkey : (2 : ℝ) ^ (k + 1) * (t / 2) ^ (k + 2) = t ^ k := by
    rw [div_pow, pow_add, pow_add, pow_add, ht2]
    have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    field_simp
  have hA : (1 : ℝ) ≤ 2 ^ (k + 1) * endpointScale (k + 2) ^ (k + 2) := by
    have hstep : (t / 2) ^ (k + 2) ≤ endpointScale (k + 2) ^ (k + 2) :=
      pow_le_pow_left₀ (by positivity) hcos (k + 2)
    have : (2 : ℝ) ^ (k + 1) * (t / 2) ^ (k + 2)
        ≤ 2 ^ (k + 1) * endpointScale (k + 2) ^ (k + 2) :=
      mul_le_mul_of_nonneg_left hstep (by positivity)
    have h1 : (1 : ℝ) ≤ t ^ k := one_le_pow₀ ht1
    linarith [hkey ▸ this]
  rw [comparisonBound_eq_inv hn]
  have hApos : (0 : ℝ) < 2 ^ (k + 1) * endpointScale (k + 2) ^ (k + 2) :=
    mul_pos (by positivity) (pow_pos hr (k + 2))
  have hsimp : (k + 2) - 1 = k + 1 := by omega
  rw [hsimp]
  rw [inv_le_one₀ hApos]
  exact hA

/-! ### A monic product of linear factors -/

theorem isMonicOfDegree_prod_X_sub_C {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsMonicOfDegree (∏ i ∈ s, (X - C (a i))) s.card := by
  refine ⟨?_, monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (a i)⟩
  rw [natDegree_prod _ _ fun i _ => (monic_X_sub_C (a i)).ne_zero]
  simp

/-! ### Sign alternation between consecutive root gaps -/

/-- Two points separated by exactly one root `Y t` of `∏ j, (X - Y j)`, with all
other roots outside the interval they span, give values of opposite sign. -/
theorem prod_pair_neg {N : ℕ} (Y : Fin N → ℝ) (t : Fin N) {x x' : ℝ}
    (hxt : x < Y t) (hx't : Y t < x')
    (hlow : ∀ j : Fin N, j < t → Y j < x)
    (hhigh' : ∀ j : Fin N, t < j → x' < Y j) :
    (∏ j, (x - Y j)) * (∏ j, (x' - Y j)) < 0 := by
  classical
  rw [← Finset.prod_mul_distrib, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t)]
  apply mul_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  · apply Finset.prod_pos
    intro j hj
    have hjt : j ≠ t := (Finset.mem_erase.mp hj).1
    rcases lt_or_gt_of_ne hjt with h | h
    · have h1 : Y j < x := hlow j h
      have h2 : Y j < x' := by linarith
      exact mul_pos (by linarith) (by linarith)
    · have h1 : x' < Y j := hhigh' j h
      have h2 : x < Y j := by linarith
      exact mul_pos_of_neg_of_neg (by linarith) (by linarith)

/-! ### Gap maxima -/

/-- In each gap between consecutive roots, `|∏ j, (· - Y j)|` attains a maximum,
and that maximum is attained strictly inside the gap. -/
theorem exists_gap_max {m : ℕ} (Y : Fin (m + 2) → ℝ) (hY : StrictMono Y)
    (i : Fin (m + 1)) :
    ∃ c, c ∈ Ioo (Y i.castSucc) (Y i.succ) ∧
      ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
        |∏ j, (x - Y j)| ≤ |∏ j, (c - Y j)| := by
  classical
  have hlt : Y i.castSucc < Y i.succ := hY i.castSucc_lt_succ
  have hcont : Continuous fun x : ℝ => |∏ j, (x - Y j)| := by
    apply Continuous.abs
    exact continuous_finset_prod _ fun j _ => continuous_id.sub continuous_const
  obtain ⟨c, hcmem, hcmax'⟩ :=
    (isCompact_Icc (a := Y i.castSucc) (b := Y i.succ)).exists_isMaxOn
      (Set.nonempty_Icc.mpr hlt.le) hcont.continuousOn
  have hcmax : ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ |∏ j, (c - Y j)| := isMaxOn_iff.mp hcmax'
  -- interior points are not roots
  have hne : ∀ x : ℝ, Y i.castSucc < x → x < Y i.succ → (∏ j, (x - Y j)) ≠ 0 := by
    intro x h1 h2
    refine Finset.prod_ne_zero_iff.mpr fun j _ => sub_ne_zero.mpr ?_
    rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with h | h
    · have hjge : i.succ ≤ j := by
        rw [Fin.le_def, Fin.val_succ]; omega
      have := hY.monotone hjge
      intro hEq; rw [← hEq] at this; linarith
    · have hjle : j ≤ i.castSucc := by
        rw [Fin.le_def, Fin.val_castSucc]; omega
      have := hY.monotone hjle
      intro hEq; rw [← hEq] at this; linarith
  -- the endpoints are roots
  have hzero : ∀ a : Fin (m + 2), (∏ j, (Y a - Y j)) = 0 := fun a =>
    Finset.prod_eq_zero (Finset.mem_univ a) (by ring)
  set mid : ℝ := (Y i.castSucc + Y i.succ) / 2 with hmid
  have hmid1 : Y i.castSucc < mid := by rw [hmid]; linarith
  have hmid2 : mid < Y i.succ := by rw [hmid]; linarith
  have hmidpos : 0 < |∏ j, (mid - Y j)| := abs_pos.mpr (hne mid hmid1 hmid2)
  have hcpos : 0 < |∏ j, (c - Y j)| :=
    lt_of_lt_of_le hmidpos (hcmax mid ⟨hmid1.le, hmid2.le⟩)
  refine ⟨c, ⟨?_, ?_⟩, hcmax⟩
  · refine lt_of_le_of_ne hcmem.1 (fun hEq => ?_)
    rw [← hEq, hzero i.castSucc] at hcpos
    simp at hcpos
  · refine lt_of_le_of_ne hcmem.2 (fun hEq => ?_)
    rw [hEq, hzero i.succ] at hcpos
    simp at hcpos

/-! ### The normalised core: a whole gap below `C_n` -/

/-- **The normalised sharp collinear bound.**  If `Y` is a strictly increasing
list of `m + 2` reals with `Y 0 = -1` and `Y (last) = 1`, then the monic
polynomial `∏ j, (X - Y j)` is bounded by `C_{m+2}` on ALL of one gap between
consecutive roots, not merely at one interior point. -/
theorem exists_gap_le_comparisonBound {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1) (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ comparisonBound (m + 2) := by
  classical
  have hcast0 : ((0 : Fin (m + 1)).castSucc) = (0 : Fin (m + 2)) :=
    Fin.val_injective (by simp)
  have hsucclast : ((Fin.last m).succ) = Fin.last (m + 1) :=
    Fin.val_injective (by simp)
  set q : ℝ[X] := ∏ j, (X - C (Y j)) with hqdef
  have hqeval : ∀ x : ℝ, q.eval x = ∏ j, (x - Y j) := by
    intro x; rw [hqdef]; simp [eval_prod]
  have hqmonic : q.IsMonicOfDegree (m + 2) := by
    have h := isMonicOfDegree_prod_X_sub_C (R := ℝ) (Finset.univ : Finset (Fin (m + 2))) Y
    rw [hqdef]
    simpa using h
  choose c hcIoo hcmax using fun i : Fin (m + 1) => exists_gap_max Y hY i
  -- basic order facts about the chosen points
  have hlo : ∀ i : Fin (m + 1), Y i.castSucc < c i := fun i => (hcIoo i).1
  have hhi : ∀ i : Fin (m + 1), c i < Y i.succ := fun i => (hcIoo i).2
  have hcSM : StrictMono c := by
    intro i i' h
    have hvi : (i : ℕ) < (i' : ℕ) := Fin.lt_def.mp h
    have h1 : i.succ ≤ i'.castSucc := by
      rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; omega
    exact lt_of_lt_of_le (hhi i) (le_trans (hY.monotone h1) (hlo i').le)
  have ha : (-1 : ℝ) < c 0 := by
    have := hlo 0
    rwa [hcast0, hY0] at this
  have hb : c (Fin.last m) < 1 := by
    have := hhi (Fin.last m)
    rwa [hsucclast, hY1] at this
  have hmemlow : ∀ i : Fin (m + 1), Y 0 ≤ Y i.castSucc := fun i =>
    hY.monotone (by rw [Fin.le_def]; simp)
  have hmemhigh : ∀ i : Fin (m + 1), Y i.succ ≤ Y (Fin.last (m + 1)) := fun i =>
    hY.monotone (by rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_last]; omega)
  have hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1 := by
    intro i
    rw [abs_le]
    constructor
    · have h1 := hmemlow i
      have h2 := hlo i
      rw [hY0] at h1; linarith
    · have h1 := hmemhigh i
      have h2 := hhi i
      rw [hY1] at h1; linarith
  have hpa : q.eval (-1) = 0 := by
    rw [hqeval, ← hY0]
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (m + 2))) (by ring)
  have hpb : q.eval 1 = 0 := by
    rw [hqeval, ← hY1]
    exact Finset.prod_eq_zero (Finset.mem_univ (Fin.last (m + 1))) (by ring)
  have hpalt : ∀ i : Fin m, q.eval (c i.castSucc) * q.eval (c i.succ) < 0 := by
    intro i
    rw [hqeval, hqeval]
    refine prod_pair_neg Y ((i.castSucc : Fin (m + 1)).succ) ?_ ?_ ?_ ?_
    · exact hhi i.castSucc
    · have h := hlo i.succ
      have heq : ((i.succ : Fin (m + 1)).castSucc) = ((i.castSucc : Fin (m + 1)).succ) :=
        Fin.val_injective (by simp)
      rwa [heq] at h
    · intro j hj
      have hjv := Fin.lt_def.mp hj
      simp only [Fin.val_succ, Fin.val_castSucc] at hjv
      have hjle : j ≤ (i.castSucc : Fin (m + 1)).castSucc := by
        rw [Fin.le_def, Fin.val_castSucc, Fin.val_castSucc]; omega
      exact lt_of_le_of_lt (hY.monotone hjle) (hlo i.castSucc)
    · intro j hj
      have hjv := Fin.lt_def.mp hj
      simp only [Fin.val_succ, Fin.val_castSucc] at hjv
      have hjge : (i.succ : Fin (m + 1)).succ ≤ j := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_succ]; omega
      exact lt_of_lt_of_le (hhi i.succ) (hY.monotone hjge)
  obtain ⟨i, hi⟩ :=
    exists_peak_le_comparisonBound hqmonic hcSM ha hb hpa hpb hpalt hc_mem
  refine ⟨i, fun x hx => ?_⟩
  calc |∏ j, (x - Y j)| ≤ |∏ j, (c i - Y j)| := hcmax i x hx
    _ = |q.eval (c i)| := by rw [hqeval]
    _ ≤ comparisonBound (m + 2) := hi

/-! ### Transport between the root line and `ℝ` -/

theorem dist_collinear (base dir : ℂ) (hdir : ‖dir‖ = 1) (a b : ℝ) :
    dist (base + dir * (a : ℂ)) (base + dir * (b : ℂ)) = |a - b| := by
  rw [dist_eq_norm]
  have h : base + dir * (a : ℂ) - (base + dir * (b : ℂ)) = dir * ((a - b : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, norm_mul, hdir, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_eval_collinear {n : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1) (y : Fin n → ℝ)
    (f : ℂ[X]) (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ)))) (s : ℝ) :
    ‖f.eval (base + dir * (s : ℂ))‖ = |∏ k, (s - y k)| := by
  subst hf
  rw [eval_prod]
  have hfac : ∀ k : Fin n,
      (X - C (base + dir * (y k : ℂ))).eval (base + dir * (s : ℂ))
        = dir * ((s - y k : ℝ) : ℂ) := by
    intro k; simp only [eval_sub, eval_X, eval_C]; push_cast; ring
  rw [Finset.prod_congr rfl fun k _ => hfac k, norm_prod]
  rw [Finset.abs_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [norm_mul, hdir, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem segment_collinear {base dir : ℂ} {a b : ℝ} {z : ℂ}
    (hz : z ∈ segment ℝ (base + dir * (a : ℂ)) (base + dir * (b : ℂ))) :
    ∃ s ∈ Icc (min a b) (max a b), z = base + dir * (s : ℂ) := by
  obtain ⟨p, r, hp, hr, hpr, hzeq⟩ := hz
  refine ⟨p * a + r * b, ⟨?_, ?_⟩, ?_⟩
  · have h1 : min a b ≤ a := min_le_left a b
    have h2 : min a b ≤ b := min_le_right a b
    have e1 : p * min a b ≤ p * a := mul_le_mul_of_nonneg_left h1 hp
    have e2 : r * min a b ≤ r * b := mul_le_mul_of_nonneg_left h2 hr
    have e3 : p * min a b + r * min a b = min a b := by rw [← add_mul, hpr, one_mul]
    linarith
  · have h1 : a ≤ max a b := le_max_left a b
    have h2 : b ≤ max a b := le_max_right a b
    have e1 : p * a ≤ p * max a b := mul_le_mul_of_nonneg_left h1 hp
    have e2 : r * b ≤ r * max a b := mul_le_mul_of_nonneg_left h2 hr
    have e3 : p * max a b + r * max a b = max a b := by rw [← add_mul, hpr, one_mul]
    linarith
  · rw [← hzeq]
    simp only [Complex.real_smul]
    push_cast
    have : (p : ℂ) + (r : ℂ) = 1 := by
      rw [← Complex.ofReal_add, hpr]; norm_num
    linear_combination base * this

/-- The greatest pairwise distance between the zero occurrences exists. -/
theorem exists_isGreatest_dist {n : ℕ} (hn : 0 < n) (base dir : ℂ) (y : Fin n → ℝ) :
    ∃ D : ℝ, IsGreatest {d : ℝ | ∃ j k : Fin n,
      d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D := by
  classical
  have hne : (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  set g : Fin n × Fin n → ℝ :=
    fun p => dist (base + dir * (y p.1 : ℂ)) (base + dir * (y p.2 : ℂ)) with hg
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' hne g
  refine ⟨g p, ⟨p.1, p.2, rfl⟩, ?_⟩
  rintro d ⟨j, k, rfl⟩
  rw [← hp]
  exact Finset.le_sup' g (Finset.mem_univ (j, k))

/-! ### The sharp collinear root-diameter theorem -/

/-- **Sharp collinear root-diameter bound**
(`res:sharp-collinear-root-diameter`, `thm:sharp-collinear-diameter`).

`f` is monic of degree `n ≥ 2` with all its zero occurrences on the line
`base + dir * ℝ` (`‖dir‖ = 1`), at the real coordinates `y k`; `D` is the
diameter of the zero occurrences, i.e. the greatest distance between two of
them.  Then two ADJACENT zero occurrences — no zero occurrence lies strictly
between them — are joined by their straight segment, whose length is at most
`D`, and on the WHOLE of which

`|f| ≤ C_n (D/2)^n`,  `C_n = 1 / (2^(n-1) cos^n (π/(2n)))`. -/
theorem sharp_collinear_root_diameter {n : ℕ} (hn : 2 ≤ n)
    (base dir : ℂ) (hdir : ‖dir‖ = 1) (y : Fin n → ℝ) (f : ℂ[X])
    (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ)))) (D : ℝ)
    (hD : IsGreatest {d : ℝ | ∃ j k : Fin n,
        d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D) :
    ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
      (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
      dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
      ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
        ‖f.eval z‖
          ≤ 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) * (D / 2) ^ n := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [← comparisonBound_eq hn]
  have hCpos : 0 < comparisonBound (m + 2) := comparisonBound_pos hn
  have hDnn : (0 : ℝ) ≤ D :=
    hD.2 (show (0 : ℝ) ∈ _ from ⟨0, 0, by simp⟩)
  by_cases hinj : Function.Injective y
  · -- distinct zeros: the Chebyshev comparison
    obtain ⟨w, hwSM, hwrange⟩ :
        ∃ w : Fin (m + 2) → ℝ, StrictMono w ∧ Set.range w = Set.range y := by
      have hcard : (Finset.image y Finset.univ).card = m + 2 := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      refine ⟨(Finset.image y Finset.univ).orderEmbOfFin hcard,
        OrderEmbedding.strictMono _, ?_⟩
      rw [Finset.range_orderEmbOfFin, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hwinj : Function.Injective w := hwSM.injective
    have hwy : ∀ a : Fin (m + 2), ∃ l, y l = w a := by
      intro a
      have h : w a ∈ Set.range y := by rw [← hwrange]; exact Set.mem_range_self a
      exact h
    have hyw : ∀ l : Fin (m + 2), ∃ a, y l = w a := by
      intro l
      have h : y l ∈ Set.range w := by rw [hwrange]; exact Set.mem_range_self l
      obtain ⟨a, ha⟩ := h
      exact ⟨a, ha.symm⟩
    have hw0le : ∀ l, w 0 ≤ y l := by
      intro l; obtain ⟨a, ha⟩ := hyw l; rw [ha]; exact hwSM.monotone (Fin.zero_le a)
    have hwlastge : ∀ l, y l ≤ w (Fin.last (m + 1)) := by
      intro l; obtain ⟨a, ha⟩ := hyw l; rw [ha]; exact hwSM.monotone (Fin.le_last a)
    have hwlt : w 0 < w (Fin.last (m + 1)) :=
      hwSM (by rw [Fin.lt_def]; simp only [Fin.val_zero, Fin.val_last]; omega)
    have hne : w (Fin.last (m + 1)) - w 0 ≠ 0 := ne_of_gt (sub_pos.mpr hwlt)
    have hDeq : D = w (Fin.last (m + 1)) - w 0 := by
      refine hD.unique ⟨?_, ?_⟩
      · obtain ⟨l1, hl1⟩ := hwy (Fin.last (m + 1))
        obtain ⟨l0, hl0⟩ := hwy 0
        exact ⟨l1, l0, by
          rw [dist_collinear _ _ hdir, hl1, hl0, abs_of_nonneg (by linarith)]⟩
      · rintro d ⟨j, k, rfl⟩
        rw [dist_collinear _ _ hdir, abs_le]
        constructor
        · linarith [hwlastge k, hw0le j]
        · linarith [hwlastge j, hw0le k]
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (w (Fin.last (m + 1)) - w 0) / 2 := ⟨_, rfl⟩
    obtain ⟨mid, hmiddef⟩ : ∃ mid : ℝ, mid = (w 0 + w (Fin.last (m + 1))) / 2 := ⟨_, rfl⟩
    obtain ⟨Y, hYdef⟩ : ∃ Y : Fin (m + 2) → ℝ, ∀ a, Y a = (w a - mid) / R :=
      ⟨_, fun _ => rfl⟩
    have hRpos : 0 < R := by rw [hRdef]; linarith
    have hYSM : StrictMono Y := by
      intro a b hab
      rw [hYdef, hYdef]
      exact div_lt_div_of_pos_right (by linarith [hwSM hab]) hRpos
    have hY0 : Y 0 = -1 := by
      rw [hYdef, hmiddef, hRdef]; field_simp; try ring
    have hY1 : Y (Fin.last (m + 1)) = 1 := by
      rw [hYdef, hmiddef, hRdef]; field_simp; try ring
    obtain ⟨i, hi⟩ := exists_gap_le_comparisonBound Y hYSM hY0 hY1
    obtain ⟨j, hj⟩ := hwy i.castSucc
    obtain ⟨k, hk⟩ := hwy i.succ
    have hwij : w i.castSucc < w i.succ := hwSM i.castSucc_lt_succ
    refine ⟨j, k, ?_, ?_, ?_, ?_, ?_⟩
    · intro hEq; rw [hEq, hk] at hj; linarith
    · rw [hj, hk]; exact hwij.le
    · intro l
      obtain ⟨a, ha⟩ := hyw l
      rcases Nat.lt_or_ge (i : ℕ) (a : ℕ) with h | h
      · exact Or.inr (by
          rw [ha, hk]
          exact hwSM.monotone (by rw [Fin.le_def, Fin.val_succ]; omega))
      · exact Or.inl (by
          rw [ha, hj]
          exact hwSM.monotone (by rw [Fin.le_def, Fin.val_castSucc]; omega))
    · rw [dist_collinear _ _ hdir, hj, hk, abs_of_nonpos (by linarith), hDeq]
      have h1 : w 0 ≤ w i.castSucc := hwSM.monotone (Fin.zero_le _)
      have h2 : w i.succ ≤ w (Fin.last (m + 1)) := hwSM.monotone (Fin.le_last _)
      linarith
    · intro z hz
      obtain ⟨s, hs, rfl⟩ := segment_collinear hz
      rw [norm_eval_collinear base dir hdir y f hf s]
      have himgy : Finset.image y Finset.univ = Finset.image w Finset.univ := by
        apply Finset.coe_injective
        rw [Finset.coe_image, Finset.coe_image, Finset.coe_univ, Set.image_univ,
          Set.image_univ, hwrange]
      have hpy : ∏ t ∈ Finset.image y Finset.univ, (s - t) = ∏ l, (s - y l) :=
        Finset.prod_image (fun x _ x' _ h => hinj h)
      have hpw : ∏ t ∈ Finset.image w Finset.univ, (s - t) = ∏ a, (s - w a) :=
        Finset.prod_image (fun x _ x' _ h => hwinj h)
      have hreindex : (∏ l, (s - y l)) = ∏ a, (s - w a) := by
        rw [← hpy, ← hpw, himgy]
      have hscale : ∀ a, s - w a = R * ((s - mid) / R - Y a) := by
        intro a; rw [hYdef]; field_simp; ring
      have hprod : (∏ a, (s - w a)) = R ^ (m + 2) * ∏ a, ((s - mid) / R - Y a) := by
        rw [Finset.prod_congr rfl fun a _ => hscale a, Finset.prod_mul_distrib]
        simp
      have hsmem : w i.castSucc ≤ s ∧ s ≤ w i.succ := by
        rw [hj, hk, min_eq_left hwij.le, max_eq_right hwij.le] at hs
        exact ⟨hs.1, hs.2⟩
      have hdiff1 : (s - mid) / R - Y i.castSucc = (s - w i.castSucc) / R := by
        rw [hYdef]; field_simp; ring
      have hdiff2 : Y i.succ - (s - mid) / R = (w i.succ - s) / R := by
        rw [hYdef]; field_simp; ring
      have hx : (s - mid) / R ∈ Icc (Y i.castSucc) (Y i.succ) := by
        constructor
        · have h := div_nonneg (sub_nonneg.mpr hsmem.1) hRpos.le
          rw [← hdiff1] at h; linarith
        · have h := div_nonneg (sub_nonneg.mpr hsmem.2) hRpos.le
          rw [← hdiff2] at h; linarith
      have hbound := hi _ hx
      have hRD : R = D / 2 := by rw [hRdef, hDeq]
      rw [hreindex, hprod, abs_mul, abs_of_pos (pow_pos hRpos (m + 2))]
      calc R ^ (m + 2) * |∏ a, ((s - mid) / R - Y a)|
          ≤ R ^ (m + 2) * comparisonBound (m + 2) :=
            mul_le_mul_of_nonneg_left hbound (pow_pos hRpos _).le
        _ = comparisonBound (m + 2) * (D / 2) ^ (m + 2) := by rw [hRD]; ring
  · -- a repeated zero occurrence: the constant path
    obtain ⟨j, k, h1, h2⟩ := Function.not_injective_iff.mp hinj
    refine ⟨j, k, h2, le_of_eq h1, ?_, ?_, ?_⟩
    · intro l
      rcases le_total (y l) (y j) with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [← h1]; exact h)
    · rw [dist_collinear _ _ hdir, h1, sub_self, abs_zero]; exact hDnn
    · intro z hz
      obtain ⟨s, hs, rfl⟩ := segment_collinear hz
      have hsj : s = y j := by
        rw [← h1, min_self, max_self] at hs
        exact le_antisymm hs.2 hs.1
      rw [norm_eval_collinear base dir hdir y f hf s, hsj,
        Finset.prod_eq_zero (Finset.mem_univ j) (by ring), abs_zero]
      exact mul_nonneg hCpos.le (pow_nonneg (by linarith) _)

/-! ### The Erdős case: a short curve inside the unit lemniscate -/

/-- **`cor:collinear-erdos-1041`.**  If the zero occurrences of a monic
polynomial of degree `n ≥ 2` lie on one line inside the open unit disc, then two
of them are joined by a rectifiable curve of total variation strictly below `2`
along which `|f| < 1`. -/
theorem collinear_erdos_1041 {n : ℕ} (hn : 2 ≤ n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (y : Fin n → ℝ) (f : ℂ[X]) (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ))))
    (hdisc : ∀ k : Fin n, ‖base + dir * (y k : ℂ)‖ < 1) :
    ∃ j k : Fin n, j ≠ k ∧
      ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow f.eval 1 2
        (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) := by
  classical
  obtain ⟨D, hD⟩ := exists_isGreatest_dist (n := n) (by omega) base dir y
  have hDnn : (0 : ℝ) ≤ D :=
    hD.2 (show (0 : ℝ) ∈ _ from ⟨⟨0, by omega⟩, ⟨0, by omega⟩, by simp⟩)
  have hDlt : D < 2 := by
    obtain ⟨a, b, hab⟩ := hD.1
    rw [hab]
    exact lt_of_le_of_lt (dist_le_norm_add_norm _ _) (by linarith [hdisc a, hdisc b])
  have hlevel :
      1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) * (D / 2) ^ n < 1 := by
    rw [← comparisonBound_eq hn]
    have h1 : (D / 2) ^ n < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
    have h2 : comparisonBound n ≤ 1 := comparisonBound_le_one hn
    have h3 : 0 < comparisonBound n := comparisonBound_pos hn
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ D / 2 by linarith) n]
  obtain ⟨j, k, hjk, _hyjk, _hadj, hlen, hseg⟩ :=
    sharp_collinear_root_diameter hn base dir hdir y f hf D hD
  refine ⟨j, k, hjk, ?_⟩
  apply ErdosProblems.Erdos1041.PaperCurve.connectedBelow_of_spokes
    (h := base + dir * (y k : ℂ))
  · intro u hu0 hu1
    have hmem :
        base + dir * (y k : ℂ) + (u : ℂ) *
            ((base + dir * (y j : ℂ)) - (base + dir * (y k : ℂ)))
          ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) := by
      refine ⟨u, 1 - u, hu0, by linarith, by ring, ?_⟩
      simp only [Complex.real_smul]
      push_cast
      ring
    exact lt_of_le_of_lt (hseg _ hmem) hlevel
  · intro u hu0 hu1
    have hcollapse :
        base + dir * (y k : ℂ) + (u : ℂ) *
            ((base + dir * (y k : ℂ)) - (base + dir * (y k : ℂ)))
          = base + dir * (y k : ℂ) := by ring
    rw [hcollapse]
    have hz : ‖f.eval (base + dir * (y k : ℂ))‖ = 0 := by
      rw [norm_eval_collinear base dir hdir y f hf (y k),
        Finset.prod_eq_zero (Finset.mem_univ k) (by ring), abs_zero]
    rw [hz]; norm_num
  · have h0 : ‖(base + dir * (y k : ℂ)) - (base + dir * (y k : ℂ))‖ = 0 := by simp
    have h1 : ‖(base + dir * (y k : ℂ)) - (base + dir * (y j : ℂ))‖
        = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) := by
      rw [dist_eq_norm, norm_sub_rev]
    rw [h0, h1]
    linarith

/-! ### Sharpness: the scaled Chebyshev root configuration -/

private theorem angle_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * Real.pi / b :=
  div_nonneg (mul_nonneg ha Real.pi_pos.le) hb.le

private theorem angle_le_pi {a b : ℝ} (hb : 0 < b) (h : a ≤ b) :
    a * Real.pi / b ≤ Real.pi := by
  have h1 : a / b ≤ 1 := (div_le_one hb).mpr h
  have h2 : a * Real.pi / b = Real.pi * (a / b) := by ring
  rw [h2]
  nlinarith [Real.pi_pos]

private theorem angle_lt {a a' b : ℝ} (hb : 0 < b) (h : a < a') :
    a * Real.pi / b < a' * Real.pi / b :=
  div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) hb

/-- `cos` of an angle `a π / b` is strictly decreasing in `a` on the admissible
range `0 ≤ a' < a ≤ b`. -/
private theorem cos_angle_lt {a a' b : ℝ} (hb : 0 < b) (ha' : 0 ≤ a') (hab : a ≤ b)
    (h : a' < a) :
    Real.cos (a * Real.pi / b) < Real.cos (a' * Real.pi / b) :=
  Real.cos_lt_cos_of_nonneg_of_le_pi (angle_nonneg ha' hb) (angle_le_pi hb hab)
    (angle_lt hb h)

/-- The zeros of the endpoint-normalised scaled Chebyshev polynomial
`q_*(x) = T_n(r_n x) / (2^(n-1) r_n^n)` of degree `n = m + 2`, listed in
increasing order: `cos((2k+1)π/(2n)) / cos(π/(2n))`. -/
def chebNode (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  Real.cos ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))
    / endpointScale (m + 2)

/-- The scaled Chebyshev extremum `cos(jπ/n) / cos(π/(2n))` lying inside the
`i`-th gap between consecutive nodes. -/
def chebPeak (m : ℕ) (i : Fin (m + 1)) : ℝ :=
  Real.cos (((m + 1 - (i : ℕ) : ℕ) : ℝ) * Real.pi / ((m + 2 : ℕ) : ℝ))
    / endpointScale (m + 2)

private theorem endpointScale_pos' (m : ℕ) : 0 < endpointScale (m + 2) :=
  endpointScale_pos (Nat.le_add_left 2 m)

private theorem twoN_pos (m : ℕ) : (0 : ℝ) < 2 * ((m + 2 : ℕ) : ℝ) := by
  have h : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos (m + 1)
  linarith

theorem chebNode_strictMono (m : ℕ) : StrictMono (chebNode m) := by
  intro i i' h
  have hr := endpointScale_pos' m
  have hv : (i : ℕ) < (i' : ℕ) := Fin.lt_def.mp h
  have hilt := i.isLt
  have hi'lt := i'.isLt
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hbig : ((m + 1 - (i : ℕ) : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
    have h1 : (m + 1 - (i : ℕ) : ℕ) ≤ m + 1 := by omega
    have h2 : ((m + 1 - (i : ℕ) : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hsmall : ((m + 1 - (i' : ℕ) : ℕ) : ℝ) < ((m + 1 - (i : ℕ) : ℕ) : ℝ) := by
    have h1 : (m + 1 - (i' : ℕ) : ℕ) < (m + 1 - (i : ℕ) : ℕ) := by omega
    exact_mod_cast h1
  simp only [chebNode]
  apply div_lt_div_of_pos_right _ hr
  refine cos_angle_lt (twoN_pos m) (by positivity) ?_ (by linarith)
  rw [hcast]; linarith

theorem chebNode_zero (m : ℕ) : chebNode m 0 = -1 := by
  have hr := endpointScale_pos' m
  have hne : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hidx : (m + 1 - ((0 : Fin (m + 2)) : ℕ) : ℕ) = m + 1 := by simp
  have hang : (2 * ((m + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ))
      = Real.pi - Real.pi / (2 * ((m + 2 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    ring
  have hes : endpointScale (m + 2) = Real.cos (Real.pi / (2 * ((m + 2 : ℕ) : ℝ))) := rfl
  simp only [chebNode, hidx]
  rw [hang, Real.cos_pi_sub, ← hes]
  field_simp

theorem chebNode_last (m : ℕ) : chebNode m (Fin.last (m + 1)) = 1 := by
  have hr := endpointScale_pos' m
  have hidx : (m + 1 - ((Fin.last (m + 1) : Fin (m + 2)) : ℕ) : ℕ) = 0 := by simp
  have hang : (2 * ((0 : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ))
      = Real.pi / (2 * ((m + 2 : ℕ) : ℝ)) := by norm_num
  have hes : endpointScale (m + 2) = Real.cos (Real.pi / (2 * ((m + 2 : ℕ) : ℝ))) := rfl
  simp only [chebNode, hidx]
  rw [hang, ← hes]
  field_simp

theorem chebNode_abs_le (m : ℕ) (i : Fin (m + 2)) : |chebNode m i| ≤ 1 := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · rw [← chebNode_zero m]; exact (chebNode_strictMono m).monotone (Fin.zero_le i)
  · rw [← chebNode_last m]; exact (chebNode_strictMono m).monotone (Fin.le_last i)

theorem eval_monicScaledChebyshev_chebNode (m : ℕ) (i : Fin (m + 2)) :
    (monicScaledChebyshev (m + 2)).eval (chebNode m i) = 0 := by
  have hn : 2 ≤ m + 2 := Nat.le_add_left 2 m
  have hr := endpointScale_pos' m
  have hne : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [eval_monicScaledChebyshev hn]
  have hx : endpointScale (m + 2) * chebNode m i
      = Real.cos ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi
          / (2 * ((m + 2 : ℕ) : ℝ))) := by
    simp only [chebNode]
    field_simp
  rw [hx, Polynomial.Chebyshev.T_real_cos]
  have hzero : Real.cos ((((m + 2 : ℕ) : ℤ) : ℝ) *
      ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))) = 0 := by
    rw [Real.cos_eq_zero_iff]
    refine ⟨((m + 1 - (i : ℕ) : ℕ) : ℤ), ?_⟩
    push_cast
    field_simp
  rw [hzero, mul_zero]

/-- The comparison polynomial factors over its `n` distinct real zeros. -/
theorem monicScaledChebyshev_eq_prod (m : ℕ) :
    monicScaledChebyshev (m + 2) = ∏ i : Fin (m + 2), (X - C (chebNode m i)) := by
  have hn : 2 ≤ m + 2 := Nat.le_add_left 2 m
  have h1 := monicScaledChebyshev_isMonicOfDegree (n := m + 2) hn
  have h2 : (∏ i : Fin (m + 2), (X - C (chebNode m i))).IsMonicOfDegree (m + 2) := by
    have h := isMonicOfDegree_prod_X_sub_C (R := ℝ)
      (Finset.univ : Finset (Fin (m + 2))) (chebNode m)
    simpa using h
  have hdeg : (monicScaledChebyshev (m + 2)
      - ∏ i : Fin (m + 2), (X - C (chebNode m i))).natDegree < m + 2 :=
    h1.natDegree_sub_lt (by simp) h2
  have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (monicScaledChebyshev (m + 2) - ∏ i : Fin (m + 2), (X - C (chebNode m i)))
    (f := chebNode m) (chebNode_strictMono m).injective
    (fun i => by
      rw [eval_sub, eval_monicScaledChebyshev_chebNode, eval_prod,
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp)]
      ring)
    (by simpa using hdeg)
  exact sub_eq_zero.mp hz

theorem abs_eval_monicScaledChebyshev_chebPeak (m : ℕ) (i : Fin (m + 1)) :
    |(monicScaledChebyshev (m + 2)).eval (chebPeak m i)| = comparisonBound (m + 2) := by
  have hn : 2 ≤ m + 2 := Nat.le_add_left 2 m
  have hr := endpointScale_pos' m
  have hne : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [eval_monicScaledChebyshev hn, abs_mul]
  have hx : endpointScale (m + 2) * chebPeak m i
      = Real.cos (((m + 1 - (i : ℕ) : ℕ) : ℝ) * Real.pi / ((m + 2 : ℕ) : ℝ)) := by
    simp only [chebPeak]
    field_simp
  rw [hx]
  have hT : |(Polynomial.Chebyshev.T ℝ ((m + 2 : ℕ) : ℤ)).eval
      (Real.cos (((m + 1 - (i : ℕ) : ℕ) : ℝ) * Real.pi / ((m + 2 : ℕ) : ℝ)))| = 1 := by
    refine (Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff (n := m + 2) (by omega) _).mpr ?_
    exact ⟨m + 1 - (i : ℕ), by omega, rfl⟩
  rw [hT, mul_one]
  rfl

theorem chebPeak_mem_gap (m : ℕ) (i : Fin (m + 1)) :
    chebNode m i.castSucc < chebPeak m i ∧ chebPeak m i < chebNode m i.succ := by
  have hr := endpointScale_pos' m
  have hilt := i.isLt
  have hne : ((m + 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  have hp : ((m - (i : ℕ) : ℕ) : ℝ) ≤ (m : ℝ) := by
    have h1 : (m - (i : ℕ) : ℕ) ≤ m := by omega
    exact_mod_cast h1
  have h1 : (m + 1 - ((i.castSucc : Fin (m + 2)) : ℕ) : ℕ) = (m - (i : ℕ)) + 1 := by
    simp only [Fin.val_castSucc]; omega
  have h2 : (m + 1 - ((i.succ : Fin (m + 2)) : ℕ) : ℕ) = m - (i : ℕ) := by
    simp only [Fin.val_succ]; omega
  have h3 : (m + 1 - (i : ℕ) : ℕ) = (m - (i : ℕ)) + 1 := by omega
  have hangle : (((m + 1 - (i : ℕ) : ℕ)) : ℝ) * Real.pi / ((m + 2 : ℕ) : ℝ)
      = (2 * ((m - (i : ℕ) : ℕ) : ℝ) + 2) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)) := by
    rw [h3]
    push_cast
    field_simp
  have hpeak : chebPeak m i
      = Real.cos ((2 * ((m - (i : ℕ) : ℕ) : ℝ) + 2) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))
        / endpointScale (m + 2) := by
    simp only [chebPeak]; rw [hangle]
  simp only [chebNode, h1, h2, hpeak]
  constructor
  · apply div_lt_div_of_pos_right _ hr
    exact cos_angle_lt (twoN_pos m) (by positivity) (by push_cast; linarith)
      (by push_cast; linarith)
  · apply div_lt_div_of_pos_right _ hr
    exact cos_angle_lt (twoN_pos m) (by positivity) (by push_cast; linarith)
      (by push_cast; linarith)

theorem mem_segment_collinear {base dir : ℂ} {a b s p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (hs : p * a + q * b = s) :
    base + dir * (s : ℂ) ∈ segment ℝ (base + dir * (a : ℂ)) (base + dir * (b : ℂ)) := by
  refine ⟨p, q, hp, hq, hpq, ?_⟩
  simp only [Complex.real_smul]
  rw [← hs]
  push_cast
  have hc : (p : ℂ) + (q : ℂ) = 1 := by rw [← Complex.ofReal_add, hpq]; norm_num
  linear_combination base * hc

/-- **The Chebyshev configuration attains the bound in every adjacent gap.**
Its zero occurrences are `base + dir * (R * chebNode m k)`; their diameter is
`2R`; and every adjacent-zero segment carries a point at which `|f|` equals
`C_n R^n`. -/
theorem chebyshev_configuration_attains {m : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1)
    {R : ℝ} (hR : 0 < R) (f : ℂ[X])
    (hf : f = ∏ k : Fin (m + 2), (X - C (base + dir * ((R * chebNode m k : ℝ) : ℂ)))) :
    IsGreatest {d : ℝ | ∃ j k : Fin (m + 2),
        d = dist (base + dir * ((R * chebNode m j : ℝ) : ℂ))
                 (base + dir * ((R * chebNode m k : ℝ) : ℂ))} (2 * R) ∧
      ∀ i : Fin (m + 1),
        ∃ z ∈ segment ℝ (base + dir * ((R * chebNode m i.castSucc : ℝ) : ℂ))
                        (base + dir * ((R * chebNode m i.succ : ℝ) : ℂ)),
          ‖f.eval z‖ = comparisonBound (m + 2) * R ^ (m + 2) := by
  constructor
  · constructor
    · refine ⟨Fin.last (m + 1), 0, ?_⟩
      rw [dist_collinear _ _ hdir, chebNode_last, chebNode_zero,
        show R * 1 - R * (-1) = 2 * R by ring, abs_of_pos (by linarith)]
    · rintro d ⟨j, k, rfl⟩
      rw [dist_collinear _ _ hdir]
      have hcj := chebNode_abs_le m j
      have hck := chebNode_abs_le m k
      rw [abs_le] at hcj hck
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · nlinarith [mul_nonneg hR.le (show (0 : ℝ) ≤ chebNode m j + 1 by linarith [hcj.1]),
          mul_nonneg hR.le (show (0 : ℝ) ≤ 1 - chebNode m k by linarith [hck.2])]
      · nlinarith [mul_nonneg hR.le (show (0 : ℝ) ≤ 1 - chebNode m j by linarith [hcj.2]),
          mul_nonneg hR.le (show (0 : ℝ) ≤ chebNode m k + 1 by linarith [hck.1])]
  · intro i
    obtain ⟨hg1, hg2⟩ := chebPeak_mem_gap m i
    refine ⟨base + dir * ((R * chebPeak m i : ℝ) : ℂ), ?_, ?_⟩
    · obtain ⟨A, hA⟩ : ∃ A : ℝ, A = R * chebNode m i.castSucc := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B : ℝ, B = R * chebNode m i.succ := ⟨_, rfl⟩
      obtain ⟨S, hS⟩ : ∃ S : ℝ, S = R * chebPeak m i := ⟨_, rfl⟩
      have hAS : A ≤ S := by
        rw [hA, hS]; exact mul_le_mul_of_nonneg_left hg1.le hR.le
      have hSB : S ≤ B := by
        rw [hS, hB]; exact mul_le_mul_of_nonneg_left hg2.le hR.le
      have hAB : A < B := by
        rw [hA, hB]; exact mul_lt_mul_of_pos_left (lt_trans hg1 hg2) hR
      have hBA : B - A ≠ 0 := ne_of_gt (sub_pos.mpr hAB)
      rw [← hA, ← hB, ← hS]
      refine mem_segment_collinear (p := (B - S) / (B - A)) (q := (S - A) / (B - A))
        (div_nonneg (by linarith) (by linarith))
        (div_nonneg (by linarith) (by linarith)) ?_ ?_
      · rw [← add_div, show B - S + (S - A) = B - A by ring]
        exact div_self hBA
      · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hBA]
        ring
    · rw [norm_eval_collinear base dir hdir (fun k => R * chebNode m k) f hf
        (R * chebPeak m i)]
      have hsplit : ∀ k : Fin (m + 2),
          R * chebPeak m i - R * chebNode m k = R * (chebPeak m i - chebNode m k) := by
        intro k; ring
      rw [Finset.prod_congr rfl fun k _ => hsplit k, Finset.prod_mul_distrib]
      have hev : (∏ k : Fin (m + 2), (chebPeak m i - chebNode m k))
          = (monicScaledChebyshev (m + 2)).eval (chebPeak m i) := by
        rw [monicScaledChebyshev_eq_prod, eval_prod]
        simp
      rw [hev]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [abs_mul, abs_of_pos (pow_pos hR (m + 2)),
        abs_eval_monicScaledChebyshev_chebPeak]
      ring

/-- **Sharpness, in the paper's `D` normalisation.**  The affine image of the
scaled Chebyshev root configuration whose extreme zeros are at distance `D`
attains `C_n (D/2)^n` on every adjacent-zero segment; so the constant in the
sharp collinear bound is best possible in every degree. -/
theorem sharp_collinear_equality_attained {m : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1)
    {D : ℝ} (hD : 0 < D) (f : ℂ[X])
    (hf : f = ∏ k : Fin (m + 2), (X - C (base + dir * ((D / 2 * chebNode m k : ℝ) : ℂ)))) :
    IsGreatest {d : ℝ | ∃ j k : Fin (m + 2),
        d = dist (base + dir * ((D / 2 * chebNode m j : ℝ) : ℂ))
                 (base + dir * ((D / 2 * chebNode m k : ℝ) : ℂ))} D ∧
      ∀ i : Fin (m + 1),
        ∃ z ∈ segment ℝ (base + dir * ((D / 2 * chebNode m i.castSucc : ℝ) : ℂ))
                        (base + dir * ((D / 2 * chebNode m i.succ : ℝ) : ℂ)),
          ‖f.eval z‖
            = 1 / (2 ^ ((m + 2) - 1)
                * Real.cos (Real.pi / (2 * ((m + 2 : ℕ) : ℝ))) ^ (m + 2))
              * (D / 2) ^ (m + 2) := by
  obtain ⟨h1, h2⟩ :=
    chebyshev_configuration_attains base dir hdir (R := D / 2) (by linarith) f hf
  rw [show 2 * (D / 2) = D by ring] at h1
  refine ⟨h1, fun i => ?_⟩
  obtain ⟨z, hz, hval⟩ := h2 i
  exact ⟨z, hz, by rw [hval, comparisonBound_eq (Nat.le_add_left 2 m)]⟩

/-! ### "Best possible in every degree" -/

/-- The conclusion of the sharp collinear diameter theorem, with the constant
left as a parameter `K`. -/
def CollinearDiameterBound (n : ℕ) (K : ℝ) : Prop :=
  ∀ base dir : ℂ, ‖dir‖ = 1 → ∀ (y : Fin n → ℝ) (f : ℂ[X]),
    f = (∏ k, (X - C (base + dir * (y k : ℂ)))) → ∀ D : ℝ,
      IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
            ‖f.eval z‖ ≤ K * (D / 2) ^ n

theorem collinearDiameterBound_sharpConstant {n : ℕ} (hn : 2 ≤ n) :
    CollinearDiameterBound n
      (1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n)) :=
  fun base dir hdir y f hf D hD => sharp_collinear_root_diameter hn base dir hdir y f hf D hD

/-- **The constant is best possible in every degree.**  No constant smaller than
`C_n` satisfies the conclusion of the sharp collinear diameter theorem. -/
theorem sharpConstant_le_of_collinearDiameterBound {n : ℕ} (hn : 2 ≤ n) {K : ℝ}
    (hK : CollinearDiameterBound n K) :
    1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) ≤ K := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [← comparisonBound_eq hn]
  obtain ⟨hgreat, hattain⟩ :=
    chebyshev_configuration_attains (m := m) (0 : ℂ) (1 : ℂ) (by simp) (R := 1) one_pos
      (∏ k : Fin (m + 2), (X - C ((0 : ℂ) + (1 : ℂ) * (((1 : ℝ) * chebNode m k : ℝ) : ℂ))))
      rfl
  obtain ⟨j, k, hjk, hyjk, hadj, _hlen, hseg⟩ :=
    hK (0 : ℂ) (1 : ℂ) (by simp) (fun k => (1 : ℝ) * chebNode m k) _ rfl (2 * 1) hgreat
  have hmono := chebNode_strictMono m
  have hjle : j ≤ k := hmono.le_iff_le.mp (by simpa using hyjk)
  have hjltk : j < k := lt_of_le_of_ne hjle hjk
  have hvlt : (j : ℕ) < (k : ℕ) := Fin.lt_def.mp hjltk
  have hklt := k.isLt
  have hadjval : (k : ℕ) = (j : ℕ) + 1 := by
    by_contra hcon
    have hgt : (j : ℕ) + 1 < (k : ℕ) := by omega
    have hlbound : (j : ℕ) + 1 < m + 2 := by omega
    rcases hadj ⟨(j : ℕ) + 1, hlbound⟩ with h | h
    · have hle := hmono.le_iff_le.mp (show chebNode m ⟨(j : ℕ) + 1, hlbound⟩ ≤ chebNode m j by
        simpa using h)
      rw [Fin.le_def] at hle
      simp only at hle
      omega
    · have hle := hmono.le_iff_le.mp (show chebNode m k ≤ chebNode m ⟨(j : ℕ) + 1, hlbound⟩ by
        simpa using h)
      rw [Fin.le_def] at hle
      simp only at hle
      omega
  have hjm : (j : ℕ) < m + 1 := by omega
  obtain ⟨z, hzmem, hzval⟩ := hattain ⟨(j : ℕ), hjm⟩
  have hij : (⟨(j : ℕ), hjm⟩ : Fin (m + 1)).castSucc = j := Fin.val_injective rfl
  have hik : (⟨(j : ℕ), hjm⟩ : Fin (m + 1)).succ = k :=
    Fin.val_injective (by simp only [Fin.val_succ]; omega)
  rw [hij, hik] at hzmem
  have hfinal := hseg z hzmem
  rw [hzval] at hfinal
  simpa using hfinal

/-! ### From an abstract monic polynomial with collinear zeros -/

/-- A monic polynomial of degree `n` over `ℂ` whose zeros all lie on the line
`base + dir * ℝ` is the product of the `n` linear factors attached to an
indexing `y : Fin n → ℝ` of its zero occurrences along that line.  This is the
bridge showing that the factored hypothesis used above is exactly the paper's
"monic of degree `n` with collinear zero occurrences", not a strengthening of
it: the indexing is what the paper calls the zero occurrences, repeated zeros
included. -/
theorem exists_collinear_factorisation (base dir : ℂ) :
    ∀ (n : ℕ) (f : ℂ[X]), f.IsMonicOfDegree n →
      (∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) →
      ∃ y : Fin n → ℝ, f = ∏ k : Fin n, (X - C (base + dir * (y k : ℂ))) := by
  intro n
  induction n with
  | zero =>
      intro f hf _
      refine ⟨Fin.elim0, ?_⟩
      rw [isMonicOfDegree_zero_iff.mp hf]
      simp
  | succ n ih =>
      intro f hf hcol
      have hfne : f ≠ 0 := hf.ne_zero
      have hdeg : 0 < f.degree := by
        rw [Polynomial.degree_eq_natDegree hfne, hf.natDegree_eq]
        exact_mod_cast Nat.succ_pos n
      obtain ⟨z, hz⟩ := Complex.exists_root hdeg
      have hzmem : z ∈ f.roots := Polynomial.mem_roots'.mpr ⟨hfne, hz⟩
      obtain ⟨t, ht⟩ := hcol z hzmem
      obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hz
      have hfg : IsMonicOfDegree ((X - C z) * g) (1 + n) := by
        rw [Nat.add_comm 1 n, ← hg]
        exact hf
      have hgmono : g.IsMonicOfDegree n := (isMonicOfDegree_X_sub_one z).of_mul_left hfg
      have hgcol : ∀ w ∈ g.roots, ∃ s : ℝ, w = base + dir * (s : ℂ) := by
        intro w hw
        refine hcol w ?_
        rw [hg, Polynomial.roots_mul (by rw [← hg]; exact hfne)]
        exact Multiset.mem_add.mpr (Or.inr hw)
      obtain ⟨y, hy⟩ := ih g hgmono hgcol
      refine ⟨Fin.cons t y, ?_⟩
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← ht, ← hy]
      exact hg

/-- **The sharp collinear root-diameter bound for an abstract monic polynomial
with collinear zeros.**  `y` indexes the `n` zero occurrences on the line. -/
theorem sharp_collinear_root_diameter_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) :
    ∃ y : Fin n → ℝ, f = (∏ k, (X - C (base + dir * (y k : ℂ)))) ∧
      ∀ D : ℝ, IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
            ‖f.eval z‖
              ≤ 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n)
                * (D / 2) ^ n := by
  obtain ⟨y, hy⟩ := exists_collinear_factorisation base dir n f hf hcol
  exact ⟨y, hy, fun D hD => sharp_collinear_root_diameter hn base dir hdir y f hy D hD⟩

/-- **`cor:collinear-erdos-1041` for an abstract monic polynomial.** -/
theorem collinear_erdos_1041_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ))
    (hdisc : ∀ z ∈ f.roots, ‖z‖ < 1) :
    ∃ a b : ℂ, a ∈ f.roots ∧ b ∈ f.roots ∧
      ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow f.eval 1 2 a b := by
  obtain ⟨y, hy⟩ := exists_collinear_factorisation base dir n f hf hcol
  have hmem : ∀ k : Fin n, base + dir * (y k : ℂ) ∈ f.roots := by
    intro k
    refine Polynomial.mem_roots'.mpr ⟨hf.ne_zero, ?_⟩
    rw [Polynomial.IsRoot.def, hy, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  obtain ⟨j, k, _hjk, hconn⟩ :=
    collinear_erdos_1041 hn base dir hdir y f hy (fun k => hdisc _ (hmem k))
  exact ⟨_, _, hmem j, hmem k, hconn⟩

#print axioms exists_collinear_factorisation
#print axioms sharp_collinear_root_diameter_monic
#print axioms collinear_erdos_1041_monic
#print axioms exists_gap_le_comparisonBound
#print axioms sharp_collinear_root_diameter
#print axioms collinear_erdos_1041
#print axioms monicScaledChebyshev_eq_prod
#print axioms chebyshev_configuration_attains
#print axioms sharp_collinear_equality_attained
#print axioms collinearDiameterBound_sharpConstant
#print axioms sharpConstant_le_of_collinearDiameterBound

end ErdosProblems.Erdos1041.PaperCompleteR21
