import ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10

/-!
# Erdős 1041: the sparse quintic `z^5 + a z^4 + b z + c` on the closed unit disc

Paper-form restatement of the long-record theorem labelled
`thm:primitive-quintic-two-tail`
(`paper/reasoning-parts/erdos1041/core.tex`, line 1873).

The paper's theorem has four assertions about `p(z) = z^5 + a z^4 + b z + c`
with five zero occurrences `w 0, …, w 4`:

* *closed disc*: at least two distinct indices satisfy `|b w i + c| ≤ 1`;
* *closed disc, `a ≠ 0`*: two indices can be chosen with strict inequalities;
* *closed disc, `a = 0`*: every index satisfies the bound, and equality holds
  exactly when `|w i| = 1`;
* *open disc*: two zero occurrences are joined inside `{|p| < 1}` by a curve of
  length below `2`, by the two radial spokes through `0` when their values
  differ, and by the constant path when the selected occurrences coincide.

The tree already carries the open-disc half
(`PaperPrimitivePath.path_of_selected_tails` on top of
`PaperPrimitiveCompletionR10.two_tails_of_rootProduct`).  What is new here is
the closed-disc half.  Its `a ≠ 0` case is the same harmonic-separator route as
the open-disc case — `PrimitiveQuinticInteriorTail.primitiveInterior_exists_two_tailEnergy_lt_one`
only needs `‖w i‖ ^ 2 ≤ 1` — so the argument is repeated here with the
non-strict root hypothesis; its `a = 0` case is the exact tail identity
`|b w i + c| = |w i| ^ 5`, which carries the equality clause.
-/

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Set
open ErdosProblems.Erdos1041.PaperCurve
open ErdosProblems.Erdos1041.PaperPrimitivePath
open ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10
open scoped BigOperators

/-! ### Real-coordinate helpers

These repeat the `private` helpers of `PaperPrimitiveCompletionR10`, which are
not visible outside that module. -/

private theorem norm_sq_coords (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

private theorem real_square (z : ℂ) :
    (z ^ 2).re = 2 * z.re ^ 2 - ‖z‖ ^ 2 := by
  rw [norm_sq_coords]
  simp [pow_two, Complex.mul_re]
  ring

private theorem real_cube (z : ℂ) :
    (z ^ 3).re = 4 * z.re ^ 3 - 3 * ‖z‖ ^ 2 * z.re := by
  rw [norm_sq_coords]
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

private theorem norm_add_real_sq (z : ℂ) (r : ℝ) :
    ‖z + (r : ℂ)‖ ^ 2 = ‖z‖ ^ 2 + r ^ 2 + 2 * r * z.re := by
  rw [norm_sq_coords, norm_sq_coords]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ### The tail identity at a zero occurrence -/

/-- At a zero occurrence the root equation eliminates the two present
low coefficients: `b w + c = -(w ^ 4 (w + a))`. -/
theorem tail_identity {a b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z) (i : Fin 5) :
    b * w i + c = -(w i ^ 4 * (w i + a)) := by
  have hroot : value a b c (w i) = 0 := by
    rw [hf]; fin_cases i <;> simp [rootProduct]
  dsimp [value] at hroot
  linear_combination hroot

/-- The `a = 0` clause of the paper theorem: the tail modulus is exactly the
fifth power of the root modulus. -/
theorem tail_norm_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (i : Fin 5) :
    ‖b * w i + c‖ = ‖w i‖ ^ 5 := by
  rw [tail_identity (a := 0) w hf i, norm_neg, add_zero, ← pow_succ, norm_pow]

/-! ### The closed-disc selector for `a ≠ 0` -/

/-- Closed-disc form of `PaperPrimitiveCompletionR10.two_tails_of_rootProduct`
for a nonzero leading tail coefficient.  The moment route only ever needs
`‖w i‖ ≤ 1`, so the open-disc hypothesis of the existing declaration is
relaxed here without weakening the strict conclusion. -/
theorem two_tails_closedDisc_of_ne_zero {a b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z)
    (hw : ∀ i, ‖w i‖ ≤ 1) (ha : a ≠ 0) :
    ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 := by
  have htail (i : Fin 5) : b * w i + c = -(w i ^ 4 * (w i + a)) :=
    tail_identity w hf i
  let r : ℝ := ‖a‖
  have hr : 0 < r := norm_pos_iff.mpr ha
  let u : ℂ := (r : ℂ) / a
  have hua : u * a = (r : ℂ) := div_mul_cancel₀ _ ha
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_self (ne_of_gt hr)
  let z : Fin 5 → ℂ := fun i => u * w i
  have hzn (i : Fin 5) : ‖z i‖ = ‖w i‖ := by simp [z, norm_mul, hu]
  have hz (i : Fin 5) : ‖z i‖ ≤ 1 := by rw [hzn]; exact hw i
  obtain ⟨hm1, hm2, hm3⟩ := newton_moments w hf
  have sum_rotation (k : ℕ) : (∑ i, z i ^ k) = u ^ k * ∑ i, w i ^ k := by
    simp only [z, mul_pow, Finset.mul_sum]
  have hz1 : (∑ i, z i) = -(r : ℂ) := by
    have H := sum_rotation 1
    simp only [pow_one] at H
    rw [H, hm1, mul_neg, hua]
  have hz2 : (∑ i, z i ^ 2) = (r : ℂ) ^ 2 := by
    rw [sum_rotation, hm2, ← mul_pow, hua]
  have hz3 : (∑ i, z i ^ 3) = -(r : ℂ) ^ 3 := by
    rw [sum_rotation, hm3, mul_neg, ← mul_pow, hua]
  have hsum3 : ‖∑ i, z i ^ 3‖ ≤ (5 : ℝ) := calc
    ‖∑ i, z i ^ 3‖ ≤ ∑ i, ‖z i ^ 3‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 5, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hz i)
    _ = 5 := by simp
  have hr3 : r ^ 3 ≤ 5 := by
    simpa [hz3, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] using hsum3
  have hr2 : r < 2 := by
    by_contra H
    have H' : (2 : ℝ) ≤ r := le_of_not_gt H
    have hplus : 0 ≤ r + 2 := by linarith
    have hsqprod : 0 ≤ (r - 2) * (r + 2) :=
      mul_nonneg (sub_nonneg.mpr H') hplus
    have hsq : (4 : ℝ) ≤ r ^ 2 := by nlinarith
    have hcubicprod : 0 ≤ (r ^ 2 - 4) * r :=
      mul_nonneg (sub_nonneg.mpr hsq) hr.le
    have hcubic : (8 : ℝ) ≤ r ^ 3 := by nlinarith
    linarith
  have hs0 (i : Fin 5) : 0 ≤ ‖z i‖ ^ 2 := sq_nonneg _
  have hs1 (i : Fin 5) : ‖z i‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hz i)
  have hxs (i : Fin 5) : (z i).re ^ 2 ≤ ‖z i‖ ^ 2 := by
    rw [norm_sq_coords]; nlinarith [sq_nonneg (z i).im]
  have hx1 : (z 0).re + (z 1).re + (z 2).re + (z 3).re + (z 4).re = -r := by
    have H := congrArg Complex.re hz1
    simpa [Fin.sum_univ_succ, add_assoc] using H
  have hx2 :
      (2*(z 0).re^2 - ‖z 0‖^2) + (2*(z 1).re^2 - ‖z 1‖^2) +
      (2*(z 2).re^2 - ‖z 2‖^2) + (2*(z 3).re^2 - ‖z 3‖^2) +
      (2*(z 4).re^2 - ‖z 4‖^2) = r^2 := by
    have H := congrArg Complex.re hz2
    calc
      _ = 2 * r ^ 2 - r ^ 2 := by
        simpa [Fin.sum_univ_succ, real_square, add_assoc] using H
      _ = r ^ 2 := by ring
  have hx3 :
      (4*(z 0).re^3 - 3*‖z 0‖^2*(z 0).re) +
      (4*(z 1).re^3 - 3*‖z 1‖^2*(z 1).re) +
      (4*(z 2).re^3 - 3*‖z 2‖^2*(z 2).re) +
      (4*(z 3).re^3 - 3*‖z 3‖^2*(z 3).re) +
      (4*(z 4).re^3 - 3*‖z 4‖^2*(z 4).re) = -r^3 := by
    have H := congrArg Complex.re hz3
    calc
      _ = 3 * r ^ 2 * r - 4 * r ^ 3 := by
        simpa [Fin.sum_univ_succ, real_cube, add_assoc] using H
      _ = -r ^ 3 := by ring
  have henergy (i : Fin 5) :
      ‖b*w i+c‖ ^ 2 = (‖z i‖^2)^4 * (‖z i‖^2 + r^2 + 2*r*(z i).re) := by
    have he : z i + (r : ℂ) = u * (w i + a) := by dsimp [z]; rw [mul_add, hua]
    have heN : ‖z i + (r : ℂ)‖ = ‖w i + a‖ := by rw [he, norm_mul, hu, one_mul]
    rw [htail, norm_neg, norm_mul, norm_pow, ← hzn, ← heN, mul_pow,
      norm_add_real_sq]
    ring
  have safe (i : Fin 5)
      (H : (‖z i‖^2)^4 * (‖z i‖^2+r^2+2*r*(z i).re) < 1) :
      ‖b*w i+c‖ < 1 := by
    rw [← henergy] at H
    nlinarith [norm_nonneg (b*w i+c), sq_nonneg (‖b*w i+c‖ - 1)]
  have H := primitiveInterior_exists_two_tailEnergy_lt_one hr hr2
    (hs0 0) (hs1 0) (hxs 0) (hs0 1) (hs1 1) (hxs 1)
    (hs0 2) (hs1 2) (hxs 2) (hs0 3) (hs1 3) (hxs 3)
    (hs0 4) (hs1 4) (hxs 4) hx1 hx2 hx3
  rcases H with H | H | H | H | H | H | H | H | H | H
  · exact ⟨0, 1, by decide, safe 0 H.1, safe 1 H.2⟩
  · exact ⟨0, 2, by decide, safe 0 H.1, safe 2 H.2⟩
  · exact ⟨0, 3, by decide, safe 0 H.1, safe 3 H.2⟩
  · exact ⟨0, 4, by decide, safe 0 H.1, safe 4 H.2⟩
  · exact ⟨1, 2, by decide, safe 1 H.1, safe 2 H.2⟩
  · exact ⟨1, 3, by decide, safe 1 H.1, safe 3 H.2⟩
  · exact ⟨1, 4, by decide, safe 1 H.1, safe 4 H.2⟩
  · exact ⟨2, 3, by decide, safe 2 H.1, safe 3 H.2⟩
  · exact ⟨2, 4, by decide, safe 2 H.1, safe 4 H.2⟩
  · exact ⟨3, 4, by decide, safe 3 H.1, safe 4 H.2⟩

/-- The `a = 0` clause in full: every tail is bounded by one, with equality
exactly at a unimodular root occurrence. -/
theorem tail_le_one_and_eq_iff_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (hw : ∀ i, ‖w i‖ ≤ 1)
    (i : Fin 5) :
    ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1) := by
  have hval : ‖b * w i + c‖ = ‖w i‖ ^ 5 := tail_norm_of_leading_zero w hf i
  have hnn : 0 ≤ ‖w i‖ := norm_nonneg _
  refine ⟨by rw [hval]; exact pow_le_one₀ hnn (hw i), ?_⟩
  rw [hval]
  constructor
  · intro h
    by_contra hne
    have hlt : ‖w i‖ < 1 := lt_of_le_of_ne (hw i) hne
    have : ‖w i‖ ^ 5 < 1 := pow_lt_one₀ hnn hlt (by norm_num)
    exact absurd h (ne_of_lt this)
  · intro h; rw [h]; norm_num

/-! ### The monic quintic carrying a prescribed list of zero occurrences -/

/-- `∏ i, (X - w i)`: the monic degree-five polynomial with the prescribed
zero occurrences. -/
def rootPoly (w : Fin 5 → ℂ) : ℂ[X] := ∏ i : Fin 5, (X - C (w i))

theorem rootPoly_monic (w : Fin 5 → ℂ) : (rootPoly w).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (w i)

theorem rootPoly_natDegree (w : Fin 5 → ℂ) : (rootPoly w).natDegree = 5 := by
  rw [rootPoly, natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (w i)]
  simp

theorem rootPoly_eval (w : Fin 5 → ℂ) (x : ℂ) :
    (rootPoly w).eval x = rootProduct w x := by
  simp [rootPoly, rootProduct, Fin.prod_univ_five, mul_assoc]

theorem rootPoly_eval_root (w : Fin 5 → ℂ) (i : Fin 5) :
    (rootPoly w).eval (w i) = 0 := by
  rw [rootPoly, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem norm_lt_one_of_rootPoly_eval_zero {w : Fin 5 → ℂ}
    (hw : ∀ i, ‖w i‖ < 1) {x : ℂ} (hx : (rootPoly w).eval x = 0) :
    ‖x‖ < 1 := by
  rw [rootPoly, eval_prod, Finset.prod_eq_zero_iff] at hx
  obtain ⟨i, -, hi⟩ := hx
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hi
  rw [hi]
  exact hw i

/-! ### The whole paper theorem -/

/-- **The long-record theorem `thm:primitive-quintic-two-tail`.**
For `p(z) = z ^ 5 + a z ^ 4 + b z + c` with five zero occurrences
`w 0, …, w 4`:

* if every occurrence lies in the closed unit disc, then two distinct indices
  satisfy `‖b * w i + c‖ ≤ 1`; when `a ≠ 0` two indices can be chosen with
  strict inequalities; and when `a = 0` every index satisfies the bound, with
  equality exactly at `‖w i‖ = 1`;
* if every occurrence lies in the open unit disc, then two zero occurrences are
  joined inside `{|p| < 1}` by a rectifiable curve of variation below `2`,
  realised by the two radial spokes through `0` when the two occurrences are
  distinct points and by the constant path when they coincide. -/
theorem primitive_quintic_two_tail (a b c : ℂ) (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z) :
    ((∀ i, ‖w i‖ ≤ 1) →
        (∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ ≤ 1 ∧ ‖b * w j + c‖ ≤ 1) ∧
        (a ≠ 0 → ∃ i j : Fin 5, i ≠ j ∧
          ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1) ∧
        (a = 0 → ∀ i : Fin 5,
          ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1))) ∧
      ((∀ i, ‖w i‖ < 1) →
        ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 ∧
          ConnectedBelow (value a b c) 1 2 (w i) (w j) ∧
          (w i ≠ w j → HubBelow (value a b c) 1 2 (w i) 0 (w j)) ∧
          (w i = w j →
            (∀ t : ℝ, ‖value a b c ((fun _ : ℝ => w i) t)‖ < 1) ∧
            eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0)) := by
  constructor
  · intro hw
    have hzero : a = 0 → ∀ i : Fin 5,
        ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1) := by
      rintro rfl
      exact tail_le_one_and_eq_iff_of_leading_zero w hf hw
    have hne : a ≠ 0 → ∃ i j : Fin 5, i ≠ j ∧
        ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 :=
      fun ha => two_tails_closedDisc_of_ne_zero w hf hw ha
    refine ⟨?_, hne, hzero⟩
    by_cases ha : a = 0
    · obtain ⟨h0, -⟩ := hzero ha 0
      obtain ⟨h1, -⟩ := hzero ha 1
      exact ⟨0, 1, by decide, h0, h1⟩
    · obtain ⟨i, j, hij, hi, hj⟩ := hne ha
      exact ⟨i, j, hij, hi.le, hj.le⟩
  · intro hw
    have hvalue : ∀ x : ℂ, (rootPoly w).eval x = value a b c x :=
      fun x => by rw [rootPoly_eval, hf]
    have hfun : (rootPoly w).eval = value a b c := funext hvalue
    have hsel : ∃ i j : Fin 5, i ≠ j ∧
        ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 :=
      two_tails_of_rootProduct w hf hw
    obtain ⟨i, j, hij, hi, hj, hconn, hhub, hconst⟩ :=
      path_of_selected_tails (rootPoly w) (rootPoly_monic w)
        (rootPoly_natDegree w) a b c hvalue
        (fun x hx => norm_lt_one_of_rootPoly_eval_zero hw hx)
        w (rootPoly_eval_root w) hsel
    refine ⟨i, j, hij, hi, hj, ?_, ?_, ?_⟩
    · rwa [hfun] at hconn
    · rwa [hfun] at hhub
    · intro heq
      obtain ⟨h1, h2⟩ := hconst heq
      exact ⟨fun t => by rw [← hvalue]; exact h1 t, h2⟩

/-- The same theorem reached from the polynomial itself: the five zero
occurrences exist by the fundamental theorem of algebra, so the hypothesis
`hf` above is never vacuous. -/
theorem primitive_quintic_two_tail_of_polynomial (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = 5) (a b c : ℂ)
    (hvalue : ∀ z, p.eval z = value a b c z) :
    ∃ w : Fin 5 → ℂ, (∀ z, p.eval z = rootProduct w z) ∧
      ((∀ i, ‖w i‖ ≤ 1) →
          (∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ ≤ 1 ∧ ‖b * w j + c‖ ≤ 1) ∧
          (a ≠ 0 → ∃ i j : Fin 5, i ≠ j ∧
            ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1) ∧
          (a = 0 → ∀ i : Fin 5,
            ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1))) ∧
        ((∀ i, ‖w i‖ < 1) →
          ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 ∧
            ConnectedBelow (value a b c) 1 2 (w i) (w j) ∧
            (w i ≠ w j → HubBelow (value a b c) 1 2 (w i) 0 (w j)) ∧
            (w i = w j →
              (∀ t : ℝ, ‖value a b c ((fun _ : ℝ => w i) t)‖ < 1) ∧
              eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0)) := by
  obtain ⟨w, hw⟩ := monic_quintic_enumeration p hp hd
  have hf : ∀ z, value a b c z = rootProduct w z := fun z => by rw [← hvalue, hw]
  exact ⟨w, hw, primitive_quintic_two_tail a b c w hf⟩

#print axioms tail_identity
#print axioms tail_norm_of_leading_zero
#print axioms two_tails_closedDisc_of_ne_zero
#print axioms tail_le_one_and_eq_iff_of_leading_zero
#print axioms rootPoly_monic
#print axioms rootPoly_natDegree
#print axioms rootPoly_eval
#print axioms rootPoly_eval_root
#print axioms norm_lt_one_of_rootPoly_eval_zero
#print axioms primitive_quintic_two_tail
#print axioms primitive_quintic_two_tail_of_polynomial

end ErdosProblems.Erdos1041.PaperCompleteR21
