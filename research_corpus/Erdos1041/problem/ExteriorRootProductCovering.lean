import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernel for the exterior root-product covering lemma

Companion to `ExteriorRootProductCovering.md`.  The note proves the covering
theorem

    max_{|z|=1} prod_j |z - r b_j| / |z - b_j|  >=  (1 - r^m B)/(1 - B)

by a Vieta product argument on `H = N - C(Λ) D`.  This file formalizes the
load-bearing algebraic core:

* `abs_prod_roots_eq_abs_eval_zero_div_abs_leadingCoeff` — the modulus form of
  Vieta's product formula over `ℂ`;
* `exists_root_norm_le_one_of_prod_norm_le_one` — a product of root norms ≤ 1
  forces a root in the closed unit disk;
* `covering_lambda_abs_identity` — the real-algebra identity
  `|1 - Λ| = B |r^k - Λ|` for `Λ = (1 - r^k B)/(1 - B)`;
* `exterior_covering_value_attained` — the covering kernel: if
  `N.leadingCoeff = c * D.leadingCoeff`, `‖D.leadingCoeff‖ = B`, the constant
  coefficients are `1`, degrees agree, and `‖1 - Λ‖ = B ‖c - Λ‖`, then `Λ` is
  a value of `N/D` at some point of the closed unit disk.  This is exactly
  step (i) of the note's theorem, with `c = r^m` and the `Λ` above.

It does not formalize the boundary-modulus translation, the maximum modulus
principle, the symmetric sharpness family, or the unrestricted Erdős theorem.
-/

namespace ErdosProblems.Erdos1041.ExteriorRootProductCovering

open Polynomial

/-- A product over a multiset of a function valued in the negatives equals
`(-1)` to the cardinality times the original product. -/
private theorem prod_map_neg_of_eq_neg {f : ℂ → ℂ} (hf : ∀ x, f x = -x) (s : Multiset ℂ) :
    (s.map f).prod = (-1) ^ Multiset.card s * s.prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, hf a, ih, Multiset.card_cons,
      Multiset.prod_cons, pow_succ]
    ring

/-- The norm is multiplicative on multiset products in `ℂ`. -/
private theorem norm_multiset_prod (s : Multiset ℂ) : ‖s.prod‖ = (s.map fun x => ‖x‖).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul, ih, Multiset.map_cons, Multiset.prod_cons]

/-- A product of reals that are all strictly greater than one is strictly
greater than one, provided the multiset is nonempty. -/
private theorem one_lt_prod_of_one_lt {s : Multiset ℝ} (hall : ∀ x ∈ s, (1 : ℝ) < x)
    (hne : s ≠ 0) : 1 < s.prod := by
  induction s using Multiset.induction with
  | empty => exact absurd rfl hne
  | cons a s ih =>
    have ha : 1 < a := by
      simpa using hall a (Multiset.mem_cons.mpr (Or.inl rfl))
    by_cases hs : s = 0
    · subst hs
      simp only [Multiset.prod_cons, Multiset.prod_zero, mul_one]
      exact ha
    · have hsp : 1 < s.prod :=
        ih (fun x hx => hall x (Multiset.mem_cons.mpr (Or.inr hx))) hs
      calc (1 : ℝ) < a := ha
        _ ≤ a * s.prod := by nlinarith
        _ = (a ::ₘ s).prod := by rw [Multiset.prod_cons]

/-- A nonnegative real power stays below one when the base does. -/
private theorem pow_le_one_of_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) :
    r ^ k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc r ^ (k + 1) = r ^ k * r := by ring
      _ ≤ 1 * r := by exact mul_le_mul_of_nonneg_right ih hr0
      _ ≤ 1 := by nlinarith

/-- Modulus form of Vieta's product formula: the product of the norms of the
roots equals the norm of the constant term over the norm of the leading
coefficient. -/
theorem abs_prod_roots_eq_abs_eval_zero_div_abs_leadingCoeff (p : ℂ[X]) (hp : p ≠ 0) :
    (p.roots.map fun ζ => ‖ζ‖).prod = ‖p.eval 0‖ / ‖p.leadingCoeff‖ := by
  have hs : p.Splits := IsAlgClosed.splits p
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have h0 : (p.roots.map fun ζ => X - C ζ).prod.eval 0
      = (-1) ^ Multiset.card p.roots * p.roots.prod := by
    rw [eval_multiset_prod, Multiset.map_map]
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    exact prod_map_neg_of_eq_neg (f := fun ζ => (0 : ℂ) - ζ) (fun x => zero_sub x) _
  have key : p.eval 0
      = p.leadingCoeff * ((-1) ^ Multiset.card p.roots * p.roots.prod) := by
    have hsplit : p = C p.leadingCoeff * (p.roots.map fun ζ => X - C ζ).prod :=
      hs.eq_prod_roots
    conv_lhs => rw [hsplit]
    rw [eval_mul, eval_C, h0]
  rw [key]
  have habs : ‖p.leadingCoeff * ((-1) ^ Multiset.card p.roots * p.roots.prod)‖
      = ‖p.leadingCoeff‖ * (p.roots.map fun ζ => ‖ζ‖).prod := by
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_multiset_prod]
  rw [habs]
  field_simp

/-- A product of root norms bounded by one forces a root in the closed unit
disk. -/
theorem exists_root_norm_le_one_of_prod_norm_le_one (p : ℂ[X]) (_hp : p ≠ 0)
    (hdeg : 0 < p.natDegree) (h : (p.roots.map fun ζ => ‖ζ‖).prod ≤ 1) :
    ∃ ζ ∈ p.roots, ‖ζ‖ ≤ 1 := by
  by_contra hall
  push Not at hall
  have hs : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := splits_iff_card_roots.mp hs
  have hcardmap : (p.roots.map fun ζ => ‖ζ‖).card = p.natDegree := by
    rw [Multiset.card_map, hcard]
  have hmapne : (p.roots.map fun ζ => ‖ζ‖) ≠ 0 := by
    intro hc
    have hcz : Multiset.card (p.roots.map fun ζ => ‖ζ‖) = 0 := by
      rw [hc, Multiset.card_zero]
    rw [hcardmap] at hcz
    exact absurd hcz (Nat.ne_of_gt hdeg)
  have hpos : (1 : ℝ) < (p.roots.map fun ζ => ‖ζ‖).prod := by
    refine one_lt_prod_of_one_lt ?_ hmapne
    intro x hx
    obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
    exact hall ζ hζ
  exact lt_irrefl (1 : ℝ) (lt_of_lt_of_le hpos h)

/-- The real-algebra identity `|1 - Λ| = B |r^k - Λ|` for
`Λ = (1 - r^k B)/(1 - B)`, `0 < r < 1`, `0 < B < 1`. -/
theorem covering_lambda_abs_identity {B r : ℝ} (hB : 0 < B) (hB1 : B < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    |1 - (1 - r ^ k * B) / (1 - B)|
      = B * |r ^ k - (1 - r ^ k * B) / (1 - B)| := by
  have hrk1 : r ^ k ≤ 1 := pow_le_one_of_le_one hr0.le hr1.le k
  have hden : 0 < 1 - B := by linarith
  set Λ := (1 - r ^ k * B) / (1 - B) with hΛdef
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛdef, one_le_div hden]
    nlinarith
  have hΛrk : r ^ k ≤ Λ := by
    rw [hΛdef, le_div_iff₀ hden]
    nlinarith
  rw [abs_sub_comm 1 Λ, abs_sub_comm (r ^ k) Λ,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Λ - 1),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Λ - r ^ k), hΛdef]
  field_simp
  ring

/-- Covering kernel: the value `Λ` is attained by `N/D` at some point of the
closed unit disk.  With `c = r^m`, `B = ∏|b_j|`, and
`Λ = (1 - r^m B)/(1 - B)` this is step (i) of the covering theorem. -/
theorem exterior_covering_value_attained
    {N D : ℂ[X]} {c : ℂ} {Λ : ℂ} {B : ℝ}
    (hN0 : N.coeff 0 = 1) (hD0 : D.coeff 0 = 1)
    (hdeg : N.natDegree = D.natDegree) (hpos : 0 < N.natDegree)
    (hlead : N.leadingCoeff = c * D.leadingCoeff)
    (hDlead : ‖D.leadingCoeff‖ = B) (hB : 0 < B)
    (hid : ‖1 - Λ‖ = B * ‖c - Λ‖)
    (_hN : N ≠ 0) (hD : D ≠ 0) :
    ∃ ζ, ‖ζ‖ ≤ 1 ∧ N.eval ζ = Λ * D.eval ζ := by
  set H := N - C Λ * D with hHdef
  have hnD : D.natDegree = N.natDegree := hdeg.symm
  have hlcN : N.leadingCoeff = N.coeff N.natDegree := rfl
  have hlcD : D.leadingCoeff = D.coeff D.natDegree := rfl
  have hcoeffn : H.coeff D.natDegree = (c - Λ) * D.leadingCoeff := by
    have h1 : H.coeff D.natDegree = N.coeff D.natDegree - (C Λ * D).coeff D.natDegree := by
      rw [hHdef, coeff_sub, coeff_C_mul]
    have hDlcN : D.leadingCoeff = D.coeff N.natDegree := by rw [hlcD, hnD]
    rw [h1, ← hdeg, ← hlcN, coeff_C_mul, ← hnD, hDlcN, hlead, hDlcN, hnD]
    ring
  by_cases hcz : ‖c - Λ‖ = 0
  · -- c = Λ: then ‖1 - Λ‖ = 0, so Λ = 1 and ζ = 0 works
    rw [hcz, mul_zero] at hid
    have hΛ1 : Λ = 1 := (sub_eq_zero.mp (norm_eq_zero.mp hid)).symm
    exact ⟨0, by simp, by simp [hΛ1, ← coeff_zero_eq_eval_zero, hN0, hD0]⟩
  · -- main branch: H is nonzero of degree = N.natDegree, product of root norms = 1
    have hcΛ : c - Λ ≠ 0 := by
      intro hc0
      rw [hc0] at hcz
      exact absurd hcz (by simp)
    have hDlc : D.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hD
    have hcoeffn_ne : H.coeff D.natDegree ≠ 0 := by
      rw [hcoeffn]
      exact mul_ne_zero hcΛ hDlc
    have hHne : H ≠ 0 := by
      intro hzero
      rw [hzero, coeff_zero] at hcoeffn_ne
      exact hcoeffn_ne rfl
    have hHdeg : H.natDegree = N.natDegree := by
      have hcoeffn_ne' : H.coeff N.natDegree ≠ 0 := by rw [← hnD]; exact hcoeffn_ne
      refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ hcoeffn_ne'
      rw [natDegree_le_iff_coeff_eq_zero]
      intro m hm
      have h3 : H.coeff m = N.coeff m - Λ * D.coeff m := by
        simp only [hHdef, coeff_sub, coeff_C_mul]
      rw [h3, coeff_eq_zero_of_natDegree_lt hm,
        coeff_eq_zero_of_natDegree_lt (by rw [hnD]; exact hm)]
      ring
    have hH0 : H.coeff 0 = 1 - Λ := by
      simp only [hHdef, coeff_sub, coeff_C_mul]
      rw [hN0, hD0, mul_one]
    have hprod1 : (H.roots.map fun ζ => ‖ζ‖).prod = 1 := by
      rw [abs_prod_roots_eq_abs_eval_zero_div_abs_leadingCoeff H hHne]
      rw [← coeff_zero_eq_eval_zero, hH0]
      have hlcH : H.leadingCoeff = (c - Λ) * D.leadingCoeff := by
        show H.coeff H.natDegree = (c - Λ) * D.leadingCoeff
        rw [hHdeg, ← hnD]
        exact hcoeffn
      rw [hlcH, norm_mul, hDlead, hid]
      field_simp
    obtain ⟨ζ, hζroot, hζabs⟩ :=
      exists_root_norm_le_one_of_prod_norm_le_one H hHne (by rw [hHdeg]; exact hpos) (le_of_eq hprod1)
    have hHz : H.eval ζ = 0 := ((Polynomial.mem_roots' (a := ζ) (p := H)).mp hζroot).2
    refine ⟨ζ, hζabs, ?_⟩
    have hval : N.eval ζ - Λ * D.eval ζ = 0 := by
      have hrew : N.eval ζ - Λ * D.eval ζ = (N - C Λ * D).eval ζ := by
        simp [eval_sub, eval_mul, eval_C]
      rw [hrew]
      exact hHz
    rw [sub_eq_zero] at hval
    exact hval

end ErdosProblems.Erdos1041.ExteriorRootProductCovering
