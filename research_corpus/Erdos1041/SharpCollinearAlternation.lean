import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Sharp constrained alternation for the collinear Erdős #1041 case

This module isolates the rigidity argument behind the sharp adjacent-gap
estimate.  If two monic real polynomials of the same degree agree at the two
endpoints, the second polynomial cannot be uniformly smaller than the first
at a full alternating sequence of interior peaks: otherwise their difference
has one zero between each consecutive pair of peaks as well as the two
endpoint zeros, although its degree has dropped by one.

The intended comparison polynomial is the endpoint-normalised scaled
Chebyshev polynomial.  Keeping the alternation engine independent of that
instantiation makes the root-counting step reusable and auditable.
-/

namespace ErdosProblems.Erdos1041.SharpCollinearAlternation

open Set
open Polynomial

/-- Subtracting a strictly smaller number in absolute value preserves the
strict sign of a nonzero real number. -/
theorem sub_mul_self_pos_of_abs_lt_abs {x y : ℝ} (h : |y| < |x|) :
    0 < (x - y) * x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx] at h
    have hxpos : 0 < x := by
      by_contra hxnot
      have : x = 0 := le_antisymm (le_of_not_gt hxnot) hx
      subst x
      exact (not_lt_of_ge (abs_nonneg y)) h
    have hylt : y < x := (abs_lt.mp h).2
    nlinarith
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hxneg] at h
    have hxlt : x < y := by simpa using (abs_lt.mp h).1
    nlinarith

/-- Pointwise domination preserves an alternating sign change after
subtraction. -/
theorem sub_values_mul_neg_of_abs_lt_abs
    {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ * x₂ < 0)
    (h₁ : |y₁| < |x₁|) (h₂ : |y₂| < |x₂|) :
    (x₁ - y₁) * (x₂ - y₂) < 0 := by
  have hs₁ := sub_mul_self_pos_of_abs_lt_abs h₁
  have hs₂ := sub_mul_self_pos_of_abs_lt_abs h₂
  rcases mul_neg_iff.mp hx with hsign | hsign
  · have hsub₁ : 0 < x₁ - y₁ := by nlinarith [hs₁]
    have hsub₂ : x₂ - y₂ < 0 := by nlinarith [hs₂]
    exact mul_neg_of_pos_of_neg hsub₁ hsub₂
  · have hsub₁ : x₁ - y₁ < 0 := by nlinarith [hs₁]
    have hsub₂ : 0 < x₂ - y₂ := by nlinarith [hs₂]
    exact mul_neg_of_neg_of_pos hsub₁ hsub₂

/-- A real polynomial whose endpoint values have opposite strict signs has a
root strictly between those endpoints. -/
theorem exists_root_between_of_eval_mul_neg
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (hneg : p.eval a * p.eval b < 0) :
    ∃ x ∈ Ioo a b, p.eval x = 0 := by
  rcases mul_neg_iff.mp hneg with hsign | hsign
  · obtain ⟨x, hx⟩ := (Set.mem_image (fun t : ℝ ↦ p.eval t) (Icc a b) 0).mp
        (intermediate_value_Icc' hab.le p.continuous.continuousOn
          (show 0 ∈ Icc (p.eval b) (p.eval a) by exact ⟨hsign.2.le, hsign.1.le⟩))
    have hax : a < x := lt_of_le_of_ne hx.1.1 (by
      intro hEq
      subst x
      linarith [hsign.1, hx.2])
    have hxb : x < b := lt_of_le_of_ne hx.1.2 (by
      intro hEq
      subst x
      linarith [hsign.2, hx.2])
    exact ⟨x, ⟨hax, hxb⟩, hx.2⟩
  · obtain ⟨x, hx⟩ := (Set.mem_image (fun t : ℝ ↦ p.eval t) (Icc a b) 0).mp
        (intermediate_value_Icc hab.le p.continuous.continuousOn
          (show 0 ∈ Icc (p.eval a) (p.eval b) by exact ⟨hsign.1.le, hsign.2.le⟩))
    have hax : a < x := lt_of_le_of_ne hx.1.1 (by
      intro hEq
      subst x
      linarith [hsign.1, hx.2])
    have hxb : x < b := lt_of_le_of_ne hx.1.2 (by
      intro hEq
      subst x
      linarith [hsign.2, hx.2])
    exact ⟨x, ⟨hax, hxb⟩, hx.2⟩

/-- Two endpoint zeros together with `n` sign changes force a polynomial of
degree below `n + 2` to vanish identically. -/
theorem eq_zero_of_endpoint_zeros_and_alternation
    {n : ℕ} {p : ℝ[X]} {a b : ℝ} {c : Fin (n + 1) → ℝ}
    (hc : StrictMono c) (ha : a < c 0) (hb : c (Fin.last n) < b)
    (hpa : p.eval a = 0) (hpb : p.eval b = 0)
    (halt : ∀ i : Fin n,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hdeg : p.natDegree < n + 2) :
    p = 0 := by
  classical
  have hex (i : Fin n) :
      ∃ x ∈ Ioo (c i.castSucc) (c i.succ), p.eval x = 0 :=
    exists_root_between_of_eval_mul_neg (hc i.castSucc_lt_succ) (halt i)
  choose z hzmem hzroot using hex
  have hzinj : Function.Injective z := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hcij : c i.succ ≤ c j.castSucc :=
        hc.monotone (Fin.succ_le_castSucc_iff.mpr hijlt)
      have hzlt : z i < z j := lt_of_lt_of_le (hzmem i).2
        (le_trans hcij (hzmem j).1.le)
      exact (ne_of_lt hzlt) hij
    · have hcji : c j.succ ≤ c i.castSucc :=
        hc.monotone (Fin.succ_le_castSucc_iff.mpr hjilt)
      have hzlt : z j < z i := lt_of_lt_of_le (hzmem j).2
        (le_trans hcji (hzmem i).1.le)
      exact (ne_of_gt hzlt) hij
  let Z : Finset ℝ := Finset.univ.image z
  have hcardZ : Z.card = n := by
    simp [Z, Finset.card_image_of_injective _ hzinj]
  have haZ : a ∉ Z := by
    simp only [Z, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i
    have haci : a < c i.castSucc := lt_of_lt_of_le ha
      (hc.monotone (Fin.zero_le _))
    exact ne_of_gt (lt_trans haci (hzmem i).1)
  have hbZ : b ∉ Z := by
    simp only [Z, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i
    have hcib : c i.succ < b := lt_of_le_of_lt
      (hc.monotone (Fin.le_last _)) hb
    exact ne_of_lt (lt_trans (hzmem i).2 hcib)
  have hab : a ≠ b := by
    exact ne_of_lt (lt_trans ha (lt_of_le_of_lt (hc.monotone (Fin.zero_le _)) hb))
  let S : Finset ℝ := insert a (insert b Z)
  have hcardS : S.card = n + 2 := by
    simp [S, Finset.card_insert_of_notMem, haZ, hbZ, hab, hcardZ]
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S
  · intro x hx
    simp only [S, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hxZ
    · exact hpa
    · exact hpb
    · rcases Finset.mem_image.mp hxZ with ⟨i, _hi, rfl⟩
      exact hzroot i
  · simpa [hcardS] using hdeg

/-- **Constrained alternation theorem.**  Let `p` and `u` be monic degree
`n + 2` real polynomials sharing two endpoint zeros.  If `p` alternates at
`n + 1` ordered interior points, then `u` cannot be bounded by `C` at all of
those points while `p` is strictly larger than `C` there. -/
theorem exists_peak_le_of_monic_comparison
    {n : ℕ} {p u : ℝ[X]} {a b C : ℝ} {c : Fin (n + 1) → ℝ}
    (hp : p.IsMonicOfDegree (n + 2)) (hu : u.IsMonicOfDegree (n + 2))
    (hc : StrictMono c) (ha : a < c 0) (hb : c (Fin.last n) < b)
    (hpa : p.eval a = 0) (hpb : p.eval b = 0)
    (hua : u.eval a = 0) (hub : u.eval b = 0)
    (hpalt : ∀ i : Fin n,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hubound : ∀ i : Fin (n + 1), |u.eval (c i)| ≤ C) :
    ∃ i : Fin (n + 1), |p.eval (c i)| ≤ C := by
  by_contra hnone
  have hnone' : ∀ i : Fin (n + 1), C < |p.eval (c i)| := by
    intro i
    exact lt_of_not_ge (fun hi ↦ hnone ⟨i, hi⟩)
  let h := p - u
  have hah : h.eval a = 0 := by simp [h, eval_sub, hpa, hua]
  have hbh : h.eval b = 0 := by simp [h, eval_sub, hpb, hub]
  have halt (i : Fin n) :
      h.eval (c i.castSucc) * h.eval (c i.succ) < 0 := by
    rw [show h.eval (c i.castSucc) =
        p.eval (c i.castSucc) - u.eval (c i.castSucc) by simp [h, eval_sub],
      show h.eval (c i.succ) =
        p.eval (c i.succ) - u.eval (c i.succ) by simp [h, eval_sub]]
    apply sub_values_mul_neg_of_abs_lt_abs (hpalt i)
    · exact lt_of_le_of_lt (hubound i.castSucc) (hnone' i.castSucc)
    · exact lt_of_le_of_lt (hubound i.succ) (hnone' i.succ)
  have hdeg : h.natDegree < n + 2 := by
    exact hp.natDegree_sub_lt (by simp) hu
  have hz : h = 0 :=
    eq_zero_of_endpoint_zeros_and_alternation hc ha hb hah hbh halt hdeg
  have hpu : p = u := sub_eq_zero.mp hz
  have hle := hubound (0 : Fin (n + 1))
  have hgt := hnone' (0 : Fin (n + 1))
  rw [hpu] at hgt
  exact (not_lt_of_ge hle) hgt

end ErdosProblems.Erdos1041.SharpCollinearAlternation
