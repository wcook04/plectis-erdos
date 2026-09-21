import ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: the inclusive one-sided `1/n` bound

This file supplies the product estimate used in short-paper
`res:inclusiveone`.  A summable positive excess over `1/n` gives a bounded
Euler product.  The telescoping `1 + 1/n` factor then bounds
`prefixProduct a n / a n` linearly, so the product defect is bounded above.
The existing exact bounded-defect endpoint finishes the recurrence.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter Finset PaperCompleteR7
open scoped BigOperators Topology

private def excess (K ε : ℝ) (n : ℕ) : ℝ :=
  K / (n : ℝ) ^ (1 + ε)

private theorem excess_nonneg {K ε : ℝ} (hK : 0 ≤ K) (n : ℕ) :
    0 ≤ excess K ε n := by
  exact div_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem excess_summable {K ε : ℝ} (hε : 0 < ε) :
    Summable (excess K ε) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + ε)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  simpa [excess, div_eq_mul_inv] using hs.mul_left K

/-- Partial products of the summable excess factors are eventually bounded. -/
private theorem excess_product_eventually_bounded
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (∏ j ∈ Finset.range n, (1 + excess K ε j)) ≤ R := by
  have hm : Multipliable (fun n : ℕ => 1 + excess K ε n) :=
    Real.multipliable_one_add_of_summable (excess_summable hε)
  obtain ⟨R, hR, s, hs⟩ := hm.eventually_bounded_finset_prod
  refine ⟨R, hR, s.sup id + 1, fun n hn => hs (Finset.range n) ?_⟩
  intro j hj
  apply Finset.mem_range.mpr
  have hjle : j ≤ s.sup id := Finset.le_sup (f := id) hj
  omega

private def tailScale (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ)

private def growthDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1

private theorem tailScale_succ (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (n : ℕ) :
    tailScale a (n + 1) = tailScale a n * (1 + growthDefect a n) := by
  have hn0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
  have hn10 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
  simp only [tailScale, growthDefect, prefixProduct_succ, Nat.cast_mul]
  field_simp [hn0, hn10]
  <;> ring

/-- The inclusive `1/n` bound with summable excess makes the paper's product
scale grow at most linearly. -/
private theorem tailScale_le_linear_of_inclusive
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (hγ : ∃ N : ℕ, ∀ n, N ≤ n →
      growthDefect a n ≤ 1 / (n : ℝ) + excess K ε n) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n → tailScale a n ≤ A * n := by
  obtain ⟨N0, hN0⟩ := hγ
  obtain ⟨R, hR, NR, hNR⟩ := excess_product_eventually_bounded hK hε
  let N := max 1 N0
  have hNpos : 0 < N := by dsimp [N]; omega
  have hiter : ∀ n, N ≤ n →
      (N : ℝ) * tailScale a n ≤
        (n : ℝ) * tailScale a N *
          ∏ j ∈ Finset.Ico N n, (1 + excess K ε j) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hNn ih =>
        have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le hNpos hNn
        have hδ : 0 ≤ excess K ε n := excess_nonneg hK n
        have hfactor : 1 + growthDefect a n ≤
            (1 + 1 / (n : ℝ)) * (1 + excess K ε n) := by
          have hg := hN0 n (by dsimp [N] at hNn; omega)
          nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / (n : ℝ)) hδ]
        have hfactor0 : 0 ≤ 1 + growthDefect a n := by
          rw [show 1 + growthDefect a n =
            (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) by simp [growthDefect]]
          positivity
        have hprod0 : 0 ≤ ∏ j ∈ Finset.Ico N n, (1 + excess K ε j) := by
          apply Finset.prod_nonneg
          intro j _
          linarith [excess_nonneg (ε := ε) hK j]
        have hright : 0 ≤
            (n : ℝ) * tailScale a N * ∏ j ∈ Finset.Ico N n, (1 + excess K ε j) := by
          exact mul_nonneg
            (mul_nonneg (Nat.cast_nonneg n)
              (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) hprod0
        rw [tailScale_succ a hpos n]
        calc
          (N : ℝ) * (tailScale a n * (1 + growthDefect a n)) =
              ((N : ℝ) * tailScale a n) * (1 + growthDefect a n) := by ring
          _ ≤ ((n : ℝ) * tailScale a N *
              ∏ j ∈ Finset.Ico N n, (1 + excess K ε j)) *
                (1 + growthDefect a n) :=
            mul_le_mul_of_nonneg_right ih hfactor0
          _ ≤ ((n : ℝ) * tailScale a N *
              ∏ j ∈ Finset.Ico N n, (1 + excess K ε j)) *
                ((1 + 1 / (n : ℝ)) * (1 + excess K ε n)) :=
            mul_le_mul_of_nonneg_left hfactor hright
          _ = ((n + 1 : ℕ) : ℝ) * tailScale a N *
              ((∏ j ∈ Finset.Ico N n, (1 + excess K ε j)) *
                (1 + excess K ε n)) := by
            have htel : (n : ℝ) * (1 + 1 / (n : ℝ)) = (n + 1 : ℕ) := by
              push_cast
              field_simp [ne_of_gt hnpos]
            set P : ℝ := ∏ j ∈ Finset.Ico N n, (1 + excess K ε j)
            set δ : ℝ := excess K ε n
            change ((n : ℝ) * tailScale a N * P) *
                ((1 + 1 / (n : ℝ)) * (1 + δ)) =
              ((n + 1 : ℕ) : ℝ) * tailScale a N * (P * (1 + δ))
            rw [← htel]
            ring
          _ = ((n + 1 : ℕ) : ℝ) * tailScale a N *
              ∏ j ∈ Finset.Ico N (n + 1), (1 + excess K ε j) := by
            rw [Finset.prod_Ico_succ_top hNn]
  let M := max N NR
  let A := tailScale a N * R / (N : ℝ)
  have hApos : 0 < A := by
    apply div_pos
    · exact mul_pos (div_pos (by exact_mod_cast (prefixProduct_pos a hpos N))
        (by exact_mod_cast hpos N)) hR
    · exact_mod_cast hNpos
  refine ⟨A, hApos, M, fun n hn => ?_⟩
  have hNn : N ≤ n := (Nat.le_max_left N NR).trans hn
  have hRn : NR ≤ n := (Nat.le_max_right N NR).trans hn
  have hi := hiter n hNn
  have hsub : Finset.Ico N n ⊆ Finset.range n := by
    intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  have hprod : (∏ j ∈ Finset.Ico N n, (1 + excess K ε j)) ≤
      ∏ j ∈ Finset.range n, (1 + excess K ε j) := by
    apply Finset.prod_le_prod_of_subset_of_one_le hsub
    · intro j _
      linarith [excess_nonneg (ε := ε) hK j]
    · intro j _ _
      exact le_add_of_nonneg_right (excess_nonneg (ε := ε) hK j)
  have hprodR := hprod.trans (hNR n hRn)
  have hscaleN : 0 ≤ tailScale a N := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hibound : (N : ℝ) * tailScale a n ≤ (n : ℝ) * tailScale a N * R :=
    hi.trans (mul_le_mul_of_nonneg_left hprodR (mul_nonneg hn0 hscaleN))
  dsimp [A]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show (0 : ℝ) < N by exact_mod_cast hNpos)).2
  nlinarith [hibound]

/-- The displayed short-paper upper bound implies eventual boundedness of the
exact product defect. -/
private theorem productDefect_bounded_of_inclusive
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε)
    (hγ : ∃ N : ℕ, ∀ n, N ≤ n →
      growthDefect a n ≤ 1 / (n : ℝ) + excess K ε n) :
    ∃ M : ℝ, ∃ N : ℕ, ∀ n, N ≤ n → productDefect a n ≤ M := by
  obtain ⟨A, hA, N0, hscale⟩ := tailScale_le_linear_of_inclusive a hpos hK hε hγ
  obtain ⟨N1, hN1⟩ := hγ
  refine ⟨A * (1 + K), max 1 (max N0 N1), ?_⟩
  intro n hn
  have hnNat : 1 ≤ n := (Nat.le_max_left 1 (max N0 N1)).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hscale' := hscale n ((Nat.le_max_left N0 N1).trans
    ((Nat.le_max_right 1 (max N0 N1)).trans hn))
  have hg := hN1 n ((Nat.le_max_right N0 N1).trans
    ((Nat.le_max_right 1 (max N0 N1)).trans hn))
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnNat) (by linarith : (1 : ℝ) ≤ 1 + ε)
  have hδle : excess K ε n ≤ K / (n : ℝ) := by
    dsimp [excess]
    exact div_le_div_of_nonneg_left hK hnpos hpow
  have hγle : growthDefect a n ≤ (1 + K) / (n : ℝ) := by
    calc
      growthDefect a n ≤ 1 / (n : ℝ) + excess K ε n := hg
      _ ≤ 1 / (n : ℝ) + K / (n : ℝ) := by gcongr
      _ = (1 + K) / (n : ℝ) := by ring
  have ht0 : 0 ≤ tailScale a n :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  unfold productDefect
  change tailScale a n * growthDefect a n ≤ A * (1 + K)
  calc
    tailScale a n * growthDefect a n ≤
        tailScale a n * ((1 + K) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hγle ht0
    _ ≤ (A * (n : ℝ)) * ((1 + K) / (n : ℝ)) := by
      gcongr
    _ = A * (1 + K) := by field_simp

/-- **Inclusive one-sided `1/n` threshold (`short243:res:inclusiveone`).**
The paper's rational value is represented exactly as `p/q`.  Its eventual
upper bound includes the endpoint coefficient one and an arbitrary summable
power excess. -/
theorem original_coordinate_inclusive_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∃ N : ℕ, ∀ n, N ≤ n →
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 ≤
        1 / (n : ℝ) + K / (n : ℝ) ^ (1 + ε)) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  apply original_coordinate_bounded_defect a ha hpos p q hq hs hgrowth
  apply productDefect_bounded_of_inclusive a hpos hK hε
  simpa only [growthDefect, excess] using hbound

/-- The explicitly mentioned pointwise endpoint `gamma_n ≤ 1/n` is the
special case `K=0` of the inclusive theorem. -/
theorem original_coordinate_inclusive_one_pointwise
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hbound : ∃ N : ℕ, ∀ n, N ≤ n →
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 ≤ 1 / (n : ℝ)) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  apply original_coordinate_inclusive_one a ha hpos p q hq hs hgrowth 0 1
  · norm_num
  · norm_num
  obtain ⟨N, hN⟩ := hbound
  refine ⟨N, fun n hn => ?_⟩
  simpa using hN n hn

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one_pointwise

end ErdosProblems.Erdos243.PaperCompleteR20
