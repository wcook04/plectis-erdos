import ErdosProblems.Erdos243.PaperCompleteR20.InclusiveOne

/-!
# Erdős 243: the product-ratio criterion and the `1/n` threshold

This file supplies the strict clause of `long243:res:onethreshold` and gives
a home to the two clauses of that corollary, and to the bounded clause of
`long243:res:strausbounded`, that the tree already states.

The paper's quantities in one-based indexing are
`P_n = a_1 ⋯ a_{n-1}`, `t_n = P_n / a_n`, `γ_n = a_n²/a_{n+1} - 1` and
`Q_n = t_n γ_n`.  The tree's `prefixProduct a n = ∏_{j < n} a j` and
`productDefect a n = (prefixProduct a n / a n) (a n ²/a (n+1) - 1)` are these
in zero-based indexing.

The strict clause says: if `limsup n (γ_n)_+ < 1`, the sequence is eventually
Sylvester.  The hypothesis is carried in the form that is equivalent to that
limsup bound, namely: there is an `r < 1` with `n (γ_n)_+ ≤ r` for all large
`n`.  The proof is the paper's, in the sharper telescoping form: from
`n (γ_n)_+ ≤ r ≤ 1` one gets `t_{n+1}/t_n = 1 + γ_n ≤ (n+1)/n`, so
`N t_n ≤ t_N n`, and hence `Q_n = t_n γ_n ≤ t_N r`.  The bounded-defect
criterion then applies.  No asymptotic estimate `t_n = O(n^r)` is needed.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open ErdosProblems.Erdos243.PaperCompleteR7

/-- The paper's product ratio `t_n = P_n / a_n`. -/
def productRatio (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ)

theorem productRatio_pos (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (n : ℕ) :
    0 < productRatio a n := by
  have h1 : (0 : ℝ) < (prefixProduct a n : ℝ) := by
    exact_mod_cast prefixProduct_pos a hpos n
  have h2 : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hpos n
  exact div_pos h1 h2

/-- The consecutive-ratio identity `t_{n+1}/t_n = a_n²/a_{n+1}`. -/
theorem productRatio_succ (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (n : ℕ) :
    productRatio a (n + 1)
      = productRatio a n * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) := by
  have h2 : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hpos n
  have h3 : (0 : ℝ) < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
  have h2' : (a n : ℝ) ≠ 0 := ne_of_gt h2
  have h3' : (a (n + 1) : ℝ) ≠ 0 := ne_of_gt h3
  simp only [productRatio, prefixProduct_succ, Nat.cast_mul]
  field_simp

/-- The telescoping growth bound.  If `n γ_n ≤ r ≤ 1` for every `n ≥ N`, then
`N t_n ≤ t_N n` for every `n ≥ N`: each step multiplies `t` by at most
`(n+1)/n`, and those factors telescope. -/
theorem natCast_mul_productRatio_le
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (r : ℝ) (hr : r ≤ 1) (N : ℕ)
    (hbound : ∀ n, N ≤ n →
      (n : ℝ) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) ≤ r)
    {n : ℕ} (hn : N ≤ n) :
    (N : ℝ) * productRatio a n ≤ productRatio a N * (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => exact le_of_eq (mul_comm _ _)
  | succ n hn ih =>
      have h2 : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hpos n
      have h3 : (0 : ℝ) < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
      have hrho : (0 : ℝ) < (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) := by positivity
      have hT : (0 : ℝ) < productRatio a N := productRatio_pos a hpos N
      have hstep : (n : ℝ) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) ≤ (n : ℝ) + 1 := by
        have h := hbound n hn
        have hexp : (n : ℝ) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
            = (n : ℝ) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) - (n : ℝ) := by ring
        rw [hexp] at h
        linarith
      calc (N : ℝ) * productRatio a (n + 1)
          = ((N : ℝ) * productRatio a n) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) := by
            rw [productRatio_succ a hpos n]; ring
        _ ≤ (productRatio a N * (n : ℝ)) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) :=
            mul_le_mul_of_nonneg_right ih hrho.le
        _ = productRatio a N * ((n : ℝ) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ))) := by
            ring
        _ ≤ productRatio a N * ((n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hstep hT.le
        _ = productRatio a N * ((n + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **The strict clause of `long243:res:onethreshold`.**
Let `a` be strictly increasing positive integers with `a_{n+1}/a_n² → 1` and
`∑ 1/a_n = p/q`.  If `limsup n (a_n²/a_{n+1} - 1)_+ < 1`, carried here as an
`r < 1` with `n (a_n²/a_{n+1} - 1)_+ ≤ r` for all large `n`, then
`a_{n+1} = a_n² - a_n + 1` for all large `n`. -/
theorem original_coordinate_strict_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (r : ℝ) (hr : r < 1)
    (hlimsup : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) * max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) 0 ≤ r) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  obtain ⟨N, hN1, hN0⟩ : ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (n : ℝ) * max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) 0 ≤ r := by
    obtain ⟨N0, hN0⟩ := hlimsup
    exact ⟨max N0 1, le_max_right _ _,
      fun n hn ↦ hN0 n ((le_max_left N0 1).trans hn)⟩
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hr0 : 0 ≤ r := by
    have h := hN0 N le_rfl
    have hmax : (0 : ℝ) ≤ max ((a N : ℝ) ^ 2 / (a (N + 1) : ℝ) - 1) 0 :=
      le_max_right _ _
    have hprod : (0 : ℝ) ≤ (N : ℝ) *
        max ((a N : ℝ) ^ 2 / (a (N + 1) : ℝ) - 1) 0 :=
      mul_nonneg (by linarith) hmax
    linarith
  have hbound : ∀ n, N ≤ n →
      (n : ℝ) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) ≤ r := by
    intro n hn
    have h := hN0 n hn
    have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmax : (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1
        ≤ max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) 0 := le_max_left _ _
    have h3 : (n : ℝ) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
        ≤ (n : ℝ) * max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) 0 :=
      mul_le_mul_of_nonneg_left hmax hnR
    linarith
  apply original_coordinate_bounded_defect a ha hpos p q hq hs hgrowth
  refine ⟨productRatio a N * r, N, fun n hn ↦ ?_⟩
  have hT : (0 : ℝ) < productRatio a N := productRatio_pos a hpos N
  have ht : (0 : ℝ) < productRatio a n := productRatio_pos a hpos n
  have hkey : (N : ℝ) * productRatio a n ≤ productRatio a N * (n : ℝ) :=
    natCast_mul_productRatio_le a hpos r hr.le N hbound hn
  have hQ : productDefect a n
      = productRatio a n * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) := rfl
  rw [hQ]
  by_cases hg0 : (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 ≤ 0
  · have h1 : productRatio a n * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) ≤ 0 := by
      nlinarith [ht.le, hg0]
    have h2 : (0 : ℝ) ≤ productRatio a N * r := mul_nonneg hT.le hr0
    linarith
  · have hg : (0 : ℝ) < (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 := not_le.mp hg0
    have hchain :
        (N : ℝ) * (productRatio a n * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1))
          ≤ productRatio a N * r := by
      calc (N : ℝ) * (productRatio a n *
              ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1))
          = ((N : ℝ) * productRatio a n) *
              ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) := by ring
        _ ≤ (productRatio a N * (n : ℝ)) *
              ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) :=
            mul_le_mul_of_nonneg_right hkey hg.le
        _ = productRatio a N *
              ((n : ℝ) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)) := by ring
        _ ≤ productRatio a N * r :=
            mul_le_mul_of_nonneg_left (hbound n hn) hT.le
    have hpos2 : (0 : ℝ) <
        productRatio a n * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) :=
      mul_pos ht hg
    nlinarith [hchain, hpos2, hNR]

/-! ## Homes for the clauses already stated in the tree

`original_coordinate_bounded_defect` is the bounded clause of
`long243:res:strausbounded`: its `productDefect` is the paper's `Q_n`, and
`limsup Q_n < ∞` is carried as an eventual upper bound.
`original_coordinate_inclusive_one` is the inclusive clause of
`long243:res:onethreshold`, and `original_coordinate_inclusive_one_pointwise`
is that corollary's final sentence "in particular the one-sided bound by
`1/n` is included", the case `K = 0`. -/

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.original_coordinate_strict_one
#print axioms ErdosProblems.Erdos243.PaperCompleteR7.original_coordinate_bounded_defect
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one
#print axioms ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one_pointwise

end ErdosProblems.Erdos243.PaperCompleteR21
