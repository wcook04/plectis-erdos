import ErdosProblems.Erdos257.PaperCompleteR8.OptimizedCoverBudget

/-!
# Finite families do not lower the optimised fractional cover cost

The residual on clause 1 of the long Erdős #257 `cor` "finite-functional
separation" (`paper/reasoning-parts/erdos257/a257_front.tex:9369`).

The paper's `K_*(F)` in display `eq:257-optimised-cover-cost` is the infimum of
the fractional-cover cost over **finite or countable** families of frames.  The
tree's `optimizedLogCoverCost A` is the infimum over `LogBudgetCover A`, whose
frames are indexed by all of `ℕ` with weights strictly positive and summing to
one.  Those `ℕ`-indexed families are a subset of the paper's admissible
families, so `optimizedLogCoverCost A ≥ K_*(F)` and the tree's inequality
`condExceedProb ≤ optimizedLogCoverCost` is a priori weaker than the paper's
display.

`optimizedLogCoverCost_le_of_finite` closes that gap: every **finite** family
`(F_j, α_j, η_j, c_{j,d})_{j < N}` with `∑_{j<N} η_j = 1` has cost at least
`optimizedLogCoverCost A`.  The proof is the paper's own remark that "covers of
infinite cost do not lower the infimum" turned around: pad the finite family out
to an `ℕ`-indexed one by giving every index the extra weight `δ 2^{-(j+1)}` and
every index `j ≥ N` the empty frame with zero coefficients.  The padded weights
are strictly positive and sum to `(1-δ) + δ = 1`, the padded frames still cover
`A`, the padded columns contribute nothing to the cost, and each surviving
column's weight is at least `(1-δ) η_j`, so — using `α_j ≤ 1` — the padded cost
is at most `(1-δ)^{-1}` times the finite cost.  Letting `δ` tend to zero gives
the claim.

Consequence, which is what clause 1 needs: since the `ℕ`-indexed costs are among
the paper's admissible costs and every finite admissible cost dominates their
infimum, the infimum over finite-or-countable families equals
`optimizedLogCoverCost A`.  Composing that with
`sup_condExceedProb_le_optimizedLogCoverCost` in
`ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCoverLowerBound.lean` gives
`eq:257-arithmetic-cover-lower` for the paper's own `K_*(F)`.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Finset
open ErdosProblems.Erdos257.PaperCompleteR8

/-- The paper's cost `∑_j C_j η_j^{-α_j}/(2^{α_j}-1)` of a finite family. -/
def finiteCoverCost (N : ℕ) (weight exponent : ℕ → ℝ) (coefficient : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N,
    (∑' d : ℕ, coefficient j d / (d : ℝ)) / (weight j ^ exponent j)
      / ((2 : ℝ) ^ exponent j - 1)

theorem two_rpow_sub_one_pos {α : ℝ} (hα : 0 < α) : 0 < (2 : ℝ) ^ α - 1 := by
  have h : (1 : ℝ) < (2 : ℝ) ^ α :=
    Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, hα⟩)
  linarith

theorem tsum_coefficient_div_nonneg {c : ℕ → ℝ} (hc : ∀ d, 0 < d → 0 ≤ c d) :
    0 ≤ ∑' d : ℕ, c d / (d : ℝ) := by
  refine tsum_nonneg fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · exact div_nonneg (hc d hd) (Nat.cast_nonneg d)

theorem finiteCoverCost_nonneg (N : ℕ) (weight exponent : ℕ → ℝ)
    (coefficient : ℕ → ℕ → ℝ) (hwpos : ∀ j, j < N → 0 < weight j)
    (hexp : ∀ j, 0 < exponent j ∧ exponent j ≤ 1)
    (hc0 : ∀ j d, 0 < d → 0 ≤ coefficient j d) :
    0 ≤ finiteCoverCost N weight exponent coefficient := by
  unfold finiteCoverCost
  refine Finset.sum_nonneg fun j hj => ?_
  have hjN : j < N := Finset.mem_range.mp hj
  have hw : (0 : ℝ) < weight j ^ exponent j := Real.rpow_pos_of_pos (hwpos j hjN) _
  have hB : (0 : ℝ) < (2 : ℝ) ^ exponent j - 1 := two_rpow_sub_one_pos (hexp j).1
  exact div_nonneg (div_nonneg (tsum_coefficient_div_nonneg (hc0 j)) hw.le) hB.le

theorem admissibleLogCoverCost_nonneg {A : Set ℕ} {x : ℝ}
    (hx : x ∈ admissibleLogCoverCosts A) : 0 ≤ x := by
  obtain ⟨C, rfl⟩ := hx
  refine tsum_nonneg fun j => ?_
  have hw : (0 : ℝ) < C.weight j ^ C.exponent j := Real.rpow_pos_of_pos (C.weight_positive j) _
  have hB : (0 : ℝ) < (2 : ℝ) ^ C.exponent j - 1 :=
    two_rpow_sub_one_pos (C.exponent_bounds j).1
  exact div_nonneg
    (div_nonneg (tsum_coefficient_div_nonneg (fun d hd => C.coefficient_nonneg j d hd)) hw.le)
    hB.le

theorem bddBelow_admissibleLogCoverCosts (A : Set ℕ) :
    BddBelow (admissibleLogCoverCosts A) :=
  ⟨0, fun _ hx => admissibleLogCoverCost_nonneg hx⟩

/-- Padding a finite family out to an `ℕ`-indexed one: for every `0 < δ < 1`
there is a genuine `LogBudgetCover A` of cost at most `(1-δ)^{-1}` times the
finite cost. -/
theorem exists_logBudgetCover_le_of_finite {A : Set ℕ} (N : ℕ)
    (frame : ℕ → Finset ℕ) (weight exponent : ℕ → ℝ) (coefficient : ℕ → ℕ → ℝ)
    (hframe0 : ∀ j, 0 ∉ frame j)
    (hwpos : ∀ j, j < N → 0 < weight j)
    (hwsum : ∑ j ∈ Finset.range N, weight j = 1)
    (hexp : ∀ j, 0 < exponent j ∧ exponent j ≤ 1)
    (hc0 : ∀ j d, 0 < d → 0 ≤ coefficient j d)
    (hcol : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ)))
    (hcov : ∀ a ∈ A, ∃ j, j < N ∧ a ∈ frame j)
    (hmaj : ∀ j n, 0 < n →
      (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j
        ≤ ∑ d ∈ n.divisors, coefficient j d)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : LogBudgetCover A,
      C.cost ≤ finiteCoverCost N weight exponent coefficient / (1 - δ) := by
  classical
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  set w' : ℕ → ℝ :=
    fun j => (1 - δ) * (if j < N then weight j else 0) + δ * (1 / 2 : ℝ) ^ (j + 1) with hw'
  have hw'pos : ∀ j, 0 < w' j := by
    intro j
    have h1 : (0 : ℝ) ≤ (1 - δ) * (if j < N then weight j else 0) := by
      refine mul_nonneg h1δ.le ?_
      split_ifs with h
      · exact (hwpos j h).le
      · exact le_rfl
    have h2 : (0 : ℝ) < δ * (1 / 2 : ℝ) ^ (j + 1) := by positivity
    rw [hw']
    linarith
  have hw'ge : ∀ j, j < N → (1 - δ) * weight j ≤ w' j := by
    intro j hj
    have h2 : (0 : ℝ) < δ * (1 / 2 : ℝ) ^ (j + 1) := by positivity
    simp only [hw', if_pos hj]
    linarith
  have hu : HasSum (fun j : ℕ => (1 - δ) * (if j < N then weight j else 0)) (1 - δ) := by
    have hzero : ∀ b ∉ Finset.range N,
        (1 - δ) * (if b < N then weight b else 0) = 0 := by
      intro b hb
      rw [if_neg (by simpa using hb), mul_zero]
    have h : HasSum (fun j : ℕ => (1 - δ) * (if j < N then weight j else 0))
        (∑ j ∈ Finset.range N, (1 - δ) * (if j < N then weight j else 0)) :=
      hasSum_sum_of_ne_finset_zero hzero
    have hsum : (∑ j ∈ Finset.range N, (1 - δ) * (if j < N then weight j else 0))
        = 1 - δ := by
      have hcongr : ∀ j ∈ Finset.range N,
          (1 - δ) * (if j < N then weight j else 0) = (1 - δ) * weight j := by
        intro j hj
        rw [if_pos (Finset.mem_range.mp hj)]
      rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, hwsum, mul_one]
    rwa [hsum] at h
  have hv : HasSum (fun j : ℕ => δ * (1 / 2 : ℝ) ^ (j + 1)) δ := by
    have h := hasSum_geometric_two.mul_left (δ / 2)
    have hfun : (fun n : ℕ => (δ / 2) * (1 / 2 : ℝ) ^ n)
        = fun j : ℕ => δ * (1 / 2 : ℝ) ^ (j + 1) := by
      funext n
      rw [pow_succ]
      ring
    rw [hfun] at h
    have hval : δ / 2 * 2 = δ := by ring
    rwa [hval] at h
  refine ⟨{
    frame := fun j => if j < N then frame j else ∅
    weight := w'
    exponent := fun j => if j < N then exponent j else 1
    coefficient := fun j d => if j < N then coefficient j d else 0
    frame_positive := by
      intro j
      by_cases h : j < N
      · simpa [h] using hframe0 j
      · simp [h]
    weight_positive := hw'pos
    weight_sum := by
      have h := hu.add hv
      have hval : (1 - δ) + δ = 1 := by ring
      rw [hval] at h
      exact h
    exponent_bounds := by
      intro j
      by_cases h : j < N
      · simpa [h] using hexp j
      · simp [h]
    coefficient_nonneg := by
      intro j d hd
      by_cases h : j < N
      · simpa [h] using hc0 j d hd
      · simp [h]
    column_summable := by
      intro j
      by_cases h : j < N
      · simpa [h] using hcol j
      · simpa [h] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    covers := by
      intro a ha
      obtain ⟨j, hj, hmem⟩ := hcov a ha
      exact ⟨j, by simpa [hj] using hmem⟩
    majorises := by
      intro j n hn
      by_cases h : j < N
      · simpa [h] using hmaj j n hn
      · simp [h, Real.rpow_one]
    budget_summable := by
      refine summable_of_ne_finset_zero (s := Finset.range N) ?_
      intro j hj
      have hjN : ¬ j < N := by simpa using hj
      simp [hjN]
  }, ?_⟩
  have hterm0 : ∀ j, ¬ j < N →
      (∑' d : ℕ, (if j < N then coefficient j d else 0) / (d : ℝ))
          / (w' j ^ (if j < N then exponent j else 1))
          / ((2 : ℝ) ^ (if j < N then exponent j else 1) - 1) = 0 := by
    intro j hj
    simp [hj]
  have hcost : (∑' j : ℕ,
      (∑' d : ℕ, (if j < N then coefficient j d else 0) / (d : ℝ))
        / (w' j ^ (if j < N then exponent j else 1))
        / ((2 : ℝ) ^ (if j < N then exponent j else 1) - 1))
      = ∑ j ∈ Finset.range N,
        (∑' d : ℕ, coefficient j d / (d : ℝ)) / (w' j ^ exponent j)
          / ((2 : ℝ) ^ exponent j - 1) := by
    rw [tsum_eq_sum (s := Finset.range N)
      (fun j hj => hterm0 j (by simpa using hj))]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [if_pos (Finset.mem_range.mp hj)]
    simp only [if_pos (Finset.mem_range.mp hj)]
  show (∑' j : ℕ,
      (∑' d : ℕ, (if j < N then coefficient j d else 0) / (d : ℝ))
        / (w' j ^ (if j < N then exponent j else 1))
        / ((2 : ℝ) ^ (if j < N then exponent j else 1) - 1))
    ≤ finiteCoverCost N weight exponent coefficient / (1 - δ)
  rw [hcost]
  have hbound : ∀ j ∈ Finset.range N,
      (∑' d : ℕ, coefficient j d / (d : ℝ)) / (w' j ^ exponent j)
          / ((2 : ℝ) ^ exponent j - 1)
        ≤ (1 / (1 - δ)) *
          ((∑' d : ℕ, coefficient j d / (d : ℝ)) / (weight j ^ exponent j)
            / ((2 : ℝ) ^ exponent j - 1)) := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hA : (0 : ℝ) ≤ ∑' d : ℕ, coefficient j d / (d : ℝ) :=
      tsum_coefficient_div_nonneg (hc0 j)
    have hwj : (0 : ℝ) < weight j := hwpos j hjN
    have hwα : (0 : ℝ) < weight j ^ exponent j := Real.rpow_pos_of_pos hwj _
    have hW : (0 : ℝ) < w' j ^ exponent j := Real.rpow_pos_of_pos (hw'pos j) _
    have hB : (0 : ℝ) < (2 : ℝ) ^ exponent j - 1 := two_rpow_sub_one_pos (hexp j).1
    have hstep1 : ((1 - δ) * weight j) ^ exponent j ≤ w' j ^ exponent j :=
      Real.rpow_le_rpow (by positivity) (hw'ge j hjN) (hexp j).1.le
    have hstep2 : ((1 - δ) * weight j) ^ exponent j
        = (1 - δ) ^ exponent j * weight j ^ exponent j :=
      Real.mul_rpow h1δ.le hwj.le
    have hstep3 : (1 - δ) ≤ (1 - δ) ^ exponent j := by
      have h := Real.rpow_le_rpow_of_exponent_ge h1δ (by linarith) (hexp j).2
      rwa [Real.rpow_one] at h
    have hlow : (1 - δ) * (weight j ^ exponent j) ≤ w' j ^ exponent j := by
      have hmul : (1 - δ) * (weight j ^ exponent j)
          ≤ (1 - δ) ^ exponent j * weight j ^ exponent j :=
        mul_le_mul_of_nonneg_right hstep3 hwα.le
      rw [← hstep2] at hmul
      linarith
    have hpos : (0 : ℝ) < (1 - δ) * (weight j ^ exponent j) := by positivity
    have hdiv : (∑' d : ℕ, coefficient j d / (d : ℝ)) / (w' j ^ exponent j)
        ≤ (∑' d : ℕ, coefficient j d / (d : ℝ)) / ((1 - δ) * (weight j ^ exponent j)) := by
      rw [div_le_div_iff₀ hW hpos]
      nlinarith
    have hfinal : (∑' d : ℕ, coefficient j d / (d : ℝ))
          / ((1 - δ) * (weight j ^ exponent j)) / ((2 : ℝ) ^ exponent j - 1)
        = (1 / (1 - δ)) *
          ((∑' d : ℕ, coefficient j d / (d : ℝ)) / (weight j ^ exponent j)
            / ((2 : ℝ) ^ exponent j - 1)) := by
      field_simp
    calc (∑' d : ℕ, coefficient j d / (d : ℝ)) / (w' j ^ exponent j)
          / ((2 : ℝ) ^ exponent j - 1)
        ≤ (∑' d : ℕ, coefficient j d / (d : ℝ))
            / ((1 - δ) * (weight j ^ exponent j)) / ((2 : ℝ) ^ exponent j - 1) := by
          exact div_le_div_of_nonneg_right hdiv hB.le
      _ = _ := hfinal
  calc (∑ j ∈ Finset.range N,
        (∑' d : ℕ, coefficient j d / (d : ℝ)) / (w' j ^ exponent j)
          / ((2 : ℝ) ^ exponent j - 1))
      ≤ ∑ j ∈ Finset.range N, (1 / (1 - δ)) *
          ((∑' d : ℕ, coefficient j d / (d : ℝ)) / (weight j ^ exponent j)
            / ((2 : ℝ) ^ exponent j - 1)) := Finset.sum_le_sum hbound
    _ = finiteCoverCost N weight exponent coefficient / (1 - δ) := by
        rw [← Finset.mul_sum]
        unfold finiteCoverCost
        field_simp

/-- Clause 1's residual: the tree's `ℕ`-indexed infimum is at most the cost of
every **finite** admissible family, so the paper's infimum over finite or
countable families is the same number. -/
theorem optimizedLogCoverCost_le_of_finite {A : Set ℕ} (N : ℕ)
    (frame : ℕ → Finset ℕ) (weight exponent : ℕ → ℝ) (coefficient : ℕ → ℕ → ℝ)
    (hframe0 : ∀ j, 0 ∉ frame j)
    (hwpos : ∀ j, j < N → 0 < weight j)
    (hwsum : ∑ j ∈ Finset.range N, weight j = 1)
    (hexp : ∀ j, 0 < exponent j ∧ exponent j ≤ 1)
    (hc0 : ∀ j d, 0 < d → 0 ≤ coefficient j d)
    (hcol : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ)))
    (hcov : ∀ a ∈ A, ∃ j, j < N ∧ a ∈ frame j)
    (hmaj : ∀ j n, 0 < n →
      (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j
        ≤ ∑ d ∈ n.divisors, coefficient j d) :
    optimizedLogCoverCost A ≤ finiteCoverCost N weight exponent coefficient := by
  set c₀ : ℝ := finiteCoverCost N weight exponent coefficient with hc₀
  have hc₀0 : 0 ≤ c₀ := finiteCoverCost_nonneg N weight exponent coefficient hwpos hexp hc0
  by_contra hcon
  push_neg at hcon
  set K : ℝ := optimizedLogCoverCost A with hK
  have hKpos : 0 < K := lt_of_le_of_lt hc₀0 hcon
  set δ : ℝ := (K - c₀) / (2 * K) with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]
    apply div_pos (by linarith)
    linarith
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by linarith)]
    linarith
  obtain ⟨C, hC⟩ := exists_logBudgetCover_le_of_finite N frame weight exponent coefficient
    hframe0 hwpos hwsum hexp hc0 hcol hcov hmaj hδ0 hδ1
  have hKle : K ≤ C.cost := csInf_le (bddBelow_admissibleLogCoverCosts A) ⟨C, rfl⟩
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  have hlt : c₀ / (1 - δ) < K := by
    rw [div_lt_iff₀ h1δ, hδ]
    have hKne : K ≠ 0 := ne_of_gt hKpos
    field_simp
    nlinarith
  linarith

/-! ### The paper's infimum over finite or countable families -/

/-- The costs of the paper's **finite** admissible fractional covers of `A`. -/
def finiteLogCoverCosts (A : Set ℕ) : Set ℝ :=
  {K : ℝ | ∃ (N : ℕ) (frame : ℕ → Finset ℕ) (weight exponent : ℕ → ℝ)
      (coefficient : ℕ → ℕ → ℝ),
    (∀ j, 0 ∉ frame j) ∧
    (∀ j, j < N → 0 < weight j) ∧
    (∑ j ∈ Finset.range N, weight j = 1) ∧
    (∀ j, 0 < exponent j ∧ exponent j ≤ 1) ∧
    (∀ j d, 0 < d → 0 ≤ coefficient j d) ∧
    (∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))) ∧
    (∀ a ∈ A, ∃ j, j < N ∧ a ∈ frame j) ∧
    (∀ j n, 0 < n →
      (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j
        ≤ ∑ d ∈ n.divisors, coefficient j d) ∧
    K = finiteCoverCost N weight exponent coefficient}

theorem finiteLogCoverCost_nonneg {A : Set ℕ} {x : ℝ}
    (hx : x ∈ finiteLogCoverCosts A) : 0 ≤ x := by
  obtain ⟨N, fr, w, e, c, -, hwpos, -, hexp, hc0, -, -, -, rfl⟩ := hx
  exact finiteCoverCost_nonneg N w e c hwpos hexp hc0

/-- The paper's `K_*(F)` of display `eq:257-optimised-cover-cost`: the infimum
of the fractional-cover cost over **finite or countable** families. -/
def paperCoverCost (A : Set ℕ) : ℝ :=
  sInf (admissibleLogCoverCosts A ∪ finiteLogCoverCosts A)

/-- Clause 1's residual, closed: allowing finite families as well as countable
ones does not lower the infimum, so the paper's `K_*(F)` is exactly the tree's
`optimizedLogCoverCost`. -/
theorem paperCoverCost_eq_optimizedLogCoverCost (A : Set ℕ)
    (hne : (admissibleLogCoverCosts A).Nonempty) :
    paperCoverCost A = optimizedLogCoverCost A := by
  have hbdd : BddBelow (admissibleLogCoverCosts A ∪ finiteLogCoverCosts A) := by
    refine ⟨0, ?_⟩
    rintro x (hx | hx)
    · exact admissibleLogCoverCost_nonneg hx
    · exact finiteLogCoverCost_nonneg hx
  refine le_antisymm ?_ ?_
  · exact csInf_le_csInf hbdd hne Set.subset_union_left
  · refine le_csInf (Set.Nonempty.mono Set.subset_union_left hne) ?_
    rintro x (hx | hx)
    · exact csInf_le (bddBelow_admissibleLogCoverCosts A) hx
    · obtain ⟨N, fr, w, e, c, h1, h2, h3, h4, h5, h6, h7, h8, rfl⟩ := hx
      exact optimizedLogCoverCost_le_of_finite N fr w e c h1 h2 h3 h4 h5 h6 h7 h8

#print axioms two_rpow_sub_one_pos
#print axioms bddBelow_admissibleLogCoverCosts
#print axioms exists_logBudgetCover_le_of_finite
#print axioms optimizedLogCoverCost_le_of_finite
#print axioms finiteLogCoverCost_nonneg
#print axioms paperCoverCost_eq_optimizedLogCoverCost

end ErdosProblems.Erdos257.PaperCompleteR21

end
