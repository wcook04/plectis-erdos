import Erdos249257.HalfCylinderLargestSkipGap
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.HalfTrappingReturnCarry
import ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowIdentity

/-!
Paper-form restatements of two asserted environments of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`:

* `lem:largest-false-rank-algebra` (line 3361) — the exact adjacent-word gap at
  the largest omitted rank, with the row-weight functional written as the literal
  floor sum `W_s(E) = ∑_{e ∈ E} ⌊4^s/(2^e−1)⌋`, plus the two branch-propagation
  clauses for the integer-greedy rows;
* `lem:reverse-carry-word` (line 3481) — the exact carry-difference spacing
  formula and the resulting terminal bound `2^L ≤ B₁ + B₂`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21
open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

/-! ## `lem:largest-false-rank-algebra` -/

/-- The paper's row-weight functional `W_s(E) = ∑_{e ∈ E} ⌊4^s/(2^e − 1)⌋`. -/
noncomputable def rowWeightSum (s : ℕ) (E : Finset ℕ) : ℤ :=
  ∑ e ∈ E, ⌊(4 : ℝ) ^ s / ((2 : ℝ) ^ e - 1)⌋

theorem rowWeightSum_eq_natSum (s : ℕ) (E : Finset ℕ) (hE : ∀ e ∈ E, 1 ≤ e) :
    rowWeightSum s E = ((∑ e ∈ E, truncatedMersenneWeight s e : ℕ) : ℤ) := by
  unfold rowWeightSum
  push_cast
  exact Finset.sum_congr rfl fun e he =>
    PaperCompleteR20.row_weight_floor s e (hE e he)

/-- Long `lem:largest-false-rank-algebra`, first clause.  For `2 ≤ d < s` with
`2s < 3d` and a common prefix `u ⊆ {2,…,d−1}`, with `E₋ = u ∪ {d+1,…,s−1}` and
`E₊ = u ∪ {d}`,
`3 W_s(E₋) + 3·2^{s+1} + 2·4^{s−d} + 4 = 3 W_s(E₊)`.
The correction is independent of `u`. -/
theorem largest_false_rank_algebra {s d : ℕ} {u : Finset ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d)
    (hlate : 2 * s < 3 * d) :
    3 * rowWeightSum s (u ∪ Finset.Ico (d + 1) s)
        + (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4)
      = 3 * rowWeightSum s (insert d u) := by
  classical
  have hdnotu : d ∉ u := fun hdu => absurd (hu d hdu).2 (Nat.lt_irrefl d)
  have hdisjoint : Disjoint u (Finset.Ico (d + 1) s) := by
    refine Finset.disjoint_left.mpr ?_
    intro e heu heI
    have h1 := (hu e heu).2
    have h2 := (Finset.mem_Ico.mp heI).1
    omega
  have hlowerPos : ∀ e ∈ u ∪ Finset.Ico (d + 1) s, 1 ≤ e := by
    intro e he
    rcases Finset.mem_union.mp he with heu | heI
    · exact le_trans (by omega) (hu e heu).1
    · have := (Finset.mem_Ico.mp heI).1; omega
  have hupperPos : ∀ e ∈ insert d u, 1 ≤ e := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · omega
    · exact le_trans (by omega) (hu e heu).1
  have hnat : 3 * (∑ e ∈ u ∪ Finset.Ico (d + 1) s, truncatedMersenneWeight s e)
        + (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4)
      = 3 * ∑ e ∈ insert d u, truncatedMersenneWeight s e := by
    rw [Finset.sum_union hdisjoint, Finset.sum_insert hdnotu,
      sum_truncatedMersenneWeight_Ico_eq_seamWeightsFrom_sum s (d + 1) (by omega)]
    have hgap := three_mul_tailWeight_add_exactLateGap_eq_three_mul_headWeight
      hd2 hds hlate
    omega
  rw [rowWeightSum_eq_natSum s _ hlowerPos, rowWeightSum_eq_natSum s _ hupperPos]
  exact_mod_cast hnat

/-- Long `lem:largest-false-rank-algebra`, second clause (right transition):
a right transition at row `s ≥ 5` preserves the largest omitted rank. -/
theorem largest_false_rank_right_preserves {s d : ℕ} (hs : 5 ≤ s)
    (hmax : IsLargestFalseRank (seamGreedyWord s) d)
    (hright : ¬ SeamGreedyUpperOrMiddleAt s hs) :
    IsLargestFalseRank (seamGreedyWord (s + 1)) d := by
  have hcarry : ¬ (seamAdjacentCut s hs).successorCarries :=
    fun h => hright (Or.inl h)
  have hnotMiddle : ¬ (4 * (seamAdjacentCut s hs).remainder +
      (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse <
      (seamAdjacentCut s hs).terminalWeight) :=
    fun h => hright (Or.inr ⟨hcarry, h⟩)
  exact IsLargestFalseRank.seamGreedyWord_succ_of_rightBranch hs hmax hcarry
    (Nat.not_lt.mp hnotMiddle)

/-- Long `lem:largest-false-rank-algebra`, third clause (upper or middle
transition): `s` becomes the largest omitted rank of the next row. -/
theorem largest_false_rank_upperOrMiddle_terminal {s : ℕ} (hs : 5 ≤ s)
    (hUM : SeamGreedyUpperOrMiddleAt s hs) :
    IsLargestFalseRank (seamGreedyWord (s + 1)) s :=
  seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle s hs hUM

/-- The whole of long `lem:largest-false-rank-algebra`. -/
theorem paper_largest_false_rank_algebra :
    (∀ (s d : ℕ) (u : Finset ℕ), 2 ≤ d → d < s → (∀ e ∈ u, 2 ≤ e ∧ e < d) →
        2 * s < 3 * d →
        3 * rowWeightSum s (u ∪ Finset.Ico (d + 1) s)
            + (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4)
          = 3 * rowWeightSum s (insert d u)) ∧
    (∀ (s d : ℕ) (hs : 5 ≤ s), IsLargestFalseRank (seamGreedyWord s) d →
        ¬ SeamGreedyUpperOrMiddleAt s hs →
        IsLargestFalseRank (seamGreedyWord (s + 1)) d) ∧
    (∀ (s : ℕ) (hs : 5 ≤ s), SeamGreedyUpperOrMiddleAt s hs →
        IsLargestFalseRank (seamGreedyWord (s + 1)) s) :=
  ⟨fun _ _ _ hd2 hds hu hlate => largest_false_rank_algebra hd2 hds hu hlate,
    fun _ _ hs hmax hright => largest_false_rank_right_preserves hs hmax hright,
    fun _ hs hUM => largest_false_rank_upperOrMiddle_terminal hs hUM⟩

/-! ## `lem:reverse-carry-word` -/

/-- Long `lem:reverse-carry-word`, spacing formula.  `a i` are the coefficients,
`b i` the output bits and `u i` the reverse carries of the two words; the seam
hypothesis is the paper's `b₁ k − b₂ k = 1` with agreeing coefficients. -/
theorem reverse_carry_word_spacing
    (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ)
    (h₁ : ∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1))
    (h₂ : ∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1))
    (k L : ℕ)
    (hcoeffSeam : a₁ k = a₂ k) (hbitSeam : b₁ k - b₂ k = 1)
    (hcoeff : ∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j))
    (hbit : ∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) :
    u₁ (k + L + 1) - u₂ (k + L + 1)
        = 2 ^ L * (2 * (u₁ k - u₂ k) + 1) ∧
      Odd (2 * (u₁ k - u₂ k) + 1) := by
  have hstep : ∀ m : ℕ,
      u₁ (m + 1) - u₂ (m + 1)
        = (b₁ m - b₂ m) + 2 * (u₁ m - u₂ m) - (a₁ m - a₂ m) := by
    intro m
    have e₁ := h₁ m
    have e₂ := h₂ m
    linarith
  have hseam : u₁ (k + 1) - u₂ (k + 1) = 2 * (u₁ k - u₂ k) + 1 := by
    rw [hstep k, hbitSeam, hcoeffSeam]
    ring
  have hdouble : ∀ j : ℕ, j ≤ L →
      u₁ (k + 1 + j) - u₂ (k + 1 + j)
        = 2 ^ j * (u₁ (k + 1) - u₂ (k + 1)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        have hs := hstep (k + 1 + n)
        rw [hcoeff n (by omega), hbit n (by omega)] at hs
        simp only [sub_self, zero_add, sub_zero] at hs
        rw [show k + 1 + (n + 1) = k + 1 + n + 1 from by omega, hs, hprev, pow_succ]
        ring
  refine ⟨?_, odd_two_mul_add_one _⟩
  rw [show k + L + 1 = k + 1 + L from by omega, hdouble L le_rfl, hseam]

/-- Long `lem:reverse-carry-word`, terminal bound.  Terminal carries with
absolute values at most `B₁` and `B₂` force `2^L ≤ B₁ + B₂`. -/
theorem reverse_carry_word_twoPow_le
    (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ)
    (h₁ : ∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1))
    (h₂ : ∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1))
    (k L : ℕ) (B₁ B₂ : ℝ)
    (hcoeffSeam : a₁ k = a₂ k) (hbitSeam : b₁ k - b₂ k = 1)
    (hcoeff : ∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j))
    (hbit : ∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j))
    (hB₁ : |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B₁)
    (hB₂ : |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B₂) :
    (2 : ℝ) ^ L ≤ B₁ + B₂ := by
  obtain ⟨heq, hodd⟩ := reverse_carry_word_spacing a₁ b₁ u₁ a₂ b₂ u₂ h₁ h₂ k L
    hcoeffSeam hbitSeam hcoeff hbit
  have hzne : (2 * (u₁ k - u₂ k) + 1) ≠ 0 := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hzabs : (1 : ℤ) ≤ |2 * (u₁ k - u₂ k) + 1| := Int.one_le_abs hzne
  have hpow : (0 : ℤ) ≤ (2 : ℤ) ^ L := by positivity
  have hlow : (2 : ℤ) ^ L ≤ |u₁ (k + L + 1) - u₂ (k + L + 1)| := by
    rw [heq, abs_mul, abs_of_nonneg hpow]
    nlinarith
  have hlowR : (2 : ℝ) ^ L
      ≤ |((u₁ (k + L + 1) : ℤ) : ℝ) - ((u₂ (k + L + 1) : ℤ) : ℝ)| := by
    exact_mod_cast hlow
  have htri : |((u₁ (k + L + 1) : ℤ) : ℝ) - ((u₂ (k + L + 1) : ℤ) : ℝ)|
      ≤ |((u₁ (k + L + 1) : ℤ) : ℝ)| + |((u₂ (k + L + 1) : ℤ) : ℝ)| := by
    have h1 := neg_abs_le ((u₁ (k + L + 1) : ℤ) : ℝ)
    have h2 := le_abs_self ((u₁ (k + L + 1) : ℤ) : ℝ)
    have h3 := neg_abs_le ((u₂ (k + L + 1) : ℤ) : ℝ)
    have h4 := le_abs_self ((u₂ (k + L + 1) : ℤ) : ℝ)
    rw [abs_le]
    constructor <;> linarith
  linarith

/-! The paper's final clause is a sharpness claim: under a common bound `B` the
conclusion is `2^L ≤ 2B`, **not** `2^L ≤ B`.  The witness below realises
`k = 0`, `L = 1`, `B = 1`, where both terminal carries have absolute value `1`
and `2^L = 2 > 1 = B`. -/

private def sharpCarryU₁ : ℕ → ℤ := fun m => if m ≤ 1 then 0 else -1
private def sharpCarryU₂ : ℕ → ℤ := fun _ => 1
private def sharpCarryB₁ : ℕ → ℤ := fun m => if m = 0 then 1 else 0
private def sharpCarryB₂ : ℕ → ℤ := fun _ => 0
private def sharpCarryA₁ : ℕ → ℤ :=
  fun m => sharpCarryB₁ m + 2 * sharpCarryU₁ m - sharpCarryU₁ (m + 1)
private def sharpCarryA₂ : ℕ → ℤ :=
  fun m => sharpCarryB₂ m + 2 * sharpCarryU₂ m - sharpCarryU₂ (m + 1)

/-- Long `lem:reverse-carry-word`, final clause: the common-bound conclusion is
`2^L ≤ 2B` and not `2^L ≤ B`, because a configuration satisfying every
hypothesis with a common bound `B` can have `B < 2^L`. -/
theorem reverse_carry_word_common_bound_sharp :
    ∃ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ) (k L : ℕ) (B : ℝ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) ∧
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) ∧
      a₁ k = a₂ k ∧ b₁ k - b₂ k = 1 ∧
      (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) ∧
      (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) ∧
      |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B ∧ |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B ∧
      ¬ ((2 : ℝ) ^ L ≤ B) := by
  refine ⟨sharpCarryA₁, sharpCarryB₁, sharpCarryU₁, sharpCarryA₂, sharpCarryB₂,
    sharpCarryU₂, 0, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m; simp only [sharpCarryA₁]; ring
  · intro m; simp only [sharpCarryA₂]; ring
  · norm_num [sharpCarryA₁, sharpCarryA₂, sharpCarryB₁, sharpCarryB₂,
      sharpCarryU₁, sharpCarryU₂]
  · norm_num [sharpCarryB₁, sharpCarryB₂]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    norm_num [sharpCarryA₁, sharpCarryA₂, sharpCarryB₁, sharpCarryB₂,
      sharpCarryU₁, sharpCarryU₂]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    norm_num [sharpCarryB₁, sharpCarryB₂]
  · norm_num [sharpCarryU₁]
  · norm_num [sharpCarryU₂]
  · norm_num

/-- The whole of long `lem:reverse-carry-word`, including the common-bound
specialisation `2^L ≤ 2B`. -/
theorem paper_reverse_carry_word :
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ k L : ℕ, a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        u₁ (k + L + 1) - u₂ (k + L + 1) = 2 ^ L * (2 * (u₁ k - u₂ k) + 1) ∧
          Odd (2 * (u₁ k - u₂ k) + 1)) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B₁ B₂ : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B₁ →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B₂ →
        (2 : ℝ) ^ L ≤ B₁ + B₂) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        (2 : ℝ) ^ L ≤ 2 * B) := by
  refine ⟨fun a₁ b₁ u₁ a₂ b₂ u₂ h₁ h₂ k L hc hb hco hbo =>
      reverse_carry_word_spacing a₁ b₁ u₁ a₂ b₂ u₂ h₁ h₂ k L hc hb hco hbo,
    fun a₁ b₁ u₁ a₂ b₂ u₂ h₁ h₂ k L B₁ B₂ hc hb hco hbo hB₁ hB₂ =>
      reverse_carry_word_twoPow_le a₁ b₁ u₁ a₂ b₂ u₂ h₁ h₂ k L B₁ B₂ hc hb hco hbo
        hB₁ hB₂,
    ?_⟩
  intro a₁ b₁ u₁ a₂ b₂ u₂ h₁ h₂ k L B hc hb hco hbo hB₁ hB₂
  have := reverse_carry_word_twoPow_le a₁ b₁ u₁ a₂ b₂ u₂ h₁ h₂ k L B B hc hb hco
    hbo hB₁ hB₂
  linarith

#print axioms paper_largest_false_rank_algebra
#print axioms largest_false_rank_algebra
#print axioms paper_reverse_carry_word
#print axioms reverse_carry_word_common_bound_sharp
end ErdosProblems.Erdos257.PaperCompleteR21
