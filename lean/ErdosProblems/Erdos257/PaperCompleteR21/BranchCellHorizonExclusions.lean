import Erdos249257.HalfCylinderMiddleCarryLowerBound

/-!
Paper-form restatements of three asserted environments of the long Erdős #257
manuscript `paper/reasoning-parts/erdos257/a257_front.tex`:

* `prop:upper-unconditional` (line 7436) — the upper (carries) successor
  satisfies the next-row bound `rem (s+1) ≤ 2^(s+1)` with no exceptional-cell
  exclusion, because the reset identity writes `2^(s+1)` as `rem (s+1)` plus a
  nonnegative reset charge;
* `thm:cd-neg3-impossible` (line 7454) — at a final middle transition with
  `D ≥ 13`, `belowPulse D + 2 ≤ 4 * rem D`, i.e. `C_D ≥ -2`, so the cell
  `C_D = -3` and every more negative value is excluded;
* `cor:cd-remaining` (line 7508) — consequently only `-2` and `-1` remain
  inside the exceptional set `{-3, -2, -1}`.

Here `C_D = 4 * rem D - belowPulse D - 4` is the signed producer-carry
coordinate of the manuscript (displayed at line 7430 and line 7533).
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy

/-! ## `prop:upper-unconditional` -/

/-- Long `prop:upper-unconditional`.  Both asserted clauses at a row `s ≥ 5`
whose adjacent cut carries: the next remainder is at most `2^(s+1)`, and the
reset identity expresses `2^(s+1)` as that remainder plus the (nonnegative)
reset charge `4 * overshoot + abovePulse`. -/
theorem paper_upper_branch_needs_no_exceptional_cell {s : ℕ} (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) ∧
      0 ≤ 4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse ∧
      seamIntegerGreedyRemainder (s + 1) +
          (4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse) =
        2 ^ (s + 1) :=
  ⟨seamUpperBranch_nextRemainder_le_pow hs hcarry, Nat.zero_le _,
    seamUpperBranch_remainder_add_resetCharge_eq hs hcarry⟩

/-! ## `thm:cd-neg3-impossible` and `cor:cd-remaining` -/

/-- Long `thm:cd-neg3-impossible`, all three asserted clauses.  Hypotheses: a
middle transition at row `D ≥ 13` (no carry, plus the middle-branch
inequality) followed by an all-right tail.  Conclusions: the displayed bound
`belowPulse D + 2 ≤ 4 * rem D`; equivalently `-2 ≤ C_D`; hence `C_D ≠ -3`,
and with it every more negative value. -/
theorem paper_final_middle_cell_at_least_neg_two
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (seamAdjacentCut D (by omega)).belowPulse + 2 ≤
        4 * (seamAdjacentCut D (by omega)).remainder ∧
      (-2 : ℤ) ≤ 4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ∧
      ∀ c : ℤ, c ≤ -3 →
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≠ c := by
  have hmain :=
    middleThenAllRight_landingExcess_two_le D hD13 hncarry hmiddle hright
  have hmainZ :
      ((seamAdjacentCut D (by omega : 5 ≤ D)).belowPulse : ℤ) + 2 ≤
        4 * ((seamAdjacentCut D (by omega : 5 ≤ D)).remainder : ℤ) := by
    exact_mod_cast hmain
  refine ⟨hmain, by omega, ?_⟩
  intro c hc hcell
  omega

/-- Long `cor:cd-remaining`.  Under the same final-middle hypotheses, the
exclusion of `-3` leaves exactly `-2` and `-1` inside the exceptional set
`{-3, -2, -1}`.  The statement is the implication: it does not assert that
`C_D` lies in that set, since nonnegative values are not excluded. -/
theorem paper_final_middle_cell_remaining_cells
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -3 ∨
          4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
              ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
            4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
                ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1) →
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
              ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1 := by
  have h := paper_final_middle_cell_at_least_neg_two D hD13 hncarry hmiddle hright
  intro hmem
  rcases hmem with hm | hm | hm
  · exact absurd hm (h.2.2 (-3) (by norm_num))
  · exact Or.inl hm
  · exact Or.inr hm

#print axioms paper_upper_branch_needs_no_exceptional_cell
#print axioms paper_final_middle_cell_at_least_neg_two
#print axioms paper_final_middle_cell_remaining_cells

-- The three tree theorems the manuscript cites inside the "Proof of the bound"
-- paragraph of `thm:cd-neg3-impossible` (the producer carry below its complete
-- incidence tail, the corrected-coordinate take-threshold bound, and the strict
-- `1/3` wall for the scaled Mersenne tail).
#print axioms Erdos249257.middleProducer_allRight_forces_carry_lt_tail
#print axioms Erdos249257.middleProducer_allRight_forces_floorZ_lt_takeThreshold
#print axioms Erdos249257.one_third_lt_scaledMersenneTail_floorWall

end ErdosProblems.Erdos257.PaperCompleteR21
