import Erdos249257.HalfCylinderLargestSkipInduction
import Erdos249257.HalfCylinderProducerLowerBound
import Erdos249257.HalfCylinderFinalMiddleCellEscape

/-!
# The last seam producer versus an eventual right tail

If the integer seam were eventually right, the explicit false terminal at
row thirteen would have a last successor row `D` with false terminal.  That
last non-right transition is either an upper producer or a middle producer.

The upper case is impossible unconditionally: its terminal-augmented affine
carry is at most `-8`, while the eventual right tail puts the corresponding
lazy endpoint below `1/2`.

The middle case is reduced to the exact, weak inequality that its positive
affine carry beats the complete future divisor-incidence tail.  A convenient
stronger socket asks only for the already-proved square-root majorant.  This
is substantially weaker than the exponential largest-skip socket.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy

noncomputable section

/-! ## The remaining middle-producer socket -/

/-- Exact last-producer input: at every genuine middle transition, the
terminal-augmented below support has affine carry larger than its complete
future divisor-incidence tail. -/
def SeamMiddleProducerTailEscape : Prop :=
  ∀ (s : ℕ) (hs : 5 ≤ s), 13 ≤ s →
    ¬ (seamAdjacentCut s hs).successorCarries →
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight →
        binaryCoeffTail
            (supportCoeff
              (insert s
                (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)))
            (2 * s + 2) <
          (producerCarry
              (insert s
                (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ))
              s : ℝ)

/-- Strictly weaker final-producer socket: the arithmetic tail inequality is
needed only away from cell `-3`, which the lazy-tail centred-carry bridge now
rules out unconditionally. -/
def SeamMiddleProducerTailEscapeExceptNegThree : Prop :=
  ∀ (s : ℕ) (hs : 5 ≤ s), 13 ≤ s →
    ¬ (seamAdjacentCut s hs).successorCarries →
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight →
        4 * ((seamAdjacentCut s hs).remainder : ℤ) -
              ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≠ -3 →
          binaryCoeffTail
              (supportCoeff
                (insert s
                  (↑(seamWordSupport
                    (seamAdjacentCut s hs).below) : Set ℕ)))
              (2 * s + 2) <
            (producerCarry
                (insert s
                  (↑(seamWordSupport
                    (seamAdjacentCut s hs).below) : Set ℕ))
                s : ℝ)

/-- The old three-cell-blind socket is a producer for the reduced socket. -/
theorem SeamMiddleProducerTailEscape.toExceptNegThree
    (hescape : SeamMiddleProducerTailEscape) :
    SeamMiddleProducerTailEscapeExceptNegThree := by
  intro s hs hs13 hncarry hmiddle _hnot
  exact hescape s hs hs13 hncarry hmiddle

/-- A theorem-ready sufficient form of the remaining input, using the
square-root tail majorant already available for `supportCoeff`. -/
def SeamMiddleProducerSqrtEscape : Prop :=
  ∀ (s : ℕ) (hs : 5 ≤ s), 13 ≤ s →
    ¬ (seamAdjacentCut s hs).successorCarries →
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight →
        2 * Real.sqrt ((2 * s + 2 : ℕ) : ℝ) + 4 <
          (producerCarry
              (insert s
                (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ))
              s : ℝ)

/-- The square-root producer socket implies the exact tail-escape socket. -/
theorem SeamMiddleProducerSqrtEscape.toTailEscape
    (hsqrt : SeamMiddleProducerSqrtEscape) :
    SeamMiddleProducerTailEscape := by
  intro s hs hs13 hncarry hmiddle
  let A : Set ℕ :=
    insert s
      (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)
  have htail := binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    A (2 * s + 2)
  exact htail.trans_lt (hsqrt s hs hs13 hncarry hmiddle)

/-! ## Support bookkeeping for a producer prefix -/

theorem one_not_mem_insert_seamWordSupport
    {s : ℕ} (hs : 5 ≤ s) (b : SeamRowWord s) :
    1 ∉ insert s (↑(seamWordSupport b) : Set ℕ) := by
  intro hmem
  rcases hmem with h | h
  · omega
  · have hbounds := seamWordSupport_below (by simpa using h)
    omega

theorem insert_seamWordSupport_subset_Iic
    {s : ℕ} (b : SeamRowWord s) :
    insert s (↑(seamWordSupport b) : Set ℕ) ⊆ Set.Iic s := by
  intro d hd
  rcases hd with h | h
  · simpa [h]
  · exact Set.mem_Iic.mpr
      ((seamWordSupport_below (by simpa using h)).2.le)

private theorem support_rank_bounds
    {s : ℕ} (b : SeamRowWord s) :
    ∀ e ∈ seamWordSupport b, 2 ≤ e ∧ e < s := by
  intro e he
  exact seamWordSupport_below he

private theorem lastProducer_seamWeights_fourteen :
    seamWeights 14 =
      [89478485, 38347922, 17895697, 8659208, 4260880, 2113665,
        1052688, 525314, 262400, 131136, 65552, 32772] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 14),
    seamWeightsFrom_eq_cons (by norm_num : 13 < 14),
    seamWeightsFrom_eq_nil (by norm_num : 14 ≤ 14)]
  norm_num [truncatedMersenneWeight]

private theorem lastProducer_seamSubsetTarget_fourteen :
    seamSubsetTarget 14 = 134201344 := by
  norm_num [seamSubsetTarget]

private theorem lastProducer_integerGreedyBits_fourteen :
    integerGreedyBits (seamWeights 14) (seamSubsetTarget 14) =
      [true, true, false, false, true, true,
        false, false, false, false, false, false] := by
  rw [lastProducer_seamWeights_fourteen,
    lastProducer_seamSubsetTarget_fourteen]
  norm_num [integerGreedyBits]

/-- The exact row-fourteen integer-greedy remainder. -/
theorem seamIntegerGreedyRemainder_fourteen_eq :
    seamIntegerGreedyRemainder 14 = 392 := by
  rw [seamIntegerGreedyRemainder, integerGreedyRemainder,
    lastProducer_integerGreedyBits_fourteen,
    lastProducer_seamWeights_fourteen,
    lastProducer_seamSubsetTarget_fourteen]
  norm_num [weightedBoolSum]

private theorem lastProducer_seamWeights_thirteen :
    seamWeights 13 =
      [22369621, 9586980, 4473924, 2164802, 1065220, 528416,
        263172, 131328, 65600, 32784, 16388] := by
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num : 2 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 3 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 4 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 5 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 6 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 7 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 8 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 9 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 10 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 11 < 13),
    seamWeightsFrom_eq_cons (by norm_num : 12 < 13),
    seamWeightsFrom_eq_nil (by norm_num : 13 ≤ 13)]
  norm_num [truncatedMersenneWeight]

private theorem lastProducer_seamSubsetTarget_thirteen :
    seamSubsetTarget 13 = 33546240 := by
  norm_num [seamSubsetTarget]

private theorem lastProducer_integerGreedyBits_thirteen :
    integerGreedyBits (seamWeights 13) (seamSubsetTarget 13) =
      [true, true, false, false, true, false,
        true, true, true, true, true] := by
  rw [lastProducer_seamWeights_thirteen,
    lastProducer_seamSubsetTarget_thirteen]
  norm_num [integerGreedyBits]

/-- The exact row-thirteen integer-greedy remainder. -/
theorem seamIntegerGreedyRemainder_thirteen_eq :
    seamIntegerGreedyRemainder 13 = 15147 := by
  rw [seamIntegerGreedyRemainder, integerGreedyRemainder,
    lastProducer_integerGreedyBits_thirteen,
    lastProducer_seamWeights_thirteen,
    lastProducer_seamSubsetTarget_thirteen]
  norm_num [weightedBoolSum]

/-- The terminal rank `13` is skipped in the exact row-fourteen seam word. -/
theorem seamGreedy_terminal_false_at_thirteen :
    SeamRowWord.terminal (by omega)
      (seamGreedyWord (13 + 1)) = false := by
  change (seamGreedyWord 14) ⟨11, by omega⟩ = false
  simp [seamGreedyWord, SeamRowWord.ofList,
    lastProducer_integerGreedyBits_fourteen]

/-! ## A named last false terminal -/

/-- Every eventual-right seam has a last false terminal row `D ≥ 13`; all
strictly later terminal bits are true. -/
theorem exists_last_false_terminal_of_eventuallyRight
    (heventual : SeamGreedyEventuallyRight) :
    ∃ (D : ℕ) (hD13 : 13 ≤ D),
      SeamRowWord.terminal (by omega)
          (seamGreedyWord (D + 1)) = false ∧
        ∀ (s : ℕ) (hDs : D < s),
          SeamRowWord.terminal (by omega)
            (seamGreedyWord (s + 1)) = true := by
  classical
  rcases heventual with ⟨S, hS5, hright⟩
  let B : ℕ := max S 14
  let bad : Finset ℕ :=
    (Finset.range B).filter
      (fun d => d ∉ seamWordSupport (seamGreedyWord (d + 1)))
  have h13B : 13 < B := by
    dsimp [B]
    omega
  have h13not : 13 ∉ seamWordSupport (seamGreedyWord (13 + 1)) := by
    apply (not_mem_seamWordSupport_iff_false
      (seamGreedyWord (13 + 1)) (by omega) (by omega)).2
    simpa [SeamRowWord.terminal] using seamGreedy_terminal_false_at_thirteen
  have hbadNonempty : bad.Nonempty := by
    refine ⟨13, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr h13B, h13not⟩
  let D : ℕ := bad.max' hbadNonempty
  have hDmem : D ∈ bad := Finset.max'_mem bad hbadNonempty
  have hDdata := Finset.mem_filter.mp hDmem
  have hD13 : 13 ≤ D := by
    exact Finset.le_max' bad 13
      (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr h13B, h13not⟩)
  have hDfalse : SeamRowWord.terminal (by omega)
      (seamGreedyWord (D + 1)) = false := by
    have hfalse := (not_mem_seamWordSupport_iff_false
      (seamGreedyWord (D + 1)) (by omega) (by omega)).1 hDdata.2
    simpa [SeamRowWord.terminal] using hfalse
  refine ⟨D, hD13, hDfalse, ?_⟩
  intro s hDs
  by_cases hsB : s < B
  · apply Bool.eq_true_of_not_eq_false
    intro hsfalse
    have hsnot : s ∉ seamWordSupport (seamGreedyWord (s + 1)) := by
      apply (not_mem_seamWordSupport_iff_false
        (seamGreedyWord (s + 1)) (by omega) (by omega)).2
      simpa [SeamRowWord.terminal] using hsfalse
    have hsmem : s ∈ bad := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hsB, hsnot⟩
    have hsD : s ≤ D := Finset.le_max' bad s hsmem
    omega
  · have hSs : S ≤ s := by
      dsimp [B] at hsB
      omega
    have hword := hright s hSs
    exact
      (seamGreedyWord_succ_eq_extend_true_iff_terminal_true
        s (hS5.trans hSs)).mp hword

private theorem right_extensions_after_last_false
    {D : ℕ} (hD13 : 13 ≤ D)
    (htrue : ∀ (s : ℕ) (hDs : D < s),
      SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = true) :
    ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true := by
  intro s hDs
  exact
    (seamGreedyWord_succ_eq_extend_true_iff_terminal_true
      s (by omega)).2 (htrue s (by omega))

/-! ## The upper last producer is impossible unconditionally -/

private theorem upperProducer_not_last
    (D : ℕ) (hD13 : 13 ≤ D)
    (hcarry : (seamAdjacentCut D (by omega)).successorCarries)
    (htrue : ∀ (s : ℕ) (hDs : D < s),
      SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = true) : False := by
  classical
  let hs5 : 5 ≤ D := by omega
  let K := seamAdjacentCut D hs5
  let u : Finset ℕ := seamWordSupport K.above
  let A : Set ℕ := insert D (↑u : Set ℕ)
  have hword : seamGreedyWord (D + 1) = K.above.extend false := by
    exact seamGreedyWord_succ_eq_upperBranch D hs5 hcarry
  have hright := right_extensions_after_last_false hD13 htrue
  have hu : ∀ e ∈ u, 2 ≤ e ∧ e < D := support_rank_bounds K.above
  have hbase : seamWordSupport (seamGreedyWord (D + 1)) =
      u ∪ Finset.Ico (D + 1) (D + 1) := by
    rw [hword, seamWordSupport_extend_false (by omega)]
    simp [u]
  have hlower := prefix_add_mersenneTail_lt_half_of_eventually_right
    (S := D + 1) (D := D) (u := u)
    (by omega) (by omega) hu hright hbase
  have hone : 1 ∉ A := by
    exact one_not_mem_insert_seamWordSupport hs5 K.above
  have hA : A ⊆ Set.Iic D := by
    exact insert_seamWordSupport_subset_Iic K.above
  have hDnotu : D ∉ u := by
    intro hDu
    exact (Nat.lt_irrefl D) (hu D hDu).2
  have hcarryEq :
      producerCarry
          (insert D (↑(seamWordSupport K.above) : Set ℕ)) D =
        -((4 * K.overshoot + K.abovePulse + 4 : ℕ) : ℤ) := by
    simpa [K] using
      (producerCarry_insert_seamAboveSupport_eq_neg_upperCoordinate D hs5)
  have hover : 1 ≤ K.overshoot := by
    unfold PerturbedFamily.AdjacentCut.overshoot
    have habove := K.above_strict
    omega
  have hcarryLe : producerCarry A D ≤ -8 := by
    change producerCarry
      (insert D (↑(seamWordSupport K.above) : Set ℕ)) D ≤ -8
    rw [hcarryEq]
    have hq : 8 ≤
        4 * K.overshoot + K.abovePulse + 4 := by omega
    have hqZ : (8 : ℤ) ≤
        ((4 * K.overshoot + K.abovePulse + 4 : ℕ) : ℤ) := by
      exact_mod_cast hq
    omega
  have hdecomp : erdosSupportSeries 2 A =
      positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight D := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    simpa [A, add_comm] using
      (positiveMersenneSupportValue_insert hDnotu)
  have hforced := producerCarry_le_neg_eight_forces_belowTail_gt_half
    A D (positiveMersenneSupportValue (↑u : Set ℕ))
    hone hA (by omega) hcarryLe hdecomp
  linarith

/-! ## The middle last producer is exactly the remaining socket -/

/-- The new lazy-tail carry bridge removes the first exceptional middle
cell directly in the last-false-terminal coordinates used by this module.
Keeping this adapter beside the global fan-in makes the downstream route
discoverable without asking a later proof to reconstruct `hright`. -/
theorem middleProducer_neg_three_not_last
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (htrue : ∀ (s : ℕ) (hDs : D < s),
      SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -3) :
    False := by
  exact finalMiddleCell_neg_three_not_last D hD13 hncarry hmiddle
    (right_extensions_after_last_false hD13 htrue) hcell

private theorem middleProducer_not_last_except_neg_three
    (hmiddleEscape : SeamMiddleProducerTailEscapeExceptNegThree)
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (htrue : ∀ (s : ℕ) (hDs : D < s),
      SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = true) : False := by
  by_cases hcell :
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -3
  · exact middleProducer_neg_three_not_last D hD13 hncarry hmiddle
      htrue hcell
  classical
  let hs5 : 5 ≤ D := by omega
  let K := seamAdjacentCut D hs5
  let u : Finset ℕ := seamWordSupport K.below
  let A : Set ℕ := insert D (↑u : Set ℕ)
  have hword : seamGreedyWord (D + 1) = K.below.extend false := by
    exact seamGreedyWord_succ_eq_middleBranch D hs5 hncarry hmiddle
  have hright := right_extensions_after_last_false hD13 htrue
  have hu : ∀ e ∈ u, 2 ≤ e ∧ e < D := support_rank_bounds K.below
  have hbase : seamWordSupport (seamGreedyWord (D + 1)) =
      u ∪ Finset.Ico (D + 1) (D + 1) := by
    rw [hword, seamWordSupport_extend_false (by omega)]
    simp [u]
  have hupper := half_lt_upper_competitor_of_eventually_right
    (S := D + 1) (D := D) (u := u)
    (by omega) (by omega) (by omega) hu hright hbase
  have hone : 1 ∉ A := by
    exact one_not_mem_insert_seamWordSupport hs5 K.below
  have hA : A ⊆ Set.Iic D := by
    exact insert_seamWordSupport_subset_Iic K.below
  have htail := hmiddleEscape D hs5 hD13 hncarry hmiddle (by
    simpa [hs5] using hcell)
  have hbelow : erdosSupportSeries 2 A < (1 : ℝ) / 2 := by
    exact (producerCarry_gt_tail_iff_supportSeries_lt_half
      A D hone hA).1 htail
  have hDnotu : D ∉ u := by
    intro hDu
    exact (Nat.lt_irrefl D) (hu D hDu).2
  have hupperSeries : (1 : ℝ) / 2 < erdosSupportSeries 2 A := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    simpa [A] using hupper
  linarith

/-! ## Global fan-in -/

/-- The reduced middle socket, with cell `-3` discharged locally, rules out
an eventual right seam tail and proves the Erdős #257 endpoint. -/
theorem half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree
    (hmiddleEscape : SeamMiddleProducerTailEscapeExceptNegThree) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  apply half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight.2
  intro heventual
  obtain ⟨D, hD13, hfalse, htrue⟩ :=
    exists_last_false_terminal_of_eventuallyRight heventual
  have hUM :=
    (seamGreedy_terminal_false_iff_upperOrMiddle D (by omega)).1 hfalse
  rcases hUM with hcarry | ⟨hncarry, hmiddle⟩
  · exact upperProducer_not_last D hD13 hcarry htrue
  · exact middleProducer_not_last_except_neg_three hmiddleEscape D hD13
      hncarry hmiddle htrue

/-- Backwards-compatible fan-in from the original stronger socket. -/
theorem half_mem_mersenneAchievementSet_of_middleProducerTailEscape
    (hmiddleEscape : SeamMiddleProducerTailEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree
    hmiddleEscape.toExceptNegThree

/-- It is enough to prove the square-root middle-producer lower bound. -/
theorem half_mem_mersenneAchievementSet_of_middleProducerSqrtEscape
    (hsqrt : SeamMiddleProducerSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_middleProducerTailEscape
    hsqrt.toTailEscape

#print axioms SeamMiddleProducerSqrtEscape.toTailEscape
#print axioms seamIntegerGreedyRemainder_fourteen_eq
#print axioms seamIntegerGreedyRemainder_thirteen_eq
#print axioms seamGreedy_terminal_false_at_thirteen
#print axioms one_not_mem_insert_seamWordSupport
#print axioms insert_seamWordSupport_subset_Iic
#print axioms exists_last_false_terminal_of_eventuallyRight
#print axioms middleProducer_neg_three_not_last
#print axioms half_mem_mersenneAchievementSet_of_middleProducerTailEscapeExceptNegThree
#print axioms half_mem_mersenneAchievementSet_of_middleProducerTailEscape
#print axioms half_mem_mersenneAchievementSet_of_middleProducerSqrtEscape

end

end Erdos249257
