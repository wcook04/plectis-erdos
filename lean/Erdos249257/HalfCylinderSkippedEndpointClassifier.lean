import Erdos249257.HalfCylinderFullShellSeamBridge

/-!
# Skipped-endpoint classifier for the half-cylinder seam

This module records the word-coordinate structure available before the
remaining arithmetic implication for Erdős #257.  In particular, a skipped
row has three possible signed endpoint cells; the zero cell is retained.
-/

namespace Erdos249257

open Set
open HalfCarryReachability
open HalfCylinderFiniteShadow
open HalfCylinderIntegerGreedy
open scoped BigOperators

/-! ## The actual finite word and its row update -/

theorem stemBitsFrom_eq_ofFn
    {s d : ℕ} (P : Finset ℕ) (hds : d ≤ s) :
    stemBitsFrom s P d =
      List.ofFn (fun i : Fin (s - d) => decide (d + i ∈ P)) := by
  by_cases hlt : d < s
  · have hsub : s - d = (s - (d + 1)) + 1 := by omega
    rw [stemBitsFrom_eq_cons hlt,
      stemBitsFrom_eq_ofFn P (by omega), hsub, List.ofFn_succ]
    congr 1
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_succ]
    apply congrArg (fun e : ℕ => decide (e ∈ P))
    omega
  · have hsd : s = d := by omega
    subst d
    simp [stemBitsFrom_eq_nil]
termination_by s - d
decreasing_by omega

theorem stemBits_eq_ofFn
    {s : ℕ} (P : Finset ℕ) (hs : 2 ≤ s) :
    stemBits s P =
      List.ofFn (fun i : Fin (s - 2) => decide ((i : ℕ) + 2 ∈ P)) := by
  unfold stemBits
  simpa [Nat.add_comm] using stemBitsFrom_eq_ofFn P hs

/-- The actual Boolean row word supplied by the rational greedy prefix. -/
def halfActualSeamWord (s : ℕ) : SeamRowWord s :=
  fun i => decide ((i : ℕ) + 2 ∈ halfGreedyPrefixSupport (s - 1))

@[simp] theorem halfActualSeamWord_toList
    (s : ℕ) (hs : 2 ≤ s) :
    (halfActualSeamWord s).toList =
      stemBits s (halfGreedyPrefixSupport (s - 1)) := by
  unfold SeamRowWord.toList halfActualSeamWord
  rw [stemBits_eq_ofFn _ hs]

theorem mem_halfGreedyPrefixSupport_succ_iff_of_lt
    {s d : ℕ} (hd : 0 < d) (hds : d < s) :
    d ∈ halfGreedyPrefixSupport s ↔
      d ∈ halfGreedyPrefixSupport (s - 1) := by
  rw [mem_halfGreedyPrefixSupport_iff hd (by omega),
    mem_halfGreedyPrefixSupport_iff hd (by omega)]

theorem self_mem_halfGreedyPrefixSupport_iff_take
    (s : ℕ) (hs : 1 ≤ s) :
    s ∈ halfGreedyPrefixSupport s ↔
      mersenneWeight s ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (s - 1) := by
  rw [mem_halfGreedyPrefixSupport_iff (by omega) le_rfl,
    halfGreedyPrefixSupport,
    ← greedyMersenneRemainderRat_eq_sub_finiteErdosSum]
  have htake := rational_greedy_take_iff_real (1 / 2 : ℚ) (s - 1)
  simpa [Nat.sub_add_cancel hs] using htake

/-- The actual word evolves by appending precisely the real greedy decision
at the terminal coordinate. -/
theorem halfActualSeamWord_succ
    (s : ℕ) (hs : 3 ≤ s) :
    halfActualSeamWord (s + 1) =
      (halfActualSeamWord s).extend
        (decide (mersenneWeight s ≤
          greedyMersenneRemainder (1 / 2 : ℝ) (s - 1))) := by
  funext i
  by_cases hi : (i : ℕ) < s - 2
  · have hdpos : 0 < (i : ℕ) + 2 := by omega
    have hdlt : (i : ℕ) + 2 < s := by omega
    have hmem := mem_halfGreedyPrefixSupport_succ_iff_of_lt hdpos hdlt
    simp only [halfActualSeamWord, SeamRowWord.extend, dif_pos hi]
    rw [show s + 1 - 1 = s by omega]
    exact Bool.decide_congr hmem
  · have hilast : (i : ℕ) = s - 2 := by omega
    have hself := self_mem_halfGreedyPrefixSupport_iff_take s (by omega)
    have hindex : (i : ℕ) + 2 = s := by omega
    simp only [halfActualSeamWord, SeamRowWord.extend, dif_neg hi]
    rw [hindex, show s + 1 - 1 = s by omega]
    exact Bool.decide_congr hself

/-! ## Full-shell margin in actual-word coordinates -/

theorem seamPerturbedFamily_oldSum_halfActualSeamWord
    (s : ℕ) (hs : 3 ≤ s) :
    (seamPerturbedFamily s hs).oldSum (halfActualSeamWord s) =
      stemTruncatedSum s (halfGreedyPrefixSupport (s - 1)) := by
  change wordWeightSum s (halfActualSeamWord s).toNatWord = _
  rw [← weightedBoolSum_toList_eq_wordWeightSum (by omega),
    halfActualSeamWord_toList s (by omega), weightedBoolSum_stemBits]

theorem greedyHalfFrozenMargin_fullShell_eq_actualOldSum_sub_target
    (s : ℕ) (hs : 3 ≤ s) :
    greedyHalfFrozenMargin (s - 1) s =
      ((seamPerturbedFamily s hs).oldSum
          (halfActualSeamWord s) : ℤ) -
        (seamSubsetTarget s : ℤ) := by
  rw [greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target s (by omega),
    seamPerturbedFamily_oldSum_halfActualSeamWord s hs]

/-- The full-shell margin is always below one adjacent-word separation gap. -/
theorem greedyHalfFrozenMargin_fullShell_lt_gap
    (s : ℕ) (hs : 1 ≤ s) :
    greedyHalfFrozenMargin (s - 1) s <
      ((2 ^ (s + 1) : ℕ) : ℤ) := by
  let r : ℝ := greedyMersenneRemainder (1 / 2 : ℝ) (s - 1)
  let T : ℝ := binaryCoeffTail
    (supportCoeff
      (↑(halfGreedyPrefixSupport (s - 1)) : Set ℕ)) (2 * s)
  have hid := greedyHalfFrozenMargin_fullShell_cast_eq_slack_sub_tail (s - 1)
  have hid' :
      (greedyHalfFrozenMargin (s - 1) s : ℝ) =
        (2 : ℝ) ^ s * (1 - (2 : ℝ) ^ s * r) - T := by
    simpa [r, T, Nat.sub_add_cancel hs, two_mul] using hid
  have hr : 0 ≤ r := by
    exact greedyMersenneRemainder_nonneg (by norm_num) (s - 1)
  have hT : 0 ≤ T := binaryCoeffTail_nonneg _ _
  have hle :
      (greedyHalfFrozenMargin (s - 1) s : ℝ) ≤ (2 : ℝ) ^ s := by
    rw [hid']
    have hsquareRem : 0 ≤ ((2 : ℝ) ^ s) ^ 2 * r :=
      mul_nonneg (sq_nonneg _) hr
    nlinarith
  have hlt : (2 : ℝ) ^ s < (2 : ℝ) ^ (s + 1) := by
    rw [pow_succ]
    nlinarith [show 0 < (2 : ℝ) ^ s by positivity]
  have hreal := hle.trans_lt hlt
  exact_mod_cast hreal

/-! ## Exact three-cell endpoint reconstruction -/

theorem halfActualSeamWord_eq_greedy_of_margin_eq_zero
    (s : ℕ) (hs : 5 ≤ s)
    (hzero : greedyHalfFrozenMargin (s - 1) s = 0) :
    halfActualSeamWord s = seamGreedyWord s ∧
      seamIntegerGreedyRemainder s = 0 := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hshadow :=
    greedyHalfFrozenMargin_fullShell_eq_actualOldSum_sub_target s (by omega)
  have hsumZ : (F.oldSum (halfActualSeamWord s) : ℤ) =
      (seamSubsetTarget s : ℤ) := by
    change greedyHalfFrozenMargin (s - 1) s =
      (F.oldSum (halfActualSeamWord s) : ℤ) -
        (seamSubsetTarget s : ℤ) at hshadow
    omega
  have hsum : F.oldSum (halfActualSeamWord s) = seamSubsetTarget s := by
    exact_mod_cast hsumZ
  have hmax : F.oldSum (halfActualSeamWord s) ≤ F.oldSum K.below := by
    simpa [F, K] using
      K.below_maximal (halfActualSeamWord s) hsum.le
  have heq : F.oldSum (halfActualSeamWord s) = F.oldSum K.below := by
    have hadm : F.oldSum K.below ≤ seamSubsetTarget s := by
      simpa [F, K] using K.below_admissible
    omega
  have hword : halfActualSeamWord s = K.below := F.oldSum_injective heq
  have hrem : K.remainder = 0 := by
    have hbelow : F.oldSum K.below = seamSubsetTarget s :=
      heq.symm.trans hsum
    simp [K, F, PerturbedFamily.AdjacentCut.remainder, hbelow]
  constructor
  · simpa [K, seamAdjacentCut] using hword
  · rw [← seamAdjacentCut_remainder hs]
    simpa [K] using hrem

theorem halfActualSeamWord_eq_above_of_margin_pos
    (s : ℕ) (hs : 5 ≤ s)
    (hpos : 0 < greedyHalfFrozenMargin (s - 1) s) :
    halfActualSeamWord s = seamAboveWord s hs ∧
      greedyHalfFrozenMargin (s - 1) s =
        ((seamAdjacentCut s hs).overshoot : ℤ) := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hshadow :=
    greedyHalfFrozenMargin_fullShell_eq_actualOldSum_sub_target s (by omega)
  have hCz : (seamSubsetTarget s : ℤ) <
      (F.oldSum (halfActualSeamWord s) : ℤ) := by
    change greedyHalfFrozenMargin (s - 1) s =
      (F.oldSum (halfActualSeamWord s) : ℤ) -
        (seamSubsetTarget s : ℤ) at hshadow
    omega
  have hC : seamSubsetTarget s < F.oldSum (halfActualSeamWord s) := by
    exact_mod_cast hCz
  have hmin := K.above_minimal (halfActualSeamWord s) hC
  have heq : F.oldSum (halfActualSeamWord s) = F.oldSum K.above := by
    by_contra hne
    have hlt : F.oldSum K.above < F.oldSum (halfActualSeamWord s) :=
      lt_of_le_of_ne hmin (Ne.symm hne)
    have hsep := F.separated hlt
    have habove : seamSubsetTarget s < F.oldSum K.above := by
      simpa [F, K] using K.above_strict
    have hgapZ : (F.gap : ℤ) <
        (F.oldSum (halfActualSeamWord s) : ℤ) -
          (seamSubsetTarget s : ℤ) := by
      have hsepZ :
          (F.oldSum K.above : ℤ) + (F.gap : ℤ) ≤
            (F.oldSum (halfActualSeamWord s) : ℤ) := by
        exact_mod_cast hsep
      have haboveZ : (seamSubsetTarget s : ℤ) <
          (F.oldSum K.above : ℤ) := by
        exact_mod_cast habove
      omega
    have hupper := greedyHalfFrozenMargin_fullShell_lt_gap s (by omega)
    have hupperF : greedyHalfFrozenMargin (s - 1) s < (F.gap : ℤ) := by
      simpa [F, seamPerturbedFamily] using hupper
    change greedyHalfFrozenMargin (s - 1) s =
      (F.oldSum (halfActualSeamWord s) : ℤ) -
        (seamSubsetTarget s : ℤ) at hshadow
    omega
  have hword : halfActualSeamWord s = K.above := F.oldSum_injective heq
  have hover := K.capacity_add_overshoot
  have hoverZ : (seamSubsetTarget s : ℤ) + (K.overshoot : ℤ) =
      (F.oldSum K.above : ℤ) := by
    exact_mod_cast hover
  have hmargin : greedyHalfFrozenMargin (s - 1) s = (K.overshoot : ℤ) := by
    change greedyHalfFrozenMargin (s - 1) s =
      (F.oldSum (halfActualSeamWord s) : ℤ) -
        (seamSubsetTarget s : ℤ) at hshadow
    have heqZ : (F.oldSum (halfActualSeamWord s) : ℤ) =
        (F.oldSum K.above : ℤ) := by exact_mod_cast heq
    omega
  constructor
  · simpa [K, seamAdjacentCut] using hword
  · simpa [K] using hmargin

/-- A skipped endpoint has exactly three signed cells.  The zero seam hit is
an allowed cell; only the negative-below cell remains to be excluded. -/
theorem halfGreedy_skipped_endpoint_trichotomy
    (s : ℕ) (hs : 5 ≤ s)
    (hskip : ¬ mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1)) :
    (greedyHalfFrozenMargin (s - 1) s < 0 ∧
        halfActualSeamWord s = seamGreedyWord s ∧
        1 ≤ seamIntegerGreedyRemainder s ∧
        greedyHalfFrozenMargin (s - 1) s =
          -(seamIntegerGreedyRemainder s : ℤ)) ∨
      (greedyHalfFrozenMargin (s - 1) s = 0 ∧
        halfActualSeamWord s = seamGreedyWord s ∧
        seamIntegerGreedyRemainder s = 0) ∨
      (0 < greedyHalfFrozenMargin (s - 1) s ∧
        halfActualSeamWord s = seamAboveWord s hs ∧
        greedyHalfFrozenMargin (s - 1) s =
          ((seamAdjacentCut s hs).overshoot : ℤ)) := by
  rcases lt_trichotomy (greedyHalfFrozenMargin (s - 1) s) 0 with
      hneg | hzero | hpos
  · left
    have halignList := stemBits_eq_integerGreedyBits_of_skipped_fullShell_neg
      s (by omega) hskip hneg
    have halign : halfActualSeamWord s = seamGreedyWord s := by
      apply SeamRowWord.toList_injective
      rw [halfActualSeamWord_toList s (by omega), seamGreedyWord_toList]
      exact halignList
    have hrem :=
      neg_greedyHalfFrozenMargin_fullShell_implies_seamRemainder_small
        s (by omega) hskip hneg
    have hmargin :=
      greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment
        s (by omega) halignList
    exact ⟨hneg, halign, hrem.1, hmargin⟩
  · right
    left
    have hz := halfActualSeamWord_eq_greedy_of_margin_eq_zero s hs hzero
    exact ⟨hzero, hz.1, hz.2⟩
  · right
    right
    have hp := halfActualSeamWord_eq_above_of_margin_pos s hs hpos
    exact ⟨hpos, hp.1, hp.2⟩

/-! ## Exact three-branch next-word rewrites -/

theorem seamGreedyWord_succ_eq_upperBranch
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    seamGreedyWord (s + 1) =
      (seamAdjacentCut s hs).above.extend false := by
  classical
  let K := seamAdjacentCut s hs
  change K.successorCarries at hcarry
  have hlt := K.carry_prefix_lt_terminal hcarry
  rw [← seamCutNextWord_eq_greedyWord_succ hs]
  change K.prefixChoice.extend
      (decide (K.terminalWeight ≤ K.prefixRemainder)) =
    K.above.extend false
  have hdec : decide (K.terminalWeight ≤ K.prefixRemainder) = false := by
    simp [Nat.not_le_of_lt hlt]
  rw [PerturbedFamily.AdjacentCut.prefixChoice, if_pos hcarry, hdec]

theorem seamGreedyWord_succ_eq_middleBranch
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
          (seamPerturbedFamily s (by omega)).gap -
          (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight) :
    seamGreedyWord (s + 1) =
      (seamAdjacentCut s hs).below.extend false := by
  classical
  let K := seamAdjacentCut s hs
  change ¬ K.successorCarries at hcarry
  change 4 * K.remainder +
      (seamPerturbedFamily s (by omega)).gap - K.belowPulse <
    K.terminalWeight at hmiddle
  rw [← seamCutNextWord_eq_greedyWord_succ hs]
  change K.prefixChoice.extend
      (decide (K.terminalWeight ≤ K.prefixRemainder)) =
    K.below.extend false
  have hpref : K.prefixRemainder =
      4 * K.remainder + (seamPerturbedFamily s (by omega)).gap -
        K.belowPulse := by
    simp [PerturbedFamily.AdjacentCut.prefixRemainder, hcarry]
  have hnle : ¬ K.terminalWeight ≤
      4 * K.remainder + (seamPerturbedFamily s (by omega)).gap -
        K.belowPulse := Nat.not_le_of_lt hmiddle
  have hdec : decide (K.terminalWeight ≤ K.prefixRemainder) = false := by
    rw [hpref]
    simp [hnle]
  rw [PerturbedFamily.AdjacentCut.prefixChoice, if_neg hcarry, hdec]

theorem seamGreedyWord_succ_eq_rightBranch
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hright : (seamAdjacentCut s hs).terminalWeight ≤
      4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse) :
    seamGreedyWord (s + 1) =
      (seamAdjacentCut s hs).below.extend true := by
  classical
  let K := seamAdjacentCut s hs
  change ¬ K.successorCarries at hcarry
  change K.terminalWeight ≤
    4 * K.remainder + (seamPerturbedFamily s (by omega)).gap -
      K.belowPulse at hright
  rw [← seamCutNextWord_eq_greedyWord_succ hs]
  change K.prefixChoice.extend
      (decide (K.terminalWeight ≤ K.prefixRemainder)) =
    K.below.extend true
  have hpref : K.prefixRemainder =
      4 * K.remainder + (seamPerturbedFamily s (by omega)).gap -
        K.belowPulse := by
    simp [PerturbedFamily.AdjacentCut.prefixRemainder, hcarry]
  have hdec : decide (K.terminalWeight ≤ K.prefixRemainder) = true := by
    rw [hpref]
    simp [hright]
  rw [PerturbedFamily.AdjacentCut.prefixChoice, if_neg hcarry, hdec]

/-- An aligned skip remains aligned at the next row exactly in the middle
seam branch. -/
theorem alignedSkip_next_alignment_iff_middle
    (s : ℕ) (hs : 5 ≤ s)
    (hskip : ¬ mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1))
    (halign : halfActualSeamWord s = seamGreedyWord s) :
    halfActualSeamWord (s + 1) = seamGreedyWord (s + 1) ↔
      ¬ (seamAdjacentCut s hs).successorCarries ∧
        4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight := by
  classical
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  change halfActualSeamWord s = K.below at halign
  have hdec : decide (mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1)) = false := by
    simp only [decide_eq_false_iff_not]
    exact hskip
  have hactual : halfActualSeamWord (s + 1) = K.below.extend false := by
    rw [halfActualSeamWord_succ s (by omega), halign, hdec]
  constructor
  · intro hnext
    by_cases hcarry : K.successorCarries
    · have hgreedy := seamGreedyWord_succ_eq_upperBranch s hs hcarry
      change seamGreedyWord (s + 1) = K.above.extend false at hgreedy
      have hext : K.below.extend false = K.above.extend false := by
        rw [← hactual, hnext, hgreedy]
      have hword := congrArg (SeamRowWord.dropTerminal (by omega)) hext
      simp only [SeamRowWord.dropTerminal_extend] at hword
      have hbelow := K.below_admissible
      have habove := K.above_strict
      rw [hword] at hbelow
      omega
    · refine ⟨hcarry, ?_⟩
      by_contra hnot
      have hright : K.terminalWeight ≤
          4 * K.remainder + F.gap - K.belowPulse :=
        Nat.le_of_not_gt hnot
      have hgreedy := seamGreedyWord_succ_eq_rightBranch s hs hcarry hright
      change seamGreedyWord (s + 1) = K.below.extend true at hgreedy
      have hext : K.below.extend false = K.below.extend true := by
        rw [← hactual, hnext, hgreedy]
      have hbit := congrArg (SeamRowWord.terminal (by omega)) hext
      simp only [SeamRowWord.terminal_extend] at hbit
      cases hbit
  · rintro ⟨hcarry, hmiddle⟩
    have hgreedy := seamGreedyWord_succ_eq_middleBranch s hs hcarry hmiddle
    change seamGreedyWord (s + 1) = K.below.extend false at hgreedy
    rw [hactual, hgreedy]

/-- The next signed full-shell margin of any aligned skip is the negative
middle-branch quantity, independently of which seam branch the greedy word
chooses. -/
theorem alignedSkip_nextMargin_eq_neg_middleQuantity
    (s : ℕ) (hs : 5 ≤ s)
    (hskip : ¬ mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1))
    (halign : halfActualSeamWord s = seamGreedyWord s) :
    greedyHalfFrozenMargin s (s + 1) =
      -((4 * (seamAdjacentCut s hs).remainder +
          (seamPerturbedFamily s (by omega)).gap -
          (seamAdjacentCut s hs).belowPulse : ℕ) : ℤ) := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  change halfActualSeamWord s = K.below at halign
  have hdec : decide (mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1)) = false := by
    simp only [decide_eq_false_iff_not]
    exact hskip
  have hactual : halfActualSeamWord (s + 1) = K.below.extend false := by
    rw [halfActualSeamWord_succ s (by omega), halign, hdec]
  have hshadow :=
    greedyHalfFrozenMargin_fullShell_eq_actualOldSum_sub_target
      (s + 1) (by omega)
  have hshadow' :
      greedyHalfFrozenMargin s (s + 1) =
        ((seamPerturbedFamily (s + 1) (by omega)).oldSum
            (halfActualSeamWord (s + 1)) : ℤ) -
          (seamSubsetTarget (s + 1) : ℤ) := by
    simpa using hshadow
  have hold :
      (seamPerturbedFamily (s + 1) (by omega)).oldSum
          (halfActualSeamWord (s + 1)) = F.newSum K.below := by
    change wordWeightSum (s + 1)
        (halfActualSeamWord (s + 1)).toNatWord = F.newSum K.below
    rw [hactual]
    simpa [F] using wordWeightSum_rowWord_extend
      (s := s) (by omega) K.below false
  have hcap : K.newCapacity = seamSubsetTarget (s + 1) :=
    seamAdjacentCut_newCapacity hs
  have hle : F.newSum K.below ≤ K.newCapacity :=
    K.below_newSum_le_capacity (seamPulseCap_lt_gap (by omega))
  have hres := K.below_residual_eq
  calc
    greedyHalfFrozenMargin s (s + 1) =
        (F.newSum K.below : ℤ) - (K.newCapacity : ℤ) := by
      rw [hshadow', hold, ← hcap]
    _ = -((K.newCapacity - F.newSum K.below : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle]
      ring
    _ = -((4 * K.remainder + F.gap - K.belowPulse : ℕ) : ℤ) := by
      rw [hres]

theorem alignedSkip_nextMargin_neg
    (s : ℕ) (hs : 5 ≤ s)
    (hskip : ¬ mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1))
    (halign : halfActualSeamWord s = seamGreedyWord s) :
    greedyHalfFrozenMargin s (s + 1) < 0 := by
  let F := seamPerturbedFamily s (by omega)
  let K := seamAdjacentCut s hs
  have hpulse : K.belowPulse ≤ F.pulseCap := by
    simpa [PerturbedFamily.AdjacentCut.belowPulse] using F.pulse_le K.below
  have hcap : F.pulseCap < F.gap := seamPulseCap_lt_gap (by omega)
  have hq : 0 < 4 * K.remainder + F.gap - K.belowPulse := by omega
  have heq := alignedSkip_nextMargin_eq_neg_middleQuantity s hs hskip halign
  change greedyHalfFrozenMargin s (s + 1) =
      -((4 * K.remainder + F.gap - K.belowPulse : ℕ) : ℤ) at heq
  have hqZ : (0 : ℤ) <
      (4 * K.remainder + F.gap - K.belowPulse : ℕ) := by
    exact_mod_cast hq
  omega

#print axioms halfActualSeamWord_succ
#print axioms greedyHalfFrozenMargin_fullShell_lt_gap
#print axioms halfGreedy_skipped_endpoint_trichotomy
#print axioms seamGreedyWord_succ_eq_upperBranch
#print axioms seamGreedyWord_succ_eq_middleBranch
#print axioms seamGreedyWord_succ_eq_rightBranch
#print axioms alignedSkip_next_alignment_iff_middle
#print axioms alignedSkip_nextMargin_eq_neg_middleQuantity
#print axioms alignedSkip_nextMargin_neg

end Erdos249257
