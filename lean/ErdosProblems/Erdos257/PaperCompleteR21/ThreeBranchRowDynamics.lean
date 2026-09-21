import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.BooleanMobiusLocalRepair

/-!
Paper-form restatement of the asserted environment `thm:dynamics`
("Exact recurrences for the three branches",
`paper/reasoning-parts/erdos257/a257_front.tex:2293`) of the long Erdős #257
manuscript.

Notation of the paper (§`ssec:seam-model`), with its Lean counterparts:

* `q(M,d) = ⌊2^M/(2^d-1)⌋` is `localMersenneQuotient M d` and
  `w(n,d) = q(2n,d) = ⌊4^n/(2^d-1)⌋` is `truncatedMersenneWeight n d`;
* `Q(S,2n) = ∑_{d ∈ S} w(n,d)` is `localPrefixQuotient S (2*n)`;
* `T_n = 2^(2n-1) - 2^n` is `seamSubsetTarget n`;
* the index set `{2,…,n-1}` is `Finset.Ico 2 n`;
* `D_n` is the unique `D` with `IsRowLower n D` (largest quotient sum at most
  `T_n`) and `B_n` the unique `B` with `IsRowUpper n B` (smallest quotient sum
  strictly above `T_n`);
* `rem(n) = T_n - Q(D_n,2n)` and `o = Q(B_n,2n) - T_n`;
* `p^- = ∑_{d ∈ D_n} (2·1_{d|2n+1} + 1_{d|2n+2})` is `∑ d ∈ D_n, rowPulse n d`,
  and `p^+` the same sum over `B_n`.

The endpoint `paper_dynamics` states every clause of the environment: the
identification of `D_n` with the greedy support, the range `[0,2(n-2)]` of the
two correction terms, the three-branch formula for `rem(n+1)`, and the
normalised display (III) for `λ_{n+1}`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfCylinderIntegerGreedy
open scoped BigOperators

attribute [local instance]
  Erdos249257.HalfCylinderIntegerGreedy.adjacentCutSuccessorCarriesDecidable

/-! ### The paper's row data -/

/-- `w(n,d) = ⌊4^n/(2^d-1)⌋`. -/
theorem paper_rowWeight_eq_floor (n d : ℕ) :
    truncatedMersenneWeight n d = 4 ^ n / (2 ^ d - 1) := rfl

/-- `T_n = 2^{2n-1} - 2^n`. -/
theorem paper_rowTarget_eq (n : ℕ) :
    seamSubsetTarget n = 2 ^ (2 * n - 1) - 2 ^ n := rfl

/-- The summand of the paper's correction terms:
`2·1_{d | 2n+1} + 1_{d | 2n+2}`. -/
theorem paper_rowPulse_eq_indicators (n d : ℕ) :
    rowPulse n d =
      2 * (if d ∣ 2 * n + 1 then 1 else 0) +
        (if d ∣ 2 * n + 2 then 1 else 0) := by
  unfold rowPulse
  ring

/-- `Q(S,2n)` is the sum of the integer quotient weights of the row. -/
theorem paper_rowQuotient_eq_weightSum (n : ℕ) (S : Finset ℕ) :
    localPrefixQuotient S (2 * n) = ∑ d ∈ S, truncatedMersenneWeight n d := by
  unfold localPrefixQuotient
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold localMersenneQuotient truncatedMersenneWeight
  congr 1
  rw [pow_mul]
  norm_num

/-- The reason the environment gives for `p^-, p^+ ≤ 2(n-2)`: a rank `d ≥ 2`
cannot divide two consecutive integers. -/
theorem paper_consecutive_not_both_divisible {d m : ℕ} (hd : 2 ≤ d) :
    ¬ (d ∣ m + 1 ∧ d ∣ m + 2) := by
  rintro ⟨h1, h2⟩
  have hsub : d ∣ (m + 2) - (m + 1) := Nat.dvd_sub h2 h1
  have hone : (m + 2) - (m + 1) = 1 := by omega
  rw [hone] at hsub
  have := Nat.le_of_dvd (by omega) hsub
  omega

/-! ### Subsets of `{2,…,n-1}` and Boolean row words -/

/-- The Boolean row word of a subset of `{2,…,n-1}`. -/
def rowWord (n : ℕ) (S : Finset ℕ) : SeamRowWord n :=
  fun i => decide ((i : ℕ) + 2 ∈ S)

/-- The subset of `{2,…,n-1}` selected by a Boolean row word. -/
def rowSupport (n : ℕ) (b : SeamRowWord n) : Finset ℕ :=
  (Finset.Ico 2 n).filter (fun d => b.toNatWord d = true)

private lemma sum_shift_eq_filter (n : ℕ) (b : ℕ → Bool) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range (n - 2), if b (i + 2) then f (i + 2) else 0) =
      ∑ d ∈ (Finset.Ico 2 n).filter (fun d => b d = true), f d := by
  classical
  rw [Finset.sum_filter, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : 2 + i = i + 2 := Nat.add_comm 2 i
  rw [h]

private lemma wordWeightSum_eq_filter (n : ℕ) (b : ℕ → Bool) :
    wordWeightSum n b =
      ∑ d ∈ (Finset.Ico 2 n).filter (fun d => b d = true),
        truncatedMersenneWeight n d :=
  sum_shift_eq_filter n b _

private lemma wordPulse_eq_filter (n : ℕ) (b : ℕ → Bool) :
    wordPulse n b =
      ∑ d ∈ (Finset.Ico 2 n).filter (fun d => b d = true), rowPulse n d :=
  sum_shift_eq_filter n b _

private lemma rowWord_apply {n d : ℕ} {S : Finset ℕ} (h2 : 2 ≤ d) (hn : d < n) :
    (rowWord n S).toNatWord d = decide (d ∈ S) := by
  unfold SeamRowWord.toNatWord
  rw [dif_pos (⟨h2, hn⟩ : 2 ≤ d ∧ d < n)]
  show decide (d - 2 + 2 ∈ S) = decide (d ∈ S)
  rw [Nat.sub_add_cancel h2]

private lemma rowWord_filter {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Ico 2 n) :
    (Finset.Ico 2 n).filter (fun d => (rowWord n S).toNatWord d = true) = S := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h2, hn⟩, hb⟩
    rw [rowWord_apply h2 hn] at hb
    simpa using hb
  · intro hd
    have hmem := Finset.mem_Ico.mp (hS hd)
    refine ⟨hmem, ?_⟩
    rw [rowWord_apply hmem.1 hmem.2]
    simpa using hd

private lemma rowSupport_subset (n : ℕ) (b : SeamRowWord n) :
    rowSupport n b ⊆ Finset.Ico 2 n := Finset.filter_subset _ _

private lemma weightSum_rowWord {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Ico 2 n) :
    wordWeightSum n (rowWord n S).toNatWord =
      ∑ d ∈ S, truncatedMersenneWeight n d := by
  rw [wordWeightSum_eq_filter, rowWord_filter hS]

private lemma pulseSum_rowWord {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.Ico 2 n) :
    wordPulse n (rowWord n S).toNatWord = ∑ d ∈ S, rowPulse n d := by
  rw [wordPulse_eq_filter, rowWord_filter hS]

private lemma weightSum_rowSupport (n : ℕ) (b : SeamRowWord n) :
    ∑ d ∈ rowSupport n b, truncatedMersenneWeight n d =
      wordWeightSum n b.toNatWord :=
  (wordWeightSum_eq_filter n b.toNatWord).symm

private lemma pulseSum_rowSupport (n : ℕ) (b : SeamRowWord n) :
    ∑ d ∈ rowSupport n b, rowPulse n d = wordPulse n b.toNatWord :=
  (wordPulse_eq_filter n b.toNatWord).symm

private lemma rowSet_ext {n : ℕ} {S S' : Finset ℕ}
    (hS : S ⊆ Finset.Ico 2 n) (hS' : S' ⊆ Finset.Ico 2 n)
    (h : (rowWord n S).toNatWord = (rowWord n S').toNatWord) : S = S' := by
  rw [← rowWord_filter hS, ← rowWord_filter hS', h]

/-! ### The concrete seam family, unfolded -/

private lemma seamFamily_gap (m : ℕ) (hm : 3 ≤ m) :
    (seamPerturbedFamily m hm).gap = 2 ^ (m + 1) := rfl

private lemma seamFamily_oldSum (m : ℕ) (hm : 3 ≤ m) (b : SeamRowWord m) :
    (seamPerturbedFamily m hm).oldSum b = wordWeightSum m b.toNatWord := rfl

private lemma seamCut_remainder (m : ℕ) (hm : 5 ≤ m) :
    (seamAdjacentCut m hm).remainder =
      seamSubsetTarget m - wordWeightSum m (seamGreedyWord m).toNatWord := rfl

private lemma seamCut_overshoot (m : ℕ) (hm : 5 ≤ m) :
    (seamAdjacentCut m hm).overshoot =
      wordWeightSum m (seamAboveWord m hm).toNatWord - seamSubsetTarget m := rfl

private lemma seamCut_belowPulse (m : ℕ) (hm : 5 ≤ m) :
    (seamAdjacentCut m hm).belowPulse =
      wordPulse m (seamGreedyWord m).toNatWord := rfl

private lemma seamCut_abovePulse (m : ℕ) (hm : 5 ≤ m) :
    (seamAdjacentCut m hm).abovePulse =
      wordPulse m (seamAboveWord m hm).toNatWord := rfl

private lemma seamCut_carries_iff (m : ℕ) (hm : 5 ≤ m) :
    (seamAdjacentCut m hm).successorCarries ↔
      4 * (seamAdjacentCut m hm).overshoot +
        (seamAdjacentCut m hm).abovePulse ≤ 2 ^ (m + 1) := Iff.rfl

private lemma seamIntegerGreedyRemainder_eq (m : ℕ) (hm : 2 ≤ m) :
    seamIntegerGreedyRemainder m =
      seamSubsetTarget m - wordWeightSum m (seamGreedyWord m).toNatWord := by
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [← seamGreedyWord_toList m, weightedBoolSum_toList_eq_wordWeightSum hm]

private lemma seamWeightsFrom_sum (n d : ℕ) :
    (seamWeightsFrom n d).sum =
      ∑ e ∈ Finset.Ico d n, truncatedMersenneWeight n e := by
  by_cases h : d < n
  · rw [seamWeightsFrom_eq_cons h, List.sum_cons, seamWeightsFrom_sum n (d + 1),
      Finset.sum_eq_sum_Ico_succ_bot h]
  · rw [seamWeightsFrom_eq_nil (by omega), Finset.Ico_eq_empty (by omega)]
    simp
termination_by n - d
decreasing_by omega

/-- The superincreasing gap of the row weights: the weight at a rank exceeds
the total of all later weights. -/
private lemma weight_gt_tail {n d : ℕ} (hn : 2 ≤ n) (hd : 1 ≤ d) (hdn : d < n) :
    ∑ e ∈ Finset.Ico (d + 1) n, truncatedMersenneWeight n e <
      truncatedMersenneWeight n d := by
  have h := truncatedMersenneWeight_dominanceGap hn hd hdn
  rw [seamWeightsFrom_sum] at h
  have hpos : 0 < 2 ^ (n + 1) := by positivity
  omega

/-! ### The two extremal supports of the environment -/

/-- `D` is the paper's `D_n`: among the quotient sums over subsets of
`{2,…,n-1}` it gives the largest sum at most `T_n`. -/
def IsRowLower (n : ℕ) (D : Finset ℕ) : Prop :=
  D ⊆ Finset.Ico 2 n ∧
    localPrefixQuotient D (2 * n) ≤ seamSubsetTarget n ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        localPrefixQuotient S (2 * n) ≤ seamSubsetTarget n →
          localPrefixQuotient S (2 * n) ≤ localPrefixQuotient D (2 * n)

/-- `B` is the paper's `B_n`: among the quotient sums over subsets of
`{2,…,n-1}` it gives the smallest sum strictly greater than `T_n`. -/
def IsRowUpper (n : ℕ) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Ico 2 n ∧
    seamSubsetTarget n < localPrefixQuotient B (2 * n) ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        seamSubsetTarget n < localPrefixQuotient S (2 * n) →
          localPrefixQuotient B (2 * n) ≤ localPrefixQuotient S (2 * n)

/-- The take set of the integer greedy process of §`ssec:seam-model`: the ranks
`d = 2,…,n-1` are visited in ascending order against `T_n`, and `d` is taken
exactly when its weight does not exceed the current residual.  The process is
`integerGreedyBits` run on the weight list `seamWeights n = [w(n,2),…,w(n,n-1)]`
with capacity `T_n`; see `paper_greedy_step`. -/
def greedySupport (n : ℕ) : Finset ℕ := rowSupport n (seamGreedyWord n)

/-- One step of the paper's integer greedy rule at rank `d`: take exactly when
the weight fits in the residual, and decrease the residual by the weight when
it is taken. -/
theorem paper_greedy_step {n d : ℕ} (hd : d < n) (C : ℕ) :
    integerGreedyBits (seamWeightsFrom n d) C =
      (decide (truncatedMersenneWeight n d ≤ C)) ::
        integerGreedyBits (seamWeightsFrom n (d + 1))
          (if truncatedMersenneWeight n d ≤ C then
            C - truncatedMersenneWeight n d else C) := by
  rw [seamWeightsFrom_eq_cons hd, integerGreedyBits]
  by_cases h : truncatedMersenneWeight n d ≤ C <;> simp [h]

/-- Membership in the greedy take set is the greedy bit at that rank. -/
theorem paper_greedySupport_mem {n d : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔ seamGreedyWord n ⟨d - 2, by omega⟩ = true := by
  unfold greedySupport rowSupport
  rw [Finset.mem_filter]
  have hval : (seamGreedyWord n).toNatWord d = seamGreedyWord n ⟨d - 2, by omega⟩ := by
    unfold SeamRowWord.toNatWord
    rw [dif_pos (⟨hd, hdn⟩ : 2 ≤ d ∧ d < n)]
  rw [hval]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨Finset.mem_Ico.mpr ⟨hd, hdn⟩, h⟩

private lemma rowQuotient_inj {n : ℕ} (hn : 5 ≤ n) {S S' : Finset ℕ}
    (hS : S ⊆ Finset.Ico 2 n) (hS' : S' ⊆ Finset.Ico 2 n)
    (h : ∑ d ∈ S, truncatedMersenneWeight n d =
      ∑ d ∈ S', truncatedMersenneWeight n d) : S = S' := by
  have hn3 : 3 ≤ n := by omega
  have hw : (seamPerturbedFamily n hn3).oldSum (rowWord n S) =
      (seamPerturbedFamily n hn3).oldSum (rowWord n S') := by
    rw [seamFamily_oldSum, seamFamily_oldSum, weightSum_rowWord hS,
      weightSum_rowWord hS', h]
  exact rowSet_ext hS hS'
    (congrArg SeamRowWord.toNatWord
      ((seamPerturbedFamily n hn3).oldSum_injective hw))

theorem paper_greedySupport_isRowLower {n : ℕ} (hn : 5 ≤ n) :
    IsRowLower n (greedySupport n) := by
  refine ⟨rowSupport_subset n _, ?_, ?_⟩
  · rw [paper_rowQuotient_eq_weightSum]
    show ∑ d ∈ rowSupport n (seamGreedyWord n), truncatedMersenneWeight n d ≤
      seamSubsetTarget n
    rw [weightSum_rowSupport]
    exact (seamAdjacentCut n hn).below_admissible
  · intro S hS hSle
    rw [paper_rowQuotient_eq_weightSum] at hSle
    rw [paper_rowQuotient_eq_weightSum, paper_rowQuotient_eq_weightSum]
    show ∑ d ∈ S, truncatedMersenneWeight n d ≤
      ∑ d ∈ rowSupport n (seamGreedyWord n), truncatedMersenneWeight n d
    rw [weightSum_rowSupport, ← weightSum_rowWord hS]
    refine (seamAdjacentCut n hn).below_maximal (rowWord n S) ?_
    rw [seamFamily_oldSum, weightSum_rowWord hS]
    exact hSle

/-- The paper's greedy rule, read off the take set itself: a rank `d` is taken
exactly when its weight still fits under `T_n` after the weights already taken
at the smaller ranks.  This is Definition `defn:greedy-orbit` in its integer
form, with residual `T_n - ∑_{e ∈ D_n, e < d} w(n,e)`. -/
theorem paper_greedySupport_greedy_rule {n : ℕ} (hn : 5 ≤ n) {d : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔
      truncatedMersenneWeight n d +
          ∑ e ∈ (greedySupport n).filter (fun e => e < d),
            truncatedMersenneWeight n e ≤ seamSubsetTarget n := by
  classical
  obtain ⟨hsub, hadm, hmax⟩ := paper_greedySupport_isRowLower hn
  rw [paper_rowQuotient_eq_weightSum] at hadm
  have hsplit :
      (∑ e ∈ (greedySupport n).filter (fun e => e < d),
          truncatedMersenneWeight n e) +
        (∑ e ∈ (greedySupport n).filter (fun e => ¬ e < d),
          truncatedMersenneWeight n e) =
        ∑ e ∈ greedySupport n, truncatedMersenneWeight n e :=
    Finset.sum_filter_add_sum_filter_not (greedySupport n) (fun e => e < d)
      (truncatedMersenneWeight n)
  constructor
  · intro hmem
    have hmem' : d ∈ (greedySupport n).filter (fun e => ¬ e < d) :=
      Finset.mem_filter.mpr ⟨hmem, by omega⟩
    have hle : truncatedMersenneWeight n d ≤
        ∑ e ∈ (greedySupport n).filter (fun e => ¬ e < d),
          truncatedMersenneWeight n e :=
      Finset.single_le_sum (f := truncatedMersenneWeight n)
        (fun e _ => Nat.zero_le _) hmem'
    omega
  · intro hfit
    by_contra hmem
    have hdnot : d ∉ (greedySupport n).filter (fun e => e < d) := by
      intro hc
      have := (Finset.mem_filter.mp hc).2
      omega
    have hQS : ∑ e ∈ insert d ((greedySupport n).filter (fun e => e < d)),
        truncatedMersenneWeight n e =
        truncatedMersenneWeight n d +
          ∑ e ∈ (greedySupport n).filter (fun e => e < d),
            truncatedMersenneWeight n e :=
      Finset.sum_insert hdnot
    have hSsub : insert d ((greedySupport n).filter (fun e => e < d)) ⊆
        Finset.Ico 2 n := by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he'
      · exact Finset.mem_Ico.mpr ⟨hd, hdn⟩
      · exact hsub (Finset.mem_filter.mp he').1
    have hSle := hmax (insert d ((greedySupport n).filter (fun e => e < d)))
      hSsub (by rw [paper_rowQuotient_eq_weightSum, hQS]; exact hfit)
    rw [paper_rowQuotient_eq_weightSum, paper_rowQuotient_eq_weightSum,
      hQS] at hSle
    have htailsub : (greedySupport n).filter (fun e => ¬ e < d) ⊆
        Finset.Ico (d + 1) n := by
      intro e he
      obtain ⟨heD, hege⟩ := Finset.mem_filter.mp he
      have hene : e ≠ d := by rintro rfl; exact hmem heD
      have hmemIco := Finset.mem_Ico.mp (hsub heD)
      exact Finset.mem_Ico.mpr ⟨by omega, hmemIco.2⟩
    have htail : ∑ e ∈ (greedySupport n).filter (fun e => ¬ e < d),
        truncatedMersenneWeight n e ≤
          ∑ e ∈ Finset.Ico (d + 1) n, truncatedMersenneWeight n e :=
      Finset.sum_le_sum_of_subset htailsub
    have hgap := weight_gt_tail (n := n) (d := d) (by omega) (by omega) hdn
    omega

theorem paper_upperSupport_isRowUpper {n : ℕ} (hn : 5 ≤ n) :
    IsRowUpper n (rowSupport n (seamAboveWord n hn)) := by
  refine ⟨rowSupport_subset n _, ?_, ?_⟩
  · rw [paper_rowQuotient_eq_weightSum, weightSum_rowSupport]
    exact seamAboveWord_strict hn
  · intro S hS hSlt
    rw [paper_rowQuotient_eq_weightSum] at hSlt
    rw [paper_rowQuotient_eq_weightSum, paper_rowQuotient_eq_weightSum]
    show ∑ d ∈ rowSupport n (seamAboveWord n hn), truncatedMersenneWeight n d ≤
      ∑ d ∈ S, truncatedMersenneWeight n d
    rw [weightSum_rowSupport, ← weightSum_rowWord hS]
    refine seamAboveWord_minimal hn (rowWord n S) ?_
    rw [seamFamily_oldSum, weightSum_rowWord hS]
    exact hSlt

theorem paper_isRowLower_unique {n : ℕ} (hn : 5 ≤ n) {D D₀ : Finset ℕ}
    (hD : IsRowLower n D) (hD₀ : IsRowLower n D₀) : D = D₀ := by
  have h1 := hD.2.2 D₀ hD₀.1 hD₀.2.1
  have h2 := hD₀.2.2 D hD.1 hD.2.1
  have heq : localPrefixQuotient D (2 * n) = localPrefixQuotient D₀ (2 * n) :=
    le_antisymm h2 h1
  rw [paper_rowQuotient_eq_weightSum, paper_rowQuotient_eq_weightSum] at heq
  exact rowQuotient_inj hn hD.1 hD₀.1 heq

theorem paper_isRowUpper_unique {n : ℕ} (hn : 5 ≤ n) {B B₀ : Finset ℕ}
    (hB : IsRowUpper n B) (hB₀ : IsRowUpper n B₀) : B = B₀ := by
  have h1 := hB.2.2 B₀ hB₀.1 hB₀.2.1
  have h2 := hB₀.2.2 B hB.1 hB.2.1
  have heq : localPrefixQuotient B (2 * n) = localPrefixQuotient B₀ (2 * n) :=
    le_antisymm h1 h2
  rw [paper_rowQuotient_eq_weightSum, paper_rowQuotient_eq_weightSum] at heq
  exact rowQuotient_inj hn hB.1 hB₀.1 heq

/-- `D_n` exists and is unique. -/
theorem paper_rowLower_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! D : Finset ℕ, IsRowLower n D :=
  ⟨greedySupport n, paper_greedySupport_isRowLower hn,
    fun _ hD => paper_isRowLower_unique hn hD (paper_greedySupport_isRowLower hn)⟩

/-- `B_n` exists and is unique. -/
theorem paper_rowUpper_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! B : Finset ℕ, IsRowUpper n B :=
  ⟨rowSupport n (seamAboveWord n hn), paper_upperSupport_isRowUpper hn,
    fun _ hB => paper_isRowUpper_unique hn hB (paper_upperSupport_isRowUpper hn)⟩

/-! ### The environment -/

/-- Paper display of `thm:dynamics` (`a257_front.tex:2293`).

Fix `n ≥ 5`.  `D_n` is the subset of `{2,…,n-1}` whose quotient sum is largest
among those at most `T_n`, and `B_n` the subset whose quotient sum is smallest
among those strictly greater than `T_n`.  With `r = rem(n)`, `o = Q(B_n,2n)-T_n`
and the two correction terms `p^-`, `p^+`, the conclusion records, in order:

* `D_n` is the greedy support of §`ssec:seam-model`;
* `p^-` and `p^+` lie in `[0, 2(n-2)]`;
* the three-branch formula for `rem(n+1)`;
* the normalised display (III) for `λ_{n+1} = (rem(n+1) - 2^{n+1})/2^{n+1}`,
  in terms of `λ_n = (r - 2^n)/2^n`.
-/
theorem paper_dynamics {n : ℕ} (hn : 5 ≤ n) {D B D' : Finset ℕ}
    (hD : IsRowLower n D) (hB : IsRowUpper n B) (hD' : IsRowLower (n + 1) D')
    {r o pm pp rem : ℕ}
    (hr : localPrefixQuotient D (2 * n) + r = seamSubsetTarget n)
    (ho : seamSubsetTarget n + o = localPrefixQuotient B (2 * n))
    (hpm : pm = ∑ d ∈ D, rowPulse n d)
    (hpp : pp = ∑ d ∈ B, rowPulse n d)
    (hrem : localPrefixQuotient D' (2 * (n + 1)) + rem = seamSubsetTarget (n + 1)) :
    D = greedySupport n ∧
      pm ≤ 2 * (n - 2) ∧ pp ≤ 2 * (n - 2) ∧
      ((rem : ℤ) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          (2 : ℤ) ^ (n + 1) - 4 * (o : ℤ) - (pp : ℤ)
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ)
        else 4 * (r : ℤ) - 2 ^ (n + 1) - (pm : ℤ) - 4) ∧
      (((rem : ℚ) - 2 ^ (n + 1)) / 2 ^ (n + 1) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          -((4 * (o : ℚ) + (pp : ℚ)) / 2 ^ (n + 1))
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) + 2 - (pm : ℚ) / 2 ^ (n + 1)
        else 2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) - ((pm : ℚ) + 4) / 2 ^ (n + 1)) := by
  classical
  have hn3 : 3 ≤ n := by omega
  have hn1 : (5 : ℕ) ≤ n + 1 := by omega
  -- the three extremal supports
  have hDg : D = greedySupport n :=
    paper_isRowLower_unique hn hD (paper_greedySupport_isRowLower hn)
  have hBg : B = rowSupport n (seamAboveWord n hn) :=
    paper_isRowUpper_unique hn hB (paper_upperSupport_isRowUpper hn)
  have hD'g : D' = greedySupport (n + 1) :=
    paper_isRowLower_unique hn1 hD' (paper_greedySupport_isRowLower hn1)
  -- transport the paper's data to the concrete adjacent cut
  have hQD : localPrefixQuotient D (2 * n) =
      wordWeightSum n (seamGreedyWord n).toNatWord := by
    rw [hDg, paper_rowQuotient_eq_weightSum]
    exact weightSum_rowSupport n _
  have hQB : localPrefixQuotient B (2 * n) =
      wordWeightSum n (seamAboveWord n hn).toNatWord := by
    rw [hBg, paper_rowQuotient_eq_weightSum]
    exact weightSum_rowSupport n _
  have hQD' : localPrefixQuotient D' (2 * (n + 1)) =
      wordWeightSum (n + 1) (seamGreedyWord (n + 1)).toNatWord := by
    rw [hD'g, paper_rowQuotient_eq_weightSum]
    exact weightSum_rowSupport (n + 1) _
  have hPM : pm = wordPulse n (seamGreedyWord n).toNatWord := by
    rw [hpm, hDg]; exact pulseSum_rowSupport n _
  have hPP : pp = wordPulse n (seamAboveWord n hn).toNatWord := by
    rw [hpp, hBg]; exact pulseSum_rowSupport n _
  rw [hQD] at hr
  rw [hQB] at ho
  rw [hQD'] at hrem
  have hrK : (seamAdjacentCut n hn).remainder = r := by
    rw [seamCut_remainder]; omega
  have hoK : (seamAdjacentCut n hn).overshoot = o := by
    rw [seamCut_overshoot]; omega
  have hpmK : (seamAdjacentCut n hn).belowPulse = pm := by
    rw [seamCut_belowPulse, hPM]
  have hppK : (seamAdjacentCut n hn).abovePulse = pp := by
    rw [seamCut_abovePulse, hPP]
  have hnextK : (seamAdjacentCut n hn).nextRemainder = rem := by
    rw [seamAdjacentCut_nextRemainder hn,
      seamIntegerGreedyRemainder_eq (n + 1) (by omega)]
    omega
  -- arithmetic facts
  have hpmle : pm ≤ 2 * (n - 2) := by rw [hPM]; exact wordPulse_le n _
  have hpple : pp ≤ 2 * (n - 2) := by rw [hPP]; exact wordPulse_le n _
  have hlin : 2 * n + 4 < 2 ^ (n + 1) := two_mul_add_four_lt_two_pow_succ hn3
  have hpow2 : (2 : ℕ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hpmlt : pm < 2 ^ (n + 1) := by omega
  have hpplt : pp < 2 ^ (n + 1) := by omega
  have hterm : (seamAdjacentCut n hn).terminalWeight = 2 ^ (n + 2) + 4 :=
    seamAdjacentCut_terminalWeight hn
  have htri := (seamAdjacentCut n hn).nextRemainder_trichotomy
  rw [hnextK, hterm, hrK, hoK, hpmK, hppK] at htri
  -- rational scaffolding
  have hQne : ((2 : ℚ) ^ n) ≠ 0 := by positivity
  have hQ1 : (2 : ℚ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  by_cases hU : 4 * o + pp ≤ 2 ^ (n + 1)
  · have hcarry : (seamAdjacentCut n hn).successorCarries := by
      rw [seamCut_carries_iff, hoK, hppK]; exact hU
    rw [if_pos hcarry] at htri
    have hvalN : rem + (4 * o + pp) = 2 ^ (n + 1) := by
      have hgap : (seamPerturbedFamily n hn3).gap = 2 ^ (n + 1) := rfl
      have htri' : rem = 2 ^ (n + 1) - (4 * o + pp) := by
        rw [← hgap]; exact htri
      omega
    have hUZ : 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast hU
    have hZ : (rem : ℤ) + (4 * (o : ℤ) + (pp : ℤ)) = 2 ^ (n + 1) := by
      exact_mod_cast hvalN
    have hQeq : (rem : ℚ) = 2 ^ (n + 1) - (4 * (o : ℚ) + (pp : ℚ)) := by
      have : (rem : ℚ) + (4 * (o : ℚ) + (pp : ℚ)) = 2 ^ (n + 1) := by
        exact_mod_cast hvalN
      linarith
    refine ⟨hDg, hpmle, hpple, ?_, ?_⟩
    · rw [if_pos hUZ]; linarith
    · rw [if_pos hUZ, hQeq, hQ1]
      field_simp
      ring
  · have hncarry : ¬ (seamAdjacentCut n hn).successorCarries := by
      intro hc
      rw [seamCut_carries_iff, hoK, hppK] at hc
      exact hU hc
    rw [if_neg hncarry] at htri
    have hgap : (seamPerturbedFamily n hn3).gap = 2 ^ (n + 1) := rfl
    rw [hgap] at htri
    have hUZ : ¬ (4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1)) := by
      intro hc
      exact hU (by exact_mod_cast hc)
    by_cases hM : 4 * r + 2 ^ (n + 1) - pm < 2 ^ (n + 2) + 4
    · rw [if_pos hM] at htri
      have hvalN : rem + pm = 4 * r + 2 ^ (n + 1) := by omega
      have hMZ : 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 := by
        have h1 : ((2 : ℕ) ^ (n + 1) : ℤ) = (2 : ℤ) ^ (n + 1) := by push_cast; ring
        have h2 : ((2 : ℕ) ^ (n + 2) : ℤ) = (2 : ℤ) ^ (n + 2) := by push_cast; ring
        have h3 : (4 * r + 2 ^ (n + 1) - pm : ℕ) < (2 ^ (n + 2) + 4 : ℕ) := hM
        have h4 : ((4 * r + 2 ^ (n + 1) - pm : ℕ) : ℤ) =
            4 * (r : ℤ) + ((2 : ℕ) ^ (n + 1) : ℤ) - (pm : ℤ) := by
          have : pm ≤ 4 * r + 2 ^ (n + 1) := by omega
          push_cast [Nat.cast_sub this]
          ring
        have h5 : ((4 * r + 2 ^ (n + 1) - pm : ℕ) : ℤ) <
            ((2 ^ (n + 2) + 4 : ℕ) : ℤ) := by exact_mod_cast h3
        rw [h4] at h5
        push_cast at h5
        linarith
      have hQeq : (rem : ℚ) = 4 * (r : ℚ) + 2 ^ (n + 1) - (pm : ℚ) := by
        have : (rem : ℚ) + (pm : ℚ) = 4 * (r : ℚ) + 2 ^ (n + 1) := by
          exact_mod_cast hvalN
        linarith
      have hZ : (rem : ℤ) + (pm : ℤ) = 4 * (r : ℤ) + 2 ^ (n + 1) := by
        exact_mod_cast hvalN
      refine ⟨hDg, hpmle, hpple, ?_, ?_⟩
      · rw [if_neg hUZ, if_pos hMZ]; linarith
      · rw [if_neg hUZ, if_pos hMZ, hQeq, hQ1]
        field_simp
        ring
    · rw [if_neg hM] at htri
      have hbig : 2 ^ (n + 1) + pm + 4 ≤ 4 * r := by omega
      have hvalN : rem + 2 ^ (n + 1) + pm + 4 = 4 * r := by omega
      have hMZ : ¬ (4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4) := by
        have hbigZ : ((2 : ℕ) ^ (n + 1) : ℤ) + (pm : ℤ) + 4 ≤ 4 * (r : ℤ) := by
          exact_mod_cast hbig
        have hpow2Z : ((2 : ℕ) ^ (n + 2) : ℤ) = 2 * ((2 : ℕ) ^ (n + 1) : ℤ) := by
          exact_mod_cast hpow2
        push_cast at hbigZ hpow2Z
        intro hcon
        linarith
      have hQeq : (rem : ℚ) = 4 * (r : ℚ) - 2 ^ (n + 1) - (pm : ℚ) - 4 := by
        have : (rem : ℚ) + 2 ^ (n + 1) + (pm : ℚ) + 4 = 4 * (r : ℚ) := by
          exact_mod_cast hvalN
        linarith
      have hZ : (rem : ℤ) + 2 ^ (n + 1) + (pm : ℤ) + 4 = 4 * (r : ℤ) := by
        exact_mod_cast hvalN
      refine ⟨hDg, hpmle, hpple, ?_, ?_⟩
      · rw [if_neg hUZ, if_neg hMZ]; linarith
      · rw [if_neg hUZ, if_neg hMZ, hQeq, hQ1]
        field_simp
        ring

#print axioms paper_rowWeight_eq_floor
#print axioms paper_rowTarget_eq
#print axioms paper_rowPulse_eq_indicators
#print axioms paper_rowQuotient_eq_weightSum
#print axioms paper_consecutive_not_both_divisible
#print axioms paper_greedy_step
#print axioms paper_greedySupport_mem
#print axioms paper_greedySupport_isRowLower
#print axioms paper_greedySupport_greedy_rule
#print axioms paper_upperSupport_isRowUpper
#print axioms paper_isRowLower_unique
#print axioms paper_isRowUpper_unique
#print axioms paper_rowLower_existsUnique
#print axioms paper_rowUpper_existsUnique
#print axioms paper_dynamics

end ErdosProblems.Erdos257.PaperCompleteR21
