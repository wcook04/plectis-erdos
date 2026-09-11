import Erdos249257.HalfCylinderFalseBitSupply
import Erdos249257.CampbellShiftSynchronization

/-!
# Fatal half gaps force an eventual right seam tail

This module proves the complete eventual-right/fatal-gap classification.
Besides the oriented adjacent-cut lemma for an arbitrary gap-dominating
Boolean word, it shows that half nonmembership forces the concrete integer
seam word eventually to extend on the right.  Conversely, an eventual right
tail has a largest missing rank; its propagated finite supports converge to
the lower endpoint of one real Mersenne gap, while a fixed adjacent competitor
controls the upper endpoint.  The two endpoint-kill lemmas make the straddle
strict and hence produce a fatal half-gap certificate.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy
open scoped BigOperators

namespace HalfCylinderIntegerGreedy

@[simp] theorem weightedBoolSum_replicate_true (weights : List ℕ) :
    weightedBoolSum weights (List.replicate weights.length true) =
      weights.sum := by
  induction weights with
  | nil => simp [weightedBoolSum]
  | cons w ws ih =>
      rw [List.length_cons, List.replicate_succ, weightedBoolSum, ih,
        List.sum_cons]

@[simp] theorem weightedBoolSum_replicate_false (weights : List ℕ) :
    weightedBoolSum weights (List.replicate weights.length false) = 0 := by
  induction weights with
  | nil => simp [weightedBoolSum]
  | cons w ws ih =>
      rw [List.length_cons, List.replicate_succ, weightedBoolSum, ih]

/-- In a gap-dominating word, the two Boolean words

`prefix ++ false ++ allTrueSuffix`

and

`prefix ++ true ++ allFalseSuffix`

are adjacent in weighted-sum order: every equal-length Boolean word lies on
one of the two closed sides.  This is the oriented strengthening of
`weightedBoolSum_separated` needed by cylinder-gap arguments. -/
theorem weightedBoolSum_adjacent_cut
    {gap cutWeight : ℕ}
    {prefixWeights suffixWeights : List ℕ}
    (hdom : GapDominates gap
      (prefixWeights ++ cutWeight :: suffixWeights))
    {prefixBits candidate : List Bool}
    (hprefix : prefixBits.length = prefixWeights.length)
    (hcandidate : candidate.length =
      (prefixWeights ++ cutWeight :: suffixWeights).length) :
    weightedBoolSum
        (prefixWeights ++ cutWeight :: suffixWeights) candidate ≤
      weightedBoolSum
        (prefixWeights ++ cutWeight :: suffixWeights)
        (prefixBits ++ false :: List.replicate suffixWeights.length true) ∨
    weightedBoolSum
        (prefixWeights ++ cutWeight :: suffixWeights)
        (prefixBits ++ true :: List.replicate suffixWeights.length false) ≤
      weightedBoolSum
        (prefixWeights ++ cutWeight :: suffixWeights) candidate := by
  induction prefixWeights generalizing prefixBits candidate with
  | nil =>
      have hprefixNil : prefixBits = [] :=
        List.length_eq_zero_iff.mp hprefix
      subst prefixBits
      cases candidate with
      | nil => simp at hcandidate
      | cons bit bits =>
          simp only [List.length_cons] at hcandidate
          cases bit
          · left
            simp only [List.nil_append, weightedBoolSum]
            rw [weightedBoolSum_replicate_true]
            exact weightedBoolSum_le_sum suffixWeights bits
          · right
            simp [weightedBoolSum]
  | cons headWeight tailWeights ih =>
      cases prefixBits with
      | nil => simp at hprefix
      | cons prefixBit prefixTail =>
          cases candidate with
          | nil => simp at hcandidate
          | cons candidateBit candidateTail =>
              simp only [List.cons_append, List.length_cons,
                Nat.succ.injEq] at hprefix hcandidate
              change
                gap + (tailWeights ++ cutWeight :: suffixWeights).sum ≤
                    headWeight ∧
                  GapDominates gap
                    (tailWeights ++ cutWeight :: suffixWeights)
                at hdom
              obtain ⟨hhead, htail⟩ := hdom
              have hcandidateTailLe :=
                weightedBoolSum_le_sum
                  (tailWeights ++ cutWeight :: suffixWeights) candidateTail
              have hupperTailLe :=
                weightedBoolSum_le_sum
                  (tailWeights ++ cutWeight :: suffixWeights)
                  (prefixTail ++
                    true :: List.replicate suffixWeights.length false)
              cases prefixBit <;> cases candidateBit
              · rcases ih htail hprefix hcandidate with h | h
                · left
                  simp only [List.cons_append, weightedBoolSum]
                  omega
                · right
                  simp only [List.cons_append, weightedBoolSum]
                  omega
              · right
                simp only [List.cons_append, weightedBoolSum]
                omega
              · left
                simp only [List.cons_append, weightedBoolSum]
                omega
              · rcases ih htail hprefix hcandidate with h | h
                · left
                  simp only [List.cons_append, weightedBoolSum]
                  omega
                · right
                  simp only [List.cons_append, weightedBoolSum]
                  omega

end HalfCylinderIntegerGreedy

/-- Every seam-greedy word from row five onward omits some rank.  Otherwise
it would contain the first three ranks, whose exact truncated sum is already
strictly above the seam target. -/
theorem seamGreedyWord_exists_false
    (s : ℕ) (hs : 5 ≤ s) :
    ∃ i : Fin (s - 2), seamGreedyWord s i = false := by
  by_contra hfalse
  push Not at hfalse
  have hall : ∀ i : Fin (s - 2), seamGreedyWord s i = true := by
    intro i
    exact Bool.eq_true_of_not_eq_false (hfalse i)
  have hsum_le :
      wordWeightSum s (seamHeadThreeWord s).toNatWord ≤
        wordWeightSum s (seamGreedyWord s).toNatWord := by
    unfold wordWeightSum
    apply Finset.sum_le_sum
    intro i hi
    have his : i + 2 < s := by
      have := Finset.mem_range.mp hi
      omega
    have hgreedy :
        (seamGreedyWord s).toNatWord (i + 2) = true := by
      simp [SeamRowWord.toNatWord, his, hall ⟨i, by omega⟩]
    simp [hgreedy]
    split <;> simp
  have hadmissible := integerGreedyBits_admissible
    (seamWeights s) (seamSubsetTarget s)
  rw [← seamGreedyWord_toList s,
    weightedBoolSum_toList_eq_wordWeightSum (by omega)] at hadmissible
  have habove := seamHeadThreeWord_above_target hs
  omega

/-- Inside the natural rank window of a seam word, absence from its support
is exactly a false Boolean coordinate. -/
theorem not_mem_seamWordSupport_iff_false
    {s d : ℕ} (b : SeamRowWord s) (hd2 : 2 ≤ d) (hds : d < s) :
    d ∉ seamWordSupport b ↔
      b ⟨d - 2, by omega⟩ = false := by
  constructor
  · intro hnot
    by_contra hfalse
    have htrue : b ⟨d - 2, by omega⟩ = true :=
      Bool.eq_true_of_not_eq_false hfalse
    apply hnot
    exact mem_seamWordSupport_iff.mpr
      ⟨⟨d - 2, by omega⟩, htrue, by
        simp [Nat.sub_add_cancel hd2]⟩
  · intro hfalse hmem
    obtain ⟨i, hi, hdi⟩ := mem_seamWordSupport_iff.mp hmem
    have hieq : i = ⟨d - 2, by omega⟩ := by
      apply Fin.ext
      change (i : ℕ) = d - 2
      omega
    rw [hieq, hfalse] at hi
    contradiction

/-- A row-five-or-later greedy support has a largest missing rank.  Splitting
just below it leaves a finite prefix and a completely filled upper interval.
This is the finite support normal form used by the reverse fatal-gap route. -/
theorem exists_maximal_missing_rank_support_decomposition
    (S : ℕ) (hS5 : 5 ≤ S) :
    ∃ (D : ℕ) (u : Finset ℕ),
      2 ≤ D ∧ D < S ∧
      D ∉ seamWordSupport (seamGreedyWord S) ∧
      (∀ e ∈ u, 2 ≤ e ∧ e < D) ∧
      seamWordSupport (seamGreedyWord S) =
        u ∪ Finset.Ico (D + 1) S := by
  classical
  obtain ⟨i, hi⟩ := seamGreedyWord_exists_false S hS5
  let d₀ : ℕ := (i : ℕ) + 2
  have hd₀2 : 2 ≤ d₀ := by omega
  have hd₀S : d₀ < S := by
    dsimp [d₀]
    omega
  have hd₀not : d₀ ∉ seamWordSupport (seamGreedyWord S) := by
    apply (not_mem_seamWordSupport_iff_false
      (seamGreedyWord S) hd₀2 hd₀S).2
    simpa [d₀] using hi
  let missing : Finset ℕ :=
    (Finset.Ico 2 S).filter
      (fun d => d ∉ seamWordSupport (seamGreedyWord S))
  have hmissing : missing.Nonempty := by
    refine ⟨d₀, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hd₀2, hd₀S⟩, hd₀not⟩
  let D : ℕ := missing.max' hmissing
  let u : Finset ℕ :=
    (seamWordSupport (seamGreedyWord S)).filter (fun e => e < D)
  have hDmissing : D ∈ missing := Finset.max'_mem missing hmissing
  have hDdata := Finset.mem_filter.mp hDmissing
  have hDbounds := Finset.mem_Ico.mp hDdata.1
  have hDnot := hDdata.2
  refine ⟨D, u, hDbounds.1, hDbounds.2, hDnot, ?_, ?_⟩
  · intro e he
    have hedata := Finset.mem_filter.mp he
    exact ⟨(seamWordSupport_below hedata.1).1, hedata.2⟩
  · ext e
    constructor
    · intro hesupport
      by_cases heD : e < D
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨hesupport, heD⟩))
      · apply Finset.mem_union.mpr
        apply Or.inr
        have hebounds := seamWordSupport_below hesupport
        have hene : e ≠ D := by
          intro heq
          subst e
          exact hDnot hesupport
        exact Finset.mem_Ico.mpr ⟨by omega, hebounds.2⟩
    · intro heunion
      rcases Finset.mem_union.mp heunion with heu | heinterval
      · exact (Finset.mem_filter.mp heu).1
      · by_contra henot
        have hebounds := Finset.mem_Ico.mp heinterval
        have hemissing : e ∈ missing := Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, hebounds.2⟩, henot⟩
        have heDle : e ≤ D := Finset.le_max' missing e hemissing
        omega

/-- The concrete right-tail predicate, expressed without duplicating the
three scalar branch inequalities. -/
def SeamGreedyEventuallyRight : Prop :=
  ∃ S : ℕ, 5 ≤ S ∧
    ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true

/-- Repeated right extension preserves the base support and fills precisely
the consecutive ranks added after the base row. -/
theorem seamWordSupport_add_eq_of_eventually_right
    (S : ℕ) (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ j : ℕ,
      seamWordSupport (seamGreedyWord (S + j)) =
        seamWordSupport (seamGreedyWord S) ∪ Finset.Ico S (S + j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show S + (j + 1) = (S + j) + 1 by omega,
        hright (S + j) (by omega),
        seamWordSupport_extend_true (by omega), ih]
      ext e
      by_cases hebase : e ∈ seamWordSupport (seamGreedyWord S)
      · simp [hebase]
      · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Ico,
          hebase, false_or]
        omega

/-- Once the largest missing rank `D` is fixed, every later support is the
same finite prefix `u` followed by the full interval strictly above `D`. -/
theorem seamWordSupport_add_eq_prefix_union_Ico
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hDS : D < S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) (j : ℕ) :
    seamWordSupport (seamGreedyWord (S + j)) =
      u ∪ Finset.Ico (D + 1) (S + j) := by
  rw [seamWordSupport_add_eq_of_eventually_right S hS5 hright j, hbase]
  ext e
  by_cases heu : e ∈ u
  · simp [heu]
  · simp only [Finset.mem_union, Finset.mem_Ico, heu, false_or]
    omega

/-- The seam word that selects exactly the ranks of `F` lying in its row
window.  A separate bounds hypothesis below turns this into an exact support
constructor. -/
def seamRowWordOfFinset (s : ℕ) (F : Finset ℕ) : SeamRowWord s :=
  fun i => decide ((i : ℕ) + 2 ∈ F)

theorem seamWordSupport_seamRowWordOfFinset
    {s : ℕ} {F : Finset ℕ}
    (hF : ∀ d ∈ F, 2 ≤ d ∧ d < s) :
    seamWordSupport (seamRowWordOfFinset s F) = F := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨i, hi, rfl⟩ := mem_seamWordSupport_iff.mp hd
    simpa [seamRowWordOfFinset] using hi
  · intro hd
    have hdbounds := hF d hd
    apply mem_seamWordSupport_iff.mpr
    refine ⟨⟨d - 2, by omega⟩, ?_, ?_⟩
    · simp [seamRowWordOfFinset, Nat.sub_add_cancel hdbounds.1, hd]
    · simp [Nat.sub_add_cancel hdbounds.1]

/-- The real finite value of a propagated right-tail support is its fixed
prefix value plus the corresponding initial segment of the Mersenne tail. -/
theorem seamGreedyFiniteValue_add_eq_prefix_add_partialTail
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) (j : ℕ) :
    seamGreedyFiniteValue (S + j) =
      positiveMersenneSupportValue (↑u : Set ℕ) +
        ∑ k ∈ Finset.range (S + j - (D + 1)),
          mersenneWeight (D + 1 + k) := by
  classical
  have hsupport := seamWordSupport_add_eq_prefix_union_Ico
    hS5 hDS hright hbase j
  have hdisjoint : Disjoint u (Finset.Ico (D + 1) (S + j)) := by
    apply Finset.disjoint_left.mpr
    intro e heu heinterval
    have heu' := hu e heu
    have heinterval' := Finset.mem_Ico.mp heinterval
    omega
  rw [seamGreedyFiniteValue, hsupport,
    positiveMersenneSupportValue_coe_finset,
    Finset.sum_union hdisjoint,
    ← positiveMersenneSupportValue_coe_finset,
    Finset.sum_Ico_eq_sum_range]

/-- The filled finite suffixes stay below the half target at every row, so
their limit—the complete Mersenne tail above `D`—does too. -/
theorem prefix_add_mersenneTail_le_half_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail D ≤
      (1 / 2 : ℝ) := by
  have hpartial : ∀ j : ℕ,
      positiveMersenneSupportValue (↑u : Set ℕ) +
          ∑ k ∈ Finset.range (S + j - (D + 1)),
            mersenneWeight (D + 1 + k) ≤
        (1 / 2 : ℝ) := by
    intro j
    rw [← seamGreedyFiniteValue_add_eq_prefix_add_partialTail
      hS5 hDS hu hright hbase j]
    have hnonneg :=
      (seamGreedyFiniteValue_general_error_bounds (S + j) (by omega)).1
    linarith
  have hindex : Tendsto (fun j : ℕ => S + j - (D + 1)) atTop atTop := by
    convert tendsto_add_atTop_nat (S - (D + 1)) using 1
    funext j
    omega
  have htail : Tendsto
      (fun j : ℕ =>
        ∑ k ∈ Finset.range (S + j - (D + 1)),
          mersenneWeight (D + 1 + k))
      atTop (nhds (mersenneTail D)) := by
    have hbaseTail :=
      (summable_mersenneTail D).tendsto_sum_tsum_nat.comp hindex
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbaseTail
  have hlimit : Tendsto
      (fun j : ℕ => positiveMersenneSupportValue (↑u : Set ℕ) +
        ∑ k ∈ Finset.range (S + j - (D + 1)),
          mersenneWeight (D + 1 + k))
      atTop
      (nhds (positiveMersenneSupportValue (↑u : Set ℕ) +
        mersenneTail D)) := by
    exact tendsto_const_nhds.add htail
  exact le_of_tendsto' hlimit hpartial

/-- The lazy endpoint is not rational; hence the preceding weak inequality
is strict at the half target. -/
theorem prefix_add_mersenneTail_lt_half_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail D <
      (1 / 2 : ℝ) := by
  apply lt_of_le_of_ne
  · exact prefix_add_mersenneTail_le_half_of_eventually_right
      hS5 hDS hu hright hbase
  · exact half_ne_coe_finset_add_mersenneTail u D

/-- The recursively generated truncated tail is exactly the sum over its
natural rank interval. -/
theorem sum_truncatedMersenneWeight_Ico_eq_seamWeightsFrom_sum
    (s d : ℕ) (hds : d ≤ s) :
    ∑ e ∈ Finset.Ico d s, truncatedMersenneWeight s e =
      (seamWeightsFrom s d).sum := by
  rw [Finset.sum_Ico_eq_sum_range,
    seamWeightsFrom_eq_ofFn hds, List.sum_ofFn]
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => truncatedMersenneWeight s (d + k)) (s - d)).symm

/-- The integer weight of any seam word is bounded by its real Mersenne
support value after multiplication by the row scale. -/
theorem wordWeightSum_cast_le_scaled_supportValue
    {s : ℕ} (b : SeamRowWord s) :
    ((wordWeightSum s b.toNatWord : ℕ) : ℝ) ≤
      (4 : ℝ) ^ s *
        positiveMersenneSupportValue (↑(seamWordSupport b) : Set ℕ) := by
  rw [wordWeightSum_eq_sum_seamWordSupport]
  push_cast
  rw [positiveMersenneSupportValue_coe_finset]
  calc
    ∑ d ∈ seamWordSupport b,
          ((truncatedMersenneWeight s d : ℕ) : ℝ)
        ≤ ∑ d ∈ seamWordSupport b,
            (4 : ℝ) ^ s * mersenneWeight d := by
          apply Finset.sum_le_sum
          intro d hd
          exact truncatedMersenneWeight_cast_le_scaled
            (by have := (seamWordSupport_below hd).1; omega)
    _ = (4 : ℝ) ^ s *
          ∑ d ∈ seamWordSupport b, mersenneWeight d := by
        rw [Finset.mul_sum]

/-- Replacing the last missing rank `D` by true and clearing all later ranks
produces a fixed-support word strictly above every later seam target. -/
theorem upper_competitor_exceeds_target_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hD2 : 2 ≤ D) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) (j : ℕ) :
    seamSubsetTarget (S + j) <
      wordWeightSum (S + j)
        (seamRowWordOfFinset (S + j) (insert D u)).toNatWord := by
  classical
  let n : ℕ := S + j
  let upper : SeamRowWord n := seamRowWordOfFinset n (insert D u)
  have hDnotu : D ∉ u := by
    intro hDu
    exact (Nat.lt_irrefl D) (hu D hDu).2
  have hupperBounds : ∀ e ∈ insert D u, 2 ≤ e ∧ e < n := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · exact ⟨hD2, by dsimp [n]; omega⟩
    · have hebounds := hu e heu
      exact ⟨hebounds.1, by dsimp [n]; omega⟩
  have hupperSupport : seamWordSupport upper = insert D u := by
    exact seamWordSupport_seamRowWordOfFinset hupperBounds
  have hlowerSupport :
      seamWordSupport (seamGreedyWord n) =
        u ∪ Finset.Ico (D + 1) n := by
    dsimp [n]
    exact seamWordSupport_add_eq_prefix_union_Ico
      hS5 hDS hright hbase j
  have hdisjoint : Disjoint u (Finset.Ico (D + 1) n) := by
    apply Finset.disjoint_left.mpr
    intro e heu heinterval
    have heu' := hu e heu
    have heinterval' := Finset.mem_Ico.mp heinterval
    omega
  have hupperSum :
      wordWeightSum n upper.toNatWord =
        truncatedMersenneWeight n D +
          ∑ e ∈ u, truncatedMersenneWeight n e := by
    rw [wordWeightSum_eq_sum_seamWordSupport, hupperSupport,
      Finset.sum_insert hDnotu]
  have hlowerSum :
      wordWeightSum n (seamGreedyWord n).toNatWord =
        (∑ e ∈ u, truncatedMersenneWeight n e) +
          ∑ e ∈ Finset.Ico (D + 1) n,
            truncatedMersenneWeight n e := by
    rw [wordWeightSum_eq_sum_seamWordSupport, hlowerSupport,
      Finset.sum_union hdisjoint]
  have hdominance := truncatedMersenneWeight_dominanceGap
    (s := n) (d := D) (by dsimp [n]; omega) (by omega)
      (by dsimp [n]; omega)
  have hinterval :=
    sum_truncatedMersenneWeight_Ico_eq_seamWeightsFrom_sum
      n (D + 1) (by dsimp [n]; omega)
  have hseparated :
      wordWeightSum n (seamGreedyWord n).toNatWord + 2 ^ (n + 1) ≤
        wordWeightSum n upper.toNatWord := by
    rw [hupperSum, hlowerSum, hinterval]
    omega
  change seamSubsetTarget n < wordWeightSum n upper.toNatWord
  by_contra hnot
  have hupperAdmissibleWord :
      wordWeightSum n upper.toNatWord ≤ seamSubsetTarget n :=
    Nat.le_of_not_gt hnot
  have hupperAdmissible :
      weightedBoolSum (seamWeights n) upper.toList ≤ seamSubsetTarget n := by
    rw [weightedBoolSum_toList_eq_wordWeightSum (by dsimp [n]; omega)]
    exact hupperAdmissibleWord
  have hmax := integerGreedyBits_maximal
    (gap := 2 ^ (n + 1)) (by positivity)
    (seamWeights_gapDominates (by dsimp [n]; omega))
    (C := seamSubsetTarget n) (bits := upper.toList)
    (by simp [SeamRowWord.toList]) hupperAdmissible
  have hmaxWord : wordWeightSum n upper.toNatWord ≤
      wordWeightSum n (seamGreedyWord n).toNatWord := by
    calc
      wordWeightSum n upper.toNatWord =
          weightedBoolSum (seamWeights n) upper.toList := by
            rw [weightedBoolSum_toList_eq_wordWeightSum
              (by dsimp [n]; omega)]
      _ ≤ weightedBoolSum (seamWeights n)
          (integerGreedyBits (seamWeights n) (seamSubsetTarget n)) := hmax
      _ = wordWeightSum n (seamGreedyWord n).toNatWord := by
        rw [← seamGreedyWord_toList n,
          weightedBoolSum_toList_eq_wordWeightSum (by dsimp [n]; omega)]
  have hgapPos : 0 < 2 ^ (n + 1) := by positivity
  omega

/-- Exact real normalization of the finite seam target. -/
theorem seamSubsetTarget_div_four_pow_eq
    (s : ℕ) (hs : 1 ≤ s) :
    ((seamSubsetTarget s : ℕ) : ℝ) / (4 : ℝ) ^ s =
      (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ s := by
  have hrat := seamSubsetTarget_cast_rat s hs
  have hreal : ((seamSubsetTarget s : ℕ) : ℝ) =
      (4 : ℝ) ^ s / 2 - (2 : ℝ) ^ s := by
    simpa using congrArg (fun q : ℚ => (q : ℝ)) hrat
  rw [hreal]
  have hfour : (4 : ℝ) ^ s = (2 : ℝ) ^ s * (2 : ℝ) ^ s := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hhalf : (1 / 2 : ℝ) ^ s = 1 / (2 : ℝ) ^ s := by
    simp
  rw [hfour, hhalf]
  field_simp

/-- Along every translated row sequence, the normalized finite seam target
converges to `1/2`. -/
theorem tendsto_seamSubsetTarget_div_four_pow_add
    (S : ℕ) (hS1 : 1 ≤ S) :
    Tendsto
      (fun j : ℕ =>
        ((seamSubsetTarget (S + j) : ℕ) : ℝ) /
          (4 : ℝ) ^ (S + j))
      atTop (nhds (1 / 2 : ℝ)) := by
  have hpowBase : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
  have hpow := hpowBase.comp (tendsto_add_atTop_nat S)
  have heq :
      (fun j : ℕ =>
        ((seamSubsetTarget (S + j) : ℕ) : ℝ) /
          (4 : ℝ) ^ (S + j)) =
        (fun j : ℕ => (1 / 2 : ℝ) - (1 / 2 : ℝ) ^ (S + j)) := by
    funext j
    exact seamSubsetTarget_div_four_pow_eq (S + j) (by omega)
  rw [heq]
  have hconst : Tendsto (fun _ : ℕ => (1 / 2 : ℝ))
      atTop (nhds (1 / 2 : ℝ)) := tendsto_const_nhds
  simpa [Nat.add_comm] using hconst.sub hpow

/-- Each normalized target lies below the real value of the fixed upper
competitor. -/
theorem normalized_target_lt_upper_competitor_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hD2 : 2 ≤ D) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) (j : ℕ) :
    ((seamSubsetTarget (S + j) : ℕ) : ℝ) /
        (4 : ℝ) ^ (S + j) <
      positiveMersenneSupportValue (↑(insert D u) : Set ℕ) := by
  have htarget := upper_competitor_exceeds_target_of_eventually_right
    hS5 hD2 hDS hu hright hbase j
  have htargetCast :
      ((seamSubsetTarget (S + j) : ℕ) : ℝ) <
        ((wordWeightSum (S + j)
          (seamRowWordOfFinset (S + j) (insert D u)).toNatWord : ℕ) : ℝ) := by
    exact_mod_cast htarget
  have hword := wordWeightSum_cast_le_scaled_supportValue
    (seamRowWordOfFinset (S + j) (insert D u))
  have hbounds : ∀ e ∈ insert D u, 2 ≤ e ∧ e < S + j := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · exact ⟨hD2, by omega⟩
    · have hebounds := hu e heu
      exact ⟨hebounds.1, by omega⟩
  have hsupport := seamWordSupport_seamRowWordOfFinset hbounds
  rw [hsupport] at hword
  have hscaled :
      ((seamSubsetTarget (S + j) : ℕ) : ℝ) <
        (4 : ℝ) ^ (S + j) *
          positiveMersenneSupportValue (↑(insert D u) : Set ℕ) :=
    htargetCast.trans_le hword
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ (S + j))).2
  simpa [mul_comm] using hscaled

/-- Passing the normalized targets to their limit puts `1/2` below the
fixed competitor; odd-denominator finiteness excludes equality. -/
theorem half_lt_upper_competitor_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hD2 : 2 ≤ D) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) :
    (1 / 2 : ℝ) <
      positiveMersenneSupportValue (↑(insert D u) : Set ℕ) := by
  have hle : (1 / 2 : ℝ) ≤
      positiveMersenneSupportValue (↑(insert D u) : Set ℕ) := by
    exact le_of_tendsto'
      (tendsto_seamSubsetTarget_div_four_pow_add S (by omega))
      (fun j => (normalized_target_lt_upper_competitor_of_eventually_right
        hS5 hD2 hDS hu hright hbase j).le)
  have hzero : 0 ∉ insert D u := by
    intro hzero
    rcases Finset.mem_insert.mp hzero with hDzero | hzeroU
    · omega
    · exact (by have := (hu 0 hzeroU).1; omega)
  exact lt_of_le_of_ne hle
    (positiveMersenneSupportValue_coe_finset_ne_half hzero).symm

/-- A true successor terminal bit can only come from the non-carry right
branch, so its prefix is definitionally the old greedy word. -/
theorem seamGreedyWord_succ_eq_extend_true_of_terminal_true
    (s : ℕ) (hs : 5 ≤ s)
    (hterminal :
      SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = true) :
    seamGreedyWord (s + 1) = (seamGreedyWord s).extend true := by
  classical
  let K := seamAdjacentCut s hs
  have hterminal' := hterminal
  rw [← seamCutNextWord_eq_greedyWord_succ hs] at hterminal'
  change SeamRowWord.terminal (by omega)
      (K.prefixChoice.extend
        (decide (K.terminalWeight ≤ K.prefixRemainder))) = true
    at hterminal'
  simp only [SeamRowWord.terminal_extend] at hterminal'
  have hle : K.terminalWeight ≤ K.prefixRemainder := by
    simpa only [decide_eq_true_eq] using hterminal'
  have hncarry : ¬ K.successorCarries := by
    intro hcarry
    exact (Nat.not_le_of_lt (K.carry_prefix_lt_terminal hcarry)) hle
  rw [← seamCutNextWord_eq_greedyWord_succ hs]
  change K.prefixChoice.extend
      (decide (K.terminalWeight ≤ K.prefixRemainder)) =
    K.below.extend true
  rw [PerturbedFamily.AdjacentCut.prefixChoice, if_neg hncarry]
  simp [hle]

/-- At every concrete row, extending on the right is exactly the same as
seeing a true terminal bit in the next greedy word. -/
theorem seamGreedyWord_succ_eq_extend_true_iff_terminal_true
    (s : ℕ) (hs : 5 ≤ s) :
    seamGreedyWord (s + 1) = (seamGreedyWord s).extend true ↔
      SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = true := by
  constructor
  · intro hright
    rw [hright]
    exact SeamRowWord.terminal_extend (by omega) (seamGreedyWord s) true
  · exact seamGreedyWord_succ_eq_extend_true_of_terminal_true s hs

/-- The word-level right-tail predicate is exactly eventual truth of the
successor terminal coordinate. -/
theorem seamGreedyEventuallyRight_iff_eventually_terminal_true :
    SeamGreedyEventuallyRight ↔
      ∃ S : ℕ, ∃ hS5 : 5 ≤ S, ∀ (s : ℕ) (hs : S ≤ s),
        SeamRowWord.terminal (by omega)
          (seamGreedyWord (s + 1)) = true := by
  constructor
  · rintro ⟨S, hS5, hright⟩
    refine ⟨S, hS5, fun s hs => ?_⟩
    exact
      (seamGreedyWord_succ_eq_extend_true_iff_terminal_true
        s (hS5.trans hs)).mp (hright s hs)
  · rintro ⟨S, hS5, hterminal⟩
    refine ⟨S, hS5, fun s hs => ?_⟩
    exact
      (seamGreedyWord_succ_eq_extend_true_iff_terminal_true
        s (hS5.trans hs)).mpr (hterminal s hs)

/-- Half nonmembership rules out false terminal bits beyond every bound by
contraposition of the cofinal-false compactness consumer.  Since the terminal
coordinate is Boolean, all sufficiently late terminals are true. -/
theorem eventually_terminal_true_of_half_not_mem
    (hnotmem : (1 / 2 : ℝ) ∉ mersenneAchievementSet) :
    ∃ S : ℕ, ∃ hS5 : 5 ≤ S, ∀ (s : ℕ) (hs : S ≤ s),
      SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = true := by
  classical
  by_contra hnot
  push Not at hnot
  have hunbounded : ∀ N, ∃ p, ∃ hp5 : 5 ≤ p,
      N ≤ p ∧
        SeamRowWord.terminal (by omega)
          (seamGreedyWord (p + 1)) = false := by
    intro N
    obtain ⟨p, hp, hterminal⟩ := hnot (max 5 N) (by omega)
    have hp5 : 5 ≤ p := by omega
    refine ⟨p, hp5, by omega, ?_⟩
    have : SeamRowWord.terminal (by omega)
        (seamGreedyWord (p + 1)) ≠ true := by
      simpa using hterminal
    exact Bool.eq_false_of_not_eq_true this
  exact hnotmem
    (half_mem_mersenneAchievementSet_of_unboundedTerminalFalse hunbounded)

/-- The already-formalized compactness route proves one exact direction of
the eventual-right classification. -/
theorem seamGreedyEventuallyRight_of_half_not_mem
    (hnotmem : (1 / 2 : ℝ) ∉ mersenneAchievementSet) :
    SeamGreedyEventuallyRight := by
  exact seamGreedyEventuallyRight_iff_eventually_terminal_true.mpr
    (eventually_terminal_true_of_half_not_mem hnotmem)

/-- Every cut-locator fatal half gap forces the concrete integer seam to
stabilize on its right extension. -/
theorem seamGreedyEventuallyRight_of_existsFatalHalfGap
    (hgap : ExistsFatalHalfGap) :
    SeamGreedyEventuallyRight :=
  seamGreedyEventuallyRight_of_half_not_mem
    (existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet.mp hgap)

/-- An eventual concrete right seam tail produces a finite fatal gap.  Choose
the largest missing rank `D` in the base row, retain the selected prefix below
`D`, and use the two limit endpoints proved above at depth `D - 1`. -/
theorem existsFatalHalfGap_of_seamGreedyEventuallyRight
    (heventual : SeamGreedyEventuallyRight) :
    ExistsFatalHalfGap := by
  rcases heventual with ⟨S, hS5, hright⟩
  obtain ⟨D, u, hD2, hDS, _hDnot, hu, hbase⟩ :=
    exists_maximal_missing_rank_support_decomposition S hS5
  refine ⟨u, D - 1, ?_, ?_, ?_⟩
  · intro e he
    have hebounds := hu e he
    exact ⟨by omega, by omega⟩
  · have hlower :=
      prefix_add_mersenneTail_lt_half_of_eventually_right
        hS5 hDS hu hright hbase
    simpa [show D - 1 + 1 = D by omega] using hlower
  · have hupper := half_lt_upper_competitor_of_eventually_right
      hS5 hD2 hDS hu hright hbase
    have hDnotu : D ∉ u := by
      intro hDu
      exact (Nat.lt_irrefl D) (hu D hDu).2
    rw [positiveMersenneSupportValue_insert hDnotu] at hupper
    simpa [show D - 1 + 1 = D by omega, add_comm] using hupper

/-- Fatal half gaps and eventual right seam tails are the same concrete
phenomenon. -/
theorem seamGreedyEventuallyRight_iff_existsFatalHalfGap :
    SeamGreedyEventuallyRight ↔ ExistsFatalHalfGap :=
  ⟨existsFatalHalfGap_of_seamGreedyEventuallyRight,
    seamGreedyEventuallyRight_of_existsFatalHalfGap⟩

/-- Equivalent membership-complement form of the classification. -/
theorem seamGreedyEventuallyRight_iff_half_not_mem :
    SeamGreedyEventuallyRight ↔
      (1 / 2 : ℝ) ∉ mersenneAchievementSet := by
  rw [seamGreedyEventuallyRight_iff_existsFatalHalfGap,
    existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet]

/-- Equivalently, a final skipped exponent of the actual real greedy orbit
forces an eventual concrete right seam tail. -/
theorem seamGreedyEventuallyRight_of_exists_isLastHalfGreedySkip
    (hlast : ∃ M : ℕ, IsLastHalfGreedySkip M) :
    SeamGreedyEventuallyRight :=
  seamGreedyEventuallyRight_of_existsFatalHalfGap
    (existsFatalHalfGap_iff_exists_isLastHalfGreedySkip.mpr hlast)

/-- Equivalent last-real-skip form of the classification. -/
theorem seamGreedyEventuallyRight_iff_exists_isLastHalfGreedySkip :
    SeamGreedyEventuallyRight ↔ ∃ M : ℕ, IsLastHalfGreedySkip M := by
  rw [seamGreedyEventuallyRight_iff_existsFatalHalfGap,
    existsFatalHalfGap_iff_exists_isLastHalfGreedySkip]

#print axioms HalfCylinderIntegerGreedy.weightedBoolSum_adjacent_cut
#print axioms seamGreedyWord_succ_eq_extend_true_of_terminal_true
#print axioms seamGreedyWord_succ_eq_extend_true_iff_terminal_true
#print axioms seamGreedyEventuallyRight_iff_eventually_terminal_true
#print axioms eventually_terminal_true_of_half_not_mem
#print axioms seamGreedyEventuallyRight_of_half_not_mem
#print axioms seamGreedyEventuallyRight_of_existsFatalHalfGap
#print axioms existsFatalHalfGap_of_seamGreedyEventuallyRight
#print axioms seamGreedyEventuallyRight_iff_existsFatalHalfGap
#print axioms seamGreedyEventuallyRight_iff_half_not_mem
#print axioms seamGreedyEventuallyRight_of_exists_isLastHalfGreedySkip
#print axioms seamGreedyEventuallyRight_iff_exists_isLastHalfGreedySkip

end Erdos249257
