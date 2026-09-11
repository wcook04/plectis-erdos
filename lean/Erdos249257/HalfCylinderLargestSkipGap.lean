import Erdos249257.HalfCylinderHalfMembershipClassification

/-!
# Largest skipped rank and its exact adjacent gap

The existing fatal-gap route extracts a largest missing seam rank when a row
is fixed.  This module packages the corresponding invariant at an arbitrary
named rank `d`, computes the adjacent lower-to-upper finite weight gap in the
late range `2 * s < 3 * d`, and records its exact behavior under the concrete
`U`/`M`/`R` successor branches.

The gap theorem is stated without division:

`3 * lowerWeight + (3 * 2^(s+1) + 2 * 4^(s-d) + 4) = 3 * upperWeight`.

This is equivalent to the correction

`2^(s+1) + (2 * 4^(s-d) + 4) / 3`

because `d < s` makes `s-d` positive and the numerator divisible by three.
The module does not prove that the first row entering `3 * d > 2 * s` must
take a `U` or `M` branch; that is the remaining first-crossing producer.
-/

namespace Erdos249257

open HalfCylinderIntegerGreedy
open scoped BigOperators

/-! ## The rightmost-false invariant -/

/-- `d` is the largest false rank of a seam word: it is absent, and every
strictly larger rank still inside the row is present. -/
def IsLargestFalseRank {s : ℕ} (b : SeamRowWord s) (d : ℕ) : Prop :=
  2 ≤ d ∧ d < s ∧
    d ∉ seamWordSupport b ∧
      ∀ e : ℕ, d < e → e < s → e ∈ seamWordSupport b

/-- A named largest false rank is exactly a fixed lower prefix followed by
the completely filled suffix `d+1,...,s-1`.  This is the parameterized form
of `exists_maximal_missing_rank_support_decomposition`. -/
theorem isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
    {s d : ℕ} (b : SeamRowWord s) (hd2 : 2 ≤ d) (hds : d < s) :
    IsLargestFalseRank b d ↔
      ∃ u : Finset ℕ,
        (∀ e ∈ u, 2 ≤ e ∧ e < d) ∧
          seamWordSupport b = u ∪ Finset.Ico (d + 1) s := by
  classical
  constructor
  · rintro ⟨_hd2, _hds, hdnot, hfull⟩
    let u := (seamWordSupport b).filter (fun e => e < d)
    refine ⟨u, ?_, ?_⟩
    · intro e he
      have hedata := Finset.mem_filter.mp he
      exact ⟨(seamWordSupport_below hedata.1).1, hedata.2⟩
    · ext e
      constructor
      · intro hesupport
        by_cases hed : e < d
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr ⟨hesupport, hed⟩))
        · have hebounds := seamWordSupport_below hesupport
          have hene : e ≠ d := by
            intro heq
            subst e
            exact hdnot hesupport
          exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_Ico.mpr ⟨by omega, hebounds.2⟩))
      · intro heunion
        rcases Finset.mem_union.mp heunion with heu | heinterval
        · exact (Finset.mem_filter.mp heu).1
        · have hebounds := Finset.mem_Ico.mp heinterval
          exact hfull e (by omega) hebounds.2
  · rintro ⟨u, hu, hsupport⟩
    refine ⟨hd2, hds, ?_, ?_⟩
    · intro hdmem
      rw [hsupport] at hdmem
      rcases Finset.mem_union.mp hdmem with hdu | hdinterval
      · exact (Nat.lt_irrefl d) (hu d hdu).2
      · have := Finset.mem_Ico.mp hdinterval
        omega
    · intro e hde hes
      rw [hsupport]
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_Ico.mpr ⟨by omega, hes⟩))

/-- Appending `false` makes the new terminal rank the largest false rank. -/
theorem isLargestFalseRank_extend_false
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    IsLargestFalseRank (b.extend false) s := by
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [seamWordSupport_extend_false hs b]
    intro hsupp
    exact (Nat.lt_irrefl s) (seamWordSupport_below hsupp).2
  · intro e hse hes
    omega

/-- Appending `true` preserves every existing largest false rank. -/
theorem IsLargestFalseRank.extend_true
    {s d : ℕ} {b : SeamRowWord s} (hs : 3 ≤ s)
    (hmax : IsLargestFalseRank b d) :
    IsLargestFalseRank (b.extend true) d := by
  rcases hmax with ⟨hd2, hds, hdnot, hfull⟩
  refine ⟨hd2, by omega, ?_, ?_⟩
  · rw [seamWordSupport_extend_true hs b]
    simp [hdnot, ne_of_lt hds]
  · intro e hde hesucc
    rw [seamWordSupport_extend_true hs b]
    by_cases hes : e = s
    · subst e
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hfull e hde (by omega))

/-! ## Exact late-rank weight arithmetic -/

/-- In the late range `2*s < 3*d`, Euclidean division has quotient two, so
the truncated Mersenne weight has exactly two power terms. -/
theorem truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d < s)
    (hlate : 2 * s < 3 * d) :
    truncatedMersenneWeight s d =
      2 ^ (2 * s - d) + 4 ^ (s - d) := by
  rw [truncatedMersenneWeight_eq_geometricCore hd2]
  have hdiv : (2 * s) / d = 2 := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  have hrem : 2 * (s - d) < d := by
    omega
  have hmod : (2 * s) % d = 2 * (s - d) := by
    rw [show 2 * s = d * 2 + 2 * (s - d) by omega,
      Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrem]
  have hpow4 : 4 ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
  have hexponent : 2 * (s - d) + d = 2 * s - d := by
    omega
  rw [hdiv, hmod]
  calc
    2 ^ (2 * (s - d)) *
          ∑ i ∈ Finset.range 2, (2 ^ d) ^ i
        = 2 ^ (2 * (s - d)) * (1 + 2 ^ d) := by
            norm_num [Finset.sum_range_succ]
    _ = 2 ^ (2 * (s - d)) * 2 ^ d +
          2 ^ (2 * (s - d)) := by ring
    _ = 2 ^ (2 * (s - d) + d) +
          2 ^ (2 * (s - d)) := by rw [pow_add]
    _ = 2 ^ (2 * s - d) + 4 ^ (s - d) := by
          rw [hexponent, hpow4]

/-- The descending binary powers in the strict suffix telescope exactly. -/
theorem twoPowerSuffixSum_add_boundary
    (s d : ℕ) (hds : d < s) :
    (∑ e ∈ Finset.Ico (d + 1) s, 2 ^ (2 * s - e)) + 2 ^ (s + 1) =
      2 ^ (2 * s - d) := by
  by_cases hstep : d + 1 < s
  · rw [Finset.sum_eq_sum_Ico_succ_bot hstep]
    have ih := twoPowerSuffixSum_add_boundary s (d + 1) hstep
    have ih' :
        (∑ e ∈ Finset.Ico (d + 2) s, 2 ^ (2 * s - e)) + 2 ^ (s + 1) =
          2 ^ (2 * s - (d + 1)) := by
      simpa [Nat.add_assoc] using ih
    calc
      2 ^ (2 * s - (d + 1)) +
            (∑ e ∈ Finset.Ico (d + 2) s, 2 ^ (2 * s - e)) +
            2 ^ (s + 1)
          = 2 ^ (2 * s - (d + 1)) +
              ((∑ e ∈ Finset.Ico (d + 2) s, 2 ^ (2 * s - e)) +
                2 ^ (s + 1)) := by omega
      _ = 2 ^ (2 * s - (d + 1)) +
              2 ^ (2 * s - (d + 1)) := by rw [ih']
      _ = 2 ^ (2 * s - (d + 1)) * 2 := by ring
      _ = 2 ^ (2 * s - (d + 1) + 1) := by rw [pow_succ]
      _ = 2 ^ (2 * s - d) := by congr 1 <;> omega
  · have heq : d + 1 = s := by omega
    have hempty : Finset.Ico (d + 1) s = ∅ :=
      Finset.Ico_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty, zero_add]
    congr 1
    omega
termination_by s - d
decreasing_by omega

/-- The descending base-four correction powers telescope in a
division-free form. -/
theorem three_mul_fourPowerSuffixSum_add_four
    (s d : ℕ) (hds : d < s) :
    3 * (∑ e ∈ Finset.Ico (d + 1) s, 4 ^ (s - e)) + 4 =
      4 ^ (s - d) := by
  by_cases hstep : d + 1 < s
  · rw [Finset.sum_eq_sum_Ico_succ_bot hstep]
    have ih := three_mul_fourPowerSuffixSum_add_four s (d + 1) hstep
    calc
      3 * (4 ^ (s - (d + 1)) +
            ∑ e ∈ Finset.Ico (d + 2) s, 4 ^ (s - e)) + 4
          = 3 * 4 ^ (s - (d + 1)) +
              (3 * (∑ e ∈ Finset.Ico (d + 2) s, 4 ^ (s - e)) + 4) := by
                ring
      _ = 3 * 4 ^ (s - (d + 1)) + 4 ^ (s - (d + 1)) := by rw [ih]
      _ = 4 ^ (s - (d + 1)) * 4 := by ring
      _ = 4 ^ (s - (d + 1) + 1) := by rw [pow_succ]
      _ = 4 ^ (s - d) := by congr 1 <;> omega
  · have heq : d + 1 = s := by omega
    have hempty : Finset.Ico (d + 1) s = ∅ :=
      Finset.Ico_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty, mul_zero, zero_add]
    rw [show s - d = 1 by omega]
    norm_num
termination_by s - d
decreasing_by omega

/-- Every strict-suffix weight is in the same two-term quotient-two range. -/
theorem seamWeightsFrom_sum_eq_twoPowerSuffix_add_fourPowerSuffix_of_lateRank
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d < s)
    (hlate : 2 * s < 3 * d) :
    (seamWeightsFrom s (d + 1)).sum =
      (∑ e ∈ Finset.Ico (d + 1) s, 2 ^ (2 * s - e)) +
        ∑ e ∈ Finset.Ico (d + 1) s, 4 ^ (s - e) := by
  rw [← sum_truncatedMersenneWeight_Ico_eq_seamWeightsFrom_sum
    s (d + 1) (by omega)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hebounds := Finset.mem_Ico.mp he
  have he2 : 2 ≤ e := le_trans hd2 (by omega)
  exact truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank
    he2 hebounds.2 (by nlinarith)

/-- Sharp division-free adjacent-gap identity.  Dividing by three gives
`2^(s+1) + (2*4^(s-d)+4)/3`. -/
theorem three_mul_tailWeight_add_exactLateGap_eq_three_mul_headWeight
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d < s)
    (hlate : 2 * s < 3 * d) :
    3 * (seamWeightsFrom s (d + 1)).sum +
        (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4) =
      3 * truncatedMersenneWeight s d := by
  have hhead :=
    truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank
      hd2 hds hlate
  have htail :=
    seamWeightsFrom_sum_eq_twoPowerSuffix_add_fourPowerSuffix_of_lateRank
      hd2 hds hlate
  have htwo := twoPowerSuffixSum_add_boundary s d hds
  have hfour := three_mul_fourPowerSuffixSum_add_four s d hds
  rw [hhead, htail]
  omega

/-! ## Concrete adjacent words and branch propagation -/

/-- The lower adjacent word at largest skipped rank `d`. -/
def largestSkipLowerWord (s d : ℕ) (u : Finset ℕ) : SeamRowWord s :=
  seamRowWordOfFinset s (u ∪ Finset.Ico (d + 1) s)

/-- The upper adjacent word replaces the filled suffix by the skipped rank. -/
def largestSkipUpperWord (s d : ℕ) (u : Finset ℕ) : SeamRowWord s :=
  seamRowWordOfFinset s (insert d u)

/-- Exact late-rank adjacent word gap, including an arbitrary common lower
prefix. -/
theorem three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight
    {s d : ℕ} {u : Finset ℕ}
    (hd2 : 2 ≤ d) (hds : d < s)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d)
    (hlate : 2 * s < 3 * d) :
    3 * wordWeightSum s (largestSkipLowerWord s d u).toNatWord +
        (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4) =
      3 * wordWeightSum s (largestSkipUpperWord s d u).toNatWord := by
  classical
  have hdnotu : d ∉ u := by
    intro hdu
    exact (Nat.lt_irrefl d) (hu d hdu).2
  have hdisjoint : Disjoint u (Finset.Ico (d + 1) s) := by
    apply Finset.disjoint_left.mpr
    intro e heu heinterval
    have heu' := hu e heu
    have heinterval' := Finset.mem_Ico.mp heinterval
    omega
  have hlowerBounds :
      ∀ e ∈ u ∪ Finset.Ico (d + 1) s, 2 ≤ e ∧ e < s := by
    intro e he
    rcases Finset.mem_union.mp he with heu | heinterval
    · have hebounds := hu e heu
      exact ⟨hebounds.1, by omega⟩
    · have hebounds := Finset.mem_Ico.mp heinterval
      exact ⟨by omega, hebounds.2⟩
  have hupperBounds : ∀ e ∈ insert d u, 2 ≤ e ∧ e < s := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · exact ⟨hd2, hds⟩
    · have hebounds := hu e heu
      exact ⟨hebounds.1, by omega⟩
  have hgap := three_mul_tailWeight_add_exactLateGap_eq_three_mul_headWeight
    hd2 hds hlate
  unfold largestSkipLowerWord largestSkipUpperWord
  rw [wordWeightSum_eq_sum_seamWordSupport,
    wordWeightSum_eq_sum_seamWordSupport,
    seamWordSupport_seamRowWordOfFinset hlowerBounds,
    seamWordSupport_seamRowWordOfFinset hupperBounds,
    Finset.sum_union hdisjoint, Finset.sum_insert hdnotu,
    sum_truncatedMersenneWeight_Ico_eq_seamWeightsFrom_sum
      s (d + 1) (by omega)]
  omega

/-- On the `U` branch, the new terminal rank is the largest false rank. -/
theorem seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperBranch
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    IsLargestFalseRank (seamGreedyWord (s + 1)) s := by
  rw [seamGreedyWord_succ_eq_upperBranch s hs hcarry]
  exact isLargestFalseRank_extend_false (by omega)
    (seamAdjacentCut s hs).above

/-- On the `M` branch, the new terminal rank is the largest false rank. -/
theorem seamGreedyWord_succ_isLargestFalseRank_terminal_of_middleBranch
    (s : ℕ) (hs : 5 ≤ s)
    (hcarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
          (seamPerturbedFamily s (by omega)).gap -
          (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight) :
    IsLargestFalseRank (seamGreedyWord (s + 1)) s := by
  rw [seamGreedyWord_succ_eq_middleBranch s hs hcarry hmiddle]
  exact isLargestFalseRank_extend_false (by omega)
    (seamAdjacentCut s hs).below

/-- The combined arithmetic `U/M` predicate makes the successor terminal
rank the largest false rank. -/
theorem seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle
    (s : ℕ) (hs : 5 ≤ s)
    (hUM : SeamGreedyUpperOrMiddleAt s hs) :
    IsLargestFalseRank (seamGreedyWord (s + 1)) s := by
  rcases hUM with hcarry | ⟨hcarry, hmiddle⟩
  · exact seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperBranch
      s hs hcarry
  · exact seamGreedyWord_succ_isLargestFalseRank_terminal_of_middleBranch
      s hs hcarry hmiddle

/-- On the `R` branch, the old largest false rank is preserved. -/
theorem IsLargestFalseRank.seamGreedyWord_succ_of_rightBranch
    {s d : ℕ} (hs : 5 ≤ s)
    (hmax : IsLargestFalseRank (seamGreedyWord s) d)
    (hcarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hright : (seamAdjacentCut s hs).terminalWeight ≤
      4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse) :
    IsLargestFalseRank (seamGreedyWord (s + 1)) d := by
  rw [seamGreedyWord_succ_eq_rightBranch s hs hcarry hright]
  change IsLargestFalseRank ((seamGreedyWord s).extend true) d
  exact hmax.extend_true (by omega)

#print axioms isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
#print axioms isLargestFalseRank_extend_false
#print axioms IsLargestFalseRank.extend_true
#print axioms truncatedMersenneWeight_eq_twoPower_add_fourPower_of_lateRank
#print axioms twoPowerSuffixSum_add_boundary
#print axioms three_mul_fourPowerSuffixSum_add_four
#print axioms seamWeightsFrom_sum_eq_twoPowerSuffix_add_fourPowerSuffix_of_lateRank
#print axioms three_mul_tailWeight_add_exactLateGap_eq_three_mul_headWeight
#print axioms three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight
#print axioms seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperBranch
#print axioms seamGreedyWord_succ_isLargestFalseRank_terminal_of_middleBranch
#print axioms seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperOrMiddle
#print axioms IsLargestFalseRank.seamGreedyWord_succ_of_rightBranch

end Erdos249257
