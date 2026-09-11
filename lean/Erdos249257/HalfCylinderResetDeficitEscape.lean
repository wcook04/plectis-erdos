import Erdos249257.HalfCylinderLargestSkipGap

/-!
# Reset-deficit escape geometry for the largest-skip crossing

The remaining `#257` half-membership producer is
`LargestSkipLateStepSocket`: a late largest false rank cannot cross the
two-thirds boundary on a right branch.  This module pins the exact
arithmetic window that a right branch forces on the greedy remainder, and
proves the deficit-side run-length law observed numerically (rows
`14..1500`, `714` resets, slack `0`).

Unconditional content:

* `upperOrMiddle_of_four_mul_remainder_lt` — the `M` trigger: a remainder
  below a quarter of the doubled gap forces an upper-or-middle successor.
* `three_mul_remainder_lt_exactLateGap` — the strip invariant: at a late
  largest false rank the greedy remainder is strictly below the exact
  adjacent-word gap `2^(s+1) + (2*4^(s-d)+4)/3` (division-free form).
* `successorCarries_of_twelve_mul_remainder_ge` — the `U` trigger: once
  twelve times the remainder reaches the explicit carry threshold, the
  successor carries.
* `rightBranch_remainder_window` — the two triggers combined: a right
  branch at a late row pins the remainder into one explicit interval.
  At the boundary cells `3*d ∈ {2*s+1, 2*s+2}` this interval is exactly
  the open middle-cell condition; its emptiness for the actual greedy
  orbit is equivalent to the socket and remains the open input.
* `rightBranch_remainder_succ_eq` — the exact right-branch remainder
  recurrence `rem(s+1) = 4*rem(s) - 2^(s+1) - pulse - 4`.
* `upperOrMiddle_within_of_two_pow_deficit` — the deficit-side run law:
  if `2^k * (2^s - rem(s)) ≥ 2^s` then an upper-or-middle branch occurs
  within `k` rows.  Contrapositive: an all-right run of length `k` forces
  the remainder within `2^(s-k)` of the half-point `2^s`.

The module proves no new unconditional case of the socket itself: the
open core is that the deterministic remainder sequence avoids the pinned
window, i.e. quantitative anti-concentration of `rem(s)` around `2^s`.
-/

namespace Erdos249257

open HalfCylinderIntegerGreedy

noncomputable section

noncomputable local instance
    {α : Type*} {F : PerturbedFamily α} {C : ℕ}
    (K : F.AdjacentCut C) : Decidable K.successorCarries :=
  Classical.propDecidable _

/-! ## Elementary cut facts -/

theorem seamAdjacentCut_gap_eq {s : ℕ} (hs : 3 ≤ s) :
    (seamPerturbedFamily s hs).gap = 2 ^ (s + 1) := rfl

theorem seamAdjacentCut_terminalWeight_eq {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).terminalWeight = 2 * 2 ^ (s + 1) + 4 := rfl

theorem seamAdjacentCut_belowPulse_le {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) :=
  (seamPerturbedFamily s (by omega)).pulse_le _

theorem seamAdjacentCut_abovePulse_le {s : ℕ} (hs : 5 ≤ s) :
    (seamAdjacentCut s hs).abovePulse ≤ 2 * (s - 2) :=
  (seamPerturbedFamily s (by omega)).pulse_le _

/-- The greedy word weight and the greedy remainder split the target. -/
theorem seamGreedy_weight_add_remainder {s : ℕ} (hs : 5 ≤ s) :
    wordWeightSum s (seamGreedyWord s).toNatWord +
        seamIntegerGreedyRemainder s = seamSubsetTarget s := by
  have h := (seamAdjacentCut s hs).old_below_add_remainder
  rw [seamAdjacentCut_remainder hs] at h
  exact h

/-! ## The `M` trigger -/

/-- A remainder strictly below a quarter of the doubled gap forces an
upper-or-middle successor: the new terminal weight cannot be paid. -/
theorem upperOrMiddle_of_four_mul_remainder_lt
    {s : ℕ} (hs : 5 ≤ s)
    (hsmall : 4 * seamIntegerGreedyRemainder s < 2 ^ (s + 1) + 4) :
    SeamGreedyUpperOrMiddleAt s hs := by
  by_cases hcarry : (seamAdjacentCut s hs).successorCarries
  · exact Or.inl hcarry
  · refine Or.inr ⟨hcarry, ?_⟩
    have hrem := seamAdjacentCut_remainder hs
    have hterm := seamAdjacentCut_terminalWeight_eq hs
    have hgap : (seamPerturbedFamily s (by omega)).gap = 2 ^ (s + 1) := rfl
    rw [hrem, hterm, hgap]
    omega

/-! ## The strip invariant -/

/-- The greedy word has the same weight as the lower adjacent word carried
by its largest-false-rank decomposition. -/
theorem seamGreedy_weight_eq_largestSkipLowerWord
    {s d : ℕ} {u : Finset ℕ}
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d) (hd2 : 2 ≤ d) (hds : d < s)
    (hsupp : seamWordSupport (seamGreedyWord s) =
      u ∪ Finset.Ico (d + 1) s) :
    wordWeightSum s (largestSkipLowerWord s d u).toNatWord =
      wordWeightSum s (seamGreedyWord s).toNatWord := by
  classical
  have hbounds : ∀ e ∈ u ∪ Finset.Ico (d + 1) s, 2 ≤ e ∧ e < s := by
    intro e he
    rcases Finset.mem_union.mp he with heu | hei
    · exact ⟨(hu e heu).1, by have := (hu e heu).2; omega⟩
    · have := Finset.mem_Ico.mp hei
      omega
  rw [wordWeightSum_eq_sum_seamWordSupport,
    wordWeightSum_eq_sum_seamWordSupport]
  unfold largestSkipLowerWord
  rw [seamWordSupport_seamRowWordOfFinset hbounds, hsupp]

/-- Strip invariant: at a late largest false rank the greedy remainder is
strictly below the exact adjacent gap (division-free three-fold form). -/
theorem three_mul_remainder_lt_exactLateGap
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    3 * seamIntegerGreedyRemainder s <
      3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 := by
  classical
  have hd2 : 2 ≤ d := hd.1
  have hds : d < s := hd.2.1
  obtain ⟨u, hu, hsupp⟩ :=
    (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
      (seamGreedyWord s) hd2 hds).mp hd
  have hlow := seamGreedy_weight_eq_largestSkipLowerWord hu hd2 hds hsupp
  have hgapId :=
    three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight
      hd2 hds hu hlate
  have hsplit := seamGreedy_weight_add_remainder hs
  by_contra hbig
  push_neg at hbig
  -- the upper adjacent word would be admissible, beating greedy maximality
  have hupperLe :
      wordWeightSum s (largestSkipUpperWord s d u).toNatWord ≤
        seamSubsetTarget s := by omega
  have hmax := (seamAdjacentCut s hs).below_maximal
    (largestSkipUpperWord s d u) hupperLe
  change wordWeightSum s (largestSkipUpperWord s d u).toNatWord ≤
      wordWeightSum s (seamGreedyWord s).toNatWord at hmax
  omega

/-! ## The `U` trigger -/

/-- Carry threshold: once twelve times the remainder reaches the explicit
gap-and-pulse budget, the successor carries into the upper word. -/
theorem successorCarries_of_twelve_mul_remainder_ge
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hbig : 4 * (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4) +
        3 * (2 * (s - 2)) ≤
      12 * seamIntegerGreedyRemainder s + 3 * 2 ^ (s + 1)) :
    (seamAdjacentCut s hs).successorCarries := by
  classical
  have hd2 : 2 ≤ d := hd.1
  have hds : d < s := hd.2.1
  obtain ⟨u, hu, hsupp⟩ :=
    (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
      (seamGreedyWord s) hd2 hds).mp hd
  have hlow := seamGreedy_weight_eq_largestSkipLowerWord hu hd2 hds hsupp
  have hgapId :=
    three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight
      hd2 hds hu hlate
  have hsplit := seamGreedy_weight_add_remainder hs
  have hstrip := three_mul_remainder_lt_exactLateGap hs hd hlate
  -- the upper adjacent word lies strictly above the target
  have hupperStrict :
      seamSubsetTarget s <
        wordWeightSum s (largestSkipUpperWord s d u).toNatWord := by
    omega
  have hmin := (seamAdjacentCut s hs).above_minimal
    (largestSkipUpperWord s d u) hupperStrict
  change (seamPerturbedFamily s (by omega)).oldSum
      (seamAdjacentCut s hs).above ≤
    wordWeightSum s (largestSkipUpperWord s d u).toNatWord at hmin
  have hap := seamAdjacentCut_abovePulse_le hs
  show 4 * (seamAdjacentCut s hs).overshoot +
      (seamAdjacentCut s hs).abovePulse ≤
    (seamPerturbedFamily s (by omega)).gap
  have hgap : (seamPerturbedFamily s (by omega)).gap = 2 ^ (s + 1) := rfl
  rw [hgap]
  -- capacity + overshoot = above ≤ upper word; upper word pinned by identity
  have hcap' : seamSubsetTarget s + (seamAdjacentCut s hs).overshoot =
      (seamPerturbedFamily s (by omega)).oldSum
        (seamAdjacentCut s hs).above := by
    have := (seamAdjacentCut s hs).capacity_add_overshoot
    exact this
  omega

/-! ## Right-branch window and exact recurrence -/

/-- A right branch at a late row pins the greedy remainder into one
explicit interval: above the quarter point, and strictly below the carry
threshold.  At the boundary cells `3*d ∈ {2*s+1, 2*s+2}` the emptiness of
this interval for the actual orbit is exactly the remaining socket. -/
theorem rightBranch_remainder_window
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hR : ¬ SeamGreedyUpperOrMiddleAt s hs) :
    2 ^ (s + 1) + 4 ≤ 4 * seamIntegerGreedyRemainder s ∧
      12 * seamIntegerGreedyRemainder s + 3 * 2 ^ (s + 1) <
        4 * (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4) + 3 * (2 * (s - 2)) := by
  constructor
  · by_contra hsmall
    push_neg at hsmall
    exact hR (upperOrMiddle_of_four_mul_remainder_lt hs (by omega))
  · by_contra hbig
    push_neg at hbig
    exact hR (Or.inl
      (successorCarries_of_twelve_mul_remainder_ge hs hd hlate hbig))

/-- Exact right-branch remainder recurrence. -/
theorem rightBranch_remainder_succ_eq
    {s : ℕ} (hs : 5 ≤ s)
    (hR : ¬ SeamGreedyUpperOrMiddleAt s hs) :
    seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) +
        (seamAdjacentCut s hs).belowPulse + 4 =
      4 * seamIntegerGreedyRemainder s := by
  classical
  have hcarry : ¬ (seamAdjacentCut s hs).successorCarries := by
    intro h
    exact hR (Or.inl h)
  have hmiddle : ¬ (4 * (seamAdjacentCut s hs).remainder +
      (seamPerturbedFamily s (by omega)).gap -
      (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight) := by
    intro h
    exact hR (Or.inr ⟨hcarry, h⟩)
  have htri := (seamAdjacentCut s hs).nextRemainder_trichotomy
  rw [if_neg hcarry, if_neg hmiddle] at htri
  have hnext := seamAdjacentCut_nextRemainder hs
  have hrem := seamAdjacentCut_remainder hs
  have hgap : (seamPerturbedFamily s (by omega)).gap = 2 ^ (s + 1) := rfl
  have hterm := seamAdjacentCut_terminalWeight_eq hs
  have hbp : (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) :=
    seamAdjacentCut_belowPulse_le hs
  have hpc : 2 * (s - 2) < 2 ^ (s + 1) := by
    have := two_mul_add_four_lt_two_pow_succ (show 3 ≤ s by omega)
    omega
  -- the right branch also certifies the terminal payment inequality
  have hpay : (seamAdjacentCut s hs).terminalWeight ≤
      4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse := Nat.le_of_not_gt hmiddle
  rw [hrem, hgap, hterm] at hpay hmiddle
  rw [← hnext, htri, hrem, hgap]
  omega

/-! ## The deficit-side run law -/

/-- Deficit-side run law: once the doubled-scale deficit
`2^s - rem(s)` reaches `2^(s-k)` (stated multiplicatively to avoid
truncated subtraction in the exponent), an upper-or-middle branch fires
within `k` rows.  Contrapositive: an all-right run of length `k` from row
`s` forces `rem(s)` within `2^(s-k)` of the half-point `2^s`. -/
theorem upperOrMiddle_within_of_two_pow_deficit :
    ∀ k s : ℕ, 5 ≤ s →
      seamIntegerGreedyRemainder s ≤ 2 ^ s →
      2 ^ s ≤ 2 ^ k * (2 ^ s - seamIntegerGreedyRemainder s) →
      ∃ t : ℕ, s ≤ t ∧ t ≤ s + k ∧ ∃ h : 5 ≤ t,
        SeamGreedyUpperOrMiddleAt t h := by
  intro k
  induction k with
  | zero =>
      intro s hs hle hdef
      refine ⟨s, le_refl s, by omega, hs, ?_⟩
      apply upperOrMiddle_of_four_mul_remainder_lt hs
      simp only [pow_zero, one_mul] at hdef
      have : seamIntegerGreedyRemainder s = 0 := by omega
      omega
  | succ k ih =>
      intro s hs hle hdef
      by_cases hUM : SeamGreedyUpperOrMiddleAt s hs
      · exact ⟨s, le_refl s, by omega, hs, hUM⟩
      · have hrec := rightBranch_remainder_succ_eq hs hUM
        have hbp : (seamAdjacentCut s hs).belowPulse ≤
            2 * (s - 2) := seamAdjacentCut_belowPulse_le hs
        have hpow : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by
          rw [pow_succ]; ring
        -- the successor stays on the deficit side, with deficit at least
        -- quadrupled
        have hleNext : seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) := by
          omega
        have hgrow : 4 * (2 ^ s - seamIntegerGreedyRemainder s) ≤
            2 ^ (s + 1) - seamIntegerGreedyRemainder (s + 1) := by
          omega
        have hdefNext : 2 ^ (s + 1) ≤
            2 ^ k * (2 ^ (s + 1) - seamIntegerGreedyRemainder (s + 1)) := by
          have hmono : 2 ^ k * (4 * (2 ^ s - seamIntegerGreedyRemainder s)) ≤
              2 ^ k * (2 ^ (s + 1) - seamIntegerGreedyRemainder (s + 1)) :=
            Nat.mul_le_mul_left _ hgrow
          calc 2 ^ (s + 1) = 2 * 2 ^ s := hpow
            _ ≤ 2 * (2 ^ (k + 1) *
                (2 ^ s - seamIntegerGreedyRemainder s)) := by omega
            _ = 2 ^ k * (4 * (2 ^ s - seamIntegerGreedyRemainder s)) := by
                rw [pow_succ]; ring
            _ ≤ _ := hmono
        obtain ⟨t, hst, htk, ht5, hUMt⟩ := ih (s + 1) (by omega) hleNext hdefNext
        exact ⟨t, by omega, by omega, ht5, hUMt⟩

#print axioms upperOrMiddle_of_four_mul_remainder_lt
#print axioms three_mul_remainder_lt_exactLateGap
#print axioms successorCarries_of_twelve_mul_remainder_ge
#print axioms rightBranch_remainder_window
#print axioms rightBranch_remainder_succ_eq
#print axioms upperOrMiddle_within_of_two_pow_deficit

end

end Erdos249257
