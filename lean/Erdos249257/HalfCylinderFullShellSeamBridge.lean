import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.HalfCylinderConcreteSeamAdapter

/-!
# Full-shell frozen-margin / integer-seam bridge for Erdős #257

The bridge exposes exact sufficient conditions for half-membership and the
rigidity forced by any hypothetical negative-margin skip.  It does not claim
an unconditional decision of Erdős #257.
-/

namespace Erdos249257

open Set Filter
open HalfCarryReachability
open HalfCylinderFiniteShadow
open HalfCylinderIntegerGreedy
open scoped BigOperators

/-- A shifted natural square root grows much more slowly than the shift.
This form is tuned to the binary tail sum. -/
theorem sqrt_shift_le_sqrt_add_one_add_div (N j : ℕ) :
    Nat.sqrt (N + j + 1) ≤
      Nat.sqrt N + 1 + j / (Nat.sqrt N + 1) := by
  let q := Nat.sqrt N
  let t := j / (q + 1)
  have hN : N < (q + 1) * (q + 1) := by
    simpa [q] using Nat.lt_succ_sqrt N
  have hj : j < (q + 1) * (t + 1) := by
    dsimp [t]
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ j (by omega : 0 < q + 1))
  have hsq : N + j + 1 < (q + t + 2) * (q + t + 2) := by
    nlinarith
  have hsqrt : Nat.sqrt (N + j + 1) < q + t + 2 :=
    (Nat.sqrt_lt).2 hsq
  dsimp [q, t] at hsqrt ⊢
  omega

/-- A one-unit sharpening of the generic support-coefficient tail strip.
The gain comes from summing the slow square-root growth in blocks of length
`sqrt N + 1`, rather than bounding that growth by the row shift itself. -/
theorem binaryCoeffTail_supportCoeff_lt_two_natSqrt_add_three
    (A : Set ℕ) (N : ℕ) (hN : 4 ≤ N) :
    binaryCoeffTail (supportCoeff A) N <
      2 * (Nat.sqrt N : ℝ) + 3 := by
  let q := Nat.sqrt N
  let C : ℕ := (q + 1) ^ 2
  let g : ℕ → ℝ := fun j ↦
    (1 / (q + 1 : ℝ)) * ((C : ℝ) + (j : ℝ)) *
      ((1 : ℝ) / 2) ^ j
  have hq : 0 < (q + 1 : ℝ) := by positivity
  have hsum : Summable (fun j : ℕ ↦
      (supportCoeff A (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)) :=
    summable_coeff_shift_tail 2 N (supportCoeff A)
      (by norm_num) (supportCoeff_le_self A)
  have hcmp : Summable g := by
    have hbase := summable_const_add_mul_geometric C
      (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    have hscaled := hbase.mul_left (1 / (q + 1 : ℝ))
    exact hscaled.congr (fun j ↦ by simp only [g]; ring)
  have hterm : ∀ j : ℕ,
      (supportCoeff A (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) ≤ g j := by
    intro j
    have hsqrt := sqrt_shift_le_sqrt_add_one_add_div N j
    have hcoeffNat :
        supportCoeff A (N + j + 1) ≤
          2 * (q + 1 + j / (q + 1)) := by
      apply (supportCoeff_le_two_mul_sqrt A (N + j + 1)).trans
      dsimp [q]
      exact Nat.mul_le_mul_left 2 hsqrt
    have hcoeff :
        (supportCoeff A (N + j + 1) : ℝ) ≤
          2 * ((q + 1 + j / (q + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcoeffNat
    have hfloorMul :
        ((j / (q + 1) : ℕ) : ℝ) * (q + 1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self j (q + 1)
    have hratio :
        ((q + 1 + j / (q + 1) : ℕ) : ℝ) ≤
          ((C : ℝ) + (j : ℝ)) / (q + 1 : ℝ) := by
      dsimp [C]
      push_cast
      rw [pow_two]
      apply (le_div_iff₀ hq).2
      nlinarith [hfloorMul]
    calc
      (supportCoeff A (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
          ≤ (2 * ((q + 1 + j / (q + 1) : ℕ) : ℝ)) /
              (2 : ℝ) ^ (j + 1) := by gcongr
      _ ≤ (2 * (((C : ℝ) + (j : ℝ)) / (q + 1 : ℝ))) /
              (2 : ℝ) ^ (j + 1) := by gcongr
      _ = g j := by
        simp only [g, pow_succ, div_pow, one_pow]
        field_simp
  have htail : binaryCoeffTail (supportCoeff A) N ≤ ∑' j : ℕ, g j := by
    unfold binaryCoeffTail
    exact Summable.tsum_le_tsum hterm hsum hcmp
  have hbaseBound := tsum_const_add_mul_geometric_le C
    (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  have hgBound : (∑' j : ℕ, g j) ≤
      (1 / (q + 1 : ℝ)) * (2 * (C : ℝ) + 2) := by
    have htsum : (∑' j : ℕ, g j) =
        (1 / (q + 1 : ℝ)) *
          ∑' j : ℕ, ((C : ℝ) + (j : ℝ)) * ((1 : ℝ) / 2) ^ j := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun j ↦ by simp only [g]; ring)
    rw [htsum]
    exact mul_le_mul_of_nonneg_left hbaseBound (by positivity)
  have hqNat : 2 ≤ q := by
    dsimp [q]
    rw [Nat.le_sqrt]
    omega
  have hfinal :
      (1 / (q + 1 : ℝ)) * (2 * (C : ℝ) + 2) <
        2 * (q : ℝ) + 3 := by
    dsimp [C]
    push_cast
    rw [pow_two]
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hqNat
    field_simp
    nlinarith
  exact htail.trans_lt (hgBound.trans_lt hfinal)

/-- Closed weighted-sum form of the recursive finite-window numerator. -/
theorem finiteCoeffWindowNumerator_eq_weighted_sum
    (A : Set ℕ) (n J : ℕ) :
    finiteCoeffWindowNumerator A n J =
      ∑ j ∈ Finset.range J,
        2 ^ (J - 1 - j) * supportCoeff A (n + j + 1) := by
  induction J with
  | zero => simp [finiteCoeffWindowNumerator]
  | succ J ih =>
      rw [finiteCoeffWindowNumerator, ih, Finset.sum_range_succ]
      have hscale :
          2 * (∑ j ∈ Finset.range J,
              2 ^ (J - 1 - j) * supportCoeff A (n + j + 1)) =
            ∑ j ∈ Finset.range J,
              2 ^ (J - j) * supportCoeff A (n + j + 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjJ : j < J := Finset.mem_range.mp hj
        rw [show J - j = (J - 1 - j) + 1 by omega, pow_succ]
        ring
      rw [hscale]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]

/-- At the full first shell `J=n`, the frozen margin is exactly the signed
integer-seam subset-sum defect. -/
theorem frozenMargin_fullShell_eq_stemTruncatedSum_sub_target
    (P : Finset ℕ) (n : ℕ) (hn : 2 ≤ n)
    (hbelow : ∀ d ∈ P, 2 ≤ d ∧ d < n) :
    (finiteCoeffWindowNumerator (↑P : Set ℕ) n n : ℤ) -
        (2 : ℤ) ^ n * mobiusCenteredHalfCarry (↑P : Set ℕ) (n - 1) =
      (stemTruncatedSum n P : ℤ) - (seamSubsetTarget n : ℤ) := by
  let A : Set ℕ := ↑P
  let preSum : ℤ :=
    ∑ j ∈ Finset.range (n - 1),
      (2 : ℤ) ^ (n - 2 - j) * (supportCoeff A (j + 2) : ℤ)
  let futureSum : ℤ :=
    ∑ j ∈ Finset.range n,
      (2 : ℤ) ^ (n - 1 - j) * (supportCoeff A (n + j + 1) : ℤ)
  have hnumNat := finiteCoeffWindowNumerator_eq_weighted_sum A n n
  have hnum : (finiteCoeffWindowNumerator A n n : ℤ) = futureSum := by
    dsimp [futureSum]
    exact_mod_cast hnumNat
  have hcarry := integerHalfCarry_eq_pow_sub_sum A (n - 1)
  have hnsub : n - 1 - 1 = n - 2 := by omega
  rw [hnsub] at hcarry
  change integerHalfCarry A (n - 1) = (2 : ℤ) ^ (n - 1) - preSum at hcarry
  have hswap := stemIncidenceSwap (s := n) (P := P) hbelow
  have hfull :
      (stemTruncatedSum n P : ℤ) = (2 : ℤ) ^ n * preSum + futureSum := by
    change
      (∑ j ∈ Finset.range (2 * n - 1),
          (2 : ℤ) ^ (2 * n - 2 - j) *
            (supportCoeff A (j + 2) : ℤ)) =
        (stemTruncatedSum n P : ℤ) at hswap
    have hlen : 2 * n - 1 = (n - 1) + n := by omega
    rw [hlen, Finset.sum_range_add] at hswap
    have hprefix :
        (∑ j ∈ Finset.range (n - 1),
            (2 : ℤ) ^ (2 * n - 2 - j) *
              (supportCoeff A (j + 2) : ℤ)) =
          (2 : ℤ) ^ n * preSum := by
      dsimp [preSum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n - 1 := Finset.mem_range.mp hj
      rw [show 2 * n - 2 - j = n + (n - 2 - j) by omega, pow_add]
      ring
    have hfuture :
        (∑ j ∈ Finset.range n,
            (2 : ℤ) ^ (2 * n - 2 - (n - 1 + j)) *
              (supportCoeff A (n - 1 + j + 2) : ℤ)) = futureSum := by
      dsimp [futureSum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      congr 1
      · congr 1 <;> omega
      · congr 2 <;> omega
    rw [hprefix, hfuture] at hswap
    exact hswap.symm
  have htarget :
      (seamSubsetTarget n : ℤ) =
        (2 : ℤ) ^ (2 * n - 1) - (2 : ℤ) ^ n := by
    have hpowle : 2 ^ n ≤ 2 ^ (2 * n - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold seamSubsetTarget
    rw [Nat.cast_sub hpowle]
    norm_num
  rw [hnum, mobiusCenteredHalfCarry, hcarry, htarget, hfull]
  rw [show (2 : ℤ) ^ (2 * n - 1) =
      (2 : ℤ) ^ n * (2 : ℤ) ^ (n - 1) by
    rw [← pow_add]
    congr 1 <;> omega]
  ring

/-- The rational greedy prefix before rank `n` is supported exactly on the
proper exponent range needed by the seam machinery. -/
theorem halfGreedyPrefixSupport_pred_below
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ d ∈ halfGreedyPrefixSupport (n - 1), 2 ≤ d ∧ d < n := by
  intro d hd
  have hd' := hd
  unfold halfGreedyPrefixSupport greedyMersennePrefixRat at hd
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
  have hjlt : j < n - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hne : j + 1 ≠ 1 := by
    intro heq
    have hone := one_not_mem_halfGreedyPrefixSupport (n - 1)
    apply hone
    simpa [heq] using hd'
  omega

/-- Concrete greedy specialization of the full-shell integer identity. -/
theorem greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target
    (n : ℕ) (hn : 2 ≤ n) :
    greedyHalfFrozenMargin (n - 1) n =
      (stemTruncatedSum n (halfGreedyPrefixSupport (n - 1)) : ℤ) -
        (seamSubsetTarget n : ℤ) := by
  have h := frozenMargin_fullShell_eq_stemTruncatedSum_sub_target
    (halfGreedyPrefixSupport (n - 1)) n hn
    (halfGreedyPrefixSupport_pred_below n hn)
  simpa [greedyHalfFrozenMargin, Nat.sub_add_cancel (by omega : 1 ≤ n)] using h

/-- Analytic form of the same full-shell margin: amplified dyadic safety
slack minus the coefficient tail still pending after row `2(k+1)`. -/
theorem greedyHalfFrozenMargin_fullShell_cast_eq_slack_sub_tail
    (k : ℕ) :
    (greedyHalfFrozenMargin k (k + 1) : ℝ) =
      (2 : ℝ) ^ (k + 1) *
          (1 - (2 : ℝ) ^ (k + 1) *
            greedyMersenneRemainder (1 / 2 : ℝ) k) -
        binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ))
          ((k + 1) + (k + 1)) := by
  let P : Set ℕ := ↑(halfGreedyPrefixSupport k)
  let C : ℤ := mobiusCenteredHalfCarry P k
  let T : ℝ := binaryCoeffTail (supportCoeff P) (k + 1)
  let U : ℝ := binaryCoeffTail (supportCoeff P) ((k + 1) + (k + 1))
  have hmargin :=
    greedyHalfFrozenMargin_cast_eq_pow_mul_window_sub_carry k (k + 1)
  have hsplit :=
    binaryCoeffTail_eq_finiteCoeffWindow_add_shiftedTail P (k + 1) (k + 1)
  have hrem := greedyHalfRemainder_eq_integerCarry_sub_coeffTail_div_pow k
  have hcarry : halfGreedyPrefixIntegerCarry k = C + 1 := by
    dsimp [halfGreedyPrefixIntegerCarry, C, P, mobiusCenteredHalfCarry,
      integerHalfCarry]
    ring
  have htail : halfGreedyPrefixCoeffTail k = T := by
    rfl
  rw [hcarry, htail] at hrem
  change
    greedyMersenneRemainder (1 / 2 : ℝ) k =
      (((C + 1 : ℤ) : ℝ) - T) / (2 : ℝ) ^ (k + 1) at hrem
  change
    T = finiteCoeffWindow P (k + 1) (k + 1) +
      U / (2 : ℝ) ^ (k + 1) at hsplit
  change
    (greedyHalfFrozenMargin k (k + 1) : ℝ) =
      (2 : ℝ) ^ (k + 1) *
        (finiteCoeffWindow P (k + 1) (k + 1) - (C : ℝ)) at hmargin
  change
    (greedyHalfFrozenMargin k (k + 1) : ℝ) =
      (2 : ℝ) ^ (k + 1) *
          (1 - (2 : ℝ) ^ (k + 1) *
            greedyMersenneRemainder (1 / 2 : ℝ) k) - U
  have hpow : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  rw [hmargin, hrem, hsplit]
  field_simp
  push_cast
  ring

/-- A skipped rank can exceed its dyadic boundary by less than two after the
full-shell amplification.  This is the only use of the skip inequality in
the seam adapter. -/
theorem greedyHalf_skip_amplified_dyadic_overshoot_lt_two
    (n : ℕ) (hn : 2 ≤ n)
    (hskip : ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) :
    (2 : ℝ) ^ n *
        ((2 : ℝ) ^ n *
          greedyMersenneRemainder (1 / 2 : ℝ) (n - 1) - 1) < 2 := by
  let a : ℝ := (2 : ℝ) ^ n
  let r : ℝ := greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)
  have haNat : 2 ^ 2 ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hn
  have ha : (4 : ℝ) ≤ a := by
    dsimp [a]
    exact_mod_cast haNat
  have hden : 0 < a - 1 := by linarith
  have hlt : r < 1 / (a - 1) := by
    simpa [mersenneWeight, a, r] using lt_of_not_ge hskip
  have hmul := mul_lt_mul_of_pos_left hlt (mul_pos (by positivity : 0 < a) (by positivity : 0 < a))
  have hover : a * (a * r - 1) < a / (a - 1) := by
    calc
      a * (a * r - 1) = a * a * r - a := by ring
      _ < a * a * (1 / (a - 1)) - a := by linarith
      _ = a / (a - 1) := by
        field_simp
        ring
  have hratio : a / (a - 1) < 2 := by
    apply (div_lt_iff₀ hden).2
    linarith
  exact hover.trans hratio

/-- If the full-shell margin is still negative at an actual skip, its
integer seam defect lies inside the existing square-root strip. -/
theorem neg_greedyHalfFrozenMargin_fullShell_le_halfStripBound
    (n : ℕ) (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    -greedyHalfFrozenMargin (n - 1) n ≤
      (halfStripBound (2 * n) : ℤ) := by
  let P : Set ℕ := ↑(halfGreedyPrefixSupport (n - 1))
  let M : ℤ := greedyHalfFrozenMargin (n - 1) n
  let T : ℝ := binaryCoeffTail (supportCoeff P) (2 * n)
  have hid := greedyHalfFrozenMargin_fullShell_cast_eq_slack_sub_tail (n - 1)
  have hcast : (M : ℝ) =
      (2 : ℝ) ^ n *
          (1 - (2 : ℝ) ^ n *
            greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) - T := by
    simpa [M, P, T, Nat.sub_add_cancel (by omega : 1 ≤ n), two_mul] using hid
  have hover := greedyHalf_skip_amplified_dyadic_overshoot_lt_two n
    (by omega) hskip
  have htail := binaryCoeffTail_supportCoeff_lt_two_natSqrt_add_three
    P (2 * n) (by omega)
  have hreal : ((-M : ℤ) : ℝ) <
      2 * (Nat.sqrt (2 * n) : ℝ) + 5 := by
    push_cast
    rw [hcast]
    linarith
  have hint : -M < (2 * Nat.sqrt (2 * n) + 5 : ℕ) := by
    exact_mod_cast hreal
  change -M ≤ (halfStripBound (2 * n) : ℤ)
  unfold halfStripBound
  omega

/-- Exact adapter requested by the seam lane: a negative full-shell frozen
margin at an actual skipped rank produces the right-hand small integer-greedy
remainder statement of `seam_smallPositiveDefect_iff_integerGreedyRemainder`.
-/
theorem neg_greedyHalfFrozenMargin_fullShell_implies_seamRemainder_small
    (n : ℕ) (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    1 ≤ seamIntegerGreedyRemainder n ∧
      seamIntegerGreedyRemainder n ≤ halfStripBound (2 * n) := by
  let P := halfGreedyPrefixSupport (n - 1)
  have hshadow :=
    greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target n (by omega)
  have hstemZ : (stemTruncatedSum n P : ℤ) < (seamSubsetTarget n : ℤ) := by
    change (stemTruncatedSum n P : ℤ) < (seamSubsetTarget n : ℤ)
    change greedyHalfFrozenMargin (n - 1) n =
      (stemTruncatedSum n P : ℤ) - (seamSubsetTarget n : ℤ) at hshadow
    linarith
  have hstem : stemTruncatedSum n P < seamSubsetTarget n := by
    exact_mod_cast hstemZ
  have hmarginBound :=
    neg_greedyHalfFrozenMargin_fullShell_le_halfStripBound n hn hskip hneg
  have hshadowP : greedyHalfFrozenMargin (n - 1) n =
      (stemTruncatedSum n P : ℤ) - (seamSubsetTarget n : ℤ) := by
    simpa [P] using hshadow
  have hdefectZ :
      (seamSubsetTarget n : ℤ) - (stemTruncatedSum n P : ℤ) ≤
        (halfStripBound (2 * n) : ℤ) := by
    linarith
  have hdefect :
      seamSubsetTarget n - stemTruncatedSum n P ≤ halfStripBound (2 * n) := by
    have hcastsub :
        ((seamSubsetTarget n - stemTruncatedSum n P : ℕ) : ℤ) =
          (seamSubsetTarget n : ℤ) - (stemTruncatedSum n P : ℤ) := by
      rw [Nat.cast_sub hstem.le]
    have hdefectZ' :
        ((seamSubsetTarget n - stemTruncatedSum n P : ℕ) : ℤ) ≤
          (halfStripBound (2 * n) : ℤ) := by
      rw [hcastsub]
      exact hdefectZ
    exact_mod_cast hdefectZ'
  apply (seam_smallPositiveDefect_iff_integerGreedyRemainder (s := n) hn).1
  refine ⟨stemBits n P, stemBits_length_eq_seamWeights_length n P, ?_, ?_⟩
  · rw [weightedBoolSum_stemBits]
    exact hstem
  · rw [weightedBoolSum_stemBits]
    exact hdefect

/-- Any Boolean word giving a positive defect shorter than the separation
gap is the descending greedy word itself. -/
theorem smallPositiveDefect_bits_eq_integerGreedyBits
    {gap B C : ℕ} (hgap : 0 < gap) (hB : B < gap)
    {weights : List ℕ} (hdom : GapDominates gap weights)
    {bits : List Bool}
    (hlen : bits.length = weights.length)
    (hlt : weightedBoolSum weights bits < C)
    (hdef : C - weightedBoolSum weights bits ≤ B) :
    bits = integerGreedyBits weights C := by
  let greedy := integerGreedyBits weights C
  let bsum := weightedBoolSum weights bits
  let gsum := weightedBoolSum weights greedy
  have hgreedyLen : greedy.length = weights.length :=
    integerGreedyBits_length weights C
  have hgreedyAdm : gsum ≤ C :=
    integerGreedyBits_admissible weights C
  have hbitsAdm : bsum ≤ C := hlt.le
  have hmax : bsum ≤ gsum :=
    integerGreedyBits_maximal hgap hdom hlen hbitsAdm
  by_contra hne
  rcases weightedBoolSum_separated hgap hdom hlen hgreedyLen hne with
    hsep | hsep
  · have hgapDef : gap ≤ C - bsum := by omega
    omega
  · omega

/-- Taking rank `n` forces the actual full-shell frozen margin to be
strictly negative.  This is the easy half of the observed sign dichotomy. -/
theorem greedyHalfFrozenMargin_fullShell_neg_of_take
    (n : ℕ) (hn : 1 ≤ n)
    (htake : mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) :
    greedyHalfFrozenMargin (n - 1) n < 0 := by
  let r : ℝ := greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)
  let a : ℝ := (2 : ℝ) ^ n
  let P : Set ℕ := ↑(halfGreedyPrefixSupport (n - 1))
  let T : ℝ := binaryCoeffTail (supportCoeff P) (2 * n)
  have haNat : 2 ^ 1 ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num) hn
  have ha : (2 : ℝ) ≤ a := by
    dsimp [a]
    exact_mod_cast haNat
  have hden : 0 < a - 1 := by linarith
  have htake' : 1 / (a - 1) ≤ r := by
    simpa [mersenneWeight, a, r] using htake
  have hrpos : 0 < r := lt_of_lt_of_le (one_div_pos.mpr hden) htake'
  have har : 1 < a * r := by
    have hone : 1 ≤ r * (a - 1) := (div_le_iff₀ hden).mp htake'
    nlinarith
  have htail : 0 ≤ T := binaryCoeffTail_nonneg _ _
  have hid := greedyHalfFrozenMargin_fullShell_cast_eq_slack_sub_tail (n - 1)
  have hid' :
      (greedyHalfFrozenMargin (n - 1) n : ℝ) =
        a * (1 - a * r) - T := by
    simpa [a, r, P, T, Nat.sub_add_cancel hn, two_mul] using hid
  have hreal : (greedyHalfFrozenMargin (n - 1) n : ℝ) < 0 := by
    rw [hid']
    nlinarith [show 0 < a by positivity]
  exact_mod_cast hreal

/-- Therefore nonnegativity of the full-shell margin forces an actual skip.
The converse is the exact remaining arithmetic direction. -/
theorem skip_of_fullShell_margin_nonneg
    (n : ℕ) (hn : 1 ≤ n)
    (hmargin : 0 ≤ greedyHalfFrozenMargin (n - 1) n) :
    ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1) := by
  intro htake
  have hneg := greedyHalfFrozenMargin_fullShell_neg_of_take n hn htake
  omega

/-- A hypothetical negative full-shell margin at an actual skip aligns the
actual finite Mersenne prefix with the integer-seam greedy word exactly. -/
theorem stemBits_eq_integerGreedyBits_of_skipped_fullShell_neg
    (n : ℕ) (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    stemBits n (halfGreedyPrefixSupport (n - 1)) =
      integerGreedyBits (seamWeights n) (seamSubsetTarget n) := by
  let P := halfGreedyPrefixSupport (n - 1)
  have hshadow :=
    greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target n (by omega)
  have hstemZ : (stemTruncatedSum n P : ℤ) < (seamSubsetTarget n : ℤ) := by
    change greedyHalfFrozenMargin (n - 1) n =
      (stemTruncatedSum n P : ℤ) - (seamSubsetTarget n : ℤ) at hshadow
    linarith
  have hstem : stemTruncatedSum n P < seamSubsetTarget n := by
    exact_mod_cast hstemZ
  have hmarginBound :=
    neg_greedyHalfFrozenMargin_fullShell_le_halfStripBound n hn hskip hneg
  have hdefectZ :
      (seamSubsetTarget n : ℤ) - (stemTruncatedSum n P : ℤ) ≤
        (halfStripBound (2 * n) : ℤ) := by
    change greedyHalfFrozenMargin (n - 1) n =
      (stemTruncatedSum n P : ℤ) - (seamSubsetTarget n : ℤ) at hshadow
    linarith
  have hdefect :
      seamSubsetTarget n - stemTruncatedSum n P ≤ halfStripBound (2 * n) := by
    have hcastsub :
        ((seamSubsetTarget n - stemTruncatedSum n P : ℕ) : ℤ) =
          (seamSubsetTarget n : ℤ) - (stemTruncatedSum n P : ℤ) := by
      rw [Nat.cast_sub hstem.le]
    exact_mod_cast (show
      ((seamSubsetTarget n - stemTruncatedSum n P : ℕ) : ℤ) ≤
        (halfStripBound (2 * n) : ℤ) by simpa [hcastsub] using hdefectZ)
  apply smallPositiveDefect_bits_eq_integerGreedyBits
    (gap := 2 ^ (n + 1)) (B := halfStripBound (2 * n))
  · positivity
  · exact halfStripBound_lt_truncatedWeightGap hn
  · exact seamWeights_gapDominates (by omega)
  · exact stemBits_length_eq_seamWeights_length n P
  · simpa [weightedBoolSum_stemBits] using hstem
  · simpa [weightedBoolSum_stemBits] using hdefect

/-- Once the actual stem is the descending seam-greedy word, the full-shell
margin is exactly the negative integer-greedy seam remainder. -/
theorem greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment
    (n : ℕ) (hn : 3 ≤ n)
    (halign :
      stemBits n (halfGreedyPrefixSupport (n - 1)) =
        integerGreedyBits (seamWeights n) (seamSubsetTarget n)) :
    greedyHalfFrozenMargin (n - 1) n =
      -(seamIntegerGreedyRemainder n : ℤ) := by
  let P := halfGreedyPrefixSupport (n - 1)
  have hshadow :
      greedyHalfFrozenMargin (n - 1) n =
        (stemTruncatedSum n P : ℤ) - (seamSubsetTarget n : ℤ) := by
    simpa [P] using
      greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target n (by omega)
  have hsum :
      stemTruncatedSum n P =
        weightedBoolSum (seamWeights n)
          (integerGreedyBits (seamWeights n) (seamSubsetTarget n)) := by
    calc
      stemTruncatedSum n P =
          weightedBoolSum (seamWeights n) (stemBits n P) :=
        (weightedBoolSum_stemBits n P).symm
      _ = weightedBoolSum (seamWeights n)
          (integerGreedyBits (seamWeights n) (seamSubsetTarget n)) := by
        rw [show stemBits n P =
            integerGreedyBits (seamWeights n) (seamSubsetTarget n) by
          simpa [P] using halign]
  have hadm :
      weightedBoolSum (seamWeights n)
          (integerGreedyBits (seamWeights n) (seamSubsetTarget n)) ≤
        seamSubsetTarget n :=
    integerGreedyBits_admissible (seamWeights n) (seamSubsetTarget n)
  rw [hshadow, hsum]
  unfold seamIntegerGreedyRemainder integerGreedyRemainder
  rw [Nat.cast_sub hadm]
  ring

/-- At a genuine skip, negativity of the full-shell margin is equivalent to
positive seam remainder together with exact actual/seam word alignment. -/
theorem skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos
    (n : ℕ) (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) :
    greedyHalfFrozenMargin (n - 1) n < 0 ↔
      stemBits n (halfGreedyPrefixSupport (n - 1)) =
          integerGreedyBits (seamWeights n) (seamSubsetTarget n) ∧
        1 ≤ seamIntegerGreedyRemainder n := by
  constructor
  · intro hneg
    exact ⟨stemBits_eq_integerGreedyBits_of_skipped_fullShell_neg
        n hn hskip hneg,
      (neg_greedyHalfFrozenMargin_fullShell_implies_seamRemainder_small
        n hn hskip hneg).1⟩
  · rintro ⟨halign, hpos⟩
    rw [greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment
      n hn halign]
    have hposZ : (1 : ℤ) ≤ (seamIntegerGreedyRemainder n : ℤ) := by
      exact_mod_cast hpos
    omega

/-- Exact word-level replacement for the skipped full-shell sign invariant:
if a skipped actual word equals the seam-greedy word, its seam remainder must
vanish. -/
def HalfGreedySkippedSeamAlignmentZero : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    stemBits n (halfGreedyPrefixSupport (n - 1)) =
        integerGreedyBits (seamWeights n) (seamSubsetTarget n) →
      seamIntegerGreedyRemainder n = 0

/-- Direct full-shell sign socket.  It asks only that the actual frozen margin
has already crossed by the full-shell horizon at every genuine skipped rank;
no seam or abstract adjacent-cut coordinate remains in the hypothesis. -/
def HalfGreedySkippedFullShellNonnegative : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    0 ≤ greedyHalfFrozenMargin (n - 1) n

/-- The full-shell sign socket is itself a governed frozen-margin producer,
with the two initial ranks discharged directly. -/
theorem governedFrozenMarginProducer_of_skippedFullShellNonnegative
    (hsign : HalfGreedySkippedFullShellNonnegative) :
    HalfGreedyGovernedFrozenMarginProducer := by
  intro k hskip
  by_cases hk0 : k = 0
  · subst k
    refine ⟨0, by omega, ?_⟩
    simp [greedyHalfFrozenMargin]
  by_cases hk1 : k = 1
  · subst k
    exfalso
    apply hskip
    have hmem := two_mem_greedyMersenneSupport_half
    have htake :=
      (succ_mem_greedyMersenneSupport_iff (1 / 2 : ℝ) 1).mp
        (by simpa using hmem)
    simpa using htake
  exact ⟨k + 1, by omega,
    hsign (k + 1) (by omega) (by simpa using hskip)⟩

/-- Final direct consumer for the actual full-shell sign invariant. -/
theorem half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
    (hsign : HalfGreedySkippedFullShellNonnegative) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer
    (governedFrozenMarginProducer_of_skippedFullShellNonnegative hsign)

/-- The exact word-level condition implies the skipped full-shell sign
invariant. -/
theorem skippedFullShellNonnegative_of_seamAlignmentZero
    (hsafe : HalfGreedySkippedSeamAlignmentZero) :
    HalfGreedySkippedFullShellNonnegative := by
  intro n hn hskip
  by_contra hnot
  have hneg : greedyHalfFrozenMargin (n - 1) n < 0 :=
    lt_of_not_ge hnot
  obtain ⟨halign, hpos⟩ :=
    (skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos
      n hn hskip).1 hneg
  have hzero := hsafe n hn hskip halign
  omega

/-- Conversely, nonnegative skipped margins force zero seam remainder at
every aligned skipped word. -/
theorem seamAlignmentZero_of_skippedFullShellNonnegative
    (hsign : HalfGreedySkippedFullShellNonnegative) :
    HalfGreedySkippedSeamAlignmentZero := by
  intro n hn hskip halign
  by_contra hne
  have hpos : 1 ≤ seamIntegerGreedyRemainder n :=
    Nat.one_le_iff_ne_zero.mpr hne
  have hneg :=
    (skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos
      n hn hskip).2 ⟨halign, hpos⟩
  have hnonneg := hsign n hn hskip
  omega

/-- The word-alignment-zero condition and the direct sign socket are exactly
equivalent. -/
theorem skippedSeamAlignmentZero_iff_skippedFullShellNonnegative :
    HalfGreedySkippedSeamAlignmentZero ↔
      HalfGreedySkippedFullShellNonnegative := by
  exact ⟨skippedFullShellNonnegative_of_seamAlignmentZero,
    seamAlignmentZero_of_skippedFullShellNonnegative⟩

/-- Final exact half-membership consumer in word-level seam coordinates. -/
theorem half_mem_mersenneAchievementSet_of_skippedSeamAlignmentZero
    (hsafe : HalfGreedySkippedSeamAlignmentZero) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
    (skippedFullShellNonnegative_of_seamAlignmentZero hsafe)

/-- Smallest skip-conditioned seam escape socket needed by the actual half
orbit.  Exceptional seam rows that are actual takes are deliberately absent.
-/
def HalfGreedySkippedSeamEscape : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    halfStripBound (2 * n) < seamIntegerGreedyRemainder n

/-- The skip-conditioned seam escape socket forces a governed crossing at
the full-shell horizon `J=k+1`. -/
theorem governedFrozenMarginProducer_of_skippedSeamEscape
    (hescape : HalfGreedySkippedSeamEscape) :
    HalfGreedyGovernedFrozenMarginProducer := by
  intro k hskip
  by_cases hk0 : k = 0
  · subst k
    refine ⟨0, by omega, ?_⟩
    simp [greedyHalfFrozenMargin]
  by_cases hk1 : k = 1
  · subst k
    exfalso
    apply hskip
    have hmem := two_mem_greedyMersenneSupport_half
    have htake :=
      (succ_mem_greedyMersenneSupport_iff (1 / 2 : ℝ) 1).mp (by simpa using hmem)
    simpa using htake
  refine ⟨k + 1, by omega, ?_⟩
  by_contra hnot
  have hneg : greedyHalfFrozenMargin k (k + 1) < 0 := lt_of_not_ge hnot
  have hsmall :=
    neg_greedyHalfFrozenMargin_fullShell_implies_seamRemainder_small
      (k + 1) (by omega) (by simpa using hskip) (by simpa using hneg)
  have hlarge := hescape (k + 1) (by omega) (by simpa using hskip)
  omega

/-- Final conditional consumer: the skip-conditioned seam escape statement
is sufficient for exact half-membership. -/
theorem half_mem_mersenneAchievementSet_of_skippedSeamEscape
    (hescape : HalfGreedySkippedSeamEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_governedFrozenMarginProducer
    (governedFrozenMarginProducer_of_skippedSeamEscape hescape)

end Erdos249257

#print axioms Erdos249257.binaryCoeffTail_supportCoeff_lt_two_natSqrt_add_three
#print axioms Erdos249257.greedyHalfFrozenMargin_fullShell_eq_stemTruncatedSum_sub_target
#print axioms Erdos249257.neg_greedyHalfFrozenMargin_fullShell_implies_seamRemainder_small
#print axioms Erdos249257.smallPositiveDefect_bits_eq_integerGreedyBits
#print axioms Erdos249257.greedyHalfFrozenMargin_fullShell_neg_of_take
#print axioms Erdos249257.skip_of_fullShell_margin_nonneg
#print axioms Erdos249257.stemBits_eq_integerGreedyBits_of_skipped_fullShell_neg
#print axioms Erdos249257.greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment
#print axioms Erdos249257.skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos
#print axioms Erdos249257.skippedSeamAlignmentZero_iff_skippedFullShellNonnegative
#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamAlignmentZero
#print axioms Erdos249257.governedFrozenMarginProducer_of_skippedFullShellNonnegative
#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
#print axioms Erdos249257.governedFrozenMarginProducer_of_skippedSeamEscape
#print axioms Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape
