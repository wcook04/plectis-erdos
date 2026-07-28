import Erdos249257.HalfCylinderLastProducerContradiction
import Erdos249257.HalfCylinderFinalMiddleTailSocket
import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.HalfCylinderResetDeficitEscape

/-!
# A cardinality-scale bound for the last middle producer

The square-root envelope for an arbitrary divisor-incidence support is much
larger than necessary for a finite seam prefix.  If `F` is finite, every
future coefficient counts at most `F.card` divisors, and the normalized
binary geometric tail has total mass one.  Hence

`binaryCoeffTail (supportCoeff (↑F)) N ≤ F.card`.

For the concrete middle producer this gives an alternative reduction of the
remaining tail escape to the exact natural-number inequality

`card(below support) + belowPulse + 5 < 4 * remainder`.

Equivalently, the affine carry is larger than the cardinality of the
terminal-augmented support.  This is sharper than the generic square-root
strip only for sparse finite prefixes; it is not a uniform improvement when
the support cardinality grows linearly with the row.  It does handle the
exceptional middle row seven, where the square-root inequality is false.
The theorem below does not assert the remaining cardinality inequality; it
exposes its exact arithmetic content.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy
open HalfCylinderFiniteShadow
open scoped BigOperators

noncomputable section

/-! ## A sharp tail bound for finite supports -/

/-- The first four future coefficient rows form a locally usable lower
surface for the complete binary tail.  Keeping this next to the forced-
divisor lemma lets later cell sieves combine exact divisibility at four rows
without reopening the analytic `tsum`. -/
theorem four_coeff_lower_le_binaryCoeffTail
    (A : Set ℕ) (N : ℕ) :
    (supportCoeff A (N + 1) : ℝ) / 2 +
          (supportCoeff A (N + 2) : ℝ) / 4 +
          (supportCoeff A (N + 3) : ℝ) / 8 +
          (supportCoeff A (N + 4) : ℝ) / 16 ≤
      binaryCoeffTail (supportCoeff A) N := by
  calc
    (supportCoeff A (N + 1) : ℝ) / 2 +
          (supportCoeff A (N + 2) : ℝ) / 4 +
          (supportCoeff A (N + 3) : ℝ) / 8 +
          (supportCoeff A (N + 4) : ℝ) / 16 =
        finiteCoeffWindow A N 4 := by
          norm_num [finiteCoeffWindow, Finset.sum_range_succ]
    _ ≤ binaryCoeffTail (supportCoeff A) N :=
      finiteCoeffWindow_le_binaryCoeffTail A N 4

/-- Four rows of the lazy support already outweigh charge two unless the
last producer depth is `2 mod 3`.  The selected divisors are the row itself,
its cofinite half on even rows, and the forced seam ranks `2,3,6`.  This is
the coefficient-tail version of the adjacent
`seamRankFloorError_two_three_six_eq` phase split. -/
theorem two_lt_binaryCoeffTail_union_Ioi_of_forced_two_three_six
    (U : Set ℕ) (D : ℕ) (hD13 : 13 ≤ D) (hU : U ⊆ Set.Iio D)
    (h2 : 2 ∈ U) (h3 : 3 ∈ U) (h6 : 6 ∈ U)
    (hmod : D % 3 ≠ 2) :
    2 < binaryCoeffTail (supportCoeff (U ∪ Set.Ioi D)) (2 * D + 2) := by
  classical
  let B : Set ℕ := U ∪ Set.Ioi D
  have hself (n : ℕ) (hDn : D < n) :
      1 ≤ supportCoeff B n := by
    have h := card_le_supportCoeff_of_forced_divisors
      B ({n} : Finset ℕ) n (by omega)
      (by
        intro d hd
        simp only [Finset.mem_singleton] at hd
        subst d
        exact Set.mem_union_right U (Set.mem_Ioi.mpr hDn))
      (by simp)
    simpa using h
  have heven (k : ℕ) (hk : D < k) :
      3 ≤ supportCoeff B (2 * k) := by
    have h := card_le_supportCoeff_of_forced_divisors
      B ({2, k, 2 * k} : Finset ℕ) (2 * k) (by omega)
      (by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact Set.mem_union_left _ h2
        · exact Set.mem_union_right U (Set.mem_Ioi.mpr hk)
        · exact Set.mem_union_right U (Set.mem_Ioi.mpr (by omega)))
      (by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact ⟨k, by omega⟩
        · exact ⟨2, by omega⟩
        · exact dvd_rfl)
    have hcard : ({2, k, 2 * k} : Finset ℕ).card = 3 := by
      have h2k : 2 ≠ k := by omega
      have h22k : 2 ≠ 2 * k := by omega
      have hk2k : k ≠ 2 * k := by omega
      simp [h2k, h22k, hk2k]
    rwa [hcard] at h
  have hthreeSelf (n : ℕ) (hDn : D < n) (hthree : 3 ∣ n) :
      2 ≤ supportCoeff B n := by
    have h := card_le_supportCoeff_of_forced_divisors
      B ({3, n} : Finset ℕ) n (by omega)
      (by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact Set.mem_union_left _ h3
        · exact Set.mem_union_right U (Set.mem_Ioi.mpr hDn))
      (by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact hthree
        · exact dvd_rfl)
    have hcard : ({3, n} : Finset ℕ).card = 2 := by
      have h3n : 3 ≠ n := by omega
      simp [h3n]
    rwa [hcard] at h
  have hfive (k : ℕ) (hk : D < k) (hsix : 6 ∣ 2 * k) :
      5 ≤ supportCoeff B (2 * k) := by
    have h := card_le_supportCoeff_of_forced_divisors
      B ({2, 3, 6, k, 2 * k} : Finset ℕ) (2 * k) (by omega)
      (by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · exact Set.mem_union_left _ h2
        · exact Set.mem_union_left _ h3
        · exact Set.mem_union_left _ h6
        · exact Set.mem_union_right U (Set.mem_Ioi.mpr hk)
        · exact Set.mem_union_right U (Set.mem_Ioi.mpr (by omega)))
      (by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl | rfl | rfl
        · exact ⟨k, by omega⟩
        · exact dvd_trans (by norm_num : 3 ∣ 6) hsix
        · exact hsix
        · exact ⟨2, by omega⟩
        · exact dvd_rfl)
    have hcard : ({2, 3, 6, k, 2 * k} : Finset ℕ).card = 5 := by
      have h2k : 2 ≠ k := by omega
      have h22k : 2 ≠ 2 * k := by omega
      have h3k : 3 ≠ k := by omega
      have h32k : 3 ≠ 2 * k := by omega
      have h6k : 6 ≠ k := by omega
      have h62k : 6 ≠ 2 * k := by omega
      have hk2k : k ≠ 2 * k := by omega
      simp [h2k, h22k, h3k, h32k, h6k, h62k, hk2k]
    rwa [hcard] at h
  have hwindow := four_coeff_lower_le_binaryCoeffTail B (2 * D + 2)
  have hrange : D % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hDmod : D % 3
  · have hc1 : 2 ≤ supportCoeff B (2 * D + 3) :=
      hthreeSelf _ (by omega)
        (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
    have hc2 : 3 ≤ supportCoeff B (2 * D + 4) := by
      simpa only [show 2 * D + 4 = 2 * (D + 2) by omega] using
        heven (D + 2) (by omega)
    have hc3 : 1 ≤ supportCoeff B (2 * D + 5) := hself _ (by omega)
    have hc4 : 5 ≤ supportCoeff B (2 * D + 6) := by
      simpa only [show 2 * D + 6 = 2 * (D + 3) by omega] using
        hfive (D + 3) (by omega)
          (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
    norm_num only [show 2 * D + 2 + 1 = 2 * D + 3 by omega,
      show 2 * D + 2 + 2 = 2 * D + 4 by omega,
      show 2 * D + 2 + 3 = 2 * D + 5 by omega,
      show 2 * D + 2 + 4 = 2 * D + 6 by omega] at hwindow
    have hc1R : (2 : ℝ) ≤ supportCoeff B (2 * D + 3) := by exact_mod_cast hc1
    have hc2R : (3 : ℝ) ≤ supportCoeff B (2 * D + 4) := by exact_mod_cast hc2
    have hc3R : (1 : ℝ) ≤ supportCoeff B (2 * D + 5) := by exact_mod_cast hc3
    have hc4R : (5 : ℝ) ≤ supportCoeff B (2 * D + 6) := by exact_mod_cast hc4
    dsimp [B] at hwindow ⊢
    linarith only [hwindow, hc1R, hc2R, hc3R, hc4R]
  · have hc1 : 1 ≤ supportCoeff B (2 * D + 3) := hself _ (by omega)
    have hc2 : 5 ≤ supportCoeff B (2 * D + 4) := by
      simpa only [show 2 * D + 4 = 2 * (D + 2) by omega] using
        hfive (D + 2) (by omega)
          (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
    have hc3 : 1 ≤ supportCoeff B (2 * D + 5) := hself _ (by omega)
    have hc4 : 3 ≤ supportCoeff B (2 * D + 6) := by
      simpa only [show 2 * D + 6 = 2 * (D + 3) by omega] using
        heven (D + 3) (by omega)
    norm_num only [show 2 * D + 2 + 1 = 2 * D + 3 by omega,
      show 2 * D + 2 + 2 = 2 * D + 4 by omega,
      show 2 * D + 2 + 3 = 2 * D + 5 by omega,
      show 2 * D + 2 + 4 = 2 * D + 6 by omega] at hwindow
    have hc1R : (1 : ℝ) ≤ supportCoeff B (2 * D + 3) := by exact_mod_cast hc1
    have hc2R : (5 : ℝ) ≤ supportCoeff B (2 * D + 4) := by exact_mod_cast hc2
    have hc3R : (1 : ℝ) ≤ supportCoeff B (2 * D + 5) := by exact_mod_cast hc3
    have hc4R : (3 : ℝ) ≤ supportCoeff B (2 * D + 6) := by exact_mod_cast hc4
    dsimp [B] at hwindow ⊢
    linarith only [hwindow, hc1R, hc2R, hc3R, hc4R]
  · exact (hmod rfl).elim

/-- A finite support contributes at most one divisor per support element. -/
theorem supportCoeff_coe_finset_le_card
    (F : Finset ℕ) (n : ℕ) :
    supportCoeff (↑F : Set ℕ) n ≤ F.card := by
  rw [supportCoeff_finset_eq_indicatorSum]
  calc
    (∑ d ∈ F, if d ∈ n.divisors then 1 else 0)
        ≤ ∑ _d ∈ F, 1 := by
          apply Finset.sum_le_sum
          intro d hd
          split <;> omega
    _ = F.card := by simp

/-- The normalized future divisor-incidence tail of a finite support is at
most the cardinality of that support.  The constant is one, not two: the
weights `2^(-(j+1))` have total mass exactly one. -/
theorem binaryCoeffTail_supportCoeff_coe_finset_le_card
    (F : Finset ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff (↑F : Set ℕ)) N ≤ (F.card : ℝ) := by
  let C : ℝ := F.card
  have hsource : Summable
      (fun j : ℕ ↦
        (supportCoeff (↑F : Set ℕ) (N + j + 1) : ℝ) /
          (2 : ℝ) ^ (j + 1)) :=
    summable_coeff_shift_tail 2 N (supportCoeff (↑F : Set ℕ))
      (by norm_num) (supportCoeff_le_self _)
  have hgeom : Summable (fun j : ℕ ↦ ((1 : ℝ) / 2) ^ j) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hmajorant : Summable
      (fun j : ℕ ↦ C / (2 : ℝ) ^ (j + 1)) := by
    have h := hgeom.mul_left (C / 2)
    refine h.congr fun j ↦ ?_
    rw [pow_succ, div_pow, one_pow]
    ring
  have hterm : ∀ j : ℕ,
      (supportCoeff (↑F : Set ℕ) (N + j + 1) : ℝ) /
          (2 : ℝ) ^ (j + 1) ≤
        C / (2 : ℝ) ^ (j + 1) := by
    intro j
    have hcoeff :
        (supportCoeff (↑F : Set ℕ) (N + j + 1) : ℝ) ≤ C := by
      dsimp [C]
      exact_mod_cast supportCoeff_coe_finset_le_card F (N + j + 1)
    exact div_le_div_of_nonneg_right hcoeff (by positivity)
  have hmajorantSum :
      (∑' j : ℕ, C / (2 : ℝ) ^ (j + 1)) = C := by
    calc
      (∑' j : ℕ, C / (2 : ℝ) ^ (j + 1)) =
          (C / 2) * ∑' j : ℕ, ((1 : ℝ) / 2) ^ j := by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro j
            rw [pow_succ, div_pow, one_pow]
            ring
      _ = C := by
        rw [tsum_geometric_of_norm_lt_one
          (by norm_num : ‖(1 : ℝ) / 2‖ < 1)]
        norm_num
  unfold binaryCoeffTail
  calc
    (∑' j : ℕ,
        (supportCoeff (↑F : Set ℕ) (N + j + 1) : ℝ) /
          (2 : ℝ) ^ (j + 1)) ≤
        ∑' j : ℕ, C / (2 : ℝ) ^ (j + 1) :=
      Summable.tsum_le_tsum hterm hsource hmajorant
    _ = C := hmajorantSum
    _ = (F.card : ℝ) := by rfl

/-! ## The exact middle-coordinate socket -/

/-- The late middle producer only has to clear the cardinality of its finite
prefix.  Written in source coordinates, this is exactly the strict affine
carry inequality after cancelling the terminal support element. -/
def SeamMiddleProducerCardEscape : Prop :=
  ∀ (s : ℕ) (hs : 5 ≤ s), 13 ≤ s →
    ¬ (seamAdjacentCut s hs).successorCarries →
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight →
        (seamWordSupport (seamAdjacentCut s hs).below).card +
            (seamAdjacentCut s hs).belowPulse + 5 <
          4 * (seamAdjacentCut s hs).remainder

/-- The source-coordinate cardinal inequality says precisely that the
producer carry beats the cardinality of the terminal-augmented support. -/
theorem middleProducer_card_lt_carry
    {s : ℕ} (hs : 5 ≤ s)
    (hcard :
      (seamWordSupport (seamAdjacentCut s hs).below).card +
            (seamAdjacentCut s hs).belowPulse + 5 <
          4 * (seamAdjacentCut s hs).remainder) :
    (((insert s
        (seamWordSupport (seamAdjacentCut s hs).below)).card : ℕ) : ℝ) <
      (producerCarry
          (insert s
            (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)) s : ℝ) := by
  let K := seamAdjacentCut s hs
  have hsnot : s ∉ seamWordSupport K.below := by
    intro hmem
    exact (Nat.lt_irrefl s) (seamWordSupport_below hmem).2
  have hcarry := producerCarry_insert_seamBelowSupport_eq_middleCoordinate s hs
  have hcardInsert : (insert s (seamWordSupport K.below)).card =
      (seamWordSupport K.below).card + 1 := by
    rw [Finset.card_insert_of_notMem hsnot]
  change
    (((insert s (seamWordSupport K.below)).card : ℕ) : ℝ) <
      (producerCarry
        (insert s (↑(seamWordSupport K.below) : Set ℕ)) s : ℝ)
  rw [hcarry, hcardInsert]
  have hcardZ :
      (((seamWordSupport K.below).card : ℕ) : ℤ) +
          (K.belowPulse : ℤ) + 5 <
        4 * (K.remainder : ℤ) := by
    exact_mod_cast hcard
  have hgoalZ :
    (((seamWordSupport K.below).card : ℕ) : ℤ) + 1 <
      4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 := by
    omega
  exact_mod_cast hgoalZ

/-- The accumulated pulse of a finite seam word is at most twice the number
of selected ranks.  Consecutive pulse rows prevent a rank `d ≥ 2` from
contributing to both channels with total weight three. -/
theorem wordPulse_le_two_mul_supportCard
    {s : ℕ} (b : SeamRowWord s) :
    wordPulse s b.toNatWord ≤ 2 * (seamWordSupport b).card := by
  rw [wordPulse_eq_sum_seamWordSupport]
  calc
    (∑ d ∈ seamWordSupport b, rowPulse s d)
        ≤ ∑ _d ∈ seamWordSupport b, 2 := by
          apply Finset.sum_le_sum
          intro d hd
          exact rowPulse_le_two s d (seamWordSupport_below hd).1
    _ = 2 * (seamWordSupport b).card := by simp [Nat.mul_comm]

/-! ## Pulse absorption by the exact floor error -/

/-- Every quotient digit created by the row transition was already present,
at quarter scale, in the fractional error of that rank.  This is the exact
pointwise cancellation behind the floor-error update. -/
theorem rowPulse_le_four_mul_seamRankFloorError
    {s d : ℕ} (hs : 2 ≤ s) (hd : 2 ≤ d) :
    (rowPulse s d : ℚ) ≤ 4 * seamRankFloorError s d := by
  have hupdate :
      seamRankFloorError (s + 1) d =
        4 * seamRankFloorError s d - (rowPulse s d : ℚ) := by
    rw [seamRankFloorError, seamRankFloorError,
      truncatedMersenneWeight_succ hs hd, pow_succ]
    push_cast
    ring
  have hnonneg := seamRankFloorError_nonneg
    (s := s + 1) (d := d) (by omega : 1 ≤ d)
  rw [hupdate] at hnonneg
  linarith

/-- Summing the pointwise cancellation says that the complete word pulse is
at most four times the old floor error. -/
theorem wordPulse_le_four_mul_seamWordFloorError
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    (wordPulse s b.toNatWord : ℚ) ≤ 4 * seamWordFloorError b := by
  have hnonneg := seamWordFloorError_nonneg (b.extend false)
  rw [seamWordFloorError_extend_false hs b] at hnonneg
  linarith

/-! ## The forced low-rank prefix -/

/-- By row thirteen the half-capacity is already large enough that sixty
three copies of the dyadic side term fit below the leading half power.  This
is the common denominator estimate behind the forced `2,3,6` prefix. -/
theorem sixtyThree_mul_twoPow_le_twoPow_predDouble
    {s : ℕ} (hs : 13 ≤ s) :
    63 * 2 ^ s ≤ 2 ^ (2 * s - 1) := by
  have hexp : 6 ≤ s - 1 := by omega
  have hpow : 2 ^ 6 ≤ 2 ^ (s - 1) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hcoef : 63 ≤ 2 ^ (s - 1) := by
    norm_num at hpow ⊢
    omega
  have hmul := Nat.mul_le_mul_right (2 ^ s) hcoef
  calc
    63 * 2 ^ s ≤ 2 ^ (s - 1) * 2 ^ s := hmul
    _ = 2 ^ (2 * s - 1) := by
      rw [← pow_add]
      congr 1
      omega

/-- The first five descending-greedy decisions are forced uniformly from
row thirteen onward: take ranks two and three, skip four and five, then take
rank six.  The proof keeps the integer floors visible.  Upper quotient
bounds use the common denominator `63`; lower quotient bounds show that the
two skipped weights are individually larger than the remaining capacity. -/
theorem seamGreedy_head236_decisions
    (s : ℕ) (hs : 13 ≤ s) :
    truncatedMersenneWeight s 2 ≤ seamSubsetTarget s ∧
      truncatedMersenneWeight s 3 ≤
        seamSubsetTarget s - truncatedMersenneWeight s 2 ∧
      seamSubsetTarget s - truncatedMersenneWeight s 2 -
          truncatedMersenneWeight s 3 < truncatedMersenneWeight s 4 ∧
      seamSubsetTarget s - truncatedMersenneWeight s 2 -
          truncatedMersenneWeight s 3 < truncatedMersenneWeight s 5 ∧
      truncatedMersenneWeight s 6 ≤
        seamSubsetTarget s - truncatedMersenneWeight s 2 -
          truncatedMersenneWeight s 3 := by
  have hside := sixtyThree_mul_twoPow_le_twoPow_predDouble hs
  have hside21 : 21 * 2 ^ s ≤ 2 ^ (2 * s - 1) := by omega
  have hfour : 4 ^ s = 2 * 2 ^ (2 * s - 1) := by
    calc
      4 ^ s = 2 ^ (2 * s) := by
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
      _ = 2 ^ ((2 * s - 1) + 1) := by congr 1 <;> omega
      _ = 2 * 2 ^ (2 * s - 1) := by
        rw [pow_succ]
        ring
  have hsmall : 4 ≤ 2 ^ s := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hw2Upper :
      3 * truncatedMersenneWeight s 2 ≤ 4 ^ s := by
    change 3 * (4 ^ s / 3) ≤ 4 ^ s
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 3
  have hw3Upper :
      7 * truncatedMersenneWeight s 3 ≤ 4 ^ s := by
    change 7 * (4 ^ s / 7) ≤ 4 ^ s
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 7
  have hw6Upper :
      63 * truncatedMersenneWeight s 6 ≤ 4 ^ s := by
    change 63 * (4 ^ s / 63) ≤ 4 ^ s
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 63
  have hw2Lower :
      4 ^ s < 3 * (truncatedMersenneWeight s 2 + 1) := by
    change 4 ^ s < 3 * (4 ^ s / 3 + 1)
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 3))
  have hw3Lower :
      4 ^ s < 7 * (truncatedMersenneWeight s 3 + 1) := by
    change 4 ^ s < 7 * (4 ^ s / 7 + 1)
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 7))
  have hw4Lower :
      4 ^ s < 15 * (truncatedMersenneWeight s 4 + 1) := by
    change 4 ^ s < 15 * (4 ^ s / 15 + 1)
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 15))
  have hw5Lower :
      4 ^ s < 31 * (truncatedMersenneWeight s 5 + 1) := by
    change 4 ^ s < 31 * (4 ^ s / 31 + 1)
    simpa [Nat.mul_comm] using
      (Nat.lt_mul_div_succ (4 ^ s) (by norm_num : 0 < 31))
  have htake23 :
      truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 ≤
        seamSubsetTarget s := by
    unfold seamSubsetTarget
    omega
  have hskip4 :
      seamSubsetTarget s - truncatedMersenneWeight s 2 -
          truncatedMersenneWeight s 3 < truncatedMersenneWeight s 4 := by
    unfold seamSubsetTarget
    omega
  have hskip5 :
      seamSubsetTarget s - truncatedMersenneWeight s 2 -
          truncatedMersenneWeight s 3 < truncatedMersenneWeight s 5 := by
    unfold seamSubsetTarget
    omega
  have htake236 :
      truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
          truncatedMersenneWeight s 6 ≤ seamSubsetTarget s := by
    unfold seamSubsetTarget
    omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · exact hskip4
  constructor
  · exact hskip5
  · omega

/-- List-level normal form of the forced low-rank decisions. -/
theorem seamGreedyBits_head236
    (s : ℕ) (hs : 13 ≤ s) :
    integerGreedyBits (seamWeights s) (seamSubsetTarget s) =
      true :: true :: false :: false :: true ::
        integerGreedyBits (seamWeightsFrom s 7)
          (seamSubsetTarget s - truncatedMersenneWeight s 2 -
            truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6) := by
  rcases seamGreedy_head236_decisions s hs with
    ⟨h2, h3, h4, h5, h6⟩
  unfold seamWeights
  rw [seamWeightsFrom_eq_cons (by omega : 2 < s),
    seamWeightsFrom_eq_cons (by omega : 3 < s),
    seamWeightsFrom_eq_cons (by omega : 4 < s),
    seamWeightsFrom_eq_cons (by omega : 5 < s),
    seamWeightsFrom_eq_cons (by omega : 6 < s)]
  simp only [integerGreedyBits]
  rw [if_pos h2, if_pos h3, if_neg (by omega), if_neg (by omega),
    if_pos h6]

/-- The next greedy decision is forced one row later.  The denominator
identity `1/3 + 1/7 + 1/63 + 1/127 = 4000/8001` leaves exactly enough room
below one half once `s ≥ 14`. -/
theorem truncatedMersenneWeight_two_three_six_seven_le_target
    (s : ℕ) (hs : 14 ≤ s) :
    truncatedMersenneWeight s 2 + truncatedMersenneWeight s 3 +
        truncatedMersenneWeight s 6 + truncatedMersenneWeight s 7 ≤
      seamSubsetTarget s := by
  have hpow : 8001 ≤ 2 ^ (s - 1) := by
    have hexp : 13 ≤ s - 1 := by omega
    have hmono : 2 ^ 13 ≤ 2 ^ (s - 1) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    norm_num at hmono ⊢
    omega
  have hside : 8001 * 2 ^ s ≤ 2 ^ (2 * s - 1) := by
    have hmul := Nat.mul_le_mul_right (2 ^ s) hpow
    calc
      8001 * 2 ^ s ≤ 2 ^ (s - 1) * 2 ^ s := hmul
      _ = 2 ^ (2 * s - 1) := by
        rw [← pow_add]
        congr 1
        omega
  have hfour : 4 ^ s = 2 * 2 ^ (2 * s - 1) := by
    calc
      4 ^ s = 2 ^ (2 * s) := by
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
      _ = 2 ^ ((2 * s - 1) + 1) := by congr 1 <;> omega
      _ = 2 * 2 ^ (2 * s - 1) := by
        rw [pow_succ]
        ring
  have hw2 : 3 * truncatedMersenneWeight s 2 ≤ 4 ^ s := by
    change 3 * (4 ^ s / 3) ≤ 4 ^ s
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 3
  have hw3 : 7 * truncatedMersenneWeight s 3 ≤ 4 ^ s := by
    change 7 * (4 ^ s / 7) ≤ 4 ^ s
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 7
  have hw6 : 63 * truncatedMersenneWeight s 6 ≤ 4 ^ s := by
    change 63 * (4 ^ s / 63) ≤ 4 ^ s
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 63
  have hw7 : 127 * truncatedMersenneWeight s 7 ≤ 4 ^ s := by
    change 127 * (4 ^ s / 127) ≤ 4 ^ s
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (4 ^ s) 127
  unfold seamSubsetTarget
  omega

/-- List-level normal form exposing the newly forced rank seven. -/
theorem seamGreedyBits_head2367
    (s : ℕ) (hs : 14 ≤ s) :
    integerGreedyBits (seamWeights s) (seamSubsetTarget s) =
      true :: true :: false :: false :: true :: true ::
        integerGreedyBits (seamWeightsFrom s 8)
          (seamSubsetTarget s - truncatedMersenneWeight s 2 -
            truncatedMersenneWeight s 3 - truncatedMersenneWeight s 6 -
            truncatedMersenneWeight s 7) := by
  have htake := truncatedMersenneWeight_two_three_six_seven_le_target s hs
  rw [seamGreedyBits_head236 s (by omega : 13 ≤ s),
    seamWeightsFrom_eq_cons (by omega : 7 < s)]
  simp only [integerGreedyBits]
  rw [if_pos (by omega)]

/-- Rank seven is a fourth mandatory selected seam rank from row fourteen
onward.  It is kept separate from the established `2,3,6` interface so
downstream proofs can adopt the stronger sieve without API churn. -/
theorem seven_mem_seamGreedySupport
    (s : ℕ) (hs : 14 ≤ s) :
    7 ∈ seamWordSupport (seamGreedyWord s) := by
  have hbits := seamGreedyBits_head2367 s hs
  apply mem_seamWordSupport_iff.mpr
  refine ⟨⟨5, by omega⟩, ?_, by norm_num⟩
  simp [seamGreedyWord, SeamRowWord.ofList, hbits]

/-- The two ranks between the forced `3` and `6` decisions are genuinely
skipped.  This local negative interface lets the residual-pulse route turn
"not one of `2,3,6`" into the useful lower bound `7 ≤ d` without reopening
the list-level greedy calculation. -/
theorem four_five_not_mem_seamGreedySupport
    (s : ℕ) (hs : 13 ≤ s) :
    4 ∉ seamWordSupport (seamGreedyWord s) ∧
      5 ∉ seamWordSupport (seamGreedyWord s) := by
  have hbits := seamGreedyBits_head236 s hs
  constructor
  · apply (not_mem_seamWordSupport_iff_false
      (seamGreedyWord s) (by omega) (by omega)).2
    simp [seamGreedyWord, SeamRowWord.ofList, hbits]
  · apply (not_mem_seamWordSupport_iff_false
      (seamGreedyWord s) (by omega) (by omega)).2
    simp [seamGreedyWord, SeamRowWord.ofList, hbits]

/-- Ranks `2`, `3`, and `6` are mandatory selected ranks in every concrete
seam word from row thirteen onward. -/
theorem two_three_six_mem_seamGreedySupport
    (s : ℕ) (hs : 13 ≤ s) :
    2 ∈ seamWordSupport (seamGreedyWord s) ∧
      3 ∈ seamWordSupport (seamGreedyWord s) ∧
      6 ∈ seamWordSupport (seamGreedyWord s) := by
  have hbits := seamGreedyBits_head236 s hs
  constructor
  · apply mem_seamWordSupport_iff.mpr
    refine ⟨⟨0, by omega⟩, ?_, by norm_num⟩
    simp [seamGreedyWord, SeamRowWord.ofList, hbits]
  constructor
  · apply mem_seamWordSupport_iff.mpr
    refine ⟨⟨1, by omega⟩, ?_, by norm_num⟩
    simp [seamGreedyWord, SeamRowWord.ofList, hbits]
  · apply mem_seamWordSupport_iff.mpr
    refine ⟨⟨4, by omega⟩, ?_, by norm_num⟩
    simp [seamGreedyWord, SeamRowWord.ofList, hbits]

/-- The signed middle landing splits exactly into four times the corrected
floor coordinate plus the nonnegative next-row floor slack.  This is the
equality hidden behind pulse absorption. -/
theorem middleLandingSignedExcess_eq_four_floorZ_add_nextFloorError
    (s : ℕ) (hs : 5 ≤ s) :
    4 * ((seamAdjacentCut s hs).remainder : ℚ) -
        ((seamAdjacentCut s hs).belowPulse : ℚ) =
      4 * seamGreedyFloorZ s +
        seamWordFloorError ((seamAdjacentCut s hs).below.extend false) := by
  let K := seamAdjacentCut s hs
  have hrem : K.remainder = seamIntegerGreedyRemainder s := by
    simpa [K] using seamAdjacentCut_remainder hs
  have hZ := seamGreedyFloorZ_eq_remainder_sub_error s hs
  have hnext :
      seamWordFloorError (K.below.extend false) =
        4 * seamGreedyFloorError s - (K.belowPulse : ℚ) := by
    simpa [K, seamAdjacentCut, seamGreedyFloorError] using
      seamWordFloorError_extend_false
        (by omega : 3 ≤ s) (seamGreedyWord s)
  change
    4 * (K.remainder : ℚ) - (K.belowPulse : ℚ) =
      4 * seamGreedyFloorZ s + seamWordFloorError (K.below.extend false)
  rw [hnext, hZ]
  have hremQ : (K.remainder : ℚ) =
      (seamIntegerGreedyRemainder s : ℚ) := by exact_mod_cast hrem
  rw [hremQ]
  ring

/-- Exact three-rank floor slack.  Its only branch datum is the row modulo
three, because ranks three and six see the same exponent residue at their
respective Mersenne denominators. -/
theorem seamRankFloorError_two_three_six_eq (s : ℕ) :
    seamRankFloorError s 2 + seamRankFloorError s 3 +
        seamRankFloorError s 6 =
      if s % 3 = 0 then 31 / 63
      else if s % 3 = 1 then 61 / 63
      else 55 / 63 := by
  have hrange : s % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hmod : s % 3
  all_goals
    have hmod2 : (2 * s) % 2 = 0 := by omega
    have hmod3 : (2 * s) % 3 = (2 * (s % 3)) % 3 := by omega
    have hmod6 : (2 * s) % 6 = 2 * (s % 3) := by omega
    rw [seamRankFloorError_eq_modPow (by norm_num : 2 ≤ 2),
      seamRankFloorError_eq_modPow (by norm_num : 2 ≤ 3),
      seamRankFloorError_eq_modPow (by norm_num : 2 ≤ 6),
      hmod2, hmod3, hmod6, hmod]
    norm_num

/-- The forced `2,3,6` ranks give a concrete lower bound for the exact
false-extension slack which appears in the middle landing identity. -/
theorem seamRankFloorError_two_three_six_le_nextFloorError
    (s : ℕ) (hs : 13 ≤ s) :
    seamRankFloorError (s + 1) 2 + seamRankFloorError (s + 1) 3 +
        seamRankFloorError (s + 1) 6 ≤
      seamWordFloorError ((seamGreedyWord s).extend false) := by
  classical
  have hmem := two_three_six_mem_seamGreedySupport s hs
  unfold seamWordFloorError
  rw [seamWordSupport_extend_false (by omega : 3 ≤ s)]
  calc
    seamRankFloorError (s + 1) 2 + seamRankFloorError (s + 1) 3 +
          seamRankFloorError (s + 1) 6 =
        ∑ d ∈ ({2, 3, 6} : Finset ℕ),
          seamRankFloorError (s + 1) d := by
            norm_num [Finset.sum_insert]
            ring
    _ ≤ ∑ d ∈ seamWordSupport (seamGreedyWord s),
          seamRankFloorError (s + 1) d := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exact hmem.1
        · exact hmem.2.1
        · exact hmem.2.2
      · intro d hd hdnot
        exact seamRankFloorError_nonneg
          (by have := (seamWordSupport_below hd).1; omega)

/-- Exact final-cell routing for the first surviving middle charge.  The
analytic socket in `HalfCylinderFinalMiddleCellEscape` says charge `-2`
forces the lazy coefficient tail below two; the four-row `2,3,6` sieve above
forces it above two in the other residue classes. -/
theorem finalMiddleCell_neg_two_forces_mod_three_two
    (D : ℕ) (hD13 : 13 ≤ D)
    (hone : 1 ∉
      (↑(seamWordSupport (seamGreedyWord D)) : Set ℕ) ∪ Set.Ioi D)
    (hseries :
      erdosSupportSeries 2
          ((↑(seamWordSupport (seamGreedyWord D)) : Set ℕ) ∪ Set.Ioi D) <
        (1 : ℝ) / 2)
    (hcell :
      producerCarry
          (insert D
            (↑(seamWordSupport (seamGreedyWord D)) : Set ℕ)) D = -2) :
    D % 3 = 2 := by
  let U : Set ℕ := ↑(seamWordSupport (seamGreedyWord D))
  have hU : U ⊆ Set.Iio D := by
    intro d hd
    exact (seamWordSupport_below hd).2
  have hmem := two_three_six_mem_seamGreedySupport D hD13
  by_contra hmod
  have hlower :
      2 < binaryCoeffTail (supportCoeff (U ∪ Set.Ioi D)) (2 * D + 2) :=
    two_lt_binaryCoeffTail_union_Ioi_of_forced_two_three_six
      U D hD13 hU hmem.1 hmem.2.1 hmem.2.2 hmod
  have hupper :
      binaryCoeffTail (supportCoeff (U ∪ Set.Ioi D)) (2 * D + 2) < 2 := by
    apply binaryCoeffTail_union_Ioi_lt_two_of_producerCarry_eq_neg_two
      U D (by omega) hU
    · simpa [U] using hone
    · simpa [U] using hseries
    · simpa [U] using hcell
  linarith

/-- Pulse remaining after deleting the three forced low ranks. -/
def seamResidualPulse236 (s : ℕ) : ℕ :=
  ∑ d ∈ (((seamWordSupport (seamGreedyWord s)).erase 2).erase 3).erase 6,
    rowPulse s d

/-- In the residue class `s+1 ≡ 0 (mod 3)`, each forced rank contributes
exactly one pulse unit, so the total pulse is three plus the residual pulse. -/
theorem wordPulse_eq_three_add_seamResidualPulse236
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0) :
    wordPulse s (seamGreedyWord s).toNatWord =
      3 + seamResidualPulse236 s := by
  classical
  let S := seamWordSupport (seamGreedyWord s)
  have hmem := two_three_six_mem_seamGreedySupport s hs
  have h2 : 2 ∈ S := by simpa [S] using hmem.1
  have h3 : 3 ∈ S.erase 2 := by
    exact Finset.mem_erase.mpr ⟨by norm_num, by simpa [S] using hmem.2.1⟩
  have h6 : 6 ∈ (S.erase 2).erase 3 := by
    exact Finset.mem_erase.mpr
      ⟨by norm_num, Finset.mem_erase.mpr
        ⟨by norm_num, by simpa [S] using hmem.2.2⟩⟩
  have hthree : 3 ∣ s + 1 := Nat.dvd_iff_mod_eq_zero.mpr hmod
  have hsix : 6 ∣ 2 * s + 2 := by
    obtain ⟨k, hk⟩ := hthree
    refine ⟨k, ?_⟩
    omega
  have hthreeEven : 3 ∣ 2 * s + 2 := dvd_trans (by norm_num : 3 ∣ 6) hsix
  have htwoEven : 2 ∣ 2 * s + 2 := by omega
  have htwoOdd : ¬ 2 ∣ 2 * s + 1 := by omega
  have hthreeOdd : ¬ 3 ∣ 2 * s + 1 := by
    intro hbad
    have hevenmod := Nat.dvd_iff_mod_eq_zero.mp hthreeEven
    have hbadmod := Nat.dvd_iff_mod_eq_zero.mp hbad
    omega
  have hsixOdd : ¬ 6 ∣ 2 * s + 1 := by omega
  have hp2 : rowPulse s 2 = 1 := by
    simp [rowPulse, htwoEven, htwoOdd]
  have hp3 : rowPulse s 3 = 1 := by
    simp [rowPulse, hthreeEven, hthreeOdd]
  have hp6 : rowPulse s 6 = 1 := by
    simp [rowPulse, hsix, hsixOdd]
  rw [wordPulse_eq_sum_seamWordSupport]
  change (∑ d ∈ S, rowPulse s d) = _
  calc
    (∑ d ∈ S, rowPulse s d) =
        rowPulse s 2 + ∑ d ∈ S.erase 2, rowPulse s d :=
      (Finset.add_sum_erase _ _ h2).symm
    _ = rowPulse s 2 + rowPulse s 3 +
          ∑ d ∈ (S.erase 2).erase 3, rowPulse s d := by
      rw [← Finset.add_sum_erase _ _ h3]
      omega
    _ = rowPulse s 2 + rowPulse s 3 + rowPulse s 6 +
          ∑ d ∈ ((S.erase 2).erase 3).erase 6, rowPulse s d := by
      rw [← Finset.add_sum_erase _ _ h6]
      omega
    _ = 3 + seamResidualPulse236 s := by
      rw [hp2, hp3, hp6]
      simp [seamResidualPulse236, S]

/-- Charge `-1` fixes the seam pulse to the residue class one modulo four.
This is the exact arithmetic information hidden by the affine carry formula. -/
theorem wordPulse_mod_four_eq_one_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 5 ≤ s)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    wordPulse s (seamGreedyWord s).toNatWord % 4 = 1 := by
  have hcarry := producerCarry_insert_seamWordSupport_eq
    hs (seamGreedyWord s)
  rw [hcell] at hcarry
  omega

/-- In the surviving `s ≡ 2 (mod 3)` phase, charge `-1` therefore forces
the pulse outside the mandatory `2,3,6` ranks to be two modulo four. -/
theorem seamResidualPulse236_mod_four_eq_two_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    seamResidualPulse236 s % 4 = 2 := by
  have hpulse := wordPulse_eq_three_add_seamResidualPulse236 s hs hmod
  have hpmod := wordPulse_mod_four_eq_one_of_producerCarry_eq_neg_one
    s (by omega) hcell
  omega

/-- Consequently a `-1` cell in that phase must contain at least two units
of genuinely additional boundary pulse beyond the forced low ranks. -/
theorem two_le_seamResidualPulse236_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    2 ≤ seamResidualPulse236 s := by
  have hres :=
    seamResidualPulse236_mod_four_eq_two_of_producerCarry_eq_neg_one
      s hs hmod hcell
  omega

/-- The residual pulse forced by a `-1` cell is carried by an actual selected
rank `d ≥ 7` on one of the two new incidence boundaries.  This consumes
`two_le_seamResidualPulse236_of_producerCarry_eq_neg_one` and feeds the next
divisor-incidence/tail sieve: the congruence obstruction is therefore not an
abstract pulse count but a concrete extra divisor of `2*s+1` or `2*s+2`. -/
theorem exists_high_boundary_divisor_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    ∃ d : ℕ,
      d ∈ seamWordSupport (seamGreedyWord s) ∧
        7 ≤ d ∧ d < s ∧ (d ∣ 2 * s + 1 ∨ d ∣ 2 * s + 2) := by
  classical
  let R := (((seamWordSupport (seamGreedyWord s)).erase 2).erase 3).erase 6
  have hres : 2 ≤ ∑ d ∈ R, rowPulse s d := by
    simpa [R, seamResidualPulse236] using
      two_le_seamResidualPulse236_of_producerCarry_eq_neg_one
        s hs hmod hcell
  have hexists : ∃ d ∈ R, 0 < rowPulse s d := by
    by_contra hnot
    have hzero : ∑ d ∈ R, rowPulse s d = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      exact Nat.eq_zero_of_not_pos fun hpos => hnot ⟨d, hd, hpos⟩
    omega
  obtain ⟨d, hdR, hdpulse⟩ := hexists
  have hdErase6 := Finset.mem_erase.mp hdR
  have hdErase3 := Finset.mem_erase.mp hdErase6.2
  have hdErase2 := Finset.mem_erase.mp hdErase3.2
  have hdmem : d ∈ seamWordSupport (seamGreedyWord s) := hdErase2.2
  have hdbounds := seamWordSupport_below hdmem
  have hskip := four_five_not_mem_seamGreedySupport s hs
  have hdne4 : d ≠ 4 := by
    intro hd4
    subst d
    exact hskip.1 hdmem
  have hdne5 : d ≠ 5 := by
    intro hd5
    subst d
    exact hskip.2 hdmem
  have hd7 : 7 ≤ d := by
    omega
  have hddiv : d ∣ 2 * s + 1 ∨ d ∣ 2 * s + 2 := by
    by_contra hnot
    rcases not_or.mp hnot with ⟨hodd, heven⟩
    simp [rowPulse, hodd, heven] at hdpulse
  exact ⟨d, hdmem, hd7, hdbounds.2, hddiv⟩

/-- The weighted residual pulse has the exact multiplicity dichotomy needed
by later tail sieves.  Either one selected high rank hits the odd boundary
`2*s+1` (and contributes pulse weight two), or at least two distinct selected
high ranks hit the even boundary `2*s+2` (each contributing weight one).
This refines the preceding existence theorem without incorrectly identifying
pulse magnitude with the number of selected ranks. -/
theorem high_boundary_divisor_dichotomy_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    (∃ d : ℕ,
        d ∈ seamWordSupport (seamGreedyWord s) ∧
          7 ≤ d ∧ d < s ∧ d ∣ 2 * s + 1) ∨
      ∃ d e : ℕ,
        d ∈ seamWordSupport (seamGreedyWord s) ∧
          e ∈ seamWordSupport (seamGreedyWord s) ∧
          7 ≤ d ∧ 7 ≤ e ∧ d < s ∧ e < s ∧ d ≠ e ∧
          d ∣ 2 * s + 2 ∧ e ∣ 2 * s + 2 := by
  classical
  let R := (((seamWordSupport (seamGreedyWord s)).erase 2).erase 3).erase 6
  have hres : 2 ≤ ∑ d ∈ R, rowPulse s d := by
    simpa [R, seamResidualPulse236] using
      two_le_seamResidualPulse236_of_producerCarry_eq_neg_one
        s hs hmod hcell
  have hskip := four_five_not_mem_seamGreedySupport s hs
  have hrank (d : ℕ) (hdR : d ∈ R) :
      d ∈ seamWordSupport (seamGreedyWord s) ∧ 7 ≤ d ∧ d < s := by
    have hdErase6 := Finset.mem_erase.mp hdR
    have hdErase3 := Finset.mem_erase.mp hdErase6.2
    have hdErase2 := Finset.mem_erase.mp hdErase3.2
    have hdmem : d ∈ seamWordSupport (seamGreedyWord s) := hdErase2.2
    have hdbounds := seamWordSupport_below hdmem
    have hdne4 : d ≠ 4 := by
      intro hd4
      subst d
      exact hskip.1 hdmem
    have hdne5 : d ≠ 5 := by
      intro hd5
      subst d
      exact hskip.2 hdmem
    exact ⟨hdmem, by omega, hdbounds.2⟩
  by_cases hodd : ∃ d ∈ R, d ∣ 2 * s + 1
  · obtain ⟨d, hdR, hddiv⟩ := hodd
    obtain ⟨hdmem, hd7, hdlt⟩ := hrank d hdR
    exact Or.inl ⟨d, hdmem, hd7, hdlt, hddiv⟩
  · have hexists : ∃ d ∈ R, 0 < rowPulse s d := by
      by_contra hnot
      have hzero : ∑ d ∈ R, rowPulse s d = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        exact Nat.eq_zero_of_not_pos fun hpos => hnot ⟨d, hd, hpos⟩
      omega
    obtain ⟨d, hdR, hdpulse⟩ := hexists
    have hdodd : ¬ d ∣ 2 * s + 1 := by
      intro hddiv
      exact hodd ⟨d, hdR, hddiv⟩
    have hdeven : d ∣ 2 * s + 2 := by
      by_contra hddiv
      simp [rowPulse, hdodd, hddiv] at hdpulse
    have hdpulse_eq : rowPulse s d = 1 := by
      simp [rowPulse, hdodd, hdeven]
    have hsecond : ∃ e ∈ R, e ≠ d ∧ e ∣ 2 * s + 2 := by
      by_contra hnone
      have heven_none : ∀ e ∈ R, e ≠ d → ¬ e ∣ 2 * s + 2 := by
        intro e heR hne hediv
        exact hnone ⟨e, heR, hne, hediv⟩
      have hsumErase : ∑ e ∈ R.erase d, rowPulse s e = 0 := by
        apply Finset.sum_eq_zero
        intro e heErase
        have heData := Finset.mem_erase.mp heErase
        have heodd : ¬ e ∣ 2 * s + 1 := by
          intro hediv
          exact hodd ⟨e, heData.2, hediv⟩
        have heeven := heven_none e heData.2 heData.1
        simp [rowPulse, heodd, heeven]
      have hsum : ∑ e ∈ R, rowPulse s e = 1 := by
        calc
          ∑ e ∈ R, rowPulse s e =
              rowPulse s d + ∑ e ∈ R.erase d, rowPulse s e :=
            (Finset.add_sum_erase _ _ hdR).symm
          _ = 1 := by rw [hdpulse_eq, hsumErase]
      omega
    obtain ⟨e, heR, hene, hediv⟩ := hsecond
    obtain ⟨hdmem, hd7, hdlt⟩ := hrank d hdR
    obtain ⟨hemem, he7, helt⟩ := hrank e heR
    exact Or.inr
      ⟨d, e, hdmem, hemem, hd7, he7, hdlt, helt, hene.symm, hdeven, hediv⟩

/-- The boundary divisor exposed by
`exists_high_boundary_divisor_of_producerCarry_eq_neg_one` reappears as a
second selected divisor at a definite future row of the lazy `Ioi` tail.
This is the local bridge from the residual-pulse sieve to coefficient-tail
lower bounds: a hypothetical `-1` cell cannot leave every future coefficient
at its self-divisor baseline. -/
theorem exists_future_coeff_bump_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    ∃ d : ℕ,
      7 ≤ d ∧ d < s ∧
        ((d ∣ 2 * s + 1 ∧
            2 ≤ supportCoeff
              ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                Set.Ioi s)
              (2 * s + 1 + d)) ∨
          (d ∣ 2 * s + 2 ∧
            2 ≤ supportCoeff
              ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                Set.Ioi s)
              (2 * s + 2 + d))) := by
  classical
  obtain ⟨d, hdmem, hd7, hdlt, hdiv | hdiv⟩ :=
    exists_high_boundary_divisor_of_producerCarry_eq_neg_one
      s hs hmod hcell
  · refine ⟨d, hd7, hdlt, Or.inl ⟨hdiv, ?_⟩⟩
    let B : Set ℕ :=
      (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪ Set.Ioi s
    let n := 2 * s + 1 + d
    have hdn : d ∣ n := by
      simpa [n] using dvd_add hdiv (dvd_refl d)
    have hforced := card_le_supportCoeff_of_forced_divisors
      B ({d, n} : Finset ℕ) n (by dsimp [n]; omega)
      (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact Set.mem_union_left _ hdmem
        · exact Set.mem_union_right _ (Set.mem_Ioi.mpr (by dsimp [n]; omega)))
      (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hdn
        · exact dvd_rfl)
    have hdne : d ≠ n := by
      dsimp [n]
      omega
    have hcard : ({d, n} : Finset ℕ).card = 2 := by
      simp [hdne]
    simpa [B, n] using (show 2 ≤ supportCoeff B n by
      rwa [hcard] at hforced)
  · refine ⟨d, hd7, hdlt, Or.inr ⟨hdiv, ?_⟩⟩
    let B : Set ℕ :=
      (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪ Set.Ioi s
    let n := 2 * s + 2 + d
    have hdn : d ∣ n := by
      simpa [n] using dvd_add hdiv (dvd_refl d)
    have hforced := card_le_supportCoeff_of_forced_divisors
      B ({d, n} : Finset ℕ) n (by dsimp [n]; omega)
      (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact Set.mem_union_left _ hdmem
        · exact Set.mem_union_right _ (Set.mem_Ioi.mpr (by dsimp [n]; omega)))
      (by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with rfl | rfl
        · exact hdn
        · exact dvd_rfl)
    have hdne : d ≠ n := by
      dsimp [n]
      omega
    have hcard : ({d, n} : Finset ℕ).card = 2 := by
      simp [hdne]
    simpa [B, n] using (show 2 ≤ supportCoeff B n by
      rwa [hcard] at hforced)

/-- The future coefficient bump has a precise analytic price in the complete
tail after row `2*s+2`: an odd-boundary divisor contributes at offset `d-1`,
while an even-boundary divisor contributes at offset `d`.  This consumes the
local bump theorem together with the reusable one-row projection
`coeff_term_le_binaryCoeffTail`, and feeds the surviving `tail < 3` sieve
without hiding the selected rank inside an oversized finite window. -/
theorem exists_weighted_tail_bump_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    ∃ d : ℕ,
      7 ≤ d ∧ d < s ∧
        ((2 : ℝ) / (2 : ℝ) ^ (d - 1) ≤
            binaryCoeffTail
              (supportCoeff
                ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                  Set.Ioi s))
              (2 * s + 2) ∨
          (2 : ℝ) / (2 : ℝ) ^ d ≤
            binaryCoeffTail
              (supportCoeff
                ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                  Set.Ioi s))
              (2 * s + 2)) := by
  let B : Set ℕ :=
    (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪ Set.Ioi s
  obtain ⟨d, hd7, hdlt, ⟨_, hcoeff⟩ | ⟨_, hcoeff⟩⟩ :=
    exists_future_coeff_bump_of_producerCarry_eq_neg_one
      s hs hmod hcell
  · refine ⟨d, hd7, hdlt, Or.inl ?_⟩
    have hindex : 2 * s + 2 + (d - 2) + 1 = 2 * s + 1 + d := by
      omega
    have hexponent : d - 2 + 1 = d - 1 := by
      omega
    have hterm := coeff_term_le_binaryCoeffTail B (2 * s + 2) (d - 2)
    rw [hindex, hexponent] at hterm
    have hcast : (2 : ℝ) ≤ supportCoeff B (2 * s + 1 + d) := by
      exact_mod_cast hcoeff
    exact (div_le_div_of_nonneg_right hcast (by positivity)).trans hterm
  · refine ⟨d, hd7, hdlt, Or.inr ?_⟩
    have hindex : 2 * s + 2 + (d - 1) + 1 = 2 * s + 2 + d := by
      omega
    have hexponent : d - 1 + 1 = d := by
      omega
    have hterm := coeff_term_le_binaryCoeffTail B (2 * s + 2) (d - 1)
    rw [hindex, hexponent] at hterm
    have hcast : (2 : ℝ) ≤ supportCoeff B (2 * s + 2 + d) := by
      exact_mod_cast hcoeff
    exact (div_le_div_of_nonneg_right hcast (by positivity)).trans hterm

private theorem two_le_lazy_supportCoeff_add_of_selected_divisor
    {s d n : ℕ}
    (hdmem : d ∈ seamWordSupport (seamGreedyWord s))
    (hsn : s < n) (hddiv : d ∣ n) :
    2 ≤ supportCoeff
      ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪ Set.Ioi s)
      (n + d) := by
  classical
  let B : Set ℕ :=
    (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪ Set.Ioi s
  have hdn : d ∣ n + d := dvd_add hddiv (dvd_refl d)
  have hforced := card_le_supportCoeff_of_forced_divisors
    B ({d, n + d} : Finset ℕ) (n + d) (by omega)
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact Set.mem_union_left _ hdmem
      · exact Set.mem_union_right _ (Set.mem_Ioi.mpr (by omega)))
    (by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hdn
      · exact dvd_rfl)
  have hdne : d ≠ n + d := by omega
  have hdnot : d ∉ ({n + d} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hdne
  have hcard : ({d, n + d} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem hdnot]
    norm_num
  simpa [B] using (show 2 ≤ supportCoeff B (n + d) by
    rwa [hcard] at hforced)

private theorem two_le_lazy_supportCoeff_add_mul_of_selected_divisor
    {s d n : ℕ}
    (hdmem : d ∈ seamWordSupport (seamGreedyWord s))
    (hsn : s < n) (hddiv : d ∣ n) (j : ℕ) :
    2 ≤ supportCoeff
      ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪ Set.Ioi s)
      (n + (j + 1) * d) := by
  have hddiv' : d ∣ n + j * d :=
    dvd_add hddiv (dvd_mul_left d j)
  have h := two_le_lazy_supportCoeff_add_of_selected_divisor
    hdmem (by omega : s < n + j * d) hddiv'
  simpa [add_mul, add_assoc] using h

/-- The boundary-divisor dichotomy forces whole arithmetic-progression
channels in the lazy coefficient word, not merely the first coefficient
bump.  The odd boundary produces one infinite channel; otherwise the even
boundary produces two distinct infinite channels. -/
theorem infinite_coeff_channel_dichotomy_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    (∃ d : ℕ,
        7 ≤ d ∧ d < s ∧
          ∀ j : ℕ,
            2 ≤ supportCoeff
              ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                Set.Ioi s)
              (2 * s + 1 + (j + 1) * d)) ∨
      ∃ d e : ℕ,
        7 ≤ d ∧ 7 ≤ e ∧ d < s ∧ e < s ∧ d ≠ e ∧
          ∀ j : ℕ,
            2 ≤ supportCoeff
              ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                Set.Ioi s)
              (2 * s + 2 + (j + 1) * d) ∧
            2 ≤ supportCoeff
              ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                Set.Ioi s)
              (2 * s + 2 + (j + 1) * e) := by
  rcases high_boundary_divisor_dichotomy_of_producerCarry_eq_neg_one
      s hs hmod hcell with
    ⟨d, hdmem, hd7, hdlt, hddiv⟩ |
      ⟨d, e, hdmem, hemel, hd7, he7, hdlt, helt, hde, hddiv, hediv⟩
  · refine Or.inl ⟨d, hd7, hdlt, ?_⟩
    intro j
    exact two_le_lazy_supportCoeff_add_mul_of_selected_divisor
      hdmem (by omega : s < 2 * s + 1) hddiv j
  · refine Or.inr ⟨d, e, hd7, he7, hdlt, helt, hde, ?_⟩
    intro j
    exact ⟨
      two_le_lazy_supportCoeff_add_mul_of_selected_divisor
        hdmem (by omega : s < 2 * s + 2) hddiv j,
      two_le_lazy_supportCoeff_add_mul_of_selected_divisor
        hemel (by omega : s < 2 * s + 2) hediv j⟩

private theorem two_coeff_terms_le_binaryCoeffTail
    (A : Set ℕ) (N j k : ℕ) (hjk : j ≠ k) :
    (supportCoeff A (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) +
        (supportCoeff A (N + k + 1) : ℝ) / (2 : ℝ) ^ (k + 1) ≤
      binaryCoeffTail (supportCoeff A) N := by
  have hsum : Summable (fun r : ℕ ↦
      (supportCoeff A (N + r + 1) : ℝ) / (2 : ℝ) ^ (r + 1)) :=
    summable_coeff_shift_tail 2 N (supportCoeff A)
      (by norm_num) (supportCoeff_le_self A)
  unfold binaryCoeffTail
  have hjnot : j ∉ ({k} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hjk
  calc
    (supportCoeff A (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1) +
          (supportCoeff A (N + k + 1) : ℝ) / (2 : ℝ) ^ (k + 1) =
        ∑ r ∈ ({j, k} : Finset ℕ),
          (supportCoeff A (N + r + 1) : ℝ) / (2 : ℝ) ^ (r + 1) := by
            rw [Finset.sum_insert hjnot, Finset.sum_singleton]
    _ ≤ ∑' r : ℕ,
          (supportCoeff A (N + r + 1) : ℝ) / (2 : ℝ) ^ (r + 1) :=
      hsum.sum_le_tsum ({j, k} : Finset ℕ) (fun r _ ↦ by positivity)

/-- **Two-channel spend of the boundary-divisor dichotomy.**  A hypothetical
final producer cell `-1` has one of two quantitatively distinct consequences
for the complete lazy coefficient tail.  An odd-boundary divisor contributes
one weight-two channel at offset `d-1`.  Otherwise two distinct even-boundary
divisors contribute two separate weight-two channels, and their dyadic prices
add inside the same tail.

Unlike `exists_weighted_tail_bump_of_producerCarry_eq_neg_one`, the even case
does not discard the second divisor forced by the exact residual pulse. -/
theorem weighted_tail_channel_dichotomy_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    (∃ d : ℕ,
        7 ≤ d ∧ d < s ∧
          (2 : ℝ) / (2 : ℝ) ^ (d - 1) ≤
            binaryCoeffTail
              (supportCoeff
                ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                  Set.Ioi s))
              (2 * s + 2)) ∨
      ∃ d e : ℕ,
        7 ≤ d ∧ 7 ≤ e ∧ d < s ∧ e < s ∧ d ≠ e ∧
          (2 : ℝ) / (2 : ℝ) ^ d + (2 : ℝ) / (2 : ℝ) ^ e ≤
            binaryCoeffTail
              (supportCoeff
                ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                  Set.Ioi s))
              (2 * s + 2) := by
  let B : Set ℕ :=
    (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪ Set.Ioi s
  rcases high_boundary_divisor_dichotomy_of_producerCarry_eq_neg_one
      s hs hmod hcell with
    ⟨d, hdmem, hd7, hdlt, hddiv⟩ |
      ⟨d, e, hdmem, hemel, hd7, he7, hdlt, helt, hde, hddiv, hediv⟩
  · have hcoeff := two_le_lazy_supportCoeff_add_of_selected_divisor
      hdmem (by omega : s < 2 * s + 1) hddiv
    have hterm := coeff_term_le_binaryCoeffTail B (2 * s + 2) (d - 2)
    have hindex : 2 * s + 2 + (d - 2) + 1 = 2 * s + 1 + d := by omega
    have hexponent : d - 2 + 1 = d - 1 := by omega
    rw [hindex, hexponent] at hterm
    have hcast : (2 : ℝ) ≤ supportCoeff B (2 * s + 1 + d) := by
      exact_mod_cast hcoeff
    refine Or.inl ⟨d, hd7, hdlt, ?_⟩
    exact (div_le_div_of_nonneg_right hcast (by positivity)).trans hterm
  · have hdcoeff := two_le_lazy_supportCoeff_add_of_selected_divisor
      hdmem (by omega : s < 2 * s + 2) hddiv
    have hecoeff := two_le_lazy_supportCoeff_add_of_selected_divisor
      hemel (by omega : s < 2 * s + 2) hediv
    have hoffsets : d - 1 ≠ e - 1 := by omega
    have hpair := two_coeff_terms_le_binaryCoeffTail
      B (2 * s + 2) (d - 1) (e - 1) hoffsets
    have hdindex : 2 * s + 2 + (d - 1) + 1 = 2 * s + 2 + d := by omega
    have heindex : 2 * s + 2 + (e - 1) + 1 = 2 * s + 2 + e := by omega
    have hdexponent : d - 1 + 1 = d := by omega
    have heexponent : e - 1 + 1 = e := by omega
    rw [hdindex, heindex, hdexponent, heexponent] at hpair
    have hdcast : (2 : ℝ) ≤ supportCoeff B (2 * s + 2 + d) := by
      exact_mod_cast hdcoeff
    have hecast : (2 : ℝ) ≤ supportCoeff B (2 * s + 2 + e) := by
      exact_mod_cast hecoeff
    refine Or.inr ⟨d, e, hd7, he7, hdlt, helt, hde, ?_⟩
    exact (add_le_add
      (div_le_div_of_nonneg_right hdcast (by positivity))
      (div_le_div_of_nonneg_right hecast (by positivity))).trans hpair

/-- **Iterated spend of the odd boundary channel.**  The odd-boundary arm of
`infinite_coeff_channel_dichotomy_of_producerCarry_eq_neg_one` contributes at
least two distinct weight-two coefficients to the same complete dyadic tail,
at the first two positive multiples of its selected divisor.  The even arm
retains the two distinct divisor channels already forced by the residual
pulse.  Thus neither arm is reduced to a single isolated coefficient bump. -/
theorem iterated_weighted_tail_channel_dichotomy_of_producerCarry_eq_neg_one
    (s : ℕ) (hs : 13 ≤ s) (hmod : (s + 1) % 3 = 0)
    (hcell : producerCarry
        (insert s
          (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ)) s = -1) :
    (∃ d : ℕ,
        7 ≤ d ∧ d < s ∧
          (2 : ℝ) / (2 : ℝ) ^ (d - 1) +
              (2 : ℝ) / (2 : ℝ) ^ (2 * d - 1) ≤
            binaryCoeffTail
              (supportCoeff
                ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                  Set.Ioi s))
              (2 * s + 2)) ∨
      ∃ d e : ℕ,
        7 ≤ d ∧ 7 ≤ e ∧ d < s ∧ e < s ∧ d ≠ e ∧
          (2 : ℝ) / (2 : ℝ) ^ d + (2 : ℝ) / (2 : ℝ) ^ e ≤
            binaryCoeffTail
              (supportCoeff
                ((↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪
                  Set.Ioi s))
              (2 * s + 2) := by
  let B : Set ℕ :=
    (↑(seamWordSupport (seamGreedyWord s)) : Set ℕ) ∪ Set.Ioi s
  rcases high_boundary_divisor_dichotomy_of_producerCarry_eq_neg_one
      s hs hmod hcell with
    ⟨d, hdmem, hd7, hdlt, hddiv⟩ |
      ⟨d, e, hdmem, hemel, hd7, he7, hdlt, helt, hde, hddiv, hediv⟩
  · have hcoeff0 : 2 ≤ supportCoeff B (2 * s + 1 + d) := by
      simpa [B] using
        (two_le_lazy_supportCoeff_add_mul_of_selected_divisor
          hdmem (by omega : s < 2 * s + 1) hddiv 0)
    have hcoeff1 : 2 ≤ supportCoeff B (2 * s + 1 + 2 * d) := by
      simpa [B] using
        (two_le_lazy_supportCoeff_add_mul_of_selected_divisor
          hdmem (by omega : s < 2 * s + 1) hddiv 1)
    have hoffsets : d - 2 ≠ 2 * d - 2 := by omega
    have hpair := two_coeff_terms_le_binaryCoeffTail
      B (2 * s + 2) (d - 2) (2 * d - 2) hoffsets
    have hindex0 : 2 * s + 2 + (d - 2) + 1 = 2 * s + 1 + d := by omega
    have hindex1 : 2 * s + 2 + (2 * d - 2) + 1 =
        2 * s + 1 + 2 * d := by omega
    have hexponent0 : d - 2 + 1 = d - 1 := by omega
    have hexponent1 : 2 * d - 2 + 1 = 2 * d - 1 := by omega
    rw [hindex0, hindex1, hexponent0, hexponent1] at hpair
    have hcast0 : (2 : ℝ) ≤ supportCoeff B (2 * s + 1 + d) := by
      exact_mod_cast hcoeff0
    have hcast1 : (2 : ℝ) ≤ supportCoeff B (2 * s + 1 + 2 * d) := by
      exact_mod_cast hcoeff1
    refine Or.inl ⟨d, hd7, hdlt, ?_⟩
    exact (add_le_add
      (div_le_div_of_nonneg_right hcast0 (by positivity))
      (div_le_div_of_nonneg_right hcast1 (by positivity))).trans hpair
  · have hdcoeff := two_le_lazy_supportCoeff_add_of_selected_divisor
      hdmem (by omega : s < 2 * s + 2) hddiv
    have hecoeff := two_le_lazy_supportCoeff_add_of_selected_divisor
      hemel (by omega : s < 2 * s + 2) hediv
    have hoffsets : d - 1 ≠ e - 1 := by omega
    have hpair := two_coeff_terms_le_binaryCoeffTail
      B (2 * s + 2) (d - 1) (e - 1) hoffsets
    have hdindex : 2 * s + 2 + (d - 1) + 1 = 2 * s + 2 + d := by omega
    have heindex : 2 * s + 2 + (e - 1) + 1 = 2 * s + 2 + e := by omega
    have hdexponent : d - 1 + 1 = d := by omega
    have heexponent : e - 1 + 1 = e := by omega
    rw [hdindex, heindex, hdexponent, heexponent] at hpair
    have hdcast : (2 : ℝ) ≤ supportCoeff B (2 * s + 2 + d) := by
      exact_mod_cast hdcoeff
    have hecast : (2 : ℝ) ≤ supportCoeff B (2 * s + 2 + e) := by
      exact_mod_cast hecoeff
    refine Or.inr ⟨d, e, hd7, he7, hdlt, helt, hde, ?_⟩
    exact (add_le_add
      (div_le_div_of_nonneg_right hdcast (by positivity))
      (div_le_div_of_nonneg_right hecast (by positivity))).trans hpair

/-! ## The exact middle-producer tail -/

/-- The complete binary incidence tail of the terminal-augmented below word
is exactly the floor error after extending the word by `false`, plus the
new terminal rank's floor error.  This is an identity, not a majorant. -/
theorem binaryCoeffTail_insert_seamBelowSupport_eq_nextFloorError
    (s : ℕ) (hs : 5 ≤ s) :
    binaryCoeffTail
        (supportCoeff
          (insert s
            (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)))
        (2 * s + 2) =
      ((seamWordFloorError ((seamAdjacentCut s hs).below.extend false) +
          seamRankFloorError (s + 1) s : ℚ) : ℝ) := by
  classical
  let K := seamAdjacentCut s hs
  let P : Finset ℕ := seamWordSupport K.below
  let A : Set ℕ := insert s (↑P : Set ℕ)
  have hsnot : s ∉ P := by
    intro hmem
    exact (Nat.lt_irrefl s) (seamWordSupport_below hmem).2
  have hone : 1 ∉ A := by
    simpa [A, P] using one_not_mem_insert_seamWordSupport hs K.below
  have hA : A ⊆ Set.Iic s := by
    simpa [A, P] using insert_seamWordSupport_subset_Iic K.below
  have hseries :
      erdosSupportSeries 2 A =
        ((seamWordRationalSum K.below + mersenneWeightRat s : ℚ) : ℝ) := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    have hcoe : (↑(insert s P) : Set ℕ) = A := by
      ext d
      simp [A]
    rw [← hcoe]
    rw [positiveMersenneSupportValue_insert hsnot,
      positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    change mersenneWeight s + ((seamWordRationalSum K.below : ℚ) : ℝ) = _
    rw [← cast_mersenneWeightRat]
    push_cast
    ring
  have hleft :
      (1 : ℝ) / 2 - erdosSupportSeries 2 A =
        ((seamWordRationalRemainder K.below - mersenneWeightRat s : ℚ) : ℝ) := by
    rw [hseries]
    unfold seamWordRationalRemainder
    push_cast
    ring
  have hcarry :
      producerCarry A s =
        4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 := by
    simpa [A, P, K] using
      producerCarry_insert_seamBelowSupport_eq_middleCoordinate s hs
  have hrem :
      seamWordRationalRemainder K.below =
        ((2 : ℚ) ^ s + seamGreedyFloorZ s) / (4 : ℚ) ^ s := by
    simpa [K, seamAdjacentCut, seamGreedyFloorZ] using
      seamWordRationalRemainder_eq_pow_add_floorZ_div
        (by omega : 1 ≤ s) K.below
  have hfloor := seamWordFloorError_extend_false (by omega : 3 ≤ s) K.below
  have hrank := seamRankFloorError_newRank (s := s) (by omega : 3 ≤ s)
  have hKremainder :
      K.remainder = seamIntegerGreedyRemainder s := by
    simpa [K] using seamAdjacentCut_remainder hs
  have hKerror :
      seamGreedyFloorError s = seamWordFloorError K.below := by
    rfl
  have hKpulse :
      wordPulse s K.below.toNatWord = K.belowPulse := by
    rfl
  have hscale :
      (4 : ℚ) ^ (s + 1) *
          (seamWordRationalRemainder K.below - mersenneWeightRat s) =
        ((producerCarry A s : ℤ) : ℚ) -
          (seamWordFloorError (K.below.extend false) +
            seamRankFloorError (s + 1) s) := by
    rw [hcarry, hrem, hfloor, hrank,
      seamGreedyFloorZ_eq_remainder_sub_error s hs,
      ← hKremainder, hKerror, hKpulse]
    unfold mersenneWeightRat
    change
      (4 : ℚ) ^ (s + 1) *
          (((2 : ℚ) ^ s +
              ((K.remainder : ℚ) - seamWordFloorError K.below)) /
            (4 : ℚ) ^ s -
            1 / ((2 : ℚ) ^ s - 1)) =
        ((4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 : ℤ) : ℚ) -
          (4 * seamWordFloorError K.below - (K.belowPulse : ℚ) +
            4 / ((2 : ℚ) ^ s - 1))
    push_cast
    rw [pow_succ, four_pow_eq_two_pow_sq]
    have hden : (2 : ℚ) ^ s - 1 ≠ 0 := by
      have : (1 : ℚ) < (2 : ℚ) ^ s :=
        one_lt_pow₀ (by norm_num) (by omega)
      linarith
    field_simp
    ring
  have hres := producerCarry_residual_identity A s hone hA
  rw [hleft] at hres
  have hden : (2 : ℝ) ^ (2 * s + 2) ≠ 0 := by positivity
  have hnum := (eq_div_iff hden).mp hres
  have hpow : (2 : ℝ) ^ (2 * s + 2) = (4 : ℝ) ^ (s + 1) := by
    rw [show 2 * s + 2 = 2 * (s + 1) by omega, pow_mul]
    norm_num
  have hscaleR :
      (4 : ℝ) ^ (s + 1) *
          (((seamWordRationalRemainder K.below - mersenneWeightRat s : ℚ) : ℝ)) =
        (producerCarry A s : ℝ) -
          ((seamWordFloorError (K.below.extend false) +
            seamRankFloorError (s + 1) s : ℚ) : ℝ) := by
    exact_mod_cast hscale
  change binaryCoeffTail (supportCoeff A) (2 * s + 2) = _
  rw [hpow] at hnum
  linarith

/-- Exact middle-producer safety criterion in the corrected seam coordinate:
the complete tail is smaller than the affine carry precisely when the
rational take threshold is strictly below `Z = remainder - floorError`. -/
theorem middleProducer_tail_lt_carry_iff_takeThreshold_lt_floorZ
    (s : ℕ) (hs : 5 ≤ s) :
    binaryCoeffTail
        (supportCoeff
          (insert s
            (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)))
        (2 * s + 2) <
        (producerCarry
          (insert s
            (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ))
          s : ℝ) ↔
      seamTakeThreshold s < seamGreedyFloorZ s := by
  classical
  let K := seamAdjacentCut s hs
  let A : Set ℕ :=
    insert s (↑(seamWordSupport K.below) : Set ℕ)
  have htail :
      binaryCoeffTail (supportCoeff A) (2 * s + 2) =
        ((seamWordFloorError (K.below.extend false) +
          seamRankFloorError (s + 1) s : ℚ) : ℝ) := by
    simpa [A, K] using
      binaryCoeffTail_insert_seamBelowSupport_eq_nextFloorError s hs
  have hcarry :
      producerCarry A s =
        4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 := by
    simpa [A, K] using
      producerCarry_insert_seamBelowSupport_eq_middleCoordinate s hs
  have hfloor := seamWordFloorError_extend_false (by omega : 3 ≤ s) K.below
  have hrank := seamRankFloorError_newRank (s := s) (by omega : 3 ≤ s)
  have hKremainder :
      K.remainder = seamIntegerGreedyRemainder s := by
    simpa [K] using seamAdjacentCut_remainder hs
  have hKerror :
      seamGreedyFloorError s = seamWordFloorError K.below := by
    rfl
  have hKpulse :
      wordPulse s K.below.toNatWord = K.belowPulse := by
    rfl
  have hden : (2 : ℚ) ^ s - 1 ≠ 0 := by
    have : (1 : ℚ) < (2 : ℚ) ^ s :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hthreshold :
      seamTakeThreshold s = 1 + 1 / ((2 : ℚ) ^ s - 1) := by
    unfold seamTakeThreshold
    field_simp
    ring
  have hrat :
      seamWordFloorError (K.below.extend false) +
            seamRankFloorError (s + 1) s <
          ((producerCarry A s : ℤ) : ℚ) ↔
        seamTakeThreshold s < seamGreedyFloorZ s := by
    rw [hfloor, hrank, hcarry]
    push_cast
    rw [hKpulse, hthreshold,
      seamGreedyFloorZ_eq_remainder_sub_error s hs,
      ← hKremainder, hKerror]
    have hfour_div :
        4 / ((2 : ℚ) ^ s - 1) = 4 * (1 / ((2 : ℚ) ^ s - 1)) := by
      ring
    constructor <;> intro h
    · rw [hfour_div] at h
      linarith
    · rw [hfour_div]
      linarith
  change binaryCoeffTail (supportCoeff A) (2 * s + 2) <
      (producerCarry A s : ℝ) ↔ _
  rw [htail]
  constructor
  · intro h
    exact hrat.mp (by exact_mod_cast h)
  · intro h
    exact_mod_cast hrat.mpr h

/-- Exact signed margin behind both strict producer comparisons.  After the
pulse cancels, the carry-minus-tail margin is four times the corrected seam
coordinate's distance above the rational take threshold. -/
theorem middleProducer_carry_sub_tail_eq_four_mul_floorZ_sub_threshold
    (s : ℕ) (hs : 5 ≤ s) :
    (producerCarry
        (insert s
          (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ))
        s : ℝ) -
        binaryCoeffTail
          (supportCoeff
            (insert s
              (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)))
          (2 * s + 2) =
      4 * (((seamGreedyFloorZ s - seamTakeThreshold s : ℚ) : ℝ)) := by
  classical
  let K := seamAdjacentCut s hs
  let A : Set ℕ :=
    insert s (↑(seamWordSupport K.below) : Set ℕ)
  have htail :
      binaryCoeffTail (supportCoeff A) (2 * s + 2) =
        ((seamWordFloorError (K.below.extend false) +
          seamRankFloorError (s + 1) s : ℚ) : ℝ) := by
    simpa [A, K] using
      binaryCoeffTail_insert_seamBelowSupport_eq_nextFloorError s hs
  have hcarry :
      producerCarry A s =
        4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 := by
    simpa [A, K] using
      producerCarry_insert_seamBelowSupport_eq_middleCoordinate s hs
  have hfloor := seamWordFloorError_extend_false (by omega : 3 ≤ s) K.below
  have hrank := seamRankFloorError_newRank (s := s) (by omega : 3 ≤ s)
  have hKremainder :
      K.remainder = seamIntegerGreedyRemainder s := by
    simpa [K] using seamAdjacentCut_remainder hs
  have hKerror :
      seamGreedyFloorError s = seamWordFloorError K.below := by
    rfl
  have hKpulse :
      wordPulse s K.below.toNatWord = K.belowPulse := by
    rfl
  have hden : (2 : ℚ) ^ s - 1 ≠ 0 := by
    have : (1 : ℚ) < (2 : ℚ) ^ s :=
      one_lt_pow₀ (by norm_num) (by omega)
    linarith
  have hthreshold :
      seamTakeThreshold s = 1 + 1 / ((2 : ℚ) ^ s - 1) := by
    unfold seamTakeThreshold
    field_simp
    ring
  have hrat :
      ((producerCarry A s : ℤ) : ℚ) -
          (seamWordFloorError (K.below.extend false) +
            seamRankFloorError (s + 1) s) =
        4 * (seamGreedyFloorZ s - seamTakeThreshold s) := by
    rw [hcarry, hfloor, hrank]
    push_cast
    rw [hKpulse, hthreshold,
      seamGreedyFloorZ_eq_remainder_sub_error s hs,
      ← hKremainder, hKerror]
    ring
  change (producerCarry A s : ℝ) -
      binaryCoeffTail (supportCoeff A) (2 * s + 2) = _
  rw [htail]
  exact_mod_cast hrat

/-- The reverse strict comparison is the reverse strict threshold
comparison; no equality case is hidden in the tail formula. -/
theorem middleProducer_carry_lt_tail_iff_floorZ_lt_takeThreshold
    (s : ℕ) (hs : 5 ≤ s) :
    (producerCarry
        (insert s
          (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ))
        s : ℝ) <
        binaryCoeffTail
          (supportCoeff
            (insert s
              (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)))
          (2 * s + 2) ↔
      seamGreedyFloorZ s < seamTakeThreshold s := by
  have hmargin :=
    middleProducer_carry_sub_tail_eq_four_mul_floorZ_sub_threshold s hs
  constructor
  · intro h
    have hneg :
        (producerCarry
            (insert s
              (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ))
            s : ℝ) -
            binaryCoeffTail
              (supportCoeff
                (insert s
                  (↑(seamWordSupport
                    (seamAdjacentCut s hs).below) : Set ℕ)))
              (2 * s + 2) < 0 := sub_neg.mpr h
    rw [hmargin] at hneg
    have hcast :
        (((seamGreedyFloorZ s - seamTakeThreshold s : ℚ) : ℝ)) < 0 := by
      nlinarith
    have hrat :
        seamGreedyFloorZ s - seamTakeThreshold s < 0 := by
      exact_mod_cast hcast
    exact sub_neg.mp hrat
  · intro h
    have hrat : seamGreedyFloorZ s - seamTakeThreshold s < 0 := sub_neg.mpr h
    have hcast :
        (((seamGreedyFloorZ s - seamTakeThreshold s : ℚ) : ℝ)) < 0 := by
      exact_mod_cast hrat
    have hneg :
        4 * (((seamGreedyFloorZ s - seamTakeThreshold s : ℚ) : ℝ)) < 0 := by
      nlinarith
    rw [← hmargin] at hneg
    exact sub_neg.mp hneg

/-- Equality with the terminal take threshold cannot occur: it would make
the terminal-augmented finite Mersenne support sum exactly to `1/2`, which
is excluded by the odd-denominator finite-support theorem. -/
theorem seamGreedyFloorZ_ne_takeThreshold
    (s : ℕ) (hs : 5 ≤ s) :
    seamGreedyFloorZ s ≠ seamTakeThreshold s := by
  classical
  let K := seamAdjacentCut s hs
  let P : Finset ℕ := seamWordSupport K.below
  let F : Finset ℕ := insert s P
  let A : Set ℕ := insert s (↑P : Set ℕ)
  have h0 : 0 ∉ F := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · omega
    · have hbounds := seamWordSupport_below (by simpa [P] using h)
      omega
  have hone : 1 ∉ A := by
    simpa [A, P] using one_not_mem_insert_seamWordSupport hs K.below
  have hA : A ⊆ Set.Iic s := by
    simpa [A, P] using insert_seamWordSupport_subset_Iic K.below
  intro heq
  have hmargin :=
    middleProducer_carry_sub_tail_eq_four_mul_floorZ_sub_threshold s hs
  change (producerCarry A s : ℝ) -
      binaryCoeffTail (supportCoeff A) (2 * s + 2) =
        4 * (((seamGreedyFloorZ s - seamTakeThreshold s : ℚ) : ℝ))
    at hmargin
  rw [heq, sub_self] at hmargin
  norm_num at hmargin
  have hres := producerCarry_residual_identity A s hone hA
  rw [hmargin] at hres
  norm_num at hres
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
    linarith
  have hvalue :
      positiveMersenneSupportValue (↑F : Set ℕ) = (1 : ℝ) / 2 := by
    rw [positiveMersenneSupportValue_eq_erdosSupportSeries]
    simpa [A, F, P] using hseries
  exact positiveMersenneSupportValue_coe_finset_ne_half h0 hvalue

/-- Because the threshold equality is impossible, the producer-tail escape
is exactly the non-strict corrected take condition. -/
theorem middleProducer_tail_lt_carry_iff_takeThreshold_le_floorZ
    (s : ℕ) (hs : 5 ≤ s) :
    binaryCoeffTail
        (supportCoeff
          (insert s
            (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)))
        (2 * s + 2) <
        (producerCarry
          (insert s
            (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ))
          s : ℝ) ↔
      seamTakeThreshold s ≤ seamGreedyFloorZ s := by
  rw [middleProducer_tail_lt_carry_iff_takeThreshold_lt_floorZ s hs]
  constructor
  · exact fun h ↦ h.le
  · intro h
    exact lt_of_le_of_ne h (Ne.symm (seamGreedyFloorZ_ne_takeThreshold s hs))

/-- Thus the complete producer-tail inequality is not a separate analytic
majorant at all: it is precisely the rational greedy decision to take the
terminal Mersenne weight from the below prefix. -/
theorem middleProducer_tail_lt_carry_iff_rational_take
    (s : ℕ) (hs : 5 ≤ s) :
    binaryCoeffTail
        (supportCoeff
          (insert s
            (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)))
        (2 * s + 2) <
        (producerCarry
          (insert s
            (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ))
          s : ℝ) ↔
      mersenneWeightRat s ≤
        seamWordRationalRemainder (seamGreedyWord s) := by
  rw [middleProducer_tail_lt_carry_iff_takeThreshold_le_floorZ s hs]
  simpa [seamGreedyFloorZ] using
    (seamWord_take_iff_floorZ
      (by omega : 1 ≤ s) (seamGreedyWord s)).symm

/-- Failure of the exact cardinal carry inequality forces the concrete seam
remainder into a tiny linear cell: it is strictly smaller than the row.  This
is the precise residual obstruction left by the cardinal-tail reduction. -/
theorem middleProducer_not_cardEscape_forces_remainder_lt_row
    {s : ℕ} (hs : 5 ≤ s)
    (hfail : ¬
      (seamWordSupport (seamAdjacentCut s hs).below).card +
            (seamAdjacentCut s hs).belowPulse + 5 <
          4 * (seamAdjacentCut s hs).remainder) :
    (seamAdjacentCut s hs).remainder < s := by
  let K := seamAdjacentCut s hs
  have hpulse : K.belowPulse ≤
      2 * (seamWordSupport K.below).card := by
    exact wordPulse_le_two_mul_supportCard K.below
  have hcard := seamWordSupport_card_le_width K.below
  change ¬
      (seamWordSupport K.below).card + K.belowPulse + 5 <
        4 * K.remainder at hfail
  change K.remainder < s
  omega

/-- A simple sufficient socket: on every late middle row, the integer seam
remainder reaches the row index.  This implies the cardinality carry
inequality and is far weaker than an exponential bound, but it is stronger
than the already exposed square-root-scale carry target. -/
def SeamMiddleProducerRowEscape : Prop :=
  ∀ (s : ℕ) (hs : 5 ≤ s), 13 ≤ s →
    ¬ (seamAdjacentCut s hs).successorCarries →
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight →
        s ≤ (seamAdjacentCut s hs).remainder

/-- Row-scale escape implies the exact cardinality socket. -/
theorem SeamMiddleProducerRowEscape.toCardEscape
    (hrow : SeamMiddleProducerRowEscape) :
    SeamMiddleProducerCardEscape := by
  intro s hs hs13 hncarry hmiddle
  by_contra hfail
  have hsmall := middleProducer_not_cardEscape_forces_remainder_lt_row
    hs hfail
  exact (Nat.not_lt_of_ge (hrow s hs hs13 hncarry hmiddle)) hsmall

/-- The cardinality socket implies the exact complete-tail socket consumed
by the last-producer contradiction. -/
theorem SeamMiddleProducerCardEscape.toTailEscape
    (hcard : SeamMiddleProducerCardEscape) :
    SeamMiddleProducerTailEscape := by
  intro s hs hs13 hncarry hmiddle
  let P : Finset ℕ := seamWordSupport (seamAdjacentCut s hs).below
  let F : Finset ℕ := insert s P
  have htail := binaryCoeffTail_supportCoeff_coe_finset_le_card F (2 * s + 2)
  have hcarry := middleProducer_card_lt_carry hs
    (hcard s hs hs13 hncarry hmiddle)
  have hcoe : (↑F : Set ℕ) =
      insert s (↑P : Set ℕ) := by
    ext d
    simp [F, P]
  rw [hcoe] at htail
  exact htail.trans_lt (by simpa [F, P] using hcarry)

/-! ## Exact shape of a hypothetical final middle producer -/

/-- If a concrete middle transition is followed only by right extensions,
then its terminal-augmented finite prefix lies above `1/2`.  Equivalently,
the middle producer carry is *strictly smaller* than its complete future
incidence tail.  Thus this strict reverse inequality is not an artifact of a
chosen majorant: it is the exact arithmetic signature that any hypothetical
final middle producer must satisfy. -/
theorem middleProducer_allRight_forces_carry_lt_tail
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (producerCarry
        (insert D
          (↑(seamWordSupport
            (seamAdjacentCut D (by omega)).below) : Set ℕ)) D : ℝ) <
      binaryCoeffTail
        (supportCoeff
          (insert D
            (↑(seamWordSupport
              (seamAdjacentCut D (by omega)).below) : Set ℕ)))
        (2 * D + 2) := by
  classical
  let hs5 : 5 ≤ D := by omega
  let K := seamAdjacentCut D hs5
  let u : Finset ℕ := seamWordSupport K.below
  let A : Set ℕ := insert D (↑u : Set ℕ)
  have hword : seamGreedyWord (D + 1) = K.below.extend false := by
    exact seamGreedyWord_succ_eq_middleBranch D hs5 hncarry hmiddle
  have hu : ∀ e ∈ u, 2 ≤ e ∧ e < D := by
    intro e he
    exact seamWordSupport_below he
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
  have hDnotu : D ∉ u := by
    intro hDu
    exact (Nat.lt_irrefl D) (hu D hDu).2
  have hupperSeries : (1 : ℝ) / 2 < erdosSupportSeries 2 A := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    simpa [A, u] using hupper
  have htail :=
    (producerCarry_lt_tail_iff_half_lt_supportSeries A D hone hA).2
      hupperSeries
  simpa [A, u, K, hs5] using htail

/-- Consuming the exact tail formula, a hypothetical final middle producer
followed by an all-right suffix lies strictly *below* the rational take
threshold in the corrected seam coordinate. -/
theorem middleProducer_allRight_forces_floorZ_lt_takeThreshold
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    seamGreedyFloorZ D < seamTakeThreshold D := by
  have hcarry := middleProducer_allRight_forces_carry_lt_tail
    D hD13 hncarry hmiddle hright
  exact
    (middleProducer_carry_lt_tail_iff_floorZ_lt_takeThreshold
      D (by omega)).1 hcarry

/-- Equivalently, the below word at a hypothetical final middle producer
strictly skips its terminal Mersenne weight in the exact rational model. -/
theorem middleProducer_allRight_forces_rational_skip
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    seamWordRationalRemainder (seamGreedyWord D) <
      mersenneWeightRat D := by
  have hZ := middleProducer_allRight_forces_floorZ_lt_takeThreshold
    D hD13 hncarry hmiddle hright
  have htake := seamWord_take_iff_floorZ
    (by omega : 1 ≤ D) (seamGreedyWord D)
  apply lt_of_not_ge
  intro hweight
  exact (not_le_of_gt hZ) (htake.mp hweight)

/-! ## Exact rational and floor-`Z` orbit of the all-right suffix -/

/-- A false extension preserves the exact rational residual. -/
theorem seamWordRationalRemainder_extend_false
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordRationalRemainder (b.extend false) =
      seamWordRationalRemainder b := by
  simp only [seamWordRationalRemainder,
    seamWordRationalSum_extend_false hs b]

/-- A true extension subtracts exactly the newly selected Mersenne weight
from the rational residual. -/
theorem seamWordRationalRemainder_extend_true
    {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord s) :
    seamWordRationalRemainder (b.extend true) =
      seamWordRationalRemainder b - mersenneWeightRat s := by
  simp only [seamWordRationalRemainder,
    seamWordRationalSum_extend_true hs b]
  ring

/-- The accumulated affine charge in the exact floor-`Z` right recurrence.
It is the rational analogue of `affineRightRunCharge`, retaining the
Mersenne floor correction rather than only the integer pulse. -/
def floorZRightRunCharge (S : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 =>
      4 * floorZRightRunCharge S k + (2 : ℚ) ^ (S + k + 1) + 4 +
        4 / ((2 : ℚ) ^ (S + k) - 1)

/-- The exact finite rational-residual orbit along any all-right suffix. -/
theorem eventualRightTail_rationalRemainder_add_eq
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ k : ℕ,
      seamWordRationalRemainder (seamGreedyWord (S + k)) =
        seamWordRationalRemainder (seamGreedyWord S) -
          ∑ j ∈ Finset.range k, mersenneWeightRat (S + j) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show S + (k + 1) = (S + k) + 1 by omega,
        hright (S + k) (by omega),
        seamWordRationalRemainder_extend_true (by omega), ih,
        Finset.sum_range_succ]
      ring

/-- One exact floor-`Z` step along an all-right suffix. -/
theorem eventualRightTail_floorZ_succ_eq
    {S s : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ t : ℕ, S ≤ t →
      seamGreedyWord (t + 1) = (seamGreedyWord t).extend true)
    (hSs : S ≤ s) :
    seamGreedyFloorZ (s + 1) =
      4 * seamGreedyFloorZ s - (2 : ℚ) ^ (s + 1) - 4 -
        4 / ((2 : ℚ) ^ s - 1) := by
  change seamWordFloorZ (seamGreedyWord (s + 1)) = _
  rw [hright s hSs]
  simpa [seamGreedyFloorZ] using
    seamWordFloorZ_extend_true (by omega : 3 ≤ s) (seamGreedyWord s)

/-- Closed division-free iterate of the floor-`Z` right recurrence. -/
theorem eventualRightTail_floorZ_add_charge_eq
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ k : ℕ,
      seamGreedyFloorZ (S + k) + floorZRightRunCharge S k =
        (4 : ℚ) ^ k * seamGreedyFloorZ S := by
  intro k
  induction k with
  | zero => simp [floorZRightRunCharge]
  | succ k ih =>
      have hstep := eventualRightTail_floorZ_succ_eq
        hS5 hright (s := S + k) (by omega)
      calc
        seamGreedyFloorZ (S + (k + 1)) +
              floorZRightRunCharge S (k + 1) =
            4 * (seamGreedyFloorZ (S + k) +
              floorZRightRunCharge S k) := by
                rw [show S + (k + 1) = (S + k) + 1 by omega, hstep]
                simp only [floorZRightRunCharge]
                ring
        _ = 4 * ((4 : ℚ) ^ k * seamGreedyFloorZ S) := by rw [ih]
        _ = (4 : ℚ) ^ (k + 1) * seamGreedyFloorZ S := by
          rw [pow_succ]
          ring

/-- Explicit partial-tail closed form for the same floor-`Z` orbit. -/
theorem eventualRightTail_floorZ_add_eq_partialTail
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (k : ℕ) :
    seamGreedyFloorZ (S + k) =
      (4 : ℚ) ^ (S + k) *
          (seamWordRationalRemainder (seamGreedyWord S) -
            ∑ j ∈ Finset.range k, mersenneWeightRat (S + j)) -
        (2 : ℚ) ^ (S + k) := by
  have horbit := eventualRightTail_rationalRemainder_add_eq
    hS5 hright k
  have hrem := seamWordRationalRemainder_eq_pow_add_floorZ_div
    (by omega : 1 ≤ S + k) (seamGreedyWord (S + k))
  have hpow : (4 : ℚ) ^ (S + k) ≠ 0 := by positivity
  have hscaled := (eq_div_iff hpow).mp hrem
  rw [horbit] at hscaled
  change seamWordFloorZ (seamGreedyWord (S + k)) = _
  calc
    seamWordFloorZ (seamGreedyWord (S + k)) =
        (seamWordRationalRemainder (seamGreedyWord S) -
            ∑ j ∈ Finset.range k, mersenneWeightRat (S + j)) *
          (4 : ℚ) ^ (S + k) - (2 : ℚ) ^ (S + k) := by
            linarith
    _ = _ := by ring

/-- A middle landing preserves the old rational residual, after which the
all-right suffix subtracts exactly the consecutive Mersenne partial tail. -/
theorem middleThenAllRight_rationalRemainder_add_eq
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (k : ℕ) :
    seamWordRationalRemainder (seamGreedyWord (D + 1 + k)) =
      seamWordRationalRemainder (seamGreedyWord D) -
        ∑ j ∈ Finset.range k, mersenneWeightRat (D + 1 + j) := by
  have hbase :
      seamWordRationalRemainder (seamGreedyWord (D + 1)) =
        seamWordRationalRemainder (seamGreedyWord D) := by
    rw [seamGreedyWord_succ_eq_middleBranch D (by omega) hncarry hmiddle]
    simpa [seamAdjacentCut] using
      seamWordRationalRemainder_extend_false
        (by omega : 3 ≤ D) (seamGreedyWord D)
  have horbit := eventualRightTail_rationalRemainder_add_eq
    (S := D + 1) (by omega) hright k
  rw [hbase] at horbit
  simpa [Nat.add_assoc] using horbit

/-- The same middle-then-right orbit in exact affine floor-`Z` coordinates.
The right-run charge closes against the genuine middle landing value, not
against a merely assumed skip decision. -/
theorem middleThenAllRight_floorZ_add_charge_eq
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (k : ℕ) :
    seamGreedyFloorZ (D + 1 + k) + floorZRightRunCharge (D + 1) k =
      (4 : ℚ) ^ k *
        (4 * seamGreedyFloorZ D + (2 : ℚ) ^ (D + 1)) := by
  have hiter := eventualRightTail_floorZ_add_charge_eq
    (S := D + 1) (by omega) hright k
  have hlanding := seamGreedyFloorZ_succ_middle
    D (by omega) hncarry hmiddle
  rw [hlanding] at hiter
  simpa [Nat.add_assoc] using hiter

/-- Explicit partial-tail closed form after substituting the genuine middle
landing. -/
theorem middleThenAllRight_floorZ_eq_partialTail
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (k : ℕ) :
    seamGreedyFloorZ (D + 1 + k) =
      (4 : ℚ) ^ (D + 1 + k) *
          (seamWordRationalRemainder (seamGreedyWord D) -
            ∑ j ∈ Finset.range k,
              mersenneWeightRat (D + 1 + j)) -
        (2 : ℚ) ^ (D + 1 + k) := by
  have hbase := middleThenAllRight_rationalRemainder_add_eq
    D hD13 hncarry hmiddle hright 0
  simp only [add_zero, Finset.range_zero, Finset.sum_empty, sub_zero] at hbase
  have horbit := eventualRightTail_floorZ_add_eq_partialTail
    (S := D + 1) (by omega) hright k
  rw [hbase] at horbit
  simpa [Nat.add_assoc] using horbit

/-- Every finite prefix after the middle landing is the old finite value plus
the corresponding initial segment of the consecutive Mersenne tail. -/
theorem middleThenAllRight_finiteValue_add_eq
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (k : ℕ) :
    seamGreedyFiniteValue (D + 1 + k) =
      seamGreedyFiniteValue D +
        ∑ j ∈ Finset.range k, mersenneWeight (D + 1 + j) := by
  have horbit := middleThenAllRight_rationalRemainder_add_eq
    D hD13 hncarry hmiddle hright k
  have hsumQ :
      seamWordRationalSum (seamGreedyWord (D + 1 + k)) =
        seamWordRationalSum (seamGreedyWord D) +
          ∑ j ∈ Finset.range k,
            mersenneWeightRat (D + 1 + j) := by
    rw [seamWordRationalRemainder,
      seamWordRationalRemainder] at horbit
    linarith
  rw [seamGreedyFiniteValue_eq_cast_rationalSum,
    seamGreedyFiniteValue_eq_cast_rationalSum]
  calc
    ((seamWordRationalSum
          (seamGreedyWord (D + 1 + k)) : ℚ) : ℝ) =
        (((seamWordRationalSum (seamGreedyWord D) +
          ∑ j ∈ Finset.range k,
            mersenneWeightRat (D + 1 + j) : ℚ)) : ℝ) := by
              exact_mod_cast hsumQ
    _ = ((seamWordRationalSum (seamGreedyWord D) : ℚ) : ℝ) +
          ∑ j ∈ Finset.range k, mersenneWeight (D + 1 + j) := by
            push_cast
            simp only [cast_mersenneWeightRat]

/-- The propagated finite prefixes converge to the old prefix plus the
complete Mersenne tail above the middle rank. -/
theorem tendsto_middleThenAllRight_finiteValue
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    Tendsto (fun k : ℕ ↦ seamGreedyFiniteValue (D + 1 + k))
      atTop
      (nhds (seamGreedyFiniteValue D + mersenneTail D)) := by
  have htail : Tendsto
      (fun k : ℕ ↦
        ∑ j ∈ Finset.range k, mersenneWeight (D + 1 + j))
      atTop (nhds (mersenneTail D)) := by
    have h := (summable_mersenneTail D).tendsto_sum_tsum_nat
    simpa [mersenneTail, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  have hconst : Tendsto
      (fun _ : ℕ ↦ seamGreedyFiniteValue D) atTop
      (nhds (seamGreedyFiniteValue D)) := tendsto_const_nhds
  have hsum := hconst.add htail
  convert hsum using 1
  funext k
  exact middleThenAllRight_finiteValue_add_eq
    D hD13 hncarry hmiddle hright k

/-- The limiting lazy endpoint remains strictly below `1/2`. -/
theorem middleThenAllRight_limit_lt_half
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    seamGreedyFiniteValue D + mersenneTail D < (1 / 2 : ℝ) := by
  classical
  let u : Finset ℕ := seamWordSupport (seamGreedyWord D)
  have hu : ∀ e ∈ u, 2 ≤ e ∧ e < D := by
    intro e he
    exact seamWordSupport_below (by simpa [u] using he)
  have hword := seamGreedyWord_succ_eq_middleBranch
    D (by omega) hncarry hmiddle
  have hbase : seamWordSupport (seamGreedyWord (D + 1)) =
      u ∪ Finset.Ico (D + 1) (D + 1) := by
    rw [hword, seamWordSupport_extend_false (by omega)]
    simp [u, seamAdjacentCut]
  have hlimit := prefix_add_mersenneTail_lt_half_of_eventually_right
    (S := D + 1) (D := D) (u := u)
    (by omega) (by omega) hu hright hbase
  simpa [u, seamGreedyFiniteValue] using hlimit

/-- Exact fatal-gap interval forced by a final middle landing and an
all-right suffix.  The lower wall comes from the completed tail; the upper
wall is the skipped terminal weight. -/
theorem middleThenAllRight_rationalRemainder_fatalGap
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    mersenneTail D <
        ((seamWordRationalRemainder (seamGreedyWord D) : ℚ) : ℝ) ∧
      ((seamWordRationalRemainder (seamGreedyWord D) : ℚ) : ℝ) <
        mersenneWeight D := by
  have hlimit := middleThenAllRight_limit_lt_half
    D hD13 hncarry hmiddle hright
  have hremCast :
      ((seamWordRationalRemainder (seamGreedyWord D) : ℚ) : ℝ) =
        (1 / 2 : ℝ) - seamGreedyFiniteValue D := by
    rw [seamWordRationalRemainder,
      seamGreedyFiniteValue_eq_cast_rationalSum]
    push_cast
    rfl
  have hlower : mersenneTail D <
      ((seamWordRationalRemainder (seamGreedyWord D) : ℚ) : ℝ) := by
    rw [hremCast]
    linarith
  have hupperQ := middleProducer_allRight_forces_rational_skip
    D hD13 hncarry hmiddle hright
  have hupperR :
      ((seamWordRationalRemainder (seamGreedyWord D) : ℚ) : ℝ) <
        ((mersenneWeightRat D : ℚ) : ℝ) := by
    exact_mod_cast hupperQ
  rw [cast_mersenneWeightRat] at hupperR
  exact ⟨hlower, hupperR⟩

/-- The same fatal gap in the corrected floor coordinate.  This is the
precise remaining arithmetic window that a genuinely middle transition
would have to avoid in order to contradict an all-right suffix. -/
theorem middleThenAllRight_floorZ_fatalGap
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (4 : ℝ) ^ D * mersenneTail D - (2 : ℝ) ^ D <
        ((seamGreedyFloorZ D : ℚ) : ℝ) ∧
      ((seamGreedyFloorZ D : ℚ) : ℝ) <
        ((seamTakeThreshold D : ℚ) : ℝ) := by
  have hgap := middleThenAllRight_rationalRemainder_fatalGap
    D hD13 hncarry hmiddle hright
  have hremQ := seamWordRationalRemainder_eq_pow_add_floorZ_div
    (by omega : 1 ≤ D) (seamGreedyWord D)
  have hremR :
      ((seamWordRationalRemainder (seamGreedyWord D) : ℚ) : ℝ) =
        ((2 : ℝ) ^ D + ((seamGreedyFloorZ D : ℚ) : ℝ)) /
          (4 : ℝ) ^ D := by
    exact_mod_cast hremQ
  have hlower := hgap.1
  rw [hremR] at hlower
  have hscaled := (lt_div_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ D)).mp
    hlower
  constructor
  · ring_nf at hscaled ⊢
    linarith
  · exact_mod_cast middleProducer_allRight_forces_floorZ_lt_takeThreshold
      D hD13 hncarry hmiddle hright

/-- The scaled lower wall of the fatal gap has an exact leading constant:
`1/3`, followed by the positive higher-channel tail. -/
theorem scaledMersenneTail_floorWall_eq (D : ℕ) :
    (4 : ℝ) ^ D * mersenneTail D - (2 : ℝ) ^ D =
      (1 / 3 : ℝ) +
        (4 : ℝ) ^ D * mersenneWeightRemainderTail D := by
  have hhalf :
      (4 : ℝ) ^ D * ((1 : ℝ) / 2) ^ D = (2 : ℝ) ^ D := by
    rw [← mul_pow]
    norm_num
  have hquarter :
      (4 : ℝ) ^ D * ((1 : ℝ) / 4) ^ D = 1 := by
    rw [← mul_pow]
    norm_num
  rw [mersenneTail_eq_two_channels_add_remainderTail]
  calc
    (4 : ℝ) ^ D *
          (((1 : ℝ) / 2) ^ D +
            (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ D +
            mersenneWeightRemainderTail D) - (2 : ℝ) ^ D =
        ((4 : ℝ) ^ D * ((1 : ℝ) / 2) ^ D - (2 : ℝ) ^ D) +
          (1 / 3 : ℝ) *
            ((4 : ℝ) ^ D * ((1 : ℝ) / 4) ^ D) +
          (4 : ℝ) ^ D * mersenneWeightRemainderTail D := by ring
    _ = (1 / 3 : ℝ) +
          (4 : ℝ) ^ D * mersenneWeightRemainderTail D := by
            rw [hhalf, hquarter]
            ring

/-- In particular, the exact scaled tail wall is strictly larger than
`1/3` at every row. -/
theorem one_third_lt_scaledMersenneTail_floorWall (D : ℕ) :
    (1 / 3 : ℝ) <
      (4 : ℝ) ^ D * mersenneTail D - (2 : ℝ) ^ D := by
  rw [scaledMersenneTail_floorWall_eq]
  have hpos := mersenneWeightRemainderTail_pos D
  have hpow : (0 : ℝ) < (4 : ℝ) ^ D := by positivity
  nlinarith [mul_pos hpow hpos]

/-- The first genuinely middle-specific consequence of the fatal-gap
orbit: pulse absorption and the strict `1/3` wall force the integer landing
excess to be at least two, excluding the first positive cell. -/
theorem middleThenAllRight_landingExcess_two_le
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
      4 * (seamAdjacentCut D (by omega)).remainder := by
  let K := seamAdjacentCut D (by omega : 5 ≤ D)
  have hfatal := middleThenAllRight_floorZ_fatalGap
    D hD13 hncarry hmiddle hright
  have hwall := one_third_lt_scaledMersenneTail_floorWall D
  have hZthirdR : (1 / 3 : ℝ) <
      ((seamGreedyFloorZ D : ℚ) : ℝ) := hwall.trans hfatal.1
  have hZthirdQ : (1 / 3 : ℚ) < seamGreedyFloorZ D := by
    by_contra h
    have hleQ : seamGreedyFloorZ D ≤ (1 / 3 : ℚ) := le_of_not_gt h
    have hleR : ((seamGreedyFloorZ D : ℚ) : ℝ) ≤
        (((1 / 3 : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast hleQ
    norm_num at hleR
    exact (not_le_of_gt hZthirdR) hleR
  have hpulse := wordPulse_le_four_mul_seamWordFloorError
    (by omega : 3 ≤ D) K.below
  change (K.belowPulse : ℚ) ≤ 4 * seamGreedyFloorError D at hpulse
  have hKrem : K.remainder = seamIntegerGreedyRemainder D := by
    simpa [K] using seamAdjacentCut_remainder (by omega : 5 ≤ D)
  have hKremQ : (K.remainder : ℚ) =
      (seamIntegerGreedyRemainder D : ℚ) := by
    exact_mod_cast hKrem
  have hZ := seamGreedyFloorZ_eq_remainder_sub_error
    D (by omega : 5 ≤ D)
  rw [hZ, ← hKremQ] at hZthirdQ
  have hstrictQ : (K.belowPulse : ℚ) + 1 < 4 * (K.remainder : ℚ) := by
    linarith
  have hstrictNat : K.belowPulse + 1 < 4 * K.remainder := by
    exact_mod_cast hstrictQ
  simpa [K] using (show K.belowPulse + 2 ≤ 4 * K.remainder by omega)

/-- The exact cardinality-scale middle bound rules out the final middle
producer of an eventual right seam and therefore proves the half endpoint. -/
theorem half_mem_mersenneAchievementSet_of_middleProducerCardEscape
    (hcard : SeamMiddleProducerCardEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_middleProducerTailEscape
    hcard.toTailEscape

/-- It is enough that every late middle remainder be at least its row index. -/
theorem half_mem_mersenneAchievementSet_of_middleProducerRowEscape
    (hrow : SeamMiddleProducerRowEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_middleProducerCardEscape
    hrow.toCardEscape

/-! ## Reverse classification of a small seam remainder

The exact three-branch recurrence already rules out one apparent source of
a late row-scale failure.  A middle successor contains the full positive
gap `2^(s+1)` and loses only the linear row pulse, so it cannot create a
remainder below the next row.  More strongly, once the source remainder is
at least its row, a middle successor enters the exponential barrier

`2^(s+1) + (s+1) ≤ R_(s+1)`.

That barrier is preserved by every subsequent right successor.  Therefore a
hypothetical first late row with `R_s < s`, traced backwards over its final
run of right successors, cannot have a middle producer at the start of the
run.  Its last producer must be an upper/successor-carry reset.  This is the
formal part of the reverse-classification route; excluding the remaining
upper-reset ancestry is still an arithmetic obligation.
-/

theorem three_mul_le_two_pow_succ
    {s : ℕ} (hs : 5 ≤ s) :
    3 * s ≤ 2 ^ (s + 1) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      rw [pow_succ]
      have hthree : 3 ≤ 2 ^ (s + 1) := by
        calc
          3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (s + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- From row five onward, four times the row index is still below the next
dyadic seam gap. -/
theorem four_mul_le_two_pow_succ
    {s : ℕ} (hs : 5 ≤ s) :
    4 * s ≤ 2 ^ (s + 1) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      rw [pow_succ]
      have hfour : 4 ≤ 2 ^ (s + 1) := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (s + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- Any row-scale-small remainder forces a non-right successor, without
using largest-false geometry. -/
theorem seamRowSmall_upperOrMiddle
    {s : ℕ} (hs : 5 ≤ s)
    (hsmall : seamIntegerGreedyRemainder s < s) :
    SeamGreedyUpperOrMiddleAt s hs := by
  apply upperOrMiddle_of_four_mul_remainder_lt hs
  have hfour := four_mul_le_two_pow_succ hs
  omega

/-- A right-only tail cannot start on or below the dyadic half-point.  A
strict deficit is consumed by `upperOrMiddle_within_of_two_pow_deficit`;
at exact equality, one right step creates a strict deficit because its
pulse charge contains the positive terminal correction `4`. -/
theorem allRightTail_forces_twoPow_lt_remainder
    {s : ℕ} (hs : 5 ≤ s)
    (hright : ∀ (t : ℕ) (hst : s ≤ t),
      ¬ SeamGreedyUpperOrMiddleAt t (by omega)) :
    2 ^ s < seamIntegerGreedyRemainder s := by
  by_contra hnot
  have hle : seamIntegerGreedyRemainder s ≤ 2 ^ s :=
    Nat.le_of_not_gt hnot
  by_cases heq : seamIntegerGreedyRemainder s = 2 ^ s
  · have hrec := rightBranch_remainder_succ_eq hs (hright s le_rfl)
    have hscale : 4 * 2 ^ s = 2 * 2 ^ (s + 1) := by
      rw [pow_succ]
      ring
    have hnextlt :
        seamIntegerGreedyRemainder (s + 1) < 2 ^ (s + 1) := by
      rw [heq, hscale] at hrec
      omega
    have hdiff : 1 ≤
        2 ^ (s + 1) - seamIntegerGreedyRemainder (s + 1) := by
      omega
    have hdef : 2 ^ (s + 1) ≤
        2 ^ (s + 1) *
          (2 ^ (s + 1) - seamIntegerGreedyRemainder (s + 1)) := by
      simpa using Nat.mul_le_mul_left (2 ^ (s + 1)) hdiff
    obtain ⟨t, hst, _ht, ht5, hUM⟩ :=
      upperOrMiddle_within_of_two_pow_deficit
        (s + 1) (s + 1) (by omega) (Nat.le_of_lt hnextlt) hdef
    exact (hright t (by omega)) hUM
  · have hlt : seamIntegerGreedyRemainder s < 2 ^ s := by omega
    have hdiff : 1 ≤ 2 ^ s - seamIntegerGreedyRemainder s := by omega
    have hdef : 2 ^ s ≤
        2 ^ s * (2 ^ s - seamIntegerGreedyRemainder s) := by
      simpa using Nat.mul_le_mul_left (2 ^ s) hdiff
    obtain ⟨t, hst, _ht, ht5, hUM⟩ :=
      upperOrMiddle_within_of_two_pow_deficit s s hs hle hdef
    exact (hright t hst) hUM

/-- Word-level form: every row of an eventual right-extension tail lies
strictly above its dyadic half-point.  This isolates the only possible
survivor as the positive affine-excess orbit. -/
theorem eventualRightTail_forces_twoPow_lt_remainder
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ (s : ℕ), S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ (s : ℕ), S ≤ s →
      2 ^ s < seamIntegerGreedyRemainder s := by
  intro s hSs
  apply allRightTail_forces_twoPow_lt_remainder (hS5.trans hSs)
  intro t hst hUM
  have hfalse :=
    (seamGreedy_terminal_false_iff_upperOrMiddle t (by omega)).2 hUM
  have htrue :=
    (seamGreedyWord_succ_eq_extend_true_iff_terminal_true
      t (by omega)).1 (hright t (hSs.trans hst))
  simpa [hfalse] using htrue

/-- On a right branch, the signed excess above the dyadic half-point is an
exact base-four affine orbit driven by the below-pulse charge. -/
theorem rightBranch_excess_succ_eq
    {s : ℕ} (hs : 5 ≤ s)
    (hR : ¬ SeamGreedyUpperOrMiddleAt s hs) :
    (seamIntegerGreedyRemainder (s + 1) : ℤ) -
          ((2 ^ (s + 1) : ℕ) : ℤ) =
      4 * ((seamIntegerGreedyRemainder s : ℤ) -
          ((2 ^ s : ℕ) : ℤ)) -
        ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 := by
  have hrec := rightBranch_remainder_succ_eq hs hR
  have hrecZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hrec
  push_cast at hrecZ ⊢
  rw [pow_succ] at hrecZ ⊢
  ring_nf at hrecZ ⊢
  omega

/-- Hence an eventual right tail is precisely a strictly positive affine
excess orbit.  The deficit and zero regimes have been eliminated
unconditionally above. -/
theorem eventualRightTail_positive_affineExcess
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ (s : ℕ), S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    ∀ (s : ℕ) (hSs : S ≤ s),
      0 < (seamIntegerGreedyRemainder s : ℤ) -
            ((2 ^ s : ℕ) : ℤ) ∧
        (seamIntegerGreedyRemainder (s + 1) : ℤ) -
              ((2 ^ (s + 1) : ℕ) : ℤ) =
          4 * ((seamIntegerGreedyRemainder s : ℤ) -
              ((2 ^ s : ℕ) : ℤ)) -
            ((seamAdjacentCut s (by omega)).belowPulse : ℤ) - 4 := by
  intro s hSs
  have hgt := eventualRightTail_forces_twoPow_lt_remainder
    hS5 hright s hSs
  have hgtZ : ((2 ^ s : ℕ) : ℤ) <
      (seamIntegerGreedyRemainder s : ℤ) := by
    exact_mod_cast hgt
  have hno : ¬ SeamGreedyUpperOrMiddleAt s (by omega) := by
    intro hUM
    have hfalse :=
      (seamGreedy_terminal_false_iff_upperOrMiddle s (by omega)).2 hUM
    have htrue :=
      (seamGreedyWord_succ_eq_extend_true_iff_terminal_true
        s (by omega)).1 (hright s hSs)
    simpa [hfalse] using htrue
  exact ⟨by omega, rightBranch_excess_succ_eq (by omega) hno⟩

/-- A hypothetical final middle producer can land only in a very thin
positive-excess window.  Its landing excess is exactly the producer carry
plus four, while the complete future-tail inequality bounds that carry by
the universal support tail strip. -/
theorem middleProducer_allRight_landingExcess_window
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    0 < (seamIntegerGreedyRemainder (D + 1) : ℤ) -
          ((2 ^ (D + 1) : ℕ) : ℤ) ∧
      (((seamIntegerGreedyRemainder (D + 1) : ℤ) -
          ((2 ^ (D + 1) : ℕ) : ℤ) : ℤ) : ℝ) <
        2 * Real.sqrt ((2 * D + 2 : ℕ) : ℝ) + 8 := by
  classical
  let hs5 : 5 ≤ D := by omega
  let K := seamAdjacentCut D hs5
  let A : Set ℕ :=
    insert D (↑(seamWordSupport K.below) : Set ℕ)
  have hposNat : 2 ^ (D + 1) <
      seamIntegerGreedyRemainder (D + 1) :=
    eventualRightTail_forces_twoPow_lt_remainder
      (S := D + 1) (by omega) hright (D + 1) le_rfl
  have hposZ : (0 : ℤ) <
      (seamIntegerGreedyRemainder (D + 1) : ℤ) -
        ((2 ^ (D + 1) : ℕ) : ℤ) := by
    have hposZ' : ((2 ^ (D + 1) : ℕ) : ℤ) <
        (seamIntegerGreedyRemainder (D + 1) : ℤ) := by
      exact_mod_cast hposNat
    omega
  have htail : (producerCarry A D : ℝ) <
      binaryCoeffTail (supportCoeff A) (2 * D + 2) := by
    have htail' := middleProducer_allRight_forces_carry_lt_tail
      D hD13 hncarry hmiddle hright
    change (producerCarry A D : ℝ) <
      binaryCoeffTail (supportCoeff A) (2 * D + 2) at htail'
    exact htail'
  have htailBound :=
    binaryCoeffTail_supportCoeff_le_two_sqrt_add_four A (2 * D + 2)
  have hcarry : producerCarry A D =
      4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 := by
    simpa [A, K] using
      producerCarry_insert_seamBelowSupport_eq_middleCoordinate D hs5
  have hnext := K.nextRemainder_trichotomy
  rw [if_neg hncarry, if_pos hmiddle,
    seamAdjacentCut_nextRemainder hs5] at hnext
  change seamIntegerGreedyRemainder (D + 1) =
      4 * K.remainder + 2 ^ (D + 1) - K.belowPulse at hnext
  have hpulse := (seamPerturbedFamily D (by omega)).pulse_le K.below
  change K.belowPulse ≤ 2 * (D - 2) at hpulse
  have hpow := four_mul_le_two_pow_succ (s := D) (by omega)
  have hadd : seamIntegerGreedyRemainder (D + 1) + K.belowPulse =
      4 * K.remainder + 2 ^ (D + 1) := by
    omega
  have haddZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hadd
  push_cast at haddZ
  have hlanding :
      (seamIntegerGreedyRemainder (D + 1) : ℤ) -
          ((2 ^ (D + 1) : ℕ) : ℤ) =
        producerCarry A D + 4 := by
    rw [hcarry]
    omega
  refine ⟨hposZ, ?_⟩
  have hupper : (producerCarry A D : ℝ) + 4 <
      2 * Real.sqrt ((2 * D + 2 : ℕ) : ℝ) + 8 := by
    calc
      (producerCarry A D : ℝ) + 4 <
          binaryCoeffTail (supportCoeff A) (2 * D + 2) + 4 := by
            linarith
      _ ≤ (2 * Real.sqrt ((2 * D + 2 : ℕ) : ℝ) + 4) + 4 := by
            linarith
      _ = 2 * Real.sqrt ((2 * D + 2 : ℕ) : ℝ) + 8 := by ring
  rw [hlanding]
  norm_num [Nat.cast_add, Nat.cast_mul] at hupper ⊢
  exact hupper

/-- Exact additive recurrence on the middle branch.  Keeping the pulse on
the left removes the truncated subtraction from `nextRemainder_trichotomy`
and exposes the full dyadic recovery term used by late-row arguments. -/
theorem seamMiddleBranch_nextRemainder_add_belowPulse_eq
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight) :
    seamIntegerGreedyRemainder (s + 1) +
        (seamAdjacentCut s hs).belowPulse =
      4 * seamIntegerGreedyRemainder s + 2 ^ (s + 1) := by
  classical
  have hpulse :=
    (seamPerturbedFamily s (by omega)).pulse_le
      (seamAdjacentCut s hs).below
  change (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) at hpulse
  have hnext := (seamAdjacentCut s hs).nextRemainder_trichotomy
  rw [if_neg hncarry, if_pos hmiddle,
    seamAdjacentCut_nextRemainder hs] at hnext
  change seamIntegerGreedyRemainder (s + 1) =
      4 * (seamAdjacentCut s hs).remainder + 2 ^ (s + 1) -
        (seamAdjacentCut s hs).belowPulse at hnext
  have hpow := three_mul_le_two_pow_succ hs
  rw [seamAdjacentCut_remainder hs] at hnext
  omega

/-- A middle branch cannot itself create a row-scale-small successor.  This
uses no lower bound on the source remainder. -/
theorem seamMiddleBranch_nextRemainder_ge_row
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight) :
    s + 1 ≤ seamIntegerGreedyRemainder (s + 1) := by
  classical
  have hpulse :=
    (seamPerturbedFamily s (by omega)).pulse_le
      (seamAdjacentCut s hs).below
  change (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) at hpulse
  have hnext := (seamAdjacentCut s hs).nextRemainder_trichotomy
  rw [if_neg hncarry, if_pos hmiddle,
    seamAdjacentCut_nextRemainder hs] at hnext
  change seamIntegerGreedyRemainder (s + 1) =
      4 * (seamAdjacentCut s hs).remainder + 2 ^ (s + 1) -
        (seamAdjacentCut s hs).belowPulse at hnext
  have hpow := three_mul_le_two_pow_succ hs
  omega

/-- With the row-scale source lower bound, a middle branch enters an
exponential barrier above the next row. -/
theorem seamMiddleBranch_nextRemainder_ge_expBarrier
    {s : ℕ} (hs : 5 ≤ s)
    (hrow : s ≤ (seamAdjacentCut s hs).remainder)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight) :
    2 ^ (s + 1) + (s + 1) ≤
      seamIntegerGreedyRemainder (s + 1) := by
  classical
  have hpulse :=
    (seamPerturbedFamily s (by omega)).pulse_le
      (seamAdjacentCut s hs).below
  change (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) at hpulse
  have hnext := (seamAdjacentCut s hs).nextRemainder_trichotomy
  rw [if_neg hncarry, if_pos hmiddle,
    seamAdjacentCut_nextRemainder hs] at hnext
  change seamIntegerGreedyRemainder (s + 1) =
      4 * (seamAdjacentCut s hs).remainder + 2 ^ (s + 1) -
        (seamAdjacentCut s hs).belowPulse at hnext
  omega

/-- A right branch preserves the exponential barrier.  The pulse cap is
exactly strong enough: four copies of the linear surplus `s` pay for the
row pulse and leave the next linear surplus. -/
theorem seamRightBranch_preserves_expBarrier
    {s : ℕ} (hs : 5 ≤ s)
    (hbarrier :
      2 ^ s + s ≤ (seamAdjacentCut s hs).remainder)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hright : (seamAdjacentCut s hs).terminalWeight ≤
      4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse) :
    2 ^ (s + 1) + (s + 1) ≤
      seamIntegerGreedyRemainder (s + 1) := by
  classical
  have hpulse :=
    (seamPerturbedFamily s (by omega)).pulse_le
      (seamAdjacentCut s hs).below
  change (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) at hpulse
  have hnterminal : ¬
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight :=
    Nat.not_lt_of_ge hright
  have hnext := (seamAdjacentCut s hs).nextRemainder_trichotomy
  rw [if_neg hncarry, if_neg hnterminal,
    seamAdjacentCut_nextRemainder hs] at hnext
  change seamIntegerGreedyRemainder (s + 1) =
      4 * (seamAdjacentCut s hs).remainder - 2 ^ (s + 1) -
        (seamAdjacentCut s hs).belowPulse - 4 at hnext
  have hpow : 4 * 2 ^ s = 2 * 2 ^ (s + 1) := by
    rw [pow_succ]
    ring
  omega

/-- Iterated form of `seamRightBranch_preserves_expBarrier` on a concrete
right-only interval. -/
theorem seamRightRun_preserves_expBarrier
    {d s : ℕ} (hd5 : 5 ≤ d) (hds : d ≤ s)
    (hstart : 2 ^ d + d ≤ seamIntegerGreedyRemainder d)
    (hrun : ∀ (t : ℕ) (hdt : d ≤ t), t < s →
      ¬ (seamAdjacentCut t (by omega)).successorCarries ∧
        (seamAdjacentCut t (by omega)).terminalWeight ≤
          4 * (seamAdjacentCut t (by omega)).remainder +
            (seamPerturbedFamily t (by omega)).gap -
            (seamAdjacentCut t (by omega)).belowPulse) :
    2 ^ s + s ≤ seamIntegerGreedyRemainder s := by
  induction s, hds using Nat.le_induction with
  | base => exact hstart
  | succ s hds ih =>
      rcases hrun s hds (by omega) with ⟨hncarry, hright⟩
      have ih0 := ih (fun t hdt hts ↦ hrun t hdt (by omega))
      have ih' :
          2 ^ s + s ≤
            (seamAdjacentCut s (by omega : 5 ≤ s)).remainder := by
        simpa [seamAdjacentCut_remainder] using ih0
      exact seamRightBranch_preserves_expBarrier
        (by omega : 5 ≤ s) ih' hncarry hright

/-- A row-scale middle producer followed by any finite run of right
successors can never end in a row-scale-small remainder.  This is the exact
fan-in used when tracing a hypothetical first late failure backwards to its
last non-right producer. -/
theorem seamMiddleThenRightRun_expBarrier
    {d s : ℕ} (hd5 : 5 ≤ d) (hds : d + 1 ≤ s)
    (hrow : d ≤ (seamAdjacentCut d hd5).remainder)
    (hncarry : ¬ (seamAdjacentCut d hd5).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut d hd5).remainder +
            (seamPerturbedFamily d (by omega)).gap -
            (seamAdjacentCut d hd5).belowPulse <
          (seamAdjacentCut d hd5).terminalWeight)
    (hrun : ∀ (t : ℕ) (hdt : d + 1 ≤ t), t < s →
      ¬ (seamAdjacentCut t (by omega)).successorCarries ∧
        (seamAdjacentCut t (by omega)).terminalWeight ≤
          4 * (seamAdjacentCut t (by omega)).remainder +
            (seamPerturbedFamily t (by omega)).gap -
            (seamAdjacentCut t (by omega)).belowPulse) :
    2 ^ s + s ≤ seamIntegerGreedyRemainder s := by
  have hstart := seamMiddleBranch_nextRemainder_ge_expBarrier
    hd5 hrow hncarry hmiddle
  exact seamRightRun_preserves_expBarrier (by omega) hds hstart hrun

/-! ## Largest-false coordinates of an upper reset -/

/-- In a gap-separated adjacent cut, any above-target candidate less than
two separation gaps above the lower word is the actual minimal upper word. -/
theorem PerturbedFamily.AdjacentCut.above_eq_of_candidate_lt_two_gap
    {α : Type*} {F : PerturbedFamily α} {C : ℕ}
    (K : F.AdjacentCut C) (x : α)
    (hx : C < F.oldSum x)
    (hwindow : F.oldSum x < F.oldSum K.below + 2 * F.gap) :
    K.above = x := by
  have hmin := K.above_minimal x hx
  apply F.oldSum_injective
  apply Nat.le_antisymm hmin
  by_contra hnot
  have hstrict : F.oldSum K.above < F.oldSum x := Nat.lt_of_not_ge hnot
  have hbelowAbove : F.oldSum K.below < F.oldSum K.above :=
    K.below_admissible.trans_lt K.above_strict
  have hsep₁ := F.separated hbelowAbove
  have hsep₂ := F.separated hstrict
  omega

/-- The explicit lower word determined by a largest false rank has exactly
the greedy word's weight. -/
theorem largestSkipLowerWord_weight_eq_greedy_of_support
    {s d : ℕ} {u : Finset ℕ}
    (hd2 : 2 ≤ d) (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d) (hds : d < s)
    (hsupp : seamWordSupport (seamGreedyWord s) =
      u ∪ Finset.Ico (d + 1) s) :
    wordWeightSum s (largestSkipLowerWord s d u).toNatWord =
      wordWeightSum s (seamGreedyWord s).toNatWord := by
  classical
  have hbounds : ∀ e ∈ u ∪ Finset.Ico (d + 1) s,
      2 ≤ e ∧ e < s := by
    intro e he
    rcases Finset.mem_union.mp he with heu | hei
    · exact ⟨(hu e heu).1, by have := (hu e heu).2; omega⟩
    · rcases Finset.mem_Ico.mp hei with ⟨hlo, hhi⟩
      exact ⟨by omega, hhi⟩
  rw [wordWeightSum_eq_sum_seamWordSupport,
    wordWeightSum_eq_sum_seamWordSupport]
  unfold largestSkipLowerWord
  rw [seamWordSupport_seamRowWordOfFinset hbounds, hsupp]

/-- The correction in the exact late adjacent gap is strictly smaller than
one further dyadic gap. -/
theorem exactLateGap_correction_lt_three_mul_gap
    {s d : ℕ} (hs : 5 ≤ s) (hds : d < s)
    (hlate : 2 * s < 3 * d) :
    2 * 4 ^ (s - d) + 4 < 3 * 2 ^ (s + 1) := by
  have hexponent : 2 * (s - d) ≤ s := by omega
  have hfour : 4 ^ (s - d) = 2 ^ (2 * (s - d)) := by
    rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
  have hpowle : 4 ^ (s - d) ≤ 2 ^ s := by
    rw [hfour]
    exact Nat.pow_le_pow_right (by norm_num) hexponent
  have hdouble : 2 * 2 ^ s = 2 ^ (s + 1) := by
    rw [pow_succ]
    ring
  have hfourLe : 4 ≤ 2 ^ (s + 1) := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (s + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 ^ (s + 1) := by positivity
  omega

/-- For a late largest false rank, the explicit upper adjacent word is not
merely a competitor: it is the actual minimal word above the target.  This
exposes the upper word itself, rather than only the size of its gap from the
greedy word. -/
theorem seamAdjacentCut_above_eq_largestSkipUpperWord_of_support
    {s d : ℕ} {u : Finset ℕ} (hs : 5 ≤ s)
    (hd2 : 2 ≤ d) (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d) (hds : d < s)
    (hsupp : seamWordSupport (seamGreedyWord s) =
      u ∪ Finset.Ico (d + 1) s)
    (hlate : 2 * s < 3 * d) :
    (seamAdjacentCut s hs).above = largestSkipUpperWord s d u := by
  classical
  let lower := largestSkipLowerWord s d u
  let upper := largestSkipUpperWord s d u
  have hlower := largestSkipLowerWord_weight_eq_greedy_of_support
    hd2 hu hds hsupp
  have hgap :=
    three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight
      hd2 hds hu hlate
  have hupperGt :
      wordWeightSum s (seamGreedyWord s).toNatWord <
        wordWeightSum s upper.toNatWord := by
    dsimp [lower, upper] at hlower hgap ⊢
    omega
  have hcandidateAbove : seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum upper := by
    by_contra hnot
    have hle : (seamPerturbedFamily s (by omega)).oldSum upper ≤
        seamSubsetTarget s := Nat.le_of_not_gt hnot
    have hmax := (seamAdjacentCut s hs).below_maximal upper hle
    exact (Nat.not_lt_of_ge hmax) hupperGt
  have hcorrection := exactLateGap_correction_lt_three_mul_gap hs hds hlate
  have hcandidateWindow :
      (seamPerturbedFamily s (by omega)).oldSum upper <
        (seamPerturbedFamily s (by omega)).oldSum
            (seamAdjacentCut s hs).below +
          2 * (seamPerturbedFamily s (by omega)).gap := by
    change wordWeightSum s upper.toNatWord <
      wordWeightSum s (seamGreedyWord s).toNatWord + 2 * 2 ^ (s + 1)
    dsimp [lower, upper] at hlower hgap ⊢
    omega
  have habove :=
    PerturbedFamily.AdjacentCut.above_eq_of_candidate_lt_two_gap
      (seamAdjacentCut s hs) upper hcandidateAbove hcandidateWindow
  simpa [upper] using habove

/-- At a late largest false rank, the actual upper word replaces the filled
strict suffix by the missing boundary rank.  The strict suffix has zero
pulse, so the upper pulse is exactly the lower pulse plus the boundary-rank
pulse. -/
theorem seamAdjacentCut_abovePulse_eq_belowPulse_add_rowPulse_of_largestFalse_late
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    (seamAdjacentCut s hs).abovePulse =
      (seamAdjacentCut s hs).belowPulse + rowPulse s d := by
  classical
  obtain ⟨u, hu, hsupp, hbelowPulse⟩ :=
    exists_lowerPrefix_wordPulse_eq_of_largestFalse_late hd hlate
  have habove :=
    seamAdjacentCut_above_eq_largestSkipUpperWord_of_support
      hs hd.1 hu hd.2.1 hsupp hlate
  have hdnotu : d ∉ u := by
    intro hdu
    exact (Nat.lt_irrefl d) (hu d hdu).2
  have hupperBounds : ∀ e ∈ insert d u, 2 ≤ e ∧ e < s := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | heu
    · exact ⟨hd.1, hd.2.1⟩
    · exact ⟨(hu e heu).1, (hu e heu).2.trans hd.2.1⟩
  have hupperPulse :
      wordPulse s (largestSkipUpperWord s d u).toNatWord =
        rowPulse s d + ∑ e ∈ u, rowPulse s e := by
    rw [wordPulse_eq_sum_seamWordSupport]
    unfold largestSkipUpperWord
    rw [seamWordSupport_seamRowWordOfFinset hupperBounds,
      Finset.sum_insert hdnotu]
  change wordPulse s (seamAdjacentCut s hs).above.toNatWord =
    wordPulse s (seamGreedyWord s).toNatWord + rowPulse s d
  rw [habove, hupperPulse, hbelowPulse]
  omega

/-- At a late largest false rank, the actual adjacent cut has exactly the
explicit largest-skip separation.  This is stated without division. -/
theorem three_mul_remainder_add_overshoot_eq_exactLateGap
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    3 * ((seamAdjacentCut s hs).remainder +
        (seamAdjacentCut s hs).overshoot) =
      3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 := by
  classical
  have hd' := hd
  obtain ⟨hd2, hds, _, _⟩ := hd'
  obtain ⟨u, hu, hsupp⟩ :=
    (isLargestFalseRank_iff_exists_lowerPrefix_fullSuffix
      (seamGreedyWord s) hd2 hds).mp hd
  let lower := largestSkipLowerWord s d u
  let upper := largestSkipUpperWord s d u
  have hlower := largestSkipLowerWord_weight_eq_greedy_of_support
    hd2 hu hds hsupp
  have hgap :=
    three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight
      hd2 hds hu hlate
  have hupperGt :
      wordWeightSum s (seamGreedyWord s).toNatWord <
        wordWeightSum s upper.toNatWord := by
    dsimp [lower, upper] at hlower hgap ⊢
    omega
  have hcandidateAbove : seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum upper := by
    by_contra hnot
    have hle : (seamPerturbedFamily s (by omega)).oldSum upper ≤
        seamSubsetTarget s := Nat.le_of_not_gt hnot
    have hmax := (seamAdjacentCut s hs).below_maximal upper hle
    exact (Nat.not_lt_of_ge hmax) hupperGt
  have hcorrection := exactLateGap_correction_lt_three_mul_gap hs hds hlate
  have hcandidateWindow :
      (seamPerturbedFamily s (by omega)).oldSum upper <
        (seamPerturbedFamily s (by omega)).oldSum
            (seamAdjacentCut s hs).below +
          2 * (seamPerturbedFamily s (by omega)).gap := by
    change wordWeightSum s upper.toNatWord <
      wordWeightSum s (seamGreedyWord s).toNatWord + 2 * 2 ^ (s + 1)
    dsimp [lower, upper] at hlower hgap ⊢
    omega
  have habove :=
    PerturbedFamily.AdjacentCut.above_eq_of_candidate_lt_two_gap
      (seamAdjacentCut s hs) upper hcandidateAbove hcandidateWindow
  have hbelowRem := (seamAdjacentCut s hs).old_below_add_remainder
  have hcapOver := (seamAdjacentCut s hs).capacity_add_overshoot
  change wordWeightSum s (seamGreedyWord s).toNatWord +
      (seamAdjacentCut s hs).remainder = seamSubsetTarget s at hbelowRem
  change seamSubsetTarget s + (seamAdjacentCut s hs).overshoot =
      wordWeightSum s (seamAdjacentCut s hs).above.toNatWord at hcapOver
  rw [habove] at hcapOver
  dsimp [lower, upper] at hlower hgap hupperGt hcandidateAbove hcandidateWindow habove hcapOver ⊢
  omega

/-- The terminal predecessor never contributes to the row pulse once the
row is at least six.  Indeed, after subtracting twice the candidate divisor,
the two new incidence indices leave the fixed remainders three and four,
both strictly smaller than `s - 1`. -/
theorem rowPulse_terminalPred_eq_zero
    {s : ℕ} (hs : 6 ≤ s) :
    rowPulse s (s - 1) = 0 := by
  have hodd : ¬ s - 1 ∣ 2 * s + 1 := by
    intro hdiv
    have htwice : s - 1 ∣ 2 * (s - 1) := ⟨2, by omega⟩
    have hrem : s - 1 ∣ (2 * s + 1) - 2 * (s - 1) :=
      Nat.dvd_sub hdiv htwice
    have heq : (2 * s + 1) - 2 * (s - 1) = 3 := by omega
    rw [heq] at hrem
    have hle : s - 1 ≤ 3 := Nat.le_of_dvd (by norm_num) hrem
    omega
  have heven : ¬ s - 1 ∣ 2 * s + 2 := by
    intro hdiv
    have htwice : s - 1 ∣ 2 * (s - 1) := ⟨2, by omega⟩
    have hrem : s - 1 ∣ (2 * s + 2) - 2 * (s - 1) :=
      Nat.dvd_sub hdiv htwice
    have heq : (2 * s + 2) - 2 * (s - 1) = 4 := by omega
    rw [heq] at hrem
    have hle : s - 1 ≤ 4 := Nat.le_of_dvd (by norm_num) hrem
    omega
  simp [rowPulse, hodd, heven]

/-- If the largest false rank is the terminal predecessor, the explicit
late-gap formula collapses to a constant correction: the adjacent remainder
and overshoot add to exactly `2^(s+1) + 4`. -/
theorem remainder_add_overshoot_eq_of_terminalLargestFalse
    {s : ℕ} (hs : 6 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) (s - 1)) :
    (seamAdjacentCut s (by omega)).remainder +
        (seamAdjacentCut s (by omega)).overshoot =
      2 ^ (s + 1) + 4 := by
  have hgap := three_mul_remainder_add_overshoot_eq_exactLateGap
    (s := s) (d := s - 1) (by omega) hd (by omega)
  have hsub : s - (s - 1) = 1 := by omega
  rw [hsub] at hgap
  have hthree :
      3 * ((seamAdjacentCut s (by omega)).remainder +
          (seamAdjacentCut s (by omega)).overshoot) =
        3 * (2 ^ (s + 1) + 4) := by
    calc
      3 * ((seamAdjacentCut s (by omega)).remainder +
          (seamAdjacentCut s (by omega)).overshoot) =
          3 * 2 ^ (s + 1) + 2 * 4 ^ 1 + 4 := hgap
      _ = 3 * (2 ^ (s + 1) + 4) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) hthree

/-- At a terminal largest false rank the upper replacement has exactly the
same pulse as the greedy lower word.  Thus the terminal reset carries no
hidden incidence correction. -/
theorem seamAdjacentCut_abovePulse_eq_belowPulse_of_terminalLargestFalse
    {s : ℕ} (hs : 6 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) (s - 1)) :
    (seamAdjacentCut s (by omega)).abovePulse =
      (seamAdjacentCut s (by omega)).belowPulse := by
  have hpulse :=
    seamAdjacentCut_abovePulse_eq_belowPulse_add_rowPulse_of_largestFalse_late
      (s := s) (d := s - 1) (by omega) hd (by omega)
  rw [rowPulse_terminalPred_eq_zero hs, add_zero] at hpulse
  exact hpulse

/-- Exact non-tautological reset/middle balance at a late largest false
rank.  If `G = remainder + overshoot` is the actual adjacent gap, `E` is the
upper reset charge, `M` the signed middle coordinate, and `ρ` the boundary
row pulse, then `E + M = 4*G + ρ - 4`. -/
theorem exists_exactLateGap_upperResetCharge_add_middleCoordinate
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    ∃ G : ℕ,
      3 * G = 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 ∧
        (((4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse : ℕ) : ℤ) +
          (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4)) =
        4 * (G : ℤ) + (rowPulse s d : ℤ) - 4 := by
  refine ⟨(seamAdjacentCut s hs).remainder +
      (seamAdjacentCut s hs).overshoot, ?_, ?_⟩
  · exact three_mul_remainder_add_overshoot_eq_exactLateGap hs hd hlate
  · have hpulse :=
      seamAdjacentCut_abovePulse_eq_belowPulse_add_rowPulse_of_largestFalse_late
        hs hd hlate
    push_cast
    omega

/-- Terminal largest-false resets obey an exact conservation law with no
boundary-pulse defect.  The upper reset charge plus the signed middle
coordinate is the fixed dyadic quantity `4 * (2^(s+1) + 4) - 4`. -/
theorem upperResetCharge_add_middleCoordinate_eq_of_terminalLargestFalse
    {s : ℕ} (hs : 6 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) (s - 1)) :
    (((4 * (seamAdjacentCut s (by omega)).overshoot +
          (seamAdjacentCut s (by omega)).abovePulse : ℕ) : ℤ) +
      (4 * ((seamAdjacentCut s (by omega)).remainder : ℤ) -
        ((seamAdjacentCut s (by omega)).belowPulse : ℤ) - 4)) =
      4 * ((2 ^ (s + 1) + 4 : ℕ) : ℤ) - 4 := by
  obtain ⟨G, hG, hbalance⟩ :=
    exists_exactLateGap_upperResetCharge_add_middleCoordinate
      (s := s) (d := s - 1) (by omega) hd (by omega)
  have hsub : s - (s - 1) = 1 := by omega
  rw [hsub] at hG
  norm_num [pow_one] at hG
  have hGexact : G = 2 ^ (s + 1) + 4 := by omega
  rw [hGexact, rowPulse_terminalPred_eq_zero hs] at hbalance
  norm_num at hbalance ⊢
  exact hbalance

/-- At the first two-thirds crossing, the balance has one of two exact
integer offsets: `4*G-2` in the odd boundary cell and `4*G-3` in the even
boundary cell. -/
theorem exists_exactLateGap_upperResetCharge_add_middleCoordinate_firstCrossing
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hcross : ¬ 2 * (s + 1) < 3 * d) :
    ∃ G : ℕ,
      3 * G = 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 ∧
        ((3 * d = 2 * s + 1 ∧
            (((4 * (seamAdjacentCut s hs).overshoot +
                (seamAdjacentCut s hs).abovePulse : ℕ) : ℤ) +
              (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
                ((seamAdjacentCut s hs).belowPulse : ℤ) - 4)) =
              4 * (G : ℤ) - 2) ∨
          (3 * d = 2 * s + 2 ∧
            (((4 * (seamAdjacentCut s hs).overshoot +
                (seamAdjacentCut s hs).abovePulse : ℕ) : ℤ) +
              (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
                ((seamAdjacentCut s hs).belowPulse : ℤ) - 4)) =
              4 * (G : ℤ) - 3)) := by
  obtain ⟨G, hG, hbalance⟩ :=
    exists_exactLateGap_upperResetCharge_add_middleCoordinate hs hd hlate
  refine ⟨G, hG, ?_⟩
  rcases rowPulse_boundary_of_late_firstCrossing hd.1 hlate hcross with
      ⟨hboundary, hpulse⟩ | ⟨hboundary, hpulse⟩
  · exact Or.inl ⟨hboundary, by omega⟩
  · exact Or.inr ⟨hboundary, by omega⟩

/-- In the late largest-false cell, a row-scale-small remainder cannot take
the upper branch.  The exact adjacent gap gives `2^(s+1) < R+O`, while an
upper carry would force both `4R < 2^(s+1)` and `4O ≤ 2^(s+1)`, an
impossible pair. -/
theorem seamRowSmall_not_successorCarries_of_largestFalse_late
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hsmall : seamIntegerGreedyRemainder s < s) :
    ¬ (seamAdjacentCut s hs).successorCarries := by
  intro hcarry
  have hgap :=
    three_mul_remainder_add_overshoot_eq_exactLateGap hs hd hlate
  have hGapStrict : 2 ^ (s + 1) <
      (seamAdjacentCut s hs).remainder +
        (seamAdjacentCut s hs).overshoot := by
    omega
  have hfour := four_mul_le_two_pow_succ hs
  have hR : 4 * (seamAdjacentCut s hs).remainder < 2 ^ (s + 1) := by
    rw [seamAdjacentCut_remainder hs]
    omega
  have hO : 4 * (seamAdjacentCut s hs).overshoot ≤ 2 ^ (s + 1) := by
    change 4 * (seamAdjacentCut s hs).overshoot +
      (seamAdjacentCut s hs).abovePulse ≤ 2 ^ (s + 1) at hcarry
    omega
  have hGapFour : 4 * 2 ^ (s + 1) <
      4 * ((seamAdjacentCut s hs).remainder +
        (seamAdjacentCut s hs).overshoot) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < 4)).2 hGapStrict
  omega

/-- Therefore a late row-scale-small state takes the middle branch
specifically. -/
theorem seamRowSmall_middleBranch_of_largestFalse_late
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hsmall : seamIntegerGreedyRemainder s < s) :
    ¬ (seamAdjacentCut s hs).successorCarries ∧
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight := by
  have hncarry :=
    seamRowSmall_not_successorCarries_of_largestFalse_late
      hs hd hlate hsmall
  have hUM := seamRowSmall_upperOrMiddle hs hsmall
  rcases hUM with hcarry | ⟨_, hmiddle⟩
  · exact False.elim (hncarry hcarry)
  · exact ⟨hncarry, hmiddle⟩

/-- A late row-small state is not merely cleared at the next row.  Its
forced middle transition recovers to within the full linear pulse budget of
the dyadic gap, while the terminal reset preserves the late largest-skip
invariant.  In particular, two row-small states cannot occur consecutively
along a late largest-false orbit. -/
theorem seamRowSmall_late_nextRemainder_recovers
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hsmall : seamIntegerGreedyRemainder s < s) :
    2 ^ (s + 1) - 2 * (s - 2) ≤
        seamIntegerGreedyRemainder (s + 1) ∧
      s + 1 ≤ seamIntegerGreedyRemainder (s + 1) ∧
        LargestSkipLateAt (s + 1) := by
  obtain ⟨hncarry, hmiddle⟩ :=
    seamRowSmall_middleBranch_of_largestFalse_late
      hs hd hlate hsmall
  have hadd := seamMiddleBranch_nextRemainder_add_belowPulse_eq
    hs hncarry hmiddle
  have hpulse :=
    (seamPerturbedFamily s (by omega)).pulse_le
      (seamAdjacentCut s hs).below
  change (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) at hpulse
  have hpow := three_mul_le_two_pow_succ hs
  refine ⟨by omega,
    seamMiddleBranch_nextRemainder_ge_row hs hncarry hmiddle, ?_⟩
  refine ⟨s,
    seamGreedyWord_succ_isLargestFalseRank_terminal_of_middleBranch
      s hs hncarry hmiddle, ?_⟩
  omega

/-- A late row-scale-small state resets its successor's largest false rank
to the old terminal rank, and that rank is automatically late at the next
row.  This is the unconditional descent/reset consequence consumed by any
minimal-counterexample argument. -/
theorem largestSkipLateAt_succ_of_rowSmall
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d)
    (hsmall : seamIntegerGreedyRemainder s < s) :
    LargestSkipLateAt (s + 1) := by
  obtain ⟨hncarry, hmiddle⟩ :=
    seamRowSmall_middleBranch_of_largestFalse_late hs hd hlate hsmall
  refine ⟨s,
    seamGreedyWord_succ_isLargestFalseRank_terminal_of_middleBranch
      s hs hncarry hmiddle, ?_⟩
  omega

/-- Source-coordinate form requested by the reverse-producer argument:
with `G` the exact largest-false adjacent gap, the upper reset charge is
`4 * (G - R_s) + abovePulse`. -/
theorem exists_exactLateGap_upperResetCharge_coordinate
    {s d : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    ∃ G : ℕ,
      3 * G = 3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4 ∧
        4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse =
          4 * (G - (seamAdjacentCut s hs).remainder) +
            (seamAdjacentCut s hs).abovePulse := by
  refine ⟨(seamAdjacentCut s hs).remainder +
      (seamAdjacentCut s hs).overshoot, ?_, ?_⟩
  · exact three_mul_remainder_add_overshoot_eq_exactLateGap hs hd hlate
  · omega

/-- Exact signed distance from an upper-reset charge to any dyadic boundary.
The factor three removes the largest-skip denominator, leaving a completely
explicit affine expression in the source remainder, the largest-false
correction, and the above pulse. -/
theorem three_mul_upperResetCharge_signedDistance_to_dyadic
    {s d j : ℕ} (hs : 5 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) :
    3 * (((2 ^ (s - j + 1) : ℕ) : ℤ) -
          ((4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse : ℕ) : ℤ)) =
      12 * ((seamAdjacentCut s hs).remainder : ℤ) +
        3 * ((2 ^ (s - j + 1) : ℕ) : ℤ) -
        12 * ((2 ^ (s + 1) : ℕ) : ℤ) -
        8 * ((4 ^ (s - d) : ℕ) : ℤ) - 16 -
        3 * ((seamAdjacentCut s hs).abovePulse : ℤ) := by
  have hgap :=
    three_mul_remainder_add_overshoot_eq_exactLateGap hs hd hlate
  have hgapZ :
      3 * (((seamAdjacentCut s hs).remainder : ℤ) +
          ((seamAdjacentCut s hs).overshoot : ℤ)) =
        3 * ((2 ^ (s + 1) : ℕ) : ℤ) +
          2 * ((4 ^ (s - d) : ℕ) : ℤ) + 4 := by
    exact_mod_cast hgap
  push_cast at hgapZ ⊢
  omega

/-- Unscaled form of the same boundary coordinate.  When `j+1 ≤ s`, the
dyadic boundary is four times `2^(s-j-1)`, so its signed distance from the
reset charge is four times the signed distance of the source remainder from
`G - 2^(s-j-1)`, minus the above pulse.  Here the exact gap is represented
on disk as `G = remainder + overshoot`. -/
theorem upperResetCharge_signedDistance_eq_remainderBoundary
    {s j : ℕ} (hs : 5 ≤ s) (hj : j + 1 ≤ s) :
    (((2 ^ (s - j + 1) : ℕ) : ℤ) -
        ((4 * (seamAdjacentCut s hs).overshoot +
          (seamAdjacentCut s hs).abovePulse : ℕ) : ℤ)) =
      4 * (((seamAdjacentCut s hs).remainder : ℤ) +
          ((2 ^ (s - j - 1) : ℕ) : ℤ) -
          (((seamAdjacentCut s hs).remainder +
            (seamAdjacentCut s hs).overshoot : ℕ) : ℤ)) -
        ((seamAdjacentCut s hs).abovePulse : ℤ) := by
  have hpow :
      (2 : ℕ) ^ (s - j + 1) = 4 * 2 ^ (s - j - 1) := by
    rw [show s - j + 1 = (s - j - 1) + 2 by omega,
      pow_succ, pow_succ]
    ring
  rw [hpow]
  push_cast
  ring

/-! ## Exact upper-reset cylinders

The preceding barrier identifies the only remaining ancestry of a late
row-small remainder: an upper reset followed by right branches.  For that
case it is important not to throw away the reset geometry.  The recursive
charge below records every right-branch pulse with its exact base-four
weight.  Its additive form avoids all truncated subtraction.
-/

/-- The accumulated non-gap charge in `k` affine right steps.  The newest
pulse has weight one and all older pulses are multiplied by four. -/
def affineRightRunCharge (pulse : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 4 * affineRightRunCharge pulse k + pulse k + 4

/-- Exact finite iterate of a signed base-four excess orbit.  This is the
division-free form of
`X₀ = X_k / 4^k + ∑_{j<k} (pulse_j+4)/4^(j+1)`. -/
theorem affineRightExcess_exactIterate
    (X : ℕ → ℤ) (pulse : ℕ → ℕ) (k : ℕ)
    (hrec : ∀ j : ℕ, j < k →
      X (j + 1) = 4 * X j - (pulse j : ℤ) - 4) :
    X k + (affineRightRunCharge pulse k : ℤ) =
      ((4 ^ k : ℕ) : ℤ) * X 0 := by
  revert hrec
  induction k with
  | zero =>
      intro _hrec
      simp [affineRightRunCharge]
  | succ k ih =>
      intro hrec
      have hprev := ih (fun j hj ↦ hrec j (by omega))
      have hstep := hrec k (by omega)
      calc
        X (k + 1) + (affineRightRunCharge pulse (k + 1) : ℤ) =
            4 * (X k + (affineRightRunCharge pulse k : ℤ)) := by
          rw [hstep]
          simp only [affineRightRunCharge]
          push_cast
          ring
        _ = 4 * (((4 ^ k : ℕ) : ℤ) * X 0) := by rw [hprev]
        _ = ((4 ^ (k + 1) : ℕ) : ℤ) * X 0 := by
          rw [pow_succ]
          push_cast
          ring

/-- Positivity at the endpoint turns the exact iterate into a strict lower
bound for the initial excess by the finite pulse charge. -/
theorem affineRightExcess_charge_lt_scaledInitial
    (X : ℕ → ℤ) (pulse : ℕ → ℕ) (k : ℕ)
    (hrec : ∀ j : ℕ, j < k →
      X (j + 1) = 4 * X j - (pulse j : ℤ) - 4)
    (hpos : 0 < X k) :
    (affineRightRunCharge pulse k : ℤ) <
      ((4 ^ k : ℕ) : ℤ) * X 0 := by
  have hexact := affineRightExcess_exactIterate X pulse k hrec
  omega

/-- Concrete finite iterate along an eventual seam right tail. -/
theorem eventualRightTail_excess_exactIterate
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ (s : ℕ), S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (k : ℕ) :
    ((seamIntegerGreedyRemainder (S + k) : ℤ) -
        ((2 ^ (S + k) : ℕ) : ℤ)) +
        (affineRightRunCharge
          (fun j ↦ (seamAdjacentCut (S + j) (by omega)).belowPulse) k : ℤ) =
      ((4 ^ k : ℕ) : ℤ) *
        ((seamIntegerGreedyRemainder S : ℤ) -
          ((2 ^ S : ℕ) : ℤ)) := by
  let X : ℕ → ℤ := fun j ↦
    (seamIntegerGreedyRemainder (S + j) : ℤ) -
      ((2 ^ (S + j) : ℕ) : ℤ)
  let pulse : ℕ → ℕ := fun j ↦
    (seamAdjacentCut (S + j) (by omega)).belowPulse
  have hrec : ∀ j : ℕ, j < k →
      X (j + 1) = 4 * X j - (pulse j : ℤ) - 4 := by
    intro j _hj
    have hno : ¬ SeamGreedyUpperOrMiddleAt (S + j) (by omega) := by
      intro hUM
      have hfalse :=
        (seamGreedy_terminal_false_iff_upperOrMiddle
          (S + j) (by omega)).2 hUM
      have htrue :=
        (seamGreedyWord_succ_eq_extend_true_iff_terminal_true
          (S + j) (by omega)).1 (hright (S + j) (by omega))
      simpa [hfalse] using htrue
    simpa [X, pulse, Nat.add_assoc] using
      rightBranch_excess_succ_eq (s := S + j) (by omega) hno
  simpa [X, pulse] using affineRightExcess_exactIterate X pulse k hrec

/-- Exact signed-excess iterate after substituting the genuine middle
landing.  The initial excess is the positive middle coordinate
`4 * remainder - belowPulse`; every later term is consumed by the same
base-four pulse charge as in the generic all-right orbit. -/
theorem middleThenAllRight_excess_exactIterate
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (k : ℕ) :
    ((seamIntegerGreedyRemainder (D + 1 + k) : ℤ) -
        ((2 ^ (D + 1 + k) : ℕ) : ℤ)) +
        (affineRightRunCharge
          (fun j ↦
            (seamAdjacentCut (D + 1 + j) (by omega)).belowPulse) k : ℤ) =
      ((4 ^ k : ℕ) : ℤ) *
        (4 * (seamIntegerGreedyRemainder D : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ)) := by
  classical
  let hs5 : 5 ≤ D := by omega
  let K := seamAdjacentCut D hs5
  have hnext := K.nextRemainder_trichotomy
  rw [if_neg hncarry, if_pos hmiddle,
    seamAdjacentCut_nextRemainder hs5] at hnext
  change seamIntegerGreedyRemainder (D + 1) =
      4 * K.remainder + 2 ^ (D + 1) - K.belowPulse at hnext
  have hpulse := (seamPerturbedFamily D (by omega)).pulse_le K.below
  change K.belowPulse ≤ 2 * (D - 2) at hpulse
  have hpow := four_mul_le_two_pow_succ (s := D) (by omega)
  have hadd : seamIntegerGreedyRemainder (D + 1) + K.belowPulse =
      4 * K.remainder + 2 ^ (D + 1) := by
    omega
  have haddZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hadd
  push_cast at haddZ
  have hKrem : K.remainder = seamIntegerGreedyRemainder D := by
    simpa [K] using seamAdjacentCut_remainder hs5
  have hKremZ : (K.remainder : ℤ) =
      (seamIntegerGreedyRemainder D : ℤ) := by
    exact_mod_cast hKrem
  have hlanding :
      (seamIntegerGreedyRemainder (D + 1) : ℤ) -
          ((2 ^ (D + 1) : ℕ) : ℤ) =
        4 * (seamIntegerGreedyRemainder D : ℤ) -
          (K.belowPulse : ℤ) := by
    omega
  have hiter := eventualRightTail_excess_exactIterate
    (S := D + 1) (by omega) hright k
  rw [hlanding] at hiter
  simpa [K, hs5, Nat.add_assoc] using hiter

/-- Since every eventual-right excess is positive, every finite pulse
charge is strictly below the correspondingly scaled initial excess. -/
theorem eventualRightTail_charge_lt_scaledInitialExcess
    {S : ℕ} (hS5 : 5 ≤ S)
    (hright : ∀ (s : ℕ), S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (k : ℕ) :
    (affineRightRunCharge
        (fun j ↦ (seamAdjacentCut (S + j) (by omega)).belowPulse) k : ℤ) <
      ((4 ^ k : ℕ) : ℤ) *
        ((seamIntegerGreedyRemainder S : ℤ) -
          ((2 ^ S : ℕ) : ℤ)) := by
  have hexact := eventualRightTail_excess_exactIterate hS5 hright k
  have hposNat := eventualRightTail_forces_twoPow_lt_remainder
    hS5 hright (S + k) (by omega)
  have hpos : (0 : ℤ) <
      (seamIntegerGreedyRemainder (S + k) : ℤ) -
        ((2 ^ (S + k) : ℕ) : ℤ) := by
    have hposZ' : ((2 ^ (S + k) : ℕ) : ℤ) <
        (seamIntegerGreedyRemainder (S + k) : ℤ) := by
      exact_mod_cast hposNat
    omega
  omega

/-- The newest pulse creates no independent congruence condition: it
cancels exactly between the terminal middle coordinate and the newest
affine charge digit.  Any stronger base-four obstruction must therefore
come from information beyond the right-run recurrence itself. -/
theorem middleCoordinate_add_affineRightRunCharge_succ
    (R : ℕ) (pulse : ℕ → ℕ) (k : ℕ) :
    (4 * (R : ℤ) - (pulse k : ℤ) - 4) +
        (affineRightRunCharge pulse (k + 1) : ℤ) =
      4 * ((R : ℤ) + (affineRightRunCharge pulse k : ℤ)) := by
  simp only [affineRightRunCharge]
  push_cast
  ring

/-- Iterating

`R_(j+1) + 2^(d+j+2) + pulse_j + 4 = 4 R_j`

from a reset `R_0 + E = 2^(d+1)` gives one exact dyadic cylinder. -/
theorem affineRightRun_exactCylinder
    (R pulse : ℕ → ℕ) (d E k : ℕ)
    (hreset : R (d + 1) + E = 2 ^ (d + 1))
    (hrun : ∀ j : ℕ, j < k →
      R (d + j + 2) + 2 ^ (d + j + 2) + pulse j + 4 =
        4 * R (d + j + 1)) :
    R (d + k + 1) + 4 ^ k * E + affineRightRunCharge pulse k =
      2 ^ (d + k + 1) := by
  revert hrun
  induction k with
  | zero =>
      intro _hrun
      simpa [affineRightRunCharge] using hreset
  | succ k ih =>
      intro hrun
      have hprev := ih (fun j hj => hrun j (by omega))
      have hstep := hrun k (by omega)
      have hpowTwo :
          (2 : ℕ) ^ (d + k + 2) = 2 * 2 ^ (d + k + 1) := by
        rw [show d + k + 2 = (d + k + 1) + 1 by omega, pow_succ]
        ring
      change R (d + k + 2) + 4 ^ (k + 1) * E +
          affineRightRunCharge pulse (k + 1) = 2 ^ (d + k + 2)
      rw [affineRightRunCharge,
        show 4 ^ (k + 1) = 4 ^ k * 4 by rw [pow_succ], hpowTwo]
      ring_nf at hprev hstep ⊢
      omega

/-- If every pulse in a right run is at most the common budget `2*S - 4`,
then the exact accumulated charge satisfies a division-free geometric
bound. -/
theorem three_mul_affineRightRunCharge_add_two_mul_le
    (pulse : ℕ → ℕ) (S k : ℕ)
    (hpulse : ∀ j : ℕ, j < k → pulse j + 4 ≤ 2 * S) :
    3 * affineRightRunCharge pulse k + 2 * S ≤
      2 * S * 4 ^ k := by
  revert hpulse
  induction k with
  | zero =>
      intro _hpulse
      simp [affineRightRunCharge]
  | succ k ih =>
      intro hpulse
      have hprev := ih (fun j hj => hpulse j (by omega))
      have hlast := hpulse k (by omega)
      simp only [affineRightRunCharge, pow_succ]
      ring_nf at hprev hlast ⊢
      omega

/-- On an upper branch, the next remainder and the full reset charge add
exactly to the dyadic gap. -/
theorem seamUpperBranch_remainder_add_resetCharge_eq
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    seamIntegerGreedyRemainder (d + 1) +
        (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) =
      2 ^ (d + 1) := by
  classical
  have hnext := (seamAdjacentCut d hd5).nextRemainder_trichotomy
  rw [if_pos hcarry, seamAdjacentCut_nextRemainder hd5] at hnext
  change seamIntegerGreedyRemainder (d + 1) =
      2 ^ (d + 1) -
        (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) at hnext
  have hcharge := hcarry
  change 4 * (seamAdjacentCut d hd5).overshoot +
      (seamAdjacentCut d hd5).abovePulse ≤ 2 ^ (d + 1) at hcharge
  omega

/-- Additive form of one right-branch recurrence.  Keeping every term on
the natural-number side avoids losing the payment inequalities hidden by
truncated subtraction. -/
theorem seamRightBranch_remainder_add_charge_eq
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hright : (seamAdjacentCut s hs).terminalWeight ≤
      4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse) :
    seamIntegerGreedyRemainder (s + 1) + 2 ^ (s + 1) +
        (seamAdjacentCut s hs).belowPulse + 4 =
      4 * seamIntegerGreedyRemainder s := by
  classical
  have hnterminal : ¬
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight :=
    Nat.not_lt_of_ge hright
  have hnext := (seamAdjacentCut s hs).nextRemainder_trichotomy
  rw [if_neg hncarry, if_neg hnterminal,
    seamAdjacentCut_nextRemainder hs] at hnext
  have hgap : (seamPerturbedFamily s (by omega)).gap = 2 ^ (s + 1) := rfl
  have hrem := seamAdjacentCut_remainder hs
  have hterm := seamAdjacentCut_terminalWeight_eq hs
  have hpulse :=
    (seamPerturbedFamily s (by omega)).pulse_le
      (seamAdjacentCut s hs).below
  change (seamAdjacentCut s hs).belowPulse ≤ 2 * (s - 2) at hpulse
  change seamIntegerGreedyRemainder (s + 1) =
      4 * (seamAdjacentCut s hs).remainder - 2 ^ (s + 1) -
        (seamAdjacentCut s hs).belowPulse - 4 at hnext
  rw [hrem, hgap, hterm] at hright hnterminal
  rw [hrem] at hnext
  omega

/-- Concrete exact cylinder for an upper reset followed by `k` right
recurrences.  The recurrence is accepted in additive form, so callers can
supply it directly from the right-branch trichotomy without any natural
subtraction side conditions. -/
theorem seamUpperThenRightRun_exactCylinder
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    seamIntegerGreedyRemainder (d + k + 1) +
          4 ^ k *
            (4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse) +
          affineRightRunCharge
            (fun j ↦
              (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k =
      2 ^ (d + k + 1) := by
  apply affineRightRun_exactCylinder
  · exact seamUpperBranch_remainder_add_resetCharge_eq hd5 hcarry
  · exact hrun

/-- An upper reset cannot be followed by more right steps than its reset
row.  The exact cylinder already proves this: the reset charge is at least
four, so `k > d` would make its `4^k`-dilate exceed the whole dyadic
capacity `2^(d+k+1)`. -/
theorem seamUpperThenRightRun_length_le_resetRow
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    k ≤ d := by
  let E := 4 * (seamAdjacentCut d hd5).overshoot +
    (seamAdjacentCut d hd5).abovePulse
  have hcylinder :=
    seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E +
      affineRightRunCharge
        (fun j ↦
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k =
      2 ^ (d + k + 1) at hcylinder
  have hover : 1 ≤ (seamAdjacentCut d hd5).overshoot := by
    unfold PerturbedFamily.AdjacentCut.overshoot
    have habove := (seamAdjacentCut d hd5).above_strict
    omega
  have hE : 4 ≤ E := by
    dsimp [E]
    omega
  by_contra hk
  have hdk : d < k := Nat.lt_of_not_ge hk
  have hpow : 2 ^ (d + k + 1) < 4 ^ k * 4 := by
    calc
      2 ^ (d + k + 1) < 2 ^ (2 * (k + 1)) :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ = 4 ^ k * 4 := by
        rw [show (4 : ℕ) ^ k = 2 ^ (2 * k) by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]]
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
        norm_num
  have hweighted : 4 ^ k * 4 ≤ 4 ^ k * E :=
    Nat.mul_le_mul_left _ hE
  omega

/-- The exact reverse coordinate of an upper reset followed by `k` right
steps.  After scaling the gap from the reset charge to the next relevant
dyadic threshold by `4^(k+1)`, it is exactly the terminal middle coordinate
plus the full `(k+1)`-step affine pulse charge.  Thus every possible
congruence obstruction is retained, rather than lost in a one-sided bound.
-/
theorem seamUpperThenRightRun_scaledDyadicGap_eq_middleCoordinate_add_charge
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    (((4 ^ (k + 1) : ℕ) : ℤ) *
        (((2 ^ (d - k + 1) : ℕ) : ℤ) -
          ((4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse : ℕ) : ℤ))) =
      (4 * (seamIntegerGreedyRemainder (d + k + 1) : ℤ) -
          ((seamAdjacentCut (d + k + 1) (by omega)).belowPulse : ℤ) - 4) +
        (affineRightRunCharge
          (fun j ↦
            (seamAdjacentCut (d + j + 1) (by omega)).belowPulse)
          (k + 1) : ℤ) := by
  let pulse : ℕ → ℕ := fun j ↦
    (seamAdjacentCut (d + j + 1) (by omega)).belowPulse
  have hcylinder :=
    seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  change seamIntegerGreedyRemainder (d + k + 1) +
      4 ^ k *
        (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) +
      affineRightRunCharge pulse k = 2 ^ (d + k + 1) at hcylinder
  have hbase :
      4 ^ k * 2 ^ (d - k + 1) = 2 ^ (d + k + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hfactor :
      4 ^ (k + 1) * 2 ^ (d - k + 1) =
        4 * 2 ^ (d + k + 1) := by
    calc
      4 ^ (k + 1) * 2 ^ (d - k + 1) =
          4 * (4 ^ k * 2 ^ (d - k + 1)) := by
            rw [pow_succ]
            ring
      _ = 4 * 2 ^ (d + k + 1) := by rw [hbase]
  have hcylinderZ :
      (seamIntegerGreedyRemainder (d + k + 1) : ℤ) +
          (4 ^ k : ℤ) *
            (4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse) +
          (affineRightRunCharge pulse k : ℤ) =
        (2 ^ (d + k + 1) : ℤ) := by
    exact_mod_cast hcylinder
  have hfactorZ :
      (4 ^ (k + 1) : ℤ) * (2 ^ (d - k + 1) : ℤ) =
        4 * (2 ^ (d + k + 1) : ℤ) := by
    exact_mod_cast hfactor
  change (4 ^ (k + 1) : ℤ) *
      ((2 ^ (d - k + 1) : ℤ) -
        (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse : ℤ)) = _
  change _ =
      (4 * (seamIntegerGreedyRemainder (d + k + 1) : ℤ) -
          (pulse k : ℤ) - 4) +
        (affineRightRunCharge pulse (k + 1) : ℤ)
  simp only [affineRightRunCharge]
  push_cast
  rw [pow_succ] at hfactorZ ⊢
  ring_nf at hcylinderZ hfactorZ ⊢
  omega

/-- Along the concrete interval, the accumulated pulse charge is strictly
smaller than one terminal-row multiple of `4^k`. -/
theorem seamRightRunCharge_lt_row_mul_four_pow
    {d k : ℕ} (hd5 : 5 ≤ d) :
    affineRightRunCharge
          (fun j ↦
            (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k <
      (d + k) * 4 ^ k := by
  let pulse : ℕ → ℕ := fun j ↦
    (seamAdjacentCut (d + j + 1) (by omega)).belowPulse
  have hpulse : ∀ j : ℕ, j < k → pulse j + 4 ≤ 2 * (d + k) := by
    intro j hj
    have hp :=
      (seamPerturbedFamily (d + j + 1) (by omega)).pulse_le
        (seamAdjacentCut (d + j + 1) (by omega)).below
    have hp' : pulse j ≤ 2 * (d + j + 1 - 2) := by
      simpa [pulse] using hp
    omega
  have hcharge :=
    three_mul_affineRightRunCharge_add_two_mul_le pulse (d + k) k hpulse
  have hpos : 0 < (d + k) * 4 ^ k := by positivity
  have hdouble : 2 * (d + k) * 4 ^ k =
      2 * ((d + k) * 4 ^ k) := by ring
  rw [hdouble] at hcharge
  change affineRightRunCharge pulse k < (d + k) * 4 ^ k
  omega

/-- A row-small terminal state after an upper reset forces the reset charge,
together with the explicitly bounded pulse charge, to occupy almost the
entire dyadic cylinder.  This is the exact reverse-producer lower bound; it
retains the upper word's overshoot geometry rather than reducing to the
scalar source remainder. -/
theorem seamUpperThenRightRun_rowSmall_forces_resetCylinder
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hsmall : seamIntegerGreedyRemainder (d + k + 1) < d + k + 1) :
    2 ^ (d + k + 1) < d + k + 1 +
      4 ^ k *
        (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) +
      affineRightRunCharge
        (fun j ↦
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k := by
  have hcylinder :=
    seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  omega

/-- In any additive cylinder `remainder + charge = capacity`, a row-small
remainder is exactly the assertion that the charge lies in the top `row`
window below capacity. -/
theorem remainder_lt_iff_charge_in_topWindow
    {remainder charge capacity row : ℕ}
    (hcylinder : remainder + charge = capacity) :
    remainder < row ↔
      charge ≤ capacity ∧ capacity < row + charge := by
  omega

/-- If `remainder + charge = H`, the middle-branch inequality at the next
doubling scale is exactly the assertion that the next base-four charge has
crossed its dyadic capacity.  This is the algebraic reason a middle reset
sits immediately above the row-small right window. -/
theorem middleInequality_iff_nextCharge_exceeds
    {remainder charge H pulse : ℕ}
    (hcylinder : remainder + charge = H)
    (hpulse : pulse ≤ 4 * remainder + 2 * H) :
    4 * remainder + 2 * H - pulse < 4 * H + 4 ↔
      2 * H < 4 * charge + pulse + 4 := by
  omega

/-- Exact reverse-producer classification: after an upper reset and a
right run, a row-small endpoint is equivalent to one explicit top window
for the base-four weighted reset-and-pulse charge. -/
theorem seamUpperThenRightRun_rowSmall_iff_resetCylinderWindow
    {d k : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    seamIntegerGreedyRemainder (d + k + 1) < d + k + 1 ↔
      4 ^ k *
            (4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse) +
          affineRightRunCharge
            (fun j ↦
              (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k ≤
        2 ^ (d + k + 1) ∧
      2 ^ (d + k + 1) < d + k + 1 +
        (4 ^ k *
            (4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse) +
          affineRightRunCharge
            (fun j ↦
              (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k) := by
  apply remainder_lt_iff_charge_in_topWindow
  simpa [Nat.add_assoc] using
    (seamUpperThenRightRun_exactCylinder hd5 hcarry hrun)

/-- After dividing out the base-four length of the right run, a row-small
terminal state forces an exponential lower bound on the *upper reset
charge* itself.  The loss is only twice the terminal row.  Under the late
largest-false geometry one has `k ≤ d`, so the exponent `d-k+1` is the
natural reverse-producer scale. -/
theorem seamUpperThenRightRun_rowSmall_forces_resetCharge_lower
    {d k : ℕ} (hd5 : 5 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1))
    (hsmall : seamIntegerGreedyRemainder (d + k + 1) < d + k + 1) :
    2 ^ (d - k + 1) <
      4 * (seamAdjacentCut d hd5).overshoot +
        (seamAdjacentCut d hd5).abovePulse + 2 * (d + k) := by
  let E := 4 * (seamAdjacentCut d hd5).overshoot +
    (seamAdjacentCut d hd5).abovePulse
  let pulse : ℕ → ℕ := fun j ↦
    (seamAdjacentCut (d + j + 1) (by omega)).belowPulse
  have hcylinder :=
    seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
  change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E +
      affineRightRunCharge pulse k = 2 ^ (d + k + 1) at hcylinder
  have hcharge :=
    seamRightRunCharge_lt_row_mul_four_pow (d := d) (k := k) hd5
  change affineRightRunCharge pulse k < (d + k) * 4 ^ k at hcharge
  have hfour : 1 ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hrowWeighted :
      seamIntegerGreedyRemainder (d + k + 1) ≤ (d + k) * 4 ^ k := by
    calc
      seamIntegerGreedyRemainder (d + k + 1) ≤ d + k := by omega
      _ = (d + k) * 1 := by omega
      _ ≤ (d + k) * 4 ^ k := Nat.mul_le_mul_left _ hfour
  have hfactor :
      4 ^ k * 2 ^ (d - k + 1) = 2 ^ (d + k + 1) := by
    rw [show 4 ^ k = 2 ^ (2 * k) by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
    congr 1
    omega
  have hweighted : 4 ^ k * 2 ^ (d - k + 1) <
      4 ^ k * (E + 2 * (d + k)) := by
    rw [hfactor]
    ring_nf at hcylinder hcharge hrowWeighted ⊢
    omega
  exact (Nat.mul_lt_mul_left (pow_pos (by norm_num) k)).mp hweighted

/-! ## A two-sided dyadic branch invariant

There is a substantially smaller local obstruction than the full reset-band
socket.  At row `s`, compare both sides of the adjacent cut with `2^s`.
The upper branch always puts the next lower remainder below `2^(s+1)`.
On the middle branch, the lower candidate and its terminal toggle show that
one of the two next distances is below `2^(s+1)`, except when the signed
middle coordinate is one of `-3, -2, -1`.  On the right branch the lower
side of the invariant propagates unconditionally; the upper side propagates
as soon as its pulse-corrected charge does not cross `2^(s+2)`.

The lemmas in this section are unconditional branch algebra.  They isolate
the two actual-run cells which a future induction must exclude; they do not
assert that those cells are absent.
-/

/-- Any explicit word above the seam target bounds the overshoot of the
minimal adjacent upper word by its own excess. -/
theorem seamAdjacentCut_overshoot_le_candidateExcess
    {s : ℕ} (hs : 5 ≤ s) (x : SeamRowWord s)
    (hx : seamSubsetTarget s < wordWeightSum s x.toNatWord) :
    (seamAdjacentCut s hs).overshoot ≤
      wordWeightSum s x.toNatWord - seamSubsetTarget s := by
  have hmin := (seamAdjacentCut s hs).above_minimal x hx
  have hover := (seamAdjacentCut s hs).capacity_add_overshoot
  change wordWeightSum s (seamAdjacentCut s hs).above.toNatWord ≤
      wordWeightSum s x.toNatWord at hmin
  change seamSubsetTarget s + (seamAdjacentCut s hs).overshoot =
      wordWeightSum s (seamAdjacentCut s hs).above.toNatWord at hover
  omega

/-- An upper successor always satisfies the lower half of the next-row
two-sided dyadic invariant. -/
theorem seamUpperBranch_nextRemainder_le_pow
    {s : ℕ} (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) := by
  have hreset := seamUpperBranch_remainder_add_resetCharge_eq hs hcarry
  omega

/-- Upper resets are isolated: an upper branch cannot be followed by a
second upper branch.  The first reset makes the next row's terminal rank
the largest false rank; its exact terminal gap then forces the next
overshoot far above the next upper-charge budget. -/
theorem seamUpperBranch_next_not_successorCarries
    {s : ℕ} (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    ¬ (seamAdjacentCut (s + 1) (by omega)).successorCarries := by
  intro hnext
  have hdNext :=
    seamGreedyWord_succ_isLargestFalseRank_terminal_of_upperBranch
      s hs hcarry
  have hgap :=
    remainder_add_overshoot_eq_of_terminalLargestFalse
      (s := s + 1) (by omega) hdNext
  have hR := seamUpperBranch_nextRemainder_le_pow hs hcarry
  rw [seamAdjacentCut_remainder (by omega)] at hgap
  have hcharge := hnext
  change 4 * (seamAdjacentCut (s + 1) (by omega)).overshoot +
      (seamAdjacentCut (s + 1) (by omega)).abovePulse ≤
        2 ^ (s + 2) at hcharge
  have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
    ring
  rw [hpow] at hgap hcharge
  omega

/-- Outside the three signed cells `-3,-2,-1`, a middle successor satisfies
one side of the next-row dyadic invariant.  If the coordinate is at most
`-4`, the untoggled lower candidate already has small remainder.  If it is
nonnegative, toggling its terminal bit supplies an upper candidate with
small excess. -/
theorem seamMiddleBranch_next_twoSided_of_not_neg_small
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hcell :
      4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≤ -4 ∨
        0 ≤ 4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4) :
    seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) ∨
      (seamAdjacentCut (s + 1) (by omega)).overshoot ≤ 2 ^ (s + 1) := by
  classical
  let K := seamAdjacentCut s hs
  change ¬ K.successorCarries at hncarry
  change 4 * K.remainder + (seamPerturbedFamily s (by omega)).gap -
      K.belowPulse < K.terminalWeight at hmiddle
  change 4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 ≤ -4 ∨
      0 ≤ 4 * (K.remainder : ℤ) - (K.belowPulse : ℤ) - 4 at hcell
  have htri := K.nextRemainder_trichotomy
  rw [if_neg hncarry, if_pos hmiddle,
    seamAdjacentCut_nextRemainder hs] at htri
  unfold PerturbedFamily.AdjacentCut.belowPulse at htri hmiddle hcell
  rcases hcell with hnegative | hnonnegative
  · left
    change seamIntegerGreedyRemainder (s + 1) =
      4 * K.remainder + (seamPerturbedFamily s (by omega)).gap -
        (seamPerturbedFamily s (by omega)).pulse K.below at htri
    have hgap : (seamPerturbedFamily s (by omega)).gap =
        2 ^ (s + 1) := rfl
    rw [hgap] at htri
    omega
  · right
    let x : SeamRowWord (s + 1) := K.below.extend true
    have hbelow := K.old_below_add_remainder
    have hword := wordWeightSum_rowWord_extend (by omega : 3 ≤ s)
      K.below true
    have hterminal := seamAdjacentCut_terminalWeight_eq hs
    change K.terminalWeight = 2 * 2 ^ (s + 1) + 4 at hterminal
    have htarget := seamSubsetTarget_succ (s := s) (by omega : 2 ≤ s)
    have hpow : (2 : ℕ) ^ (s + 2) = 2 * 2 ^ (s + 1) := by
      rw [show s + 2 = s + 1 + 1 by omega, pow_succ]
      ring
    have hx : seamSubsetTarget (s + 1) <
        wordWeightSum (s + 1) x.toNatWord := by
      dsimp [x]
      change wordWeightSum (s + 1) (K.below.extend true).toNatWord =
          (seamPerturbedFamily s (by omega)).newSum K.below +
            (2 ^ (s + 2) + 4) at hword
      change (seamPerturbedFamily s (by omega)).oldSum K.below +
          K.remainder = seamSubsetTarget s at hbelow
      have hgap : (seamPerturbedFamily s (by omega)).gap =
          2 ^ (s + 1) := rfl
      rw [hgap, hterminal] at hmiddle
      change seamSubsetTarget (s + 1) =
        4 * seamSubsetTarget s + 2 ^ (s + 1) at htarget
      unfold PerturbedFamily.newSum at hword
      rw [hpow] at hword
      omega
    have hbound := seamAdjacentCut_overshoot_le_candidateExcess
      (s := s + 1) (by omega) x hx
    change (seamAdjacentCut (s + 1) (by omega)).overshoot ≤
      wordWeightSum (s + 1) (K.below.extend true).toNatWord -
        seamSubsetTarget (s + 1) at hbound
    change wordWeightSum (s + 1) (K.below.extend true).toNatWord =
        (seamPerturbedFamily s (by omega)).newSum K.below +
          (2 ^ (s + 2) + 4) at hword
    change (seamPerturbedFamily s (by omega)).oldSum K.below +
        K.remainder = seamSubsetTarget s at hbelow
    change seamSubsetTarget (s + 1) =
      4 * seamSubsetTarget s + 2 ^ (s + 1) at htarget
    unfold PerturbedFamily.newSum at hword
    rw [hpow] at hword
    omega

/-- The remainder witness of the two-sided dyadic invariant is strictly
preserved by a right successor. -/
theorem seamRightBranch_nextRemainder_le_pow_of_remainder_le
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hright : (seamAdjacentCut s hs).terminalWeight ≤
      4 * (seamAdjacentCut s hs).remainder +
        (seamPerturbedFamily s (by omega)).gap -
        (seamAdjacentCut s hs).belowPulse)
    (hrem : seamIntegerGreedyRemainder s ≤ 2 ^ s) :
    seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) := by
  have hstep := seamRightBranch_remainder_add_charge_eq hs hncarry hright
  rw [pow_succ]
  omega

/-- The overshoot witness is preserved by a right successor whenever its
pulse-corrected upper charge stays below twice the old gap.  The negation of
this hypothesis is exactly the narrow pulse leak left by the raw bound
`overshoot ≤ 2^s`. -/
theorem seamRightBranch_nextOvershoot_le_pow_of_charge_le
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hcharge :
      4 * (seamAdjacentCut s hs).overshoot +
          (seamAdjacentCut s hs).abovePulse ≤ 2 ^ (s + 2)) :
    (seamAdjacentCut (s + 1) (by omega)).overshoot ≤ 2 ^ (s + 1) := by
  let K := seamAdjacentCut s hs
  change ¬ K.successorCarries at hncarry
  change 4 * K.overshoot + K.abovePulse ≤ 2 ^ (s + 2) at hcharge
  let x : SeamRowWord (s + 1) := K.above.extend false
  have hover := K.capacity_add_overshoot
  have hword := wordWeightSum_rowWord_extend (by omega : 3 ≤ s)
    K.above false
  have htarget := seamSubsetTarget_succ (s := s) (by omega : 2 ≤ s)
  have hgap : (seamPerturbedFamily s (by omega)).gap = 2 ^ (s + 1) := rfl
  have hpow : (2 : ℕ) ^ (s + 2) = 4 * 2 ^ s := by
    rw [show s + 2 = s + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  have hnocarry : 2 ^ (s + 1) <
      4 * K.overshoot + K.abovePulse := by
    unfold PerturbedFamily.AdjacentCut.successorCarries at hncarry
    rw [hgap] at hncarry
    omega
  unfold PerturbedFamily.AdjacentCut.abovePulse at hnocarry hcharge
  have hx : seamSubsetTarget (s + 1) <
      wordWeightSum (s + 1) x.toNatWord := by
    dsimp [x]
    change wordWeightSum (s + 1) (K.above.extend false).toNatWord =
        (seamPerturbedFamily s (by omega)).newSum K.above at hword
    change seamSubsetTarget s + K.overshoot =
      (seamPerturbedFamily s (by omega)).oldSum K.above at hover
    change seamSubsetTarget (s + 1) =
      4 * seamSubsetTarget s + 2 ^ (s + 1) at htarget
    unfold PerturbedFamily.newSum at hword
    omega
  have hbound := seamAdjacentCut_overshoot_le_candidateExcess
    (s := s + 1) (by omega) x hx
  change (seamAdjacentCut (s + 1) (by omega)).overshoot ≤
    wordWeightSum (s + 1) (K.above.extend false).toNatWord -
      seamSubsetTarget (s + 1) at hbound
  change wordWeightSum (s + 1) (K.above.extend false).toNatWord =
      (seamPerturbedFamily s (by omega)).newSum K.above at hword
  change seamSubsetTarget s + K.overshoot =
    (seamPerturbedFamily s (by omega)).oldSum K.above at hover
  change seamSubsetTarget (s + 1) =
    4 * seamSubsetTarget s + 2 ^ (s + 1) at htarget
  unfold PerturbedFamily.newSum at hword
  rw [hpow] at hcharge
  omega

/-- A raw overshoot witness therefore propagates unless it lies in the
explicit pulse leak above twice the old gap. -/
theorem seamRightBranch_nextOvershoot_le_pow_of_overshoot_le_of_noPulseLeak
    {s : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hover : (seamAdjacentCut s hs).overshoot ≤ 2 ^ s)
    (hnoleak :
      4 * (seamAdjacentCut s hs).overshoot +
          (seamAdjacentCut s hs).abovePulse ≤ 2 ^ (s + 2)) :
    (seamAdjacentCut (s + 1) (by omega)).overshoot ≤ 2 ^ (s + 1) := by
  exact seamRightBranch_nextOvershoot_le_pow_of_charge_le hs hncarry hnoleak

/-- The complement of the safe middle-coordinate range consists of exactly
three integers. -/
theorem seamMiddleCoordinate_not_safe_iff_three_cells
    {s : ℕ} (hs : 5 ≤ s) :
    ¬ (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
          ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≤ -4 ∨
        0 ≤ 4 * ((seamAdjacentCut s hs).remainder : ℤ) -
          ((seamAdjacentCut s hs).belowPulse : ℤ) - 4) ↔
      4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -3 ∨
        4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -2 ∨
        4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -1 := by
  omega

/-- In a middle cell `4*R = pulse + c`, the pulse part of `4*R` is already
absorbed by the exact floor error.  Hence the corrected rational coordinate
`4*Z` is bounded by the bare cell label `c`. -/
theorem seamMiddleCell_four_mul_floorZ_le
    {s c : ℕ} (hs : 5 ≤ s)
    (hcell :
      4 * (seamAdjacentCut s hs).remainder =
        (seamAdjacentCut s hs).belowPulse + c) :
    4 * seamGreedyFloorZ s ≤ (c : ℚ) := by
  let K := seamAdjacentCut s hs
  have hpulse := wordPulse_le_four_mul_seamWordFloorError
    (by omega : 3 ≤ s) K.below
  change (K.belowPulse : ℚ) ≤ 4 * seamGreedyFloorError s at hpulse
  have hrem := seamAdjacentCut_remainder hs
  change K.remainder = seamIntegerGreedyRemainder s at hrem
  have hremQ :
      (K.remainder : ℚ) = (seamIntegerGreedyRemainder s : ℚ) := by
    exact_mod_cast hrem
  have hcellQ :
      4 * (K.remainder : ℚ) = (K.belowPulse : ℚ) + (c : ℚ) := by
    exact_mod_cast hcell
  rw [seamGreedyFloorZ_eq_remainder_sub_error s hs]
  linarith

/-- On an actual middle transition, the preceding cancellation bounds the
scaled rational residual by the binary tail channel plus the cell label.
For the first exceptional cell this leaves only `1`, strictly less than the
true correction-tail slack `4/3 + ε`. -/
theorem seamMiddleCell_scaledRationalRemainder_le
    {s c : ℕ} (hs : 5 ≤ s)
    (hncarry : ¬ (seamAdjacentCut s hs).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight)
    (hcell :
      4 * (seamAdjacentCut s hs).remainder =
        (seamAdjacentCut s hs).belowPulse + c) :
    (4 : ℚ) ^ (s + 1) *
          seamWordRationalRemainder (seamGreedyWord (s + 1)) ≤
      (2 : ℚ) ^ (s + 2) + c := by
  have hZ := seamMiddleCell_four_mul_floorZ_le hs hcell
  have hnext := seamGreedyFloorZ_succ_middle s hs hncarry hmiddle
  have hrem := seamWordRationalRemainder_eq_pow_add_floorZ_div
    (by omega : 1 ≤ s + 1) (seamGreedyWord (s + 1))
  calc
    (4 : ℚ) ^ (s + 1) *
          seamWordRationalRemainder (seamGreedyWord (s + 1)) =
        (2 : ℚ) ^ (s + 1) + seamGreedyFloorZ (s + 1) := by
      rw [hrem]
      change (4 : ℚ) ^ (s + 1) *
          (((2 : ℚ) ^ (s + 1) + seamGreedyFloorZ (s + 1)) /
            (4 : ℚ) ^ (s + 1)) = _
      field_simp
    _ = (2 : ℚ) ^ (s + 2) + 4 * seamGreedyFloorZ s := by
      rw [hnext, show s + 2 = (s + 1) + 1 by omega, pow_succ]
      ring
    _ ≤ (2 : ℚ) ^ (s + 2) + c := by linarith

/-- Under the raw overshoot witness, a right-branch pulse leak is exactly a
distance cell immediately below `2^s`; its distance `k` satisfies
`4*k < abovePulse`. -/
theorem seamRightPulseLeak_iff_distanceCell
    {s : ℕ} (hs : 5 ≤ s)
    (hover : (seamAdjacentCut s hs).overshoot ≤ 2 ^ s) :
    2 ^ (s + 2) <
          4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse ↔
      ∃ k : ℕ,
        (seamAdjacentCut s hs).overshoot = 2 ^ s - k ∧
          4 * k < (seamAdjacentCut s hs).abovePulse := by
  have hpow : (2 : ℕ) ^ (s + 2) = 4 * 2 ^ s := by
    rw [show s + 2 = s + 1 + 1 by omega, pow_succ, pow_succ]
    ring
  rw [hpow]
  constructor
  · intro hleak
    refine ⟨2 ^ s - (seamAdjacentCut s hs).overshoot, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨k, hk, hpulse⟩
    omega

/-! ### Pure-half prefix coordinate

The same two-sided invariant has a useful one-coordinate normal form.  Run
the descending integer greedy algorithm on the old-rank seam weights, but at
the unshifted half capacity `2^(2*s-1)`.  This capacity is exactly `2^s`
above the seam target.  The greedy sum is therefore the seam upper word when
that word lies in the added half-gap, and the seam lower word otherwise.
-/

def seamPureHalfPrefixRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (2 ^ (2 * s - 1))

/-- Exact cut formula for the pure-half prefix residual.  Below the upper
midpoint it is `2^s - overshoot`; above that midpoint it is
`2^s + remainder`. -/
theorem seamPureHalfPrefixRemainder_eq_ite
    {s : ℕ} (hs : 5 ≤ s) :
    seamPureHalfPrefixRemainder s =
      if (seamAdjacentCut s hs).overshoot ≤ 2 ^ s then
        2 ^ s - (seamAdjacentCut s hs).overshoot
      else
        2 ^ s + seamIntegerGreedyRemainder s := by
  classical
  let K := seamAdjacentCut s hs
  let D := 2 ^ (2 * s - 1)
  let bits := integerGreedyBits (seamWeights s) D
  let G := weightedBoolSum (seamWeights s) bits
  have hbitsLength : bits.length = s - 2 := by
    dsimp [bits]
    rw [integerGreedyBits_length, seamWeights_length_eq]
  let gword : SeamRowWord s := SeamRowWord.ofList bits hbitsLength
  have hgwordSum : wordWeightSum s gword.toNatWord = G := by
    rw [← weightedBoolSum_toList_eq_wordWeightSum (by omega : 2 ≤ s)]
    dsimp [gword]
    rw [SeamRowWord.toList_ofList]
  have hGadm : G ≤ D := by
    exact integerGreedyBits_admissible (seamWeights s) D
  have hcap : seamSubsetTarget s + 2 ^ s = D := by
    dsimp [D]
    unfold seamSubsetTarget
    have hpow : 2 ^ s ≤ 2 ^ (2 * s - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbelow := K.old_below_add_remainder
  change wordWeightSum s K.below.toNatWord + K.remainder =
    seamSubsetTarget s at hbelow
  have habove := K.capacity_add_overshoot
  change seamSubsetTarget s + K.overshoot =
    wordWeightSum s K.above.toNatWord at habove
  have hgap : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by
    rw [pow_succ]
    ring
  by_cases hover : K.overshoot ≤ 2 ^ s
  · rw [if_pos hover]
    have haboveAdm : weightedBoolSum (seamWeights s) K.above.toList ≤ D := by
      rw [weightedBoolSum_toList_eq_wordWeightSum (by omega : 2 ≤ s)]
      omega
    have haboveLeG : wordWeightSum s K.above.toNatWord ≤ G := by
      have hmax := integerGreedyBits_maximal
        (gap := 2 ^ (s + 1)) (by positivity)
        (seamWeights_gapDominates (by omega : 2 ≤ s))
        (bits := K.above.toList)
        (by simp [SeamRowWord.toList]) haboveAdm
      change weightedBoolSum (seamWeights s) K.above.toList ≤ G at hmax
      rwa [weightedBoolSum_toList_eq_wordWeightSum (by omega : 2 ≤ s)] at hmax
    have hGleAbove : G ≤ wordWeightSum s K.above.toNatWord := by
      by_contra hnot
      have hstrict : wordWeightSum s K.above.toNatWord < G := by omega
      have hne : K.above.toList ≠ bits := by
        intro heq
        have heqsum : wordWeightSum s K.above.toNatWord = G := by
          rw [← weightedBoolSum_toList_eq_wordWeightSum
            (by omega : 2 ≤ s), heq]
        omega
      have hsep := weightedBoolSum_separated
        (gap := 2 ^ (s + 1)) (weights := seamWeights s)
        (by positivity) (seamWeights_gapDominates (by omega : 2 ≤ s))
        (a := K.above.toList) (b := bits)
        (by simp [SeamRowWord.toList])
        (by dsimp [bits]; rw [integerGreedyBits_length]) hne
      rw [weightedBoolSum_toList_eq_wordWeightSum
        (by omega : 2 ≤ s)] at hsep
      change wordWeightSum s K.above.toNatWord + 2 ^ (s + 1) ≤ G ∨
        G + 2 ^ (s + 1) ≤ wordWeightSum s K.above.toNatWord at hsep
      rcases hsep with hsep | hsep <;> omega
    have hGeq : G = wordWeightSum s K.above.toNatWord := by omega
    unfold seamPureHalfPrefixRemainder integerGreedyRemainder
    change D - G = 2 ^ s - K.overshoot
    omega
  · rw [if_neg hover]
    have haboveGtD : D < wordWeightSum s K.above.toNatWord := by omega
    have hGleTarget : G ≤ seamSubsetTarget s := by
      by_contra hnot
      have htargetLtG : seamSubsetTarget s < G := by omega
      have htargetLtWord : seamSubsetTarget s <
          wordWeightSum s gword.toNatWord := by rwa [hgwordSum]
      have hmin := K.above_minimal gword htargetLtWord
      change wordWeightSum s K.above.toNatWord ≤
        wordWeightSum s gword.toNatWord at hmin
      rw [hgwordSum] at hmin
      omega
    have hGleBelow : G ≤ wordWeightSum s K.below.toNatWord := by
      have hgwordLeTarget :
          (seamPerturbedFamily s (by omega)).oldSum gword ≤
            seamSubsetTarget s := by
        change wordWeightSum s gword.toNatWord ≤ seamSubsetTarget s
        rwa [hgwordSum]
      have hmax := K.below_maximal gword hgwordLeTarget
      change wordWeightSum s gword.toNatWord ≤
        wordWeightSum s K.below.toNatWord at hmax
      rwa [hgwordSum] at hmax
    have hbelowAdm : weightedBoolSum (seamWeights s) K.below.toList ≤ D := by
      rw [weightedBoolSum_toList_eq_wordWeightSum (by omega : 2 ≤ s)]
      omega
    have hbelowLeG : wordWeightSum s K.below.toNatWord ≤ G := by
      have hmax := integerGreedyBits_maximal
        (gap := 2 ^ (s + 1)) (by positivity)
        (seamWeights_gapDominates (by omega : 2 ≤ s))
        (bits := K.below.toList)
        (by simp [SeamRowWord.toList]) hbelowAdm
      change weightedBoolSum (seamWeights s) K.below.toList ≤ G at hmax
      rwa [weightedBoolSum_toList_eq_wordWeightSum (by omega : 2 ≤ s)] at hmax
    have hGeq : G = wordWeightSum s K.below.toNatWord := by omega
    have hrem := seamAdjacentCut_remainder hs
    change K.remainder = seamIntegerGreedyRemainder s at hrem
    rw [hrem] at hbelow
    unfold seamPureHalfPrefixRemainder integerGreedyRemainder
    change D - G = 2 ^ s + seamIntegerGreedyRemainder s
    omega

/-- Consequently the two-sided dyadic cut bound is exactly the single
pure-half prefix estimate with the complete omitted-tail budget
`2^(s+1)`. -/
theorem seamPureHalfPrefixRemainder_le_iff_twoSided
    {s : ℕ} (hs : 5 ≤ s) :
    seamPureHalfPrefixRemainder s ≤ 2 ^ (s + 1) ↔
      seamIntegerGreedyRemainder s ≤ 2 ^ s ∨
        (seamAdjacentCut s hs).overshoot ≤ 2 ^ s := by
  rw [seamPureHalfPrefixRemainder_eq_ite hs]
  have hpow : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by
    rw [pow_succ]
    ring
  by_cases hover : (seamAdjacentCut s hs).overshoot ≤ 2 ^ s
  · rw [if_pos hover]
    omega
  · rw [if_neg hover]
    omega

/-- The minimal actual-run input for propagating the two-sided dyadic
invariant.  It excludes the three middle cells and the right pulse leak,
only on branches where those exclusions are needed. -/
def SeamTwoSidedDyadicCellEscape : Prop :=
  ∀ (s : ℕ) (hs : 5 ≤ s),
    (¬ (seamAdjacentCut s hs).successorCarries →
        4 * (seamAdjacentCut s hs).remainder +
              (seamPerturbedFamily s (by omega)).gap -
              (seamAdjacentCut s hs).belowPulse <
            (seamAdjacentCut s hs).terminalWeight →
          4 * ((seamAdjacentCut s hs).remainder : ℤ) -
                ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≠ -3 ∧
            4 * ((seamAdjacentCut s hs).remainder : ℤ) -
                ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≠ -2 ∧
            4 * ((seamAdjacentCut s hs).remainder : ℤ) -
                ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≠ -1) ∧
    (¬ (seamAdjacentCut s hs).successorCarries →
        (seamAdjacentCut s hs).terminalWeight ≤
            4 * (seamAdjacentCut s hs).remainder +
              (seamPerturbedFamily s (by omega)).gap -
              (seamAdjacentCut s hs).belowPulse →
        (seamAdjacentCut s hs).overshoot ≤ 2 ^ s →
          4 * (seamAdjacentCut s hs).overshoot +
              (seamAdjacentCut s hs).abovePulse ≤ 2 ^ (s + 2))

/-- One branch step of the two-sided dyadic invariant under the exact cell
escape input. -/
theorem SeamTwoSidedDyadicCellEscape.step
    (hescape : SeamTwoSidedDyadicCellEscape)
    {s : ℕ} (hs : 5 ≤ s)
    (hinvariant :
      seamIntegerGreedyRemainder s ≤ 2 ^ s ∨
        (seamAdjacentCut s hs).overshoot ≤ 2 ^ s) :
    seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) ∨
      (seamAdjacentCut (s + 1) (by omega)).overshoot ≤ 2 ^ (s + 1) := by
  by_cases hcarry : (seamAdjacentCut s hs).successorCarries
  · exact Or.inl (seamUpperBranch_nextRemainder_le_pow hs hcarry)
  · by_cases hmiddle :
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
          (seamAdjacentCut s hs).terminalWeight
    · have hnotcells := (hescape s hs).1 hcarry hmiddle
      apply seamMiddleBranch_next_twoSided_of_not_neg_small hs hcarry hmiddle
      omega
    · have hright : (seamAdjacentCut s hs).terminalWeight ≤
          4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse :=
        Nat.le_of_not_gt hmiddle
      rcases hinvariant with hrem | hover
      · exact Or.inl
          (seamRightBranch_nextRemainder_le_pow_of_remainder_le
            hs hcarry hright hrem)
      · have hcharge := (hescape s hs).2 hcarry hright hover
        exact Or.inr
          (seamRightBranch_nextOvershoot_le_pow_of_charge_le
            hs hcarry hcharge)

/-- The row-five cut is the concrete base of the two-sided invariant. -/
private theorem seamTwoSidedDyadicAt_five :
    seamIntegerGreedyRemainder 5 ≤ 2 ^ 5 ∨
      (seamAdjacentCut 5 (by omega)).overshoot ≤ 2 ^ 5 := by
  right
  let x : SeamRowWord 5 :=
    SeamRowWord.ofList [true, true, false] (by decide)
  have hx : seamSubsetTarget 5 < wordWeightSum 5 x.toNatWord := by
    decide
  have hbound := seamAdjacentCut_overshoot_le_candidateExcess
    (s := 5) (by omega) x hx
  have hword : wordWeightSum 5 x.toNatWord = 487 := by
    decide
  norm_num [hword, seamSubsetTarget] at hbound ⊢
  omega

/-- Excluding only the two local cell families propagates the universal
two-sided bound `min(remainder, overshoot) ≤ 2^s`. -/
theorem SeamTwoSidedDyadicCellEscape.twoSided
    (hescape : SeamTwoSidedDyadicCellEscape)
    (s : ℕ) (hs : 5 ≤ s) :
    seamIntegerGreedyRemainder s ≤ 2 ^ s ∨
      (seamAdjacentCut s hs).overshoot ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => exact seamTwoSidedDyadicAt_five
  | succ s hs ih => exact hescape.step hs ih

/-! ## The dyadic forbidden-band producer

The normalized lower bound isolates a concrete arithmetic producer.  At an
upper row `d`, the reset charge must avoid a linear-width interval immediately
below every dyadic threshold `2^(d-j+1)`.  Values above the threshold cannot
feed `j` right steps (the exact cylinder forbids them); values below the
window cannot end row-small (the preceding lower bound forbids them).
-/

/-- On an upper branch, avoiding a danger band with the reset charge is
exactly the same as the successor remainder avoiding the translated band
above the complementary dyadic boundary. -/
theorem seamUpperReset_band_iff_successorRemainder_avoids
    {d j : ℕ} (hd5 : 5 ≤ d) (hj : j ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    (2 ^ (d - j + 1) <
          4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse ∨
        4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
          2 ^ (d - j + 1)) ↔
      (seamIntegerGreedyRemainder (d + 1) <
          2 ^ (d + 1) - 2 ^ (d - j + 1) ∨
        2 ^ (d + 1) - 2 ^ (d - j + 1) + 2 * (d + j) ≤
          seamIntegerGreedyRemainder (d + 1)) := by
  have hcylinder := seamUpperBranch_remainder_add_resetCharge_eq hd5 hcarry
  have hpow : 2 ^ (d - j + 1) ≤ 2 ^ (d + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- When the reset charge lies below a dyadic boundary, its exact remaining
distance plus the above pulse is four times the distance of the adjacent
overshoot from the quarter-scale boundary. -/
theorem upperResetCharge_dyadicDistance_add_abovePulse
    {d j : ℕ} (hd5 : 5 ≤ d) (hj : j + 1 ≤ d)
    (hle :
      4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse ≤
        2 ^ (d - j + 1)) :
    (2 ^ (d - j + 1) -
          (4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse)) +
        (seamAdjacentCut d hd5).abovePulse =
      4 * (2 ^ (d - j - 1) -
        (seamAdjacentCut d hd5).overshoot) := by
  have hpow :
      (2 : ℕ) ^ (d - j + 1) = 4 * 2 ^ (d - j - 1) := by
    rw [show d - j + 1 = (d - j - 1) + 2 by omega,
      pow_succ, pow_succ]
    ring
  rw [hpow] at hle ⊢
  omega

/-- Thus a quarter-scale exclusion for the adjacent overshoot is sufficient
for the full reset-charge exclusion.  This is the natural-number form of
`upperResetCharge_signedDistance_eq_remainderBoundary`, with the linear
pulse loss paid explicitly. -/
theorem seamUpperReset_band_of_overshoot_band
    {d j : ℕ} (hd5 : 5 ≤ d) (hj : j + 1 ≤ d)
    (hO :
      2 ^ (d - j - 1) < (seamAdjacentCut d hd5).overshoot ∨
        (seamAdjacentCut d hd5).overshoot + (d + j) ≤
          2 ^ (d - j - 1)) :
    2 ^ (d - j + 1) <
          4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse ∨
      4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
        2 ^ (d - j + 1) := by
  have hpulse :=
    (seamPerturbedFamily d (by omega)).pulse_le
      (seamAdjacentCut d hd5).above
  change (seamAdjacentCut d hd5).abovePulse ≤ 2 * (d - 2) at hpulse
  have hpow :
      (2 : ℕ) ^ (d - j + 1) = 4 * 2 ^ (d - j - 1) := by
    rw [show d - j + 1 = (d - j - 1) + 2 by omega,
      pow_succ, pow_succ]
    ring
  rcases hO with hhigh | hlow
  · left
    rw [hpow]
    omega
  · right
    rw [hpow]
    omega

/-- The sole non-late upper row at the start of the late regime already
escapes every reset band.  Its upper successor remainder is exactly `392`,
so the main boundary has margin `392` and all smaller boundaries lie above
the remainder. -/
theorem seamUpperResetDyadicBandEscape_at_thirteen
    (hd5 : 5 ≤ 13)
    (hcarry : (seamAdjacentCut 13 hd5).successorCarries) :
    ∀ j : ℕ, j ≤ 13 →
      2 ^ (13 - j + 1) <
            4 * (seamAdjacentCut 13 hd5).overshoot +
              (seamAdjacentCut 13 hd5).abovePulse ∨
        4 * (seamAdjacentCut 13 hd5).overshoot +
              (seamAdjacentCut 13 hd5).abovePulse + 2 * (13 + j) ≤
          2 ^ (13 - j + 1) := by
  intro j hj
  rw [seamUpperReset_band_iff_successorRemainder_avoids hd5 hj hcarry]
  have hrem : seamIntegerGreedyRemainder (13 + 1) = 392 := by
    decide +kernel
  rw [hrem]
  interval_cases j <;> norm_num

/-- No upper reset charge at or after row thirteen lies in any of the
linear-width danger bands below the relevant dyadic powers. -/
def SeamUpperResetDyadicBandEscape : Prop :=
  ∀ (d : ℕ) (hd5 : 5 ≤ d), 13 ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
      ∀ j : ℕ, j ≤ d →
        2 ^ (d - j + 1) <
            4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse ∨
          4 * (seamAdjacentCut d hd5).overshoot +
                (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
            2 ^ (d - j + 1)

/-- The forbidden-band producer excludes every row-small endpoint whose
last non-right producer was an upper reset. -/
theorem SeamUpperResetDyadicBandEscape.not_rowSmall_after_upperRightRun
    (hband : SeamUpperResetDyadicBandEscape)
    {d k : ℕ} (hd5 : 5 ≤ d) (hd13 : 13 ≤ d) (hk : k ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries)
    (hrun : ∀ j : ℕ, j < k →
      seamIntegerGreedyRemainder (d + j + 2) +
          2 ^ (d + j + 2) +
          (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
        4 * seamIntegerGreedyRemainder (d + j + 1)) :
    ¬ seamIntegerGreedyRemainder (d + k + 1) < d + k + 1 := by
  intro hsmall
  let E := 4 * (seamAdjacentCut d hd5).overshoot +
    (seamAdjacentCut d hd5).abovePulse
  have hlower := seamUpperThenRightRun_rowSmall_forces_resetCharge_lower
    hd5 hk hcarry hrun hsmall
  change 2 ^ (d - k + 1) < E + 2 * (d + k) at hlower
  rcases hband d hd5 hd13 hcarry k hk with hhigh | hlow
  · change 2 ^ (d - k + 1) < E at hhigh
    have hcylinder :=
      seamUpperThenRightRun_exactCylinder hd5 hcarry hrun
    change seamIntegerGreedyRemainder (d + k + 1) + 4 ^ k * E +
        affineRightRunCharge
          (fun j ↦
            (seamAdjacentCut (d + j + 1) (by omega)).belowPulse) k =
          2 ^ (d + k + 1) at hcylinder
    have hweighted : 4 ^ k * E ≤ 2 ^ (d + k + 1) := by omega
    have hfactor :
        4 ^ k * 2 ^ (d - k + 1) = 2 ^ (d + k + 1) := by
      rw [show 4 ^ k = 2 ^ (2 * k) by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul], ← pow_add]
      congr 1
      omega
    rw [← hfactor] at hweighted
    have hle : E ≤ 2 ^ (d - k + 1) :=
      Nat.le_of_mul_le_mul_left hweighted (pow_pos (by norm_num) k)
    omega
  · change E + 2 * (d + k) ≤ 2 ^ (d - k + 1) at hlow
    omega

/-! ## Last-ancestor fan-in

The dyadic band is not merely a local estimate.  It forces the row-scale
middle socket consumed above.  The proof takes the first row whose remainder
is smaller than its index, then the last false terminal before it.  Every
intervening transition is right.  A middle last ancestor enters the preserved
exponential barrier; an upper last ancestor is excluded by the band.
-/

private theorem seamIntegerGreedyRemainder_thirteen_ge :
    13 ≤ seamIntegerGreedyRemainder 13 := by
  decide +kernel

/-- The row-thirteen transition is a concrete non-right producer.  This is
extracted from the already certified largest-false base at row fourteen. -/
private theorem thirteen_not_mem_seamGreedyWord_fourteen :
    13 ∉ seamWordSupport (seamGreedyWord (13 + 1)) := by
  decide +kernel

/-- If the dyadic upper-reset bands are avoided, no seam remainder at or
after row thirteen can be smaller than its row index.  This is the global
last-ancestor theorem missing from the local reverse-cylinder development.
-/
theorem SeamUpperResetDyadicBandEscape.remainder_ge_row
    (hband : SeamUpperResetDyadicBandEscape)
    {s : ℕ} (hs13 : 13 ≤ s) :
    s ≤ seamIntegerGreedyRemainder s := by
  classical
  by_contra hnot
  have hsmall : seamIntegerGreedyRemainder s < s :=
    Nat.lt_of_not_ge hnot
  let bad : Finset ℕ :=
    (Finset.Icc 13 s).filter
      (fun n ↦ seamIntegerGreedyRemainder n < n)
  have hbadNonempty : bad.Nonempty := by
    refine ⟨s, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hs13, le_rfl⟩, hsmall⟩
  let D : ℕ := bad.min' hbadNonempty
  have hDmem : D ∈ bad := Finset.min'_mem bad hbadNonempty
  have hDdata := Finset.mem_filter.mp hDmem
  have hDbounds := Finset.mem_Icc.mp hDdata.1
  have hD13 : 13 ≤ D := hDbounds.1
  have hDsmall : seamIntegerGreedyRemainder D < D := hDdata.2
  have hDgt13 : 13 < D := by
    by_contra hle
    have hD : D = 13 := by omega
    rw [hD] at hDsmall
    exact (Nat.not_lt_of_ge seamIntegerGreedyRemainder_thirteen_ge)
      hDsmall
  have hprior : ∀ n : ℕ, 13 ≤ n → n < D →
      n ≤ seamIntegerGreedyRemainder n := by
    intro n hn13 hnD
    by_contra hn
    have hnsmall : seamIntegerGreedyRemainder n < n :=
      Nat.lt_of_not_ge hn
    have hnmem : n ∈ bad := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hn13, by omega⟩, hnsmall⟩
    have hDle : D ≤ n := by
      dsimp [D]
      exact Finset.min'_le bad n hnmem
    omega

  let producers : Finset ℕ :=
    (Finset.Icc 13 (D - 1)).filter
      (fun t ↦ t ∉ seamWordSupport (seamGreedyWord (t + 1)))
  have hproducersNonempty : producers.Nonempty := by
    refine ⟨13, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩,
        thirteen_not_mem_seamGreedyWord_fourteen⟩
  let d : ℕ := producers.max' hproducersNonempty
  have hdmem : d ∈ producers := Finset.max'_mem producers hproducersNonempty
  have hddata := Finset.mem_filter.mp hdmem
  have hdbounds := Finset.mem_Icc.mp hddata.1
  have hd13 : 13 ≤ d := hdbounds.1
  have hdD : d < D := by omega
  have hdrow : d ≤ seamIntegerGreedyRemainder d :=
    hprior d hd13 hdD
  have hUMd : SeamGreedyUpperOrMiddleAt d (by omega) := by
    apply (seamGreedy_terminal_false_iff_upperOrMiddle d (by omega)).mp
    have hfalse :=
      (not_mem_seamWordSupport_iff_false
        (seamGreedyWord (d + 1)) (by omega) (by omega)).mp hddata.2
    simpa [SeamRowWord.terminal] using hfalse
  have hnotUMAfter : ∀ (t : ℕ) (ht5 : 5 ≤ t), d < t → t < D →
      ¬ SeamGreedyUpperOrMiddleAt t ht5 := by
    intro t ht5 hdt htD hUMt
    have hfalse :=
      (seamGreedy_terminal_false_iff_upperOrMiddle t (by omega)).mpr hUMt
    have htnot : t ∉ seamWordSupport (seamGreedyWord (t + 1)) := by
      apply (not_mem_seamWordSupport_iff_false
        (seamGreedyWord (t + 1)) (by omega) (by omega)).mpr
      simpa [SeamRowWord.terminal] using hfalse
    have htmem : t ∈ producers := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, htnot⟩
    have htd : t ≤ d := by
      dsimp [d]
      exact Finset.le_max' producers t htmem
    omega
  have hrightBetween : ∀ (t : ℕ) (ht5 : 5 ≤ t), d + 1 ≤ t → t < D →
      ¬ (seamAdjacentCut t ht5).successorCarries ∧
        (seamAdjacentCut t ht5).terminalWeight ≤
          4 * (seamAdjacentCut t ht5).remainder +
            (seamPerturbedFamily t (by omega)).gap -
            (seamAdjacentCut t ht5).belowPulse := by
    intro t ht5 hdt htD
    have hnotUM := hnotUMAfter t ht5 (by omega) htD
    have hncarry : ¬ (seamAdjacentCut t ht5).successorCarries := by
      intro hcarry
      exact hnotUM (Or.inl hcarry)
    refine ⟨hncarry, Nat.le_of_not_gt ?_⟩
    intro hmiddle
    exact hnotUM (Or.inr ⟨hncarry, hmiddle⟩)

  rcases hUMd with hcarry | ⟨hncarry, hmiddle⟩
  · let k : ℕ := D - d - 1
    have hDdk : D = d + k + 1 := by
      dsimp [k]
      omega
    have hrun : ∀ j : ℕ, j < k →
        seamIntegerGreedyRemainder (d + j + 2) +
            2 ^ (d + j + 2) +
            (seamAdjacentCut (d + j + 1) (by omega)).belowPulse + 4 =
          4 * seamIntegerGreedyRemainder (d + j + 1) := by
      intro j hj
      have htD : d + j + 1 < D := by
        dsimp [k] at hj
        omega
      rcases hrightBetween (d + j + 1) (by omega) (by omega) htD with
        ⟨hncarry', hright'⟩
      exact seamRightBranch_remainder_add_charge_eq
        (by omega) hncarry' hright'
    have hk : k ≤ d :=
      seamUpperThenRightRun_length_le_resetRow
        (by omega) hcarry hrun
    have hnotSmall :=
      hband.not_rowSmall_after_upperRightRun
        (by omega) hd13 hk hcarry hrun
    apply hnotSmall
    simpa [hDdk] using hDsmall
  · have hd5 : 5 ≤ d := by omega
    have hdDsucc : d + 1 ≤ D := by omega
    have hdrow' : d ≤ (seamAdjacentCut d hd5).remainder := by
      simpa [seamAdjacentCut_remainder] using hdrow
    have hrightBetween' : ∀ (t : ℕ) (hdt : d + 1 ≤ t), t < D →
        ¬ (seamAdjacentCut t (by omega)).successorCarries ∧
          (seamAdjacentCut t (by omega)).terminalWeight ≤
            4 * (seamAdjacentCut t (by omega)).remainder +
              (seamPerturbedFamily t (by omega)).gap -
              (seamAdjacentCut t (by omega)).belowPulse := by
      intro t hdt htD
      exact hrightBetween t (by omega) hdt htD
    have hbarrier := seamMiddleThenRightRun_expBarrier
      (d := d) (s := D) hd5 hdDsucc hdrow' hncarry hmiddle
      hrightBetween'
    have hDle : D ≤ 2 ^ D + D := Nat.le_add_left D (2 ^ D)
    exact (Nat.not_lt_of_ge (hDle.trans hbarrier)) hDsmall

/-- The dyadic upper-reset producer supplies the exact row-scale middle
producer required by the cardinality tail argument. -/
theorem SeamUpperResetDyadicBandEscape.toMiddleProducerRowEscape
    (hband : SeamUpperResetDyadicBandEscape) :
    SeamMiddleProducerRowEscape := by
  intro s hs hs13 hncarry hmiddle
  simpa [seamAdjacentCut_remainder] using
    (hband.remainder_ge_row hs13)

/-- Final fan-in from the dyadic reset-band producer to the Erdős #257
half-achievement endpoint. -/
theorem half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape
    (hband : SeamUpperResetDyadicBandEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_middleProducerRowEscape
    hband.toMiddleProducerRowEscape

#print axioms supportCoeff_coe_finset_le_card
#print axioms binaryCoeffTail_supportCoeff_coe_finset_le_card
#print axioms middleProducer_card_lt_carry
#print axioms wordPulse_le_two_mul_supportCard
#print axioms rowPulse_le_four_mul_seamRankFloorError
#print axioms wordPulse_le_four_mul_seamWordFloorError
#print axioms binaryCoeffTail_insert_seamBelowSupport_eq_nextFloorError
#print axioms middleProducer_tail_lt_carry_iff_takeThreshold_lt_floorZ
#print axioms middleProducer_carry_sub_tail_eq_four_mul_floorZ_sub_threshold
#print axioms middleProducer_carry_lt_tail_iff_floorZ_lt_takeThreshold
#print axioms seamGreedyFloorZ_ne_takeThreshold
#print axioms middleProducer_tail_lt_carry_iff_takeThreshold_le_floorZ
#print axioms middleProducer_tail_lt_carry_iff_rational_take
#print axioms middleProducer_not_cardEscape_forces_remainder_lt_row
#print axioms SeamMiddleProducerRowEscape.toCardEscape
#print axioms SeamMiddleProducerCardEscape.toTailEscape
#print axioms middleProducer_allRight_forces_carry_lt_tail
#print axioms middleProducer_allRight_forces_floorZ_lt_takeThreshold
#print axioms middleProducer_allRight_forces_rational_skip
#print axioms seamWordRationalRemainder_extend_false
#print axioms seamWordRationalRemainder_extend_true
#print axioms eventualRightTail_rationalRemainder_add_eq
#print axioms eventualRightTail_floorZ_succ_eq
#print axioms eventualRightTail_floorZ_add_charge_eq
#print axioms eventualRightTail_floorZ_add_eq_partialTail
#print axioms middleThenAllRight_rationalRemainder_add_eq
#print axioms middleThenAllRight_floorZ_add_charge_eq
#print axioms middleThenAllRight_floorZ_eq_partialTail
#print axioms middleThenAllRight_finiteValue_add_eq
#print axioms tendsto_middleThenAllRight_finiteValue
#print axioms middleThenAllRight_limit_lt_half
#print axioms middleThenAllRight_rationalRemainder_fatalGap
#print axioms middleThenAllRight_floorZ_fatalGap
#print axioms scaledMersenneTail_floorWall_eq
#print axioms one_third_lt_scaledMersenneTail_floorWall
#print axioms middleThenAllRight_landingExcess_two_le
#print axioms half_mem_mersenneAchievementSet_of_middleProducerCardEscape
#print axioms half_mem_mersenneAchievementSet_of_middleProducerRowEscape
#print axioms three_mul_le_two_pow_succ
#print axioms seamMiddleBranch_nextRemainder_add_belowPulse_eq
#print axioms seamMiddleBranch_nextRemainder_ge_row
#print axioms seamRowSmall_late_nextRemainder_recovers
#print axioms largestSkipLateAt_succ_of_rowSmall
#print axioms seamMiddleBranch_nextRemainder_ge_expBarrier
#print axioms seamRightBranch_preserves_expBarrier
#print axioms seamRightRun_preserves_expBarrier
#print axioms seamMiddleThenRightRun_expBarrier
#print axioms seamAdjacentCut_overshoot_le_candidateExcess
#print axioms truncatedMersenneWeight_two_three_six_seven_le_target
#print axioms seamGreedyBits_head2367
#print axioms seven_mem_seamGreedySupport
#print axioms four_coeff_lower_le_binaryCoeffTail
#print axioms two_lt_binaryCoeffTail_union_Ioi_of_forced_two_three_six
#print axioms finalMiddleCell_neg_two_forces_mod_three_two
#print axioms wordPulse_mod_four_eq_one_of_producerCarry_eq_neg_one
#print axioms seamResidualPulse236_mod_four_eq_two_of_producerCarry_eq_neg_one
#print axioms two_le_seamResidualPulse236_of_producerCarry_eq_neg_one
#print axioms four_five_not_mem_seamGreedySupport
#print axioms exists_high_boundary_divisor_of_producerCarry_eq_neg_one
#print axioms high_boundary_divisor_dichotomy_of_producerCarry_eq_neg_one
#print axioms exists_future_coeff_bump_of_producerCarry_eq_neg_one
#print axioms exists_weighted_tail_bump_of_producerCarry_eq_neg_one
#print axioms infinite_coeff_channel_dichotomy_of_producerCarry_eq_neg_one
#print axioms weighted_tail_channel_dichotomy_of_producerCarry_eq_neg_one
#print axioms iterated_weighted_tail_channel_dichotomy_of_producerCarry_eq_neg_one
#print axioms seamUpperBranch_nextRemainder_le_pow
#print axioms seamMiddleBranch_next_twoSided_of_not_neg_small
#print axioms seamRightBranch_nextRemainder_le_pow_of_remainder_le
#print axioms seamRightBranch_nextOvershoot_le_pow_of_charge_le
#print axioms seamRightBranch_nextOvershoot_le_pow_of_overshoot_le_of_noPulseLeak
#print axioms seamMiddleCoordinate_not_safe_iff_three_cells
#print axioms seamMiddleCell_four_mul_floorZ_le
#print axioms seamMiddleCell_scaledRationalRemainder_le
#print axioms seamRightPulseLeak_iff_distanceCell
#print axioms seamPureHalfPrefixRemainder_eq_ite
#print axioms seamPureHalfPrefixRemainder_le_iff_twoSided
#print axioms SeamTwoSidedDyadicCellEscape.step
#print axioms SeamTwoSidedDyadicCellEscape.twoSided
#print axioms PerturbedFamily.AdjacentCut.above_eq_of_candidate_lt_two_gap
#print axioms exactLateGap_correction_lt_three_mul_gap
#print axioms three_mul_remainder_add_overshoot_eq_exactLateGap
#print axioms exists_exactLateGap_upperResetCharge_coordinate
#print axioms three_mul_upperResetCharge_signedDistance_to_dyadic
#print axioms upperResetCharge_signedDistance_eq_remainderBoundary
#print axioms middleThenAllRight_excess_exactIterate
#print axioms middleCoordinate_add_affineRightRunCharge_succ
#print axioms affineRightRun_exactCylinder
#print axioms three_mul_affineRightRunCharge_add_two_mul_le
#print axioms seamUpperBranch_remainder_add_resetCharge_eq
#print axioms seamUpperThenRightRun_exactCylinder
#print axioms seamUpperThenRightRun_scaledDyadicGap_eq_middleCoordinate_add_charge
#print axioms seamRightRunCharge_lt_row_mul_four_pow
#print axioms seamUpperThenRightRun_rowSmall_forces_resetCylinder
#print axioms remainder_lt_iff_charge_in_topWindow
#print axioms middleInequality_iff_nextCharge_exceeds
#print axioms seamUpperThenRightRun_rowSmall_iff_resetCylinderWindow
#print axioms seamUpperThenRightRun_rowSmall_forces_resetCharge_lower
#print axioms seamUpperReset_band_iff_successorRemainder_avoids
#print axioms upperResetCharge_dyadicDistance_add_abovePulse
#print axioms seamUpperReset_band_of_overshoot_band
#print axioms seamUpperResetDyadicBandEscape_at_thirteen
#print axioms SeamUpperResetDyadicBandEscape.not_rowSmall_after_upperRightRun
#print axioms SeamUpperResetDyadicBandEscape.remainder_ge_row
#print axioms SeamUpperResetDyadicBandEscape.toMiddleProducerRowEscape
#print axioms half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape

end

end Erdos249257
