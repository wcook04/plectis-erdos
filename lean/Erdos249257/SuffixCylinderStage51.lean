import Erdos249257.SuffixCylinderThreshold

/-!
# Exact cutoff-25 prefix and the second feedback row

Private continuation of the integrated suffix-cylinder threshold module.
It exposes the literal cutoff-25 word, evaluates the exact endpoint through
depth 51, and feeds that receipt into the reusable feedback transition.
-/

namespace Erdos249257.SuffixCylinderStage51

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.HalfCarrySelectedWindowBase
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SuffixCylinderPromotion
open Erdos249257.SuffixCylinderThreshold

/-! ## Literal normalized prefix at depth 29 -/

def depth29Prefix14 : HalfWord 14 :=
  extendHalfWord depth18PrefixWord true

def depth29Prefix15 : HalfWord 15 := extendHalfWord depth29Prefix14 false
def depth29Prefix16 : HalfWord 16 := extendHalfWord depth29Prefix15 false
def depth29Prefix17 : HalfWord 17 := extendHalfWord depth29Prefix16 false
def depth29Prefix18 : HalfWord 18 := extendHalfWord depth29Prefix17 false
def depth29Prefix19 : HalfWord 19 := extendHalfWord depth29Prefix18 false
def depth29Prefix20 : HalfWord 20 := extendHalfWord depth29Prefix19 true
def depth29Prefix21 : HalfWord 21 := extendHalfWord depth29Prefix20 true
def depth29Prefix22 : HalfWord 22 := extendHalfWord depth29Prefix21 false
def depth29Prefix23 : HalfWord 23 := extendHalfWord depth29Prefix22 false
def depth29Prefix24 : HalfWord 24 := extendHalfWord depth29Prefix23 false
def depth29Prefix25 : HalfWord 25 := extendHalfWord depth29Prefix24 false

/-- Low-side literal refinement complementary to the integrated high-side
refinement: the newly common bit is specifically `false`. -/
theorem restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    {K N R E : ℕ} (W : SelectedHalfWindow N R)
    (hK1N : K + 1 ≤ N) (pfx : HalfWord K)
    (hpfx : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord ((Nat.le_succ K).trans hK1N) (W.word k hk hkR) = pfx)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E)
    (hbelow : E ≤ 2 ^ (N - (K + 1))) :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord hK1N (W.word k hk hkR) =
        extendHalfWord pfx false := by
  intro k hk hkR
  rcases hcyl with ⟨_pfx, hcyl⟩
  have hendpoint := (hcyl k hk hkR).2
  have hfalse : W.word k hk hkR ⟨K + 1, by omega⟩ = false := by
    cases hbit : W.word k hk hkR ⟨K + 1, by omega⟩
    · rfl
    · have hle := headPower_le_wordSuffixNumeral_of_true hK1N
        (W.word k hk hkR) hbit
      change wordSuffixNumeral (W.word k hk hkR) K (N - K) + k = E
        at hendpoint
      change 2 ^ (N - (K + 1)) ≤
        wordSuffixNumeral (W.word k hk hkR) K (N - K) at hle
      omega
  exact restrictWord_succ_eq_extendHalfWord hK1N
    (W.word k hk hkR) pfx false (hpfx k hk hkR) hfalse

theorem depth29SelectedHalfWindow_restrict_fourteen :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 14 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix14 := by
  simpa [depth29SelectedHalfWindow, depth29Prefix14] using
    (SelectedHalfWindow.stepExplicit_preserves_literalPrefix
      (M := 14) (C := 0) depth28SelectedHalfWindow (by omega)
      (extendHalfWord depth18PrefixWord true) (by omega)
      (le_refl (halfStripBound 29))
      depth28SelectedHalfWindow_selectedRowCoeff_eq_zero
      depth28_to_depth29_buffer
      depth28SelectedHalfWindow_restrict_fourteen)

theorem depth29SelectedHalfWindow_restrict_fifteen :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 15 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix15 := by
  apply restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    (K := 14) (E := 782) depth29SelectedHalfWindow (by omega) depth29Prefix14
  · exact depth29SelectedHalfWindow_restrict_fourteen
  · exact depth29SelectedHalfWindow_hasSuffixCylinderAt_fourteen
  · norm_num

theorem depth29SelectedHalfWindow_restrict_sixteen :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 16 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix16 := by
  apply restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    (K := 15) (E := 782) depth29SelectedHalfWindow (by omega) depth29Prefix15
  · exact depth29SelectedHalfWindow_restrict_fifteen
  · simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_fifteen
  · norm_num

theorem depth29SelectedHalfWindow_restrict_seventeen :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 17 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix17 := by
  apply restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    (K := 16) (E := 782) depth29SelectedHalfWindow (by omega) depth29Prefix16
  · exact depth29SelectedHalfWindow_restrict_sixteen
  · simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_sixteen
  · norm_num

theorem depth29SelectedHalfWindow_restrict_eighteen :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 18 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix18 := by
  apply restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    (K := 17) (E := 782) depth29SelectedHalfWindow (by omega) depth29Prefix17
  · exact depth29SelectedHalfWindow_restrict_seventeen
  · simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_seventeen
  · norm_num

theorem depth29SelectedHalfWindow_restrict_nineteen :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 19 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix19 := by
  apply restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    (K := 18) (E := 782) depth29SelectedHalfWindow (by omega) depth29Prefix18
  · exact depth29SelectedHalfWindow_restrict_eighteen
  · simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_eighteen
  · norm_num

theorem depth29SelectedHalfWindow_restrict_twenty :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 20 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix20 := by
  simpa [depth29Prefix20] using
    (restrictWord_succ_eq_extend_true_of_headThreshold_add_width_le_endpoint
      (K := 19) (E := 782) depth29SelectedHalfWindow (by omega)
      depth29Prefix19 depth29SelectedHalfWindow_restrict_nineteen
      (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_nineteen)
      (by rw [halfStripBound_twentyNine]; norm_num))

theorem depth29SelectedHalfWindow_restrict_twentyOne :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 21 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix21 := by
  simpa [depth29Prefix21] using
    (restrictWord_succ_eq_extend_true_of_headThreshold_add_width_le_endpoint
      (K := 20) (E := 270) depth29SelectedHalfWindow (by omega)
      depth29Prefix20 depth29SelectedHalfWindow_restrict_twenty
      (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twenty)
      (by rw [halfStripBound_twentyNine]; norm_num))

theorem depth29SelectedHalfWindow_restrict_twentyTwo :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 22 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix22 := by
  apply restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    (K := 21) (E := 14) depth29SelectedHalfWindow (by omega) depth29Prefix21
  · exact depth29SelectedHalfWindow_restrict_twentyOne
  · simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyOne
  · norm_num

theorem depth29SelectedHalfWindow_restrict_twentyThree :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 23 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix23 := by
  apply restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    (K := 22) (E := 14) depth29SelectedHalfWindow (by omega) depth29Prefix22
  · exact depth29SelectedHalfWindow_restrict_twentyTwo
  · simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyTwo
  · norm_num

theorem depth29SelectedHalfWindow_restrict_twentyFour :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 24 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix24 := by
  apply restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    (K := 23) (E := 14) depth29SelectedHalfWindow (by omega) depth29Prefix23
  · exact depth29SelectedHalfWindow_restrict_twentyThree
  · simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyThree
  · norm_num

theorem depth29SelectedHalfWindow_restrict_twentyFive :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29),
      restrictWord (by omega : 25 ≤ 29)
          (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix25 := by
  apply restrictWord_succ_eq_extend_false_of_endpoint_le_headThreshold
    (K := 24) (E := 14) depth29SelectedHalfWindow (by omega) depth29Prefix24
  · exact depth29SelectedHalfWindow_restrict_twentyFour
  · simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyFour
  · norm_num

/-! ## Exact coefficient and endpoint run to depth 51 -/

def cutoff25CoeffTable : List ℕ :=
  [3, 0, 1, 1, 1, 1, 3, 0, 1, 1, 2, 0, 6, 0, 1, 1, 1, 0, 3, 1, 1, 1]

/-! Each row is reflected separately.  Keeping these certificates scalar
prevents the evaluator from retaining the full 22-row word computation in
one reduction term. -/

theorem depth29Prefix25_wordCoeff_thirty :
    wordCoeff depth29Prefix25 30 = 3 := by decide +kernel

theorem depth29Prefix25_wordCoeff_thirtyOne :
    wordCoeff depth29Prefix25 31 = 0 := by decide +kernel

theorem depth29Prefix25_wordCoeff_thirtyTwo :
    wordCoeff depth29Prefix25 32 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_thirtyThree :
    wordCoeff depth29Prefix25 33 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_thirtyFour :
    wordCoeff depth29Prefix25 34 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_thirtyFive :
    wordCoeff depth29Prefix25 35 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_thirtySix :
    wordCoeff depth29Prefix25 36 = 3 := by decide +kernel

theorem depth29Prefix25_wordCoeff_thirtySeven :
    wordCoeff depth29Prefix25 37 = 0 := by decide +kernel

theorem depth29Prefix25_wordCoeff_thirtyEight :
    wordCoeff depth29Prefix25 38 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_thirtyNine :
    wordCoeff depth29Prefix25 39 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_forty :
    wordCoeff depth29Prefix25 40 = 2 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fortyOne :
    wordCoeff depth29Prefix25 41 = 0 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fortyTwo :
    wordCoeff depth29Prefix25 42 = 6 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fortyThree :
    wordCoeff depth29Prefix25 43 = 0 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fortyFour :
    wordCoeff depth29Prefix25 44 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fortyFive :
    wordCoeff depth29Prefix25 45 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fortySix :
    wordCoeff depth29Prefix25 46 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fortySeven :
    wordCoeff depth29Prefix25 47 = 0 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fortyEight :
    wordCoeff depth29Prefix25 48 = 3 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fortyNine :
    wordCoeff depth29Prefix25 49 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fifty :
    wordCoeff depth29Prefix25 50 = 1 := by decide +kernel

theorem depth29Prefix25_wordCoeff_fiftyOne :
    wordCoeff depth29Prefix25 51 = 1 := by decide +kernel

/-- All coefficients from rows 30 through 51, in one consumer-facing table. -/
theorem depth29Prefix25_wordCoeff_thirty_add
    (j : ℕ) (hj : j < 22) :
    wordCoeff depth29Prefix25 (30 + j) = cutoff25CoeffTable.getD j 0 := by
  interval_cases j <;>
    norm_num [cutoff25CoeffTable,
      depth29Prefix25_wordCoeff_thirty,
      depth29Prefix25_wordCoeff_thirtyOne,
      depth29Prefix25_wordCoeff_thirtyTwo,
      depth29Prefix25_wordCoeff_thirtyThree,
      depth29Prefix25_wordCoeff_thirtyFour,
      depth29Prefix25_wordCoeff_thirtyFive,
      depth29Prefix25_wordCoeff_thirtySix,
      depth29Prefix25_wordCoeff_thirtySeven,
      depth29Prefix25_wordCoeff_thirtyEight,
      depth29Prefix25_wordCoeff_thirtyNine,
      depth29Prefix25_wordCoeff_forty,
      depth29Prefix25_wordCoeff_fortyOne,
      depth29Prefix25_wordCoeff_fortyTwo,
      depth29Prefix25_wordCoeff_fortyThree,
      depth29Prefix25_wordCoeff_fortyFour,
      depth29Prefix25_wordCoeff_fortyFive,
      depth29Prefix25_wordCoeff_fortySix,
      depth29Prefix25_wordCoeff_fortySeven,
      depth29Prefix25_wordCoeff_fortyEight,
      depth29Prefix25_wordCoeff_fortyNine,
      depth29Prefix25_wordCoeff_fifty,
      depth29Prefix25_wordCoeff_fiftyOne]

/-- Computable endpoint recurrence driven by the literal cutoff word. -/
def literalPrefixEndpointRun
    {K : ℕ} (pfx : HalfWord K) (N E : ℕ) : ℕ → ℕ
  | 0 => E
  | d + 1 =>
      2 * literalPrefixEndpointRun pfx N E d - wordCoeff pfx (N + d + 1)

theorem literalPrefixEndpointRun_succ
    {K : ℕ} (pfx : HalfWord K) (N E d : ℕ) :
    literalPrefixEndpointRun pfx N E (d + 1) =
      2 * literalPrefixEndpointRun pfx N E d -
        wordCoeff pfx (N + d + 1) := by
  rfl

theorem depth29Prefix25_endpointRun_zero :
    literalPrefixEndpointRun depth29Prefix25 29 14 0 = 14 := by
  rfl

theorem depth29Prefix25_endpointRun_one :
    literalPrefixEndpointRun depth29Prefix25 29 14 1 = 25 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_zero,
    depth29Prefix25_wordCoeff_thirty]

theorem depth29Prefix25_endpointRun_two :
    literalPrefixEndpointRun depth29Prefix25 29 14 2 = 50 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_one,
    depth29Prefix25_wordCoeff_thirtyOne]

theorem depth29Prefix25_endpointRun_three :
    literalPrefixEndpointRun depth29Prefix25 29 14 3 = 99 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_two,
    depth29Prefix25_wordCoeff_thirtyTwo]

theorem depth29Prefix25_endpointRun_four :
    literalPrefixEndpointRun depth29Prefix25 29 14 4 = 197 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_three,
    depth29Prefix25_wordCoeff_thirtyThree]

theorem depth29Prefix25_endpointRun_five :
    literalPrefixEndpointRun depth29Prefix25 29 14 5 = 393 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_four,
    depth29Prefix25_wordCoeff_thirtyFour]

theorem depth29Prefix25_endpointRun_six :
    literalPrefixEndpointRun depth29Prefix25 29 14 6 = 785 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_five,
    depth29Prefix25_wordCoeff_thirtyFive]

theorem depth29Prefix25_endpointRun_seven :
    literalPrefixEndpointRun depth29Prefix25 29 14 7 = 1567 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_six,
    depth29Prefix25_wordCoeff_thirtySix]

theorem depth29Prefix25_endpointRun_eight :
    literalPrefixEndpointRun depth29Prefix25 29 14 8 = 3134 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_seven,
    depth29Prefix25_wordCoeff_thirtySeven]

theorem depth29Prefix25_endpointRun_nine :
    literalPrefixEndpointRun depth29Prefix25 29 14 9 = 6267 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_eight,
    depth29Prefix25_wordCoeff_thirtyEight]

theorem depth29Prefix25_endpointRun_ten :
    literalPrefixEndpointRun depth29Prefix25 29 14 10 = 12533 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_nine,
    depth29Prefix25_wordCoeff_thirtyNine]

theorem depth29Prefix25_endpointRun_eleven :
    literalPrefixEndpointRun depth29Prefix25 29 14 11 = 25064 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_ten,
    depth29Prefix25_wordCoeff_forty]

theorem depth29Prefix25_endpointRun_twelve :
    literalPrefixEndpointRun depth29Prefix25 29 14 12 = 50128 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_eleven,
    depth29Prefix25_wordCoeff_fortyOne]

theorem depth29Prefix25_endpointRun_thirteen :
    literalPrefixEndpointRun depth29Prefix25 29 14 13 = 100250 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_twelve,
    depth29Prefix25_wordCoeff_fortyTwo]

theorem depth29Prefix25_endpointRun_fourteen :
    literalPrefixEndpointRun depth29Prefix25 29 14 14 = 200500 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_thirteen,
    depth29Prefix25_wordCoeff_fortyThree]

theorem depth29Prefix25_endpointRun_fifteen :
    literalPrefixEndpointRun depth29Prefix25 29 14 15 = 400999 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_fourteen,
    depth29Prefix25_wordCoeff_fortyFour]

theorem depth29Prefix25_endpointRun_sixteen :
    literalPrefixEndpointRun depth29Prefix25 29 14 16 = 801997 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_fifteen,
    depth29Prefix25_wordCoeff_fortyFive]

theorem depth29Prefix25_endpointRun_seventeen :
    literalPrefixEndpointRun depth29Prefix25 29 14 17 = 1603993 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_sixteen,
    depth29Prefix25_wordCoeff_fortySix]

theorem depth29Prefix25_endpointRun_eighteen :
    literalPrefixEndpointRun depth29Prefix25 29 14 18 = 3207986 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_seventeen,
    depth29Prefix25_wordCoeff_fortySeven]

theorem depth29Prefix25_endpointRun_nineteen :
    literalPrefixEndpointRun depth29Prefix25 29 14 19 = 6415969 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_eighteen,
    depth29Prefix25_wordCoeff_fortyEight]

theorem depth29Prefix25_endpointRun_twenty :
    literalPrefixEndpointRun depth29Prefix25 29 14 20 = 12831937 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_nineteen,
    depth29Prefix25_wordCoeff_fortyNine]

theorem depth29Prefix25_endpointRun_twentyOne :
    literalPrefixEndpointRun depth29Prefix25 29 14 21 = 25663873 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_twenty,
    depth29Prefix25_wordCoeff_fifty]

theorem depth29Prefix25_endpointRun_twentyTwo :
    literalPrefixEndpointRun depth29Prefix25 29 14 22 = 51327745 := by
  rw [literalPrefixEndpointRun_succ, depth29Prefix25_endpointRun_twentyOne,
    depth29Prefix25_wordCoeff_fiftyOne]

/-- A full-cylinder stage has one literal word at its cutoff. -/
def FullCylinderStageHasLiteralPrefix
    {K N : ℕ} (S : FullCylinderStage K N) (pfx : HalfWord K) : Prop :=
  ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound N),
    restrictWord S.hKN (S.window.word k hk hkR) = pfx

theorem fullCylinderStage29_hasLiteralPrefix :
    FullCylinderStageHasLiteralPrefix fullCylinderStage29 depth29Prefix25 := by
  intro k hk hkR
  change restrictWord (by omega : 25 ≤ 29)
      (depth29SelectedHalfWindow.word k hk hkR) = depth29Prefix25
  exact depth29SelectedHalfWindow_restrict_twentyFive k hk hkR

theorem FullCylinderStageHasLiteralPrefix_advance
    {K N : ℕ} (S : FullCylinderStage K N) (pfx : HalfWord K)
    (hN : 1 ≤ N) (hhalf : (N + 1) / 2 ≤ K)
    (hpfx : FullCylinderStageHasLiteralPrefix S pfx) :
    FullCylinderStageHasLiteralPrefix (S.advance hN hhalf) pfx := by
  unfold FullCylinderStageHasLiteralPrefix at hpfx ⊢
  intro q hq hqR
  unfold CylinderStage.advance
  dsimp only
  apply SelectedHalfWindow.stepExplicit_preserves_literalPrefix
  exact hpfx

theorem FullCylinderStageHasLiteralPrefix_advanceWithinCutoff
    {K N : ℕ} (S : FullCylinderStage K N) (pfx : HalfWord K)
    (hN : 1 ≤ N) (hpfx : FullCylinderStageHasLiteralPrefix S pfx)
    (d : ℕ) (hhorizon : N + d ≤ 2 * K + 1) :
    FullCylinderStageHasLiteralPrefix
      (S.advanceWithinCutoff hN d hhorizon) pfx := by
  induction d with
  | zero => simpa [CylinderStage.advanceWithinCutoff] using hpfx
  | succ d ih =>
      have hprevHorizon : N + d ≤ 2 * K + 1 := by omega
      have hprev := ih hprevHorizon
      have hprevN : 1 ≤ N + d := by omega
      have hhalf : (N + d + 1) / 2 ≤ K := by omega
      have hstep := FullCylinderStageHasLiteralPrefix_advance
        (S.advanceWithinCutoff hN d hprevHorizon) pfx hprevN hhalf hprev
      simpa [CylinderStage.advanceWithinCutoff] using hstep

theorem CylinderStage.endpoint_advance
    {K N : ℕ} (S : CylinderStage K N) (hN : 1 ≤ N)
    (hhalf : (N + 1) / 2 ≤ K)
    (hR : 1 ≤ halfStripBound N) :
    (S.advance hN hhalf).endpoint = 2 * S.endpoint -
      supportCoeff
        (wordSupport (S.window.word 1 (by omega) hR)) (N + 1) := by
  rfl

theorem fullCylinderStage_nextCoeff_eq_literalPrefix
    {K N : ℕ} (S : FullCylinderStage K N) (pfx : HalfWord K)
    (hpfx : FullCylinderStageHasLiteralPrefix S pfx)
    (hhorizon : N + 1 ≤ 2 * K + 1) :
    supportCoeff
        (wordSupport (S.window.word 1 (by omega)
          (by unfold halfStripBound; omega))) (N + 1) =
      wordCoeff pfx (N + 1) := by
  calc
    supportCoeff
        (wordSupport (S.window.word 1 (by omega)
          (by unfold halfStripBound; omega))) (N + 1) =
        supportCoeff (wordSupport pfx) (N + 1) :=
      supportCoeff_word_eq_of_restrict_before_feedback S.hKN
        (S.window.word 1 (by omega) (by unfold halfStripBound; omega)) pfx
        (hpfx 1 (by omega) (by unfold halfStripBound; omega))
        (by have hKN := S.hKN; omega) hhorizon (by omega)
    _ = wordCoeff pfx (N + 1) :=
      (wordCoeff_eq_supportCoeff_wordSupport pfx (N + 1)).symm

theorem fullCylinderStage_endpoint_advanceWithinCutoff_eq_literalPrefixEndpointRun
    {K N : ℕ} (S : FullCylinderStage K N) (pfx : HalfWord K)
    (hN : 1 ≤ N) (hpfx : FullCylinderStageHasLiteralPrefix S pfx)
    (d : ℕ) (hhorizon : N + d ≤ 2 * K + 1) :
    (S.advanceWithinCutoff hN d hhorizon).endpoint =
      literalPrefixEndpointRun pfx N S.endpoint d := by
  induction d with
  | zero => simp [CylinderStage.advanceWithinCutoff, literalPrefixEndpointRun]
  | succ d ih =>
      have hprevHorizon : N + d ≤ 2 * K + 1 := by omega
      let prev := S.advanceWithinCutoff hN d hprevHorizon
      have hprevN : 1 ≤ N + d := by omega
      have hhalf : (N + d + 1) / 2 ≤ K := by omega
      have hprevPrefix :=
        FullCylinderStageHasLiteralPrefix_advanceWithinCutoff
          S pfx hN hpfx d hprevHorizon
      have hcoeff := fullCylinderStage_nextCoeff_eq_literalPrefix
        prev pfx hprevPrefix (by omega)
      have hendpoint := CylinderStage.endpoint_advance prev hprevN hhalf
        (by unfold halfStripBound; omega)
      have hprevEndpoint := ih hprevHorizon
      rw [hcoeff, hprevEndpoint] at hendpoint
      simpa [prev, CylinderStage.advanceWithinCutoff,
        literalPrefixEndpointRun] using hendpoint

theorem fullCylinderStage51_endpoint :
    fullCylinderStage51.endpoint = 51327745 := by
  have hrun :=
    fullCylinderStage_endpoint_advanceWithinCutoff_eq_literalPrefixEndpointRun
      fullCylinderStage29 depth29Prefix25 (by norm_num)
      fullCylinderStage29_hasLiteralPrefix 22 (by norm_num)
  have hbaseEndpoint : fullCylinderStage29.endpoint = 14 := by rfl
  rw [hbaseEndpoint, depth29Prefix25_endpointRun_twentyTwo] at hrun
  simpa [fullCylinderStage51] using hrun

theorem halfStripBound_fiftyOne : halfStripBound 51 = 18 := by
  have hsqrt : Nat.sqrt 51 = 7 := by
    symm
    exact Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩
  simp [halfStripBound, hsqrt]

theorem fullCylinderStage51_feedback_headThreshold_margin :
    2 ^ (51 - (25 + 1)) + halfStripBound 51 ≤
      fullCylinderStage51.endpoint := by
  rw [fullCylinderStage51_endpoint, halfStripBound_fiftyOne]
  norm_num

noncomputable def fullCylinderStage51Promoted : FullCylinderStage 26 51 :=
  fullCylinderStage51.promoteHigh (by omega)
    fullCylinderStage51_feedback_headThreshold_margin

/-- Full selected window at row 52, beyond the second feedback boundary. -/
noncomputable def fullCylinderStage52 : FullCylinderStage 26 52 :=
  fullCylinderStage51.feedbackAdvanceHigh (by omega) (by omega) (by norm_num)
    fullCylinderStage51_feedback_headThreshold_margin

#print axioms depth29Prefix25_wordCoeff_thirty_add
#print axioms fullCylinderStage51_endpoint
#print axioms fullCylinderStage51_feedback_headThreshold_margin
#print axioms fullCylinderStage51Promoted
#print axioms fullCylinderStage52

end Erdos249257.SuffixCylinderStage51
