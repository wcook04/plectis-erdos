import Erdos249257.SelectedSuffixCylinderPreFeedback
import Erdos249257.SuffixCylinderPromotion

/-!
# Exact endpoint threshold for promoting a suffix cylinder

This scratch overlay characterizes the first feedback bit directly from the
endpoint-indexed cylinder geometry.  The `K+1` bit is common exactly when the
consecutive suffix interval avoids its binary head threshold.
-/

namespace Erdos249257.SuffixCylinderThreshold

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.HalfCarrySelectedWindowBase
open Erdos249257.FixedCoeffRewind
open Erdos249257.FixedCoeffRewindPhase
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SelectedSuffixCylinderPreFeedback
open Erdos249257.SuffixCylinderPromotion
open Erdos249257.RewindHalfDivisorAdapter

/-- Exact cylinder-geometry criterion for promoting the common prefix by one
bit.  The suffixes are the consecutive interval `E-R, ..., E-1`; their head
bit is constant iff this interval lies wholly below or wholly above the head
weight `2^(N-(K+1))`. -/
theorem commonRestrictionAt_succ_iff_endpoint_avoids_headThreshold
    {K N R E : ℕ} (W : SelectedHalfWindow N R)
    (hK1N : K + 1 ≤ N) (hR : 1 ≤ R)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E) :
    W.CommonRestrictionAt hK1N ↔
      E ≤ 2 ^ (N - (K + 1)) ∨
        2 ^ (N - (K + 1)) + R ≤ E := by
  classical
  rcases hcyl with ⟨pfx, hcyl⟩
  let H := 2 ^ (N - (K + 1))
  constructor
  · rintro ⟨pfx', hpfx'⟩
    let β := pfx' (Fin.last (K + 1))
    have hbit : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
        W.word k hk hkR ⟨K + 1, by omega⟩ = β := by
      intro k hk hkR
      have hraw := congrFun (hpfx' k hk hkR) (Fin.last (K + 1))
      simpa [restrictWord, β] using hraw
    cases hβ : β
    · left
      obtain ⟨_hpfx, hendpoint⟩ := hcyl 1 (by omega) hR
      have hfalse : W.word 1 (by omega) hR ⟨K + 1, by omega⟩ = false := by
        simpa [hβ] using hbit 1 (by omega) hR
      have hlt := wordSuffixNumeral_lt_headPower_of_false hK1N
        (W.word 1 (by omega) hR) hfalse
      change E ≤ H
      change wordSuffixNumeral (W.word 1 (by omega) hR) K (N - K) + 1 = E
        at hendpoint
      change wordSuffixNumeral (W.word 1 (by omega) hR) K (N - K) < H
        at hlt
      omega
    · right
      obtain ⟨_hpfx, hendpoint⟩ := hcyl R hR (le_refl R)
      have htrue : W.word R hR (le_refl R) ⟨K + 1, by omega⟩ = true := by
        simpa [hβ] using hbit R hR (le_refl R)
      have hle := headPower_le_wordSuffixNumeral_of_true hK1N
        (W.word R hR (le_refl R)) htrue
      change H + R ≤ E
      change wordSuffixNumeral (W.word R hR (le_refl R)) K (N - K) + R = E
        at hendpoint
      change H ≤ wordSuffixNumeral
        (W.word R hR (le_refl R)) K (N - K) at hle
      omega
  · rintro (hbelow | habove)
    · refine ⟨extendHalfWord pfx false, ?_⟩
      intro k hk hkR
      obtain ⟨hprefix, hendpoint⟩ := hcyl k hk hkR
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
        (W.word k hk hkR) pfx false hprefix hfalse
    · refine ⟨extendHalfWord pfx true, ?_⟩
      intro k hk hkR
      obtain ⟨hprefix, hendpoint⟩ := hcyl k hk hkR
      have htrue : W.word k hk hkR ⟨K + 1, by omega⟩ = true := by
        cases hbit : W.word k hk hkR ⟨K + 1, by omega⟩
        · have hlt := wordSuffixNumeral_lt_headPower_of_false hK1N
            (W.word k hk hkR) hbit
          change wordSuffixNumeral (W.word k hk hkR) K (N - K) + k = E
            at hendpoint
          change wordSuffixNumeral (W.word k hk hkR) K (N - K) <
            2 ^ (N - (K + 1)) at hlt
          omega
        · rfl
      exact restrictWord_succ_eq_extendHalfWord hK1N
        (W.word k hk hkR) pfx true hprefix htrue

/-- Positive-distance form: a cylinder promotes whenever its endpoint is at
least one full protected-window width beyond the head threshold. -/
theorem commonRestrictionAt_succ_of_headThreshold_add_width_le_endpoint
    {K N R E : ℕ} (W : SelectedHalfWindow N R)
    (hK1N : K + 1 ≤ N) (hR : 1 ≤ R)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E)
    (hmargin : 2 ^ (N - (K + 1)) + R ≤ E) :
    W.CommonRestrictionAt hK1N := by
  exact (commonRestrictionAt_succ_iff_endpoint_avoids_headThreshold
    W hK1N hR hcyl).2 (Or.inr hmargin)

/-- Exact high-side promotion.  Beyond the full-width threshold margin the
new common bit is `true`, so removing it shifts the endpoint by exactly its
head weight. -/
theorem promoteSuffixCylinderAt_succ_of_headThreshold_add_width_le_endpoint
    {K N R E : ℕ} (W : SelectedHalfWindow N R)
    (hK1N : K + 1 ≤ N) (hR : 1 ≤ R)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E)
    (hmargin : 2 ^ (N - (K + 1)) + R ≤ E) :
    HasSuffixCylinderAt W hK1N (E - 2 ^ (N - (K + 1))) ∧
      R ≤ E - 2 ^ (N - (K + 1)) := by
  classical
  rcases hcyl with ⟨pfx, hcyl⟩
  have hcommon :=
    commonRestrictionAt_succ_of_headThreshold_add_width_le_endpoint
      W hK1N hR ⟨pfx, hcyl⟩ hmargin
  rcases hcommon with ⟨pfx', hpfx'⟩
  constructor
  · refine ⟨pfx', ?_⟩
    intro k hk hkR
    obtain ⟨_hprefix, hendpoint⟩ := hcyl k hk hkR
    have htrue : W.word k hk hkR ⟨K + 1, by omega⟩ = true := by
      cases hbit : W.word k hk hkR ⟨K + 1, by omega⟩
      · have hlt := wordSuffixNumeral_lt_headPower_of_false hK1N
          (W.word k hk hkR) hbit
        change wordSuffixNumeral (W.word k hk hkR) K (N - K) + k = E
          at hendpoint
        change wordSuffixNumeral (W.word k hk hkR) K (N - K) <
          2 ^ (N - (K + 1)) at hlt
        omega
      · rfl
    have hsplit := wordSuffixNumeral_split_head hK1N (W.word k hk hkR)
    rw [htrue] at hsplit
    constructor
    · exact hpfx' k hk hkR
    · change wordSuffixNumeral (W.word k hk hkR) (K + 1)
          (N - (K + 1)) + k = E - 2 ^ (N - (K + 1))
      change wordSuffixNumeral (W.word k hk hkR) K (N - K) =
        2 ^ (N - (K + 1)) +
          wordSuffixNumeral (W.word k hk hkR) (K + 1)
            (N - (K + 1)) at hsplit
      omega
  · omega

/-- Exact low-side promotion.  When the endpoint has not reached the head
weight, the newly common bit is `false`, so the endpoint is unchanged. -/
theorem promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    {K N R E : ℕ} (W : SelectedHalfWindow N R)
    (hK1N : K + 1 ≤ N) (hR : 1 ≤ R)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E)
    (hbelow : E ≤ 2 ^ (N - (K + 1))) :
    HasSuffixCylinderAt W hK1N E ∧ R ≤ E := by
  classical
  rcases hcyl with ⟨pfx, hcyl⟩
  have hcommon :=
    (commonRestrictionAt_succ_iff_endpoint_avoids_headThreshold
      W hK1N hR ⟨pfx, hcyl⟩).2 (Or.inl hbelow)
  rcases hcommon with ⟨pfx', hpfx'⟩
  constructor
  · refine ⟨pfx', ?_⟩
    intro k hk hkR
    obtain ⟨_hprefix, hendpoint⟩ := hcyl k hk hkR
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
    have hsplit :
        wordSuffixNumeral (W.word k hk hkR) K (N - K) =
          wordSuffixNumeral (W.word k hk hkR) (K + 1)
            (N - (K + 1)) := by
      simpa [hfalse] using
        wordSuffixNumeral_split_head hK1N (W.word k hk hkR)
    constructor
    · exact hpfx' k hk hkR
    · change wordSuffixNumeral (W.word k hk hkR) (K + 1)
          (N - (K + 1)) + k = E
      omega
  · have hlast := (hcyl R hR (le_refl R)).2
    omega

/-- Literal-prefix refinement of high-side promotion: the newly common bit
is specifically `true`. -/
theorem restrictWord_succ_eq_extend_true_of_headThreshold_add_width_le_endpoint
    {K N R E : ℕ} (W : SelectedHalfWindow N R)
    (hK1N : K + 1 ≤ N) (pfx : HalfWord K)
    (hpfx : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord ((Nat.le_succ K).trans hK1N) (W.word k hk hkR) = pfx)
    (hcyl : HasSuffixCylinderAt W
      ((Nat.le_succ K).trans hK1N) E)
    (hmargin : 2 ^ (N - (K + 1)) + R ≤ E) :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord hK1N (W.word k hk hkR) =
        extendHalfWord pfx true := by
  intro k hk hkR
  rcases hcyl with ⟨_pfx, hcyl⟩
  have hendpoint := (hcyl k hk hkR).2
  have htrue : W.word k hk hkR ⟨K + 1, by omega⟩ = true := by
    cases hbit : W.word k hk hkR ⟨K + 1, by omega⟩
    · have hlt := wordSuffixNumeral_lt_headPower_of_false hK1N
        (W.word k hk hkR) hbit
      change wordSuffixNumeral (W.word k hk hkR) K (N - K) + k = E
        at hendpoint
      change wordSuffixNumeral (W.word k hk hkR) K (N - K) <
        2 ^ (N - (K + 1)) at hlt
      omega
    · rfl
  exact restrictWord_succ_eq_extendHalfWord hK1N
    (W.word k hk hkR) pfx true (hpfx k hk hkR) htrue

/-! ## First live feedback row -/

/-- The concrete depth-13 base prefix persists through a packaged stage. -/
def HasDepth13BasePrefix {N : ℕ} (S : Stage N) : Prop :=
  ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound N),
    restrictWord S.h13 (S.window.word k hk hkR) = depth18PrefixWord

theorem stage18_hasDepth13BasePrefix : HasDepth13BasePrefix stage18 := by
  intro k hk hkR
  change restrictWord (by omega : 13 ≤ 18) (depth18Word k) =
    depth18PrefixWord
  exact restrictWord_depth18Word_thirteen k

/-- Definitional endpoint recurrence exposed without opening the packaged
stage implementation downstream. -/
theorem Stage.endpoint_step
    {N : ℕ} (S : Stage N) (hhalf : (N + 1) / 2 ≤ 13)
    (hR : 1 ≤ halfStripBound N) :
    (S.step hhalf).endpoint = 2 * S.endpoint -
      supportCoeff
        (wordSupport (S.window.word 1 (by omega) hR)) (N + 1) := by
  rfl

/-- A canonical explicit successor preserves any already common literal
prefix. -/
theorem SelectedHalfWindow.stepExplicit_preserves_literalPrefix
    {M N R S C : ℕ} (W : SelectedHalfWindow N R)
    (hMN : M ≤ N) (pfx : HalfWord M)
    (hN : 1 ≤ N) (hSstrip : S ≤ halfStripBound (N + 1))
    (hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ R → selectedRowCoeff W k = C)
    (hbuffer : S + C ≤ 2 * R)
    (hpfx : ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord hMN (W.word k hk hkR) = pfx) :
    ∀ q (hq : 1 ≤ q) (hqS : q ≤ S),
      restrictWord (hMN.trans (Nat.le_succ N))
        ((W.stepExplicit hN hSstrip hp_common hbuffer).word q hq hqS) =
          pfx := by
  intro q hq hqS
  let k := parent C q
  have hk : 1 ≤ k := explicitParent_pos hq
  have hkR : k ≤ R := explicitParent_le hqS hbuffer
  calc
    restrictWord (hMN.trans (Nat.le_succ N))
        ((W.stepExplicit hN hSstrip hp_common hbuffer).word q hq hqS) =
        restrictWord hMN
          (restrictWord (Nat.le_succ N)
            ((W.stepExplicit hN hSstrip hp_common hbuffer).word q hq hqS)) :=
      (restrictWord_trans hMN (Nat.le_succ N) _).symm
    _ = restrictWord hMN (W.word k hk hkR) := by
      rw [W.restrictWord_stepExplicit hN hSstrip hp_common hbuffer q hq hqS]
    _ = pfx := hpfx k hk hkR

theorem HasDepth13BasePrefix.step
    {N : ℕ} (S : Stage N) (hhalf : (N + 1) / 2 ≤ 13)
    (hpfx : HasDepth13BasePrefix S) :
    HasDepth13BasePrefix (S.step hhalf) := by
  unfold HasDepth13BasePrefix at hpfx ⊢
  intro q hq hqR
  unfold Stage.step
  dsimp only
  apply SelectedHalfWindow.stepExplicit_preserves_literalPrefix
  exact hpfx

theorem stage19_hasDepth13BasePrefix : HasDepth13BasePrefix stage19 := by
  simpa [stage19] using
    (HasDepth13BasePrefix.step stage18 (by norm_num)
      stage18_hasDepth13BasePrefix)

theorem stage20_hasDepth13BasePrefix : HasDepth13BasePrefix stage20 := by
  simpa [stage20] using
    (HasDepth13BasePrefix.step stage19 (by norm_num)
      stage19_hasDepth13BasePrefix)

theorem stage21_hasDepth13BasePrefix : HasDepth13BasePrefix stage21 := by
  simpa [stage21] using
    (HasDepth13BasePrefix.step stage20 (by norm_num)
      stage20_hasDepth13BasePrefix)

theorem stage22_hasDepth13BasePrefix : HasDepth13BasePrefix stage22 := by
  simpa [stage22] using
    (HasDepth13BasePrefix.step stage21 (by norm_num)
      stage21_hasDepth13BasePrefix)

theorem stage23_hasDepth13BasePrefix : HasDepth13BasePrefix stage23 := by
  simpa [stage23] using
    (HasDepth13BasePrefix.step stage22 (by norm_num)
      stage22_hasDepth13BasePrefix)

theorem stage24_hasDepth13BasePrefix : HasDepth13BasePrefix stage24 := by
  simpa [stage24] using
    (HasDepth13BasePrefix.step stage23 (by norm_num)
      stage23_hasDepth13BasePrefix)

theorem stage25_hasDepth13BasePrefix : HasDepth13BasePrefix stage25 := by
  simpa [stage25] using
    (HasDepth13BasePrefix.step stage24 (by norm_num)
      stage24_hasDepth13BasePrefix)

theorem stage26_hasDepth13BasePrefix : HasDepth13BasePrefix stage26 := by
  simpa [stage26] using
    (HasDepth13BasePrefix.step stage25 (by norm_num)
      stage25_hasDepth13BasePrefix)

theorem stage27_hasDepth13BasePrefix : HasDepth13BasePrefix stage27 := by
  simpa [stage27] using
    (HasDepth13BasePrefix.step stage26 (by norm_num)
      stage26_hasDepth13BasePrefix)

/-- Before feedback, a word's next coefficient is already determined by its
literal cutoff restriction. -/
theorem supportCoeff_word_eq_of_restrict_before_feedback
    {M N n : ℕ} (hMN : M ≤ N) (w : HalfWord N) (pfx : HalfWord M)
    (hrestrict : restrictWord hMN w = pfx)
    (hMn : M < n) (hnfeedback : n ≤ 2 * M + 1) (hNn : N < n) :
    supportCoeff (wordSupport w) n = supportCoeff (wordSupport pfx) n := by
  classical
  have hnmem : n ∉ wordSupport w := by
    rintro ⟨hnlt, _hbit⟩
    omega
  have hset := congrArg wordSupport hrestrict
  rw [wordSupport_restrictWord] at hset
  have hcoeff := supportCoeff_eq_prefix_add_currentBit
    (wordSupport w) hMn hnfeedback
  rw [if_neg hnmem, Nat.add_zero, hset] at hcoeff
  exact hcoeff

theorem Stage.nextCoeff_eq_depth18Prefix
    {N : ℕ} (S : Stage N) (hN26 : N ≤ 26)
    (hpfx : HasDepth13BasePrefix S) :
    supportCoeff
        (wordSupport (S.window.word 1 (by omega)
          (by unfold halfStripBound; omega))) (N + 1) =
      supportCoeff (wordSupport depth18PrefixWord) (N + 1) := by
  apply supportCoeff_word_eq_of_restrict_before_feedback
    S.h13 (S.window.word 1 (by omega)
      (by unfold halfStripBound; omega)) depth18PrefixWord
  · exact hpfx 1 (by omega) (by unfold halfStripBound; omega)
  · have h13 := S.h13
    omega
  · omega
  · omega

theorem depth18PrefixWord_supportCoeff_nineteen :
    supportCoeff (wordSupport depth18PrefixWord) 19 = 0 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth18PrefixWord_supportCoeff_twenty :
    supportCoeff (wordSupport depth18PrefixWord) 20 = 1 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth18PrefixWord_supportCoeff_twentyOne :
    supportCoeff (wordSupport depth18PrefixWord) 21 = 2 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth18PrefixWord_supportCoeff_twentyTwo :
    supportCoeff (wordSupport depth18PrefixWord) 22 = 1 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth18PrefixWord_supportCoeff_twentyThree :
    supportCoeff (wordSupport depth18PrefixWord) 23 = 0 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth18PrefixWord_supportCoeff_twentyFour :
    supportCoeff (wordSupport depth18PrefixWord) 24 = 3 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth18PrefixWord_supportCoeff_twentyFive :
    supportCoeff (wordSupport depth18PrefixWord) 25 = 0 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth18PrefixWord_supportCoeff_twentySix :
    supportCoeff (wordSupport depth18PrefixWord) 26 = 1 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth18PrefixWord_supportCoeff_twentySeven :
    supportCoeff (wordSupport depth18PrefixWord) 27 = 1 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem Stage.endpoint_step_eq
    {N C E : ℕ} (S : Stage N) (hhalf : (N + 1) / 2 ≤ 13)
    (hendpoint : S.endpoint = E)
    (hcoeff : supportCoeff
      (wordSupport (S.window.word 1 (by omega)
        (by unfold halfStripBound; omega))) (N + 1) = C) :
    (S.step hhalf).endpoint = 2 * E - C := by
  rw [Stage.endpoint_step S hhalf (by unfold halfStripBound; omega),
    hendpoint, hcoeff]

theorem stage18_endpoint : stage18.endpoint = 17 := by rfl

theorem stage19_endpoint : stage19.endpoint = 34 := by
  have hcoeff := Stage.nextCoeff_eq_depth18Prefix stage18 (by norm_num)
    stage18_hasDepth13BasePrefix
  rw [depth18PrefixWord_supportCoeff_nineteen] at hcoeff
  simpa [stage19] using Stage.endpoint_step_eq stage18 (by norm_num)
    stage18_endpoint hcoeff

theorem stage20_endpoint : stage20.endpoint = 67 := by
  have hcoeff := Stage.nextCoeff_eq_depth18Prefix stage19 (by norm_num)
    stage19_hasDepth13BasePrefix
  rw [depth18PrefixWord_supportCoeff_twenty] at hcoeff
  simpa [stage20] using Stage.endpoint_step_eq stage19 (by norm_num)
    stage19_endpoint hcoeff

theorem stage21_endpoint : stage21.endpoint = 132 := by
  have hcoeff := Stage.nextCoeff_eq_depth18Prefix stage20 (by norm_num)
    stage20_hasDepth13BasePrefix
  rw [depth18PrefixWord_supportCoeff_twentyOne] at hcoeff
  simpa [stage21] using Stage.endpoint_step_eq stage20 (by norm_num)
    stage20_endpoint hcoeff

theorem stage22_endpoint : stage22.endpoint = 263 := by
  have hcoeff := Stage.nextCoeff_eq_depth18Prefix stage21 (by norm_num)
    stage21_hasDepth13BasePrefix
  rw [depth18PrefixWord_supportCoeff_twentyTwo] at hcoeff
  simpa [stage22] using Stage.endpoint_step_eq stage21 (by norm_num)
    stage21_endpoint hcoeff

theorem stage23_endpoint : stage23.endpoint = 526 := by
  have hcoeff := Stage.nextCoeff_eq_depth18Prefix stage22 (by norm_num)
    stage22_hasDepth13BasePrefix
  rw [depth18PrefixWord_supportCoeff_twentyThree] at hcoeff
  simpa [stage23] using Stage.endpoint_step_eq stage22 (by norm_num)
    stage22_endpoint hcoeff

theorem stage24_endpoint : stage24.endpoint = 1049 := by
  have hcoeff := Stage.nextCoeff_eq_depth18Prefix stage23 (by norm_num)
    stage23_hasDepth13BasePrefix
  rw [depth18PrefixWord_supportCoeff_twentyFour] at hcoeff
  simpa [stage24] using Stage.endpoint_step_eq stage23 (by norm_num)
    stage23_endpoint hcoeff

theorem stage25_endpoint : stage25.endpoint = 2098 := by
  have hcoeff := Stage.nextCoeff_eq_depth18Prefix stage24 (by norm_num)
    stage24_hasDepth13BasePrefix
  rw [depth18PrefixWord_supportCoeff_twentyFive] at hcoeff
  simpa [stage25] using Stage.endpoint_step_eq stage24 (by norm_num)
    stage24_endpoint hcoeff

theorem stage26_endpoint : stage26.endpoint = 4195 := by
  have hcoeff := Stage.nextCoeff_eq_depth18Prefix stage25 (by norm_num)
    stage25_hasDepth13BasePrefix
  rw [depth18PrefixWord_supportCoeff_twentySix] at hcoeff
  simpa [stage26] using Stage.endpoint_step_eq stage25 (by norm_num)
    stage25_endpoint hcoeff

theorem stage27_endpoint : stage27.endpoint = 8389 := by
  have hcoeff := Stage.nextCoeff_eq_depth18Prefix stage26 (by norm_num)
    stage26_hasDepth13BasePrefix
  rw [depth18PrefixWord_supportCoeff_twentySeven] at hcoeff
  simpa [stage27] using Stage.endpoint_step_eq stage26 (by norm_num)
    stage26_endpoint hcoeff

/-- The first feedback head weight lies strictly below the complete live
suffix interval, with 183 units of spare endpoint margin. -/
theorem halfStripBound_twentySeven : halfStripBound 27 = 14 := by
  have hsqrt : Nat.sqrt 27 = 5 := by
    symm
    exact Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩
  simp [halfStripBound, hsqrt]

theorem depth27_feedback_headThreshold_margin :
    2 ^ (27 - (13 + 1)) + halfStripBound 27 ≤ stage27.endpoint := by
  rw [stage27_endpoint, halfStripBound_twentySeven]
  norm_num

theorem depth27SelectedHalfWindow_commonRestrictionAt_fourteen :
    depth27SelectedHalfWindow.CommonRestrictionAt
      (by omega : 14 ≤ 27) := by
  apply commonRestrictionAt_succ_of_headThreshold_add_width_le_endpoint
    (K := 13) (E := stage27.endpoint)
      depth27SelectedHalfWindow (by omega)
  · unfold halfStripBound
    omega
  · simpa using depth27SelectedHalfWindow_hasSuffixCylinderAt_thirteen
  · exact depth27_feedback_headThreshold_margin

/-- Exact promoted cylinder at the first feedback cutoff: removing the now
common true bit of weight `8192` shifts endpoint `8389` to `197`. -/
theorem depth27SelectedHalfWindow_hasSuffixCylinderAt_fourteen :
    HasSuffixCylinderAt depth27SelectedHalfWindow
      (by omega : 14 ≤ 27) 197 := by
  have hpromote :=
    promoteSuffixCylinderAt_succ_of_headThreshold_add_width_le_endpoint
      (K := 13) (E := stage27.endpoint)
      depth27SelectedHalfWindow (by omega)
      (by unfold halfStripBound; omega)
      (by simpa using depth27SelectedHalfWindow_hasSuffixCylinderAt_thirteen)
      depth27_feedback_headThreshold_margin
  have hshift : stage27.endpoint - 2 ^ (27 - (13 + 1)) = 197 := by
    rw [stage27_endpoint]
    norm_num
  rw [hshift] at hpromote
  exact hpromote.1

theorem depth27_promoted_endpoint_covers_strip :
    halfStripBound 27 ≤ 197 := by
  rw [halfStripBound_twentySeven]
  norm_num

theorem depth27SelectedHalfWindow_restrict_fourteen :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 27),
      restrictWord (by omega : 14 ≤ 27)
          (depth27SelectedHalfWindow.word k hk hkR) =
        extendHalfWord depth18PrefixWord true := by
  apply
    restrictWord_succ_eq_extend_true_of_headThreshold_add_width_le_endpoint
      (K := 13) (E := stage27.endpoint)
      depth27SelectedHalfWindow (by omega) depth18PrefixWord
  · simpa [depth27SelectedHalfWindow, HasDepth13BasePrefix] using
      stage27_hasDepth13BasePrefix
  · simpa using depth27SelectedHalfWindow_hasSuffixCylinderAt_thirteen
  · exact depth27_feedback_headThreshold_margin

theorem depth14PromotedPrefix_supportCoeff_twentyEight :
    supportCoeff (wordSupport (extendHalfWord depth18PrefixWord true)) 28 = 3 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth27SelectedHalfWindow_supportCoeff_twentyEight
    (k : ℕ) (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 27) :
    supportCoeff
      (wordSupport (depth27SelectedHalfWindow.word k hk hkR)) 28 = 3 := by
  calc
    supportCoeff
        (wordSupport (depth27SelectedHalfWindow.word k hk hkR)) 28 =
        supportCoeff
          (wordSupport (extendHalfWord depth18PrefixWord true)) 28 :=
      supportCoeff_eq_of_restriction_at_halfDivisor
        (K := 13) (M := 27) (by omega) (by omega)
        (depth27SelectedHalfWindow.word k hk hkR)
        (extendHalfWord depth18PrefixWord true)
        (depth27SelectedHalfWindow_restrict_fourteen k hk hkR)
    _ = 3 := depth14PromotedPrefix_supportCoeff_twentyEight

theorem depth27SelectedHalfWindow_selectedRowCoeff_eq_three
    (k : ℕ) (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 27) :
    selectedRowCoeff depth27SelectedHalfWindow k = 3 := by
  rw [selectedRowCoeff, dif_pos ⟨hk, hkR⟩]
  exact_mod_cast depth27SelectedHalfWindow_supportCoeff_twentyEight k hk hkR

theorem halfStripBound_twentyEight : halfStripBound 28 = 14 := by
  have hsqrt : Nat.sqrt 28 = 5 := by
    symm
    exact Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩
  simp [halfStripBound, hsqrt]

theorem depth27_to_depth28_buffer :
    halfStripBound 28 + 3 ≤ 2 * halfStripBound 27 := by
  rw [halfStripBound_twentySeven, halfStripBound_twentyEight]
  norm_num

/-- First full selected window beyond the first genuine feedback row. -/
noncomputable def depth28SelectedHalfWindow :
    SelectedHalfWindow 28 (halfStripBound 28) :=
  depth27SelectedHalfWindow.stepExplicit (C := 3) (by omega) le_rfl
    depth27SelectedHalfWindow_selectedRowCoeff_eq_three
    depth27_to_depth28_buffer

/-- The exact depth-28 endpoint is `2*197-3 = 391`. -/
theorem depth28SelectedHalfWindow_hasSuffixCylinderAt_fourteen :
    HasSuffixCylinderAt depth28SelectedHalfWindow
      (by omega : 14 ≤ 28) 391 := by
  have hstep :=
    SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit
      (M := 14) (E := 197) (C := 3)
      (by omega : 1 ≤ 27) depth27SelectedHalfWindow (by omega)
      (le_refl (halfStripBound 28))
      depth27SelectedHalfWindow_selectedRowCoeff_eq_three
      depth27_to_depth28_buffer
      depth27SelectedHalfWindow_hasSuffixCylinderAt_fourteen
      depth27_promoted_endpoint_covers_strip
  simpa [depth28SelectedHalfWindow] using hstep.1

theorem depth28SelectedHalfWindow_endpoint_covers_strip :
    halfStripBound 28 ≤ 391 := by
  rw [halfStripBound_twentyEight]
  norm_num

theorem depth28SelectedHalfWindow_admissible
    {k : ℕ} (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 28) :
    HalfStripAdmissible 28
      (depth28SelectedHalfWindow.word k hk hkR) :=
  depth28SelectedHalfWindow.admissible k hk hkR

theorem depth28SelectedHalfWindow_restrict_fourteen :
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 28),
      restrictWord (by omega : 14 ≤ 28)
          (depth28SelectedHalfWindow.word k hk hkR) =
        extendHalfWord depth18PrefixWord true := by
  simpa [depth28SelectedHalfWindow] using
    (SelectedHalfWindow.stepExplicit_preserves_literalPrefix
      (M := 14) (C := 3) depth27SelectedHalfWindow (by omega)
      (extendHalfWord depth18PrefixWord true) (by omega)
      (le_refl (halfStripBound 28))
      depth27SelectedHalfWindow_selectedRowCoeff_eq_three
      depth27_to_depth28_buffer
      depth27SelectedHalfWindow_restrict_fourteen)

theorem depth14PromotedPrefix_supportCoeff_twentyNine :
    supportCoeff (wordSupport (extendHalfWord depth18PrefixWord true)) 29 = 0 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth28SelectedHalfWindow_supportCoeff_twentyNine
    (k : ℕ) (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 28) :
    supportCoeff
      (wordSupport (depth28SelectedHalfWindow.word k hk hkR)) 29 = 0 := by
  calc
    supportCoeff
        (wordSupport (depth28SelectedHalfWindow.word k hk hkR)) 29 =
        supportCoeff
          (wordSupport (extendHalfWord depth18PrefixWord true)) 29 :=
      supportCoeff_word_eq_of_restrict_before_feedback
        (M := 14) (N := 28) (n := 29) (by omega)
        (depth28SelectedHalfWindow.word k hk hkR)
        (extendHalfWord depth18PrefixWord true)
        (depth28SelectedHalfWindow_restrict_fourteen k hk hkR)
        (by omega) (by omega) (by omega)
    _ = 0 := depth14PromotedPrefix_supportCoeff_twentyNine

theorem depth28SelectedHalfWindow_selectedRowCoeff_eq_zero
    (k : ℕ) (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 28) :
    selectedRowCoeff depth28SelectedHalfWindow k = 0 := by
  rw [selectedRowCoeff, dif_pos ⟨hk, hkR⟩]
  exact_mod_cast depth28SelectedHalfWindow_supportCoeff_twentyNine k hk hkR

theorem halfStripBound_twentyNine : halfStripBound 29 = 14 := by
  have hsqrt : Nat.sqrt 29 = 5 := by
    symm
    exact Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩
  simp [halfStripBound, hsqrt]

theorem depth28_to_depth29_buffer :
    halfStripBound 29 + 0 ≤ 2 * halfStripBound 28 := by
  rw [halfStripBound_twentyEight, halfStripBound_twentyNine]
  norm_num

noncomputable def depth29SelectedHalfWindow :
    SelectedHalfWindow 29 (halfStripBound 29) :=
  depth28SelectedHalfWindow.stepExplicit (C := 0) (by omega) le_rfl
    depth28SelectedHalfWindow_selectedRowCoeff_eq_zero
    depth28_to_depth29_buffer

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_fourteen :
    HasSuffixCylinderAt depth29SelectedHalfWindow
      (by omega : 14 ≤ 29) 782 := by
  have hstep :=
    SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit
      (M := 14) (E := 391) (C := 0)
      (by omega : 1 ≤ 28) depth28SelectedHalfWindow (by omega)
      (le_refl (halfStripBound 29))
      depth28SelectedHalfWindow_selectedRowCoeff_eq_zero
      depth28_to_depth29_buffer
      depth28SelectedHalfWindow_hasSuffixCylinderAt_fourteen
      depth28SelectedHalfWindow_endpoint_covers_strip
  simpa [depth29SelectedHalfWindow] using hstep.1

theorem depth29SelectedHalfWindow_endpoint_covers_strip :
    halfStripBound 29 ≤ 782 := by
  rw [halfStripBound_twentyNine]
  norm_num

theorem depth29SelectedHalfWindow_admissible
    {k : ℕ} (hk : 1 ≤ k) (hkR : k ≤ halfStripBound 29) :
    HalfStripAdmissible 29
      (depth29SelectedHalfWindow.word k hk hkR) :=
  depth29SelectedHalfWindow.admissible k hk hkR

/-! Exact maximal normalization of the depth-29 cylinder. -/

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_fifteen :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 15 ≤ 29) 782 :=
  (promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    (K := 14) depth29SelectedHalfWindow (by omega)
    (by rw [halfStripBound_twentyNine]; omega)
    depth29SelectedHalfWindow_hasSuffixCylinderAt_fourteen (by norm_num)).1

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_sixteen :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 16 ≤ 29) 782 :=
  (promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    (K := 15) depth29SelectedHalfWindow (by omega)
    (by rw [halfStripBound_twentyNine]; omega)
    (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_fifteen)
    (by norm_num)).1

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_seventeen :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 17 ≤ 29) 782 :=
  (promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    (K := 16) depth29SelectedHalfWindow (by omega)
    (by rw [halfStripBound_twentyNine]; omega)
    (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_sixteen)
    (by norm_num)).1

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_eighteen :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 18 ≤ 29) 782 :=
  (promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    (K := 17) depth29SelectedHalfWindow (by omega)
    (by rw [halfStripBound_twentyNine]; omega)
    (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_seventeen)
    (by norm_num)).1

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_nineteen :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 19 ≤ 29) 782 :=
  (promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    (K := 18) depth29SelectedHalfWindow (by omega)
    (by rw [halfStripBound_twentyNine]; omega)
    (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_eighteen)
    (by norm_num)).1

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_twenty :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 20 ≤ 29) 270 := by
  have h :=
    (promoteSuffixCylinderAt_succ_of_headThreshold_add_width_le_endpoint
      (K := 19) depth29SelectedHalfWindow (by omega)
      (by rw [halfStripBound_twentyNine]; omega)
      (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_nineteen)
      (by rw [halfStripBound_twentyNine]; norm_num)).1
  simpa using h

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyOne :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 21 ≤ 29) 14 := by
  have h :=
    (promoteSuffixCylinderAt_succ_of_headThreshold_add_width_le_endpoint
      (K := 20) depth29SelectedHalfWindow (by omega)
      (by rw [halfStripBound_twentyNine]; omega)
      (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twenty)
      (by rw [halfStripBound_twentyNine]; norm_num)).1
  simpa using h

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyTwo :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 22 ≤ 29) 14 :=
  (promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    (K := 21) depth29SelectedHalfWindow (by omega)
    (by rw [halfStripBound_twentyNine]; omega)
    (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyOne)
    (by norm_num)).1

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyThree :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 23 ≤ 29) 14 :=
  (promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    (K := 22) depth29SelectedHalfWindow (by omega)
    (by rw [halfStripBound_twentyNine]; omega)
    (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyTwo)
    (by norm_num)).1

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyFour :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 24 ≤ 29) 14 :=
  (promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    (K := 23) depth29SelectedHalfWindow (by omega)
    (by rw [halfStripBound_twentyNine]; omega)
    (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyThree)
    (by norm_num)).1

theorem depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyFive :
    HasSuffixCylinderAt depth29SelectedHalfWindow (by omega : 25 ≤ 29) 14 :=
  (promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
    (K := 24) depth29SelectedHalfWindow (by omega)
    (by rw [halfStripBound_twentyNine]; omega)
    (by simpa using depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyFour)
    (by norm_num)).1

/-- Cutoff 25 is maximal: the next suffix bit splits the protected interval
exactly across weight eight. -/
theorem depth29SelectedHalfWindow_not_commonRestrictionAt_twentySix :
    ¬ depth29SelectedHalfWindow.CommonRestrictionAt
      (by omega : 26 ≤ 29) := by
  intro hcommon
  have hcrit :=
    (commonRestrictionAt_succ_iff_endpoint_avoids_headThreshold
      (K := 25) (E := 14) depth29SelectedHalfWindow (by omega)
      (by rw [halfStripBound_twentyNine]; omega)
      (by simpa using
        depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyFive)).1 hcommon
  rw [halfStripBound_twentyNine] at hcrit
  norm_num at hcrit

/-! ## Reusable feedback macrostep -/

/-- Full-strip suffix-cylinder state with a movable common-prefix cutoff. -/
structure CylinderStage (K N : ℕ) where
  hKN : K ≤ N
  window : SelectedHalfWindow N (halfStripBound N)
  endpoint : ℕ
  cylinder : HasSuffixCylinderAt window hKN endpoint
  covers : halfStripBound N ≤ endpoint

/-- Consumer-facing name emphasizing that every stage covers the complete
square-root strip. -/
abbrev FullCylinderStage := CylinderStage

/-- Ordinary row advance whenever the current cutoff sees every proper
divisor of the next row. -/
noncomputable def CylinderStage.advance
    {K N : ℕ} (S : CylinderStage K N) (hN : 1 ≤ N)
    (hhalf : (N + 1) / 2 ≤ K) : CylinderStage K (N + 1) := by
  let W := S.window
  have hR : 1 ≤ halfStripBound N := by
    unfold halfStripBound
    omega
  have hcommon : W.CommonRestrictionAt S.hKN :=
    commonRestrictionAt_of_suffixCylinder W S.hKN S.cylinder
  have hagree : W.NextRowDivisorAgreement :=
    W.nextRowDivisorAgreement_of_commonRestriction S.hKN hhalf hcommon
  let a₁ := W.word 1 (by omega) hR
  let C : ℕ := supportCoeff (wordSupport a₁) (N + 1)
  have hp_common : ∀ k : ℕ, 1 ≤ k → k ≤ halfStripBound N →
      selectedRowCoeff W k = C := by
    intro k hk hkR
    calc
      selectedRowCoeff W k = selectedRowCoeff W 1 :=
        W.selectedRowCoeff_eq hagree hk hkR (by omega) hR
      _ = C := by
        rw [selectedRowCoeff, dif_pos ⟨show 1 ≤ (1 : ℕ) by omega, hR⟩]
  have hbuffer : halfStripBound (N + 1) + C ≤
      2 * halfStripBound N := by
    have hC : C ≤ 2 * Nat.sqrt (N + 1) := by
      exact supportCoeff_le_two_mul_sqrt (wordSupport a₁) (N + 1)
    simpa using halfStripBound_add_coeff_le_two_mul_pred
      (n := N + 1) (c := C) (by omega) hC
  let W' : SelectedHalfWindow (N + 1) (halfStripBound (N + 1)) :=
    W.stepExplicit hN le_rfl hp_common hbuffer
  have hcyl' : HasSuffixCylinderAt W'
      (S.hKN.trans (Nat.le_succ N)) (2 * S.endpoint - C) ∧
      halfStripBound (N + 1) ≤ 2 * S.endpoint - C :=
    SelectedHalfWindow.hasSuffixCylinderAt_stepExplicit
      hN W S.hKN le_rfl hp_common hbuffer S.cylinder S.covers
  exact ⟨S.hKN.trans (Nat.le_succ N), W', 2 * S.endpoint - C,
    hcyl'.1, hcyl'.2⟩

/-- Iterate ordinary full-strip advances as long as the fixed cutoff remains
at least the half-depth of every newly inspected row. -/
noncomputable def CylinderStage.advanceWithinCutoff
    {K N : ℕ} (S : CylinderStage K N) (hN : 1 ≤ N) :
    (d : ℕ) → N + d ≤ 2 * K + 1 → CylinderStage K (N + d)
  | 0, _horizon => by simpa using S
  | d + 1, hhorizon => by
      have hprevHorizon : N + d ≤ 2 * K + 1 := by omega
      let prev := S.advanceWithinCutoff hN d hprevHorizon
      have hprevN : 1 ≤ N + d := by omega
      have hhalf : (N + d + 1) / 2 ≤ K := by omega
      have next := prev.advance hprevN hhalf
      simpa [Nat.add_assoc] using next

/-- Promote the cutoff itself through a high-side binary threshold, without
changing the selected window. -/
noncomputable def CylinderStage.promoteHigh
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hmargin : 2 ^ (N - (K + 1)) + halfStripBound N ≤ S.endpoint) :
    CylinderStage (K + 1) N := by
  have hR : 1 ≤ halfStripBound N := by
    unfold halfStripBound
    omega
  have hpromote :=
    promoteSuffixCylinderAt_succ_of_headThreshold_add_width_le_endpoint
      S.window hK1N hR S.cylinder hmargin
  exact ⟨hK1N, S.window, S.endpoint - 2 ^ (N - (K + 1)),
    hpromote.1, hpromote.2⟩

/-- Reusable feedback macrostep: first absorb the newly visible half-divisor
bit using the exact endpoint margin, then perform the ordinary full-strip
advance with the promoted cutoff. -/
noncomputable def CylinderStage.feedbackAdvanceHigh
    {K N : ℕ} (S : CylinderStage K N) (hN : 1 ≤ N)
    (hK1N : K + 1 ≤ N) (hfeedback : (N + 1) / 2 ≤ K + 1)
    (hmargin : 2 ^ (N - (K + 1)) + halfStripBound N ≤ S.endpoint) :
    CylinderStage (K + 1) (N + 1) :=
  (S.promoteHigh hK1N hmargin).advance hN hfeedback

noncomputable def fullCylinderOrdinaryTransition
    {K N : ℕ} (S : FullCylinderStage K N) (hN : 1 ≤ N)
    (hhalf : (N + 1) / 2 ≤ K) : FullCylinderStage K (N + 1) :=
  S.advance hN hhalf

noncomputable def fullCylinderFeedbackTransitionHigh
    {K N : ℕ} (S : FullCylinderStage K N) (hN : 1 ≤ N)
    (hK1N : K + 1 ≤ N) (hfeedback : (N + 1) / 2 ≤ K + 1)
    (hmargin : 2 ^ (N - (K + 1)) + halfStripBound N ≤ S.endpoint) :
    FullCylinderStage (K + 1) (N + 1) :=
  S.feedbackAdvanceHigh hN hK1N hfeedback hmargin

noncomputable def fullCylinderStage29 : FullCylinderStage 25 29 :=
  ⟨by omega, depth29SelectedHalfWindow, 14,
    depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyFive,
    by rw [halfStripBound_twentyNine]⟩

/-- The normalized depth-29 state advances unconditionally through depth 51;
no new feedback decision is required in this entire finite band. -/
noncomputable def fullCylinderStage51 : FullCylinderStage 25 51 := by
  simpa using fullCylinderStage29.advanceWithinCutoff (by norm_num) 22
    (by norm_num)

noncomputable def cylinderStage27 : CylinderStage 13 27 :=
  ⟨by omega, depth27SelectedHalfWindow, stage27.endpoint,
    depth27SelectedHalfWindow_hasSuffixCylinderAt_thirteen,
    depth27SelectedHalfWindow_endpoint_covers_strip⟩

/-- The generic feedback macrostep is inhabited on the live first-feedback
state, independently of the separately exposed exact depth-28 window. -/
noncomputable def cylinderStage28 : CylinderStage 14 28 :=
  cylinderStage27.feedbackAdvanceHigh (by omega) (by omega) (by norm_num)
    depth27_feedback_headThreshold_margin

#print axioms commonRestrictionAt_succ_iff_endpoint_avoids_headThreshold
#print axioms commonRestrictionAt_succ_of_headThreshold_add_width_le_endpoint
#print axioms promoteSuffixCylinderAt_succ_of_headThreshold_add_width_le_endpoint
#print axioms promoteSuffixCylinderAt_succ_of_endpoint_le_headThreshold
#print axioms stage27_endpoint
#print axioms depth27SelectedHalfWindow_commonRestrictionAt_fourteen
#print axioms depth27SelectedHalfWindow_hasSuffixCylinderAt_fourteen
#print axioms depth28SelectedHalfWindow
#print axioms depth28SelectedHalfWindow_hasSuffixCylinderAt_fourteen
#print axioms depth29SelectedHalfWindow
#print axioms depth29SelectedHalfWindow_hasSuffixCylinderAt_fourteen
#print axioms depth29SelectedHalfWindow_hasSuffixCylinderAt_twentyFive
#print axioms depth29SelectedHalfWindow_not_commonRestrictionAt_twentySix
#print axioms CylinderStage.advance
#print axioms CylinderStage.advanceWithinCutoff
#print axioms CylinderStage.feedbackAdvanceHigh
#print axioms fullCylinderStage51

end Erdos249257.SuffixCylinderThreshold
