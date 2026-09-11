import Erdos249257.SuffixCylinderThreshold

namespace Erdos249257.SuffixCylinderThreshold

open Erdos249257
open Erdos249257.HalfCarryReachability
open Erdos249257.HalfCarrySelectedWindow
open Erdos249257.HalfCarrySelectedWindowBase
open Erdos249257.SelectedSuffixCylinder
open Erdos249257.SelectedSuffixCylinderPreFeedback
open Erdos249257.RewindSeamOperationalBridge

theorem carryOneCoeff_eq_depth13Prefix
    {N : ℕ} (S : Stage N) (hhalf : (N + 1) / 2 ≤ 13)
    (hpfx : HasDepth13BasePrefix S)
    (hR : 1 ≤ halfStripBound N) :
    supportCoeff
        (wordSupport (S.window.word 1 (by omega) hR)) (N + 1) =
      supportCoeff (wordSupport depth18PrefixWord) (N + 1) := by
  exact supportCoeff_nextRow_eq_of_restriction
    S.h13 hhalf
    (S.window.word 1 (by omega) hR) depth18PrefixWord
    (hpfx 1 (by omega) hR)

theorem depth13Prefix_coeff_nineteen :
    supportCoeff (wordSupport depth18PrefixWord) 19 = 0 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth13Prefix_coeff_twenty :
    supportCoeff (wordSupport depth18PrefixWord) 20 = 1 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth13Prefix_coeff_twentyOne :
    supportCoeff (wordSupport depth18PrefixWord) 21 = 2 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth13Prefix_coeff_twentyTwo :
    supportCoeff (wordSupport depth18PrefixWord) 22 = 1 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth13Prefix_coeff_twentyThree :
    supportCoeff (wordSupport depth18PrefixWord) 23 = 0 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth13Prefix_coeff_twentyFour :
    supportCoeff (wordSupport depth18PrefixWord) 24 = 3 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth13Prefix_coeff_twentyFive :
    supportCoeff (wordSupport depth18PrefixWord) 25 = 0 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth13Prefix_coeff_twentySix :
    supportCoeff (wordSupport depth18PrefixWord) 26 = 1 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem depth13Prefix_coeff_twentySeven :
    supportCoeff (wordSupport depth18PrefixWord) 27 = 1 := by
  rw [← wordCoeff_eq_supportCoeff_wordSupport]
  decide

theorem stage18_endpoint_eq : stage18.endpoint = 17 := rfl

theorem stage19_endpoint_eq : stage19.endpoint = 34 := by
  rw [stage19]
  rw [Stage.endpoint_step stage18 (by norm_num) (by unfold halfStripBound; omega)]
  rw [stage18_endpoint_eq]
  rw [carryOneCoeff_eq_depth13Prefix stage18
    (by norm_num) stage18_hasDepth13BasePrefix
      (by unfold halfStripBound; omega)]
  rw [depth13Prefix_coeff_nineteen]

theorem stage20_endpoint_eq : stage20.endpoint = 67 := by
  rw [stage20]
  rw [Stage.endpoint_step stage19 (by norm_num) (by unfold halfStripBound; omega)]
  rw [stage19_endpoint_eq]
  rw [carryOneCoeff_eq_depth13Prefix stage19
    (by norm_num) stage19_hasDepth13BasePrefix
      (by unfold halfStripBound; omega)]
  rw [depth13Prefix_coeff_twenty]

theorem stage21_endpoint_eq : stage21.endpoint = 132 := by
  rw [stage21]
  rw [Stage.endpoint_step stage20 (by norm_num) (by unfold halfStripBound; omega)]
  rw [stage20_endpoint_eq]
  rw [carryOneCoeff_eq_depth13Prefix stage20
    (by norm_num) stage20_hasDepth13BasePrefix
      (by unfold halfStripBound; omega)]
  rw [depth13Prefix_coeff_twentyOne]

theorem stage22_endpoint_eq : stage22.endpoint = 263 := by
  rw [stage22]
  rw [Stage.endpoint_step stage21 (by norm_num) (by unfold halfStripBound; omega)]
  rw [stage21_endpoint_eq]
  rw [carryOneCoeff_eq_depth13Prefix stage21
    (by norm_num) stage21_hasDepth13BasePrefix
      (by unfold halfStripBound; omega)]
  rw [depth13Prefix_coeff_twentyTwo]

theorem stage23_endpoint_eq : stage23.endpoint = 526 := by
  rw [stage23]
  rw [Stage.endpoint_step stage22 (by norm_num) (by unfold halfStripBound; omega)]
  rw [stage22_endpoint_eq]
  rw [carryOneCoeff_eq_depth13Prefix stage22
    (by norm_num) stage22_hasDepth13BasePrefix
      (by unfold halfStripBound; omega)]
  rw [depth13Prefix_coeff_twentyThree]

theorem stage24_endpoint_eq : stage24.endpoint = 1049 := by
  rw [stage24]
  rw [Stage.endpoint_step stage23 (by norm_num) (by unfold halfStripBound; omega)]
  rw [stage23_endpoint_eq]
  rw [carryOneCoeff_eq_depth13Prefix stage23
    (by norm_num) stage23_hasDepth13BasePrefix
      (by unfold halfStripBound; omega)]
  rw [depth13Prefix_coeff_twentyFour]

theorem stage25_endpoint_eq : stage25.endpoint = 2098 := by
  rw [stage25]
  rw [Stage.endpoint_step stage24 (by norm_num) (by unfold halfStripBound; omega)]
  rw [stage24_endpoint_eq]
  rw [carryOneCoeff_eq_depth13Prefix stage24
    (by norm_num) stage24_hasDepth13BasePrefix
      (by unfold halfStripBound; omega)]
  rw [depth13Prefix_coeff_twentyFive]

theorem stage26_endpoint_eq : stage26.endpoint = 4195 := by
  rw [stage26]
  rw [Stage.endpoint_step stage25 (by norm_num) (by unfold halfStripBound; omega)]
  rw [stage25_endpoint_eq]
  rw [carryOneCoeff_eq_depth13Prefix stage25
    (by norm_num) stage25_hasDepth13BasePrefix
      (by unfold halfStripBound; omega)]
  rw [depth13Prefix_coeff_twentySix]

theorem stage27_endpoint_eq : stage27.endpoint = 8389 := by
  rw [stage27]
  rw [Stage.endpoint_step stage26 (by norm_num) (by unfold halfStripBound; omega)]
  rw [stage26_endpoint_eq]
  rw [carryOneCoeff_eq_depth13Prefix stage26
    (by norm_num) stage26_hasDepth13BasePrefix
      (by unfold halfStripBound; omega)]
  rw [depth13Prefix_coeff_twentySeven]

theorem depth27_commonRestrictionAt_fourteen :
    depth27SelectedHalfWindow.CommonRestrictionAt (by omega : 14 ≤ 27) := by
  apply commonRestrictionAt_succ_of_headThreshold_add_width_le_endpoint
    depth27SelectedHalfWindow (K := 13) (E := stage27.endpoint)
    (by norm_num) (by unfold halfStripBound; omega)
  · exact depth27SelectedHalfWindow_hasSuffixCylinderAt_thirteen
  · rw [stage27_endpoint_eq]
    have hB : halfStripBound 27 = 14 := by decide +kernel
    rw [hB]
    norm_num

#print axioms stage27_endpoint_eq
#print axioms depth27_commonRestrictionAt_fourteen

end Erdos249257.SuffixCylinderThreshold
