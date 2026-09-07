import Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy
import Mathlib.Tactic

/-!
# Literal low-row certificates for long obs:anchors-low

These are kernel certificates against the existing actual seam recursion. They
use `decide`, never `native_decide`, and no external computation is trusted.

A bare `decide` on `seamIntegerGreedyRemainder` does not reduce. The weight word
comes from `seamWeightsFrom`, which is defined by well-founded recursion
(`termination_by d => s - d`), and the kernel does not reduce `WellFounded.fix`;
the reported failure is exactly "reduction got stuck at the `Decidable`
instance". The library supplies the two equation lemmas this needs,
`seamWeightsFrom_eq_nil` and `seamWeightsFrom_eq_cons`, so each weight word is
first evaluated to a literal list and only the structural part of the greedy
recursion is left to `decide`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR7
open Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy

/-- Decode the actual greedy bit list into its exponent positions. -/
def seamSelectedExponents (s : ℕ) : Finset ℕ :=
  ((Finset.range (s - 2)).filter fun k =>
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))[k]?.getD false).image
      (fun k => k + 2)

/-! ### The weight words, evaluated through the equation lemmas -/

theorem seamWeights_fourteen : seamWeights 14 = [89478485, 38347922, 17895697, 8659208, 4260880, 2113665, 1052688, 525314, 262400, 131136, 65552, 32772] := by
  norm_num [seamWeights, seamWeightsFrom_eq_cons, seamWeightsFrom_eq_nil,
    truncatedMersenneWeight]

theorem seamWeights_fifteen : seamWeights 15 = [357913941, 153391689, 71582788, 34636833, 17043521, 8454660, 4210752, 2101256, 1049601, 524544, 262208, 131088, 65540] := by
  norm_num [seamWeights, seamWeightsFrom_eq_cons, seamWeightsFrom_eq_nil,
    truncatedMersenneWeight]

theorem seamWeights_thirtyOne : seamWeights 31 = [1537228672809129301, 658812288346769700, 307445734561825860, 148764065110560900, 73201365371863300, 36312488334073920, 18085043209519168, 9024825867763968, 4508001973047300, 2252899862446208, 1126174851874820, 563018681287680, 281492157628480, 140741783453700, 70369817935872, 35184640526336, 17592253153536, 8796109799456, 4398050705412, 2199024304128, 1099511889920, 549755879424, 274877923328, 137438957568, 68719477760, 34359738624, 17179869248, 8589934608, 4294967300] := by
  norm_num [seamWeights, seamWeightsFrom_eq_cons, seamWeightsFrom_eq_nil,
    truncatedMersenneWeight]

theorem seamWeights_thirtyTwo : seamWeights 32 = [6148914691236517205, 2635249153387078802, 1229782938247303441, 595056260442243600, 292805461487453200, 145249953336295682, 72340172838076673, 36099303471055874, 18032007892189200, 9011599449784832, 4504699407499280, 2252074725150720, 1125968630513920, 562967133814800, 281479271743489, 140738562105344, 70369012614144, 35184439197824, 17592202821648, 8796097216514, 4398047559680, 2199023517696, 1099511693312, 549755830272, 274877911040, 137438954496, 68719476992, 34359738432, 17179869200, 8589934596] := by
  norm_num [seamWeights, seamWeightsFrom_eq_cons, seamWeightsFrom_eq_nil,
    truncatedMersenneWeight]

/-! ### The certificates -/

set_option maxRecDepth 100000 in
theorem seam_remainder_fourteen : seamIntegerGreedyRemainder 14 = 392 := by
  simp only [seamIntegerGreedyRemainder, seamWeights_fourteen, seamSubsetTarget]
  decide

set_option maxRecDepth 100000 in
theorem seam_selected_exponents_fourteen :
    seamSelectedExponents 14 = ({2, 3, 6, 7} : Finset ℕ) := by
  simp only [seamSelectedExponents, seamWeights_fourteen, seamSubsetTarget]
  decide

set_option maxRecDepth 100000 in
theorem seam_remainder_fifteen : seamIntegerGreedyRemainder 15 = 34333 := by
  simp only [seamIntegerGreedyRemainder, seamWeights_fifteen, seamSubsetTarget]
  decide

set_option maxRecDepth 100000 in
theorem seam_remainder_thirtyTwo : seamIntegerGreedyRemainder 32 = 3865046005 := by
  simp only [seamIntegerGreedyRemainder, seamWeights_thirtyTwo, seamSubsetTarget]
  decide

set_option maxRecDepth 100000 in
/-- The extra numeric checkpoint in cert:band-through-31, not the claimed
all-rows band-avoidance certificate, which is a separate missing obligation. -/
theorem row_thirty_one_remainder : seamIntegerGreedyRemainder 31 = 4187487147 := by
  simp only [seamIntegerGreedyRemainder, seamWeights_thirtyOne, seamSubsetTarget]
  decide

/-- Full mathematical data of long obs:anchors-low, in one certificate. -/
theorem low_row_certificates :
    seamIntegerGreedyRemainder 14 = 392 ∧
    seamSelectedExponents 14 = ({2, 3, 6, 7} : Finset ℕ) ∧
    seamIntegerGreedyRemainder 15 = 34333 ∧
    seamIntegerGreedyRemainder 32 = 3865046005 ∧
    (seamIntegerGreedyRemainder 32 : ℤ) - (2 : ℤ) ^ 32 = -429921291 := by
  refine ⟨seam_remainder_fourteen, seam_selected_exponents_fourteen,
    seam_remainder_fifteen, seam_remainder_thirtyTwo, ?_⟩
  rw [seam_remainder_thirtyTwo]
  norm_num

end ErdosProblems.Erdos257.PaperCompleteR7
