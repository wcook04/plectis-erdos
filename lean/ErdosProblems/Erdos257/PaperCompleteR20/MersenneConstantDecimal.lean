import Erdos249257.GreedyAchievementSet

namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257

set_option maxHeartbeats 4000000 in
/-- Exact interval certifying the printed 16-place truncation of E-3/2. -/
theorem mersenne_constant_decimal :
    (1066951524152917 : ℝ)/10^16 < erdosBorweinMersenneConstant-3/2 ∧
      erdosBorweinMersenneConstant-3/2 < (1066951524152918 : ℝ)/10^16 := by
  have he := erdosBorweinMersenneConstant_eq_prefix_add_tail 60
  have ht := mersenneTail_pos 60
  have hu := mersenneTail_le_two_mul_weight 60
  have hl : (1066951524152917 : ℝ)/10^16 < mersennePrefixMass 60-3/2 := by
    norm_num [mersennePrefixMass, Finset.sum_range_succ, mersenneWeight]
  have hh : mersennePrefixMass 60+2*mersenneWeight 61-3/2 < (1066951524152918 : ℝ)/10^16 := by
    norm_num [mersennePrefixMass, Finset.sum_range_succ, mersenneWeight]
  constructor <;> linarith

/-- Quantitative ambient-span and cylinder-limit clauses in the topology theorem. -/
theorem mersenne_topology_quantitative :
    |erdosBorweinMersenneConstant-(16067 : ℝ)/10000| < 1/20000 ∧
    1 < erdosBorweinMersenneConstant ∧
    Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ)^n*mersenneTail n) Filter.atTop (nhds 1) := by
  have h := mersenne_constant_decimal
  refine ⟨?_, ?_, tendsto_two_pow_mul_mersenneTail_one⟩
  · rw [abs_lt]
    constructor <;> linarith [h.1, h.2]
  · linarith [h.1]

#print axioms mersenne_topology_quantitative
#print axioms mersenne_constant_decimal
end ErdosProblems.Erdos257.PaperCompleteR20
