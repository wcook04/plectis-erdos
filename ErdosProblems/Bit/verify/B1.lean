/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Bit.Corr1
import ErdosProblems.Skip.D3

/-! Adversarial verification scratch file for `ErdosProblems/Bit/Corr1.lean`. -/

namespace Erdos249257
namespace BitCorr

open HalfCylinderIntegerGreedy

/-! ## 1. Axiom audit: every theorem in Corr1.lean -/

#print axioms mod_sub_of_le_mod
#print axioms testBit_sub_of_le_mod
#print axioms lateCorrection_eq_zero
#print axioms lateCorrection_eq_cons
#print axioms lateCorrection_succ_le
#print axioms three_mul_lateCorrection_add_four
#print axioms lateCorrection_lt_two_pow
#print axioms lateBitWord_eq_nil
#print axioms lateBitWord_eq_cons
#print axioms lateBitWord_congr
#print axioms lateBitWord_length
#print axioms lateBitWord_getElem?
#print axioms integerGreedyBits_seamWeightsFrom_eq_lateBitWord
#print axioms getElem?_eq_testBit
#print axioms takes_iff_testBit
#print axioms all_true_iff_forall_testBit
#print axioms integerGreedyBits_append
#print axioms seamWeightsFrom_drop
#print axioms seamWeights_eq_take_append
#print axioms earlyWeights_length
#print axioms seamGreedyBits_split
#print axioms mem_seamGreedySupport_iff_getElem
#print axioms mem_seamGreedySupport_iff_testBit

#print axioms Concrete.fourteen_is_first_late
#print axioms Concrete.seamWeightsFrom_twenty_fourteen
#print axioms Concrete.lateCorrection_twenty_fourteen
#print axioms Concrete.hypotheses_hold
#print axioms Concrete.greedy_word
#print axioms Concrete.bit_word
#print axioms Concrete.correspondence
#print axioms Concrete.seamWeights_twenty
#print axioms Concrete.lateEntryRemainder_twenty_fourteen
#print axioms Concrete.actual_hypotheses_hold
#print axioms Concrete.actual_late_word
#print axioms Concrete.fourteen_mem_seamGreedySupport_twenty
#print axioms Concrete.fifteen_not_mem_seamGreedySupport_twenty
#print axioms Concrete.fifteen_is_late
#print axioms Concrete.nineteen_not_mem_seamGreedySupport_twenty
#print axioms Concrete.largestSkipLateAt_twenty

/-! ## 2. Full elaborated statements — hunting for hidden hypotheses -/

#check @integerGreedyBits_seamWeightsFrom_eq_lateBitWord
#check @mem_seamGreedySupport_iff_testBit
#check @takes_iff_testBit
#check @all_true_iff_forall_testBit
#print lateCorrection
#print lateBitWord
#print earlyWeights
#print lateEntryRemainder
#print Erdos249257.LargestSkipLateAt
#print Erdos249257.IsLargestFalseRank
#print Erdos249257.HalfCylinderIntegerGreedy.truncatedMersenneWeight
#print Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget

/-! ## 3. SATISFIABILITY SWEEP

Executable models of the corpus definitions, cross-validated below against the
numerals Corr1 proves by `decide +kernel`, then swept over a wide range of `s`. -/

namespace Probe

/-- `truncatedMersenneWeight`, unfolded. -/
def w (s d : ℕ) : ℕ := 4 ^ s / (2 ^ d - 1)

/-- `seamWeightsFrom s d`, structurally. -/
def wts (s : ℕ) : ℕ → List ℕ
  | 0 => []
  | (n + 1) => w s (s - (n + 1)) :: wts s n

/-- Weights for ranks `d, …, s-1`. -/
def wtsFrom (s d : ℕ) : List ℕ := wts s (s - d)

/-- Weights for ranks `2, …, d-1`. -/
def wtsEarly (s d : ℕ) : List ℕ := (wts s (s - 2)).take (d - 2)

def tgt (s : ℕ) : ℕ := 2 ^ (2 * s - 1) - 2 ^ s

def grd : List ℕ → ℕ → List Bool
  | [], _ => []
  | (x :: xs), C => if x ≤ C then true :: grd xs (C - x) else false :: grd xs C

def rem : List ℕ → ℕ → ℕ
  | [], C => C
  | (x :: xs), C => if x ≤ C then rem xs (C - x) else rem xs C

/-- `lateCorrection s d = ∑_{k=1}^{s-d} 4 ^ k`. -/
def corr (s d : ℕ) : ℕ := ((List.range (s - d)).map (fun k => 4 ^ (k + 1))).sum

/-- `lateEntryRemainder s d`. -/
def entry (s d : ℕ) : ℕ := rem (wtsEarly s d) (tgt s)

/-- First late rank: least `d` with `2 * s < 3 * d`. -/
def firstLate (s : ℕ) : ℕ := 2 * s / 3 + 1

/-- The two side conditions of `mem_seamGreedySupport_iff_testBit`. -/
def hyps (s d : ℕ) : Bool :=
  decide (entry s d < 2 ^ (2 * s - d + 1)) && decide (corr s d ≤ entry s d % 2 ^ (s + 1))

/-! ### 3a. Cross-validation of the model against Corr1's kernel-checked numerals -/

-- must be [67112960, 33555456, 16777472, 8388672, 4194320, 2097156]
#eval wtsFrom 20 14
-- must be 5460  (Concrete.lateCorrection_twenty_fourteen)
#eval corr 20 14
-- must be 67662313  (Concrete.lateEntryRemainder_twenty_fourteen)
#eval entry 20 14
-- must be [true, false, false, false, false, false]  (Concrete.actual_late_word)
#eval grd (wtsFrom 20 14) (entry 20 14)
-- must equal Concrete.seamWeights_twenty
#eval wts 20 18
-- 14 is the first late rank at s = 20
#eval firstLate 20

/-! ### 3b. Does `firstLate` really compute the least late rank? -/

#eval (List.range 200).all (fun s =>
  decide (2 * s < 3 * firstLate s) && (decide (firstLate s = 0) ||
    decide (¬ (2 * s < 3 * (firstLate s - 1)))))

/-! ### 3c. THE SWEEP: for how many rows do the hypotheses of
`mem_seamGreedySupport_iff_testBit` actually hold, at the first late rank? -/

-- Rows `s in [5,120]` on which BOTH side conditions hold at `d = firstLate s`:
#eval ((List.range 116).map (· + 5)).filter (fun s => hyps s (firstLate s)) |>.length
-- Rows `s in [5,120]` on which they FAIL:
#eval ((List.range 116).map (· + 5)).filter (fun s => ! hyps s (firstLate s))
-- Which side fails, on each failing row:
#eval ((List.range 116).map (· + 5)).map (fun s =>
  (s, firstLate s, decide (entry s (firstLate s) < 2 ^ (2 * s - firstLate s + 1)),
      decide (corr s (firstLate s) ≤ entry s (firstLate s) % 2 ^ (s + 1))))
  |>.filter (fun t => ! (t.2.2.1 && t.2.2.2))

-- Sweep over EVERY late rank `d` (not just the first) on rows `s in [5,60]`:
-- (number of admissible (s,d) pairs, number on which both side conditions hold)
#eval
  let pairs := ((List.range 56).map (· + 5)).flatMap (fun s =>
    ((List.range s).filter (fun d => 2 ≤ d && 2 * s < 3 * d && d < s)).map (fun d => (s, d)))
  (pairs.length, (pairs.filter (fun p => hyps p.1 p.2)).length)

-- The failing (s,d) pairs:
#eval
  let pairs := ((List.range 56).map (· + 5)).flatMap (fun s =>
    ((List.range s).filter (fun d => 2 ≤ d && 2 * s < 3 * d && d < s)).map (fun d => (s, d)))
  pairs.filter (fun p => ! hyps p.1 p.2)

/-! ### 3d. Is the CONCLUSION non-trivial?  If every late bit were `1` the
criterion would say nothing.  Here is the actual late word on each row. -/

#eval ((List.range 26).map (· + 5)).map (fun s =>
  (s, firstLate s, grd (wtsFrom s (firstLate s)) (entry s (firstLate s))))

-- Largest false rank of each row, and whether it is late (2*s < 3*L):
#eval ((List.range 40).map (· + 5)).map (fun s =>
  let bits := grd (wts s (s - 2)) (tgt s)
  let fr := ((List.zip (List.range (s - 2)) bits).filter (fun p => ! p.2)).map (fun p => p.1 + 2)
  let L := fr.foldl max 0
  (s, L, decide (2 * s < 3 * L)))

end Probe

/-! ## 4. INDEPENDENT cross-check of the concrete payload.

`Concrete.largestSkipLateAt_twenty` is re-proved here WITHOUT any of Corr1's
machinery, using only the corpus's own decidable membership criterion
`SkipD3.mem_support_iff`.  Two purposes: (i) confirm the numeric claim is true,
(ii) measure how much Corr1's apparatus actually buys at a concrete row. -/

set_option maxRecDepth 100000 in
theorem probe_nineteen_not_mem : 19 ∉ seamWordSupport (seamGreedyWord 20) := by
  rw [SkipD3.mem_support_iff (by norm_num) (by norm_num)]
  decide +kernel

set_option maxRecDepth 100000 in
theorem probe_fifteen_not_mem : 15 ∉ seamWordSupport (seamGreedyWord 20) := by
  rw [SkipD3.mem_support_iff (by norm_num) (by norm_num)]
  decide +kernel

set_option maxRecDepth 100000 in
theorem probe_fourteen_mem : 14 ∈ seamWordSupport (seamGreedyWord 20) := by
  rw [SkipD3.mem_support_iff (by norm_num) (by norm_num)]
  decide +kernel

/-- `LargestSkipLateAt 20`, proved with zero input from Corr1. -/
theorem probe_largestSkipLateAt_twenty : LargestSkipLateAt 20 :=
  ⟨19, ⟨by norm_num, by norm_num, probe_nineteen_not_mem,
      fun e h1 h2 => absurd h2 (by omega)⟩, by norm_num⟩

#print axioms probe_largestSkipLateAt_twenty

/-! ## 5. Is the general theorem stronger than the concrete row?

Sanity check that `mem_seamGreedySupport_iff_testBit` is a genuine biconditional
with a computable right-hand side at an unrelated row, `s = 26`
(first late rank `18`), using Corr1's own theorem and nothing hand-fed. -/

theorem probe_lateEntryRemainder_26 : lateEntryRemainder 26 18 = 6478002689 := by
  unfold lateEntryRemainder earlyWeights seamWeights
  rw [seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_cons (by norm_num), seamWeightsFrom_eq_cons (by norm_num),
    seamWeightsFrom_eq_nil (by norm_num)]
  simp only [truncatedMersenneWeight, seamSubsetTarget]
  decide +kernel

theorem probe_lateCorrection_26 : lateCorrection 26 18 = 87380 := by
  rw [lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_cons (by norm_num), lateCorrection_eq_cons (by norm_num),
    lateCorrection_eq_zero (by norm_num)]
  decide +kernel

/-- The side conditions hold at a SECOND, independently chosen row. -/
theorem probe_hyps_26 :
    lateEntryRemainder 26 18 < 2 ^ (2 * 26 - 18 + 1) ∧
      lateCorrection 26 18 ≤ lateEntryRemainder 26 18 % 2 ^ (26 + 1) := by
  rw [probe_lateEntryRemainder_26, probe_lateCorrection_26]
  exact ⟨by norm_num, by decide +kernel⟩

/-- Corr1's criterion, applied at `s = 26`, produces a genuine late skip. -/
theorem probe_25_not_mem_26 : 25 ∉ seamWordSupport (seamGreedyWord 26) := by
  rw [mem_seamGreedySupport_iff_testBit (d := 18) (by norm_num) (by norm_num)
      (by norm_num) probe_hyps_26.1 probe_hyps_26.2 (by norm_num) (by norm_num),
    probe_lateEntryRemainder_26]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  decide +kernel

/-- …and hence `LargestSkipLateAt 26`, a row Corr1 does not itself treat. -/
theorem probe_largestSkipLateAt_26 : LargestSkipLateAt 26 :=
  ⟨25, ⟨by norm_num, by norm_num, probe_25_not_mem_26,
      fun e h1 h2 => absurd h2 (by omega)⟩, by norm_num⟩

#print axioms probe_25_not_mem_26
#print axioms probe_largestSkipLateAt_26

end BitCorr
end Erdos249257
