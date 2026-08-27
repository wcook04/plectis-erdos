import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Erdős #1041: scalar kernels for the self-inversive comparison dual

The companion ordinary proof identifies the evaluation image of the admissible
self-inversive comparison family with a positive weighted affine hyperplane.
This file checks the two finite-dimensional consequences used downstream:

* a positive weighted average equal to one has a coordinate at least one;
* any prescribed nonempty proper candidate set occurs in that hyperplane.

The resultant, residue, and self-inversive polynomial arguments remain in the
ordinary proof.  This module does not assert a metric connector or solve the
unrestricted Erdős problem.
-/

namespace ErdosProblems.Erdos1041.SelfInversiveComparisonDual

open Finset

/-- The scalar alternation consequence of the exact positive quadrature. -/
theorem exists_one_le_of_weightedAverage_eq_one
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (ω x : ι → ℝ)
    (hω : ∀ i, 0 < ω i)
    (hωsum : ∑ i, ω i = 1)
    (havg : ∑ i, ω i * x i = 1) :
    ∃ i, 1 ≤ x i := by
  by_contra h
  push Not at h
  have hlt : ∀ i, ω i * x i < ω i := fun i => by
    simpa using mul_lt_mul_of_pos_left (h i) (hω i)
  have hsumlt : (∑ i, ω i * x i) < ∑ i, ω i := by
    apply Finset.sum_lt_sum (fun i _ => le_of_lt (hlt i))
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Finset.mem_univ i, hlt i⟩
  linarith

/-- Two-level ratios of the ordinary proof have weighted average exactly one.
They are above one precisely on the chosen proper candidate set. -/
theorem prescribedCandidateRatios
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W ε : ℝ)
    (hε : 0 < ε)
    (hW0 : 0 < W)
    (hW1 : W < 1) :
    let x := fun i => if i ∈ S then 1 + ε else 1 - ε * W / (1 - W)
    (W * (1 + ε) + (1 - W) * (1 - ε * W / (1 - W)) = 1) ∧
      (∀ i, 1 < x i ↔ i ∈ S) := by
  dsimp
  have hWne : 1 - W ≠ 0 := by
    linarith
  constructor
  · field_simp
    ring
  · intro i
    by_cases hi : i ∈ S
    · simp [hi, hε]
    · have hden : 0 < 1 - W := sub_pos.mpr hW1
      have hdrop : 0 < ε * W / (1 - W) := div_pos (mul_pos hε hW0) hden
      simp [hi]
      linarith

end ErdosProblems.Erdos1041.SelfInversiveComparisonDual
