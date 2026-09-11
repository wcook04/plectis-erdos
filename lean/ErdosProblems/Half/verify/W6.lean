/-
Adversarial verification of `ErdosProblems/Half/FreeWalk2.lean`.

Section A: axiom audit of every declaration in FreeWalk2.
Section B: non-vacuity probes.  Each probe *instantiates* a FreeWalk2 theorem at
  concrete numerals whose hypotheses are discharged here by `norm_num`/`decide
  +kernel`, so a hypothesis that could never hold would surface as an unprovable
  side goal.  B3/B4 additionally show neither disjunct of the split is trivial.
Section C: cross-check that `consecutiveFail_of_deep_fail` produces the statement
  its docstring advertises — the 13-run is re-derived by direct kernel
  enumeration of `ConsecutiveFail`, bypassing the deep-failure route.
Section D: the one claim FreeWalk2 leaves entirely to Python — "the constant 4 in
  `certifiedKill_depth_split` is sharp" — deposited as a kernel-checked
  counterexample to the same statement with `3` in place of `4`.

Note on scope: `decide +kernel` on `ConsecutiveFail 22 4518 L K` (17-20 cells of
six-digit totients) does not terminate in reasonable time in the kernel, so those
two runs are cross-checked outside Lean instead; the 13-run below is the
in-kernel test of the indexing convention.
-/
import ErdosProblems.Half.FreeWalk2

namespace ErdosProblems
namespace Half
namespace VerifyW6

open Erdos249257 Erdos249257.TotientTailPeriodKiller
open ErdosProblems.Half.FreeWalk2

/-! ## A. Axiom audit -/

#print axioms ErdosProblems.Half.FreeWalk2.certifiedKill_depth_split
#print axioms ErdosProblems.Half.FreeWalk2.exists_certifiedKill_shift
#print axioms ErdosProblems.Half.FreeWalk2.certifiedKill_window_iff
#print axioms ErdosProblems.Half.FreeWalk2.ConsecutiveFail
#print axioms ErdosProblems.Half.FreeWalk2.consecutiveFail_of_deep_fail
#print axioms ErdosProblems.Half.FreeWalk2.deep_fail_of_consecutiveFail
#print axioms ErdosProblems.Half.FreeWalk2.consecutiveFail_iff
#print axioms ErdosProblems.Half.FreeWalk2.forall_consecutiveFail_iff
#print axioms ErdosProblems.Half.FreeWalk2.fail_26_3_19
#print axioms ErdosProblems.Half.FreeWalk2.depth_seven_nondegenerate
#print axioms ErdosProblems.Half.FreeWalk2.freeWalk_run_13
#print axioms ErdosProblems.Half.FreeWalk2.freeWalk_run_13_sharp
#print axioms ErdosProblems.Half.FreeWalk2.fail_22_4518_32
#print axioms ErdosProblems.Half.FreeWalk2.depth_fourteen_nondegenerate
#print axioms ErdosProblems.Half.FreeWalk2.freeWalk_run_19
#print axioms ErdosProblems.Half.FreeWalk2.freeWalk_run_19_sharp
#print axioms ErdosProblems.Half.FreeWalk2.freeWalk_run_19_exact
#print axioms ErdosProblems.Half.FreeWalk2.freeWalk_run_17
#print axioms ErdosProblems.Half.FreeWalk2.freeWalk_run_17_threshold
#print axioms ErdosProblems.Half.FreeWalk2.freeWalk_run_17_sharp
#print axioms ErdosProblems.Half.FreeWalk2.freeWalk_run_17_exact
#print axioms ErdosProblems.Half.FreeWalk2.no_small_absolute_run_bound

/-! ## B. Non-vacuity probes -/

/-- B1/B2.  `certifiedKill_depth_split` is NOT vacuous.  At `(h, N, L) =
(22, 4535, 15)` the doubling hypothesis holds (`4 * 4574 = 18296 < 32768 = 2^15`)
AND the depth-`16` certificate holds, so the theorem fires on live data. -/
theorem probe_split_fires :
    certifiedKill 22 4535 15 ∨ certifiedKill 22 4536 15 :=
  certifiedKill_depth_split (by norm_num) (by decide +kernel)

/-- B3.  Neither disjunct is trivially true: here the LEFT one is FALSE, so the
split genuinely has to move the base point. -/
theorem probe_split_left_false : ¬ certifiedKill 22 4535 15 := by decide +kernel

/-- B4.  …and the RIGHT one is the one that holds. -/
theorem probe_split_right_true : certifiedKill 22 4536 15 := by decide +kernel

/-- B5.  `certifiedKill_window_iff` at live numerals (`L = K = 16`,
`4 * 4574 = 18296 < 65536`): the hypothesis is dischargeable. -/
theorem probe_window_iff_applies :
    certifiedKill 22 4518 (16 + 16) ↔ ∃ j ≤ 16, certifiedKill 22 (4518 + j) 16 :=
  certifiedKill_window_iff (by norm_num)

/-- B6.  `consecutiveFail_iff` does apply to the `run_17` cell, so that run — and
only that one of the three — is governed by the two-sided law. -/
theorem probe_consecutiveFail_iff_applies :
    ConsecutiveFail 22 4518 16 16 ↔ ¬ certifiedKill 22 4518 (16 + 16) :=
  consecutiveFail_iff (by norm_num)

/-- B7.  The law also reaches one step above the depth floor `F(22,4518) = 14`:
at `L = 15`, `K = 18`, `4 * 4575 = 18300 < 32768`. -/
theorem probe_consecutiveFail_iff_at_floor_plus_one :
    ConsecutiveFail 22 4518 15 18 ↔ ¬ certifiedKill 22 4518 (15 + 18) :=
  consecutiveFail_iff (by norm_num)

/-- B8.  But it does NOT reach the floor itself, nor the `run_13` cell: both
`freeWalk_run_19` (`L = 14`) and `freeWalk_run_13` (`L = 7`) sit strictly outside
the hypothesis of `consecutiveFail_iff`, so for those two runs only the
one-directional `consecutiveFail_of_deep_fail` is available. -/
theorem probe_threshold_fails_for_run19_and_run13 :
    ¬ (4 * ((4518 : ℤ) + 18 + 22 + 14 + 2) < 2 ^ 14) ∧
    ¬ (4 * ((3 : ℤ) + 12 + 26 + 7 + 2) < 2 ^ 7) := by
  constructor <;> norm_num

/-- B9.  `ConsecutiveFail` is not a vacuously-true predicate: base `2` certifies
at `(h, L) = (26, 7)`, so the length-1 run there fails. -/
theorem probe_consecutiveFail_has_content : ¬ ConsecutiveFail 26 2 7 0 := by
  intro hrun
  exact hrun 0 (le_refl 0) (by decide +kernel)

/-! ## C. Indexing cross-check on the 13-run -/

/-- C1.  `ConsecutiveFail 26 3 7 12` re-derived by direct kernel enumeration of
all thirteen cells, not via `consecutiveFail_of_deep_fail`.  Agreement confirms
the deep-failure route means what its docstring says. -/
theorem xcheck_run_13 : ConsecutiveFail 26 3 7 12 := by decide +kernel

/-- C2.  …and the run is exactly thirteen long. -/
theorem xcheck_run_13_exact : ¬ ConsecutiveFail 26 3 7 13 := by decide +kernel

/-! ## D. The sharpness of the constant `4`, formalised

FreeWalk2 asserts "the constant `4` is sharp" from a Python grid only.  Here is
the assertion as a kernel-checked counterexample: at `(h, N, L) = (1, 10592, 15)`
the hypothesis `3 * (N+h+L+2) < 2^L` holds, `4 * (N+h+L+2) < 2^L` does not, the
depth-`16` certificate holds, and BOTH depth-`15` cells fail.  So
`certifiedKill_depth_split` is FALSE with `3` in place of `4`. -/

theorem sharp3_hyp_holds : 3 * ((10592 : ℤ) + 1 + 15 + 2) < 2 ^ 15 := by norm_num

theorem sharp4_hyp_fails : ¬ (4 * ((10592 : ℤ) + 1 + 15 + 2) < 2 ^ 15) := by
  norm_num

theorem sharp_deep_cert : certifiedKill 1 10592 (15 + 1) := by decide +kernel

theorem sharp_left_fails : ¬ certifiedKill 1 10592 15 := by decide +kernel

theorem sharp_right_fails : ¬ certifiedKill 1 (10592 + 1) 15 := by decide +kernel

/-- **The constant `4` cannot be lowered to `3`.** -/
theorem depth_split_fails_at_three :
    ¬ (∀ h N L : ℕ, 3 * ((N : ℤ) + (h : ℤ) + (L : ℤ) + 2) < 2 ^ L →
        certifiedKill h N (L + 1) →
        certifiedKill h N L ∨ certifiedKill h (N + 1) L) := by
  intro hall
  rcases hall 1 10592 15 (by norm_num) sharp_deep_cert with hx | hx
  · exact sharp_left_fails hx
  · exact sharp_right_fails hx

#print axioms probe_split_fires
#print axioms probe_consecutiveFail_iff_applies
#print axioms probe_consecutiveFail_iff_at_floor_plus_one
#print axioms xcheck_run_13
#print axioms depth_split_fails_at_three

end VerifyW6
end Half
end ErdosProblems
