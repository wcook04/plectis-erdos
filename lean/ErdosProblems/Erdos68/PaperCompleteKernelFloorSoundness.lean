import ErdosProblems.Erdos68.PaperCompleteKernelFloorAlgorithm
import ErdosProblems.Erdos68.PaperCompleteDyadicEnclosure
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Soundness and composition of independently kernel-reduced blocks

All index shifts and interval endpoints are proved symbolically. In particular,
no program outside Lean chooses the terms of the finite sum without a theorem
connecting that choice to `floorPrefix`.

Status: supplied proof candidate; not elaborated in this environment.
-/

namespace ErdosProblems.Erdos68.PaperComplete.FiniteLead

open scoped BigOperators

-- Ascending-factorial APIs below: Mathlib/Data/Nat/Factorial/Basic.lean, pinned source.
/-- With enough fuel, the structural balanced product is the ascending factorial. -/
theorem kernelProduct_spec (fuel start count : Nat) (hc : count ≤ fuel) :
    kernelProduct fuel start count = start.ascFactorial count := by
  induction fuel generalizing start count with
  | zero =>
      have hzero : count = 0 := by omega
      subst count
      rfl
  | succ fuel ih =>
      by_cases hzero : count = 0
      · subst count
        simp only [kernelProduct, Nat.ascFactorial_zero, ↓reduceIte]
      by_cases hone : count = 1
      · subst count
        simp [kernelProduct, Nat.ascFactorial]
      have hleft : count / 2 ≤ fuel := by omega
      have hright : count - count / 2 ≤ fuel := by omega
      have hsplit : count / 2 + (count - count / 2) = count := by omega
      calc
        kernelProduct (fuel + 1) start count =
            kernelProduct fuel start (count / 2) *
              kernelProduct fuel (start + count / 2) (count - count / 2) := by
            simp only [kernelProduct, hzero, hone, ↓reduceIte]
        _ = start.ascFactorial (count / 2) *
              (start + count / 2).ascFactorial (count - count / 2) := by
            rw [ih start (count / 2) hleft,
              ih (start + count / 2) (count - count / 2) hright]
        _ = start.ascFactorial (count / 2 + (count - count / 2)) :=
            -- Mathlib/Data/Nat/Factorial/Basic.lean.
            Nat.ascFactorial_mul_ascFactorial start (count / 2) (count - count / 2)
        _ = start.ascFactorial count := by rw [hsplit]

/-- The structural factorial computes the ordinary mathematical factorial. -/
theorem kernelFactorial_eq (n : Nat) : kernelFactorial n = n.factorial := by
  unfold kernelFactorial
  -- Nat.one_ascFactorial: Mathlib/Data/Nat/Factorial/Basic.lean.
  rw [kernelProduct_spec n 1 n (Nat.le_refl n), Nat.one_ascFactorial]

/-- Rewriting rule for closed arithmetic proofs without unary factorial recursion. -/
theorem kernelFactorial_function_eq : Nat.factorial = kernelFactorial := by
  funext n
  exact (kernelFactorial_eq n).symm

/-- Exact specification of the factorial-accumulator walk. -/
theorem kernelFloorWalk_spec (scale count start : Nat) :
    kernelFloorWalk scale count start start.factorial =
      ∑ j ∈ Finset.range count, scale / ((start + j).factorial - 1) := by
  induction count generalizing start with
  | zero =>
      -- range_zero: Mathlib/Data/Finset/Range.lean.
      -- sum_empty: Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean.
      simp only [kernelFloorWalk, Finset.range_zero, Finset.sum_empty]
  | succ count ih =>
      -- Nat.factorial_succ: Mathlib/Data/Nat/Factorial/Basic.lean.
      have hfac : (start + 1) * start.factorial = (start + 1).factorial :=
        (Nat.factorial_succ start).symm
      -- sum_range_succ': additive declaration generated from prod_range_succ',
      -- Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean (pinned source).
      have hshift :
          (∑ j ∈ Finset.range count,
            scale / ((start + 1 + j).factorial - 1)) =
          ∑ j ∈ Finset.range count,
            scale / ((start + (j + 1)).factorial - 1) := by
        -- sum_congr: Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean.
        apply Finset.sum_congr rfl
        intro j _
        have hindex : start + 1 + j = start + (j + 1) := by omega
        rw [hindex]
      calc
        kernelFloorWalk scale (count + 1) start start.factorial =
            scale / (start.factorial - 1) +
              kernelFloorWalk scale count (start + 1) ((start + 1) * start.factorial) := rfl
        _ = scale / (start.factorial - 1) +
              ∑ j ∈ Finset.range count,
                scale / ((start + (j + 1)).factorial - 1) := by
            rw [hfac, ih, hshift]
        _ = ∑ j ∈ Finset.range (count + 1),
              scale / ((start + j).factorial - 1) := by
            rw [Finset.sum_range_succ']
            simp only [Nat.add_zero, Nat.add_comm]

/-- The fast factorial in the executable block has its ordinary factorial meaning. -/
theorem kernelFloorBlock_spec (scale start count : Nat) :
    kernelFloorBlock scale start count =
      ∑ j ∈ Finset.range count, scale / ((start + j).factorial - 1) := by
  unfold kernelFloorBlock
  rw [kernelFactorial_eq]
  exact kernelFloorWalk_spec scale count start

/-- Adjacent blocks compose with no omitted or duplicated index. -/
theorem kernelFloorBlock_add (scale start a b : Nat) :
    kernelFloorBlock scale start (a + b) =
      kernelFloorBlock scale start a + kernelFloorBlock scale (start + a) b := by
  rw [kernelFloorBlock_spec, kernelFloorBlock_spec, kernelFloorBlock_spec]
  -- sum_range_add: Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean.
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hindex : start + (a + j) = start + a + j := (Nat.add_assoc start a j).symm
  rw [hindex]

/-- Convert the paper's closed prefix [2,N] to exactly N-1 consecutive terms. -/
theorem floorPrefix_eq_kernelFloorBlock (scale cutoff : Nat) (hc : 2 ≤ cutoff) :
    floorPrefix scale cutoff = kernelFloorBlock scale 2 (cutoff - 1) := by
  rw [kernelFloorBlock_spec]
  unfold floorPrefix
  symm
  -- sum_bij: Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean.
  -- mem_Icc: Mathlib/Order/Interval/Finset/Defs.lean.
  refine Finset.sum_bij (fun j _ => 2 + j) ?_ ?_ ?_ ?_
  · intro j hj
    -- mem_range: Mathlib/Data/Finset/Range.lean.
    dsimp only
    have hjlt : j < cutoff - 1 := Finset.mem_range.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj k hk heq
    dsimp only at heq
    omega
  · intro n hn
    obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
    refine ⟨n - 2, Finset.mem_range.mpr (by omega), ?_⟩
    dsimp only
    omega
  · intro j _
    rfl

end ErdosProblems.Erdos68.PaperComplete.FiniteLead
