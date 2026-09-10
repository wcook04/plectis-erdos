import Init

/-!
# Structurally recursive kernel computation of factorial-gap floor blocks

Only total definitions occur here. The balanced product has an explicit fuel
argument, avoiding well-founded-recursion proof reduction during the large
kernel computations. Its specification is proved in the soundness module.
No external arithmetic result, compiled evaluator or factorial oracle is trusted.

The walk contains `count` consecutive summands starting at `start`. Its first
factorial is computed by the balanced product; later factorials are updated by
one multiplication. Each generated leaf recomputes at most 4096 summands.
-/

namespace ErdosProblems.Erdos68.PaperComplete.FiniteLead

/-- Balanced interval product with structural recursion on fuel. The value at
insufficient fuel is deliberately unspecified by the specification theorem. -/
def kernelProduct : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | fuel + 1, start, count =>
      if count = 0 then 1
      else if count = 1 then start
      else
        kernelProduct fuel start (count / 2) *
          kernelProduct fuel (start + count / 2) (count - count / 2)

/-- Enough structural fuel to multiply the interval [1,n], with early leaves. -/
def kernelFactorial (n : Nat) : Nat := kernelProduct n 1 n

/-- Straight-line factorial update followed by exact natural division.
The recurrence decreases its first argument after the fixed scale. -/
def kernelFloorWalk (scale : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | count + 1, start, fac =>
      scale / (fac - 1) +
        kernelFloorWalk scale count (start + 1) ((start + 1) * fac)

/-- One block, with the initial factorial also computed in the kernel. -/
def kernelFloorBlock (scale start count : Nat) : Nat :=
  kernelFloorWalk scale count start (kernelFactorial start)

end ErdosProblems.Erdos68.PaperComplete.FiniteLead
