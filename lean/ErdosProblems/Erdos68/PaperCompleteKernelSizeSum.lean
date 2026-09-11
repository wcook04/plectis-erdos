import ErdosProblems.Erdos68.PaperCompleteKernelFloorSoundness
import ErdosProblems.Erdos68.PaperCompleteFiniteSizeData
import ErdosProblems.Erdos68.FiniteLeadBlocks.Size000
import ErdosProblems.Erdos68.FiniteLeadBlocks.Size001

/-! Compose proved adjacent blocks and check the final addition of their witnesses.
There is no trusted certificate hypothesis in this theorem. Compilation has not
been performed in the return environment.
-/
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

namespace ErdosProblems.Erdos68.PaperComplete.FiniteLead

/-- Complete exact size floor prefix, assembled from 2 checked blocks. -/
theorem size_floorPrefix_checked :
    floorPrefix (2 ^ 80000) 7053 = sizeLower := by
  calc
    floorPrefix (2 ^ 80000) 7053 =
        kernelFloorBlock (2 ^ 80000) 2 7052 :=
      floorPrefix_eq_kernelFloorBlock (2 ^ 80000) 7053 (by decide)
    _ = (KernelBlocks.Size000.value + KernelBlocks.Size001.value) := ((kernelFloorBlock_add (2 ^ 80000) 2 4096 2956).trans
  (congrArg₂ (fun x y : Nat => x + y) KernelBlocks.Size000.checked KernelBlocks.Size001.checked))
    _ = sizeLower := by decide +kernel

end ErdosProblems.Erdos68.PaperComplete.FiniteLead
