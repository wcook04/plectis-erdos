import ErdosProblems.Erdos68.PaperCompleteKernelFloorSoundness

/-! Small end-to-end compile gates, including a deliberately altered witness.
No full-size computation is required by this file. -/
set_option maxRecDepth 100000
namespace ErdosProblems.Erdos68.PaperComplete.FiniteLead

theorem kernel_block_smoke :
    kernelFloorBlock (2 ^ 128) 7 37 = 0xed4e682f0f593c87574ccdd22998d := by decide +kernel

theorem kernel_block_mutation_rejected :
    ¬ kernelFloorBlock (2 ^ 128) 7 37 = 0xed4e682f0f593c87574ccdd22998e := by decide +kernel

theorem kernel_prefix_smoke : floorPrefix (2 ^ 128) 43 = 0x140e54b614ed8ada92c805445ce0c226e := by
  rw [floorPrefix_eq_kernelFloorBlock (2 ^ 128) 43 (by decide)]
  decide +kernel

end ErdosProblems.Erdos68.PaperComplete.FiniteLead
