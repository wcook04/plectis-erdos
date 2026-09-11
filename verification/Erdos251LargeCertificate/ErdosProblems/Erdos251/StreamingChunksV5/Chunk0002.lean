import ErdosProblems.Erdos251.StreamingChunksV5.Chunk0001

/-! Generated UNRUN kernel candidates: primes in [4096,8192).
The endpoint literal is untrusted until block0002 is kernel checked.
Do not replace decide +kernel by native_decide. -/
namespace ErdosProblems.Erdos251.PaperV5.Streaming.Chunks
open ErdosProblems.Erdos251.PaperV5.Streaming
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

def state0002 : ℕ × ℕ := (1028, 10569411569218878494960326053720498114742957069340367173181946444411091756697041380554817906033884217833778535518322447155037103850167571116728816627507585436710091698851788935056090665635347601190767853017270433623651427238804751461629568697219904910941280342321211603197545243026679877334000558808196476773753)

theorem block0002 : scanBlock 4096 4096 state0001 = state0002 := by
  decide +kernel

theorem endpoint0002 : prefix 8192 = state0002 := by
  have h := scanBlock_prefix 4096 4096
  rw [endpoint0001] at h
  exact h.symm.trans block0002

end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks
