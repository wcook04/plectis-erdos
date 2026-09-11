import ErdosProblems.Erdos251.PaperStreamingCertificateV5

/-! Generated UNRUN kernel candidates: primes in [0,4096).
The endpoint literal is untrusted until block0001 is kernel checked.
Do not replace decide +kernel by native_decide. -/
namespace ErdosProblems.Erdos251.PaperV5.Streaming.Chunks
open ErdosProblems.Erdos251.PaperV5.Streaming
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

def state0001 : ℕ × ℕ := (564, 221887492037183359089323184397659057448942149792317033529572580577745796315091940954466776222219341534476968768777723659381081173903710178852653214927570217850816520966055)

theorem block0001 : scanBlock 0 4096 (0, 0) = state0001 := by
  decide +kernel

theorem endpoint0001 : prefix 4096 = state0001 := by
  have h := scanBlock_prefix 0 4096
  change scanBlock 0 4096 (0, 0) = prefix 4096 at h
  exact h.symm.trans block0001

end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks
