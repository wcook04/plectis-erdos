import ErdosProblems.Erdos251.StreamingChunksV5.Chunk0002

/-! Generated UNRUN kernel candidates: primes in [8192,12288).
The endpoint literal is untrusted until block0003 is kernel checked.
Do not replace decide +kernel by native_decide. -/
namespace ErdosProblems.Erdos251.PaperV5.Streaming.Chunks
open ErdosProblems.Erdos251.PaperV5.Streaming
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

def state0003 : ℕ × ℕ := (1469, 60017637668174048522662856492438349301005488546327364823219617698960074297542399639920607748139445363151451102111142587683004738619870522980382263003960093590271380106546327748835130176115173658337235030837847265112169086689972005860702448269970649535648410259960854453307520764998161042991534509820802382754488197048980296394327810464708336118075807218492351883178557082393251036797785507613566934040064442188852011134064424503274263704613055)

theorem block0003 : scanBlock 8192 4096 state0002 = state0003 := by
  decide +kernel

theorem endpoint0003 : prefix 12288 = state0003 := by
  have h := scanBlock_prefix 8192 4096
  rw [endpoint0002] at h
  exact h.symm.trans block0003

end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks
