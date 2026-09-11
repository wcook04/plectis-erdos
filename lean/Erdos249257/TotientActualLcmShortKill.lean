import Erdos249257.TotientActualLcmOrbitArithmetic
import Erdos249257.DiagonalPincerCertificateT64Endpoint

namespace Erdos249257
namespace DiagonalFreshLossBridge
namespace PowerTwoOddWindowAffine

/-!
# The short actual-LCM arithmetic-kill producer

The endpoint-facing producer in `TotientActualLcmOrbitArithmetic` asks for
cofinally many residue-band kills inside the window `L < 2 * 2^a`.  We begin
with the first exact witnesses, stated directly as that producer rather than
as detached numerical identities.
-/

/-- The first exact short-window kill, at `t = 2^4` and length `23`. -/
theorem lcmDiagonalArithmeticKill_two_pow_four :
    LcmDiagonalArithmeticKill (2 ^ 4) 23 := by
  apply (lcmDiagonalArithmeticKill_iff_certifiedKill (2 ^ 4) 23).2
  simpa using
    TotientTailPeriodKiller.certifiedKill_diagonal_t16

/-- The compressed t=64 certificate supplies the exponent-six short-window
kill.  This consumes `certifiedKill_diagonal_t64` and feeds both the actual
orbit nonintegrality route and `PowerTwoActualLcmShortArithmeticKillSupply`. -/
theorem lcmDiagonalArithmeticKill_two_pow_six :
    LcmDiagonalArithmeticKill (2 ^ 6) 93 := by
  apply (lcmDiagonalArithmeticKill_iff_certifiedKill (2 ^ 6) 93).2
  simpa using
    TotientTailPeriodKiller.certifiedKill_diagonal_t64

/-- The two routed arithmetic kills already rule out integral actual-LCM
tail orbits at exponents four and six. -/
theorem actualLcmTailOrbit_four_and_six_notMem_int :
    actualLcmTailOrbit 4 ∉ Set.range ((↑) : ℤ → ℝ) ∧
      actualLcmTailOrbit 6 ∉ Set.range ((↑) : ℤ → ℝ) := by
  exact ⟨
    actualLcmTailOrbit_notMem_int_of_arithmeticKill
      lcmDiagonalArithmeticKill_two_pow_four,
    actualLcmTailOrbit_notMem_int_of_arithmeticKill
      lcmDiagonalArithmeticKill_two_pow_six⟩

/-- The new exponent-six certificate rules out the next actual-LCM tail
orbit directly, reusing `actualLcmTailOrbit_notMem_int_of_arithmeticKill`. -/
theorem actualLcmTailOrbit_six_notMem_int :
    actualLcmTailOrbit 6 ∉ Set.range ((↑) : ℤ → ℝ) := by
  exact actualLcmTailOrbit_notMem_int_of_arithmeticKill
    lcmDiagonalArithmeticKill_two_pow_six

/-- The exponent-six witness extends the exact cofinal-producer shape through
six; the remaining endpoint gap is now precisely the unbounded continuation
beyond this finite prefix. -/
theorem powerTwoActualLcmShortArithmeticKillSupply_through_six
    (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      LcmDiagonalArithmeticKill (2 ^ a) L := by
  exact ⟨6, 93, ha₀, by norm_num,
    lcmDiagonalArithmeticKill_two_pow_six⟩

/-- Endpoint fan-in: a cofinal supply of the exact short arithmetic kills is
already sufficient for Erdős #249. -/
theorem irrational_totientSeries_of_shortArithmeticKillSupply
    (hsupply : PowerTwoActualLcmShortArithmeticKillSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_actualLcmOrbitNonintegralitySupply
    (actualLcmOrbitNonintegralitySupply_of_shortArithmeticKill hsupply)

#print axioms lcmDiagonalArithmeticKill_two_pow_four
#print axioms lcmDiagonalArithmeticKill_two_pow_six
#print axioms actualLcmTailOrbit_four_and_six_notMem_int
#print axioms actualLcmTailOrbit_six_notMem_int
#print axioms powerTwoActualLcmShortArithmeticKillSupply_through_six
#print axioms irrational_totientSeries_of_shortArithmeticKillSupply

end PowerTwoOddWindowAffine
end DiagonalFreshLossBridge
end Erdos249257
