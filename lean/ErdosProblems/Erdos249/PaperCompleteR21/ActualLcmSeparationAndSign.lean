import Erdos249257.TotientActualLcmOrbitSeparation
import Erdos249257.TotientActualLcmOrbitSign

/-! Paper-form restatements of the separation and sign block of the long #249
manuscript: the global-to-local identity (`prop:SEP-01-inv`), the rational
approximation with an explicit error bound (`prop:SEP-02-inv`), unconditional
positivity of the translated tail difference (`prop:SGN-01`), and the residue
forced by integrality (`prop:SGN-03`).  Throughout `H = H(2^a) = lcm(1,…,2^a)`
and `Ω_a = R_{2H} - R_H`. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine

/-! ### `prop:SEP-01-inv` -- a global-to-local identity -/

/-- **A global-to-local identity** (`prop:SEP-01-inv`).
`Ω_a = 2^H(2^H-1)·S - (Φ_{2H} - Φ_H)` with `H = H(2^a)`, so a separation
estimate for `Ω_a` is an estimate for this integer translate of a multiple
of `S`. -/
theorem actualLcmTailOrbit_global_to_local (a : ℕ) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      = (2 : ℝ) ^ periodLcm (2 ^ a) * ((2 : ℝ) ^ periodLcm (2 ^ a) - 1)
            * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
          - ((totientPrefix (2 * periodLcm (2 ^ a)) : ℝ)
              - (totientPrefix (periodLcm (2 ^ a)) : ℝ)) := by
  simpa [actualLcmTailOrbit, actualLcmHeight] using
    actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix a

/-! ### `prop:SEP-02-inv` -- a rational approximation with an error bound -/

/-- **A rational approximation with an error bound** (`prop:SEP-02-inv`).
For all `a, q`, with `H = H(2^a)` and the finite `ρ_{a,q}`,
`|Ω_a - ρ_{a,q}| < ε_{a,q} = (2H + 2q + 3)/2^(2q+1)`.
The bound tends to zero with `q` for fixed `a`; no optimality is asserted. -/
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit (a q : ℕ) :
    |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)))
        - actualLcmRawApprox a q|
      < ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1) := by
  simpa [actualLcmTailOrbit, actualLcmHeight, actualLcmRawErrorRadius] using
    abs_actualLcmTailOrbit_sub_rawApprox_lt a q

/-! ### `prop:SGN-01` -- unconditional positivity -/

/-- **Unconditional positivity** (`prop:SGN-01`).
For `a ≥ 8` and `J + (a+6) < 2·2^a`, the true infinite translated tail
difference satisfies `0 < R_{2H+J} - R_{H+J}` with `H = H(2^a)`, with no
irrationality hypothesis.  Specialised at `J = 0` this gives `0 < Ω_a`. -/
theorem actualLcm_tailDiff_shift_pos_paper {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 < totientTail (2 * periodLcm (2 ^ a) + J)
          - totientTail (periodLcm (2 ^ a) + J) :=
  actualLcmTailDiff_shift_pos ha hshort

/-- **Unconditional positivity** (`prop:SGN-01`) at `J = 0`: `0 < Ω_a`. -/
theorem actualLcmTailOrbit_pos {a : ℕ} (ha : 8 ≤ a) :
    0 < totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) := by
  have hpow : a < 2 ^ a := Nat.lt_two_pow_self
  have h := actualLcmTailDiff_shift_pos (a := a) (J := 0) ha (by omega)
  simpa using h

/-! ### `prop:SGN-03` -- the residue forced by integrality -/

/-- **The residue forced by integrality** (`prop:SGN-03`).
Let `a, J, K` with `a ≥ 8`, `H = H(2^a)`, `J+K+(a+6) < 2·2^a` and
`2H+J+K+2 < 2^K`.  If `R_{2H+J} - R_{H+J} ∈ ℤ`, then
`D(H, H+J, K) mod 2^K = 2^K - (R_{2H+J+K} - R_{H+J+K})` and
`0 < R_{2H+J+K} - R_{H+J+K} < 2H+J+K+2`: the later tail difference is a
positive integer whose least nonnegative residue lies near `2^K`.  Positivity
alone therefore does not prove nonintegrality. -/
theorem actualLcm_integral_forces_topEdgeResidue_paper {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ K)
    (hint : ∃ d : ℤ, (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J)
        - totientTail (periodLcm (2 ^ a) + J)) :
    ∃ e : ℤ,
      ((e : ℝ) = totientTail (2 * periodLcm (2 ^ a) + J + K)
          - totientTail (periodLcm (2 ^ a) + J + K))
        ∧ windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K
              % (2 : ℤ) ^ K
            = (2 : ℤ) ^ K - e
        ∧ 0 < e
        ∧ e < ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) := by
  obtain ⟨d, hd⟩ := hint
  obtain ⟨h1, h2, h3⟩ := actualLcm_integral_forces_topEdgeResidue ha hshort hd hroom
  have hd' : (d : ℝ)
      = totientTail ((periodLcm (2 ^ a) + J) + periodLcm (2 ^ a))
        - totientTail (periodLcm (2 ^ a) + J) := by
    rw [show periodLcm (2 ^ a) + J + periodLcm (2 ^ a)
        = 2 * periodLcm (2 ^ a) + J from by omega]
    exact hd
  have htrack := carryOrbit_eq_tail_diff hd' K
  refine ⟨carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) d K, ?_, h1, ?_, ?_⟩
  · rw [htrack, show periodLcm (2 ^ a) + J + K + periodLcm (2 ^ a)
      = 2 * periodLcm (2 ^ a) + J + K from by omega]
  · linarith
  · linarith

#print axioms actualLcmTailOrbit_global_to_local
#print axioms abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit
#print axioms actualLcm_tailDiff_shift_pos_paper
#print axioms actualLcmTailOrbit_pos
#print axioms actualLcm_integral_forces_topEdgeResidue_paper
end ErdosProblems.Erdos249.PaperCompleteR21
