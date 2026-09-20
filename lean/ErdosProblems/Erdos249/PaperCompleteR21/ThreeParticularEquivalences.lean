import ErdosProblems.Erdos249.PeriodMultipleEscape
import Erdos249257.PivotAntiReconstruction
import Erdos249257.FullTargetPrimeAdjunctionNoGo

/-! The three particular equivalences of the long #249 manuscript
(`prop:b2`): the complete residue test, the selectable two-point window
sample, and the four integral tail differences.  Each is an equivalence, so
rewriting the quantified condition through it neither weakens nor strengthens
the arithmetic assertion. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21
open Erdos249257.TotientTailPeriodKiller
open Erdos249257.DiagonalPincerDecomposition
open Erdos249257.FullTargetPrimeAdjunctionNoGo
open ErdosProblems.Erdos249.PeriodMultipleEscape

/-- **Three particular equivalences** (`prop:b2`).

(a) the complete residue test `PeriodMultipleKillSupply` is equivalent to
irrationality of `S`;

(b) the selectable two-point window sample `DTWWindowSeparatedPairs` --
for every `h ≥ 1` and `X₀` a choice of `X, L` with `max(X₀,1) ≤ X` and
`16(2X+h+L+2) ≤ 2ᴸ`, a nonempty `T ⊆ [X,2X)`, a set `P ⊆ T × T` of ordered
pairs and a real `δ ≥ 0` with `δ ≤ ‖E_i - E_j‖` on `P` and
`2|T|²/5 ≤ |P|δ²` -- is equivalent to irrationality of `S`;

(c) for `H ≥ 0` and positive `p, q`, the conjunction of the four
integrality assertions `R_{2kH} - R_{kH} ∈ ℤ` for `k ∈ {1, p, q, pq}` is
equivalent to `R_{2H} - R_H ∈ ℤ` alone; neither `p` nor `q` is assumed
prime. -/
theorem three_particular_equivalences :
    (PeriodMultipleKillSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ (DTWWindowSeparatedPairs ↔
          Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ (∀ H p q : ℕ, 0 < p → 0 < q →
          ((IsIntegralValue (totientTail (2 * H) - totientTail H)
              ∧ IsIntegralValue (totientTail (2 * (p * H)) - totientTail (p * H))
              ∧ IsIntegralValue (totientTail (2 * (q * H)) - totientTail (q * H))
              ∧ IsIntegralValue
                  (totientTail (2 * (p * q * H)) - totientTail (p * q * H)))
            ↔ IsIntegralValue (totientTail (2 * H) - totientTail H))) := by
  refine ⟨periodMultipleKillSupply_iff_irrational,
    Erdos249257.TotientTailPeriodKiller.dtwWindowSeparatedPairs_iff_irrational_totient_series,
    ?_⟩
  intro H p q hp hq
  have h := fullTarget_primeAdjunction_diamond_iff_root H p q hp hq
  simpa only [scaleFullTargetHit_iff_integral, scaleDiagonalTailDifference] using h

/-- **The converse sample's numerical requirement** (`prop:b2` (b)): with the
two-point sample `T = {N, N+1}` and `P = {(N,N+1),(N+1,N)}`, so `|T| = 2` and
`|P| = 2`, and with `δ = 9/10`, the counted requirement `2|T|²/5 ≤ |P|δ²`
reads `8/5 ≤ 2(9/10)²`, and it holds. -/
theorem two_point_sample_numerical_requirement :
    2 * ((2 : ℝ)) ^ 2 / 5 = 8 / 5 ∧ (8 : ℝ) / 5 ≤ 2 * (9 / 10) ^ 2 :=
  ⟨by norm_num, by norm_num⟩

#print axioms three_particular_equivalences
#print axioms two_point_sample_numerical_requirement
end ErdosProblems.Erdos249.PaperCompleteR21
