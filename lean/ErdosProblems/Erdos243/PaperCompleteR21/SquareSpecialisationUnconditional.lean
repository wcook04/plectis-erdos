import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR21.CubicRateExclusionChain
import ErdosProblems.Erdos243.PaperCompleteR21.SquareSpecialisationDedekind

/-!
# Erdős 243: the square-specialisation lemma and its consumers, unconditionally

`SquareSpecialisationDedekind.lean` proves the statement of `long243:res:squarespec`
(`paper/reasoning-parts/erdos243/core.tex`, lemma at line 303) from the simple pole of the
Dedekind zeta function, which is in Mathlib; the Chebotarev density theorem is not used.  This
file records it as `squareSpecialisation : SquareSpecialisation` and discharges the hypothesis
`hss : SquareSpecialisation` of the three downstream paper statements in
`CubicRateExclusionChain.lean`:

* `transport_square_unconditional` — `long243:res:transportsquare`;
* `cubic_exclusion_unconditional` — `long243:res:cubicexclusion`;
* `cubic_rate_irrationality_unconditional` — `res:cubicrate` and `long243:res:cubicrate`.

Each is the corresponding `CubicRateExclusionChain` theorem applied to `squareSpecialisation`,
with no hypothesis added.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20

/-- **`long243:res:squarespec`**, with no hypothesis: if `f ∈ ℚ[T]` is irreducible with root
`α`, `H (α) ≠ 0`, and for all but finitely many primes `ℓ` every root `r` of `f` modulo `ℓ` has
`H (r)` a nonzero square modulo `ℓ`, then `H (α)` is a square in `ℚ(α)`. -/
theorem squareSpecialisation : SquareSpecialisation :=
  squareSpecialisation_holds

/-- `long243:res:transportsquare`, unconditionally. -/
theorem transport_square_unconditional
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀)
    (hroot : α ^ 3 = α - algebraMap ℚ L₀ (6 * (c : ℚ) / (m : ℚ))) :
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = α ^ 2 - 1 :=
  transport_square squareSpecialisation a u v m c T hm hv hnum hden hcop hzero L₀ α hroot

/-- `long243:res:cubicexclusion`, unconditionally. -/
theorem cubic_exclusion_unconditional
    (a C D : ℕ → ℤ) (ha : ∀ n, 0 < a n) (hC : ∀ n, 0 < C n) (hD : ∀ n, 0 < D n)
    (hCrec : ∀ n, C (n + 1) = a n * C n - D n)
    (hDrec : ∀ n, D (n + 1) = a n * D n)
    (A B : ℚ) (hA : 0 < A) :
    (∃ dens : ℝ, 0 < dens ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        dens * (X : ℝ) ≤ (exceptionCount
          {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
          (X + 1) : ℝ)) ∧
      ¬ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℚ) = A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B :=
  cubic_exclusion squareSpecialisation a C D ha hC hD hCrec hDrec A B hA

/-- `res:cubicrate` / `long243:res:cubicrate`, unconditionally: a strictly increasing sequence
of positive integers with `a n ^ 2 / a (n + 1) = 1 + 3 / n + o (n ^ (-3))` has irrational
reciprocal sum. -/
theorem cubic_rate_irrationality_unconditional
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv :=
  cubic_rate_irrationality squareSpecialisation a ha hpos hrate Sv hS

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.transport_square_unconditional
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.cubic_exclusion_unconditional
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional

end ErdosProblems.Erdos243.PaperCompleteR21
